import CutQueryComplexity.StarContraction2022.Quantum.Forest.Run
import CutQueryComplexity.StarContraction2022.Quantum.Forest.CostBounds
import CutQueryComplexity.StarContraction2022.Certificates.Semantics

/-! # Executed residual forests and the low-cut candidate

All constructors use only public data. Successive calls update their deleted
edge set from actual returned forests, including unsuccessful spanning calls.
The certificate and minimum-cut guarantees concern this adaptive execution.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest
noncomputable section
open ProductPrograms
open CutQueryComplexity.Probability
open scoped Classical ENNReal

variable {n k : ℕ}

abbrev ForestBatch (n k : ℕ) := Fin k → State n

def batchGraphs (B : ForestBatch n k) : List (_root_.SimpleGraph (Fin n)) :=
  List.ofFn fun i => (B i).graph

@[simp] theorem batchGraphs_cons (F : State n) (B : ForestBatch n k) :
    batchGraphs (Fin.cons F B) = F.graph :: batchGraphs B := by
  simp [batchGraphs, List.ofFn_succ]

@[simp] theorem batchGraphs_length (B : ForestBatch n k) : (batchGraphs B).length = k := by
  simp [batchGraphs]

/-- Fresh calls, with the next residual determined by the actual previous output. -/
def collectForests (E : LearnedEdges n) (delta : ℝ) :
    (k : ℕ) → ProductTree n (ForestBatch n k) (k * forestBudget n delta)
  | 0 => RTree.pure (PMF.pure Fin.elim0)
  | k + 1 => RTree.cast (by simp [Nat.succ_mul, Nat.add_comm])
      ((forestRun n E delta).bind fun F =>
        RTree.map (Fin.cons F) (collectForests (E ∪ F.val) delta k))

@[simp] theorem collectForests_eval_zero (E : LearnedEdges n) (delta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (collectForests E delta 0).eval read = PMF.pure Fin.elim0 := by
  simp [collectForests]

theorem collectForests_eval_succ (E : LearnedEdges n) (delta : ℝ) (k : ℕ)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (collectForests E delta (k + 1)).eval read =
      ((forestRun n E delta).eval read).bind fun F =>
        ((collectForests (E ∪ F.val) delta k).eval read).map (Fin.cons F) := by
  simp only [collectForests, RTree.eval_cast, RTree.eval_bind, RTree.eval_map]

/-- The exact operational law also records the sum of the executed query counts. -/
theorem collectForests_run_succ (E : LearnedEdges n) (delta : ℝ) (k : ℕ)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (collectForests E delta (k + 1)) =
      (RTree.run read (forestRun n E delta)).bind fun first =>
        (RTree.run read (collectForests (E ∪ first.1.val) delta k)).map
          fun rest => (Fin.cons first.1 rest.1, first.2 + rest.2) := by
  simp only [collectForests, RTree.run_cast, RTree.run_bind,
    run_map_outputs, PMF.map_comp, Function.comp_def]

theorem collectForests_cost (E : LearnedEdges n) (delta : ℝ) (k : ℕ)
    (read : Finset (Fin n) → ProductAnswer n 1) {out : ForestBatch n k × ℕ}
    (hout : out ∈ (RTree.run read (collectForests E delta k)).support) :
    out.2 ≤ k * forestBudget n delta := RTree.cost_le _ read hout

theorem knownSubgraph_empty (G : CapacityGraph (Fin n) 1) : KnownSubgraph ∅ G := by
  intro u v
  simp [knownWeight]

theorem knownSubgraph_union (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (F : State n) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) : KnownSubgraph (E ∪ F.val) G := by
  apply knownSubgraph_of_edges
  intro u v huv he
  rcases Finset.mem_union.mp he with he | he
  · apply le_antisymm (Nat.le_of_lt_succ (G.w u v).isLt)
    simpa [knownWeight, huv, he] using hE u v
  · exact ((residualNeighbor_iff_mem G E u v).mpr (hF he)).1

@[simp] theorem residualGraph_empty (G : CapacityGraph (Fin n) 1) :
    residualGraph G ∅ = G := by
  ext u v
  simp [residualGraph_w, knownWeight]

/-- Finite deletion by the actual output agrees with weighted residual subtraction. -/
theorem residualGraph_union (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (F : State n) (hF : F.ResidualSound G.toWeighted.support E) :
    (residualGraph G (E ∪ F.val)).toWeighted =
      (residualGraph G E).toWeighted.subtract (SimpleGraph.toWeighted F.graph) := by
  ext u v
  have ha : F.graph.Adj u v ↔ s(u, v) ∈ F.val := by
    rw [← F.edgeFinset_graph, _root_.SimpleGraph.mem_edgeFinset,
      _root_.SimpleGraph.mem_edgeSet]
  have hf : s(u, v) ∈ F.val → ResidualNeighbor G E u v :=
    fun he => (residualNeighbor_iff_mem G E u v).mpr (hF he)
  change (((residualGraph G (E ∪ F.val)).w u v : ℕ) : ℝ) =
    max 0 ((((residualGraph G E).w u v : ℕ) : ℝ) -
      (SimpleGraph.toWeighted F.graph).w u v)
  rw [residualGraph_w_eq_indicator, residualGraph_w_eq_indicator,
    SimpleGraph.toWeighted_w, ha]
  have hu : ResidualNeighbor G (E ∪ F.val) u v ↔
      ResidualNeighbor G E u v ∧ s(u, v) ∉ F.val := by
    simp [ResidualNeighbor, not_or, and_assoc]
  by_cases he : s(u, v) ∈ F.val
  · simp [he, hf he, hu]
  · by_cases hr : ResidualNeighbor G E u v <;> simp [he, hr, hu]

/-- Soundness at every residual history, without assuming any spanning success. -/
def BatchSound (G : CapacityGraph (Fin n) 1) :
    (E : LearnedEdges n) → {k : ℕ} → ForestBatch n k → Prop
  | _, 0, _ => True
  | E, k + 1, B => (B 0).ResidualSound G.toWeighted.support E ∧
      BatchSound G (E ∪ (B 0).val) (fun i : Fin k => B i.succ)

@[simp] theorem batchSound_cons (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (F : State n) (B : ForestBatch n k) :
    BatchSound G E (Fin.cons F B) ↔
      F.ResidualSound G.toWeighted.support E ∧ BatchSound G (E ∪ F.val) B := by
  simp [BatchSound]

theorem collectForests_sound (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (hE : KnownSubgraph E G) (delta : ℝ) (k : ℕ) {B : ForestBatch n k}
    (hB : B ∈ ((collectForests E delta k).eval (productRead G)).support) :
    BatchSound G E B := by
  induction k generalizing E with
  | zero => trivial
  | succ k ih =>
      rw [collectForests_eval_succ] at hB
      obtain ⟨F, hF, hB⟩ := (PMF.mem_support_bind_iff _ _ _).mp hB
      obtain ⟨C, hC, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hB
      have hs := forestRun_residualSound E delta G hE hF
      exact (batchSound_cons G E F C).mpr
        ⟨hs, ih (E ∪ F.val) (knownSubgraph_union G E F hE hs) hC⟩

/-- Conditional union bound for the actual adaptive forest chain. -/
theorem collectForests_chain_failure (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (hE : KnownSubgraph E G) (delta : ℝ) (hdelta : 0 < delta) (k : ℕ) :
    mass ((collectForests E delta k).eval (productRead G))
      (fun B => ¬Certificates.ResidualForestChain (residualGraph G E).toWeighted (batchGraphs B)) ≤
      (k : ℝ≥0∞) * ENNReal.ofReal delta := by
  induction k generalizing E with
  | zero => simp [batchGraphs, Certificates.ResidualForestChain]
  | succ k ih =>
      rw [collectForests_eval_succ, mass_bind]
      change expect ((forestRun n E delta).eval (productRead G))
        (fun F => mass (((collectForests (E ∪ F.val) delta k).eval (productRead G)).map
          (Fin.cons F)) (fun B => ¬Certificates.ResidualForestChain
            (residualGraph G E).toWeighted (batchGraphs B))) ≤ _
      calc
        _ ≤ expect ((forestRun n E delta).eval (productRead G))
            (fun F => (if ¬ForestSuccess G E F then 1 else 0) +
              (k : ℝ≥0∞) * ENNReal.ofReal delta) := by
          apply expect_mono_on_support
          intro F hF
          have hs := forestRun_residualSound E delta G hE hF
          by_cases hg : ForestSuccess G E F
          · simp only [not_true_eq_false, hg, ite_false, zero_add, mass_map,
              batchGraphs_cons, Certificates.ResidualForestChain,
              (forestSuccess_iff_capacity_residual G E F).mp hg, true_and]
            rw [← residualGraph_union G E F hs]
            exact ih (E ∪ F.val) (knownSubgraph_union G E F hE hs)
          · simp only [hg, not_false_eq_true, ite_true]
            exact (mass_le_one _ _).trans (by simp)
        _ = mass ((forestRun n E delta).eval (productRead G)) (fun F => ¬ForestSuccess G E F) +
            (k : ℝ≥0∞) * ENNReal.ofReal delta := by
          rw [expect_add, expect_const]
          congr 1
          rw [expect, mass_eq_tsum]
          apply tsum_congr
          intro F
          by_cases hg : ForestSuccess G E F <;> simp [hg]
        _ ≤ ENNReal.ofReal delta + (k : ℝ≥0∞) * ENNReal.ofReal delta :=
          add_le_add (forestRun_failure E delta G hE hdelta) le_rfl
        _ = _ := by push_cast; ring

/-- Unit forest capacities retain their multiplicities in the public certificate. -/
def batchCertificate (B : ForestBatch n k) : WeightedGraph (Fin n) :=
  Certificates.forestSum (batchGraphs B)

theorem batchCertificate_of_chain (G : CapacityGraph (Fin n) 1) (B : ForestBatch n k)
    (hB : Certificates.ResidualForestChain G.toWeighted (batchGraphs B)) :
    IsThresholdCertificate k G.toWeighted (batchCertificate B) := by
  simpa only [batchGraphs_length, batchCertificate] using
    Certificates.residualForestChain_certificate G.toWeighted G.integral_toWeighted (batchGraphs B) hB

/-- Public finite output, with per-call error eta/r and no hidden input parameter. -/
def certificateRun (n r : ℕ) (eta : ℝ) :
    ProductTree n (ForestBatch n r) (r * forestBudget n (eta / (r : ℝ))) :=
  collectForests ∅ (eta / (r : ℝ)) r

theorem certificateRun_sound (n r : ℕ) (eta : ℝ) (G : CapacityGraph (Fin n) 1)
    {B : ForestBatch n r} (hB : B ∈ ((certificateRun n r eta).eval (productRead G)).support) :
    BatchSound G ∅ B :=
  collectForests_sound G ∅ (knownSubgraph_empty G) _ r hB

@[simp] theorem certificateRun_eval_zero (n : ℕ) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (certificateRun n 0 eta).eval read = PMF.pure Fin.elim0 := by
  simp [certificateRun]

theorem certificateRun_chain_failure (n r : ℕ) (eta : ℝ) (heta : 0 < eta)
    (G : CapacityGraph (Fin n) 1) :
    mass ((certificateRun n r eta).eval (productRead G))
      (fun B => ¬Certificates.ResidualForestChain G.toWeighted (batchGraphs B)) ≤ ENNReal.ofReal eta := by
  by_cases hr : r = 0
  · subst r
    simp [batchGraphs, Certificates.ResidualForestChain]
  · have hrpos : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
    have h := collectForests_chain_failure G ∅ (knownSubgraph_empty G)
      (eta / (r : ℝ)) (div_pos heta hrpos) r
    simp only [residualGraph_empty] at h
    apply h.trans
    have he : (r : ℝ≥0∞) * ENNReal.ofReal (eta / (r : ℝ)) = ENNReal.ofReal eta := by
      rw [← ENNReal.ofReal_natCast r, ← ENNReal.ofReal_mul (Nat.cast_nonneg r)]
      congr 1
      field_simp
    exact he.le

theorem certificateRun_chain_successProb (n r : ℕ) (eta : ℝ) (heta : 0 < eta)
    (G : CapacityGraph (Fin n) 1) :
    1 - eta ≤ (certificateRun n r eta).successProb (productRead G)
      (fun B => Certificates.ResidualForestChain G.toWeighted (batchGraphs B)) := by
  rw [RTree.successProb_eq]
  exact success_of_failure_le _ _ heta.le (certificateRun_chain_failure n r eta heta G)

theorem certificateRun_certificate_failure (n r : ℕ) (eta : ℝ) (heta : 0 < eta)
    (G : CapacityGraph (Fin n) 1) :
    mass ((certificateRun n r eta).eval (productRead G))
      (fun B => ¬IsThresholdCertificate r G.toWeighted (batchCertificate B)) ≤ ENNReal.ofReal eta := by
  apply (mass_mono _ (fun B hbad hchain => hbad (batchCertificate_of_chain G B hchain))).trans
  exact certificateRun_chain_failure n r eta heta G

theorem certificateRun_certificate_successProb (n r : ℕ) (eta : ℝ) (heta : 0 < eta)
    (G : CapacityGraph (Fin n) 1) :
    1 - eta ≤ (certificateRun n r eta).successProb (productRead G)
      (fun B => IsThresholdCertificate r G.toWeighted (batchCertificate B)) := by
  rw [RTree.successProb_eq]
  exact success_of_failure_le _ _ heta.le (certificateRun_certificate_failure n r eta heta G)

/-- Free finite minimization on the learned certificate, with an empty-shore fallback. -/
def certificateShore (H : WeightedGraph (Fin n)) : Finset (Fin n) :=
  if h : (properShores (Fin n)).Nonempty then (exists_isMinCut H h).choose else ∅

theorem certificateShore_spec (H : WeightedGraph (Fin n)) (hn : 2 ≤ n) :
    IsMinCut H (certificateShore H) ∧ H.cut (certificateShore H) = mincutValue H := by
  have hp : (properShores (Fin n)).Nonempty :=
    ⟨{⟨0, by omega⟩}, (mem_properShores _).mpr
      (properShore_singleton _ (by simpa only [Fintype.card_fin] using hn))⟩
  simpa only [certificateShore, dite_eq_left hp] using (exists_isMinCut H hp).choose_spec

/-- Strictness is essential when transferring a minimizing shore back to the original graph. -/
theorem certificate_minimum_transfer (G H : WeightedGraph (Fin n)) (r : ℕ)
    (hcert : IsThresholdCertificate r G H) (hlt : mincutValue G < r) (hn : 2 ≤ n) :
    H.cut (certificateShore H) < r ∧ IsMinCut G (certificateShore H) ∧
      G.cut (certificateShore H) = mincutValue G := by
  obtain ⟨hmin, hvalue⟩ := certificateShore_spec H hn
  have hv : H.cut (certificateShore H) = mincutValue G := hvalue.trans (hcert.mincut_eq hlt.le)
  have hs : H.cut (certificateShore H) < r := hv ▸ hlt
  have he := hcert.2.2.2 (certificateShore H)
  rw [min_eq_right hs.le] at he
  have hGlt : G.cut (certificateShore H) < r := by
    by_contra h
    rw [min_eq_left (le_of_not_gt h)] at he
    linarith
  rw [min_eq_right hGlt.le] at he
  refine ⟨hs, ⟨hmin.1, ?_⟩, he.symm.trans hv⟩
  intro S hS
  rw [← he, hv]
  exact mincutValue_le G hS

/-- Inspect the finite certificate strictly below the threshold, then query the
original shore once. A malformed or unsuccessful certificate can only affect
which shore is tried; every returned value is independently verified. -/
def certificateCandidate (r : ℕ) (B : ForestBatch n r) : ProductTree n (Candidate n) 1 :=
  if (batchCertificate B).cut (certificateShore (batchCertificate B)) < r then
    verifyCandidate (certificateShore (batchCertificate B))
  else RTree.pure (PMF.pure none)

/-- Both a proper minimum shore and its exact original value are required. -/
def LowMinimumCandidate (G : CapacityGraph (Fin n) 1) (out : Candidate n) : Prop :=
  ∃ S a, out = some (S, a) ∧ IsMinCut G.toWeighted S ∧
    decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted

theorem certificateCandidate_sound (r : ℕ) (B : ForestBatch n r) (G : CapacityGraph (Fin n) 1) :
    ProductTreeSound (certificateCandidate r B) G := by
  intro out hout
  unfold certificateCandidate at hout
  split_ifs at hout with h
  · exact verifyCandidate_sound _ G out hout
  · have he : out = none := by simpa only [RTree.eval_pure, PMF.mem_support_pure_iff] using hout
    subst out
    trivial

theorem certificateCandidate_minimum (r : ℕ) (B : ForestBatch n r)
    (G : CapacityGraph (Fin n) 1) (hn : 2 ≤ n)
    (hlt : mincutValue G.toWeighted < r) (hcert : IsThresholdCertificate r G.toWeighted (batchCertificate B))
    {out : Candidate n} (hout : out ∈ ((certificateCandidate r B).eval (productRead G)).support) :
    LowMinimumCandidate G out := by
  obtain ⟨hstrict, hmin, hvalue⟩ := certificate_minimum_transfer G.toWeighted (batchCertificate B) r hcert hlt hn
  simp only [certificateCandidate, ite_eq_left hstrict, verifyCandidate_eval_honest,
    ite_eq_left hmin.1, PMF.mem_support_pure_iff] at hout
  refine ⟨certificateShore (batchCertificate B), capacityRead G _, hout, hmin,
    decode_capacityRead G _, ?_⟩
  exact (decode_capacityRead G _).trans hvalue

/-- The total public low branch; on fewer than two vertices or zero threshold
it returns none immediately. Otherwise it executes r fresh residual forests. -/
def lowCandidate (n r : ℕ) (eta : ℝ) :
    ProductTree n (Candidate n) (r * forestBudget n (eta / (r : ℝ)) + 1) :=
  if 2 ≤ n ∧ 0 < r then
    (certificateRun n r eta).bind (certificateCandidate r)
  else RTree.pure (PMF.pure none)

theorem lowCandidate_eval (n r : ℕ) (eta : ℝ) (hn : 2 ≤ n) (hr : 0 < r)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (lowCandidate n r eta).eval read =
      ((certificateRun n r eta).eval read).bind fun B => (certificateCandidate r B).eval read := by
  simp only [lowCandidate, hn, hr, and_self, ite_true, RTree.eval_bind]

theorem lowCandidate_run (n r : ℕ) (eta : ℝ) (hn : 2 ≤ n) (hr : 0 < r)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (lowCandidate n r eta) =
      (RTree.run read (certificateRun n r eta)).bind fun forests =>
        (RTree.run read (certificateCandidate r forests.1)).map
          fun verified => (verified.1, forests.2 + verified.2) := by
  simp only [lowCandidate, hn, hr, and_self, ite_true, RTree.run_bind]

@[simp] theorem lowCandidate_run_zero (n : ℕ) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (lowCandidate n 0 eta) = PMF.pure (none, 0) := by
  simp [lowCandidate, PMF.pure_map]

theorem lowCandidate_run_small (n r : ℕ) (eta : ℝ) (hn : n < 2)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (lowCandidate n r eta) = PMF.pure (none, 0) := by
  simp [lowCandidate, Nat.not_le.mpr hn, PMF.pure_map]

theorem lowCandidate_cost (n r : ℕ) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) {out : Candidate n × ℕ}
    (hout : out ∈ (RTree.run read (lowCandidate n r eta)).support) :
    out.2 ≤ r * forestBudget n (eta / (r : ℝ)) + 1 := RTree.cost_le _ read hout

theorem lowCandidate_sound (n r : ℕ) (eta : ℝ) (G : CapacityGraph (Fin n) 1) :
    ProductTreeSound (lowCandidate n r eta) G := by
  intro out hout
  unfold lowCandidate at hout
  split_ifs at hout with h
  · rw [RTree.eval_bind] at hout
    obtain ⟨B, _, hB⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    exact certificateCandidate_sound r B G out hB
  · have he : out = none := by simpa only [RTree.eval_pure, PMF.mem_support_pure_iff] using hout
    subst out
    trivial

theorem lowCandidate_failure (n r : ℕ) (eta : ℝ) (heta : 0 < eta)
    (G : CapacityGraph (Fin n) 1) (hn : 2 ≤ n) (hlt : mincutValue G.toWeighted < r) :
    mass ((lowCandidate n r eta).eval (productRead G)) (fun out => ¬LowMinimumCandidate G out) ≤
      ENNReal.ofReal eta := by
  have hr : 0 < r := by
    have hnonneg := mincutValue_nonneg G.toWeighted
    exact_mod_cast (show (0 : ℝ) < r by linarith)
  rw [lowCandidate_eval n r eta hn hr]
  have h := mass_bind_le_add ((certificateRun n r eta).eval (productRead G))
    (fun B => (certificateCandidate r B).eval (productRead G))
    (fun B => ¬IsThresholdCertificate r G.toWeighted (batchCertificate B))
    (fun out => ¬LowMinimumCandidate G out)
    (certificateRun_certificate_failure n r eta heta G) (ε := 0) (by
      intro B hB
      simpa only [mass_false] using
        (mass_mono_on_support ((certificateCandidate r B).eval (productRead G))
          (P := fun out => ¬LowMinimumCandidate G out) (Q := fun _ => False)
          (fun out hout hbad => hbad
            (certificateCandidate_minimum r B G hn hlt (not_not.mp hB) hout))))
  simpa only [add_zero] using h

theorem lowCandidate_successProb (n r : ℕ) (eta : ℝ) (heta : 0 < eta)
    (G : CapacityGraph (Fin n) 1) (hn : 2 ≤ n) (hlt : mincutValue G.toWeighted < r) :
    1 - eta ≤ (lowCandidate n r eta).successProb (productRead G) (LowMinimumCandidate G) := by
  rw [RTree.successProb_eq]
  exact success_of_failure_le _ _ heta.le (lowCandidate_failure n r eta heta G hn hlt)

/-- A literal public-before-input endpoint for the executed low-cut branch. -/
theorem lowCandidate_public (n r : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ T : ProductTree n (Candidate n) (r * forestBudget n (eta / (r : ℝ)) + 1),
      (∀ read out, out ∈ (RTree.run read T).support →
        out.2 ≤ r * forestBudget n (eta / (r : ℝ)) + 1) ∧
      ∀ G : CapacityGraph (Fin n) 1, ProductTreeSound T G ∧
        (2 ≤ n → mincutValue G.toWeighted < r →
          1 - eta ≤ T.successProb (productRead G) (LowMinimumCandidate G)) := by
  refine ⟨lowCandidate n r eta, fun read _ h => lowCandidate_cost n r eta read h, ?_⟩
  intro G
  exact ⟨lowCandidate_sound n r eta G, fun hn hlt => lowCandidate_successProb n r eta heta G hn hlt⟩

open QuantumQueryComplexity
open scoped Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

/-- The final verification is included in this exact fixed physical schedule. -/
theorem lowCandidate_physical_length (n r : ℕ) (eta : ℝ) :
    (productTreeRoutine (lowCandidate n r eta)).len =
      12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1) := rfl

/-- The implemented circuit remains normalized under every physical answer table. -/
theorem lowCandidate_physical_normalized (n r : ℕ) (eta : ℝ)
    (read : Finset (Fin n) → CutAnswer n 1) :
    IsQState ((productTreeRoutine (lowCandidate n r eta)).run read *ᵥ
      (productTreeAlg (lowCandidate n r eta)).init) := productTreeRoutine_isQState _ read

theorem lowCandidate_physical_prob (n r : ℕ) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (out : Candidate n) :
    (productTreeAlg (lowCandidate n r eta)).prob (capacityRead G)
      (12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1)) out =
      (((lowCandidate n r eta).eval (productRead G)) out).toReal :=
  productTreeAlg_prob _ G out

/-- Exact Born-event transport holds for every output predicate. -/
theorem lowCandidate_physical_event (n r : ℕ) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (Good : Candidate n → Prop) :
    goodProb (productTreeAlg (lowCandidate n r eta)).readout Good
      ((productTreeAlg (lowCandidate n r eta)).state (capacityRead G)
        (12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1))) =
      (mass ((lowCandidate n r eta).eval (productRead G)) Good).toReal := by
  exact (productTreeAlg_successProb (lowCandidate n r eta) G Good).trans
    (RTree.successProb_eq _ _ _)

/-- This is the actual minimum-shore/value probability of the physical circuit. -/
theorem lowCandidate_physical_successProb (n r : ℕ) (eta : ℝ) (heta : 0 < eta)
    (G : CapacityGraph (Fin n) 1) (hn : 2 ≤ n) (hlt : mincutValue G.toWeighted < r) :
    1 - eta ≤ goodProb (productTreeAlg (lowCandidate n r eta)).readout (LowMinimumCandidate G)
      ((productTreeAlg (lowCandidate n r eta)).state (capacityRead G)
        (12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1))) := by
  calc
    _ ≤ (lowCandidate n r eta).successProb (productRead G) (LowMinimumCandidate G) :=
      lowCandidate_successProb n r eta heta G hn hlt
    _ = _ := (productTreeAlg_successProb (lowCandidate n r eta) G (LowMinimumCandidate G)).symm

/-- The accepted analytic estimate now bounds an implemented routine's length. -/
theorem lowCandidate_physical_cost {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hrroot : r ≤ rootThreshold n) {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ((productTreeRoutine (lowCandidate n r eta)).len : ℝ) ≤
      70860 * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 3 *
        ((logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 := by
  rw [lowCandidate_physical_length]
  exact forest_physical_budget_le hn hr hrroot heta heta1

theorem lowCandidate_physical_cost_fixed_tolerance {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hrroot : r ≤ rootThreshold n) :
    ((productTreeRoutine (lowCandidate n r eta)).len : ℝ) ≤
      (70860 * (1 + Real.log (1 / eta)) ^ 2) * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 := by
  rw [lowCandidate_physical_length]
  exact forest_physical_budget_le_fixed_tolerance heta heta1 hn hr hrroot

/-- One public tree witnesses the physical schedule, normalization, soundness
and low-minimum success simultaneously, before quantifying over hidden graphs. -/
theorem lowCandidate_physical_public (n r : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ T : ProductTree n (Candidate n) (r * forestBudget n (eta / (r : ℝ)) + 1),
      (productTreeRoutine T).len = 12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1) ∧
      (∀ read : Finset (Fin n) → CutAnswer n 1,
        IsQState ((productTreeRoutine T).run read *ᵥ (productTreeAlg T).init)) ∧
      ∀ G : CapacityGraph (Fin n) 1, ProductTreeSound T G ∧
        (2 ≤ n → mincutValue G.toWeighted < r →
          1 - eta ≤ goodProb (productTreeAlg T).readout (LowMinimumCandidate G)
            ((productTreeAlg T).state (capacityRead G)
              (12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1)))) := by
  refine ⟨lowCandidate n r eta, lowCandidate_physical_length n r eta,
    lowCandidate_physical_normalized n r eta, ?_⟩
  intro G
  exact ⟨lowCandidate_sound n r eta G,
    fun hn hlt => lowCandidate_physical_successProb n r eta heta G hn hlt⟩

#print axioms collectForests_eval_succ
#print axioms collectForests_run_succ
#print axioms collectForests_cost
#print axioms knownSubgraph_union
#print axioms residualGraph_union
#print axioms collectForests_sound
#print axioms collectForests_chain_failure
#print axioms batchCertificate_of_chain
#print axioms certificateRun_sound
#print axioms certificateRun_chain_failure
#print axioms certificateRun_chain_successProb
#print axioms certificateRun_certificate_failure
#print axioms certificateRun_certificate_successProb
#print axioms certificate_minimum_transfer
#print axioms certificateCandidate_sound
#print axioms certificateCandidate_minimum
#print axioms lowCandidate_eval
#print axioms lowCandidate_run
#print axioms lowCandidate_run_zero
#print axioms lowCandidate_run_small
#print axioms lowCandidate_cost
#print axioms lowCandidate_sound
#print axioms lowCandidate_failure
#print axioms lowCandidate_successProb
#print axioms lowCandidate_public
#print axioms lowCandidate_physical_length
#print axioms lowCandidate_physical_normalized
#print axioms lowCandidate_physical_prob
#print axioms lowCandidate_physical_event
#print axioms lowCandidate_physical_successProb
#print axioms lowCandidate_physical_cost
#print axioms lowCandidate_physical_cost_fixed_tolerance
#print axioms lowCandidate_physical_public

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
