import CutQueryComplexity.StarContraction2022.Certificates.Parallel.Queries
import CutQueryComplexity.StarContraction2022.Certificates.ParallelProgress
import CutQueryComplexity.StarContraction2022.Common.Constants

/-! # Actual representative scans and finite finishing of existing forests

Part of the parallel threshold certificate. No full parallel algorithm,
expected C_P bound, or endpoint is asserted in this module.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical ENNReal

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
variable {π : PublicQuotient V Q} {r : ℕ}

namespace ParallelState

/-- The finishing search keeps original endpoints and uses the public binary
search depth of the original graph. It is not a quotient-capacity oracle. -/
def residualNeighbor (s : ParallelState π r) (hr : 0 < r) (v : V) :
    DTree (Finset V) ℝ (Option V) ((searchDepth V + 1) * 3) :=
  ((findNeighbor (searchDepth V) v (s.lastBlock hr v)ᶜ).substitute
    s.residualQuery).cast (Nat.mul_one _)

theorem residualNeighbor_eval (s : ParallelState π r) (hr : 0 < r) (v : V)
    (G : WeightedGraph V) (hs : s.usedGraph.IsSubgraph G) :
    (s.residualNeighbor hr v).eval G.cut =
      (findNeighbor (searchDepth V) v (s.lastBlock hr v)ᶜ).eval
        (G.subtract s.usedGraph).cut := by
  rw [residualNeighbor, DTree.eval_cast, DTree.eval_substitute]
  congr 1
  exact funext (s.residualQuery_eval G hs)

theorem residualNeighbor_positive (s : ParallelState π r) (hr : 0 < r) (v : V)
    (G : WeightedGraph V) (hs : s.usedGraph.IsSubgraph G)
    (hp : 0 < (G.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ) :
    ∃ w, (s.residualNeighbor hr v).eval G.cut = some w ∧
      w ∉ s.lastBlock hr v ∧ 0 < (G.subtract s.usedGraph).w v w := by
  let H := G.subtract s.usedGraph
  have hfind := findNeighbor_correct H (searchDepth V) v (s.lastBlock hr v)ᶜ
    (Nat.le_pow_clog (by decide) _)
  rw [← s.residualNeighbor_eval hr v G hs] at hfind
  cases he : (s.residualNeighbor hr v).eval G.cut with
  | none =>
      simp only [he, PositiveResult] at hfind
      have hz : H.cross {v} (s.lastBlock hr v)ᶜ = 0 := by
        simp only [WeightedGraph.cross, Finset.sum_singleton]
        apply Finset.sum_eq_zero
        intro w hw
        have hh := hfind w (Finset.mem_univ w)
        simpa only [restrictWeight, hw, ite_true] using hh
      exact False.elim (by change 0 < H.cross {v} (s.lastBlock hr v)ᶜ at hp; linarith)
  | some w =>
      simp only [he, PositiveResult] at hfind
      obtain ⟨hw, hpw⟩ := (restrictWeight_pos _ _ _).mp hfind.2
      exact ⟨w, rfl, Finset.mem_compl.mp hw, hpw⟩

/-- Turn the returned original neighbor into an actual least-layer update.
Both the quotient inequality and layer availability are tested publicly. -/
def advanceVertex (s : ParallelState π r) (hr : 0 < r) (v : V) :
    DTree (Finset V) ℝ (Option (ParallelState π r)) ((searchDepth V + 1) * 3) :=
  (s.residualNeighbor hr v).map fun ow => match ow with
    | none => none
    | some w => if h : π.map v ≠ π.map w then s.insertFirst ⟨(v, w), h⟩ else none

theorem advanceVertex_inactive (s : ParallelState π r) (hr : 0 < r) (v : V)
    (read : Finset V → ℝ) {t : ParallelState π r}
    (ht : (s.advanceVertex hr v).eval read = some t) : t.inactive = s.inactive := by
  rw [advanceVertex, DTree.eval_map] at ht
  cases he : (s.residualNeighbor hr v).eval read with
  | none => simp only [he] at ht; cases ht
  | some w =>
      simp only [he] at ht
      split at ht
      next h => exact s.insertFirst_inactive _ ht
      next h => cases ht

theorem advanceVertex_honest (s : ParallelState π r) (hr : 0 < r) (v : V)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hl : s.Laminar) (hi : s.InactiveSound hr G.toWeighted)
    (hp : 0 < (G.toWeighted.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ) :
    ∃ t, (s.advanceVertex hr v).eval G.toWeighted.cut = some t ∧
      t.usedGraph.IsSubgraph G.toWeighted ∧ t.Laminar ∧
      t.InactiveSound hr G.toWeighted ∧ t.inactive = s.inactive ∧
      t.failed = s.failed ∧
      t.livePotential + 1 ≤ s.livePotential := by
  obtain ⟨w, hw, hout, hpw⟩ := s.residualNeighbor_positive hr v G.toWeighted hs hp
  have hn : ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map v) (π.map w) :=
    fun h => hout ((s.mem_lastBlock hr v w).mpr h)
  have hneq : π.map v ≠ π.map w := by
    intro he
    apply hn
    rw [he]
  let e : OriginalEdge π := ⟨(v, w), hneq⟩
  obtain ⟨t, ht⟩ := s.insertFirst_exists e (lastIndex hr) hn
  have hact := s.positive_endpoints_active hr G.toWeighted hi hn hpw
  refine ⟨t, ?_, s.insertFirst_honest e ht G hs hpw,
    s.insertFirst_laminar hl e ht, s.insertFirst_inactiveSound e ht hr G.toWeighted hi,
    s.insertFirst_inactive e ht, s.insertFirst_failed e ht,
    s.insertFirst_livePotential e ht hact.1 hact.2⟩
  simp only [advanceVertex, DTree.eval_map, hw, dif_pos hneq]
  exact ht

/-- Query the original vertex against the complement of its finest component.
The three original cuts are made before validating the derived row count. -/
def vertexProbe (s : ParallelState π r) (hr : 0 < r) (v : V) :
    DTree (Finset V) ℝ (Option (Fin (Fintype.card V + 1))) 3 :=
  (s.residualCrossQuery {v} (s.lastBlock hr v)ᶜ).map (validateCount (Fintype.card V))

theorem vertexProbe_eval (s : ParallelState π r) (hr : 0 < r) (v : V)
    (G : WeightedGraph V) (hs : s.usedGraph.IsSubgraph G) :
    (s.vertexProbe hr v).eval G.cut = validateCount (Fintype.card V)
      ((G.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ) := by
  rw [vertexProbe, DTree.eval_map, s.residualCrossQuery_eval G hs]
  apply Finset.disjoint_left.mpr
  intro u hu hw
  have huv : u = v := Finset.mem_singleton.mp hu
  subst u
  exact (Finset.mem_compl.mp hw) (s.self_mem_lastBlock hr v)

theorem vertexProbe_honest (s : ParallelState π r) (hr : 0 < r) (v : V)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    ∃ k : Fin (Fintype.card V + 1),
      (s.vertexProbe hr v).eval G.toWeighted.cut = some k ∧
      (G.toWeighted.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ = (k : ℕ) := by
  obtain ⟨k, hk, he⟩ := s.residual_row_count G hs v (s.lastBlock hr v)ᶜ
  refine ⟨⟨k, Nat.lt_succ_of_le hk⟩, ?_, he⟩
  rw [s.vertexProbe_eval hr v G.toWeighted hs, he]
  exact validateCount_of_nat _ _ hk

theorem vertexProbe_zero (s : ParallelState π r) (hr : 0 < r) (v : V)
    (G : WeightedGraph V) (hs : s.usedGraph.IsSubgraph G)
    (hz : (s.vertexProbe hr v).eval G.cut = some 0) :
    (G.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ = 0 := by
  rw [s.vertexProbe_eval hr v G hs] at hz
  simpa using (validateCount_spec hz).1.symm

theorem vertexProbe_positive (s : ParallelState π r) (hr : 0 < r) (v : V)
    (G : WeightedGraph V) (hs : s.usedGraph.IsSubgraph G)
    {k : Fin (Fintype.card V + 1)} (hk : 0 < k.val)
    (he : (s.vertexProbe hr v).eval G.cut = some k) :
    ∃ w, w ∉ s.lastBlock hr v ∧ 0 < (G.subtract s.usedGraph).w v w := by
  rw [s.vertexProbe_eval hr v G hs] at he
  have hp : 0 < (G.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ := by
    rw [← (validateCount_spec he).1]
    exact_mod_cast hk
  obtain ⟨u, hu, w, hw, hpw⟩ := ((G.subtract s.usedGraph).cross_pos_iff _ _).mp hp
  have huv := Finset.mem_singleton.mp hu
  subst u
  exact ⟨w, Finset.mem_compl.mp hw, hpw⟩

structure ScanOutput (π : PublicQuotient V Q) (r : ℕ) where
  state : ParallelState π r
  representative : Option V

/-- A finite public scan. Zero rows are permanently retired; the first positive
row is the representative. Invalid answers terminate with failure. -/
def scanVertices (s : ParallelState π r) (hr : 0 < r) :
    (vs : List V) → DTree (Finset V) ℝ (ScanOutput π r) (3 * vs.length)
  | [] => DTree.pure ⟨s, none⟩
  | v :: vs =>
      ((s.vertexProbe hr v).bind fun answer => match answer with
        | none => DTree.pure ⟨{ s with failed := true }, none⟩
        | some k => if k.val = 0 then (s.retire v).scanVertices hr vs
            else DTree.pure ⟨s, some v⟩).cast (by simp only [List.length_cons]; omega)

theorem scanVertices_budget (s : ParallelState π r) (hr : 0 < r) (vs : List V)
    (read : Finset V → ℝ) : (s.scanVertices hr vs).cost read ≤ 3 * vs.length :=
  DTree.cost_le _ _

theorem scanVertices_forests (s : ParallelState π r) (hr : 0 < r) (vs : List V)
    (read : Finset V → ℝ) :
    ((s.scanVertices hr vs).eval read).state.forests = s.forests := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
      rw [scanVertices, DTree.eval_cast, DTree.eval_bind]
      cases he : (s.vertexProbe hr v).eval read with
      | none => simp only [DTree.eval_pure]
      | some k =>
          by_cases hk : k.val = 0
          · simp only [hk, ite_true]
            exact (ih (s.retire v)).trans rfl
          · simp only [hk, ite_false, DTree.eval_pure]

theorem scanVertices_inactive_mono (s : ParallelState π r) (hr : 0 < r) (vs : List V)
    (read : Finset V → ℝ) :
    s.inactive ⊆ ((s.scanVertices hr vs).eval read).state.inactive := by
  induction vs generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons v vs ih =>
      rw [scanVertices, DTree.eval_cast, DTree.eval_bind]
      cases he : (s.vertexProbe hr v).eval read with
      | none => simpa only [DTree.eval_pure] using (Finset.Subset.refl s.inactive)
      | some k =>
          by_cases hk : k.val = 0
          · simp only [hk, ite_true]
            exact (s.retire_mono v).trans (ih (s.retire v))
          · simp only [hk, ite_false, DTree.eval_pure]
            exact Finset.Subset.refl _

/-- All-answer charging: every zero-row query retires a new original vertex,
and the scan makes at most one further probe. No hidden-graph premise occurs. -/
theorem scanVertices_cost_charge (s : ParallelState π r) (hr : 0 < r) (vs : List V)
    (read : Finset V → ℝ) (hnodup : vs.Nodup)
    (hnew : ∀ v ∈ vs, v ∉ s.inactive) :
    (s.scanVertices hr vs).cost read ≤
      3 * (((s.scanVertices hr vs).eval read).state.inactive.card - s.inactive.card + 1) := by
  induction vs generalizing s with
  | nil => simp only [scanVertices, det_cost_pure, DTree.eval_pure, Nat.sub_self]; omega
  | cons v vs ih =>
      obtain ⟨hvnot, htail⟩ := List.nodup_cons.mp hnodup
      have hvnew := hnew v (by simp)
      have hprobe := DTree.cost_le (s.vertexProbe hr v) read
      simp only [scanVertices, det_cost_cast, det_cost_bind, DTree.eval_cast, DTree.eval_bind]
      cases he : (s.vertexProbe hr v).eval read with
      | none => simpa only [det_cost_pure, DTree.eval_pure, add_zero, Nat.sub_self] using hprobe
      | some k =>
          by_cases hk : k.val = 0
          · simp only [hk, ite_true]
            have htailnew : ∀ u ∈ vs, u ∉ (s.retire v).inactive := by
              intro u hu hui
              rcases Finset.mem_insert.mp hui with huv | hui
              · exact hvnot (huv ▸ hu)
              · exact hnew u (by simp [hu]) hui
            have hh := ih (s.retire v) htail htailnew
            have hcard := Finset.card_mono ((s.retire v).scanVertices_inactive_mono hr vs read)
            rw [s.retire_charge hvnew] at hh hcard
            omega
          · simpa only [hk, ite_false, det_cost_pure, DTree.eval_pure, add_zero,
              Nat.sub_self] using hprobe

theorem scanVertices_inactiveSound (s : ParallelState π r) (hr : 0 < r) (vs : List V)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) :
    ((s.scanVertices hr vs).eval G.toWeighted.cut).state.InactiveSound hr G.toWeighted := by
  induction vs generalizing s with
  | nil => exact hi
  | cons v vs ih =>
      obtain ⟨k, hk, hcount⟩ := s.vertexProbe_honest hr v G hs
      rw [scanVertices, DTree.eval_cast, DTree.eval_bind, hk]
      by_cases hz : k.val = 0
      · simp only [hz, ite_true]
        have hzero : (s.vertexProbe hr v).eval G.toWeighted.cut = some 0 := by
          simpa only [show k = 0 from Fin.ext hz] using hk
        have hsafe := s.retire_sound hr G.toWeighted hi v
          (s.vertexProbe_zero hr v G.toWeighted hs hzero)
        exact ih (s.retire v) hs hsafe
      · simp only [hz, ite_false, DTree.eval_pure]
        exact hi

/-- The scan's actual stopping condition: either all scanned vertices have
been retired, or its public output is an honestly positive representative. -/
def ScanResult (s : ParallelState π r) (hr : 0 < r) (vs : List V)
    (G : WeightedGraph V) (out : ScanOutput π r) : Prop :=
  out.state.forests = s.forests ∧ out.state.failed = s.failed ∧
    match out.representative with
    | none => ∀ v ∈ vs, v ∈ out.state.inactive
    | some v => v ∈ vs ∧ 0 < (G.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ

theorem scanVertices_result (s : ParallelState π r) (hr : 0 < r) (vs : List V)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    s.ScanResult hr vs G.toWeighted ((s.scanVertices hr vs).eval G.toWeighted.cut) := by
  induction vs generalizing s with
  | nil => simp [ScanResult, scanVertices]
  | cons v vs ih =>
      obtain ⟨k, hk, hcount⟩ := s.vertexProbe_honest hr v G hs
      rw [scanVertices, DTree.eval_cast, DTree.eval_bind, hk]
      by_cases hz : k.val = 0
      · simp only [hz, ite_true]
        obtain ⟨hf, hfail, hspec⟩ := ih (s.retire v) hs
        refine ⟨hf, hfail, ?_⟩
        cases hout : (((s.retire v).scanVertices hr vs).eval G.toWeighted.cut).representative with
        | none =>
            simp only [hout] at hspec ⊢
            intro u hu
            rcases List.mem_cons.mp hu with huv | hu
            · subst u
              apply (s.retire v).scanVertices_inactive_mono hr vs G.toWeighted.cut
              exact Finset.mem_insert_self _ _
            · exact hspec u hu
        | some u =>
            simp only [hout] at hspec ⊢
            exact ⟨List.mem_cons_of_mem v hspec.1, hspec.2⟩
      · simp only [hz, ite_false, DTree.eval_pure]
        refine ⟨rfl, rfl, by simp, ?_⟩
        rw [hcount]
        exact_mod_cast (Nat.pos_of_ne_zero hz)

/-- An exhausted scan of precisely the unretired original vertices closes
the actual certificate. This is a checked stopping predicate, not a promise
that a forest or cut certificate was returned by an oracle. -/
theorem scanVertices_none_certificate (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hl : s.Laminar) (hi : s.InactiveSound hr G.toWeighted)
    (hnone : ((s.scanVertices hr (Finset.univ \ s.inactive).toList).eval
      G.toWeighted.cut).representative = none) :
    let out := (s.scanVertices hr (Finset.univ \ s.inactive).toList).eval G.toWeighted.cut
    IsThresholdCertificate r (π.graph G.toWeighted) out.state.quotientGraph := by
  let vs := (Finset.univ \ s.inactive).toList
  let out := (s.scanVertices hr vs).eval G.toWeighted.cut
  have hspec := s.scanVertices_result hr vs G hs
  obtain ⟨hf, hfail, hdone⟩ := hspec
  change out.state.forests = s.forests at hf
  change (match out.representative with
    | none => ∀ v ∈ vs, v ∈ out.state.inactive
    | some v => v ∈ vs ∧
        0 < (G.toWeighted.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ) at hdone
  have hnone' : out.representative = none := hnone
  have hdone' : ∀ v ∈ vs, v ∈ out.state.inactive := by
    simpa only [hnone'] using hdone
  have hall : out.state.inactive = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    by_cases hv : v ∈ s.inactive
    · exact s.scanVertices_inactive_mono hr vs G.toWeighted.cut hv
    · have hvmem : v ∈ vs := by simp [vs, hv]
      exact hdone' v hvmem
  apply out.state.certificate_of_retired hr G.toWeighted G.integral_toWeighted
  · simpa only [usedGraph, hf] using hs
  · simpa only [Laminar, hf] using hl
  · exact s.scanVertices_inactiveSound hr vs G hs hi
  · exact hall

theorem scanVertices_livePotential (s : ParallelState π r) (hr : 0 < r) (vs : List V)
    (read : Finset V → ℝ) :
    ((s.scanVertices hr vs).eval read).state.livePotential ≤ s.livePotential := by
  apply Finset.sum_le_sum
  intro i hi
  apply s.liveBlocks_card_mono_of _ i (s.scanVertices_inactive_mono hr vs read)
  intro u v huv
  simpa only [s.scanVertices_forests hr vs read] using huv

def activeScan (s : ParallelState π r) (hr : 0 < r) :
    DTree (Finset V) ℝ (ScanOutput π r) (3 * Fintype.card V) :=
  (s.scanVertices hr (Finset.univ \ s.inactive).toList).weaken
    (Nat.mul_le_mul_left 3 (by simpa using Finset.card_le_univ (Finset.univ \ s.inactive)))

theorem activeScan_eval (s : ParallelState π r) (hr : 0 < r) (read : Finset V → ℝ) :
    (s.activeScan hr).eval read =
      (s.scanVertices hr (Finset.univ \ s.inactive).toList).eval read := by
  simp only [activeScan, DTree.eval, DTree.run_weaken]

theorem activeScan_cost_charge (s : ParallelState π r) (hr : 0 < r)
    (read : Finset V → ℝ) :
    (s.activeScan hr).cost read ≤
      3 * (((s.activeScan hr).eval read).state.inactive.card - s.inactive.card + 1) := by
  rw [activeScan_eval]
  have he : (s.activeScan hr).cost read =
      (s.scanVertices hr (Finset.univ \ s.inactive).toList).cost read := by
    simp only [activeScan, DTree.cost, DTree.run_weaken]
  rw [he]
  apply s.scanVertices_cost_charge hr _ read (Finset.nodup_toList _)
  intro v hv
  exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).2

/-- Scan only the as-yet-unretired vertices of a public component. -/
def blockScan (s : ParallelState π r) (hr : 0 < r) (B : Finset V) :
    DTree (Finset V) ℝ (ScanOutput π r) (3 * Fintype.card V) :=
  (s.scanVertices hr (B \ s.inactive).toList).weaken
    (Nat.mul_le_mul_left 3 (by simpa using Finset.card_le_univ (B \ s.inactive)))

theorem blockScan_eval (s : ParallelState π r) (hr : 0 < r) (B : Finset V)
    (read : Finset V → ℝ) :
    (s.blockScan hr B).eval read = (s.scanVertices hr (B \ s.inactive).toList).eval read := by
  simp only [blockScan, DTree.eval, DTree.run_weaken]

theorem blockScan_forests (s : ParallelState π r) (hr : 0 < r) (B : Finset V)
    (read : Finset V → ℝ) : ((s.blockScan hr B).eval read).state.forests = s.forests := by
  rw [blockScan_eval]
  exact s.scanVertices_forests hr _ read

theorem blockScan_inactive (s : ParallelState π r) (hr : 0 < r) (B : Finset V)
    (read : Finset V → ℝ) : s.inactive ⊆ ((s.blockScan hr B).eval read).state.inactive := by
  rw [blockScan_eval]
  exact s.scanVertices_inactive_mono hr _ read

theorem blockScan_cost_charge (s : ParallelState π r) (hr : 0 < r) (B : Finset V)
    (read : Finset V → ℝ) :
    (s.blockScan hr B).cost read ≤
      3 * (((s.blockScan hr B).eval read).state.inactive.card - s.inactive.card + 1) := by
  rw [blockScan_eval]
  have he : (s.blockScan hr B).cost read =
      (s.scanVertices hr (B \ s.inactive).toList).cost read := by
    simp only [blockScan, DTree.cost, DTree.run_weaken]
  rw [he]
  apply s.scanVertices_cost_charge hr _ read (Finset.nodup_toList _)
  intro v hv
  exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).2

structure RepresentativeScan (π : PublicQuotient V Q) (r : ℕ) where
  state : ParallelState π r
  selected : List (Finset V × V)

def selectedHead (B : Finset V) : Option V → List (Finset V × V)
  | none => []
  | some v => [(B, v)]

/-- Every public component is visited, retaining at most one honestly positive
original representative. Zero rows are retired across the whole scan. -/
def scanBlocks (s : ParallelState π r) (hr : 0 < r) :
    (Bs : List (Finset V)) →
      DTree (Finset V) ℝ (RepresentativeScan π r) (3 * Fintype.card V * Bs.length)
  | [] => DTree.pure ⟨s, []⟩
  | B :: Bs => ((s.blockScan hr B).bind fun out =>
      (out.state.scanBlocks hr Bs).map fun tail =>
        ⟨tail.state, selectedHead B out.representative ++ tail.selected⟩).cast
          (by simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; omega)

theorem scanBlocks_forests (s : ParallelState π r) (hr : 0 < r) (Bs : List (Finset V))
    (read : Finset V → ℝ) : ((s.scanBlocks hr Bs).eval read).state.forests = s.forests := by
  induction Bs generalizing s with
  | nil => rfl
  | cons B Bs ih =>
      rw [scanBlocks, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      exact (ih _).trans (s.blockScan_forests hr B read)

theorem scanBlocks_inactive (s : ParallelState π r) (hr : 0 < r) (Bs : List (Finset V))
    (read : Finset V → ℝ) : s.inactive ⊆ ((s.scanBlocks hr Bs).eval read).state.inactive := by
  induction Bs generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons B Bs ih =>
      rw [scanBlocks, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      exact (s.blockScan_inactive hr B read).trans (ih _)

/-- This telescoping charge is independent of repeated component scans: a
vertex is charged only on its first retirement, and each component costs at
most one further positive probe. -/
theorem scanBlocks_cost_charge (s : ParallelState π r) (hr : 0 < r)
    (Bs : List (Finset V)) (read : Finset V → ℝ) :
    (s.scanBlocks hr Bs).cost read ≤
      3 * (((s.scanBlocks hr Bs).eval read).state.inactive.card - s.inactive.card + Bs.length) := by
  induction Bs generalizing s with
  | nil => simp [scanBlocks, DTree.cost, DTree.eval, DTree.run_pure]
  | cons B Bs ih =>
      let out := (s.blockScan hr B).eval read
      have hhead := s.blockScan_cost_charge hr B read
      have htail := ih out.state
      have hcard1 : s.inactive.card ≤ out.state.inactive.card :=
        Finset.card_mono (s.blockScan_inactive hr B read)
      have hcard2 : out.state.inactive.card ≤
          ((out.state.scanBlocks hr Bs).eval read).state.inactive.card :=
        Finset.card_mono (out.state.scanBlocks_inactive hr Bs read)
      rw [scanBlocks, det_cost_cast, det_cost_bind, DTree.eval_cast, DTree.eval_bind,
        DTree.eval_map, det_cost_map, List.length_cons]
      change (s.blockScan hr B).cost read + (out.state.scanBlocks hr Bs).cost read ≤
        3 * (((out.state.scanBlocks hr Bs).eval read).state.inactive.card -
          s.inactive.card + (Bs.length + 1))
      change (s.blockScan hr B).cost read ≤
        3 * (out.state.inactive.card - s.inactive.card + 1) at hhead
      omega

theorem scanBlocks_inactiveSound (s : ParallelState π r) (hr : 0 < r)
    (Bs : List (Finset V)) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) :
    ((s.scanBlocks hr Bs).eval G.toWeighted.cut).state.InactiveSound hr G.toWeighted := by
  induction Bs generalizing s with
  | nil => exact hi
  | cons B Bs ih =>
      let out := (s.blockScan hr B).eval G.toWeighted.cut
      have hf : out.state.forests = s.forests := s.blockScan_forests hr B G.toWeighted.cut
      have hout : out.state.InactiveSound hr G.toWeighted := by
        rw [show out = (s.scanVertices hr (B \ s.inactive).toList).eval G.toWeighted.cut
          from s.blockScan_eval hr B G.toWeighted.cut]
        exact s.scanVertices_inactiveSound hr _ G hs hi
      rw [scanBlocks, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      exact ih out.state (by simpa only [usedGraph, hf] using hs) hout

/-- The selected labels preserve their public order and occur at most once
whenever the input components are distinct. This is true on every oracle. -/
theorem scanBlocks_labels_sublist (s : ParallelState π r) (hr : 0 < r)
    (Bs : List (Finset V)) (read : Finset V → ℝ) :
    (((s.scanBlocks hr Bs).eval read).selected.map Prod.fst).Sublist Bs := by
  induction Bs generalizing s with
  | nil => exact .refl _
  | cons B Bs ih =>
      rw [scanBlocks, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      cases ho : ((s.blockScan hr B).eval read).representative with
      | none => simpa only [ho, selectedHead, List.nil_append] using (ih _).cons B
      | some v =>
          simpa only [ho, selectedHead, List.cons_append, List.nil_append,
            List.map_cons] using (ih _).cons₂ B

/-- Honest scans cover every component by a positive selected vertex, or
retire every original vertex in that component. The positivity is relative
to the same unchanged original residual throughout the scan. -/
def RepresentativesGood (s : ParallelState π r) (hr : 0 < r) (Bs : List (Finset V))
    (G : WeightedGraph V) (out : RepresentativeScan π r) : Prop :=
  out.state.failed = s.failed ∧
  (∀ p ∈ out.selected, p.1 ∈ Bs ∧ p.2 ∈ p.1 ∧
    0 < (G.subtract s.usedGraph).cross {p.2} (s.lastBlock hr p.2)ᶜ) ∧
  (∀ B ∈ Bs, (∀ v ∈ B, v ∈ out.state.inactive) ∨ ∃ v, (B, v) ∈ out.selected)

theorem scanBlocks_good (s : ParallelState π r) (hr : 0 < r) (Bs : List (Finset V))
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    s.RepresentativesGood hr Bs G.toWeighted ((s.scanBlocks hr Bs).eval G.toWeighted.cut) := by
  induction Bs generalizing s with
  | nil => simp [RepresentativesGood, scanBlocks]
  | cons B Bs ih =>
      let head := (s.blockScan hr B).eval G.toWeighted.cut
      let tail := (head.state.scanBlocks hr Bs).eval G.toWeighted.cut
      have hf : head.state.forests = s.forests := s.blockScan_forests hr B G.toWeighted.cut
      have hhead : s.ScanResult hr (B \ s.inactive).toList G.toWeighted head := by
        rw [show head = (s.scanVertices hr (B \ s.inactive).toList).eval G.toWeighted.cut
          from s.blockScan_eval hr B G.toWeighted.cut]
        exact s.scanVertices_result hr _ G hs
      obtain ⟨_, hfail, hspec⟩ := hhead
      have htail := ih head.state (by simpa only [usedGraph, hf] using hs)
      change head.state.RepresentativesGood hr Bs G.toWeighted tail at htail
      obtain ⟨htfail, htpositive, htcover⟩ := htail
      have htailmono : head.state.inactive ⊆ tail.state.inactive :=
        head.state.scanBlocks_inactive hr Bs G.toWeighted.cut
      rw [scanBlocks, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      change s.RepresentativesGood hr (B :: Bs) G.toWeighted
        ⟨tail.state, selectedHead B head.representative ++ tail.selected⟩
      refine ⟨htfail.trans hfail, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hfirst | hrest
        · cases ho : head.representative with
          | none => simp [ho, selectedHead] at hfirst
          | some v =>
              have hpv : p = (B, v) := by simpa [ho, selectedHead] using hfirst
              subst p
              have hv := hspec
              simp only [ho] at hv
              exact ⟨by simp, (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv.1)).1, hv.2⟩
        · obtain ⟨hB, hv, hpos⟩ := htpositive p hrest
          refine ⟨List.mem_cons_of_mem _ hB, hv, ?_⟩
          simpa only [usedGraph, lastBlock, hf] using hpos
      · intro A hA
        rcases List.mem_cons.mp hA with rfl | hA
        · cases ho : head.representative with
          | none =>
              left
              have hz := hspec
              simp only [ho] at hz
              intro v hv
              apply htailmono
              by_cases hi : v ∈ s.inactive
              · exact s.blockScan_inactive hr A G.toWeighted.cut hi
              · exact hz v (by simp [hv, hi])
          | some v =>
              right
              exact ⟨v, List.mem_append.mpr (Or.inl (by simp [selectedHead, ho]))⟩
        · rcases htcover A hA with hall | hex
          · exact Or.inl hall
          · obtain ⟨v, hv⟩ := hex
            exact Or.inr ⟨v, List.mem_append.mpr (Or.inr hv)⟩

/-- The actual next-round representative scan uses only the current public
finest live components. Its finite index is a ceiling, not an asserted cost. -/
def representativeScan (s : ParallelState π r) (hr : 0 < r) :
    DTree (Finset V) ℝ (RepresentativeScan π r)
      (3 * Fintype.card V * (s.liveBlocks (lastIndex hr)).card) :=
  (s.scanBlocks hr (s.liveBlocks (lastIndex hr)).toList).cast (by simp)

theorem representativeScan_cost_charge (s : ParallelState π r) (hr : 0 < r)
    (read : Finset V → ℝ) :
    (s.representativeScan hr).cost read ≤
      3 * (((s.representativeScan hr).eval read).state.inactive.card - s.inactive.card +
        (s.liveBlocks (lastIndex hr)).card) := by
  simpa only [representativeScan, det_cost_cast, DTree.eval_cast, Finset.length_toList] using
    s.scanBlocks_cost_charge hr (s.liveBlocks (lastIndex hr)).toList read

theorem representativeScan_good (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    s.RepresentativesGood hr (s.liveBlocks (lastIndex hr)).toList G.toWeighted
      ((s.representativeScan hr).eval G.toWeighted.cut) := by
  simpa only [representativeScan, DTree.eval_cast] using
    s.scanBlocks_good hr (s.liveBlocks (lastIndex hr)).toList G hs

/-- Every remaining live block has a selected vertex, so the quarter-progress
experiment uses at least as many representatives as surviving live blocks. -/
theorem representativeScan_covers_live (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    let out := (s.representativeScan hr).eval G.toWeighted.cut
    (out.state.liveBlocks (lastIndex hr)).card ≤ out.selected.length := by
  let out := (s.representativeScan hr).eval G.toWeighted.cut
  let labels := out.selected.toFinset.image Prod.fst
  have hf : out.state.forests = s.forests := by
    dsimp only [out]
    rw [representativeScan, DTree.eval_cast]
    exact s.scanBlocks_forests hr (s.liveBlocks (lastIndex hr)).toList G.toWeighted.cut
  have hi : s.inactive ⊆ out.state.inactive := by
    dsimp only [out]
    rw [representativeScan, DTree.eval_cast]
    exact s.scanBlocks_inactive hr (s.liveBlocks (lastIndex hr)).toList G.toWeighted.cut
  have hg := s.representativeScan_good hr G hs
  change s.RepresentativesGood hr (s.liveBlocks (lastIndex hr)).toList G.toWeighted out at hg
  have hsub : out.state.liveBlocks (lastIndex hr) ⊆ labels := by
    intro B hB
    obtain ⟨hblock, v, hv, hactive⟩ := Finset.mem_filter.mp hB
    have hold : B ∈ s.liveBlocks (lastIndex hr) := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, v, hv, fun h => hactive (hi h)⟩
      simpa only [blocks, hf] using hblock
    rcases hg.2.2 B (Finset.mem_toList.mpr hold) with hall | hex
    · exact False.elim (hactive (hall v hv))
    · obtain ⟨u, hu⟩ := hex
      exact Finset.mem_image.mpr ⟨(B, u), List.mem_toFinset.mpr hu, rfl⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le).trans (List.toFinset_card_le _))

theorem representativeScan_distinct_labels (s : ParallelState π r) (hr : 0 < r)
    (read : Finset V → ℝ) :
    (((s.representativeScan hr).eval read).selected.map Prod.fst).Nodup := by
  have hsub := s.scanBlocks_labels_sublist hr (s.liveBlocks (lastIndex hr)).toList read
  have hn := (Finset.nodup_toList (s.liveBlocks (lastIndex hr))).sublist hsub
  simpa only [representativeScan, DTree.eval_cast] using hn

theorem representativeScan_separated (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    {a b : Finset V × V}
    (ha : a ∈ ((s.representativeScan hr).eval G.toWeighted.cut).selected)
    (hb : b ∈ ((s.representativeScan hr).eval G.toWeighted.cut).selected)
    (hne : a.1 ≠ b.1) :
    ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map a.2) (π.map b.2) := by
  have hg := s.representativeScan_good hr G hs
  obtain ⟨hA, hvA, _⟩ := hg.2.1 a ha
  obtain ⟨hB, hvB, _⟩ := hg.2.1 b hb
  have hblocksA := (Finset.mem_filter.mp (Finset.mem_toList.mp hA)).1
  have hblocksB := (Finset.mem_filter.mp (Finset.mem_toList.mp hB)).1
  intro hreach
  have he := s.block_eq_of_reachable (lastIndex hr) hreach
  rw [s.block_eq_of_mem (lastIndex hr) hblocksA hvA,
    s.block_eq_of_mem (lastIndex hr) hblocksB hvB] at he
  exact hne he

inductive FinishOutput (π : PublicQuotient V Q) (r : ℕ)
  | done (state : ParallelState π r)
  | advance (state : ParallelState π r)
  | failed

def finishStepBudget (V : Type) [Fintype V] : ℕ :=
  3 * Fintype.card V + (searchDepth V + 1) * 3

/-- One finite finishing step: retire zero rows, then find and insert one
positive original edge, or recognize exhaustion of every active vertex. -/
def finishStep (s : ParallelState π r) (hr : 0 < r) :
    DTree (Finset V) ℝ (FinishOutput π r) (finishStepBudget V) :=
  (s.activeScan hr).bind fun out =>
    if out.state.failed then DTree.pure .failed else
    match out.representative with
    | none => DTree.pure (.done out.state)
    | some v => (out.state.advanceVertex hr v).map fun next =>
        match next with
        | none => .failed
        | some t => .advance t

def FinishGood (s : ParallelState π r) (hr : 0 < r) (G : SimpleInput V) :
    FinishOutput π r → Prop
  | .failed => False
  | .done t => IsThresholdCertificate r (π.graph G.toWeighted) t.quotientGraph
  | .advance t => t.usedGraph.IsSubgraph G.toWeighted ∧ t.Laminar ∧
      t.InactiveSound hr G.toWeighted ∧ t.failed = false ∧
      t.livePotential + 1 ≤ s.livePotential

theorem finishStep_honest (s : ParallelState π r) (hr : 0 < r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false) :
    s.FinishGood hr G ((s.finishStep hr).eval G.toWeighted.cut) := by
  let vs := (Finset.univ \ s.inactive).toList
  let out := (s.scanVertices hr vs).eval G.toWeighted.cut
  have hscan := s.scanVertices_result hr vs G hs
  obtain ⟨hforest, hfailed, hrep⟩ := hscan
  change out.state.forests = s.forests at hforest
  change out.state.failed = s.failed at hfailed
  change (match out.representative with
    | none => ∀ v ∈ vs, v ∈ out.state.inactive
    | some v => v ∈ vs ∧
        0 < (G.toWeighted.subtract s.usedGraph).cross {v} (s.lastBlock hr v)ᶜ) at hrep
  have hfalse : out.state.failed = false := hfailed.trans hf
  have hsub' : out.state.usedGraph.IsSubgraph G.toWeighted := by
    simpa only [usedGraph, hforest] using hs
  have hl' : out.state.Laminar := by simpa only [Laminar, hforest] using hl
  have hi' : out.state.InactiveSound hr G.toWeighted :=
    s.scanVertices_inactiveSound hr vs G hs hi
  have hpot : out.state.livePotential ≤ s.livePotential :=
    s.scanVertices_livePotential hr vs G.toWeighted.cut
  let next : ScanOutput π r →
      DTree (Finset V) ℝ (FinishOutput π r) ((searchDepth V + 1) * 3) := fun out =>
    if out.state.failed then DTree.pure .failed else
      match out.representative with
      | none => DTree.pure (.done out.state)
      | some v => (out.state.advanceVertex hr v).map fun result =>
          match result with
          | none => .failed
          | some t => .advance t
  change s.FinishGood hr G (((s.activeScan hr).bind next).eval G.toWeighted.cut)
  rw [DTree.eval_bind, activeScan_eval]
  change s.FinishGood hr G ((next out).eval G.toWeighted.cut)
  dsimp only [next]
  simp only [hfalse, Bool.false_eq_true, ite_false]
  cases ho : out.representative with
  | none =>
      simp only [ho, DTree.eval_pure, FinishGood]
      exact s.scanVertices_none_certificate hr G hs hl hi ho
  | some v =>
      have hp : 0 < (G.toWeighted.subtract out.state.usedGraph).cross {v}
          (out.state.lastBlock hr v)ᶜ := by
        have hp' : v ∈ vs ∧ 0 < (G.toWeighted.subtract s.usedGraph).cross {v}
            (s.lastBlock hr v)ᶜ := by simpa only [ho] using hrep
        simpa only [usedGraph, lastBlock, hforest] using hp'.2
      obtain ⟨t, ht, htsub, htl, hti, htina, htf, htp⟩ :=
        out.state.advanceVertex_honest hr v G hsub' hl' hi' hp
      simp only [ho, DTree.eval_map, ht, FinishGood]
      exact ⟨htsub, htl, hti, htf.trans hfalse, htp.trans hpot⟩

/-- Every nonfailed step charges only new retirements and one neighbor search.
This operational cost statement holds against arbitrary oracle answers. -/
theorem finishStep_charge (s : ParallelState π r) (hr : 0 < r) (read : Finset V → ℝ) :
    match (s.finishStep hr).eval read with
    | .failed => True
    | .done t | .advance t => s.inactive ⊆ t.inactive ∧
        (s.finishStep hr).cost read ≤
          3 * (t.inactive.card - s.inactive.card + 1) + (searchDepth V + 1) * 3 := by
  let out := (s.activeScan hr).eval read
  have hcost := s.activeScan_cost_charge hr read
  change (s.activeScan hr).cost read ≤
    3 * (out.state.inactive.card - s.inactive.card + 1) at hcost
  have hmono : s.inactive ⊆ out.state.inactive := by
    dsimp only [out]
    rw [activeScan_eval]
    exact s.scanVertices_inactive_mono hr _ read
  let next : ScanOutput π r →
      DTree (Finset V) ℝ (FinishOutput π r) ((searchDepth V + 1) * 3) := fun out =>
    if out.state.failed then DTree.pure .failed else
      match out.representative with
      | none => DTree.pure (.done out.state)
      | some v => (out.state.advanceVertex hr v).map fun result =>
          match result with
          | none => .failed
          | some t => .advance t
  change (match ((s.activeScan hr).bind next).eval read with
    | .failed => True
    | .done t | .advance t => s.inactive ⊆ t.inactive ∧
        ((s.activeScan hr).bind next).cost read ≤
          3 * (t.inactive.card - s.inactive.card + 1) + (searchDepth V + 1) * 3)
  simp only [DTree.eval_bind, det_cost_bind]
  change (match (next out).eval read with
    | .failed => True
    | .done t | .advance t => s.inactive ⊆ t.inactive ∧
        (s.activeScan hr).cost read + (next out).cost read ≤
          3 * (t.inactive.card - s.inactive.card + 1) + (searchDepth V + 1) * 3)
  dsimp only [next]
  cases hfail : out.state.failed with
  | true => simp only [hfail, ite_true, DTree.eval_pure]
  | false =>
      simp only [hfail, Bool.false_eq_true, ite_false]
      cases hrep : out.representative with
      | none =>
          simp only [hrep, DTree.eval_pure, det_cost_pure, add_zero]
          exact ⟨hmono, hcost.trans (Nat.le_add_right _ _)⟩
      | some v =>
          simp only [hrep, DTree.eval_map, det_cost_map]
          cases hn : (out.state.advanceVertex hr v).eval read with
          | none => trivial
          | some t =>
              have heq := out.state.advanceVertex_inactive hr v read hn
              have hsearch := DTree.cost_le (out.state.advanceVertex hr v) read
              change s.inactive ⊆ t.inactive ∧
                (s.activeScan hr).cost read + (out.state.advanceVertex hr v).cost read ≤
                  3 * (t.inactive.card - s.inactive.card + 1) + (searchDepth V + 1) * 3
              rw [heq]
              exact ⟨hmono, Nat.add_le_add hcost hsearch⟩

/-- A finite finishing program. The number of steps is public; queries still
use only the original oracle and learned endpoint lists. -/
def finishRounds (hr : 0 < r) : (steps : ℕ) → ParallelState π r →
    DTree (Finset V) ℝ (Option (WeightedGraph Q)) (steps * finishStepBudget V)
  | 0, _ => DTree.pure none
  | steps + 1, s =>
      ((s.finishStep hr).bind fun out => match out with
        | .failed => DTree.pure none
        | .done t => DTree.pure (some t.quotientGraph)
        | .advance t => finishRounds hr steps t).cast (by rw [Nat.succ_mul]; omega)

/-- Completion is proved from decreasing actual live-component potential.
This theorem supplies no numerical query envelope for the parallel phase. -/
theorem finishRounds_correct (hr : 0 < r) (steps : ℕ) (s : ParallelState π r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false)
    (hsteps : s.livePotential < steps) :
    ∃ H, (finishRounds hr steps s).eval G.toWeighted.cut = some H ∧
      IsThresholdCertificate r (π.graph G.toWeighted) H := by
  induction steps generalizing s with
  | zero => omega
  | succ steps ih =>
      have hgood := s.finishStep_honest hr G hs hl hi hf
      rw [finishRounds, DTree.eval_cast, DTree.eval_bind]
      cases ho : (s.finishStep hr).eval G.toWeighted.cut with
      | failed => exact False.elim (by simpa only [ho, FinishGood] using hgood)
      | done t =>
          refine ⟨t.quotientGraph, by simp only [DTree.eval_pure], ?_⟩
          simpa only [ho, FinishGood] using hgood
      | advance t =>
          have ht : t.usedGraph.IsSubgraph G.toWeighted ∧ t.Laminar ∧
              t.InactiveSound hr G.toWeighted ∧ t.failed = false ∧
              t.livePotential + 1 ≤ s.livePotential := by
            simpa only [ho, FinishGood] using hgood
          exact ih t ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 (by omega)

/-- A uniform bound for every finite finishing approximation. Retirements
telescope over original vertices, and successful steps spend live potential. -/
theorem finishRounds_cost (hr : 0 < r) (steps : ℕ) (s : ParallelState π r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false) :
    (finishRounds hr steps s).cost G.toWeighted.cut ≤
      3 * (Fintype.card V - s.inactive.card) +
        (3 + (searchDepth V + 1) * 3) * (s.livePotential + 1) := by
  induction steps generalizing s with
  | zero => simp only [finishRounds, det_cost_pure]; omega
  | succ steps ih =>
      let K := 3 + (searchDepth V + 1) * 3
      have hgood := s.finishStep_honest hr G hs hl hi hf
      have hcharge := s.finishStep_charge hr G.toWeighted.cut
      rw [finishRounds, det_cost_cast, det_cost_bind]
      cases ho : (s.finishStep hr).eval G.toWeighted.cut with
      | failed => exact False.elim (by simpa only [ho, FinishGood] using hgood)
      | done t =>
          have hc : s.inactive ⊆ t.inactive ∧ (s.finishStep hr).cost G.toWeighted.cut ≤
              3 * (t.inactive.card - s.inactive.card + 1) + (searchDepth V + 1) * 3 := by
            simpa only [ho] using hcharge
          have htcard := t.inactive_card_le
          have hscard := Finset.card_mono hc.1
          have hk : K ≤ K * (s.livePotential + 1) := by
            calc
              K = K * 1 := (Nat.mul_one K).symm
              _ ≤ _ := Nat.mul_le_mul_left K (by omega)
          simp only [det_cost_pure, add_zero]
          change (s.finishStep hr).cost G.toWeighted.cut ≤
            3 * (Fintype.card V - s.inactive.card) + K * (s.livePotential + 1)
          have hstep : (s.finishStep hr).cost G.toWeighted.cut ≤
              3 * (Fintype.card V - s.inactive.card) + K := by
            dsimp [K]
            omega
          exact hstep.trans (Nat.add_le_add_left hk _)
      | advance t =>
          have ht : t.usedGraph.IsSubgraph G.toWeighted ∧ t.Laminar ∧
              t.InactiveSound hr G.toWeighted ∧ t.failed = false ∧
              t.livePotential + 1 ≤ s.livePotential := by
            simpa only [ho, FinishGood] using hgood
          have hc : s.inactive ⊆ t.inactive ∧ (s.finishStep hr).cost G.toWeighted.cut ≤
              3 * (t.inactive.card - s.inactive.card + 1) + (searchDepth V + 1) * 3 := by
            simpa only [ho] using hcharge
          have htail := ih t ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1
          have hscard := Finset.card_mono hc.1
          have htcard := t.inactive_card_le
          have hpot := ht.2.2.2.2
          have hmul : K * (t.livePotential + 1) ≤ K * s.livePotential :=
            Nat.mul_le_mul_left K hpot
          have hstep : (s.finishStep hr).cost G.toWeighted.cut ≤
              3 * (t.inactive.card - s.inactive.card) + K := by dsimp [K]; omega
          change (s.finishStep hr).cost G.toWeighted.cut +
              (finishRounds hr steps t).cost G.toWeighted.cut ≤
            3 * (Fintype.card V - s.inactive.card) + K * (s.livePotential + 1)
          change (finishRounds hr steps t).cost G.toWeighted.cut ≤
            3 * (Fintype.card V - t.inactive.card) + K * (t.livePotential + 1) at htail
          rw [Nat.mul_add, Nat.mul_one]
          omega

/-- The finishing cost depends on the remaining live components, not on r
fresh forests over the original quotient. -/
theorem finishRounds_cost_live (hr : 0 < r) (steps : ℕ) (s : ParallelState π r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false) :
    (finishRounds hr steps s).cost G.toWeighted.cut ≤
      3 * Fintype.card V +
        (3 + (searchDepth V + 1) * 3) * (r * (s.liveBlocks (lastIndex hr)).card + 1) := by
  apply (finishRounds_cost hr steps s G hs hl hi hf).trans
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 (Nat.sub_le _ _))
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (s.livePotential_le hr hl) 1))

/-- A fixed public finite horizon suffices to finish the current forests.
The sharp cost still uses only the remaining live components. -/
def finishProgram (hr : 0 < r) (s : ParallelState π r) :
    DTree (Finset V) ℝ (Option (WeightedGraph Q))
      ((r * Fintype.card Q + 1) * finishStepBudget V) :=
  finishRounds hr (r * Fintype.card Q + 1) s

theorem finishProgram_correct (hr : 0 < r) (s : ParallelState π r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false) :
    ∃ H, (s.finishProgram hr).eval G.toWeighted.cut = some H ∧
      IsThresholdCertificate r (π.graph G.toWeighted) H := by
  apply finishRounds_correct hr _ s G hs hl hi hf
  have hp := (s.livePotential_le hr hl).trans
    (Nat.mul_le_mul_left r (s.liveBlocks_card_le (lastIndex hr)))
  omega

/-- At the parallel stopping scale, the actual finishing program fits a
uniform part of the sharp P envelope. This is only the finishing operation,
not a bound for reaching the stopping scale. -/
theorem finishProgram_cost_at_scale (hr : 0 < r) (s : ParallelState π r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false)
    (hn : 1 ≤ Fintype.card V) (hln : 1 ≤ Real.log (Fintype.card V : ℝ))
    (hq : 2 ≤ Fintype.card Q) (hqn : Fintype.card Q ≤ Fintype.card V)
    (hstop : ((s.liveBlocks (lastIndex hr)).card : ℝ) ≤
      (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ)) :
    ((s.finishProgram hr).cost G.toWeighted.cut : ℝ) ≤
      18 * ((Fintype.card V : ℝ) + r * Fintype.card Q *
        Real.log (Fintype.card V : ℝ) / Real.log (Fintype.card Q : ℝ)) := by
  let n : ℝ := Fintype.card V
  let q : ℝ := Fintype.card Q
  let l : ℝ := (s.liveBlocks (lastIndex hr)).card
  let K : ℝ := 3 + ((searchDepth V : ℝ) + 1) * 3
  have hlogpos : 0 < Real.log n := by dsimp [n]; linarith
  have hnpos : 0 < n := by dsimp [n]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have hqpos : 0 < q := by dsimp [q]; exact_mod_cast (show 0 < Fintype.card Q by omega)
  have hql : 0 < Real.log q :=
    Real.log_pos (by dsimp [q]; exact_mod_cast (show 1 < Fintype.card Q by omega))
  have hK : K ≤ 15 * Real.log n := by
    have hc := Schedule.clog_le_twice_log_add_one (Fintype.card V) hn
    dsimp [K, n, searchDepth] at *
    linarith
  have hstop' : Real.log n * l ≤ q := by
    have hh := (le_div_iff₀ hlogpos).mp hstop
    simpa only [n, q, l, mul_comm] using hh
  have hmul := mul_le_mul_of_nonneg_left hstop' (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hfinish : K * ((r : ℝ) * l + 1) ≤ 15 * ((r : ℝ) * q) + 15 * Real.log n := by
    calc
      K * ((r : ℝ) * l + 1) ≤ 15 * Real.log n * ((r : ℝ) * l + 1) :=
        mul_le_mul_of_nonneg_right hK (by dsimp [l]; positivity)
      _ = 15 * ((r : ℝ) * (Real.log n * l)) + 15 * Real.log n := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 15)) le_rfl
  have hlogn : Real.log n ≤ n := by linarith [Real.log_le_sub_one_of_pos hnpos]
  have hratio : (r : ℝ) * q ≤ (r : ℝ) * q * Real.log n / Real.log q := by
    apply (le_div_iff₀ hql).mpr
    have hlog := Real.log_le_log hqpos (show q ≤ n by dsimp [q, n]; exact_mod_cast hqn)
    exact mul_le_mul_of_nonneg_left hlog (by dsimp [q]; positivity)
  have hc : ((s.finishProgram hr).cost G.toWeighted.cut : ℝ) ≤
      3 * n + K * ((r : ℝ) * l + 1) := by
    dsimp only [n, K, l, finishProgram]
    exact_mod_cast finishRounds_cost_live hr (r * Fintype.card Q + 1) s G hs hl hi hf
  change ((s.finishProgram hr).cost G.toWeighted.cut : ℝ) ≤
    18 * (n + (r : ℝ) * q * Real.log n / Real.log q)
  have hrq : 0 ≤ (r : ℝ) * q := by positivity
  nlinarith

end ParallelState

#print axioms ParallelState.residualNeighbor_positive
#print axioms ParallelState.advanceVertex_honest
#print axioms ParallelState.vertexProbe_honest
#print axioms ParallelState.vertexProbe_zero
#print axioms ParallelState.vertexProbe_positive
#print axioms ParallelState.scanVertices_budget
#print axioms ParallelState.scanVertices_forests
#print axioms ParallelState.scanVertices_inactive_mono
#print axioms ParallelState.scanVertices_cost_charge
#print axioms ParallelState.activeScan_cost_charge
#print axioms ParallelState.blockScan_cost_charge
#print axioms ParallelState.scanBlocks_forests
#print axioms ParallelState.scanBlocks_inactive
#print axioms ParallelState.scanBlocks_cost_charge
#print axioms ParallelState.scanBlocks_inactiveSound
#print axioms ParallelState.scanBlocks_labels_sublist
#print axioms ParallelState.scanBlocks_good
#print axioms ParallelState.representativeScan_cost_charge
#print axioms ParallelState.representativeScan_good
#print axioms ParallelState.representativeScan_covers_live
#print axioms ParallelState.representativeScan_distinct_labels
#print axioms ParallelState.representativeScan_separated
#print axioms ParallelState.scanVertices_inactiveSound
#print axioms ParallelState.scanVertices_result
#print axioms ParallelState.scanVertices_none_certificate
#print axioms ParallelState.scanVertices_livePotential
#print axioms ParallelState.finishStep_honest
#print axioms ParallelState.finishStep_charge
#print axioms ParallelState.finishRounds_correct
#print axioms ParallelState.finishRounds_cost
#print axioms ParallelState.finishRounds_cost_live
#print axioms ParallelState.finishProgram_correct
#print axioms ParallelState.finishProgram_cost_at_scale

end
end CutQueryComplexity.StarContraction2022.Certificates
