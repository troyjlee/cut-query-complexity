import CutQueryComplexity.StarContraction2022.Quantum.Forest.Progress

/-! # Actual bounded residual spanning-forest construction

The public program starts with the empty forest and appends fresh executed
component rounds using `RTree.bind`. Its finite iteration law, edge soundness,
query cap and spanning probability are derived below from that program.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest
noncomputable section
open ProductPrograms
open CutQueryComplexity.Probability
open scoped Classical ENNReal

variable {n : ℕ}

/-- Append one fresh actual round to the previous public program. -/
def forestIter (E : LearnedEdges n) (eta : ℝ) :
    (h : ℕ) → State n → ProductTree n (State n) (h * recoverBudget n eta)
  | 0, F => RTree.pure (PMF.pure F)
  | h + 1, F => RTree.cast (by simp only [Nat.add_mul, Nat.one_mul])
      ((forestIter E eta h F).bind fun H => forestRound H E eta)

/-- The finite adaptive iteration law is a consequence of `RTree.bind`. -/
def forestLaw (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) : ℕ → State n → PMF (State n)
  | 0, F => PMF.pure F
  | h + 1, F => (forestLaw E eta read h F).bind fun H => (forestRound H E eta).eval read

theorem forestIter_eval (E : LearnedEdges n) (eta : ℝ) (h : ℕ) (F : State n)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (forestIter E eta h F).eval read = forestLaw E eta read h F := by
  induction h with
  | zero => simp [forestIter, forestLaw]
  | succ h ih => simp only [forestIter, RTree.eval_cast, RTree.eval_bind, ih, forestLaw]

theorem forestIter_eval_succ (E : LearnedEdges n) (eta : ℝ) (h : ℕ) (F : State n)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (forestIter E eta (h + 1) F).eval read =
      ((forestIter E eta h F).eval read).bind fun H => (forestRound H E eta).eval read := by
  simp only [forestIter, RTree.eval_cast, RTree.eval_bind]

/-- The exact operational law retains every accumulated query count. -/
theorem forestIter_run_succ (E : LearnedEdges n) (eta : ℝ) (h : ℕ) (F : State n)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (forestIter E eta (h + 1) F) =
      (RTree.run read (forestIter E eta h F)).bind fun old =>
        (RTree.run read (forestRound old.1 E eta)).map fun next => (next.1, old.2 + next.2) := by
  simp only [forestIter, RTree.run_cast, RTree.run_bind]

theorem forestIter_cost (E : LearnedEdges n) (eta : ℝ) (h : ℕ) (F : State n)
    (read : Finset (Fin n) → ProductAnswer n 1) {out : State n × ℕ}
    (hout : out ∈ (RTree.run read (forestIter E eta h F)).support) :
    out.2 ≤ h * recoverBudget n eta := RTree.cost_le _ read hout

theorem forestIter_residualSound (E : LearnedEdges n) (eta : ℝ) (h : ℕ) (F : State n)
    (G : CapacityGraph (Fin n) 1) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) {H : State n}
    (hH : H ∈ ((forestIter E eta h F).eval (productRead G)).support) :
    H.ResidualSound G.toWeighted.support E := by
  induction h generalizing H with
  | zero =>
      have he : H = F := by simpa only [forestIter, RTree.eval_pure, PMF.mem_support_pure_iff] using hH
      exact he ▸ hF
  | succ h ih =>
      rw [forestIter_eval_succ] at hH
      obtain ⟨K, hK, hH⟩ := (PMF.mem_support_bind_iff _ _ _).mp hH
      exact forestRound_residualSound K G E eta hE (ih hK) hH

/-- The public schedule begins with the actual empty residual forest. -/
def forestRun (n : ℕ) (E : LearnedEdges n) (eta : ℝ) :
    ProductTree n (State n) (forestBudget n eta) :=
  forestIter E eta (forestRounds n eta) (State.empty n)

theorem forestRun_eval (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (forestRun n E eta).eval read = forestLaw E eta read (forestRounds n eta) (State.empty n) :=
  forestIter_eval E eta _ _ read

theorem forestRun_cost (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) {out : State n × ℕ}
    (hout : out ∈ (RTree.run read (forestRun n E eta)).support) :
    out.2 ≤ forestBudget n eta := RTree.cost_le _ read hout

theorem forestRun_residualSound (E : LearnedEdges n) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (hE : KnownSubgraph E G) {F : State n}
    (hF : F ∈ ((forestRun n E eta).eval (productRead G)).support) :
    F.ResidualSound G.toWeighted.support E :=
  forestIter_residualSound E eta _ _ G hE (State.empty_residualSound _ _) hF

/-- Acyclicity and the edge bound hold even for arbitrary reply functions. -/
theorem forestRun_output_forest (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) {F : State n}
    (_hF : F ∈ ((forestRun n E eta).eval read).support) :
    F.graph.IsAcyclic ∧ F.val.card ≤ n - 1 := ⟨F.acyclic, F.card_le⟩

theorem state_eq_empty_of_small (F : State n) (hn : n ≤ 1) : F = State.empty n := by
  apply Subtype.ext
  have hc := F.card_le
  have hz : F.val.card = 0 := by omega
  exact Finset.card_eq_zero.mp hz

/-- The same total program is explicitly trivial for zero or one vertex,
under every answer function and without a graph-correctness assumption. -/
theorem forestRun_eval_small (E : LearnedEdges n) (eta : ℝ) (hn : n ≤ 1)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (forestRun n E eta).eval read = PMF.pure (State.empty n) := by
  have he : (id : State n → State n) = fun _ => State.empty n :=
    funext fun F => state_eq_empty_of_small F hn
  rw [← PMF.map_id ((forestRun n E eta).eval read), he]
  exact PMF.map_const _ _

theorem forestRun_eval_zero (E : LearnedEdges 0) (eta : ℝ)
    (read : Finset (Fin 0) → ProductAnswer 0 1) :
    (forestRun 0 E eta).eval read = PMF.pure (State.empty 0) :=
  forestRun_eval_small E eta (by omega) read

theorem forestRun_eval_one (E : LearnedEdges 1) (eta : ℝ)
    (read : Finset (Fin 1) → ProductAnswer 1 1) :
    (forestRun 1 E eta).eval read = PMF.pure (State.empty 1) :=
  forestRun_eval_small E eta (by omega) read

private theorem drift_envelope_step (z : ℝ≥0∞) (h : ℕ) (eta : ℝ) (heta : 0 ≤ eta) :
    (3 / 4 : ℝ≥0∞) * (z * (3 / 4 : ℝ≥0∞) ^ h + ENNReal.ofReal (eta / 2)) +
        ENNReal.ofReal (eta / 8) =
      z * (3 / 4 : ℝ≥0∞) ^ (h + 1) + ENNReal.ofReal (eta / 2) := by
  have hc : ENNReal.ofReal (3 / 4 : ℝ) = (3 / 4 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have herr : (3 / 4 : ℝ≥0∞) * ENNReal.ofReal (eta / 2) + ENNReal.ofReal (eta / 8) =
      ENNReal.ofReal (eta / 2) := by
    rw [← hc, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [mul_add, add_assoc, herr, pow_succ]
  ring

/-- Iterate the proved conditional drift of the actual last round. The
expectation is over all execution branches, including unsuccessful recovery. -/
theorem forestIter_expected_deficit (E : LearnedEdges n) (eta : ℝ) (h : ℕ) (F : State n)
    (G : CapacityGraph (Fin n) 1) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) (heta : 0 < eta) :
    expect ((forestIter E eta h F).eval (productRead G))
      (fun H => (H.deficit G.toWeighted.support E : ℝ≥0∞)) ≤
      (F.deficit G.toWeighted.support E : ℝ≥0∞) * (3 / 4 : ℝ≥0∞) ^ h +
        ENNReal.ofReal (eta / 2) := by
  induction h with
  | zero => simp [forestIter]
  | succ h ih =>
      rw [forestIter_eval_succ, expect_bind]
      calc
        _ ≤ expect ((forestIter E eta h F).eval (productRead G))
            (fun H => (3 / 4 : ℝ≥0∞) * H.deficit G.toWeighted.support E +
              ENNReal.ofReal (eta / 8)) := by
          apply expect_mono_on_support
          intro H hH
          exact forestRound_drift H G E eta hE
            (forestIter_residualSound E eta h F G hE hF hH) heta
        _ = (3 / 4 : ℝ≥0∞) * expect ((forestIter E eta h F).eval (productRead G))
            (fun H => (H.deficit G.toWeighted.support E : ℝ≥0∞)) + ENNReal.ofReal (eta / 8) := by
          rw [expect_add, expect_const_mul, expect_const]
        _ ≤ (3 / 4 : ℝ≥0∞) * ((F.deficit G.toWeighted.support E : ℝ≥0∞) *
            (3 / 4 : ℝ≥0∞) ^ h + ENNReal.ofReal (eta / 2)) + ENNReal.ofReal (eta / 8) :=
          add_le_add (mul_le_mul le_rfl ih (by positivity) (by positivity)) le_rfl
        _ = _ := drift_envelope_step _ h eta heta.le

theorem forestIter_expected_deficit_le_n (E : LearnedEdges n) (eta : ℝ) (h : ℕ) (F : State n)
    (G : CapacityGraph (Fin n) 1) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) (heta : 0 < eta) :
    expect ((forestIter E eta h F).eval (productRead G))
      (fun H => (H.deficit G.toWeighted.support E : ℝ≥0∞)) ≤
      (n : ℝ≥0∞) * (3 / 4 : ℝ≥0∞) ^ h + ENNReal.ofReal (eta / 2) := by
  apply (forestIter_expected_deficit E eta h F G hE hF heta).trans
  apply add_le_add_left
  exact mul_le_mul (by exact_mod_cast F.deficit_le G.toWeighted.support E) le_rfl
    (by positivity) (by positivity)

theorem forestRun_expected_deficit (E : LearnedEdges n) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (hE : KnownSubgraph E G) (heta : 0 < eta) :
    expect ((forestRun n E eta).eval (productRead G))
      (fun F => (F.deficit G.toWeighted.support E : ℝ≥0∞)) ≤ ENNReal.ofReal eta := by
  by_cases hn : n = 0
  · subst n
    rw [forestRun_eval_zero, expect_pure]
    have hz := (State.empty 0).deficit_le G.toWeighted.support E
    have he : (State.empty 0).deficit G.toWeighted.support E = 0 := by omega
    simp [he]
  · have hnpos : 0 < n := by omega
    have htail : (n : ℝ≥0∞) * (3 / 4 : ℝ≥0∞) ^ forestRounds n eta ≤
        ENNReal.ofReal (eta / 2) := by
      have ht := ENNReal.ofReal_le_ofReal (forestRounds_deficit_tail hnpos heta)
      simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 4),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_ofNat] using ht
    apply (forestIter_expected_deficit_le_n E eta (forestRounds n eta) (State.empty n)
      G hE (State.empty_residualSound _ _) heta).trans
    calc
      _ ≤ ENNReal.ofReal (eta / 2) + ENNReal.ofReal (eta / 2) := add_le_add htail le_rfl
      _ = ENNReal.ofReal eta := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Success means a spanning forest of the actual deleted residual graph. -/
def ForestSuccess (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n) (F : State n) : Prop :=
  IsSpanningForest (SimpleGraph.toWeighted (trueResidual G E)) F.graph

theorem forestSuccess_of_deficit_zero (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (F : State n) (hF : F.ResidualSound G.toWeighted.support E)
    (hz : F.deficit G.toWeighted.support E = 0) : ForestSuccess G E F :=
  F.spanningForest_of_deficit_zero G.toWeighted.support E hF hz

/-- Markov at the positive integer deficit converts the actual expectation
bound into a failure bound for the existing spanning-forest semantics. -/
theorem forestRun_failure (E : LearnedEdges n) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (hE : KnownSubgraph E G) (heta : 0 < eta) :
    mass ((forestRun n E eta).eval (productRead G)) (fun F => ¬ForestSuccess G E F) ≤
      ENNReal.ofReal eta := by
  have hm := mul_mass_le_expect ((forestRun n E eta).eval (productRead G))
    (fun F => ¬ForestSuccess G E F) (fun F => (F.deficit G.toWeighted.support E : ℝ≥0∞)) 1
    (by
      intro F hF hbad
      have hs := forestRun_residualSound E eta G hE hF
      have hn : F.deficit G.toWeighted.support E ≠ 0 :=
        fun hz => hbad (forestSuccess_of_deficit_zero G E F hs hz)
      exact_mod_cast (show 1 ≤ F.deficit G.toWeighted.support E by omega))
  rw [one_mul] at hm
  exact hm.trans (forestRun_expected_deficit E eta G hE heta)

theorem forestRun_successProb (E : LearnedEdges n) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (hE : KnownSubgraph E G) (heta : 0 < eta) :
    1 - eta ≤ (forestRun n E eta).successProb (productRead G) (ForestSuccess G E) := by
  rw [RTree.successProb_eq]
  exact success_of_failure_le _ _ heta.le (forestRun_failure E eta G hE heta)

/-- The edge-set residual used by the deficit is exactly the support of the
accepted capacity-graph deletion routine. -/
theorem trueResidual_eq_capacity_support (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n) :
    trueResidual G E = (residualGraph G E).toWeighted.support := by
  ext u v
  rw [trueResidual_adj]
  change ResidualNeighbor G E u v ↔ (((residualGraph G E).w u v : ℕ) : ℝ) ≠ 0
  rw [Nat.cast_ne_zero, residualGraph_w_eq_indicator]
  by_cases h : ResidualNeighbor G E u v <;> simp [h]

theorem forestSuccess_iff_capacity_residual (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (F : State n) :
    ForestSuccess G E F ↔ IsSpanningForest (residualGraph G E).toWeighted F.graph := by
  simp only [ForestSuccess, IsSpanningForest, support_toWeighted, trueResidual_eq_capacity_support]

theorem forestSuccess_of_small (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (F : State n) (hn : n ≤ 1) (hF : F.ResidualSound G.toWeighted.support E) :
    ForestSuccess G E F := by
  apply forestSuccess_of_deficit_zero G E F hF
  apply (F.deficit_zero_iff_spans G.toWeighted.support E hF).mpr
  intro u v _
  have he : u = v := Fin.ext (by have hu := u.isLt; have hv := v.isLt; omega)
  subst v
  exact _root_.SimpleGraph.Reachable.refl u

theorem forestRun_failure_small (E : LearnedEdges n) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (hE : KnownSubgraph E G) (hn : n ≤ 1) :
    mass ((forestRun n E eta).eval (productRead G)) (fun F => ¬ForestSuccess G E F) = 0 := by
  apply le_antisymm ?_ (by positivity)
  calc
    _ ≤ mass ((forestRun n E eta).eval (productRead G)) (fun _ => False) := by
      apply mass_mono_on_support
      intro F hF hbad
      exact hbad (forestSuccess_of_small G E F hn (forestRun_residualSound E eta G hE hF))
    _ = 0 := mass_false _

theorem forestRun_failure_zero (E : LearnedEdges 0) (eta : ℝ)
    (G : CapacityGraph (Fin 0) 1) (hE : KnownSubgraph E G) :
    mass ((forestRun 0 E eta).eval (productRead G)) (fun F => ¬ForestSuccess G E F) = 0 :=
  forestRun_failure_small E eta G hE (by omega)

theorem forestRun_failure_one (E : LearnedEdges 1) (eta : ℝ)
    (G : CapacityGraph (Fin 1) 1) (hE : KnownSubgraph E G) :
    mass ((forestRun 1 E eta).eval (productRead G)) (fun F => ¬ForestSuccess G E F) = 0 :=
  forestRun_failure_small E eta G hE (by omega)

/-- The actual public tree is chosen before every hidden graph. The success
predicate names the accepted capacity residual, and all soundness and cost
claims are derived from this tree's execution. -/
theorem forestRun_public (n : ℕ) (E : LearnedEdges n) (eta : ℝ) (heta : 0 < eta) :
    ∃ T : ProductTree n (State n) (forestBudget n eta),
      (∀ read out, out ∈ (RTree.run read T).support → out.2 ≤ forestBudget n eta) ∧
      ∀ G : CapacityGraph (Fin n) 1, KnownSubgraph E G →
        (∀ F ∈ (T.eval (productRead G)).support,
          F.ResidualSound G.toWeighted.support E ∧ F.graph.IsAcyclic ∧ F.val.card ≤ n - 1) ∧
        mass (T.eval (productRead G))
          (fun F => ¬IsSpanningForest (residualGraph G E).toWeighted F.graph) ≤ ENNReal.ofReal eta ∧
        1 - eta ≤ T.successProb (productRead G)
          (fun F => IsSpanningForest (residualGraph G E).toWeighted F.graph) := by
  refine ⟨forestRun n E eta, fun read _ h => forestRun_cost E eta read h, ?_⟩
  intro G hE
  refine ⟨fun F hF => ⟨forestRun_residualSound E eta G hE hF, F.acyclic, F.card_le⟩, ?_, ?_⟩
  · simpa only [← forestSuccess_iff_capacity_residual] using forestRun_failure E eta G hE heta
  · simpa only [← forestSuccess_iff_capacity_residual] using forestRun_successProb E eta G hE heta

open QuantumQueryComplexity
open scoped Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

theorem forestRun_physical_length (E : LearnedEdges n) (eta : ℝ) :
    (productTreeRoutine (forestRun n E eta)).len =
      12 * productBits n 1 * forestBudget n eta := rfl

/-- Arbitrary physical answer tables keep the same normalized circuit. -/
theorem forestRun_physical_normalized (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → CutAnswer n 1) :
    IsQState ((productTreeRoutine (forestRun n E eta)).run read *ᵥ
      (productTreeAlg (forestRun n E eta)).init) := productTreeRoutine_isQState _ read

theorem forestRun_physical_prob (E : LearnedEdges n) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (F : State n) :
    (productTreeAlg (forestRun n E eta)).prob (capacityRead G)
      (physicalQueries n (forestBudget n eta)) F =
      (forestLaw E eta (productRead G) (forestRounds n eta) (State.empty n) F).toReal := by
  rw [productTreeAlg_prob]
  change (((forestRun n E eta).eval (productRead G)) F).toReal = _
  rw [forestRun_eval]

/-- Exact Born-event identity for every predicate, not only the success event. -/
theorem forestRun_physical_event (E : LearnedEdges n) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (Good : State n → Prop) :
    goodProb (productTreeAlg (forestRun n E eta)).readout Good
      ((productTreeAlg (forestRun n E eta)).state (capacityRead G)
        (physicalQueries n (forestBudget n eta))) =
      (mass (forestLaw E eta (productRead G) (forestRounds n eta) (State.empty n)) Good).toReal := by
  rw [productTreeAlg_successProb, RTree.successProb_eq, forestRun_eval]
  rfl

theorem forestRun_physical_successProb (E : LearnedEdges n) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (hE : KnownSubgraph E G) (heta : 0 < eta) :
    1 - eta ≤ goodProb (productTreeAlg (forestRun n E eta)).readout
      (fun F => IsSpanningForest (residualGraph G E).toWeighted F.graph)
      ((productTreeAlg (forestRun n E eta)).state (capacityRead G)
        (physicalQueries n (forestBudget n eta))) := by
  rw [productTreeAlg_successProb]
  simpa only [← forestSuccess_iff_capacity_residual] using forestRun_successProb E eta G hE heta

#print axioms forestIter_eval
#print axioms forestIter_run_succ
#print axioms forestIter_cost
#print axioms forestIter_residualSound
#print axioms forestRun_eval
#print axioms forestRun_cost
#print axioms forestRun_residualSound
#print axioms forestRun_output_forest
#print axioms forestRun_eval_zero
#print axioms forestRun_eval_one
#print axioms forestIter_expected_deficit
#print axioms forestIter_expected_deficit_le_n
#print axioms forestRun_expected_deficit
#print axioms forestRun_failure
#print axioms forestRun_successProb
#print axioms trueResidual_eq_capacity_support
#print axioms forestSuccess_iff_capacity_residual
#print axioms forestRun_failure_zero
#print axioms forestRun_failure_one
#print axioms forestRun_public
#print axioms forestRun_physical_length
#print axioms forestRun_physical_normalized
#print axioms forestRun_physical_prob
#print axioms forestRun_physical_event
#print axioms forestRun_physical_successProb

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
