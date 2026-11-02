import CutQueryComplexity.GHReduction.Randomized.TreeOps
import CutQueryComplexity.GHReduction.ThresholdCosts

/-! # Phase 3b: threshold rounds and source maxima as call programs

Twins of the threshold programs (`ThresholdProgram`, `ThresholdEndpoint`,
`ThresholdAmplification`, `SourceMaximum`): the deterministic level and round
programs as `CallProg`s, and the seeded rounds, adaptive elimination,
classification and binary-search maximum as `CallTree`s in the namespace
`Twin`, under their old names. Each comes with its bridge (ideal law equals the
old program's law under any exact family with size-regular cost, on promised
graphs) and its realized charged cost, as in `ThresholdCosts`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal BigOperators
open WeightedGraph Probability

namespace CallProg

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Twin of `thresholdLevelProgram`. -/
def thresholdLevelCall (U R : Finset V) (s : V) (W : ℝ) (z : ℕ) : CallProg V (Finset V) :=
  if 2 ≤ R.card then (isolatingValuesCall R).map (thresholdCoverage U s W z) else pure ∅

theorem thresholdLevel_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (U R : Finset V) (s : V) (W : ℝ) (z : ℕ) :
    Prog.eval G.cut (thresholdLevelProgram E U R s W z) =
      idealEval G (thresholdLevelCall U R s W z) := by
  unfold thresholdLevelProgram thresholdLevelCall
  split_ifs <;> simp [isolatingValues_idealEval E G hG]

theorem thresholdLevelCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (U R : Finset V) (s : V) (W : ℝ) (z : ℕ) (G : WeightedGraph V) :
    n * idealCost G Q (thresholdLevelCall U R s W z) ≤
      (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) := by
  by_cases hR : 2 ≤ R.card
  · have hcost := isolatingCall_idealCost_scaled R hvn hQ G
    have hcard := Finset.card_le_univ R
    have hlog := Nat.clog_mono_right 2 (hcard.trans hvn)
    have hcostValues : idealCost G Q (isolatingValuesCall R) =
        idealCost G Q (isolatingCall R) + R.card := by
      simp [isolatingValuesCall]
    simp only [thresholdLevelCall, hR, ite_true, idealCost_map, hcostValues]
    have hsum := Nat.add_le_add hcost (Nat.mul_le_mul_left n hcard)
    have hlogmul := Nat.mul_le_mul_right (Fintype.card V * Q n) hlog
    calc
      _ ≤ (Nat.clog 2 n + 2) * Fintype.card V * Q n + n * Fintype.card V := by
        nlinarith only [hsum, hlogmul]
      _ ≤ (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) := by
        have hbase : n * Fintype.card V ≤
            (Nat.clog 2 n + 3) * Fintype.card V * n := by
          have := Nat.mul_le_mul_right (Fintype.card V * n)
            (show 1 ≤ Nat.clog 2 n + 3 by omega)
          nlinarith only [this]
        nlinarith only [hbase, Nat.zero_le (Fintype.card V * Q n)]
  · simp [thresholdLevelCall, hR]

/-- Twin of `thresholdRoundProgram`. -/
def thresholdRoundCall (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ)
    (seed : ThresholdSeed V levels) : CallProg V (Finset V) :=
  (tableProgram (levels + 1) (fun i =>
    thresholdLevelCall U (levelSample U s i.val seed) s W z)).map
      (fun covered => Finset.univ.biUnion covered)

theorem thresholdRound_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ)
    (seed : ThresholdSeed V levels) :
    Prog.eval G.cut (thresholdRoundProgram E U s W z levels seed) =
      idealEval G (thresholdRoundCall U s W z levels seed) := by
  simp only [thresholdRoundProgram, thresholdRoundCall, Prog.eval_map, tableProgram_eval,
    idealEval_map, idealEval_tableProgram, thresholdLevel_idealEval E G hG]

theorem thresholdRoundCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ)
    (seed : ThresholdSeed V levels) (G : WeightedGraph V) :
    n * idealCost G Q (thresholdRoundCall U s W z levels seed) ≤
      (levels + 1) * ((Nat.clog 2 n + 3) * Fintype.card V * (Q n + n)) := by
  simp only [thresholdRoundCall, idealCost_map, idealCost_tableProgram, Finset.mul_sum]
  calc
    _ ≤ ∑ _i : Fin (levels + 1), (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) :=
      Finset.sum_le_sum (fun i _ => thresholdLevelCall_idealCost_scaled hvn hQ U _ s W z G)
    _ = _ := by simp

theorem thresholdRoundCall_idealCost {n : ℕ} {Q : ℕ → ℕ} (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ)
    (seed : ThresholdSeed V levels) (G : WeightedGraph V) :
    idealCost G Q (thresholdRoundCall U s W z levels seed) ≤ thresholdRoundBudget Q n levels := by
  have : Nonempty V := ⟨s⟩
  have hn : 0 < n := lt_of_lt_of_le Fintype.card_pos hvn
  have h := thresholdRoundCall_idealCost_scaled hvn hQ U s W z levels seed G
  have hmul := Nat.mul_le_mul_left ((levels + 1) * (Nat.clog 2 n + 3) * (Q n + n)) hvn
  have hfinal : n * idealCost G Q (thresholdRoundCall U s W z levels seed) ≤
      n * thresholdRoundBudget Q n levels := by
    unfold thresholdRoundBudget
    nlinarith
  exact Nat.le_of_mul_le_mul_left hfinal hn

end CallProg

namespace Twin

variable {V : Type} [Fintype V] [DecidableEq V]
open CallTree

/-- Twin of `thresholdRoundTree`. -/
def thresholdRoundTree (Q : ℕ → ℕ) (n : ℕ) (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) :
    CallTree V Q (Finset V) (thresholdRoundBudget Q n levels) :=
  random (thresholdSeedPMF V levels) (fun seed =>
    (CallProg.compile Q (CallProg.thresholdRoundCall U s W z levels seed)
      (thresholdRoundBudget Q n levels)).map (fun output => output.getD ∅))

/-- Twin of `thresholdRemainingTree`. -/
def thresholdRemainingTree (Q : ℕ → ℕ) (n : ℕ) (s : V) (W : ℝ) (levels : ℕ) :
    (rounds : ℕ) → (U : Finset V) →
      CallTree V Q (Finset V) (rounds * thresholdRoundBudget Q n levels)
  | 0, U => up (Nat.zero_le _) (pure (PMF.pure U))
  | rounds + 1, U =>
    ((thresholdRoundTree Q n U s W n levels).bind (fun covered =>
      thresholdRemainingTree Q n s W levels rounds (U \ covered))).cast (by ring)

/-- Twin of `thresholdClassifyTree`. -/
def thresholdClassifyTree (Q : ℕ → ℕ) (n : ℕ) (U : Finset V) (s : V) (W : ℝ)
    (levels scale exponent : ℕ) :
    CallTree V Q (Finset V) (thresholdRounds levels scale exponent * thresholdRoundBudget Q n levels) :=
  (thresholdRemainingTree Q n s W levels (thresholdRounds levels scale exponent) U).map
    (fun remaining => U \ remaining)

/-- Twin of `sourceMaxAtTree`. -/
def sourceMaxAtTree (Q : ℕ → ℕ) (n : ℕ) (s : V) (levels scale exponent : ℕ) : (fuel : ℕ) →
    Finset V → ℕ → ℕ → CallTree V Q (Option V) (fuel * sourceThresholdBudget Q n levels scale exponent)
  | 0, R, _, _ => up (Nat.zero_le _) (pure (PMF.pure (selectVertex R)))
  | fuel + 1, R, lo, hi =>
    if hi ≤ lo then up (Nat.zero_le _) (pure (PMF.pure (selectVertex R))) else
      let mid := lo + (hi - lo) / 2
      ((thresholdClassifyTree Q n (insert s R) s (mid : ℝ) levels scale exponent).bind
        (fun covered => if (R \ covered).Nonempty then
          sourceMaxAtTree Q n s levels scale exponent fuel (R \ covered) (mid + 1) hi
        else sourceMaxAtTree Q n s levels scale exponent fuel R lo mid)).cast (by
          simp only [sourceThresholdBudget]
          ring)

/-- Twin of `sourceMaxTree`. -/
def sourceMaxTree (M : ℕ) (Q : ℕ → ℕ) (n : ℕ) (R : Finset V) (s : V) (levels scale exponent : ℕ) :
    CallTree V Q (Option V) (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent) :=
  sourceMaxAtTree Q n s levels scale exponent (Nat.clog 2 (M + 1)) R 0 M

/-! ### Bridges -/

variable {M n : ℕ} {Q QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)

theorem thresholdRoundTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) :
    interpIdeal G (thresholdRoundTree Q n U s W z levels) =
      (GHReduction.thresholdRoundTree E n U s W z levels).eval G.cut := by
  rw [GHReduction.thresholdRoundTree]
  refine random_eq _ (fun seed _ => ?_)
  rw [interpIdeal_map, CallProg.interpIdeal_compile G Q _ _
      (CallProg.thresholdRoundCall_idealCost hvn hQ U s W z levels seed G),
    RTree.eval_ofDeterministic, DTree.eval_map,
    Prog.toDTree_eval _ _ _ (thresholdRoundProgram_cost E hvn hQE U s W z levels seed G.cut),
    CallProg.thresholdRound_idealEval E G hG, PMF.pure_map]

theorem thresholdRemainingTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G)
    (s : V) (W : ℝ) (levels rounds : ℕ) (U : Finset V) :
    interpIdeal G (thresholdRemainingTree Q n s W levels rounds U) =
      (GHReduction.thresholdRemainingTree E n s W levels rounds U).eval G.cut := by
  induction rounds generalizing U with
  | zero => simp [thresholdRemainingTree, GHReduction.thresholdRemainingTree]
  | succ rounds ih =>
      simp only [thresholdRemainingTree, GHReduction.thresholdRemainingTree, interpIdeal_cast,
        RTree.eval_cast]
      exact bind_eq (thresholdRoundTree_eq E hvn hQ hQE G hG U s W n levels) (fun _ _ => ih _)

theorem thresholdClassifyTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : V) (W : ℝ) (levels scale exponent : ℕ) :
    interpIdeal G (thresholdClassifyTree Q n U s W levels scale exponent) =
      (GHReduction.thresholdClassifyTree E n U s W levels scale exponent).eval G.cut :=
  map_eq _ (thresholdRemainingTree_eq E hvn hQ hQE G hG s W levels _ U)

theorem sourceMaxAtTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G)
    (s : V) (levels scale exponent fuel : ℕ) (R : Finset V) (lo hi : ℕ) :
    interpIdeal G (sourceMaxAtTree Q n s levels scale exponent fuel R lo hi) =
      (GHReduction.sourceMaxAtTree E n s levels scale exponent fuel R lo hi).eval G.cut := by
  induction fuel generalizing R lo hi with
  | zero => simp [sourceMaxAtTree, GHReduction.sourceMaxAtTree]
  | succ fuel ih =>
      by_cases hhilo : hi ≤ lo
      · simp [sourceMaxAtTree, GHReduction.sourceMaxAtTree, hhilo]
      · simp only [sourceMaxAtTree, GHReduction.sourceMaxAtTree, hhilo, ite_false,
          interpIdeal_cast, RTree.eval_cast]
        refine bind_eq (thresholdClassifyTree_eq E hvn hQ hQE G hG _ s _ levels scale exponent)
          (fun covered _ => ?_)
        split_ifs
        · exact ih _ _ _
        · exact ih _ _ _

theorem sourceMaxTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G)
    (R : Finset V) (s : V) (levels scale exponent : ℕ) :
    interpIdeal G (sourceMaxTree M Q n R s levels scale exponent) =
      (GHReduction.sourceMaxTree E n R s levels scale exponent).eval G.cut :=
  sourceMaxAtTree_eq E hvn hQ hQE G hG s levels scale exponent _ R 0 M

/-! ### Realized charged costs -/

omit E in
theorem thresholdRoundTree_cost_scaled (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) {p : Finset V × ℕ}
    (hp : p ∈ (idealRun G (thresholdRoundTree Q n U s W z levels)).support) :
    n * p.2 ≤ Fintype.card V * thresholdRoundBudget Q n levels := by
  simp only [thresholdRoundTree, idealRun_random, idealRun_map] at hp
  obtain ⟨seed, _, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  rw [idealRun_compile G _ _ (CallProg.thresholdRoundCall_idealCost hvn hQ U s W z levels seed G),
    PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hp
  rw [hp]
  have h := CallProg.thresholdRoundCall_idealCost_scaled hvn hQ U s W z levels seed G
  simpa only [thresholdRoundBudget, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

omit E in
theorem thresholdRemainingTree_cost_scaled (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (s : V) (W : ℝ) (levels rounds : ℕ) (U : Finset V)
    {p : Finset V × ℕ}
    (hp : p ∈ (idealRun G (thresholdRemainingTree Q n s W levels rounds U)).support) :
    n * p.2 ≤ Fintype.card V * (rounds * thresholdRoundBudget Q n levels) := by
  induction rounds generalizing U p with
  | zero =>
      simp only [thresholdRemainingTree, idealRun_up] at hp
      simp [idealRun_pure_cost G _ hp]
  | succ rounds ih =>
      simp only [thresholdRemainingTree, idealRun_cast] at hp
      have h := idealRun_bind_cost G _ _ n _ _
        (fun p hp => thresholdRoundTree_cost_scaled hvn hQ G U s W n levels hp)
        (fun first _ q hq => ih (U := U \ first.1) hq) hp
      calc
        _ ≤ _ := h
        _ = _ := by ring

omit E in
theorem thresholdClassifyTree_cost_scaled (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (U : Finset V) (s : V) (W : ℝ) (levels scale exponent : ℕ)
    {p : Finset V × ℕ}
    (hp : p ∈ (idealRun G (thresholdClassifyTree Q n U s W levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V * sourceThresholdBudget Q n levels scale exponent :=
  idealRun_map_cost G _ _ n _
    (fun _ hq => thresholdRemainingTree_cost_scaled hvn hQ G s W levels _ U hq) hp

omit E in
theorem sourceMaxAtTree_cost_scaled (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (s : V) (levels scale exponent fuel : ℕ) (R : Finset V) (lo hi : ℕ)
    {p : Option V × ℕ}
    (hp : p ∈ (idealRun G (sourceMaxAtTree Q n s levels scale exponent fuel R lo hi)).support) :
    n * p.2 ≤ Fintype.card V * (fuel * sourceThresholdBudget Q n levels scale exponent) := by
  induction fuel generalizing R lo hi p with
  | zero =>
      simp only [sourceMaxAtTree, idealRun_up] at hp
      simp [idealRun_pure_cost G _ hp]
  | succ fuel ih =>
      by_cases hhilo : hi ≤ lo
      · simp only [sourceMaxAtTree, hhilo, ite_true, idealRun_up] at hp
        simp [idealRun_pure_cost G _ hp]
      · simp only [sourceMaxAtTree, hhilo, ite_false, idealRun_cast] at hp
        have h := idealRun_bind_cost G _ _ n _ _
          (fun p hp => thresholdClassifyTree_cost_scaled hvn hQ G _ s _ levels scale exponent hp)
          (fun first _ q hq => by
            split_ifs at hq
            · exact ih _ _ _ hq
            · exact ih _ _ _ hq) hp
        calc
          _ ≤ _ := h
          _ = _ := by ring

omit E in
theorem sourceMaxTree_cost_scaled (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (R : Finset V) (s : V) (levels scale exponent : ℕ) {p : Option V × ℕ}
    (hp : p ∈ (idealRun G (sourceMaxTree M Q n R s levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V *
      (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent) :=
  sourceMaxAtTree_cost_scaled hvn hQ G s levels scale exponent _ R 0 M hp

end Twin
end
end CutQueryComplexity.GHReduction.Randomized
