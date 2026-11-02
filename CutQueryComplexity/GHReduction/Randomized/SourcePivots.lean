import CutQueryComplexity.GHReduction.Randomized.GuideCosts
import CutQueryComplexity.GHReduction.SourcePivotCosts

/-! # Phase 3d, first part: pivot steps, sampled guides and single-source values

Twins of the outer pivot step (`OuterPivot.Step`: `levelProgram` and
`stepProgram` as call programs, `randomStepTree` as a call tree), the sampled
guides (`SampledGuides`), the single-source values (`SingleSource`) and the
source pivot (`SourcePivot`), with their bridges and realized charged costs
(mirroring `SingleSourceBudget` and `SourcePivotCosts`). The guide sample is
call-free and is embedded unchanged with `CallTree.ofRTree`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal BigOperators
open WeightedGraph Probability OuterPivot

namespace CallProg

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Twin of `OuterPivot.levelProgram`. -/
def levelCall (U R : Finset V) (s : V) (values : V → Option ℝ) : CallProg V (Batch V) :=
  if 2 ≤ R.card then (isolatingValuesCall R).map (prepareBatch U R s values) else pure Batch.empty

theorem level_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (U R : Finset V) (s : V)
    (values : V → Option ℝ) :
    Prog.eval G.cut (levelProgram E U R s values) = idealEval G (levelCall U R s values) := by
  unfold levelProgram levelCall
  split_ifs <;> simp [isolatingValues_idealEval E G hG]

theorem levelCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (U R : Finset V) (s : V) (values : V → Option ℝ)
    (G : WeightedGraph V) :
    n * idealCost G Q (levelCall U R s values) ≤ (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) := by
  have he : idealCost G Q (levelCall U R s values) = idealCost G Q (thresholdLevelCall U R s 0 0) := by
    by_cases hR : 2 ≤ R.card <;> simp [levelCall, thresholdLevelCall, hR]
  rw [he]
  exact thresholdLevelCall_idealCost_scaled hvn hQ U R s 0 0 G

/-- Twin of `OuterPivot.stepProgram`. -/
def stepCall (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) : CallProg V (Output V levels) :=
  (tableProgram (levels + 1) (fun i =>
    levelCall U (levelSample U s i.val seed) s values)).map (selectLevel U)

theorem step_idealEval {M : ℕ} {QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V)
    (values : V → Option ℝ) (levels : ℕ) (seed : ThresholdSeed V levels) :
    Prog.eval G.cut (stepProgram E U s values levels seed) =
      idealEval G (stepCall U s values levels seed) := by
  simp only [stepProgram, stepCall, Prog.eval_map, tableProgram_eval, idealEval_map,
    idealEval_tableProgram, level_idealEval E G hG]

theorem stepCall_idealCost_scaled {n : ℕ} {Q : ℕ → ℕ} (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (G : WeightedGraph V) :
    n * idealCost G Q (stepCall U s values levels seed) ≤
      (levels + 1) * ((Nat.clog 2 n + 3) * Fintype.card V * (Q n + n)) := by
  simp only [stepCall, idealCost_map, idealCost_tableProgram, Finset.mul_sum]
  calc
    _ ≤ ∑ _i : Fin (levels + 1), (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) :=
      Finset.sum_le_sum (fun i _ => levelCall_idealCost_scaled hvn hQ U _ s values G)
    _ = _ := by simp

theorem stepCall_idealCost {n : ℕ} {Q : ℕ → ℕ} (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (G : WeightedGraph V) :
    idealCost G Q (stepCall U s values levels seed) ≤ stepBudget Q n levels := by
  have : Nonempty V := ⟨s⟩
  have hn : 0 < n := lt_of_lt_of_le Fintype.card_pos hvn
  have h := stepCall_idealCost_scaled hvn hQ U s values levels seed G
  have hmul := Nat.mul_le_mul_left (stepBudget Q n levels) hvn
  have hfinal : n * idealCost G Q (stepCall U s values levels seed) ≤ n * stepBudget Q n levels := by
    unfold stepBudget at *
    nlinarith
  exact Nat.le_of_mul_le_mul_left hfinal hn

end CallProg

namespace Twin

open CallTree

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Twin of `OuterPivot.randomStepTree`. -/
def randomStepTree (Q : ℕ → ℕ) (n : ℕ) (U : Finset V) (s : V) (values : V → Option ℝ)
    (levels : ℕ) : CallTree V Q (Output V levels) (stepBudget Q n levels) :=
  random (thresholdSeedPMF V levels) (fun seed =>
    (CallProg.compile Q (CallProg.stepCall U s values levels seed) (stepBudget Q n levels)).map
      (fun output => output.getD (Output.empty levels)))

/-- Twin of `sampledGuideContinuation`. -/
def sampledGuideContinuation (M : ℕ) (Q : ℕ → ℕ) (n samples trials levels scale exponent : ℕ)
    (U : Finset V) (s : U) (hvn : Fintype.card V ≤ n) (L : List (RootedTree U)) :
    CallTree V Q (V → Option ℝ)
      (samples * guideTwoBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) :=
  if hlen : L.length = samples then
    ((CallTree.randomTable (fun _ => none) (fun i : Fin samples =>
      guideTwoTree M Q n trials levels scale exponent (Nat.clog 2 (n + 1))
        (terminalGuide U s (guideListEntry L hlen i)) hvn)).map mergeGuideValues).cast (by simp)
  else up (Nat.zero_le _) (CallTree.pure (PMF.pure (fun _ => none)))

/-- Twin of `sampledGuideTree`. The guide sample makes no query. -/
def sampledGuideTree (M : ℕ) (Q : ℕ → ℕ) (n samples trials levels scale exponent : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : U) (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U)
    (hvn : Fintype.card V ≤ n) :
    CallTree V Q (V → Option ℝ)
      (samples * guideTwoBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) :=
  ((CallTree.ofRTree (Q := Q) (guideSampleProgram K U hU hpos samples)).bind
    (sampledGuideContinuation M Q n samples trials levels scale exponent U s hvn)).cast (by omega)

/-- Twin of `bucketSourceTree`. -/
def bucketSourceTree (M : ℕ) (Q : ℕ → ℕ) (n samples trials levels scale exponent : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) (j : ℕ) :
    CallTree V Q (V → Option ℝ)
      (samples * guideTwoBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) :=
  if hne : (sourceBucket K U s j).Nonempty then
    sampledGuideTree M Q n samples trials levels scale exponent K (bucketTerminals K U s j)
      ⟨s, Finset.mem_insert_self _ _⟩ (bucketTerminals_two_le K U s j hne)
      (bucketTerminals_pos K U s j hne) hvn
  else up (Nat.zero_le _) (CallTree.pure (PMF.pure (fun _ => none)))

/-- Twin of `singleSourceTree`. -/
def singleSourceTree (M : ℕ) (Q : ℕ → ℕ) (n samples trials levels scale exponent : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) :
    CallTree V Q (V → Option ℝ) (singleSourceBudget M Q n samples trials levels scale exponent) :=
  ((CallTree.randomTable (fun _ => none) (fun j : Fin (bucketCount M) =>
    bucketSourceTree M Q n samples trials levels scale exponent K U s hvn j.val)).map
      (mergeBucketValues K U s)).cast (by simp [singleSourceBudget])

/-- Twin of `sourcePivotFor`. -/
def sourcePivotFor (M : ℕ) (Q : ℕ → ℕ) (n samples trials guideLevels scale exponent pivotLevels : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) :
    CallTree V Q (SourcePivotOutput V pivotLevels)
      (sourcePivotBudget M Q n samples trials guideLevels scale exponent pivotLevels) :=
  (singleSourceTree M Q n samples trials guideLevels scale exponent K U s hvn).bind
    (fun values => (randomStepTree Q n U s values pivotLevels).map
      (fun output => ⟨s, values, output⟩))

/-- Twin of `sourcePivotTree`. -/
def sourcePivotTree (M : ℕ) (Q : ℕ → ℕ) (n samples trials guideLevels scale exponent pivotLevels : ℕ)
    (K : WeightedGraph V) (U : Finset V) (hU : U.Nonempty) (hvn : Fintype.card V ≤ n) :
    CallTree V Q (SourcePivotOutput V pivotLevels)
      (sourcePivotBudget M Q n samples trials guideLevels scale exponent pivotLevels) :=
  random (PMF.uniformOfFinset U hU) (fun s =>
    sourcePivotFor M Q n samples trials guideLevels scale exponent pivotLevels K U s hvn)

/-! ### Bridges -/

section Bridges

variable {M n : ℕ} {Q QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)

theorem randomStepTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V)
    (values : V → Option ℝ) (levels : ℕ) :
    interpIdeal G (randomStepTree Q n U s values levels) =
      (OuterPivot.randomStepTree E n U s values levels).eval G.cut := by
  rw [randomStepTree_eval E hvn hQE, randomStepTree, interpIdeal_random, ← PMF.bind_pure_comp]
  congr 1
  funext seed
  rw [interpIdeal_compile_map G _ _ _ (CallProg.stepCall_idealCost hvn hQ U s values levels seed G),
    Option.getD_some, Function.comp_apply, CallProg.step_idealEval E G hG]

theorem sampledGuideContinuation_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (samples trials levels scale exponent : ℕ)
    (U : Finset V) (s : U) (hvn : Fintype.card V ≤ n) (L : List (RootedTree U)) :
    interpIdeal G (sampledGuideContinuation M Q n samples trials levels scale exponent U s hvn L) =
      (GHReduction.sampledGuideContinuation E n samples trials levels scale exponent U s hvn L).eval
        G.cut := by
  by_cases hlen : L.length = samples
  · simp only [sampledGuideContinuation, GHReduction.sampledGuideContinuation, hlen, dite_true,
      interpIdeal_cast, RTree.eval_cast]
    exact map_eq _ (randomTable_eq _ (fun i =>
      guideTwoTree_eq E hQ hQE trials levels scale exponent _ G hG _ hvn))
  · simp [sampledGuideContinuation, GHReduction.sampledGuideContinuation, hlen]

theorem sampledGuideTree_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (samples trials levels scale exponent : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : U) (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U)
    (hvn : Fintype.card V ≤ n) :
    interpIdeal G (sampledGuideTree M Q n samples trials levels scale exponent K U s hU hpos hvn) =
      (GHReduction.sampledGuideTree E n samples trials levels scale exponent K U s hU hpos hvn).eval
        G.cut := by
  simp only [sampledGuideTree, GHReduction.sampledGuideTree, interpIdeal_cast, RTree.eval_cast]
  exact bind_eq (interpIdeal_ofRTree G _) (fun L _ =>
    sampledGuideContinuation_eq E hQ hQE G hG samples trials levels scale exponent U s hvn L)

theorem bucketSourceTree_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (samples trials levels scale exponent : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) (j : ℕ) :
    interpIdeal G (bucketSourceTree M Q n samples trials levels scale exponent K U s hvn j) =
      (GHReduction.bucketSourceTree E n samples trials levels scale exponent K U s hvn j).eval
        G.cut := by
  by_cases hne : (sourceBucket K U s j).Nonempty
  · simp only [bucketSourceTree, GHReduction.bucketSourceTree, hne, dite_true]
    exact sampledGuideTree_eq E hQ hQE G hG samples trials levels scale exponent K _ _ _ _ hvn
  · simp [bucketSourceTree, GHReduction.bucketSourceTree, hne]

theorem singleSourceTree_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (G : WeightedGraph V) (hG : InputPromise M G) (samples trials levels scale exponent : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) :
    interpIdeal G (singleSourceTree M Q n samples trials levels scale exponent K U s hvn) =
      (GHReduction.singleSourceTree E n samples trials levels scale exponent K U s hvn).eval
        G.cut := by
  unfold singleSourceTree GHReduction.singleSourceTree singleSourceBudget
  rw [interpIdeal_cast, RTree.eval_cast]
  exact map_eq _ (randomTable_eq _ (fun j =>
    bucketSourceTree_eq E hQ hQE G hG samples trials levels scale exponent K U s hvn j.val))

theorem sourcePivotFor_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (G : WeightedGraph V) (hG : InputPromise M G)
    (samples trials guideLevels scale exponent pivotLevels : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) :
    interpIdeal G (sourcePivotFor M Q n samples trials guideLevels scale exponent pivotLevels K U s hvn) =
      (GHReduction.sourcePivotFor E n samples trials guideLevels scale exponent pivotLevels
        K U s hvn).eval G.cut :=
  bind_eq (singleSourceTree_eq E hQ hQE G hG samples trials guideLevels scale exponent K U s hvn)
    (fun values _ => map_eq _ (randomStepTree_eq E hvn hQ hQE G hG U s values pivotLevels))

theorem sourcePivotTree_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (G : WeightedGraph V) (hG : InputPromise M G)
    (samples trials guideLevels scale exponent pivotLevels : ℕ)
    (K : WeightedGraph V) (U : Finset V) (hU : U.Nonempty) (hvn : Fintype.card V ≤ n) :
    interpIdeal G
        (sourcePivotTree M Q n samples trials guideLevels scale exponent pivotLevels K U hU hvn) =
      (GHReduction.sourcePivotTree E n samples trials guideLevels scale exponent pivotLevels
        K U hU hvn).eval G.cut :=
  random_eq _ (fun s _ =>
    sourcePivotFor_eq E hQ hQE G hG samples trials guideLevels scale exponent pivotLevels K U s hvn)

end Bridges

/-! ### Realized charged costs -/

section Costs

variable {M n : ℕ} {Q : ℕ → ℕ}

theorem randomStepTree_cost_scaled (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    {out : Output V levels × ℕ}
    (hout : out ∈ (idealRun G (randomStepTree Q n U s values levels)).support) :
    n * out.2 ≤ Fintype.card V * stepBudget Q n levels := by
  simp only [randomStepTree, idealRun_random, idealRun_map] at hout
  obtain ⟨seed, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  rw [idealRun_compile G _ _ (CallProg.stepCall_idealCost hvn hQ U s values levels seed G),
    PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hrun
  rw [hrun]
  simpa only [stepBudget, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    CallProg.stepCall_idealCost_scaled hvn hQ U s values levels seed G

theorem sampledGuideContinuation_cost_scaled (hQ : SizeRegular n Q)
    (samples trials levels scale exponent : ℕ) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : U) (hvn : Fintype.card V ≤ n) (L : List (RootedTree U))
    {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G
      (sampledGuideContinuation M Q n samples trials levels scale exponent U s hvn L)).support) :
    n * p.2 ≤ Fintype.card V * (samples *
      guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) := by
  by_cases hlen : L.length = samples
  · simp only [sampledGuideContinuation, hlen, dite_true, idealRun_cast] at hp
    apply idealRun_map_cost G _ _ n _ ?_ hp
    intro out hout
    have h := CallTree.randomTable_cost G (fun _ => none)
      (fun i : Fin samples => guideTwoTree M Q n trials levels scale exponent
        (Nat.clog 2 (n + 1)) (terminalGuide U s (guideListEntry L hlen i)) hvn)
      n (fun _ => Fintype.card V * guideTwoSharpBudget M Q n trials levels scale exponent
        (Nat.clog 2 (n + 1)))
      (fun i p hp => guideTwoTree_cost_linear hQ trials levels scale exponent _ G hG
        (terminalGuide U s (guideListEntry L hlen i)) hvn hp) hout
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id,
      Nat.mul_assoc, Nat.mul_left_comm] using h
  · simp only [sampledGuideContinuation, hlen, dite_false, idealRun_up] at hp
    simp [idealRun_pure_cost G _ hp]

theorem sampledGuideTree_cost_scaled (hQ : SizeRegular n Q)
    (samples trials levels scale exponent : ℕ) (G K : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : U) (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U)
    (hvn : Fintype.card V ≤ n) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G
      (sampledGuideTree M Q n samples trials levels scale exponent K U s hU hpos hvn)).support) :
    n * p.2 ≤ Fintype.card V * (samples *
      guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) := by
  rw [sampledGuideTree, idealRun_cast] at hp
  have h := idealRun_bind_cost G _ _ n 0 _
    (fun p hp => by rw [Nat.le_zero.mp (idealRun_cost_le G _ hp)]; simp)
    (fun first _ p hp => sampledGuideContinuation_cost_scaled hQ samples trials levels scale
      exponent G hG U s hvn first.1 hp) hp
  simpa only [zero_add] using h

theorem bucketSourceTree_cost_scaled (hQ : SizeRegular n Q)
    (samples trials levels scale exponent : ℕ) (G K : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) (j : ℕ) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G
      (bucketSourceTree M Q n samples trials levels scale exponent K U s hvn j)).support) :
    n * p.2 ≤ Fintype.card V * (samples *
      guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) := by
  by_cases hne : (sourceBucket K U s j).Nonempty
  · simp only [bucketSourceTree, hne, dite_true] at hp
    exact sampledGuideTree_cost_scaled hQ samples trials levels scale exponent G K hG
      _ _ _ _ hvn hp
  · simp only [bucketSourceTree, hne, dite_false, idealRun_up] at hp
    simp [idealRun_pure_cost G _ hp]

theorem singleSourceTree_cost_scaled (hQ : SizeRegular n Q)
    (samples trials levels scale exponent : ℕ) (G K : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G
      (singleSourceTree M Q n samples trials levels scale exponent K U s hvn)).support) :
    n * p.2 ≤ Fintype.card V * singleSourceSharpBudget M Q n samples trials levels scale exponent := by
  unfold singleSourceTree singleSourceBudget at hp
  rw [idealRun_cast] at hp
  apply idealRun_map_cost G _ _ n _ ?_ hp
  intro out hout
  have h := CallTree.randomTable_cost G (fun _ => none)
    (fun j : Fin (bucketCount M) =>
      bucketSourceTree M Q n samples trials levels scale exponent K U s hvn j.val)
    n (fun _ => Fintype.card V * (samples *
      guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))))
    (fun j p hp => bucketSourceTree_cost_scaled hQ samples trials levels scale exponent G K hG
      U s hvn j.val hp) hout
  simpa only [singleSourceSharpBudget, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, Nat.mul_assoc, Nat.mul_left_comm] using h

theorem sourcePivotFor_cost_scaled (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V)
    (hvn : Fintype.card V ≤ n) {out : SourcePivotOutput V levels × ℕ}
    (hout : out ∈ (idealRun G
      (sourcePivotFor M Q n samples trials guideLevels scale exponent levels K U s hvn)).support) :
    n * out.2 ≤ Fintype.card V *
      sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels := by
  unfold sourcePivotFor at hout
  have h := idealRun_bind_cost G _ _ n
    (Fintype.card V * singleSourceSharpBudget M Q n samples trials guideLevels scale exponent)
    (Fintype.card V * stepBudget Q n levels)
    (fun first hfirst => singleSourceTree_cost_scaled hQ samples trials guideLevels scale exponent
      G K hG U s hvn hfirst)
    (fun first _ next hnext => idealRun_map_cost G _ _ n _
      (fun step hstep => randomStepTree_cost_scaled hvn hQ G U s first.1 levels hstep)
      hnext) hout
  simpa only [sourcePivotSharpBudget, Nat.mul_add] using h

theorem sourcePivotTree_cost_scaled (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (hU : U.Nonempty)
    (hvn : Fintype.card V ≤ n) {out : SourcePivotOutput V levels × ℕ}
    (hout : out ∈ (idealRun G
      (sourcePivotTree M Q n samples trials guideLevels scale exponent levels K U hU hvn)).support) :
    n * out.2 ≤ Fintype.card V *
      sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels := by
  simp only [sourcePivotTree, idealRun_random] at hout
  obtain ⟨s, _, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  exact sourcePivotFor_cost_scaled hQ samples trials guideLevels scale exponent levels
    G K hG U s hvn hs

end Costs

end Twin
end
end CutQueryComplexity.GHReduction.Randomized
