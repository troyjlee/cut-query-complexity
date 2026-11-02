import CutQueryComplexity.GHReduction.OuterPivot.Balance
import CutQueryComplexity.GHReduction.OuterPivot.Step
import CutQueryComplexity.GHReduction.ThresholdProgress

/-! # Expected removal by the actual maximum-coverage level

A successful canonical target is charged its entire terminal trace. At each
level these traces are disjoint. The public step selects the largest coverage,
so all levels together lose only a single factor `levels + 1`. The pivot average
is taken only in the semantic analysis; no program queries source vectors for
all possible pivots.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.OuterPivot
noncomputable section
open scoped Classical BigOperators ENNReal
open WeightedGraph Probability

variable {V : Type} [Fintype V] [DecidableEq V]

theorem successfulTargets_charge_level {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (D U : Finset V) (s : V)
    (values : V → Option ℝ) (levels : ℕ) (C : V → Finset V) (index : V → Fin (levels + 1))
    (hDU : D ⊆ U) (hsU : s ∈ U)
    (hC : ∀ v ∈ D, IsCanonicalSTCut G v s (C v))
    (hvalue : ∀ v ∈ D, values v = some (stValue G v s))
    (hsize : ∀ v ∈ D, 2 * (C v ∩ U).card ≤ U.card)
    (seed : ThresholdSeed V levels) (i : Fin (levels + 1)) :
    (∑ v ∈ successfulTargets D U C index i seed, (C v ∩ U).card) ≤
      ((Prog.eval G.cut (levelProgram family U
        (levelSample U s i.val seed) s values)).covered U).card := by
  let A := successfulTargets D U C index i seed
  have hA (v : V) (hv : v ∈ A) :
      v ∈ D ∧ index v = i ∧ UniqueSurvivor (C v ∩ U) v i.val seed := by
    obtain ⟨hvD, hindex, hhit⟩ := Finset.mem_filter.mp hv
    exact ⟨hvD, hindex, hindex ▸ hhit⟩
  have hdisj : (A : Set V).PairwiseDisjoint (fun v => C v ∩ U) := by
    intro v hv w hw hvw
    exact uniqueSurvivor_canonical_disjoint G U (hC v (hA v hv).1) (hC w (hA w hw).1)
      (hDU (hA v hv).1) (hDU (hA w hw).1) hvw seed (hA v hv).2.2 (hA w hw).2.2
  have hsub : A.biUnion (fun v => C v ∩ U) ⊆
      (Prog.eval G.cut (levelProgram family U (levelSample U s i.val seed) s values)).covered U := by
    intro x hx
    obtain ⟨v, hv, hx⟩ := Finset.mem_biUnion.mp hx
    have hcanon := hC v (hA v hv).1
    have htrace : C v ∩ levelSample U s i.val seed = {v} := by
      rw [Finset.inter_comm]
      exact uniqueSurvivor_trace U (C v) s seed
        (Finset.mem_inter.mpr ⟨hcanon.1.1, hDU (hA v hv).1⟩) hcanon.1.2.1 (hA v hv).2.2
    exact levelProgram_hit family G hG values (source_mem_levelSample hsU i.val seed)
      (hDU (hA v hv).1) hcanon htrace (hvalue v (hA v hv).1) (hsize v (hA v hv).1) hx
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card hsub

theorem stepProgram_charge {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (D U : Finset V) (s : V)
    (values : V → Option ℝ) (levels : ℕ) (C : V → Finset V) (index : V → Fin (levels + 1))
    (hDU : D ⊆ U) (hsU : s ∈ U)
    (hC : ∀ v ∈ D, IsCanonicalSTCut G v s (C v))
    (hvalue : ∀ v ∈ D, values v = some (stValue G v s))
    (hsize : ∀ v ∈ D, 2 * (C v ∩ U).card ≤ U.card) (seed : ThresholdSeed V levels) :
    (∑ v ∈ D, if UniqueSurvivor (C v ∩ U) v (index v).val seed
      then (C v ∩ U).card else 0) ≤
        (levels + 1) * ((Prog.eval G.cut (stepProgram family U s values levels seed)).batch.covered U).card := by
  have he : (∑ v ∈ D, if UniqueSurvivor (C v ∩ U) v (index v).val seed
        then (C v ∩ U).card else 0) =
      ∑ i : Fin (levels + 1), ∑ v ∈ successfulTargets D U C index i seed, (C v ∩ U).card := by
    simp only [successfulTargets, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hh : UniqueSurvivor (C v ∩ U) v (index v).val seed <;> simp [hh]
  rw [he]
  calc
    _ ≤ ∑ i : Fin (levels + 1), ((Prog.eval G.cut
        (levelProgram family U (levelSample U s i.val seed) s values)).covered U).card :=
      Finset.sum_le_sum (fun i _ => successfulTargets_charge_level family G hG D U s values
        levels C index hDU hsU hC hvalue hsize seed i)
    _ ≤ ∑ _i : Fin (levels + 1),
        ((Prog.eval G.cut (stepProgram family U s values levels seed)).batch.covered U).card :=
      Finset.sum_le_sum (fun i _ => level_coverage_le_step family U s values levels seed G.cut i)
    _ = _ := by simp

/-- This is an expectation of the concrete program, not a supplied progress
oracle. The canonical family `C` serves only as a proof witness. -/
theorem stepProgram_expected_progress {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (D U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ) (C : V → Finset V)
    (hlevels : thresholdLevels U.card ≤ levels) (hDU : D ⊆ U) (hsU : s ∈ U)
    (hC : ∀ v ∈ D, IsCanonicalSTCut G v s (C v))
    (hvalue : ∀ v ∈ D, values v = some (stValue G v s))
    (hsize : ∀ v ∈ D, 2 * (C v ∩ U).card ≤ U.card) :
    (D.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) ≤ (levels + 1 : ℕ) *
      expect (thresholdSeedPMF V levels) (fun seed =>
        (((Prog.eval G.cut (stepProgram family U s values levels seed)).batch.covered U).card : ℝ≥0∞)) := by
  let index : V → Fin (levels + 1) := fun v =>
    ⟨hitLevel (C v ∩ U).card, Nat.lt_succ_of_le
      ((hitLevel_le (Finset.card_le_card Finset.inter_subset_right)).trans hlevels)⟩
  let score (seed : ThresholdSeed V levels) : ℝ≥0∞ :=
    ∑ v ∈ D, if UniqueSurvivor (C v ∩ U) v (index v).val seed
      then ((C v ∩ U).card : ℝ≥0∞) else 0
  have hlower : (D.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) ≤
      expect (thresholdSeedPMF V levels) score := by
    rw [show score = (fun seed => ∑ v ∈ D,
      if UniqueSurvivor (C v ∩ U) v (index v).val seed
        then ((C v ∩ U).card : ℝ≥0∞) else 0) from rfl, expect_sum]
    calc
      _ = ∑ _v ∈ D, ENNReal.ofReal (1 / 8 : ℝ) := by simp [nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        rw [expect_indicator]
        exact uniqueSurvivor_hitLevel (C v ∩ U)
          (Finset.mem_inter.mpr ⟨(hC v hv).1.1, hDU hv⟩)
          (by exact Nat.le_of_lt_succ (index v).isLt)
  have hupper : expect (thresholdSeedPMF V levels) score ≤
      expect (thresholdSeedPMF V levels) (fun seed => (levels + 1 : ℕ) *
        (((Prog.eval G.cut (stepProgram family U s values levels seed)).batch.covered U).card : ℝ≥0∞)) := by
    apply expect_mono_on_support
    intro seed hseed
    have h := stepProgram_charge family G hG D U s values levels C index
      hDU hsU hC hvalue hsize seed
    have hcast := (Nat.cast_le (α := ℝ≥0∞)).mpr h
    simpa only [score, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul] using hcast
  exact hlower.trans (hupper.trans_eq (expect_const_mul _ _ _))

theorem balanced_expected_progress {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels) (hsU : s ∈ U)
    (hvalues : ∀ v ∈ U.erase s, values v = some (stValue G v s)) :
    ((balancedTargets G U s).card : ℝ≥0∞) ≤ (8 * (levels + 1) : ℕ) *
      expect (thresholdSeedPMF V levels) (fun seed =>
        (((Prog.eval G.cut (stepProgram family U s values levels seed)).batch.covered U).card : ℝ≥0∞)) := by
  have h := stepProgram_expected_progress family G hG (balancedTargets G U s) U s values levels
    (fun v => canonicalShore G v s) hlevels
    ((balancedTargets_subset G U s).trans (Finset.erase_subset _ _)) hsU
    (fun v hv => canonicalShore_correct G ((mem_balancedTargets G U s v).mp hv).1)
    (fun v hv => hvalues v (balancedTargets_subset G U s hv))
    (fun v hv => ((mem_balancedTargets G U s v).mp hv).2.2)
  have hc : (8 : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) = 1 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8)]
    norm_num
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc
    _ = 8 * (((balancedTargets G U s).card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ)) := by
      rw [mul_left_comm, hc, mul_one]
    _ ≤ 8 * ((levels + 1 : ℕ) * expect (thresholdSeedPMF V levels) (fun seed =>
        (((Prog.eval G.cut (stepProgram family U s values levels seed)).batch.covered U).card : ℝ≥0∞))) :=
      mul_le_mul_right h 8
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc]

/-- The expected progress belongs to the actual capped randomized program.
Only the vector for this fixed pivot is an argument of that program. -/
theorem randomStepTree_expected_progress {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V)
    (values : V → Option ℝ) (levels : ℕ) (hlevels : thresholdLevels U.card ≤ levels)
    (hsU : s ∈ U) (hvalues : ∀ v ∈ U.erase s, values v = some (stValue G v s)) :
    ((balancedTargets G U s).card : ℝ≥0∞) ≤ (8 * (levels + 1) : ℕ) *
      expect ((randomStepTree family n U s values levels).eval G.cut)
        (fun output => ((output.batch.covered U).card : ℝ≥0∞)) := by
  rw [randomStepTree_eval family hvn hQ, expect_map]
  exact balanced_expected_progress family G hG U s values levels hlevels hsU hvalues

/-- Semantic output law of a uniform public pivot followed by its actual
finite seed. `values` describes the already-obtained vector in each branch;
it is not a source-value solver nor an input to an outer GH algorithm. -/
def pivotOutputLaw {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (read : Finset V → ℝ) : PMF (Output V levels) :=
  (PMF.uniformOfFinset U hU).bind (fun s =>
    (thresholdSeedPMF V levels).map (fun seed =>
      Prog.eval read (stepProgram family U s (values s) levels seed)))

theorem pivot_expected_removal {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels)
    (hvalues : ∀ s ∈ U, ∀ v ∈ U.erase s, values s v = some (stValue G v s)) :
    ((U.card - 1 : ℕ) : ℝ≥0∞) ≤ (16 * (levels + 1) : ℕ) *
      expect (pivotOutputLaw family U hU values levels G.cut)
        (fun output => ((output.batch.covered U).card : ℝ≥0∞)) := by
  have hprogress : expect (PMF.uniformOfFinset U hU)
      (fun s => ((balancedTargets G U s).card : ℝ≥0∞)) ≤
      expect (PMF.uniformOfFinset U hU) (fun s => (8 * (levels + 1) : ℕ) *
        expect (thresholdSeedPMF V levels) (fun seed =>
          (((Prog.eval G.cut (stepProgram family U s (values s) levels seed)).batch.covered U).card : ℝ≥0∞))) := by
    apply expect_mono_on_support
    intro s hs
    have hsU := (PMF.mem_support_uniformOfFinset_iff _ _).mp hs
    exact balanced_expected_progress family G hG U s (values s) levels hlevels hsU (hvalues s hsU)
  rw [expect_const_mul] at hprogress
  have h := (pivot_balance G U hU).trans (mul_le_mul_right hprogress 2)
  simpa only [pivotOutputLaw, expect_bind, expect_map, Nat.cast_mul, Nat.cast_ofNat,
    ← mul_assoc, show (2 : ℝ≥0∞) * 8 = 16 by norm_num] using h

/-- Conservative literal denominator reserved by the transfer contract. -/
def removalDenominator (levels : ℕ) : ℕ := 32 * (levels + 1) ^ 2

theorem pivot_expected_removal_literal {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels)
    (hvalues : ∀ s ∈ U, ∀ v ∈ U.erase s, values s v = some (stValue G v s)) :
    ((U.card - 1 : ℕ) : ℝ≥0∞) ≤ (removalDenominator levels : ℝ≥0∞) *
      expect (pivotOutputLaw family U hU values levels G.cut)
        (fun output => ((output.batch.covered U).card : ℝ≥0∞)) := by
  apply (pivot_expected_removal family G hG U hU values levels hlevels hvalues).trans
  apply mul_le_mul_left
  have h : 16 * (levels + 1) ≤ removalDenominator levels := by
    unfold removalDenominator
    nlinarith [Nat.zero_le levels]
  exact_mod_cast h

#print axioms successfulTargets_charge_level
#print axioms stepProgram_charge
#print axioms stepProgram_expected_progress
#print axioms balanced_expected_progress
#print axioms randomStepTree_expected_progress
#print axioms pivot_expected_removal
#print axioms pivot_expected_removal_literal

end
end CutQueryComplexity.GHReduction.OuterPivot
