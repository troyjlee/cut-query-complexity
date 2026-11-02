import CutQueryComplexity.GHReduction.SourcePivot
import CutQueryComplexity.GHReduction.OuterPivot.Depth

/-! # Progress for the actual source-value and pivot program

The potential below is an analysis quantity: it becomes zero when this call's
source-value computation fails. It does not appear in the query program.
The selected pivot remains uniform before the source call; no distribution is
conditioned on future correctness. The source failure probability is bounded
separately in `SourcePivot`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability OuterPivot

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A failed source-value call stops this analysis path, not the actual
algorithm. On a good call this is the actual residual terminal excess. -/
def sourcePivotPotential (G : WeightedGraph V) (U : Finset V) {levels : ℕ}
    (out : SourcePivotOutput V levels) : ℕ :=
  if SourceValuesSuccess G U out.pivot out.values then excess (remaining U out.step) else 0

theorem sourcePivotPotential_of_good (G : WeightedGraph V) (U : Finset V) {levels : ℕ}
    (out : SourcePivotOutput V levels) (hg : SourcePivotGood G U out) :
    sourcePivotPotential G U out = excess (remaining U out.step) := by
  simp only [sourcePivotPotential, hg.2.1, ite_true]

theorem sourcePivotPotential_le (G : WeightedGraph V) (U : Finset V) {levels : ℕ}
    (out : SourcePivotOutput V levels) : sourcePivotPotential G U out ≤ excess U := by
  by_cases hg : SourceValuesSuccess G U out.pivot out.values
  · simp only [sourcePivotPotential, hg, ite_true, excess]
    exact Nat.sub_le_sub_right (Finset.card_le_card (remaining_subset U out.step)) 1
  · simp [sourcePivotPotential, hg]

/-- Every fixed returned value vector satisfies the same affine progress
bound. For a failed vector the killed potential is zero; for a good vector
the concrete fresh isolating program supplies the removal term. -/
theorem randomStep_sourcePotential_charge {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V)
    (hs : s ∈ U) (values : V → Option ℝ) (levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels) :
    (8 * (levels + 1) : ℕ) *
      expect ((randomStepTree family n U s values levels).eval G.cut)
        (fun step => (sourcePivotPotential G U (SourcePivotOutput.mk s values step) : ℝ≥0∞)) +
      ((balancedTargets G U s).card : ℝ≥0∞) ≤
        (8 * (levels + 1) : ℕ) * (excess U : ℝ≥0∞) := by
  by_cases hg : SourceValuesSuccess G U s values
  · have hexact : ∀ v ∈ U.erase s, values v = some (stValue G v s) := by
      intro v hv
      exact hg.2 v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1
    let P := (randomStepTree family n U s values levels).eval G.cut
    have hsum : expect P (fun step => (excess (remaining U step) : ℝ≥0∞)) +
        expect P (fun step => ((step.batch.covered U).card : ℝ≥0∞)) = (excess U : ℝ≥0∞) := by
      rw [← expect_add]
      calc
        _ = expect P (fun _ => (excess U : ℝ≥0∞)) := by
          apply expect_congr_on_support
          intro step hstep
          have hform := (randomStepTree_correct family hvn hQ G U s values levels hexact hstep).1
          exact_mod_cast remaining_accounting hs hform
        _ = _ := expect_const _ _
    have hcharge := randomStepTree_expected_progress family hvn hQ G hG U s values levels
      hlevels hs hexact
    simp only [sourcePivotPotential, hg, ite_true]
    calc
      _ ≤ (8 * (levels + 1) : ℕ) * expect P (fun step => (excess (remaining U step) : ℝ≥0∞)) +
          (8 * (levels + 1) : ℕ) * expect P (fun step => ((step.batch.covered U).card : ℝ≥0∞)) :=
        add_le_add le_rfl hcharge
      _ = _ := by rw [← mul_add, hsum]
  · have hb : (balancedTargets G U s).card ≤ excess U := by
      simpa only [Finset.card_erase_of_mem hs, excess] using
        Finset.card_le_card (balancedTargets_subset G U s)
    have hd : 1 ≤ 8 * (levels + 1) := by omega
    have hn : (balancedTargets G U s).card ≤ 8 * (levels + 1) * excess U := by
      nlinarith
    simpa only [sourcePivotPotential, hg, ite_false, Nat.cast_zero, expect_const,
      mul_zero, zero_add, Nat.cast_mul] using (Nat.cast_le (α := ℝ≥0∞)).mpr hn

theorem sourcePivotFor_potential_charge {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V) (hs : s ∈ U)
    (samples trials guideLevels scale exponent levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels) :
    (8 * (levels + 1) : ℕ) *
      expect ((sourcePivotFor family n samples trials guideLevels scale exponent levels K U s hvn).eval G.cut)
        (fun out => (sourcePivotPotential G U out : ℝ≥0∞)) +
      ((balancedTargets G U s).card : ℝ≥0∞) ≤
        (8 * (levels + 1) : ℕ) * (excess U : ℝ≥0∞) := by
  rw [sourcePivotFor_eval, expect_bind]
  simp only [expect_map]
  calc
    _ = expect ((singleSourceTree family n samples trials guideLevels scale exponent K U s hvn).eval G.cut)
        (fun values => (8 * (levels + 1) : ℕ) *
          expect ((randomStepTree family n U s values levels).eval G.cut)
            (fun step => (sourcePivotPotential G U (SourcePivotOutput.mk s values step) : ℝ≥0∞)) +
          ((balancedTargets G U s).card : ℝ≥0∞)) := by
      simp only [expect_add, expect_const_mul, expect_const]
    _ ≤ _ := expect_le_of_le_on_support _ (fun values _ =>
      randomStep_sourcePotential_charge family hvn hQ G hG U s hs values levels hlevels)

/-- Uniform pivot averaging takes place outside its actual adaptive source
solve. In particular its source success probability may depend on the pivot. -/
theorem sourcePivotTree_potential_charge {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (hU : U.Nonempty)
    (samples trials guideLevels scale exponent levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels) :
    (16 * (levels + 1) : ℕ) *
      expect ((sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn).eval G.cut)
        (fun out => (sourcePivotPotential G U out : ℝ≥0∞)) + (excess U : ℝ≥0∞) ≤
      (16 * (levels + 1) : ℕ) * (excess U : ℝ≥0∞) := by
  let P := PMF.uniformOfFinset U hU
  let f (s : V) := expect
    ((sourcePivotFor family n samples trials guideLevels scale exponent levels K U s hvn).eval G.cut)
    (fun out => (sourcePivotPotential G U out : ℝ≥0∞))
  have haverage : (8 * (levels + 1) : ℕ) * expect P f +
      expect P (fun s => ((balancedTargets G U s).card : ℝ≥0∞)) ≤
      (8 * (levels + 1) : ℕ) * (excess U : ℝ≥0∞) := by
    rw [← expect_const_mul, ← expect_add]
    apply expect_le_of_le_on_support
    intro s hs
    exact sourcePivotFor_potential_charge family hvn hQ G K hG U s
      ((PMF.mem_support_uniformOfFinset_iff _ _).mp hs)
      samples trials guideLevels scale exponent levels hlevels
  have hbalance := pivot_balance G U hU
  have hlinear : 2 * ((8 * (levels + 1) : ℕ) * expect P f) + (excess U : ℝ≥0∞) ≤
      2 * ((8 * (levels + 1) : ℕ) * (excess U : ℝ≥0∞)) := by
    calc
      _ ≤ 2 * ((8 * (levels + 1) : ℕ) * expect P f) +
          2 * expect P (fun s => ((balancedTargets G U s).card : ℝ≥0∞)) :=
        add_le_add le_rfl hbalance
      _ = 2 * ((8 * (levels + 1) : ℕ) * expect P f +
          expect P (fun s => ((balancedTargets G U s).card : ℝ≥0∞))) := by
        exact (mul_add 2 _ _).symm
      _ ≤ _ := mul_le_mul' le_rfl haverage
  rw [sourcePivotTree_eval, expect_bind]
  simpa only [P, f, Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc,
    show (2 : ℝ≥0∞) * 8 = 16 by norm_num] using hlinear

/-- The same literal contraction rate as the outer-depth interface, now for
the actual program and a potential killed at source failures. -/
theorem sourcePivotTree_expected_potential {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (hU : U.Nonempty)
    (samples trials guideLevels scale exponent levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels) :
    expect ((sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn).eval G.cut)
      (fun out => (sourcePivotPotential G U out : ℝ≥0∞)) ≤
      contractionRate levels * (excess U : ℝ≥0∞) := by
  let P := (sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn).eval G.cut
  let r := expect P (fun out => (sourcePivotPotential G U out : ℝ≥0∞))
  have hrle : r ≤ (excess U : ℝ≥0∞) := expect_le_of_le_on_support P (fun out _ =>
    (Nat.cast_le (α := ℝ≥0∞)).mpr (sourcePivotPotential_le G U out))
  have hr : r ≠ ∞ := ne_of_lt (hrle.trans_lt (by simp))
  have hcharge := sourcePivotTree_potential_charge family hvn hQ G K hG U hU
    samples trials guideLevels scale exponent levels hlevels
  have hK : ((16 * (levels + 1) : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  change ((16 * (levels + 1) : ℕ) : ℝ≥0∞) * r + (excess U : ℝ≥0∞) ≤
    ((16 * (levels + 1) : ℕ) : ℝ≥0∞) * (excess U : ℝ≥0∞) at hcharge
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hK (by simp)) hcharge
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hK hr) (by simp)] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  change ((16 * (levels + 1) : ℕ) : ℝ) * r.toReal + (excess U : ℝ) ≤
    ((16 * (levels + 1) : ℕ) : ℝ) * (excess U : ℝ) at hreal
  have hrreal := ENNReal.toReal_mono (by simp) hrle
  simp only [ENNReal.toReal_natCast] at hrreal
  have hden : (16 * (levels + 1) : ℕ) ≤ removalDenominator levels := by
    unfold removalDenominator
    nlinarith [Nat.zero_le levels]
  have hdenreal : ((16 * (levels + 1) : ℕ) : ℝ) ≤ (removalDenominator levels : ℝ) := by
    exact_mod_cast hden
  have hlarge : (removalDenominator levels : ℝ) * r.toReal + (excess U : ℝ) ≤
      (removalDenominator levels : ℝ) * (excess U : ℝ) := by
    nlinarith
  apply (ENNReal.toReal_le_toReal hr
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))).mp
  simp only [ENNReal.toReal_mul, contractionRate,
    ENNReal.toReal_ofReal (contractionRate_arg_nonneg levels), ENNReal.toReal_natCast]
  have hpos : (0 : ℝ) < removalDenominator levels := by
    exact_mod_cast removalDenominator_pos levels
  have hcancel : (removalDenominator levels : ℝ) *
      (1 - (removalDenominator levels : ℝ)⁻¹) = (removalDenominator levels : ℝ) - 1 := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ (ne_of_gt hpos)]
  apply (mul_le_mul_iff_of_pos_left hpos).mp
  rw [← mul_assoc, hcancel]
  nlinarith

end
end CutQueryComplexity.GHReduction
