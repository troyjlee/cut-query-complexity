import CutQueryComplexity.GHReduction.ThresholdElimination
import Mathlib.Analysis.Complex.Exponential

/-! # Explicit high-probability threshold classification

The public number of rounds is logarithmic in the requested error scale.
Every round has a hard query cap; amplification changes the number of such
rounds, not a Markov-derived query threshold.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

def thresholdRounds (levels scale exponent : ℕ) : ℕ :=
  (8 * (levels + 1)) * ((exponent + 1) * Nat.clog 2 (scale + 2))

theorem thresholdRate_block (levels : ℕ) :
    thresholdRate levels ^ (8 * (levels + 1)) ≤ (2 : ℝ≥0∞)⁻¹ := by
  have hnat : (1 : ℝ) ≤ (8 * (levels + 1) : ℕ) := by
    exact_mod_cast (show 1 ≤ 8 * (levels + 1) by omega)
  have hpow := Real.one_sub_div_pow_le_exp_neg (n := 8 * (levels + 1)) (t := 1) hnat
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hexp
  have hreal : (1 - (8 * (levels + 1 : ℝ))⁻¹) ^ (8 * (levels + 1)) ≤ (2 : ℝ)⁻¹ := by
    have he : Real.exp (-1) ≤ (2 : ℝ)⁻¹ := by
      simpa only [Real.exp_neg, one_div] using hinv
    have hp : (1 - (8 * (levels + 1 : ℝ))⁻¹) ^ (8 * (levels + 1)) ≤ Real.exp (-1) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, one_div] using hpow
    exact hp.trans he
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa only [thresholdRate, ENNReal.ofReal_pow (thresholdRate_arg_nonneg levels),
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat] using h

theorem thresholdRate_rounds (levels scale exponent : ℕ) :
    thresholdRate levels ^ thresholdRounds levels scale exponent ≤
      (((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ (exponent + 1) := by
  have hlog : ((scale + 2 : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ Nat.clog 2 (scale + 2) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (scale + 2)
  have hinv : (2⁻¹ : ℝ≥0∞) ^ Nat.clog 2 (scale + 2) ≤ ((scale + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.inv_pow]
    exact ENNReal.inv_le_inv.mpr hlog
  calc
    _ = (thresholdRate levels ^ (8 * (levels + 1))) ^
        ((exponent + 1) * Nat.clog 2 (scale + 2)) := by rw [thresholdRounds, pow_mul]
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ ((exponent + 1) * Nat.clog 2 (scale + 2)) :=
      pow_le_pow_left₀ zero_le (thresholdRate_block levels) _
    _ = ((2⁻¹ : ℝ≥0∞) ^ Nat.clog 2 (scale + 2)) ^ (exponent + 1) := by
      rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := pow_le_pow_left₀ zero_le hinv _

theorem thresholdRate_rounds_mul_card {count scale : ℕ} (hcount : count ≤ scale)
    (levels exponent : ℕ) :
    thresholdRate levels ^ thresholdRounds levels scale exponent * (count : ℝ≥0∞) ≤
      (((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent := by
  let a : ℝ≥0∞ := ((scale + 2 : ℕ) : ℝ≥0∞)
  have ha0 : a ≠ 0 := by simp [a]
  have hat : a ≠ ∞ := by simp [a]
  have hca : (count : ℝ≥0∞) ≤ a := by
    change (count : ℝ≥0∞) ≤ ((scale + 2 : ℕ) : ℝ≥0∞)
    exact Nat.cast_le.mpr (by omega)
  calc
    _ ≤ a⁻¹ ^ (exponent + 1) * a :=
      mul_le_mul' (thresholdRate_rounds levels scale exponent) hca
    _ = a⁻¹ ^ exponent := by
      rw [pow_succ, mul_assoc, ENNReal.inv_mul_cancel ha0 hat, mul_one]
    _ = _ := rfl

variable {V : Type} [Fintype V] [DecidableEq V]

def thresholdClassifyTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (U : Finset V) (s : V) (W : ℝ) (levels scale exponent : ℕ) :
    RTree (Finset V) ℝ (Finset V)
      (thresholdRounds levels scale exponent * thresholdRoundBudget Q n levels) :=
  (thresholdRemainingTree family n s W levels (thresholdRounds levels scale exponent) U).map
    (fun remaining => U \ remaining)

/-- Classification never includes a vertex above the threshold. -/
theorem thresholdClassifyTree_subset {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (U : Finset V) (s : V) (W : ℝ) (levels scale exponent : ℕ)
    {covered : Finset V}
    (hc : covered ∈ ((thresholdClassifyTree family n U s W levels scale exponent).eval G.cut).support) :
    covered ⊆ lowTargets G U s W := by
  simp only [thresholdClassifyTree, RTree.eval_map] at hc
  obtain ⟨R, hR, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  have hinv := thresholdRemainingTree_invariant family hvn hQ G s W levels _ U hR
  intro x hx
  exact (mem_lowTargets G U s W x).mpr ⟨(Finset.mem_sdiff.mp hx).1, hinv.2.2 x hx⟩

/-- Exact classification with polynomially small failure probability. The
public error scale may include a later adaptive call count or capacity bound. -/
theorem thresholdClassifyTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hnscale : n ≤ scale) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (s : V) (W : ℝ) (levels exponent : ℕ)
    (hlevels : thresholdLevels n ≤ levels) (hsU : s ∈ U) :
    mass ((thresholdClassifyTree family n U s W levels scale exponent).eval G.cut)
      (fun covered => covered ≠ lowTargets G U s W) ≤
        (((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent := by
  simp only [thresholdClassifyTree, RTree.eval_map, mass_map]
  calc
    _ ≤ mass ((thresholdRemainingTree family n s W levels
        (thresholdRounds levels scale exponent) U).eval G.cut)
          (fun R => (lowTargets G R s W).Nonempty) := by
      apply mass_mono_on_support
      intro R hR hbad
      have hinv := thresholdRemainingTree_invariant family hvn hQ G s W levels _ U hR
      by_contra hempty
      apply hbad
      apply Finset.Subset.antisymm
      · intro x hx
        exact (mem_lowTargets G U s W x).mpr ⟨(Finset.mem_sdiff.mp hx).1, hinv.2.2 x hx⟩
      · intro x hx
        obtain ⟨hxU, hxs, hxW⟩ := (mem_lowTargets G U s W x).mp hx
        exact Finset.mem_sdiff.mpr ⟨hxU, fun hxR =>
          hempty ⟨x, (mem_lowTargets G R s W x).mpr ⟨hxR, hxs, hxW⟩⟩⟩
    _ ≤ thresholdRate levels ^ thresholdRounds levels scale exponent *
        ((lowTargets G U s W).card : ℝ≥0∞) :=
      thresholdRemainingTree_failure_le family hvn hQ G hG s W levels hlevels _ U hsU
    _ ≤ _ := thresholdRate_rounds_mul_card
      (((Finset.card_le_univ _).trans hvn).trans hnscale) levels exponent

end
end CutQueryComplexity.GHReduction
