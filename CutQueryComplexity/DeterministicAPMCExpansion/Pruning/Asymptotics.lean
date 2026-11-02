import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Budget
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Strict subquadratic growth of the implemented query cap

The ceiling-logarithm factor is bounded explicitly by a natural logarithm.
Its fifth power is little-o of the remaining one-third power of the input
size. The conclusion applies to the actual natural-number budget from the
public query program; no asymptotic estimate is an input hypothesis.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open Filter Asymptotics
noncomputable section

theorem sizeLog_le_log {n : ℕ} (hn : 2 ≤ n) :
    (sizeLog n : ℝ) ≤ (5 / Real.log 2) * Real.log (n : ℝ) := by
  have hn₂ : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog₂ : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM₁ : (1 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 2 by omega)
  have hc := Nat.ceil_lt_add_one
    (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hM₁)
  have hceil := Real.natCeil_logb_natCast 2 (2 * n + 2)
  norm_num only [Nat.cast_ofNat] at hceil
  rw [hceil] at hc
  push_cast at hc
  have hsize : (sizeLog n : ℝ) ≤ Real.logb 2 ((2 * n + 2 : ℕ) : ℝ) + 2 := by
    unfold sizeLog
    push_cast
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hsize hlog₂.le
  simp only [add_mul, Real.logb, div_mul_cancel₀ _ hlog₂.ne'] at hscaled
  have hM : ((2 * n + 2 : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by
    push_cast
    linarith
  have hlogM := Real.log_le_log (by linarith : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ)) hM
  have hlog₄ : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have htwo : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
    simpa only [htwo, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hn₀.ne', hlog₄] at hlogM
  have hlogn := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn₂
  have hfinal : (sizeLog n : ℝ) * Real.log 2 ≤ 5 * Real.log (n : ℝ) := by
    linarith
  calc
    _ ≤ (5 * Real.log (n : ℝ)) / Real.log 2 := (le_div_iff₀ hlog₂).mpr hfinal
    _ = _ := by ring

theorem sizeLog_isBigO_log :
    (fun n : ℕ => (sizeLog n : ℝ)) =O[atTop] fun n => Real.log (n : ℝ) := by
  apply isBigO_iff.mpr
  refine ⟨5 / Real.log 2, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn₁ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Real.log_nonneg hn₁)]
  exact sizeLog_le_log hn

theorem sizeLog_fifth_isLittleO_third :
    (fun n : ℕ => (sizeLog n : ℝ) ^ 5) =o[atTop]
      fun n => (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hlog : (fun n : ℕ => Real.log (n : ℝ) ^ 5) =o[atTop]
      fun n => (n : ℝ) ^ (1 / 3 : ℝ) := by
    have h := (isLittleO_log_rpow_rpow_atTop ((5 : ℕ) : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 3)).comp_tendsto
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    simpa only [Function.comp_def, Real.rpow_natCast] using h
  exact (sizeLog_isBigO_log.pow 5).trans_isLittleO hlog

theorem headline_isLittleO_square :
    (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ) * (sizeLog n : ℝ) ^ 5) =o[atTop]
      fun n => (n : ℝ) ^ 2 := by
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) atTop).mul_isLittleO
    sizeLog_fifth_isLittleO_third
  apply h.congr_right
  intro n
  rw [← Real.rpow_add_of_nonneg (Nat.cast_nonneg n)
    (by norm_num : (0 : ℝ) ≤ 5 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  norm_num

theorem budget_isBigO_headline :
    (fun n : ℕ => (budget n : ℝ)) =O[atTop]
      fun n => (n : ℝ) ^ (5 / 3 : ℝ) * (sizeLog n : ℝ) ^ 5 := by
  apply isBigO_iff.mpr
  refine ⟨headlineConstant, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  simpa only [mul_assoc] using budget_le hn

/-- The public, all-transcript cap itself grows strictly slower than n². -/
theorem budget_isLittleO_square :
    (fun n : ℕ => (budget n : ℝ)) =o[atTop] fun n => (n : ℝ) ^ 2 :=
  budget_isBigO_headline.trans_isLittleO headline_isLittleO_square

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.sizeLog_le_log
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.headline_isLittleO_square
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget_isLittleO_square
