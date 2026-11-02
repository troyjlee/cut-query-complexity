import CutQueryComplexity.BoundedFlowMinCut.Main
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The cap is `O(n^{3/2} log² n)` (M7)

With `t = ⌊√n⌋ + 1 ≤ 2√n` and `L ≥ 1`, `queryBudget n ≤ C n^{3/2} L²` for
`n ≥ 2` with the explicit `C = 2 · totalConst + 2` (`queryBudget_bound`); and
`L = ⌈log₂(2n+2)⌉ + 1 ≤ (5 / ln 2) ln n` (`logFactor_le_log`). The conclusion is
about the actual natural-number cap of the public program.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open Filter Asymptotics

theorem cutoffRoot_le_two_sqrt {n : ℕ} (hn : 1 ≤ n) :
    (cutoffRoot n : ℝ) ≤ 2 * Real.sqrt n := by
  unfold cutoffRoot
  push_cast
  have h1 : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have h2 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  linarith

theorem rpow_three_halves (n : ℕ) : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' (Nat.cast_nonneg n) (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- `queryBudget n ≤ C n^{3/2} L(n)²` with `C = 2 · totalConst + 2`. -/
theorem queryBudget_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      (queryBudget n : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ) * (logFactor n : ℝ) ^ 2 := by
  refine ⟨2 * totalConst + 2, by positivity, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
  have hL1 : (1 : ℝ) ≤ logFactor n := by exact_mod_cast one_le_logFactor n
  have ht := cutoffRoot_le_two_sqrt hn1
  rw [rpow_three_halves]
  set s := Real.sqrt n
  set L : ℝ := (logFactor n : ℝ)
  have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hns : (1 : ℝ) ≤ n * s := by nlinarith
  have hnsL : (1 : ℝ) ≤ n * s * L ^ 2 := by nlinarith
  have hn_le : (n : ℝ) ≤ n * s * L ^ 2 := by
    have : (1 : ℝ) ≤ s * L ^ 2 := by nlinarith
    nlinarith
  have htL : (n : ℝ) * cutoffRoot n * L ^ 2 ≤ 2 * (n * s * L ^ 2) := by
    have hnL : (0 : ℝ) ≤ n * L ^ 2 := by positivity
    nlinarith
  unfold queryBudget
  push_cast
  have hT : (0 : ℝ) ≤ totalConst := Nat.cast_nonneg _
  nlinarith

theorem logFactor_le_log {n : ℕ} (hn : 2 ≤ n) :
    (logFactor n : ℝ) ≤ (5 / Real.log 2) * Real.log (n : ℝ) := by
  have hn₂ : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog₂ : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM₁ : (1 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 2 by omega)
  have hc := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hM₁)
  have hceil := Real.natCeil_logb_natCast 2 (2 * n + 2)
  norm_num only [Nat.cast_ofNat] at hceil
  rw [hceil] at hc
  push_cast at hc
  have hsize : (logFactor n : ℝ) ≤ Real.logb 2 ((2 * n + 2 : ℕ) : ℝ) + 2 := by
    unfold logFactor
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
  have hfinal : (logFactor n : ℝ) * Real.log 2 ≤ 5 * Real.log (n : ℝ) := by
    linarith
  calc
    _ ≤ (5 * Real.log (n : ℝ)) / Real.log 2 := (le_div_iff₀ hlog₂).mpr hfinal
    _ = _ := by ring

/-- **`O(n^{3/2} log² n)` queries.** -/
theorem queryBudget_isBigO :
    (fun n : ℕ => (queryBudget n : ℝ)) =O[atTop]
      (fun n => (n : ℝ) ^ (3 / 2 : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := queryBudget_bound
  apply isBigO_iff.mpr
  refine ⟨C * (5 / Real.log 2) ^ 2, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn₁ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn₁
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  have hL := logFactor_le_log hn
  have hL0 : (0 : ℝ) ≤ logFactor n := Nat.cast_nonneg _
  have hsq : (logFactor n : ℝ) ^ 2 ≤ ((5 / Real.log 2) * Real.log (n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hL0 hL 2
  have hp : (0 : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  calc (queryBudget n : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ) * (logFactor n : ℝ) ^ 2 := hbound n hn
    _ ≤ C * (n : ℝ) ^ (3 / 2 : ℝ) * ((5 / Real.log 2) * Real.log (n : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hp
    _ = C * (5 / Real.log 2) ^ 2 * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.log (n : ℝ) ^ 2) := by ring

end
end CutQueryComplexity.BoundedFlowMinCut
