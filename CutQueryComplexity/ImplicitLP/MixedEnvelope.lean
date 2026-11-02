import CutQueryComplexity.ImplicitLP.Movement

set_option autoImplicit false

/-! # The mixed-norm envelope `N_w ≤ T₀ ‖·‖_∞` (D7/D8)

`prop_batch` takes `hT : ∀ v, N_w(v) ≤ T₀ ‖v‖_∞` at the current weights. It follows from the
weight sum alone: `‖v‖_w ≤ √(Σw) ‖v‖_∞`, so `T₀ = 1 + C √(Σw)` works (`mixed_le_sum`). With
`Σw ≤ 4r` from `weight_invariants`, the public `T₀ = 1 + C√(4r)` works at every batch
(`mixed_le_public`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Finset

noncomputable section

variable {M : ℕ}

theorem wnorm_le_sqrt_sum {w : Fin M → ℝ} (hw : ∀ i, 0 ≤ w i) (v : Fin M → ℝ) :
    wnorm w v ≤ Real.sqrt (∑ i, w i) * ‖v‖ := by
  have h : ∑ i, w i * v i ^ 2 ≤ (∑ i, w i) * ‖v‖ ^ 2 := by
    rw [sum_mul]
    refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw i)
    have := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [wnorm, ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (sum_nonneg fun i _ => hw i)]
  exact Real.sqrt_le_sqrt h

/-- **`N_w ≤ (1 + C√(Σw)) ‖·‖_∞`.** -/
theorem mixed_le_sum {C : ℝ} (hC : 0 ≤ C) {w : Fin M → ℝ} (hw : ∀ i, 0 ≤ w i)
    (v : Fin M → ℝ) : mixed C w v ≤ (1 + C * Real.sqrt (∑ i, w i)) * ‖v‖ := by
  have := mul_le_mul_of_nonneg_left (wnorm_le_sqrt_sum hw v) hC
  rw [mixed]; nlinarith [norm_nonneg v]

/-- **The public envelope:** `Σw ≤ 4r` gives `N_w ≤ (1 + C√(4r)) ‖·‖_∞`. -/
theorem mixed_le_public {C : ℝ} (hC : 0 ≤ C) {w : Fin M → ℝ} (hw : ∀ i, 0 ≤ w i) {r : ℝ}
    (hsum : ∑ i, w i ≤ 4 * r) (v : Fin M → ℝ) :
    mixed C w v ≤ (1 + C * Real.sqrt (4 * r)) * ‖v‖ := by
  refine (mixed_le_sum hC hw v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
  have := Real.sqrt_le_sqrt hsum
  nlinarith

end

end ImplicitLP
end CutQueryComplexity
