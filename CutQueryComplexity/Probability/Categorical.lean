import CutQueryComplexity.Probability.Expectation

/-! # Finite weight-proportional draws

Zero-weight categories have probability zero. A positive total weight is
required explicitly, so no arbitrary outcome is chosen for an empty bucket.
-/

namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical ENNReal
variable {α : Type*} [Fintype α]

def categorical (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hpos : 0 < ∑ x, w x) : PMF α :=
  PMF.ofFintype (fun x => ENNReal.ofReal (w x / ∑ y, w y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => div_nonneg (hw x) hpos.le),
      ← Finset.sum_div, div_self (ne_of_gt hpos), ENNReal.ofReal_one])

@[simp] theorem categorical_apply (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hpos : 0 < ∑ x, w x) (x : α) :
    categorical w hw hpos x = ENNReal.ofReal (w x / ∑ y, w y) := rfl

@[simp] theorem mem_support_categorical (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hpos : 0 < ∑ x, w x) (x : α) :
    x ∈ (categorical w hw hpos).support ↔ 0 < w x := by
  rw [PMF.mem_support_iff, categorical_apply, ne_eq, ENNReal.ofReal_eq_zero,
    not_le, div_pos_iff_of_pos_right hpos]

theorem expect_categorical (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hpos : 0 < ∑ x, w x) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    expect (categorical w hw hpos) (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal ((∑ x, w x * f x) / ∑ x, w x) := by
  simp only [expect, tsum_fintype, categorical_apply]
  simp_rw [← ENNReal.ofReal_mul (div_nonneg (hw _) hpos.le)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
    mul_nonneg (div_nonneg (hw x) hpos.le) (hf x)), Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

end
end CutQueryComplexity.Probability
