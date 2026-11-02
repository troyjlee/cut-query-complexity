import CutQueryComplexity.Model.RandomizedComposition

/-! # Exact choice between two observed nonnegative masses -/
namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical NNReal ENNReal
variable {α : Type}

/-- Zero total mass chooses the right branch; positive mass is normalized exactly. -/
def chooseWeight (l r : ℝ≥0) : PMF Bool :=
  if h : l + r = 0 then PMF.pure false else
    PMF.ofFintype (fun b => (↑(if b then l else r) : ℝ≥0∞) * (↑(l + r) : ℝ≥0∞)⁻¹) (by
      have hn : (↑(l + r) : ℝ≥0∞) ≠ 0 := by exact_mod_cast h
      simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      rw [← add_mul, ← ENNReal.coe_add]
      exact ENNReal.mul_inv_cancel hn ENNReal.coe_ne_top)

/-- The unnormalized branch probability is its observed mass, including the zero case. -/
theorem chooseWeight_scaled (l r : ℝ≥0) (b : Bool) :
    (↑(l + r) : ℝ≥0∞) * chooseWeight l r b = ↑(if b then l else r) := by
  by_cases h : l + r = 0
  · have hl : l = 0 := (add_eq_zero.mp h).1
    have hr : r = 0 := (add_eq_zero.mp h).2
    simp [hl, hr, chooseWeight]
  · have hn : (↑(l + r) : ℝ≥0∞) ≠ 0 := by exact_mod_cast h
    simp only [chooseWeight, dite_eq_right h, PMF.ofFintype_apply]
    rw [mul_left_comm, ENNReal.mul_inv_cancel hn ENNReal.coe_ne_top, mul_one]

/-- Mixtures add unnormalized masses; no positive-mass premise is needed on either child. -/
theorem chooseWeight_bind_scaled (l r : ℝ≥0) (p q : PMF α) (a : α) :
    (↑(l + r) : ℝ≥0∞) * ((chooseWeight l r).bind (fun b => if b then p else q)) a =
      (l : ℝ≥0∞) * p a + (r : ℝ≥0∞) * q a := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, mul_add, ← mul_assoc]
  rw [chooseWeight_scaled, chooseWeight_scaled]
  simp [add_comm]

end
end CutQueryComplexity.Probability
