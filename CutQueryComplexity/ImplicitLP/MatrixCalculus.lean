import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Entrywise calculus of the matrix inverse (Lee–Sidford audit)

Mathlib's derivative of `Ring.inverse` needs a normed-ring structure on matrices, which is not a
global instance. We instead work entrywise: the determinant and the adjugate are polynomials in
the entries, so

* `contDiffAt_det`, `contDiffAt_adjugate`, `contDiffAt_inv_entry`: if every entry of `A y` is
  `C^k` at `x` and `det (A x) ≠ 0`, every entry of `(A y)⁻¹` is `C^k` at `x`;
* `hasDerivAt_inv_entry`: along a curve, `(A⁻¹)' = −A⁻¹ A' A⁻¹`, obtained by differentiating
  `A A⁻¹ = 1` near the point.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : WithTop ℕ∞}

theorem contDiffAt_det {A : E → Matrix ι ι ℝ} {x : E}
    (h : ∀ i j, ContDiffAt ℝ k (fun y => A y i j) x) :
    ContDiffAt ℝ k (fun y => (A y).det) x := by
  simp_rw [det_apply']
  exact ContDiffAt.sum fun σ _ =>
    contDiffAt_const.mul (contDiffAt_prod (f := fun i y => A y (σ i) i) fun i _ => h _ _)

theorem contDiffAt_adjugate {A : E → Matrix ι ι ℝ} {x : E}
    (h : ∀ i j, ContDiffAt ℝ k (fun y => A y i j) x) (i j : ι) :
    ContDiffAt ℝ k (fun y => (A y).adjugate i j) x := by
  simp_rw [adjugate_apply]
  apply contDiffAt_det
  intro a b
  by_cases ha : a = j
  · subst ha; simp only [updateRow_self]; exact contDiffAt_const
  · simp only [updateRow_ne ha]; exact h a b

theorem contDiffAt_inv_entry {A : E → Matrix ι ι ℝ} {x : E}
    (h : ∀ i j, ContDiffAt ℝ k (fun y => A y i j) x) (hx : (A x).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ k (fun y => (A y)⁻¹ i j) x := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ((contDiffAt_det h).inv hx).mul (contDiffAt_adjugate h i j)

/-- **Derivative of the inverse along a curve:** `(A⁻¹)' = −A⁻¹ A' A⁻¹`. -/
theorem hasDerivAt_inv_entry {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hC : ∀ i j, ContDiffAt ℝ 1 (fun s => A s i j) t) (hdet : (A t).det ≠ 0) (i j : ι) :
    HasDerivAt (fun s => (A s)⁻¹ i j) ((-((A t)⁻¹ * A' * (A t)⁻¹)) i j) t := by
  set D : Matrix ι ι ℝ := fun a b => deriv (fun s => (A s)⁻¹ a b) t
  have hN : ∀ a b, HasDerivAt (fun s => (A s)⁻¹ a b) (D a b) t := fun a b =>
    ((contDiffAt_inv_entry hC hdet a b).differentiableAt one_ne_zero).hasDerivAt
  -- `A s * (A s)⁻¹ = 1` near `t`
  have hev : ∀ᶠ s in nhds t, (A s).det ≠ 0 :=
    ((contDiffAt_det hC).continuousAt).eventually_ne hdet
  have hzero : A' * (A t)⁻¹ + A t * D = 0 := by
    ext a b
    have hprod : HasDerivAt (fun s => (A s * (A s)⁻¹) a b)
        (∑ c, (A' a c * (A t)⁻¹ c b + A t a c * D c b)) t := by
      simp only [mul_apply]
      exact HasDerivAt.fun_sum fun c _ => (hA a c).mul (hN c b)
    have hconst : HasDerivAt (fun s => (A s * (A s)⁻¹) a b) 0 t := by
      apply (hasDerivAt_const t ((1 : Matrix ι ι ℝ) a b)).congr_of_eventuallyEq
      filter_upwards [hev] with s hs
      rw [mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs)]
    have := hprod.unique hconst
    simpa [Matrix.add_apply, mul_apply, sum_add_distrib] using this
  have hD : D = -((A t)⁻¹ * A' * (A t)⁻¹) := by
    have hu : IsUnit (A t).det := isUnit_iff_ne_zero.mpr hdet
    have : A t * D = -(A' * (A t)⁻¹) := eq_neg_of_add_eq_zero_right hzero
    calc D = (A t)⁻¹ * (A t * D) := (nonsing_inv_mul_cancel_left (A t) D hu).symm
      _ = _ := by rw [this, Matrix.mul_neg, Matrix.mul_assoc]
  rw [← hD]
  exact hN i j

end ImplicitLP
end CutQueryComplexity
