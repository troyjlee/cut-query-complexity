import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Quadratic forms and the Euclidean operator norm (D3)

For real square matrices with the L2 operator norm (`Matrix.Norms.L2Operator`):

* `abs_quad_le_norm`: `|xᵀ M x| ≤ ‖M‖ xᵀx`;
* `norm_le_of_abs_quad_le`: for symmetric `M`, `|xᵀ M x| ≤ c xᵀx` for all `x` gives `‖M‖ ≤ c`
  (Rayleigh quotients, `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`);
* `sq_quad_le`: Cauchy–Schwarz for the semi-inner product of a positive semidefinite symmetric
  `M`, `(xᵀ M y)² ≤ (xᵀ M x)(yᵀ M y)`;
* `quad_sq_le`: `A² ⪯ ‖A‖ A` for positive semidefinite symmetric `A`.
-/

namespace CutQueryComplexity
namespace Spectral

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

theorem dot_self_nonneg (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- The Euclidean vector of `x`. -/
noncomputable abbrev euc (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x

theorem inner_euc (x y : Fin n → ℝ) : inner ℝ (euc x) (euc y) = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

theorem norm_euc_sq (x : Fin n → ℝ) : ‖euc x‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq, inner_euc]

theorem toEuclideanCLM_euc (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    toEuclideanCLM (𝕜 := ℝ) M (euc x) = euc (M *ᵥ x) := toEuclideanCLM_toLp M x

/-- `|xᵀ M x| ≤ ‖M‖ xᵀx`. -/
theorem abs_quad_le_norm (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ ‖M‖ * (x ⬝ᵥ x) := by
  have h1 : x ⬝ᵥ (M *ᵥ x) = inner ℝ (toEuclideanCLM (𝕜 := ℝ) M (euc x)) (euc x) := by
    rw [toEuclideanCLM_euc, inner_euc, dotProduct_comm]
  rw [h1, ← norm_euc_sq, ← l2_opNorm_toEuclideanCLM]
  calc |inner ℝ (toEuclideanCLM (𝕜 := ℝ) M (euc x)) (euc x)|
      ≤ ‖toEuclideanCLM (𝕜 := ℝ) M (euc x)‖ * ‖euc x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖toEuclideanCLM (𝕜 := ℝ) M‖ * ‖euc x‖ * ‖euc x‖ :=
        mul_le_mul_of_nonneg_right ((toEuclideanCLM (𝕜 := ℝ) M).le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

/-- **A quadratic-form bound bounds the operator norm** of a symmetric matrix. -/
theorem norm_le_of_abs_quad_le {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x, |x ⬝ᵥ (M *ᵥ x)| ≤ c * (x ⬝ᵥ x)) : ‖M‖ ≤ c := by
  set T := toEuclideanCLM (𝕜 := ℝ) M
  have hT : (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := by
    rw [coe_toEuclideanCLM_eq_toEuclideanLin]; exact isSymmetric_toEuclideanLin_iff.mpr hM
  rw [← l2_opNorm_toEuclideanCLM, T.norm_eq_iSup_rayleighQuotient hT]
  refine ciSup_le fun X => ?_
  set x : Fin n → ℝ := X.ofLp
  have hX : X = euc x := rfl
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, hX,
    toEuclideanCLM_euc, RCLike.re_to_real, inner_euc, norm_euc_sq, dotProduct_comm]
  rw [abs_div, abs_of_nonneg (dot_self_nonneg x)]
  by_cases hx : x ⬝ᵥ x = 0
  · rw [hx, div_zero]; exact hc
  · rw [div_le_iff₀ (lt_of_le_of_ne (dot_self_nonneg x) (Ne.symm hx))]
    exact h x

/-- Symmetric matrices move across the dot product. -/
theorem dot_mulVec_symm {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) (x y : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose]
  have : Mᵀ = M := by
    have := hM.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [this, dotProduct_comm]

/-- **Cauchy–Schwarz for a positive semidefinite symmetric matrix.** -/
theorem sq_quad_le {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (hpsd : ∀ z, 0 ≤ z ⬝ᵥ (M *ᵥ z)) (x y : Fin n → ℝ) :
    (x ⬝ᵥ (M *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (M *ᵥ x)) * (y ⬝ᵥ (M *ᵥ y)) := by
  have hsym := dot_mulVec_symm hM y x
  have hq : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ (M *ᵥ y)) * (t * t) + 2 * (x ⬝ᵥ (M *ᵥ y)) * t +
      (x ⬝ᵥ (M *ᵥ x)) := by
    intro t
    have := hpsd (x + t • y)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at this
    have h2 : y ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M *ᵥ y) := by
      rw [hsym, dotProduct_comm]
    rw [h2] at this
    nlinarith
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

/-- **`A² ⪯ ‖A‖ A`** for positive semidefinite symmetric `A`. -/
theorem quad_sq_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hpsd : ∀ z, 0 ≤ z ⬝ᵥ (A *ᵥ z)) (x : Fin n → ℝ) :
    x ⬝ᵥ ((A * A) *ᵥ x) ≤ ‖A‖ * (x ⬝ᵥ (A *ᵥ x)) := by
  set y := A *ᵥ x
  have hq : x ⬝ᵥ ((A * A) *ᵥ x) = y ⬝ᵥ y := by
    rw [← mulVec_mulVec, dot_mulVec_symm hA]
  have hxy : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ y := by rw [dot_mulVec_symm hA]
  have hcs := sq_quad_le hA hpsd x y
  rw [hxy] at hcs
  have hyy : y ⬝ᵥ (A *ᵥ y) ≤ ‖A‖ * (y ⬝ᵥ y) := (le_abs_self _).trans (abs_quad_le_norm A y)
  have hx0 := hpsd x
  have hy0 : 0 ≤ y ⬝ᵥ y := dot_self_nonneg y
  rw [hq]
  by_cases h0 : y ⬝ᵥ y = 0
  · rw [h0]; exact mul_nonneg (norm_nonneg _) hx0
  · have hpos : 0 < y ⬝ᵥ y := lt_of_le_of_ne hy0 (Ne.symm h0)
    have : (y ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (‖A‖ * (y ⬝ᵥ y)) :=
      hcs.trans (mul_le_mul_of_nonneg_left hyy hx0)
    nlinarith

end Spectral
end CutQueryComplexity
