import CutQueryComplexity.ImplicitLP.MatrixCalculus
import CutQueryComplexity.ImplicitLP.LewisJacobian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Leverage scores and their derivative (Lee–Sidford Lemma 49)

For `X ∈ ℝ^{M×r}` with `XᵀX` invertible, `P(X) = X(XᵀX)⁻¹Xᵀ` is the orthogonal projection onto
the column space, and the leverage scores are `σ(X)ᵢ = P(X)ᵢᵢ`. `proj_symm` and `proj_idem`
show that `P(X)` is symmetric and idempotent, so P0 applies to it.

`hasDerivAt_lev` (P1): scaling the rows by `e^{τh}`,
`d/dτ σ(diag(e^{τh}) B)ᵢ |_{τ=0} = 2 (Λ h)ᵢ` where `Λ = Σ − P ⊙ P` and `P = P(B)`.
This is the log-coordinate form of Lee–Sidford Lemma 49, `J_σ = 2ΛD⁻¹`. Since `B` is
arbitrary, the derivative at any `τ₀` follows by replacing `B` with `diag(e^{τ₀h}) B`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ}

/-- The orthogonal projection onto the column space, `P(X) = X(XᵀX)⁻¹Xᵀ`. -/
def proj (X : Matrix (Fin M) (Fin r) ℝ) : Matrix (Fin M) (Fin M) ℝ := X * (Xᵀ * X)⁻¹ * Xᵀ

/-- Leverage scores `σ(X)ᵢ = P(X)ᵢᵢ`. -/
def lev (X : Matrix (Fin M) (Fin r) ℝ) (i : Fin M) : ℝ := proj X i i

theorem proj_symm (X : Matrix (Fin M) (Fin r) ℝ) : (proj X)ᵀ = proj X := by
  simp [proj, transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc]

theorem proj_idem {X : Matrix (Fin M) (Fin r) ℝ} (hX : (Xᵀ * X).det ≠ 0) :
    proj X * proj X = proj X := by
  have hu : IsUnit (Xᵀ * X).det := isUnit_iff_ne_zero.mpr hX
  calc proj X * proj X = X * ((Xᵀ * X)⁻¹ * (Xᵀ * X)) * (Xᵀ * X)⁻¹ * Xᵀ := by
        simp only [proj, Matrix.mul_assoc]
    _ = proj X := by rw [nonsing_inv_mul _ hu, Matrix.mul_one]; rfl

/-- **Leverage-score derivative** (P1; Lee–Sidford Lemma 49 in log coordinates). -/
theorem hasDerivAt_lev (B : Matrix (Fin M) (Fin r) ℝ) (hB : (Bᵀ * B).det ≠ 0)
    (h : Fin M → ℝ) (i : Fin M) :
    HasDerivAt (fun τ => lev (diagonal (fun j => exp (τ * h j)) * B) i)
      (2 * ((diagonal (fun j => proj B j j) - proj B ⊙ proj B) *ᵥ h) i) 0 := by
  set e : ℝ → Fin M → ℝ := fun τ j => exp (τ * (2 * h j)) with he
  set A : ℝ → Matrix (Fin r) (Fin r) ℝ := fun τ => Bᵀ * diagonal (e τ) * B with hAdef
  set A' : Matrix (Fin r) (Fin r) ℝ := Bᵀ * diagonal (fun j => 2 * h j) * B with hA'
  set P := proj B with hP
  -- the scaled Gram matrix and the scaled leverage score
  have hgram : ∀ τ, (diagonal (fun j => exp (τ * h j)) * B)ᵀ *
      (diagonal (fun j => exp (τ * h j)) * B) = A τ := fun τ => by
    have hd : diagonal (fun j => exp (τ * h j)) * diagonal (fun j => exp (τ * h j)) =
        diagonal (e τ) := by
      rw [diagonal_mul_diagonal]; congr 1; funext j
      simp only [he, ← exp_add]; ring_nf
    simp only [hAdef, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal _) (diagonal _) B, hd]
  have hlev : ∀ τ, lev (diagonal (fun j => exp (τ * h j)) * B) i =
      e τ i * (B * (A τ)⁻¹ * Bᵀ) i i := fun τ => by
    unfold lev proj
    rw [hgram τ, transpose_mul, diagonal_transpose]
    have : diagonal (fun j => exp (τ * h j)) * B * (A τ)⁻¹ * (Bᵀ * diagonal fun j =>
        exp (τ * h j)) = diagonal (fun j => exp (τ * h j)) * (B * (A τ)⁻¹ * Bᵀ) *
        diagonal (fun j => exp (τ * h j)) := by simp only [Matrix.mul_assoc]
    rw [this, mul_diagonal, diagonal_mul, he]
    simp only
    rw [show τ * (2 * h i) = τ * h i + τ * h i by ring, exp_add]; ring
  -- entries of `A`
  have hAe : ∀ τ a b, A τ a b = ∑ j, B j a * e τ j * B j b := fun τ a b => by
    simp only [hAdef]; rw [mul_apply]; simp only [mul_diagonal, transpose_apply]
  have hA'e : ∀ a b, A' a b = ∑ j, B j a * (2 * h j) * B j b := fun a b => by
    simp only [hA']; rw [mul_apply]; simp only [mul_diagonal, transpose_apply]
  have he' : ∀ j, HasDerivAt (fun τ => e τ j) (2 * h j) 0 := fun j => by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (2 * h j)).exp
    simpa [he] using this
  have hAd : ∀ a b, HasDerivAt (fun τ => A τ a b) (A' a b) 0 := fun a b => by
    simp_rw [hAe, hA'e]
    exact HasDerivAt.fun_sum fun j _ => ((he' j).const_mul (B j a)).mul_const (B j b)
  have hAc : ∀ a b, ContDiffAt ℝ 1 (fun τ => A τ a b) 0 := fun a b => by
    simp_rw [hAe, he]; fun_prop
  have hA0 : A 0 = Bᵀ * B := by
    simp [hAdef, he]
  have hdet : (A 0).det ≠ 0 := by rwa [hA0]
  have hN := hasDerivAt_inv_entry hAd hAc hdet
  -- differentiate `e τ i * (B N(τ) Bᵀ)ᵢᵢ`
  have hQ : HasDerivAt (fun τ => (B * (A τ)⁻¹ * Bᵀ) i i)
      ((B * (-((A 0)⁻¹ * A' * (A 0)⁻¹)) * Bᵀ) i i) 0 := by
    simp only [mul_apply, transpose_apply, sum_mul]
    exact HasDerivAt.fun_sum fun b _ => HasDerivAt.fun_sum fun a _ =>
      ((hN a b).const_mul (B i a)).mul_const (B i b)
  have hprod := (he' i).mul hQ
  simp_rw [hlev]
  convert hprod using 1
  -- identify the derivative
  have he0 : e 0 i = 1 := by simp [he]
  rw [he0, hA0, one_mul]
  have hPP : B * ((Bᵀ * B)⁻¹ * A' * (Bᵀ * B)⁻¹) * Bᵀ = P * diagonal (fun j => 2 * h j) * P := by
    simp only [hP, proj, hA', Matrix.mul_assoc]
  have hsymm := proj_symm B
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, hPP]
  have hsym : ∀ j, P j i = P i j := fun j => by
    have := congrFun (congrFun hsymm i) j; simpa [transpose_apply] using this
  have h1 : ((diagonal (fun j => P j j) - P ⊙ P) *ᵥ h) i =
      P i i * h i - ∑ j, P i j * P i j * h j := by
    rw [sub_mulVec, Pi.sub_apply, mulVec_diagonal]
    congr 1
  have h2 : (P * diagonal (fun j => 2 * h j) * P) i i = ∑ j, P i j * (2 * h j) * P i j := by
    rw [mul_apply]; simp only [mul_diagonal, hsym]
  have h3 : ∑ j, P i j * (2 * h j) * P i j = 2 * ∑ j, P i j * P i j * h j := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  have h4 : (B * (Bᵀ * B)⁻¹ * Bᵀ) i i = P i i := rfl
  rw [h1, h2, h3, h4]
  ring

end

end ImplicitLP
end CutQueryComplexity
