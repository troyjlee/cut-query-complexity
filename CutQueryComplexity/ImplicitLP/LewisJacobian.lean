import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # The projection-Jacobian bound (Lee–Sidford Lemma 25)

This is the linear-algebra core of Lewis-weight movement. Let `P` be a symmetric idempotent
matrix with positive diagonal `σ`, put `Λ = Σ − P ⊙ P`, fix `c ≥ 0`, and put `β = 2/(1+c)`.
Then `Σ + cΛ` is invertible, and `K = 2(Σ + cΛ)⁻¹Λ` satisfies, for every `h`,

* `‖Kh‖_σ ≤ β‖h‖_σ`;
* `‖Kh − βh‖_∞ ≤ β‖h‖_σ`;
* for every `C > 0`, `‖Kh‖_∞ + C‖Kh‖_σ ≤ β(1 + 1/C)(‖h‖_∞ + C‖h‖_σ)`.

At the Lewis weights, `P` is the projection of `W^{1/2−1/p}A`, `σ = w`, and `c = 2/p − 1`
gives `β = p` (`beta_of_p`). Then `K` is the log–log Jacobian of the Lewis weights under row
scaling (Lee–Sidford Lemma 24), and the third item is the consistency bound `p(1 + 1/C)`.

The proof avoids the spectral theorem used by Lee–Sidford. With `(Σ + cΛ)u = Σh` and
`v = Σ⁻¹Λu`, we have `h = u + cv` and `Kh = 2v`. The quantities `X = ‖v‖²_σ`,
`Y = uᵀΛu`, `Z = ‖u‖²_σ` satisfy `X ≤ Y ≤ Z`: `Y ≤ Z` and `X ≤ Y` both follow from
`Λ ⪰ 0` and `P ⊙ P ⪰ 0` (Schur product theorem), applied to `u` and to `u − v`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Finset Matrix

noncomputable section

variable {M : ℕ}

/-- The weighted Euclidean norm `‖x‖_σ = (∑ σᵢ xᵢ²)^{1/2}`. -/
def wnorm (σ x : Fin M → ℝ) : ℝ := Real.sqrt (∑ i, σ i * x i ^ 2)

theorem wnorm_nonneg (σ x : Fin M → ℝ) : 0 ≤ wnorm σ x := Real.sqrt_nonneg _

/-- At the Lewis-weight instantiation `c = 2/p − 1`, `β = 2/(1+c) = p`. -/
theorem beta_of_p {p : ℝ} (hp : 0 < p) : 2 / (1 + (2 / p - 1)) = p := by
  field_simp; ring

section Projection

variable {P : Matrix (Fin M) (Fin M) ℝ}

theorem symm_apply (hsymm : Pᵀ = P) (i j : Fin M) : P j i = P i j := by
  have := congrFun (congrFun hsymm i) j
  simpa [transpose_apply] using this

/-- `σᵢ = ∑ⱼ Pᵢⱼ²` (Lee–Sidford Lemma 47(1)). -/
theorem diag_eq_sum_sq (hsymm : Pᵀ = P) (hidem : P * P = P) (i : Fin M) :
    P i i = ∑ j, P i j ^ 2 := by
  have := congrFun (congrFun hidem i) i
  rw [mul_apply] at this
  rw [← this]
  exact sum_congr rfl fun j _ => by rw [symm_apply hsymm j i]; ring

/-- `Pᵢⱼ² ≤ σᵢσⱼ` (Lee–Sidford Lemma 47(3)). -/
theorem sq_le_diag_mul (hsymm : Pᵀ = P) (hidem : P * P = P) (i j : Fin M) :
    P i j ^ 2 ≤ P i i * P j j := by
  have h := congrFun (congrFun hidem i) j
  rw [mul_apply] at h
  have h' : P i j = ∑ k, P i k * P j k := by
    rw [← h]; exact sum_congr rfl fun k _ => by rw [symm_apply hsymm j k]
  rw [h', diag_eq_sum_sq hsymm hidem i, diag_eq_sum_sq hsymm hidem j]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

/-- The row of `P ⊙ P` against `u`: `(∑ⱼ Pᵢⱼ² uⱼ)² ≤ σᵢ² ‖u‖²_σ` (Lee–Sidford Lemma 47(4)). -/
theorem row_sq_le (hsymm : Pᵀ = P) (hidem : P * P = P) (hpos : ∀ i, 0 < P i i)
    (u : Fin M → ℝ) (i : Fin M) :
    (∑ j, P i j ^ 2 * u j) ^ 2 ≤ P i i ^ 2 * ∑ j, P j j * u j ^ 2 := by
  have h1 := sum_sq_le_sum_mul_sum_of_sq_le_mul univ (r := fun j => P i j ^ 2 * u j)
    (f := fun j => P i j ^ 2) (g := fun j => P i j ^ 2 * u j ^ 2)
    (fun j _ => sq_nonneg _) (fun j _ => by positivity) (fun j _ => by ring_nf; rfl)
  rw [← diag_eq_sum_sq hsymm hidem i] at h1
  refine h1.trans ?_
  rw [sq, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hpos i).le
  rw [mul_sum]
  exact sum_le_sum fun j _ => by
    have := sq_le_diag_mul hsymm hidem i j
    have := sq_nonneg (u j)
    nlinarith

/-- The bilinear form of `P ⊙ P`: `H(u, v) = ∑ᵢⱼ Pᵢⱼ² uᵢ vⱼ`. -/
def hform (P : Matrix (Fin M) (Fin M) ℝ) (u v : Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j, P i j ^ 2 * u i * v j

/-- The bilinear form of `Σ`: `S(u, v) = ∑ᵢ σᵢ uᵢ vᵢ`. -/
def sform (P : Matrix (Fin M) (Fin M) ℝ) (u v : Fin M → ℝ) : ℝ :=
  ∑ i, P i i * u i * v i

theorem hform_comm (hsymm : Pᵀ = P) (u v : Fin M → ℝ) : hform P u v = hform P v u := by
  unfold hform
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [symm_apply hsymm i j]; ring

theorem hform_sub (u v : Fin M → ℝ) :
    hform P (u - v) (u - v) = hform P u u - hform P u v - hform P v u + hform P v v := by
  unfold hform
  simp only [Pi.sub_apply, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem sform_sub (u v : Fin M → ℝ) :
    sform P (u - v) (u - v) = sform P u u - 2 * sform P u v + sform P v v := by
  unfold sform
  simp only [Pi.sub_apply, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

theorem hform_eq_sum (u v : Fin M → ℝ) :
    hform P u v = ∑ i, u i * ∑ j, P i j ^ 2 * v j := by
  unfold hform
  exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring

/-- **`P ⊙ P ⪰ 0`** (Schur product theorem, since `P = PᵀP ⪰ 0`). -/
theorem hform_nonneg (hsymm : Pᵀ = P) (hidem : P * P = P) (u : Fin M → ℝ) :
    0 ≤ hform P u u := by
  have hP : P.PosSemidef := by
    have := posSemidef_conjTranspose_mul_self P
    rwa [conjTranspose_eq_transpose_of_trivial, hsymm, hidem] at this
  have := (hP.hadamard hP).dotProduct_mulVec_nonneg u
  rw [hform_eq_sum]
  simpa [dotProduct, mulVec, hadamard_apply, sq] using this

/-- **`Λ = Σ − P ⊙ P ⪰ 0`**: `uᵀΛu = ½ ∑ᵢⱼ Pᵢⱼ² (uᵢ − uⱼ)²`. -/
theorem hform_le_sform (hsymm : Pᵀ = P) (hidem : P * P = P) (u : Fin M → ℝ) :
    hform P u u ≤ sform P u u := by
  have h0 : 0 ≤ ∑ i, ∑ j, P i j ^ 2 * (u i - u j) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => by positivity
  have hexp : ∑ i, ∑ j, P i j ^ 2 * (u i - u j) ^ 2 =
      (∑ i, ∑ j, P i j ^ 2 * u i ^ 2) + (∑ i, ∑ j, P i j ^ 2 * u j ^ 2) - 2 * hform P u u := by
    unfold hform
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have h1 : ∑ i, ∑ j, P i j ^ 2 * u i ^ 2 = sform P u u := by
    unfold sform
    exact sum_congr rfl fun i _ => by
      rw [← sum_mul, ← diag_eq_sum_sq hsymm hidem i]; ring
  have h2 : ∑ i, ∑ j, P i j ^ 2 * u j ^ 2 = sform P u u := by
    rw [sum_comm, ← h1]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [symm_apply hsymm i j]
  linarith

end Projection

/-- **The projection-Jacobian bound** (the core of Lee–Sidford Lemma 25). -/
theorem proj_jacobian_bound {P : Matrix (Fin M) (Fin M) ℝ} (hsymm : Pᵀ = P)
    (hidem : P * P = P) (hpos : ∀ i, 0 < P i i) {c : ℝ} (hc : 0 ≤ c) :
    let σ : Fin M → ℝ := fun i => P i i
    let Λ : Matrix (Fin M) (Fin M) ℝ := diagonal σ - P ⊙ P
    let K : Matrix (Fin M) (Fin M) ℝ := (2 : ℝ) • ((diagonal σ + c • Λ)⁻¹ * Λ)
    IsUnit (diagonal σ + c • Λ).det ∧ ∀ h : Fin M → ℝ,
      wnorm σ (K *ᵥ h) ≤ 2 / (1 + c) * wnorm σ h ∧
      ‖K *ᵥ h - (2 / (1 + c)) • h‖ ≤ 2 / (1 + c) * wnorm σ h := by
  intro σ Λ K
  set B := diagonal σ + c • Λ with hB
  -- the actions of `Λ` and `B`
  have hΛ : ∀ u i, (Λ *ᵥ u) i = σ i * u i - ∑ j, P i j ^ 2 * u j := by
    intro u i
    rw [sub_mulVec, Pi.sub_apply, mulVec_diagonal]
    congr 1
    simp only [mulVec, dotProduct, hadamard_apply, sq, mul_assoc]
  have hBv : ∀ u i, (B *ᵥ u) i = σ i * u i + c * (Λ *ᵥ u) i := by
    intro u i
    rw [hB, add_mulVec, Pi.add_apply, mulVec_diagonal, smul_mulVec, Pi.smul_apply, smul_eq_mul]
  have hS : ∀ u, sform P u u = ∑ i, σ i * u i ^ 2 := fun u =>
    sum_congr rfl fun i _ => by simp [σ]; ring
  -- invertibility: `uᵀBu ≥ ‖u‖²_σ`
  have hdet : B.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hBx⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have hq : ∑ i, x i * (B *ᵥ x) i = sform P x x + c * (sform P x x - hform P x x) := by
      simp only [hBv, hΛ, mul_add, sum_add_distrib, sform, hform_eq_sum, mul_sub,
        sum_sub_distrib, mul_sum]
      congr 1
      · exact sum_congr rfl fun i _ => by simp [σ]; ring
      · congr 1
        · exact sum_congr rfl fun i _ => by simp [σ]; ring
        · exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rw [hBx] at hq
    simp only [Pi.zero_apply, mul_zero, sum_const_zero] at hq
    have h1 := hform_le_sform hsymm hidem x
    have h2 : 0 ≤ sform P x x := by
      rw [hS]; exact sum_nonneg fun i _ => mul_nonneg (hpos i).le (sq_nonneg _)
    have h3 : sform P x x = 0 := by nlinarith
    rw [hS] at h3
    apply hx
    funext i
    have := (sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hpos i).le (sq_nonneg (x i))).mp h3 i (mem_univ i)
    simpa [(hpos i).ne'] using this
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨hunit, fun h => ?_⟩
  -- reparametrise: `Bu = Σh`, `v = Σ⁻¹Λu`
  set u := B⁻¹ *ᵥ (fun i => σ i * h i) with hu
  have hBu : B *ᵥ u = fun i => σ i * h i := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec]
  set r : Fin M → ℝ := fun i => ∑ j, P i j ^ 2 * u j with hr
  set v : Fin M → ℝ := fun i => u i - r i / σ i with hv
  have hσv : ∀ i, σ i * v i = (Λ *ᵥ u) i := fun i => by
    rw [hΛ]; simp only [hv, hr]; rw [mul_sub, mul_div_cancel₀ _ (hpos i).ne']
  have hhuv : h = u + c • v := by
    funext i
    have := congrFun hBu i
    rw [hBv, ← hσv] at this
    have hσ : σ i ≠ 0 := (hpos i).ne'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply mul_left_cancel₀ hσ
    linarith
  have hKh : K *ᵥ h = (2 : ℝ) • v := by
    have hΛh : Λ *ᵥ h = B *ᵥ v := by
      funext i
      rw [hhuv, mulVec_add, mulVec_smul, hBv, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        ← hσv]
    show ((2 : ℝ) • (B⁻¹ * Λ)) *ᵥ h = _
    rw [smul_mulVec, ← mulVec_mulVec, hΛh, mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  -- the three quadratic quantities
  have hX : sform P v v = sform P u v - hform P v u := by
    rw [hform_eq_sum]
    unfold sform
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by
      have := hσv i; rw [hΛ] at this
      show σ i * v i * v i = σ i * u i * v i - v i * ∑ j, P i j ^ 2 * u j
      linear_combination v i * this
  have hsuv : sform P u v = sform P v u := sum_congr rfl fun i _ => by ring
  have hY : sform P u v = sform P u u - hform P u u := by
    rw [hform_eq_sum]
    unfold sform
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by
      have := hσv i; rw [hΛ] at this
      show σ i * u i * v i = σ i * u i * u i - u i * ∑ j, P i j ^ 2 * u j
      linear_combination u i * this
  set X := sform P v v
  set Z := sform P u u
  set Y := Z - hform P u u
  have hXY : X ≤ Y := by
    have h1 := hform_le_sform hsymm hidem (u - v)
    rw [hform_sub, sform_sub] at h1
    have h2 := hform_nonneg hsymm hidem v
    have h3 := hform_comm hsymm u v
    simp only [Y]
    nlinarith
  have hYZ : Y ≤ Z := by simp only [Y]; linarith [hform_nonneg hsymm hidem u]
  have hX0 : 0 ≤ X := by
    simp only [X]; rw [hS]; exact sum_nonneg fun i _ => mul_nonneg (hpos i).le (sq_nonneg _)
  have hnh : ∑ i, σ i * h i ^ 2 = Z + 2 * c * Y + c ^ 2 * X := by
    rw [← hS, hhuv]
    simp only [X, Y, Z, ← hY, sform, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum,
      ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hc1 : 0 < 1 + c := by linarith
  have hβ : 0 ≤ 2 / (1 + c) := by positivity
  have hZh : Real.sqrt Z ≤ wnorm σ h := by
    unfold wnorm; rw [hnh]
    exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨?_, ?_⟩
  · -- `‖Kh‖_σ ≤ β‖h‖_σ`
    rw [hKh]
    unfold wnorm
    rw [hnh, ← Real.sqrt_sq hβ, ← Real.sqrt_mul (sq_nonneg _)]
    apply Real.sqrt_le_sqrt
    have hKX : ∑ i, σ i * ((2 : ℝ) • v) i ^ 2 = 4 * X := by
      simp only [X]; rw [hS, mul_sum]
      exact sum_congr rfl fun i _ => by simp; ring
    rw [hKX, div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc1 2)]
    nlinarith
  · -- `‖Kh − βh‖_∞ ≤ β‖h‖_σ`
    have hdiff : K *ᵥ h - (2 / (1 + c)) • h = fun i => -(2 / (1 + c)) * (r i / σ i) := by
      rw [hKh, hhuv]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hv]
      field_simp
      ring
    rw [hdiff]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hβ (wnorm_nonneg σ h))).mpr fun i => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hβ]
    refine mul_le_mul_of_nonneg_left ?_ hβ
    refine le_trans ?_ hZh
    rw [abs_div, abs_of_pos (hpos i), div_le_iff₀ (hpos i)]
    have hrow := row_sq_le hsymm hidem hpos u i
    have hZ0 : 0 ≤ Z := hX0.trans (hXY.trans hYZ)
    have hZ' : ∑ j, P j j * u j ^ 2 = Z := (hS u).symm
    rw [hZ'] at hrow
    rw [← Real.sqrt_sq (abs_nonneg (r i)), ← Real.sqrt_sq (hpos i).le, ← Real.sqrt_mul hZ0]
    exact Real.sqrt_le_sqrt (by rw [sq_abs, mul_comm]; exact hrow)

/-- **Mixed-norm consequence** (the consistency bound): for every `C > 0`,
`‖Kh‖_∞ + C‖Kh‖_σ ≤ β(1 + 1/C)(‖h‖_∞ + C‖h‖_σ)`. -/
theorem proj_jacobian_mixed {P : Matrix (Fin M) (Fin M) ℝ} (hsymm : Pᵀ = P)
    (hidem : P * P = P) (hpos : ∀ i, 0 < P i i) {c C : ℝ} (hc : 0 ≤ c) (hC : 0 < C)
    (h : Fin M → ℝ) :
    let σ : Fin M → ℝ := fun i => P i i
    let K : Matrix (Fin M) (Fin M) ℝ :=
      (2 : ℝ) • ((diagonal σ + c • (diagonal σ - P ⊙ P))⁻¹ * (diagonal σ - P ⊙ P))
    ‖K *ᵥ h‖ + C * wnorm σ (K *ᵥ h) ≤
      2 / (1 + c) * (1 + 1 / C) * (‖h‖ + C * wnorm σ h) := by
  intro σ K
  obtain ⟨-, hK⟩ := proj_jacobian_bound hsymm hidem hpos hc
  obtain ⟨h1, h2⟩ := hK h
  set β := 2 / (1 + c)
  have hβ : 0 ≤ β := by positivity
  have hinf : ‖K *ᵥ h‖ ≤ β * ‖h‖ + β * wnorm σ h := by
    calc ‖K *ᵥ h‖ = ‖(K *ᵥ h - β • h) + β • h‖ := by rw [sub_add_cancel]
      _ ≤ ‖K *ᵥ h - β • h‖ + ‖β • h‖ := norm_add_le _ _
      _ ≤ β * wnorm σ h + β * ‖h‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ]; exact add_le_add h2 le_rfl
      _ = _ := by ring
  have hw := wnorm_nonneg σ h
  have hn : 0 ≤ ‖h‖ := norm_nonneg _
  have key : β * ‖h‖ + β * wnorm σ h + C * (β * wnorm σ h) ≤
      β * (1 + 1 / C) * (‖h‖ + C * wnorm σ h) := by
    have : β * (1 + 1 / C) * (‖h‖ + C * wnorm σ h) =
        β * ‖h‖ + β * wnorm σ h + C * (β * wnorm σ h) + β / C * ‖h‖ := by
      field_simp; ring
    rw [this]
    have : 0 ≤ β / C * ‖h‖ := by positivity
    linarith
  calc ‖K *ᵥ h‖ + C * wnorm σ (K *ᵥ h)
      ≤ (β * ‖h‖ + β * wnorm σ h) + C * (β * wnorm σ h) :=
        add_le_add hinf (mul_le_mul_of_nonneg_left h1 hC.le)
    _ ≤ _ := key

end

end ImplicitLP
end CutQueryComplexity
