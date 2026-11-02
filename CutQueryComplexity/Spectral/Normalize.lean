import CutQueryComplexity.Spectral.MatrixNorm
import CutQueryComplexity.Spectral.Energy
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Normalization on the range of a Laplacian (D3)

For a symmetric positive semidefinite `L = U diag(λ) Uᵀ` (`IsHermitian.spectral_theorem`), the
spectral functions `fnL g = U diag(g ∘ λ) Uᵀ` multiply pointwise (`fnL_mul`). With

  `W = L^{+1/2}` (`g = 1/√t` on `t > 0`, else `0`), `R = L^{1/2}`, `P` the range projector,

`W R = P`, `W L W = P`, `R R = L`, and `L P = L`. Quadratic forms of `fnL g` with `0 ≤ g ≤ 1` lie
between `0` and `xᵀx` (`quad_fnL_le`).

* `transfer`: if a symmetric `M` vanishes on `ker L` and `‖W M W‖ ≤ δ`, then
  `|vᵀ M v| ≤ δ vᵀ L v` for every `v`.
* `normPair`: the normalized pair matrices `A_e = W (ω_e a_e a_eᵀ) W` are symmetric positive
  semidefinite (`normPair_psd`) and sum to at most `I` over the support (`sum_normPair_le`). The
  bundle bound `ω_e (x_u − x_v)² ≤ λ xᵀ L x` gives `‖A_e‖ ≤ λ` (`norm_normPair_le`).
* `kernel_pairs`: a signed combination of support pairs with nonnegative conductances
  annihilates `ker L`.
-/

namespace CutQueryComplexity
namespace Spectral

open Matrix Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsHermitian)

/-- The eigenvector matrix. -/
def eU : Matrix (Fin n) (Fin n) ℝ := (hL.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)

/-- The spectral function `U diag(g ∘ λ) Uᵀ`. -/
def fnL (g : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  eU hL * diagonal (fun i => g (hL.eigenvalues i)) * star (eU hL)

theorem eU_star_mul : star (eU hL) * eU hL = 1 := Unitary.coe_star_mul_self _
theorem eU_mul_star : eU hL * star (eU hL) = 1 := Unitary.coe_mul_star_self _

theorem fnL_id : fnL hL id = L := by
  conv_rhs => rw [hL.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

theorem fnL_mul (g h : ℝ → ℝ) : fnL hL g * fnL hL h = fnL hL (fun t => g t * h t) := by
  unfold fnL
  calc eU hL * diagonal (fun i => g (hL.eigenvalues i)) * star (eU hL) *
        (eU hL * diagonal (fun i => h (hL.eigenvalues i)) * star (eU hL))
      = eU hL * diagonal (fun i => g (hL.eigenvalues i)) * (star (eU hL) * eU hL) *
          diagonal (fun i => h (hL.eigenvalues i)) * star (eU hL) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [eU_star_mul, Matrix.mul_one, Matrix.mul_assoc (eU hL), diagonal_mul_diagonal]

theorem fnL_congr {g h : ℝ → ℝ} (hgh : ∀ i, g (hL.eigenvalues i) = h (hL.eigenvalues i)) :
    fnL hL g = fnL hL h := by
  unfold fnL; congr 2; ext i j; simp [diagonal_apply, hgh]

theorem fnL_isHermitian (g : ℝ → ℝ) : (fnL hL g).IsHermitian := by
  unfold fnL IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose,
    conjTranspose_conjTranspose, Matrix.mul_assoc]
  congr 2

theorem star_eU_eq : star (eU hL) = (eU hL)ᵀ := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- `xᵀ (fnL g) x = Σ_i g(λ_i) y_i²` with `y = Uᵀ x`. -/
theorem quad_fnL (g : ℝ → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (fnL hL g *ᵥ x) =
      ∑ i, g (hL.eigenvalues i) * (star (eU hL) *ᵥ x) i * (star (eU hL) *ᵥ x) i := by
  unfold fnL
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, ← star_eU_eq,
    dotProduct]
  simp only [mulVec_diagonal]
  exact sum_congr rfl fun i _ => by ring

theorem dot_star_eU (x : Fin n → ℝ) :
    (star (eU hL) *ᵥ x) ⬝ᵥ (star (eU hL) *ᵥ x) = x ⬝ᵥ x := by
  have h : ∀ z, x ⬝ᵥ (eU hL *ᵥ z) = (star (eU hL) *ᵥ x) ⬝ᵥ z := fun z => by
    rw [star_eU_eq, mulVec_transpose, ← dotProduct_mulVec]
  rw [← h, mulVec_mulVec, eU_mul_star, one_mulVec]

/-- Eigenvalues of a positive semidefinite matrix are nonnegative. -/
theorem eigenvalues_nonneg (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (L *ᵥ x)) (i : Fin n) :
    0 ≤ hL.eigenvalues i := by
  have h := hpsd (eU hL *ᵥ Pi.single i 1)
  have h' := quad_fnL hL id (eU hL *ᵥ Pi.single i 1)
  rw [fnL_id] at h'
  simp only [mulVec_mulVec, eU_star_mul, one_mulVec] at h h'
  rw [h'] at h
  simpa [Pi.single_apply] using h

/-- Quadratic forms of spectral functions with values in `[0, 1]`. -/
theorem quad_fnL_le {g : ℝ → ℝ} (hg : ∀ i, 0 ≤ g (hL.eigenvalues i) ∧ g (hL.eigenvalues i) ≤ 1)
    (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ (fnL hL g *ᵥ x) ∧ x ⬝ᵥ (fnL hL g *ᵥ x) ≤ x ⬝ᵥ x := by
  rw [quad_fnL, ← dot_star_eU hL x]
  constructor
  · exact sum_nonneg fun i _ => by
      have := (hg i).1; rw [mul_assoc]; exact mul_nonneg this (mul_self_nonneg _)
  · refine sum_le_sum fun i _ => ?_
    rw [mul_assoc]
    exact mul_le_of_le_one_left (mul_self_nonneg _) (hg i).2

/-- `1/√t` on `t > 0`. -/
def gW (t : ℝ) : ℝ := if 0 < t then 1 / Real.sqrt t else 0
/-- The indicator of `t > 0`. -/
def gP (t : ℝ) : ℝ := if 0 < t then 1 else 0

/-- `W = L^{+1/2}`. -/
def matW : Matrix (Fin n) (Fin n) ℝ := fnL hL gW
/-- `R = L^{1/2}`. -/
def matR : Matrix (Fin n) (Fin n) ℝ := fnL hL Real.sqrt
/-- The projector onto the range. -/
def matP : Matrix (Fin n) (Fin n) ℝ := fnL hL gP

theorem matW_isHermitian : (matW hL).IsHermitian := fnL_isHermitian hL gW
theorem matR_isHermitian : (matR hL).IsHermitian := fnL_isHermitian hL Real.sqrt

theorem matW_mul_matR : matW hL * matR hL = matP hL := by
  rw [matW, matR, matP, fnL_mul]
  refine fnL_congr hL fun i => ?_
  unfold gW gP
  split_ifs with h
  · field_simp
  · simp

theorem matW_mul_mul_matW : matW hL * L * matW hL = matP hL := by
  have h : matW hL * fnL hL id * matW hL = matP hL := by
    rw [matW, matP, fnL_mul, fnL_mul]
    refine fnL_congr hL fun i => ?_
    unfold gW gP
    split_ifs with h
    · have hs : 0 < Real.sqrt (hL.eigenvalues i) := Real.sqrt_pos.mpr h
      have hsq := Real.mul_self_sqrt h.le
      simp only [id]
      field_simp
      linarith
    · simp
  rwa [fnL_id] at h


theorem matR_mul_matR (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (L *ᵥ x)) : matR hL * matR hL = L := by
  have h : matR hL * matR hL = fnL hL id := by
    rw [matR, fnL_mul]
    exact fnL_congr hL fun i => Real.mul_self_sqrt (eigenvalues_nonneg hL hpsd i)
  rwa [fnL_id] at h

theorem mul_matP (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (L *ᵥ x)) : L * matP hL = L := by
  have h : fnL hL id * matP hL = fnL hL id := by
    rw [matP, fnL_mul]
    refine fnL_congr hL fun i => ?_
    unfold gP
    split_ifs with h
    · simp
    · have := eigenvalues_nonneg hL hpsd i
      simp only [id, mul_zero]; linarith
  rwa [fnL_id] at h

theorem matP_quad (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (matP hL *ᵥ x) ∧ x ⬝ᵥ (matP hL *ᵥ x) ≤ x ⬝ᵥ x :=
  quad_fnL_le hL (fun i => by unfold gP; split_ifs <;> norm_num) x

/-- **Transfer from the normalized space.** -/
theorem transfer (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (L *ᵥ x)) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) (hker : ∀ k, L *ᵥ k = 0 → M *ᵥ k = 0) {δ : ℝ}
    (hδ : ‖matW hL * M * matW hL‖ ≤ δ) (v : Fin n → ℝ) :
    |v ⬝ᵥ (M *ᵥ v)| ≤ δ * (v ⬝ᵥ (L *ᵥ v)) := by
  set w := matP hL *ᵥ v
  set k := v - w
  have hk : L *ᵥ k = 0 := by
    simp only [k, w, mulVec_sub, mulVec_mulVec, mul_matP hL hpsd, sub_self]
  have hMk := hker k hk
  have hv : v = w + k := by simp [k]
  have h1 : v ⬝ᵥ (M *ᵥ v) = w ⬝ᵥ (M *ᵥ w) := by
    conv_lhs => rw [hv]
    rw [mulVec_add, hMk, add_zero, add_dotProduct, dot_mulVec_symm hM k w, hMk, zero_dotProduct,
      add_zero]
  set y := matR hL *ᵥ v
  have hw : w = matW hL *ᵥ y := by
    simp only [w, y, mulVec_mulVec, matW_mul_matR]
  have hWsym := matW_isHermitian hL
  have h2 : w ⬝ᵥ (M *ᵥ w) = y ⬝ᵥ ((matW hL * M * matW hL) *ᵥ y) := by
    rw [hw, ← mulVec_mulVec, ← mulVec_mulVec, dot_mulVec_symm hWsym]
  have h3 : y ⬝ᵥ y = v ⬝ᵥ (L *ᵥ v) := by
    have hRsym := matR_isHermitian hL
    rw [show y ⬝ᵥ y = v ⬝ᵥ (matR hL *ᵥ y) from (dot_mulVec_symm hRsym v y).symm, mulVec_mulVec,
      matR_mul_matR hL hpsd]
  rw [h1, h2, ← h3]
  exact (abs_quad_le_norm _ y).trans (mul_le_mul_of_nonneg_right hδ (dot_self_nonneg y))

/-- The normalized pair matrix `A_e = W (ω_e a_e a_eᵀ) W`. -/
def normPair (ω : Sym2 (Fin n) → ℝ) (e : Sym2 (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  matW hL * (ω e • pairMat e) * matW hL

theorem quad_normPair (ω : Sym2 (Fin n) → ℝ) (e : Sym2 (Fin n)) (x : Fin n → ℝ) :
    x ⬝ᵥ (normPair hL ω e *ᵥ x) = ω e * pairSq (matW hL *ᵥ x) e := by
  rw [normPair, ← mulVec_mulVec, ← mulVec_mulVec, dot_mulVec_symm (matW_isHermitian hL),
    smul_mulVec, dotProduct_smul, quad_pairMat, smul_eq_mul]

theorem normPair_isHermitian (ω : Sym2 (Fin n) → ℝ) (e : Sym2 (Fin n)) :
    (normPair hL ω e).IsHermitian := by
  have hW := matW_isHermitian hL
  rw [normPair, IsHermitian, conjTranspose_mul, conjTranspose_mul, hW.eq, conjTranspose_smul,
    star_trivial, (pairMat_isHermitian e).eq, Matrix.mul_assoc]

theorem normPair_psd {ω : Sym2 (Fin n) → ℝ} (hω : ∀ e, 0 ≤ ω e) (e : Sym2 (Fin n))
    (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ (normPair hL ω e *ᵥ x) := by
  rw [quad_normPair]; exact mul_nonneg (hω e) (pairSq_nonneg _ e)

/-- **The normalized pair matrices sum to at most `I`** on the support of `L`. -/
theorem sum_normPair_le {ω : Sym2 (Fin n) → ℝ} {S : Finset (Sym2 (Fin n))}
    (hLS : L = lap ω S) (x : Fin n → ℝ) :
    ∑ e ∈ S, x ⬝ᵥ (normPair hL ω e *ᵥ x) ≤ x ⬝ᵥ x := by
  have : ∑ e ∈ S, x ⬝ᵥ (normPair hL ω e *ᵥ x) =
      x ⬝ᵥ ((matW hL * lap ω S * matW hL) *ᵥ x) := by
    rw [← dotProduct_sum, ← sum_mulVec, lap, Matrix.mul_sum, Matrix.sum_mul]
    rfl
  rw [this, ← hLS, matW_mul_mul_matW]
  exact (matP_quad hL x).2

/-- **Bundle domination bounds the normalized norm.** -/
theorem norm_normPair_le {ω : Sym2 (Fin n) → ℝ} (hω : ∀ e, 0 ≤ ω e)
    {S : Finset (Sym2 (Fin n))} (hLS : L = lap ω S) {e : Sym2 (Fin n)} {lam : ℝ}
    (hlam : 0 ≤ lam) (hlev : ∀ y, ω e * pairSq y e ≤ lam * energy ω S y) :
    ‖normPair hL ω e‖ ≤ lam := by
  refine norm_le_of_abs_quad_le (normPair_isHermitian hL ω e) hlam fun x => ?_
  rw [abs_of_nonneg (normPair_psd hL hω e x), quad_normPair]
  have h1 := hlev (matW hL *ᵥ x)
  have h2 : energy ω S (matW hL *ᵥ x) = x ⬝ᵥ (matP hL *ᵥ x) := by
    rw [← quad_lap, ← hLS, ← matW_mul_mul_matW, ← mulVec_mulVec, ← mulVec_mulVec,
      dot_mulVec_symm (matW_isHermitian hL), mulVec_mulVec]
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (matP_quad hL x).2 hlam)

/-- **Support pairs annihilate the kernel.** -/
theorem kernel_pairs {ω : Sym2 (Fin n) → ℝ} (hω : ∀ e, 0 ≤ ω e) {S : Finset (Sym2 (Fin n))}
    (hLS : L = lap ω S) {ι : Type} (I : Finset ι) (q : ι → Sym2 (Fin n)) (hq : ∀ i ∈ I, q i ∈ S)
    (c : ι → ℝ) {k : Fin n → ℝ} (hk : L *ᵥ k = 0) :
    (∑ i ∈ I, c i • (ω (q i) • pairMat (q i))) *ᵥ k = 0 := by
  have hE : energy ω S k = 0 := (lap_mulVec_eq_zero_iff hω S k).mp (hLS ▸ hk)
  have hterm : ∀ e ∈ S, ω e * pairSq k e = 0 :=
    (sum_eq_zero_iff_of_nonneg fun e _ => mul_nonneg (hω e) (pairSq_nonneg k e)).mp hE
  rw [sum_mulVec]
  refine sum_eq_zero fun i hi => ?_
  rw [smul_mulVec, smul_mulVec]
  have hpair : ω (q i) • (pairMat (q i) *ᵥ k) = 0 := by
    rcases (mul_eq_zero.mp (hterm (q i) (hq i hi))) with h | h
    · simp [h]
    · generalize q i = e at h ⊢
      induction e using Sym2.ind with
      | h u v =>
          rw [pairSq_mk, sq_eq_zero_iff, sub_eq_zero] at h
          have : pairMat s(u, v) *ᵥ k = 0 := by
            rw [pairMat_mk, vecMulVec_mulVec, incVec_dot, h, sub_self]
            ext j; simp
          rw [this, smul_zero]
  rw [hpair, smul_zero]

end

end Spectral
end CutQueryComplexity
