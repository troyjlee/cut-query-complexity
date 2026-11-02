import CutQueryComplexity.ImplicitLP.Refine
import CutQueryComplexity.Sparsify.Recursion

/-! # The frozen normal solve from the D4 sparsifier (D7 item 5)

The frozen normal matrix splits as `L = Pzᵀ L_G Pz + E`. Here `Pz` reads the vertex-potential
block of a variable vector, `L_G = lap ω S` is the Laplacian of the hidden pair rows, and `E`
is the explicit part, which the identity rows make positive definite. D4's `Good` output `out`
satisfies `(1−δ)^R E₀ ≤ E_out ≤ (1+δ)^R E₀` for every potential vector. With the preconditioner
`P = Pzᵀ L_out Pz + E`:
* `(1−2ε)P ⪯ L ⪯ (1+2ε)P` (`frozen_precond`, via `precond_of_sparsifier`);
* `P` is invertible, because `xᵀPx ≥ d_min‖x‖² > 0` (`det_ne_zero_of_quad_pos`);
* `k` Richardson steps from `0` give relative energy error `β²` once `2ᵏβ ≥ 1` and `ε ≤ 1/8`
  (`frozen_solve`). This is exactly the hypothesis `hpt` of `direction_error`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Spectral

noncomputable section

variable {r n : ℕ}

/-- A symmetric form that is positive off zero has nonzero determinant. -/
theorem det_ne_zero_of_quad_pos {P : Matrix (Fin r) (Fin r) ℝ}
    (hP : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x)) : P.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have := hP v hv
  rw [hPv, dotProduct_zero] at this
  exact lt_irrefl _ this

theorem euc_pos_of_ne_zero {x : Fin r → ℝ} (hx : x ≠ 0) : 0 < euc x := by
  rcases (euc_nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso; apply hx
    have h2 : ∑ i, x i ^ 2 = 0 := by rw [← euc_sq, ← h]; ring
    funext i
    have := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).mp h2 i (mem_univ _)
    simpa using this

/-- The pulled-back Laplacian `Pzᵀ (lap ω S) Pz`. -/
def pullLap (Pz : Matrix (Fin n) (Fin r) ℝ) (ω : Sym2 (Fin n) → ℝ) (S : Finset (Sym2 (Fin n))) :
    Matrix (Fin r) (Fin r) ℝ :=
  Pzᵀ * lap ω S * Pz

theorem quad_pullLap (Pz : Matrix (Fin n) (Fin r) ℝ) (ω : Sym2 (Fin n) → ℝ)
    (S : Finset (Sym2 (Fin n))) (x : Fin r → ℝ) :
    x ⬝ᵥ (pullLap Pz ω S *ᵥ x) = energy ω S (Pz *ᵥ x) := by
  rw [pullLap, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    quad_lap]

theorem pullLap_symm (Pz : Matrix (Fin n) (Fin r) ℝ) (ω : Sym2 (Fin n) → ℝ)
    (S : Finset (Sym2 (Fin n))) : (pullLap Pz ω S)ᵀ = pullLap Pz ω S := by
  have h : (lap ω S)ᵀ = lap ω S := by
    have := (lap_isHermitian ω S).eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [pullLap, transpose_mul, transpose_mul, h, transpose_transpose, Matrix.mul_assoc]

/-- The stored output energy is the energy of the output weights on all pairs. -/
theorem Eo_eq_energy (out : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) :
    Sparsify.Eo out x = energy out univ x := rfl

theorem E0_eq_energy (G : DiGraph (Fin n)) (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) :
    Sparsify.E0 G w x =
      energy (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) x := rfl

theorem E0_nonneg (G : DiGraph (Fin n)) {w : Sym2 (Fin n) → ℝ} (hw0 : ∀ e, 0 ≤ w e)
    (x : Fin n → ℝ) : 0 ≤ Sparsify.E0 G w x := by
  rw [E0_eq_energy]
  refine energy_nonneg (fun e => ?_) _ x
  simp only [Sparsify.omegaR, Sparsify.cR, pow_zero, one_mul]
  exact mul_nonneg (Nat.cast_nonneg _) (hw0 e)

/-- **The D4 output is a two-sided preconditioner** for the frozen normal matrix
`Pzᵀ L_G Pz + E`, where `L_G` carries the D4 input energy `E₀`. -/
theorem frozen_precond {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ} {K t R : ℕ} {δ ε : ℝ}
    {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G w K t δ R out) (hw0 : ∀ e, 0 ≤ w e)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    (Pz : Matrix (Fin n) (Fin r) ℝ) {E : Matrix (Fin r) (Fin r) ℝ}
    (hE : ∀ x, 0 ≤ x ⬝ᵥ (E *ᵥ x)) (x : Fin r → ℝ) :
    let LG := pullLap Pz (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true)
    let LQ := pullLap Pz out univ
    (1 - 2 * ε) * (x ⬝ᵥ ((LQ + E) *ᵥ x)) ≤ x ⬝ᵥ ((LG + E) *ᵥ x) ∧
      x ⬝ᵥ ((LG + E) *ᵥ x) ≤ (1 + 2 * ε) * (x ⬝ᵥ ((LQ + E) *ᵥ x)) := by
  intro LG LQ
  have hq : ∀ y, y ⬝ᵥ (LG *ᵥ y) = Sparsify.E0 G w (Pz *ᵥ y) := fun y => by
    rw [quad_pullLap, E0_eq_energy]
  have hqo : ∀ y, y ⬝ᵥ (LQ *ᵥ y) = Sparsify.Eo out (Pz *ᵥ y) := fun y => by
    rw [quad_pullLap, Eo_eq_energy]
  refine precond_of_sparsifier hε0 hε hE (fun y => by rw [hq]; exact E0_nonneg G hw0 _)
    (fun y => ?_) (fun y => ?_) x
  · rw [hq, hqo]
    exact (mul_le_mul_of_nonneg_right hδlo (E0_nonneg G hw0 _)).trans (hgood.1 _).1
  · rw [hq, hqo]
    exact (hgood.1 _).2.trans (mul_le_mul_of_nonneg_right hδhi (E0_nonneg G hw0 _))

/-- **The frozen normal solve.** Run `k` preconditioned Richardson steps from `0` on
`L x = b`, with `L = Pzᵀ L_G Pz + E` and preconditioner `P = Pzᵀ L_out Pz + E` from a `Good` D4
output. The result `xₖ` satisfies `‖xₖ − x*‖²_L ≤ β²‖x*‖²_L` whenever `2ᵏβ ≥ 1`. -/
theorem frozen_solve {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ} {K t R : ℕ} {δ ε : ℝ}
    {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G w K t δ R out) (hw0 : ∀ e, 0 ≤ w e)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    (Pz : Matrix (Fin n) (Fin r) ℝ) {E : Matrix (Fin r) (Fin r) ℝ} (hEs : Eᵀ = E)
    {dmin : ℝ} (hdmin : 0 < dmin) (hE : ∀ x, dmin * euc x ^ 2 ≤ x ⬝ᵥ (E *ᵥ x))
    (b xs : Fin r → ℝ)
    (hxs : (pullLap Pz (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) + E)
      *ᵥ xs = b)
    {β : ℝ} (k : ℕ) (hk : 1 ≤ β * 2 ^ k) :
    let L := pullLap Pz (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) + E
    let P := pullLap Pz out univ + E
    let step : (Fin r → ℝ) → Fin r → ℝ := fun x => x + P⁻¹ *ᵥ (b - L *ᵥ x)
    P.det ≠ 0 ∧ (step^[k] 0 - xs) ⬝ᵥ (L *ᵥ (step^[k] 0 - xs)) ≤ β ^ 2 * (xs ⬝ᵥ (L *ᵥ xs)) := by
  intro L P step
  have hE0 : ∀ x, 0 ≤ x ⬝ᵥ (E *ᵥ x) := fun x =>
    (mul_nonneg hdmin.le (sq_nonneg _)).trans (hE x)
  have hbd := frozen_precond hgood hw0 hε0.le (by linarith) hδlo hδhi Pz hE0
  have hout0 : ∀ e, 0 ≤ out e := hgood.2.1
  have hPpos : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x) := fun x hx => by
    have h1 : 0 ≤ x ⬝ᵥ (pullLap Pz out univ *ᵥ x) := by
      rw [quad_pullLap]; exact energy_nonneg hout0 _ _
    have h2 := hE x
    have h3 : 0 < dmin * euc x ^ 2 := mul_pos hdmin (pow_pos (euc_pos_of_ne_zero hx) 2)
    simp only [P, add_mulVec, dotProduct_add]
    linarith
  have hPdet : P.det ≠ 0 := det_ne_zero_of_quad_pos hPpos
  refine ⟨hPdet, ?_⟩
  have hLs : Lᵀ = L := by simp [L, transpose_add, pullLap_symm, hEs]
  have hPs : Pᵀ = P := by simp [P, transpose_add, pullLap_symm, hEs]
  have hit := richardson_iter hLs hPs hPdet (ε := 2 * ε) (by linarith) (by linarith)
    (fun x => (hbd x).1) (fun x => (hbd x).2) b 0 xs hxs k
  simp only at hit
  -- the contraction factor is at most `1/4`
  have hc0 : 0 ≤ (2 * ε) ^ 2 * (1 + 2 * ε) / (1 - 2 * ε) :=
    div_nonneg (by positivity) (by linarith)
  have hc : (2 * ε) ^ 2 * (1 + 2 * ε) / (1 - 2 * ε) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hxsL : 0 ≤ xs ⬝ᵥ (L *ᵥ xs) := by
    simp only [L, add_mulVec, dotProduct_add]
    rw [quad_pullLap]
    exact add_nonneg (energy_nonneg (fun e => by
      simp only [Sparsify.omegaR, Sparsify.cR, pow_zero, one_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (hw0 e)) _ _) (hE0 xs)
  have hpow : (1 / 4 : ℝ) ^ k ≤ β ^ 2 := by
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have : (1 / 4 : ℝ) ^ k = 1 / (2 ^ k) ^ 2 := by
      rw [_root_.one_div_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  have hz : (0 : Fin r → ℝ) - xs = -xs := zero_sub xs
  rw [hz, mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg] at hit
  calc _ ≤ ((2 * ε) ^ 2 * (1 + 2 * ε) / (1 - 2 * ε)) ^ k * (xs ⬝ᵥ (L *ᵥ xs)) := hit
    _ ≤ (1 / 4) ^ k * (xs ⬝ᵥ (L *ᵥ xs)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hc k) hxsL
    _ ≤ β ^ 2 * (xs ⬝ᵥ (L *ᵥ xs)) := mul_le_mul_of_nonneg_right hpow hxsL

end

end ImplicitLP
end CutQueryComplexity
