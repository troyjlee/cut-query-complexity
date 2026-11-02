import CutQueryComplexity.ImplicitLP.NormalPerturb
import CutQueryComplexity.ImplicitLP.Repair

/-! # The normal-system envelope and preconditioned refinement (D7 item 5)

**Envelope.** If every row of `A` has squared norm at most `2` (`row norms ≤ √2`):
* `|(Ax)ᵢ| ≤ √2‖x‖₂` (`row_apply_le`);
* `‖Ax‖₂ ≤ √(2M)‖x‖₂` (`opnorm_le`) and `‖Aᵀy‖₂ ≤ √(2M)‖y‖₂` (`opnorm_transpose_le`), by
  Cauchy–Schwarz against the Frobenius norm.

The explicit rows `+e_j` give `xᵀ(AᵀDA)x ≥ d_min‖x‖₂²` whenever `D ≥ d_min` on those rows
(`gram_ge_of_idRows`). This is the lower bound in `eq:normalbounds`.

**Preconditioned refinement.** Suppose `(1−ε)P ⪯ L ⪯ (1+ε)P` as quadratic forms, `P` is
symmetric positive semidefinite and invertible, and `L` is symmetric. Then the Richardson step
`e ↦ e − P⁻¹Le` contracts the `L`-energy: `‖e'‖²_L ≤ ε²(1+ε)/(1−ε)‖e‖²_L` (`richardson_step`).
The proof uses the polarized Cauchy–Schwarz inequality `(eᵀBy)² ≤ ε²(eᵀPe)(yᵀPy)` for a symmetric
`B` with `|xᵀBx| ≤ ε xᵀPx` (`polar_cs`), extracting the coefficient from a quadratic in a scale
parameter instead of square roots. With `P` the explicit part plus the Laplacian of the D4
sparsifier, this gives the frozen normal solve to any relative energy accuracy.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ}

section Envelope

variable {A : Matrix (Fin M) (Fin r) ℝ}

theorem row_apply_le (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ 2) (x : Fin r → ℝ) (i : Fin M) :
    |(A *ᵥ x) i| ≤ Real.sqrt 2 * euc x := by
  have h := sum_mul_sq_le_sq_mul_sq univ (A i) x
  have h2 : (∑ j, A i j * x j) ^ 2 ≤ (Real.sqrt 2 * euc x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), euc_sq]
    exact h.trans (mul_le_mul_of_nonneg_right (hrow i) (sum_nonneg fun j _ => sq_nonneg _))
  exact abs_le_of_sq_le_sq' h2 (mul_nonneg (Real.sqrt_nonneg _) (euc_nonneg x)) |> fun h => abs_le.mpr h

theorem opnorm_le (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ 2) (x : Fin r → ℝ) :
    euc (A *ᵥ x) ≤ Real.sqrt (2 * M) * euc x := by
  have h : euc (A *ᵥ x) ^ 2 ≤ (Real.sqrt (2 * M) * euc x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), euc_sq]
    calc ∑ i, (A *ᵥ x) i ^ 2 ≤ ∑ _i : Fin M, 2 * euc x ^ 2 := sum_le_sum fun i _ => by
          have := row_apply_le hrow x i
          rw [← sq_abs]
          calc |(A *ᵥ x) i| ^ 2 ≤ (Real.sqrt 2 * euc x) ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) this 2
            _ = 2 * euc x ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
      _ = 2 * M * euc x ^ 2 := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  exact abs_le_of_sq_le_sq' h (mul_nonneg (Real.sqrt_nonneg _) (euc_nonneg x)) |>.2

theorem opnorm_transpose_le (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ 2) (y : Fin M → ℝ) :
    euc (Aᵀ *ᵥ y) ≤ Real.sqrt (2 * M) * euc y := by
  have h : euc (Aᵀ *ᵥ y) ^ 2 ≤ (Real.sqrt (2 * M) * euc y) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), euc_sq, euc_sq]
    have hj : ∀ j, (Aᵀ *ᵥ y) j ^ 2 ≤ (∑ i, A i j ^ 2) * ∑ i, y i ^ 2 := fun j => by
      have := sum_mul_sq_le_sq_mul_sq univ (fun i => A i j) y
      simpa [mulVec, dotProduct, transpose_apply] using this
    calc ∑ j, (Aᵀ *ᵥ y) j ^ 2 ≤ ∑ j, (∑ i, A i j ^ 2) * ∑ i, y i ^ 2 := sum_le_sum fun j _ => hj j
      _ = (∑ i, ∑ j, A i j ^ 2) * ∑ i, y i ^ 2 := by rw [← sum_mul, sum_comm]
      _ ≤ (∑ _i : Fin M, (2 : ℝ)) * ∑ i, y i ^ 2 :=
          mul_le_mul_of_nonneg_right (sum_le_sum fun i _ => hrow i) (sum_nonneg fun i _ => sq_nonneg _)
      _ = 2 * M * ∑ i, y i ^ 2 := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  exact abs_le_of_sq_le_sq' h (mul_nonneg (Real.sqrt_nonneg _) (euc_nonneg y)) |>.2

/-- The explicit identity rows give `xᵀ(AᵀDA)x ≥ d_min‖x‖²`. -/
theorem gram_ge_of_idRows {ι : Fin r → Fin M} (hι : IdRows A ι) {D : Fin M → ℝ}
    (hD0 : ∀ i, 0 ≤ D i) {dmin : ℝ} (hD : ∀ j, dmin ≤ D (ι j)) (x : Fin r → ℝ) :
    dmin * euc x ^ 2 ≤ x ⬝ᵥ (gram A D *ᵥ x) := by
  rw [gram_quad, euc_sq, mul_sum]
  have hrow : ∀ j, (A *ᵥ x) (ι j) = x j := fun j => by
    simp [mulVec, hι.2 j, dotProduct, Pi.single_apply]
  calc ∑ j, dmin * x j ^ 2 ≤ ∑ j, D (ι j) * (A *ᵥ x) (ι j) ^ 2 :=
        sum_le_sum fun j _ => by rw [hrow]; exact mul_le_mul_of_nonneg_right (hD j) (sq_nonneg _)
    _ = ∑ i ∈ univ.image ι, D i * (A *ᵥ x) i ^ 2 := by
        rw [sum_image fun a _ b _ h => hι.1 h]
    _ ≤ ∑ i, D i * (A *ᵥ x) i ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ =>
          mul_nonneg (hD0 i) (sq_nonneg _)

end Envelope

section Refinement

variable {P L B : Matrix (Fin r) (Fin r) ℝ}

/-- **Polarized Cauchy–Schwarz** for a symmetric form bounded by a PSD form. -/
theorem polar_cs (hB : Bᵀ = B) (hP : Pᵀ = P) {ε : ℝ} (hε : 0 < ε)
    (hbd : ∀ x, |x ⬝ᵥ (B *ᵥ x)| ≤ ε * (x ⬝ᵥ (P *ᵥ x))) (e y : Fin r → ℝ) :
    (e ⬝ᵥ (B *ᵥ y)) ^ 2 ≤ ε ^ 2 * (e ⬝ᵥ (P *ᵥ e)) * (y ⬝ᵥ (P *ᵥ y)) := by
  -- `2s(eᵀBy) ≤ ε(s² eᵀPe + yᵀPy)` for every real `s`, from polarization
  have hpol : ∀ s : ℝ, ∀ e : Fin r → ℝ,
      2 * s * (e ⬝ᵥ (B *ᵥ y)) ≤ ε * (s ^ 2 * (e ⬝ᵥ (P *ᵥ e)) + y ⬝ᵥ (P *ᵥ y)) := by
    intro s e
    have h1 := hbd (s • e + y)
    have h2 := hbd (s • e - y)
    have eB : ∀ u v : Fin r → ℝ, u ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (B *ᵥ u) := dot_mulVec_comm hB
    have eP : ∀ u v : Fin r → ℝ, u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := dot_mulVec_comm hP
    simp only [mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub, add_dotProduct,
      sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1 h2
    rw [eB y e, eP y e] at h1 h2
    have := (abs_le.mp h1).2
    have := (abs_le.mp h2).1
    nlinarith
  set c := e ⬝ᵥ (B *ᵥ y)
  set u := e ⬝ᵥ (P *ᵥ e)
  set v := y ⬝ᵥ (P *ᵥ y)
  have hu : 0 ≤ u := by
    have := hbd e; have h0 := abs_nonneg (e ⬝ᵥ (B *ᵥ e))
    have : 0 ≤ ε * u := h0.trans this
    exact nonneg_of_mul_nonneg_right (by linarith) hε |> fun h => by nlinarith
  -- reduce to `c ≥ 0` by replacing `e` with `−e`
  have key : ∀ c' u' : ℝ, 0 ≤ c' → 0 ≤ u' →
      (∀ s : ℝ, 2 * s * c' ≤ ε * (s ^ 2 * u' + v)) → c' ^ 2 ≤ ε ^ 2 * u' * v := by
    intro c' u' hc' hu' hq
    rcases eq_or_lt_of_le hc' with h0 | hcp
    · have hv : 0 ≤ v := by
        have := hq 0; simp at this; nlinarith
      rw [← h0, show (0 : ℝ) ^ 2 = 0 by norm_num]
      exact mul_nonneg (mul_nonneg (sq_nonneg ε) hu') hv
    rcases eq_or_lt_of_le hu' with hu0 | hup
    · -- `u' = 0` contradicts `c' > 0`
      exfalso
      have := hq ((ε * v + 1) / (2 * c'))
      rw [← hu0] at this
      field_simp at this
      nlinarith
    · have := hq (c' / (ε * u'))
      field_simp at this
      nlinarith
  rcases le_total 0 c with hc | hc
  · exact key c u hc hu fun s => hpol s e
  · have hneg : ∀ s : ℝ, 2 * s * (-c) ≤ ε * (s ^ 2 * u + v) := fun s => by
      have := hpol s (-e)
      simp only [neg_dotProduct, mulVec_neg, dotProduct_neg, neg_neg] at this
      linarith
    have := key (-c) u (by linarith) hu hneg
    nlinarith

/-- **The Richardson step contracts the energy error.** -/
theorem richardson_step (hL : Lᵀ = L) (hP : Pᵀ = P) (hPdet : P.det ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (hlo : ∀ x, (1 - ε) * (x ⬝ᵥ (P *ᵥ x)) ≤ x ⬝ᵥ (L *ᵥ x))
    (hhi : ∀ x, x ⬝ᵥ (L *ᵥ x) ≤ (1 + ε) * (x ⬝ᵥ (P *ᵥ x))) (e : Fin r → ℝ) :
    let e' := e - P⁻¹ *ᵥ (L *ᵥ e)
    e' ⬝ᵥ (L *ᵥ e') ≤ ε ^ 2 * (1 + ε) / (1 - ε) * (e ⬝ᵥ (L *ᵥ e)) := by
  intro e'
  set B := P - L
  have hB : Bᵀ = B := by simp [B, transpose_sub, hL, hP]
  have hbd : ∀ x, |x ⬝ᵥ (B *ᵥ x)| ≤ ε * (x ⬝ᵥ (P *ᵥ x)) := fun x => by
    have e1 : x ⬝ᵥ (B *ᵥ x) = x ⬝ᵥ (P *ᵥ x) - x ⬝ᵥ (L *ᵥ x) := by
      simp [B, sub_mulVec, dotProduct_sub]
    rw [e1, abs_le]; constructor <;> nlinarith [hlo x, hhi x]
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  set g := B *ᵥ e
  have he' : e' = P⁻¹ *ᵥ g := by
    simp only [e', g, B, sub_mulVec, mulVec_sub, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hPf : P *ᵥ e' = g := by
    rw [he', mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  -- `e'ᵀPe' = gᵀe' = eᵀBe' ≤ ε√(ePe)√(e'Pe')`, so `e'ᵀPe' ≤ ε² eᵀPe`
  have ht : e' ⬝ᵥ (P *ᵥ e') = e ⬝ᵥ (B *ᵥ e') := by
    rw [hPf, dot_mulVec_comm hB e e']
  have hcs := polar_cs hB hP hε hbd e e'
  rw [← ht] at hcs
  set t := e' ⬝ᵥ (P *ᵥ e')
  have ht0 : 0 ≤ t := by
    have h1 := hlo e'; have h2 := hhi e'
    nlinarith
  have hePe : 0 ≤ e ⬝ᵥ (P *ᵥ e) := by
    have h1 := hlo e; have h2 := hhi e; nlinarith
  have htb : t ≤ ε ^ 2 * (e ⬝ᵥ (P *ᵥ e)) := by
    rcases eq_or_lt_of_le ht0 with h0 | hpos
    · rw [← h0]; positivity
    · have : t * t ≤ ε ^ 2 * (e ⬝ᵥ (P *ᵥ e)) * t := by nlinarith
      exact le_of_mul_le_mul_right (by linarith) hpos
  have hPL : e ⬝ᵥ (P *ᵥ e) ≤ (e ⬝ᵥ (L *ᵥ e)) / (1 - ε) := by
    rw [le_div_iff₀ (by linarith)]; linarith [hlo e]
  calc e' ⬝ᵥ (L *ᵥ e') ≤ (1 + ε) * t := hhi e'
    _ ≤ (1 + ε) * (ε ^ 2 * ((e ⬝ᵥ (L *ᵥ e)) / (1 - ε))) :=
        mul_le_mul_of_nonneg_left (htb.trans (mul_le_mul_of_nonneg_left hPL (sq_nonneg _)))
          (by linarith)
    _ = ε ^ 2 * (1 + ε) / (1 - ε) * (e ⬝ᵥ (L *ᵥ e)) := by ring

/-- **The sparsifier preconditioner.** If `(1−ε)xᵀL_G x ≤ xᵀL_Q x ≤ (1+ε)xᵀL_G x` and `E` is PSD,
then `P = L_Q + E` and `L = L_G + E` satisfy `(1−2ε)P ⪯ L ⪯ (1+2ε)P` for `0 ≤ ε ≤ 1/4`. -/
theorem precond_of_sparsifier {LG LQ E : Matrix (Fin r) (Fin r) ℝ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 4) (hE : ∀ x, 0 ≤ x ⬝ᵥ (E *ᵥ x)) (hG : ∀ x, 0 ≤ x ⬝ᵥ (LG *ᵥ x))
    (hlo : ∀ x, (1 - ε) * (x ⬝ᵥ (LG *ᵥ x)) ≤ x ⬝ᵥ (LQ *ᵥ x))
    (hhi : ∀ x, x ⬝ᵥ (LQ *ᵥ x) ≤ (1 + ε) * (x ⬝ᵥ (LG *ᵥ x))) (x : Fin r → ℝ) :
    (1 - 2 * ε) * (x ⬝ᵥ ((LQ + E) *ᵥ x)) ≤ x ⬝ᵥ ((LG + E) *ᵥ x) ∧
      x ⬝ᵥ ((LG + E) *ᵥ x) ≤ (1 + 2 * ε) * (x ⬝ᵥ ((LQ + E) *ᵥ x)) := by
  simp only [add_mulVec, dotProduct_add]
  have h1 := hlo x; have h2 := hhi x; have h3 := hE x; have h4 := hG x
  constructor
  · nlinarith
  · -- `L_G ≤ L_Q/(1−ε) ≤ (1+2ε)L_Q`
    have : x ⬝ᵥ (LG *ᵥ x) ≤ (1 + 2 * ε) * (x ⬝ᵥ (LQ *ᵥ x)) := by nlinarith
    nlinarith

/-- **Iterated refinement:** `n` Richardson steps reduce the energy error by `cⁿ`, with
`c = ε²(1+ε)/(1−ε)`. -/
theorem richardson_iter (hL : Lᵀ = L) (hP : Pᵀ = P) (hPdet : P.det ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (hlo : ∀ x, (1 - ε) * (x ⬝ᵥ (P *ᵥ x)) ≤ x ⬝ᵥ (L *ᵥ x))
    (hhi : ∀ x, x ⬝ᵥ (L *ᵥ x) ≤ (1 + ε) * (x ⬝ᵥ (P *ᵥ x))) (b x₀ xs : Fin r → ℝ)
    (hxs : L *ᵥ xs = b) (n : ℕ) :
    let step : (Fin r → ℝ) → Fin r → ℝ := fun x => x + P⁻¹ *ᵥ (b - L *ᵥ x)
    (step^[n] x₀ - xs) ⬝ᵥ (L *ᵥ (step^[n] x₀ - xs)) ≤
      (ε ^ 2 * (1 + ε) / (1 - ε)) ^ n * ((x₀ - xs) ⬝ᵥ (L *ᵥ (x₀ - xs))) := by
  intro step
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      set x := step^[n] x₀
      have he : step x - xs = (x - xs) - P⁻¹ *ᵥ (L *ᵥ (x - xs)) := by
        simp only [step, mulVec_sub, hxs]; abel
      have h := richardson_step hL hP hPdet hε hε1 hlo hhi (x - xs)
      rw [he]
      have hc : 0 ≤ ε ^ 2 * (1 + ε) / (1 - ε) := div_nonneg (by positivity) (by linarith)
      calc _ ≤ ε ^ 2 * (1 + ε) / (1 - ε) * ((x - xs) ⬝ᵥ (L *ᵥ (x - xs))) := h
        _ ≤ ε ^ 2 * (1 + ε) / (1 - ε) * ((ε ^ 2 * (1 + ε) / (1 - ε)) ^ n *
              ((x₀ - xs) ⬝ᵥ (L *ᵥ (x₀ - xs)))) := mul_le_mul_of_nonneg_left ih hc
        _ = _ := by rw [pow_succ]; ring

end Refinement

end

end ImplicitLP
end CutQueryComplexity
