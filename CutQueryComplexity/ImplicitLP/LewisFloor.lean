import CutQueryComplexity.ImplicitLP.LewisIter
import CutQueryComplexity.ImplicitLP.Support

/-! # The concrete Lewis-weight floor `q_*` (D7 item 4, `eq:lewisfloor`)

Every leverage is at least its row's share of the Frobenius mass:
`σ(B)ᵢ = bᵢᵀ(BᵀB)⁻¹bᵢ ≥ ‖bᵢ‖² / Σⱼ‖bⱼ‖²` (`lev_ge_share`). This follows from the variational
formula at `y = bᵢ / Σⱼ‖bⱼ‖²` and Cauchy–Schwarz. For the barrier-scaled matrix `B = S⁻¹A`
the row norms satisfy `a₀² ≤ ‖aᵢ‖² ≤ 2`, `1/U ≤ Sᵢ ≤ 2/sᵢ` and `sᵢ ≥ s_*`, so every leverage is at
least `q_* = a₀² s_*² / (8 M U²)` (`lev_ge_qstar`). With `lewis_floor` this gives
`q_* ≤ (w_p)ᵢ`, the audited draft's `eq:lewisfloor` (`lewis_floor_qstar`).

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ} {B : Matrix (Fin M) (Fin r) ℝ}

theorem lev_eq_qform (i : Fin M) : lev B i = qform B (fun _ => 1) i := by
  have h := lev_diag (B := B) (fun _ => 1) i
  simp only [one_pow, one_mul] at h
  rwa [show diagonal (fun _ : Fin M => (1 : ℝ)) * B = B by
    rw [show diagonal (fun _ : Fin M => (1 : ℝ)) = 1 from diagonal_one, Matrix.one_mul]] at h

/-- The variational formula at `y = b/T`: `bᵀb/T ≤ bᵀG⁻¹b` when `bᵀGb ≤ T bᵀb`. -/
theorem invQuad_ge {G : Matrix (Fin r) (Fin r) ℝ} (hG : Gᵀ = G)
    (hpsd : ∀ y, 0 ≤ y ⬝ᵥ (G *ᵥ y)) (hdet : G.det ≠ 0) (b : Fin r → ℝ) {T : ℝ} (hT0 : 0 < T)
    (hbGb : b ⬝ᵥ (G *ᵥ b) ≤ T * (b ⬝ᵥ b)) : (b ⬝ᵥ b) / T ≤ b ⬝ᵥ (G⁻¹ *ᵥ b) := by
  have h := variational_le hG hpsd hdet b ((1 / T) • b)
  simp only [dotProduct_smul, mulVec_smul, smul_dotProduct, smul_eq_mul] at h
  have hTi : 0 ≤ 1 / T := by positivity
  have h1 : 1 / T * (1 / T * (b ⬝ᵥ (G *ᵥ b))) ≤ 1 / T * (1 / T * (T * (b ⬝ᵥ b))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbGb hTi) hTi
  have h2 : 1 / T * (1 / T * (T * (b ⬝ᵥ b))) = (b ⬝ᵥ b) / T := by field_simp
  have h3 : 2 * (1 / T * (b ⬝ᵥ b)) = 2 * ((b ⬝ᵥ b) / T) := by ring
  linarith

theorem dot_self_eq_euc_sq (b : Fin r → ℝ) : b ⬝ᵥ b = euc b ^ 2 := by
  rw [euc_sq]; simp [dotProduct, sq]

/-- **A leverage is at least its row's share of the Frobenius mass.** -/
theorem lev_ge_share (hB : (Bᵀ * B).det ≠ 0) (i : Fin M) :
    euc (B i) ^ 2 / ∑ j, euc (B j) ^ 2 ≤ lev B i := by
  rw [lev_eq_qform, qform]
  have hpsd : ∀ y, 0 ≤ y ⬝ᵥ (gram B (fun _ => (1 : ℝ)) *ᵥ y) := gram_psd fun _ => zero_le_one
  have hdet : (gram B (fun _ => (1 : ℝ))).det ≠ 0 := gram_det_ne hB fun _ => one_pos
  have hq0 : 0 ≤ B i ⬝ᵥ ((gram B (fun _ => (1 : ℝ)))⁻¹ *ᵥ B i) := by
    simpa using variational_le (gram_symm _) hpsd hdet (B i) 0
  rcases (sum_nonneg fun j _ => sq_nonneg (euc (B j)) :
      0 ≤ ∑ j, euc (B j) ^ 2).lt_or_eq with hT0 | hT
  · have hbGb : B i ⬝ᵥ (gram B (fun _ => (1 : ℝ)) *ᵥ B i) ≤
        (∑ j, euc (B j) ^ 2) * (B i ⬝ᵥ B i) := by
      rw [gram_quad, dot_self_eq_euc_sq, sum_mul]
      refine sum_le_sum fun j _ => ?_
      have := sum_mul_sq_le_sq_mul_sq univ (B j) (B i)
      rw [one_mul, euc_sq, euc_sq]
      simpa [mulVec, dotProduct] using this
    have := invQuad_ge (gram_symm _) hpsd hdet (B i) hT0 hbGb
    rwa [dot_self_eq_euc_sq] at this
  · rw [← hT, div_zero]; exact hq0

/-- **The concrete leverage floor** for the barrier-scaled matrix `B = S⁻¹A`. -/
theorem lev_ge_qstar {A : Matrix (Fin M) (Fin r) ℝ} {S sl : Fin M → ℝ} {a0 U sst : ℝ}
    (hB : ((diagonal (fun i => (S i)⁻¹) * A)ᵀ * (diagonal (fun i => (S i)⁻¹) * A)).det ≠ 0)
    (hM : 0 < M) (ha0 : 0 < a0) (hU : 0 < U) (hsst : 0 < sst)
    (hrowlo : ∀ i, a0 ^ 2 ≤ euc (A i) ^ 2) (hrowhi : ∀ i, euc (A i) ^ 2 ≤ 2)
    (hSlo : ∀ i, 1 / U ≤ S i) (hShi : ∀ i, S i ≤ 2 / sl i) (hsl : ∀ i, sst ≤ sl i) (i : Fin M) :
    a0 ^ 2 * sst ^ 2 / (8 * M * U ^ 2) ≤ lev (diagonal (fun i => (S i)⁻¹) * A) i := by
  set B := diagonal (fun i => (S i)⁻¹) * A
  have hrowB : ∀ j, B j = (S j)⁻¹ • A j := fun j => by
    funext k; simp [B, diagonal_mul]
  have hS0 : ∀ j, 0 < S j := fun j => lt_of_lt_of_le (by positivity) (hSlo j)
  have hnorm : ∀ j, euc (B j) ^ 2 = euc (A j) ^ 2 / S j ^ 2 := fun j => by
    rw [hrowB, euc_smul, mul_pow, sq_abs, inv_pow, div_eq_inv_mul]
  -- the row's own mass and the total mass
  have hown : a0 ^ 2 * sst ^ 2 / 4 ≤ euc (B i) ^ 2 := by
    rw [hnorm, le_div_iff₀ (pow_pos (hS0 i) 2)]
    have hsl0 : 0 < sl i := lt_of_lt_of_le hsst (hsl i)
    have h1 : S i * sl i ≤ 2 := by
      have := hShi i; rw [le_div_iff₀ hsl0] at this; linarith
    have h2 : S i * sst ≤ 2 := le_trans (mul_le_mul_of_nonneg_left (hsl i) (hS0 i).le) h1
    have h3 : (S i * sst) ^ 2 ≤ 4 := by nlinarith [mul_pos (hS0 i) hsst]
    have h4 := hrowlo i
    nlinarith [sq_nonneg a0]
  have htot : ∑ j, euc (B j) ^ 2 ≤ M * (2 * U ^ 2) := by
    calc ∑ j, euc (B j) ^ 2 ≤ ∑ _j : Fin M, 2 * U ^ 2 := sum_le_sum fun j _ => by
          rw [hnorm, div_le_iff₀ (pow_pos (hS0 j) 2)]
          have h1 : 1 ≤ U * S j := by
            have := hSlo j; rw [div_le_iff₀ hU] at this; linarith
          have h2 : 1 ≤ (U * S j) ^ 2 := by nlinarith
          nlinarith [hrowhi j]
      _ = M * (2 * U ^ 2) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have htot0 : 0 < ∑ j, euc (B j) ^ 2 :=
    lt_of_lt_of_le (by positivity) (hown.trans (single_le_sum (f := fun j => euc (B j) ^ 2)
      (fun j _ => sq_nonneg _) (mem_univ i)))
  have hshare := lev_ge_share hB i
  calc a0 ^ 2 * sst ^ 2 / (8 * M * U ^ 2)
      = (a0 ^ 2 * sst ^ 2 / 4) / (M * (2 * U ^ 2)) := by field_simp; ring
    _ ≤ euc (B i) ^ 2 / (M * (2 * U ^ 2)) :=
        div_le_div_of_nonneg_right hown (by positivity)
    _ ≤ euc (B i) ^ 2 / ∑ j, euc (B j) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) htot0 htot
    _ ≤ lev B i := hshare

/-- **`eq:lewisfloor`:** every Lewis weight of the barrier-scaled matrix is at least
`q_* = a₀² s_*² / (8 M U²)`. -/
theorem lewis_floor_qstar {A : Matrix (Fin M) (Fin r) ℝ} {S sl : Fin M → ℝ} {a0 U sst p : ℝ}
    (hB : ((diagonal (fun i => (S i)⁻¹) * A)ᵀ * (diagonal (fun i => (S i)⁻¹) * A)).det ≠ 0)
    (hrow : ∀ i, (diagonal (fun i => (S i)⁻¹) * A) i ≠ 0) (hp0 : 0 < p) (hp1 : p < 2)
    (hM : 0 < M) (ha0 : 0 < a0) (hU : 0 < U) (hsst : 0 < sst)
    (hrowlo : ∀ i, a0 ^ 2 ≤ euc (A i) ^ 2) (hrowhi : ∀ i, euc (A i) ^ 2 ≤ 2)
    (hSlo : ∀ i, 1 / U ≤ S i) (hShi : ∀ i, S i ≤ 2 / sl i) (hsl : ∀ i, sst ≤ sl i) (i : Fin M) :
    a0 ^ 2 * sst ^ 2 / (8 * M * U ^ 2) ≤
      exp (lewisLog p (diagonal (fun i => (S i)⁻¹) * A) i) :=
  lewis_floor hB hrow hp0 hp1
    (fun k => lev_ge_qstar hB hM ha0 hU hsst hrowlo hrowhi hSlo hShi hsl k) i

end

end ImplicitLP
end CutQueryComplexity
