import CutQueryComplexity.ImplicitLP.Projection

/-! # Size of the regularized Lewis weights (`eq:gsize`; Lee–Sidford audit)

Leverage scores of a full-rank `M × r` matrix sum to `r`, because the trace of the projection is
`tr((XᵀX)⁻¹XᵀX) = r` (`sum_lev`), and each lies in `(0, 1]`. So the Lewis weights satisfy
`Σ w = r` and `0 < wᵢ ≤ 1`, and `g = w + c₀` satisfies `Σ g = r + M c₀` and `c₀ < gᵢ ≤ 1 + c₀`
(`eq_gsize`). With the repaired `c₀ = 1/(2M)` this is `Σ g = r + 1/2` and
`1/(2M) < gᵢ ≤ 1 + 1/(2M)`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ}

/-- **Leverage scores sum to the rank:** `Σᵢ σᵢ(X) = r` when `XᵀX` is invertible. -/
theorem sum_lev {X : Matrix (Fin M) (Fin r) ℝ} (hX : (Xᵀ * X).det ≠ 0) : ∑ i, lev X i = r := by
  have : ∑ i, lev X i = (proj X).trace := rfl
  rw [this, proj, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hX), trace_one, Fintype.card_fin]

/-- **`eq:gsize`** for any regularization `c₀ ≥ 0`. -/
theorem eq_gsize {A : Matrix (Fin M) (Fin r) ℝ} {p : ℝ} (hA : (Aᵀ * A).det ≠ 0)
    (hrow : ∀ i, A i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2) (c₀ : ℝ) :
    (∑ i, (exp (lewisLog p A i) + c₀) = r + M * c₀) ∧
      ∀ i, c₀ < exp (lewisLog p A i) + c₀ ∧ exp (lewisLog p A i) + c₀ ≤ 1 + c₀ := by
  set X := diagonal (fun j => exp ((1 / 2 - 1 / p) * lewisLog p A j)) * A
  have hX : (Xᵀ * X).det ≠ 0 := diag_det hA fun j => exp_ne_zero _
  have hw : ∀ i, exp (lewisLog p A i) = lev X i := fun i => (lev_lewisLog hA hrow hp0 hp2 i).symm
  refine ⟨?_, fun i => ⟨by linarith [exp_pos (lewisLog p A i)], ?_⟩⟩
  · rw [sum_add_distrib]
    simp only [hw, sum_lev hX, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  · rw [hw]; linarith [lev_le_one hX i]

end

end ImplicitLP
end CutQueryComplexity
