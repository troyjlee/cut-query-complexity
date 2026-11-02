import CutQueryComplexity.ImplicitLP.GMove

/-! # The finite-interval barrier (`eq:barrier`; Lee–Sidford audit)

For `φᵢ = −log cos θᵢ` with `θᵢ = κᵢ(xᵢ − mᵢ)` and `κᵢ = π/(uᵢ − ℓᵢ)`, we have
`φᵢ' = κᵢ tan θᵢ` (`barDphi`) and `Sᵢ = √φᵢ'' = κᵢ / cos θᵢ` (`barS`). The slack
`sᵢ = min{xᵢ − ℓᵢ, uᵢ − xᵢ}` equals `(π/2 − |θᵢ|)/κᵢ` (`slack_eq`).

`barrier_bounds` proves the audited draft's `eq:barrier`:
`|φ'| ≤ S`, `|φ'| s ≤ 1`, `1 ≤ S s ≤ 2`, `κ ≤ S`, and `φ'(v − x) ≤ 1` for `ℓ ≤ v ≤ u`.
With box widths `uᵢ − ℓᵢ ≤ U`, `κᵢ ≤ Sᵢ` gives `U⁻¹ ≤ Sᵢ`.

The common core is `abs_sin_mul_le_cos`: `|sin θ|(π/2 − |θ|) ≤ cos θ` for `|θ| < π/2`. This is
`y cos y ≤ sin y` for `y = π/2 − |θ|`, i.e. `y ≤ tan y`.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Real

noncomputable section

/-- `|sin θ| (π/2 − |θ|) ≤ cos θ` for `|θ| < π/2`. -/
theorem abs_sin_mul_le_cos {θ : ℝ} (h : |θ| < π / 2) : |sin θ| * (π / 2 - |θ|) ≤ cos θ := by
  set y := π / 2 - |θ|
  have hy0 : 0 < y := by simp only [y]; linarith
  have hy1 : y ≤ π / 2 := by simp only [y]; linarith [abs_nonneg θ]
  have hcos : cos θ = sin y := by rw [← cos_abs, ← sin_pi_div_two_sub]
  have hsin : |sin θ| = cos y := by
    rw [show y = π / 2 - |θ| from rfl, cos_pi_div_two_sub, ← abs_sin_eq_sin_abs_of_abs_le_pi]
    · linarith [pi_pos]
  rw [hcos, hsin]
  rcases eq_or_lt_of_le hy1 with he | hlt
  · rw [he, cos_pi_div_two, zero_mul]; exact (sin_pos_of_pos_of_lt_pi (by linarith [pi_pos])
      (by linarith [pi_pos])).le
  · have hc : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
    have := le_tan hy0.le hlt
    rw [tan_eq_sin_div_cos, le_div_iff₀ hc] at this
    linarith [mul_comm (cos y) y]

variable {κ θ : ℝ}

/-- **`eq:barrier`** in the angle variable. With `φ' = κ tan θ`, `S = κ/cos θ`,
`s = (π/2 − |θ|)/κ`, and `|θ| < π/2`. -/
theorem barrier_bounds (hκ : 0 < κ) (h : |θ| < π / 2) :
    |κ * tan θ| ≤ κ / cos θ ∧ |κ * tan θ| * ((π / 2 - |θ|) / κ) ≤ 1 ∧
      1 ≤ κ / cos θ * ((π / 2 - |θ|) / κ) ∧ κ / cos θ * ((π / 2 - |θ|) / κ) ≤ 2 ∧
      κ ≤ κ / cos θ ∧
      ∀ θv, |θv| ≤ π / 2 → κ * tan θ * ((θv - θ) / κ) ≤ 1 := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ], by
    linarith [le_abs_self θ]⟩
  have hc1 : cos θ ≤ 1 := cos_le_one θ
  have hkey := abs_sin_mul_le_cos h
  set y := π / 2 - |θ|
  have hy0 : 0 < y := by simp only [y]; linarith
  have hcy : cos θ = sin y := by rw [← cos_abs, ← sin_pi_div_two_sub]
  have htan : |κ * tan θ| = κ * |sin θ| / cos θ := by
    rw [abs_mul, abs_of_pos hκ, tan_eq_sin_div_cos, abs_div, abs_of_pos hc]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htan, div_le_div_iff_of_pos_right hc]
    exact mul_le_of_le_one_right hκ.le (abs_sin_le_one θ)
  · rw [htan]
    rw [show κ * |sin θ| / cos θ * (y / κ) = |sin θ| * y / cos θ by field_simp]
    rw [div_le_one hc]; exact hkey
  · rw [show κ / cos θ * (y / κ) = y / cos θ by field_simp, le_div_iff₀ hc, one_mul, hcy]
    exact (sin_lt hy0).le
  · rw [show κ / cos θ * (y / κ) = y / cos θ by field_simp, div_le_iff₀ hc, hcy]
    have := mul_le_sin hy0.le (by simp only [y]; linarith [abs_nonneg θ])
    have hpi : π ≤ 4 := pi_le_four
    have : y ≤ 2 / π * y * 2 := by
      rw [show 2 / π * y * 2 = 4 / π * y by ring]
      exact le_mul_of_one_le_left hy0.le (by rw [le_div_iff₀ pi_pos]; linarith)
    linarith
  · rw [le_div_iff₀ hc]; exact mul_le_of_le_one_right hκ.le hc1
  · intro θv hv
    rw [show κ * tan θ * ((θv - θ) / κ) = tan θ * (θv - θ) by field_simp]
    rw [tan_eq_sin_div_cos, div_mul_eq_mul_div, div_le_one hc]
    rcases le_total 0 θ with hθ | hθ
    · have hθπ : θ ≤ π := by have := le_abs_self θ; linarith [pi_pos]
      have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ hθπ
      have : θv - θ ≤ y := by simp only [y]; rw [abs_of_nonneg hθ]; linarith [le_abs_self θv]
      calc sin θ * (θv - θ) ≤ sin θ * y := mul_le_mul_of_nonneg_left this hs
        _ = |sin θ| * y := by rw [abs_of_nonneg hs]
        _ ≤ cos θ := hkey
    · have hθπ : -π ≤ θ := by have := neg_abs_le θ; linarith [pi_pos]
      have hs : sin θ ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le hθ hθπ
      have : -y ≤ θv - θ := by simp only [y]; rw [abs_of_nonpos hθ]; linarith [neg_abs_le θv]
      calc sin θ * (θv - θ) ≤ sin θ * (-y) := mul_le_mul_of_nonpos_left this hs
        _ = |sin θ| * y := by rw [abs_of_nonpos hs]; ring
        _ ≤ cos θ := hkey

/-- `φᵢ' = κᵢ tan θᵢ`. -/
def barDphi {M : ℕ} (κ m x : Fin M → ℝ) (i : Fin M) : ℝ := κ i * tan (theta κ m x i)

/-- The slack `min{xᵢ − ℓᵢ, uᵢ − xᵢ}` for the box `[mᵢ − π/(2κᵢ), mᵢ + π/(2κᵢ)]` equals
`(π/2 − |θᵢ|)/κᵢ`. -/
theorem slack_eq {k xi mi : ℝ} (hk : 0 < k) :
    min (xi - (mi - π / (2 * k))) ((mi + π / (2 * k)) - xi) = (π / 2 - |k * (xi - mi)|) / k := by
  rw [abs_mul, abs_of_pos hk]
  rcases le_total xi mi with h | h
  · rw [abs_of_nonpos (by linarith), min_eq_left (by linarith)]; field_simp; ring
  · rw [abs_of_nonneg (by linarith), min_eq_right (by linarith)]; field_simp; ring

/-- **The barrier inequalities at a point** (`eq:barrier`): `|φ'| ≤ S`, `|φ'| s ≤ 1`, and
`1 ≤ S s ≤ 2`. -/
theorem eq_barrier {M : ℕ} {κ m x : Fin M → ℝ} (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x)
    (i : Fin M) :
    |barDphi κ m x i| ≤ barS κ m x i ∧
      |barDphi κ m x i| * ((π / 2 - |theta κ m x i|) / κ i) ≤ 1 ∧
      1 ≤ barS κ m x i * ((π / 2 - |theta κ m x i|) / κ i) ∧
      barS κ m x i * ((π / 2 - |theta κ m x i|) / κ i) ≤ 2 ∧ κ i ≤ barS κ m x i := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := barrier_bounds (hκ i) (hx i)
  exact ⟨h1, h2, h3, h4, h5⟩

end

end ImplicitLP
end CutQueryComplexity
