import CutQueryComplexity.ImplicitLP.CenterClose

/-! # The noncircular slack floor (`eq:slackfloor`, D7)

`slack_floor`: suppose `x` is approximately central (as in `lem_center`) and a strictly feasible
reference `x⁰` with slacks at least `s₀` exists. The frozen-weight center `x̄` exists
(`center_exists`), its slacks are at least `min{s₀/2, w_min s₀/(4D)}` (`lem_slack`), and
`sᵢ(x) ≥ sᵢ(x̄)/2` (`lem_center`). Hence every slack of `x` is at least
`min{s₀/2, w_min s₀/(4D)}/2`.

`slack_floor_note` takes the repaired regime: `w ≥ 1/(4M̄)`, `Σw ≤ 4r`, `|t| ≤ 16r/ε`,
`‖c‖_∞ ≤ 4U`, `s₀ ≥ 1/U`, `M ≤ M̄`, `U ≥ 1`, and `0 < ε ≤ 1`. It gives the explicit floor
`s_* = ε/(2¹² r M̄² U³)`. Because the repaired weight floor is `1/(4M̄)` rather than the audited draft's
`r/M`, this is a factor of `r(M̄/M)²` below the audited draft's `ε/(2¹² M² U³)`. The later constants in D7
must use this value.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c w : Fin M → ℝ} {t : ℝ}

/-- **The slack floor**, in the general form. -/
theorem slack_floor (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ U : ℝ} (hc₀ : 0 ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) (hUnn : 0 ≤ U) (hU : ∀ i, π / κ i ≤ U) {x x₀ : Fin M → ℝ}
    (hx : x ∈ Feasible A b κ m) (hx₀ : x₀ ∈ Feasible A b κ m) {wmin s₀ D : ℝ}
    (hwmin : 0 < wmin) (hw : ∀ i, wmin ≤ w i)
    (hwin : ∀ i, |Real.log (w i) - Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)| ≤ 1 / 20)
    (hδ : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs₀ : 0 < s₀) (hs0 : ∀ i, s₀ ≤ slk κ m x₀ i) (hD : |t| * ‖c‖ * M * U + ∑ i, w i ≤ D)
    (i : Fin M) :
    min (s₀ / 2) (wmin * s₀ / (4 * D)) / 2 ≤ slk κ m x i := by
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le hwmin (hw i)
  obtain ⟨xbar, hxbar, hmin⟩ := center_exists (c := c) (t := t) hκ hwpos hx₀
  have h1 := lem_slack hκ hwmin hw hxbar hx₀ hmin hs₀ hs0 hU hD i
  have h2 := ((lem_center hA hrow hL hLM hκ hc₀ hcM hUnn hU hx hwpos hwin hδ hxbar hmin).1 i).2
  have : min (s₀ / 2) (wmin * s₀ / (4 * D)) ≤ slk κ m xbar i := h1
  linarith

/-- **The slack floor with the repaired constants:** `sᵢ(x) ≥ ε/(2¹² r M̄² U³)`. -/
theorem slack_floor_note (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ U Mbar ε : ℝ} (hc₀ : 0 ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) (hU1 : 1 ≤ U) (hU : ∀ i, π / κ i ≤ U) {x x₀ : Fin M → ℝ}
    (hx : x ∈ Feasible A b κ m) (hx₀ : x₀ ∈ Feasible A b κ m) (hMbar : (M : ℝ) ≤ Mbar)
    (hr : (1 : ℝ) ≤ r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hw : ∀ i, 1 / (4 * Mbar) ≤ w i) (hwsum : ∑ i, w i ≤ 4 * r) (ht : |t| ≤ 16 * r / ε)
    (hc : ‖c‖ ≤ 4 * U)
    (hwin : ∀ i, |Real.log (w i) - Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)| ≤ 1 / 20)
    (hδ : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs0 : ∀ i, 1 / U ≤ slk κ m x₀ i) (i : Fin M) :
    ε / (2 ^ 12 * r * Mbar ^ 2 * U ^ 3) ≤ slk κ m x i := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Fin.pos i
  have hMb : 1 ≤ Mbar := hM1.trans hMbar
  have hU0 : 0 < U := by linarith
  set D : ℝ := 68 * r * Mbar * U ^ 2 / ε
  have hD : |t| * ‖c‖ * M * U + ∑ i, w i ≤ D := by
    have h1 : |t| * ‖c‖ * M * U ≤ 16 * r / ε * (4 * U) * Mbar * U := by
      have := mul_le_mul ht hc (norm_nonneg c) (by positivity)
      have h2 := mul_le_mul this hMbar (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right h2 hU0.le
    have h3 : 4 * (r : ℝ) ≤ 4 * r * Mbar * U ^ 2 / ε := by
      rw [le_div_iff₀ hε]
      have : 1 ≤ Mbar * U ^ 2 := by nlinarith
      nlinarith
    calc |t| * ‖c‖ * M * U + ∑ i, w i ≤ 16 * r / ε * (4 * U) * Mbar * U + 4 * r * Mbar * U ^ 2 / ε :=
          add_le_add h1 (hwsum.trans h3)
      _ = D := by simp only [D]; field_simp; ring
  have hwmin : 0 < 1 / (4 * Mbar) := by positivity
  have h := slack_floor hA hrow hL hLM hκ hc₀ hcM hU0.le hU hx hx₀ hwmin hw hwin hδ
    (by positivity) hs0 hD i
  refine le_trans ?_ h
  -- `min{1/(2U), (1/(4M̄))(1/U)/(4D)}/2 ≥ ε/(2¹² r M̄² U³)`
  have hq : ε / (2 ^ 12 * r * Mbar ^ 2 * U ^ 3) ≤ 1 / (4 * Mbar) * (1 / U) / (4 * D) / 2 := by
    simp only [D]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [mul_pos hε (mul_pos (by positivity : (0 : ℝ) < r) (by positivity : (0 : ℝ) < Mbar))]
  have hq2 : ε / (2 ^ 12 * r * Mbar ^ 2 * U ^ 3) ≤ 1 / U / 2 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ r * Mbar ^ 2 * U ^ 2 := by
      have := mul_le_mul hr (show (1 : ℝ) ≤ Mbar ^ 2 by nlinarith) zero_le_one (by positivity)
      have h2 : (1 : ℝ) ≤ U ^ 2 := by nlinarith
      nlinarith
    field_simp
    nlinarith
  rcases min_choice (1 / U / 2) (1 / (4 * Mbar) * (1 / U) / (4 * D)) with hmin | hmin
  · rw [hmin]; exact hq2
  · rw [hmin]; exact hq

end

end ImplicitLP
end CutQueryComplexity
