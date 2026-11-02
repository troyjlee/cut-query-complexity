import CutQueryComplexity.ImplicitLP.Center
import CutQueryComplexity.ImplicitLP.Barrier
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Center slack from an interior reference (`lem:slack`, D7)

`center_stationary`: at a frozen-weight center `x̄`, the directional derivative toward any
feasible `x⁰` vanishes, `Σⱼ wⱼ φⱼ'(x̄ⱼ)(x⁰ⱼ − x̄ⱼ) = −t cᵀ(x⁰ − x̄)`. Only a one-dimensional local
minimum is used; no Lagrange multiplier is needed.

`lem_slack`: suppose `wᵢ ≥ w_min > 0`, the reference `x⁰` has slacks at least `s₀`, the box widths
are at most `U`, and `|t|‖c‖_∞ M U + Σw ≤ D`. Then every slack of `x̄` is at least
`min{s₀/2, w_min s₀/(4D)}`. Each summand is at most `wⱼ` (`eq:barrier`). Near a wall at distance
`s < s₀/2`, the barrier satisfies `|φ'| = κ cot(κs) ≥ 1/(2s)` because `κs ≤ π/4`, and the step
toward `x⁰` has length at least `s₀/2`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Filter Topology

noncomputable section

variable {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c w : Fin M → ℝ} {t : ℝ}

/-- `θⱼ(y + τv) = θⱼ(y) + τ κⱼ vⱼ`. -/
theorem theta_line (y v : Fin M → ℝ) (τ : ℝ) (j : Fin M) :
    theta κ m (y + τ • v) j = theta κ m y j + τ * (κ j * v j) := by
  simp only [theta, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- **Stationarity of the center along a feasible direction.** -/
theorem center_stationary {xbar x₀ : Fin M → ℝ} (hxbar : xbar ∈ Feasible A b κ m)
    (hx₀ : x₀ ∈ Feasible A b κ m)
    (hmin : ∀ y ∈ Feasible A b κ m, centerObj κ m c w t xbar ≤ centerObj κ m c w t y) :
    t * (c ⬝ᵥ (x₀ - xbar)) + ∑ j, w j * barDphi κ m xbar j * (x₀ j - xbar j) = 0 := by
  set v := x₀ - xbar
  set φ : ℝ → ℝ := fun τ => centerObj κ m c w t (xbar + τ • v)
  -- the derivative of `φ` at `0`
  have hc : ∀ j, 0 < cos (theta κ m xbar j) := cos_theta_pos hxbar.2
  have hd : HasDerivAt φ (t * (c ⬝ᵥ v) + ∑ j, w j * (tan (theta κ m xbar j) * (κ j * v j))) 0 := by
    have hlin : HasDerivAt (fun τ : ℝ => t * (c ⬝ᵥ (xbar + τ • v))) (t * (c ⬝ᵥ v)) 0 := by
      have : (fun τ : ℝ => t * (c ⬝ᵥ (xbar + τ • v))) =
          fun τ => t * (c ⬝ᵥ xbar) + τ * (t * (c ⬝ᵥ v)) := by
        funext τ; simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (t * (c ⬝ᵥ v))).const_add (t * (c ⬝ᵥ xbar))
    have hbar : ∀ j, HasDerivAt (fun τ : ℝ => w j * -Real.log (cos (theta κ m (xbar + τ • v) j)))
        (w j * (tan (theta κ m xbar j) * (κ j * v j))) 0 := fun j => by
      simp_rw [theta_line]
      have h1 : HasDerivAt (fun τ : ℝ => theta κ m xbar j + τ * (κ j * v j)) (κ j * v j) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (κ j * v j)).const_add (theta κ m xbar j)
      have h2 := (h1.cos.log (by simpa using (hc j).ne')).neg.const_mul (w j)
      refine h2.congr_deriv ?_
      simp only [zero_mul, add_zero, tan_eq_sin_div_cos]
      field_simp
    have hsum := HasDerivAt.fun_sum (u := univ) fun j (_ : j ∈ univ) => hbar j
    exact hlin.add hsum
  -- `0` is a local minimum of `φ`
  have hloc : IsLocalMin φ 0 := by
    have hint : ∀ j, ∀ᶠ τ in 𝓝 (0 : ℝ), |theta κ m xbar j + τ * (κ j * v j)| < π / 2 := fun j => by
      have hcont : Continuous fun τ : ℝ => |theta κ m xbar j + τ * (κ j * v j)| := by fun_prop
      have := hcont.continuousAt (x := 0) |>.eventually_lt continuousAt_const
        (by simpa using hxbar.2 j)
      exact this
    filter_upwards [eventually_all.mpr hint] with τ hτ
    have hfeas : xbar + τ • v ∈ Feasible A b κ m := by
      refine ⟨?_, fun j => by rw [theta_line]; exact hτ j⟩
      simp only [v, mulVec_add, mulVec_smul, mulVec_sub, hx₀.1, hxbar.1, sub_self, smul_zero,
        add_zero]
    have := hmin _ hfeas
    simpa [φ] using this
  have h0 := hloc.hasDerivAt_eq_zero hd
  rw [← h0]
  congr 1
  exact sum_congr rfl fun j _ => by simp only [barDphi, v, Pi.sub_apply]; ring

/-- `κ cot(κs) ≥ 1/(2s)` for `0 < κs ≤ π/4`, in the form used at a wall:
`κ cos y / sin y ≥ 1/(2s)` with `y = κs`. -/
theorem wall_bound {k s : ℝ} (hk : 0 < k) (hs : 0 < s) (hy : k * s ≤ π / 4) :
    1 / (2 * s) ≤ k * (cos (k * s) / sin (k * s)) := by
  have hy0 : 0 < k * s := mul_pos hk hs
  have hsin : 0 < sin (k * s) := sin_pos_of_pos_of_lt_pi hy0 (by linarith [pi_pos])
  have hsinle : sin (k * s) ≤ k * s := (sin_lt hy0).le
  have hcos : 1 / 2 ≤ cos (k * s) := by
    have := one_sub_sq_div_two_le_cos (x := k * s)
    have hpi : π ≤ 4 := pi_le_four
    nlinarith [hy0]
  rw [mul_div_assoc', le_div_iff₀ hsin, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **`lem:slack`**: center slack from an interior reference. -/
theorem lem_slack (hκ : ∀ i, 0 < κ i) {wmin : ℝ} (hwmin : 0 < wmin) (hw : ∀ i, wmin ≤ w i)
    {xbar x₀ : Fin M → ℝ} (hxbar : xbar ∈ Feasible A b κ m) (hx₀ : x₀ ∈ Feasible A b κ m)
    (hmin : ∀ y ∈ Feasible A b κ m, centerObj κ m c w t xbar ≤ centerObj κ m c w t y)
    {s₀ U D : ℝ} (hs₀ : 0 < s₀) (hs0 : ∀ i, s₀ ≤ (π / 2 - |theta κ m x₀ i|) / κ i)
    (hU : ∀ i, π / κ i ≤ U) (hD : |t| * ‖c‖ * M * U + ∑ i, w i ≤ D) (i : Fin M) :
    min (s₀ / 2) (wmin * s₀ / (4 * D)) ≤ (π / 2 - |theta κ m xbar i|) / κ i := by
  set σ := (π / 2 - |theta κ m xbar i|) / κ i with hσdef
  by_cases hσ : s₀ / 2 ≤ σ
  · exact (min_le_left _ _).trans hσ
  push Not at hσ
  refine (min_le_right _ _).trans ?_
  have hk := hκ i
  have hw0 : ∀ j, 0 ≤ w j := fun j => hwmin.le.trans (hw j)
  have hσ0 : 0 < σ := div_pos (by linarith [hxbar.2 i]) hk
  set T : Fin M → ℝ := fun j => w j * barDphi κ m xbar j * (x₀ j - xbar j)
  -- each summand is at most `wⱼ`
  have hTj : ∀ j, T j ≤ w j := fun j => by
    obtain ⟨-, -, -, -, -, h6⟩ := barrier_bounds (hκ j) (hxbar.2 j)
    have := h6 (theta κ m x₀ j) (hx₀.2 j).le
    have e : (theta κ m x₀ j - theta κ m xbar j) / κ j = x₀ j - xbar j := by
      simp only [theta]; field_simp [(hκ j).ne']; ring
    rw [e] at this
    simp only [T, barDphi]
    rw [mul_assoc]
    exact mul_le_of_le_one_right (hw0 j) this
  -- the `i`-th summand is very negative
  have hy : κ i * σ ≤ π / 4 := by
    have h1 := hs0 i
    have h2 : (π / 2 - |theta κ m x₀ i|) / κ i ≤ π / 2 / κ i :=
      div_le_div_of_nonneg_right (by linarith [abs_nonneg (theta κ m x₀ i)]) hk.le
    have : σ ≤ π / 4 / κ i := by
      calc σ ≤ s₀ / 2 := hσ.le
        _ ≤ π / 2 / κ i / 2 := by linarith
        _ = π / 4 / κ i := by ring
    rw [le_div_iff₀ hk] at this; linarith
  have hwall := wall_bound hk hσ0 hy
  have hθabs : |theta κ m xbar i| = π / 2 - κ i * σ := by
    simp only [hσdef]; field_simp; ring
  have hθ0 : -(π / 2) + κ i * s₀ ≤ theta κ m x₀ i ∧ theta κ m x₀ i ≤ π / 2 - κ i * s₀ := by
    have := hs0 i
    rw [le_div_iff₀ hk] at this
    constructor <;> linarith [neg_abs_le (theta κ m x₀ i), le_abs_self (theta κ m x₀ i)]
  have hTi : T i ≤ -(wmin * s₀ / (4 * σ)) := by
    have hdx : x₀ i - xbar i = (theta κ m x₀ i - theta κ m xbar i) / κ i := by
      simp only [theta]; field_simp; ring
    set y := κ i * σ
    have hsy : 0 < sin y := sin_pos_of_pos_of_lt_pi (mul_pos hk hσ0) (by linarith [pi_pos])
    rcases le_total (theta κ m xbar i) 0 with hθ | hθ
    · -- near the lower wall: `θ̄ = −(π/2 − y)`, `φ' = −κ cot y`, and `x⁰ − x̄ ≥ s₀/2`
      have hθe : theta κ m xbar i = -(π / 2 - y) := by rw [← hθabs, abs_of_nonpos hθ]; ring
      have hφ : barDphi κ m xbar i = -(κ i * (cos y / sin y)) := by
        simp only [barDphi, hθe, tan_eq_sin_div_cos, sin_neg, cos_neg, sin_pi_div_two_sub,
          cos_pi_div_two_sub]; ring
      have hv : s₀ / 2 ≤ x₀ i - xbar i := by
        rw [hdx, le_div_iff₀ hk, hθe]; nlinarith [hθ0.1]
      simp only [T]
      rw [hφ]
      have hc : 1 / (2 * σ) ≤ κ i * (cos y / sin y) := hwall
      have hφneg : 0 < κ i * (cos y / sin y) := lt_of_lt_of_le (by positivity) hc
      calc w i * -(κ i * (cos y / sin y)) * (x₀ i - xbar i)
          = -(w i * (κ i * (cos y / sin y)) * (x₀ i - xbar i)) := by ring
        _ ≤ -(wmin * (1 / (2 * σ)) * (s₀ / 2)) := by
            apply neg_le_neg
            apply mul_le_mul (mul_le_mul (hw i) hc (by positivity) (hw0 i)) hv
              (by positivity) (mul_nonneg (hw0 i) hφneg.le)
        _ = -(wmin * s₀ / (4 * σ)) := by field_simp; ring
    · -- near the upper wall
      have hθe : theta κ m xbar i = π / 2 - y := by rw [← hθabs, abs_of_nonneg hθ]
      have hφ : barDphi κ m xbar i = κ i * (cos y / sin y) := by
        simp only [barDphi, hθe, tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]
      have hv : s₀ / 2 ≤ xbar i - x₀ i := by
        have : xbar i - x₀ i = -(x₀ i - xbar i) := by ring
        rw [this, hdx, hθe, neg_div', le_div_iff₀ hk]; nlinarith [hθ0.2]
      simp only [T]
      rw [hφ]
      have hc : 1 / (2 * σ) ≤ κ i * (cos y / sin y) := hwall
      have hφpos : 0 < κ i * (cos y / sin y) := lt_of_lt_of_le (by positivity) hc
      calc w i * (κ i * (cos y / sin y)) * (x₀ i - xbar i)
          = -(w i * (κ i * (cos y / sin y)) * (xbar i - x₀ i)) := by ring
        _ ≤ -(wmin * (1 / (2 * σ)) * (s₀ / 2)) := by
            apply neg_le_neg
            apply mul_le_mul (mul_le_mul (hw i) hc (by positivity) (hw0 i)) hv
              (by positivity) (mul_nonneg (hw0 i) hφpos.le)
        _ = -(wmin * s₀ / (4 * σ)) := by field_simp; ring
  -- stationarity bounds `−T_i` by `D`
  have hstat := center_stationary (c := c) (t := t) hxbar hx₀ hmin
  have hv : ∀ j, |x₀ j - xbar j| ≤ U := fun j => by
    have e : x₀ j - xbar j = (theta κ m x₀ j - theta κ m xbar j) / κ j := by
      simp only [theta]; field_simp [(hκ j).ne']; ring
    rw [e, abs_div, abs_of_pos (hκ j)]
    refine le_trans ?_ (hU j)
    apply div_le_div_of_nonneg_right _ (hκ j).le
    have := abs_add_le (theta κ m x₀ j) (-theta κ m xbar j)
    rw [abs_neg, ← sub_eq_add_neg] at this
    linarith [hx₀.2 j, hxbar.2 j]
  have hlin : |t * (c ⬝ᵥ (x₀ - xbar))| ≤ |t| * ‖c‖ * M * U := by
    rw [abs_mul, mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |c j * (x₀ - xbar) j| ≤ ∑ _j : Fin M, ‖c‖ * U := sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c j) (hv j)
            (abs_nonneg _) (norm_nonneg c)
      _ = ‖c‖ * (M * U) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsplit : ∑ j, T j = T i + ∑ j ∈ univ.erase i, T j := (add_sum_erase _ _ (mem_univ i)).symm
  have hrest : ∑ j ∈ univ.erase i, T j ≤ ∑ j, w j :=
    (sum_le_sum fun j _ => hTj j).trans (sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
      fun j _ _ => hw0 j)
  have hnegT : -T i ≤ D := by
    have : t * (c ⬝ᵥ (x₀ - xbar)) + ∑ j, T j = 0 := hstat
    linarith [le_abs_self (t * (c ⬝ᵥ (x₀ - xbar)))]
  have hq : wmin * s₀ / (4 * σ) ≤ D := by linarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hq
  rw [div_le_iff₀ (by positivity)] at hq
  rw [div_le_iff₀ (by positivity)]
  linarith

end

end ImplicitLP
end CutQueryComplexity
