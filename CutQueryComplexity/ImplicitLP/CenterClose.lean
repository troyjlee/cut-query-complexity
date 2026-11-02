import CutQueryComplexity.ImplicitLP.Newton
import CutQueryComplexity.ImplicitLP.Slack
import CutQueryComplexity.ImplicitLP.NewtonDir
import CutQueryComplexity.ImplicitLP.Projection
import CutQueryComplexity.ImplicitLP.Attain

/-! # Approximate centers are near the exact center (`lem:center`, D7)

Tools for comparing an approximately central point with the frozen-weight center:

* `neg_log_cos_tangent`: `−log cos` lies above its tangent lines on `(−π/2, π/2)`. This follows
  from the mean value theorem and the monotonicity of `tan`.
* `centerObj_ge_residual`: if `ν` is any multiplier and `r = (tc + wφ'(x) − Aν)/(wS(x))`, then
  every feasible `y` satisfies `F(y) ≥ F(x) − ‖r‖_∞ Σᵢ wᵢ Sᵢ(x)|yᵢ − xᵢ|`. As the centrality
  tends to zero along a sequence, every limit point is therefore a minimizer. This avoids
  subsequences and Lagrange multipliers.
* `segment_interior`: if `Sᵢ(x)|dᵢ| < 1` for all `i`, the whole segment `x + [0,1]d` is interior.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

/-- **`−log cos` lies above its tangents** on `(−π/2, π/2)`. -/
theorem neg_log_cos_tangent {a b : ℝ} (ha : |a| < π / 2) (hb : |b| < π / 2) :
    -Real.log (cos a) + tan a * (b - a) ≤ -Real.log (cos b) := by
  have hI : ∀ x, |x| < π / 2 → 0 < cos x := fun x hx =>
    cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hD : ∀ x, |x| < π / 2 → HasDerivAt (fun x => -Real.log (cos x)) (tan x) x := fun x hx => by
    have := ((hasDerivAt_cos x).log (hI x hx).ne').neg
    refine this.congr_deriv ?_
    rw [tan_eq_sin_div_cos]; ring
  -- the segment between `a` and `b` stays in the interval
  have hseg : ∀ x, min a b ≤ x → x ≤ max a b → |x| < π / 2 := fun x h1 h2 => by
    rw [abs_lt]; constructor
    · linarith [min_le_left a b, min_le_right a b, neg_abs_le a, neg_abs_le b,
        show -(π / 2) < min a b from lt_min (by linarith [neg_abs_le a]) (by linarith [neg_abs_le b])]
    · linarith [show max a b < π / 2 from max_lt (by linarith [le_abs_self a])
        (by linarith [le_abs_self b])]
  have hmem : ∀ x, |x| < π / 2 → x ∈ Ioo (-(π / 2)) (π / 2) := fun x hx =>
    ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun x => -Real.log (cos x)) tan hab
      (fun x hx => (hD x (hseg x (by rw [min_eq_left hab.le]; exact hx.1)
        (by rw [max_eq_right hab.le]; exact hx.2))).continuousAt.continuousWithinAt)
      (fun x hx => hD x (hseg x (by rw [min_eq_left hab.le]; exact hx.1.le)
        (by rw [max_eq_right hab.le]; exact hx.2.le)))
    have hξI : |ξ| < π / 2 := hseg ξ (by rw [min_eq_left hab.le]; exact hξ.1.le)
      (by rw [max_eq_right hab.le]; exact hξ.2.le)
    have hmono : tan a ≤ tan ξ := (strictMonoOn_tan (hmem a ha) (hmem ξ hξI) hξ.1).le
    rw [eq_div_iff (by linarith)] at hξe
    nlinarith
  · subst hab; simp
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun x => -Real.log (cos x)) tan hab
      (fun x hx => (hD x (hseg x (by rw [min_eq_right hab.le]; exact hx.1)
        (by rw [max_eq_left hab.le]; exact hx.2))).continuousAt.continuousWithinAt)
      (fun x hx => hD x (hseg x (by rw [min_eq_right hab.le]; exact hx.1.le)
        (by rw [max_eq_left hab.le]; exact hx.2.le)))
    have hξI : |ξ| < π / 2 := hseg ξ (by rw [min_eq_right hab.le]; exact hξ.1.le)
      (by rw [max_eq_left hab.le]; exact hξ.2.le)
    have hmono : tan ξ ≤ tan a := (strictMonoOn_tan (hmem ξ hξI) (hmem a ha) hξ.2).le
    rw [eq_div_iff (by linarith)] at hξe
    nlinarith

variable {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c w : Fin M → ℝ} {t : ℝ}

/-- **The objective is bounded below through any residual.** -/
theorem centerObj_ge_residual (hκ : ∀ i, 0 < κ i) {x y : Fin M → ℝ}
    (hx : x ∈ Feasible A b κ m) (hy : y ∈ Feasible A b κ m) (hw : ∀ i, 0 < w i)
    (ν : Fin r → ℝ) :
    centerObj κ m c w t x -
        ‖fun i => (t * c i + w i * barDphi κ m x i - (A *ᵥ ν) i) / (w i * barS κ m x i)‖ *
          ∑ i, w i * barS κ m x i * |y i - x i| ≤ centerObj κ m c w t y := by
  set R : Fin M → ℝ := fun i => (t * c i + w i * barDphi κ m x i - (A *ᵥ ν) i) /
    (w i * barS κ m x i)
  have hS : ∀ i, 0 < barS κ m x i := barS_pos hκ hx.2
  -- tangent inequalities, coordinatewise
  have htan : ∀ i, w i * -Real.log (cos (theta κ m x i)) + w i * barDphi κ m x i * (y i - x i) ≤
      w i * -Real.log (cos (theta κ m y i)) := fun i => by
    have h := neg_log_cos_tangent (hx.2 i) (hy.2 i)
    have e : theta κ m y i - theta κ m x i = κ i * (y i - x i) := by simp only [theta]; ring
    rw [e] at h
    have := mul_le_mul_of_nonneg_left h (hw i).le
    simp only [barDphi]; nlinarith [this]
  -- `tc + wφ' = Aν + wSR`, and `Aᵀ(y − x) = 0`
  have hq : ∀ i, t * c i + w i * barDphi κ m x i = (A *ᵥ ν) i + w i * barS κ m x i * R i := fun i => by
    simp only [R]; field_simp [(hw i).ne', (hS i).ne']; ring
  have hAν : ∑ i, (A *ᵥ ν) i * (y i - x i) = 0 := by
    have : ∑ i, (A *ᵥ ν) i * (y i - x i) = (A *ᵥ ν) ⬝ᵥ (y - x) := by
      simp only [dotProduct, Pi.sub_apply]
    rw [this, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_sub, hy.1, hx.1,
      sub_self, zero_dotProduct]
  have hR : ∀ i, -(‖R‖ * (w i * barS κ m x i * |y i - x i|)) ≤
      w i * barS κ m x i * R i * (y i - x i) := fun i => by
    have h1 : |R i| ≤ ‖R‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm R i
    have h2 : 0 ≤ w i * barS κ m x i := by have := hw i; have := hS i; positivity
    have h3 : |w i * barS κ m x i * R i * (y i - x i)| ≤ ‖R‖ * (w i * barS κ m x i * |y i - x i|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg h2]
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 (abs_nonneg (y i - x i)))
      nlinarith [abs_nonneg (y i - x i), abs_nonneg (R i)]
    exact (abs_le.mp h3).1
  -- assemble
  have hsum : centerObj κ m c w t y - centerObj κ m c w t x ≥
      ∑ i, w i * barS κ m x i * R i * (y i - x i) := by
    have hlin : t * (c ⬝ᵥ y) - t * (c ⬝ᵥ x) = ∑ i, t * c i * (y i - x i) := by
      simp only [dotProduct, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    have hbar := sum_le_sum fun i (_ : i ∈ Finset.univ) => htan i
    rw [sum_add_distrib] at hbar
    unfold centerObj
    have : ∑ i, w i * barS κ m x i * R i * (y i - x i) =
        ∑ i, t * c i * (y i - x i) + ∑ i, w i * barDphi κ m x i * (y i - x i) -
          ∑ i, (A *ᵥ ν) i * (y i - x i) := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by
        simp only [R]; field_simp [(hw i).ne', (hS i).ne']
    rw [this, hAν]
    linarith
  have := sum_le_sum fun i (_ : i ∈ Finset.univ) => hR i
  rw [sum_neg_distrib, ← mul_sum] at this
  linarith

/-- **The whole segment is interior** when `Sᵢ(x)|dᵢ| < 1` for all `i`. -/
theorem segment_interior (hκ : ∀ i, 0 < κ i) {x d : Fin M → ℝ} (hx : Interior κ m x)
    (hd : ∀ i, barS κ m x i * |d i| < 1) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    Interior κ m (x + τ • d) := fun i => by
  have hc := cos_theta_pos hx i
  have hu : |κ i * (τ * d i)| / cos (theta κ m x i) < 1 := by
    have : |κ i * (τ * d i)| / cos (theta κ m x i) = τ * (barS κ m x i * |d i|) := by
      rw [abs_mul, abs_of_pos (hκ i), abs_mul, abs_of_nonneg hτ.1, barS]; field_simp
    rw [this]
    calc τ * (barS κ m x i * |d i|) ≤ 1 * (barS κ m x i * |d i|) :=
          mul_le_mul_of_nonneg_right hτ.2 (mul_nonneg (barS_pos hκ hx i).le (abs_nonneg _))
      _ < 1 := by rw [one_mul]; exact hd i
  have := (newton_coord (hx i) hu).1
  have e : theta κ m (x + τ • d) i = theta κ m x i + κ i * (τ * d i) := by
    simp only [theta, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]; exact this

/-- `e^{1/5} ≤ 5/4` and `4/5 ≤ e^{-1/5}`. -/
theorem exp_fifth_bounds : exp (1 / 5 : ℝ) ≤ 5 / 4 ∧ 4 / 5 ≤ exp (-(1 / 5 : ℝ)) := by
  have h1 : exp (1 / 5 : ℝ) ≤ 5 / 4 := by
    have := abs_exp_sub_one_sub_id_le (x := (1 / 5 : ℝ)) (by norm_num)
    rw [abs_le] at this; norm_num at this ⊢; linarith
  refine ⟨h1, ?_⟩
  rw [exp_neg, le_inv_comm₀ (by norm_num) (exp_pos _)]
  linarith

/-- **One frozen-weight Newton step** (the inner step of `lem:center`). -/
theorem center_step (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) {y : Fin M → ℝ} (hy : y ∈ Feasible A b κ m) (hw : ∀ i, 0 < w i)
    (hwin : ∀ i, |Real.log (w i) - Real.log (gfun κ m (1 - 1 / L₀) c₀ A y i)| ≤ 1 / 5)
    (hδ : cent (48 * (2 * L₀)) A (barS κ m y) (barDphi κ m y) c t w ≤ 1 / 100) :
    let h := newtonDir A w (barS κ m y) (fun i => t * c i + w i * barDphi κ m y i)
    let δ := cent (48 * (2 * L₀)) A (barS κ m y) (barDphi κ m y) c t w
    y + h ∈ Feasible A b κ m ∧
      cent (48 * (2 * L₀)) A (barS κ m (y + h)) (barDphi κ m (y + h)) c t w ≤ 8 * δ ^ 2 ∧
      (∀ i, |Real.log (gfun κ m (1 - 1 / L₀) c₀ A (y + h) i) -
        Real.log (gfun κ m (1 - 1 / L₀) c₀ A y i)| ≤ 2 * δ) ∧
      ∀ i, barS κ m y i * |h i| ≤ 2 * δ := by
  intro h δ
  set C : ℝ := 48 * (2 * L₀)
  set g := gfun κ m (1 - 1 / L₀) c₀ A y
  have hC : 0 < C := by positivity
  have hS : ∀ i, 0 < barS κ m y i := barS_pos hκ hy.2
  have hg : ∀ i, 0 < g i := fun i => add_pos_of_pos_of_nonneg (exp_pos _) hc₀
  obtain ⟨he1, he2⟩ := exp_fifth_bounds
  -- the window `4/5 g ≤ w ≤ 5/4 g`
  have hwg : ∀ i, w i ≤ exp (1 / 5) * g i ∧ g i ≤ exp (1 / 5) * w i := fun i => by
    have h1 := abs_le.mp (hwin i)
    constructor
    · rw [← exp_log (hw i), ← exp_log (hg i), ← exp_add, exp_le_exp]; linarith
    · rw [← exp_log (hw i), ← exp_log (hg i), ← exp_add, exp_le_exp]; linarith
  have hlo : ∀ i, 4 / 5 * g i ≤ w i := fun i => by
    have := (hwg i).2
    have h' : g i * exp (-(1 / 5)) ≤ w i := by
      rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]; linarith
    nlinarith [hg i]
  have hhi : ∀ i, w i ≤ 5 / 4 * g i := fun i => by nlinarith [(hwg i).1, hg i]
  -- the exact direction and `eq:projection`
  obtain ⟨hh1, hh2⟩ := newtonDir_spec hA (q := fun i => t * c i + w i * barDphi κ m y i) hw hS
  have hproj := eq_projection_note hA hrow hL hLM hκ hc₀ hcM hy.2 hlo hhi hh1 hh2
  have hγ : 1 + 1 / (16 * (2 * L₀)) ≤ 17 / 16 := by
    have : 1 / (16 * (2 * L₀)) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hδ0 : 0 ≤ δ := cent_nonneg hC.le t w
  have hSh : mixed C w (fun i => barS κ m y i * h i) ≤ (1 + 1 / (16 * (2 * L₀))) * δ :=
    hproj.2
  -- `eq:newton` with `e = 0`
  have hzero : Aᵀ *ᵥ (0 : Fin M → ℝ) = 0 := mulVec_zero _
  have hnew := eq_newton (e := 0) (η := 0) hκ hC hy.2 hw hh1 hh2 hzero (by positivity) hγ hδ0 hSh
    (by simp only [Pi.zero_apply, mul_zero]
        rw [show (fun _ : Fin M => (0 : ℝ)) = 0 from rfl]; simp [mixed, wnorm]) (by nlinarith)
  simp only [add_zero, mul_zero] at hnew
  obtain ⟨hint, hfeas, hcent⟩ := hnew
  -- the step size
  have hSh' : ∀ i, barS κ m y i * |h i| ≤ 2 * δ := fun i => by
    have h1 : |barS κ m y i * h i| ≤ mixed C w (fun i => barS κ m y i * h i) := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (fun i => barS κ m y i * h i) i).trans (norm_le_mixed hC.le _)
    rw [abs_mul, abs_of_pos (hS i)] at h1
    nlinarith
  have hfeas' : y + h ∈ Feasible A b κ m :=
    ⟨by rw [mulVec_add, hy.1, hfeas, add_zero], hint⟩
  refine ⟨hfeas', by simpa [h] using hcent, fun i => ?_, hSh'⟩
  -- `eq:gmove` bounds the change of `log g`
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, Interior κ m (y + τ • h) := fun τ hτ =>
    segment_interior hκ hy.2 (fun i => by linarith [hSh' i]) hτ
  have hv : mixed C g (fun i => barS κ m y i * h i) ≤ exp (1 / 5 / 2) * ((17 / 16) * δ) := by
    refine (mixed_le_of_le_exp hC.le (by norm_num) (fun i => (hwg i).2) _).trans ?_
    exact mul_le_mul_of_nonneg_left (hSh.trans (mul_le_mul_of_nonneg_right hγ hδ0)) (exp_pos _).le
  have he10 : exp (1 / 5 / 2 : ℝ) ≤ 5 / 4 := (exp_le_exp.mpr (by norm_num)).trans he1
  have hv1 : mixed C g (fun i => barS κ m y i * h i) ≤ 1 / 10 := by nlinarith
  have hgm := eq_gmove_note hA hrow hL hκ hc₀ hseg hv1
  set v := mixed C g (fun i => barS κ m y i * h i)
  have hv0 : 0 ≤ v := mixed_nonneg hC.le _
  have hbound : (1 - 1 / (2 * L₀) + 4 * v) * v ≤ 2 * δ := by
    have : 1 / (2 * L₀) ≥ 0 := by positivity
    nlinarith
  have hcoord : |Real.log (gfun κ m (1 - 1 / L₀) c₀ A (y + h) i) - Real.log (g i)| ≤
      mixed C g (fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A (y + h) i) - Real.log (g i)) := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A (y + h) i) -
      Real.log (g i)) i).trans (norm_le_mixed hC.le _)
  exact hcoord.trans (hgm.trans hbound)

/-- The slack `sᵢ(y) = (π/2 − |θᵢ(y)|)/κᵢ = min{yᵢ − ℓᵢ, uᵢ − yᵢ}`. -/
def slk (κ m y : Fin M → ℝ) (i : Fin M) : ℝ := (π / 2 - |theta κ m y i|) / κ i

theorem slk_lip (hκ : ∀ i, 0 < κ i) (y h : Fin M → ℝ) (i : Fin M) :
    |slk κ m (y + h) i - slk κ m y i| ≤ |h i| := by
  have e : slk κ m (y + h) i - slk κ m y i = (|theta κ m y i| - |theta κ m (y + h) i|) / κ i := by
    simp only [slk]; field_simp [(hκ i).ne']; ring
  rw [e, abs_div, abs_of_pos (hκ i), div_le_iff₀ (hκ i)]
  have h1 := abs_abs_sub_abs_le_abs_sub (theta κ m y i) (theta κ m (y + h) i)
  have h2 : theta κ m y i - theta κ m (y + h) i = -(κ i * h i) := by
    simp only [theta, Pi.add_apply]; ring
  rw [h2, abs_neg, abs_mul, abs_of_pos (hκ i)] at h1
  linarith

theorem continuous_slk (i : Fin M) : Continuous fun y : Fin M → ℝ => slk κ m y i := by
  unfold slk theta; fun_prop

theorem continuousAt_centerObj {y : Fin M → ℝ} (hy : Interior κ m y) :
    ContinuousAt (centerObj κ m c w t) y := by
  have hc := cos_theta_pos hy
  have hterm : ∀ i, ContinuousAt (fun y => w i * -Real.log (cos (theta κ m y i))) y := fun i => by
    refine continuousAt_const.mul (ContinuousAt.neg ?_)
    have hθ : Continuous fun y : Fin M → ℝ => theta κ m y i := by unfold theta; fun_prop
    exact ((continuous_cos.comp hθ).continuousAt).log (hc i).ne'
  unfold centerObj
  exact (continuousAt_const.mul (by fun_prop)).add
    (tendsto_finsetSum Finset.univ fun i _ => (hterm i).tendsto)

set_option maxHeartbeats 1600000 in
/-- **`lem:center`** (frozen-weight center closeness). Suppose `x` is strictly feasible, the
weights are within `e^{±1/20}` of `g(x)`, and `δ_t(x, w) ≤ 1/1000`. Then every frozen-weight
center `x̄` satisfies `sᵢ(x)/2 ≤ sᵢ(x̄) ≤ 2sᵢ(x)` and `‖x − x̄‖_∞ ≤ 4U δ_t(x, w)`. -/
theorem lem_center (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ U : ℝ} (hc₀ : 0 ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) (hUnn : 0 ≤ U) (hU : ∀ i, π / κ i ≤ U) {x : Fin M → ℝ}
    (hx : x ∈ Feasible A b κ m) (hw : ∀ i, 0 < w i)
    (hwin : ∀ i, |Real.log (w i) - Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)| ≤ 1 / 20)
    (hδ : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    {xbar : Fin M → ℝ} (hxbar : xbar ∈ Feasible A b κ m)
    (hmin : ∀ y ∈ Feasible A b κ m, centerObj κ m c w t xbar ≤ centerObj κ m c w t y) :
    (∀ i, slk κ m x i / 2 ≤ slk κ m xbar i ∧ slk κ m xbar i ≤ 2 * slk κ m x i) ∧
      ‖x - xbar‖ ≤ 4 * U * cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t w := by
  set C : ℝ := 48 * (2 * L₀)
  have hC : 0 < C := by positivity
  set g := gfun κ m (1 - 1 / L₀) c₀ A
  set δf : (Fin M → ℝ) → ℝ := fun y => cent C A (barS κ m y) (barDphi κ m y) c t w
  set N : (Fin M → ℝ) → Fin M → ℝ := fun y =>
    y + newtonDir A w (barS κ m y) (fun i => t * c i + w i * barDphi κ m y i)
  set X : ℕ → Fin M → ℝ := fun j => N^[j] x
  set δ₀ := δf x
  have hδ₀ : 0 ≤ δ₀ := cent_nonneg hC.le t w
  have hU0 : ∀ i, 1 / κ i ≤ U := fun i => by
    have := hU i
    have hpi : (1 : ℝ) ≤ π := by linarith [two_le_pi]
    calc 1 / κ i ≤ π / κ i := div_le_div_of_nonneg_right hpi (hκ i).le
      _ ≤ U := this
  -- the inductive invariant
  set Q : ℕ → Prop := fun j => X j ∈ Feasible A b κ m ∧ δf (X j) ≤ δ₀ / 2 ^ j ∧
      (∀ i, |Real.log (g (X j) i) - Real.log (g x i)| ≤ 4 * δ₀ * (1 - 1 / 2 ^ j)) ∧
      (∀ i, slk κ m x i * (1 - 4 * δ₀ * (1 - 1 / 2 ^ j)) ≤ slk κ m (X j) i ∧
        slk κ m (X j) i ≤ slk κ m x i * exp (4 * δ₀ * (1 - 1 / 2 ^ j))) ∧
      ‖X j - x‖ ≤ 4 * U * δ₀ * (1 - 1 / 2 ^ j) with hQdef
  have hslk0 : ∀ i, 0 < slk κ m x i := fun i => div_pos (by linarith [hx.2 i]) (hκ i)
  have hXs : ∀ j, X (j + 1) = X j + newtonDir A w (barS κ m (X j))
      (fun i => t * c i + w i * barDphi κ m (X j) i) := fun j => by
    simp only [X, N]; rw [Function.iterate_succ_apply']
  have step : ∀ j, Q j → Q (j + 1) ∧ dist (X j) (X (j + 1)) ≤ 2 * U * δ₀ / 2 ^ j := by
    intro j hQ
    obtain ⟨hfe, hδj, hlog, hslk, hdist⟩ := hQ
    set δj := δf (X j)
    have hδj0 : 0 ≤ δj := cent_nonneg hC.le t w
    have hpow : (0 : ℝ) < 2 ^ j := by positivity
    have hq1 : δ₀ / 2 ^ j ≤ δ₀ := div_le_self hδ₀ (one_le_pow₀ (by norm_num))
    have hfrac : 0 ≤ 1 - 1 / (2 : ℝ) ^ j ∧ 1 - 1 / (2 : ℝ) ^ j ≤ 1 := by
      constructor
      · rw [sub_nonneg, div_le_one hpow]; exact one_le_pow₀ (by norm_num)
      · have : 0 ≤ 1 / (2 : ℝ) ^ j := by positivity
        linarith
    have hwj : ∀ i, |Real.log (w i) - Real.log (g (X j) i)| ≤ 1 / 5 := fun i => by
      have h1 := hwin i
      have h2 := hlog i
      have h3 := abs_sub_le (Real.log (w i)) (Real.log (g x i)) (Real.log (g (X j) i))
      rw [abs_sub_comm (Real.log (g x i))] at h3
      nlinarith [hfrac.2]
    have hδj1 : δj ≤ 1 / 100 := by linarith
    obtain ⟨hfe', hcent, hlogstep, hstep⟩ := center_step hA hrow hL hLM hκ hc₀ hcM hfe hw hwj hδj1
    set h := newtonDir A w (barS κ m (X j)) (fun i => t * c i + w i * barDphi κ m (X j) i)
    have hX1 : X (j + 1) = X j + h := hXs j
    have hS : ∀ i, 0 < barS κ m (X j) i := barS_pos hκ hfe.2
    have hbar := fun i => eq_barrier hκ hfe.2 i
    -- the coordinate step
    have hhi : ∀ i, |h i| ≤ 2 * (δ₀ / 2 ^ j) * slk κ m (X j) i := fun i => by
      have h1 := hstep i
      have h2 : 1 ≤ barS κ m (X j) i * slk κ m (X j) i := (hbar i).2.2.1
      have h3 : |h i| * 1 ≤ |h i| * (barS κ m (X j) i * slk κ m (X j) i) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have hs0 : 0 ≤ slk κ m (X j) i := div_nonneg (by linarith [hfe.2 i]) (hκ i).le
      nlinarith
    have hhU : ∀ i, |h i| ≤ 2 * U * (δ₀ / 2 ^ j) := fun i => by
      have h1 := hstep i
      have h2 : κ i ≤ barS κ m (X j) i := (hbar i).2.2.2.2
      have h3 : κ i * |h i| ≤ 2 * δj := (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)).trans h1
      have h4 : |h i| ≤ 2 * δj * (1 / κ i) := by
        rw [mul_one_div, le_div_iff₀ (hκ i)]; linarith
      calc |h i| ≤ 2 * δj * (1 / κ i) := h4
        _ ≤ 2 * (δ₀ / 2 ^ j) * U := mul_le_mul (by linarith) (hU0 i)
            (one_div_pos.mpr (hκ i)).le (mul_nonneg (by norm_num) (div_nonneg hδ₀ hpow.le))
        _ = 2 * U * (δ₀ / 2 ^ j) := by ring
    have hnorm : ‖h‖ ≤ 2 * U * δ₀ / 2 ^ j :=
      (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hUnn) hδ₀)
        hpow.le)).mpr fun i => by
        rw [Real.norm_eq_abs, mul_div_assoc]; exact hhU i
    have hsplit : 1 - 1 / (2 : ℝ) ^ (j + 1) = (1 - 1 / 2 ^ j) + (1 / 2 ^ j) / 2 := by
      rw [pow_succ]; field_simp; ring
    refine ⟨⟨by rw [hX1]; exact hfe', ?_, fun i => ?_, fun i => ?_, ?_⟩, ?_⟩
    · -- centrality halves
      rw [hX1]
      calc δf (X j + h) ≤ 8 * δj ^ 2 := hcent
        _ ≤ δj / 2 := by nlinarith
        _ ≤ δ₀ / 2 ^ j / 2 := by linarith
        _ = δ₀ / 2 ^ (j + 1) := by rw [pow_succ]; ring
    · -- `log g` moves by `2δⱼ`
      rw [hX1]
      have h1 := hlogstep i
      have h2 := hlog i
      have h3 := abs_sub_le (Real.log (g (X j + h) i)) (Real.log (g (X j) i)) (Real.log (g x i))
      rw [hsplit]
      have : 2 * δj ≤ 4 * δ₀ * (1 / 2 ^ j / 2) := by
        have : 4 * δ₀ * (1 / 2 ^ j / 2) = 2 * (δ₀ / 2 ^ j) := by ring
        linarith
      linarith
    · -- slacks change by a relative `2δ₀/2^j`
      obtain ⟨hl, hu⟩ := hslk i
      set a := 4 * δ₀ * (1 - 1 / 2 ^ j)
      set bb := 2 * (δ₀ / 2 ^ j)
      have ha0 : 0 ≤ a := mul_nonneg (by positivity) hfrac.1
      have hb0 : 0 ≤ bb := by positivity
      have hab : a + bb = 4 * δ₀ * (1 - 1 / 2 ^ (j + 1)) := by rw [hsplit]; ring
      have hb1 : bb ≤ 1 / 100 := by
        have : δ₀ / 2 ^ j ≤ 1 / 1000 := hq1.trans hδ
        linarith
      have ha1 : a ≤ 1 / 100 := by
        have : a ≤ 4 * δ₀ := by
          have := mul_le_mul_of_nonneg_left hfrac.2 (by positivity : (0 : ℝ) ≤ 4 * δ₀)
          simpa [a] using this
        linarith
      have hlip := slk_lip (m := m) hκ (X j) h i
      have hsj0 : 0 ≤ slk κ m (X j) i := div_nonneg (by linarith [hfe.2 i]) (hκ i).le
      have hh := hhi i
      rw [hX1, ← hab]
      constructor
      · have h1 : slk κ m (X j) i * (1 - bb) ≤ slk κ m (X j + h) i := by
          rw [abs_le] at hlip; nlinarith
        have h2 : slk κ m x i * (1 - a) * (1 - bb) ≤ slk κ m (X j) i * (1 - bb) :=
          mul_le_mul_of_nonneg_right hl (by linarith)
        have h3 : slk κ m x i * (1 - (a + bb)) ≤ slk κ m x i * (1 - a) * (1 - bb) := by
          have := hslk0 i
          nlinarith [mul_nonneg ha0 hb0]
        linarith
      · have h1 : slk κ m (X j + h) i ≤ slk κ m (X j) i * (1 + bb) := by
          rw [abs_le] at hlip; nlinarith
        have h2 : slk κ m (X j) i * (1 + bb) ≤ slk κ m x i * exp a * exp bb :=
          mul_le_mul (by simpa [a] using hu) (by linarith [add_one_le_exp bb]) (by linarith)
            (by have := hslk0 i; positivity)
        rw [exp_add, ← mul_assoc]
        linarith
    · -- distance from `x`
      rw [hX1]
      calc ‖X j + h - x‖ = ‖(X j - x) + h‖ := by congr 1; abel
        _ ≤ ‖X j - x‖ + ‖h‖ := norm_add_le _ _
        _ ≤ 4 * U * δ₀ * (1 - 1 / 2 ^ j) + 2 * U * δ₀ / 2 ^ j := add_le_add hdist hnorm
        _ = 4 * U * δ₀ * (1 - 1 / 2 ^ (j + 1)) := by rw [hsplit]; ring
    · rw [hX1, dist_eq_norm, show X j - (X j + h) = -h by abel, norm_neg]; exact hnorm
  have hQ : ∀ j, Q j := by
    intro j
    induction j with
    | zero =>
        refine ⟨hx, ?_, fun i => by simp [X], fun i => ?_, by simp [X]⟩
        · simp only [X, Function.iterate_zero, id, pow_zero, div_one]; exact le_rfl
        · simp [X]
    | succ j ih => exact (step j ih).1
  -- the limit
  have hcauchy : CauchySeq X := cauchySeq_of_le_geometric_two (C := 4 * U * δ₀) fun j => by
    have := (step j (hQ j)).2
    calc dist (X j) (X (j + 1)) ≤ 2 * U * δ₀ / 2 ^ j := this
      _ = 4 * U * δ₀ / 2 / 2 ^ j := by ring
  obtain ⟨xinf, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hfrac' : ∀ j, 0 ≤ 1 - 1 / (2 : ℝ) ^ j ∧ 1 - 1 / (2 : ℝ) ^ j ≤ 1 := fun j => by
    have hpow : (0 : ℝ) < 2 ^ j := by positivity
    constructor
    · rw [sub_nonneg, div_le_one hpow]; exact one_le_pow₀ (by norm_num)
    · have : 0 ≤ 1 / (2 : ℝ) ^ j := by positivity
      linarith
  -- slack bounds in the limit
  have hslim : ∀ i, slk κ m x i * (1 - 4 * δ₀) ≤ slk κ m xinf i ∧
      slk κ m xinf i ≤ slk κ m x i * exp (4 * δ₀) := fun i => by
    have ht := ((continuous_slk (κ := κ) (m := m) i).tendsto xinf).comp hlim
    constructor
    · refine ge_of_tendsto ht (Filter.Eventually.of_forall fun j => ?_)
      have := ((hQ j).2.2.2.1 i).1
      have h1 := hfrac' j
      have : slk κ m x i * (1 - 4 * δ₀) ≤ slk κ m x i * (1 - 4 * δ₀ * (1 - 1 / 2 ^ j)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (hslk0 i).le
      simp only [Function.comp]; linarith
    · refine le_of_tendsto ht (Filter.Eventually.of_forall fun j => ?_)
      have := ((hQ j).2.2.2.1 i).2
      have h1 := hfrac' j
      have : slk κ m x i * exp (4 * δ₀ * (1 - 1 / 2 ^ j)) ≤ slk κ m x i * exp (4 * δ₀) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith)) (hslk0 i).le
      simp only [Function.comp]; linarith
  have h4δ : 4 * δ₀ ≤ 1 / 250 := by linarith
  have hexp2 : exp (4 * δ₀) ≤ 2 := by
    have : exp (4 * δ₀) ≤ exp (1 / 250) := exp_le_exp.mpr h4δ
    have h2 : exp (1 / 250 : ℝ) ≤ 2 := by
      have := abs_exp_sub_one_sub_id_le (x := (1 / 250 : ℝ)) (by norm_num)
      rw [abs_le] at this; norm_num at this ⊢; linarith
    linarith
  -- `xinf` is strictly feasible
  have hinf_int : Interior κ m xinf := fun i => by
    have h1 := (hslim i).1
    have h2 : 0 < slk κ m xinf i := lt_of_lt_of_le (mul_pos (hslk0 i) (by linarith only [h4δ])) h1
    simp only [slk] at h2
    have := (div_pos_iff_of_pos_right (hκ i)).mp h2
    linarith
  have hinf_eq : Aᵀ *ᵥ xinf = b := by
    have ht : Filter.Tendsto (fun j => Aᵀ *ᵥ X j) Filter.atTop (nhds (Aᵀ *ᵥ xinf)) :=
      ((Continuous.matrix_mulVec continuous_const continuous_id).tendsto xinf).comp hlim
    have : (fun j => Aᵀ *ᵥ X j) = fun _ => b := funext fun j => (hQ j).1.1
    rw [this] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hinf : xinf ∈ Feasible A b κ m := ⟨hinf_eq, hinf_int⟩
  -- `xinf` minimizes the objective
  set K : ℝ := ∑ i, w i * (4 / slk κ m x i) * U
  have hmin_inf : ∀ y ∈ Feasible A b κ m, centerObj κ m c w t xinf ≤ centerObj κ m c w t y := by
    intro y hy
    have hbound : ∀ j, centerObj κ m c w t (X j) - δ₀ / 2 ^ j * K ≤ centerObj κ m c w t y := by
      intro j
      obtain ⟨hfe, hδj, -, hslk, -⟩ := hQ j
      obtain ⟨ν, hν⟩ := cent_attained (dφ := barDphi κ m (X j)) (c := c) hC hA
        (barS_pos hκ hfe.2) t hw
      have hres := centerObj_ge_residual (c := c) (t := t) hκ hfe hy hw ν
      set R : Fin M → ℝ := fun i => (t * c i + w i * barDphi κ m (X j) i - (A *ᵥ ν) i) /
        (w i * barS κ m (X j) i)
      have hR : ‖R‖ ≤ δ₀ / 2 ^ j := by
        have : ‖R‖ ≤ mixed C w R := norm_le_mixed hC.le R
        rw [← hν] at this; exact this.trans hδj
      have hsum : ∑ i, w i * barS κ m (X j) i * |y i - X j i| ≤ K := by
        refine sum_le_sum fun i _ => ?_
        have hS2 : barS κ m (X j) i ≤ 4 / slk κ m x i := by
          have h1 := (eq_barrier hκ hfe.2 i).2.2.2.1
          have h2 := (hslk i).1
          have hs0 : 0 < slk κ m (X j) i := div_pos (by linarith [hfe.2 i]) (hκ i)
          have h3 : slk κ m x i / 2 ≤ slk κ m (X j) i := by
            have hf := hfrac' j
            have ha : 4 * δ₀ * (1 - 1 / 2 ^ j) ≤ 1 / 2 := by
              have := mul_le_mul_of_nonneg_left hf.2 (by positivity : (0 : ℝ) ≤ 4 * δ₀)
              linarith
            have : slk κ m x i / 2 ≤ slk κ m x i * (1 - 4 * δ₀ * (1 - 1 / 2 ^ j)) := by
              nlinarith [hslk0 i]
            linarith
          rw [le_div_iff₀ (hslk0 i)]
          change barS κ m (X j) i * slk κ m (X j) i ≤ 2 at h1
          nlinarith [barS_pos hκ hfe.2 i]
        have hyx : |y i - X j i| ≤ U := by
          have e : y i - X j i = (theta κ m y i - theta κ m (X j) i) / κ i := by
            simp only [theta]; field_simp [(hκ i).ne']; ring
          rw [e, abs_div, abs_of_pos (hκ i)]
          refine le_trans ?_ (hU i)
          apply div_le_div_of_nonneg_right _ (hκ i).le
          have := abs_add_le (theta κ m y i) (-theta κ m (X j) i)
          rw [abs_neg, ← sub_eq_add_neg] at this
          linarith [hy.2 i, hfe.2 i]
        have hw0 := (hw i).le
        calc w i * barS κ m (X j) i * |y i - X j i| ≤ w i * (4 / slk κ m x i) * U :=
              mul_le_mul (mul_le_mul_of_nonneg_left hS2 hw0) hyx (abs_nonneg _)
                (mul_nonneg hw0 (by have := hslk0 i; positivity))
          _ = w i * (4 / slk κ m x i) * U := rfl
      have hK0 : 0 ≤ ∑ i, w i * barS κ m (X j) i * |y i - X j i| :=
        sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hw i).le (barS_pos hκ hfe.2 i).le)
          (abs_nonneg _)
      calc centerObj κ m c w t (X j) - δ₀ / 2 ^ j * K
          ≤ centerObj κ m c w t (X j) - ‖R‖ * ∑ i, w i * barS κ m (X j) i * |y i - X j i| := by
            have := mul_le_mul hR hsum hK0 (by positivity)
            linarith
        _ ≤ centerObj κ m c w t y := hres
    have ht1 : Filter.Tendsto (fun j => centerObj κ m c w t (X j)) Filter.atTop
        (nhds (centerObj κ m c w t xinf)) := (continuousAt_centerObj hinf_int).tendsto.comp hlim
    have ht2 : Filter.Tendsto (fun j : ℕ => δ₀ / 2 ^ j * K) Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun j : ℕ => δ₀ * K * (1 / 2) ^ j) Filter.atTop (nhds (δ₀ * K * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
      rw [mul_zero] at this
      refine this.congr fun j => ?_
      rw [_root_.one_div_pow]; ring
    have := le_of_tendsto (ht1.sub ht2) (Filter.Eventually.of_forall hbound)
    simpa using this
  -- uniqueness identifies `xbar` with `xinf`
  have hxe : xbar = xinf := center_unique hκ hw hxbar hinf hmin hmin_inf
  subst hxe
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · have := (hslim i).1
    nlinarith [hslk0 i]
  · have := (hslim i).2
    nlinarith [hslk0 i]
  · have hd : ∀ j, ‖X j - x‖ ≤ 4 * U * δ₀ := fun j => by
      have := (hQ j).2.2.2.2
      have h1 := hfrac' j
      have : 4 * U * δ₀ * (1 - 1 / 2 ^ j) ≤ 4 * U * δ₀ :=
        mul_le_of_le_one_right (mul_nonneg (mul_nonneg (by norm_num) hUnn) hδ₀) h1.2
      linarith
    have ht : Filter.Tendsto (fun j => ‖X j - x‖) Filter.atTop (nhds ‖xbar - x‖) :=
      ((continuous_norm.comp (continuous_id.sub continuous_const)).tendsto xbar).comp hlim
    rw [norm_sub_rev]
    exact le_of_tendsto ht (Filter.Eventually.of_forall hd)

end

end ImplicitLP
end CutQueryComplexity
