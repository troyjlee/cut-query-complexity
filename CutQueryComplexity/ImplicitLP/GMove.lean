import CutQueryComplexity.ImplicitLP.LewisDeriv
import CutQueryComplexity.ImplicitLP.Movement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Regularized Lewis weights move slowly along interior segments (`eq:gmove`; Lee–Sidford audit)

The audited draft's barrier is `φᵢ(xᵢ) = −log cos θᵢ` with `θᵢ = κᵢ(xᵢ − mᵢ)`, `κᵢ = π/(uᵢ − ℓᵢ)` and
`mᵢ` the midpoint. Then `Sᵢ = √φᵢ'' = κᵢ / cos θᵢ` (`barS`), and the scaled constraint matrix is
`A_x = S(x)⁻¹ A = diag(e^{s(x)}) A` with `sᵢ(x) = log(cos θᵢ / κᵢ)` (`sfun`). The regularized
Lewis weights are `g(x) = w_p(A_x) + c₀` (`gfun`), for any `c₀ ≥ 0`.

`eq_gmove`: if the segment `x + [0,1]d` is interior, `v = N_{g(x)}(S(x)d) ≤ 1/10`, and
`p(1 + 1/C) ≤ 1 − a` with `0 ≤ a ≤ 1`, then `N_{g(x)}(log g(x+d) − log g(x)) ≤ (1 − a + 4v)v`.
With the audited draft's parameters `p = 1 − 1/L₀`, `k = 2L₀`, `C = 48k`, the hypothesis holds with
`a = 1/k` (`note_consistency`), giving the audited draft's `(1 − 1/k + 4v)v`.

The proof follows Lee–Sidford Lemma 16 with two repairs:
* the norm comparison is the sharp `N_{g'} ≤ e^{u/2} N_g` (gap G2);
* consistency is applied in the `g`-norm through `g ≥ w` (gap G4).

The pieces are:
* along the segment, `Sᵢ(t)|dᵢ| ≤ Sᵢ(0)|dᵢ| / (1 − Sᵢ(0)|dᵢ|)` (`barS_segment`), from the
  1-Lipschitz cosine;
* `sᵢ' = −sin θᵢ · Sᵢ dᵢ`, so the row log-scaling moves by at most `|S d|` (`hasDerivAt_sfun`);
* `(log g)' = (w/g) ⊙ K(s')` (`hasDerivAt_lewisLog_curve`, P2);
* `N_g((w/g) ⊙ Kh) ≤ p(1 + 1/C) N_g(h)` (`mixed_ratio_le`, P0);
* the bootstrap (`bootstrap`), closed by `e^{1.4ε}(1 − a)/(1 − ε) < 1 − a + 4ε` (`closing`).

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Filter Topology Set

noncomputable section

variable {M r : ℕ} {B : Matrix (Fin M) (Fin r) ℝ} {p : ℝ}

section Curve

variable (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2)
include hB hrow hp0 hp2

/-- **The Lewis Jacobian along a curve of row scalings.** -/
theorem hasDerivAt_lewisLog_curve {s : ℝ → Fin M → ℝ} {s' : Fin M → ℝ} {t₀ : ℝ}
    (hs : HasDerivAt s s' t₀) (i : Fin M) :
    let B₀ := diagonal (fun j => exp (s t₀ j)) * B
    let P := proj (diagonal (fun j => exp ((1 / 2 - 1 / p) * lewisLog p B₀ j)) * B₀)
    let σ : Fin M → ℝ := fun j => P j j
    let Λ : Matrix (Fin M) (Fin M) ℝ := diagonal σ - P ⊙ P
    let K : Matrix (Fin M) (Fin M) ℝ := (2 : ℝ) • ((diagonal σ + (2 / p - 1) • Λ)⁻¹ * Λ)
    HasDerivAt (fun t => lewisLog p (diagonal (fun j => exp (s t j)) * B) i) ((K *ᵥ s') i) t₀ := by
  intro B₀ P σ Λ K
  have hB₀ : (B₀ᵀ * B₀).det ≠ 0 := diag_det hB fun j => exp_ne_zero _
  have hr₀ : ∀ i, B₀ i ≠ 0 := diag_rows hrow fun j => exp_ne_zero _
  obtain ⟨L, hL⟩ := hasFDerivAt_lewisLog_scale hB₀ hr₀ hp0 hp2
  set F : (Fin M → ℝ) → Fin M → ℝ := fun u => lewisLog p (diagonal (fun j => exp (u j)) * B₀)
  have hcurve : HasDerivAt (fun t => s t - s t₀) s' t₀ := hs.sub_const _
  have hL' : HasFDerivAt F L ((fun t => s t - s t₀) t₀) := by simpa using hL
  have hcomp := HasFDerivAt.comp_hasDerivAt t₀ hL' hcurve
  have heq : (fun t => lewisLog p (diagonal (fun j => exp (s t j)) * B)) =
      F ∘ fun t => s t - s t₀ := by
    funext t
    simp only [Function.comp, F, B₀, diag_exp_mul, Pi.sub_apply, sub_add_cancel]
  rw [← heq] at hcomp
  have hci := hasDerivAt_pi.mp hcomp i
  -- identify `L s'` with `K s'` along the line `τ s'`
  have h1 := hasDerivAt_lewisLog hB₀ hr₀ hp0 hp2 s' i
  have hline : HasDerivAt (fun τ : ℝ => τ • s') s' 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const s'
  have hL0 : HasFDerivAt F L ((0 : ℝ) • s') := by rwa [zero_smul]
  have h2 := hasDerivAt_pi.mp (HasFDerivAt.comp_hasDerivAt (0 : ℝ) hL0 hline) i
  have hval : L s' i = (K *ᵥ s') i := h2.unique h1
  rw [← hval]
  exact hci

end Curve

section Barrier

variable (κ m : Fin M → ℝ)

/-- `θᵢ(x) = κᵢ(xᵢ − mᵢ)`. -/
def theta (x : Fin M → ℝ) (i : Fin M) : ℝ := κ i * (x i - m i)

/-- `Sᵢ(x) = √φᵢ''(xᵢ) = κᵢ / cos θᵢ`. -/
def barS (x : Fin M → ℝ) (i : Fin M) : ℝ := κ i / cos (theta κ m x i)

/-- The row log-scaling of `A_x = S(x)⁻¹ A`: `sᵢ(x) = log(cos θᵢ / κᵢ)`. -/
def sfun (x : Fin M → ℝ) (i : Fin M) : ℝ := Real.log (cos (theta κ m x i) / κ i)

/-- `x` is interior: `|θᵢ(x)| < π/2` for all `i`. -/
def Interior (x : Fin M → ℝ) : Prop := ∀ i, |theta κ m x i| < π / 2

/-- The regularized Lewis weights `g(x) = w_p(A_x) + c₀`. -/
def gfun (p c₀ : ℝ) (A : Matrix (Fin M) (Fin r) ℝ) (x : Fin M → ℝ) : Fin M → ℝ :=
  fun i => exp (lewisLog p (diagonal (fun j => exp (sfun κ m x j)) * A) i) + c₀

variable {κ m}

theorem cos_theta_pos {x : Fin M → ℝ} (hx : Interior κ m x) (i : Fin M) :
    0 < cos (theta κ m x i) :=
  cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le (theta κ m x i), hx i],
    by linarith [le_abs_self (theta κ m x i), hx i]⟩

theorem barS_pos (hκ : ∀ i, 0 < κ i) {x : Fin M → ℝ} (hx : Interior κ m x) (i : Fin M) :
    0 < barS κ m x i := div_pos (hκ i) (cos_theta_pos hx i)

theorem exp_sfun (hκ : ∀ i, 0 < κ i) {x : Fin M → ℝ} (hx : Interior κ m x) (i : Fin M) :
    exp (sfun κ m x i) = 1 / barS κ m x i := by
  rw [sfun, exp_log (div_pos (cos_theta_pos hx i) (hκ i)), barS, one_div_div]

/-- **The row log-scaling moves at rate `−sin θᵢ · Sᵢ dᵢ`.** -/
theorem hasDerivAt_sfun (hκ : ∀ i, 0 < κ i) {x d : Fin M → ℝ} {t : ℝ}
    (hx : Interior κ m (x + t • d)) :
    HasDerivAt (fun τ => sfun κ m (x + τ • d))
      (fun i => -sin (theta κ m (x + t • d) i) * (barS κ m (x + t • d) i * d i)) t := by
  refine hasDerivAt_pi.mpr fun i => ?_
  have hc := cos_theta_pos hx i
  have hθ : HasDerivAt (fun τ => theta κ m (x + τ • d) i) (κ i * d i) t := by
    have : (fun τ => theta κ m (x + τ • d) i) = fun τ => κ i * (x i + τ * d i - m i) := by
      funext τ; simp [theta]
    rw [this]
    have := (((hasDerivAt_id t).mul_const (d i)).const_add (x i)).sub_const (m i)
    simpa using this.const_mul (κ i)
  have hcos := (hθ.cos).div_const (κ i)
  have hlog := hcos.log (div_pos hc (hκ i)).ne'
  have hval : -sin (theta κ m (x + t • d) i) * (barS κ m (x + t • d) i * d i) =
      -sin (theta κ m (x + t • d) i) * (κ i * d i) / κ i / (cos (theta κ m (x + t • d) i) / κ i) := by
    unfold barS; field_simp
  rw [hval]
  exact hlog

/-- **Hessian control along the segment:** `Sᵢ(t)|dᵢ| ≤ Sᵢ(0)|dᵢ| / (1 − Sᵢ(0)|dᵢ|)`. -/
theorem barS_segment (hκ : ∀ i, 0 < κ i) {x d : Fin M → ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hx0 : Interior κ m x) (hxt : Interior κ m (x + t • d)) (i : Fin M)
    (hsmall : barS κ m x i * |d i| < 1) :
    barS κ m (x + t • d) i * |d i| ≤ barS κ m x i * |d i| / (1 - barS κ m x i * |d i|) := by
  have hc0 := cos_theta_pos hx0 i
  have hct := cos_theta_pos hxt i
  have hk := hκ i
  -- `cos θ(t) ≥ cos θ(0) − κ|d|`
  have hlip := abs_cos_sub_cos_le (theta κ m (x + t • d) i) (theta κ m x i)
  have hdiff : theta κ m (x + t • d) i - theta κ m x i = κ i * (t * d i) := by
    simp [theta]; ring
  rw [hdiff, abs_mul, abs_of_pos hk, abs_mul, abs_of_nonneg ht.1] at hlip
  have hcos : cos (theta κ m x i) - κ i * |d i| ≤ cos (theta κ m (x + t • d) i) := by
    have : κ i * (t * |d i|) ≤ κ i * |d i| := by
      apply mul_le_mul_of_nonneg_left _ hk.le
      nlinarith [ht.2, abs_nonneg (d i)]
    linarith [neg_abs_le (cos (theta κ m (x + t • d) i) - cos (theta κ m x i)), abs_sub_comm
      (cos (theta κ m (x + t • d) i)) (cos (theta κ m x i))]
  simp only [barS] at hsmall ⊢
  set c0 := cos (theta κ m x i)
  set ct := cos (theta κ m (x + t • d) i)
  have h1 : κ i / c0 * |d i| = κ i * |d i| / c0 := by ring
  rw [h1] at hsmall ⊢
  rw [div_lt_one hc0] at hsmall
  have hpos : 0 < c0 - κ i * |d i| := by linarith
  have hR : κ i * |d i| / c0 / (1 - κ i * |d i| / c0) = κ i * |d i| / (c0 - κ i * |d i|) := by
    field_simp
  rw [hR, show κ i / ct * |d i| = κ i * |d i| / ct by ring]
  exact div_le_div_of_nonneg_left (by positivity) hpos hcos

end Barrier

section Transfer

/-- **Consistency in the regularized norm** (audit gap G4): with `w = diag P` and `g = w + c₀`,
`N_g((w/g) ⊙ Kh) ≤ p(1 + 1/C) N_g(h)`. -/
theorem mixed_ratio_le {P : Matrix (Fin M) (Fin M) ℝ} (hsymm : Pᵀ = P) (hidem : P * P = P)
    (hpos : ∀ i, 0 < P i i) {w : Fin M → ℝ} (hw : ∀ i, w i = P i i) {c₀ C : ℝ} (hc₀ : 0 ≤ c₀)
    (hp0 : 0 < p) (hp2 : p ≤ 2) (hC : 0 < C) (h : Fin M → ℝ) :
    let σ : Fin M → ℝ := fun i => P i i
    let K : Matrix (Fin M) (Fin M) ℝ :=
      (2 : ℝ) • ((diagonal σ + (2 / p - 1) • (diagonal σ - P ⊙ P))⁻¹ * (diagonal σ - P ⊙ P))
    mixed C (fun i => w i + c₀) (fun i => w i / (w i + c₀) * (K *ᵥ h) i) ≤
      p * (1 + 1 / C) * mixed C (fun i => w i + c₀) h := by
  intro σ K
  have hc : 0 ≤ 2 / p - 1 := by rw [sub_nonneg, le_div_iff₀ hp0]; linarith
  have hmix := proj_jacobian_mixed hsymm hidem hpos hc hC h
  rw [beta_of_p hp0] at hmix
  have hwpos : ∀ i, 0 < w i := fun i => by rw [hw]; exact hpos i
  have hg : ∀ i, 0 < w i + c₀ := fun i => by linarith [hwpos i]
  have hr : ∀ i, 0 ≤ w i / (w i + c₀) ∧ w i / (w i + c₀) ≤ 1 := fun i =>
    ⟨(div_pos (hwpos i) (hg i)).le, (div_le_one (hg i)).mpr (by linarith)⟩
  have hσw : σ = w := funext fun i => (hw i).symm
  -- the sup part shrinks
  have h1 : ‖fun i => w i / (w i + c₀) * (K *ᵥ h) i‖ ≤ ‖K *ᵥ h‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr i).1]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hr i).2).trans
        (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i)
  -- the weighted part: `g (w/g)² ≤ w`
  have h2 : wnorm (fun i => w i + c₀) (fun i => w i / (w i + c₀) * (K *ᵥ h) i) ≤
      wnorm σ (K *ᵥ h) := by
    unfold wnorm
    apply Real.sqrt_le_sqrt
    refine sum_le_sum fun i _ => ?_
    rw [hσw]
    have e : (w i + c₀) * (w i / (w i + c₀) * (K *ᵥ h) i) ^ 2 =
        w i * (w i / (w i + c₀)) * (K *ᵥ h) i ^ 2 := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hwpos i).le (hr i).2)
      (sq_nonneg _)
  -- `‖h‖_w ≤ ‖h‖_g`
  have h3 : wnorm σ h ≤ wnorm (fun i => w i + c₀) h := by
    unfold wnorm
    apply Real.sqrt_le_sqrt
    refine sum_le_sum fun i _ => ?_
    rw [hσw]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hp : 0 ≤ p * (1 + 1 / C) := by positivity
  unfold mixed
  calc ‖fun i => w i / (w i + c₀) * (K *ᵥ h) i‖ +
        C * wnorm (fun i => w i + c₀) (fun i => w i / (w i + c₀) * (K *ᵥ h) i)
      ≤ ‖K *ᵥ h‖ + C * wnorm σ (K *ᵥ h) := add_le_add h1 (mul_le_mul_of_nonneg_left h2 hC.le)
    _ ≤ p * (1 + 1 / C) * (‖h‖ + C * wnorm σ h) := hmix
    _ ≤ p * (1 + 1 / C) * (‖h‖ + C * wnorm (fun i => w i + c₀) h) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 hC.le)) hp

end Transfer

/-- **The closing inequality** of the repaired Lemma 16:
`e^{(1−a+4ε)ε} (1 − a) ε / (1 − ε) < (1 − a + 4ε) ε` for `0 < ε ≤ 1/10`, `0 ≤ a ≤ 1`. -/
theorem closing {a ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    exp ((1 - a + 4 * ε) * ε) * (1 - a) * ε / (1 - ε) < (1 - a + 4 * ε) * ε := by
  set θ := (1 - a + 4 * ε) * ε
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1.4 * ε := by simp only [θ]; nlinarith
  have hexp : exp θ ≤ 1 + 1.6 * ε := by
    have := abs_exp_sub_one_sub_id_le (x := θ) (by rw [abs_of_nonneg hθ0]; linarith)
    rw [abs_le] at this
    nlinarith
  have hden : 0 < 1 - ε := by linarith
  rw [div_lt_iff₀ hden]
  have h1a : 0 ≤ 1 - a := by linarith
  have key : exp θ * (1 - a) * ε ≤ (1 + 1.6 * ε) * (1 - a) * ε := by
    apply mul_le_mul_of_nonneg_right _ hε.le
    exact mul_le_mul_of_nonneg_right hexp h1a
  calc exp θ * (1 - a) * ε ≤ (1 + 1.6 * ε) * (1 - a) * ε := key
    _ < θ * (1 - ε) := by
        have hq : 0 < ε ^ 2 * (4 - 2.6 * (1 - a) - 4 * ε) := mul_pos (by positivity) (by linarith)
        simp only [θ]; nlinarith [hq]


section GMove

variable {κ m : Fin M → ℝ} {A : Matrix (Fin M) (Fin r) ℝ}

/-- **`log g` along the segment:** `(log g)' = (w/g) ⊙ K(s')` with `s' = −sin θ ⊙ S ⊙ d`. -/
theorem hasDerivAt_log_gfun (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) (hp0 : 0 < p)
    (hp2 : p < 2) (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) {x d : Fin M → ℝ} {t : ℝ}
    (hxt : Interior κ m (x + t • d)) :
    let B₀ := diagonal (fun j => exp (sfun κ m (x + t • d) j)) * A
    let P := proj (diagonal (fun j => exp ((1 / 2 - 1 / p) * lewisLog p B₀ j)) * B₀)
    let σ : Fin M → ℝ := fun j => P j j
    let K : Matrix (Fin M) (Fin M) ℝ :=
      (2 : ℝ) • ((diagonal σ + (2 / p - 1) • (diagonal σ - P ⊙ P))⁻¹ * (diagonal σ - P ⊙ P))
    let s' : Fin M → ℝ := fun i => -sin (theta κ m (x + t • d) i) * (barS κ m (x + t • d) i * d i)
    HasDerivAt (fun τ => fun i => Real.log (gfun κ m p c₀ A (x + τ • d) i))
      (fun i => exp (lewisLog p B₀ i) / (exp (lewisLog p B₀ i) + c₀) * (K *ᵥ s') i) t := by
  intro B₀ P σ K s'
  refine hasDerivAt_pi.mpr fun i => ?_
  have hy := hasDerivAt_lewisLog_curve hA hrow hp0 hp2 (hasDerivAt_sfun (m := m) hκ hxt) i
  have hpos : 0 < exp (lewisLog p B₀ i) + c₀ := add_pos_of_pos_of_nonneg (exp_pos _) hc₀
  have h := (hy.exp.add_const c₀).log hpos.ne'
  exact h.congr_deriv (by ring)

/-- **Regularized Lewis weights move slowly** (`eq:gmove`, repaired Lee–Sidford Lemma 16). -/
theorem eq_gmove (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2)
    (hκ : ∀ i, 0 < κ i) {c₀ C a : ℝ} (hc₀ : 0 ≤ c₀) (hC : 0 < C) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hpa : p * (1 + 1 / C) ≤ 1 - a) {x d : Fin M → ℝ}
    (hint : ∀ t ∈ Icc (0 : ℝ) 1, Interior κ m (x + t • d))
    (hv : mixed C (gfun κ m p c₀ A x) (fun i => barS κ m x i * d i) ≤ 1 / 10) :
    mixed C (gfun κ m p c₀ A x)
        (fun i => Real.log (gfun κ m p c₀ A (x + d) i) - Real.log (gfun κ m p c₀ A x i)) ≤
      (1 - a + 4 * mixed C (gfun κ m p c₀ A x) (fun i => barS κ m x i * d i)) *
        mixed C (gfun κ m p c₀ A x) (fun i => barS κ m x i * d i) := by
  set g0 := gfun κ m p c₀ A x with hg0def
  set ε := mixed C g0 (fun i => barS κ m x i * d i) with hεdef
  set G : ℝ → Fin M → ℝ := fun t => gfun κ m p c₀ A (x + t • d) with hGdef
  have hG0 : G 0 = g0 := by simp [G, g0]
  have hG1 : G 1 = gfun κ m p c₀ A (x + d) := by simp [G]
  have hx0 : Interior κ m x := by simpa using hint 0 (left_mem_Icc.mpr zero_le_one)
  have hGpos : ∀ t i, 0 < G t i := fun t i => add_pos_of_pos_of_nonneg (exp_pos _) hc₀
  have hg0pos : ∀ i, 0 < g0 i := fun i => add_pos_of_pos_of_nonneg (exp_pos _) hc₀
  have hg0nn : ∀ i, 0 ≤ g0 i := fun i => (hg0pos i).le
  set q : ℝ → Fin M → ℝ := fun t i => Real.log (G t i) - Real.log (g0 i) with hqdef
  have hq1 : q 1 = fun i => Real.log (gfun κ m p c₀ A (x + d) i) - Real.log (g0 i) := by
    simp only [q, hG1]
  rw [← hq1]
  have hS0 : ∀ i, |barS κ m x i * d i| ≤ ε := fun i => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (fun i => barS κ m x i * d i) i).trans (norm_le_mixed hC.le _)
  rcases eq_or_lt_of_le (mixed_nonneg (g := g0) hC.le (fun i => barS κ m x i * d i)) with
    hε0 | hεpos
  · -- `ε = 0` forces `d = 0`
    have hε0' : ε = 0 := by rw [hεdef]; exact hε0.symm
    have hd0 : d = 0 := funext fun i => by
      have h := hS0 i
      rw [hε0', abs_mul, abs_of_pos (barS_pos hκ hx0 i)] at h
      have := mul_nonneg (barS_pos hκ hx0 i).le (abs_nonneg (d i))
      have h0 : barS κ m x i * |d i| = 0 := le_antisymm h this
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 (barS_pos hκ hx0 i).ne'
      · exact abs_eq_zero.mp h1
    have : q 1 = 0 := by funext i; simp [q, G, hd0, g0]
    rw [this, hε0']
    simp [mixed, wnorm]
  -- the bootstrap with `θ = (1 − a + 4ε)ε`
  set θ := (1 - a + 4 * ε) * ε with hθ
  set lam := exp θ * (1 - a) * ε / (1 - ε) with hlam
  have hcl : lam < θ := closing ha0 ha1 hεpos hv
  have hε1 : ε < 1 := by linarith
  have hlam0 : 0 ≤ lam := by
    have : 0 ≤ 1 - a := by linarith
    have : 0 < 1 - ε := by linarith
    positivity
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, ∃ q't, HasDerivAt q q't t ∧ (‖q t‖ < θ → mixed C g0 q't ≤ lam) := by
    intro t ht
    have hxt := hint t ht
    have hder := hasDerivAt_log_gfun (m := m) hA hrow hp0 hp2 hκ hc₀ hxt
    set B₀ := diagonal (fun j => exp (sfun κ m (x + t • d) j)) * A
    set P := proj (diagonal (fun j => exp ((1 / 2 - 1 / p) * lewisLog p B₀ j)) * B₀)
    set s' : Fin M → ℝ := fun i => -sin (theta κ m (x + t • d) i) * (barS κ m (x + t • d) i * d i)
    refine ⟨_, hder.sub_const (fun i => Real.log (g0 i)), fun hqt => ?_⟩
    set u := ‖q t‖
    have hu0 : 0 ≤ u := norm_nonneg _
    -- norm comparisons between `g0` and `G t`
    have hlogb : ∀ i, |Real.log (G t i) - Real.log (g0 i)| ≤ u := fun i => by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (q t) i
    have hcmp1 : ∀ i, g0 i ≤ exp u * G t i := fun i => by
      have h := (abs_le.mp (hlogb i)).2
      have := (abs_le.mp (hlogb i)).1
      rw [← exp_log (hg0pos i), ← exp_log (hGpos t i), ← exp_add, exp_le_exp]
      linarith
    have hcmp2 : ∀ i, G t i ≤ exp u * g0 i := fun i => by
      have h := (abs_le.mp (hlogb i)).2
      rw [← exp_log (hg0pos i), ← exp_log (hGpos t i), ← exp_add, exp_le_exp]
      linarith
    -- the Lewis-weight structure at time `t`
    have hBt : (B₀ᵀ * B₀).det ≠ 0 := diag_det hA fun j => exp_ne_zero _
    have hrt : ∀ i, B₀ i ≠ 0 := diag_rows hrow fun j => exp_ne_zero _
    have hPs : Pᵀ = P := proj_symm _
    have hPi : P * P = P := proj_idem (diag_det hBt fun j => exp_ne_zero _)
    have hw : ∀ i, exp (lewisLog p B₀ i) = P i i := fun i =>
      (lev_lewisLog hBt hrt hp0 hp2 i).symm
    have hPpos : ∀ i, 0 < P i i := fun i => by rw [← hw]; exact exp_pos _
    have hratio := mixed_ratio_le hPs hPi hPpos hw hc₀ hp0 hp2.le hC s'
    -- `|s'| ≤ |S_t d| ≤ |S₀ d| / (1 − ε)`
    have hs' : ∀ i, |s' i| ≤ |((1 - ε)⁻¹ • fun i => barS κ m x i * d i) i| := fun i => by
      have hS0i := hS0 i
      rw [abs_mul, abs_of_pos (barS_pos hκ hx0 i)] at hS0i
      have hseg := barS_segment hκ ht hx0 hxt i (by linarith)
      have hden : 1 - ε ≤ 1 - barS κ m x i * |d i| := by linarith
      have h1 : barS κ m x i * |d i| / (1 - barS κ m x i * |d i|) ≤
          barS κ m x i * |d i| / (1 - ε) :=
        div_le_div_of_nonneg_left (mul_nonneg (barS_pos hκ hx0 i).le (abs_nonneg _))
          (by linarith) hden
      simp only [s', Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg,
        abs_of_pos (barS_pos hκ hxt i), abs_of_pos (barS_pos hκ hx0 i),
        abs_of_pos (inv_pos.mpr (by linarith : (0 : ℝ) < 1 - ε))]
      calc |sin (theta κ m (x + t • d) i)| * (barS κ m (x + t • d) i * |d i|)
          ≤ 1 * (barS κ m (x + t • d) i * |d i|) :=
            mul_le_mul_of_nonneg_right (abs_sin_le_one _)
              (mul_nonneg (barS_pos hκ hxt i).le (abs_nonneg _))
        _ ≤ barS κ m x i * |d i| / (1 - ε) := by rw [one_mul]; exact hseg.trans h1
        _ = (1 - ε)⁻¹ * (barS κ m x i * |d i|) := by rw [div_eq_inv_mul]
    have hGt : G t = fun i => exp (lewisLog p B₀ i) + c₀ := rfl
    have hGnn : ∀ i, 0 ≤ G t i := fun i => (hGpos t i).le
    have hmono := mixed_mono hC.le hGnn hs'
    rw [mixed_smul, abs_of_pos (inv_pos.mpr (by linarith : (0 : ℝ) < 1 - ε))] at hmono
    have hback := mixed_le_of_le_exp (g := g0) hC.le hu0 hcmp2 (fun i => barS κ m x i * d i)
    have hpa' : 0 ≤ p * (1 + 1 / C) := by positivity
    have h1a : 0 ≤ 1 - a := by linarith
    have hinv : 0 ≤ (1 - ε)⁻¹ := (inv_pos.mpr (by linarith)).le
    have he : 0 ≤ exp (u / 2) := (exp_pos _).le
    have hmGt := mixed_nonneg (g := G t) hC.le s'
    have hmS := mixed_nonneg (g := G t) hC.le (fun i => barS κ m x i * d i)
    calc mixed C g0 _ ≤ exp (u / 2) * mixed C (G t) _ := mixed_le_of_le_exp hC.le hu0 hcmp1 _
      _ ≤ exp (u / 2) * (p * (1 + 1 / C) * mixed C (G t) s') :=
          mul_le_mul_of_nonneg_left hratio he
      _ ≤ exp (u / 2) * ((1 - a) * ((1 - ε)⁻¹ * mixed C (G t) fun i => barS κ m x i * d i)) := by
          apply mul_le_mul_of_nonneg_left _ he
          exact mul_le_mul hpa hmono hmGt h1a
      _ ≤ exp (u / 2) * ((1 - a) * ((1 - ε)⁻¹ * (exp (u / 2) * ε))) := by
          apply mul_le_mul_of_nonneg_left _ he
          apply mul_le_mul_of_nonneg_left _ h1a
          exact mul_le_mul_of_nonneg_left hback hinv
      _ = exp u * (1 - a) * ε / (1 - ε) := by
          rw [show exp u = exp (u / 2) * exp (u / 2) by rw [← exp_add]; ring_nf]
          field_simp
      _ ≤ lam := by
          rw [hlam]
          apply div_le_div_of_nonneg_right _ (by linarith)
          apply mul_le_mul_of_nonneg_right _ hεpos.le
          exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr hqt.le) h1a
  -- assemble the bootstrap
  classical
  have hq0 : q 0 = 0 := by funext i; simp [q, hG0]
  let q' : ℝ → Fin M → ℝ := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then (hd t ht).choose else 0
  have hq' : ∀ t (ht : t ∈ Icc (0 : ℝ) 1),
      HasDerivAt q (q' t) t ∧ (‖q t‖ < θ → mixed C g0 (q' t) ≤ lam) := fun t ht => by
    simp only [q', ht, ↓reduceDIte]; exact (hd t ht).choose_spec
  have hcont : ContinuousOn q (Icc 0 1) := fun t ht =>
    (hq' t ht).1.continuousAt.continuousWithinAt
  have hboot := bootstrap hC.le hg0nn hlam0 hcl hq0 hcont
    (fun t ht => (hq' t (Ico_subset_Icc_self ht)).1.hasDerivWithinAt)
    (fun t ht => (hq' t (Ico_subset_Icc_self ht)).2)
  exact hboot.trans hcl.le

/-- **The audited draft's consistency constant:** with `p = 1 − 1/L₀`, `k = 2L₀`, `C_N = 48k`,
`p(1 + 1/C_N) ≤ 1 − 1/k`. -/
theorem note_consistency {L₀ : ℝ} (hL : 1 ≤ L₀) :
    (1 - 1 / L₀) * (1 + 1 / (48 * (2 * L₀))) ≤ 1 - 1 / (2 * L₀) := by
  have hL0 : 0 < L₀ := by linarith
  set y := 1 / L₀ with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one hL0]; exact hL
  have e1 : 1 / (48 * (2 * L₀)) = y / 96 := by rw [hy]; field_simp; ring
  have e2 : 1 / (2 * L₀) = y / 2 := by rw [hy]; field_simp
  rw [e1, e2]
  nlinarith

/-- **`eq:gmove` with the audited draft's parameters:** `p = 1 − 1/L₀`, `k = 2L₀`, `C_N = 48k`, and any
regularization `c₀ ≥ 0` (in particular the repaired `c₀ = 1/(2M̄)`). -/
theorem eq_gmove_note (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) {x d : Fin M → ℝ}
    (hint : ∀ t ∈ Icc (0 : ℝ) 1, Interior κ m (x + t • d))
    (hv : mixed (48 * (2 * L₀)) (gfun κ m (1 - 1 / L₀) c₀ A x)
      (fun i => barS κ m x i * d i) ≤ 1 / 10) :
    let g := gfun κ m (1 - 1 / L₀) c₀ A
    let v := mixed (48 * (2 * L₀)) (g x) (fun i => barS κ m x i * d i)
    mixed (48 * (2 * L₀)) (g x) (fun i => Real.log (g (x + d) i) - Real.log (g x i)) ≤
      (1 - 1 / (2 * L₀) + 4 * v) * v := by
  intro g v
  have hL0 : 0 < L₀ := by linarith
  have hp0 : 0 < 1 - 1 / L₀ := by
    rw [sub_pos, div_lt_one hL0]; linarith
  have hp2 : 1 - 1 / L₀ < 2 := by
    have : 0 < 1 / L₀ := by positivity
    linarith
  have ha1 : 1 / (2 * L₀) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  exact eq_gmove hA hrow hp0 hp2 hκ hc₀ (by positivity) (by positivity) ha1
    (note_consistency (by linarith)) hint hv

end GMove

end

end ImplicitLP
end CutQueryComplexity
