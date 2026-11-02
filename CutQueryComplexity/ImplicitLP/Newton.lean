import CutQueryComplexity.ImplicitLP.Barrier
import CutQueryComplexity.ImplicitLP.Centrality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # The perturbed feasible Newton step (`lem:newton`, D7)

`lem_newton`: let `h` be the exact feasible Newton direction at `(x, w)`, and let `d = h + e`
with `Aᵀe = 0`, `N_w(Se) ≤ η`, and `N_w(Sd) ≤ a ≤ 1/10`. Then `x + d` is strictly interior,
`Aᵀd = 0`, and `δ_t(x + d, w) ≤ η/(1−a) + a²/(1−a)²`. With `a = γδ + η` and `γ ≤ 17/16` this
is at most `8δ² + 4η` (`newton_bound`). That is the audited draft's `eq:newton`, with absolute error `η`;
`η = 0` is allowed.

Keep the multiplier of `h`. The new residual is then
`(φ'(x+d) − φ'(x) − S²d)/S(x+d) + S²e/S(x+d)`. Per coordinate, write `θ = κ(x − m)`,
`u = κd`, and `s = |u|/cos θ = |S d|`. Then:
* `cos θ(1 − τs) ≤ cos(θ + τu) ≤ cos θ(1 + τs)`, by the 1-Lipschitz cosine;
* the Hessian variation `g(τ) = tan(θ+τu) − tan θ − τu sec²θ` satisfies
  `|g'(τ)| ≤ |u| sec²θ ((1−τs)⁻² − 1)`. Comparing with `B(τ) = |u| sec²θ · τ²s/(1−τs)` bounds
  the residual coordinate by `s²/(1−s)²` (`newton_coord`). There is no integral.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

/-- `1 − (1+v)⁻² ≤ (1−v)⁻² − 1` for `0 ≤ v < 1`. -/
theorem inv_sq_gap {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    1 - 1 / (1 + v) ^ 2 ≤ 1 / (1 - v) ^ 2 - 1 := by
  have h1 : 0 < 1 - v := by linarith
  have h2 : 0 < 1 + v := by linarith
  rw [div_sub' (by positivity), sub_div' (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_nonneg hv0 (sq_nonneg v), mul_nonneg hv0 hv0, mul_nonneg (mul_nonneg hv0 hv0) hv0,
    pow_pos h1 2, pow_pos h2 2, mul_nonneg (mul_nonneg hv0 hv0) (mul_nonneg hv0 hv0)]

/-- **One coordinate of the Newton step.** For `|θ| < π/2` and `s = |u|/cos θ < 1`:
`θ + u` is interior, `cos(θ + u) ≤ (1 + s) cos θ`, and the Hessian-variation residual
`(tan(θ+u) − tan θ − u/cos²θ) cos(θ+u)` is at most `s²/(1−s)²` in absolute value. -/
theorem newton_coord {θ u : ℝ} (hθ : |θ| < π / 2) (hs : |u| / cos θ < 1) :
    |θ + u| < π / 2 ∧ cos (θ + u) ≤ (1 + |u| / cos θ) * cos θ ∧
      |(tan (θ + u) - tan θ - u / cos θ ^ 2) * cos (θ + u)| ≤
        (|u| / cos θ) ^ 2 / (1 - |u| / cos θ) ^ 2 := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ], by
    linarith [le_abs_self θ]⟩
  set s := |u| / cos θ with hsdef
  have hs0 : 0 ≤ s := div_nonneg (abs_nonneg u) hc.le
  have hus : |u| = s * cos θ := by rw [hsdef]; field_simp
  -- cosine bounds along the segment
  have hcos : ∀ τ ∈ Icc (0 : ℝ) 1, (1 - τ * s) * cos θ ≤ cos (θ + τ * u) ∧
      cos (θ + τ * u) ≤ (1 + τ * s) * cos θ := fun τ hτ => by
    have := abs_cos_sub_cos_le (θ + τ * u) θ
    rw [show θ + τ * u - θ = τ * u by ring, abs_mul, abs_of_nonneg hτ.1, hus] at this
    rw [abs_le] at this
    constructor <;> nlinarith [this.1, this.2]
  have hcpos : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < cos (θ + τ * u) := fun τ hτ => by
    have h := (hcos τ hτ).1
    have : 0 < 1 - τ * s := by nlinarith [hτ.2]
    exact lt_of_lt_of_le (mul_pos this hc) h
  -- interiority
  have hint : |θ + u| < π / 2 := by
    have h1 : cos θ ≤ π / 2 - |θ| := by
      rw [← cos_abs, ← sin_pi_div_two_sub]
      exact (sin_lt (by linarith)).le
    have h2 : |u| < cos θ := by rw [hus]; nlinarith
    linarith [abs_add_le θ u]
  have hc1 := hcos 1 (right_mem_Icc.mpr zero_le_one)
  simp only [one_mul] at hc1
  refine ⟨hint, by linarith [hc1.2], ?_⟩
  -- the comparison argument
  set g : ℝ → ℝ := fun τ => tan (θ + τ * u) - tan θ - τ * u / cos θ ^ 2
  set g' : ℝ → ℝ := fun τ => u * (1 / cos (θ + τ * u) ^ 2) - u / cos θ ^ 2
  set B : ℝ → ℝ := fun τ => |u| / cos θ ^ 2 * (τ ^ 2 * s / (1 - τ * s))
  set B' : ℝ → ℝ := fun τ => |u| / cos θ ^ 2 * (1 / (1 - τ * s) ^ 2 - 1)
  have hg : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' τ) τ := fun τ hτ => by
    have h1 : HasDerivAt (fun τ => θ + τ * u) u τ := by
      simpa using ((hasDerivAt_id τ).mul_const u).const_add θ
    have h2 := (hasDerivAt_tan (hcpos τ hτ).ne').comp τ h1
    have h3 : HasDerivAt (fun τ => τ * u / cos θ ^ 2) (u / cos θ ^ 2) τ := by
      simpa using ((hasDerivAt_id τ).mul_const u).div_const (cos θ ^ 2)
    have := (h2.sub_const (tan θ)).sub h3
    exact this.congr_deriv (by ring)
  have hden : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < 1 - τ * s := fun τ hτ => by nlinarith [hτ.2]
  have hB : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt B (B' τ) τ := fun τ hτ => by
    have hd := hden τ hτ
    have h1 : HasDerivAt (fun τ : ℝ => τ ^ 2 * s) (2 * τ * s) τ := by
      simpa using ((hasDerivAt_pow 2 τ).mul_const s)
    have h2 : HasDerivAt (fun τ : ℝ => 1 - τ * s) (-s) τ := by
      simpa using ((hasDerivAt_id τ).mul_const s).const_sub 1
    have := (h1.div h2 hd.ne').const_mul (|u| / cos θ ^ 2)
    convert this using 1
    simp only [B']
    field_simp
    ring
  have hbound : ∀ τ ∈ Ico (0 : ℝ) 1, ‖g' τ‖ ≤ B' τ := fun τ hτ => by
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hτ
    obtain ⟨hlo, hhi⟩ := hcos τ hτ'
    have hd := hden τ hτ'
    have hcp := hcpos τ hτ'
    have hv1 : τ * s < 1 := by linarith
    have hv0 : 0 ≤ τ * s := mul_nonneg hτ.1 hs0
    -- `1/cos² ∈ [sec²θ (1+τs)⁻², sec²θ (1−τs)⁻²]`
    have hup : 1 / cos (θ + τ * u) ^ 2 ≤ 1 / cos θ ^ 2 * (1 / (1 - τ * s) ^ 2) := by
      rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
        one_mul]
      have := pow_le_pow_left₀ (by positivity) hlo 2
      nlinarith [this]
    have hlow : 1 / cos θ ^ 2 * (1 / (1 + τ * s) ^ 2) ≤ 1 / cos (θ + τ * u) ^ 2 := by
      rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
        one_mul]
      have := pow_le_pow_left₀ hcp.le hhi 2
      nlinarith [this]
    have hgap := inv_sq_gap hv0 hv1
    simp only [g', B', Real.norm_eq_abs]
    rw [show u * (1 / cos (θ + τ * u) ^ 2) - u / cos θ ^ 2 =
      u * (1 / cos (θ + τ * u) ^ 2 - 1 / cos θ ^ 2) by ring, abs_mul,
      show |u| / cos θ ^ 2 * (1 / (1 - τ * s) ^ 2 - 1) =
        |u| * (1 / cos θ ^ 2 * (1 / (1 - τ * s) ^ 2 - 1)) by ring]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg u)
    have hsec : 0 < 1 / cos θ ^ 2 := by positivity
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hgap hsec.le]
    · nlinarith
  have hcmp := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := g) (f' := g')
    (a := 0) (b := 1)
    (fun τ hτ => (hg τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hg τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
    (B := B) (B' := B') (by simp [g, B])
    (fun τ hτ => (hB τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hB τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt) hbound
    (right_mem_Icc.mpr zero_le_one)
  simp only [g, B, one_mul, one_pow, Real.norm_eq_abs] at hcmp
  -- `B(1) cos(θ+u) ≤ s²(1+s)/(1−s) ≤ s²/(1−s)²`
  have hd1 : 0 < 1 - s := by linarith
  have hcθu := hcpos 1 (right_mem_Icc.mpr zero_le_one)
  simp only [one_mul] at hcθu
  rw [abs_mul, abs_of_pos hcθu]
  calc |tan (θ + u) - tan θ - u / cos θ ^ 2| * cos (θ + u)
      ≤ |u| / cos θ ^ 2 * (s / (1 - s)) * ((1 + s) * cos θ) :=
        mul_le_mul hcmp hc1.2 hcθu.le (by positivity)
    _ = s ^ 2 * (1 + s) / (1 - s) := by rw [hus]; field_simp
    _ ≤ s ^ 2 / (1 - s) ^ 2 := by
        rw [div_le_div_iff₀ hd1 (by positivity)]
        have : (1 + s) * (1 - s) ≤ 1 := by nlinarith
        nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) hd1.le]

/-- The numeric close of `eq:newton`: with `a = γδ + η ≤ 1/10` and `0 ≤ γ ≤ 17/16`,
`η/(1−a) + a²/(1−a)² ≤ 8δ² + 4η`. -/
theorem newton_bound {γ δ η : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 17 / 16) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (ha : γ * δ + η ≤ 1 / 10) :
    η / (1 - (γ * δ + η)) + (γ * δ + η) ^ 2 / (1 - (γ * δ + η)) ^ 2 ≤ 8 * δ ^ 2 + 4 * η := by
  set a := γ * δ + η
  have ha0 : 0 ≤ a := by positivity
  have h1a : 9 / 10 ≤ 1 - a := by linarith
  have t1 : η / (1 - a) ≤ 10 / 9 * η := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have t2 : a ^ 2 / (1 - a) ^ 2 ≤ 100 / 81 * a ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 81 / 100 ≤ (1 - a) ^ 2 := by nlinarith
    nlinarith [sq_nonneg a]
  have t3 : a ^ 2 ≤ 289 / 256 * δ ^ 2 + 1 / 5 * η := by
    have hg : (γ * δ) ^ 2 ≤ (17 / 16) ^ 2 * δ ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hγ0 hγ 2) (sq_nonneg _)
    have : η * (2 * (γ * δ) + η) ≤ η * (1 / 5) := by
      apply mul_le_mul_of_nonneg_left _ hη
      have : 0 ≤ γ * δ := mul_nonneg hγ0 hδ
      linarith
    nlinarith
  nlinarith

variable {M r : ℕ}

/-- **The perturbed feasible Newton step** (`lem:newton`). -/
theorem lem_newton {κ m x w c : Fin M → ℝ} {t C : ℝ} {A : Matrix (Fin M) (Fin r) ℝ}
    (hκ : ∀ i, 0 < κ i) (hC : 0 < C) (hx : Interior κ m x) (hw : ∀ i, 0 < w i)
    {h e : Fin M → ℝ} {π₀ : Fin r → ℝ} (hh1 : Aᵀ *ᵥ h = 0)
    (hh2 : ∀ i, t * c i + w i * barDphi κ m x i + w i * barS κ m x i ^ 2 * h i = (A *ᵥ π₀) i)
    (he1 : Aᵀ *ᵥ e = 0) {η a : ℝ} (he : mixed C w (fun i => barS κ m x i * e i) ≤ η)
    (ha : mixed C w (fun i => barS κ m x i * (h i + e i)) ≤ a) (ha1 : a ≤ 1 / 10) :
    Interior κ m (x + (h + e)) ∧ Aᵀ *ᵥ (h + e) = 0 ∧
      cent C A (barS κ m (x + (h + e))) (barDphi κ m (x + (h + e))) c t w ≤
        η / (1 - a) + a ^ 2 / (1 - a) ^ 2 := by
  set d := h + e with hd
  set z : Fin M → ℝ := fun i => barS κ m x i * d i
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have ha0 : 0 ≤ a := (mixed_nonneg hC.le z).trans ha
  have hzi : ∀ i, |z i| ≤ a := fun i => by
    rw [← Real.norm_eq_abs]; exact ((norm_le_pi_norm z i).trans (norm_le_mixed hC.le z)).trans ha
  have hc : ∀ i, 0 < cos (theta κ m x i) := cos_theta_pos hx
  -- per-coordinate data: `θ' = θ + κd`, `s = |z|`
  have hθ' : ∀ i, theta κ m (x + d) i = theta κ m x i + κ i * d i := fun i => by
    simp only [theta, Pi.add_apply]; ring
  have hsz : ∀ i, |κ i * d i| / cos (theta κ m x i) = |z i| := fun i => by
    simp only [z, barS, abs_mul, abs_of_pos (hκ i), abs_div, abs_of_pos (hc i)]; ring
  have hcoord : ∀ i, |theta κ m (x + d) i| < π / 2 ∧
      cos (theta κ m (x + d) i) ≤ (1 + |z i|) * cos (theta κ m x i) ∧
      |(tan (theta κ m (x + d) i) - tan (theta κ m x i) - κ i * d i / cos (theta κ m x i) ^ 2) *
        cos (theta κ m (x + d) i)| ≤ |z i| ^ 2 / (1 - |z i|) ^ 2 := fun i => by
    have := newton_coord (hx i) (by rw [hsz]; linarith [hzi i])
    rw [hsz] at this; rw [hθ']; exact this
  have hx' : Interior κ m (x + d) := fun i => (hcoord i).1
  have hc' : ∀ i, 0 < cos (theta κ m (x + d) i) := cos_theta_pos hx'
  refine ⟨hx', by rw [hd, mulVec_add, hh1, he1, add_zero], ?_⟩
  -- the residual at the old multiplier
  set R1 : Fin M → ℝ := fun i =>
    (tan (theta κ m (x + d) i) - tan (theta κ m x i) - κ i * d i / cos (theta κ m x i) ^ 2) *
      cos (theta κ m (x + d) i)
  set R2 : Fin M → ℝ := fun i => barS κ m x i * e i * (cos (theta κ m (x + d) i) /
    cos (theta κ m x i))
  have hres : (fun i => (t * c i + w i * barDphi κ m (x + d) i - (A *ᵥ π₀) i) /
      (w i * barS κ m (x + d) i)) = R1 + R2 := by
    funext i
    rw [← hh2 i]
    simp only [Pi.add_apply, R1, R2, barDphi, barS]
    have hdi : d i = h i + e i := rfl
    field_simp [(hw i).ne', (hκ i).ne', (hc i).ne', (hc' i).ne']
    rw [hdi]; ring
  have h1a : 0 < 1 - a := by linarith
  have hK0 : 0 ≤ a / (1 - a) ^ 2 := by positivity
  have h1 : mixed C w R1 ≤ a ^ 2 / (1 - a) ^ 2 := by
    have hR1 : ∀ i, |R1 i| ≤ |((a / (1 - a) ^ 2) • z) i| := fun i => by
      have hzi' := hzi i
      have hz0 := abs_nonneg (z i)
      have hden : 0 < 1 - |z i| := by linarith
      rw [Pi.smul_apply, smul_eq_mul, abs_mul (a / (1 - a) ^ 2), abs_of_nonneg hK0]
      refine (hcoord i).2.2.trans ?_
      have hq : |z i| / (1 - |z i|) ^ 2 ≤ a / (1 - a) ^ 2 :=
        calc |z i| / (1 - |z i|) ^ 2 ≤ a / (1 - |z i|) ^ 2 :=
              div_le_div_of_nonneg_right hzi' (by positivity)
          _ ≤ a / (1 - a) ^ 2 :=
              div_le_div_of_nonneg_left ha0 (by positivity)
                (pow_le_pow_left₀ h1a.le (by linarith) 2)
      calc |z i| ^ 2 / (1 - |z i|) ^ 2 = |z i| * (|z i| / (1 - |z i|) ^ 2) := by ring
        _ ≤ |z i| * (a / (1 - a) ^ 2) := mul_le_mul_of_nonneg_left hq hz0
        _ = a / (1 - a) ^ 2 * |z i| := by ring
    have := mixed_mono hC.le hw0 hR1
    rw [mixed_smul, abs_of_nonneg hK0] at this
    calc mixed C w R1 ≤ a / (1 - a) ^ 2 * mixed C w z := this
      _ ≤ a / (1 - a) ^ 2 * a := mul_le_mul_of_nonneg_left ha hK0
      _ = a ^ 2 / (1 - a) ^ 2 := by ring
  have hK1 : 0 < 1 / (1 - a) := one_div_pos.mpr h1a
  have h2 : mixed C w R2 ≤ η / (1 - a) := by
    have hR2 : ∀ i, |R2 i| ≤ |((1 / (1 - a)) • fun i => barS κ m x i * e i) i| := fun i => by
      have hzi' := hzi i
      rw [Pi.smul_apply, smul_eq_mul, abs_mul (1 / (1 - a)), abs_of_pos hK1]
      have hratio : |cos (theta κ m (x + d) i) / cos (theta κ m x i)| ≤ 1 / (1 - a) := by
        rw [abs_of_pos (div_pos (hc' i) (hc i)), div_le_iff₀ (hc i)]
        refine (hcoord i).2.1.trans ?_
        apply mul_le_mul_of_nonneg_right _ (hc i).le
        rw [le_div_iff₀ h1a]
        nlinarith [abs_nonneg (z i)]
      show |barS κ m x i * e i * (cos (theta κ m (x + d) i) / cos (theta κ m x i))| ≤ _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
    have := mixed_mono hC.le hw0 hR2
    rw [mixed_smul, abs_of_pos hK1] at this
    calc mixed C w R2 ≤ 1 / (1 - a) * mixed C w (fun i => barS κ m x i * e i) := this
      _ ≤ 1 / (1 - a) * η := mul_le_mul_of_nonneg_left he hK1.le
      _ = η / (1 - a) := by ring
  calc cent C A (barS κ m (x + d)) (barDphi κ m (x + d)) c t w
      ≤ mixed C w (fun i => (t * c i + w i * barDphi κ m (x + d) i - (A *ᵥ π₀) i) /
          (w i * barS κ m (x + d) i)) := ciInf_le (cent_bdd hC.le t w) π₀
    _ = mixed C w (R1 + R2) := by rw [hres]
    _ ≤ mixed C w R1 + mixed C w R2 := mixed_add_le hC.le hw0 _ _
    _ ≤ η / (1 - a) + a ^ 2 / (1 - a) ^ 2 := by linarith

/-- **`eq:newton`**: if the exact direction satisfies `N_w(Sh) ≤ γδ` with `0 ≤ γ ≤ 17/16`, as
given by `eq:projection`, and `γδ + η ≤ 1/10`, then the perturbed step is interior and exactly
feasible, and `δ_t(x + d, w) ≤ 8δ² + 4η`. -/
theorem eq_newton {κ m x w c : Fin M → ℝ} {t C : ℝ} {A : Matrix (Fin M) (Fin r) ℝ}
    (hκ : ∀ i, 0 < κ i) (hC : 0 < C) (hx : Interior κ m x) (hw : ∀ i, 0 < w i)
    {h e : Fin M → ℝ} {π₀ : Fin r → ℝ} (hh1 : Aᵀ *ᵥ h = 0)
    (hh2 : ∀ i, t * c i + w i * barDphi κ m x i + w i * barS κ m x i ^ 2 * h i = (A *ᵥ π₀) i)
    (he1 : Aᵀ *ᵥ e = 0) {γ δ η : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 17 / 16) (hδ : 0 ≤ δ)
    (hSh : mixed C w (fun i => barS κ m x i * h i) ≤ γ * δ)
    (he : mixed C w (fun i => barS κ m x i * e i) ≤ η) (ha : γ * δ + η ≤ 1 / 10) :
    Interior κ m (x + (h + e)) ∧ Aᵀ *ᵥ (h + e) = 0 ∧
      cent C A (barS κ m (x + (h + e))) (barDphi κ m (x + (h + e))) c t w ≤
        8 * δ ^ 2 + 4 * η := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hη : 0 ≤ η := (mixed_nonneg hC.le _).trans he
  have hd : mixed C w (fun i => barS κ m x i * (h i + e i)) ≤ γ * δ + η := by
    have : (fun i => barS κ m x i * (h i + e i)) =
        (fun i => barS κ m x i * h i) + fun i => barS κ m x i * e i := by
      funext i; simp only [Pi.add_apply]; ring
    rw [this]
    exact (mixed_add_le hC.le hw0 _ _).trans (add_le_add hSh he)
  obtain ⟨h1, h2, h3⟩ := lem_newton hκ hC hx hw hh1 hh2 he1 he hd ha
  exact ⟨h1, h2, h3.trans (newton_bound hγ0 hγ hδ hη ha)⟩

end

end ImplicitLP
end CutQueryComplexity
