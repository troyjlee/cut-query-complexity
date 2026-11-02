import CutQueryComplexity.ImplicitLP.LewisJacobian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Mixed norms and the movement bootstrap (Lee–Sidford audit, toward `eq:gmove`)

The audited draft's norm is `N_g(y) = ‖y‖_∞ + C‖y‖_g` (`mixed`). This file proves:

* `mixed` is a continuous seminorm (`wnorm_add_le` is Minkowski for the weighted `ℓ₂` norm);
* `mixed_le_of_le_exp`: if `g' ≤ e^u g` coordinatewise then `N_{g'} ≤ e^{u/2} N_g`. This is the
  sharp norm comparison that repairs the proof of Lee–Sidford Lemma 16 (audit gap G2), where the
  factor `1 + 2ε` was paid once instead of twice;
* `bootstrap`: if `q(0) = 0` and `N_g(q'(t)) ≤ λ` whenever `‖q(t)‖_∞ < θ`, with `λ < θ`, then
  `N_g(q(1)) ≤ λ`. This is the continuity argument of Lemma 16, run as a comparison with the
  line `t ↦ μt` for every `μ ∈ (λ, θ)`.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Finset Filter Topology Set

noncomputable section

variable {M : ℕ}

/-- The audited draft's mixed norm `N_g(y) = ‖y‖_∞ + C‖y‖_g`. -/
def mixed (C : ℝ) (g y : Fin M → ℝ) : ℝ := ‖y‖ + C * wnorm g y

section WNorm

variable {g : Fin M → ℝ}

theorem wnorm_sq (hg : ∀ i, 0 ≤ g i) (y : Fin M → ℝ) : wnorm g y ^ 2 = ∑ i, g i * y i ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun i _ => mul_nonneg (hg i) (sq_nonneg _))

theorem wnorm_smul (c : ℝ) (y : Fin M → ℝ) : wnorm g (c • y) = |c| * wnorm g y := by
  unfold wnorm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), mul_sum]
  congr 1
  exact sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem wnorm_neg (y : Fin M → ℝ) : wnorm g (-y) = wnorm g y := by
  simp [wnorm]

/-- **Minkowski** for the weighted `ℓ₂` norm. -/
theorem wnorm_add_le (hg : ∀ i, 0 ≤ g i) (x y : Fin M → ℝ) :
    wnorm g (x + y) ≤ wnorm g x + wnorm g y := by
  have hx := wnorm_nonneg g x
  have hy := wnorm_nonneg g y
  rw [← Real.sqrt_sq (add_nonneg hx hy)]
  show Real.sqrt (∑ i, g i * (x + y) i ^ 2) ≤ Real.sqrt ((wnorm g x + wnorm g y) ^ 2)
  apply Real.sqrt_le_sqrt
  have hcs : ∑ i, g i * x i * y i ≤ wnorm g x * wnorm g y := by
    have h := sum_mul_sq_le_sq_mul_sq univ (fun i => Real.sqrt (g i) * x i)
      (fun i => Real.sqrt (g i) * y i)
    have e1 : ∀ i, Real.sqrt (g i) * x i * (Real.sqrt (g i) * y i) = g i * x i * y i := fun i => by
      calc Real.sqrt (g i) * x i * (Real.sqrt (g i) * y i)
          = (Real.sqrt (g i) * Real.sqrt (g i)) * x i * y i := by ring
        _ = g i * x i * y i := by rw [Real.mul_self_sqrt (hg i)]
    have e2 : ∀ (z : Fin M → ℝ) i, (Real.sqrt (g i) * z i) ^ 2 = g i * z i ^ 2 := fun z i => by
      rw [mul_pow, Real.sq_sqrt (hg i)]
    simp only [e1, e2] at h
    rw [← wnorm_sq hg x, ← wnorm_sq hg y, ← mul_pow] at h
    exact abs_le_of_sq_le_sq' h (by positivity) |>.2
  have : ∑ i, g i * (x + y) i ^ 2 =
      ∑ i, g i * x i ^ 2 + 2 * ∑ i, g i * x i * y i + ∑ i, g i * y i ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  rw [this, ← wnorm_sq hg x, ← wnorm_sq hg y]
  nlinarith

theorem continuous_wnorm : Continuous (wnorm (M := M) g) := by
  unfold wnorm; fun_prop

end WNorm

section Mixed

variable {C : ℝ} {g : Fin M → ℝ}

theorem norm_le_mixed (hC : 0 ≤ C) (y : Fin M → ℝ) : ‖y‖ ≤ mixed C g y :=
  le_add_of_nonneg_right (mul_nonneg hC (wnorm_nonneg g y))

theorem mixed_nonneg (hC : 0 ≤ C) (y : Fin M → ℝ) : 0 ≤ mixed C g y :=
  (norm_nonneg y).trans (norm_le_mixed hC y)

theorem mixed_smul (c : ℝ) (y : Fin M → ℝ) : mixed C g (c • y) = |c| * mixed C g y := by
  simp only [mixed, norm_smul, Real.norm_eq_abs, wnorm_smul]; ring

theorem mixed_add_le (hC : 0 ≤ C) (hg : ∀ i, 0 ≤ g i) (x y : Fin M → ℝ) :
    mixed C g (x + y) ≤ mixed C g x + mixed C g y := by
  unfold mixed
  have := norm_add_le x y
  have := mul_le_mul_of_nonneg_left (wnorm_add_le hg x y) hC
  linarith

theorem mixed_sub_le (hC : 0 ≤ C) (hg : ∀ i, 0 ≤ g i) (x y : Fin M → ℝ) :
    mixed C g x - mixed C g y ≤ mixed C g (x - y) := by
  have := mixed_add_le hC hg (x - y) y
  rw [sub_add_cancel] at this
  linarith

theorem continuous_mixed : Continuous (mixed (M := M) C g) := by
  unfold mixed; exact continuous_norm.add (continuous_const.mul continuous_wnorm)

/-- Coordinatewise domination `|x| ≤ |y|` gives `N_g(x) ≤ N_g(y)` for `g ≥ 0`. -/
theorem mixed_mono (hC : 0 ≤ C) (hg : ∀ i, 0 ≤ g i) {x y : Fin M → ℝ}
    (hxy : ∀ i, |x i| ≤ |y i|) : mixed C g x ≤ mixed C g y := by
  unfold mixed
  have h1 : ‖x‖ ≤ ‖y‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun i => by
    rw [Real.norm_eq_abs]; exact (hxy i).trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y i)
  have h2 : wnorm g x ≤ wnorm g y := by
    unfold wnorm
    apply Real.sqrt_le_sqrt
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (by rw [← sq_abs, ← sq_abs (y i)]; exact pow_le_pow_left₀ (abs_nonneg _) (hxy i) 2) (hg i)
  nlinarith

/-- **Sharp norm comparison** (repair of audit gap G2): if `g' ≤ e^u g` then
`N_{g'} ≤ e^{u/2} N_g`. -/
theorem mixed_le_of_le_exp (hC : 0 ≤ C) {g' : Fin M → ℝ} {u : ℝ}
    (hu : 0 ≤ u) (hle : ∀ i, g' i ≤ Real.exp u * g i) (y : Fin M → ℝ) :
    mixed C g' y ≤ Real.exp (u / 2) * mixed C g y := by
  have hw : wnorm g' y ≤ Real.exp (u / 2) * wnorm g y := by
    unfold wnorm
    rw [← Real.sqrt_sq (Real.exp_pos _).le, ← Real.sqrt_mul (sq_nonneg _), mul_sum]
    apply Real.sqrt_le_sqrt
    refine sum_le_sum fun i _ => ?_
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (u / 2) = u by push_cast; ring, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)
  have h1 : (1 : ℝ) ≤ Real.exp (u / 2) := Real.one_le_exp (by linarith)
  unfold mixed
  have := mul_le_mul_of_nonneg_left hw hC
  nlinarith [norm_nonneg y, wnorm_nonneg g y]

/-- **The movement bootstrap** (the continuity argument of Lee–Sidford Lemma 16). -/
theorem bootstrap (hC : 0 ≤ C) (hg : ∀ i, 0 ≤ g i) {q q' : ℝ → Fin M → ℝ} {θ lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam : lam < θ) (hq0 : q 0 = 0) (hcont : ContinuousOn q (Icc 0 1))
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt q (q' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖q t‖ < θ → mixed C g (q' t) ≤ lam) :
    mixed C g (q 1) ≤ lam := by
  -- comparison with `t ↦ μ t` for every `μ ∈ (lam, θ)`
  have key : ∀ μ, lam < μ → μ < θ → mixed C g (q 1) ≤ μ := by
    intro μ hμ1 hμ2
    have hf : ContinuousOn (fun t => mixed C g (q t)) (Icc 0 1) :=
      continuous_mixed.comp_continuousOn hcont
    have hslope : ∀ x ∈ Ico (0 : ℝ) 1, ∀ r, mixed C g (q' x) < r →
        ∃ᶠ z in 𝓝[>] x, slope (fun t => mixed C g (q t)) x z < r := by
      intro x hx r hr
      have ht : Tendsto (slope q x) (𝓝[>] x) (𝓝 (q' x)) := by
        have := (hasDerivWithinAt_iff_tendsto_slope.mp (hd x hx))
        have hset : Ici x \ {x} = Ioi x := by
          ext z; simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
          constructor
          · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
          · intro h; exact ⟨h.le, h.ne'⟩
        rwa [hset] at this
      have hlim : Tendsto (fun z => mixed C g (slope q x z)) (𝓝[>] x) (𝓝 (mixed C g (q' x))) :=
        (continuous_mixed.tendsto _).comp ht
      have hev : ∀ᶠ z in 𝓝[>] x, mixed C g (slope q x z) < r := hlim.eventually (gt_mem_nhds hr)
      refine (hev.mp ?_).frequently
      filter_upwards [self_mem_nhdsWithin] with z hz h
      refine lt_of_le_of_lt ?_ h
      have hzx : 0 < z - x := sub_pos.mpr hz
      rw [slope_def_field, slope_def_module, mixed_smul, abs_of_pos (inv_pos.mpr hzx),
        div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (mixed_sub_le hC hg _ _) (inv_pos.mpr hzx).le
    have := image_le_of_liminf_slope_right_lt_deriv_boundary (B := fun t => μ * t)
      (B' := fun _ => μ) hf hslope (by simp [hq0, mixed, wnorm])
      (fun x => by simpa using (hasDerivAt_id x).const_mul μ) (fun x hx heq => by
        have h1 : ‖q x‖ ≤ μ * x := heq ▸ norm_le_mixed hC (q x)
        have h2 : μ * x ≤ μ := by nlinarith [hx.1, hx.2, hμ1, (norm_nonneg (q x))]
        exact lt_of_le_of_lt (hbound x hx (by linarith)) hμ1)
      (right_mem_Icc.mpr zero_le_one)
    simpa using this
  by_contra hcon
  push Not at hcon
  set μ := (lam + min (mixed C g (q 1)) θ) / 2
  have h1 : lam < min (mixed C g (q 1)) θ := lt_min hcon hlam
  have hm1 := min_le_left (mixed C g (q 1)) θ
  have hm2 := min_le_right (mixed C g (q 1)) θ
  have := key μ (by simp only [μ]; linarith) (by simp only [μ]; linarith)
  simp only [μ] at this
  linarith

end Mixed

end

end ImplicitLP
end CutQueryComplexity
