import CutQueryComplexity.ImplicitLP.Support
import CutQueryComplexity.ImplicitLP.Trisection

/-! # Assembling the support oracle (`lem:support`, D7)

`support_main`: the support oracle composed from the normalization, the regularization
(`G₀ ≤ G_ρ + ρ`), the endpoint restriction to `[h, 1 − h]` (Lipschitz loss `Lh`), trisection with
an incumbent over the certified fixed-`τ` evaluator, and unscaling. The output `v̂` lies in the ball
`{N_w ≤ C_*}`, is sign-aligned with `q`, and satisfies
`⟨q, v⟩ ≤ ⟨q, v̂⟩ + ρ + Lh + 3ε + L(1 − 2h)(2/3)ⁿ` for every `v` in the ball, where `ε` is the
evaluator's interval width. `round_down` then accounts for dyadic rounding of the magnitudes:
feasibility and sign alignment are kept, and the loss is at most `Σ|qᵢ|` times the grid width.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Finset Real Set

noncomputable section

variable {M : ℕ}

/-- `G₀ ≤ G_ρ + ρ` on `[0,1]`: feasible points have `‖z‖₂ ≤ 1`. -/
theorem Gval_zero_le {a κ : Fin M → ℝ} (hκ : ∀ i, 0 < κ i) {ρ τ : ℝ} (hρ : 0 ≤ ρ)
    (hτ : τ ∈ Icc (0 : ℝ) 1) : Gval a κ 0 τ ≤ Gval a κ ρ τ + ρ := by
  obtain ⟨z, hz, he⟩ := Gval_attained hκ a 0 hτ
  rw [he]
  have h1 : euc z ^ 2 ≤ 1 := by
    have := hz.1; have := euc_nonneg z
    nlinarith [hτ.1]
  have := le_Gval a κ ρ τ hz
  unfold fobj at this ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1 hρ]

/-- **Rounding magnitudes down** keeps feasibility and sign alignment, and loses at most
`Σ|qᵢ| · δ` when each magnitude decreases by at most `δ`. -/
theorem round_down {C Cs : ℝ} {w q v v' : Fin M → ℝ} (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i)
    (hv : mixed C w v ≤ Cs) (habs : ∀ i, |v' i| ≤ |v i|) (hsign : ∀ i, 0 ≤ v i * v' i)
    {δ : ℝ} (hδ : ∀ i, |v i - v' i| ≤ δ) (hal : ∀ i, 0 ≤ q i * v i) :
    mixed C w v' ≤ Cs ∧ (∀ i, 0 ≤ q i * v' i) ∧ q ⬝ᵥ v - (∑ i, |q i|) * δ ≤ q ⬝ᵥ v' := by
  refine ⟨(mixed_mono hC hw habs).trans hv, fun i => ?_, ?_⟩
  · have h1 := hal i; have h2 := hsign i
    rcases lt_trichotomy (v i) 0 with h | h | h
    · have : v' i ≤ 0 := by nlinarith
      have : q i ≤ 0 := by nlinarith
      nlinarith
    · have : v' i = 0 := by
        have := habs i; rw [h, abs_zero] at this; exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      rw [this, mul_zero]
    · have : 0 ≤ v' i := by nlinarith
      have : 0 ≤ q i := by nlinarith
      nlinarith
  · have : q ⬝ᵥ v - q ⬝ᵥ v' ≤ (∑ i, |q i|) * δ := by
      rw [← dotProduct_sub, sum_mul]
      refine (le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_))
      simp only [Pi.sub_apply]; rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hδ i) (abs_nonneg _)
    linarith

/-- **The support oracle** (`lem:support`, exact-arithmetic assembly). With the normalized data
`a, κ` of `support_normalize`, regularization `ρ > 0`, endpoint margin `0 < h ≤ 1/2`, a public
bound `A₊ ≥ ‖a‖₂`, `n` trisection steps and `m` bisection steps per evaluation, there is `v̂` in the
ball `{N_w ≤ C_*}`, sign-aligned with `q`, with
`⟨q, v⟩ ≤ ⟨q, v̂⟩ + ρ + Lh + 3ε + L(1 − 2h)(2/3)ⁿ` for every `v` in the ball. Here
`L = max{‖a‖₂, Σ|aᵢ|κᵢ}` and `ε = Λ²‖a‖₂/(ρ² 2^m)` with `Λ = A₊/h`. -/
theorem support_main {C Cs : ℝ} {w q : Fin M → ℝ} (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < w i)
    {ρ h Ap : ℝ} (hρ : 0 < ρ) (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * q i / (C * Real.sqrt (w i))) ≤ Ap) (n m : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let ε := (Ap / h) ^ 2 * euc a / (ρ ^ 2 * 2 ^ m)
    ∃ vh : Fin M → ℝ, mixed C w vh ≤ Cs ∧ (∀ i, 0 ≤ q i * vh i) ∧
      ∀ v, mixed C w v ≤ Cs →
        q ⬝ᵥ v ≤ q ⬝ᵥ vh + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ n)) := by
  intro κ a L ε
  have hsq : ∀ i, 0 < Real.sqrt (w i) := fun i => Real.sqrt_pos.mpr (hw i)
  have hκ : ∀ i, 0 < κ i := fun i => mul_pos hC (hsq i)
  have hL0 : 0 ≤ L := (euc_nonneg a).trans (le_max_left _ _)
  have hΛ0 : 0 ≤ Ap / h := div_nonneg ((euc_nonneg a).trans hAp) hh0.le
  -- the evaluator on `[h, 1 − h]`
  have hev : ∀ τ ∈ Icc h (1 - h), ∃ zh : Fin M → ℝ, ∃ ℓ u : ℝ, zh ∈ Fset κ τ ∧
      (∀ i, 0 ≤ a i * zh i) ∧ ℓ = fobj a ρ zh ∧ ℓ ≤ Gval a κ ρ τ ∧ Gval a κ ρ τ ≤ u ∧
      u - ℓ ≤ ε := by
    intro τ hτ
    have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hΛr : euc (zlam a κ ρ τ (Ap / h)) ≤ 1 - τ := by
      refine (euc_zlam_le hκ hτ01.1 (by positivity)).trans ?_
      have h1 : euc a / (2 * (ρ + Ap / h)) ≤ Ap / (2 * (Ap / h)) ∨ Ap = 0 := by
        rcases eq_or_lt_of_le ((euc_nonneg a).trans hAp) with h0 | h0
        · exact Or.inr h0.symm
        · left
          apply div_le_div₀ (by linarith [euc_nonneg a]) hAp (by positivity) (by linarith)
      rcases h1 with h1 | h1
      · have : Ap / (2 * (Ap / h)) ≤ h / 2 := by
          rcases eq_or_lt_of_le ((euc_nonneg a).trans hAp) with h0 | h0
          · rw [← h0]; simp; positivity
          · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; field_simp; linarith
        linarith [hτ.2]
      · have : euc a = 0 := le_antisymm (h1 ▸ hAp) (euc_nonneg a)
        rw [this, zero_div]; linarith [hτ.2]
    exact evaluator hκ hρ hτ01 hΛ0 hΛr m
  choose! zf lf uf hzf using hev
  -- trisection
  have hcc : ∀ s ∈ Icc h (1 - h), ∀ t ∈ Icc h (1 - h), ∀ θ ∈ Icc (0 : ℝ) 1,
      θ * Gval a κ ρ s + (1 - θ) * Gval a κ ρ t ≤ Gval a κ ρ (θ * s + (1 - θ) * t) :=
    fun s hs t ht θ hθ => Gval_concave hκ hρ.le ⟨by linarith [hs.1], by linarith [hs.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ hθ
  have hlip : ∀ s ∈ Icc h (1 - h), ∀ t ∈ Icc h (1 - h), Gval a κ ρ s ≤ Gval a κ ρ t + L * |s - t| :=
    fun s hs t ht => Gval_lipschitz hκ hρ.le ⟨by linarith [hs.1], by linarith [hs.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have horacle : ∀ t ∈ Icc h (1 - h), lf t ≤ Gval a κ ρ t ∧ Gval a κ ρ t ≤ uf t ∧
      uf t ≤ lf t + ε := fun t ht => by
    obtain ⟨-, -, -, h4, h5, h6⟩ := hzf t ht
    exact ⟨h4, h5, by linarith⟩
  have hε0 : 0 ≤ ε := by
    have := horacle h ⟨le_rfl, by linarith⟩
    linarith [this.1, this.2.1, this.2.2]
  obtain ⟨⟨t₀, ht₀, hbest⟩, hbound⟩ := trisect_bound (by linarith) hε0 hcc hlip horacle hL0 n
  set best := (trisect lf uf h (1 - h) n).best
  obtain ⟨hzmem, hzsign, hzval, -, -, -⟩ := hzf t₀ ht₀
  set zh := zf t₀
  set vh : Fin M → ℝ := fun i => Cs * zh i / (C * Real.sqrt (w i))
  -- `v̂` normalizes back to `ẑ`
  have hnorm := support_normalize (q := q) hC hCs hw vh
  have hzv : (fun i => C / Cs * Real.sqrt (w i) * vh i) = zh := by
    funext i; simp only [vh]; field_simp [(hsq i).ne', hC.ne', hCs.ne']
  have hzv' : ∀ i, C / Cs * Real.sqrt (w i) * vh i = zh i := fun i => congrFun hzv i
  simp only [hzv'] at hnorm
  have ht₀01 : t₀ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  refine ⟨vh, hnorm.1.mpr ((split_iff hκ zh).mpr ⟨t₀, ht₀01, hzmem⟩), fun i => ?_, ?_⟩
  · have : q i * vh i = a i * zh i := by
      simp only [vh, a]; field_simp [(hsq i).ne', hC.ne']
    rw [this]; exact hzsign i
  · intro v hv
    have hnv := support_normalize (q := q) hC hCs hw v
    set z : Fin M → ℝ := fun i => C / Cs * Real.sqrt (w i) * v i
    obtain ⟨τ, hτ, hzτ⟩ := (split_iff hκ z).mp (hnv.1.mp hv)
    -- `⟨q, v⟩ = aᵀz ≤ G₀(τ) ≤ G_ρ(τ) + ρ`
    have h1 : q ⬝ᵥ v ≤ Gval a κ 0 τ := by
      rw [hnv.2]
      have := le_Gval a κ 0 τ hzτ
      simpa [fobj] using this
    have h2 := Gval_zero_le (a := a) hκ hρ.le hτ
    -- clamp `τ` into `[h, 1 − h]`
    set τc := max h (min τ (1 - h))
    have hτc : τc ∈ Icc h (1 - h) := ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
    have hτc01 : τc ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτc.1], by linarith [hτc.2]⟩
    have hdist : |τ - τc| ≤ h := by
      rw [abs_le]; constructor
      · simp only [τc]
        rcases le_total τ (1 - h) with h' | h'
        · rw [min_eq_left h']
          rcases le_total h τ with h'' | h''
          · rw [max_eq_right h'']; linarith
          · rw [max_eq_left h'']; linarith [hτ.1]
        · rw [min_eq_right h', max_eq_right (by linarith)]; linarith
      · simp only [τc]
        rcases le_total τ (1 - h) with h' | h'
        · rw [min_eq_left h']
          rcases le_total h τ with h'' | h''
          · rw [max_eq_right h'']; linarith
          · rw [max_eq_left h'']; linarith
        · rw [min_eq_right h', max_eq_right (by linarith)]; linarith [hτ.2]
    have h3 := Gval_lipschitz (a := a) hκ hρ.le hτ hτc01
    have h4 := hbound τc hτc
    -- `best = f_ρ(ẑ) ≤ aᵀẑ = ⟨q, v̂⟩`
    have h5 : best ≤ q ⬝ᵥ vh := by
      rw [hbest, hzval]
      refine (fobj_le_dot hρ.le zh).trans (le_of_eq ?_)
      rw [hnorm.2]
    have h6 := mul_le_mul_of_nonneg_left hdist hL0
    linarith

end

end ImplicitLP
end CutQueryComplexity
