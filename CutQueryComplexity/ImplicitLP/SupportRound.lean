import CutQueryComplexity.ImplicitLP.SupportAgg
import CutQueryComplexity.ImplicitLP.LewisLev

/-! # Conservative rounding of the support output (`lem:support`, D7)

The proved search (`supportProg`) outputs real scalars `(τ, λ̂, c)` and the vector
`v̂ = unscale(c · z(τ, λ̂))`. Afterwards, offline and with no queries:

* `τ` is rounded **down** to `2^{−k_τ}ℤ`, `λ̂` **up** to `2^{−k_λ}ℤ` and `c` **down** to
  `2^{−k_c}ℤ` (`roundScalars`). Each coordinate of `c' · z(τ', λ')` then has magnitude at most
  that of `c · z(τ, λ̂)` and the same sign (`shrink_scalar`): the box `τκᵢ` shrinks, the
  shrinkage `|aᵢ|/(2(ρ+λ))` grows, and `c' ≤ c`. The objective loss is at most
  `2^{−k_τ}Σ|aᵢ|κᵢ + ‖a‖₂²(2^{−k_c}/(2ρ) + 2^{−k_λ}/(2ρ²))` (`loss_scalar`, from the clip
  Lipschitz bound `abs_clip_sub`).
* Each output coordinate is then truncated toward zero to `2^{−p}ℤ` (`truncDyadic`), and
  `round_down` gives the loss `(Σ|qᵢ|)2^{−p}`.

Both steps keep feasibility (`mixed_mono`) and sign alignment, so trisection's intermediate
points need not be dyadic. The output coordinate `i` is the public formula
`roundCoord … (q i) (w i)`, a function of the per-pair data only (`supportRoundProg_hidden`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Finset Real Set

noncomputable section

/-! ## Dyadic rounding of scalars -/

/-- Rounding up to the dyadic mesh `2^{-k}ℤ`. -/
def dyadicUp (k : ℕ) (x : ℝ) : ℝ := ⌈x * 2 ^ k⌉ / 2 ^ k

theorem dyadicRound_le (k : ℕ) (x : ℝ) : dyadicRound k x ≤ x :=
  (div_le_iff₀ (by positivity)).mpr (Int.floor_le _)

theorem dyadicRound_nonneg (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ dyadicRound k x :=
  div_nonneg (by exact_mod_cast Int.floor_nonneg.mpr (by positivity)) (by positivity)

theorem sub_dyadicRound_le (k : ℕ) (x : ℝ) : |x - dyadicRound k x| ≤ (1 / 2) ^ k := by
  rw [abs_sub_comm]; exact abs_dyadicRound_sub_le k x

theorem le_dyadicUp (k : ℕ) (x : ℝ) : x ≤ dyadicUp k x :=
  (le_div_iff₀ (by positivity)).mpr (Int.le_ceil _)

theorem abs_dyadicUp_sub_le (k : ℕ) (x : ℝ) : |x - dyadicUp k x| ≤ (1 / 2) ^ k := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have h3 := Int.ceil_lt_add_one (x * 2 ^ k)
  have e : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := _root_.one_div_pow 2 k
  have hb : (⌈x * 2 ^ k⌉ : ℝ) / 2 ^ k ≤ x + 1 / 2 ^ k := by
    rw [div_le_iff₀ h2, add_mul, one_div_mul_cancel h2.ne']; linarith
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_dyadicUp k x)), e]
  unfold dyadicUp; linarith

theorem dyadicRound_int (k : ℕ) (x : ℝ) : ∃ m : ℤ, dyadicRound k x = m / 2 ^ k := ⟨_, rfl⟩

theorem dyadicUp_int (k : ℕ) (x : ℝ) : ∃ m : ℤ, dyadicUp k x = m / 2 ^ k := ⟨_, rfl⟩

/-- Truncation toward zero to `2^{-p}ℤ`: `sign(x)⌊|x|2^p⌋/2^p`. -/
def truncDyadic (p : ℕ) (x : ℝ) : ℝ := if 0 ≤ x then dyadicRound p x else -dyadicRound p (-x)

theorem truncDyadic_props (p : ℕ) (x : ℝ) :
    |truncDyadic p x| ≤ |x| ∧ 0 ≤ x * truncDyadic p x ∧ |x - truncDyadic p x| ≤ (1 / 2) ^ p ∧
      ∃ m : ℤ, truncDyadic p x = m / 2 ^ p := by
  unfold truncDyadic
  split_ifs with h
  · have h1 := dyadicRound_le p x
    have h2 := dyadicRound_nonneg p h
    refine ⟨?_, mul_nonneg h h2, sub_dyadicRound_le p x, dyadicRound_int p x⟩
    rw [abs_of_nonneg h, abs_of_nonneg h2]; exact h1
  · have hx : 0 ≤ -x := by linarith [lt_of_not_ge h]
    have h1 := dyadicRound_le p (-x)
    have h2 := dyadicRound_nonneg p hx
    refine ⟨?_, by nlinarith, ?_, ?_⟩
    · rw [abs_neg, abs_of_nonneg h2, abs_of_neg (lt_of_not_ge h)]; exact h1
    · have := sub_dyadicRound_le p (-x)
      rw [show x - -dyadicRound p (-x) = -(-x - dyadicRound p (-x)) by ring, abs_neg]
      exact this
    · obtain ⟨m, hm⟩ := dyadicRound_int p (-x)
      exact ⟨-m, by rw [hm]; push_cast; ring⟩

/-! ## Monotonicity and Lipschitz bounds of the clip formula -/

/-- **The clip magnitude shrinks** when the box shrinks (`B' ≤ B`) and the shrinkage grows
(`μ ≤ μ'`). -/
theorem abs_clip_mono {x B B' μ μ' : ℝ} (hB' : 0 ≤ B') (hBB : B' ≤ B) (hμ : 0 < μ)
    (hμμ : μ ≤ μ') : |clip x B' μ'| ≤ |clip x B μ| := by
  rw [clip_abs (hB'.trans hBB) hμ, clip_abs hB' (hμ.trans_le hμμ)]
  exact min_le_min hBB (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by linarith))

/-- Two clips of the same `x` have the same sign. -/
theorem clip_mul_clip_nonneg {x B B' μ μ' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B') (hμ : 0 < μ)
    (hμ' : 0 < μ') : 0 ≤ clip x B μ * clip x B' μ' := by
  unfold clip
  split_ifs with h
  · exact mul_nonneg (le_min hB (div_nonneg h (by positivity)))
      (le_min hB' (div_nonneg h (by positivity)))
  · have hx : 0 ≤ -x := by linarith [lt_of_not_ge h]
    rw [neg_mul_neg]
    exact mul_nonneg (le_min hB (div_nonneg hx (by positivity)))
      (le_min hB' (div_nonneg hx (by positivity)))

theorem abs_min_sub_min_left (B B' x : ℝ) : |min B x - min B' x| ≤ |B - B'| := by
  rw [min_comm B, min_comm B']; exact abs_min_sub_min x B B'

/-- **The clip formula is Lipschitz** in the box and the shrinkage:
`|clip(x, B, μ) − clip(x, B', μ')| ≤ |B − B'| + |x|/(2ρ²)|μ − μ'|` for `μ, μ' ≥ ρ > 0`. -/
theorem abs_clip_sub {x B B' μ μ' ρ : ℝ} (hρ : 0 < ρ) (hμ : ρ ≤ μ) (hμ' : ρ ≤ μ') :
    |clip x B μ - clip x B' μ'| ≤ |B - B'| + |x| / (2 * ρ ^ 2) * |μ - μ'| := by
  have hμ0 : 0 < μ := hρ.trans_le hμ
  have hμ0' : 0 < μ' := hρ.trans_le hμ'
  have hdiv : |(|x| / (2 * μ)) - |x| / (2 * μ')| ≤ |x| / (2 * ρ ^ 2) * |μ - μ'| := by
    have e : |x| / (2 * μ) - |x| / (2 * μ') = |x| * (μ' - μ) / (2 * (μ * μ')) := by
      field_simp
    rw [e, abs_div, abs_mul, abs_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * (μ * μ')),
      abs_sub_comm μ' μ]
    calc |x| * |μ - μ'| / (2 * (μ * μ')) ≤ |x| * |μ - μ'| / (2 * ρ ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      _ = |x| / (2 * ρ ^ 2) * |μ - μ'| := by ring
  have key : |min B (|x| / (2 * μ)) - min B' (|x| / (2 * μ'))| ≤
      |B - B'| + |x| / (2 * ρ ^ 2) * |μ - μ'| := by
    calc |min B (|x| / (2 * μ)) - min B' (|x| / (2 * μ'))|
        ≤ |min B (|x| / (2 * μ)) - min B (|x| / (2 * μ'))| +
            |min B (|x| / (2 * μ')) - min B' (|x| / (2 * μ'))| := abs_sub_le _ _ _
      _ ≤ |(|x| / (2 * μ)) - |x| / (2 * μ')| + |B - B'| :=
          add_le_add (abs_min_sub_min _ _ _) (abs_min_sub_min_left _ _ _)
      _ ≤ |B - B'| + |x| / (2 * ρ ^ 2) * |μ - μ'| := by linarith
  unfold clip
  split_ifs with h
  · rw [abs_of_nonneg h] at key ⊢; exact key
  · rw [abs_of_neg (lt_of_not_ge h)] at key ⊢
    rw [show -min B (-x / (2 * μ)) - -min B' (-x / (2 * μ')) =
      -(min B (-x / (2 * μ)) - min B' (-x / (2 * μ'))) by ring, abs_neg]
    exact key

/-! ## Rounding the scalars -/

section Scalars

variable {M : ℕ} {a κ : Fin M → ℝ} {ρ : ℝ}

/-- **Conservative scalar rounding shrinks every coordinate, keeping its sign.** With
`0 ≤ τ' ≤ τ`, `0 ≤ λ ≤ λ'` and `0 ≤ c' ≤ c`, each coordinate of `c' z(τ', λ')` has magnitude at
most that of `c z(τ, λ)` and the same sign. -/
theorem shrink_scalar (hκ : ∀ i, 0 ≤ κ i) (hρ : 0 < ρ) {τ τ' lm lm' c c' : ℝ} (hτ' : 0 ≤ τ')
    (hττ : τ' ≤ τ) (hlm : 0 ≤ lm) (hll : lm ≤ lm') (hc' : 0 ≤ c') (hcc : c' ≤ c) (i : Fin M) :
    |(c' • zlam a κ ρ τ' lm') i| ≤ |(c • zlam a κ ρ τ lm) i| ∧
      0 ≤ (c • zlam a κ ρ τ lm) i * (c' • zlam a κ ρ τ' lm') i := by
  simp only [Pi.smul_apply, smul_eq_mul, zlam]
  have hB' : 0 ≤ τ' * κ i := mul_nonneg hτ' (hκ i)
  have hB : 0 ≤ τ * κ i := mul_nonneg (hτ'.trans hττ) (hκ i)
  have hBB : τ' * κ i ≤ τ * κ i := mul_le_mul_of_nonneg_right hττ (hκ i)
  have hm := abs_clip_mono (x := a i) hB' hBB (by linarith : 0 < ρ + lm)
    (by linarith : ρ + lm ≤ ρ + lm')
  have hc : 0 ≤ c := hc'.trans hcc
  refine ⟨?_, ?_⟩
  · rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hc']
    exact mul_le_mul hcc hm (abs_nonneg _) hc
  · have := clip_mul_clip_nonneg (x := a i) hB hB' (by linarith : 0 < ρ + lm)
      (by linarith : 0 < ρ + lm')
    have e : c * clip (a i) (τ * κ i) (ρ + lm) * (c' * clip (a i) (τ' * κ i) (ρ + lm')) =
        (c * c') * (clip (a i) (τ * κ i) (ρ + lm) * clip (a i) (τ' * κ i) (ρ + lm')) := by ring
    rw [e]; exact mul_nonneg (mul_nonneg hc hc') this

/-- The coordinatewise rounding error of the scalar rounding. -/
theorem coord_scalar_err (hκ : ∀ i, 0 ≤ κ i) (hρ : 0 < ρ) {τ τ' lm lm' c c' μτ μl μc : ℝ}
    (hτ' : 0 ≤ τ') (hττ : τ' ≤ τ) (hlm : 0 ≤ lm) (hll : lm ≤ lm') (hc' : 0 ≤ c') (hc1 : c ≤ 1)
    (hcc : c' ≤ c) (hdτ : |τ - τ'| ≤ μτ) (hdl : |lm - lm'| ≤ μl) (hdc : |c - c'| ≤ μc)
    (i : Fin M) :
    |(c • zlam a κ ρ τ lm) i - (c' • zlam a κ ρ τ' lm') i| ≤
      μc * (|a i| / (2 * ρ)) + (μτ * κ i + |a i| / (2 * ρ ^ 2) * μl) := by
  simp only [Pi.smul_apply, smul_eq_mul, zlam]
  set cl := clip (a i) (τ * κ i) (ρ + lm)
  set cl' := clip (a i) (τ' * κ i) (ρ + lm')
  have hcl : |cl| ≤ |a i| / (2 * ρ) :=
    abs_clip_le (mul_nonneg (hτ'.trans hττ) (hκ i)) hρ hlm
  have hsub := abs_clip_sub (x := a i) (B := τ * κ i) (B' := τ' * κ i) hρ
    (by linarith : ρ ≤ ρ + lm) (by linarith : ρ ≤ ρ + lm')
  have hsub' : |cl - cl'| ≤ μτ * κ i + |a i| / (2 * ρ ^ 2) * μl := by
    have e1 : |τ * κ i - τ' * κ i| = |τ - τ'| * κ i := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (hκ i)]
    have e2 : ρ + lm - (ρ + lm') = lm - lm' := by ring
    rw [e1, e2] at hsub
    have h1 : |τ - τ'| * κ i ≤ μτ * κ i := mul_le_mul_of_nonneg_right hdτ (hκ i)
    have h2 : |a i| / (2 * ρ ^ 2) * |lm - lm'| ≤ |a i| / (2 * ρ ^ 2) * μl :=
      mul_le_mul_of_nonneg_left hdl (by positivity)
    linarith
  have hμc0 : 0 ≤ μc := (abs_nonneg _).trans hdc
  have e : c * cl - c' * cl' = (c - c') * cl + c' * (cl - cl') := by ring
  rw [e]
  calc |(c - c') * cl + c' * (cl - cl')| ≤ |(c - c') * cl| + |c' * (cl - cl')| := abs_add_le _ _
    _ = |c - c'| * |cl| + c' * |cl - cl'| := by rw [abs_mul, abs_mul, abs_of_nonneg hc']
    _ ≤ μc * (|a i| / (2 * ρ)) + 1 * (μτ * κ i + |a i| / (2 * ρ ^ 2) * μl) :=
        add_le_add (mul_le_mul hdc hcl (abs_nonneg _) hμc0)
          (mul_le_mul (hcc.trans hc1) hsub' (abs_nonneg _) zero_le_one)
    _ = _ := by ring

/-- **The objective loss of the scalar rounding:**
`aᵀ(c z(τ, λ)) − aᵀ(c' z(τ', λ')) ≤ μ_τ Σ|aᵢ|κᵢ + ‖a‖₂²(μ_c/(2ρ) + μ_λ/(2ρ²))`. -/
theorem loss_scalar (hκ : ∀ i, 0 ≤ κ i) (hρ : 0 < ρ) {τ τ' lm lm' c c' μτ μl μc : ℝ}
    (hτ' : 0 ≤ τ') (hττ : τ' ≤ τ) (hlm : 0 ≤ lm) (hll : lm ≤ lm') (hc' : 0 ≤ c') (hc1 : c ≤ 1)
    (hcc : c' ≤ c) (hdτ : |τ - τ'| ≤ μτ) (hdl : |lm - lm'| ≤ μl) (hdc : |c - c'| ≤ μc) :
    a ⬝ᵥ (c • zlam a κ ρ τ lm) - a ⬝ᵥ (c' • zlam a κ ρ τ' lm') ≤
      μτ * ∑ i, |a i| * κ i + euc a ^ 2 * (μc / (2 * ρ) + μl / (2 * ρ ^ 2)) := by
  rw [← dotProduct_sub, euc_sq, mul_sum, sum_mul, ← sum_add_distrib]
  refine (le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_))
  rw [abs_mul]
  have h := coord_scalar_err (a := a) hκ hρ hτ' hττ hlm hll hc' hc1 hcc hdτ hdl hdc i
  have h' := mul_le_mul_of_nonneg_left h (abs_nonneg (a i))
  have e : |a i| * (μc * (|a i| / (2 * ρ)) + (μτ * κ i + |a i| / (2 * ρ ^ 2) * μl)) =
      μτ * (|a i| * κ i) + a i ^ 2 * (μc / (2 * ρ) + μl / (2 * ρ ^ 2)) := by
    rw [← sq_abs (a i)]; field_simp; ring
  simp only [Pi.sub_apply]
  linarith

end Scalars

/-! ## The rounded output -/

section Output

variable {M : ℕ}

/-- The rounded scalars `(⌊τ⌋_{k_τ}, ⌈λ̂⌉_{k_λ}, ⌊c⌋_{k_c})` from the program's output
`(τ, (λ̂, c, ℓ, u))`. -/
def roundScalars (kτ kl kc : ℕ) (o : ℝ × (ℝ × ℝ × ℝ × ℝ)) : ℝ × ℝ × ℝ :=
  (dyadicRound kτ o.1, dyadicUp kl o.2.1, dyadicRound kc o.2.2.1)

/-- **The public per-coordinate output formula**: coordinate `i` is
`trunc_p(unscale(c · clip(aᵢ, τκᵢ, ρ + λ)))`, a function of `(qᵢ, wᵢ)` and the public scalars. -/
def roundCoord (C Cs ρ : ℝ) (p : ℕ) (τ lm c qi wi : ℝ) : ℝ :=
  truncDyadic p (Cs * (c * clip (Cs * qi / (C * Real.sqrt wi)) (τ * (C * Real.sqrt wi)) (ρ + lm)) /
    (C * Real.sqrt wi))

/-- Sign alignment passes to a coordinatewise shrinking with the same signs. -/
theorem aligned_of_shrink {q x x' : ℝ} (hqx : 0 ≤ q * x) (hab : |x'| ≤ |x|) (hs : 0 ≤ x * x') :
    0 ≤ q * x' := by
  rcases eq_or_ne x 0 with h | h
  · have : x' = 0 := by
      rw [h, abs_zero] at hab; exact abs_eq_zero.mp (le_antisymm hab (abs_nonneg _))
    rw [this, mul_zero]
  · have hx2 : 0 < x ^ 2 := by positivity
    have : 0 ≤ x ^ 2 * (q * x') := by
      have e : x ^ 2 * (q * x') = (q * x) * (x * x') := by ring
      rw [e]; exact mul_nonneg hqx hs
    exact (mul_nonneg_iff_of_pos_left hx2).mp this

/-- **Rounding the support output conservatively.** Let `v̂ = unscale(c z(τ, λ))` with
`τ, λ ≥ 0`, `c ∈ [0, 1]`, lie in the ball and be sign-aligned with `q`. Round `τ` down, `λ` up,
`c` down, and truncate each coordinate toward zero to `2^{−p}ℤ`. The result `v` is dyadic, lies
in the ball, is sign-aligned, and `⟨q, v̂⟩ − loss ≤ ⟨q, v⟩` with
`loss = 2^{−k_τ}Σ|aᵢ|κᵢ + ‖a‖₂²(2^{−k_c}/(2ρ) + 2^{−k_λ}/(2ρ²)) + (Σ|qᵢ|)2^{−p}`. -/
theorem round_support {C Cs : ℝ} {w q : Fin M → ℝ} (hC : 0 < C) (hw : ∀ i, 0 < w i) {ρ : ℝ}
    (hρ : 0 < ρ) {τ lm c : ℝ} (hτ : 0 ≤ τ) (hlm : 0 ≤ lm) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (kτ kl kc p : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let vh : Fin M → ℝ := fun i => Cs * (c • zlam a κ ρ τ lm) i / (C * Real.sqrt (w i))
    let s := roundScalars kτ kl kc (τ, (lm, c, 0, 0))
    let v : Fin M → ℝ := fun i => roundCoord C Cs ρ p s.1 s.2.1 s.2.2 (q i) (w i)
    mixed C w vh ≤ Cs → (∀ i, 0 ≤ q i * vh i) →
    (∀ i, ∃ m : ℤ, v i = m / 2 ^ p) ∧ mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ q i * v i) ∧
      q ⬝ᵥ vh - ((1 / 2) ^ kτ * ∑ i, |a i| * κ i +
          euc a ^ 2 * ((1 / 2) ^ kc / (2 * ρ) + (1 / 2) ^ kl / (2 * ρ ^ 2)) +
          (∑ i, |q i|) * (1 / 2) ^ p) ≤ q ⬝ᵥ v := by
  intro κ a vh s v hvh hal
  have hκ : ∀ i, 0 ≤ κ i := fun i => mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hd : ∀ i, 0 < C * Real.sqrt (w i) := fun i => mul_pos hC (Real.sqrt_pos.mpr (hw i))
  set τ' := dyadicRound kτ τ
  set lm' := dyadicUp kl lm
  set c' := dyadicRound kc c
  have hτ' : 0 ≤ τ' := dyadicRound_nonneg kτ hτ
  have hττ : τ' ≤ τ := dyadicRound_le kτ τ
  have hll : lm ≤ lm' := le_dyadicUp kl lm
  have hc' : 0 ≤ c' := dyadicRound_nonneg kc hc0
  have hcc : c' ≤ c := dyadicRound_le kc c
  -- the intermediate (scalar-rounded) vector
  set vs : Fin M → ℝ := fun i => Cs * (c' • zlam a κ ρ τ' lm') i / (C * Real.sqrt (w i))
  have hv : ∀ i, v i = truncDyadic p (vs i) := fun i => rfl
  have hsh : ∀ i, |vs i| ≤ |vh i| ∧ 0 ≤ vh i * vs i := by
    intro i
    obtain ⟨h1, h2⟩ := shrink_scalar (a := a) hκ hρ hτ' hττ hlm hll hc' hcc i
    simp only [vs, vh]
    set d := C * Real.sqrt (w i)
    constructor
    · rw [abs_div, abs_div]
      refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    · have e : Cs * (c • zlam a κ ρ τ lm) i / d * (Cs * (c' • zlam a κ ρ τ' lm') i / d) =
          (Cs / d) ^ 2 * ((c • zlam a κ ρ τ lm) i * (c' • zlam a κ ρ τ' lm') i) := by ring
      rw [e]; exact mul_nonneg (sq_nonneg _) h2
  have hvs_ball : mixed C w vs ≤ Cs :=
    (mixed_mono hC.le (fun i => (hw i).le) fun i => (hsh i).1).trans hvh
  have hvs_al : ∀ i, 0 ≤ q i * vs i := fun i => aligned_of_shrink (hal i) (hsh i).1 (hsh i).2
  -- the dyadic truncation
  obtain ⟨hball, hal', hloss⟩ := round_down (δ := (1 / 2) ^ p) hC.le (fun i => (hw i).le)
    hvs_ball (v' := v) (fun i => by rw [hv]; exact (truncDyadic_props p (vs i)).1)
    (fun i => by rw [hv]; exact (truncDyadic_props p (vs i)).2.1)
    (fun i => by rw [hv]; exact (truncDyadic_props p (vs i)).2.2.1) hvs_al
  refine ⟨fun i => by rw [hv]; exact (truncDyadic_props p (vs i)).2.2.2, hball, hal', ?_⟩
  -- the scalar loss, in normalized coordinates
  have hdot : ∀ z : Fin M → ℝ,
      q ⬝ᵥ (fun i => Cs * z i / (C * Real.sqrt (w i))) = a ⬝ᵥ z := fun z => by
    simp only [dotProduct, a]
    exact sum_congr rfl fun i _ => by ring
  have hls := loss_scalar (a := a) hκ hρ hτ' hττ hlm hll hc' hc1 hcc
    (sub_dyadicRound_le kτ τ) (abs_dyadicUp_sub_le kl lm) (sub_dyadicRound_le kc c)
  have e1 : q ⬝ᵥ vh = a ⬝ᵥ (c • zlam a κ ρ τ lm) := hdot _
  have e2 : q ⬝ᵥ vs = a ⬝ᵥ (c' • zlam a κ ρ τ' lm') := hdot _
  rw [e1]; rw [e2] at hloss
  linarith

end Output

/-! ## In the program -/

section Program

variable {I A : Type} {Q : ℕ}

theorem supportProg_eval (EV : ℝ → DTree I A (ℝ × ℝ × ℝ × ℝ) Q) (h : ℝ) (N : ℕ)
    (read : I → A) :
    (supportProg EV h N).eval read = (((trisectProg EV h (1 - h) N).eval read).2,
      (EV ((trisectProg EV h (1 - h) N).eval read).2).eval read) := by
  simp only [supportProg, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]

/-- **The rounded support program**: `supportProg`, then (offline, no queries) the conservative
scalar rounding and the per-coordinate dyadic truncation. It outputs the rounded scalars and the
vector `i ↦ roundCoord … (q i) (w i)`. -/
def supportRoundProg {M : ℕ} (EV : ℝ → DTree I A (ℝ × ℝ × ℝ × ℝ) Q) (h : ℝ) (N : ℕ)
    (C Cs ρ : ℝ) (kτ kl kc p : ℕ) (q w : Fin M → ℝ) :
    DTree I A ((ℝ × ℝ × ℝ) × (Fin M → ℝ)) ((2 * N + 2) * Q) :=
  (supportProg EV h N).map fun out =>
    let s := roundScalars kτ kl kc out
    (s, fun i => roundCoord C Cs ρ p s.1 s.2.1 s.2.2 (q i) (w i))

end Program

theorem ibisect_nonneg {Nt : ℝ → ℝ} {r2 Λ : ℝ} (hΛ : 0 ≤ Λ) (k : ℕ) :
    0 ≤ (ibisect Nt r2 Λ k).1 ∧ 0 ≤ (ibisect Nt r2 Λ k).2 := by
  induction k with
  | zero => exact ⟨le_rfl, hΛ⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [ibisect]
      split_ifs
      · exact ⟨h1, by positivity⟩
      · exact ⟨by positivity, h2⟩

theorem ilam_nonneg {Nt : ℝ → ℝ} {r2 Λ : ℝ} (hΛ : 0 ≤ Λ) (k : ℕ) : 0 ≤ ilam Nt r2 Λ k := by
  unfold ilam; split_ifs
  · exact le_rfl
  · exact (ibisect_nonneg hΛ k).2

section HiddenProgram

variable {M n : ℕ}

/-- **The rounded support oracle as an outgoing-cut query program.** Under the hypotheses of
`supportProg_hidden`, the rounded program outputs dyadic scalars `(τ', λ', c')` (`τ' ≥ 0`,
`λ' ≥ 0`, `c' ∈ [0, 1]`) and a vector `v` whose coordinates lie in `2^{−p}ℤ`. The vector lies in
the ball, is sign-aligned with `q`, loses at most
`R = 2^{−k_τ}L + ‖a‖₂²(2^{−k_c}/(2ρ) + 2^{−k_λ}/(2ρ²)) + (Σ|qᵢ|)2^{−p}` against the unrounded
output `v̂`, and so satisfies `⟨q, v₀⟩ ≤ ⟨q, v⟩ + ρ + Lh + 3ε + L(1 − 2h)(2/3)ᴺ + R` for every `v₀`
in the ball. Coordinate `i` is the public formula `roundCoord … (q i) (w i)`, so on hidden copies
of a pair `e` it is `roundCoord … (qb e) (wb e)`. The query cap is unchanged. -/
theorem supportRoundProg_hidden (G : DiGraph (Fin n)) (hid : Fin M → Option (Sym2 (Fin n)))
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {C Cs : ℝ} {w q : Fin M → ℝ} {wb qb : Sym2 (Fin n) → ℝ}
    (hwb : ∀ i e, hid i = some e → w i = wb e) (hqb : ∀ i e, hid i = some e → q i = qb e)
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < w i) {ρ h Ap Abar Φ : ℝ} (hρ : 0 < ρ)
    (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * q i / (C * Real.sqrt (w i))) ≤ Ap)
    (hAbar : ∀ e, |Cs * qb e / (C * Real.sqrt (wb e))| ≤ Abar)
    (hΦ1 : Abar ^ 2 / (4 * ρ ^ 2) ≤ Φ) (hΦ2 : Abar ^ 2 / (2 * ρ) ≤ Φ)
    {p B : ℕ} (hB : Φ * 2 ^ p + 1 ≤ 2 ^ B) (hp : (M : ℝ) / 2 ^ p ≤ 3 * h ^ 2 / 4) (N m : ℕ)
    (kτ kl kc po : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let ab : Sym2 (Fin n) → ℝ := fun e => Cs * qb e / (C * Real.sqrt (wb e))
    let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (wb e)
    let δ : ℝ := M / 2 ^ p
    let NP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), zlam a κ ρ τ lm i ^ 2)
        (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B
    let PP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), a i * zlam a κ ρ τ lm i)
        (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B
    let Λ := Ap / h
    let ε := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ m) + (3 * Λ + 4 * ρ + euc a / (2 * h)) * δ + 4 * δ
    let EV := fun τ => ievalProg (NP τ) (PP τ) δ δ ρ (1 - τ) Λ m
    let out := (supportProg EV h N).eval G.out
    let vh : Fin M → ℝ := fun i =>
      Cs * (out.2.2.1 • zlam a κ ρ out.1 out.2.1) i / (C * Real.sqrt (w i))
    let R := (1 / 2) ^ kτ * L + euc a ^ 2 * ((1 / 2) ^ kc / (2 * ρ) + (1 / 2) ^ kl / (2 * ρ ^ 2)) +
      (∑ i, |q i|) * (1 / 2) ^ po
    let res := (supportRoundProg EV h N C Cs ρ kτ kl kc po q w).eval G.out
    let v := res.2
    res.1 = roundScalars kτ kl kc out ∧
      (∃ m₁ : ℤ, res.1.1 = m₁ / 2 ^ kτ) ∧ (∃ m₂ : ℤ, res.1.2.1 = m₂ / 2 ^ kl) ∧
      (∃ m₃ : ℤ, res.1.2.2 = m₃ / 2 ^ kc) ∧
      0 ≤ res.1.1 ∧ 0 ≤ res.1.2.1 ∧ 0 ≤ res.1.2.2 ∧ res.1.2.2 ≤ 1 ∧
      (∀ i, v i = roundCoord C Cs ρ po res.1.1 res.1.2.1 res.1.2.2 (q i) (w i)) ∧
      (∀ i e, hid i = some e →
        v i = roundCoord C Cs ρ po res.1.1 res.1.2.1 res.1.2.2 (qb e) (wb e)) ∧
      (∀ i, ∃ m : ℤ, v i = m / 2 ^ po) ∧
      mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ q i * v i) ∧
      q ⬝ᵥ vh - R ≤ q ⬝ᵥ v ∧
      (∀ v₀, mixed C w v₀ ≤ Cs →
        q ⬝ᵥ v₀ ≤ q ⬝ᵥ v + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N) + R)) ∧
      (supportRoundProg EV h N C Cs ρ kτ kl kc po q w).cost G.out ≤
        (2 * N + 2) * ((m + 3) * (6 * B * n)) := by
  intro κ a L ab κb δ NP PP Λ ε EV out vh R res v
  obtain ⟨hτ, hball, hal, hsupp, -⟩ :=
    supportProg_hidden G hid hcount hwb hqb hC hCs hw hρ hh0 hh hAp hAbar hΦ1 hΦ2 hB hp N m
  replace hτ : out.1 ∈ Icc h (1 - h) := hτ
  have hres : res = (roundScalars kτ kl kc out,
      fun i => roundCoord C Cs ρ po (roundScalars kτ kl kc out).1
        (roundScalars kτ kl kc out).2.1 (roundScalars kτ kl kc out).2.2 (q i) (w i)) := by
    simp only [res, supportRoundProg, DTree.eval_map]; rfl
  -- the scalars of the unrounded output
  have hΛ0 : 0 ≤ Λ := div_nonneg ((euc_nonneg a).trans hAp) hh0.le
  have hout2 : out.2 = ieval (fun lm => (NP out.1 lm).eval G.out)
      (fun lm => (PP out.1 lm).eval G.out) δ δ ρ (1 - out.1) Λ m := by
    have e := supportProg_eval EV h N G.out
    have e1 : out.2 = (EV out.1).eval G.out := by simp only [out, e]
    rw [e1]; exact ievalProg_eval _ _ _ _ _ _ _ _ _
  have hlm0 : 0 ≤ out.2.1 := by rw [hout2]; simp only [ieval]; exact ilam_nonneg hΛ0 m
  have hc : 0 ≤ out.2.2.1 ∧ out.2.2.1 ≤ 1 := by
    rw [hout2]; exact iscale_mem (by linarith [hτ.2])
  have hτ0 : 0 ≤ out.1 := by linarith [hτ.1]
  obtain ⟨hdy, hball', hal', hloss⟩ :=
    round_support (Cs := Cs) (q := q) hC hw hρ hτ0 hlm0 hc.1 hc.2 kτ kl kc po hball hal
  have hsL : ∑ i, |a i| * κ i ≤ L := le_max_right _ _
  have hR : (1 / 2) ^ kτ * ∑ i, |a i| * κ i +
      euc a ^ 2 * ((1 / 2) ^ kc / (2 * ρ) + (1 / 2) ^ kl / (2 * ρ ^ 2)) +
      (∑ i, |q i|) * (1 / 2) ^ po ≤ R :=
    by have := mul_le_mul_of_nonneg_left hsL (by positivity : (0 : ℝ) ≤ (1 / 2) ^ kτ)
       simp only [R]; linarith
  have hv : v = fun i => roundCoord C Cs ρ po (roundScalars kτ kl kc out).1
      (roundScalars kτ kl kc out).2.1 (roundScalars kτ kl kc out).2.2 (q i) (w i) := by
    simp only [v, hres]
  have hres1 : res.1 = roundScalars kτ kl kc out := by rw [hres]
  have hcopy : ∀ i e, hid i = some e →
      roundCoord C Cs ρ po (roundScalars kτ kl kc out).1 (roundScalars kτ kl kc out).2.1
        (roundScalars kτ kl kc out).2.2 (q i) (w i) =
      roundCoord C Cs ρ po (roundScalars kτ kl kc out).1 (roundScalars kτ kl kc out).2.1
        (roundScalars kτ kl kc out).2.2 (qb e) (wb e) := fun i e he => by
    rw [hqb i e he, hwb i e he]
  set vr : Fin M → ℝ := fun i => roundCoord C Cs ρ po (roundScalars kτ kl kc out).1
      (roundScalars kτ kl kc out).2.1 (roundScalars kτ kl kc out).2.2 (q i) (w i) with hvr
  have hloss' : q ⬝ᵥ vh - ((1 / 2) ^ kτ * ∑ i, |a i| * κ i +
      euc a ^ 2 * ((1 / 2) ^ kc / (2 * ρ) + (1 / 2) ^ kl / (2 * ρ ^ 2)) +
      (∑ i, |q i|) * (1 / 2) ^ po) ≤ q ⬝ᵥ vr := hloss
  have hsupp' : ∀ v₀, mixed C w v₀ ≤ Cs →
      q ⬝ᵥ v₀ ≤ q ⬝ᵥ vh + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N)) := hsupp
  rw [hv, hres1]
  refine ⟨rfl, dyadicRound_int _ _, dyadicUp_int _ _, dyadicRound_int _ _,
    dyadicRound_nonneg _ hτ0, hlm0.trans (le_dyadicUp _ _), dyadicRound_nonneg _ hc.1,
    (dyadicRound_le _ _).trans hc.2, fun i => rfl, hcopy, hdy, hball', hal', by linarith,
    fun v₀ hv₀ => by have := hsupp' v₀ hv₀; linarith, ?_⟩
  exact DTree.cost_le _ _

end HiddenProgram

end

end ImplicitLP
end CutQueryComplexity
