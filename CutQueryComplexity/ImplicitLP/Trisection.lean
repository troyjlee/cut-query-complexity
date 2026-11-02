import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Set.Basic

/-! # Trisection with certified intervals and an incumbent (`lem:support`, D7)

Let `G` be concave and `L`-Lipschitz on `[α, β]`, and let an oracle return certified intervals
`ℓ(t) ≤ G(t) ≤ u(t) ≤ ℓ(t) + ζ`. Each step queries the two trisection points `m₁ < m₂` and
updates the incumbent `best = max(best, ℓ(m₁), ℓ(m₂))`:
* if `u(m₁) < ℓ(m₂)`, discard `[lo, m₁)`;
* if `u(m₂) < ℓ(m₁)`, discard `(m₂, hi]`;
* otherwise keep the middle third `[m₁, m₂]`.

Concavity bounds every discarded point by `best + 3ζ` (`concave_extrap`): when the intervals
overlap, `G(m₁) − G(m₂) ≤ 2ζ`. Since `best` only increases, these losses do not accumulate. After
`n` steps (`trisect_bound`), every `t ∈ [α, β]` satisfies `G(t) ≤ best + 3ζ + L(β − α)(2/3)ⁿ`,
and `best = ℓ(t₀)` for some queried `t₀` (a certified lower value of a witness).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Set

noncomputable section

variable {G ℓ u : ℝ → ℝ} {α β ζ L : ℝ}

/-- **Concave extrapolation:** for `s < m₁ < m₂` with `m₁ − s ≤ m₂ − m₁`,
`G(s) ≤ G(m₁) + max(0, G(m₁) − G(m₂))`. -/
theorem concave_extrap
    (hcc : ∀ s ∈ Icc α β, ∀ t ∈ Icc α β, ∀ θ ∈ Icc (0 : ℝ) 1,
      θ * G s + (1 - θ) * G t ≤ G (θ * s + (1 - θ) * t))
    {s m₁ m₂ : ℝ} (hs : s ∈ Icc α β) (hm₂ : m₂ ∈ Icc α β) (h1 : s < m₁) (h2 : m₁ < m₂)
    (hgap : m₁ - s ≤ m₂ - m₁) : G s ≤ G m₁ + max 0 (G m₁ - G m₂) := by
  set θ := (m₂ - m₁) / (m₂ - s)
  have hd : 0 < m₂ - s := by linarith
  have hθ0 : 0 < θ := div_pos (by linarith) hd
  have hθ1 : θ ≤ 1 := by rw [div_le_one hd]; linarith
  have hm : θ * s + (1 - θ) * m₂ = m₁ := by simp only [θ]; field_simp; ring
  have hcon := hcc s hs m₂ hm₂ θ ⟨hθ0.le, hθ1⟩
  rw [hm] at hcon
  -- `G s ≤ G m₁ + ((1−θ)/θ)(G m₁ − G m₂)` with `(1−θ)/θ ≤ 1`
  have hratio : (1 - θ) / θ ≤ 1 := by
    rw [div_le_one hθ0]
    have : 1 - θ = (m₁ - s) / (m₂ - s) := by simp only [θ]; field_simp; ring
    rw [this]; exact div_le_div_of_nonneg_right hgap hd.le
  have hr0 : 0 ≤ (1 - θ) / θ := div_nonneg (by linarith) hθ0.le
  have key : G s ≤ G m₁ + (1 - θ) / θ * (G m₁ - G m₂) := by
    rw [div_mul_eq_mul_div, ← sub_le_iff_le_add', le_div_iff₀ hθ0]
    nlinarith
  calc G s ≤ G m₁ + (1 - θ) / θ * (G m₁ - G m₂) := key
    _ ≤ G m₁ + (1 - θ) / θ * max 0 (G m₁ - G m₂) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_max_right _ _) hr0)
    _ ≤ G m₁ + 1 * max 0 (G m₁ - G m₂) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hratio (le_max_left _ _))
    _ = G m₁ + max 0 (G m₁ - G m₂) := by ring

/-- The mirror image: for `m₁ < m₂ < s` with `s − m₂ ≤ m₂ − m₁`. -/
theorem concave_extrap'
    (hcc : ∀ s ∈ Icc α β, ∀ t ∈ Icc α β, ∀ θ ∈ Icc (0 : ℝ) 1,
      θ * G s + (1 - θ) * G t ≤ G (θ * s + (1 - θ) * t))
    {s m₁ m₂ : ℝ} (hs : s ∈ Icc α β) (hm₁ : m₁ ∈ Icc α β) (h1 : m₁ < m₂) (h2 : m₂ < s)
    (hgap : s - m₂ ≤ m₂ - m₁) : G s ≤ G m₂ + max 0 (G m₂ - G m₁) := by
  -- reflect `t ↦ −t`
  have hcc' : ∀ s ∈ Icc (-β) (-α), ∀ t ∈ Icc (-β) (-α), ∀ θ ∈ Icc (0 : ℝ) 1,
      θ * G (-s) + (1 - θ) * G (-t) ≤ G (-(θ * s + (1 - θ) * t)) := by
    intro s hs t ht θ hθ
    have := hcc (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ (-t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩ θ hθ
    rw [show -(θ * s + (1 - θ) * t) = θ * -s + (1 - θ) * -t by ring]; exact this
  have := concave_extrap (G := fun t => G (-t)) (α := -β) (β := -α) hcc'
    (s := -s) (m₁ := -m₂) (m₂ := -m₁) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    ⟨by linarith [hm₁.2], by linarith [hm₁.1]⟩ (by linarith) (by linarith) (by linarith)
  simpa using this

/-- The trisection state: interval `[lo, hi]`, incumbent `best`, a queried point `q ∈ [lo, hi]`. -/
structure TState where
  lo : ℝ
  hi : ℝ
  best : ℝ
  q : ℝ

/-- One trisection step. -/
def tstep (ℓ u : ℝ → ℝ) (s : TState) : TState :=
  let m₁ := s.lo + (s.hi - s.lo) / 3
  let m₂ := s.hi - (s.hi - s.lo) / 3
  let b := max s.best (max (ℓ m₁) (ℓ m₂))
  if u m₁ < ℓ m₂ then ⟨m₁, s.hi, b, m₂⟩
  else if u m₂ < ℓ m₁ then ⟨s.lo, m₂, b, m₁⟩
  else ⟨m₁, m₂, b, m₁⟩

/-- `n` trisection steps from `[α, β]`. -/
def trisect (ℓ u : ℝ → ℝ) (α β : ℝ) : ℕ → TState
  | 0 => ⟨α, β, ℓ α, α⟩
  | n + 1 => tstep ℓ u (trisect ℓ u α β n)

/-- The trisection invariant at a state. -/
def TInv (G ℓ : ℝ → ℝ) (α β ζ w : ℝ) (s : TState) : Prop :=
  α ≤ s.lo ∧ s.lo ≤ s.q ∧ s.q ≤ s.hi ∧ s.hi ≤ β ∧ s.hi - s.lo ≤ w ∧ ℓ s.q ≤ s.best ∧
    (∃ t₀ ∈ Icc α β, s.best = ℓ t₀) ∧
    ∀ t ∈ Icc α β, (t < s.lo ∨ s.hi < t) → G t ≤ s.best + 3 * ζ

/-- One step preserves the invariant, with width multiplied by `2/3`. -/
theorem tstep_inv (hζ : 0 ≤ ζ)
    (hcc : ∀ s ∈ Icc α β, ∀ t ∈ Icc α β, ∀ θ ∈ Icc (0 : ℝ) 1,
      θ * G s + (1 - θ) * G t ≤ G (θ * s + (1 - θ) * t))
    (horacle : ∀ t ∈ Icc α β, ℓ t ≤ G t ∧ G t ≤ u t ∧ u t ≤ ℓ t + ζ) {w : ℝ} {s : TState}
    (hs : TInv G ℓ α β ζ w s) : TInv G ℓ α β ζ (2 / 3 * w) (tstep ℓ u s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, ⟨t₀, ht₀, hb⟩, h8⟩ := hs
  unfold tstep
  dsimp only
  set m₁ := s.lo + (s.hi - s.lo) / 3 with hm₁
  set m₂ := s.hi - (s.hi - s.lo) / 3 with hm₂
  set b := max s.best (max (ℓ m₁) (ℓ m₂)) with hbdef
  have hw : 0 ≤ s.hi - s.lo := by linarith
  have hm1 : m₁ ∈ Icc α β := ⟨by linarith, by linarith⟩
  have hm2 : m₂ ∈ Icc α β := ⟨by linarith, by linarith⟩
  have hb1 : ℓ m₁ ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hb2 : ℓ m₂ ≤ b := (le_max_right _ _).trans (le_max_right _ _)
  have hbs : s.best ≤ b := le_max_left _ _
  have hbw : ∃ t₀ ∈ Icc α β, b = ℓ t₀ := by
    rcases le_total s.best (max (ℓ m₁) (ℓ m₂)) with h | h
    · rw [hbdef, max_eq_right h]
      rcases le_total (ℓ m₁) (ℓ m₂) with h' | h'
      · exact ⟨m₂, hm2, max_eq_right h'⟩
      · exact ⟨m₁, hm1, max_eq_left h'⟩
    · exact ⟨t₀, ht₀, by rw [hbdef, max_eq_left h]; exact hb⟩
  have hold : ∀ t ∈ Icc α β, (t < s.lo ∨ s.hi < t) → G t ≤ b + 3 * ζ := fun t ht h =>
    (h8 t ht h).trans (by linarith)
  obtain ⟨hl1, hg1, hu1⟩ := horacle m₁ hm1
  obtain ⟨hl2, hg2, hu2⟩ := horacle m₂ hm2
  -- the left discarded region `[lo, m₁)`
  have left : ∀ t ∈ Icc α β, s.lo ≤ t → t < m₁ → G m₁ - G m₂ ≤ 2 * ζ → G t ≤ b + 3 * ζ := by
    intro t ht hlo h hd12
    have hlt : m₁ < m₂ := by linarith
    have := concave_extrap hcc ht hm2 h hlt (by linarith)
    have hmax : max 0 (G m₁ - G m₂) ≤ 2 * ζ := max_le (by linarith) hd12
    linarith
  have right : ∀ t ∈ Icc α β, t ≤ s.hi → m₂ < t → G m₂ - G m₁ ≤ 2 * ζ → G t ≤ b + 3 * ζ := by
    intro t ht hhi h hd21
    have hlt : m₁ < m₂ := by linarith
    have := concave_extrap' hcc ht hm1 hlt h (by linarith)
    have hmax : max 0 (G m₂ - G m₁) ≤ 2 * ζ := max_le (by linarith) hd21
    linarith
  split_ifs with hA hB
  · refine ⟨by linarith, by linarith, by linarith, h4, by linarith, hb2, hbw,
      fun t ht h => ?_⟩
    rcases h with h | h
    · by_cases hlo : t < s.lo
      · exact hold t ht (Or.inl hlo)
      · exact left t ht (not_lt.mp hlo) h (by linarith)
    · exact hold t ht (Or.inr h)
  · refine ⟨h1, by linarith, by linarith, by linarith, by linarith, hb1, hbw,
      fun t ht h => ?_⟩
    rcases h with h | h
    · exact hold t ht (Or.inl h)
    · by_cases hhi : s.hi < t
      · exact hold t ht (Or.inr hhi)
      · exact right t ht (not_lt.mp hhi) h (by linarith)
  · push Not at hA hB
    refine ⟨by linarith, le_rfl, by linarith, by linarith, by linarith, hb1, hbw,
      fun t ht h => ?_⟩
    rcases h with h | h
    · by_cases hlo : t < s.lo
      · exact hold t ht (Or.inl hlo)
      · exact left t ht (not_lt.mp hlo) h (by linarith)
    · by_cases hhi : s.hi < t
      · exact hold t ht (Or.inr hhi)
      · exact right t ht (not_lt.mp hhi) h (by linarith)

/-- **Trisection with an incumbent.** -/
theorem trisect_bound (hαβ : α ≤ β) (hζ : 0 ≤ ζ)
    (hcc : ∀ s ∈ Icc α β, ∀ t ∈ Icc α β, ∀ θ ∈ Icc (0 : ℝ) 1,
      θ * G s + (1 - θ) * G t ≤ G (θ * s + (1 - θ) * t))
    (hlip : ∀ s ∈ Icc α β, ∀ t ∈ Icc α β, G s ≤ G t + L * |s - t|)
    (horacle : ∀ t ∈ Icc α β, ℓ t ≤ G t ∧ G t ≤ u t ∧ u t ≤ ℓ t + ζ) (hL : 0 ≤ L) (n : ℕ) :
    (∃ t₀ ∈ Icc α β, (trisect ℓ u α β n).best = ℓ t₀) ∧
      ∀ t ∈ Icc α β, G t ≤ (trisect ℓ u α β n).best + 3 * ζ + L * ((β - α) * (2 / 3) ^ n) := by
  have inv : ∀ n, TInv G ℓ α β ζ ((β - α) * (2 / 3) ^ n) (trisect ℓ u α β n) := by
    intro n
    induction n with
    | zero =>
        refine ⟨le_rfl, le_rfl, hαβ, le_rfl, by simp [trisect], le_rfl,
          ⟨α, ⟨le_rfl, hαβ⟩, rfl⟩, ?_⟩
        intro t ht h; rcases h with h | h
        · exact absurd ht.1 (not_le.mpr h)
        · exact absurd ht.2 (not_le.mpr h)
    | succ n ih =>
        have := tstep_inv hζ hcc horacle ih
        rw [show (β - α) * (2 / 3) ^ (n + 1) = 2 / 3 * ((β - α) * (2 / 3) ^ n) by ring]
        exact this
  obtain ⟨h1, h2, h3, h4, h5, h6, hw, h8⟩ := inv n
  refine ⟨hw, fun t ht => ?_⟩
  set s := trisect ℓ u α β n
  by_cases hin : s.lo ≤ t ∧ t ≤ s.hi
  · have hq : s.q ∈ Icc α β := ⟨by linarith, by linarith⟩
    obtain ⟨hlq, hgq, huq⟩ := horacle s.q hq
    have hlipq := hlip t ht s.q hq
    have hdist : |t - s.q| ≤ (β - α) * (2 / 3) ^ n := by
      rw [abs_le]; constructor <;> linarith [hin.1, hin.2]
    have := mul_le_mul_of_nonneg_left hdist hL
    linarith
  · have hout : t < s.lo ∨ s.hi < t := by
      by_contra hc; push Not at hc; exact hin hc
    have := h8 t ht hout
    have : 0 ≤ L * ((β - α) * (2 / 3) ^ n) := by
      have : 0 ≤ β - α := by linarith
      positivity
    linarith

end

end ImplicitLP
end CutQueryComplexity
