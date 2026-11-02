import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

/-! # Public precision parameters (D7)

Every precision parameter is an explicit public natural number computed from public reals by
`Nat.clog 2 ⌈·⌉₊`:
* `iters β` refinement steps give `2^{−iters β} ≤ β` (`half_pow_iters_le`);
* `bits c β` fractional bits give `c · 2^{−bits c β} ≤ β` (`div_two_pow_bits_le`);
* `magBits X` magnitude bits give `X < 2^{magBits X}` (`lt_two_pow_magBits`).

Each parameter is logarithmic in the public envelope (`clog_le_log_add_one`), so the query
budgets they enter are polylogarithmic factors.
-/

namespace CutQueryComplexity
namespace ImplicitLP

noncomputable section

theorem le_two_pow_clog_ceil (x : ℝ) : x ≤ (2 : ℝ) ^ Nat.clog 2 ⌈x⌉₊ := by
  calc x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    _ ≤ ((2 ^ Nat.clog 2 ⌈x⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_pow_clog one_lt_two _
    _ = (2 : ℝ) ^ Nat.clog 2 ⌈x⌉₊ := by push_cast; rfl

/-- Refinement steps for accuracy `β`. -/
def iters (β : ℝ) : ℕ := Nat.clog 2 ⌈1 / β⌉₊

theorem half_pow_iters_le {β : ℝ} (hβ : 0 < β) : (1 / 2 : ℝ) ^ iters β ≤ β := by
  have h := le_two_pow_clog_ceil (1 / β)
  have h2 : (0 : ℝ) < 2 ^ iters β := by positivity
  rw [one_div_pow, div_le_iff₀ h2]
  rw [div_le_iff₀ hβ] at h
  simpa [iters, mul_comm] using h

/-- Fractional bits for a grid error `c · 2^{−p} ≤ β`. -/
def bits (c β : ℝ) : ℕ := Nat.clog 2 ⌈c / β⌉₊

theorem div_two_pow_bits_le {c β : ℝ} (hβ : 0 < β) : c / (2 : ℝ) ^ bits c β ≤ β := by
  have h := le_two_pow_clog_ceil (c / β)
  have h2 : (0 : ℝ) < 2 ^ bits c β := by positivity
  rw [div_le_iff₀ h2]
  rw [div_le_iff₀ hβ] at h
  simpa [bits, mul_comm] using h

/-- Magnitude bits for a bound `X < 2^B`. -/
def magBits (X : ℝ) : ℕ := Nat.clog 2 ⌈X⌉₊ + 1

theorem lt_two_pow_magBits (X : ℝ) : X < (2 : ℝ) ^ magBits X := by
  have h := le_two_pow_clog_ceil X
  have h2 : (0 : ℝ) < 2 ^ Nat.clog 2 ⌈X⌉₊ := by positivity
  rw [magBits, pow_succ]
  linarith

theorem le_two_pow_magBits (X : ℝ) : X ≤ (2 : ℝ) ^ magBits X := (lt_two_pow_magBits X).le

/-- The parameters are logarithmic: `clog₂ ⌈x⌉ ≤ log₂ x + 1` for `x ≥ 1`. -/
theorem clog_le_log_add_one {x : ℝ} (hx : 1 ≤ x) :
    (Nat.clog 2 ⌈x⌉₊ : ℝ) ≤ Real.logb 2 x + 2 := by
  have hc : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hcpos : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; have := Nat.le_ceil x; rw [h] at this; push_cast at this; linarith)
  rcases Nat.eq_zero_or_pos (Nat.clog 2 ⌈x⌉₊) with h0 | hpos
  · rw [h0]; push_cast
    have : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
    linarith
  · -- `2^{c−1} < ⌈x⌉ ≤ x + 1 ≤ 2x`
    have hlt : 2 ^ (Nat.clog 2 ⌈x⌉₊ - 1) < ⌈x⌉₊ := by
      have := Nat.pow_pred_clog_lt_self one_lt_two (show 1 < ⌈x⌉₊ by
        by_contra hle
        push Not at hle
        have : ⌈x⌉₊ = 1 := le_antisymm hle hcpos
        rw [this, Nat.clog_one_right] at hpos
        exact lt_irrefl _ hpos)
      exact this
    have hltR : (2 : ℝ) ^ (Nat.clog 2 ⌈x⌉₊ - 1) < 2 * x := by
      have : ((2 ^ (Nat.clog 2 ⌈x⌉₊ - 1) : ℕ) : ℝ) < (⌈x⌉₊ : ℝ) := by exact_mod_cast hlt
      push_cast at this
      linarith
    have hlog := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hltR
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
      Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at hlog
    have hcast : ((Nat.clog 2 ⌈x⌉₊ - 1 : ℕ) : ℝ) = (Nat.clog 2 ⌈x⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hpos]; push_cast; ring
    rw [hcast] at hlog
    linarith


/-- **The D4 accuracy choice.** If `δ ≤ ε/(2R)` and `0 ≤ ε ≤ 1`, the `R`-level sparsifier's
energy factors `(1 ∓ δ)^R` lie in `[1 − ε, 1 + ε]`. -/
theorem sparsify_factor_bounds {δ ε : ℝ} {R : ℕ} (hδ0 : 0 ≤ δ) (hε1 : ε ≤ 1)
    (hδ : 2 * R * δ ≤ ε) : 1 - ε ≤ (1 - δ) ^ R ∧ (1 + δ) ^ R ≤ 1 + ε := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp only [Nat.cast_zero, mul_zero, zero_mul] at hδ
    simp only [pow_zero]
    constructor <;> linarith
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  set y : ℝ := R * δ with hydef
  have hy0 : 0 ≤ y := mul_nonneg (Nat.cast_nonneg R) hδ0
  have hy : y ≤ 1 / 2 := by linarith
  have hδ1 : δ ≤ 1 / 2 := by nlinarith
  -- Bernoulli: `1 − Rδ ≤ (1 − δ)^R`
  have hB : 1 - y ≤ (1 - δ) ^ R := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) R
    rw [← sub_eq_add_neg] at this
    linarith [show (R : ℝ) * -δ = -y by rw [hydef]; ring]
  refine ⟨by linarith, ?_⟩
  -- `(1+δ)^R (1 − Rδ) ≤ ((1+δ)(1−δ))^R ≤ 1`
  have hX0 : 0 ≤ (1 + δ) ^ R := by positivity
  have hprod : (1 + δ) ^ R * (1 - y) ≤ 1 := by
    calc (1 + δ) ^ R * (1 - y) ≤ (1 + δ) ^ R * (1 - δ) ^ R :=
          mul_le_mul_of_nonneg_left hB hX0
      _ = (1 - δ ^ 2) ^ R := by rw [← mul_pow]; ring_nf
      _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)
  nlinarith [mul_nonneg hy0 (show 0 ≤ 1 - 2 * y by linarith)]

end

end ImplicitLP
end CutQueryComplexity
