import CutQueryComplexity.Sparsify.Main
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Public parameters of the spectral primitive (D4; source `eq:parameters`)

For `0 < ε, ζ ≤ 1/2`, `C ≥ 1`, and `n ≥ 2`:

  `K = ⌈log₂ n⌉`, `R = ⌈log₄(4n²/ζ)⌉`, `δ = ε/(3R)`,
  `t = ⌈8 C (2K + 1) δ⁻² ln(8nR/ζ)⌉`, `J = ⌈log₂(4Rt/ζ)⌉`.

`params_ok` verifies the four conditions of `spectral_of_params`, and `spectral_primitive`
states the resulting theorem with these parameters.
-/

namespace CutQueryComplexity
namespace Sparsify

open Finset Probability Spanner Spectral Real
open scoped ENNReal

noncomputable section

variable (n : ℕ) (C ε ζ : ℝ)

/-- `K = ⌈log₂ n⌉`. -/
def pK : ℕ := ⌈logb 2 n⌉₊
/-- `R = ⌈log₄(4n²/ζ)⌉`. -/
def pR : ℕ := ⌈logb 4 (4 * n ^ 2 / ζ)⌉₊
/-- `δ = ε/(3R)`. -/
def pδ : ℝ := ε / (3 * pR n ζ)
/-- `t = ⌈8 C (2K + 1) δ⁻² ln(8nR/ζ)⌉`. -/
def pt : ℕ := ⌈8 * C * (2 * pK n + 1 : ℕ) / pδ n ε ζ ^ 2 * log (8 * n * pR n ζ / ζ)⌉₊
/-- `J = ⌈log₂(4Rt/ζ)⌉`. -/
def pJ : ℕ := ⌈logb 2 (4 * pR n ζ * pt n C ε ζ / ζ)⌉₊

variable {n C ε ζ}

theorem le_two_pow_ceil_logb {b x : ℝ} (hb : 1 < b) (hx : 0 < x) : x ≤ b ^ ⌈logb b x⌉₊ := by
  have h := Nat.le_ceil (logb b x)
  calc x = b ^ logb b x := (rpow_logb (by linarith) hb.ne' hx).symm
    _ ≤ b ^ (⌈logb b x⌉₊ : ℝ) := rpow_le_rpow_of_exponent_le hb.le h
    _ = b ^ ⌈logb b x⌉₊ := rpow_natCast b _

theorem pR_pos (hn : 2 ≤ n) (hζ : 0 < ζ) (hζ2 : ζ ≤ 1 / 2) : 1 ≤ pR n ζ := by
  unfold pR
  rw [Nat.one_le_ceil_iff]
  apply logb_pos (by norm_num)
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [lt_div_iff₀ hζ]; nlinarith

/-- **The four parameter conditions.** -/
theorem params_ok (hn : 2 ≤ n) (hC : 1 ≤ C) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hζ : 0 < ζ)
    (hζ2 : ζ ≤ 1 / 2) :
    n ≤ 2 ^ pK n ∧ 0 < pt n C ε ζ ∧ 0 < pδ n ε ζ ∧ pδ n ε ζ ≤ 1 ∧
      (pR n ζ : ℝ) * pδ n ε ζ ≤ ε / 3 ∧
      (pR n ζ : ℝ≥0∞) * (pt n C ε ζ * (2⁻¹ : ℝ≥0∞) ^ pJ n C ε ζ) ≤ ENNReal.ofReal (ζ / 4) ∧
      (pR n ζ : ℝ) * (2 * n * exp (-(pδ n ε ζ ^ 2) /
        (8 * (C * (2 * pK n + 1 : ℕ) / pt n C ε ζ)))) ≤ ζ / 4 ∧
      (n : ℝ) ^ 2 * (4⁻¹ : ℝ) ^ pR n ζ ≤ ζ / 4 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hR1 := pR_pos hn hζ hζ2
  have hR : (1 : ℝ) ≤ pR n ζ := by exact_mod_cast hR1
  have hδ : 0 < pδ n ε ζ := by unfold pδ; positivity
  have hδ1 : pδ n ε ζ ≤ 1 := by
    unfold pδ; rw [div_le_one (by positivity)]; nlinarith
  have hlog : 0 < log (8 * n * pR n ζ / ζ) := by
    apply log_pos; rw [lt_div_iff₀ hζ]; nlinarith
  have htreal : 0 < 8 * C * (2 * pK n + 1 : ℕ) / pδ n ε ζ ^ 2 * log (8 * n * pR n ζ / ζ) := by
    have : (0 : ℝ) < (2 * pK n + 1 : ℕ) := by positivity
    positivity
  have ht : 0 < pt n C ε ζ := Nat.ceil_pos.mpr htreal
  have htR : (0 : ℝ) < pt n C ε ζ := by exact_mod_cast ht
  refine ⟨?_, ht, hδ, hδ1, ?_, ?_, ?_, ?_⟩
  · have := le_two_pow_ceil_logb (b := 2) (by norm_num) (show (0 : ℝ) < n by linarith)
    unfold pK; exact_mod_cast this
  · apply le_of_eq; unfold pδ; field_simp
  · -- spanner failures
    have hx : (0 : ℝ) < 4 * pR n ζ * pt n C ε ζ / ζ := by positivity
    have h2J := le_two_pow_ceil_logb (b := 2) (by norm_num) hx
    have key : (pR n ζ : ℝ) * (pt n C ε ζ * (2⁻¹ : ℝ) ^ pJ n C ε ζ) ≤ ζ / 4 := by
      rw [inv_pow, ← div_eq_mul_inv, mul_div_assoc', div_le_iff₀ (by positivity)]
      unfold pJ
      rw [div_le_iff₀ hζ] at h2J
      nlinarith
    calc (pR n ζ : ℝ≥0∞) * (pt n C ε ζ * (2⁻¹ : ℝ≥0∞) ^ pJ n C ε ζ)
        = ENNReal.ofReal ((pR n ζ : ℝ) * (pt n C ε ζ * (2⁻¹ : ℝ) ^ pJ n C ε ζ)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal key
  · -- one-round failures
    have hK0 : (0 : ℝ) < (2 * pK n + 1 : ℕ) := by positivity
    have htle := Nat.le_ceil (8 * C * (2 * pK n + 1 : ℕ) / pδ n ε ζ ^ 2 *
      log (8 * n * pR n ζ / ζ))
    set A : ℝ := 8 * C * (2 * pK n + 1 : ℕ)
    set X : ℝ := 8 * n * pR n ζ / ζ
    have hA : 0 < A := by positivity
    have hX : 0 < X := by positivity
    have h1 : -(pδ n ε ζ ^ 2) / (8 * (C * (2 * pK n + 1 : ℕ) / pt n C ε ζ)) =
        -(pδ n ε ζ ^ 2 * pt n C ε ζ / A) := by
      simp only [A]; field_simp
    have h2 : log X ≤ pδ n ε ζ ^ 2 * pt n C ε ζ / A := by
      have htle' : A / pδ n ε ζ ^ 2 * log X ≤ pt n C ε ζ := htle
      rw [le_div_iff₀ hA]
      calc log X * A = A / pδ n ε ζ ^ 2 * log X * pδ n ε ζ ^ 2 := by field_simp
        _ ≤ pt n C ε ζ * pδ n ε ζ ^ 2 := mul_le_mul_of_nonneg_right htle' (by positivity)
        _ = _ := by ring
    have h3 : exp (-(pδ n ε ζ ^ 2) / (8 * (C * (2 * pK n + 1 : ℕ) / pt n C ε ζ))) ≤ X⁻¹ := by
      rw [h1, ← exp_log hX, ← exp_neg, exp_le_exp]
      linarith
    calc (pR n ζ : ℝ) * (2 * n * exp (-(pδ n ε ζ ^ 2) / (8 * (C * (2 * pK n + 1 : ℕ) /
          pt n C ε ζ)))) ≤ (pR n ζ : ℝ) * (2 * n * X⁻¹) := by gcongr
      _ = ζ / 4 := by simp only [X]; field_simp; ring
  · -- terminal residual
    have hx : (0 : ℝ) < 4 * n ^ 2 / ζ := by positivity
    have h4R := le_two_pow_ceil_logb (b := 4) (by norm_num) hx
    unfold pR
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hζ] at h4R
    nlinarith

theorem card_resid_le (G : DiGraph (Fin n)) (P : Sym2 (Fin n) → Bool) :
    ((resid G P).card : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h1 : (resid G P).card ≤ Fintype.card (Sym2 (Fin n)) := card_le_univ _
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right] at h1
  have h2 : (n + 1) * n / 2 ≤ n ^ 2 := by
    apply Nat.div_le_of_le_mul
    nlinarith
  exact_mod_cast h1.trans h2

/-- **The spectral primitive** (source `thm:main`): with the public parameters above,
probability at least `1 − ζ`, for every real vector. -/
theorem spectral_primitive {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ}
    (hn : 2 ≤ n) (hC : 1 ≤ C) (hCG : ∀ e, (symS G e : ℝ) ≤ C) (hw0 : ∀ e, 0 ≤ w e)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hζ : 0 < ζ) (hζ2 : ζ ≤ 1 / 2) :
    mass ((sparsify w (pK n) (pJ n C ε ζ) (pt n C ε ζ) (pR n ζ)).eval G.out)
      (fun o => ¬ ∃ out, o = some out ∧
        (∀ x, (1 - ε) * E0 G w x ≤ Eo out x ∧ Eo out x ≤ (1 + ε) * E0 G w x) ∧
        (∀ e, out e ≠ 0 → 0 < symS G e ∧ 0 < w e) ∧
        (univ.filter fun e => out e ≠ 0).card ≤
          pR n ζ * (pt n C ε ζ * capH (Fin n) (pK n)) ∧
        (∀ e, out e ≠ 0 → ∃ r' < pR n ζ, out e = (symS G e : ℝ) * (4 : ℝ) ^ r' * w e)) ≤
          ENNReal.ofReal ζ := by
  obtain ⟨hK, ht, hδ, hδ1, hRδ, hJ, hγ, hres⟩ := params_ok hn hC hε hε2 hζ hζ2
  refine spectral_of_params (by linarith) hCG hw0 hK ht hδ hδ1 hε hε2 hζ.le hRδ hJ hγ ?_
  have hc := card_resid_le G (P0 w)
  calc ((resid G (P0 w)).card : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ pR n ζ
      = ENNReal.ofReal (((resid G (P0 w)).card : ℝ) * (4⁻¹ : ℝ) ^ pR n ζ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * (4⁻¹ : ℝ) ^ pR n ζ) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc (by positivity))
    _ ≤ _ := ENNReal.ofReal_le_ofReal hres

end

end Sparsify
end CutQueryComplexity
