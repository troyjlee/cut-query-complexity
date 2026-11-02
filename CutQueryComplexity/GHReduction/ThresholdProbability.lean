import CutQueryComplexity.GHReduction.ThresholdSampling
import Mathlib.Data.Nat.Log

/-! # A quantitative singleton event for the actual terminal sampler

The level is a proof-only choice from the hidden shore size. The public routine
runs every level through `clog 2 (2 * n)`. Pairwise survival and a union bound
give a lower bound of `1 / (8 * |A|)` for a specified unique survivor.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

def thresholdLevels (n : ℕ) : ℕ := Nat.clog 2 (2 * n)

def hitLevel (m : ℕ) : ℕ := Nat.clog 2 (2 * m)

theorem hitLevel_le {m n : ℕ} (hmn : m ≤ n) : hitLevel m ≤ thresholdLevels n :=
  Nat.clog_mono_right 2 (Nat.mul_le_mul_left 2 hmn)

theorem hitLevel_scale {m : ℕ} (hm : 0 < m) :
    2 * m ≤ 2 ^ hitLevel m ∧ 2 ^ hitLevel m ≤ 4 * m := by
  refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
  have hpos : 0 < Nat.clog 2 (2 * m) := Nat.clog_pos (by decide) (by omega)
  have hprev := Nat.pow_pred_clog_lt_self (b := 2) (by decide) (x := 2 * m) (by omega)
  have he : hitLevel m = (Nat.clog 2 (2 * m)).pred + 1 := by
    dsimp [hitLevel]
    omega
  rw [he, pow_succ]
  omega

variable {V : Type} [Fintype V] [DecidableEq V]

theorem uniqueSurvivor_real_bound {levels i : ℕ} (hi : i ≤ levels)
    (A : Finset V) {v : V} (hv : v ∈ A) :
    (2⁻¹ : ℝ) ^ i ≤
      (mass (thresholdSeedPMF V levels) (UniqueSurvivor A v i)).toReal +
        (A.card - 1 : ℕ) * (((2⁻¹ : ℝ) ^ i) ^ 2) := by
  have hf : ((A.card - 1 : ℕ) : ℝ≥0∞) * (((2⁻¹ : ℝ≥0∞) ^ i) ^ 2) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp)
      (ENNReal.pow_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))))
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨mass_ne_top _ _, hf⟩)
    (uniqueSurvivor_mass_bound hi A hv)
  simpa only [ENNReal.toReal_add (mass_ne_top _ _) hf, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast] using h

/-- Multiplicative form avoids division at the empty shore; membership ensures
that the shore size is positive. -/
theorem uniqueSurvivor_hitLevel_real {levels : ℕ} (A : Finset V) {v : V}
    (hv : v ∈ A) (hi : hitLevel A.card ≤ levels) :
    1 ≤ 8 * (A.card : ℝ) *
      (mass (thresholdSeedPMF V levels) (UniqueSurvivor A v (hitLevel A.card))).toReal := by
  let p : ℝ := (2⁻¹ : ℝ) ^ hitLevel A.card
  let q : ℝ := (mass (thresholdSeedPMF V levels)
    (UniqueSurvivor A v (hitLevel A.card))).toReal
  have hm : 0 < A.card := Finset.card_pos.mpr ⟨v, hv⟩
  have hmR : 0 < (A.card : ℝ) := by exact_mod_cast hm
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hprod : p * (2 : ℝ) ^ hitLevel A.card = 1 := by
    dsimp [p]
    rw [inv_pow, inv_mul_cancel₀ (by positivity)]
  obtain ⟨hlo, hhi⟩ := hitLevel_scale hm
  have hloR : 2 * (A.card : ℝ) ≤ (2 : ℝ) ^ hitLevel A.card := by exact_mod_cast hlo
  have hhiR : (2 : ℝ) ^ hitLevel A.card ≤ 4 * (A.card : ℝ) := by exact_mod_cast hhi
  have hsmall : 2 * (A.card : ℝ) * p ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hloR hp
    nlinarith
  have hlarge : 1 ≤ 4 * (A.card : ℝ) * p := by
    have := mul_le_mul_of_nonneg_left hhiR hp
    nlinarith
  have hquad : (A.card : ℝ) * p ^ 2 ≤ p / 2 := by
    have := mul_le_mul_of_nonneg_right hsmall hp
    nlinarith
  have hpred : ((A.card - 1 : ℕ) : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Nat.sub_le A.card 1
  have hbound : p ≤ q + ((A.card - 1 : ℕ) : ℝ) * p ^ 2 :=
    uniqueSurvivor_real_bound hi A hv
  have hpredquad := mul_le_mul_of_nonneg_right hpred (sq_nonneg p)
  have hq : p ≤ 2 * q := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hq (show 0 ≤ 4 * (A.card : ℝ) by positivity)
  change 1 ≤ 8 * (A.card : ℝ) * q
  nlinarith

theorem uniqueSurvivor_hitLevel {levels : ℕ} (A : Finset V) {v : V}
    (hv : v ∈ A) (hi : hitLevel A.card ≤ levels) :
    ENNReal.ofReal (1 / 8 : ℝ) ≤ (A.card : ℝ≥0∞) *
      mass (thresholdSeedPMF V levels) (UniqueSurvivor A v (hitLevel A.card)) := by
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (by simp) (mass_ne_top _ _))).mp
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have h := uniqueSurvivor_hitLevel_real A hv hi
  linarith

end
end CutQueryComplexity.GHReduction
