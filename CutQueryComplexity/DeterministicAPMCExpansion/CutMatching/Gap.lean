import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Entropy
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp

/-!
# A proved uniform entropy gain for imbalanced matched probabilities

The analytic constant is obtained from a fixed continuous function on [0,1/2].
It is independent of the hidden graph, size, history and matching response.
Strict concavity proves its positivity; no entropy-gap assumption is supplied.
The resulting natural round factor has an explicit definition from this proved
constant. This module does not yet prove the balanced-game progress invariant.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open scoped Classical
noncomputable section

def pairGain (p q : ℝ) : ℝ :=
  2 * Real.negMulLog ((p + q) / 2) - Real.negMulLog p - Real.negMulLog q

theorem pairGain_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) : 0 ≤ pairGain p q := by
  have h := entropy_pair_average p q hp hq
  unfold pairGain
  linarith

/-- The logarithms of the common scale cancel exactly, including zero. -/
theorem pairGain_scale (c p q : ℝ) : pairGain (c * p) (c * q) = c * pairGain p q := by
  have he : (c * p + c * q) / 2 = c * ((p + q) / 2) := by ring
  simp only [pairGain, he, Real.negMulLog_mul]
  ring

theorem pairGain_ratio_pos {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    0 < pairGain 1 r := by
  have h := Real.strictConcaveOn_negMulLog.2
    (show (0 : ℝ) ≤ 1 by norm_num) hr.1 (show (1 : ℝ) ≠ r by linarith [hr.2])
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  have he : (1 / 2 : ℝ) * 1 + (1 / 2 : ℝ) * r = (1 + r) / 2 := by ring
  rw [he] at h
  unfold pairGain
  linarith

theorem continuous_pairGain_ratio : Continuous (fun r : ℝ => pairGain 1 r) := by
  unfold pairGain
  fun_prop

private theorem exists_gap_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Set.Icc (0 : ℝ) (1 / 2), c ≤ pairGain 1 r := by
  exact isCompact_Icc.exists_forall_le' continuous_pairGain_ratio.continuousOn
    (fun _ hr => pairGain_ratio_pos hr)

/-- One universal constant fixed by the analytic proof, before all inputs. -/
def gapConstant : ℝ := Classical.choose exists_gap_constant

theorem gapConstant_pos : 0 < gapConstant :=
  (Classical.choose_spec exists_gap_constant).1

theorem gapConstant_le {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    gapConstant ≤ pairGain 1 r := (Classical.choose_spec exists_gap_constant).2 r hr

/-- A good endpoint's probability pays a fixed positive entropy increment.
This also covers `p=q=0` without dividing by zero. -/
theorem pairGain_ge {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hbalance : 2 * q ≤ p) :
    gapConstant * p ≤ pairGain p q := by
  by_cases hpzero : p = 0
  · have hqzero : q = 0 := by linarith
    simp [hpzero, hqzero, pairGain]
  · have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpzero)
    have hr : q / p ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      refine ⟨div_nonneg hq hp, (div_le_iff₀ hppos).mpr ?_⟩
      linarith
    have he : p * (q / p) = q := by field_simp
    have hs := pairGain_scale p 1 (q / p)
    rw [mul_one, he] at hs
    calc
      gapConstant * p = p * gapConstant := mul_comm _ _
      _ ≤ p * pairGain 1 (q / p) := mul_le_mul_of_nonneg_left (gapConstant_le hr) hp
      _ = pairGain p q := hs.symm

/-- A public natural coefficient to be used in the logarithmic strategy
budget after proving the combinatorial progress bound. -/
def entropyRoundFactor : ℕ := max 2 ⌈64 / gapConstant⌉₊

theorem entropyRoundFactor_ge_two : 2 ≤ entropyRoundFactor := le_max_left _ _

theorem entropyRoundFactor_scaled : (64 : ℝ) ≤ entropyRoundFactor * gapConstant := by
  have hceil : 64 / gapConstant ≤ (⌈64 / gapConstant⌉₊ : ℝ) := Nat.le_ceil _
  have hc : (64 : ℝ) ≤ (⌈64 / gapConstant⌉₊ : ℝ) * gapConstant :=
    (div_le_iff₀ gapConstant_pos).mp hceil
  have hfactor : (⌈64 / gapConstant⌉₊ : ℝ) ≤ entropyRoundFactor := by
    exact_mod_cast (show ⌈64 / gapConstant⌉₊ ≤ entropyRoundFactor from le_max_right _ _)
  exact hc.trans (mul_le_mul_of_nonneg_right hfactor gapConstant_pos.le)

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.gapConstant_pos
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pairGain_ge
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropyRoundFactor_scaled
