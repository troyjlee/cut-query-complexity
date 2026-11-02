import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.FullPlayer
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log

/-!
# Public parameters for the five-thirds construction

The cube root is chosen by a finite search bounded by `N+1`. The round
budget uses the proved entropy constant and a ceiling logarithm large
enough for every local clone type. No strategy or round-bound assumption
is a parameter of the resulting query program.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open CutMatching
noncomputable section

private theorem cubeRoot_exists (N : ℕ) : ∃ t : ℕ, 0 < t ∧ N ≤ t ^ 3 := by
  refine ⟨N + 1, by omega, ?_⟩
  exact (Nat.le_succ N).trans (le_self_pow₀ (by omega) (by decide))

def cubeRoot (N : ℕ) : ℕ := Nat.find (cubeRoot_exists N)

theorem cubeRoot_pos (N : ℕ) : 0 < cubeRoot N := (Nat.find_spec (cubeRoot_exists N)).1

theorem le_cubeRoot_pow (N : ℕ) : N ≤ cubeRoot N ^ 3 := (Nat.find_spec (cubeRoot_exists N)).2

theorem cubeRoot_min {N t : ℕ} (ht : 0 < t) (hN : N ≤ t ^ 3) : cubeRoot N ≤ t :=
  Nat.find_min' (cubeRoot_exists N) ⟨ht, hN⟩

theorem cubeRoot_le_succ (N : ℕ) : cubeRoot N ≤ N + 1 :=
  cubeRoot_min (by omega) ((Nat.le_succ N).trans (le_self_pow₀ (by omega) (by decide)))

theorem pred_cubeRoot_pow_lt {N : ℕ} (hN : 0 < N) : (cubeRoot N - 1) ^ 3 < N := by
  have ht := cubeRoot_pos N
  by_cases he : cubeRoot N = 1
  · simpa only [he, Nat.sub_self, zero_pow (by decide : 3 ≠ 0)] using hN
  · by_contra hn
    have hle := cubeRoot_min (by omega : 0 < cubeRoot N - 1) (le_of_not_gt hn)
    omega

theorem log_nat_le_clog (N : ℕ) : Real.log (N : ℝ) ≤ (Nat.clog 2 (N + 1) : ℝ) := by
  by_cases hzero : N = 0
  · simp [hzero]
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (N : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (N + 1) := by
    exact_mod_cast (Nat.le_succ N).trans (Nat.le_pow_clog (by decide : 1 < 2) (N + 1))
  have hl := Real.log_le_log hN hp
  rw [Real.log_pow] at hl
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hm := mul_le_mul_of_nonneg_left htwo
    (Nat.cast_nonneg (Nat.clog 2 (N + 1)) : (0 : ℝ) ≤ Nat.clog 2 (N + 1))
  simpa only [mul_one] using hl.trans hm

theorem balancedRounds_le_clog (N : ℕ) :
    balancedRounds N ≤ entropyRoundFactor * Nat.clog 2 (N + 1) + 1 := by
  have hfactor : 64 / gapConstant ≤ (entropyRoundFactor : ℝ) := by
    exact (div_le_iff₀ gapConstant_pos).mpr entropyRoundFactor_scaled
  have hlog := log_nat_le_clog N
  have hleft := mul_le_mul_of_nonneg_left hlog
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 64) gapConstant_pos.le)
  have hright := mul_le_mul_of_nonneg_right hfactor
    (Nat.cast_nonneg (Nat.clog 2 (N + 1)) : (0 : ℝ) ≤ Nat.clog 2 (N + 1))
  apply Nat.add_le_add_right _ 1
  apply Nat.ceil_le.mpr
  simpa only [Nat.cast_mul] using hleft.trans hright

def roundBudget (N : ℕ) : ℕ :=
  16 * (entropyRoundFactor * Nat.clog 2 (2 * N * (N + 1) + 1) + 1) + 4

theorem roundBudget_ge_two (N : ℕ) : 2 ≤ roundBudget N := by unfold roundBudget; omega

theorem local_rounds_le {N q : ℕ} (hq : q ≤ N) :
    normalizedRounds (q * (2 * cubeRoot N)) ≤ roundBudget N := by
  have hsize : q * (2 * cubeRoot N) ≤ 2 * N * (N + 1) := by
    have h := Nat.mul_le_mul hq (Nat.mul_le_mul_left 2 (cubeRoot_le_succ N))
    nlinarith
  have hlog := Nat.clog_mono_right 2 (Nat.add_le_add_right hsize 1)
  have hb := balancedRounds_le_clog (q * (2 * cubeRoot N))
  have hm := Nat.mul_le_mul_left entropyRoundFactor hlog
  unfold normalizedRounds roundBudget
  omega

def sizeLog (N : ℕ) : ℕ := Nat.clog 2 (2 * N + 2) + 1

theorem sizeLog_pos (N : ℕ) : 0 < sizeLog N := by unfold sizeLog; omega

def roundCoefficient : ℕ := 32 * entropyRoundFactor + 20

theorem roundBudget_le (N : ℕ) : roundBudget N ≤ roundCoefficient * sizeLog N := by
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (2 * N + 2)
  have hs : 2 * N * (N + 1) + 1 ≤ (2 * N + 2) ^ 2 := by nlinarith
  have hpow := Nat.mul_le_mul hp hp
  have hlarge : 2 * N * (N + 1) + 1 ≤ 2 ^ (2 * Nat.clog 2 (2 * N + 2)) := by
    calc
      _ ≤ (2 * N + 2) ^ 2 := hs
      _ ≤ (2 ^ Nat.clog 2 (2 * N + 2)) ^ 2 := by simpa only [pow_two] using hpow
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hlog := Nat.clog_le_of_le_pow hlarge
  have hm := Nat.mul_le_mul_left (16 * entropyRoundFactor) hlog
  unfold roundBudget roundCoefficient sizeLog
  nlinarith

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.le_cubeRoot_pow
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.local_rounds_le
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.roundBudget_le
