import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr

/-!
# Explicit five-thirds bound for the implemented query budget

This expands `coreBudget`, including the three-query subtype adapter, all
active work, shaving, recovery, and triangle padding. No cost or asymptotic
claim is a hypothesis. The entropy coefficient is the public constant
constructed by the cut-player proof.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open Finset Decomposition AllPairs
noncomputable section

theorem search_logs_le (N : ℕ) :
    Nat.clog 2 (N + 2) + 1 ≤ sizeLog N ∧
      Nat.clog 2 (N + 1) ≤ sizeLog N ∧ Nat.clog 2 N + 1 ≤ sizeLog N := by
  have h₁ := Nat.clog_mono_right 2 (show N + 2 ≤ 2 * N + 2 by omega)
  have h₂ := Nat.clog_mono_right 2 (show N + 1 ≤ 2 * N + 2 by omega)
  have h₃ := Nat.clog_mono_right 2 (show N ≤ 2 * N + 2 by omega)
  unfold sizeLog
  omega

theorem decomposition_budget_le (N R t : ℕ) :
    queryBudget N R t ≤ 73728 * (R + 1) * R ^ 2 * N * t ^ 2 * sizeLog N ^ 2 := by
  have hlogs := search_logs_le N
  calc
    _ = 73728 * (R + 1) * R ^ 2 * N * t ^ 2 *
        (Nat.clog 2 (N + 2) + 1) * Nat.clog 2 (N + 1) := by
      unfold queryBudget nodeUnitBudget
      ring
    _ ≤ 73728 * (R + 1) * R ^ 2 * N * t ^ 2 * sizeLog N * sizeLog N := by
      gcongr
      · exact hlogs.1
      · exact hlogs.2.1
    _ = _ := by ring

theorem recovery_edgeCap_le (N R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    edgeCap N (2 * t) (8 * R) (t ^ 2) ≤ 2018 * N * R * t ^ 2 * sizeLog N := by
  let L := sizeLog N
  have hL : 1 ≤ L := sizeLog_pos N
  have hlog : Nat.clog 2 N ≤ L := by have h := (search_logs_le N).2.2; omega
  have ht2 : t ≤ R * t ^ 2 := by
    have hsq : t ≤ t ^ 2 := le_self_pow₀ ht (by decide)
    calc t ≤ t ^ 2 := hsq
         _ = 1 * t ^ 2 := by ring
         _ ≤ R * t ^ 2 := by gcongr
  have hfirst : 49 * (2 * t) * N * Nat.clog 2 N ≤ 98 * N * R * t ^ 2 * L := by
    calc
      _ = 98 * N * t * Nat.clog 2 N := by ring
      _ ≤ 98 * N * (R * t ^ 2) * L := by gcongr
      _ = _ := by ring
  have hsecond : 60 * N * shavingScale (8 * R) (t ^ 2) ≤ 1920 * N * R * t ^ 2 * L := by
    calc
      _ = 1920 * N * R * t ^ 2 * 1 := by unfold shavingScale; ring
      _ ≤ _ := by gcongr
  change 49 * (2 * t) * N * Nat.clog 2 N + 60 * N * shavingScale (8 * R) (t ^ 2) ≤ _
  nlinarith only [hfirst, hsecond]

theorem recovery_budget_le (V : Type) [Fintype V] (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    partitionRecoveryBudget V (2 * t) (8 * R) (t ^ 2) ≤
      12116 * Fintype.card V * R * t ^ 2 * sizeLog (Fintype.card V) ^ 2 := by
  classical
  let N := Fintype.card V
  let L := sizeLog N
  have hL : 1 ≤ L := sizeLog_pos N
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have hlog := (search_logs_le N).2.2
  have hcap := recovery_edgeCap_le N R t hR ht
  have hbase : N ≤ N * R * t ^ 2 * L := by
    calc N = N * 1 * 1 * 1 := by ring
         _ ≤ _ := by gcongr
  have hbase2 : N ≤ N * R * t ^ 2 * L ^ 2 := by
    calc N = N * 1 * 1 * 1 := by ring
         _ ≤ _ := by gcongr; exact one_le_pow₀ hL
  have hinside : N + 2 * edgeCap N (2 * t) (8 * R) (t ^ 2) ≤ 4037 * N * R * t ^ 2 * L := by
    nlinarith only [hcap, hbase]
  have hproduct := Nat.mul_le_mul hinside (Nat.mul_le_mul_right 3 hlog)
  rw [partitionRecoveryBudget_eq]
  change 5 * N + (N + 2 * edgeCap N (2 * t) (8 * R) (t ^ 2)) *
    ((Nat.clog 2 N + 1) * 3) ≤ 12116 * N * R * t ^ 2 * L ^ 2
  nlinarith only [hproduct, hbase2]

def constructionCoefficient : ℕ := 100000 * (roundCoefficient + 1) ^ 3

theorem coreBudget_le (V : Type) [Fintype V] :
    coreBudget V ≤ constructionCoefficient * cubeRoot (Fintype.card V) ^ 5 *
      sizeLog (Fintype.card V) ^ 5 := by
  let N := Fintype.card V
  let R := roundBudget N
  let t := cubeRoot N
  let L := sizeLog N
  have hR : 1 ≤ R := by have h := roundBudget_ge_two N; omega
  have ht : 1 ≤ t := cubeRoot_pos N
  have hL : 1 ≤ L := sizeLog_pos N
  have hround := roundBudget_le N
  have hRplus : R + 1 ≤ (roundCoefficient + 1) * L := by nlinarith
  have hN : N ≤ t ^ 3 := le_cubeRoot_pow N
  have hfirst := decomposition_budget_le N R t
  have hsecond := recovery_budget_le V R t hR ht
  have hpow : (R + 1) * R ^ 2 ≤ (R + 1) ^ 3 := by
    calc
      _ ≤ (R + 1) * (R + 1) ^ 2 := by gcongr; omega
      _ = _ := by ring
  have hRpow : R ≤ (R + 1) ^ 3 :=
    (Nat.le_succ R).trans (le_self_pow₀ (by omega) (by decide))
  have hfirst' : queryBudget N R t ≤ 73728 * (R + 1) ^ 3 * N * t ^ 2 * L ^ 2 := by
    apply hfirst.trans
    calc
      _ = 73728 * ((R + 1) * R ^ 2) * N * t ^ 2 * L ^ 2 := by ring
      _ ≤ _ := by gcongr
  have hsecond' : partitionRecoveryBudget V (2 * t) (8 * R) (t ^ 2) ≤
      12116 * (R + 1) ^ 3 * N * t ^ 2 * L ^ 2 := by
    apply hsecond.trans
    calc
      _ ≤ 12116 * N * (R + 1) ^ 3 * t ^ 2 * L ^ 2 := by gcongr
      _ = _ := by ring
  calc
    coreBudget V ≤ 100000 * (R + 1) ^ 3 * N * t ^ 2 * L ^ 2 := by
      change queryBudget N R t + partitionRecoveryBudget V (2 * t) (8 * R) (t ^ 2) ≤ _
      nlinarith only [hfirst', hsecond']
    _ ≤ 100000 * ((roundCoefficient + 1) * L) ^ 3 * (t ^ 3) * t ^ 2 * L ^ 2 := by
      gcongr
    _ = constructionCoefficient * t ^ 5 * L ^ 5 := by unfold constructionCoefficient; ring

theorem cubeRoot_cube_le {N : ℕ} (hN : 1 ≤ N) : cubeRoot N ^ 3 ≤ 8 * N := by
  have ht := cubeRoot_pos N
  by_cases he : cubeRoot N = 1
  · rw [he]
    norm_num
    omega
  have hpred : cubeRoot N ≤ 2 * (cubeRoot N - 1) := by omega
  have hp := pred_cubeRoot_pow_lt (show 0 < N by omega)
  have hc : cubeRoot N ^ 3 ≤ 8 * (cubeRoot N - 1) ^ 3 := by
    calc
      _ ≤ (2 * (cubeRoot N - 1)) ^ 3 := by gcongr
      _ = _ := by ring
  omega

theorem padded_root_fifth_le {n : ℕ} (hn : 1 ≤ n) :
    (cubeRoot (3 * n) : ℝ) ^ 5 ≤ (24 : ℝ) ^ (5 / 3 : ℝ) * (n : ℝ) ^ (5 / 3 : ℝ) := by
  have hc : (cubeRoot (3 * n) : ℝ) ^ 3 ≤ 24 * (n : ℝ) := by
    have h := cubeRoot_cube_le (N := 3 * n) (by omega)
    have h' : cubeRoot (3 * n) ^ 3 ≤ 24 * n := by nlinarith
    exact_mod_cast h'
  have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (cubeRoot (3 * n) : ℝ) ^ 3)
    hc (by norm_num : (0 : ℝ) ≤ 5 / 3)
  have he : ((cubeRoot (3 * n) : ℝ) ^ 3) ^ (5 / 3 : ℝ) = (cubeRoot (3 * n) : ℝ) ^ 5 := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _) 3 (5 / 3)]
    norm_num
  rw [he, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)] at hp
  exact hp

theorem sizeLog_padded_le {n : ℕ} (hn : 1 ≤ n) : sizeLog (3 * n) ≤ 4 * sizeLog n := by
  have hp : 2 * (3 * n) + 2 ≤ 2 ^ (Nat.clog 2 n + 3) := by
    calc
      _ ≤ 8 * n := by omega
      _ ≤ 8 * 2 ^ Nat.clog 2 n := Nat.mul_le_mul_left 8 (Nat.le_pow_clog (by decide) n)
      _ = _ := by rw [pow_add]; ring
  have hc := Nat.clog_le_of_le_pow hp
  have hnlog := Nat.clog_mono_right 2 (show n ≤ 2 * n + 2 by omega)
  unfold sizeLog
  omega

def headlineConstant : ℝ := (constructionCoefficient : ℝ) * (24 : ℝ) ^ (5 / 3 : ℝ) * 4 ^ 5

theorem headlineConstant_pos : 0 < headlineConstant := by
  unfold headlineConstant constructionCoefficient
  positivity

theorem budget_le {n : ℕ} (hn : 1 ≤ n) :
    (budget n : ℝ) ≤ headlineConstant * (n : ℝ) ^ (5 / 3 : ℝ) * (sizeLog n : ℝ) ^ 5 := by
  have hb := coreBudget_le (Padded (Fin n))
  simp only [padded_card, Fintype.card_fin] at hb
  have hbR : (budget n : ℝ) ≤ (constructionCoefficient : ℝ) *
      (cubeRoot (3 * n) : ℝ) ^ 5 * (sizeLog (3 * n) : ℝ) ^ 5 := by
    exact_mod_cast hb
  have ht := padded_root_fifth_le hn
  have hlog : (sizeLog (3 * n) : ℝ) ≤ 4 * (sizeLog n : ℝ) := by
    exact_mod_cast sizeLog_padded_le hn
  calc
    _ ≤ (constructionCoefficient : ℝ) * (cubeRoot (3 * n) : ℝ) ^ 5 *
        (sizeLog (3 * n) : ℝ) ^ 5 := hbR
    _ ≤ (constructionCoefficient : ℝ) *
        ((24 : ℝ) ^ (5 / 3 : ℝ) * (n : ℝ) ^ (5 / 3 : ℝ)) * (4 * (sizeLog n : ℝ)) ^ 5 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hlog 5)
        (pow_nonneg (Nat.cast_nonneg _) _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    _ = _ := by unfold headlineConstant; ring

/-- Literal requested exponent and explicit logarithmic power. -/
theorem budget_bound : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    (budget n : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) *
      ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 5 :=
  ⟨headlineConstant, headlineConstant_pos, fun _ hn => budget_le (by omega)⟩

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.coreBudget_le
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.padded_root_fifth_le
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget_bound
