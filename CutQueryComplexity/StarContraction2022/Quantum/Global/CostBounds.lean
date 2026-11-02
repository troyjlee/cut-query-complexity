import CutQueryComplexity.StarContraction2022.Quantum.Forest.CostBounds
import CutQueryComplexity.StarContraction2022.Quantum.Forest.LowCertificate
import CutQueryComplexity.StarContraction2022.Quantum.MinimumDegreeWitness
import CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Program

/-! # The concrete combined quantum schedule

The numerical sum charges the implemented minimum-degree witness, one low-cut
certificate at the public root threshold, and K verified high-cut trials.
Each verification and each physical product-query conversion is retained.
The coefficient depends only on the fixed repetition counts and tolerance,
not the number of vertices. No global program or global success is asserted.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds
noncomputable section
open ProductPrograms

/-- The exact native-query sum to be matched by the separate global execution. -/
def combinedQueries (n t K : ℕ) (eta : ℝ) : ℕ :=
  minimumDegreeWitnessQueries n t +
    12 * productBits n 1 *
      (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) +
    K * (12 * productBits n 1 * UniformStars.QH n)

/-- Explicit coefficient chosen using public fixed parameters before n. -/
def coefficient (t K : ℕ) (eta : ℝ) : ℝ :=
  819205 * (t : ℝ) + 70860 * (1 + Real.log (1 / eta)) ^ 2 + 600000000000 * (K : ℝ)

theorem coefficient_pos {t : ℕ} (ht : 1 ≤ t) (K : ℕ) (eta : ℝ) :
    0 < coefficient t K eta := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  unfold coefficient
  positivity

theorem one_le_sqrt {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  simpa only [Real.sqrt_one] using
    Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)

/-- The public ceiling supplies all low-branch rank premises. -/
theorem rootThreshold_parameters {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ rootThreshold n ∧ rootThreshold n ≤ n ∧
      Real.sqrt (n : ℝ) ≤ rootThreshold n ∧
      (rootThreshold n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  exact ⟨Nat.succ_le_of_lt (rootThreshold_pos (by omega)), rootThreshold_le_n n,
    sqrt_le_rootThreshold n, rootThreshold_le_two_sqrt (by omega)⟩

theorem splitTolerance_pos {n : ℕ} (hn : 2 ≤ n) {eta : ℝ} (heta : 0 < eta) :
    0 < eta / (rootThreshold n : ℝ) := by
  have hr : (0 : ℝ) < rootThreshold n := by
    exact_mod_cast (show 0 < rootThreshold n from (rootThreshold_parameters hn).1)
  exact div_pos heta hr

theorem splitTolerance_le_one {n : ℕ} (hn : 2 ≤ n) {eta : ℝ} (heta1 : eta ≤ 1) :
    eta / (rootThreshold n : ℝ) ≤ 1 := by
  have hr : (1 : ℝ) ≤ rootThreshold n := by exact_mod_cast (rootThreshold_parameters hn).1
  exact (div_le_iff₀ (by linarith : (0 : ℝ) < rootThreshold n)).mpr (by linarith)

/-- The additive one from the actual base-budget ceiling is explicit. -/
theorem minimumDegreeBaseBudget_le_sqrt_add_one (n : ℕ) :
    (minimumDegreeBaseBudget n : ℝ) ≤ 204800 * Real.sqrt (n : ℝ) + 1 := by
  have hcap : minimumDegreeBaseBudget n ≤ ⌈204800 * Real.sqrt (n : ℝ)⌉₊ := Nat.min_le_right _ _
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 204800 * Real.sqrt (n : ℝ))
  exact (Nat.cast_le.mpr hcap).trans hc.le

theorem minimumDegreeBaseBudget_le_sqrt {n : ℕ} (hn : 1 ≤ n) :
    (minimumDegreeBaseBudget n : ℝ) ≤ 204801 * Real.sqrt (n : ℝ) := by
  have hs := one_le_sqrt hn
  exact (minimumDegreeBaseBudget_le_sqrt_add_one n).trans (by linarith)

/-- Four physical calls per repeated base count, plus the actual singleton verification. -/
theorem minimumWitness_le_sqrt {n t : ℕ} (hn : 2 ≤ n) (ht : 1 ≤ t) :
    (minimumDegreeWitnessQueries n t : ℝ) ≤ 819205 * (t : ℝ) * Real.sqrt (n : ℝ) := by
  have hs := one_le_sqrt (show 1 ≤ n by omega)
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hts : (1 : ℝ) ≤ (t : ℝ) * Real.sqrt (n : ℝ) :=
    one_le_mul_of_one_le_of_one_le htR hs
  rw [minimumDegreeWitnessQueries_pos (by omega)]
  push_cast
  calc
    _ ≤ 4 * (t : ℝ) * (204801 * Real.sqrt (n : ℝ)) + 1 := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (minimumDegreeBaseBudget_le_sqrt (by omega)) (by positivity)) le_rfl
    _ ≤ _ := by nlinarith

theorem logWidth_power_five_ge_one (n : ℕ) : (1 : ℝ) ≤ (logWidth n : ℝ) ^ 5 := by
  simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (UniformStars.logWidth_ge_one n) 5

theorem logWidth_power_four_le_five (n : ℕ) :
    (logWidth n : ℝ) ^ 4 ≤ (logWidth n : ℝ) ^ 5 := by
  calc
    _ = (logWidth n : ℝ) ^ 4 * 1 := by ring
    _ ≤ (logWidth n : ℝ) ^ 4 * (logWidth n : ℝ) :=
      mul_le_mul_of_nonneg_left (UniformStars.logWidth_ge_one n) (by positivity)
    _ = _ := by ring

theorem minimumWitness_le_logWidth {n t : ℕ} (hn : 2 ≤ n) (ht : 1 ≤ t) :
    (minimumDegreeWitnessQueries n t : ℝ) ≤
      819205 * (t : ℝ) * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 := by
  apply (minimumWitness_le_sqrt hn ht).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (logWidth_power_five_ge_one n)
    (by positivity : 0 ≤ 819205 * (t : ℝ) * Real.sqrt (n : ℝ))

/-- Root-threshold substitution discharges the accepted forest estimate's rank premises. -/
theorem lowSchedule_le_logWidth {n : ℕ} (hn : 2 ≤ n) {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ((12 * productBits n 1 *
      (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) : ℕ) : ℝ) ≤
      (70860 * (1 + Real.log (1 / eta)) ^ 2) * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 :=
  Forest.forest_physical_budget_le_fixed_tolerance heta heta1 hn (rootThreshold_parameters hn).1 le_rfl

/-- The accepted high-trial physical estimate already includes its verified finish. -/
theorem highSchedule_le_logWidth {n : ℕ} (hn : 2 ≤ n) :
    ((12 * productBits n 1 * UniformStars.QH n : ℕ) : ℝ) ≤
      600000000000 * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 := by
  have h := UniformStars.highCandidate_physical_envelope hn
  rw [UniformStars.highCandidate_physical_length] at h
  exact h.trans (mul_le_mul_of_nonneg_left (logWidth_power_four_le_five n) (by positivity))

/-- Bound the exact three-part sum; no component cost envelope is a hypothesis. -/
theorem combinedQueries_le {n t : ℕ} (hn : 2 ≤ n) (ht : 1 ≤ t) (K : ℕ)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (combinedQueries n t K eta : ℝ) ≤
      coefficient t K eta * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 := by
  calc
    _ = (minimumDegreeWitnessQueries n t : ℝ) +
        ((12 * productBits n 1 *
          (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) : ℕ) : ℝ) +
        (K : ℝ) * ((12 * productBits n 1 * UniformStars.QH n : ℕ) : ℝ) := by
      simp only [combinedQueries, Nat.cast_add, Nat.cast_mul]
    _ ≤ 819205 * (t : ℝ) * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 +
        (70860 * (1 + Real.log (1 / eta)) ^ 2) * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 +
        (K : ℝ) * (600000000000 * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5) := by
      exact add_le_add (add_le_add (minimumWitness_le_logWidth hn ht)
        (lowSchedule_le_logWidth hn heta heta1))
        (mul_le_mul_of_nonneg_left (highSchedule_le_logWidth hn) (Nat.cast_nonneg K))
    _ = _ := by unfold coefficient; ring

/-- Literal expression for downstream matching against the separately implemented run. -/
theorem concreteSum_le {n t : ℕ} (hn : 2 ≤ n) (ht : 1 ≤ t) (K : ℕ)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ((minimumDegreeWitnessQueries n t +
      12 * productBits n 1 *
        (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) +
      K * (12 * productBits n 1 * UniformStars.QH n) : ℕ) : ℝ) ≤
      (819205 * (t : ℝ) + 70860 * (1 + Real.log (1 / eta)) ^ 2 + 600000000000 * (K : ℝ)) *
        Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 :=
  combinedQueries_le hn ht K heta heta1

/-- For each fixed t,K,eta one positive coefficient works for every input size. -/
theorem exists_combined_constant (t K : ℕ) (ht : 1 ≤ t) (eta : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ((minimumDegreeWitnessQueries n t +
        12 * productBits n 1 *
          (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) +
        K * (12 * productBits n 1 * UniformStars.QH n) : ℕ) : ℝ) ≤
        C * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 := by
  exact ⟨coefficient t K eta, coefficient_pos ht K eta,
    fun n hn => combinedQueries_le hn ht K heta heta1⟩

open scoped Classical
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

/-- This numerical sum is exactly the sum of the already accepted physical
routine lengths. It does not construct or assume a global composition. -/
theorem combinedQueries_eq_routine_lengths (n t K : ℕ) (eta : ℝ) (ht : 0 < t) :
    combinedQueries n t K eta =
      (minimumDegreeWitnessRoutine n t ht).len +
      (productTreeRoutine (Forest.lowCandidate n (rootThreshold n) eta)).len +
      K * (productTreeRoutine (UniformStars.highCandidate n)).len := by
  rw [Forest.lowCandidate_physical_length, UniformStars.highCandidate_physical_length]
  rfl

theorem routine_lengths_le {n t : ℕ} (hn : 2 ≤ n) (ht : 0 < t) (K : ℕ)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (((minimumDegreeWitnessRoutine n t ht).len +
      (productTreeRoutine (Forest.lowCandidate n (rootThreshold n) eta)).len +
      K * (productTreeRoutine (UniformStars.highCandidate n)).len : ℕ) : ℝ) ≤
      coefficient t K eta * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 := by
  rw [← combinedQueries_eq_routine_lengths]
  exact combinedQueries_le hn (by omega) K heta heta1

#print axioms coefficient_pos
#print axioms rootThreshold_parameters
#print axioms splitTolerance_pos
#print axioms splitTolerance_le_one
#print axioms minimumDegreeBaseBudget_le_sqrt_add_one
#print axioms minimumDegreeBaseBudget_le_sqrt
#print axioms minimumWitness_le_sqrt
#print axioms logWidth_power_five_ge_one
#print axioms logWidth_power_four_le_five
#print axioms minimumWitness_le_logWidth
#print axioms lowSchedule_le_logWidth
#print axioms highSchedule_le_logWidth
#print axioms combinedQueries_le
#print axioms concreteSum_le
#print axioms exists_combined_constant
#print axioms combinedQueries_eq_routine_lengths
#print axioms routine_lengths_le

end
end CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds
