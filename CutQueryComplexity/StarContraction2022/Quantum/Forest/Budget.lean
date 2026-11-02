import CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Basic
import CutQueryComplexity.StarContraction2022.Quantum.Forest.Isolation

/-! # Public schedules for residual row recovery

The schedules are the logarithmic ceilings in the reviewed forest plan.
They are total public functions, including n = 0 and invalid tolerances.
The estimates here are numerical facts; the actual recovery law is proved
separately for the finite query program in Recover.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest
noncomputable section
open scoped Classical ENNReal

def rowTrials (n : ℕ) (eta : ℝ) : ℕ :=
  ⌈Real.log (8 * (n : ℝ) ^ 2 / eta) / Real.log (8 / 7 : ℝ)⌉₊

def forestRounds (n : ℕ) (eta : ℝ) : ℕ :=
  ⌈Real.log (2 * (n : ℝ) / eta) / Real.log (4 / 3 : ℝ)⌉₊

def recoverBudget (n : ℕ) (eta : ℝ) : ℕ :=
  ProductPrograms.logWidth n * rowTrials n eta * (ProductPrograms.logWidth n + 1)

def forestBudget (n : ℕ) (eta : ℝ) : ℕ :=
  forestRounds n eta * recoverBudget n eta

theorem recoverBudget_eq (n : ℕ) (eta : ℝ) :
    recoverBudget n eta = ProductPrograms.logWidth n * rowTrials n eta *
      (ProductPrograms.logWidth n + 1) := rfl

theorem forestBudget_eq (n : ℕ) (eta : ℝ) :
    forestBudget n eta = forestRounds n eta * ProductPrograms.logWidth n *
      rowTrials n eta * (ProductPrograms.logWidth n + 1) := by
  simp only [forestBudget, recoverBudget, Nat.mul_assoc]

/-- A logarithmic ceiling gives its geometric tail, without a probabilistic
premise. The statement also covers x < 1, where the ceiling may be zero. -/
theorem inverse_pow_ceil_log_le (a x : ℝ) (ha : 1 < a) (hx : 0 < x) :
    (a⁻¹) ^ ⌈Real.log x / Real.log a⌉₊ ≤ x⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hlog : 0 < Real.log a := Real.log_pos ha
  have hk := (div_le_iff₀ hlog).mp
    (Nat.le_ceil (Real.log x / Real.log a))
  calc
    _ = Real.exp ((⌈Real.log x / Real.log a⌉₊ : ℝ) * Real.log a⁻¹) := by
      rw [Real.exp_nat_mul, Real.exp_log (inv_pos.mpr ha0)]
    _ ≤ Real.exp (-Real.log x) := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_inv]
      nlinarith
    _ = x⁻¹ := by rw [Real.exp_neg, Real.exp_log hx]

theorem rowTrials_tail {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : 0 < eta) :
    (7 / 8 : ℝ) ^ rowTrials n eta ≤ eta / (8 * (n : ℝ) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := inverse_pow_ceil_log_le (8 / 7 : ℝ) (8 * (n : ℝ) ^ 2 / eta)
    (by norm_num) (by positivity)
  norm_num only [inv_div] at h
  simpa only [rowTrials] using h

theorem rowTrials_tail_ennreal {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : 0 < eta) :
    (7 / 8 : ℝ≥0∞) ^ rowTrials n eta ≤ ENNReal.ofReal (eta / (8 * (n : ℝ) ^ 2)) := by
  have h := ENNReal.ofReal_le_ofReal (rowTrials_tail hn heta)
  simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 7 / 8),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8), ENNReal.ofReal_ofNat] using h

theorem rowTrials_union_error {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : 0 < eta) :
    (n : ℝ≥0∞) * (7 / 8 : ℝ≥0∞) ^ rowTrials n eta ≤
      ENNReal.ofReal (eta / (8 * (n : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (n : ℝ≥0∞) * ENNReal.ofReal (eta / (8 * (n : ℝ) ^ 2)) :=
      mul_le_mul le_rfl (rowTrials_tail_ennreal hn heta) (by positivity) (by positivity)
    _ = ENNReal.ofReal ((n : ℝ) * (eta / (8 * (n : ℝ) ^ 2))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ = _ := by congr 1; field_simp

theorem forestRounds_tail {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : 0 < eta) :
    (3 / 4 : ℝ) ^ forestRounds n eta ≤ eta / (2 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := inverse_pow_ceil_log_le (4 / 3 : ℝ) (2 * (n : ℝ) / eta)
    (by norm_num) (by positivity)
  norm_num only [inv_div] at h
  simpa only [forestRounds] using h

theorem forestRounds_deficit_tail {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : 0 < eta) :
    (n : ℝ) * (3 / 4 : ℝ) ^ forestRounds n eta ≤ eta / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (n : ℝ) * (eta / (2 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (forestRounds_tail hn heta) hnR.le
    _ = eta / 2 := by field_simp

#print axioms recoverBudget_eq
#print axioms forestBudget_eq
#print axioms inverse_pow_ceil_log_le
#print axioms rowTrials_tail
#print axioms rowTrials_tail_ennreal
#print axioms rowTrials_union_error
#print axioms forestRounds_tail
#print axioms forestRounds_deficit_tail

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
