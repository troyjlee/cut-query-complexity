import CutQueryComplexity.StarContraction2022.Quantum.Forest.Budget
import CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Basic
import CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Budget

/-! # Explicit numerical bounds for the public forest schedules

These inequalities bound the existing total schedules, including both natural
ceilings, the tolerance eta/r, the product-oracle conversion and the final one
query for value verification. They assert no forest execution or success law.
All estimates use n >= 2 and 0 < eta <= 1; the schedule definitions are unchanged.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest
noncomputable section

private theorem tolerance_log_nonneg {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    0 ≤ Real.log (1 / eta) :=
  Real.log_nonneg ((le_div_iff₀ heta).mpr (by simpa using heta1))

private theorem log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

private theorem log_eight_le_three : Real.log (8 : ℝ) ≤ 3 := by
  have h : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_ofNat] using
      (Real.log_pow (2 : ℝ) 3)
  linarith [log_two_le_one]

private theorem row_log_denominator : (1 / 8 : ℝ) ≤ Real.log (8 / 7 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 8 / 7)
  norm_num at h
  exact h

private theorem round_log_denominator : (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  norm_num at h
  exact h

/-- The additive one from the actual row-trial ceiling is included. -/
theorem rowTrials_le_logWidth {n : ℕ} (hn : 2 ≤ n) {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (rowTrials n eta : ℝ) ≤
      41 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL := UniformStars.logWidth_ge_one n
  have ht := tolerance_log_nonneg heta heta1
  have hlogn := UniformStars.log_n_le_logWidth hn
  have hnum : Real.log (8 * (n : ℝ) ^ 2 / eta) ≤
      5 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) := by
    rw [Real.log_div (by positivity) (ne_of_gt heta),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    simp only [one_div, Real.log_inv]
    norm_num only [Nat.cast_ofNat]
    have ht' : 0 ≤ -Real.log eta := by simpa only [one_div, Real.log_inv] using ht
    linarith [log_eight_le_three]
  have hnum0 : 0 ≤ Real.log (8 * (n : ℝ) ^ 2 / eta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ heta).mpr
    nlinarith
  have hden : 0 < Real.log (8 / 7 : ℝ) := by linarith [row_log_denominator]
  have hratio : Real.log (8 * (n : ℝ) ^ 2 / eta) / Real.log (8 / 7 : ℝ) ≤
      40 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) := by
    apply (div_le_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_left row_log_denominator
      (by positivity : 0 ≤ 40 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)))
    nlinarith
  have hc := Nat.ceil_lt_add_one (div_nonneg hnum0 hden.le)
  change (⌈Real.log (8 * (n : ℝ) ^ 2 / eta) / Real.log (8 / 7 : ℝ)⌉₊ : ℝ) ≤ _
  linarith

/-- The additive one from the actual forest-round ceiling is included. -/
theorem forestRounds_le_logWidth {n : ℕ} (hn : 2 ≤ n) {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (forestRounds n eta : ℝ) ≤
      9 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL := UniformStars.logWidth_ge_one n
  have ht := tolerance_log_nonneg heta heta1
  have hlogn := UniformStars.log_n_le_logWidth hn
  have hnum : Real.log (2 * (n : ℝ) / eta) ≤
      2 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) := by
    rw [Real.log_div (by positivity) (ne_of_gt heta),
      Real.log_mul (by norm_num) (ne_of_gt hn0)]
    simp only [one_div, Real.log_inv]
    have ht' : 0 ≤ -Real.log eta := by simpa only [one_div, Real.log_inv] using ht
    linarith [log_two_le_one]
  have hnum0 : 0 ≤ Real.log (2 * (n : ℝ) / eta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ heta).mpr
    nlinarith
  have hden : 0 < Real.log (4 / 3 : ℝ) := by linarith [round_log_denominator]
  have hratio : Real.log (2 * (n : ℝ) / eta) / Real.log (4 / 3 : ℝ) ≤
      8 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) := by
    apply (div_le_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_left round_log_denominator
      (by positivity : 0 ≤ 8 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)))
    nlinarith
  have hc := Nat.ceil_lt_add_one (div_nonneg hnum0 hden.le)
  change (⌈Real.log (2 * (n : ℝ) / eta) / Real.log (4 / 3 : ℝ)⌉₊ : ℝ) ≤ _
  linarith

/-- One recovery call uses all L masks and its total-count query. -/
theorem recoverBudget_le_logWidth {n : ℕ} (hn : 2 ≤ n) {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (recoverBudget n eta : ℝ) ≤
      82 * (ProductPrograms.logWidth n : ℝ) ^ 2 *
        ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) := by
  have hL := UniformStars.logWidth_ge_one n
  have ht := tolerance_log_nonneg heta heta1
  have hr := rowTrials_le_logWidth hn heta heta1
  calc
    (recoverBudget n eta : ℝ) =
        (ProductPrograms.logWidth n : ℝ) * (rowTrials n eta : ℝ) *
          ((ProductPrograms.logWidth n : ℝ) + 1) := by
      simp only [recoverBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    _ ≤ (ProductPrograms.logWidth n : ℝ) *
        (41 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta))) *
        (2 * (ProductPrograms.logWidth n : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
      · linarith
      · positivity
      · positivity
    _ = _ := by ring

/-- Both actual ceilings and every per-round recovery query are charged. -/
theorem forestBudget_le_logWidth {n : ℕ} (hn : 2 ≤ n) {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (forestBudget n eta : ℝ) ≤
      738 * (ProductPrograms.logWidth n : ℝ) ^ 2 *
        ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 := by
  have ht := tolerance_log_nonneg heta heta1
  calc
    (forestBudget n eta : ℝ) =
        (forestRounds n eta : ℝ) * (recoverBudget n eta : ℝ) := by
      simp only [forestBudget, Nat.cast_mul]
    _ ≤ (9 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta))) *
        (82 * (ProductPrograms.logWidth n : ℝ) ^ 2 *
          ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta))) :=
      mul_le_mul (forestRounds_le_logWidth hn heta heta1)
        (recoverBudget_le_logWidth hn heta heta1) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- Splitting the tolerance among r <= n calls costs one further log n. -/
theorem split_tolerance_log_le {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n)
    {eta : ℝ} (heta : 0 < eta) :
    Real.log (1 / (eta / (r : ℝ))) ≤
      (ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrnR : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have heq : 1 / (eta / (r : ℝ)) = (r : ℝ) * (1 / eta) := by field_simp
  rw [heq, Real.log_mul (ne_of_gt hr0) (by positivity)]
  exact add_le_add ((Real.log_le_log hr0 hrnR).trans
    (UniformStars.log_n_le_logWidth hn)) le_rfl

/-- The bound for the exact public eta/r schedule, uniform in r <= n. -/
theorem forestBudget_split_le_logWidth {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n) {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (forestBudget n (eta / (r : ℝ)) : ℝ) ≤
      2952 * (ProductPrograms.logWidth n : ℝ) ^ 2 *
        ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hsplit0 : 0 < eta / (r : ℝ) := div_pos heta hr0
  have hsplit1 : eta / (r : ℝ) ≤ 1 := (div_le_iff₀ hr0).mpr (by linarith)
  have ht := tolerance_log_nonneg heta heta1
  have hs := tolerance_log_nonneg hsplit0 hsplit1
  have hlog := split_tolerance_log_le hn hr hrn heta
  have hsum : (ProductPrograms.logWidth n : ℝ) + Real.log (1 / (eta / (r : ℝ))) ≤
      2 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) := by linarith
  calc
    _ ≤ 738 * (ProductPrograms.logWidth n : ℝ) ^ 2 *
        ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / (eta / (r : ℝ)))) ^ 2 :=
      forestBudget_le_logWidth hn hsplit0 hsplit1
    _ ≤ 738 * (ProductPrograms.logWidth n : ℝ) ^ 2 *
        (2 * ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta))) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hsum 2
    _ = _ := by ring

/-- The final +1 value-verification query is part of this natural budget. -/
theorem repeated_forestBudget_add_one_le {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hrroot : r ≤ ProductPrograms.rootThreshold n) {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ((r * forestBudget n (eta / (r : ℝ)) + 1 : ℕ) : ℝ) ≤
      5905 * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 2 *
        ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 := by
  have ht := tolerance_log_nonneg heta heta1
  have hL := UniformStars.logWidth_ge_one n
  have hA : 1 ≤ (ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta) := by linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))
  have hrbound : (r : ℝ) ≤ 2 * Real.sqrt (n : ℝ) :=
    (by exact_mod_cast hrroot : (r : ℝ) ≤ ProductPrograms.rootThreshold n).trans
      (ProductPrograms.rootThreshold_le_two_sqrt (by omega))
  have hf := forestBudget_split_le_logWidth hn hr
    (hrroot.trans (ProductPrograms.rootThreshold_le_n n)) heta heta1
  have hone : 1 ≤ Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 2 *
      ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 := by
    have hL2 : (1 : ℝ) ≤ (ProductPrograms.logWidth n : ℝ) ^ 2 := by nlinarith
    have hA2 : (1 : ℝ) ≤ ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 :=
      by nlinarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hsqrt hL2) hA2
  calc
    _ = (r : ℝ) * (forestBudget n (eta / (r : ℝ)) : ℝ) + 1 := by push_cast; rfl
    _ ≤ (2 * Real.sqrt (n : ℝ)) *
        (2952 * (ProductPrograms.logWidth n : ℝ) ^ 2 *
          ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2) + 1 := by
      exact add_le_add (mul_le_mul hrbound hf (Nat.cast_nonneg _) (by positivity)) le_rfl
    _ ≤ _ := by nlinarith

/-- Explicit universal physical cost bound, including compute/copy/uncompute
and the final verification. This is a numerical statement about the schedule. -/
theorem forest_physical_budget_le {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hrroot : r ≤ ProductPrograms.rootThreshold n) {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ((12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1) : ℕ) : ℝ) ≤
      70860 * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 3 *
        ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 := by
  have ht := tolerance_log_nonneg heta heta1
  have hbits : (productBits n 1 : ℝ) ≤ ProductPrograms.logWidth n := by
    exact_mod_cast ProductPrograms.productBits_le_logWidth n
  calc
    _ = 12 * (productBits n 1 : ℝ) *
        ((r * forestBudget n (eta / (r : ℝ)) + 1 : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (12 * (ProductPrograms.logWidth n : ℝ)) *
        (5905 * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 2 *
          ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbits (by norm_num))
        (repeated_forestBudget_add_one_le hn hr hrroot heta heta1)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- The positive constant is chosen before all size, rank and tolerance inputs. -/
theorem exists_forest_physical_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (n r : ℕ), 2 ≤ n → 1 ≤ r →
      r ≤ ProductPrograms.rootThreshold n → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ((12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1) : ℕ) : ℝ) ≤
        C * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 3 *
          ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 := by
  refine ⟨70860, by norm_num, ?_⟩
  intro n r hn hr hrroot eta heta heta1
  exact forest_physical_budget_le hn hr hrroot heta heta1

/-- For each fixed admissible tolerance the coefficient is independent of n,r,
and the numerical bound has the advertised sqrt(n) * L^5 form. -/
theorem forest_physical_budget_le_fixed_tolerance {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hrroot : r ≤ ProductPrograms.rootThreshold n) :
    ((12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1) : ℕ) : ℝ) ≤
      (70860 * (1 + Real.log (1 / eta)) ^ 2) * Real.sqrt (n : ℝ) *
        (ProductPrograms.logWidth n : ℝ) ^ 5 := by
  have ht := tolerance_log_nonneg heta heta1
  have hL := UniformStars.logWidth_ge_one n
  have hsum : (ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta) ≤
      (ProductPrograms.logWidth n : ℝ) * (1 + Real.log (1 / eta)) := by nlinarith
  calc
    _ ≤ 70860 * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 3 *
        ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 :=
      forest_physical_budget_le hn hr hrroot heta heta1
    _ ≤ 70860 * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 3 *
        ((ProductPrograms.logWidth n : ℝ) * (1 + Real.log (1 / eta))) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hsum 2
    _ = _ := by ring

theorem exists_fixed_tolerance_forest_constant {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n r : ℕ), 2 ≤ n → 1 ≤ r →
      r ≤ ProductPrograms.rootThreshold n →
      ((12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1) : ℕ) : ℝ) ≤
        C * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 5 := by
  have ht := tolerance_log_nonneg heta heta1
  refine ⟨70860 * (1 + Real.log (1 / eta)) ^ 2, by positivity, ?_⟩
  intro n r hn hr hrroot
  exact forest_physical_budget_le_fixed_tolerance heta heta1 hn hr hrroot

#print axioms rowTrials_le_logWidth
#print axioms forestRounds_le_logWidth
#print axioms recoverBudget_le_logWidth
#print axioms forestBudget_le_logWidth
#print axioms split_tolerance_log_le
#print axioms forestBudget_split_le_logWidth
#print axioms repeated_forestBudget_add_one_le
#print axioms forest_physical_budget_le
#print axioms exists_forest_physical_constant
#print axioms forest_physical_budget_le_fixed_tolerance
#print axioms exists_fixed_tolerance_forest_constant

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
