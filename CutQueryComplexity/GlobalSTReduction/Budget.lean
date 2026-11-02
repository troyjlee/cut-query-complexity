import CutQueryComplexity.GlobalSTReduction.Specification
import CutQueryComplexity.GHReduction.ThresholdProbability

/-! # Public budgets and the two target statements

All parameters depend only on the vertex count `n` and the confidence `b`:

* `trialCount n b = 8 (b+1) ⌈log₂(n+2)⌉` fresh sampling trials;
* each trial runs the levels `0, …, thresholdLevels n = ⌈log₂(2n)⌉`;
* one level costs at most `levelBudget n Q = (⌈log₂ n⌉ + 2) Q(n) + n`;
* `detGlobalBudget n b Q = 1 + trialCount · (levels + 1) · levelBudget`, the
  `1` paying for the singleton fallback query;
* at most `callCount n b = trialCount · (levels + 1) · (⌈log₂ n⌉ + n)` s-t calls;
* `repetitions n b = 1 + ⌈log₃(max 1 callCount · (n+2)^b)⌉` amplification
  rounds for a randomized family, whose charge is `amplifiedCost` (`r(Q k + k)`).

No budget depends on edge weights. `trialFailure_le` and `callFailure_le` are the
two numerical facts used by the endpoints. `DetGlobalTarget` and
`RandomGlobalTarget` are the statements to be proved.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical ENNReal
open Probability GHReduction GHReduction.Randomized

/-- Fresh sampling trials. -/
def trialCount (n b : ℕ) : ℕ := 8 * (b + 1) * Nat.clog 2 (n + 2)

/-- Query cost of one isolating level: binary separators, local calls, values. -/
def levelBudget (n : ℕ) (Q : ℕ → ℕ) : ℕ := (Nat.clog 2 n + 2) * Q n + n

/-- Query cost of all trials and levels after the fallback query. -/
def searchBudget (n b : ℕ) (Q : ℕ → ℕ) : ℕ :=
  trialCount n b * (thresholdLevels n + 1) * levelBudget n Q

/-- The cap with a deterministic s-t family. -/
def detGlobalBudget (n b : ℕ) (Q : ℕ → ℕ) : ℕ := 1 + searchBudget n b Q

/-- At most `⌈log₂ n⌉` separator calls and `n` local calls per level. -/
def callCount (n b : ℕ) : ℕ := trialCount n b * (thresholdLevels n + 1) * (Nat.clog 2 n + n)

/-- Amplification rounds for a randomized family. -/
def repetitions (n b : ℕ) : ℕ := 1 + Nat.clog 3 (max 1 (callCount n b) * (n + 2) ^ b)

/-- The cap with a randomized s-t family: the deterministic cap at the amplified charge. -/
def randomGlobalBudget (n b : ℕ) (Q : ℕ → ℕ) : ℕ :=
  detGlobalBudget n b (amplifiedCost (repetitions n b) Q)

/-- `(7/8)^8 ≤ 1/2`. -/
theorem seven_eighths_pow_eight_le : ((7 / 8 : ℝ)) ^ 8 ≤ 1 / 2 := by norm_num

theorem real_trialFailure_le (n b : ℕ) :
    ((7 / 8 : ℝ)) ^ trialCount n b ≤ (1 / ((n + 2 : ℕ) : ℝ)) ^ b := by
  set ℓ := Nat.clog 2 (n + 2)
  have hpow : ((n + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ℓ := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) (n + 2)
  have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hhalf : ((1 / 2 : ℝ)) ^ ℓ ≤ 1 / ((n + 2 : ℕ) : ℝ) := by
    rw [one_div_pow]
    exact one_div_le_one_div_of_le hpos hpow
  have hx : (0 : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) := by positivity
  have hx1 : 1 / ((n + 2 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hpos]
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  calc
    ((7 / 8 : ℝ)) ^ trialCount n b = (((7 / 8 : ℝ)) ^ 8) ^ ((b + 1) * ℓ) := by
      rw [← pow_mul]
      congr 1
      simp only [trialCount, ℓ]
      ring
    _ ≤ ((1 / 2 : ℝ)) ^ ((b + 1) * ℓ) :=
      pow_le_pow_left₀ (by positivity) seven_eighths_pow_eight_le _
    _ = (((1 / 2 : ℝ)) ^ ℓ) ^ (b + 1) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (1 / ((n + 2 : ℕ) : ℝ)) ^ (b + 1) := pow_le_pow_left₀ (by positivity) hhalf _
    _ ≤ (1 / ((n + 2 : ℕ) : ℝ)) ^ b := pow_le_pow_of_le_one hx hx1 (Nat.le_succ b)

/-- `(n+2)^{-b}` as an extended real. -/
theorem inv_pow_eq_ofReal (n b : ℕ) :
    (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b = ENNReal.ofReal ((1 / ((n + 2 : ℕ) : ℝ)) ^ b) := by
  rw [ENNReal.ofReal_pow (by positivity), one_div,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]

/-- All trials miss with probability at most `(n+2)^{-b}`. -/
theorem trialFailure_le (n b : ℕ) :
    ((7 / 8 : ℝ≥0∞)) ^ trialCount n b ≤ (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  have h78 : (7 / 8 : ℝ≥0∞) = ENNReal.ofReal (7 / 8) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  rw [h78, ← ENNReal.ofReal_pow (by norm_num), inv_pow_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal (real_trialFailure_le n b)

/-- `callCount · 3^{-repetitions} ≤ (n+2)^{-b}`. -/
theorem callFailure_le (n b : ℕ) :
    (callCount n b : ℝ≥0∞) * (3⁻¹ : ℝ≥0∞) ^ repetitions n b ≤ (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  set N := callCount n b
  set X := max 1 N * (n + 2) ^ b
  have hX : X ≤ 3 ^ Nat.clog 3 X := Nat.le_pow_clog (by norm_num) X
  have hNX : N * (n + 2) ^ b ≤ 3 ^ repetitions n b := by
    calc
      N * (n + 2) ^ b ≤ X := Nat.mul_le_mul_right _ (le_max_right 1 N)
      _ ≤ 3 ^ Nat.clog 3 X := hX
      _ ≤ 3 ^ repetitions n b := Nat.pow_le_pow_right (by norm_num) (by simp [repetitions, X, N])
  have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hreal : (N : ℝ) * ((1 / 3 : ℝ)) ^ repetitions n b ≤ (1 / ((n + 2 : ℕ) : ℝ)) ^ b := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ repetitions n b := by positivity
    have hcast : (N : ℝ) * ((n + 2 : ℕ) : ℝ) ^ b ≤ (3 : ℝ) ^ repetitions n b := by
      exact_mod_cast hNX
    rw [one_div_pow, one_div_pow, ← div_eq_mul_one_div, div_le_div_iff₀ h3 (by positivity)]
    linarith
  have hlhs : (N : ℝ≥0∞) * (3⁻¹ : ℝ≥0∞) ^ repetitions n b =
      ENNReal.ofReal ((N : ℝ) * ((1 / 3 : ℝ)) ^ repetitions n b) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  rw [hlhs, inv_pow_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The statement for a deterministic s-t family: one public randomized program
per `n` and `b`, built from the family before the hidden graph. Every run on
every oracle stays within `detGlobalBudget n b Q`; on every real-weighted graph
every output is a proper shore with its exact value, and the output fails to be
a global minimum cut with probability at most `(n+2)^{-b}`. -/
def DetGlobalTarget : Prop :=
  ∀ (n : ℕ) (Q : ℕ → ℕ), RealSTFamily Q → SizeRegular n Q → 2 ≤ n → ∀ b : ℕ,
    ∃ program : RTree (Finset (Fin n)) ℝ (Finset (Fin n) × ℝ) (detGlobalBudget n b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ detGlobalBudget n b Q) ∧
      (∀ G : WeightedGraph (Fin n), ∀ out ∈ (program.eval G.cut).support,
        ValidOutput G out) ∧
      ∀ G : WeightedGraph (Fin n),
        mass (program.eval G.cut) (fun out => ¬GlobalSuccess G out) ≤
          (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b

/-- The statement for a randomized s-t family, with failure `2 (n+2)^{-b}`. -/
def RandomGlobalTarget : Prop :=
  ∀ (n : ℕ) (Q : ℕ → ℕ), RandomRealSTFamily Q → SizeRegular n Q → 2 ≤ n → ∀ b : ℕ,
    ∃ program : RTree (Finset (Fin n)) ℝ (Finset (Fin n) × ℝ) (randomGlobalBudget n b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ randomGlobalBudget n b Q) ∧
      (∀ G : WeightedGraph (Fin n), ∀ out ∈ (program.eval G.cut).support,
        ValidOutput G out) ∧
      ∀ G : WeightedGraph (Fin n),
        mass (program.eval G.cut) (fun out => ¬GlobalSuccess G out) ≤
          2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b

end
end CutQueryComplexity.GlobalSTReduction
