import CutQueryComplexity.GHReduction.Main
import CutQueryComplexity.GHReduction.Randomized.Family
import CutQueryComplexity.AllPairsAudit.CutAlgebra

/-! # Target: the Gomory-Hu reduction with a randomized s-t primitive

The statement is fixed here before its proof. `RandomizedGHTarget` is the
randomized analogue of `exists_weighted_gh_reduction`: one public randomized
program, built from a `RandomCanonicalSTFamily`, returns a Gomory-Hu tree of
every graph with integral weights of total at most `M`.
`UnweightedAllPairsTarget` is its specialization to all-pairs minimum cuts of
unweighted graphs, where the family is called on weighted contractions with
edge weights at most `n * n`. `RandomizedGHTarget → UnweightedAllPairsTarget`
is proved below.

The family is amplified to `amplificationRounds n M b Q` repetitions. The
budget is the deterministic budget at the amplified cost. The arithmetic that
makes this choice work is also proved here: `3^{-r}` times the budget is at most
`(n+2)^{-b}`, so a union bound over the calls adds at most that much failure.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability

attribute [local irreducible] RTree

/-- Number of repetitions of the s-t family. With `x = ⌈log₃((n+2)^b q₁)⌉`,
where `q₁` is the budget for a single repetition, `r = 2x + 2` satisfies
`3^r ≥ r q₁ (n+2)^b`. -/
def amplificationRounds (n M b : ℕ) (Q : ℕ → ℕ) : ℕ :=
  2 * Nat.clog 3 ((n + 2) ^ b * weightedGHBudget n M b (amplifiedCost 1 Q)) + 2

/-- The deterministic budget at the amplified cost. -/
def randomizedGHBudget (n M b : ℕ) (Q : ℕ → ℕ) : ℕ :=
  weightedGHBudget n M b (amplifiedCost (amplificationRounds n M b Q) Q)

/-- The randomized relative reduction. -/
def RandomizedGHTarget : Prop :=
  ∀ (n M : ℕ) (Q : ℕ → ℕ), RandomCanonicalSTFamily M Q → SizeRegular n Q → 2 ≤ n →
    ∀ b : ℕ, ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n)))
        (randomizedGHBudget n M b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support,
        out.2 ≤ randomizedGHBudget n M b Q) ∧
      ∀ G : WeightedGraph (Fin n), InputPromise M G →
        mass (program.eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
          2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b

/-- Randomized all-pairs minimum cuts of unweighted graphs from a randomized
canonical s-t family on weighted graphs. -/
def UnweightedAllPairsTarget : Prop :=
  ∀ (n : ℕ) (Q : ℕ → ℕ), RandomCanonicalSTFamily (n * n) Q → SizeRegular n Q → 2 ≤ n →
    ∀ b : ℕ, ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n)))
        (randomizedGHBudget n (n * n) b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support,
        out.2 ≤ randomizedGHBudget n (n * n) b Q) ∧
      ∀ G : WeightedGraph (Fin n), AllPairsAudit.Unweighted G →
        mass (program.eval G.cut) (fun output => ¬AllPairsTreeSuccess G output) ≤
          2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b

/-- An unweighted graph on `n` vertices is integral with total weight at most `n * n`. -/
theorem inputPromise_of_unweighted {n : ℕ} (G : WeightedGraph (Fin n))
    (hG : AllPairsAudit.Unweighted G) : InputPromise (n * n) G := by
  refine ⟨fun u v => ?_, ?_⟩
  · rcases hG u v with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  · have hle : ∑ u : Fin n, ∑ v : Fin n, G.w u v ≤ ∑ _u : Fin n, ∑ _v : Fin n, (1 : ℝ) :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
        rcases hG u v with h | h <;> simp [h]
    have hnonneg : 0 ≤ ∑ u : Fin n, ∑ v : Fin n, G.w u v :=
      Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => G.nonneg u v
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hle
    rw [edgeMass]
    push_cast
    linarith

theorem unweightedAllPairs_of_randomizedGH (h : RandomizedGHTarget) :
    UnweightedAllPairsTarget := by
  intro n Q family hQ hn b
  obtain ⟨program, hcost, hfail⟩ := h n (n * n) Q family hQ hn b
  refine ⟨program, hcost, fun G hG => ?_⟩
  refine le_trans (mass_mono _ ?_) (hfail G (inputPromise_of_unweighted G hG))
  intro output hbad hgood
  exact hbad (hgood.allPairs G)

/-! ## Arithmetic of the amplification count -/

/-- More repetitions cost proportionally more. -/
theorem weightedGHBudget_amplified_le (n M b : ℕ) (Q : ℕ → ℕ) {r : ℕ} (hr : 1 ≤ r) :
    weightedGHBudget n M b (amplifiedCost r Q) ≤
      r * weightedGHBudget n M b (amplifiedCost 1 Q) := by
  simp only [weightedGHBudget, amplifiedCost, one_mul]
  have hn : n + r * (Q n + n) ≤ r * (n + (Q n + n)) := by nlinarith
  calc
    reductionPolynomialConstant b * (n + r * (Q n + n)) * (1 + Nat.clog 2 (n + M + 2)) ^ 22 ≤
        reductionPolynomialConstant b * (r * (n + (Q n + n))) *
          (1 + Nat.clog 2 (n + M + 2)) ^ 22 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
    _ = r * (reductionPolynomialConstant b * (n + (Q n + n)) *
          (1 + Nat.clog 2 (n + M + 2)) ^ 22) := by ring

/-- `3^r` exceeds `(n+2)^b` times the randomized budget. -/
theorem randomizedGHBudget_mul_le (n M b : ℕ) (Q : ℕ → ℕ) :
    (n + 2) ^ b * randomizedGHBudget n M b Q ≤ 3 ^ amplificationRounds n M b Q := by
  set q₁ := weightedGHBudget n M b (amplifiedCost 1 Q)
  set x := Nat.clog 3 ((n + 2) ^ b * q₁)
  have hX : (n + 2) ^ b * q₁ ≤ 3 ^ x := Nat.le_pow_clog (by norm_num) _
  have hx : x < 3 ^ x := Nat.lt_pow_self (by norm_num)
  have hr : amplificationRounds n M b Q = 2 * x + 2 := rfl
  have hbudget : randomizedGHBudget n M b Q ≤ (2 * x + 2) * q₁ := by
    rw [randomizedGHBudget, hr]
    exact weightedGHBudget_amplified_le n M b Q (by omega)
  calc
    (n + 2) ^ b * randomizedGHBudget n M b Q ≤ (n + 2) ^ b * ((2 * x + 2) * q₁) :=
      Nat.mul_le_mul_left _ hbudget
    _ = (2 * x + 2) * ((n + 2) ^ b * q₁) := by ring
    _ ≤ 3 ^ (x + 2) * 3 ^ x := by
      apply Nat.mul_le_mul _ hX
      rw [pow_add]
      omega
    _ = 3 ^ amplificationRounds n M b Q := by
      rw [hr, ← pow_add]
      ring_nf

/-- The union bound over the calls adds at most `(n+2)^{-b}`. -/
theorem amplification_slack (n M b : ℕ) (Q : ℕ → ℕ) :
    (3⁻¹ : ℝ≥0∞) ^ amplificationRounds n M b Q * (randomizedGHBudget n M b Q : ℝ≥0∞) ≤
      (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  set r := amplificationRounds n M b Q
  set B := randomizedGHBudget n M b Q
  have hnat : ((n + 2) ^ b * B : ℕ) ≤ 3 ^ r := randomizedGHBudget_mul_le n M b Q
  have hcast : (((n + 2 : ℕ) : ℝ≥0∞)) ^ b * (B : ℝ≥0∞) ≤ (3 : ℝ≥0∞) ^ r := by
    exact_mod_cast hnat
  have hpos : (((n + 2 : ℕ) : ℝ≥0∞)) ^ b ≠ 0 := pow_ne_zero _ (by simp)
  have hfin : (((n + 2 : ℕ) : ℝ≥0∞)) ^ b ≠ ∞ := ENNReal.pow_ne_top (by simp)
  have h3 : (3⁻¹ : ℝ≥0∞) ^ r * (3 : ℝ≥0∞) ^ r = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  calc
    (3⁻¹ : ℝ≥0∞) ^ r * (B : ℝ≥0∞) =
        (3⁻¹ : ℝ≥0∞) ^ r * ((((n + 2 : ℕ) : ℝ≥0∞)) ^ b * (B : ℝ≥0∞)) *
          ((((n + 2 : ℕ) : ℝ≥0∞)) ^ b)⁻¹ := by
      rw [mul_comm ((((n + 2 : ℕ) : ℝ≥0∞)) ^ b), mul_assoc, mul_assoc,
        ENNReal.mul_inv_cancel hpos hfin, mul_one]
    _ ≤ (3⁻¹ : ℝ≥0∞) ^ r * (3 : ℝ≥0∞) ^ r * ((((n + 2 : ℕ) : ℝ≥0∞)) ^ b)⁻¹ := by
      gcongr
    _ = (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by rw [h3, one_mul, ENNReal.inv_pow]

end
end CutQueryComplexity.GHReduction.Randomized
