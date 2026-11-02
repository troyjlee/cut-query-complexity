import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Asymptotics

/-!
# Literal uniform deterministic five-thirds APMC contract

The budget and query-tree family are chosen before every hidden graph.
Correctness uses only the unit-weight promise. The public cap applies to
every real-valued transcript, and its explicit bound and little-o estimate
are conclusions of the construction.

This is the unrestricted five-thirds endpoint. It does not import the
separate degree-ratio research plan or strengthen its graph promises.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open AllPairs Filter Asymptotics
noncomputable section

/-- Both the original-graph shore and its value are exact for every
distinct ordered pair; there is no probability or error parameter. -/
theorem program_exact (n : ℕ) (G : WeightedGraph (Fin n))
    (hG : AllPairsAudit.Unweighted G) (s t : Fin n) (hst : s ≠ t) :
    IsSTMinCut G s t (((program n).eval G.cut) s t).shore ∧
      (((program n).eval G.cut) s t).value =
        G.cut (((program n).eval G.cut) s t).shore :=
  program_correct n G hG s t hst

/-- The displayed bound holds even when the answers are not cuts of any
graph. Honest-input correctness is a separate statement above. -/
theorem program_cost_bound (n : ℕ) (hn : 2 ≤ n) (read : Finset (Fin n) → ℝ) :
    ((program n).cost read : ℝ) ≤ headlineConstant * (n : ℝ) ^ (5 / 3 : ℝ) *
      ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 5 := by
  have hc : ((program n).cost read : ℝ) ≤ (budget n : ℝ) := by
    exact_mod_cast program_cost n read
  exact hc.trans (budget_le (by omega))

/-- Literal endpoint with the quantifier order exposing uniformity and
with every query bound proved, rather than supplied as a premise. -/
theorem deterministic_allPairs :
    ∃ (q : ℕ → ℕ)
      (P : (n : ℕ) → DTree (Finset (Fin n)) ℝ (Answers (Fin n)) (q n)),
      (∀ (n : ℕ) (G : WeightedGraph (Fin n)), AllPairsAudit.Unweighted G →
        allPairsGood G ((P n).eval G.cut)) ∧
      (∀ (n : ℕ) (read : Finset (Fin n) → ℝ), (P n).cost read ≤ q n) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        (q n : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) *
          ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 5) ∧
      ((fun n : ℕ => (q n : ℝ)) =o[atTop] fun n => (n : ℝ) ^ 2) := by
  exact ⟨budget, program, program_correct, program_cost, budget_bound,
    budget_isLittleO_square⟩

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_exact
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_cost_bound
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.deterministic_allPairs
