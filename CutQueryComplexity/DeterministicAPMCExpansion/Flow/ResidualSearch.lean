import CutQueryComplexity.DeterministicAPMCExpansion.Flow.Network
import CutQueryComplexity.Primitive.BinarySearch

/-!
# Actual residual neighbor search for the symmetric two-star network

The program is defined even for inconsistent real answers. Nonnegative row
entries and the zero diagonal are correctness invariants, not program inputs.
Its budget is `3 * (clog₂(card V + 2) + 1)` internal-graph queries.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset WeightedGraph AllPairsAudit Certificate DirectedCertificate
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Erasing the row vertex makes every rectangle query legal. Feasible
residuals have zero diagonal, so this does not change their row sum. -/
def residualRowQuery (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (u : NetworkVertex V)
    (U : Finset (NetworkVertex V)) : DTree (Finset V) ℝ ℝ 3 :=
  residualRectangleQuery a z f {u} (U.erase u)

theorem residualRowQuery_eval (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (u : NetworkVertex V)
    (U : Finset (NetworkVertex V)) :
    (residualRowQuery a z f u U).eval G.cut = subsetSum (residualEntry G a z f u) U := by
  have hdisj : Disjoint ({u} : Finset (NetworkVertex V)) (U.erase u) := by simp
  rw [residualRowQuery, residual_rectangle_query G a z f hdisj, sum_singleton]
  unfold subsetSum
  by_cases hu : u ∈ U
  · have h := sum_erase_add U (residualEntry G a z f u) hu
    simpa only [residual_diagonal hf, add_zero] using h
  · rw [erase_eq_of_notMem hu]

def neighborBudget (V : Type) [Fintype V] : ℕ :=
  (searchDepth (NetworkVertex V) + 1) * 3

/-- Public signed flow and terminal stars are the only non-oracle inputs. -/
def residualNeighbor (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (u : NetworkVertex V)
    (U : Finset (NetworkVertex V)) :
    DTree (Finset V) ℝ (Option (NetworkVertex V)) (neighborBudget V) :=
  (findPositive (searchDepth (NetworkVertex V)) U).substitute (residualRowQuery a z f u)

theorem residualNeighbor_correct (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) (u : NetworkVertex V)
    (U : Finset (NetworkVertex V)) :
    PositiveResult (residualEntry G a z f u) U
      ((residualNeighbor a z f u U).eval G.cut) := by
  have hread : (fun S => (residualRowQuery a z f u S).eval G.cut) =
      subsetSum (residualEntry G a z f u) :=
    funext (residualRowQuery_eval G a z f hf u)
  have he : (residualNeighbor a z f u U).eval G.cut =
      (findPositive (searchDepth (NetworkVertex V)) U).eval
        (fun S => (residualRowQuery a z f u S).eval G.cut) :=
    DTree.eval_substitute (q := searchDepth (NetworkVertex V) + 1) (k := 3)
      (residualRowQuery a z f u) (findPositive (searchDepth (NetworkVertex V)) U) G.cut
  rw [hread] at he
  rw [he]
  exact findPositive_correct _ (fun v => residual_nonneg hf u v) _ U
    (card_le_pow_searchDepth U)

theorem residualNeighbor_cost (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (u : NetworkVertex V)
    (U : Finset (NetworkVertex V)) (oracle : Finset V → ℝ) :
    (residualNeighbor a z f u U).cost oracle ≤ neighborBudget V := DTree.cost_le _ _

theorem neighborBudget_eq : neighborBudget V =
    (Nat.clog 2 (Fintype.card V + 2) + 1) * 3 := by
  simp only [neighborBudget, searchDepth, network_card]

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.residualNeighbor_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.residualNeighbor_cost
