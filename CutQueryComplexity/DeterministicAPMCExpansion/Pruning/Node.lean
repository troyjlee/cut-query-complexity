import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds
import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.LocalParameters
import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Solver

/-!
# Execute one active decomposition node

The public matching game runs its actual unit-capacity flows. A failed game
returns a split immediately. A completed game constructs the fake degree
table from its recorded rounds and feeds that table to one exact pruning
flow. No hidden graph, fake certificate, flow solution, or query-cost proof
is an input to this program.

The remaining premises in the correctness theorem are public numeric
parameter conditions. The recursive caller must establish them from the
global parameters and the actual part cardinality.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open Finset Flow CutMatching AllPairsAudit ActualRounds
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem even_clone (t : ℕ) : Even (Fintype.card (Clone V (2 * t))) := by
  refine ⟨Fintype.card V * t, ?_⟩
  simp only [Clone, Fintype.card_prod, Fintype.card_fin]
  ring

def fakeDegrees {b : ℕ} (rounds : List (RoutedRound V b)) : V → ℕ :=
  FakeEdges.degreeTable (markedHistory rounds)

theorem sum_fakeDegrees {b : ℕ} (rounds : List (RoutedRound V b)) :
    (∑ v, fakeDegrees rounds v) = 2 * FakeEdges.edgeCount (markedHistory rounds) := by
  have h := FakeEdges.sum_degrees (markedHistory rounds)
  simp only [FakeEdges.fakeGraph_degree] at h
  exact_mod_cast h

theorem completed_edge_budget (G : WeightedGraph V) (hG : Unweighted G)
    (R t : ℕ) (ht : 1 ≤ t) (hV : 0 < Fintype.card V)
    (hrounds : normalizedRounds (Fintype.card (Clone V (2 * t))) ≤ R)
    (out : BalancedResult (Clone V (2 * t))) (rounds : List (RoutedRound V (2 * t)))
    (hexec : (executedCutPlayer (localTolerance (Fintype.card V) R : ℝ)
      (even_clone (V := V) t)).eval G.cut = .complete out rounds) :
    32 * FakeEdges.edgeCount (markedHistory rounds) ≤ Fintype.card V * (2 * t) := by
  have hc := completed_certificate G hG (localTolerance (Fintype.card V) R) R
    (by omega : 0 < 2 * t) hV (even_clone (V := V) t) hrounds out rounds hexec
  calc
    32 * FakeEdges.edgeCount (markedHistory rounds) ≤
        32 * (R * localTolerance (Fintype.card V) R * (2 * t)) :=
      Nat.mul_le_mul_left 32 hc.2.1
    _ = (32 * R * localTolerance (Fintype.card V) R) * (2 * t) := by ring
    _ ≤ Fintype.card V * (2 * t) :=
      Nat.mul_le_mul_right (2 * t) (localTolerance_budget (Fintype.card V) R)

theorem completed_source_cap (G : WeightedGraph V) (hG : Unweighted G)
    (R t : ℕ) (ht : 1 ≤ t) (hV : 0 < Fintype.card V)
    (hrounds : normalizedRounds (Fintype.card (Clone V (2 * t))) ≤ R)
    (out : BalancedResult (Clone V (2 * t))) (rounds : List (RoutedRound V (2 * t)))
    (hexec : (executedCutPlayer (localTolerance (Fintype.card V) R : ℝ)
      (even_clone (V := V) t)).eval G.cut = .complete out rounds) :
    (∑ v, fakeDegrees rounds v) ≤ Fintype.card V * t := by
  have hbudget := completed_edge_budget G hG R t ht hV hrounds out rounds hexec
  rw [sum_fakeDegrees]
  nlinarith

inductive NodeResult (V : Type) where
  | split : Finset V → NodeResult V
  | pruned : Finset V → NodeResult V
  | invalid : NodeResult V

def nodeProg (R t : ℕ) : Prog (Finset V) ℝ (NodeResult V) :=
  (executedCutPlayer (localTolerance (Fintype.card V) R : ℝ)
    (even_clone (V := V) t)).bind fun answer =>
      match answer with
      | .split P => .pure (.split P)
      | .invalid => .pure .invalid
      | .complete _ rounds => (pruneProg R t (fakeDegrees rounds)).map NodeResult.pruned

def NodeCorrect (G : WeightedGraph V) (R t : ℕ) : NodeResult V → Prop
  | .split P => SplitCorrect G (2 * t) (localTolerance (Fintype.card V) R) P
  | .pruned P =>
      8 * P.card ≤ Fintype.card V ∧ G.cut P ≤ (2 * (t : ℝ)) * P.card ∧
        ∀ T : Finset V, T ⊆ Pᶜ →
          (2 * (t : ℝ)) * min (T.card : ℝ) ((Pᶜ \ T).card : ℝ) ≤
            4 * (R : ℝ) * G.localCut Pᶜ T
  | .invalid => False

theorem completed_prune_correct (G : WeightedGraph V) (hG : Unweighted G)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hV : 0 < Fintype.card V)
    (hrounds : normalizedRounds (Fintype.card (Clone V (2 * t))) ≤ R)
    (out : BalancedResult (Clone V (2 * t))) (rounds : List (RoutedRound V (2 * t)))
    (hexec : (executedCutPlayer (localTolerance (Fintype.card V) R : ℝ)
      (even_clone (V := V) t)).eval G.cut = .complete out rounds) :
    NodeCorrect G R t (.pruned ((pruneProg R t (fakeDegrees rounds)).eval G.cut)) := by
  let history := markedHistory rounds
  let D := FakeEdges.fakeGraph history
  have hc := completed_certificate G hG (localTolerance (Fintype.card V) R) R
    (by omega : 0 < 2 * t) hV (even_clone (V := V) t) hrounds out rounds hexec
  have hdegree (v : V) : D.degree v ≤ (R : ℝ) * (2 * t) := by
    dsimp only [D]
    rw [FakeEdges.fakeGraph_degree]
    exact_mod_cast hc.2.2 v
  have ha (v : V) : (fakeDegrees rounds v : ℝ) = D.degree v := by
    exact (FakeEdges.fakeGraph_degree history v).symm
  have hbudget : 32 * (FakeEdges.edgeCount history : ℝ) ≤
      (Fintype.card V : ℝ) * (2 * t) := by
    exact_mod_cast completed_edge_budget G hG R t ht hV hrounds out rounds hexec
  exact pruneProg_structure G D hG R t hR ht (fakeDegrees rounds)
    (FakeEdges.edgeCount history) ha hdegree (FakeEdges.sum_degrees history) hbudget
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc.1)

theorem nodeProg_correct (G : WeightedGraph V) (hG : Unweighted G)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hV : 0 < Fintype.card V)
    (hrounds : normalizedRounds (Fintype.card (Clone V (2 * t))) ≤ R) :
    NodeCorrect G R t ((nodeProg R t).eval G.cut) := by
  have hc := runMatchingGame_correct G hG (localTolerance (Fintype.card V) R)
    (Nat.cast_nonneg _) (by omega : 0 < 2 * t) (cutPlayer (even_clone (V := V) t))
  change GameCorrect G (localTolerance (Fintype.card V) R)
    (cutPlayer (even_clone (V := V) t))
    ((executedCutPlayer (localTolerance (Fintype.card V) R : ℝ)
      (even_clone (V := V) t)).eval G.cut) at hc
  rw [nodeProg, Prog.eval_bind]
  cases he : (executedCutPlayer (localTolerance (Fintype.card V) R : ℝ)
      (even_clone (V := V) t)).eval G.cut with
  | split P => simpa only [he, GameCorrect, Prog.eval_pure, NodeCorrect] using hc
  | invalid =>
      have hf : False := by simpa only [he, GameCorrect] using hc
      exact hf.elim
  | complete out rounds =>
      simpa only [Prog.eval_map] using
        completed_prune_correct G hG R t hR ht hV hrounds out rounds he

def nodeBudget (V : Type) [Fintype V] (R t : ℕ) : ℕ :=
  (R + 1) * exactSharpBudget V R t

/-- Failed games are charged for every actual flow before their split;
completed games add the pruning flow whose source bound is derived above. -/
theorem nodeProg_cost (G : WeightedGraph V) (hG : Unweighted G)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hV : 0 < Fintype.card V)
    (hq : Fintype.card V ≤ t ^ 3)
    (hrounds : normalizedRounds (Fintype.card (Clone V (2 * t))) ≤ R) :
    (nodeProg (V := V) R t).cost G.cut ≤ nodeBudget V R t := by
  have hgame := executedCutPlayer_cost G hG R t hR ht (by omega) hq
    (localTolerance (Fintype.card V) R) (even_clone (V := V) t)
  have hg : (executedCutPlayer (localTolerance (Fintype.card V) R : ℝ)
      (even_clone (V := V) t)).cost G.cut ≤ exactSharpBudget V R t * R :=
    hgame.trans (Nat.mul_le_mul_left _ hrounds)
  rw [nodeProg, Prog.cost_bind]
  cases he : (executedCutPlayer (localTolerance (Fintype.card V) R : ℝ)
      (even_clone (V := V) t)).eval G.cut with
  | split P =>
      simp only [Prog.cost_pure, Nat.add_zero]
      dsimp only [nodeBudget]
      nlinarith
  | invalid =>
      simp only [Prog.cost_pure, Nat.add_zero]
      dsimp only [nodeBudget]
      nlinarith
  | complete out rounds =>
      have ha := completed_source_cap G hG R t ht hV hrounds out rounds he
      have hp := pruneProg_cost G hG R t hR ht (by omega) hq (fakeDegrees rounds) ha
      rw [Prog.cost_map]
      dsimp only [nodeBudget]
      nlinarith

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.completed_source_cap
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.completed_prune_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.nodeProg_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.nodeProg_cost
