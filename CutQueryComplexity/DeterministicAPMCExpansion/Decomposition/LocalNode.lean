import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Node
import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.SubtypeQueries

/-!
# Capped nodes on the actual public part subtype

Each node is capped before its queries are lifted to the fixed ambient
oracle. This is one subtype adapter, regardless of recursion depth. Honest
unit-graph executions fit the cap by the proved node cost; arbitrary real
answers still obey the indexed budget and may return `invalid`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

open Finset Flow CutMatching Pruning
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def cappedNode (R t : ℕ) :
    DTree (Finset V) ℝ (NodeResult V) (nodeBudget V R t) :=
  ((nodeProg R t).toDTree (nodeBudget V R t)).map (fun answer => answer.getD .invalid)

theorem cappedNode_eval (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hV : 0 < Fintype.card V)
    (hq : Fintype.card V ≤ t ^ 3)
    (hrounds : normalizedRounds (Fintype.card (Clone V (2 * t))) ≤ R) :
    (cappedNode (V := V) R t).eval G.cut = (nodeProg R t).eval G.cut := by
  rw [cappedNode, DTree.eval_map,
    Prog.toDTree_eval G.cut _ _ (nodeProg_cost G hG R t hR ht hV hq hrounds)]
  rfl

def partNode (R t : ℕ) (W : Finset V) :
    Prog (Finset V) ℝ (NodeResult (PartVertex W)) :=
  treeProg (subtypeProgram W (cappedNode R t))

theorem partNode_cost (R t : ℕ) (W : Finset V) (read : Finset V → ℝ) :
    (partNode R t W).cost read ≤ nodeBudget (PartVertex W) R t * 3 := by
  rw [partNode, treeProg_cost]
  exact DTree.cost_le _ _

theorem partNode_eval (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (W : Finset V) (hW : 0 < W.card)
    (hq : W.card ≤ t ^ 3)
    (hrounds : normalizedRounds (W.card * (2 * t)) ≤ R) :
    (partNode R t W).eval G.cut = (nodeProg R t).eval (partGraph G W).cut := by
  rw [partNode, treeProg_eval, subtypeProgram_eval]
  apply cappedNode_eval (partGraph G W) (partGraph_unweighted hG W) R t hR ht
  · simpa only [partVertex_card] using hW
  · simpa only [partVertex_card] using hq
  · simpa only [Clone, Fintype.card_prod, Fintype.card_fin, partVertex_card] using hrounds

theorem partNode_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (W : Finset V) (hW : 0 < W.card)
    (hq : W.card ≤ t ^ 3)
    (hrounds : normalizedRounds (W.card * (2 * t)) ≤ R) :
    NodeCorrect (partGraph G W) R t ((partNode R t W).eval G.cut) := by
  rw [partNode_eval G hG R t hR ht W hW hq hrounds]
  apply nodeProg_correct (partGraph G W) (partGraph_unweighted hG W) R t hR ht
  · simpa only [partVertex_card] using hW
  · simpa only [Clone, Fintype.card_prod, Fintype.card_fin, partVertex_card] using hrounds

/-- This coefficient is independent of the current part. The factor three
for the ambient subtype adapter is already included. -/
def nodeUnitBudget (N R t : ℕ) : ℕ :=
  1152 * (R + 1) * R * t ^ 2 * (Nat.clog 2 (N + 2) + 1)

theorem partNode_linear_cost (N R t : ℕ) (W : Finset V) (hW : W.card ≤ N)
    (read : Finset V → ℝ) :
    (partNode R t W).cost read ≤ nodeUnitBudget N R t * W.card := by
  have hlog := Nat.add_le_add_right (Nat.clog_mono_right 2
    (Nat.add_le_add_right hW 2)) 1
  have hmul := Nat.mul_le_mul_left (1152 * (R + 1) * R * t ^ 2 * W.card) hlog
  apply (partNode_cost R t W read).trans
  have he : nodeBudget (PartVertex W) R t * 3 =
      (1152 * (R + 1) * R * t ^ 2 * W.card) * (Nat.clog 2 (W.card + 2) + 1) := by
    simp only [nodeBudget, exactSharpBudget, neighborBudget, searchDepth,
      network_card, partVertex_card]
    ring
  rw [he]
  simpa only [nodeUnitBudget, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

end
end CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.cappedNode_eval
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.partNode_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.partNode_linear_cost
