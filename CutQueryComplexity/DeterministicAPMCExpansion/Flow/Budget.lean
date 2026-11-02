import CutQueryComplexity.DeterministicAPMCExpansion.Flow.SharpBudget

/-!
# A public exact-flow tree with the sharp cap on every reply sequence

The tree is selected from the public scale, terminal capacities and numeric
parameters before the hidden graph is supplied. Exhausting its budget returns
a fixed unfinished result. The executed sharp-cost theorem proves that this
fallback is never reached on a promised input; its output is then exactly the
BFS and blocking-phase result, with a feasible integral maximum flow and a
minimum source shore. No solver or query-cost premise is an input.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate DirectedCertificate
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The entire query tree depends only on public data. -/
def scaledExactTree (C R t : ℕ) (a z : V → ℕ) :
    DTree (Finset V) ℝ (ExactResult V) (exactSharpBudget V R t) :=
  ((scaledExactProg C a z).toDTree (exactSharpBudget V R t)).map
    (fun result => result.getD (exactEmpty (fun _ _ => 0) {source} false))

/-- The type-indexed cap holds even for replies that describe no graph. -/
theorem scaledExactTree_cost (read : Finset V → ℝ) (C R t : ℕ) (a z : V → ℕ) :
    (scaledExactTree C R t a z).cost read ≤ exactSharpBudget V R t :=
  DTree.cost_le _ _

theorem scaledExactTree_eval (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C R t : ℕ) (hC : 1 ≤ C) (hCR : C ≤ R) (ht : 1 ≤ t)
    (hqpos : 1 ≤ Fintype.card V) (hq : Fintype.card V ≤ t ^ 3) (a z : V → ℕ)
    (ha : (∑ v, a v) ≤ Fintype.card V * t) :
    (scaledExactTree C R t a z).eval G.cut = (scaledExactProg C a z).eval G.cut := by
  rw [scaledExactTree, DTree.eval_map,
    Prog.toDTree_eval G.cut _ _
      (scaledExactProg_cost_sharp G hG C R t hC hCR ht hqpos hq a z ha),
    Option.getD_some]

/-- Correctness of the actual capped oracle execution. -/
theorem scaledExactTree_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C R t : ℕ) (hC : 1 ≤ C) (hCR : C ≤ R) (ht : 1 ≤ t)
    (hqpos : 1 ≤ Fintype.card V) (hq : Fintype.card V ≤ t ^ 3) (a z : V → ℕ)
    (ha : (∑ v, a v) ≤ Fintype.card V * t) :
    ExactCertificate (directed (twoStar (scaledInternal G C) a z))
      ((scaledExactTree C R t a z).eval G.cut) := by
  rw [scaledExactTree_eval G hG C R t hC hCR ht hqpos hq a z ha]
  exact scaledExactProg_correct G hG C a z

theorem exactSharpBudget_eq (R t : ℕ) :
    exactSharpBudget V R t =
      384 * Fintype.card V * R * t ^ 2 * (Nat.clog 2 (Fintype.card V + 2) + 1) := by
  rw [exactSharpBudget, neighborBudget_eq]
  ring

/-- A single graph-independent program has the cap for every oracle and
returns the certificate on every graph satisfying the stated input promise. -/
theorem exists_scaledExactTree (C R t : ℕ) (hC : 1 ≤ C) (hCR : C ≤ R) (ht : 1 ≤ t)
    (hqpos : 1 ≤ Fintype.card V) (hq : Fintype.card V ≤ t ^ 3) (a z : V → ℕ)
    (ha : (∑ v, a v) ≤ Fintype.card V * t) :
    ∃ tree : DTree (Finset V) ℝ (ExactResult V) (exactSharpBudget V R t),
      (∀ read, tree.cost read ≤ exactSharpBudget V R t) ∧
      ∀ G : WeightedGraph V, AllPairsAudit.Unweighted G →
        ExactCertificate (directed (twoStar (scaledInternal G C) a z)) (tree.eval G.cut) := by
  refine ⟨scaledExactTree C R t a z, ?_, ?_⟩
  · intro read
    exact scaledExactTree_cost read C R t a z
  · intro G hG
    exact scaledExactTree_correct G hG C R t hC hCR ht hqpos hq a z ha

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactTree_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactTree_eval
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactTree_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactSharpBudget_eq
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.exists_scaledExactTree
