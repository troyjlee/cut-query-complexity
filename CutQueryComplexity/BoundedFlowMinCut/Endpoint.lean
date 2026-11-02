import CutQueryComplexity.BoundedFlowMinCut.Asymptotics

/-! # Deterministic unweighted global minimum cut in `O(n^{3/2} log² n)` cut queries

The endpoint of the bounded-flow minimum cut, after Kenneth-Mordoch,
*Deterministic Global Minimum Cut Using Õ(n^{3/2}) Cut Queries*
(arXiv 2610.23461v1), with the cutoff `t L` instead of `√n`.

`program n` is one public decision tree on `Fin n`, fixed before the graph, with
budget index `queryBudget n`: every run on every oracle stays within it
(`program_cost`). On every unweighted graph (weights 0 or 1) with at least two
vertices it returns a global minimum shore and its exact cut value
(`program_correct`). `queryBudget n = O(n^{3/2} log² n)` is in `Asymptotics`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section

/-- **The program.** One public decision tree on the labelled vertices `Fin n`,
fixed before the graph; every run on every oracle stays within `queryBudget n`. -/
def program (n : ℕ) :
    DTree (Finset (Fin n)) ℝ (Option (AllPairs.STAnswer (Fin n))) (queryBudget n) :=
  (mainProg (V := Fin n)).toDTree (queryBudget n)

/-- On every unweighted graph with at least two vertices, the program completes
with a global minimum shore and its exact cut value. -/
theorem program_correct (n : ℕ) (hn : 2 ≤ n) (G : WeightedGraph (Fin n))
    (hG : AllPairsAudit.Unweighted G) :
    ∃ out, (program n).eval G.cut = some out ∧
      IsMinCut G out.shore ∧ out.value = G.cut out.shore := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hcost := mainProg_cost (V := Fin n) hG
  rw [hcard] at hcost
  exact ⟨_, Prog.toDTree_eval G.cut _ _ hcost, mainProg_correct hG (by rw [hcard]; exact hn)⟩

/-- The cap holds on every oracle. -/
theorem program_cost (n : ℕ) (read : Finset (Fin n) → ℝ) :
    (program n).cost read ≤ queryBudget n :=
  DTree.cost_le _ read

end
end CutQueryComplexity.BoundedFlowMinCut
