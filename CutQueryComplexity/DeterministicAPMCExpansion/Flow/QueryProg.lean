import CutQueryComplexity.DeterministicAPMCExpansion.Flow.ResidualSearch
import CutQueryComplexity.Model.Prog

/-! # Executing the concrete residual query trees inside adaptive programs -/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open DirectedCertificate Prog
open scoped Classical
noncomputable section

/-- The same queries and continuations, forgetting only the tree's index.
This adapter never evaluates or inspects an input oracle. -/
def treeProg {I A O : Type} : {q : ℕ} → DTree I A O q → Prog I A O
  | 0, out => .pure out
  | _ + 1, Sum.inl out => .pure out
  | _ + 1, Sum.inr (queryIndex, next) => .query queryIndex (fun answer => treeProg (next answer))

theorem treeProg_run {I A O : Type} {q : ℕ} (T : DTree I A O q) (read : I → A) :
    (treeProg T).run read = T.run read := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rcases T with out | ⟨query, next⟩
      · rfl
      · simp only [treeProg, Prog.run, DTree.run, ih]

@[simp] theorem treeProg_eval {I A O : Type} {q : ℕ}
    (T : DTree I A O q) (read : I → A) :
    (treeProg T).eval read = T.eval read := by
  exact congrArg Prod.fst (treeProg_run T read)

@[simp] theorem treeProg_cost {I A O : Type} {q : ℕ}
    (T : DTree I A O q) (read : I → A) :
    (treeProg T).cost read = T.cost read := by
  exact congrArg Prod.snd (treeProg_run T read)

variable {V : Type} [Fintype V] [DecidableEq V]

def neighborProg (a z : V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (u : NetworkVertex V) (U : Finset (NetworkVertex V)) :
    Prog (Finset V) ℝ (Option (NetworkVertex V)) :=
  treeProg (residualNeighbor a z f u U)

theorem neighborProg_correct (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f)
    (u : NetworkVertex V) (U : Finset (NetworkVertex V)) :
    PositiveResult (residualEntry G a z f u) U ((neighborProg a z f u U).eval G.cut) := by
  simpa only [neighborProg, treeProg_eval] using residualNeighbor_correct G a z f hf u U

theorem neighborProg_cost (read : Finset V → ℝ) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (u : NetworkVertex V) (U : Finset (NetworkVertex V)) :
    (neighborProg a z f u U).cost read ≤ neighborBudget V := by
  simpa only [neighborProg, treeProg_cost] using residualNeighbor_cost a z f u U read

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.treeProg_run
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.neighborProg_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.neighborProg_cost
