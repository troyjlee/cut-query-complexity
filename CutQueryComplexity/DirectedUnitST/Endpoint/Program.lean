import CutQueryComplexity.Model.Prog
import CutQueryComplexity.Model.Reduction

/-! # Independent public-tree capping infrastructure

The final preparation/repair/terminal composition will be added only after
its external dependencies are checked. These helpers already fix the
semantics of the final public budget cap, without referring to any graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Endpoint

variable {I A O : Type} {q : ℕ}

theorem tree_bind_cost {P : Type} {r : ℕ} (T : DTree I A O q)
    (next : O → DTree I A P r) (read : I → A) :
    (T.bind next).cost read = T.cost read + (next (T.eval read)).cost read :=
  congrArg Prod.snd (DTree.run_bind T next read)

/-- The continuation index bounds all answer histories, independently of
what the first tree reports. The first tree's sharper actual cost is retained. -/
theorem tree_bind_cost_le {P : Type} {r : ℕ} (T : DTree I A O q)
    (next : O → DTree I A P r) (read : I → A) :
    (T.bind next).cost read ≤ T.cost read + r := by
  rw [tree_bind_cost]
  exact Nat.add_le_add_left (DTree.cost_le (next (T.eval read)) read) _

/-- Forget a tree's type-level budget without changing its queries. -/
def treeProg : {q : ℕ} → DTree I A O q → Prog I A O
  | 0, out => .pure out
  | _ + 1, .inl out => .pure out
  | _ + 1, .inr (i, next) => .query i fun answer => treeProg (next answer)

theorem treeProg_run (T : DTree I A O q) (read : I → A) :
    Prog.run read (treeProg T) = DTree.run read T := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rcases T with out | ⟨i, next⟩
    · rfl
    · simp only [treeProg, Prog.run, DTree.run, ih]

theorem treeProg_eval (T : DTree I A O q) (read : I → A) :
    (treeProg T).eval read = T.eval read := by
  simp only [Prog.eval, DTree.eval, treeProg_run]

theorem treeProg_cost (T : DTree I A O q) (read : I → A) :
    (treeProg T).cost read = T.cost read := by
  simp only [Prog.cost, DTree.cost, treeProg_run]

/-- The requested budget is public and independent of the oracle replies. -/
def capTree (T : DTree I A O q) (budget : ℕ) : DTree I A (Option O) budget :=
  (treeProg T).toDTree budget

theorem capTree_eval (T : DTree I A O q) (budget : ℕ) (read : I → A)
    (hcost : T.cost read ≤ budget) :
    (capTree T budget).eval read = some (T.eval read) := by
  have h := Prog.toDTree_eval read (treeProg T) budget
    (by simpa only [treeProg_cost] using hcost)
  simpa only [capTree, treeProg_eval] using h

theorem capTree_cost (T : DTree I A O q) (budget : ℕ) (read : I → A) :
    (capTree T budget).cost read ≤ budget := DTree.cost_le _ _

theorem capTree_cost_eq (T : DTree I A O q) (budget : ℕ) (read : I → A)
    (hcost : T.cost read ≤ budget) :
    (capTree T budget).cost read = T.cost read := by
  have h := Prog.toDTree_cost read (treeProg T) budget
    (by simpa only [treeProg_cost] using hcost)
  simpa only [capTree, treeProg_cost] using h

/-- A rejected branch and exhausted final cap both return `none`. -/
def cappedOptionTree (T : DTree I A (Option O) q) (budget : ℕ) :
    DTree I A (Option O) budget := (capTree T budget).map Option.join

theorem cappedOptionTree_eval (T : DTree I A (Option O) q) (budget : ℕ)
    (read : I → A) (hcost : T.cost read ≤ budget) :
    (cappedOptionTree T budget).eval read = T.eval read := by
  simp only [cappedOptionTree, DTree.eval_map, capTree_eval T budget read hcost, Option.join]
  rfl

theorem cappedOptionTree_cost (T : DTree I A (Option O) q) (budget : ℕ)
    (read : I → A) : (cappedOptionTree T budget).cost read ≤ budget :=
  DTree.cost_le _ _

theorem cappedOptionTree_cost_eq (T : DTree I A (Option O) q) (budget : ℕ)
    (read : I → A) (hcost : T.cost read ≤ budget) :
    (cappedOptionTree T budget).cost read = T.cost read := by
  change (DTree.run read ((capTree T budget).map Option.join)).2 = _
  rw [DTree.run_map]
  exact capTree_cost_eq T budget read hcost

end CutQueryComplexity.DirectedUnitST.Endpoint

#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.treeProg_run
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.tree_bind_cost
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.tree_bind_cost_le
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.capTree_eval
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.capTree_cost
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.cappedOptionTree_eval
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.cappedOptionTree_cost_eq
