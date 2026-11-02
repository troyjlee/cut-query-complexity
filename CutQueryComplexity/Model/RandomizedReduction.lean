import CutQueryComplexity.Model.RandomizedComposition
import CutQueryComplexity.Model.Reduction

/-! # Substituting exact deterministic oracle implementations into randomized trees -/
namespace CutQueryComplexity.RTree
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {I A J B O : Type} {q k : ℕ}

@[simp] theorem eval_ofDeterministic (T : DTree I A O q) (read : I → A) :
    (ofDeterministic T).eval read = PMF.pure (T.eval read) := by
  simp [eval, run_ofDeterministic, DTree.eval, PMF.pure_map]

/-- Each virtual query is answered by a deterministic program of public budget `k`. -/
def substitute (call : J → DTree I A B k) :
    {q : ℕ} → RTree J B O q → RTree I A O (q * k)
  | 0, T => pure T
  | q + 1, T => mix (PMF.map (fun action => match action with
      | Sum.inl o => pure (PMF.pure o)
      | Sum.inr (j, next) =>
          ((ofDeterministic (call j)).bind (fun b => substitute call (next b))).cast
            (by rw [Nat.succ_mul, Nat.add_comm])) T)

theorem eval_substitute (call : J → DTree I A B k) (T : RTree J B O q) (read : I → A) :
    (T.substitute call).eval read = T.eval (fun j => (call j).eval read) := by
  induction q with
  | zero => simp [substitute, eval, run, PMF.map_comp, Function.comp_def]
  | succ q ih =>
      simp only [substitute, eval_mix, PMF.bind_map, Function.comp_def]
      simp only [eval, run, PMF.map_bind]
      congr 1
      funext action
      rcases action with o | ⟨j, next⟩
      · simp [PMF.pure_map]
      · simp only [run_cast, PMF.map_comp, Function.comp_def]
        change ((ofDeterministic (call j)).bind (fun b => substitute call (next b))).eval read =
          (next ((call j).eval read)).eval (fun j => (call j).eval read)
        rw [eval_bind, eval_ofDeterministic, PMF.pure_bind, ih]

end
end CutQueryComplexity.RTree
