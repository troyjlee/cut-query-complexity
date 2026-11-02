import CutQueryComplexity.Model.Composition

/-! # Substitution of concrete oracle programs -/

namespace CutQueryComplexity.DTree

variable {I A J B O : Type} {q k : ℕ}

@[simp] theorem eval_cast {r : ℕ} (h : q = r) (T : DTree I A O q) (read : I → A) :
    (T.cast h).eval read = T.eval read := by simp [eval]

@[simp] theorem eval_bind (T : DTree I A O q) (f : O → DTree I A B k) (read : I → A) :
    (T.bind f).eval read = (f (T.eval read)).eval read := by simp [eval, run_bind]

/-- Replace each virtual query by a public adaptive program of budget `k`. -/
def substitute (call : J → DTree I A B k) :
    {q : ℕ} → DTree J B O q → DTree I A O (q * k)
  | 0, o => pure o
  | q + 1, Sum.inl o => pure o
  | q + 1, Sum.inr (j, next) =>
      ((call j).bind (fun b => substitute call (next b))).cast
        (by rw [Nat.succ_mul, Nat.add_comm])

/-- Substitution computes the virtual tree on the answers returned by its subprograms. -/
theorem eval_substitute (call : J → DTree I A B k) (T : DTree J B O q) (read : I → A) :
    (T.substitute call).eval read = T.eval (fun j => (call j).eval read) := by
  induction q with
  | zero => exact congrArg Prod.fst (run_pure (q := 0 * k) read T)
  | succ q ih =>
      rcases T with o | ⟨j, next⟩
      · simp [substitute, eval, run]
      · simp only [substitute, eval, run_cast, run_bind]
        exact ih (next ((call j).eval read))

/-- A proved oracle reduction transports any deterministic output relation. -/
theorem substitute_solves {X : Type} (call : J → DTree I A B k)
    (T : DTree J B O q) (read : X → I → A) (virtual : X → J → B)
    (hcall : ∀ x j, (call j).eval (read x) = virtual x j) (Good : X → O → Prop)
    (hT : T.Solves virtual Good) : (T.substitute call).Solves read Good := by
  intro x
  have h : (fun j => (call j).eval (read x)) = virtual x := funext (hcall x)
  simpa only [eval_substitute, h] using hT x

end CutQueryComplexity.DTree
