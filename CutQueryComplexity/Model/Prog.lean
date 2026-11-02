import CutQueryComplexity.Model.Deterministic

/-! # Deterministic query programs as a monad

`Prog I A α` is the free monad over one query instruction: a program either
returns a value or asks the oracle about `i : I` and continues with the answer.
Unlike `DTree`, its type carries no budget, so long adaptive procedures can be
written with ordinary recursion and `do` notation. `run` returns the output
together with the actual number of queries.

`toDTree p q` compiles a program into a budget-`q` tree that stops with `none`
when the budget runs out. `toDTree_run` shows that a program whose cost is at most
`q` is executed exactly, with the same output and cost.
-/

namespace CutQueryComplexity

inductive Prog (I A α : Type) where
  | pure : α → Prog I A α
  | query : I → (A → Prog I A α) → Prog I A α

namespace Prog

variable {I A α β γ : Type}

def bind : Prog I A α → (α → Prog I A β) → Prog I A β
  | pure a, f => f a
  | query i k, f => query i (fun x => bind (k x) f)

instance : Monad (Prog I A) where
  pure := Prog.pure
  bind := Prog.bind

/-- Output and number of queries on an oracle. -/
def run (read : I → A) : Prog I A α → α × ℕ
  | pure a => (a, 0)
  | query i k => let r := run read (k (read i)); (r.1, r.2 + 1)

def eval (read : I → A) (p : Prog I A α) : α := (run read p).1
def cost (read : I → A) (p : Prog I A α) : ℕ := (run read p).2

/-- Ask one question. -/
def ask (i : I) : Prog I A A := query i Prog.pure

@[simp] theorem run_pure (read : I → A) (a : α) : run read (Prog.pure a : Prog I A α) = (a, 0) := rfl

@[simp] theorem run_query (read : I → A) (i : I) (k : A → Prog I A α) :
    run read (query i k) = ((run read (k (read i))).1, (run read (k (read i))).2 + 1) := rfl

@[simp] theorem pure_eq (a : α) : (Pure.pure a : Prog I A α) = Prog.pure a := rfl

@[simp] theorem bind_eq (p : Prog I A α) (f : α → Prog I A β) : (p >>= f) = p.bind f := rfl

@[simp] theorem run_bind (read : I → A) (p : Prog I A α) (f : α → Prog I A β) :
    run read (p.bind f) =
      ((run read (f (run read p).1)).1, (run read p).2 + (run read (f (run read p).1)).2) := by
  induction p with
  | pure a => simp [bind]
  | query i k ih => simp [bind, run, ih, Nat.add_right_comm]

@[simp] theorem run_ask (read : I → A) (i : I) : run read (ask i : Prog I A A) = (read i, 1) := rfl

@[simp] theorem eval_bind (read : I → A) (p : Prog I A α) (f : α → Prog I A β) :
    eval read (p.bind f) = eval read (f (eval read p)) := by
  simp [eval]

@[simp] theorem cost_bind (read : I → A) (p : Prog I A α) (f : α → Prog I A β) :
    cost read (p.bind f) = cost read p + cost read (f (eval read p)) := by
  simp [cost, eval]

@[simp] theorem eval_pure (read : I → A) (a : α) : eval read (Prog.pure a : Prog I A α) = a := rfl
@[simp] theorem cost_pure (read : I → A) (a : α) : cost read (Prog.pure a : Prog I A α) = 0 := rfl
@[simp] theorem eval_ask (read : I → A) (i : I) : eval read (ask i : Prog I A A) = read i := rfl
@[simp] theorem cost_ask (read : I → A) (i : I) : cost read (ask i : Prog I A A) = 1 := rfl

/-- Map over the output, at no cost. -/
def map (f : α → β) (p : Prog I A α) : Prog I A β := p.bind (fun a => Prog.pure (f a))

@[simp] theorem eval_map (read : I → A) (f : α → β) (p : Prog I A α) :
    eval read (p.map f) = f (eval read p) := by simp [map]

@[simp] theorem cost_map (read : I → A) (f : α → β) (p : Prog I A α) :
    cost read (p.map f) = cost read p := by simp [map]

/-! ### Compiling to budgeted trees -/

/-- Run within budget `q`, reporting `none` if the budget is exhausted. -/
def toDTree : Prog I A α → (q : ℕ) → DTree I A (Option α) q
  | pure a, _ => DTree.pure (some a)
  | query _ _, 0 => DTree.pure none
  | query i k, q + 1 => DTree.query i (fun x => toDTree (k x) q)

theorem toDTree_run (read : I → A) (p : Prog I A α) (q : ℕ) (h : cost read p ≤ q) :
    DTree.run read (toDTree p q) = (some (eval read p), cost read p) := by
  induction p generalizing q with
  | pure a => simp [toDTree, eval, cost]
  | query i k ih =>
      rcases q with _ | q
      · simp [cost, run] at h
      · simp only [toDTree, DTree.run_query]
        have h' : cost read (k (read i)) ≤ q := by
          simp only [cost, run] at h ⊢
          omega
        rw [ih (read i) q h']
        rfl

theorem toDTree_eval (read : I → A) (p : Prog I A α) (q : ℕ) (h : cost read p ≤ q) :
    (toDTree p q).eval read = some (eval read p) := by
  simp [DTree.eval, toDTree_run read p q h]

theorem toDTree_cost (read : I → A) (p : Prog I A α) (q : ℕ) (h : cost read p ≤ q) :
    (toDTree p q).cost read = cost read p := by
  simp [DTree.cost, toDTree_run read p q h]

end Prog
end CutQueryComplexity
