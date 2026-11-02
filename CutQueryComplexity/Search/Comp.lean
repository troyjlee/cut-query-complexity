import CutQueryComplexity.Model.Deterministic

/-! # Adaptive oracle computations with unbounded query counts

`Comp Q A β` is the free monad of an oracle with questions `Q` and answers
`A`. Programs may recurse without a budget in their type. `cost` counts the
oracle calls made on a particular oracle, and `toDTree` compiles a program into
a budgeted `DTree` that agrees with it whenever the actual cost fits.
-/

namespace CutQueryComplexity
namespace Search

/-- An adaptive computation that asks an oracle questions of type `Q`. -/
inductive Comp (Q A β : Type) : Type
  | pure : β → Comp Q A β
  | query : Q → (A → Comp Q A β) → Comp Q A β

namespace Comp

variable {Q A β γ δ : Type}

/-- Sequential composition. -/
def bind : Comp Q A β → (β → Comp Q A γ) → Comp Q A γ
  | pure b, f => f b
  | query q k, f => query q fun a => bind (k a) f

instance : Monad (Comp Q A) where
  pure := pure
  bind := bind

/-- Ask one question and return its answer. -/
def ask (q : Q) : Comp Q A A := query q pure

/-- Output and number of oracle calls on a fixed oracle. -/
def run (o : Q → A) : Comp Q A β → β × ℕ
  | pure b => (b, 0)
  | query q k => let r := run o (k (o q)); (r.1, r.2 + 1)

/-- The output on a fixed oracle. -/
def eval (o : Q → A) (c : Comp Q A β) : β := (run o c).1

/-- The number of oracle calls on a fixed oracle. -/
def cost (o : Q → A) (c : Comp Q A β) : ℕ := (run o c).2

@[simp] theorem pure_def (b : β) : (Pure.pure b : Comp Q A β) = pure b := rfl

@[simp] theorem bind_def (c : Comp Q A β) (f : β → Comp Q A γ) :
    c >>= f = c.bind f := rfl

@[simp] theorem eval_pure (o : Q → A) (b : β) : (pure b : Comp Q A β).eval o = b := rfl

@[simp] theorem cost_pure (o : Q → A) (b : β) : (pure b : Comp Q A β).cost o = 0 := rfl

@[simp] theorem eval_query (o : Q → A) (q : Q) (k : A → Comp Q A β) :
    (query q k).eval o = (k (o q)).eval o := rfl

@[simp] theorem cost_query (o : Q → A) (q : Q) (k : A → Comp Q A β) :
    (query q k).cost o = (k (o q)).cost o + 1 := rfl

theorem run_bind (o : Q → A) (c : Comp Q A β) (f : β → Comp Q A γ) :
    run o (c.bind f) = ((run o (f (c.eval o))).1,
      c.cost o + (run o (f (c.eval o))).2) := by
  induction c with
  | pure b => simp [bind, run, eval, cost]
  | query q k ih =>
      simp only [bind, run, ih, eval, cost]
      exact Prod.ext rfl (by simp only; omega)

@[simp] theorem eval_bind (o : Q → A) (c : Comp Q A β) (f : β → Comp Q A γ) :
    (c.bind f).eval o = (f (c.eval o)).eval o := by
  simp [eval, run_bind]

@[simp] theorem cost_bind (o : Q → A) (c : Comp Q A β) (f : β → Comp Q A γ) :
    (c.bind f).cost o = c.cost o + (f (c.eval o)).cost o := by
  simp [cost, run_bind]

@[simp] theorem eval_ask (o : Q → A) (q : Q) : (ask q : Comp Q A A).eval o = o q := rfl

@[simp] theorem cost_ask (o : Q → A) (q : Q) : (ask q : Comp Q A A).cost o = 1 := rfl

/-- Free postprocessing. -/
def map (f : β → γ) (c : Comp Q A β) : Comp Q A γ := c.bind fun b => pure (f b)

@[simp] theorem eval_map (o : Q → A) (f : β → γ) (c : Comp Q A β) :
    (c.map f).eval o = f (c.eval o) := by simp [map]

@[simp] theorem cost_map (o : Q → A) (f : β → γ) (c : Comp Q A β) :
    (c.map f).cost o = c.cost o := by simp [map]

/-- Compile to a budgeted tree; branches that exhaust the budget return `none`. -/
def toDTree : (q : ℕ) → Comp Q A β → DTree Q A (Option β) q
  | _, pure b => DTree.pure (some b)
  | 0, query _ _ => (none : Option β)
  | q + 1, query x k => DTree.query x fun a => toDTree q (k a)

/-- The compiled tree agrees with the computation whenever the budget suffices. -/
theorem toDTree_eval (o : Q → A) (c : Comp Q A β) {q : ℕ} (h : c.cost o ≤ q) :
    (c.toDTree q).eval o = some (c.eval o) := by
  induction c generalizing q with
  | pure b => simp [toDTree]
  | query x k ih =>
      cases q with
      | zero => simp at h
      | succ q =>
          simp only [cost_query] at h
          simp only [toDTree, DTree.eval_query, eval_query]
          exact ih (o x) (by omega)

end Comp
end Search
end CutQueryComplexity
