import CutQueryComplexity.Model.Prog
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Finite query-program plumbing for the reduction

These operations execute supplied budgeted primitives, sequence their actual
costs, and pull queries back through public maps. No hidden graph is an argument
to a program constructor.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction

variable {I J A O P : Type}

def liftDTree : {q : ℕ} → DTree I A O q → Prog I A O
  | 0, o => Prog.pure o
  | _ + 1, Sum.inl o => Prog.pure o
  | _ + 1, Sum.inr (i, next) => Prog.query i (fun a => liftDTree (next a))

theorem liftDTree_run {q : ℕ} (T : DTree I A O q) (read : I → A) :
    Prog.run read (liftDTree T) = T.run read := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rcases T with o | ⟨i, next⟩
    · rfl
    · simp [liftDTree, Prog.run, DTree.run, ih]

@[simp] theorem liftDTree_eval {q : ℕ} (T : DTree I A O q) (read : I → A) :
    Prog.eval read (liftDTree T) = T.eval read := by
  simp [Prog.eval, DTree.eval, liftDTree_run]

@[simp] theorem liftDTree_cost {q : ℕ} (T : DTree I A O q) (read : I → A) :
    Prog.cost read (liftDTree T) = T.cost read := by
  simp [Prog.cost, DTree.cost, liftDTree_run]

theorem liftDTree_cost_le {q : ℕ} (T : DTree I A O q) (read : I → A) :
    Prog.cost read (liftDTree T) ≤ q := by
  rw [liftDTree_cost]
  exact T.cost_le read

def queryMap (f : J → I) : Prog J A O → Prog I A O
  | Prog.pure o => Prog.pure o
  | Prog.query j next => Prog.query (f j) (fun a => queryMap f (next a))

theorem queryMap_run (f : J → I) (p : Prog J A O) (read : I → A) :
    Prog.run read (queryMap f p) = Prog.run (read ∘ f) p := by
  induction p with
  | pure o => rfl
  | query j next ih => simp [queryMap, Prog.run, ih, Function.comp_def]

@[simp] theorem queryMap_eval (f : J → I) (p : Prog J A O) (read : I → A) :
    Prog.eval read (queryMap f p) = Prog.eval (read ∘ f) p := by
  simp [Prog.eval, queryMap_run]

@[simp] theorem queryMap_cost (f : J → I) (p : Prog J A O) (read : I → A) :
    Prog.cost read (queryMap f p) = Prog.cost (read ∘ f) p := by
  simp [Prog.cost, queryMap_run]

/-- An actual sequential execution, with each primitive's realized cost. -/
def sequenceList (p : P → Prog I A O) : List P → Prog I A (List O)
  | [] => Prog.pure []
  | x :: xs => (p x).bind (fun o => (sequenceList p xs).map (o :: ·))

@[simp] theorem sequenceList_eval (p : P → Prog I A O) (xs : List P) (read : I → A) :
    Prog.eval read (sequenceList p xs) = xs.map (fun x => Prog.eval read (p x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sequenceList, ih]

@[simp] theorem sequenceList_cost (p : P → Prog I A O) (xs : List P) (read : I → A) :
    Prog.cost read (sequenceList p xs) = (xs.map (fun x => Prog.cost read (p x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sequenceList, ih]

theorem sequenceList_cost_le (p : P → Prog I A O) (xs : List P) (read : I → A)
    (bound : P → ℕ) (h : ∀ x ∈ xs, Prog.cost read (p x) ≤ bound x) :
    Prog.cost read (sequenceList p xs) ≤ (xs.map bound).sum := by
  rw [sequenceList_cost]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- A finite indexed table of outputs, implemented by sequential calls. -/
def tableProgram : (n : ℕ) → (Fin n → Prog I A O) → Prog I A (Fin n → O)
  | 0, _ => Prog.pure (fun i => Fin.elim0 i)
  | n + 1, p => (p 0).bind (fun o =>
      (tableProgram n (fun i => p i.succ)).map (Fin.cases o))

@[simp] theorem tableProgram_eval (n : ℕ) (p : Fin n → Prog I A O) (read : I → A) :
    Prog.eval read (tableProgram n p) = fun i => Prog.eval read (p i) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [tableProgram, Prog.eval_bind, Prog.eval_map, ih]
    funext i
    cases i using Fin.cases <;> rfl

@[simp] theorem tableProgram_cost (n : ℕ) (p : Fin n → Prog I A O) (read : I → A) :
    Prog.cost read (tableProgram n p) = ∑ i, Prog.cost read (p i) := by
  induction n with
  | zero => simp [tableProgram]
  | succ n ih => simp [tableProgram, ih, Fin.sum_univ_succ]

noncomputable def finiteTable {D : Type} [Fintype D] (p : D → Prog I A O) :
    Prog I A (D → O) :=
  (tableProgram (Fintype.card D) (fun i => p ((Fintype.equivFin D).symm i))).map
    (fun f x => f ((Fintype.equivFin D) x))

@[simp] theorem finiteTable_eval {D : Type} [Fintype D] (p : D → Prog I A O)
    (read : I → A) : Prog.eval read (finiteTable p) = fun x => Prog.eval read (p x) := by
  simp [finiteTable]

@[simp] theorem finiteTable_cost {D : Type} [Fintype D] (p : D → Prog I A O)
    (read : I → A) : Prog.cost read (finiteTable p) = ∑ x, Prog.cost read (p x) := by
  simp only [finiteTable, Prog.cost_map, tableProgram_cost]
  exact (Fintype.equivFin D).symm.sum_comp (fun x => Prog.cost read (p x))

end CutQueryComplexity.GHReduction
