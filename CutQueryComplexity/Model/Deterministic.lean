import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Cases

/-! # Adaptive deterministic oracle programs with a worst-case budget

Answers and outputs need not be finite. The tree is chosen before the hidden
input; only an oracle answer selects its continuation.
-/

namespace CutQueryComplexity

/-- A deterministic tree with at most `q` whole-answer oracle calls. -/
def DTree (I A O : Type) : ℕ → Type
  | 0 => O
  | q + 1 => O ⊕ (I × (A → DTree I A O q))

namespace DTree

variable {I A O P X : Type} {q : ℕ}

/-- Halt immediately, at any available budget. -/
def pure (o : O) : {q : ℕ} → DTree I A O q
  | 0 => o
  | _ + 1 => Sum.inl o

/-- Spend one query and continue using its entire answer. -/
def query (i : I) (next : A → DTree I A O q) : DTree I A O (q + 1) :=
  Sum.inr (i, next)

/-- Output and actual query count on an oracle. -/
def run (read : I → A) : {q : ℕ} → DTree I A O q → O × ℕ
  | 0, o => (o, 0)
  | _ + 1, Sum.inl o => (o, 0)
  | _ + 1, Sum.inr (i, next) =>
      let result := run read (next (read i))
      (result.1, result.2 + 1)

/-- The announced output. -/
def eval (T : DTree I A O q) (read : I → A) : O := (run read T).1

/-- The realized number of queries, which can be smaller than the budget. -/
def cost (T : DTree I A O q) (read : I → A) : ℕ := (run read T).2

@[simp] theorem run_pure (read : I → A) (o : O) :
    run read (pure (q := q) o) = (o, 0) := by cases q <;> rfl

@[simp] theorem run_query (read : I → A) (i : I) (next : A → DTree I A O q) :
    run read (query i next) = ((run read (next (read i))).1,
      (run read (next (read i))).2 + 1) := rfl

@[simp] theorem eval_pure (read : I → A) (o : O) :
    (pure (q := q) o).eval read = o := by simp [eval]

@[simp] theorem eval_query (read : I → A) (i : I) (next : A → DTree I A O q) :
    (query i next).eval read = (next (read i)).eval read := rfl

/-- Every execution obeys its indexed budget. -/
theorem cost_le (T : DTree I A O q) (read : I → A) : T.cost read ≤ q := by
  induction q with
  | zero => simp [cost, run]
  | succ q ih =>
      rcases T with o | ⟨i, next⟩
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (ih (next (read i)))

/-- Free output postprocessing does not change the queries. -/
def map (f : O → P) : {q : ℕ} → DTree I A O q → DTree I A P q
  | 0, o => f o
  | _ + 1, Sum.inl o => Sum.inl (f o)
  | _ + 1, Sum.inr (i, next) => query i fun a => map f (next a)

@[simp] theorem run_map (f : O → P) (T : DTree I A O q) (read : I → A) :
    run read (map f T) = (f (run read T).1, (run read T).2) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rcases T with o | ⟨i, next⟩
      · rfl
      · simp [map, run, query, ih]

@[simp] theorem eval_map (f : O → P) (T : DTree I A O q) (read : I → A) :
    (map f T).eval read = f (T.eval read) := by simp [eval]

/-- The chronological query/answer transcript. -/
def transcript (read : I → A) : {q : ℕ} → DTree I A O q → List (I × A)
  | 0, _ => []
  | _ + 1, Sum.inl _ => []
  | _ + 1, Sum.inr (i, next) => (i, read i) :: transcript read (next (read i))

/-- Agreement on the queries actually asked preserves the entire execution. -/
theorem run_eq_of_agree (T : DTree I A O q) (a b : I → A)
    (h : ∀ i v, (i, v) ∈ transcript a T → a i = b i) : run a T = run b T := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rcases T with o | ⟨i, next⟩
      · rfl
      · have hi : a i = b i := h i (a i) (by simp [transcript])
        have ht := ih (next (a i)) (fun j v hj => h j v (by simp [transcript, hj]))
        simp only [run, ← hi, ht]

/-- Decode a finite answer symbol without charging a query per bit. -/
def mapAnswers {B : Type} (decode : B → A) :
    {q : ℕ} → DTree I A O q → DTree I B O q
  | 0, o => o
  | _ + 1, Sum.inl o => Sum.inl o
  | _ + 1, Sum.inr (i, next) => query i fun b => mapAnswers decode (next (decode b))

@[simp] theorem run_mapAnswers {B : Type} (decode : B → A) (T : DTree I A O q)
    (read : I → B) : run read (mapAnswers decode T) = run (decode ∘ read) T := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rcases T with o | ⟨i, next⟩
      · rfl
      · simp [mapAnswers, run, query, ih, Function.comp_def]

/-- Exact relational correctness, uniformly over the promised inputs. -/
def Solves (T : DTree I A O q) (read : X → I → A) (Good : X → O → Prop) : Prop :=
  ∀ x, Good x (T.eval (read x))

end DTree
end CutQueryComplexity
