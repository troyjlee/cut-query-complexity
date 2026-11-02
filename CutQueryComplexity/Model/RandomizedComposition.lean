import CutQueryComplexity.Model.Randomized
import CutQueryComplexity.Model.Composition

/-! # Free random choices and adaptive randomized composition with exact cost semantics -/

namespace CutQueryComplexity.RTree

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I A O P : Type} {q r : ℕ}

/-- Draw an output without using the oracle, at any advertised budget. -/
def pure (p : PMF O) : {q : ℕ} → RTree I A O q
  | 0 => p
  | _ + 1 => p.map Sum.inl

@[simp] theorem run_pure (p : PMF O) (read : I → A) :
    run read (pure (q := q) p) = p.map (fun o => (o, 0)) := by
  cases q <;> simp [pure, run, PMF.map, Function.comp_def]

/-- One query followed by an answer-dependent stochastic continuation. -/
def query (i : I) (next : A → RTree I A O q) : RTree I A O (q + 1) :=
  PMF.pure (Sum.inr (i, next))

@[simp] theorem run_query (i : I) (next : A → RTree I A O q) (read : I → A) :
    run read (query i next) = (run read (next (read i))).map (fun p => (p.1, p.2 + 1)) := by
  simp [query, run]

/-- Choose a bounded program at no query cost, then run it. -/
def mix : {q : ℕ} → PMF (RTree I A O q) → RTree I A O q
  | 0, p => p.bind id
  | _ + 1, p => p.bind id

@[simp] theorem run_mix (p : PMF (RTree I A O q)) (read : I → A) :
    run read (mix p) = p.bind (run read) := by
  cases q <;> simp [mix, run, PMF.map, Function.comp_def]

/-- Reindex a worst-case budget by equality. -/
def cast (h : q = r) (T : RTree I A O q) : RTree I A O r := h ▸ T

@[simp] theorem run_cast (h : q = r) (T : RTree I A O q) (read : I → A) :
    run read (T.cast h) = run read T := by cases h; rfl

/-- Budget weakening inserts no actual oracle calls. -/
def weaken : {q r : ℕ} → q ≤ r → RTree I A O q → RTree I A O r
  | 0, _, _, T => pure T
  | _ + 1, 0, h, _ => False.elim (Nat.not_succ_le_zero _ h)
  | _ + 1, _ + 1, h, T => T.map fun action => match action with
      | Sum.inl o => Sum.inl o
      | Sum.inr (i, next) => Sum.inr (i, fun a => weaken (Nat.le_of_succ_le_succ h) (next a))

@[simp] theorem run_weaken (h : q ≤ r) (T : RTree I A O q) (read : I → A) :
    run read (T.weaken h) = run read T := by
  induction r generalizing q with
  | zero =>
      cases q with
      | zero => rfl
      | succ q => exact False.elim (Nat.not_succ_le_zero _ h)
  | succ r ih =>
      cases q with
      | zero => exact run_pure (q := r + 1) T read
      | succ q =>
          simp only [weaken, run, PMF.bind_map, Function.comp_def]
          congr 1
          funext action
          rcases action with o | ⟨i, next⟩
          · rfl
          · dsimp only
            rw [ih]

/-- Run the second bounded program selected by the first output. -/
def bind : {q r : ℕ} → RTree I A O q → (O → RTree I A P r) → RTree I A P (q + r)
  | 0, r, T, f => (mix (T.map f)).cast (Nat.zero_add r).symm
  | q + 1, r, T, f => mix (T.map fun action => match action with
      | Sum.inl o => (f o).weaken (by omega)
      | Sum.inr (i, next) =>
          (query i (fun a => bind (next a) f)).cast (Nat.succ_add q r).symm)

/-- The operational distribution keeps both actual costs and adds them. -/
theorem run_bind (T : RTree I A O q) (f : O → RTree I A P r) (read : I → A) :
    run read (T.bind f) = (run read T).bind fun p =>
      (run read (f p.1)).map (fun t => (t.1, p.2 + t.2)) := by
  induction q with
  | zero =>
      simp [bind, run, PMF.map, Function.comp_def]
  | succ q ih =>
      rw [bind, run_mix, PMF.bind_map]
      simp only [run, PMF.bind_bind]
      congr 1
      funext action
      rcases action with o | ⟨i, next⟩
      · simp [Function.comp_def, PMF.map]
      · simp [Function.comp_def, ih, PMF.map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Marginal distribution of the reported output. -/
def eval (T : RTree I A O q) (read : I → A) : PMF O := (run read T).map Prod.fst

@[simp] theorem eval_pure (p : PMF O) (read : I → A) : (pure (q := q) p).eval read = p := by
  simp only [eval, run_pure, PMF.map_comp]
  exact PMF.map_id p

@[simp] theorem eval_query (i : I) (next : A → RTree I A O q) (read : I → A) :
    (query i next).eval read = (next (read i)).eval read := by
  simp [eval, PMF.map_comp, Function.comp_def]

@[simp] theorem eval_cast (h : q = r) (T : RTree I A O q) (read : I → A) :
    (T.cast h).eval read = T.eval read := by simp [eval]

@[simp] theorem eval_weaken (h : q ≤ r) (T : RTree I A O q) (read : I → A) :
    (T.weaken h).eval read = T.eval read := by simp [eval]

@[simp] theorem eval_mix (p : PMF (RTree I A O q)) (read : I → A) :
    (mix p).eval read = p.bind (fun T => T.eval read) := by
  simp [eval, PMF.map_bind]

@[simp] theorem eval_bind (T : RTree I A O q) (f : O → RTree I A P r) (read : I → A) :
    (T.bind f).eval read = (T.eval read).bind (fun o => (f o).eval read) := by
  simp [eval, run_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Free output postprocessing. -/
def map (f : O → P) (T : RTree I A O q) : RTree I A P q :=
  (T.bind (fun o => pure (q := 0) (PMF.pure (f o)))).cast (Nat.add_zero q)

@[simp] theorem eval_map (f : O → P) (T : RTree I A O q) (read : I → A) :
    (T.map f).eval read = (T.eval read).map f := by
  simp [map, PMF.map, Function.comp_def]

theorem successProb_eq (T : RTree I A O q) (read : I → A) (Good : O → Prop) :
    T.successProb read Good = ((T.eval read).toOuterMeasure {o | Good o}).toReal := by
  rw [eval, PMF.toOuterMeasure_map_apply]
  rfl

end
end CutQueryComplexity.RTree
