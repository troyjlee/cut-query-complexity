import CutQueryComplexity.Model.Deterministic

/-! # Budget weakening and adaptive deterministic composition -/

namespace CutQueryComplexity.DTree

variable {I A O P : Type} {q r : ℕ}

/-- Reindex a budget by an equality. -/
def cast (h : q = r) (T : DTree I A O q) : DTree I A O r := h ▸ T

@[simp] theorem run_cast (h : q = r) (T : DTree I A O q) (read : I → A) :
    run read (T.cast h) = run read T := by cases h; rfl

/-- Increase the advertised budget without inserting actual queries. -/
def weaken : {q r : ℕ} → q ≤ r → DTree I A O q → DTree I A O r
  | 0, _, _, o => pure o
  | _ + 1, 0, h, _ => False.elim (Nat.not_succ_le_zero _ h)
  | _ + 1, _ + 1, _, Sum.inl o => Sum.inl o
  | _ + 1, _ + 1, h, Sum.inr (i, next) =>
      query i fun a => weaken (Nat.le_of_succ_le_succ h) (next a)

@[simp] theorem run_weaken (h : q ≤ r) (T : DTree I A O q) (read : I → A) :
    run read (weaken h T) = run read T := by
  induction r generalizing q with
  | zero =>
      cases q with
      | zero => rfl
      | succ q => exact False.elim (Nat.not_succ_le_zero _ h)
  | succ r ih =>
      cases q with
      | zero => rfl
      | succ q =>
          rcases T with o | ⟨i, next⟩
          · rfl
          · simp [weaken, run, query, ih]

/-- Run a second tree selected by the first output; budgets add. -/
def bind : {q r : ℕ} → DTree I A O q → (O → DTree I A P r) → DTree I A P (q + r)
  | 0, r, o, f => (f o).cast (Nat.zero_add r).symm
  | q + 1, r, Sum.inl o, f => weaken (by omega) (f o)
  | q + 1, r, Sum.inr (i, next), f =>
      (query i fun a => bind (next a) f).cast (Nat.succ_add q r).symm

/-- Adaptive composition preserves the output semantics and adds realized costs. -/
theorem run_bind (T : DTree I A O q) (f : O → DTree I A P r) (read : I → A) :
    run read (bind T f) =
      ((run read (f (T.eval read))).1, T.cost read + (run read (f (T.eval read))).2) := by
  induction q with
  | zero =>
      rw [bind, run_cast]
      simp [eval, cost, run]
  | succ q ih =>
      rcases T with o | ⟨i, next⟩
      · simp [bind, eval, cost, run]
      · rw [bind, run_cast, run_query, ih]
        simp [eval, cost, run, Nat.add_assoc, Nat.add_comm]

/-- The transcript's length agrees with the operational query counter. -/
theorem transcript_length (T : DTree I A O q) (read : I → A) :
    (transcript read T).length = T.cost read := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rcases T with o | ⟨i, next⟩
      · rfl
      · simp [transcript, cost, run, ih]

end CutQueryComplexity.DTree
