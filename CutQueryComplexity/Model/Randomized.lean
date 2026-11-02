import CutQueryComplexity.Model.Deterministic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Bounded randomized query trees

The next action is a probability mass function conditional on the transcript.
There is no finite-answer or fixed finite random-seed assumption. Every outcome
in the operational distribution obeys the same worst-case query budget.
-/

namespace CutQueryComplexity

/-- A stochastic decision tree with at most `q` oracle calls. -/
def RTree (I A O : Type) : ℕ → Type
  | 0 => PMF O
  | q + 1 => PMF (O ⊕ (I × (A → RTree I A O q)))

namespace RTree

variable {I A O X : Type} {q : ℕ}

noncomputable section

/-- Distribution of the output and the actual query count. -/
def run (read : I → A) : {q : ℕ} → RTree I A O q → PMF (O × ℕ)
  | 0, T => T.map (fun o => (o, 0))
  | _ + 1, T => T.bind fun action => match action with
    | Sum.inl o => PMF.pure (o, 0)
    | Sum.inr (i, next) => (run read (next (read i))).map (fun p => (p.1, p.2 + 1))

/-- Every supported execution respects the advertised worst-case budget. -/
theorem cost_le (T : RTree I A O q) (read : I → A) {p : O × ℕ}
    (hp : p ∈ (run read T).support) : p.2 ≤ q := by
  induction q generalizing p with
  | zero =>
      obtain ⟨o, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      exact le_rfl
  | succ q ih =>
      obtain ⟨action, _, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      rcases action with o | ⟨i, next⟩
      · have heq := (PMF.mem_support_pure_iff _ _).mp hp
        subst p
        exact Nat.zero_le _
      · obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
        exact Nat.succ_le_succ (ih (next (read i)) hr)

/-- Embed a deterministic tree by using point masses for all random choices. -/
def ofDeterministic : {q : ℕ} → DTree I A O q → RTree I A O q
  | 0, o => PMF.pure o
  | _ + 1, Sum.inl o => PMF.pure (Sum.inl o)
  | _ + 1, Sum.inr (i, next) =>
      PMF.pure (Sum.inr (i, fun a => ofDeterministic (next a)))

/-- The embedding preserves the exact output and cost, with probability one. -/
@[simp] theorem run_ofDeterministic (T : DTree I A O q) (read : I → A) :
    run read (ofDeterministic T) = PMF.pure (DTree.run read T) := by
  induction q with
  | zero => exact PMF.pure_map _ _
  | succ q ih =>
      rcases T with o | ⟨i, next⟩
      · simp [ofDeterministic, run, DTree.run]
      · simp [ofDeterministic, run, DTree.run, ih, PMF.pure_map]

/-- Real-valued probability of a valid output, summing over all realized costs. -/
def successProb (T : RTree I A O q) (read : I → A) (Good : O → Prop) : ℝ :=
  ((run read T).toOuterMeasure {p | Good p.1}).toReal

/-- Per-input bounded-error relational correctness. -/
def SolvesWithError (T : RTree I A O q) (read : X → I → A)
    (Good : X → O → Prop) (ε : ℝ) : Prop :=
  ∀ x, 1 - ε ≤ T.successProb (read x) (Good x)

theorem SolvesWithError.mono {T : RTree I A O q} {read : X → I → A}
    {Good : X → O → Prop} {ε δ : ℝ} (h : T.SolvesWithError read Good ε)
    (hεδ : ε ≤ δ) : T.SolvesWithError read Good δ := by
  intro x
  exact (sub_le_sub_left hεδ 1).trans (h x)

/-- An exact deterministic algorithm is a zero-error randomized algorithm. -/
theorem ofDeterministic_solves {T : DTree I A O q} {read : X → I → A}
    {Good : X → O → Prop} (h : T.Solves read Good) :
    (ofDeterministic T).SolvesWithError read Good 0 := by
  intro x
  classical
  have hx : Good x (DTree.run (read x) T).1 := h x
  simp [successProb, PMF.toOuterMeasure_pure_apply, hx]

end
end RTree
end CutQueryComplexity
