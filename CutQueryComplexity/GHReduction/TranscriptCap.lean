import CutQueryComplexity.Model.Randomized

/-! # Structural query caps against arbitrary answer transcripts

The answer to a query may have any probability distribution depending on the
entire preceding query-answer history. In particular, repeated queries need
not receive consistent answers. Each realized query extends that history and
consumes one level of the actual bounded randomized tree.

The cap below uses only the tree's type. Graph promises and correctness of
intermediate subroutines are irrelevant to this operational bound. A point
mass at a fixed oracle answer recovers the repository's ordinary semantics.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section

namespace TranscriptOracle

variable {I A O : Type} {q : ℕ}

/-- A response distribution chosen after seeing the current query and the
full prior history. History is stored with the newest pair first. -/
abbrev AnswerPolicy (I A : Type) := List (I × A) → I → PMF A

/-- Execute the given tree with history-dependent oracle answers. The result
records its output and the number of additional queries since `history`. -/
def run (answer : AnswerPolicy I A) :
    {q : ℕ} → RTree I A O q → List (I × A) → PMF (O × ℕ)
  | 0, T, _ => T.map (fun o => (o, 0))
  | _ + 1, T, history => T.bind fun action => match action with
    | Sum.inl o => PMF.pure (o, 0)
    | Sum.inr (i, next) => (answer history i).bind fun a =>
        (run answer (next a) ((i, a) :: history)).map (fun p => (p.1, p.2 + 1))

/-- Every supported execution obeys the cap, even when answers are randomized,
depend on previous answers, or disagree at two occurrences of the same query. -/
theorem cost_le (T : RTree I A O q) (answer : AnswerPolicy I A)
    (history : List (I × A)) {p : O × ℕ}
    (hp : p ∈ (run answer T history).support) : p.2 ≤ q := by
  induction q generalizing history p with
  | zero =>
    obtain ⟨o, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    exact le_rfl
  | succ q ih =>
    obtain ⟨action, _, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
    rcases action with o | ⟨i, next⟩
    · have heq := (PMF.mem_support_pure_iff _ _).mp hp
      subst p
      exact Nat.zero_le _
    · obtain ⟨a, _, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      exact Nat.succ_le_succ (ih (T := next a) (history := (i, a) :: history) hr)

/-- Fixed graph oracles are a special case, with the exact same output and
cost law. This is equality of the implemented executions, not an extra model
assumption. -/
theorem run_fixed (T : RTree I A O q) (read : I → A) (history : List (I × A)) :
    run (fun _ i => PMF.pure (read i)) T history = RTree.run read T := by
  induction q generalizing history with
  | zero => rfl
  | succ q ih =>
    simp only [run, RTree.run, PMF.pure_bind, ih]
    rfl

/-- Deterministic transcript-dependent answers inherit the same universal
cap; no consistency premise on `answer` is needed. -/
theorem deterministic_cost_le (T : RTree I A O q)
    (answer : List (I × A) → I → A) (history : List (I × A)) {p : O × ℕ}
    (hp : p ∈ (run (fun h i => PMF.pure (answer h i)) T history).support) : p.2 ≤ q :=
  cost_le T _ history hp

end TranscriptOracle

#print axioms TranscriptOracle.cost_le
#print axioms TranscriptOracle.run_fixed
#print axioms TranscriptOracle.deterministic_cost_le

end
end CutQueryComplexity.GHReduction
