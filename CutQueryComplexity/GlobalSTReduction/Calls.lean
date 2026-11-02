import CutQueryComplexity.GlobalSTReduction.Replies

/-! # Compiled call programs with a fallible primitive

A call program `p` is compiled at budget `q` with `CallProg.compile Q`, and the
randomized interpretation `CallTree.interpRand P` runs the family's program `P`
afresh at every call, on the contracted oracle. Every run on every oracle stays
within `q` by the budget index of the tree.

* `support_interpRand_compile`: if the charged cost is at most `q` for every
  history (`CostWithin`), the compiled program never runs out of budget, and a
  guarantee for arbitrary replies holds on every supported run.
* `mass_interpRand_compile_le`: if each call misses a minimum shore with
  probability at most `δ` (`OptFailsAtMost`), every run makes at most `N` calls
  (`CallsWithin`), and every run with minimum replies satisfies `post`, then the
  output fails `post` with probability at most `δ · N`.

The second statement is an adaptive union bound. It is proved by induction over
the program: at a call, the reply is a minimum shore except with probability
`δ` (conditionally on the history so far), and only runs with minimum replies
are followed further. No independence between calls and no unique ideal reply
is assumed; the graph and terminals of each call are fixed by its history.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability GHReduction.Randomized

variable {V : Type} [Fintype V] [DecidableEq V] {Q : ℕ → ℕ} {α : Type}

omit [DecidableEq V] in
/-- Within the charged budget, every supported output is `some a` with `post a`
whenever `post` holds under arbitrary replies. -/
theorem support_interpRand_compile (P : STPrograms Q) (read : Finset V → ℝ) {post : α → Prop}
    (p : CallProg V α) {q : ℕ} (hq : CostWithin Q p q) (h : Holds read (anyReply V) post p) :
    ∀ o ∈ ((CallTree.interpRand P (CallProg.compile Q p q)).eval read).support,
      ∃ a, o = some a ∧ post a := by
  induction p generalizing q with
  | pure a =>
      intro o ho
      simp only [CallProg.compile, CallTree.eval_interpRand_up, CallTree.eval_interpRand_ret,
        PMF.support_pure, Set.mem_singleton_iff] at ho
      exact ⟨a, ho, h⟩
  | query S next ih =>
      obtain ⟨hq1, hnext⟩ := hq
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      intro o ho
      simp only [CallProg.compile, CallTree.eval_interpRand_query] at ho
      exact ih (read S) (by simpa using hnext (read S)) h o ho
  | call k π s t hst next ih =>
      obtain ⟨hk, hnext⟩ := hq
      intro o ho
      simp only [CallProg.compile, dite_eq_left hk, CallTree.eval_interpRand_up,
        CallTree.eval_interpRand_call] at ho
      obtain ⟨S, _, hS⟩ := (PMF.mem_support_bind_iff _ _ _).mp ho
      exact ih S (hnext S) (h S trivial) o hS

omit [DecidableEq V] in
/-- Without a cost hypothesis: every supported `some a` satisfies a guarantee that
holds under arbitrary replies (a truncated run returns `none`). -/
theorem support_interpRand_compile_some (P : STPrograms Q) (read : Finset V → ℝ)
    {post : α → Prop} (p : CallProg V α) (q : ℕ) (h : Holds read (anyReply V) post p) :
    ∀ o ∈ ((CallTree.interpRand P (CallProg.compile Q p q)).eval read).support,
      ∀ a, o = some a → post a := by
  induction p generalizing q with
  | pure a =>
      intro o ho b hb
      simp only [CallProg.compile, CallTree.eval_interpRand_up, CallTree.eval_interpRand_ret,
        PMF.support_pure, Set.mem_singleton_iff] at ho
      rw [ho, Option.some.injEq] at hb
      exact hb ▸ h
  | query S next ih =>
      intro o ho b hb
      cases q with
      | zero =>
          simp only [CallProg.compile, CallTree.eval_interpRand_ret, PMF.support_pure,
            Set.mem_singleton_iff] at ho
          rw [ho] at hb
          exact absurd hb (by simp)
      | succ q =>
          simp only [CallProg.compile, CallTree.eval_interpRand_query] at ho
          exact ih (read S) q h o ho b hb
  | call k π s t hst next ih =>
      intro o ho b hb
      by_cases hk : Q k ≤ q
      · simp only [CallProg.compile, dite_eq_left hk, CallTree.eval_interpRand_up,
          CallTree.eval_interpRand_call] at ho
        obtain ⟨S, _, hS⟩ := (PMF.mem_support_bind_iff _ _ _).mp ho
        exact ih S (q - Q k) (h S trivial) o hS b hb
      · simp only [CallProg.compile, dite_eq_right hk, CallTree.eval_interpRand_up,
          CallTree.eval_interpRand_ret, PMF.support_pure, Set.mem_singleton_iff] at ho
        rw [ho] at hb
        exact absurd hb (by simp)

/-- Adaptive union bound over the calls of a compiled program. -/
theorem mass_interpRand_compile_le (P : STPrograms Q) {δ : ℝ≥0∞} (hP : OptFailsAtMost P δ)
    (G : WeightedGraph V) {post : α → Prop} (p : CallProg V α) {q N : ℕ}
    (hq : CostWithin Q p q) (hN : CallsWithin p N) (h : Holds G.cut (optReply G) post p) :
    mass ((CallTree.interpRand P (CallProg.compile Q p q)).eval G.cut)
      (fun o => ¬∃ a, o = some a ∧ post a) ≤ δ * N := by
  induction p generalizing q N with
  | pure a =>
      have hout : ∃ b, (some a : Option α) = some b ∧ post b := ⟨a, rfl, h⟩
      simp only [CallProg.compile, CallTree.eval_interpRand_up, CallTree.eval_interpRand_ret,
        mass_pure, hout, not_true_eq_false, ite_false]
      exact bot_le
  | query S next ih =>
      obtain ⟨hq1, hnext⟩ := hq
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp only [CallProg.compile, CallTree.eval_interpRand_query]
      exact ih (G.cut S) (by simpa using hnext (G.cut S)) (by simpa using hN.2 (G.cut S)) h
  | call k π s t hst next ih =>
      obtain ⟨hk, hnext⟩ := hq
      obtain ⟨hN1, hNnext⟩ := hN
      have hN1' : 1 ≤ N := hN1
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      simp only [CallProg.compile, dite_eq_left hk, CallTree.eval_interpRand_up,
        CallTree.eval_interpRand_call]
      refine (mass_bind_le_add _ _ (fun S => ¬IsSTMinCut (G.contract π) s t S) _
        (δ := δ) (ε := δ * N') ?_ (fun S hS => ?_)).trans ?_
      · rw [CallTree.callProgram_eval]
        exact hP k s t hst _
      · exact ih S (hnext S) (by simpa using hNnext S) (h S (not_not.mp hS))
      · push_cast
        rw [mul_add, mul_one, add_comm]

end
end CutQueryComplexity.GlobalSTReduction
