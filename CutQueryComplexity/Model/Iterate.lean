import CutQueryComplexity.Model.RandomizedComposition
import CutQueryComplexity.Probability.Events

/-! # Iterating an adaptive step with fuel

`iterate step N s` runs a state transformer `N` times. Each step is an arbitrary
randomized query program whose choice may depend on the whole previous state, and
the total worst-case budget is `N` times the step budget.

Two generic tools make long adaptive runs tractable:

* **Failure accumulation.** Let `Inv N` be a fuel-indexed invariant. If one step
  started from `Inv (N+1)` breaks `Inv N` with probability at most `δ`, then `N`
  steps started from `Inv N` break `Inv 0` with probability at most `N·δ`. This is
  the conditional union bound; no independence between steps is assumed.
* **Cost accounting.** Let `acc` be a counter stored in the state. If every
  supported execution of one step makes at most `acc s' − acc s` actual queries,
  the same holds for the iteration. On good histories, a bound on the final
  counter therefore bounds the actual number of queries.
-/

namespace CutQueryComplexity.RTree
noncomputable section
open scoped ENNReal
open Probability
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {I A S : Type} {b : ℕ}

/-- Run `step` `N` times, threading the state. -/
def iterate (step : S → RTree I A S b) : (N : ℕ) → S → RTree I A S (N * b)
  | 0, s => pure (PMF.pure s)
  | N + 1, s => ((step s).bind (fun s' => iterate step N s')).cast (by ring)

@[simp] theorem eval_iterate_zero (step : S → RTree I A S b) (s : S) (read : I → A) :
    (iterate step 0 s).eval read = PMF.pure s := by
  simp [iterate]

theorem eval_iterate_succ (step : S → RTree I A S b) (N : ℕ) (s : S) (read : I → A) :
    (iterate step (N + 1) s).eval read =
      ((step s).eval read).bind (fun s' => (iterate step N s').eval read) := by
  rw [iterate, eval_cast, eval_bind]

/-- **Failure accumulation** along an adaptive run. -/
theorem iterate_failure_le (step : S → RTree I A S b) (read : I → A) (Inv : ℕ → S → Prop)
    (δ : ℝ≥0∞) (h : ∀ N s, Inv (N + 1) s → mass ((step s).eval read) (fun s' => ¬Inv N s') ≤ δ) :
    ∀ N s, Inv N s → mass ((iterate step N s).eval read) (fun s' => ¬Inv 0 s') ≤ N * δ := by
  intro N
  induction N with
  | zero =>
      intro s hs
      simp [hs]
  | succ N ih =>
      intro s hs
      rw [eval_iterate_succ]
      calc
        _ ≤ δ + N * δ := mass_bind_le_add _ _ (fun s' => ¬Inv N s') _ (h N s hs)
              (fun s' hs' => ih s' (not_not.mp hs'))
        _ = ((N + 1 : ℕ) : ℝ≥0∞) * δ := by push_cast; ring

theorem mem_support_run_bind {P : Type} {q r : ℕ} (T : RTree I A S q) (f : S → RTree I A P r)
    (read : I → A) {p : P × ℕ} (hp : p ∈ (run read (T.bind f)).support) :
    ∃ s c, (s, c) ∈ (run read T).support ∧ ∃ c', (p.1, c') ∈ (run read (f s)).support ∧
      p.2 = c + c' := by
  rw [run_bind] at hp
  obtain ⟨⟨s, c⟩, hs, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  obtain ⟨⟨o, c'⟩, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  exact ⟨s, c, hs, c', ho, rfl⟩

/-- **Cost accounting** along an iteration, through a counter in the state. -/
theorem iterate_cost (step : S → RTree I A S b) (read : I → A) (acc : S → ℕ)
    (h : ∀ s p, p ∈ (run read (step s)).support → acc s + p.2 ≤ acc p.1) :
    ∀ N s p, p ∈ (run read (iterate step N s)).support → acc s + p.2 ≤ acc p.1 := by
  intro N
  induction N with
  | zero =>
      intro s p hp
      simp only [iterate, run_pure] at hp
      obtain ⟨s', hs', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      rw [(PMF.mem_support_pure_iff _ _).mp hs']
      simp
  | succ N ih =>
      intro s p hp
      rw [iterate, run_cast] at hp
      obtain ⟨s', c, hs', c', hp', he⟩ := mem_support_run_bind _ _ read hp
      have h1 := h s (s', c) hs'
      have h2 := ih s' (p.1, c') hp'
      simp only at h1 h2
      omega

/-- An executed output's cost is at most the counter increase. -/
theorem eval_cost_of_iterate (step : S → RTree I A S b) (read : I → A) (acc : S → ℕ)
    (h : ∀ s p, p ∈ (run read (step s)).support → acc s + p.2 ≤ acc p.1) (N : ℕ) (s : S)
    {p : S × ℕ} (hp : p ∈ (run read (iterate step N s)).support) : p.2 ≤ acc p.1 - acc s := by
  have := iterate_cost step read acc h N s p hp
  omega

end
end CutQueryComplexity.RTree
