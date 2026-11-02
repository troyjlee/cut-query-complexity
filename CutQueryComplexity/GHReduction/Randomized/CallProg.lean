import CutQueryComplexity.GHReduction.Randomized.Interpret
import CutQueryComplexity.GHReduction.Programs

/-! # Deterministic programs with explicit s-t calls

`CallProg V α` is the unbudgeted analogue of `CallTree`, as `Prog` is of
`DTree`: a free monad over cut queries and s-t calls. The deterministic parts of
the Gomory-Hu reduction are written in it.

* `compile Q p q` turns a program into a call tree of budget `q`, charging one
  unit per cut query and `Q k` per call on `k` vertices, and returning `none`
  when the budget runs out.
* `idealEval G p` and `idealCost G Q p` are the output and the charged cost of
  the ideal run, in which calls return canonical shores. If the charged cost
  fits the budget, the compiled tree's ideal law is the point mass at
  `some (idealEval G p)` (`interpIdeal_compile`).
* `toProg A p` runs the calls with an exact deterministic family `A`. On a
  promised graph it evaluates to the ideal output (`eval_toProg`), within the
  ideal charged cost (`cost_toProg_le`).
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section

/-- Deterministic programs with cut queries and s-t calls. -/
inductive CallProg (V : Type) (α : Type) : Type where
  /-- Return a value. -/
  | pure : α → CallProg V α
  /-- Ask the cut value of a vertex set. -/
  | query : Finset V → (ℝ → CallProg V α) → CallProg V α
  /-- Ask for the canonical s-t shore of the contraction along `π`. -/
  | call (k : ℕ) (π : V → Fin k) (s t : Fin k) (hst : s ≠ t) :
      (Finset (Fin k) → CallProg V α) → CallProg V α

namespace CallProg

variable {V : Type} {α β : Type}

def bind : CallProg V α → (α → CallProg V β) → CallProg V β
  | pure a, f => f a
  | query S next, f => query S (fun x => bind (next x) f)
  | call k π s t hst next, f => call k π s t hst (fun S => bind (next S) f)

instance : Monad (CallProg V) where
  pure := CallProg.pure
  bind := CallProg.bind

/-- Ask one cut value. -/
def ask (S : Finset V) : CallProg V ℝ := query S pure

/-- Make one s-t call. -/
def stCall (k : ℕ) (π : V → Fin k) (s t : Fin k) (hst : s ≠ t) :
    CallProg V (Finset (Fin k)) :=
  call k π s t hst pure

/-- Free postprocessing of the output. -/
def map (f : α → β) (p : CallProg V α) : CallProg V β := p.bind (fun a => pure (f a))

/-- Compile within budget `q`, charging `Q k` per call. The result is `none` when
the budget runs out. -/
def compile (Q : ℕ → ℕ) : CallProg V α → (q : ℕ) → CallTree V Q (Option α) q
  | pure a, q => CallTree.up (Nat.zero_le q) (CallTree.ret (some a))
  | query _ _, 0 => CallTree.ret none
  | query S next, q + 1 => CallTree.query S (fun x => compile Q (next x) q)
  | call k π s t hst next, q =>
      if h : Q k ≤ q then
        CallTree.up (by omega)
          (CallTree.call k π s t hst (fun S => compile Q (next S) (q - Q k)))
      else CallTree.up (Nat.zero_le q) (CallTree.ret none)

@[simp] theorem prog_eval_query (read : Finset V → ℝ) (S : Finset V)
    (next : ℝ → Prog (Finset V) ℝ α) :
    Prog.eval read (Prog.query S next) = Prog.eval read (next (read S)) := rfl

@[simp] theorem prog_cost_query (read : Finset V → ℝ) (S : Finset V)
    (next : ℝ → Prog (Finset V) ℝ α) :
    Prog.cost read (Prog.query S next) = Prog.cost read (next (read S)) + 1 := rfl

variable [Fintype V] [DecidableEq V]

/-- Output of the ideal run. -/
def idealEval (G : WeightedGraph V) : CallProg V α → α
  | pure a => a
  | query S next => idealEval G (next (G.cut S))
  | call _ π s t _ next => idealEval G (next (idealShore (G.contract π) s t))

/-- Charged cost of the ideal run: one per cut query and `Q k` per call. -/
def idealCost (G : WeightedGraph V) (Q : ℕ → ℕ) : CallProg V α → ℕ
  | pure _ => 0
  | query S next => idealCost G Q (next (G.cut S)) + 1
  | call k π s t _ next => idealCost G Q (next (idealShore (G.contract π) s t)) + Q k

theorem idealEval_bind (G : WeightedGraph V) (p : CallProg V α) (f : α → CallProg V β) :
    idealEval G (p.bind f) = idealEval G (f (idealEval G p)) := by
  induction p with
  | pure a => rfl
  | query S next ih => exact ih _
  | call k π s t hst next ih => exact ih _

theorem idealCost_bind (G : WeightedGraph V) (Q : ℕ → ℕ) (p : CallProg V α)
    (f : α → CallProg V β) :
    idealCost G Q (p.bind f) = idealCost G Q p + idealCost G Q (f (idealEval G p)) := by
  induction p with
  | pure a => simp [bind, idealCost, idealEval]
  | query S next ih =>
      simp only [bind, idealCost, idealEval, ih]
      omega
  | call k π s t hst next ih =>
      simp only [bind, idealCost, idealEval, ih]
      omega

/-- With enough budget for the ideal run, compilation does not change the ideal output. -/
theorem interpIdeal_compile (G : WeightedGraph V) (Q : ℕ → ℕ) (p : CallProg V α) (q : ℕ)
    (h : idealCost G Q p ≤ q) :
    CallTree.interpIdeal G (compile Q p q) = PMF.pure (some (idealEval G p)) := by
  induction p generalizing q with
  | pure a => simp [compile, CallTree.interpIdeal, idealEval]
  | query S next ih =>
      cases q with
      | zero => simp [idealCost] at h
      | succ q =>
          simp only [compile, CallTree.interpIdeal, idealEval]
          exact ih _ q (by simp only [idealCost] at h; omega)
  | call k π s t hst next ih =>
      have hk : Q k ≤ q := by simp only [idealCost] at h; omega
      simp only [compile, dite_eq_left hk, CallTree.interpIdeal, idealEval]
      exact ih _ (q - Q k) (by simp only [idealCost] at h; omega)

/-- Run the calls with an exact deterministic family. -/
def toProg {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q) :
    CallProg V α → Prog (Finset V) ℝ α
  | pure a => Prog.pure a
  | query S next => Prog.query S (fun x => toProg A (next x))
  | call k π s t _ next =>
      (liftDTree (contractDetProgram π (A.program k s t))).bind (fun S => toProg A (next S))

/-- On a promised graph, an exact family gives the ideal output. -/
theorem eval_toProg {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q) (G : WeightedGraph V)
    (hG : InputPromise M G) (p : CallProg V α) :
    Prog.eval G.cut (toProg A p) = idealEval G p := by
  induction p with
  | pure a => rfl
  | query S next ih =>
      simp only [toProg, idealEval, prog_eval_query]
      exact ih _
  | call k π s t hst next ih =>
      simp only [toProg, idealEval, Prog.eval_bind, liftDTree_eval, contractDetProgram_eval]
      rw [← eq_idealShore hst (A.correct k s t hst _ (call_promise G hG π).1
        (call_promise G hG π).2)]
      exact ih _

/-- On a promised graph, an exact family stays within the ideal charged cost. -/
theorem cost_toProg_le {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q) (G : WeightedGraph V)
    (hG : InputPromise M G) (p : CallProg V α) :
    Prog.cost G.cut (toProg A p) ≤ idealCost G Q p := by
  induction p with
  | pure a => simp [toProg, idealCost]
  | query S next ih =>
      simp only [toProg, idealCost, prog_cost_query]
      exact Nat.add_le_add_right (ih _) 1
  | call k π s t hst next ih =>
      simp only [toProg, idealCost, Prog.cost_bind, liftDTree_eval, contractDetProgram_eval]
      rw [← eq_idealShore hst (A.correct k s t hst _ (call_promise G hG π).1
        (call_promise G hG π).2), Nat.add_comm]
      exact Nat.add_le_add (ih _) (liftDTree_cost_le _ G.cut)

/-- The compiled deterministic program, as the existing reduction builds it,
returns the ideal output when the ideal charged cost fits the budget. -/
theorem toDTree_toProg_eval {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (p : CallProg V α) (q : ℕ)
    (h : idealCost G Q p ≤ q) :
    (Prog.toDTree (toProg A p) q).eval G.cut = some (idealEval G p) := by
  rw [Prog.toDTree_eval G.cut _ q ((cost_toProg_le A G hG p).trans h), eval_toProg A G hG p]

end CallProg
end
end CutQueryComplexity.GHReduction.Randomized
