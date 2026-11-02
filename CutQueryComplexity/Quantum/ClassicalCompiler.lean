import CutQueryComplexity.Quantum.Model
import QuantumQueryComplexity.Quantum.PostQuery

/-! # Exact finite-alphabet compilation of adaptive deterministic trees

One native quantum query simulates one classical whole-answer query. Each
step preserves its measurement history in finite workspace using `postQuery`.
Halted branches select the idle index. Output types may be infinite.
-/

namespace CutQueryComplexity

open QuantumQueryComplexity
open scoped Classical

noncomputable section

variable {X I A O P : Type} [Fintype X] [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A]

/-- Correct post-query decoding preserves the error bound of the first algorithm. -/
theorem computes_postQuery {W : Type} [Fintype W] [DecidableEq W]
    [DecidableEq O] [DecidableEq P] {T : QAlg I A O W} {Q k : ℕ}
    {read : X → I → A} {f : X → O} {g : X → P} {ε : ℝ}
    (hT : ComputesWithErrorOn T Q read f ε)
    (sel : O → Fin k → Option I) (dec : O → (Fin k → Option A) → P)
    (hdec : ∀ x, dec (f x) (fun j => (sel (f x) j).map (read x)) = g x) :
    ComputesWithErrorOn (T.postQuery sel Q dec) (Q + k) read g ε := by
  intro x
  apply (hT x).trans
  rw [postQuery_prob, QAlg.prob, qProb]
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : T.readout p = f x
  · simp only [hp, hdec x, if_true]
    exact le_rfl
  · rw [if_neg hp]
    split
    · exact Complex.normSq_nonneg _
    · exact le_rfl

/-- Computing a selected valid witness also solves the full output relation. -/
theorem computes_solves_relation {W : Type} [Fintype W] [DecidableEq W]
    {T : QAlg I A O W} {q : ℕ} {read : X → I → A} {f : X → O}
    {Good : X → O → Prop} [∀ x, DecidablePred (Good x)] {ε : ℝ}
    (hT : ComputesWithErrorOn T q read f ε) (hf : ∀ x, Good x (f x)) :
    SolvesWithErrorOn T q read Good ε := by
  intro x
  apply (hT x).trans
  rw [QAlg.prob, qProb, successProbOn, goodProb_eq_sum_ite]
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : T.readout p = f x
  · simp only [hp, hf x, if_true]
    exact le_rfl
  · rw [if_neg hp]
    split
    · exact Complex.normSq_nonneg _
    · exact le_rfl

namespace DTree

variable [Inhabited A]

/-- The next query, or an idle query after a branch has halted. -/
def nextQuery {q : ℕ} : DTree I A O (q + 1) → Fin 1 → Option I
  | Sum.inl _, _ => none
  | Sum.inr (i, _), _ => some i

/-- Consume one answer, retaining halted outputs at the smaller remaining budget. -/
def nextTree {q : ℕ} (T : DTree I A O (q + 1)) (ans : Fin 1 → Option A) :
    DTree I A O q := match T with
  | Sum.inl o => pure o
  | Sum.inr (_, next) => next ((ans 0).getD default)

/-- The deterministic semantics is preserved by one compiled step. -/
theorem eval_nextTree {q : ℕ} (T : DTree I A O (q + 1)) (read : I → A) :
    (nextTree T (fun j => (nextQuery T j).map read)).eval read = T.eval read := by
  rcases T with o | ⟨i, next⟩
  · simp [nextTree, nextQuery, eval, run]
  · rfl

/-- Complete a quantum computation whose output describes a remaining classical tree.
This inductive construction handles adaptive choices while preserving the error bound. -/
theorem exists_finish {q Q : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {T : QAlg I A (DTree I A O q) W} {read : X → I → A}
    {f : X → DTree I A O q} {ε : ℝ}
    (hT : ComputesWithErrorOn T Q read f ε) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work) (B : QAlg I A O Work),
      ComputesWithErrorOn B (Q + q) read (fun x => (f x).eval (read x)) ε := by
  classical
  induction q generalizing W Q with
  | zero => exact ⟨W, inferInstance, inferInstance, T, hT⟩
  | succ q ih =>
      let step (x : X) := nextTree (f x) (fun j => (nextQuery (f x) j).map (read x))
      have hstep : ComputesWithErrorOn (T.postQuery nextQuery Q nextTree)
          (Q + 1) read step ε := computes_postQuery hT nextQuery nextTree (fun _ => rfl)
      obtain ⟨Work, hWork, hWorkEq, B, hB⟩ := ih hstep
      refine ⟨Work, hWork, hWorkEq, B, ?_⟩
      have hcount : Q + 1 + q = Q + (q + 1) := by omega
      simpa only [hcount, step, eval_nextTree] using hB

/-- Every bounded adaptive deterministic tree over a finite inhabited answer alphabet
has an exact quantum implementation with the same query budget. -/
theorem exists_quantum {q : ℕ} (T : DTree I A O q) (read : X → I → A) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (B : QAlg I A O W),
      ComputesWithErrorOn B q read (fun x => T.eval (read x)) 0 := by
  classical
  have h : ComputesWithErrorOn (constAlg I A T) 0 read (fun _ => T) 0 :=
    computesWithErrorOn_const read T (fun _ => rfl) le_rfl
  simpa only [Nat.zero_add] using exists_finish h

end DTree

/-- Exact classical algorithms compile at unit query cost in the compatible finite model. -/
theorem quantumComplexity_le_deterministic [Inhabited A] (read : X → I → A)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] {ε : ℝ} (hε : 0 ≤ ε) :
    quantumComplexity read Good ε ≤ deterministicComplexity read Good := by
  apply queryComplexity_mono
  rintro q ⟨T, hT⟩
  obtain ⟨W, hW, hWEq, B, hB⟩ := T.exists_quantum read
  exact ⟨W, hW, hWEq, B, (computes_solves_relation hB hT).mono hε⟩

end
end CutQueryComplexity
