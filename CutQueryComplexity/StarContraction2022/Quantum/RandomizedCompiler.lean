import CutQueryComplexity.StarContraction2022.Quantum.FinitePolicy
import CutQueryComplexity.Quantum.ClassicalCompiler
import QuantumQueryComplexity.Quantum.Mixture
import QuantumQueryComplexity.Quantum.Routine
import Mathlib.Basic.ENNReal.BigOperators

/-! # Exact compilation of finite-alphabet randomized query trees

First sample a complete deterministic policy using the proved finite-policy
distribution. Each policy is implemented by the existing operational
deterministic compiler, on every possible answer table. The actual quantum
mixture construction places these implementations in orthogonal sectors.
Its Born output law equals the original randomized tree's output law exactly.
The physical schedule has length q, including idle calls; the original varying
classical count is separately retained by `policies_run`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum

noncomputable section

open QuantumQueryComplexity
open scoped Matrix

namespace RandomizedCompiler

variable {S O : Type} [Fintype S]

theorem pmf_toReal_sum (p : PMF S) : ∑ s, (p s).toReal = 1 := by
  have hsum : ∑ s, p s = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [← ENNReal.toReal_sum (fun s _ => p.apply_ne_top s), hsum, ENNReal.toReal_one]

theorem pmf_map_toReal [DecidableEq O] (p : PMF S) (f : S → O) (o : O) :
    ((p.map f) o).toReal = ∑ s, if o = f s then (p s).toReal else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp
  · intro s _
    split_ifs
    · exact p.apply_ne_top s
    · exact ENNReal.zero_ne_top

theorem pmf_event_toReal (p : PMF S) (Good : S → Prop) [DecidablePred Good] :
    (p.toOuterMeasure {s | Good s}).toReal =
      ∑ s, if Good s then (p s).toReal else 0 := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype]
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hfinite : ∀ s ∈ (Finset.univ : Finset S),
      (if Good s then p s else 0) ≠ (⊤ : ENNReal) := by
    intro s _
    split_ifs
    · exact p.apply_ne_top s
    · exact ENNReal.zero_ne_top
  rw [ENNReal.toReal_sum hfinite]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

end RandomizedCompiler

variable {I A O : Type} [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O] [Inhabited A]

/-- Turn the deterministic compiler's zero-error guarantee into the complete
point-mass outcome law. This uses the normalized operational state. -/
theorem quantum_prob_eq_ite_of_exact {W : Type} [Fintype W] [DecidableEq W]
    (B : QAlg I A O W) (read : I → A) (q : ℕ) (target : O)
    (h : 1 ≤ B.prob read q target) (o : O) :
    B.prob read q o = if o = target then 1 else 0 := by
  by_cases ho : o = target
  · subst o
    rw [if_pos rfl]
    exact le_antisymm (B.prob_le_one read q target) h
  · rw [if_neg ho]
    have hadd := qProb_add_qProb_le_one (B.state_isQState read q) B.readout ho
    change B.prob read q o + B.prob read q target ≤ 1 at hadd
    have hnonneg := B.prob_nonneg read q o
    linarith

/-- The deterministic implementation is selected before every answer table,
by instantiating the existing compiler on the entire finite table type. -/
def policyWork {q : ℕ} (D : DTree I A O q) : Type :=
  (DTree.exists_quantum D (id : (I → A) → I → A)).choose

instance policyWorkFintype {q : ℕ} (D : DTree I A O q) : Fintype (policyWork D) :=
  (DTree.exists_quantum D (id : (I → A) → I → A)).choose_spec.choose

instance policyWorkDecidableEq {q : ℕ} (D : DTree I A O q) :
    DecidableEq (policyWork D) :=
  (DTree.exists_quantum D (id : (I → A) → I → A)).choose_spec.choose_spec.choose

def policyAlg {q : ℕ} (D : DTree I A O q) : QAlg I A O (policyWork D) :=
  (DTree.exists_quantum D (id : (I → A) → I → A)).choose_spec.choose_spec.choose_spec.choose

theorem policyAlg_exact {q : ℕ} (D : DTree I A O q) :
    ComputesWithErrorOn (policyAlg D) q id (fun read => D.eval read) 0 := by
  obtain rfl := Subsingleton.elim (inferInstance : DecidableEq O) (Classical.decEq O)
  exact (DTree.exists_quantum D (id : (I → A) → I → A)).choose_spec.choose_spec.choose_spec.choose_spec

theorem policyAlg_prob {q : ℕ} (D : DTree I A O q) (read : I → A) (o : O) :
    (policyAlg D).prob read q o = if o = D.eval read then 1 else 0 := by
  apply quantum_prob_eq_ite_of_exact
  simpa only [sub_zero, id_eq] using policyAlg_exact D read

/-- Actual finite-sector quantum mixture, chosen before every oracle. No
solver, finite random seed, successful-run or cost record is supplied. -/
theorem exists_randomizedCompiler {q : ℕ} (T : RTree I A O q) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (B : QAlg I A O Work),
      ∀ (read : I → A) (o : O),
        B.prob read q o = (((RTree.run read T).map Prod.fst) o).toReal := by
  classical
  let weight (D : DTree I A O q) : ℝ := ((policies T) D).toReal
  have hp : ∀ D, 0 ≤ weight D := fun _ => ENNReal.toReal_nonneg
  have hsum : ∑ D, weight D = 1 := RandomizedCompiler.pmf_toReal_sum (policies T)
  obtain ⟨Work, hF, hD, B, hB⟩ := exists_mixture
    (Ω := DTree I A O q) (W := fun D : DTree I A O q => policyWork D)
    weight hp hsum (fun _ => q) q (fun _ => le_rfl) (fun D => policyAlg D)
  letI := hF
  letI := hD
  refine ⟨Work, hF, hD, B, ?_⟩
  intro read o
  rw [hB]
  simp_rw [policyAlg_prob]
  rw [← policies_output T read, RandomizedCompiler.pmf_map_toReal]
  apply Finset.sum_congr rfl
  intro D _
  split_ifs <;> simp [weight]

def randomizedWork {q : ℕ} (T : RTree I A O q) : Type :=
  (exists_randomizedCompiler T).choose

instance randomizedWorkFintype {q : ℕ} (T : RTree I A O q) :
    Fintype (randomizedWork T) := (exists_randomizedCompiler T).choose_spec.choose

instance randomizedWorkDecidableEq {q : ℕ} (T : RTree I A O q) :
    DecidableEq (randomizedWork T) :=
  (exists_randomizedCompiler T).choose_spec.choose_spec.choose

/-- Named public compiler. Its inputs are the bounded randomized tree and
finite structural instances, with no oracle or semantic promise. -/
def randomizedAlg {q : ℕ} (T : RTree I A O q) : QAlg I A O (randomizedWork T) :=
  (exists_randomizedCompiler T).choose_spec.choose_spec.choose_spec.choose

theorem randomizedAlg_prob {q : ℕ} (T : RTree I A O q) (read : I → A) (o : O) :
    (randomizedAlg T).prob read q o = (((RTree.run read T).map Prod.fst) o).toReal :=
  (exists_randomizedCompiler T).choose_spec.choose_spec.choose_spec.choose_spec read o

/-- Fixed physical query schedule, including idle calls on halted branches. -/
def randomizedRoutine {q : ℕ} (T : RTree I A O q) : QRoutine I A (randomizedWork T) where
  len := q
  step := (randomizedAlg T).step
  step_unitary := (randomizedAlg T).step_unitary

@[simp] theorem randomizedRoutine_len {q : ℕ} (T : RTree I A O q) :
    (randomizedRoutine T).len = q := rfl

theorem randomizedRoutine_state {q : ℕ} (T : RTree I A O q) (read : I → A) :
    (randomizedRoutine T).run read *ᵥ (randomizedAlg T).init =
      (randomizedAlg T).state read q :=
  ((randomizedAlg T).state_eq_runUpto (randomizedRoutine T) rfl read q).symm

/-- Exact relational success for every event. Neither the event nor the
oracle occurs in the selected algorithm. -/
theorem randomizedAlg_successProb {q : ℕ} (T : RTree I A O q) (read : I → A)
    (Good : O → Prop) [DecidablePred Good] :
    goodProb (randomizedAlg T).readout Good ((randomizedAlg T).state read q) =
      T.successProb read Good := by
  rw [goodProb_eq_sum]
  change (∑ o, if Good o then (randomizedAlg T).prob read q o else 0) = _
  simp_rw [randomizedAlg_prob]
  rw [← RandomizedCompiler.pmf_event_toReal]
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- Exact transfer of any relational error bound; there is no compiler loss. -/
theorem randomizedAlg_solves_iff {X : Type} [Fintype X] {q : ℕ}
    (T : RTree I A O q) (read : X → I → A) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (ε : ℝ) :
    SolvesWithErrorOn (randomizedAlg T) q read Good ε ↔
      T.SolvesWithError read Good ε := by
  unfold SolvesWithErrorOn RTree.SolvesWithError successProbOn
  simp only [randomizedAlg_successProb]

/-- Zero-budget randomness is realized without any physical query. -/
theorem randomizedAlg_zero_prob (T : RTree I A O 0) (read : I → A) (o : O) :
    (randomizedAlg T).prob read 0 o = ((show PMF O from T) o).toReal := by
  let p : PMF O := T
  have h : (RTree.run read T).map Prod.fst = p := by
    calc
      _ = p.map (id : O → O) :=
        PMF.map_comp (fun x : O => (x, (0 : ℕ))) p (Prod.fst : O × ℕ → O)
      _ = p := PMF.map_id p
  exact (randomizedAlg_prob (q := 0) T read o).trans
    (congrArg (fun m : PMF O => (m o).toReal) h)

#print axioms RandomizedCompiler.pmf_toReal_sum
#print axioms RandomizedCompiler.pmf_map_toReal
#print axioms RandomizedCompiler.pmf_event_toReal
#print axioms quantum_prob_eq_ite_of_exact
#print axioms policyAlg_exact
#print axioms policyAlg_prob
#print axioms exists_randomizedCompiler
#print axioms randomizedAlg_prob
#print axioms randomizedRoutine_len
#print axioms randomizedRoutine_state
#print axioms randomizedAlg_successProb
#print axioms randomizedAlg_solves_iff
#print axioms randomizedAlg_zero_prob

end

end CutQueryComplexity.StarContraction2022.Quantum
