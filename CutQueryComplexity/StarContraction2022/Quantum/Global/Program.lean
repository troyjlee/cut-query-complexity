import CutQueryComplexity.StarContraction2022.Quantum.MinimumDegreeWitness
import CutQueryComplexity.StarContraction2022.Quantum.Forest.LowCertificate
import CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Program
import QuantumQueryComplexity.Quantum.Plurality

/-! # Public physical composition of the three minimum-cut producers

One verified singleton, one low-cut candidate and K fresh high-cut candidates
are compiled by the actual tensor-bank product-run construction. All choices
precede the answer table. The final readout selects the least verified value.
-/
set_option autoImplicit false
namespace CutQueryComplexity.StarContraction2022.Quantum.Global
noncomputable section
open QuantumQueryComplexity ProductPrograms
open scoped Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

abbrev AnswerTable (n : ℕ) := Finset (Fin n) → CutAnswer n 1
abbrev Batch (n K : ℕ) := Fin (K + 2) → Candidate n

def witnessCandidate {n : ℕ} : DegreeWitness n → Candidate n
  | none => none
  | some (v, a) => some ({v}, a)

def lowQueries (n : ℕ) (eta : ℝ) : ℕ :=
  12 * productBits n 1 *
    (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1)

def highQueries (n : ℕ) : ℕ := 12 * productBits n 1 * UniformStars.QH n

def singletonLaw (n t : ℕ) (ht : 0 < t) (read : AnswerTable n) (c : Candidate n) : ℝ :=
  ∑ w ∈ Finset.univ.filter (fun w => witnessCandidate w = c),
    (minimumDegreeWitnessAlg n t ht).prob read (minimumDegreeWitnessQueries n t) w

def lowLaw (n : ℕ) (eta : ℝ) (read : AnswerTable n) (c : Candidate n) : ℝ :=
  (productTreeAlg (Forest.lowCandidate n (rootThreshold n) eta)).prob read (lowQueries n eta) c

def highLaw (n : ℕ) (read : AnswerTable n) (c : Candidate n) : ℝ :=
  (productTreeAlg (UniformStars.highCandidate n)).prob read (highQueries n) c

def componentQueries (n t K : ℕ) (eta : ℝ) : Fin (K + 2) → ℕ :=
  Fin.cons (minimumDegreeWitnessQueries n t) (Fin.cons (lowQueries n eta) (fun _ => highQueries n))

def componentLaw (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    Fin (K + 2) → AnswerTable n → Candidate n → ℝ :=
  Fin.cons (singletonLaw n t ht) (Fin.cons (lowLaw n eta) (fun _ => highLaw n))

def jointQueries (n t K : ℕ) (eta : ℝ) : ℕ :=
  minimumDegreeWitnessQueries n t + lowQueries n eta + K * highQueries n

def jointLaw (n t K : ℕ) (ht : 0 < t) (eta : ℝ) (read : AnswerTable n) (y : Batch n K) : ℝ :=
  ∏ i, componentLaw n t K ht eta i read (y i)

theorem singleton_realizes (n t : ℕ) (ht : 0 < t) :
    Realizes (id : AnswerTable n → AnswerTable n) (minimumDegreeWitnessQueries n t)
      (singletonLaw n t ht) := by
  have h : Realizes (id : AnswerTable n → AnswerTable n) (minimumDegreeWitnessQueries n t)
      (fun read w => (minimumDegreeWitnessAlg n t ht).prob read (minimumDegreeWitnessQueries n t) w) :=
    ⟨minimumDegreeWitnessWork n t ht, inferInstance, inferInstance,
      minimumDegreeWitnessAlg n t ht, fun _ _ => rfl⟩
  exact h.map witnessCandidate

theorem low_realizes (n : ℕ) (eta : ℝ) :
    Realizes (id : AnswerTable n → AnswerTable n) (lowQueries n eta) (lowLaw n eta) :=
  ⟨productTreeWork (Forest.lowCandidate n (rootThreshold n) eta), inferInstance, inferInstance,
    productTreeAlg (Forest.lowCandidate n (rootThreshold n) eta), fun _ _ => rfl⟩

theorem high_realizes (n : ℕ) :
    Realizes (id : AnswerTable n → AnswerTable n) (highQueries n) (highLaw n) :=
  ⟨productTreeWork (UniformStars.highCandidate n), inferInstance, inferInstance,
    productTreeAlg (UniformStars.highCandidate n), fun _ _ => rfl⟩

theorem component_realizes (n t K : ℕ) (ht : 0 < t) (eta : ℝ) (i : Fin (K + 2)) :
    Realizes (id : AnswerTable n → AnswerTable n) (componentQueries n t K eta i)
      (componentLaw n t K ht eta i) := by
  refine Fin.cases (singleton_realizes n t ht) (fun j => ?_) i
  exact Fin.cases (low_realizes n eta) (fun _ => high_realizes n) j

/-- This is the exact summed native schedule, with every producer verification. -/
theorem sum_componentQueries (n t K : ℕ) (eta : ℝ) :
    ∑ i, componentQueries n t K eta i = jointQueries n t K eta := by
  simp [componentQueries, jointQueries, Fin.sum_univ_succ, Nat.add_assoc]

/-- The accepted product-run compiler constructs this Born law, for every table. -/
theorem joint_realizes (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    Realizes (id : AnswerTable n → AnswerTable n) (jointQueries n t K eta)
      (jointLaw n t K ht eta) := by
  have h := Realizes.foldRec (K + 2) (componentQueries n t K eta)
    (componentLaw n t K ht eta) (component_realizes n t K ht eta)
  rw [sum_componentQueries] at h
  exact h.congr (fun _ _ => rfl)

/-- A deterministic, public comparison of verified finite answer values. -/
def chooseCandidate {n : ℕ} : Candidate n → Candidate n → Candidate n
  | none, b => b
  | a, none => a
  | some (S, a), some (T, b) =>
      if decodeCutAnswer a ≤ decodeCutAnswer b then some (S, a) else some (T, b)

def bestList {n : ℕ} (xs : List (Candidate n)) : Candidate n :=
  xs.foldr chooseCandidate none

def selectCandidate {n K : ℕ} (y : Batch n K) : Candidate n := bestList (List.ofFn y)

/-- Tiny inputs have a pure absent-output convention and execute no oracle call. -/
def globalQueries (n t K : ℕ) (eta : ℝ) : ℕ :=
  if 2 ≤ n then jointQueries n t K eta else 0

def globalLaw (n t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (c : Candidate n) : ℝ :=
  if 2 ≤ n then
    ∑ y ∈ Finset.univ.filter (fun y => selectCandidate y = c), jointLaw n t K ht eta read y
  else if c = none then 1 else 0

theorem global_realizes (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    Realizes (id : AnswerTable n → AnswerTable n) (globalQueries n t K eta)
      (globalLaw n t K ht eta) := by
  by_cases hn : 2 ≤ n
  · rw [globalQueries, ite_eq_left hn]
    apply ((joint_realizes n t K ht eta).map selectCandidate).congr
    intro read c
    simp only [globalLaw, ite_eq_left hn]
  · refine ⟨Unit, inferInstance, inferInstance,
      constAlg (Finset (Fin n)) (CutAnswer n 1) (none : Candidate n), ?_⟩
    intro read c
    by_cases hc : c = none
    · subst c
      simp [globalQueries, globalLaw, hn, QAlg.prob, constAlg]
    · simp [globalLaw, hn, QAlg.prob, constAlg, qProb, hc, Ne.symm hc]

/-- Workspace and circuit are chosen before the hidden answer table or graph. -/
def globalWork (n t K : ℕ) (ht : 0 < t) (eta : ℝ) : Type :=
  (global_realizes n t K ht eta).choose
instance globalWorkFintype (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    Fintype (globalWork n t K ht eta) := (global_realizes n t K ht eta).choose_spec.choose
instance globalWorkDecidableEq (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    DecidableEq (globalWork n t K ht eta) :=
  (global_realizes n t K ht eta).choose_spec.choose_spec.choose

def globalAlg (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    CutQAlg n 1 (Candidate n) (globalWork n t K ht eta) :=
  (global_realizes n t K ht eta).choose_spec.choose_spec.choose_spec.choose

theorem globalAlg_law (n t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (c : Candidate n) :
    (globalAlg n t K ht eta).prob read (globalQueries n t K eta) c =
      globalLaw n t K ht eta read c :=
  (global_realizes n t K ht eta).choose_spec.choose_spec.choose_spec.choose_spec read c

def globalRoutine (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    QRoutine (Finset (Fin n)) (CutAnswer n 1) (globalWork n t K ht eta) where
  len := globalQueries n t K eta
  step := (globalAlg n t K ht eta).step
  step_unitary := (globalAlg n t K ht eta).step_unitary

@[simp] theorem globalRoutine_len (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    (globalRoutine n t K ht eta).len = globalQueries n t K eta := rfl

theorem globalRoutine_exact_schedule {n : ℕ} (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    (globalRoutine n t K ht eta).len =
      (4 * t * minimumDegreeBaseBudget n + 1) +
      12 * productBits n 1 *
        (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) +
      K * (12 * productBits n 1 * UniformStars.QH n) := by
  simp [globalQueries, hn, jointQueries, lowQueries, highQueries,
    minimumDegreeWitnessQueries_pos (by omega : 0 < n)]

theorem globalRoutine_state (n t K : ℕ) (ht : 0 < t) (eta : ℝ) (read : AnswerTable n) :
    (globalRoutine n t K ht eta).run read *ᵥ (globalAlg n t K ht eta).init =
      (globalAlg n t K ht eta).state read (globalQueries n t K eta) :=
  ((globalAlg n t K ht eta).state_eq_runUpto (globalRoutine n t K ht eta)
    rfl read (globalQueries n t K eta)).symm

theorem globalRoutine_normalized (n t K : ℕ) (ht : 0 < t) (eta : ℝ) (read : AnswerTable n) :
    IsQState ((globalRoutine n t K ht eta).run read *ᵥ (globalAlg n t K ht eta).init) := by
  rw [globalRoutine_state]
  exact (globalAlg n t K ht eta).state_isQState _ _

theorem globalRoutine_event_law (n t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (Good : Candidate n → Prop) [DecidablePred Good] :
    goodProb (globalAlg n t K ht eta).readout Good
      ((globalRoutine n t K ht eta).run read *ᵥ (globalAlg n t K ht eta).init) =
      ∑ c, if Good c then globalLaw n t K ht eta read c else 0 := by
  rw [globalRoutine_state, goodProb_eq_sum]
  change (∑ c, if Good c then (globalAlg n t K ht eta).prob read (globalQueries n t K eta) c else 0) = _
  simp_rw [globalAlg_law]

theorem global_small {n : ℕ} (hn : n < 2) (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) :
    (globalRoutine n t K ht eta).len = 0 ∧ (globalAlg n t K ht eta).prob read 0 none = 1 := by
  have hq : globalQueries n t K eta = 0 := by simp [globalQueries, Nat.not_le.mpr hn]
  refine ⟨hq, ?_⟩
  rw [← hq, globalAlg_law]
  simp [globalLaw, Nat.not_le.mpr hn]

#print axioms joint_realizes
#print axioms globalAlg_law
#print axioms globalRoutine_exact_schedule
#print axioms globalRoutine_normalized
#print axioms globalRoutine_event_law
#print axioms global_small
end
end CutQueryComplexity.StarContraction2022.Quantum.Global
