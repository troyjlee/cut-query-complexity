import CutQueryComplexity.Quantum.DirectedReconstruction.Program

/-! Physical directed-unit global, terminal and all-pairs minimum-cut endpoints.
The outgoing-cut function, not the unidentifiable orientations, is recovered.
All final optimization uses public recovered data, with no further query. -/
set_option autoImplicit false
namespace CutQueryComplexity.Quantum.DirectedReconstruction
noncomputable section
open QuantumQueryComplexity Reconstruction DirectedCertificate
open scoped Matrix Classical
attribute [local instance] basisDecidableEq directedWorkDecidableEq

variable {n : ℕ}

/-- Empty shore and zero value for a problem with no admissible shore. -/
def zeroAnswer (n : ℕ) : AllPairs.STAnswer (Fin n) := ⟨∅, 0⟩
def zeroAnswers (n : ℕ) : AllPairs.Answers (Fin n) := fun _ _ => zeroAnswer n

/-- Proof-only description of the exact recovered cut function. -/
def honestData (G : DiGraph (Fin n)) : DirectedData (Fin n) :=
  ⟨(realGraph G).sym, (realGraph G).imbalance⟩

def terminalQueries (s t : Fin n) : ℕ := if s = t then 0 else 50 * n
def globalQueries (n : ℕ) : ℕ := if n ≤ 1 then 0 else 50 * n
def allPairsQueries (n : ℕ) : ℕ := globalQueries n

/-- Public original-terminal solver. Equal terminals use the zero-query convention. -/
def terminalAlg (s t : Fin n) : CutQAlg n 1 (AllPairs.STAnswer (Fin n)) (DirectedWork n) :=
  let T := recoverDirected n (fun D => D.terminalAnswer s t)
  if s = t then haltAlg T (zeroAnswer n) else T

/-- Public original-global solver, bypassing every query for at most one vertex. -/
def globalAlg (n : ℕ) : CutQAlg n 1 (AllPairs.STAnswer (Fin n)) (DirectedWork n) :=
  let T := recoverDirected n DirectedData.globalAnswer
  if n ≤ 1 then haltAlg T (zeroAnswer n) else T

/-- One recovered cut function serves all ordered terminal pairs simultaneously. -/
def allPairsAlg (n : ℕ) : CutQAlg n 1 (AllPairs.Answers (Fin n)) (DirectedWork n) :=
  let T := recoverDirected n DirectedData.allPairsAnswers
  if n ≤ 1 then haltAlg T (zeroAnswers n) else T

def terminalRoutine (s t : Fin n) : QRoutine (Finset (Fin n)) (CutAnswer n 1) (DirectedWork n) :=
  ⟨terminalQueries s t, (terminalAlg s t).step, (terminalAlg s t).step_unitary⟩
def globalRoutine (n : ℕ) : QRoutine (Finset (Fin n)) (CutAnswer n 1) (DirectedWork n) :=
  ⟨globalQueries n, (globalAlg n).step, (globalAlg n).step_unitary⟩
def allPairsRoutine (n : ℕ) : QRoutine (Finset (Fin n)) (CutAnswer n 1) (DirectedWork n) :=
  ⟨allPairsQueries n, (allPairsAlg n).step, (allPairsAlg n).step_unitary⟩

@[simp] theorem terminalRoutine_len (s t : Fin n) :
    (terminalRoutine s t).len = if s = t then 0 else 50 * n := rfl
@[simp] theorem globalRoutine_len (n : ℕ) :
    (globalRoutine n).len = if n ≤ 1 then 0 else 50 * n := rfl
@[simp] theorem allPairsRoutine_len (n : ℕ) :
    (allPairsRoutine n).len = if n ≤ 1 then 0 else 50 * n := rfl

theorem terminalQueries_le (s t : Fin n) : terminalQueries s t ≤ 50 * n := by
  unfold terminalQueries; split_ifs <;> omega
theorem globalQueries_le (n : ℕ) : globalQueries n ≤ 50 * n := by
  unfold globalQueries; split_ifs <;> omega
theorem allPairsQueries_le (n : ℕ) : allPairsQueries n ≤ 50 * n := globalQueries_le n

theorem terminalRoutine_state (s t : Fin n) (read : Finset (Fin n) → CutAnswer n 1) :
    (terminalRoutine s t).run read *ᵥ (terminalAlg s t).init =
      (terminalAlg s t).state read (terminalQueries s t) :=
  (state_eq_runUpto2 (terminalAlg s t) (terminalQueries s t) read (terminalQueries s t)).symm

theorem globalRoutine_state (n : ℕ) (read : Finset (Fin n) → CutAnswer n 1) :
    (globalRoutine n).run read *ᵥ (globalAlg n).init =
      (globalAlg n).state read (globalQueries n) :=
  (state_eq_runUpto2 (globalAlg n) (globalQueries n) read (globalQueries n)).symm

theorem allPairsRoutine_state (n : ℕ) (read : Finset (Fin n) → CutAnswer n 1) :
    (allPairsRoutine n).run read *ᵥ (allPairsAlg n).init =
      (allPairsAlg n).state read (allPairsQueries n) :=
  (state_eq_runUpto2 (allPairsAlg n) (allPairsQueries n) read (allPairsQueries n)).symm

/-- All three algorithms normalize every answer table at every time. -/
theorem endpoints_normalized (n : ℕ) (read : Finset (Fin n) → CutAnswer n 1) (k : ℕ) :
    IsQState ((globalAlg n).state read k) ∧
    IsQState ((allPairsAlg n).state read k) ∧
    ∀ s t, IsQState ((terminalAlg s t).state read k) :=
  ⟨(globalAlg n).state_isQState read k, (allPairsAlg n).state_isQState read k,
    fun s t => (terminalAlg s t).state_isQState read k⟩

theorem terminalAlg_prob (s t : Fin n) (G : DiGraph (Fin n)) (hG : G.Simple) :
    (terminalAlg s t).prob (unitRead G hG) (terminalQueries s t)
      ((honestData G).terminalAnswer s t) = 1 := by
  by_cases hst : s = t
  · subst t
    simp only [terminalAlg, terminalQueries, ite_true, DirectedData.terminalAnswer_self]
    exact haltAlg_prob _ _ _
  · simp only [terminalAlg, terminalQueries, hst, ite_false]
    exact recoverDirected_prob n _ G hG

theorem globalAlg_prob (n : ℕ) (G : DiGraph (Fin n)) (hG : G.Simple) :
    (globalAlg n).prob (unitRead G hG) (globalQueries n)
      (honestData G).globalAnswer = 1 := by
  by_cases hn : n ≤ 1
  · simp only [globalAlg, globalQueries, hn, ite_true]
    rw [DirectedData.globalAnswer_tiny _ (by simpa using (by omega : n < 2))]
    exact haltAlg_prob _ _ _
  · simp only [globalAlg, globalQueries, hn, ite_false]
    exact recoverDirected_prob n _ G hG

theorem allPairsAlg_prob (n : ℕ) (G : DiGraph (Fin n)) (hG : G.Simple) :
    (allPairsAlg n).prob (unitRead G hG) (allPairsQueries n)
      (honestData G).allPairsAnswers = 1 := by
  by_cases hn : n ≤ 1
  · have ht : (honestData G).allPairsAnswers = zeroAnswers n := by
      funext s t
      have hst : t = s := Fin.ext (by have ht := t.isLt; have hs := s.isLt; omega)
      subst t
      exact DirectedData.terminalAnswer_self _ _
    simp only [allPairsAlg, allPairsQueries, globalQueries, hn, ite_true, ht]
    exact haltAlg_prob _ _ _
  · simp only [allPairsAlg, allPairsQueries, globalQueries, hn, ite_false]
    exact recoverDirected_prob n _ G hG

/-- Original directed shore/value correctness, including the equal-terminal convention. -/
def TerminalGood (G : DiGraph (Fin n)) (s t : Fin n) (o : AllPairs.STAnswer (Fin n)) : Prop :=
  if s = t then o = zeroAnswer n else
    s ∈ o.shore ∧ t ∉ o.shore ∧ o.value = (G.out o.shore : ℝ) ∧
      ∀ S, s ∈ S → t ∉ S → (G.out o.shore : ℝ) ≤ G.out S

/-- Simultaneous correctness for every ordered pair, including diagonal entries. -/
def AllPairsGood (G : DiGraph (Fin n)) (a : AllPairs.Answers (Fin n)) : Prop :=
  ∀ s t, TerminalGood G s t (a s t)

/-- Proper original global minimum, or the total tiny-input convention. -/
def GlobalGood (G : DiGraph (Fin n)) (o : AllPairs.STAnswer (Fin n)) : Prop :=
  if n ≤ 1 then o = zeroAnswer n else
    IsGlobalMinCut (realGraph G) o.shore ∧ o.value = (G.out o.shore : ℝ) ∧
      o.value = (realGraph G).minValue

theorem honestData_terminal_good (G : DiGraph (Fin n)) (s t : Fin n) :
    TerminalGood G s t ((honestData G).terminalAnswer s t) := by
  by_cases hst : s = t
  · subst t
    simp [TerminalGood, zeroAnswer]
  · simp only [TerminalGood, hst, ite_false]
    simpa only [realGraph_out] using
      DirectedData.terminalAnswer_correct (honestData G) (realGraph G) rfl rfl hst

theorem honestData_allPairs_good (G : DiGraph (Fin n)) :
    AllPairsGood G (honestData G).allPairsAnswers :=
  fun s t => honestData_terminal_good G s t

theorem honestData_global_good (G : DiGraph (Fin n)) :
    GlobalGood G (honestData G).globalAnswer := by
  by_cases hn : n ≤ 1
  · simp only [GlobalGood, hn, ite_true]
    exact DirectedData.globalAnswer_tiny _ (by simpa using (by omega : n < 2))
  · simp only [GlobalGood, hn, ite_false]
    simpa only [realGraph_out] using DirectedData.globalAnswer_correct
      (honestData G) (realGraph G) rfl rfl (by simpa using (by omega : 2 ≤ n))

/-- Probability-one original directed terminal minimum-cut correctness. -/
theorem terminal_correct (s t : Fin n) (G : DiGraph (Fin n)) (hG : G.Simple) :
    goodProb (terminalAlg s t).readout (TerminalGood G s t)
      ((terminalAlg s t).state (unitRead G hG) (terminalQueries s t)) = 1 :=
  goodProb_of_prob_one _ _ _ _ (terminalAlg_prob s t G hG) _ (honestData_terminal_good G s t)

/-- Probability-one simultaneous original directed all-pairs correctness. -/
theorem allPairs_correct (n : ℕ) (G : DiGraph (Fin n)) (hG : G.Simple) :
    goodProb (allPairsAlg n).readout (AllPairsGood G)
      ((allPairsAlg n).state (unitRead G hG) (allPairsQueries n)) = 1 :=
  goodProb_of_prob_one _ _ _ _ (allPairsAlg_prob n G hG) _ (honestData_allPairs_good G)

/-- Probability-one original directed global shore and minimum value correctness. -/
theorem global_correct (n : ℕ) (G : DiGraph (Fin n)) (hG : G.Simple) :
    goodProb (globalAlg n).readout (GlobalGood G)
      ((globalAlg n).state (unitRead G hG) (globalQueries n)) = 1 :=
  goodProb_of_prob_one _ _ _ _ (globalAlg_prob n G hG) _ (honestData_global_good G)

/-- A concrete public global physical program is selected before every hidden input. -/
theorem physical_global_endpoint (n : ℕ) :
    ∃ (T : CutQAlg n 1 (AllPairs.STAnswer (Fin n)) (DirectedWork n))
      (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) (DirectedWork n)),
      R.len = (if n ≤ 1 then 0 else 50 * n) ∧ R.len ≤ 50 * n ∧
      (∀ read, R.run read *ᵥ T.init = T.state read R.len) ∧
      (∀ read k, IsQState (T.state read k)) ∧
      ∀ (G : DiGraph (Fin n)) (hG : G.Simple),
        goodProb T.readout (GlobalGood G) (T.state (unitRead G hG) R.len) = 1 :=
  ⟨globalAlg n, globalRoutine n, rfl, globalQueries_le n, globalRoutine_state n,
    (fun read k => (globalAlg n).state_isQState read k), global_correct n⟩

/-- A concrete public terminal program is selected before every hidden input. -/
theorem physical_terminal_endpoint (s t : Fin n) :
    ∃ (T : CutQAlg n 1 (AllPairs.STAnswer (Fin n)) (DirectedWork n))
      (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) (DirectedWork n)),
      R.len = (if s = t then 0 else 50 * n) ∧ R.len ≤ 50 * n ∧
      (∀ read, R.run read *ᵥ T.init = T.state read R.len) ∧
      (∀ read k, IsQState (T.state read k)) ∧
      ∀ (G : DiGraph (Fin n)) (hG : G.Simple),
        goodProb T.readout (TerminalGood G s t) (T.state (unitRead G hG) R.len) = 1 :=
  ⟨terminalAlg s t, terminalRoutine s t, rfl, terminalQueries_le s t, terminalRoutine_state s t,
    (fun read k => (terminalAlg s t).state_isQState read k), terminal_correct s t⟩

/-- One public physical program solves all original ordered pairs simultaneously. -/
theorem physical_allPairs_endpoint (n : ℕ) :
    ∃ (T : CutQAlg n 1 (AllPairs.Answers (Fin n)) (DirectedWork n))
      (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) (DirectedWork n)),
      R.len = (if n ≤ 1 then 0 else 50 * n) ∧ R.len ≤ 50 * n ∧
      (∀ read, R.run read *ᵥ T.init = T.state read R.len) ∧
      (∀ read k, IsQState (T.state read k)) ∧
      ∀ (G : DiGraph (Fin n)) (hG : G.Simple),
        goodProb T.readout (AllPairsGood G) (T.state (unitRead G hG) R.len) = 1 :=
  ⟨allPairsAlg n, allPairsRoutine n, rfl, allPairsQueries_le n, allPairsRoutine_state n,
    (fun read k => (allPairsAlg n).state_isQState read k), allPairs_correct n⟩

#print axioms physical_global_endpoint
#print axioms physical_terminal_endpoint
#print axioms physical_allPairs_endpoint

#print axioms terminalRoutine_len
#print axioms globalRoutine_len
#print axioms allPairsRoutine_len
#print axioms terminalRoutine_state
#print axioms globalRoutine_state
#print axioms allPairsRoutine_state
#print axioms endpoints_normalized
#print axioms terminal_correct
#print axioms allPairs_correct
#print axioms global_correct
end
end CutQueryComplexity.Quantum.DirectedReconstruction
