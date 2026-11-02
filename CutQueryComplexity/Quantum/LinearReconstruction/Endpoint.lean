import CutQueryComplexity.Quantum.LinearReconstruction.Graph
import CutQueryComplexity.AllPairs.Representation

/-! # Physical exact terminal and all-pairs cut endpoints
Public programs recover a bounded-capacity graph and perform finite offline
optimization. Outputs contain original vertex shores and original cut values.
Empty and singleton graphs bypass all queries. -/
set_option autoImplicit false
namespace CutQueryComplexity.Quantum.LinearReconstruction
noncomputable section
open QuantumQueryComplexity
open CutQueryComplexity.StarContraction2022.Quantum
open scoped Classical Matrix
open Matrix

attribute [local instance] graphAnswerDecidableEq graphWorkDecidableEq basisDecidableEq

/-- No unknown capacity exists when there is at most one vertex. -/
theorem graphRead_tiny {n W : ℕ} (hn : n ≤ 1) (G : CapacityGraph (Fin n) W) :
    graphRead G = graphZero n W := by
  funext v u
  have huv : u = v := Fin.ext (by have := u.isLt; have := v.isLt; omega)
  subst u
  apply Fin.ext
  simp [graphRead, rowRead, graphZero, rowZero, G.diag]

def endpointBudget (n W : ℕ) : ℕ := if n ≤ 1 then 0 else n * (6 * rowBits W)

def endpointRoutine (n W : ℕ) :
    QRoutine (Finset (Fin n)) (CutAnswer n W) (GraphWork n W) :=
  if n ≤ 1 then QRoutine.identity else recoverGraph n W

@[simp] theorem endpointRoutine_len (n W : ℕ) :
    (endpointRoutine n W).len = endpointBudget n W := by
  by_cases h : n ≤ 1 <;> simp [endpointRoutine, endpointBudget, h]

theorem endpointRoutine_run {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    (endpointRoutine n W).run (capacityRead G) *ᵥ
      qBasis (none, none, graphZero n W, rowZero n W) =
      qBasis (none, none, graphRead G, rowZero n W) := by
  by_cases hn : n ≤ 1
  · simp [endpointRoutine, hn, graphRead_tiny hn G]
  · simpa [endpointRoutine, hn] using recoverGraph_run G

/-- Public finite offline postprocessing of the recovered matrix. -/
def reconstructAlg {O : Type} (n W : ℕ) (f : CapacityGraph (Fin n) W → O) :
    CutQAlg n W O (GraphWork n W) :=
  (endpointRoutine n W).toAlg
    (qBasis (none, none, graphZero n W, rowZero n W)) (isQState_qBasis _)
    (fun p => f (graphToCapacity p.2.2.1))

theorem reconstructAlg_state {O : Type} {n W : ℕ}
    (f : CapacityGraph (Fin n) W → O) (G : CapacityGraph (Fin n) W) :
    (reconstructAlg n W f).state (capacityRead G) (endpointBudget n W) =
      qBasis (none, none, graphRead G, rowZero n W) := by
  unfold reconstructAlg
  rw [← endpointRoutine_len, QRoutine.toAlg_state_len, endpointRoutine_run]

theorem reconstructAlg_born {O : Type} [DecidableEq O] {n W : ℕ}
    (f : CapacityGraph (Fin n) W → O) (G : CapacityGraph (Fin n) W) (o : O) :
    (reconstructAlg n W f).prob (capacityRead G) (endpointBudget n W) o =
      if f G = o then 1 else 0 := by
  rw [QAlg.prob, reconstructAlg_state, qProb_qBasis]
  simp only [reconstructAlg, QRoutine.toAlg, graphToCapacity_read]

theorem reconstructAlg_good {O : Type} {n W : ℕ}
    (f : CapacityGraph (Fin n) W → O) (G : CapacityGraph (Fin n) W)
    (Good : O → Prop) [DecidablePred Good] (h : Good (f G)) :
    goodProb (reconstructAlg n W f).readout Good
      ((reconstructAlg n W f).state (capacityRead G) (endpointBudget n W)) = 1 := by
  rw [goodProb, reconstructAlg_state, qProb_qBasis]
  simp [reconstructAlg, QRoutine.toAlg, h]

/-- All physical states remain normalized for every finite answer table. -/
theorem reconstructAlg_normalized {O : Type} (n W : ℕ)
    (f : CapacityGraph (Fin n) W → O) (read : Finset (Fin n) → CutAnswer n W) (t : ℕ) :
    IsQState ((reconstructAlg n W f).state read t) :=
  (reconstructAlg n W f).state_isQState read t

/-- Original finite vertex shore together with its exact original cut value. -/
def terminalAnswer {n W : ℕ} (G : CapacityGraph (Fin n) W) (s t : Fin n) :
    AllPairs.STAnswer (Fin n) :=
  let S := AllPairs.offlineST G.toWeighted s t
  ⟨S, G.toWeighted.cut S⟩

def graphAnswers {n W : ℕ} (G : CapacityGraph (Fin n) W) : AllPairs.Answers (Fin n) :=
  terminalAnswer G

def terminalGood {n W : ℕ} (G : CapacityGraph (Fin n) W) (s t : Fin n)
    (out : AllPairs.STAnswer (Fin n)) : Prop :=
  (if s = t then out.shore = ∅ else IsSTMinCut G.toWeighted s t out.shore) ∧
    out.value = G.toWeighted.cut out.shore

theorem terminalAnswer_good {n W : ℕ} (G : CapacityGraph (Fin n) W) (s t : Fin n) :
    terminalGood G s t (terminalAnswer G s t) := by
  refine ⟨?_, rfl⟩
  by_cases h : s = t
  · simp [terminalAnswer, AllPairs.offlineST, h]
  · simp only [ite_eq_right h]
    exact AllPairs.offlineST_correct G.toWeighted h

theorem graphAnswers_good {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    AllPairs.allPairsGood G.toWeighted (graphAnswers G) := by
  intro s t hst
  exact ⟨AllPairs.offlineST_correct G.toWeighted hst, rfl⟩

/-- A physical terminal program chosen before the hidden graph. -/
def terminalAlg (n W : ℕ) (s t : Fin n) :
    CutQAlg n W (AllPairs.STAnswer (Fin n)) (GraphWork n W) :=
  reconstructAlg n W (fun G => terminalAnswer G s t)

/-- One physical program returns every original terminal shore and value. -/
def allPairsAlg (n W : ℕ) : CutQAlg n W (AllPairs.Answers (Fin n)) (GraphWork n W) :=
  reconstructAlg n W graphAnswers

theorem terminalAlg_born {n W : ℕ} (s t : Fin n) (G : CapacityGraph (Fin n) W)
    (o : AllPairs.STAnswer (Fin n)) :
    (terminalAlg n W s t).prob (capacityRead G) (endpointBudget n W) o =
      if terminalAnswer G s t = o then 1 else 0 :=
  reconstructAlg_born _ G o

theorem allPairsAlg_born {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (o : AllPairs.Answers (Fin n)) :
    (allPairsAlg n W).prob (capacityRead G) (endpointBudget n W) o =
      if graphAnswers G = o then 1 else 0 :=
  reconstructAlg_born _ G o

theorem terminalAlg_success {n W : ℕ} (s t : Fin n) (G : CapacityGraph (Fin n) W) :
    successProbOn (terminalAlg n W s t) (endpointBudget n W) capacityRead
      (fun G o => terminalGood G s t o) G = 1 :=
  reconstructAlg_good _ G _ (terminalAnswer_good G s t)

theorem allPairsAlg_success {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    successProbOn (allPairsAlg n W) (endpointBudget n W) capacityRead
      (fun G o => AllPairs.allPairsGood G.toWeighted o) G = 1 :=
  reconstructAlg_good _ G _ (graphAnswers_good G)

/-- Simultaneous correctness also records the diagonal convention. -/
theorem allPairsAlg_success_with_diagonal {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    successProbOn (allPairsAlg n W) (endpointBudget n W) capacityRead
      (fun G o => ∀ s t, terminalGood G s t (o s t)) G = 1 :=
  reconstructAlg_good _ G _ (fun s t => terminalAnswer_good G s t)

theorem endpointBudget_le (n W : ℕ) : endpointBudget n W ≤ n * (6 * Nat.clog 2 (W + 1)) := by
  simp only [endpointBudget, rowBits]
  split_ifs <;> omega

theorem endpointBudget_unit (n : ℕ) : endpointBudget n 1 ≤ 6 * n := by
  have h := endpointBudget_le n 1
  change endpointBudget n 1 ≤ n * (6 * rowBits 1) at h
  simpa [Nat.mul_comm] using h

theorem endpointBudget_two (n : ℕ) : endpointBudget n 2 ≤ 12 * n := by
  have h := endpointBudget_le n 2
  change endpointBudget n 2 ≤ n * (6 * rowBits 2) at h
  simpa [Nat.mul_comm] using h

@[simp] theorem endpointBudget_tiny {n W : ℕ} (h : n ≤ 1) : endpointBudget n W = 0 := by
  simp [endpointBudget, h]

@[simp] theorem terminalAnswer_diagonal {n W : ℕ} (G : CapacityGraph (Fin n) W) (s : Fin n) :
    terminalAnswer G s s = ⟨∅, 0⟩ := by
  simp [terminalAnswer, AllPairs.offlineST]

/-- Quantifiers explicitly choose the actual public unit terminal algorithm before G. -/
theorem exists_unit_terminal (n : ℕ) (s t : Fin n) :
    ∃ T : CutQAlg n 1 (AllPairs.STAnswer (Fin n)) (GraphWork n 1),
      T = terminalAlg n 1 s t ∧ endpointBudget n 1 ≤ 6 * n ∧
      ∀ G : CapacityGraph (Fin n) 1,
        successProbOn T (endpointBudget n 1) capacityRead
          (fun G o => terminalGood G s t o) G = 1 :=
  ⟨terminalAlg n 1 s t, rfl, endpointBudget_unit n, terminalAlg_success s t⟩

/-- The same linear schedule yields simultaneous original all-pairs shores and values. -/
theorem exists_unit_allPairs (n : ℕ) :
    ∃ T : CutQAlg n 1 (AllPairs.Answers (Fin n)) (GraphWork n 1),
      T = allPairsAlg n 1 ∧ endpointBudget n 1 ≤ 6 * n ∧
      ∀ G : CapacityGraph (Fin n) 1,
        successProbOn T (endpointBudget n 1) capacityRead
          (fun G o => AllPairs.allPairsGood G.toWeighted o) G = 1 :=
  ⟨allPairsAlg n 1, rfl, endpointBudget_unit n, allPairsAlg_success⟩

/-- Literal zero-query behavior for the empty all-pairs problem. -/
theorem allPairsAlg_empty (W : ℕ) (G : CapacityGraph (Fin 0) W) :
    (allPairsAlg 0 W).prob (capacityRead G) 0 (graphAnswers G) = 1 := by
  have h := allPairsAlg_born G (graphAnswers G)
  simpa [endpointBudget] using h

/-- The single-vertex terminal convention returns the empty shore and value zero. -/
theorem terminalAlg_singleton (W : ℕ) (s t : Fin 1) (G : CapacityGraph (Fin 1) W) :
    (terminalAlg 1 W s t).prob (capacityRead G) 0 ⟨∅, 0⟩ = 1 := by
  have hst : t = s := Subsingleton.elim _ _
  subst t
  have h := terminalAlg_born s s G ⟨∅, 0⟩
  simpa [endpointBudget] using h

@[simp] theorem endpointBudget_zeroCapacity (n : ℕ) : endpointBudget n 0 = 0 := by
  simp [endpointBudget]

/-- The physical public terminal endpoint also applies directly to the simple-graph oracle. -/
theorem terminalAlg_simple_success {n : ℕ} (s t : Fin n) (G : SimpleGraph (Fin n)) :
    successProbOn (terminalAlg n 1 s t) (endpointBudget n 1) simpleRead
      (fun G o => terminalGood (SimpleGraph.toCapacity G) s t o) G = 1 := by
  exact terminalAlg_success s t (SimpleGraph.toCapacity G)

theorem allPairsAlg_simple_success {n : ℕ} (G : SimpleGraph (Fin n)) :
    successProbOn (allPairsAlg n 1) (endpointBudget n 1) simpleRead
      (fun G o => AllPairs.allPairsGood (SimpleGraph.toWeighted G) o) G = 1 := by
  exact allPairsAlg_success (SimpleGraph.toCapacity G)

/-- An original global minimum shore with its exact value; the empty shore when no
proper shore exists. -/
def globalAnswer {n W : ℕ} (G : CapacityGraph (Fin n) W) : AllPairs.STAnswer (Fin n) :=
  if h : ∃ S, IsMinCut G.toWeighted S then
    ⟨Classical.choose h, G.toWeighted.cut (Classical.choose h)⟩
  else ⟨∅, 0⟩

def globalGood {n W : ℕ} (G : CapacityGraph (Fin n) W) (out : AllPairs.STAnswer (Fin n)) :
    Prop :=
  IsMinCut G.toWeighted out.shore ∧ out.value = G.toWeighted.cut out.shore

theorem globalAnswer_good {n W : ℕ} (hn : 2 ≤ n) (G : CapacityGraph (Fin n) W) :
    globalGood G (globalAnswer G) := by
  have h := exists_isMinCut_of_two_le_card G.toWeighted (by simpa using hn)
  rw [globalAnswer, dite_eq_left h]
  exact ⟨Classical.choose_spec h, rfl⟩

/-- A physical global program on the same linear schedule. -/
def globalReconstructAlg (n W : ℕ) :
    CutQAlg n W (AllPairs.STAnswer (Fin n)) (GraphWork n W) :=
  reconstructAlg n W globalAnswer

theorem globalReconstructAlg_success {n W : ℕ} (hn : 2 ≤ n) (G : CapacityGraph (Fin n) W) :
    successProbOn (globalReconstructAlg n W) (endpointBudget n W) capacityRead
      (fun G o => globalGood G o) G = 1 :=
  reconstructAlg_good _ G _ (globalAnswer_good hn G)

/-- Capacities in `{0,…,W}`: the public terminal program uses at most
`6n⌈log₂(W+1)⌉` native calls and is exact with probability one. -/
theorem exists_capacity_terminal (n W : ℕ) (s t : Fin n) :
    ∃ T : CutQAlg n W (AllPairs.STAnswer (Fin n)) (GraphWork n W),
      T = terminalAlg n W s t ∧ endpointBudget n W ≤ n * (6 * Nat.clog 2 (W + 1)) ∧
      ∀ G : CapacityGraph (Fin n) W,
        successProbOn T (endpointBudget n W) capacityRead
          (fun G o => terminalGood G s t o) G = 1 :=
  ⟨terminalAlg n W s t, rfl, endpointBudget_le n W, terminalAlg_success s t⟩

/-- Capacities in `{0,…,W}`: one public program returns all original terminal shores
and values. -/
theorem exists_capacity_allPairs (n W : ℕ) :
    ∃ T : CutQAlg n W (AllPairs.Answers (Fin n)) (GraphWork n W),
      T = allPairsAlg n W ∧ endpointBudget n W ≤ n * (6 * Nat.clog 2 (W + 1)) ∧
      ∀ G : CapacityGraph (Fin n) W,
        successProbOn T (endpointBudget n W) capacityRead
          (fun G o => AllPairs.allPairsGood G.toWeighted o) G = 1 :=
  ⟨allPairsAlg n W, rfl, endpointBudget_le n W, allPairsAlg_success⟩

/-- Capacities in `{0,…,W}`: the public global program returns an original minimum
shore and its value. -/
theorem exists_capacity_global (n W : ℕ) (hn : 2 ≤ n) :
    ∃ T : CutQAlg n W (AllPairs.STAnswer (Fin n)) (GraphWork n W),
      T = globalReconstructAlg n W ∧ endpointBudget n W ≤ n * (6 * Nat.clog 2 (W + 1)) ∧
      ∀ G : CapacityGraph (Fin n) W,
        successProbOn T (endpointBudget n W) capacityRead
          (fun G o => globalGood G o) G = 1 :=
  ⟨globalReconstructAlg n W, rfl, endpointBudget_le n W, globalReconstructAlg_success hn⟩

#print axioms globalAnswer_good
#print axioms globalReconstructAlg_success
#print axioms exists_capacity_terminal
#print axioms exists_capacity_allPairs
#print axioms exists_capacity_global
#print axioms graphRead_tiny
#print axioms endpointBudget
#print axioms endpointRoutine
#print axioms endpointRoutine_len
#print axioms endpointRoutine_run
#print axioms reconstructAlg
#print axioms reconstructAlg_state
#print axioms reconstructAlg_born
#print axioms reconstructAlg_good
#print axioms reconstructAlg_normalized
#print axioms terminalAnswer
#print axioms graphAnswers
#print axioms terminalGood
#print axioms terminalAnswer_good
#print axioms graphAnswers_good
#print axioms terminalAlg
#print axioms allPairsAlg
#print axioms terminalAlg_born
#print axioms allPairsAlg_born
#print axioms terminalAlg_success
#print axioms allPairsAlg_success
#print axioms allPairsAlg_success_with_diagonal
#print axioms endpointBudget_le
#print axioms endpointBudget_unit
#print axioms endpointBudget_two
#print axioms endpointBudget_tiny
#print axioms terminalAnswer_diagonal
#print axioms exists_unit_terminal
#print axioms exists_unit_allPairs
#print axioms allPairsAlg_empty
#print axioms terminalAlg_singleton
#print axioms endpointBudget_zeroCapacity
#print axioms terminalAlg_simple_success
#print axioms allPairsAlg_simple_success
end
end CutQueryComplexity.Quantum.LinearReconstruction
