import CutQueryComplexity.Quantum.DirectedReconstruction.Oracle
import CutQueryComplexity.Quantum.LinearReconstruction.Graph
import CutQueryComplexity.Reconstruction.DirectedData

/-! Actual outgoing singleton/complement queries discover every imbalance.
The public schedule and workspace are finite; malformed answers are totalized. -/
set_option autoImplicit false
namespace CutQueryComplexity.Quantum.DirectedReconstruction
noncomputable section
open QuantumQueryComplexity
open DirectedCertificate
open scoped Matrix
attribute [local instance] basisDecidableEq
  LinearReconstruction.graphAnswerDecidableEq LinearReconstruction.graphWorkDecidableEq

local instance pairWorkEq {A J B W : Type} [DecidableEq A] [DecidableEq J]
    [DecidableEq B] [DecidableEq W] : DecidableEq (PairWork A J B W) :=
  inferInstanceAs (DecidableEq (Option A × (Option J × Option B × W)))

local instance pqWorkEq {n : ℕ} {W : Type} [DecidableEq W] :
    DecidableEq (PQWork (Finset (Fin n)) (CutAnswer n 1) W (n + n)) :=
  inferInstanceAs (DecidableEq
    (W × ((Option (Finset (Fin n)) × Option (CutAnswer n 1)) ×
      (Fin (n + n) → Option (CutAnswer n 1)))))

variable {n : ℕ}

/-- The first n queries are singletons, the next n their complements. -/
def imbalanceSelect {O : Type} (_o : O) (j : Fin (n + n)) : Option (Finset (Fin n)) :=
  some (match finSumFinEquiv.symm j with
    | Sum.inl v => {v}
    | Sum.inr v => {v}ᶜ)

/-- Public decoding from retained native answers; no hidden graph is used. -/
def imbalanceDecode (ans : Fin (n + n) → Option (CutAnswer n 1)) (v : Fin n) : ℝ :=
  ((ans (Fin.castAdd n v)).getD 0).val - ((ans (Fin.natAdd n v)).getD 0).val

theorem imbalanceDecode_honest {O : Type} (o : O) (G : DiGraph (Fin n)) (hG : G.Simple) :
    imbalanceDecode (fun j => (imbalanceSelect o j).map (unitRead G hG)) =
      (realGraph G).imbalance := by
  funext v
  simp only [imbalanceDecode, imbalanceSelect, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Option.map_some, Option.getD_some, unitRead_val]
  rw [← realGraph_out, ← realGraph_out, WeightedDiGraph.out_singleton,
    WeightedDiGraph.out_compl_singleton]
  rfl

variable {O P W : Type} [Fintype W] [DecidableEq W]

/-- Append the literal 2n physical outgoing-cut calls to a public quantum algorithm. -/
def withImbalance (T : CutQAlg n 1 O W) (q : ℕ)
    (decode : O → (Fin n → ℝ) → P) :
    CutQAlg n 1 P (PQWork (Finset (Fin n)) (CutAnswer n 1) W (n + n)) :=
  T.postQuery imbalanceSelect q (fun o ans => decode o (imbalanceDecode ans))

/-- The actual native routine for the complete schedule. -/
def withImbalanceRoutine (T : CutQAlg n 1 O W) (q : ℕ)
    (decode : O → (Fin n → ℝ) → P) :
    QRoutine (Finset (Fin n)) (CutAnswer n 1)
      (PQWork (Finset (Fin n)) (CutAnswer n 1) W (n + n)) :=
  ⟨q + (n + n), (withImbalance T q decode).step, (withImbalance T q decode).step_unitary⟩

@[simp] theorem withImbalanceRoutine_len (T : CutQAlg n 1 O W) (q : ℕ)
    (decode : O → (Fin n → ℝ) → P) :
    (withImbalanceRoutine T q decode).len = q + (n + n) := rfl

theorem withImbalanceRoutine_state [DecidableEq P] (T : CutQAlg n 1 O W) (q : ℕ)
    (decode : O → (Fin n → ℝ) → P) (read : Finset (Fin n) → CutAnswer n 1) :
    (withImbalanceRoutine T q decode).run read *ᵥ (withImbalance T q decode).init =
      (withImbalance T q decode).state read (q + (n + n)) :=
  (state_eq_runUpto2 (withImbalance T q decode) (q + (n + n)) read (q + (n + n))).symm

theorem withImbalance_normalized (T : CutQAlg n 1 O W) (q : ℕ)
    (decode : O → (Fin n → ℝ) → P) (read : Finset (Fin n) → CutAnswer n 1) (t : ℕ) :
    IsQState ((withImbalance T q decode).state read t) :=
  (withImbalance T q decode).state_isQState read t

/-- An exact Born-law formula for every native answer table. -/
theorem withImbalance_prob [DecidableEq O] [DecidableEq P] (T : CutQAlg n 1 O W) (q : ℕ)
    (decode : O → (Fin n → ℝ) → P) (read : Finset (Fin n) → CutAnswer n 1) (p : P) :
    (withImbalance T q decode).prob read (q + (n + n)) p =
      ∑ b, if decode (T.readout b)
        (imbalanceDecode (fun j => (imbalanceSelect (T.readout b) j).map read)) = p
        then Complex.normSq (T.state read q b) else 0 :=
  postQuery_prob T imbalanceSelect q (fun o ans => decode o (imbalanceDecode ans)) read p

/-- Honest singleton/complement queries provide exactly the original imbalance. -/
theorem withImbalance_prob_honest [DecidableEq O] [DecidableEq P] (T : CutQAlg n 1 O W) (q : ℕ)
    (decode : O → (Fin n → ℝ) → P) (G : DiGraph (Fin n)) (hG : G.Simple) (p : P) :
    (withImbalance T q decode).prob (unitRead G hG) (q + (n + n)) p =
      ∑ b, if decode (T.readout b) (realGraph G).imbalance = p
        then Complex.normSq (T.state (unitRead G hG) q b) else 0 := by
  rw [withImbalance_prob]
  simp_rw [imbalanceDecode_honest]

/-- A probability-one raw output remains certain after physically discovering imbalance. -/
theorem withImbalance_prob_one [DecidableEq O] [DecidableEq P]
    (T : CutQAlg n 1 O W) (q : ℕ) (decode : O → (Fin n → ℝ) → P)
    (G : DiGraph (Fin n)) (hG : G.Simple) (o : O)
    (ho : T.prob (unitRead G hG) q o = 1) :
    (withImbalance T q decode).prob (unitRead G hG) (q + (n + n))
      (decode o (realGraph G).imbalance) = 1 := by
  apply le_antisymm
  · change qProb _ _ _ ≤ 1
    rw [← goodProb_eq]
    exact goodProb_le_one _ _ ((withImbalance T q decode).state_isQState _ _)
  · rw [← ho, QAlg.prob, qProb, withImbalance_prob_honest]
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : T.readout b = o
    · simp [hb]
    · simp only [hb, ↓reduceIte]
      split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl


/-- A zero-query branch on the same finite workspace as a public program. -/
def haltAlg (T : CutQAlg n 1 O W) (o : O) : CutQAlg n 1 O W where
  init := T.init
  init_isQState := T.init_isQState
  step _ := 1
  step_unitary _ := one_mem_qUnitary
  readout _ := o

theorem haltAlg_prob [DecidableEq O] (T : CutQAlg n 1 O W) (o : O)
    (read : Finset (Fin n) → CutAnswer n 1) : (haltAlg T o).prob read 0 o = 1 := by
  change qProb (fun _ => o) ((1 : Matrix _ _ ℂ) *ᵥ T.init) o = 1
  simp only [Matrix.one_mulVec, qProb]
  exact T.init_isQState

/-- Any probability-one canonical answer implies probability-one relational correctness. -/
theorem goodProb_of_prob_one [DecidableEq O] (T : CutQAlg n 1 O W)
    (read : Finset (Fin n) → CutAnswer n 1) (q : ℕ) (o : O)
    (ho : T.prob read q o = 1) (Good : O → Prop) [DecidablePred Good] (hGood : Good o) :
    goodProb T.readout Good (T.state read q) = 1 := by
  apply le_antisymm (goodProb_le_one _ _ (T.state_isQState _ _))
  rw [← ho, QAlg.prob, qProb, goodProb_eq_sum_ite]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : T.readout b = o
  · simp [hb, hGood]
  · simp only [hb, ↓reduceIte]
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl

#print axioms haltAlg_prob
#print axioms goodProb_of_prob_one
#print axioms imbalanceDecode_honest
#print axioms withImbalanceRoutine_len
#print axioms withImbalanceRoutine_state
#print axioms withImbalance_normalized
#print axioms withImbalance_prob
#print axioms withImbalance_prob_one

section Reconstruct
open Reconstruction LinearReconstruction

/-- Finite scratch for symmetrized reconstruction followed by physical imbalance queries. -/
abbrev DirectedWork (n : ℕ) :=
  PQWork (Finset (Fin n)) (CutAnswer n 1)
    (PairWork (CutAnswer n 1) (Finset (Fin n)) (CutAnswer n 2) (GraphWork n 2)) (n + n)

instance directedWorkDecidableEq (n : ℕ) : DecidableEq (DirectedWork n) :=
  pqWorkEq

/-- Recovered public data, followed by arbitrary public offline processing. -/
def recoverDirected {O : Type} (n : ℕ) (decode : DirectedData (Fin n) → O) :
    CutQAlg n 1 O (DirectedWork n) :=
  withImbalance (symAlg (recoverGraphAlg n 2) (n * (6 * rowBits 2)))
    (4 * (n * (6 * rowBits 2)))
    (fun a β => decode ⟨(graphToCapacity (W := 2) a).toWeighted, β⟩)

/-- Literal native schedule, including the symmetrization compute/uncompute calls. -/
def recoverDirectedRoutine {O : Type} (n : ℕ) (decode : DirectedData (Fin n) → O) :
    QRoutine (Finset (Fin n)) (CutAnswer n 1) (DirectedWork n) :=
  ⟨50 * n, (recoverDirected n decode).step, (recoverDirected n decode).step_unitary⟩

@[simp] theorem recoverDirectedRoutine_len {O : Type} (n : ℕ)
    (decode : DirectedData (Fin n) → O) : (recoverDirectedRoutine n decode).len = 50 * n := rfl

theorem recoverDirectedRoutine_state {O : Type} [DecidableEq O] (n : ℕ)
    (decode : DirectedData (Fin n) → O) (read : Finset (Fin n) → CutAnswer n 1) :
    (recoverDirectedRoutine n decode).run read *ᵥ (recoverDirected n decode).init =
      (recoverDirected n decode).state read (50 * n) :=
  (state_eq_runUpto2 (recoverDirected n decode) (50 * n) read (50 * n)).symm

theorem recoverDirected_normalized {O : Type} (n : ℕ)
    (decode : DirectedData (Fin n) → O) (read : Finset (Fin n) → CutAnswer n 1) (t : ℕ) :
    IsQState ((recoverDirected n decode).state read t) :=
  (recoverDirected n decode).state_isQState read t

/-- The only hidden data in this statement describes the result, never the program. -/
theorem recoverDirected_prob {O : Type} [DecidableEq O] (n : ℕ)
    (decode : DirectedData (Fin n) → O) (G : DiGraph (Fin n)) (hG : G.Simple) :
    (recoverDirected n decode).prob (unitRead G hG) (50 * n)
      (decode ⟨(realGraph G).sym, (realGraph G).imbalance⟩) = 1 := by
  have hg : (symAlg (recoverGraphAlg n 2) (n * (6 * rowBits 2))).prob
      (unitRead G hG) (4 * (n * (6 * rowBits 2))) (graphRead (symCapacity G hG)) = 1 := by
    rw [symAlg_prob]
    exact recoverGraphAlg_prob (symCapacity G hG)
  have h := withImbalance_prob_one
    (symAlg (recoverGraphAlg n 2) (n * (6 * rowBits 2))) (4 * (n * (6 * rowBits 2)))
    (fun a β => decode ⟨(graphToCapacity (W := 2) a).toWeighted, β⟩) G hG
    (graphRead (symCapacity G hG)) hg
  have hq : 4 * (n * (6 * rowBits 2)) + (n + n) = 50 * n := by
    rw [rowBits_two]
    omega
  simpa only [recoverDirected, hq, graphToCapacity_read, symCapacity_real] using h


open scoped Classical in
/-- Probability-one recovery of the entire original outgoing-cut function. -/
theorem recoverDirected_out_prob (n : ℕ) (G : DiGraph (Fin n)) (hG : G.Simple) :
    (recoverDirected n DirectedData.cut).prob (unitRead G hG) (50 * n)
      (fun S => (G.out S : ℝ)) = 1 := by
  have h := recoverDirected_prob n DirectedData.cut G hG
  have he : DirectedData.cut ⟨(realGraph G).sym, (realGraph G).imbalance⟩ =
      fun S => (G.out S : ℝ) := by
    funext S
    rw [DirectedData.cut_correct _ (realGraph G) rfl rfl, realGraph_out]
  rwa [he] at h

#print axioms recoverDirected_out_prob
#print axioms recoverDirectedRoutine_len
#print axioms recoverDirectedRoutine_state
#print axioms recoverDirected_normalized
#print axioms recoverDirected_prob
end Reconstruct

end
end CutQueryComplexity.Quantum.DirectedReconstruction
