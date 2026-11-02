import CutQueryComplexity.Quantum.DirectedReconstruction.Endpoint

/-! Physical directed global, terminal and all-pairs endpoints for natural arc
capacities in `{0,…,W}`. The unit construction is repeated with the public bound
`W`: four native calls simulate one symmetrized call with capacities at most `2W`,
and `2n` singleton/complement calls give the imbalances. The outgoing-cut function,
not the arc orientations, is recovered. -/
set_option autoImplicit false
namespace CutQueryComplexity.Quantum.DirectedReconstruction
noncomputable section
open QuantumQueryComplexity Reconstruction DirectedCertificate LinearReconstruction
open scoped Matrix Classical
attribute [local instance] basisDecidableEq
  LinearReconstruction.graphAnswerDecidableEq LinearReconstruction.graphWorkDecidableEq

local instance pairWorkEqW {A J B W : Type} [DecidableEq A] [DecidableEq J]
    [DecidableEq B] [DecidableEq W] : DecidableEq (PairWork A J B W) :=
  inferInstanceAs (DecidableEq (Option A × (Option J × Option B × W)))

local instance pqWorkEqW {n W : ℕ} {Work : Type} [DecidableEq Work] :
    DecidableEq (PQWork (Finset (Fin n)) (CutAnswer n W) Work (n + n)) :=
  inferInstanceAs (DecidableEq
    (Work × ((Option (Finset (Fin n)) × Option (CutAnswer n W)) ×
      (Fin (n + n) → Option (CutAnswer n W)))))

variable {n : ℕ}

section BoundedOracle
open Finset

/-- Arc capacities at most `W` give a public finite whole-answer alphabet. -/
theorem bounded_out_le (W : ℕ) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W)
    (S : Finset (Fin n)) : G.out S ≤ W * n * n := by
  calc
    G.out S ≤ ∑ _u ∈ S, ∑ _v ∈ Sᶜ, W :=
      sum_le_sum fun u _ => sum_le_sum fun v _ => hG u v
    _ = S.card * (Sᶜ.card * W) := by simp
    _ ≤ n * (n * W) := Nat.mul_le_mul (by simpa using card_le_univ S)
      (Nat.mul_le_mul_right _ (by simpa using card_le_univ Sᶜ))
    _ = W * n * n := by ring

def boundedRead (W : ℕ) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W)
    (S : Finset (Fin n)) : CutAnswer n W :=
  ⟨G.out S, Nat.lt_succ_of_le (bounded_out_le W G hG S)⟩

@[simp] theorem boundedRead_val (W : ℕ) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W)
    (S : Finset (Fin n)) : (boundedRead W G hG S : ℕ) = G.out S := rfl

/-- Antiparallel arcs give undirected capacities in `{0,…,2W}`. -/
def symCapacityW (W : ℕ) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W) :
    CapacityGraph (Fin n) (2 * W) where
  w u v := ⟨G.sym u v, by
    have h₁ := hG u v; have h₂ := hG v u; simp only [DiGraph.sym]; omega⟩
  symm u v := Fin.ext (G.sym_comm u v)
  diag v := Fin.ext (G.sym_self v)

theorem symCapacityW_real (W : ℕ) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W) :
    (symCapacityW W G hG).toWeighted = (realGraph G).sym := by
  ext u v
  simp [CapacityGraph.toWeighted, symCapacityW, WeightedDiGraph.sym, realGraph, DiGraph.sym]

theorem symCapacityW_cut (W : ℕ) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W)
    (S : Finset (Fin n)) : (symCapacityW W G hG).cut S = G.out S + G.out Sᶜ := by
  change G.symCut S = _
  simp only [DiGraph.symCut, DiGraph.pairs_eq, DiGraph.out, compl_compl]

/-- Total recoding, including arbitrary inconsistent native answer tables. -/
def symTagW (W : ℕ) (_S : Finset (Fin n)) (a b : CutAnswer n W) : CutAnswer n (2 * W) :=
  ⟨a.val + b.val, by
    have ha := a.isLt; have hb := b.isLt
    have h : 2 * W * n * n = W * n * n + W * n * n := by ring
    rw [h]; omega⟩

def symReadW (W : ℕ) (read : Finset (Fin n) → CutAnswer n W) (S : Finset (Fin n)) :
    CutAnswer n (2 * W) :=
  symTagW W S (read S) (read Sᶜ)

theorem symReadW_honest (W : ℕ) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W) :
    symReadW W (boundedRead W G hG) = capacityRead (symCapacityW W G hG) := by
  funext S
  apply Fin.ext
  exact (symCapacityW_cut W G hG S).symm

variable {Work O : Type} [Fintype Work] [DecidableEq Work]

def symAlgW (W : ℕ) (T : CutQAlg n (2 * W) O Work) (q : ℕ) :=
  pairAlg id (fun S => Sᶜ) (symTagW W) T q

theorem symAlgW_prob [DecidableEq O] (W : ℕ) (T : CutQAlg n (2 * W) O Work) (q : ℕ)
    (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W) (o : O) :
    (symAlgW W T q).prob (boundedRead W G hG) (4 * q) o =
      T.prob (capacityRead (symCapacityW W G hG)) q o := by
  change (pairAlg _ _ _ T q).prob _ _ _ = _
  rw [pairAlg_prob]
  change T.prob (symReadW W (boundedRead W G hG)) q o = _
  rw [symReadW_honest]

end BoundedOracle

section BoundedImbalance

variable {O P Work : Type} [Fintype Work] [DecidableEq Work]

/-- Public decoding from retained native answers; no hidden graph is used. -/
def imbalanceDecodeW {W : ℕ} (ans : Fin (n + n) → Option (CutAnswer n W)) (v : Fin n) : ℝ :=
  ((ans (Fin.castAdd n v)).getD 0).val - ((ans (Fin.natAdd n v)).getD 0).val

theorem imbalanceDecodeW_honest (W : ℕ) (o : O) (G : DiGraph (Fin n))
    (hG : ∀ u v, G.c u v ≤ W) :
    imbalanceDecodeW (fun j => (imbalanceSelect o j).map (boundedRead W G hG)) =
      (realGraph G).imbalance := by
  funext v
  simp only [imbalanceDecodeW, imbalanceSelect, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Option.map_some, Option.getD_some, boundedRead_val]
  rw [← realGraph_out, ← realGraph_out, WeightedDiGraph.out_singleton,
    WeightedDiGraph.out_compl_singleton]
  rfl

/-- Append the literal 2n physical outgoing-cut calls to a public quantum algorithm. -/
def withImbalanceW {W : ℕ} (T : CutQAlg n W O Work) (q : ℕ)
    (decode : O → (Fin n → ℝ) → P) :
    CutQAlg n W P (PQWork (Finset (Fin n)) (CutAnswer n W) Work (n + n)) :=
  T.postQuery imbalanceSelect q (fun o ans => decode o (imbalanceDecodeW ans))

theorem withImbalanceW_prob_one [DecidableEq O] [DecidableEq P] {W : ℕ}
    (T : CutQAlg n W O Work) (q : ℕ) (decode : O → (Fin n → ℝ) → P)
    (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W) (o : O)
    (ho : T.prob (boundedRead W G hG) q o = 1) :
    (withImbalanceW T q decode).prob (boundedRead W G hG) (q + (n + n))
      (decode o (realGraph G).imbalance) = 1 := by
  have hp : ∀ p, (withImbalanceW T q decode).prob (boundedRead W G hG) (q + (n + n)) p =
      ∑ b, if decode (T.readout b) (realGraph G).imbalance = p
        then Complex.normSq (T.state (boundedRead W G hG) q b) else 0 := by
    intro p
    rw [withImbalanceW, postQuery_prob]
    simp_rw [imbalanceDecodeW_honest]
  apply le_antisymm
  · change qProb _ _ _ ≤ 1
    rw [← goodProb_eq]
    exact goodProb_le_one _ _ ((withImbalanceW T q decode).state_isQState _ _)
  · rw [← ho, QAlg.prob, qProb, hp]
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : T.readout b = o
    · simp [hb]
    · simp only [hb, ↓reduceIte]
      split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl

/-- A zero-query branch on the same finite workspace as a public program. -/
def haltAlgW {W : ℕ} (T : CutQAlg n W O Work) (o : O) : CutQAlg n W O Work where
  init := T.init
  init_isQState := T.init_isQState
  step _ := 1
  step_unitary _ := one_mem_qUnitary
  readout _ := o

theorem haltAlgW_prob [DecidableEq O] {W : ℕ} (T : CutQAlg n W O Work) (o : O)
    (read : Finset (Fin n) → CutAnswer n W) : (haltAlgW T o).prob read 0 o = 1 := by
  change qProb (fun _ => o) ((1 : Matrix _ _ ℂ) *ᵥ T.init) o = 1
  simp only [Matrix.one_mulVec, qProb]
  exact T.init_isQState

/-- Any probability-one canonical answer implies probability-one relational correctness. -/
theorem goodProb_of_prob_oneW [DecidableEq O] {W : ℕ} (T : CutQAlg n W O Work)
    (read : Finset (Fin n) → CutAnswer n W) (q : ℕ) (o : O)
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

end BoundedImbalance

section BoundedReconstruct

/-- Finite scratch for symmetrized reconstruction followed by physical imbalance queries. -/
abbrev DirectedWorkW (n W : ℕ) :=
  PQWork (Finset (Fin n)) (CutAnswer n W)
    (PairWork (CutAnswer n W) (Finset (Fin n)) (CutAnswer n (2 * W))
      (GraphWork n (2 * W))) (n + n)

instance directedWorkWDecidableEq (n W : ℕ) : DecidableEq (DirectedWorkW n W) :=
  pqWorkEqW

/-- The native schedule: four calls per symmetrized call, then `2n` imbalance calls. -/
def directedBudget (n W : ℕ) : ℕ := 4 * (n * (6 * rowBits (2 * W))) + (n + n)

theorem directedBudget_le (n W : ℕ) :
    directedBudget n W ≤ n * (24 * Nat.clog 2 (2 * W + 1) + 2) := by
  simp only [directedBudget, rowBits]
  ring_nf
  omega

theorem directedBudget_unit (n : ℕ) : directedBudget n 1 = 50 * n := by
  simp only [directedBudget, Nat.mul_one, rowBits_two]
  omega

/-- Recovered public data, followed by arbitrary public offline processing. -/
def recoverDirectedW {O : Type} (n W : ℕ) (decode : DirectedData (Fin n) → O) :
    CutQAlg n W O (DirectedWorkW n W) :=
  withImbalanceW (symAlgW W (recoverGraphAlg n (2 * W)) (n * (6 * rowBits (2 * W))))
    (4 * (n * (6 * rowBits (2 * W))))
    (fun a β => decode ⟨(graphToCapacity (W := 2 * W) a).toWeighted, β⟩)

theorem recoverDirectedW_prob {O : Type} [DecidableEq O] (n W : ℕ)
    (decode : DirectedData (Fin n) → O) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W) :
    (recoverDirectedW n W decode).prob (boundedRead W G hG) (directedBudget n W)
      (decode ⟨(realGraph G).sym, (realGraph G).imbalance⟩) = 1 := by
  have hg : (symAlgW W (recoverGraphAlg n (2 * W)) (n * (6 * rowBits (2 * W)))).prob
      (boundedRead W G hG) (4 * (n * (6 * rowBits (2 * W))))
      (graphRead (symCapacityW W G hG)) = 1 := by
    rw [symAlgW_prob]
    exact recoverGraphAlg_prob (symCapacityW W G hG)
  have h := withImbalanceW_prob_one
    (symAlgW W (recoverGraphAlg n (2 * W)) (n * (6 * rowBits (2 * W))))
    (4 * (n * (6 * rowBits (2 * W))))
    (fun a β => decode ⟨(graphToCapacity (W := 2 * W) a).toWeighted, β⟩) G hG
    (graphRead (symCapacityW W G hG)) hg
  simpa only [recoverDirectedW, directedBudget, graphToCapacity_read, symCapacityW_real]
    using h

end BoundedReconstruct

section BoundedEndpoints

def terminalQueriesW (W : ℕ) (s t : Fin n) : ℕ := if s = t then 0 else directedBudget n W
def globalQueriesW (n W : ℕ) : ℕ := if n ≤ 1 then 0 else directedBudget n W

def terminalAlgW (W : ℕ) (s t : Fin n) :
    CutQAlg n W (AllPairs.STAnswer (Fin n)) (DirectedWorkW n W) :=
  let T := recoverDirectedW n W (fun D => D.terminalAnswer s t)
  if s = t then haltAlgW T (zeroAnswer n) else T

def globalAlgW (n W : ℕ) : CutQAlg n W (AllPairs.STAnswer (Fin n)) (DirectedWorkW n W) :=
  let T := recoverDirectedW n W DirectedData.globalAnswer
  if n ≤ 1 then haltAlgW T (zeroAnswer n) else T

def allPairsAlgW (n W : ℕ) : CutQAlg n W (AllPairs.Answers (Fin n)) (DirectedWorkW n W) :=
  let T := recoverDirectedW n W DirectedData.allPairsAnswers
  if n ≤ 1 then haltAlgW T (zeroAnswers n) else T

theorem terminalQueriesW_le (W : ℕ) (s t : Fin n) :
    terminalQueriesW W s t ≤ directedBudget n W := by
  unfold terminalQueriesW; split_ifs <;> omega

theorem globalQueriesW_le (n W : ℕ) : globalQueriesW n W ≤ directedBudget n W := by
  unfold globalQueriesW; split_ifs <;> omega

theorem terminalAlgW_prob (W : ℕ) (s t : Fin n) (G : DiGraph (Fin n))
    (hG : ∀ u v, G.c u v ≤ W) :
    (terminalAlgW W s t).prob (boundedRead W G hG) (terminalQueriesW W s t)
      ((honestData G).terminalAnswer s t) = 1 := by
  by_cases hst : s = t
  · subst t
    simp only [terminalAlgW, terminalQueriesW, ite_true, DirectedData.terminalAnswer_self]
    exact haltAlgW_prob _ _ _
  · simp only [terminalAlgW, terminalQueriesW, hst, ite_false]
    exact recoverDirectedW_prob n W _ G hG

theorem globalAlgW_prob (n W : ℕ) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W) :
    (globalAlgW n W).prob (boundedRead W G hG) (globalQueriesW n W)
      (honestData G).globalAnswer = 1 := by
  by_cases hn : n ≤ 1
  · simp only [globalAlgW, globalQueriesW, hn, ite_true]
    rw [DirectedData.globalAnswer_tiny _ (by simpa using (by omega : n < 2))]
    exact haltAlgW_prob _ _ _
  · simp only [globalAlgW, globalQueriesW, hn, ite_false]
    exact recoverDirectedW_prob n W _ G hG

theorem allPairsAlgW_prob (n W : ℕ) (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W) :
    (allPairsAlgW n W).prob (boundedRead W G hG) (globalQueriesW n W)
      (honestData G).allPairsAnswers = 1 := by
  by_cases hn : n ≤ 1
  · have ht : (honestData G).allPairsAnswers = zeroAnswers n := by
      funext s t
      have hst : t = s := Fin.ext (by have ht := t.isLt; have hs := s.isLt; omega)
      subst t
      exact DirectedData.terminalAnswer_self _ _
    simp only [allPairsAlgW, globalQueriesW, hn, ite_true, ht]
    exact haltAlgW_prob _ _ _
  · simp only [allPairsAlgW, globalQueriesW, hn, ite_false]
    exact recoverDirectedW_prob n W _ G hG

/-- Arc capacities in `{0,…,W}`: probability-one original global shore and value. -/
theorem exists_capacity_global (n W : ℕ) :
    ∃ T : CutQAlg n W (AllPairs.STAnswer (Fin n)) (DirectedWorkW n W),
      T = globalAlgW n W ∧ globalQueriesW n W ≤ n * (24 * Nat.clog 2 (2 * W + 1) + 2) ∧
      ∀ (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W),
        goodProb T.readout (GlobalGood G) (T.state (boundedRead W G hG) (globalQueriesW n W)) = 1 :=
  ⟨globalAlgW n W, rfl, (globalQueriesW_le n W).trans (directedBudget_le n W),
    fun G hG => goodProb_of_prob_oneW _ _ _ _ (globalAlgW_prob n W G hG) _
      (honestData_global_good G)⟩

/-- Arc capacities in `{0,…,W}`: probability-one original terminal shore and value. -/
theorem exists_capacity_terminal (W : ℕ) (s t : Fin n) :
    ∃ T : CutQAlg n W (AllPairs.STAnswer (Fin n)) (DirectedWorkW n W),
      T = terminalAlgW W s t ∧ terminalQueriesW W s t ≤ n * (24 * Nat.clog 2 (2 * W + 1) + 2) ∧
      ∀ (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W),
        goodProb T.readout (TerminalGood G s t)
          (T.state (boundedRead W G hG) (terminalQueriesW W s t)) = 1 :=
  ⟨terminalAlgW W s t, rfl, (terminalQueriesW_le W s t).trans (directedBudget_le n W),
    fun G hG => goodProb_of_prob_oneW _ _ _ _ (terminalAlgW_prob W s t G hG) _
      (honestData_terminal_good G s t)⟩

/-- Arc capacities in `{0,…,W}`: one program solves every ordered pair. -/
theorem exists_capacity_allPairs (n W : ℕ) :
    ∃ T : CutQAlg n W (AllPairs.Answers (Fin n)) (DirectedWorkW n W),
      T = allPairsAlgW n W ∧ globalQueriesW n W ≤ n * (24 * Nat.clog 2 (2 * W + 1) + 2) ∧
      ∀ (G : DiGraph (Fin n)) (hG : ∀ u v, G.c u v ≤ W),
        goodProb T.readout (AllPairsGood G)
          (T.state (boundedRead W G hG) (globalQueriesW n W)) = 1 :=
  ⟨allPairsAlgW n W, rfl, (globalQueriesW_le n W).trans (directedBudget_le n W),
    fun G hG => goodProb_of_prob_oneW _ _ _ _ (allPairsAlgW_prob n W G hG) _
      (honestData_allPairs_good G)⟩

end BoundedEndpoints

#print axioms bounded_out_le
#print axioms symReadW_honest
#print axioms symAlgW_prob
#print axioms imbalanceDecodeW_honest
#print axioms withImbalanceW_prob_one
#print axioms directedBudget_le
#print axioms directedBudget_unit
#print axioms recoverDirectedW_prob
#print axioms exists_capacity_global
#print axioms exists_capacity_terminal
#print axioms exists_capacity_allPairs

end
end CutQueryComplexity.Quantum.DirectedReconstruction
