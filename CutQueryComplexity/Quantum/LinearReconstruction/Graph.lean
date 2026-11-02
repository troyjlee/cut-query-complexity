import CutQueryComplexity.Quantum.LinearReconstruction.Row

/-! # Complete physical bounded-capacity reconstruction
Each row is recovered coherently and swapped into its initially blank output
slot. The row scratch is restored to zero without another query. -/
set_option autoImplicit false
namespace CutQueryComplexity.Quantum.LinearReconstruction
noncomputable section
open QuantumQueryComplexity
open CutQueryComplexity.StarContraction2022.Quantum
open scoped Matrix
open Matrix

abbrev GraphAnswer (n W : ℕ) := Fin n → RowAnswer n W
abbrev GraphWork (n W : ℕ) := GraphAnswer n W × RowAnswer n W

local instance graphAnswerDecidableEq {n W : ℕ} : DecidableEq (GraphAnswer n W) :=
  inferInstanceAs (DecidableEq (Fin n → RowAnswer n W))
local instance graphWorkDecidableEq {n W : ℕ} : DecidableEq (GraphWork n W) :=
  inferInstanceAs (DecidableEq (GraphAnswer n W × RowAnswer n W))
local instance basisDecidableEq {I A D : Type} [DecidableEq I]
    [DecidableEq A] [DecidableEq D] : DecidableEq (QBasis I A D) :=
  inferInstanceAs (DecidableEq (Option I × Option A × D))

def graphZero (n W : ℕ) : GraphAnswer n W := fun _ => rowZero n W
def graphRead {n W : ℕ} (G : CapacityGraph (Fin n) W) : GraphAnswer n W := rowRead G

/-- A public reversible exchange of one output slot and the row scratch. -/
def swapRow {n W : ℕ} (v : Fin n) : Equiv.Perm (GraphWork n W) :=
  Function.Involutive.toPerm (fun p => (Function.update p.1 v p.2, p.1 v)) (by
    rintro ⟨a, b⟩
    simp only [Function.update_self]
    congr 1
    funext u
    by_cases h : u = v
    · subst u; simp
    · simp [Function.update_of_ne h])

@[simp] theorem swapRow_apply {n W : ℕ} (v : Fin n) (p : GraphWork n W) :
    swapRow v p = (Function.update p.1 v p.2, p.1 v) := rfl

def recoverGraphRow (n W : ℕ) (v : Fin n) :
    QRoutine (Finset (Fin n)) (CutAnswer n W) (GraphWork n W) :=
  (recoverRow n W (fun _ : GraphAnswer n W => v)).comp
    (workGate (qPerm (swapRow v)) (qPerm_mem_unitaryGroup _))

@[simp] theorem recoverGraphRow_len (n W : ℕ) (v : Fin n) :
    (recoverGraphRow n W v).len = 6 * rowBits W := by
  simp [recoverGraphRow]

theorem recoverGraphRow_run {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (v : Fin n) (a : GraphAnswer n W) (ha : a v = rowZero n W) :
    (recoverGraphRow n W v).run (capacityRead G) *ᵥ
      qBasis (none, none, a, rowZero n W) =
      qBasis (none, none, Function.update a v (rowRead G v), rowZero n W) := by
  rw [recoverGraphRow, QRoutine.comp_run, ← Matrix.mulVec_mulVec, recoverRow_run_basis]
  change (workGate (qPerm (swapRow v)) (qPerm_mem_unitaryGroup _)).run (capacityRead G) *ᵥ
    qBasis (workEncode (a, rowRead G v)) = _
  rw [workGate_perm_run]
  simp [workEncode, ha]

def graphPrefix {n W : ℕ} (G : CapacityGraph (Fin n) W) (t : ℕ) : GraphAnswer n W :=
  fun v => if v.val < t then rowRead G v else rowZero n W

@[simp] theorem graphPrefix_zero {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    graphPrefix G 0 = graphZero n W := by funext v; simp [graphPrefix, graphZero]

@[simp] theorem graphPrefix_full {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    graphPrefix G n = graphRead G := by funext v; simp [graphPrefix, graphRead, v.isLt]

theorem graphPrefix_next {n W t : ℕ} (G : CapacityGraph (Fin n) W) (ht : t < n) :
    Function.update (graphPrefix G t) ⟨t, ht⟩ (rowRead G ⟨t, ht⟩) =
      graphPrefix G (t + 1) := by
  funext v
  by_cases h : v = ⟨t, ht⟩
  · subst v; simp [graphPrefix]
  · have hv : v.val ≠ t := by intro he; apply h; exact Fin.ext he
    rw [Function.update_of_ne h]
    simp only [graphPrefix]
    have he : v.val < t ↔ v.val < t + 1 := by omega
    simp only [he]

def recoverGraphUpto (n W : ℕ) : ℕ →
    QRoutine (Finset (Fin n)) (CutAnswer n W) (GraphWork n W)
  | 0 => QRoutine.identity
  | t + 1 => if ht : t < n then
      (recoverGraphUpto n W t).comp (recoverGraphRow n W ⟨t, ht⟩)
    else recoverGraphUpto n W t

theorem recoverGraphUpto_len (n W t : ℕ) (ht : t ≤ n) :
    (recoverGraphUpto n W t).len = t * (6 * rowBits W) := by
  induction t with
  | zero => simp [recoverGraphUpto]
  | succ t ih =>
    have hlt : t < n := by omega
    simp [recoverGraphUpto, hlt, ih (by omega), Nat.succ_mul]

theorem recoverGraphUpto_run {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (t : ℕ) (ht : t ≤ n) :
    (recoverGraphUpto n W t).run (capacityRead G) *ᵥ
      qBasis (none, none, graphZero n W, rowZero n W) =
      qBasis (none, none, graphPrefix G t, rowZero n W) := by
  induction t with
  | zero => simp [recoverGraphUpto]
  | succ t ih =>
    have hlt : t < n := by omega
    rw [recoverGraphUpto, dite_eq_left hlt, QRoutine.comp_run, ← Matrix.mulVec_mulVec,
      ih (by omega), recoverGraphRow_run G ⟨t, hlt⟩ _ (by simp [graphPrefix]),
      graphPrefix_next G hlt]

/-- Public graph routine; n=0 has an empty native query schedule. -/
def recoverGraph (n W : ℕ) :
    QRoutine (Finset (Fin n)) (CutAnswer n W) (GraphWork n W) :=
  recoverGraphUpto n W n

@[simp] theorem recoverGraph_len (n W : ℕ) :
    (recoverGraph n W).len = n * (6 * rowBits W) := recoverGraphUpto_len n W n le_rfl

theorem recoverGraph_run {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    (recoverGraph n W).run (capacityRead G) *ᵥ
      qBasis (none, none, graphZero n W, rowZero n W) =
      qBasis (none, none, graphRead G, rowZero n W) := by
  simpa [recoverGraph] using recoverGraphUpto_run G n le_rfl

def recoverGraphAlg (n W : ℕ) : CutQAlg n W (GraphAnswer n W) (GraphWork n W) :=
  (recoverGraph n W).toAlg
    (qBasis (none, none, graphZero n W, rowZero n W)) (isQState_qBasis _) (fun p => p.2.2.1)

theorem recoverGraphAlg_state {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    (recoverGraphAlg n W).state (capacityRead G) (n * (6 * rowBits W)) =
      qBasis (none, none, graphRead G, rowZero n W) := by
  unfold recoverGraphAlg
  rw [← recoverGraph_len, QRoutine.toAlg_state_len, recoverGraph_run]

theorem recoverGraphAlg_born {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (y : GraphAnswer n W) :
    (recoverGraphAlg n W).prob (capacityRead G) (n * (6 * rowBits W)) y =
      if graphRead G = y then 1 else 0 := by
  rw [QAlg.prob, recoverGraphAlg_state, qProb_qBasis]
  rfl

theorem recoverGraphAlg_prob {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    (recoverGraphAlg n W).prob (capacityRead G) (n * (6 * rowBits W)) (graphRead G) = 1 := by
  simp [recoverGraphAlg_born]

theorem recoverGraphAlg_normalized (n W : ℕ)
    (read : Finset (Fin n) → CutAnswer n W) (t : ℕ) :
    ∑ y, (recoverGraphAlg n W).prob read t y = 1 :=
  sum_qProb_eq_one ((recoverGraphAlg n W).state_isQState read t) _

/-- Total finite offline decoding; invalid matrices use the zero graph. -/
def graphToCapacity {n W : ℕ} (a : GraphAnswer n W) : CapacityGraph (Fin n) W :=
  if h : ∃ G : CapacityGraph (Fin n) W, graphRead G = a then Classical.choose h
  else ⟨fun _ _ => 0, by simp, by simp⟩

@[simp] theorem graphToCapacity_read {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    graphToCapacity (graphRead G) = G := by
  unfold graphToCapacity
  rw [dite_eq_left ⟨G, rfl⟩]
  apply CapacityGraph.ext
  funext u v
  apply Fin.ext
  have h := congrFun (congrFun (Classical.choose_spec (show ∃ H : CapacityGraph (Fin n) W,
    graphRead H = graphRead G from ⟨G, rfl⟩)) v) u
  simpa only [graphRead, rowRead_val] using congrArg Fin.val h

@[simp] theorem recoverGraph_len_unit (n : ℕ) : (recoverGraph n 1).len = 6 * n := by
  simp [Nat.mul_comm]
@[simp] theorem recoverGraph_len_two (n : ℕ) : (recoverGraph n 2).len = 12 * n := by
  simp [Nat.mul_comm]
@[simp] theorem recoverGraph_len_zeroCapacity (n : ℕ) : (recoverGraph n 0).len = 0 := by simp
@[simp] theorem recoverGraph_len_empty (W : ℕ) : (recoverGraph 0 W).len = 0 := by simp

#print axioms GraphAnswer
#print axioms GraphWork
#print axioms graphZero
#print axioms graphRead
#print axioms swapRow
#print axioms swapRow_apply
#print axioms recoverGraphRow
#print axioms recoverGraphRow_len
#print axioms recoverGraphRow_run
#print axioms graphPrefix
#print axioms graphPrefix_zero
#print axioms graphPrefix_full
#print axioms graphPrefix_next
#print axioms recoverGraphUpto
#print axioms recoverGraphUpto_len
#print axioms recoverGraphUpto_run
#print axioms recoverGraph
#print axioms recoverGraph_len
#print axioms recoverGraph_run
#print axioms recoverGraphAlg
#print axioms recoverGraphAlg_state
#print axioms recoverGraphAlg_born
#print axioms recoverGraphAlg_prob
#print axioms recoverGraphAlg_normalized
#print axioms graphToCapacity
#print axioms graphToCapacity_read
#print axioms recoverGraph_len_unit
#print axioms recoverGraph_len_two
#print axioms recoverGraph_len_zeroCapacity
#print axioms recoverGraph_len_empty
end
end CutQueryComplexity.Quantum.LinearReconstruction
