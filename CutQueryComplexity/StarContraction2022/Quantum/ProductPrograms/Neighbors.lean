import CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Counts
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic

/-! # Public center-neighborhood queries with complete range validation

One singleton product query recovers a center row on honest unit-capacity
graphs. Arbitrary finite answers are checked coordinate by coordinate and at
the diagonal. A failed check returns `none` immediately. The actual query
tree, its public index, and its guards do not take a hidden graph.

The all-answer run law records both output and executed count. Honest graphs
are used only to prove validation succeeds and identify the returned rows.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms

noncomputable section
open scoped Classical

abbrev NeighborhoodTable (n : ℕ) := Fin n → Finset (Fin n)

def emptyNeighborhoodTable (n : ℕ) : NeighborhoodTable n := fun _ => ∅

variable {n : ℕ}

/-- A general product answer need not be a bit vector. -/
def neighborhoodAnswerValid (r : Fin n) (answer : ProductAnswer n 1) : Prop :=
  (∀ v, (answer v).val ≤ 1) ∧ (answer r).val = 0

def neighborhoodOfAnswer (answer : ProductAnswer n 1) : Finset (Fin n) :=
  Finset.univ.filter fun v => (answer v).val = 1

theorem neighborhoodOfAnswer_not_mem_self {r : Fin n} {answer : ProductAnswer n 1}
    (h : neighborhoodAnswerValid r answer) : r ∉ neighborhoodOfAnswer answer := by
  simp [neighborhoodOfAnswer, h.2]

/-- Reference table for a public reply function; unqueried rows are empty. -/
def measuredNeighborhoodTable (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) : NeighborhoodTable n :=
  fun r => if r ∈ R then neighborhoodOfAnswer (read {r}) else ∅

private def patchNeighborhoodRows (L : List (Fin n))
    (values rows : NeighborhoodTable n) : NeighborhoodTable n :=
  fun v => if v ∈ L then values v else rows v

private theorem patchNeighborhoodRows_cons (r : Fin n) (L : List (Fin n))
    (values rows : NeighborhoodTable n) :
    patchNeighborhoodRows L values (Function.update rows r (values r)) =
      patchNeighborhoodRows (r :: L) values rows := by
  funext v
  by_cases h : v = r
  · subst v
    by_cases hm : r ∈ L <;> simp [patchNeighborhoodRows, hm]
  · by_cases hm : v ∈ L <;>
      simp [patchNeighborhoodRows, hm, h, Function.update_apply]

/-- The actual finite query program. Invalid answers stop without further calls. -/
private def centerNeighborhoodsAux : (L : List (Fin n)) → NeighborhoodTable n →
    ProductTree n (Option (NeighborhoodTable n)) L.length
  | [], rows => RTree.pure (PMF.pure (some rows))
  | r :: L, rows => RTree.query {r} fun answer =>
      if neighborhoodAnswerValid r answer then
        centerNeighborhoodsAux L (Function.update rows r (neighborhoodOfAnswer answer))
      else RTree.pure (PMF.pure none)

/-- Explicit deterministic output/count semantics, including the failing call. -/
private def centerNeighborhoodResultAux
    (read : Finset (Fin n) → ProductAnswer n 1) :
    List (Fin n) → NeighborhoodTable n → Option (NeighborhoodTable n) × ℕ
  | [], rows => (some rows, 0)
  | r :: L, rows =>
      if neighborhoodAnswerValid r (read {r}) then
        let next := centerNeighborhoodResultAux read L
          (Function.update rows r (neighborhoodOfAnswer (read {r})))
        (next.1, next.2 + 1)
      else (none, 1)

private theorem centerNeighborhoodsAux_run
    (read : Finset (Fin n) → ProductAnswer n 1) (L : List (Fin n))
    (rows : NeighborhoodTable n) :
    RTree.run read (centerNeighborhoodsAux L rows) =
      PMF.pure (centerNeighborhoodResultAux read L rows) := by
  induction L generalizing rows with
  | nil => simp [centerNeighborhoodsAux, centerNeighborhoodResultAux, PMF.pure_map]
  | cons r L ih =>
      by_cases h : neighborhoodAnswerValid r (read {r})
      · simp [centerNeighborhoodsAux, centerNeighborhoodResultAux, h, ih, PMF.pure_map]
      · simp [centerNeighborhoodsAux, centerNeighborhoodResultAux, h, PMF.pure_map]

private theorem centerNeighborhoodResultAux_none_iff
    (read : Finset (Fin n) → ProductAnswer n 1) (L : List (Fin n))
    (rows : NeighborhoodTable n) :
    (centerNeighborhoodResultAux read L rows).1 = none ↔
      ∃ r ∈ L, ¬ neighborhoodAnswerValid r (read {r}) := by
  induction L generalizing rows with
  | nil => simp [centerNeighborhoodResultAux]
  | cons r L ih =>
      by_cases h : neighborhoodAnswerValid r (read {r})
      · simp [centerNeighborhoodResultAux, h, ih, List.mem_cons, or_and_right, exists_or]
      · simp [centerNeighborhoodResultAux, h, List.mem_cons, or_and_right, exists_or]

private theorem centerNeighborhoodResultAux_of_valid
    (read : Finset (Fin n) → ProductAnswer n 1) (L : List (Fin n))
    (rows : NeighborhoodTable n)
    (h : ∀ r ∈ L, neighborhoodAnswerValid r (read {r})) :
    centerNeighborhoodResultAux read L rows =
      (some (patchNeighborhoodRows L
        (fun r => neighborhoodOfAnswer (read {r})) rows), L.length) := by
  revert rows h
  induction L with
  | nil =>
      intro rows _
      have hp : patchNeighborhoodRows []
          (fun r => neighborhoodOfAnswer (read {r})) rows = rows := by
        funext v
        simp [patchNeighborhoodRows]
      rw [centerNeighborhoodResultAux, hp, List.length_nil]
  | cons r L ih =>
      intro rows h
      have hr : neighborhoodAnswerValid r (read {r}) := h r (by simp)
      have hL : ∀ v ∈ L, neighborhoodAnswerValid v (read {v}) :=
        fun v hv => h v (List.mem_cons_of_mem r hv)
      have ht := ih (Function.update rows r (neighborhoodOfAnswer (read {r}))) hL
      simp [centerNeighborhoodResultAux, hr, ht, patchNeighborhoodRows_cons]

/-- Exactly the public center-cardinality index; no graph or success promise. -/
def centerNeighborhoods (R : Finset (Fin n)) :
    ProductTree n (Option (NeighborhoodTable n)) R.card :=
  RTree.cast (Finset.length_toList R)
    (centerNeighborhoodsAux R.toList (emptyNeighborhoodTable n))

def centerNeighborhoodResult (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) :
    Option (NeighborhoodTable n) × ℕ :=
  centerNeighborhoodResultAux read R.toList (emptyNeighborhoodTable n)

/-- The executed output and count on every finite product-answer table. -/
theorem centerNeighborhoods_run (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (centerNeighborhoods R) =
      PMF.pure (centerNeighborhoodResult R read) := by
  simp only [centerNeighborhoods, RTree.run_cast, centerNeighborhoodsAux_run,
    centerNeighborhoodResult]

theorem centerNeighborhoods_cost (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1)
    {out : Option (NeighborhoodTable n) × ℕ}
    (h : out ∈ (RTree.run read (centerNeighborhoods R)).support) :
    out.2 ≤ R.card := RTree.cost_le _ read h

theorem centerNeighborhoodResult_cost (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (centerNeighborhoodResult R read).2 ≤ R.card := by
  apply centerNeighborhoods_cost R read
  rw [centerNeighborhoods_run]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- Every malformed center row causes explicit failure, including an unvisited
bad row following an earlier failing row. No conditioning on validation is used. -/
theorem centerNeighborhoodResult_none_iff (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (centerNeighborhoodResult R read).1 = none ↔
      ∃ r ∈ R, ¬ neighborhoodAnswerValid r (read {r}) := by
  simpa only [centerNeighborhoodResult, Finset.mem_toList] using
    centerNeighborhoodResultAux_none_iff read R.toList (emptyNeighborhoodTable n)

theorem centerNeighborhoodResult_bad_coordinate (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) {r v : Fin n} (hr : r ∈ R)
    (hbad : 1 < (read {r} v).val) :
    (centerNeighborhoodResult R read).1 = none := by
  apply (centerNeighborhoodResult_none_iff R read).mpr
  exact ⟨r, hr, fun h => (not_lt_of_ge (h.1 v)) hbad⟩

theorem centerNeighborhoodResult_bad_diagonal (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1) {r : Fin n} (hr : r ∈ R)
    (hbad : (read {r} r).val ≠ 0) :
    (centerNeighborhoodResult R read).1 = none :=
  (centerNeighborhoodResult_none_iff R read).mpr ⟨r, hr, fun h => hbad h.2⟩

theorem centerNeighborhoodResult_of_valid (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1)
    (h : ∀ r ∈ R, neighborhoodAnswerValid r (read {r})) :
    centerNeighborhoodResult R read =
      (some (measuredNeighborhoodTable R read), R.card) := by
  have hL : ∀ r ∈ R.toList, neighborhoodAnswerValid r (read {r}) :=
    fun r hr => h r (Finset.mem_toList.mp hr)
  have hp : patchNeighborhoodRows R.toList
      (fun r => neighborhoodOfAnswer (read {r})) (emptyNeighborhoodTable n) =
      measuredNeighborhoodTable R read := by
    funext v
    simp [patchNeighborhoodRows, measuredNeighborhoodTable, emptyNeighborhoodTable]
  change centerNeighborhoodResultAux read R.toList (emptyNeighborhoodTable n) = _
  rw [centerNeighborhoodResultAux_of_valid read R.toList (emptyNeighborhoodTable n) hL,
    hp, Finset.length_toList]

theorem centerNeighborhoods_run_of_valid (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1)
    (h : ∀ r ∈ R, neighborhoodAnswerValid r (read {r})) :
    RTree.run read (centerNeighborhoods R) =
      PMF.pure (some (measuredNeighborhoodTable R read), R.card) := by
  rw [centerNeighborhoods_run, centerNeighborhoodResult_of_valid R read h]

theorem centerNeighborhoods_supported_some (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1)
    {rows : NeighborhoodTable n} {k : ℕ}
    (h : (some rows, k) ∈ (RTree.run read (centerNeighborhoods R)).support) :
    rows = measuredNeighborhoodTable R read ∧ k = R.card ∧
      ∀ r ∈ R, neighborhoodAnswerValid r (read {r}) := by
  rw [centerNeighborhoods_run] at h
  have hp : (some rows, k) = centerNeighborhoodResult R read :=
    (PMF.mem_support_pure_iff _ _).mp h
  have hv : ∀ r ∈ R, neighborhoodAnswerValid r (read {r}) := by
    intro r hr
    by_contra hbad
    have hn := (centerNeighborhoodResult_none_iff R read).mpr ⟨r, hr, hbad⟩
    have he : some rows = none := (congrArg Prod.fst hp).trans hn
    cases he
  have he := hp.trans (centerNeighborhoodResult_of_valid R read hv)
  exact ⟨Option.some.inj (congrArg Prod.fst he), congrArg Prod.snd he, hv⟩

theorem centerNeighborhoods_rows_outside (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1)
    {rows : NeighborhoodTable n} {k : ℕ}
    (h : (some rows, k) ∈ (RTree.run read (centerNeighborhoods R)).support)
    {r : Fin n} (hr : r ∉ R) : rows r = ∅ := by
  rw [(centerNeighborhoods_supported_some R read h).1]
  simp [measuredNeighborhoodTable, hr]

theorem centerNeighborhoods_rows_diagonal (R : Finset (Fin n))
    (read : Finset (Fin n) → ProductAnswer n 1)
    {rows : NeighborhoodTable n} {k : ℕ}
    (h : (some rows, k) ∈ (RTree.run read (centerNeighborhoods R)).support)
    (r : Fin n) : r ∉ rows r := by
  obtain ⟨hrows, _, hv⟩ := centerNeighborhoods_supported_some R read h
  rw [hrows]
  by_cases hr : r ∈ R
  · simp [measuredNeighborhoodTable, hr, neighborhoodOfAnswer, (hv r hr).2]
  · simp [measuredNeighborhoodTable, hr]

/-! The graph enters only the following target definitions and theorems. -/

def capacityNeighbors (G : CapacityGraph (Fin n) 1) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => (G.w r v : ℕ) = 1

def exactCenterNeighborhoodTable (G : CapacityGraph (Fin n) 1)
    (R : Finset (Fin n)) : NeighborhoodTable n :=
  fun r => if r ∈ R then capacityNeighbors G r else ∅

theorem productRead_singleton_val (G : CapacityGraph (Fin n) 1) (r v : Fin n) :
    (productRead G {r} v).val = (G.w r v : ℕ) := by
  rw [productRead_val]
  by_cases h : v = r
  · subst v
    simp [productNat, G.diag]
  · rw [productNat_of_not_mem G {r} (by simpa only [Finset.mem_singleton] using h)]
    simp only [Finset.sum_singleton]
    exact congrArg Fin.val (G.symm v r)

theorem neighborhoodAnswerValid_honest (G : CapacityGraph (Fin n) 1) (r : Fin n) :
    neighborhoodAnswerValid r (productRead G {r}) := by
  constructor
  · intro v
    rw [productRead_singleton_val]
    exact Nat.le_of_lt_succ (G.w r v).isLt
  · simp [productRead_singleton_val, G.diag]

theorem neighborhoodOfAnswer_honest (G : CapacityGraph (Fin n) 1) (r : Fin n) :
    neighborhoodOfAnswer (productRead G {r}) = capacityNeighbors G r := by
  ext v
  simp only [neighborhoodOfAnswer, capacityNeighbors, Finset.mem_filter,
    Finset.mem_univ, true_and, productRead_singleton_val]

theorem measuredNeighborhoodTable_honest (R : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) :
    measuredNeighborhoodTable R (productRead G) = exactCenterNeighborhoodTable G R := by
  funext r
  by_cases hr : r ∈ R <;>
    simp [measuredNeighborhoodTable, exactCenterNeighborhoodTable, hr,
      neighborhoodOfAnswer_honest]

/-- Exact joint law: honest validation loses no outcomes and executes R.card calls. -/
theorem centerNeighborhoods_run_honest (R : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) :
    RTree.run (productRead G) (centerNeighborhoods R) =
      PMF.pure (some (exactCenterNeighborhoodTable G R), R.card) := by
  rw [centerNeighborhoods_run_of_valid R (productRead G)
    (fun r _ => neighborhoodAnswerValid_honest G r), measuredNeighborhoodTable_honest]

theorem centerNeighborhoods_eval_honest (R : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) :
    (centerNeighborhoods R).eval (productRead G) =
      PMF.pure (some (exactCenterNeighborhoodTable G R)) := by
  simp only [RTree.eval, centerNeighborhoods_run_honest, PMF.pure_map]

theorem centerNeighborhoods_successProb_honest (R : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) :
    (centerNeighborhoods R).successProb (productRead G)
      (fun out => out = some (exactCenterNeighborhoodTable G R)) = 1 := by
  rw [RTree.successProb_eq, centerNeighborhoods_eval_honest]
  simp [PMF.toOuterMeasure_pure_apply]

/-- Public outside-to-center lookup; it is total even for vertices in R. -/
def outsideCenterNeighbors (R : Finset (Fin n)) (rows : NeighborhoodTable n)
    (v : Fin n) : Finset (Fin n) := R.filter fun r => v ∈ rows r

theorem outsideCenterNeighbors_exact (R : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) (v : Fin n) :
    outsideCenterNeighbors R (exactCenterNeighborhoodTable G R) v =
      R.filter (fun r => (G.w v r : ℕ) = 1) := by
  ext r
  by_cases hr : r ∈ R
  · simp [outsideCenterNeighbors, exactCenterNeighborhoodTable, hr,
      capacityNeighbors, G.symm r v]
  · simp [outsideCenterNeighbors, hr]

theorem outsideCenterNeighbors_supported (R : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) {rows : NeighborhoodTable n}
    (h : some rows ∈ ((centerNeighborhoods R).eval (productRead G)).support)
    (v : Fin n) :
    outsideCenterNeighbors R rows v = R.filter (fun r => (G.w v r : ℕ) = 1) := by
  rw [centerNeighborhoods_eval_honest] at h
  have he := (PMF.mem_support_pure_iff _ _).mp h
  have ht : rows = exactCenterNeighborhoodTable G R := Option.some.inj he
  rw [ht]
  exact outsideCenterNeighbors_exact R G v

theorem centerNeighborhoods_run_empty
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (centerNeighborhoods (∅ : Finset (Fin n))) =
      PMF.pure (some (emptyNeighborhoodTable n), 0) := by
  have ht : measuredNeighborhoodTable (∅ : Finset (Fin n)) read =
      emptyNeighborhoodTable n := by
    funext r
    simp [measuredNeighborhoodTable, emptyNeighborhoodTable]
  rw [centerNeighborhoods_run_of_valid (∅ : Finset (Fin n)) read (by simp), ht]
  rfl

theorem centerNeighborhoods_zero (R : Finset (Fin 0))
    (read : Finset (Fin 0) → ProductAnswer 0 1) :
    RTree.run read (centerNeighborhoods R) =
      PMF.pure (some (emptyNeighborhoodTable 0), 0) := by
  have hR : R = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v _
    exact Fin.elim0 v
  subst R
  exact centerNeighborhoods_run_empty read

theorem centerNeighborhoods_one_honest (R : Finset (Fin 1))
    (G : CapacityGraph (Fin 1) 1) :
    RTree.run (productRead G) (centerNeighborhoods R) =
      PMF.pure (some (emptyNeighborhoodTable 1), R.card) := by
  have ht : exactCenterNeighborhoodTable G R = emptyNeighborhoodTable 1 := by
    funext r
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hrv : r = v := Subsingleton.elim _ _
    subst v
    by_cases hr : r ∈ R <;>
      simpa [exactCenterNeighborhoodTable, capacityNeighbors, hr, G.diag] using hv
  rw [centerNeighborhoods_run_honest, ht]

theorem centerNeighborhoods_one_cost (R : Finset (Fin 1))
    (read : Finset (Fin 1) → ProductAnswer 1 1)
    {out : Option (NeighborhoodTable 1) × ℕ}
    (h : out ∈ (RTree.run read (centerNeighborhoods R)).support) : out.2 ≤ 1 :=
  (centerNeighborhoods_cost R read h).trans (by simpa using Finset.card_le_univ R)

section PhysicalCompiler

attribute [local instance] basisDecidableEq workspaceDecidableEq

/-- Reuse the accepted physical compiler, with no new oracle simulation claim. -/
theorem centerNeighborhoods_physical_length (R : Finset (Fin n)) :
    (productTreeRoutine (centerNeighborhoods R)).len =
      12 * productBits n 1 * R.card := productTreeRoutine_len _

end PhysicalCompiler

#print axioms productRead_singleton_val
#print axioms neighborhoodAnswerValid_honest
#print axioms neighborhoodOfAnswer_honest
#print axioms centerNeighborhoods_run
#print axioms centerNeighborhoods_cost
#print axioms centerNeighborhoodResult_none_iff
#print axioms centerNeighborhoodResult_bad_coordinate
#print axioms centerNeighborhoodResult_bad_diagonal
#print axioms centerNeighborhoods_run_of_valid
#print axioms centerNeighborhoods_supported_some
#print axioms centerNeighborhoods_rows_outside
#print axioms centerNeighborhoods_rows_diagonal
#print axioms centerNeighborhoods_run_honest
#print axioms centerNeighborhoods_eval_honest
#print axioms centerNeighborhoods_successProb_honest
#print axioms outsideCenterNeighbors_exact
#print axioms outsideCenterNeighbors_supported
#print axioms centerNeighborhoods_run_empty
#print axioms centerNeighborhoods_zero
#print axioms centerNeighborhoods_one_honest
#print axioms centerNeighborhoods_one_cost
#print axioms centerNeighborhoods_physical_length

end
end CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms
