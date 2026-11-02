import CutQueryComplexity.DirectedUnitST.Repair.Basic
import CutQueryComplexity.DirectedCertificate.Basic
import Mathlib.Tactic.Tauto

/-!
# Public learned residual state

The state contains only measured singleton values, a public direction table,
and learned residual entries. `Realizes` relates this public data to the
original outgoing-cut oracle and the currently represented residual graph.
It is a proof invariant, never an argument to an executable choice.

Learning a previously unknown positive pair records both residual directions.
Flow updates are allowed only on learned pairs; all unknown capacities retain
their original public direction. Heavy auxiliary terminal arcs are stored by
the full-network wrapper separately and are never queried.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Blocking

open Finset DirectedCertificate Certificate
open scoped Classical
noncomputable section

variable {V : Type} [DecidableEq V]

/-- No hidden capacity matrix or correctness proof is stored in the public state. -/
structure State (V : Type) where
  singletonValue : V → ℝ
  outward : V → Finset V
  known : Finset (V × V)
  knownResidual : V → V → ℝ

namespace State

variable [Fintype V]

/-- Exact information maintained by learning and by supported flow updates. -/
structure Realizes (G H : WeightedDiGraph V) (st : State V) : Prop where
  singleton : ∀ v, st.singletonValue v = G.out {v}
  known_symm : ∀ u v, (u, v) ∈ st.known ↔ (v, u) ∈ st.known
  direction : ∀ u v, u ≠ v → (v ∈ st.outward u ↔ u ∉ st.outward v)
  learned : ∀ u v, (u, v) ∈ st.known → H.c u v = st.knownResidual u v
  unknown : ∀ u v, (u, v) ∉ st.known →
    H.c u v = if v ∈ st.outward u then G.sym.w u v else 0

/-- Row-specific public argument used by the residual neighbor program. -/
def knownNeighbors (st : State V) (u : V) : Finset V :=
  univ.filter fun v => (u, v) ∈ st.known

@[simp] theorem mem_knownNeighbors (st : State V) (u v : V) :
    v ∈ st.knownNeighbors u ↔ (u, v) ∈ st.known := by
  simp [knownNeighbors]

omit [Fintype V] in
/-- Record a new forward pair. Its reverse capacity is zero before any push. -/
def record (st : State V) (u v : V) (capacity : ℝ) : State V where
  singletonValue := st.singletonValue
  outward := st.outward
  known := insert (u, v) (insert (v, u) st.known)
  knownResidual x y :=
    if x = u ∧ y = v then capacity else
    if x = v ∧ y = u then 0 else st.knownResidual x y

omit [Fintype V] in
theorem known_subset_record (st : State V) (u v : V) (capacity : ℝ) :
    st.known ⊆ (st.record u v capacity).known := by
  intro e he
  exact mem_insert_of_mem (mem_insert_of_mem he)

omit [Fintype V] in
@[simp] theorem record_known_forward (st : State V) (u v : V) (capacity : ℝ) :
    (u, v) ∈ (st.record u v capacity).known := by simp [record]

omit [Fintype V] in
@[simp] theorem record_known_reverse (st : State V) (u v : V) (capacity : ℝ) :
    (v, u) ∈ (st.record u v capacity).known := by simp [record]

/-- Unknown positive residuals point in the supplied public direction. -/
theorem Realizes.unknown_positive {G H : WeightedDiGraph V} {st : State V}
    (h : st.Realizes G H) {u v : V} (huv : (u, v) ∉ st.known)
    (hpos : 0 < H.c u v) :
    u ≠ v ∧ v ∈ st.outward u ∧ H.c u v = G.sym.w u v ∧ H.c v u = 0 := by
  have hne : u ≠ v := by
    intro he
    subst v
    simp [H.diag] at hpos
  have hout : v ∈ st.outward u := by
    by_contra hn
    have hz := h.unknown u v huv
    simp only [hn, ↓reduceIte] at hz
    linarith
  have hrev : (v, u) ∉ st.known := fun hm => huv ((h.known_symm u v).mpr hm)
  have hnout : u ∉ st.outward v := (h.direction u v hne).mp hout
  refine ⟨hne, hout, ?_, ?_⟩
  · simpa only [hout, ↓reduceIte] using h.unknown u v huv
  · simpa only [hnout, ↓reduceIte] using h.unknown v u hrev

/-- Recording a returned unknown positive capacity preserves the full invariant. -/
theorem Realizes.record {G H : WeightedDiGraph V} {st : State V}
    (h : st.Realizes G H) {u v : V} {capacity : ℝ}
    (huv : (u, v) ∉ st.known) (hcap : H.c u v = capacity) (hpos : 0 < capacity) :
    (st.record u v capacity).Realizes G H := by
  obtain ⟨hne, _, _, hreverse⟩ := h.unknown_positive huv (by linarith)
  refine ⟨h.singleton, ?_, h.direction, ?_, ?_⟩
  · intro x y
    have hs := h.known_symm x y
    simp only [State.record, mem_insert, Prod.mk.injEq]
    tauto
  · intro x y hknown
    by_cases hf : x = u ∧ y = v
    · obtain ⟨rfl, rfl⟩ := hf
      simpa [State.record] using hcap
    · by_cases hr : x = v ∧ y = u
      · obtain ⟨rfl, rfl⟩ := hr
        simpa [State.record, hne, Ne.symm hne] using hreverse
      · have hold : (x, y) ∈ st.known := by
          simpa only [State.record, mem_insert, Prod.mk.injEq, hf, hr, false_or] using hknown
        simpa only [State.record, hf, hr, ↓reduceIte] using h.learned x y hold
  · intro x y hunknown
    have hold : (x, y) ∉ st.known := fun hm =>
      hunknown (known_subset_record st u v capacity hm)
    exact h.unknown x y hold

omit [Fintype V] in
/-- A known neighbor is reused without changing the capacity table. -/
def learn (st : State V) (u v : V) (capacity : ℝ) : State V :=
  if (u, v) ∈ st.known then st else st.record u v capacity

omit [Fintype V] in
theorem known_subset_learn (st : State V) (u v : V) (capacity : ℝ) :
    st.known ⊆ (st.learn u v capacity).known := by
  unfold learn
  split
  · exact Subset.refl _
  · exact known_subset_record st u v capacity

omit [Fintype V] in
theorem learn_known_forward (st : State V) (u v : V) (capacity : ℝ) :
    (u, v) ∈ (st.learn u v capacity).known := by
  unfold learn
  split_ifs with h
  · exact h
  · exact record_known_forward st u v capacity

theorem Realizes.learn {G H : WeightedDiGraph V} {st : State V}
    (h : st.Realizes G H) {u v : V} {capacity : ℝ}
    (hcap : H.c u v = capacity) (hpos : 0 < capacity) :
    (st.learn u v capacity).Realizes G H := by
  unfold State.learn
  split_ifs with hk
  · exact h
  · exact h.record hk hcap hpos

omit [Fintype V] in
/-- Apply a public signed update to the learned table; discovery is unchanged. -/
def applyFlow (st : State V) (f : V → V → ℝ) : State V :=
  { st with knownResidual := fun u v => st.knownResidual u v - f u v }

/-- A feasible update supported on learned pairs exactly realizes the residual
graph. In particular, no unknown reverse arc can be created by an update. -/
theorem Realizes.applyFlow {G H : WeightedDiGraph V} {st : State V}
    (h : st.Realizes G H) (f : V → V → ℝ) (hf : H.Feasible f)
    (hsupport : ∀ u v, (u, v) ∉ st.known → f u v = 0) :
    (st.applyFlow f).Realizes G (Repair.residual H f hf) := by
  refine ⟨h.singleton, h.known_symm, h.direction, ?_, ?_⟩
  · intro u v huv
    simp only [Repair.residual_c, State.applyFlow, h.learned u v huv]
  · intro u v huv
    simp only [Repair.residual_c, hsupport u v huv, sub_zero]
    exact h.unknown u v huv

/-- All pointwise inputs expected by the residual-search API follow from the
state invariant, for every publicly selected eligible set. -/
theorem Realizes.row {G H : WeightedDiGraph V} {st : State V}
    (h : st.Realizes G H) (u : V) (eligible : Finset V) :
    (∀ v ∈ eligible ∩ st.knownNeighbors u, H.c u v = st.knownResidual u v) ∧
    (∀ v ∈ eligible \ st.knownNeighbors u,
      H.c u v = if v ∈ st.outward u then G.sym.w u v else 0) := by
  constructor
  · intro v hv
    exact h.learned u v ((mem_knownNeighbors st u v).mp (mem_inter.mp hv).2)
  · intro v hv
    exact h.unknown u v (fun hm => (mem_sdiff.mp hv).2
      ((mem_knownNeighbors st u v).mpr hm))

end State

/-- The two extra vertices have wholly public capacities and require no
outgoing-cut queries of the augmented network. -/
abbrev Node (V : Type) := V ⊕ Fin 2

def source : Node V := .inr 0
def sink : Node V := .inr 1

/-- Restriction is used only in correctness proofs, never to inspect hidden data. -/
def internalGraph (H : WeightedDiGraph (Node V)) : WeightedDiGraph V where
  c u v := H.c (.inl u) (.inl v)
  nonneg u v := H.nonneg (.inl u) (.inl v)
  diag u := H.diag (.inl u)

/-- Public learned internal pairs together with explicit heavy terminal arcs. -/
structure NetworkState (V : Type) where
  internal : State V
  terminalResidual : Node V → Node V → ℝ

namespace NetworkState

variable [Fintype V]

structure Realizes (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) : Prop where
  internal : st.internal.Realizes G (internalGraph H)
  fromTerminal : ∀ i y, H.c (.inr i) y = st.terminalResidual (.inr i) y
  toTerminal : ∀ x j, H.c x (.inr j) = st.terminalResidual x (.inr j)

omit [Fintype V] in
/-- Terminal incidences are always known, regardless of their size. -/
def Known (st : NetworkState V) : Node V → Node V → Prop
  | .inl u, .inl v => (u, v) ∈ st.internal.known
  | _, _ => True

omit [Fintype V] in
def knownCapacity (st : NetworkState V) : Node V → Node V → ℝ
  | .inl u, .inl v => st.internal.knownResidual u v
  | x, y => st.terminalResidual x y

theorem Realizes.known {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (h : st.Realizes G H) (x y : Node V) (hxy : st.Known x y) :
    H.c x y = st.knownCapacity x y := by
  cases x with
  | inl u =>
      cases y with
      | inl v => exact h.internal.learned u v hxy
      | inr j => exact h.toTerminal _ j
  | inr i => exact h.fromTerminal i y

theorem Realizes.known_symm {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (h : st.Realizes G H) (x y : Node V) :
    st.Known x y ↔ st.Known y x := by
  cases x <;> cases y
  · exact h.internal.known_symm _ _
  all_goals rfl

omit [Fintype V] in
def learn (st : NetworkState V) (x y : Node V) (capacity : ℝ) : NetworkState V :=
  match x, y with
  | .inl u, .inl v => { st with internal := st.internal.learn u v capacity }
  | _, _ => st

theorem Realizes.learn {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (h : st.Realizes G H) {x y : Node V} {capacity : ℝ}
    (hcap : H.c x y = capacity) (hpos : 0 < capacity) :
    (st.learn x y capacity).Realizes G H := by
  cases x with
  | inl u =>
      cases y with
      | inl v => exact ⟨h.internal.learn hcap hpos, h.fromTerminal, h.toTerminal⟩
      | inr j => exact h
  | inr i => exact h

omit [Fintype V] in
theorem known_learn (st : NetworkState V) (x y : Node V) (capacity : ℝ) :
    (st.learn x y capacity).Known x y := by
  cases x <;> cases y
  · exact State.learn_known_forward _ _ _ _
  all_goals trivial

omit [Fintype V] in
theorem known_mono_learn (st : NetworkState V) (x y : Node V) (capacity : ℝ)
    (a b : Node V) (hab : st.Known a b) : (st.learn x y capacity).Known a b := by
  cases x <;> cases y
  · cases a <;> cases b
    · exact State.known_subset_learn _ _ _ _ hab
    all_goals trivial
  all_goals exact hab

omit [Fintype V] in
/-- Apply a learned-support update to both internal and explicit terminal rows. -/
def applyFlow (st : NetworkState V) (f : Node V → Node V → ℝ) : NetworkState V where
  internal := st.internal.applyFlow fun u v => f (.inl u) (.inl v)
  terminalResidual x y := st.terminalResidual x y - f x y

theorem Realizes.applyFlow {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {st : NetworkState V} (h : st.Realizes G H)
    (f : Node V → Node V → ℝ) (hf : H.Feasible f)
    (hsupport : ∀ x y, ¬st.Known x y → f x y = 0) :
    (st.applyFlow f).Realizes G (Repair.residual H f hf) := by
  have hfi : (internalGraph H).Feasible (fun u v => f (.inl u) (.inl v)) :=
    ⟨fun u v => hf.1 _ _, fun u v => hf.2 _ _⟩
  refine ⟨?_, ?_, ?_⟩
  · exact h.internal.applyFlow _ hfi (fun u v hu => hsupport (.inl u) (.inl v) hu)
  · intro i y
    change H.c (.inr i) y - f (.inr i) y = st.terminalResidual (.inr i) y - f (.inr i) y
    rw [h.fromTerminal]
  · intro x j
    change H.c x (.inr j) - f x (.inr j) = st.terminalResidual x (.inr j) - f x (.inr j)
    rw [h.toTerminal]

end NetworkState

end
end CutQueryComplexity.DirectedUnitST.Blocking

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.State.Realizes.record
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.State.Realizes.learn
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.State.Realizes.applyFlow
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.State.Realizes.row
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.NetworkState.Realizes.learn
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.NetworkState.Realizes.applyFlow
