import CutQueryComplexity.Graph.ForestFacts
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! # Public finite residual-forest state

The state is a finite set of unoriented original edges with a public forest
invariant. Guarded insertion is total for every proposed endpoint pair and
keeps this invariant without consulting the hidden graph. Hidden residual
edge membership appears only in the correctness lemmas. Components and
representatives are computed from the public state.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest

noncomputable section
open Finset
open scoped Classical

abbrev Edges (n : ℕ) := Finset (Sym2 (Fin n))

def edgeGraph {n : ℕ} (E : Edges n) : _root_.SimpleGraph (Fin n) :=
  _root_.SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))

def Loopless {n : ℕ} (E : Edges n) : Prop := ∀ v : Fin n, s(v, v) ∉ E

variable {n : ℕ}

@[simp] theorem edgeGraph_adj (E : Edges n) (u v : Fin n) :
    (edgeGraph E).Adj u v ↔ s(u, v) ∈ E ∧ u ≠ v := Iff.rfl

@[simp] theorem edgeGraph_empty : edgeGraph (∅ : Edges n) = ⊥ := by
  ext u v
  simp

/-- Opposite orientations name one original unit edge. -/
theorem edge_swap (u v : Fin n) : (s(u, v) : Sym2 (Fin n)) = s(v, u) := Sym2.eq_swap

theorem edgeGraph_insert (E : Edges n) (u v : Fin n) :
    edgeGraph (insert s(u, v) E) = edgeGraph E ⊔ _root_.SimpleGraph.edge u v := by
  ext a b
  simp only [edgeGraph_adj, mem_insert, _root_.SimpleGraph.sup_adj,
    _root_.SimpleGraph.edge_adj, Sym2.eq_iff]
  tauto

theorem edgeGraph_mono {E F : Edges n} (h : E ⊆ F) : edgeGraph E ≤ edgeGraph F := by
  intro u v huv
  exact ⟨h huv.1, huv.2⟩

/-- Loopless finite edge data are recovered exactly, not merely up to support. -/
theorem edgeFinset_edgeGraph (E : Edges n) (hE : Loopless E) :
    (edgeGraph E).edgeFinset = E := by
  ext e
  refine Sym2.ind (fun u v => ?_) e
  simp only [_root_.SimpleGraph.mem_edgeFinset, _root_.SimpleGraph.mem_edgeSet,
    edgeGraph_adj]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    intro he
    subst v
    exact hE u h

theorem loopless_edgeFinset (G : _root_.SimpleGraph (Fin n)) : Loopless G.edgeFinset := by
  intro v hv
  have h : G.Adj v v := by simpa only [_root_.SimpleGraph.mem_edgeFinset,
    _root_.SimpleGraph.mem_edgeSet] using hv
  exact (G.ne_of_adj h) rfl

theorem edgeGraph_edgeFinset (G : _root_.SimpleGraph (Fin n)) :
    edgeGraph G.edgeFinset = G := by
  simp only [edgeGraph, _root_.SimpleGraph.coe_edgeFinset, _root_.SimpleGraph.fromEdgeSet_edgeSet]

/-- Finite public data; the invariant contains no hidden graph. -/
abbrev State (n : ℕ) := {E : Edges n // Loopless E ∧ (edgeGraph E).IsAcyclic}

instance stateFintype (n : ℕ) : Fintype (State n) := Fintype.ofFinite _

namespace State

def graph (F : State n) : _root_.SimpleGraph (Fin n) := edgeGraph F.val

def empty (n : ℕ) : State n :=
  ⟨∅, by simp [Loopless], by simpa using (_root_.SimpleGraph.isAcyclic_bot (V := Fin n))⟩

theorem acyclic (F : State n) : F.graph.IsAcyclic := F.property.2

theorem loopless (F : State n) : Loopless F.val := F.property.1

@[simp] theorem edgeFinset_graph (F : State n) : F.graph.edgeFinset = F.val :=
  edgeFinset_edgeGraph F.val F.loopless

theorem card_le (F : State n) : F.val.card ≤ n - 1 := by
  rw [← F.edgeFinset_graph]
  simpa only [Fintype.card_fin] using forest_card_le F.graph F.acyclic

private theorem loopless_insert (F : State n) (u v : Fin n)
    (hn : ¬F.graph.Reachable u v) : Loopless (insert s(u, v) F.val) := by
  have huv : u ≠ v := by
    intro he
    subst v
    exact hn .rfl
  intro a ha
  rcases mem_insert.mp ha with he | he
  · rcases Sym2.eq_iff.mp he with h | h
    · exact huv (h.1.symm.trans h.2)
    · exact huv (h.2.symm.trans h.1)
  · exact F.loopless a he

/-- The reachability test is entirely on the learned state. A loop, duplicate
edge, or cycle-closing edge is rejected for every answer transcript. -/
def insertEdge (F : State n) (u v : Fin n) : State n :=
  if h : ¬F.graph.Reachable u v then
    ⟨insert s(u, v) F.val, loopless_insert F u v h, by
      rw [edgeGraph_insert]
      exact F.acyclic.sup_edge_of_not_reachable h⟩
  else F

theorem insertEdge_edges_of_not_reachable (F : State n) (u v : Fin n)
    (h : ¬F.graph.Reachable u v) : (F.insertEdge u v).val = insert s(u, v) F.val := by
  simp only [insertEdge, dif_pos h]

theorem insertEdge_of_reachable (F : State n) (u v : Fin n)
    (h : F.graph.Reachable u v) : F.insertEdge u v = F := by
  simp only [insertEdge, dif_neg (not_not.mpr h)]

@[simp] theorem insertEdge_loop (F : State n) (u : Fin n) : F.insertEdge u u = F :=
  F.insertEdge_of_reachable u u .rfl

theorem insertEdge_swap (F : State n) (u v : Fin n) : F.insertEdge u v = F.insertEdge v u := by
  have he : F.graph.Reachable u v ↔ F.graph.Reachable v u := ⟨fun h => h.symm, fun h => h.symm⟩
  apply Subtype.ext
  by_cases h : F.graph.Reachable u v
  · rw [F.insertEdge_of_reachable u v h, F.insertEdge_of_reachable v u (he.mp h)]
  · rw [F.insertEdge_edges_of_not_reachable u v h,
      F.insertEdge_edges_of_not_reachable v u (fun hh => h (he.mpr hh)), edge_swap]

theorem subset_insertEdge (F : State n) (u v : Fin n) : F.val ⊆ (F.insertEdge u v).val := by
  by_cases h : F.graph.Reachable u v
  · simpa only [F.insertEdge_of_reachable u v h] using (subset_rfl : F.val ⊆ F.val)
  · rw [F.insertEdge_edges_of_not_reachable u v h]
    exact subset_insert _ _

theorem insertEdge_subset (F : State n) (u v : Fin n) :
    (F.insertEdge u v).val ⊆ insert s(u, v) F.val := by
  by_cases h : F.graph.Reachable u v
  · rw [F.insertEdge_of_reachable u v h]
    exact subset_insert _ _
  · simpa only [F.insertEdge_edges_of_not_reachable u v h] using
      (subset_rfl : insert s(u, v) F.val ⊆ insert s(u, v) F.val)

theorem graph_le_insertEdge (F : State n) (u v : Fin n) : F.graph ≤ (F.insertEdge u v).graph :=
  edgeGraph_mono (F.subset_insertEdge u v)

theorem insertEdge_graph_of_not_reachable (F : State n) (u v : Fin n)
    (h : ¬F.graph.Reachable u v) :
    (F.insertEdge u v).graph = F.graph ⊔ _root_.SimpleGraph.edge u v := by
  change edgeGraph (F.insertEdge u v).val = _
  rw [F.insertEdge_edges_of_not_reachable u v h, edgeGraph_insert]
  rfl

theorem insertEdge_card_of_not_reachable (F : State n) (u v : Fin n)
    (h : ¬F.graph.Reachable u v) : (F.insertEdge u v).val.card = F.val.card + 1 := by
  rw [F.insertEdge_edges_of_not_reachable u v h]
  apply card_insert_of_notMem
  intro he
  have huv : u ≠ v := by
    intro hh
    subst v
    exact h .rfl
  exact h ((show F.graph.Adj u v from ⟨he, huv⟩).reachable)

theorem insertEdge_card_le (F : State n) (u v : Fin n) :
    (F.insertEdge u v).val.card ≤ F.val.card + 1 :=
  (card_le_card (F.insertEdge_subset u v)).trans (card_insert_le _ _)

/-- Sequential folding only performs public cycle tests. The future round
will prove all selected red-to-blue edges pass those tests. -/
def insertList (F : State n) : List (Fin n × Fin n) → State n
  | [] => F
  | e :: es => (F.insertEdge e.1 e.2).insertList es

theorem subset_insertList (F : State n) (es : List (Fin n × Fin n)) :
    F.val ⊆ (F.insertList es).val := by
  induction es generalizing F with
  | nil => exact subset_rfl
  | cons e es ih => exact (F.subset_insertEdge e.1 e.2).trans (ih _)

theorem insertList_card_le (F : State n) (es : List (Fin n × Fin n)) :
    (F.insertList es).val.card ≤ F.val.card + es.length := by
  induction es generalizing F with
  | nil => simp [insertList]
  | cons e es ih =>
      have h := ih (F.insertEdge e.1 e.2)
      have he := F.insertEdge_card_le e.1 e.2
      change ((F.insertEdge e.1 e.2).insertList es).val.card ≤ _
      simp only [List.length_cons]
      omega

/-- Proof-side residual inclusion uses the actual original unoriented edges. -/
def ResidualSound (F : State n) (G : _root_.SimpleGraph (Fin n)) (deleted : Edges n) : Prop :=
  F.val ⊆ G.edgeFinset \ deleted

theorem empty_residualSound (G : _root_.SimpleGraph (Fin n)) (deleted : Edges n) :
    (empty n).ResidualSound G deleted := by simp [ResidualSound, empty]

theorem insertEdge_residualSound (F : State n) (G : _root_.SimpleGraph (Fin n))
    (deleted : Edges n) (hF : F.ResidualSound G deleted) (u v : Fin n)
    (he : s(u, v) ∈ G.edgeFinset \ deleted) :
    (F.insertEdge u v).ResidualSound G deleted := by
  exact (F.insertEdge_subset u v).trans (insert_subset he hF)

theorem insertList_residualSound (F : State n) (G : _root_.SimpleGraph (Fin n))
    (deleted : Edges n) (hF : F.ResidualSound G deleted) (es : List (Fin n × Fin n))
    (he : ∀ e ∈ es, s(e.1, e.2) ∈ G.edgeFinset \ deleted) :
    (F.insertList es).ResidualSound G deleted := by
  induction es generalizing F with
  | nil => exact hF
  | cons e es ih =>
      exact ih (F.insertEdge e.1 e.2)
        (F.insertEdge_residualSound G deleted hF e.1 e.2 (he e (by simp)))
        (fun f hf => he f (by simp [hf]))

theorem residualSound_subgraph (F : State n) (G : _root_.SimpleGraph (Fin n))
    (deleted : Edges n) (hF : F.ResidualSound G deleted) :
    F.graph ≤ edgeGraph (G.edgeFinset \ deleted) := edgeGraph_mono hF

def component (F : State n) (v : Fin n) : Finset (Fin n) := forestBlock F.graph v

@[simp] theorem mem_component (F : State n) (u v : Fin n) :
    v ∈ F.component u ↔ F.graph.Reachable u v := mem_forestBlock F.graph u v

theorem component_nonempty (F : State n) (v : Fin n) : (F.component v).Nonempty :=
  ⟨v, root_mem_forestBlock F.graph v⟩

def representative (F : State n) (v : Fin n) : Fin n :=
  (F.component v).min' (F.component_nonempty v)

theorem representative_mem (F : State n) (v : Fin n) : F.representative v ∈ F.component v :=
  min'_mem _ _

theorem component_eq_iff (F : State n) (u v : Fin n) :
    F.component u = F.component v ↔ F.graph.Reachable u v := by
  constructor
  · intro h
    have hv : v ∈ F.component u := by rw [h]; exact root_mem_forestBlock F.graph v
    exact (F.mem_component u v).mp hv
  · intro h
    ext w
    simp only [mem_component]
    exact ⟨fun hw => h.symm.trans hw, fun hw => h.trans hw⟩

theorem representative_eq_iff (F : State n) (u v : Fin n) :
    F.representative u = F.representative v ↔ F.graph.Reachable u v := by
  constructor
  · intro h
    have hu := (F.mem_component u _).mp (F.representative_mem u)
    have hv := (F.mem_component v _).mp (F.representative_mem v)
    rw [h] at hu
    exact hu.trans hv.symm
  · intro h
    have he := (F.component_eq_iff u v).mpr h
    unfold representative
    simp only [he]

def componentCount (F : State n) : ℕ := Nat.card F.graph.ConnectedComponent

theorem componentCount_le (F : State n) : F.componentCount ≤ n := by
  have h := Nat.card_le_card_of_surjective F.graph.connectedComponentMk
    (fun C => Quot.exists_rep C)
  simpa only [componentCount, Nat.card_fin] using h

theorem componentCount_mono {F H : State n} (h : F.graph ≤ H.graph) :
    H.componentCount ≤ F.componentCount :=
  _root_.SimpleGraph.ConnectedComponent.card_le_card_of_le h

/-- Actual component deficit relative to the hidden residual graph. It is
used only in proofs; public state updates do not evaluate this quantity. -/
def deficit (F : State n) (G : _root_.SimpleGraph (Fin n)) (deleted : Edges n) : ℕ :=
  F.componentCount - Nat.card (edgeGraph (G.edgeFinset \ deleted)).ConnectedComponent

theorem deficit_le (F : State n) (G : _root_.SimpleGraph (Fin n)) (deleted : Edges n) :
    F.deficit G deleted ≤ n := (Nat.sub_le _ _).trans F.componentCount_le

theorem deficit_add_residual_components (F : State n) (G : _root_.SimpleGraph (Fin n))
    (deleted : Edges n) (hF : F.ResidualSound G deleted) :
    F.deficit G deleted + Nat.card (edgeGraph (G.edgeFinset \ deleted)).ConnectedComponent =
      F.componentCount := by
  exact Nat.sub_add_cancel
    (_root_.SimpleGraph.ConnectedComponent.card_le_card_of_le (F.residualSound_subgraph G deleted hF))

/-- Equality of actual finite component counts under inclusion is exactly
spanning. The proof uses the surjective component map, rather than an assumed
component-count specification. -/
theorem component_card_eq_iff (F : State n) (R : _root_.SimpleGraph (Fin n))
    (hFR : F.graph ≤ R) :
    Nat.card F.graph.ConnectedComponent = Nat.card R.ConnectedComponent ↔
      ∀ u v, R.Reachable u v → F.graph.Reachable u v := by
  let f : F.graph.ConnectedComponent → R.ConnectedComponent :=
    _root_.SimpleGraph.ConnectedComponent.map (_root_.SimpleGraph.Hom.ofLE hFR)
  have hsurj : Function.Surjective f :=
    _root_.SimpleGraph.ConnectedComponent.surjective_map_ofLE hFR
  constructor
  · intro hc
    have hc' : Fintype.card F.graph.ConnectedComponent = Fintype.card R.ConnectedComponent := by
      simpa only [Nat.card_eq_fintype_card] using hc
    have hinj := ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hc'⟩).1
    intro u v huv
    apply _root_.SimpleGraph.ConnectedComponent.exact
    apply hinj
    change R.connectedComponentMk u = R.connectedComponentMk v
    exact _root_.SimpleGraph.ConnectedComponent.sound huv
  · intro hspan
    apply Nat.card_eq_of_bijective f
    refine ⟨?_, hsurj⟩
    intro A B he
    obtain ⟨u, rfl⟩ := Quot.exists_rep A
    obtain ⟨v, rfl⟩ := Quot.exists_rep B
    change R.connectedComponentMk u = R.connectedComponentMk v at he
    exact _root_.SimpleGraph.ConnectedComponent.sound
      (hspan u v (_root_.SimpleGraph.ConnectedComponent.exact he))

theorem deficit_zero_iff_spans (F : State n) (G : _root_.SimpleGraph (Fin n))
    (deleted : Edges n) (hF : F.ResidualSound G deleted) :
    F.deficit G deleted = 0 ↔ ∀ u v,
      (edgeGraph (G.edgeFinset \ deleted)).Reachable u v → F.graph.Reachable u v := by
  have hsub := F.residualSound_subgraph G deleted hF
  have hc := _root_.SimpleGraph.ConnectedComponent.card_le_card_of_le hsub
  rw [← F.component_card_eq_iff _ hsub]
  change F.componentCount - Nat.card (edgeGraph (G.edgeFinset \ deleted)).ConnectedComponent = 0 ↔ _
  rw [Nat.sub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm h hc, fun h => h.le⟩

/-- The existing graph-theoretic spanning-forest semantics is reached when
the real component deficit vanishes. No query/progress hypothesis is used. -/
theorem spanningForest_of_deficit_zero (F : State n) (G : _root_.SimpleGraph (Fin n))
    (deleted : Edges n) (hF : F.ResidualSound G deleted) (hz : F.deficit G deleted = 0) :
    IsSpanningForest (SimpleGraph.toWeighted (edgeGraph (G.edgeFinset \ deleted))) F.graph := by
  refine ⟨?_, F.acyclic, ?_⟩
  · simpa only [support_toWeighted] using F.residualSound_subgraph G deleted hF
  · simpa only [support_toWeighted] using (F.deficit_zero_iff_spans G deleted hF).mp hz

end State

#print axioms edge_swap
#print axioms edgeGraph_insert
#print axioms edgeFinset_edgeGraph
#print axioms edgeGraph_edgeFinset
#print axioms State.acyclic
#print axioms State.card_le
#print axioms State.insertEdge_swap
#print axioms State.subset_insertEdge
#print axioms State.insertEdge_card_of_not_reachable
#print axioms State.insertList_card_le
#print axioms State.insertEdge_residualSound
#print axioms State.insertList_residualSound
#print axioms State.residualSound_subgraph
#print axioms State.representative_eq_iff
#print axioms State.componentCount_le
#print axioms State.componentCount_mono
#print axioms State.deficit_le
#print axioms State.deficit_add_residual_components
#print axioms State.component_card_eq_iff
#print axioms State.deficit_zero_iff_spans
#print axioms State.spanningForest_of_deficit_zero

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
