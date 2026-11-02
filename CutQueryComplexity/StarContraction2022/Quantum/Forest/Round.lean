import CutQueryComplexity.StarContraction2022.Quantum.Forest.State
import CutQueryComplexity.StarContraction2022.Quantum.Forest.Recover
import CutQueryComplexity.StarContraction2022.Certificates.ParallelProgress

/-! # A public component-coloring and residual-recovery forest round

All constructors depend only on the public forest, deleted edges, accuracy,
fresh colors, and returned rows. One returned red-to-blue edge is chosen per
old component. The proofs below verify the actual guarded insertion list.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest
noncomputable section
open Finset ProductPrograms
open CutQueryComplexity.Probability
open scoped Classical ENNReal

variable {n : ℕ}

/-- Identifying exactly two distinct components decreases their count by one.
The proof constructs the bijection after deleting the first old component. -/
theorem componentCount_sup_edge (G : _root_.SimpleGraph (Fin n)) (u v : Fin n)
    (h : ¬G.Reachable u v) :
    Nat.card (G ⊔ _root_.SimpleGraph.edge u v).ConnectedComponent + 1 =
      Nat.card G.ConnectedComponent := by
  let H := G ⊔ _root_.SimpleGraph.edge u v
  let a := G.connectedComponentMk u
  let b := G.connectedComponentMk v
  have hab : a ≠ b := fun he => h (_root_.SimpleGraph.ConnectedComponent.exact he)
  let merge : G.ConnectedComponent → G.ConnectedComponent := fun c => if c = a then b else c
  have huv : u ≠ v := fun he => h (he ▸ _root_.SimpleGraph.Reachable.refl u)
  have hadj (x y : Fin n) (hxy : H.Adj x y) :
      merge (G.connectedComponentMk x) = merge (G.connectedComponentMk y) := by
    rcases hxy with hxy | hxy
    · rw [_root_.SimpleGraph.ConnectedComponent.sound hxy.reachable]
    · obtain ⟨hxy, _⟩ := (_root_.SimpleGraph.edge_adj ..).mp hxy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [merge, a, b]
  have hreach {x y : Fin n} (hr : H.Reachable x y) :
      merge (G.connectedComponentMk x) = merge (G.connectedComponentMk y) := by
    obtain ⟨p⟩ := hr
    induction p with
    | nil => rfl
    | cons he p ih => exact (hadj _ _ he).trans ih
  let f : {c : G.ConnectedComponent // c ≠ a} → H.ConnectedComponent :=
    fun c => _root_.SimpleGraph.ConnectedComponent.map
      (_root_.SimpleGraph.Hom.ofLE (show G ≤ H from le_sup_left)) c.val
  have hinj : Function.Injective f := by
    intro c d he
    obtain ⟨x, hx⟩ := Quot.exists_rep c.val
    obtain ⟨y, hy⟩ := Quot.exists_rep d.val
    change G.connectedComponentMk x = c.val at hx
    change G.connectedComponentMk y = d.val at hy
    have hc : G.connectedComponentMk x ≠ a := hx.symm ▸ c.property
    have hd : G.connectedComponentMk y ≠ a := hy.symm ▸ d.property
    have hh : H.connectedComponentMk x = H.connectedComponentMk y := by
      simpa only [f, ← hx, ← hy, _root_.SimpleGraph.ConnectedComponent.map_mk,
        _root_.SimpleGraph.Hom.ofLE_apply] using he
    have hm := hreach (_root_.SimpleGraph.ConnectedComponent.exact hh)
    simp only [merge, ite_eq_right hc, ite_eq_right hd] at hm
    exact Subtype.ext (hx.symm.trans (hm.trans hy))
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨x, rfl⟩ := Quot.exists_rep c
    by_cases hx : G.connectedComponentMk x = a
    · refine ⟨⟨b, Ne.symm hab⟩, ?_⟩
      change H.connectedComponentMk v = H.connectedComponentMk x
      apply _root_.SimpleGraph.ConnectedComponent.sound
      have hvu : H.Reachable v u :=
        ((_root_.SimpleGraph.edge_adj ..).mpr ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩).reachable.mono
          (show _root_.SimpleGraph.edge u v ≤ H from le_sup_right)
      exact hvu.trans ((_root_.SimpleGraph.ConnectedComponent.exact hx).symm.mono le_sup_left)
    · exact ⟨⟨G.connectedComponentMk x, hx⟩, rfl⟩
  have hc := Fintype.card_of_bijective (f := f) ⟨hinj, hsurj⟩
  have hcard : Fintype.card {c : G.ConnectedComponent // c ≠ a} + 1 =
      Fintype.card G.ConnectedComponent := by
    have hp : 0 < Fintype.card G.ConnectedComponent :=
      Fintype.card_pos_iff.mpr ⟨a⟩
    have hs : Fintype.card {c : G.ConnectedComponent // c = a} = 1 :=
      Fintype.card_subtype_eq a
    rw [Fintype.card_subtype_compl (fun c : G.ConnectedComponent => c = a), hs]
    exact Nat.sub_add_cancel hp
  simpa only [Nat.card_eq_fintype_card, hc, H] using hcard

namespace State

theorem insertEdge_componentCount (F : State n) (u v : Fin n)
    (h : ¬F.graph.Reachable u v) :
    (F.insertEdge u v).componentCount + 1 = F.componentCount := by
  unfold componentCount
  rw [F.insertEdge_graph_of_not_reachable u v h]
  exact componentCount_sup_edge F.graph u v h

/-- Every actual cycle guard succeeds, in the order used by `insertList`. -/
def AllGuards (F : State n) : List (Fin n × Fin n) → Prop
  | [] => True
  | e :: es => ¬F.graph.Reachable e.1 e.2 ∧ (F.insertEdge e.1 e.2).AllGuards es

theorem insertList_counts (F : State n) (es : List (Fin n × Fin n))
    (h : F.AllGuards es) :
    (F.insertList es).val.card = F.val.card + es.length ∧
      (F.insertList es).componentCount + es.length = F.componentCount := by
  induction es generalizing F with
  | nil => simp [insertList]
  | cons e es ih =>
      obtain ⟨hc, htail⟩ := h
      obtain ⟨he, hk⟩ := ih (F.insertEdge e.1 e.2) htail
      have hi := F.insertEdge_card_of_not_reachable e.1 e.2 hc
      have hj := F.insertEdge_componentCount e.1 e.2 hc
      simp only [insertList, List.length_cons]
      constructor <;> omega

theorem insertList_guards_of_closed (F : State n) (es : List (Fin n × Fin n))
    (A : (Fin n × Fin n) → Finset (Fin n))
    (hclosed : ∀ e ∈ es, Certificates.Closed F.graph (A e))
    (hcross : ∀ e ∈ es, e.1 ∈ A e ∧ e.2 ∉ A e)
    (havoid : es.Pairwise (fun e f => e.1 ∉ A f ∧ e.2 ∉ A f)) :
    F.AllGuards es := by
  induction es generalizing F with
  | nil => trivial
  | cons e es ih =>
      have hx := hcross e (by simp)
      have hn := (hclosed e (by simp)).not_reachable hx.1 hx.2
      refine ⟨hn, ?_⟩
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp havoid
      apply ih (F.insertEdge e.1 e.2) ?_
        (fun f hf => hcross f (by simp [hf])) htail
      intro f hf
      rw [F.insertEdge_graph_of_not_reachable e.1 e.2 hn]
      exact (hclosed f (by simp [hf])).sup_edge (hhead f hf).1 (hhead f hf).2

theorem insertList_guards_of_star (F : State n) (color : Fin n → Bool)
    (es : List (Fin n × Fin n))
    (hcolor : ∀ u v, F.graph.Reachable u v → color u = color v)
    (hdir : ∀ e ∈ es, color e.1 = true ∧ color e.2 = false)
    (hsep : es.Pairwise (fun e f => ¬F.graph.Reachable e.1 f.1)) :
    F.AllGuards es := by
  let A : (Fin n × Fin n) → Finset (Fin n) := fun e => F.component e.1
  have ht (e f : Fin n × Fin n) (he : e ∈ es) (hf : f ∈ es) : e.2 ∉ A f := by
    intro hm
    have hh := hcolor _ _ ((F.mem_component _ _).mp hm)
    rw [(hdir f hf).1, (hdir e he).2] at hh
    cases hh
  apply F.insertList_guards_of_closed es A
    (fun e _ => Certificates.forestBlock_closed F.graph e.1)
    (fun e he => ⟨by simp [A], ht e e he he⟩)
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have he := List.getElem_mem hi
  have hf := List.getElem_mem hj
  have hd := List.pairwise_iff_getElem.mp hsep i j hi hj hij
  refine ⟨?_, ht _ _ he hf⟩
  exact fun hm => hd ((F.mem_component _ _).mp hm).symm

end State

abbrev ColorTape (n : ℕ) := Finset (Fin n) → Bool

def redVertices (F : State n) (tape : ColorTape n) : Finset (Fin n) :=
  univ.filter fun u => Certificates.componentColor F.graph tape u = true

def blueVertices (F : State n) (tape : ColorTape n) : Finset (Fin n) :=
  univ.filter fun u => Certificates.componentColor F.graph tape u = false

@[simp] theorem mem_redVertices (F : State n) (tape : ColorTape n) (u : Fin n) :
    u ∈ redVertices F tape ↔ Certificates.componentColor F.graph tape u = true := by
  simp [redVertices]

@[simp] theorem mem_blueVertices (F : State n) (tape : ColorTape n) (u : Fin n) :
    u ∈ blueVertices F tape ↔ Certificates.componentColor F.graph tape u = false := by
  simp [blueVertices]

theorem red_blue_disjoint (F : State n) (tape : ColorTape n) :
    Disjoint (redVertices F tape) (blueVertices F tape) := by
  apply Finset.disjoint_left.mpr
  intro u hr hb
  simp only [mem_redVertices, mem_blueVertices] at hr hb
  rw [hr] at hb
  cases hb

/-- Public successful component labels. The hidden graph is not consulted. -/
def recoveredComponents (F : State n) (tape : ColorTape n) (rows : RowTable n) :
    Finset F.graph.ConnectedComponent :=
  univ.filter fun c => ∃ e : Fin n × Fin n,
    F.graph.connectedComponentMk e.1 = c ∧
    e.1 ∈ redVertices F tape ∧ e.2 ∈ blueVertices F tape ∧ rows e.1 = some e.2

def recoveredEdge (F : State n) (tape : ColorTape n) (rows : RowTable n)
    (c : recoveredComponents F tape rows) : Fin n × Fin n :=
  Classical.choose ((mem_filter.mp c.property).2)

theorem recoveredEdge_spec (F : State n) (tape : ColorTape n) (rows : RowTable n)
    (c : recoveredComponents F tape rows) :
    F.graph.connectedComponentMk (recoveredEdge F tape rows c).1 = c.val ∧
      (recoveredEdge F tape rows c).1 ∈ redVertices F tape ∧
      (recoveredEdge F tape rows c).2 ∈ blueVertices F tape ∧
      rows (recoveredEdge F tape rows c).1 = some (recoveredEdge F tape rows c).2 :=
  Classical.choose_spec ((mem_filter.mp c.property).2)

def recoveredEdges (F : State n) (tape : ColorTape n) (rows : RowTable n) :
    List (Fin n × Fin n) :=
  (univ.toList : List (recoveredComponents F tape rows)).map (recoveredEdge F tape rows)

theorem recoveredEdges_length (F : State n) (tape : ColorTape n) (rows : RowTable n) :
    (recoveredEdges F tape rows).length = (recoveredComponents F tape rows).card := by
  simp [recoveredEdges]

theorem recoveredEdges_separate (F : State n) (tape : ColorTape n) (rows : RowTable n) :
    (recoveredEdges F tape rows).Pairwise (fun e f => ¬F.graph.Reachable e.1 f.1) := by
  unfold recoveredEdges
  rw [List.pairwise_map]
  apply (Finset.nodup_toList (univ : Finset (recoveredComponents F tape rows))).pairwise_of_forall_ne
  intro c hc d hd hne hr
  apply hne
  apply Subtype.ext
  rw [← (recoveredEdge_spec F tape rows c).1, ← (recoveredEdge_spec F tape rows d).1]
  exact _root_.SimpleGraph.ConnectedComponent.sound hr

theorem recoveredEdges_guards (F : State n) (tape : ColorTape n) (rows : RowTable n) :
    F.AllGuards (recoveredEdges F tape rows) := by
  apply F.insertList_guards_of_star (Certificates.componentColor F.graph tape) _
    (fun _ _ h => Certificates.componentColor_constant F.graph tape h) ?_
    (recoveredEdges_separate F tape rows)
  intro e he
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  exact ⟨(mem_redVertices ..).mp (recoveredEdge_spec F tape rows c).2.1,
    (mem_blueVertices ..).mp (recoveredEdge_spec F tape rows c).2.2.1⟩

def roundUpdate (F : State n) (tape : ColorTape n) (rows : RowTable n) : State n :=
  F.insertList (recoveredEdges F tape rows)

theorem roundUpdate_counts (F : State n) (tape : ColorTape n) (rows : RowTable n) :
    (roundUpdate F tape rows).val.card = F.val.card + (recoveredComponents F tape rows).card ∧
      (roundUpdate F tape rows).componentCount + (recoveredComponents F tape rows).card =
        F.componentCount := by
  simpa only [roundUpdate, recoveredEdges_length] using
    F.insertList_counts _ (recoveredEdges_guards F tape rows)

/-- The actual round samples fresh component colors and executes recovery once. -/
def forestRound (F : State n) (E : LearnedEdges n) (eta : ℝ) :
    ProductTree n (State n) (recoverBudget n eta) :=
  RTree.mix ((Certificates.componentBits (Q := Fin n)).map fun tape =>
    RTree.map (roundUpdate F tape)
      (recoverRows n E (redVertices F tape) (blueVertices F tape) eta))

theorem forestRound_eval (F : State n) (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (forestRound F E eta).eval read =
      (Certificates.componentBits (Q := Fin n)).bind fun tape =>
        ((recoverRows n E (redVertices F tape) (blueVertices F tape) eta).eval read).map
          (roundUpdate F tape) := by
  simp only [forestRound, RTree.eval_mix, PMF.bind_map, RTree.eval_map, Function.comp_def]

theorem forestRound_cost (F : State n) (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → ProductAnswer n 1) {out : State n × ℕ}
    (h : out ∈ (RTree.run read (forestRound F E eta)).support) :
    out.2 ≤ recoverBudget n eta := RTree.cost_le _ read h

/-- The accepted capacity residual is exactly the edge-set residual used by
the public forest invariant and deficit. -/
theorem residualNeighbor_iff_mem (G : CapacityGraph (Fin n) 1) (E : LearnedEdges n)
    (u v : Fin n) :
    ResidualNeighbor G E u v ↔ s(u, v) ∈ G.toWeighted.support.edgeFinset \ E := by
  simp only [ResidualNeighbor, mem_sdiff, _root_.SimpleGraph.mem_edgeFinset,
    _root_.SimpleGraph.mem_edgeSet]
  have hw := (G.w u v).isLt
  change ((G.w u v : ℕ) = 1 ∧ _) ↔ (((G.w u v : ℕ) : ℝ) ≠ 0 ∧ _)
  have he : (G.w u v : ℕ) = 1 ↔ ((G.w u v : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  exact and_congr_left (fun _ => he)

theorem roundUpdate_residualSound (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) (tape : ColorTape n) {rows : RowTable n}
    (hr : rows ∈ ((recoverRows n E (redVertices F tape) (blueVertices F tape) eta).eval
      (productRead G)).support) :
    (roundUpdate F tape rows).ResidualSound G.toWeighted.support E := by
  apply F.insertList_residualSound G.toWeighted.support E hF
  intro e he
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  have hs := recoveredEdge_spec F tape rows c
  exact (residualNeighbor_iff_mem G E _ _).mp
    (recoverRows_sound G E hE _ _ eta hr hs.2.2.2).2.2

theorem roundUpdate_deficit (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) (tape : ColorTape n) {rows : RowTable n}
    (hr : rows ∈ ((recoverRows n E (redVertices F tape) (blueVertices F tape) eta).eval
      (productRead G)).support) :
    (roundUpdate F tape rows).deficit G.toWeighted.support E +
      (recoveredComponents F tape rows).card = F.deficit G.toWeighted.support E := by
  have hnext := roundUpdate_residualSound F G E eta hE hF tape hr
  have hbefore := F.deficit_add_residual_components G.toWeighted.support E hF
  have hafter := (roundUpdate F tape rows).deficit_add_residual_components
    G.toWeighted.support E hnext
  have hc := (roundUpdate_counts F tape rows).2
  omega

theorem forestRound_residualSound (F : State n) (G : CapacityGraph (Fin n) 1)
    (E : LearnedEdges n) (eta : ℝ) (hE : KnownSubgraph E G)
    (hF : F.ResidualSound G.toWeighted.support E) {H : State n}
    (hH : H ∈ ((forestRound F E eta).eval (productRead G)).support) :
    H.ResidualSound G.toWeighted.support E := by
  rw [forestRound_eval] at hH
  obtain ⟨tape, ht, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hH
  obtain ⟨rows, hrows, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  exact roundUpdate_residualSound F G E eta hE hF tape hrows

/-- The single public program precedes every hidden input and every reply
function. No query cap or correct-update property is an input premise. -/
theorem forestRound_public (F : State n) (E : LearnedEdges n) (eta : ℝ) :
    ∃ T : ProductTree n (State n) (recoverBudget n eta),
      (∀ read out, out ∈ (RTree.run read T).support → out.2 ≤ recoverBudget n eta) ∧
      ∀ G : CapacityGraph (Fin n) 1, KnownSubgraph E G →
        F.ResidualSound G.toWeighted.support E →
        ∀ H ∈ (T.eval (productRead G)).support, H.ResidualSound G.toWeighted.support E := by
  exact ⟨forestRound F E eta, fun read _ h => forestRound_cost F E eta read h,
    fun G hE hF _ hH => forestRound_residualSound F G E eta hE hF hH⟩

open QuantumQueryComplexity
open scoped Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

theorem forestRound_physical_length (F : State n) (E : LearnedEdges n) (eta : ℝ) :
    (productTreeRoutine (forestRound F E eta)).len =
      12 * productBits n 1 * recoverBudget n eta := rfl

theorem forestRound_physical_normalized (F : State n) (E : LearnedEdges n) (eta : ℝ)
    (read : Finset (Fin n) → CutAnswer n 1) :
    IsQState ((productTreeRoutine (forestRound F E eta)).run read *ᵥ
      (productTreeAlg (forestRound F E eta)).init) := productTreeRoutine_isQState _ read

theorem forestRound_physical_prob (F : State n) (E : LearnedEdges n) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (H : State n) :
    (productTreeAlg (forestRound F E eta)).prob (capacityRead G)
      (physicalQueries n (recoverBudget n eta)) H =
      (((Certificates.componentBits (Q := Fin n)).bind fun tape =>
        ((recoverRows n E (redVertices F tape) (blueVertices F tape) eta).eval (productRead G)).map
          (roundUpdate F tape)) H).toReal := by
  rw [productTreeAlg_prob]
  change (((forestRound F E eta).eval (productRead G)) H).toReal = _
  rw [forestRound_eval]

#print axioms componentCount_sup_edge
#print axioms State.insertList_counts
#print axioms State.insertList_guards_of_star
#print axioms recoveredEdges_guards
#print axioms roundUpdate_counts
#print axioms forestRound_eval
#print axioms forestRound_cost
#print axioms residualNeighbor_iff_mem
#print axioms roundUpdate_residualSound
#print axioms roundUpdate_deficit
#print axioms forestRound_residualSound
#print axioms forestRound_public
#print axioms forestRound_physical_length
#print axioms forestRound_physical_normalized
#print axioms forestRound_physical_prob

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
