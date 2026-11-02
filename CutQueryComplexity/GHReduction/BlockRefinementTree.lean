import CutQueryComplexity.GHReduction.BlockRefinement
import CutQueryComplexity.GHReduction.PartialTree
import CutQueryComplexity.MinCut.SpanTree

/-! # Public tree topology after splitting one block

The explicit edge family retains each old edge. An endpoint at the split
block is reattached to a publicly selected child or the residual block. One
additional edge joins each child to the residual. This edge family is
connected and has exactly one fewer edge than the number of new labels. A
public BFS supplies a rooted tree on those same labels. The result below
locates each selected parent edge in the family; it does not state the
converse assertion that every family edge is selected.

No capacity is used to construct or delete an edge. Cut-witness preservation
for the new child edges and execution-level invariants are separate from this
topological construction.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {B ι : Type} [Fintype B] [DecidableEq B] [DecidableEq ι]

/-- A fixed representative of each old block among the refined labels. -/
def refinementRepresentative (b : B) (I : Finset ι) (x : B) : RefinedBlock b I :=
  if hx : x = b then Sum.inr none
  else Sum.inl ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩⟩

/-- Move only the endpoint at `b`; `a y` is its public attachment when the
other endpoint is `y`. -/
def refinedEndpoint (b : B) (I : Finset ι) (a : B → Option I) (x y : B) :
    RefinedBlock b I :=
  if hx : x = b then Sum.inr (a y)
  else Sum.inl ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩⟩

theorem refinedBlockParent_endpoint (b : B) (I : Finset ι) (a : B → Option I)
    (x y : B) : refinedBlockParent b I (refinedEndpoint b I a x y) = x := by
  by_cases hx : x = b <;> simp [refinedEndpoint, refinedBlockParent, hx]

def refinedOldEdge (T : RootedTree B) (b : B) (I : Finset ι) (a : B → Option I)
    (e : B) : RefinedBlock b I × RefinedBlock b I :=
  (refinedEndpoint b I a e (T.parent e), refinedEndpoint b I a (T.parent e) e)

def refinedStarEdge (b : B) (I : Finset ι) (i : I) :
    RefinedBlock b I × RefinedBlock b I := (Sum.inr (some i), Sum.inr none)

def refinedEdges (T : RootedTree B) (b : B) (I : Finset ι) (a : B → Option I) :
    Finset (RefinedBlock b I × RefinedBlock b I) :=
  (Finset.univ.erase T.root).image (refinedOldEdge T b I a) ∪
    I.attach.image (refinedStarEdge b I)

theorem refinedOldEdge_mem (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) {e : B} (he : e ≠ T.root) :
    refinedOldEdge T b I a e ∈ refinedEdges T b I a := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨e, Finset.mem_erase.mpr ⟨he, Finset.mem_univ _⟩, rfl⟩

theorem refinedStarEdge_mem (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) (i : I) : refinedStarEdge b I i ∈ refinedEdges T b I a := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_attach _ _, rfl⟩

theorem refinedOldEdge_injective (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) : Function.Injective (refinedOldEdge T b I a) := by
  intro x y h
  have hc := congrArg
    (fun e : RefinedBlock b I × RefinedBlock b I => refinedBlockParent b I e.1) h
  simpa only [refinedOldEdge, refinedBlockParent_endpoint] using hc

theorem refinedStarEdge_injective (b : B) (I : Finset ι) :
    Function.Injective (refinedStarEdge b I) := by
  intro i j h
  have hc := congrArg (fun e : RefinedBlock b I × RefinedBlock b I => e.1) h
  simpa [refinedStarEdge] using hc

theorem refinedOldEdge_ne_star (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) {e : B} (he : e ≠ T.root) (i : I) :
    refinedOldEdge T b I a e ≠ refinedStarEdge b I i := by
  intro h
  have hfirst : e = b := by
    have hc := congrArg
      (fun d : RefinedBlock b I × RefinedBlock b I => refinedBlockParent b I d.1) h
    change refinedBlockParent b I (refinedEndpoint b I a e (T.parent e)) = b at hc
    exact (refinedBlockParent_endpoint b I a e (T.parent e)).symm.trans hc
  have hsecond : T.parent e = b := by
    have hc := congrArg
      (fun d : RefinedBlock b I × RefinedBlock b I => refinedBlockParent b I d.2) h
    change refinedBlockParent b I (refinedEndpoint b I a (T.parent e) e) = b at hc
    exact (refinedBlockParent_endpoint b I a (T.parent e) e).symm.trans hc
  have hcycle : T.parent e = e := hsecond.trans hfirst.symm
  have hd := T.depth_parent e he
  rw [hcycle] at hd
  omega

theorem refinedEdge_parts_disjoint (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) :
    Disjoint ((Finset.univ.erase T.root).image (refinedOldEdge T b I a))
      (I.attach.image (refinedStarEdge b I)) := by
  apply Finset.disjoint_left.mpr
  intro d hdOld hdStar
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hdOld
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hdStar
  exact refinedOldEdge_ne_star T b I a (Finset.mem_erase.mp he).1 i hi.symm

theorem refinedEdges_card (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) :
    (refinedEdges T b I a).card = Fintype.card B - 1 + I.card := by
  rw [refinedEdges, Finset.card_union_of_disjoint (refinedEdge_parts_disjoint T b I a),
    Finset.card_image_of_injective _ (refinedOldEdge_injective T b I a),
    Finset.card_image_of_injective _ (refinedStarEdge_injective b I)]
  simp

theorem refinedEdges_card_eq_vertices_sub_one (T : RootedTree B) (b : B)
    (I : Finset ι) (a : B → Option I) :
    (refinedEdges T b I a).card = Fintype.card (RefinedBlock b I) - 1 := by
  rw [refinedEdges_card, refinedBlock_card]
  have hpos : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨b⟩
  omega

/-- Arbitrary public reattachments preserve connectivity. The proof does not
assume that the accepted shores are correct minimum cuts. -/
theorem refinedEdges_spans (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) : SpanTree.Spans (refinedEdges T b I a) := by
  intro X hX
  by_contra hnone
  have hclosed : ∀ e ∈ refinedEdges T b I a, (e.1 ∈ X ↔ e.2 ∈ X) := by
    intro e he
    by_cases hx : e.1 ∈ X
    · have hy : e.2 ∈ X := by
        by_contra hy
        exact hnone ⟨e, he, by simp [hx, hy]⟩
      exact iff_of_true hx hy
    · have hy : e.2 ∉ X := by
        intro hy
        exact hnone ⟨e, he, by simp [hx, hy]⟩
      exact iff_of_false hx hy
  have hcenter (c : Option I) : (Sum.inr c : RefinedBlock b I) ∈ X ↔ Sum.inr none ∈ X := by
    cases c with
    | none => rfl
    | some i => exact hclosed _ (refinedStarEdge_mem T b I a i)
  have hend (x y : B) :
      refinedEndpoint b I a x y ∈ X ↔ refinementRepresentative b I x ∈ X := by
    by_cases hx : x = b
    · simpa [refinedEndpoint, refinementRepresentative, hx] using hcenter (a y)
    · simp [refinedEndpoint, refinementRepresentative, hx]
  let P : B → Prop := fun x => refinementRepresentative b I x ∈ X
  have hparent (x : B) (hx : x ≠ T.root) : P x ↔ P (T.parent x) :=
    (hend x (T.parent x)).symm.trans
      ((hclosed _ (refinedOldEdge_mem T b I a hx)).trans (hend (T.parent x) x))
  have hstep (x : B) : P x ↔ P (T.parent x) := by
    by_cases hx : x = T.root
    · simp only [hx, T.parent_root]
    · exact hparent x hx
  have hiter (x : B) (k : ℕ) : P x ↔ P (T.parent^[k] x) := by
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (hstep _)
  have hroot (x : B) : P x ↔ P T.root := by
    simpa only [T.iterate_depth x] using hiter x (T.depth x)
  have hall (z : RefinedBlock b I) : z ∈ X ↔ Sum.inr none ∈ X := by
    cases z with
    | inl c =>
        have hc : c.val ≠ b := (Finset.mem_erase.mp c.property).1
        simpa [P, refinementRepresentative, hc] using (hroot c.val).trans (hroot b).symm
    | inr c => exact hcenter c
  obtain ⟨z, hz⟩ := hX.1
  apply hX.2
  ext y
  simp only [Finset.mem_univ, iff_true]
  exact (hall y).mpr ((hall z).mp hz)

/-- A literal rooted tree on the same finite labels used by the refined block
map. Every choice depends only on public data. -/
def refinedBlockTree (T : RootedTree B) (b : B) (I : Finset ι) (a : B → Option I) :
    RootedTree (RefinedBlock b I) :=
  SpanTree.bfsTree (refinedEdges T b I a) (Sum.inr none) (refinedEdges_spans T b I a)

@[simp] theorem refinedBlockTree_root (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) : (refinedBlockTree T b I a).root = Sum.inr none := rfl

theorem refinedBlockTree_parent_adj (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) {v : RefinedBlock b I} (hv : v ≠ (refinedBlockTree T b I a).root) :
    SpanTree.Adj (refinedEdges T b I a) ((refinedBlockTree T b I a).parent v) v :=
  SpanTree.bfsTree_adj (refinedEdges_spans T b I a) hv

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Pulling an old block shore through the new map gives its original vertex
shore exactly. Old cut values and supplied witnesses therefore remain facts
about the same original sets. -/
theorem refinedBlock_old_shore_pull (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V) (X : Finset B) :
    pull (refinedBlockMap p b I S) (pull (refinedBlockParent b I) X) = pull p X := by
  ext v
  simp only [mem_pull, refinedBlockParent_map]

/-- A single actual refinement preserves the complete-frontier size bound.
The label count, partition map, and tree in this statement are the concrete
constructions above. Iterating this step along an algorithm's execution is a
separate obligation. -/
theorem refinedBlock_frontier_sizes (p : V → B) (T : RootedTree B) (b : B)
    (I : Finset ι) (S : ι → Finset V) (a : B → Option I)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (hp : Function.Surjective p) (r : V) (hr : p r = b)
    (hrS : ∀ i ∈ I, r ∉ S i)
    (hchild : ∀ i : I, ∃ v : V, p v = b ∧ v ∈ S i.val) :
    (∑ c, Fintype.card (FrontierVertex (refinedBlockMap p b I S)
      (refinedBlockTree T b I a) c)) = Fintype.card V + 2 * (Fintype.card B + I.card - 1) ∧
    (∑ c, Fintype.card (FrontierVertex (refinedBlockMap p b I S)
      (refinedBlockTree T b I a) c)) ≤ 3 * Fintype.card V ∧
    ∀ c, Fintype.card (FrontierVertex (refinedBlockMap p b I S)
      (refinedBlockTree T b I a) c) ≤ Fintype.card V := by
  have hsurj := refinedBlockMap_surjective p b I S hdisj hp r hr hrS hchild
  refine ⟨?_, frontier_vertex_sum_le _ hsurj _, fun c => frontierVertex_card_le _ hsurj _ c⟩
  rw [frontier_vertex_sum, refinedBlock_card]

#print axioms refinedBlockParent_endpoint
#print axioms refinedOldEdge_mem
#print axioms refinedStarEdge_mem
#print axioms refinedOldEdge_injective
#print axioms refinedStarEdge_injective
#print axioms refinedOldEdge_ne_star
#print axioms refinedEdge_parts_disjoint
#print axioms refinedEdges_card
#print axioms refinedEdges_card_eq_vertices_sub_one
#print axioms refinedEdges_spans
#print axioms refinedBlockTree
#print axioms refinedBlockTree_root
#print axioms refinedBlockTree_parent_adj
#print axioms refinedBlock_old_shore_pull
#print axioms refinedBlock_frontier_sizes

end
end CutQueryComplexity.GHReduction
