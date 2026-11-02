import CutQueryComplexity.GHReduction.BlockRefinement
import CutQueryComplexity.GHReduction.PartialTree
import CutQueryComplexity.MinCut.SpanTree
import Mathlib.Data.Fintype.Sigma

/-! # Simultaneous public refinement of a complete frontier

Every old block receives a residual label and its own accepted child labels.
The actual partition map refines each vertex only inside its own old block.
Every old edge remains, with each endpoint reattached independently; new child
edges join their residual. A public BFS supplies the next rooted topology.

This construction supports rounds on a fixed frontier, without silently
reusing an obsolete auxiliary graph after a different block is refined.
Capacity and minimum-cut witness preservation are separate propositions.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph

variable {V B ι : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq ι]

def RoundBlock (I : B → Finset ι) := (b : B) × Option (I b)

instance roundBlockFintype (I : B → Finset ι) : Fintype (RoundBlock I) :=
  inferInstanceAs (Fintype (Sigma _))

instance roundBlockDecidableEq (I : B → Finset ι) : DecidableEq (RoundBlock I) :=
  inferInstanceAs (DecidableEq (Sigma _))

def roundBlockMap (p : V → B) (I : B → Finset ι) (S : B → ι → Finset V)
    (v : V) : RoundBlock I := ⟨p v, refinementCell (I (p v)) (S (p v)) v⟩

def roundBlockParent (I : B → Finset ι) (c : RoundBlock I) : B := c.1

@[simp] theorem roundBlockParent_map (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V) (v : V) : roundBlockParent I (roundBlockMap p I S v) = p v := rfl

theorem roundBlockMap_of_fiber (p : V → B) (I : B → Finset ι) (S : B → ι → Finset V)
    (v : V) (b : B) (hv : p v = b) :
    roundBlockMap p I S v = ⟨b, refinementCell (I b) (S b) v⟩ := by
  subst b
  rfl

theorem roundBlockMap_residual_iff (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V) (v : V) (b : B) :
    roundBlockMap p I S v = ⟨b, none⟩ ↔ p v = b ∧ ∀ i ∈ I b, v ∉ S b i := by
  constructor
  · intro he
    have hv : p v = b := congrArg (roundBlockParent I) he
    rw [roundBlockMap_of_fiber p I S v b hv] at he
    exact ⟨hv, (refinementCell_eq_none (I b) (S b) v).mp
      (sigma_mk_injective (β := fun b => Option (I b)) he)⟩
  · rintro ⟨hv, hnone⟩
    rw [roundBlockMap_of_fiber p I S v b hv,
      (refinementCell_eq_none (I b) (S b) v).mpr hnone]

theorem roundBlockMap_child_iff (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (v : V) (b : B) (i : I b) :
    roundBlockMap p I S v = ⟨b, some i⟩ ↔ p v = b ∧ v ∈ S b i.val := by
  constructor
  · intro he
    have hv : p v = b := congrArg (roundBlockParent I) he
    rw [roundBlockMap_of_fiber p I S v b hv] at he
    exact ⟨hv, (refinementCell_eq_some (I b) (S b) (hdisj b) v i).mp
      (sigma_mk_injective (β := fun b => Option (I b)) he)⟩
  · rintro ⟨hv, hi⟩
    rw [roundBlockMap_of_fiber p I S v b hv,
      (refinementCell_eq_some (I b) (S b) (hdisj b) v i).mpr hi]

theorem roundBlockMap_residual_fiber (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V) (b : B) :
    fiber (roundBlockMap p I S) ⟨b, none⟩ = fiber p b \ (I b).biUnion (S b) := by
  ext v
  simp only [fiber, pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_biUnion, not_exists, not_and]
  exact Finset.mem_singleton.trans (roundBlockMap_residual_iff p I S v b)

theorem roundBlockMap_child_fiber (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (b : B) (i : I b) :
    fiber (roundBlockMap p I S) ⟨b, some i⟩ = fiber p b ∩ S b i.val := by
  ext v
  simp only [fiber, pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.mem_inter]
  exact Finset.mem_singleton.trans (roundBlockMap_child_iff p I S hdisj v b i)

theorem roundBlockMap_fiber_subset (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V) (c : RoundBlock I) :
    fiber (roundBlockMap p I S) c ⊆ fiber p c.1 := by
  intro v hv
  exact (mem_fiber p c.1 v).mpr
    (congrArg (roundBlockParent I) ((mem_fiber _ _ _).mp hv))

theorem roundBlock_old_shore_pull (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V) (X : Finset B) :
    pull (roundBlockMap p I S) (pull (roundBlockParent I) X) = pull p X := by
  ext v
  simp only [mem_pull, roundBlockParent_map]

/-- Actual retained pivots witness residual blocks; actual child vertices
witness child blocks. No independently supplied numerical ledger is used. -/
theorem roundBlockMap_surjective (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (r : B → V) (hr : ∀ b, p (r b) = b) (hrS : ∀ b, ∀ i ∈ I b, r b ∉ S b i)
    (hchild : ∀ b, ∀ i : I b, ∃ v : V, p v = b ∧ v ∈ S b i.val) :
    Function.Surjective (roundBlockMap p I S) := by
  rintro ⟨b, c⟩
  cases c with
  | none => exact ⟨r b, (roundBlockMap_residual_iff p I S (r b) b).mpr ⟨hr b, hrS b⟩⟩
  | some i =>
      obtain ⟨v, hvb, hvi⟩ := hchild b i
      exact ⟨v, (roundBlockMap_child_iff p I S hdisj v b i).mpr ⟨hvb, hvi⟩⟩

theorem roundBlock_card (I : B → Finset ι) :
    Fintype.card (RoundBlock I) = Fintype.card B + ∑ b, (I b).card := by
  let e : RoundBlock I ≃ ((b : B) × Option (I b)) := Equiv.refl _
  calc
    Fintype.card (RoundBlock I) = Fintype.card ((b : B) × Option (I b)) :=
      Fintype.card_congr e
    _ = _ := by simp [Fintype.card_sigma, Finset.sum_add_distrib, Nat.add_comm]

def roundOldEdge (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) (e : B) : RoundBlock I × RoundBlock I :=
  (⟨e, a e (T.parent e)⟩, ⟨T.parent e, a (T.parent e) e⟩)

def roundStarEdge (I : B → Finset ι) (i : (b : B) × I b) : RoundBlock I × RoundBlock I :=
  (⟨i.1, some i.2⟩, ⟨i.1, none⟩)

def roundEdges (T : RootedTree B) (I : B → Finset ι) (a : (b : B) → B → Option (I b)) :
    Finset (RoundBlock I × RoundBlock I) :=
  (Finset.univ.erase T.root).image (roundOldEdge T I a) ∪
    Finset.univ.image (roundStarEdge I)

theorem roundOldEdge_mem (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) {e : B} (he : e ≠ T.root) :
    roundOldEdge T I a e ∈ roundEdges T I a := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨e, Finset.mem_erase.mpr ⟨he, Finset.mem_univ _⟩, rfl⟩

theorem roundStarEdge_mem (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) (i : (b : B) × I b) :
    roundStarEdge I i ∈ roundEdges T I a := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem roundOldEdge_injective (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) : Function.Injective (roundOldEdge T I a) := by
  intro e f h
  exact congrArg (fun d => (roundBlockParent I) d.1) h

theorem roundStarEdge_injective (I : B → Finset ι) : Function.Injective (roundStarEdge I) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ h
  have hb : b = c := congrArg (fun d : RoundBlock I × RoundBlock I =>
    roundBlockParent I d.1) h
  subst c
  have hij : some i = some j :=
    sigma_mk_injective (β := fun b => Option (I b)) (congrArg Prod.fst h)
  have he : i = j := Option.some.inj hij
  subst j
  rfl

theorem roundEdge_parts_disjoint (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) :
    Disjoint ((Finset.univ.erase T.root).image (roundOldEdge T I a))
      (Finset.univ.image (roundStarEdge I)) := by
  apply Finset.disjoint_left.mpr
  intro d hdOld hdStar
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hdOld
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hdStar
  have hf : i.1 = e := congrArg (fun d : RoundBlock I × RoundBlock I =>
    roundBlockParent I d.1) hi
  have hs : i.1 = T.parent e := congrArg (fun d : RoundBlock I × RoundBlock I =>
    roundBlockParent I d.2) hi
  exact parent_ne_child T (Finset.mem_erase.mp he).1 (hs.symm.trans hf)

theorem roundEdges_card (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) :
    (roundEdges T I a).card = Fintype.card B - 1 + ∑ b, (I b).card := by
  rw [roundEdges, Finset.card_union_of_disjoint (roundEdge_parts_disjoint T I a),
    Finset.card_image_of_injective _ (roundOldEdge_injective T I a),
    Finset.card_image_of_injective _ (roundStarEdge_injective I)]
  simp [Fintype.card_sigma]

theorem roundEdges_spans (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) : SpanTree.Spans (roundEdges T I a) := by
  intro X hX
  by_contra hnone
  have hclosed : ∀ d ∈ roundEdges T I a, (d.1 ∈ X ↔ d.2 ∈ X) := by
    intro d hd
    by_cases hx : d.1 ∈ X
    · have hy : d.2 ∈ X := by
        by_contra hy
        exact hnone ⟨d, hd, by simp [hx, hy]⟩
      exact iff_of_true hx hy
    · have hy : d.2 ∉ X := by
        intro hy
        exact hnone ⟨d, hd, by simp [hx, hy]⟩
      exact iff_of_false hx hy
  have hcenter (b : B) (j : Option (I b)) :
      (⟨b, j⟩ : RoundBlock I) ∈ X ↔ (⟨b, none⟩ : RoundBlock I) ∈ X := by
    cases j with
    | none => rfl
    | some i => exact hclosed _ (roundStarEdge_mem T I a ⟨b, i⟩)
  let P (b : B) : Prop := (⟨b, none⟩ : RoundBlock I) ∈ X
  have hstep (b : B) : P b ↔ P (T.parent b) := by
    by_cases hb : b = T.root
    · simp only [hb, T.parent_root]
    · exact (hcenter b (a b (T.parent b))).symm.trans
        ((hclosed _ (roundOldEdge_mem T I a hb)).trans (hcenter (T.parent b) (a (T.parent b) b)))
  have hiter (b : B) (k : ℕ) : P b ↔ P (T.parent^[k] b) := by
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (hstep _)
  have hroot (b : B) : P b ↔ P T.root := by
    simpa only [T.iterate_depth b] using hiter b (T.depth b)
  have hall (c : RoundBlock I) : c ∈ X ↔ (⟨T.root, none⟩ : RoundBlock I) ∈ X :=
    (hcenter c.1 c.2).trans (hroot c.1)
  obtain ⟨c, hc⟩ := hX.1
  apply hX.2
  ext d
  simp only [Finset.mem_univ, iff_true]
  exact (hall d).mpr ((hall c).mp hc)

def roundBlockTree (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) : RootedTree (RoundBlock I) :=
  SpanTree.bfsTree (roundEdges T I a) ⟨T.root, none⟩ (roundEdges_spans T I a)

theorem roundBlock_frontier_sizes (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V) (T : RootedTree B) (a : (b : B) → B → Option (I b))
    (hmap : Function.Surjective (roundBlockMap p I S)) :
    (∑ c, Fintype.card (FrontierVertex (roundBlockMap p I S) (roundBlockTree T I a) c)) =
      Fintype.card V + 2 * (Fintype.card B + (∑ b, (I b).card) - 1) ∧
    (∑ c, Fintype.card (FrontierVertex (roundBlockMap p I S) (roundBlockTree T I a) c)) ≤
      3 * Fintype.card V ∧
    ∀ c, Fintype.card (FrontierVertex (roundBlockMap p I S) (roundBlockTree T I a) c) ≤
      Fintype.card V := by
  refine ⟨?_, frontier_vertex_sum_le _ hmap _, fun c => frontierVertex_card_le _ hmap _ c⟩
  rw [frontier_vertex_sum, roundBlock_card]

end
end CutQueryComplexity.GHReduction
