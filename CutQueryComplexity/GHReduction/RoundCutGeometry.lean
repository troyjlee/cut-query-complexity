import CutQueryComplexity.GHReduction.RoundRefinement
import CutQueryComplexity.GHReduction.TreeAssembly

/-! # Fundamental shores after a simultaneous frontier refinement

Each new child shore contains its own refined label and all labels of old
branches attached to that child. It crosses its one new star edge. Old shores
pull back through the public coarsening map and cross only their retained edge.
These statements identify the actual next BFS tree's fundamental shores.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {B ι : Type} [Fintype B] [DecidableEq B] [DecidableEq ι]

def roundChildShore (I : B → Finset ι) (a : (b : B) → B → Option (I b)) (b : B) (i : I b) :
    Finset (RoundBlock I) :=
  Finset.univ.filter (fun z => z = ⟨b, some i⟩ ∨ (z.1 ≠ b ∧ a b z.1 = some i))

@[simp] theorem mem_roundChildShore_same (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) (b : B) (i : I b) (j : Option (I b)) :
    (⟨b, j⟩ : RoundBlock I) ∈ roundChildShore I a b i ↔ j = some i := by
  constructor
  · intro h
    rcases (Finset.mem_filter.mp h).2 with he | hne
    · exact sigma_mk_injective (β := fun b => Option (I b)) he
    · exact (hne.1 rfl).elim
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (congrArg (Sigma.mk b) h)⟩

theorem mem_roundChildShore_other (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) (b : B) (i : I b) {c : B} (hc : c ≠ b)
    (j : Option (I c)) : (⟨c, j⟩ : RoundBlock I) ∈ roundChildShore I a b i ↔ a b c = some i := by
  have hne : (⟨c, j⟩ : RoundBlock I) ≠ ⟨b, some i⟩ :=
    fun he => hc (congrArg (roundBlockParent I) he)
  constructor
  · intro h
    exact ((Finset.mem_filter.mp h).2.resolve_left hne).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hc, h⟩⟩

theorem roundOldEdge_child_membership (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) (b : B)
    (hconstant : ∀ e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e))
    {e : B} (he : e ≠ T.root) (i : I b) :
    (roundOldEdge T I a e).1 ∈ roundChildShore I a b i ↔
      (roundOldEdge T I a e).2 ∈ roundChildShore I a b i := by
  by_cases heb : e = b
  · subst e
    have hpb : T.parent b ≠ b := parent_ne_child T he
    change (⟨b, a b (T.parent b)⟩ : RoundBlock I) ∈ roundChildShore I a b i ↔
      (⟨T.parent b, a (T.parent b) b⟩ : RoundBlock I) ∈ roundChildShore I a b i
    rw [mem_roundChildShore_same, mem_roundChildShore_other I a b i hpb]
  · by_cases hpb : T.parent e = b
    · subst b
      change (⟨e, a e (T.parent e)⟩ : RoundBlock I) ∈ roundChildShore I a (T.parent e) i ↔
        (⟨T.parent e, a (T.parent e) e⟩ : RoundBlock I) ∈ roundChildShore I a (T.parent e) i
      rw [mem_roundChildShore_other I a (T.parent e) i heb, mem_roundChildShore_same]
    · change (⟨e, a e (T.parent e)⟩ : RoundBlock I) ∈ roundChildShore I a b i ↔
        (⟨T.parent e, a (T.parent e) e⟩ : RoundBlock I) ∈ roundChildShore I a b i
      rw [mem_roundChildShore_other I a b i heb, mem_roundChildShore_other I a b i hpb,
        hconstant e he heb hpb]

theorem roundChildShore_edgeCut (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) (b : B)
    (hconstant : ∀ e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e))
    (i : I b) :
    (roundStarEdge I ⟨b, i⟩).1 ∈ roundChildShore I a b i ∧
    (roundStarEdge I ⟨b, i⟩).2 ∉ roundChildShore I a b i ∧
    ∀ d ∈ roundEdges T I a,
      ¬(d.1 ∈ roundChildShore I a b i ↔ d.2 ∈ roundChildShore I a b i) →
        d = roundStarEdge I ⟨b, i⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_roundChildShore_same I a b i (some i)).mpr rfl
  · intro h
    have hn := (mem_roundChildShore_same I a b i none).mp h
    cases hn
  intro d hd hc
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact (hc (roundOldEdge_child_membership T I a b hconstant (Finset.mem_erase.mp he).1 i)).elim
  · obtain ⟨⟨c, j⟩, _, rfl⟩ := Finset.mem_image.mp hd
    by_cases hcb : c = b
    · subst c
      have hji : j = i := by
        change ¬((⟨b, some j⟩ : RoundBlock I) ∈ roundChildShore I a b i ↔
          (⟨b, none⟩ : RoundBlock I) ∈ roundChildShore I a b i) at hc
        simpa only [mem_roundChildShore_same, Option.some.injEq,
          reduceCtorEq, iff_false, not_not] using hc
      subst j
      rfl
    · apply False.elim
      apply hc
      exact (mem_roundChildShore_other I a b i hcb (some j)).trans
        (mem_roundChildShore_other I a b i hcb none).symm

theorem roundOldShore_edgeCut (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) {e : B} (he : e ≠ T.root) :
    (roundOldEdge T I a e).1 ∈ pull (roundBlockParent I) (T.D e) ∧
    (roundOldEdge T I a e).2 ∉ pull (roundBlockParent I) (T.D e) ∧
    ∀ d ∈ roundEdges T I a,
      ¬(d.1 ∈ pull (roundBlockParent I) (T.D e) ↔
        d.2 ∈ pull (roundBlockParent I) (T.D e)) → d = roundOldEdge T I a e := by
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_pull _ _ _).mpr (T.self_mem_D e)
  · exact fun h => tree_parent_not_mem_subtree T he
      ((mem_pull (roundBlockParent I) (T.D e) (roundOldEdge T I a e).2).mp h)
  · intro d hd hc
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hd
      have hf0 : f ≠ T.root := (Finset.mem_erase.mp hf).1
      have hcross : ¬(f ∈ T.D e ↔ T.parent f ∈ T.D e) := by
        exact fun hm => hc
          ((mem_pull (roundBlockParent I) (T.D e) (roundOldEdge T I a f).1).trans
            (hm.trans (mem_pull (roundBlockParent I) (T.D e) (roundOldEdge T I a f).2).symm))
      by_cases hfe : f = e
      · exact congrArg (roundOldEdge T I a) hfe
      · have hef : e ≠ f := Ne.symm hfe
        have hm : f ∈ T.D e ↔ T.parent f ∈ T.D e := by
          simp only [RootedTree.mem_D, T.isAnc_iff_of_ne_root hf0, hef, false_or]
        exact (hcross hm).elim
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
      apply False.elim
      apply hc
      exact (mem_pull (roundBlockParent I) (T.D e) (roundStarEdge I i).1).trans
        (mem_pull (roundBlockParent I) (T.D e) (roundStarEdge I i).2).symm

def roundEdgeShore (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) (d : RoundBlock I × RoundBlock I) : Finset (RoundBlock I) :=
  if d.1.1 = d.2.1 then
    match d.1 with
    | ⟨b, some i⟩ => roundChildShore I a b i
    | ⟨_, none⟩ => ∅
  else pull (roundBlockParent I) (T.D d.1.1)

theorem roundEdgeShore_old (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) {e : B} (he : e ≠ T.root) :
    roundEdgeShore T I a (roundOldEdge T I a e) = pull (roundBlockParent I) (T.D e) := by
  have hne : e ≠ T.parent e := (parent_ne_child T he).symm
  exact ite_eq_right hne

theorem roundEdgeShore_star (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) (i : (b : B) × I b) :
    roundEdgeShore T I a (roundStarEdge I i) = roundChildShore I a i.1 i.2 := by
  simp [roundEdgeShore, roundStarEdge]

theorem roundEdgeShore_system (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b))
    (hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e)) :
    EdgeShoreSystem (roundEdges T I a) (roundEdgeShore T I a) := by
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    have he0 := (Finset.mem_erase.mp he).1
    simpa only [roundEdgeShore_old T I a he0] using roundOldShore_edgeCut T I a he0
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    simpa only [roundEdgeShore_star] using roundChildShore_edgeCut T I a i.1 (hconstant i.1) i.2

theorem roundBlockTree_parent_adj (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) {v : RoundBlock I}
    (hv : v ≠ (roundBlockTree T I a).root) :
    SpanTree.Adj (roundEdges T I a) ((roundBlockTree T I a).parent v) v :=
  SpanTree.bfsTree_adj (roundEdges_spans T I a) hv

theorem roundBlockTree_fundamental (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b))
    (hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e))
    {v : RoundBlock I} (hv : v ≠ (roundBlockTree T I a).root) :
    (roundBlockTree T I a).D v = roundEdgeShore T I a
      (selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v) ∨
    (roundBlockTree T I a).D v = (roundEdgeShore T I a
      (selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v))ᶜ :=
  edgeShore_fundamental _ _ (fun _ h => roundBlockTree_parent_adj T I a h)
    _ (roundEdgeShore_system T I a hconstant) hv

end
end CutQueryComplexity.GHReduction
