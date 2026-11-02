import CutQueryComplexity.GHReduction.FrontierForestCompatibility

/-! # Recursive forest attachments on retained and new round cuts -/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B ι : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq ι]

theorem roundForest_child_attach (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (I : B → Finset ι) (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b), S b i = pull (frontierMap p T b) A)
    (forest : RoundBlock I → PackedSteinerTree V)
    (hforest : ForestCompatible (roundBlockMap p I S)
      (roundBlockTree T I (roundSplitAttachment p hp I S)) forest)
    (b : B) (i : I b) (z : RoundBlock I) (x y : V)
    (hx : ¬(z ∈ roundChildShore I (roundSplitAttachment p hp I S) b i ↔ x ∈ S b i.val))
    (hy : ¬(z ∈ roundChildShore I (roundSplitAttachment p hp I S) b i ↔ y ∈ S b i.val)) :
    (forest z).value.attach x = (forest z).value.attach y := by
  let a := roundSplitAttachment p hp I S
  have hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e) :=
    fun b e he heb hpb => roundSplitAttachment_parent p hp T I S hdisj hpull b he heb hpb
  have hedge : roundStarEdge I ⟨b, i⟩ ∈ roundEdges T I a :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨b, i⟩, Finset.mem_univ _, rfl⟩)
  have hmem (v : V) : roundBlockMap p I S v ∈ roundChildShore I a b i ↔ v ∈ S b i.val := by
    rw [← mem_pull]
    rw [roundChildShore_pull p hp T I S hdisj hpull]
  apply ForestCompatible.on_edgeShore (roundBlockMap p I S) (roundBlockTree T I a) forest hforest
    (roundEdges T I a) (fun _ hv => roundBlockTree_parent_adj T I a hv)
    (roundEdgeShore T I a) (roundEdgeShore_system T I a hconstant) hedge z x y
  · simpa only [roundEdgeShore_star, hmem] using hx
  · simpa only [roundEdgeShore_star, hmem] using hy

theorem roundForest_old_attach (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (I : B → Finset ι) (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b), S b i = pull (frontierMap p T b) A)
    (forest : RoundBlock I → PackedSteinerTree V)
    (hforest : ForestCompatible (roundBlockMap p I S)
      (roundBlockTree T I (roundSplitAttachment p hp I S)) forest)
    (e : B) (he : e ≠ T.root) (z : RoundBlock I) (x y : V)
    (hx : ¬(z.1 ∈ T.D e ↔ p x ∈ T.D e)) (hy : ¬(z.1 ∈ T.D e ↔ p y ∈ T.D e)) :
    (forest z).value.attach x = (forest z).value.attach y := by
  let a := roundSplitAttachment p hp I S
  have hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e) :=
    fun b e he heb hpb => roundSplitAttachment_parent p hp T I S hdisj hpull b he heb hpb
  have hedge : roundOldEdge T I a e ∈ roundEdges T I a :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, Finset.mem_erase.mpr ⟨he, Finset.mem_univ _⟩, rfl⟩)
  apply ForestCompatible.on_edgeShore (roundBlockMap p I S) (roundBlockTree T I a) forest hforest
    (roundEdges T I a) (fun _ hv => roundBlockTree_parent_adj T I a hv)
    (roundEdgeShore T I a) (roundEdgeShore_system T I a hconstant) hedge z x y
  · simp only [roundEdgeShore_old T I a he, mem_pull]
    change ¬(z.1 ∈ T.D e ↔ p x ∈ T.D e)
    exact hx
  · simp only [roundEdgeShore_old T I a he, mem_pull]
    change ¬(z.1 ∈ T.D e ↔ p y ∈ T.D e)
    exact hy

end
end CutQueryComplexity.GHReduction
