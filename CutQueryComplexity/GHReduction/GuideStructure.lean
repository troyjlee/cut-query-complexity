import CutQueryComplexity.MinCut.RootedTree
import CutQueryComplexity.DirectedCertificate.Completion.Centroid
import CutQueryComplexity.GHReduction.GuideBudget

/-! # Public guides with real and fake vertices

Only the designated real nodes carry meaningful graph labels. The label map
is injective there; its values on fake nodes are never interpreted. Centroids
balance the real nodes, and their nonempty real groups are disjoint.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

structure GuideTree (V N : Type) where
  tree : RootedTree N
  real : Finset N
  label : N → V
  label_injective : Set.InjOn label (real : Set N)
  sourceNode : N
  source_real : sourceNode ∈ real

def centroidTree (T : RootedTree N) : TwoRespecting.RootedTree N where
  root := T.root
  parent := T.parent
  depth := T.depth
  parent_root := T.parent_root
  depth_root := T.depth_root
  depth_parent := T.depth_parent

namespace GuideTree

def source (T : GuideTree V N) : V := T.label T.sourceNode

def realVertices (T : GuideTree V N) : Finset V := T.real.image T.label

def graphGroup (T : GuideTree V N) (P : Finset N) : Finset V := P.image T.label

theorem source_mem (T : GuideTree V N) : T.source ∈ T.realVertices :=
  Finset.mem_image.mpr ⟨T.sourceNode, T.source_real, rfl⟩

theorem realVertices_card (T : GuideTree V N) : T.realVertices.card = T.real.card := by
  exact Finset.card_image_iff.mpr T.label_injective

theorem real_card_le (T : GuideTree V N) : T.real.card ≤ Fintype.card V := by
  rw [← T.realVertices_card]
  exact Finset.card_le_univ _

theorem graphGroup_card (T : GuideTree V N) {P : Finset N} (hP : P ⊆ T.real) :
    (T.graphGroup P).card = P.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb he
  exact T.label_injective (hP ha) (hP hb) he

theorem graphGroup_subset (T : GuideTree V N) {P : Finset N} (hP : P ⊆ T.real) :
    T.graphGroup P ⊆ T.realVertices := Finset.image_subset_image hP

theorem graphGroup_disjoint (T : GuideTree V N) {P Q : Finset N}
    (hP : P ⊆ T.real) (hQ : Q ⊆ T.real) (hPQ : Disjoint P Q) :
    Disjoint (T.graphGroup P) (T.graphGroup Q) := by
  apply Finset.disjoint_left.mpr
  intro v hvP hvQ
  obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hvP
  obtain ⟨b, hb, hbv⟩ := Finset.mem_image.mp hvQ
  have he := T.label_injective (hP ha) (hQ hb) (hav.trans hbv.symm)
  exact Finset.disjoint_left.mp hPQ ha (he.symm ▸ hb)

/-- Chosen entirely from the explicit guide and its real-node mask. -/
def centroid (T : GuideTree V N) : N :=
  Classical.choose (DirectedCertificate.Completion.exists_restricted_subtree_centroid
    (centroidTree T.tree) T.real ⟨T.sourceNode, T.source_real⟩)

theorem centroid_spec (T : GuideTree V N) :
    2 * (T.real \ (centroidTree T.tree).subtree T.centroid).card ≤ T.real.card ∧
      ∀ v : N, v ≠ T.tree.root → T.tree.parent v = T.centroid →
        2 * (T.real ∩ (centroidTree T.tree).subtree v).card ≤ T.real.card :=
  Classical.choose_spec (DirectedCertificate.Completion.exists_restricted_subtree_centroid
    (centroidTree T.tree) T.real ⟨T.sourceNode, T.source_real⟩)

/-- Real parts with empty centroid branches discarded. Fake vertices contribute
neither cardinality nor a terminal in this partition. -/
def parts (T : GuideTree V N) : Finset (Finset N) :=
  (DirectedCertificate.Completion.separatorParts (centroidTree T.tree) T.real T.centroid).filter
    Finset.Nonempty

theorem part_nonempty (T : GuideTree V N) {P : Finset N} (hP : P ∈ T.parts) : P.Nonempty :=
  (Finset.mem_filter.mp hP).2

theorem part_subset (T : GuideTree V N) {P : Finset N} (hP : P ∈ T.parts) : P ⊆ T.real :=
  DirectedCertificate.Completion.separatorParts_subset _ _ _ (Finset.mem_filter.mp hP).1

theorem parts_disjoint (T : GuideTree V N) : (T.parts : Set (Finset N)).PairwiseDisjoint id := by
  intro P hP Q hQ hne
  exact DirectedCertificate.Completion.separatorParts_disjoint (centroidTree T.tree)
    T.real T.centroid (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hQ).1 hne

theorem graphGroups_disjoint (T : GuideTree V N) :
    (T.parts : Set (Finset N)).PairwiseDisjoint T.graphGroup := by
  intro P hP Q hQ hne
  exact T.graphGroup_disjoint (T.part_subset hP) (T.part_subset hQ)
    (T.parts_disjoint hP hQ hne)

theorem part_half (T : GuideTree V N) {P : Finset N} (hP : P ∈ T.parts) :
    2 * P.card ≤ T.real.card := by
  rcases DirectedCertificate.Completion.separatorParts_cases _ _ _
    (Finset.mem_filter.mp hP).1 with rfl | ⟨v, hv, hp, rfl⟩
  · exact T.centroid_spec.1
  · exact T.centroid_spec.2 v hv hp

theorem graphGroup_half (T : GuideTree V N) {P : Finset N} (hP : P ∈ T.parts) :
    2 * (T.graphGroup P).card ≤ T.realVertices.card := by
  rw [T.graphGroup_card (T.part_subset hP), T.realVertices_card]
  exact T.part_half hP

theorem parts_cover_except_centroid (T : GuideTree V N) {x : N}
    (hx : x ∈ T.real) (hxc : x ≠ T.centroid) : ∃ P ∈ T.parts, x ∈ P := by
  obtain ⟨P, hP, hxP⟩ := DirectedCertificate.Completion.separatorParts_cover
    (centroidTree T.tree) T.real T.centroid hx hxc
  exact ⟨P, Finset.mem_filter.mpr ⟨hP, ⟨x, hxP⟩⟩, hxP⟩

/-- At most the centroid's one real label is omitted by the retained groups. -/
theorem real_card_le_one_add_groups (T : GuideTree V N) :
    T.real.card ≤ 1 + ∑ P ∈ T.parts, (T.graphGroup P).card := by
  have hcover : T.real ⊆ insert T.centroid (T.parts.biUnion id) := by
    intro x hx
    by_cases hxc : x = T.centroid
    · simp [hxc]
    · obtain ⟨P, hP, hxP⟩ := T.parts_cover_except_centroid hx hxc
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨P, hP, hxP⟩)
  have hle := (Finset.card_le_card hcover).trans (Finset.card_insert_le _ _)
  rw [Finset.card_biUnion T.parts_disjoint] at hle
  have hcards : (∑ P ∈ T.parts, (T.graphGroup P).card) = ∑ P ∈ T.parts, P.card :=
    Finset.sum_congr rfl (fun P hP => T.graphGroup_card (T.part_subset hP))
  simpa only [id_eq, hcards, Nat.add_comm] using hle

theorem two_le_parts (T : GuideTree V N) (hlarge : 2 < T.real.card) : 2 ≤ T.parts.card := by
  apply two_le_children_of_balanced_cover T.parts (fun P => (T.graphGroup P).card) hlarge
    T.real_card_le_one_add_groups
  intro P hP
  rw [T.graphGroup_card (T.part_subset hP)]
  exact T.part_half hP

/-- Real/fake interpretation of an ambient shore. -/
def RespectsCut (T : GuideTree V N) (S : Finset V) (k : ℕ) : Prop :=
  ∃ A : Finset N, (∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S) ∧ (T.tree.crossSet A).card ≤ k

end GuideTree
end
end CutQueryComplexity.GHReduction
