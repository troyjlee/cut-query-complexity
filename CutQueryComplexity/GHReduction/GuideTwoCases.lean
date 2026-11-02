import CutQueryComplexity.GHReduction.GuideTwoGeometry
import CutQueryComplexity.GHReduction.GuideSourceSwitch

/-! # Exhaustive branches of the two-respecting recursion

Every nonroot tree edge touches exactly one component after deleting the
centroid. For a noncentroid target, either every cut edge touches its branch,
or a crossed different branch can be removed. If that branch contains the
source, use the source-switching call; otherwise use random pruning. No
additional assumption on the pattern of the other crossed edge is needed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def branchTouchesEdge (T : RootedTree N) (c : N) (b : frontierProxies T c) (e : N) : Prop :=
  e ∈ frontierBranch T c b ∨ T.parent e ∈ frontierBranch T c b

theorem branchTouchesEdge_iff (T : RootedTree N) (c : N) (b : frontierProxies T c)
    {e : N} (he : e ≠ T.root) (hec : e ≠ c) :
    branchTouchesEdge T c b e ↔ e ∈ frontierBranch T c b := by
  constructor
  · rintro (h | h)
    · exact h
    · have hp : T.parent e ≠ c := fun hp => frontierBranch_excludes T c b (hp ▸ h)
      exact ((frontierBranch_isCentroidBranch T c b).2 e he hec hp).mpr h
  · exact Or.inl

theorem exists_branchTouchesEdge (T : RootedTree N) (c : N) {e : N} (he : e ≠ T.root) :
    ∃ b : frontierProxies T c, branchTouchesEdge T c b e := by
  by_cases hec : e = c
  · have hp : T.parent e ≠ c := by
      rw [← hec]
      exact parent_ne_child T he
    obtain ⟨b, hb⟩ := exists_frontierBranch T c (T.parent e) hp
    exact ⟨b, Or.inr hb⟩
  · obtain ⟨b, hb⟩ := exists_frontierBranch T c e hec
    exact ⟨b, Or.inl hb⟩

theorem branchTouchesEdge_unique (T : RootedTree N) (c : N) {e : N} (he : e ≠ T.root)
    {a b : frontierProxies T c} (ha : branchTouchesEdge T c a e)
    (hb : branchTouchesEdge T c b e) : a = b := by
  by_contra hab
  have hd := frontierBranches_disjoint T c hab
  by_cases hec : e = c
  · have ha' : T.parent e ∈ frontierBranch T c a := by
      rcases ha with ha | ha
      · exact (frontierBranch_excludes T c a (hec ▸ ha)).elim
      · exact ha
    have hb' : T.parent e ∈ frontierBranch T c b := by
      rcases hb with hb | hb
      · exact (frontierBranch_excludes T c b (hec ▸ hb)).elim
      · exact hb
    exact Finset.disjoint_left.mp hd ha' hb'
  · exact Finset.disjoint_left.mp hd
      ((branchTouchesEdge_iff T c a he hec).mp ha)
      ((branchTouchesEdge_iff T c b he hec).mp hb)

/-- This case split refers to the actual full centroid components, including
fake vertices, and directly supplies the witness needed by each branch. -/
theorem guideTwo_crossing_cases (T : GuideTree V N) (A : Finset N)
    (targetBranch : frontierProxies T.tree T.centroid) :
    (∀ e ∈ T.tree.crossSet A, branchTouchesEdge T.tree T.centroid targetBranch e) ∨
    (∃ b : frontierProxies T.tree T.centroid, b ≠ targetBranch ∧
      T.sourceNode ∉ frontierBranch T.tree T.centroid b ∧
      ∃ e ∈ T.tree.crossSet A, branchTouchesEdge T.tree T.centroid b e) ∨
    (∃ b : frontierProxies T.tree T.centroid, b ≠ targetBranch ∧
      T.sourceNode ∈ frontierBranch T.tree T.centroid b ∧
      ∃ e ∈ T.tree.crossSet A, branchTouchesEdge T.tree T.centroid b e) := by
  by_cases hall : ∀ e ∈ T.tree.crossSet A, branchTouchesEdge T.tree T.centroid targetBranch e
  · exact Or.inl hall
  · push_neg at hall
    obtain ⟨e, he, heT⟩ := hall
    obtain ⟨b, hb⟩ := exists_branchTouchesEdge T.tree T.centroid
      (T.tree.ne_root_of_mem_crossSet he)
    have hbT : b ≠ targetBranch := fun h => heT (h ▸ hb)
    by_cases hs : T.sourceNode ∈ frontierBranch T.tree T.centroid b
    · exact Or.inr (Or.inr ⟨b, hbT, hs, e, he, hb⟩)
    · exact Or.inr (Or.inl ⟨b, hbT, hs, e, he, hb⟩)

theorem GuideTree.branch_real_half (T : GuideTree V N)
    (b : frontierProxies T.tree T.centroid) :
    2 * (T.real ∩ frontierBranch T.tree T.centroid b).card ≤ T.real.card := by
  by_cases hb : b.val = T.centroid
  · have hset : T.real ∩ frontierBranch T.tree T.centroid b =
        T.real \ (centroidTree T.tree).subtree T.centroid := by
      ext v
      simp [frontierBranch, hb]
    rw [hset]
    exact T.centroid_spec.1
  · have hspec := (mem_frontierProxies T.tree T.centroid b.val).mp b.property
    simpa only [frontierBranch, hb, ite_false, centroidTree_subtree] using
      T.centroid_spec.2 b.val hspec.1 (hspec.2.resolve_left hb)

theorem GuideTree.outside_branch_nonempty (T : GuideTree V N)
    (b : frontierProxies T.tree T.centroid) :
    (T.real ∩ (frontierBranch T.tree T.centroid b)ᶜ).Nonempty := by
  by_contra h
  have hsub : T.real ⊆ frontierBranch T.tree T.centroid b := by
    intro v hv
    by_contra hvb
    exact h ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_compl.mpr hvb⟩⟩
  have hcard : (T.real ∩ frontierBranch T.tree T.centroid b).card = T.real.card := by
    rw [Finset.inter_eq_left.mpr hsub]
  have hhalf := T.branch_real_half b
  rw [hcard] at hhalf
  have hpos : 0 < T.real.card := Finset.card_pos.mpr ⟨T.sourceNode, T.source_real⟩
  omega

/-- A source branch is determined by the public source node alone. -/
def GuideTree.sourceBranch (T : GuideTree V N) (hs : T.sourceNode ≠ T.centroid) :
    frontierProxies T.tree T.centroid := frontierProxy T.tree T.centroid T.sourceNode hs

theorem GuideTree.sourceBranch_eq (T : GuideTree V N) (hs : T.sourceNode ≠ T.centroid)
    (b : frontierProxies T.tree T.centroid)
    (hb : T.sourceNode ∈ frontierBranch T.tree T.centroid b) : T.sourceBranch hs = b :=
  (frontierProxy_eq_iff T.tree T.centroid T.sourceNode hs b).mpr hb

end
end CutQueryComplexity.GHReduction
