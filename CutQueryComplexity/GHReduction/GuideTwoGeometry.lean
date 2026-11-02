import CutQueryComplexity.GHReduction.GuideOneGeometry
import CutQueryComplexity.GHReduction.GuidePruneSampling

/-! # Same-parameter geometry for a two-respecting guide cut

If all crossed edges touch one centroid branch, collapsing that branch removes
every crossing. Thus the side away from the centroid is contained in that
branch. Intersecting with its actual isolating shore preserves the original
minimum, and adding the contraction proxy preserves the respect parameter.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

theorem tree_membership_of_crossSet_empty (T : RootedTree N) (A : Finset N)
    (hA : T.crossSet A = ∅) (x y : N) : x ∈ A ↔ y ∈ A := by
  have hroot (v : N) : v ∈ A ↔ T.root ∈ A := by
    have h := T.mem_iff_parity A v
    simpa only [RootedTree.crossAbove, hA, Finset.filter_empty, Finset.card_empty,
      Even.zero, iff_true] using h
  exact (hroot x).trans (hroot y).symm

theorem tree_cut_subset_single_branch (T : RootedTree N) (c : N)
    (branch : frontierProxies T c) (A : Finset N) (hc : c ∉ A)
    (hall : ∀ e ∈ T.crossSet A,
      e ∈ frontierBranch T c branch ∨ T.parent e ∈ frontierBranch T c branch) :
    A ⊆ frontierBranch T c branch := by
  let C := frontierBranch T c branch
  have hcross : T.crossSet (collapseBranch c C A) = ∅ := by
    rw [collapseBranch_crossSet T c C A (frontierBranch_isCentroidBranch T c branch)]
    ext e
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro he
    have hi := hall e he
    tauto
  intro x hx
  by_contra hxC
  have hsame := tree_membership_of_crossSet_empty T (collapseBranch c C A) hcross x c
  have hx' : x ∈ collapseBranch c C A := by
    rw [mem_collapseBranch]
    split_ifs with h
    · exact (hxC h).elim
    · exact hx
  have hc' := hsame.mp hx'
  rw [mem_collapseBranch] at hc'
  exact hc (by simpa only [ite_self] using hc')

theorem GuideTree.part_of_branch (T : GuideTree V N)
    (branch : frontierProxies T.tree T.centroid) {A : Finset N}
    (hne : (A ∩ T.real).Nonempty) (hA : A ⊆ frontierBranch T.tree T.centroid branch) :
    ∃ P : T.parts, A ∩ T.real ⊆ P.val := by
  by_cases he : branch.val = T.centroid
  · apply T.part_of_rootward hne
    simpa only [frontierBranch, he, ite_true] using hA
  · have hspec := (mem_frontierProxies T.tree T.centroid branch.val).mp branch.property
    apply T.part_of_child_subtree hne hspec.1 (hspec.2.resolve_left he)
    simpa only [frontierBranch, he, ite_false] using hA

theorem GuideTree.singleBranch_trace_part (T : GuideTree V N)
    (branch : frontierProxies T.tree T.centroid) {C : Finset V} {A : Finset N}
    (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ C) (hc : T.centroid ∉ A)
    (hall : ∀ e ∈ T.tree.crossSet A,
      e ∈ frontierBranch T.tree T.centroid branch ∨
        T.tree.parent e ∈ frontierBranch T.tree T.centroid branch)
    (hne : (C ∩ T.realVertices).Nonempty) :
    ∃ P : T.parts, C ∩ T.realVertices ⊆ T.graphGroup P.val := by
  have hnA : (A ∩ T.real).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨hxC, hxR⟩ := Finset.mem_inter.mp hx
    obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hxR
    exact ⟨v, Finset.mem_inter.mpr ⟨(hA v hv).mpr (hvx.symm ▸ hxC), hv⟩⟩
  obtain ⟨P, hP⟩ := T.part_of_branch branch hnA
    (tree_cut_subset_single_branch T.tree T.centroid branch A hc hall)
  refine ⟨P, ?_⟩
  intro x hx
  obtain ⟨hxC, hxR⟩ := Finset.mem_inter.mp hx
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hxR
  exact Finset.mem_image.mpr
    ⟨v, hP (Finset.mem_inter.mpr ⟨(hA v hv).mpr (hvx.symm ▸ hxC), hv⟩), hvx⟩

theorem singleBranch_oriented_child {M k : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hlarge : 2 < T.real.card)
    (branch : frontierProxies T.tree T.centroid) {a b : V} {C : Finset V} {A : Finset N}
    (hC : IsSTMinCut G a b C) (haR : a ∈ T.realVertices)
    (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ C) (hc : T.centroid ∉ A)
    (hk : (T.tree.crossSet A).card ≤ k)
    (hall : ∀ e ∈ T.tree.crossSet A,
      e ∈ frontierBranch T.tree T.centroid branch ∨
        T.tree.parent e ∈ frontierBranch T.tree T.centroid branch) :
    ∃ P : T.parts,
      let S := Prog.eval G.cut (centroidShoreProgram family T) P
      ∃ htrace : S ∩ T.realVertices = T.graphGroup P.val,
        ∃ X : Finset (ShoreVertex S), IsSTMinCut G a b (pull (shoreMap S) X) ∧
          (childGuide T P S htrace).RespectsCut X k := by
  generalize hshores : Prog.eval G.cut (centroidShoreProgram family T) = shores
  obtain ⟨P, hCP⟩ := T.singleBranch_trace_part branch hA hc hall
    ⟨a, Finset.mem_inter.mpr ⟨hC.1, haR⟩⟩
  let S := shores P
  have hS := centroidShoreProgram_correct family G hG T hlarge P
  rw [hshores] at hS
  have htrace : S ∩ T.realVertices = T.graphGroup P.val := hS.1.1
  have haP : a ∈ T.graphGroup P.val := hCP (Finset.mem_inter.mpr ⟨hC.1, haR⟩)
  have hmin := (minCut_inter_isolating G hC hS.1 hCP haP).1
  refine ⟨P, htrace, shorePush S (C ∩ S), ?_, ?_⟩
  · change IsSTMinCut G a b (pull (shoreMap S) (shorePush S (C ∩ S)))
    rw [pull_shorePush (S := S) (X := C ∩ S) Finset.inter_subset_right]
    exact hmin
  · exact T.addProxy_respects P.val (T.part_subset P.property) S
      (labels_mem_of_trace T P S htrace) hA hc hk

/-- Choose the side away from the centroid, then restore target orientation.
The selected child is one produced by the actual canonical isolating program. -/
theorem singleBranch_child {M k : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hlarge : 2 < T.real.card)
    (branch : frontierProxies T.tree T.centroid) {t : V} (ht : t ∈ T.realVertices)
    {C : Finset V} {A : Finset N} (hC : IsSTMinCut G t T.source C)
    (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ C)
    (hk : (T.tree.crossSet A).card ≤ k)
    (hall : ∀ e ∈ T.tree.crossSet A,
      e ∈ frontierBranch T.tree T.centroid branch ∨
        T.tree.parent e ∈ frontierBranch T.tree T.centroid branch) :
    ∃ P : T.parts,
      let S := Prog.eval G.cut (centroidShoreProgram family T) P
      ∃ htrace : S ∩ T.realVertices = T.graphGroup P.val,
        ∃ X : Finset (ShoreVertex S), IsSTMinCut G t T.source (pull (shoreMap S) X) ∧
          (childGuide T P S htrace).RespectsCut X k := by
  have hcompl : T.tree.crossSet Aᶜ = T.tree.crossSet A := by
    ext v
    simp only [RootedTree.crossSet, RootedTree.Crosses, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_compl]
    tauto
  by_cases hc : T.centroid ∈ A
  · have hAcomp : ∀ v ∈ T.real, v ∈ Aᶜ ↔ T.label v ∈ Cᶜ := by
      intro v hv
      simpa only [Finset.mem_compl] using not_congr (hA v hv)
    obtain ⟨P, htrace, X, hX, hrespect⟩ := singleBranch_oriented_child family G hG T hlarge
      branch (stMinCut_compl G hC) T.source_mem hAcomp (by simpa using hc)
      (by simpa only [hcompl] using hk)
      (by simpa only [hcompl] using hall)
    refine ⟨P, htrace, Xᶜ, ?_, (childGuide T P _ htrace).respects_compl hrespect⟩
    simpa only [pull_compl] using stMinCut_compl G hX
  · exact singleBranch_oriented_child family G hG T hlarge branch hC ht hA hc hk hall

end
end CutQueryComplexity.GHReduction
