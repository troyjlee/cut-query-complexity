import CutQueryComplexity.GHReduction.GuideOne
import CutQueryComplexity.GHReduction.CutUncrossing

/-! # One-respected minimum cuts pass to an actual recursive child

Orient a guide cut away from the centroid. A one-edge tree cut on that side
lies in a single centroid component. Its real trace is therefore contained in
one isolating group, so intersection preserves minimum value and respect.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

@[simp] theorem centroidTree_subtree (T : RootedTree N) (v : N) :
    (centroidTree T).subtree v = T.D v := by
  ext x
  rw [TwoRespecting.RootedTree.mem_subtree, T.mem_D]
  rfl

private theorem guide_crossSet_compl (T : RootedTree N) (A : Finset N) :
    T.crossSet Aᶜ = T.crossSet A := by
  ext v
  simp only [RootedTree.crossSet, RootedTree.Crosses, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_compl]
  tauto

theorem GuideTree.part_of_rootward (T : GuideTree V N) {A : Finset N}
    (hne : (A ∩ T.real).Nonempty) (hA : A ⊆ (T.tree.D T.centroid)ᶜ) :
    ∃ P : T.parts, A ∩ T.real ⊆ P.val := by
  let P := T.real \ (centroidTree T.tree).subtree T.centroid
  have hsub : A ∩ T.real ⊆ P := by
    intro v hv
    obtain ⟨hvA, hvR⟩ := Finset.mem_inter.mp hv
    refine Finset.mem_sdiff.mpr ⟨hvR, ?_⟩
    simpa only [centroidTree_subtree] using (Finset.mem_compl.mp (hA hvA))
  have hP : P ∈ T.parts := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hne.mono hsub⟩
  exact ⟨⟨P, hP⟩, hsub⟩

theorem GuideTree.part_of_child_subtree (T : GuideTree V N) {A : Finset N}
    (hne : (A ∩ T.real).Nonempty) {v : N} (hv : v ≠ T.tree.root)
    (hp : T.tree.parent v = T.centroid) (hA : A ⊆ T.tree.D v) :
    ∃ P : T.parts, A ∩ T.real ⊆ P.val := by
  let P := T.real ∩ (centroidTree T.tree).subtree v
  have hsub : A ∩ T.real ⊆ P := by
    intro x hx
    obtain ⟨hxA, hxR⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨hxR, by simpa only [centroidTree_subtree] using hA hxA⟩
  have hP : P ∈ T.parts := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem ?_, hne.mono hsub⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hp⟩, rfl⟩
  exact ⟨⟨P, hP⟩, hsub⟩

theorem GuideTree.oneEdge_part (T : GuideTree V N) {A : Finset N}
    (hne : (A ∩ T.real).Nonempty) (hc : T.centroid ∉ A)
    (hk : (T.tree.crossSet A).card ≤ 1) : ∃ P : T.parts, A ∩ T.real ⊆ P.val := by
  have hproper : ProperShore A :=
    ⟨hne.mono Finset.inter_subset_left, fun he => hc (he ▸ Finset.mem_univ _)⟩
  have hnonempty := (T.tree.crossSet_nonempty hproper).card_pos
  have hcard : (T.tree.crossSet A).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  by_cases hr : T.tree.root ∈ A
  · have hcomp : Aᶜ = T.tree.D a := T.tree.eq_D_of_crossSet_one (by simpa using hr)
      (by simpa only [guide_crossSet_compl T.tree A] using ha)
    have hca : T.centroid ∈ T.tree.D a := by rw [← hcomp]; exact Finset.mem_compl.mpr hc
    apply T.part_of_rootward hne
    intro v hv
    apply Finset.mem_compl.mpr
    intro hvD
    have hvDa := T.tree.D_subset hca hvD
    rw [← hcomp] at hvDa
    exact (Finset.mem_compl.mp hvDa) hv
  · have hA : A = T.tree.D a := T.tree.eq_D_of_crossSet_one hr ha
    by_cases hac : a ∈ T.tree.D T.centroid
    · have hanc : (centroidTree T.tree).IsAnc T.centroid a :=
        (T.tree.mem_D _ _).mp hac
      have hneac : a ≠ T.centroid := by
        intro he
        apply hc
        rw [hA, ← he]
        exact T.tree.self_mem_D a
      obtain ⟨v, hv, hp, hva⟩ := DirectedCertificate.Completion.exists_child_ancestor
        (centroidTree T.tree) hanc hneac
      apply T.part_of_child_subtree hne hv hp
      rw [hA]
      exact T.tree.D_subset ((T.tree.mem_D _ _).mpr hva)
    · have hdisj : Disjoint (T.tree.D a) (T.tree.D T.centroid) := by
        rcases T.tree.D_laminar a T.centroid with hd | hca | hac'
        · exact hd
        · exact (hc (hA.symm ▸ hca)).elim
        · exact (hac hac').elim
      apply T.part_of_rootward hne
      intro v hv
      apply Finset.mem_compl.mpr
      exact Finset.disjoint_left.mp hdisj (hA ▸ hv)

theorem GuideTree.oneEdge_trace_part (T : GuideTree V N) {C : Finset V} {A : Finset N}
    (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ C)
    (hc : T.centroid ∉ A) (hk : (T.tree.crossSet A).card ≤ 1)
    (hne : (C ∩ T.realVertices).Nonempty) :
    ∃ P : T.parts, C ∩ T.realVertices ⊆ T.graphGroup P.val := by
  have hnA : (A ∩ T.real).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨hxC, hxR⟩ := Finset.mem_inter.mp hx
    obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hxR
    exact ⟨v, Finset.mem_inter.mpr ⟨(hA v hv).mpr (hvx.symm ▸ hxC), hv⟩⟩
  obtain ⟨P, hP⟩ := T.oneEdge_part hnA hc hk
  refine ⟨P, ?_⟩
  intro x hx
  obtain ⟨hxC, hxR⟩ := Finset.mem_inter.mp hx
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hxR
  have hvA := (hA v hv).mpr (hvx.symm ▸ hxC)
  exact Finset.mem_image.mpr ⟨v, hP (Finset.mem_inter.mpr ⟨hvA, hv⟩), hvx⟩

theorem GuideTree.respects_compl (T : GuideTree V N) {C : Finset V} {k : ℕ}
    (h : T.RespectsCut C k) : T.RespectsCut Cᶜ k := by
  obtain ⟨A, hA, hk⟩ := h
  refine ⟨Aᶜ, ?_, ?_⟩
  · intro v hv
    simpa only [Finset.mem_compl] using not_congr (hA v hv)
  · simpa only [guide_crossSet_compl T.tree A] using hk

/-- A respected minimum cut oriented away from the centroid is represented,
with the same respect parameter, in one of the program's actual children. -/
theorem oneEdge_oriented_child {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hlarge : 2 < T.real.card) {a b : V} {C : Finset V} {A : Finset N}
    (hC : IsSTMinCut G a b C) (haR : a ∈ T.realVertices)
    (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ C)
    (hc : T.centroid ∉ A) (hk : (T.tree.crossSet A).card ≤ 1) :
    ∃ P : T.parts,
      let S := Prog.eval G.cut (centroidShoreProgram family T) P
      ∃ htrace : S ∩ T.realVertices = T.graphGroup P.val,
        ∃ X : Finset (ShoreVertex S), IsSTMinCut G a b (pull (shoreMap S) X) ∧
          (childGuide T P S htrace).RespectsCut X 1 := by
  generalize hshores : Prog.eval G.cut (centroidShoreProgram family T) = shores
  obtain ⟨P, hCP⟩ := T.oneEdge_trace_part hA hc hk ⟨a, Finset.mem_inter.mpr ⟨hC.1, haR⟩⟩
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

theorem oneEdge_child {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hlarge : 2 < T.real.card) {t : V} (ht : t ∈ T.realVertices) {C : Finset V}
    (hC : IsSTMinCut G t T.source C) (hrespect : T.RespectsCut C 1) :
    ∃ P : T.parts,
      let S := Prog.eval G.cut (centroidShoreProgram family T) P
      ∃ htrace : S ∩ T.realVertices = T.graphGroup P.val,
        ∃ X : Finset (ShoreVertex S), IsSTMinCut G t T.source (pull (shoreMap S) X) ∧
          (childGuide T P S htrace).RespectsCut X 1 := by
  obtain ⟨A, hA, hk⟩ := hrespect
  by_cases hc : T.centroid ∈ A
  · have hAcomp : ∀ v ∈ T.real, v ∈ Aᶜ ↔ T.label v ∈ Cᶜ := by
      intro v hv
      simpa only [Finset.mem_compl] using not_congr (hA v hv)
    obtain ⟨P, htrace, X, hX, hrespectX⟩ := oneEdge_oriented_child family G hG T hlarge
      (stMinCut_compl G hC) T.source_mem hAcomp (by simpa using hc)
      (by simpa only [guide_crossSet_compl T.tree A] using hk)
    refine ⟨P, htrace, Xᶜ, ?_, (childGuide T P _ htrace).respects_compl hrespectX⟩
    simpa only [pull_compl] using stMinCut_compl G hX
  · exact oneEdge_oriented_child family G hG T hlarge hC ht hA hc hk

theorem childGuide_map_real (T : GuideTree V N) (P : T.parts) (S : Finset V)
    (htrace : S ∩ T.realVertices = T.graphGroup P.val) {v : V} (hv : v ∈ T.realVertices) :
    shoreMap S v ∈ (childGuide T P S htrace).realVertices := by
  by_cases hvS : v ∈ S
  · have hvP : v ∈ T.graphGroup P.val := by
      rw [← htrace]
      exact Finset.mem_inter.mpr ⟨hvS, hv⟩
    obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hvP
    apply Finset.mem_image.mpr
    refine ⟨some x, ?_, ?_⟩
    · simp [childGuide, GuideTree.addProxy, hx]
    · simp [childGuide, GuideTree.addProxy, hx, hxv, shoreMap, hvS]
  · apply Finset.mem_image.mpr
    refine ⟨none, ?_, ?_⟩
    · simp [childGuide, GuideTree.addProxy]
    · simp [childGuide, GuideTree.addProxy, shoreMap, hvS]

end
end CutQueryComplexity.GHReduction
