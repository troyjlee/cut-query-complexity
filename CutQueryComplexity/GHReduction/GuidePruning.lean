import CutQueryComplexity.GHReduction.GuideStructure
import CutQueryComplexity.GHReduction.ShoreContraction

/-! # Public guide pruning and complement-proxy insertion

Pruned real vertices may remain as fake guide vertices. Their labels carry no
meaning, and a cut witness can make an entire discarded centroid branch agree
with the centroid. This removes every crossing edge touching that branch.
An actual graph contraction still receives one new real proxy, represented by
a new guide leaf attached to the centroid.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

/-- Changing the source is free and does not alter the guide topology. -/
def GuideTree.withSource (T : GuideTree V N) (s : N) (hs : s ∈ T.real) : GuideTree V N where
  tree := T.tree
  real := T.real
  label := T.label
  label_injective := T.label_injective
  sourceNode := s
  source_real := hs

/-- Removed guide vertices are retained as fake vertices. A later proof may
freely choose their side when witnessing the number of respected edges. -/
def GuideTree.retain (T : GuideTree V N) (keep : Finset N) (s : N)
    (hs : s ∈ T.real ∩ keep) : GuideTree V N where
  tree := T.tree
  real := T.real ∩ keep
  label := T.label
  label_injective := fun _ ha _ hb he =>
    T.label_injective (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1 he
  sourceNode := s
  source_real := hs

theorem GuideTree.retain_respects (T : GuideTree V N) (keep : Finset N) (s : N)
    (hs : s ∈ T.real ∩ keep) {S : Finset V} {k : ℕ} (h : T.RespectsCut S k) :
    (T.retain keep s hs).RespectsCut S k := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A, fun v hv => hA v (Finset.mem_inter.mp hv).1, hc⟩

/-- A component after deleting the centroid excludes that vertex, and its
membership is constant along every edge avoiding it. Both conditions are
needed when collapsing a component to the centroid's side of a cut. -/
def IsCentroidBranch (T : RootedTree N) (c : N) (C : Finset N) : Prop :=
  c ∉ C ∧ ∀ v, v ≠ T.root → v ≠ c → T.parent v ≠ c → (v ∈ C ↔ T.parent v ∈ C)

theorem separatorPart_excludes_centroid (T : RootedTree N) (c : N) {C : Finset N}
    (hC : C ∈ DirectedCertificate.Completion.separatorParts (centroidTree T) Finset.univ c) :
    c ∉ C := by
  rcases DirectedCertificate.Completion.separatorParts_cases (centroidTree T)
    Finset.univ c hC with rfl | ⟨v, hv, hp, rfl⟩
  · intro hc
    exact (Finset.mem_sdiff.mp hc).2
      (TwoRespecting.RootedTree.self_mem_subtree (T := centroidTree T) c)
  · intro hc
    have hanc : (centroidTree T).IsAnc v c :=
      TwoRespecting.RootedTree.mem_subtree.mp (Finset.mem_inter.mp hc).2
    have hdepth := hanc.depth_le
    have hstep := (centroidTree T).depth_parent v hv
    rw [hp] at hstep
    omega

theorem separatorPart_isCentroidBranch (T : RootedTree N) (c : N) {C : Finset N}
    (hC : C ∈ DirectedCertificate.Completion.separatorParts (centroidTree T) Finset.univ c) :
    IsCentroidBranch T c C := by
  refine ⟨separatorPart_excludes_centroid T c hC, ?_⟩
  intro v _ hvc hpc
  exact DirectedCertificate.Completion.separatorParts_parent_iff (centroidTree T)
    Finset.univ c hC (Finset.mem_univ _) (Finset.mem_univ _) hvc hpc rfl

def collapseBranch (c : N) (C A : Finset N) : Finset N :=
  if c ∈ A then A ∪ C else A \ C

theorem mem_collapseBranch (c : N) (C A : Finset N) (v : N) :
    v ∈ collapseBranch c C A ↔ if v ∈ C then c ∈ A else v ∈ A := by
  by_cases hc : c ∈ A <;> by_cases hv : v ∈ C <;> simp [collapseBranch, hc, hv]

theorem collapseBranch_crossSet (T : RootedTree N) (c : N) (C A : Finset N)
    (hC : IsCentroidBranch T c C) :
    T.crossSet (collapseBranch c C A) =
      (T.crossSet A).filter (fun v => v ∉ C ∧ T.parent v ∉ C) := by
  ext v
  by_cases hvr : v = T.root
  · simp [RootedTree.crossSet, RootedTree.Crosses, hvr]
  have hmixed : (v ∈ C ∧ T.parent v ∉ C) ∨ (v ∉ C ∧ T.parent v ∈ C) →
      v = c ∨ T.parent v = c := by
    intro hm
    by_contra hn
    push_neg at hn
    have h := hC.2 v hvr hn.1 hn.2
    tauto
  simp only [RootedTree.crossSet, RootedTree.Crosses, Finset.mem_filter,
    Finset.mem_univ, true_and, hvr, not_false_eq_true, true_and, mem_collapseBranch]
  by_cases hv : v ∈ C <;> by_cases hp : T.parent v ∈ C
  · simp [hv, hp]
  · have he := hmixed (Or.inl ⟨hv, hp⟩)
    rcases he with he | he
    · exact (hC.1 (he ▸ hv)).elim
    · simp [hv, hp, he]
  · have he := hmixed (Or.inr ⟨hv, hp⟩)
    rcases he with he | he
    · subst v
      simp [hC.1, hp]
    · exact (hC.1 (he ▸ hp)).elim
  · simp [hv, hp]

theorem collapseBranch_crossing_le (T : RootedTree N) (c : N) (C A : Finset N)
    (hC : IsCentroidBranch T c C) :
    (T.crossSet (collapseBranch c C A)).card ≤ (T.crossSet A).card := by
  rw [collapseBranch_crossSet T c C A hC]
  exact Finset.card_filter_le _ _

/-- An actually removed crossing edge pays for the decrease in `k`. -/
theorem collapseBranch_crossing_decreases (T : RootedTree N) (c : N) (C A : Finset N)
    (hC : IsCentroidBranch T c C) {e : N} (he : e ∈ T.crossSet A)
    (heC : e ∈ C ∨ T.parent e ∈ C) :
    (T.crossSet (collapseBranch c C A)).card ≤ (T.crossSet A).card - 1 := by
  have hsub : T.crossSet (collapseBranch c C A) ⊆ (T.crossSet A).erase e := by
    rw [collapseBranch_crossSet T c C A hC]
    intro v hv
    obtain ⟨hvA, hvC, hpC⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_erase.mpr
    refine ⟨?_, hvA⟩
    intro hve
    subst v
    exact heC.elim hvC hpC
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_erase_of_mem he)

theorem GuideTree.retain_branch_respects (T : GuideTree V N) (C : Finset N)
    (hC : IsCentroidBranch T.tree T.centroid C) (s : N) (hs : s ∈ T.real ∩ Cᶜ)
    {S : Finset V} {A : Finset N} {k : ℕ}
    (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S)
    (hcross : (T.tree.crossSet A).card ≤ k) {e : N} (he : e ∈ T.tree.crossSet A)
    (heC : e ∈ C ∨ T.tree.parent e ∈ C) :
    (T.retain Cᶜ s hs).RespectsCut S (k - 1) := by
  refine ⟨collapseBranch T.centroid C A, ?_, ?_⟩
  · intro v hv
    obtain ⟨hvr, hvC⟩ := Finset.mem_inter.mp hv
    have hnC := Finset.mem_compl.mp hvC
    change v ∈ collapseBranch T.centroid C A ↔ T.label v ∈ S
    simpa only [mem_collapseBranch, hnC, ite_false] using hA v hvr
  · exact (collapseBranch_crossing_decreases T.tree T.centroid C A hC he heC).trans
      (Nat.sub_le_sub_right hcross 1)

/-- Add a leaf at a public tree node; the leaf is the new `none` vertex. -/
def addProxyTree (T : RootedTree N) (a : N) : RootedTree (Option N) where
  root := some T.root
  parent v := match v with | none => some a | some x => some (T.parent x)
  depth v := match v with | none => T.depth a + 1 | some x => T.depth x
  parent_root := by simp [T.parent_root]
  depth_root := T.depth_root
  depth_parent v hv := by
    cases v with
    | none => rfl
    | some x => exact T.depth_parent x (fun h => hv (congrArg some h))

theorem addProxyTree_crossSet (T : RootedTree N) (a : N) (A : Finset N) (ha : a ∉ A) :
    (addProxyTree T a).crossSet (A.image some) = (T.crossSet A).image some := by
  ext v
  simp only [RootedTree.crossSet, Finset.mem_filter, Finset.mem_univ, true_and]
  cases v with
  | none =>
    change ((none : Option N) ≠ some T.root ∧
      ¬(none ∈ A.image some ↔ some a ∈ A.image some)) ↔
      none ∈ (T.crossSet A).image some
    simp [ha]
  | some v =>
    change (some v ≠ some T.root ∧
      ¬(some v ∈ A.image some ↔ some (T.parent v) ∈ A.image some)) ↔
      some v ∈ (T.crossSet A).image some
    simp [RootedTree.crossSet, RootedTree.Crosses]

def GuideTree.addProxy (T : GuideTree V N) (P : Finset N) (hP : P ⊆ T.real)
    (S : Finset V) (hPS : ∀ v ∈ P, T.label v ∈ S) : GuideTree (ShoreVertex S) (Option N) where
  tree := addProxyTree T.tree T.centroid
  real := insert none (P.image some)
  label v := match v with
    | none => none
    | some x => if hx : x ∈ P then some ⟨T.label x, hPS x hx⟩ else none
  label_injective := by
    intro x hx y hy he
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        have hyP : y ∈ P := by simpa using hy
        simp [hyP] at he
    | some x =>
      have hxP : x ∈ P := by simpa using hx
      cases y with
      | none =>
        simp [hxP] at he
      | some y =>
        have hyP : y ∈ P := by simpa using hy
        simp only [hxP, hyP, dite_true, Option.some.injEq, Subtype.mk.injEq] at he
        exact congrArg some (T.label_injective (hP hxP) (hP hyP) he)
  sourceNode := if T.sourceNode ∈ P then some T.sourceNode else none
  source_real := by
    split
    next hs => exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨T.sourceNode, hs, rfl⟩)
    · exact Finset.mem_insert_self _ _

theorem GuideTree.addProxy_real_card (T : GuideTree V N) (P : Finset N) (hP : P ⊆ T.real)
    (S : Finset V) (hPS : ∀ v ∈ P, T.label v ∈ S) :
    (T.addProxy P hP S hPS).real.card = P.card + 1 := by
  change (insert none (P.image (some : N → Option N))).card = P.card + 1
  rw [Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective P (Option.some_injective N)]

theorem GuideTree.addProxy_source (T : GuideTree V N) (P : Finset N) (hP : P ⊆ T.real)
    (S : Finset V) (hPS : ∀ v ∈ P, T.label v ∈ S)
    (htrace : S ∩ T.realVertices = T.graphGroup P) :
    (T.addProxy P hP S hPS).source = shoreMap S T.source := by
  by_cases hsP : T.sourceNode ∈ P
  · simp [GuideTree.source, GuideTree.addProxy, hsP, shoreMap, hPS T.sourceNode hsP]
  · have hsS : T.source ∉ S := by
      intro hs
      have hmem : T.source ∈ T.graphGroup P := by
        rw [← htrace]
        exact Finset.mem_inter.mpr ⟨hs, T.source_mem⟩
      obtain ⟨v, hvP, he⟩ := Finset.mem_image.mp hmem
      have hvs : v = T.sourceNode := T.label_injective (hP hvP) T.source_real he
      exact hsP (hvs ▸ hvP)
    have hsS' : T.label T.sourceNode ∉ S := hsS
    simp [GuideTree.source, GuideTree.addProxy, hsP, shoreMap, hsS']

/-- Intersecting the graph cut with the isolating shore preserves the labels on
the retained real nodes. An excluded centroid makes the new proxy edge free. -/
theorem GuideTree.addProxy_respects (T : GuideTree V N) (P : Finset N) (hP : P ⊆ T.real)
    (S : Finset V) (hPS : ∀ v ∈ P, T.label v ∈ S) {C : Finset V} {A : Finset N} {k : ℕ}
    (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ C)
    (hc : T.centroid ∉ A) (hk : (T.tree.crossSet A).card ≤ k) :
    (T.addProxy P hP S hPS).RespectsCut (shorePush S (C ∩ S)) k := by
  refine ⟨A.image some, ?_, ?_⟩
  · intro v hv
    cases v with
    | none => simp [GuideTree.addProxy, shorePush]
    | some v =>
      have hvP : v ∈ P := by simpa only [GuideTree.addProxy, Finset.mem_insert,
        Option.some_ne_none, false_or, Finset.mem_image, Option.some.injEq,
        exists_eq_right] using hv
      simpa only [GuideTree.addProxy, hvP, dite_true, some_mem_shorePush,
        Finset.mem_image, Option.some.injEq, exists_eq_right, Finset.mem_inter,
        hPS v hvP, and_true] using hA v (hP hvP)
  · change ((addProxyTree T.tree T.centroid).crossSet (A.image some)).card ≤ k
    rw [addProxyTree_crossSet T.tree T.centroid A hc,
      Finset.card_image_of_injective _ (Option.some_injective N)]
    exact hk

end
end CutQueryComplexity.GHReduction
