import CutQueryComplexity.GHReduction.BlockRefinementTree
import CutQueryComplexity.GHReduction.FrontierCutSafety
import CutQueryComplexity.GHReduction.TreeAssembly

/-! # Fundamental shores for a public block refinement

A child shore consists of its new block label and every old branch attached
to that label. Branch-constant attachments ensure that no old edge crosses a
child shore. Old shores pull back through the coarsening map and continue to
cross exactly their own retained edge. These facts identify the fundamental
shores of the actual public BFS tree.

The final attachment construction uses only accepted auxiliary shores and
their public proxy labels. Its child shores pull back exactly to the original
lifted auxiliary shores; hidden minimum-cut facts are used only afterwards.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {B ι : Type} [Fintype B] [DecidableEq B] [DecidableEq ι]

def refinementChildShore (b : B) (I : Finset ι) (a : B → Option I) (i : I) :
    Finset (RefinedBlock b I) :=
  Finset.univ.filter (fun z => match z with
    | Sum.inl c => a c.val = some i
    | Sum.inr j => j = some i)

@[simp] theorem mem_refinementChildShore_old (b : B) (I : Finset ι)
    (a : B → Option I) (i : I) (c : (Finset.univ.erase b : Finset B)) :
    Sum.inl c ∈ refinementChildShore b I a i ↔ a c.val = some i := by
  simp [refinementChildShore]

@[simp] theorem mem_refinementChildShore_new (b : B) (I : Finset ι)
    (a : B → Option I) (i : I) (j : Option I) :
    Sum.inr j ∈ refinementChildShore b I a i ↔ j = some i := by
  simp [refinementChildShore]

theorem refinedOldEdge_child_membership (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I)
    (hconstant : ∀ e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a e = a (T.parent e))
    {e : B} (he : e ≠ T.root) (i : I) :
    (refinedOldEdge T b I a e).1 ∈ refinementChildShore b I a i ↔
      (refinedOldEdge T b I a e).2 ∈ refinementChildShore b I a i := by
  by_cases heb : e = b
  · subst e
    have hpb : T.parent b ≠ b := parent_ne_child T he
    simp [refinedOldEdge, refinedEndpoint, hpb]
  · by_cases hpb : T.parent e = b
    · simp [refinedOldEdge, refinedEndpoint, heb, hpb]
    · simp [refinedOldEdge, refinedEndpoint, heb, hpb, hconstant e he heb hpb]

theorem refinementChildShore_edgeCut (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I)
    (hconstant : ∀ e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a e = a (T.parent e))
    (i : I) :
    (refinedStarEdge b I i).1 ∈ refinementChildShore b I a i ∧
    (refinedStarEdge b I i).2 ∉ refinementChildShore b I a i ∧
    ∀ d ∈ refinedEdges T b I a,
      ¬(d.1 ∈ refinementChildShore b I a i ↔ d.2 ∈ refinementChildShore b I a i) →
        d = refinedStarEdge b I i := by
  refine ⟨by simp [refinedStarEdge], by simp [refinedStarEdge], ?_⟩
  intro d hd hc
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact (hc (refinedOldEdge_child_membership T b I a hconstant
      (Finset.mem_erase.mp he).1 i)).elim
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
    have hji : j = i := by simpa [refinedStarEdge] using hc
    exact congrArg (refinedStarEdge b I) hji

theorem refinedOldShore_edgeCut (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) {e : B} (he : e ≠ T.root) :
    (refinedOldEdge T b I a e).1 ∈ pull (refinedBlockParent b I) (T.D e) ∧
    (refinedOldEdge T b I a e).2 ∉ pull (refinedBlockParent b I) (T.D e) ∧
    ∀ d ∈ refinedEdges T b I a,
      ¬(d.1 ∈ pull (refinedBlockParent b I) (T.D e) ↔
        d.2 ∈ pull (refinedBlockParent b I) (T.D e)) → d = refinedOldEdge T b I a e := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [refinedOldEdge, mem_pull, refinedBlockParent_endpoint] using T.self_mem_D e
  · simpa only [refinedOldEdge, mem_pull, refinedBlockParent_endpoint] using
      tree_parent_not_mem_subtree T he
  · intro d hd hc
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hd
      have hf0 : f ≠ T.root := (Finset.mem_erase.mp hf).1
      have hc' : ¬(f ∈ T.D e ↔ T.parent f ∈ T.D e) := by
        simpa only [refinedOldEdge, mem_pull, refinedBlockParent_endpoint] using hc
      by_cases hfe : f = e
      · exact congrArg (refinedOldEdge T b I a) hfe
      · have hef : e ≠ f := Ne.symm hfe
        have hm : f ∈ T.D e ↔ T.parent f ∈ T.D e := by
          simp only [RootedTree.mem_D, T.isAnc_iff_of_ne_root hf0, hef, false_or]
        exact (hc' hm).elim
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
      simp [refinedStarEdge, mem_pull, refinedBlockParent] at hc

/-- Public edge-shore lookup. The coarsened endpoints distinguish retained
old edges from the new child-to-residual edges. -/
def refinedEdgeShore (T : RootedTree B) (b : B) (I : Finset ι) (a : B → Option I)
    (d : RefinedBlock b I × RefinedBlock b I) : Finset (RefinedBlock b I) :=
  if refinedBlockParent b I d.1 = refinedBlockParent b I d.2 then
    match d.1 with
    | Sum.inr (some i) => refinementChildShore b I a i
    | _ => ∅
  else pull (refinedBlockParent b I) (T.D (refinedBlockParent b I d.1))

theorem refinedEdgeShore_old (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) {e : B} (he : e ≠ T.root) :
    refinedEdgeShore T b I a (refinedOldEdge T b I a e) =
      pull (refinedBlockParent b I) (T.D e) := by
  have hne : e ≠ T.parent e := (parent_ne_child T he).symm
  simp only [refinedEdgeShore, refinedOldEdge, refinedBlockParent_endpoint, if_neg hne]

theorem refinedEdgeShore_star (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I) (i : I) :
    refinedEdgeShore T b I a (refinedStarEdge b I i) = refinementChildShore b I a i := by
  simp [refinedEdgeShore, refinedStarEdge, refinedBlockParent]

theorem refinedEdgeShore_system (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I)
    (hconstant : ∀ e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a e = a (T.parent e)) :
    EdgeShoreSystem (refinedEdges T b I a) (refinedEdgeShore T b I a) := by
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    have he0 : e ≠ T.root := (Finset.mem_erase.mp he).1
    simpa only [refinedEdgeShore_old T b I a he0] using refinedOldShore_edgeCut T b I a he0
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    simpa only [refinedEdgeShore_star] using refinementChildShore_edgeCut T b I a hconstant i

theorem refinedBlockTree_fundamental (T : RootedTree B) (b : B) (I : Finset ι)
    (a : B → Option I)
    (hconstant : ∀ e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a e = a (T.parent e))
    {v : RefinedBlock b I} (hv : v ≠ (refinedBlockTree T b I a).root) :
    (refinedBlockTree T b I a).D v = refinedEdgeShore T b I a
      (selectedParentEdge (refinedBlockTree T b I a) (refinedEdges T b I a) v) ∨
    (refinedBlockTree T b I a).D v = (refinedEdgeShore T b I a
      (selectedParentEdge (refinedBlockTree T b I a) (refinedEdges T b I a) v))ᶜ :=
  edgeShore_fundamental _ _ (fun _ h => refinedBlockTree_parent_adj T b I a h)
    _ (refinedEdgeShore_system T b I a hconstant) hv

/-- An old edge not incident to the split block stays inside one of its
branches. This is proved from the old tree, not supplied as an invariant. -/
theorem frontierBranch_parent_mem_iff (T : RootedTree B) (b : B)
    {e : B} (he : e ≠ T.root) (heb : e ≠ b) (hpb : T.parent e ≠ b)
    (f : frontierProxies T b) :
    e ∈ frontierBranch T b f ↔ T.parent e ∈ frontierBranch T b f := by
  by_cases hfb : f.val = b
  · have hbe : b ≠ e := Ne.symm heb
    simp only [frontierBranch, hfb, ite_true, Finset.mem_compl, RootedTree.mem_D,
      T.isAnc_iff_of_ne_root he, hbe, false_or]
  · have hfparent : T.parent f.val = b :=
      ((mem_frontierProxies T b f.val).mp f.property).2.resolve_left hfb
    have hfe : f.val ≠ e := by
      intro h
      apply hpb
      simpa only [h] using hfparent
    simp only [frontierBranch, hfb, ite_false, RootedTree.mem_D,
      T.isAnc_iff_of_ne_root he, hfe, false_or]

theorem frontierProxy_parent (T : RootedTree B) (b : B)
    {e : B} (he : e ≠ T.root) (heb : e ≠ b) (hpb : T.parent e ≠ b) :
    frontierProxy T b e heb = frontierProxy T b (T.parent e) hpb := by
  apply (frontierProxy_eq_iff T b e heb (frontierProxy T b (T.parent e) hpb)).mpr
  exact (frontierBranch_parent_mem_iff T b he heb hpb _).mpr
    (mem_frontierProxy_branch T b (T.parent e) hpb)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Determine where each old branch attaches by inspecting its one public
proxy in the accepted auxiliary shores. The value at `b` is unused. -/
def auxiliaryAttachment (p : V → B) (T : RootedTree B) (b : B) (I : Finset ι)
    (S : ι → Finset (FrontierVertex p T b)) (c : B) : Option I :=
  if hc : c = b then none
  else refinementCell I S (Sum.inr (frontierProxy T b c hc))

theorem auxiliaryAttachment_parent (p : V → B) (T : RootedTree B) (b : B)
    (I : Finset ι) (S : ι → Finset (FrontierVertex p T b))
    {e : B} (he : e ≠ T.root) (heb : e ≠ b) (hpb : T.parent e ≠ b) :
    auxiliaryAttachment p T b I S e = auxiliaryAttachment p T b I S (T.parent e) := by
  simp only [auxiliaryAttachment, heb, hpb, dite_false]
  rw [frontierProxy_parent T b he heb hpb]

theorem auxiliaryAttachment_some_iff (p : V → B) (T : RootedTree B) (b : B)
    (I : Finset ι) (S : ι → Finset (FrontierVertex p T b))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (c : B) (hc : c ≠ b) (i : I) :
    auxiliaryAttachment p T b I S c = some i ↔
      (Sum.inr (frontierProxy T b c hc) : FrontierVertex p T b) ∈ S i.val := by
  unfold auxiliaryAttachment
  rw [dite_eq_right hc]
  exact refinementCell_eq_some I S hdisj (Sum.inr (frontierProxy T b c hc)) i

/-- The concrete attachment rule satisfies the full edge-shore system. -/
theorem auxiliaryAttachment_shore_system (p : V → B) (T : RootedTree B) (b : B)
    (I : Finset ι) (S : ι → Finset (FrontierVertex p T b)) :
    EdgeShoreSystem (refinedEdges T b I (auxiliaryAttachment p T b I S))
      (refinedEdgeShore T b I (auxiliaryAttachment p T b I S)) :=
  refinedEdgeShore_system T b I _
    (fun _ he heb hpb => auxiliaryAttachment_parent p T b I S he heb hpb)

theorem auxiliaryShore_pull_disjoint (p : V → B) (T : RootedTree B) (b : B)
    (I : Finset ι) (S : ι → Finset (FrontierVertex p T b))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (pull (frontierMap p T b) (S i)) (pull (frontierMap p T b) (S j)) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  exact Finset.disjoint_left.mp (hdisj i hi j hj hij)
    ((mem_pull _ _ _).mp hvi) ((mem_pull _ _ _).mp hvj)

/-- The new child edge represents exactly the accepted auxiliary shore after
lifting. In particular, no old proxy branch is lost or divided between cells. -/
theorem refinementChildShore_pull (p : V → B) (T : RootedTree B) (b : B)
    (I : Finset ι) (S : ι → Finset (FrontierVertex p T b))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) (i : I) :
    pull (refinedBlockMap p b I (fun j => pull (frontierMap p T b) (S j)))
      (refinementChildShore b I (auxiliaryAttachment p T b I S) i) =
        pull (frontierMap p T b) (S i.val) := by
  have hldisj := auxiliaryShore_pull_disjoint p T b I S hdisj
  ext v
  by_cases hv : p v = b
  · simp only [mem_pull, refinedBlockMap, hv, dite_true, mem_refinementChildShore_new]
    simpa only [mem_pull] using refinementCell_eq_some I
      (fun j => pull (frontierMap p T b) (S j)) hldisj v i
  · simp only [mem_pull, refinedBlockMap, hv, dite_false, mem_refinementChildShore_old]
    change auxiliaryAttachment p T b I S (p v) = some i ↔ frontierMap p T b v ∈ S i.val
    rw [(frontierMap_eq_inr p T b v (frontierProxy T b (p v) hv)).mpr
      (mem_frontierProxy_branch T b (p v) hv)]
    exact auxiliaryAttachment_some_iff p T b I S hdisj (p v) hv i

theorem refinementChild_cut (G : WeightedGraph V) (p : V → B) (T : RootedTree B)
    (b : B) (I : Finset ι) (S : ι → Finset (FrontierVertex p T b))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) (i : I) :
    G.cut (pull (refinedBlockMap p b I (fun j => pull (frontierMap p T b) (S j)))
      (refinementChildShore b I (auxiliaryAttachment p T b I S) i)) =
        (G.contract (frontierMap p T b)).cut (S i.val) := by
  rw [refinementChildShore_pull p T b I S hdisj i, cut_contract]

/-- Accepted auxiliary minimum cuts become witnesses for the exact new
child-edge shores. Existing branch witnesses discharge quotient cut safety. -/
theorem refinementChild_minCut (G : WeightedGraph V) (p : V → B) (T : RootedTree B)
    (b : B) (I : Finset ι) (S : ι → Finset (FrontierVertex p T b))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (r c : frontierProxies T b → V)
    (hcut : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e)))
    {s t : fiber p b} (i : I)
    (hS : IsSTMinCut (G.contract (frontierMap p T b)) (Sum.inl s) (Sum.inl t) (S i.val)) :
    IsSTMinCut G s.val t.val
      (pull (refinedBlockMap p b I (fun j => pull (frontierMap p T b) (S j)))
        (refinementChildShore b I (auxiliaryAttachment p T b I S) i)) := by
  rw [refinementChildShore_pull p T b I S hdisj i]
  exact frontier_minCut_lift G p T b r c hcut hS

end
end CutQueryComplexity.GHReduction
