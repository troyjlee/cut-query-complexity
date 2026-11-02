import CutQueryComplexity.GHReduction.RoundCutGeometry
import CutQueryComplexity.GHReduction.BlockRefinementCuts
import CutQueryComplexity.GHReduction.FrontierRoundState

/-! # The shores of the actual simultaneous frontier update

The guarded output still consists of pullbacks through the old frontier map.
This fact forces the public representative-based attachments to be constant
on each old branch. The new child edge shore then pulls back to precisely the
returned shore, even after every other block is refined in the same round.
Consequently minimum-cut witnesses propagate to the actual next BFS tree.
These witnesses justify future contractions; they do not alone assert that
the partial tree is already a Gomory–Hu tree.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B ι : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq ι]

theorem refinementCell_congr_membership (I : Finset ι) (S : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (v w : V) (hmem : ∀ i ∈ I, v ∈ S i ↔ w ∈ S i) :
    refinementCell I S v = refinementCell I S w := by
  cases hv : refinementCell I S v with
  | none =>
      have hw : refinementCell I S w = none :=
        (refinementCell_eq_none I S w).mpr (fun i hi hwi =>
          (refinementCell_eq_none I S v).mp hv i hi ((hmem i hi).mpr hwi))
      exact hw.symm
  | some i =>
      have hw : refinementCell I S w = some i :=
        (refinementCell_eq_some I S hdisj w i).mpr
          ((hmem i.val i.property).mp ((refinementCell_eq_some I S hdisj v i).mp hv))
      exact hw.symm

theorem checkedFrontierSplit_shore_pull (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) {levels : ℕ}
    (out : Option (SourcePivotOutput (FrontierVertex p T b) levels)) (v : V) :
    ∃ A : Finset (FrontierVertex p T b),
      (checkedFrontierSplit p hp T b out).shore v = pull (frontierMap p T b) A := by
  unfold checkedFrontierSplit normalizeBlockSplit
  split
  · cases out with
    | none =>
        refine ⟨∅, ?_⟩
        ext x
        simp [liftFrontierSplit, emptyBlockSplit, mem_pull]
    | some out => exact ⟨out.step.batch.shore (frontierMap p T b v), rfl⟩
  · refine ⟨∅, ?_⟩
    ext x
    simp [emptyBlockSplit, mem_pull]

theorem frontierMap_representative_other (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b c : B) (hc : c ≠ b) :
    frontierMap p T b (blockRepresentative p hp c) = Sum.inr (frontierProxy T b c hc) := by
  apply (frontierMap_eq_inr p T b _ _).mpr
  simpa only [blockRepresentative_mem] using mem_frontierProxy_branch T b c hc

theorem frontierMap_representative_fiber (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) (v : V) (hv : p v ≠ b) :
    frontierMap p T b (blockRepresentative p hp (p v)) = frontierMap p T b v := by
  rw [frontierMap_representative_other p hp T b (p v) hv]
  exact ((frontierMap_eq_inr p T b v _).mpr (mem_frontierProxy_branch T b (p v) hv)).symm

theorem frontierMap_representative_parent (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) {e : B} (he : e ≠ T.root)
    (heb : e ≠ b) (hpb : T.parent e ≠ b) :
    frontierMap p T b (blockRepresentative p hp e) =
      frontierMap p T b (blockRepresentative p hp (T.parent e)) := by
  rw [frontierMap_representative_other p hp T b e heb,
    frontierMap_representative_other p hp T b (T.parent e) hpb,
    frontierProxy_parent T b he heb hpb]

def roundSplitAttachment (p : V → B) (hp : Function.Surjective p)
    (I : B → Finset ι) (S : B → ι → Finset V) (b c : B) : Option (I b) :=
  refinementCell (I b) (S b) (blockRepresentative p hp c)

theorem roundSplitAttachment_parent (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (I : B → Finset ι) (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b), S b i = pull (frontierMap p T b) A)
    (b : B) {e : B} (he : e ≠ T.root) (heb : e ≠ b) (hpb : T.parent e ≠ b) :
    roundSplitAttachment p hp I S b e = roundSplitAttachment p hp I S b (T.parent e) := by
  apply refinementCell_congr_membership (I b) (S b) (hdisj b)
  intro i _
  obtain ⟨A, hA⟩ := hpull b i
  rw [hA, mem_pull, mem_pull, frontierMap_representative_parent p hp T b he heb hpb]

/-- Refining the other old blocks cannot change this shore: their entire
old branches already shared a single proxy in the queried auxiliary graph. -/
theorem roundChildShore_pull (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (I : B → Finset ι) (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b), S b i = pull (frontierMap p T b) A)
    (b : B) (i : I b) :
    pull (roundBlockMap p I S) (roundChildShore I (roundSplitAttachment p hp I S) b i) = S b i.val := by
  ext v
  rw [mem_pull]
  by_cases hv : p v = b
  · rw [roundBlockMap_of_fiber p I S v b hv]
    exact (mem_roundChildShore_same I (roundSplitAttachment p hp I S) b i
      (refinementCell (I b) (S b) v)).trans (refinementCell_eq_some (I b) (S b) (hdisj b) v i)
  · change (⟨p v, refinementCell (I (p v)) (S (p v)) v⟩ : RoundBlock I) ∈
        roundChildShore I (roundSplitAttachment p hp I S) b i ↔ v ∈ S b i.val
    rw [mem_roundChildShore_other I (roundSplitAttachment p hp I S) b i hv]
    change refinementCell (I b) (S b) (blockRepresentative p hp (p v)) = some i ↔ v ∈ S b i.val
    rw [refinementCell_eq_some (I b) (S b) (hdisj b)]
    obtain ⟨A, hA⟩ := hpull b i.val
    rw [hA, mem_pull, mem_pull, frontierMap_representative_fiber p hp T b v hv]

theorem roundEdgeShore_minCut_witness (G : WeightedGraph V)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (I : B → Finset ι) (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b), S b i = pull (frontierMap p T b) A)
    (hold : ∀ e, e ≠ T.root → ∃ s t, IsSTMinCut G s t (pull p (T.D e)))
    (hnew : ∀ b i, i ∈ I b → ∃ s t, IsSTMinCut G s t (S b i))
    {d : RoundBlock I × RoundBlock I}
    (hd : d ∈ roundEdges T I (roundSplitAttachment p hp I S)) :
    ∃ s t, IsSTMinCut G s t
      (pull (roundBlockMap p I S) (roundEdgeShore T I (roundSplitAttachment p hp I S) d)) := by
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    have he0 : e ≠ T.root := (Finset.mem_erase.mp he).1
    rw [roundEdgeShore_old T I _ he0, roundBlock_old_shore_pull]
    exact hold e he0
  · obtain ⟨⟨b, i⟩, _, rfl⟩ := Finset.mem_image.mp hd
    rw [roundEdgeShore_star, roundChildShore_pull p hp T I S hdisj hpull]
    exact hnew b i.val i.property

theorem roundBlockTree_minCut_witness (G : WeightedGraph V)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (I : B → Finset ι) (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b), S b i = pull (frontierMap p T b) A)
    (hold : ∀ e, e ≠ T.root → ∃ s t, IsSTMinCut G s t (pull p (T.D e)))
    (hnew : ∀ b i, i ∈ I b → ∃ s t, IsSTMinCut G s t (S b i))
    {v : RoundBlock I} (hv : v ≠ (roundBlockTree T I (roundSplitAttachment p hp I S)).root) :
    ∃ s t, IsSTMinCut G s t
      (pull (roundBlockMap p I S) ((roundBlockTree T I (roundSplitAttachment p hp I S)).D v)) := by
  let a := roundSplitAttachment p hp I S
  have hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e) := by
    intro b e he heb hpb
    exact roundSplitAttachment_parent p hp T I S hdisj hpull b he heb hpb
  obtain ⟨s, t, hcut⟩ := roundEdgeShore_minCut_witness G p hp T I S hdisj hpull hold hnew
    (selectedParentEdge_mem (roundBlockTree T I a) (roundEdges T I a)
      (roundBlockTree_parent_adj T I a hv))
  rcases roundBlockTree_fundamental T I a hconstant hv with he | he
  · refine ⟨s, t, ?_⟩
    change IsSTMinCut G s t (pull (roundBlockMap p I S) ((roundBlockTree T I a).D v))
    rw [he]
    exact hcut
  · refine ⟨t, s, ?_⟩
    change IsSTMinCut G t s (pull (roundBlockMap p I S) ((roundBlockTree T I a).D v))
    rw [he, pull_compl]
    exact stMinCut_compl G hcut

end
end CutQueryComplexity.GHReduction
