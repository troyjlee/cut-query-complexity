import CutQueryComplexity.GHReduction.RoundForestGeometry
import Mathlib.Data.Finset.Pairwise

/-! # Successful backward assembly of one actual refined block

Every join guard is derived from the concrete next forest's terminal fibers
and attachment compatibility. The fold preserves both original-graph minimum
shores and all old attachment classes. Thus the compatibility premise used by
one reverse step is also its conclusion, suitable for induction from leaves.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def roundForestChild (I : B → Finset V) (forest : RoundBlock I → PackedSteinerTree V)
    (b : B) (i : V) : PackedSteinerTree V :=
  if hi : i ∈ I b then forest ⟨b, some ⟨i, hi⟩⟩ else forest ⟨b, none⟩

def roundForestAssemble (splits : B → PublicBlockSplit V)
    (forest : RoundBlock (fun b => (splits b).children) → PackedSteinerTree V)
    (b : B) : Option (PackedSteinerTree V) :=
  assembleDisjointStar (forest ⟨b, none⟩) (splits b).source
    (roundForestChild (fun b => (splits b).children) forest b)
    (splits b).shore (splits b).value (splits b).children.toList

theorem roundForestAssemble_success (G : WeightedGraph V) (p : V → B)
    (hp : Function.Surjective p) (T : RootedTree B) (splits : B → PublicBlockSplit V)
    (hvalid : ∀ b, ValidBlockSplit (fiber p b) (splits b))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b), (splits b).shore i = pull (frontierMap p T b) A)
    (hcuts : ∀ b i, i ∈ (splits b).children →
      IsSTMinCut G i (splits b).source ((splits b).shore i) ∧ (splits b).value i = G.cut ((splits b).shore i))
    (forest : RoundBlock (fun b => (splits b).children) → PackedSteinerTree V)
    (hcorrect : ∀ z, IsSteinerCutTree G (forest z).value)
    (hcover : ∀ z x, Represents (forest z) x ↔
      roundBlockMap p (fun b => (splits b).children) (fun b => (splits b).shore) x = z)
    (hcompatible : ForestCompatible
      (roundBlockMap p (fun b => (splits b).children) (fun b => (splits b).shore))
      (roundBlockTree T (fun b => (splits b).children)
        (roundSplitAttachment p hp (fun b => (splits b).children) (fun b => (splits b).shore))) forest)
    (b : B) : ∃ out, roundForestAssemble splits forest b = some out ∧
      IsSteinerCutTree G out.value ∧ (∀ x, Represents out x ↔ p x = b) ∧
      ∀ e, e ≠ T.root → ∀ x y,
        ¬(b ∈ T.D e ↔ p x ∈ T.D e) → ¬(b ∈ T.D e ↔ p y ∈ T.D e) →
          out.value.attach x = out.value.attach y := by
  let I := fun b => (splits b).children
  let S := fun b => (splits b).shore
  let child := roundForestChild I forest b
  let base := forest ⟨b, none⟩
  have hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j) :=
    fun b i hi j hj hij => (hvalid b).disjoint hi hj hij
  have hsource : p (splits b).source = b := (mem_fiber _ _ _).mp (hvalid b).source_mem
  have hbaseRep : Represents base (splits b).source := by
    apply (hcover ⟨b, none⟩ _).mpr
    exact (roundBlockMap_residual_iff p I S _ b).mpr ⟨hsource, (hvalid b).excludes⟩
  have hchildEq (i : V) (hi : i ∈ I b) : child i = forest ⟨b, some ⟨i, hi⟩⟩ := by
    exact dif_pos hi
  have hchildRep : ∀ i ∈ (I b).toList, Represents (child i) i := by
    intro i hi
    have himem : i ∈ I b := Finset.mem_toList.mp hi
    rw [hchildEq i himem]
    apply (hcover ⟨b, some ⟨i, himem⟩⟩ i).mpr
    exact (roundBlockMap_child_iff p I S hdisj i b ⟨i, himem⟩).mpr
      ⟨(mem_fiber _ _ _).mp (Finset.mem_erase.mp ((hvalid b).indices himem)).2,
        (hvalid b).contains i himem⟩
  have hchildInside : ∀ i ∈ (I b).toList, ∀ u, (child i).value.terminal u ∈ S b i := by
    intro i hi u
    have himem : i ∈ I b := Finset.mem_toList.mp hi
    have hrep : Represents (child i) ((child i).value.terminal u) := ⟨u, rfl⟩
    rw (occs := .pos [1]) [hchildEq i himem] at hrep
    exact ((roundBlockMap_child_iff p I S hdisj _ b ⟨i, himem⟩).mp ((hcover _ _).mp hrep)).2
  have hchildOutside : ∀ i ∈ (I b).toList, ∀ x, x ∉ S b i →
      (child i).value.attach x = (child i).value.attach (splits b).source := by
    intro i hi x hx
    have himem : i ∈ I b := Finset.mem_toList.mp hi
    have hr : (splits b).source ∉ S b i := (hvalid b).excludes i himem
    have hside : (⟨b, some ⟨i, himem⟩⟩ : RoundBlock I) ∈
        roundChildShore I (roundSplitAttachment p hp I S) b ⟨i, himem⟩ :=
      (mem_roundChildShore_same I _ b ⟨i, himem⟩ (some ⟨i, himem⟩)).mpr rfl
    rw [hchildEq i himem]
    apply roundForest_child_attach p hp T I S hdisj hpull forest hcompatible b ⟨i, himem⟩
      ⟨b, some ⟨i, himem⟩⟩ x (splits b).source
    · exact fun hiff => hx (hiff.mp hside)
    · exact fun hiff => hr (hiff.mp hside)
  have hbaseAvoid : ∀ i ∈ (I b).toList, ∀ u, base.value.terminal u ∉ S b i := by
    intro i hi u
    have hrep : Represents base (base.value.terminal u) := ⟨u, rfl⟩
    have hcell := (roundBlockMap_residual_iff p I S _ b).mp ((hcover ⟨b, none⟩ _).mp hrep)
    exact hcell.2 i (Finset.mem_toList.mp hi)
  have hbaseInside : ∀ i ∈ (I b).toList, ∀ x ∈ S b i, ∀ y ∈ S b i,
      base.value.attach x = base.value.attach y := by
    intro i hi x hx y hy
    have himem : i ∈ I b := Finset.mem_toList.mp hi
    have hside : (⟨b, none⟩ : RoundBlock I) ∉
        roundChildShore I (roundSplitAttachment p hp I S) b ⟨i, himem⟩ := by
      intro h
      have he := (mem_roundChildShore_same I _ b ⟨i, himem⟩ none).mp h
      cases he
    apply roundForest_child_attach p hp T I S hdisj hpull forest hcompatible b ⟨i, himem⟩
      ⟨b, none⟩ x y
    · exact fun hiff => hside (hiff.mpr hx)
    · exact fun hiff => hside (hiff.mpr hy)
  have hpairwise : (I b).toList.Pairwise (fun i j => Disjoint (S b i) (S b j)) := by
    apply List.pairwise_of_coe_toFinset_pairwise
    · rw [Finset.toList_toFinset]
      exact hdisj b
    · exact Finset.nodup_toList _
  obtain ⟨out, hout, houtCorrect, _, houtCover⟩ :=
    assembleDisjointStar_success G (splits b).source child (S b) (splits b).value (I b).toList
      base (hcorrect ⟨b, none⟩) hbaseRep hpairwise hchildRep hchildInside hchildOutside
      (by intro i hi; rw [hchildEq i (Finset.mem_toList.mp hi)]; exact hcorrect _)
      (fun i hi => (hcuts b i (Finset.mem_toList.mp hi)).1)
      (fun i hi => (hcuts b i (Finset.mem_toList.mp hi)).2) hbaseAvoid hbaseInside
  refine ⟨out, hout, houtCorrect, ?_, ?_⟩
  · intro x
    rw [houtCover x]
    constructor
    · rintro (hx | ⟨i, hi, hx⟩)
      · exact congrArg (roundBlockParent I) ((hcover ⟨b, none⟩ x).mp hx)
      · have himem : i ∈ I b := Finset.mem_toList.mp hi
        rw [hchildEq i himem] at hx
        exact congrArg (roundBlockParent I) ((hcover ⟨b, some ⟨i, himem⟩⟩ x).mp hx)
    · intro hx
      cases hc : refinementCell (I b) (S b) x with
      | none =>
          left
          apply (hcover ⟨b, none⟩ x).mpr
          rw [roundBlockMap_of_fiber p I S x b hx, hc]
      | some i =>
          right
          refine ⟨i.val, Finset.mem_toList.mpr i.property, ?_⟩
          rw [hchildEq i.val i.property]
          apply (hcover ⟨b, some i⟩ x).mpr
          rw [roundBlockMap_of_fiber p I S x b hx, hc]
  · intro e he x y hx hy
    apply assembleDisjointStar_attach (splits b).source child (S b) (splits b).value (I b).toList
      x y base out hout
    · exact roundForest_old_attach p hp T I S hdisj hpull forest hcompatible e he ⟨b, none⟩ x y hx hy
    · intro i hi
      have himem : i ∈ I b := Finset.mem_toList.mp hi
      rw [hchildEq i himem]
      exact roundForest_old_attach p hp T I S hdisj hpull forest hcompatible e he
        ⟨b, some ⟨i, himem⟩⟩ x y hx hy
    · intro i _
      obtain ⟨A, hA⟩ := hpull b i
      change S b i = pull (frontierMap p T b) A at hA
      rw [hA, mem_pull, mem_pull, frontierMap_opposite_edge p T b e he x y hx hy]

end
end CutQueryComplexity.GHReduction
