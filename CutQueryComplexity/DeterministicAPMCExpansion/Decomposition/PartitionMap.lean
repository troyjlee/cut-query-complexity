import CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.Semantics

/-!
# A representative map from the actual output tree

This conversion consumes only the public tree and its set invariants. It
does not choose a partition by inspecting the hidden graph. Empty leaves
are discarded by `Finpartition`, and each nonempty leaf gets one label.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def mergePartitions {L U : Finset V} (left : Finpartition L) (right : Finpartition U)
    (hd : Disjoint L U) : Finpartition (L ∪ U) where
  parts := left.parts ∪ right.parts
  supIndep := left.supIndep.union right.supIndep (by
    simpa only [left.sup_parts, right.sup_parts] using hd)
  sup_parts := by rw [sup_union, left.sup_parts, right.sup_parts]; rfl
  bot_notMem := by
    intro h
    rcases mem_union.mp h with h | h
    · exact left.bot_notMem h
    · exact right.bot_notMem h

theorem disjoint_parts {L U : Finset V} (left : Finpartition L) (right : Finpartition U)
    (hd : Disjoint L U) : Disjoint left.parts right.parts := by
  apply disjoint_left.mpr
  intro W hl hr
  have hself : Disjoint W W := hd.mono (left.subset hl) (right.subset hr)
  exact left.ne_empty hl (disjoint_self.mp hself)

def SplitTree.partition : (tree : SplitTree V) → tree.DisjointSplits → Finpartition tree.vertices
  | .leaf W, _ => ⊤
  | .branch left right, h => mergePartitions
      (left.partition h.2.1) (right.partition h.2.2) h.1

theorem SplitTree.partition_expands (tree : SplitTree V) (G : WeightedGraph V) (R t : ℕ)
    (hd : tree.DisjointSplits) (he : tree.ExpandingLeaves G R t) :
    ∀ W ∈ (tree.partition hd).parts, AdditiveExpands G W (2 * t) (8 * R) (t ^ 2) := by
  induction tree with
  | leaf U =>
      intro W hW
      have hw : W = U := mem_singleton.mp (Finpartition.parts_top_subset U hW)
      simpa only [hw, SplitTree.ExpandingLeaves] using he
  | branch left right ihl ihr =>
      intro W hW
      change W ∈ (left.partition hd.2.1).parts ∪ (right.partition hd.2.2).parts at hW
      exact (mem_union.mp hW).elim (ihl hd.2.1 he.1 W) (ihr hd.2.2 he.2 W)

theorem SplitTree.partition_boundary_le (tree : SplitTree V) (G : WeightedGraph V)
    (hd : tree.DisjointSplits) :
    (∑ W ∈ (tree.partition hd).parts, G.cut W) ≤ tree.leafBoundary G := by
  induction tree with
  | leaf U =>
      calc
        _ ≤ ∑ W ∈ ({U} : Finset (Finset V)), G.cut W :=
          sum_le_sum_of_subset_of_nonneg (Finpartition.parts_top_subset U)
            (fun W _ _ => G.cut_nonneg W)
        _ = _ := by simp [SplitTree.leafBoundary]
  | branch left right ihl ihr =>
      change (∑ W ∈ (left.partition hd.2.1).parts ∪ (right.partition hd.2.2).parts,
        G.cut W) ≤ left.leafBoundary G + right.leafBoundary G
      rw [sum_union (disjoint_parts _ _ hd.1)]
      exact add_le_add (ihl hd.2.1) (ihr hd.2.2)

def representative (P : Finpartition (univ : Finset V)) (v : V) : V :=
  Classical.choose (P.part_nonempty.mpr (mem_univ v))

theorem representative_mem (P : Finpartition (univ : Finset V)) (v : V) :
    representative P v ∈ P.part v := Classical.choose_spec (P.part_nonempty.mpr (mem_univ v))

theorem representative_eq_of_part_eq (P : Finpartition (univ : Finset V))
    {u v : V} (h : P.part u = P.part v) : representative P u = representative P v := by
  simp only [representative, h]

theorem part_representative (P : Finpartition (univ : Finset V)) (v : V) :
    P.part (representative P v) = P.part v :=
  P.part_eq_of_mem (P.part_mem.mpr (mem_univ v)) (representative_mem P v)

theorem representative_idempotent (P : Finpartition (univ : Finset V)) (v : V) :
    representative P (representative P v) = representative P v :=
  representative_eq_of_part_eq P (part_representative P v)

theorem representative_fiber (P : Finpartition (univ : Finset V)) {b : V}
    (hb : representative P b = b) : fiber (representative P) b = P.part b := by
  ext x
  rw [mem_fiber, P.mem_part_iff_part_eq_part (mem_univ x) (mem_univ b)]
  constructor
  · intro hx
    exact (part_representative P x).symm.trans (congrArg P.part hx)
  · intro hx
    exact (representative_eq_of_part_eq P hx).trans hb

theorem representative_fiber_empty (P : Finpartition (univ : Finset V)) {b : V}
    (hb : representative P b ≠ b) : fiber (representative P) b = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx := (mem_fiber (representative P) b x).mp hx
  apply hb
  calc
    representative P b = representative P (representative P x) := congrArg (representative P) hx.symm
    _ = representative P x := representative_idempotent P x
    _ = b := hx

theorem representative_cut_sum (G : WeightedGraph V) (P : Finpartition (univ : Finset V)) :
    (∑ b, G.cut (fiber (representative P) b)) = ∑ W ∈ P.parts, G.cut W := by
  calc
    _ = ∑ b, if representative P b = b then G.cut (P.part b) else 0 := by
      apply sum_congr rfl
      intro b _
      by_cases hb : representative P b = b
      · simp [hb, representative_fiber P hb]
      · simp [hb, representative_fiber_empty P hb]
    _ = ∑ b ∈ univ.filter (fun b => representative P b = b), G.cut (P.part b) :=
      (sum_filter _ _).symm
    _ = ∑ W ∈ P.parts, G.cut W := by
      apply sum_bij (fun b _ => P.part b)
      · intro b _
        exact P.part_mem.mpr (mem_univ b)
      · intro b hb c hc hbc
        exact ((mem_filter.mp hb).2).symm.trans
          ((representative_eq_of_part_eq P hbc).trans (mem_filter.mp hc).2)
      · intro W hW
        obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hW
        refine ⟨representative P v,
          mem_filter.mpr ⟨mem_univ _, representative_idempotent P v⟩, ?_⟩
        rw [part_representative]
        exact P.part_eq_of_mem hW hv
      · intro _ _
        rfl

def State.partition {R : ℕ} (result : State R (univ : Finset V)) : Finpartition (univ : Finset V) :=
  (result.tree.partition result.disjoint).copy result.covers

def State.representativeMap {R : ℕ} (result : State R (univ : Finset V)) : V → V :=
  representative result.partition

theorem State.representativeMap_idempotent {R : ℕ} (result : State R (univ : Finset V)) (v : V) :
    result.representativeMap (result.representativeMap v) = result.representativeMap v :=
  representative_idempotent _ _

theorem State.representativeMap_additive (G : WeightedGraph V) {R : ℕ} (t : ℕ)
    (result : State R (univ : Finset V)) (h : result.Correct G t) :
    AdditivePartition G result.representativeMap (2 * t) (8 * R) (t ^ 2) := by
  intro v
  change AdditiveExpands G (fiber (representative result.partition) v) (2 * t) (8 * R) (t ^ 2)
  by_cases hv : representative result.partition v = v
  · rw [representative_fiber _ hv]
    exact result.tree.partition_expands G R t result.disjoint h.2.2 _
      (result.partition.part_mem.mpr (mem_univ v))
  · rw [representative_fiber_empty _ hv]
    intro T hT
    have he : T = ∅ := subset_empty.mp hT
    simp only [he, card_empty, sdiff_empty, Nat.cast_zero, min_self, mul_zero]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (G.localCut_nonneg _ _))
      (by positivity)

theorem State.representativeMap_boundary (G : WeightedGraph V) {R : ℕ} (t : ℕ)
    (result : State R (univ : Finset V)) (h : result.Correct G t) :
    (∑ v, G.cut (fiber result.representativeMap v)) ≤
      2 * ((2 * t : ℕ) : ℝ) * Fintype.card V * Nat.clog 2 (Fintype.card V) := by
  rw [State.representativeMap, representative_cut_sum]
  have hp := result.tree.partition_boundary_le G result.disjoint
  have hb := result.tree.leafBoundary_le G (2 * t) h.2.1
  have hf := hp.trans hb
  simpa only [State.partition, Finpartition.copy_parts, result.covers, cut_univ, zero_add,
    card_univ] using hf

end
end CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.representative_idempotent
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State.representativeMap_additive
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State.representativeMap_boundary
