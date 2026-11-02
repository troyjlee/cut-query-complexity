import CutQueryComplexity.Graph.InducedCut
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# A partition constructed from an explicit weighted graph

Recursively split a block only when it violates the requested expansion.
The potential |W| * clog(2, |W|) pays for each split's added boundary weight.
Finally choose one representative in each part to obtain a public map V → V.

The only inputs of partitionMap are the explicit graph K and real threshold τ.
There is no hidden input graph, expansion oracle, or assumed decomposition.
This is an offline construction in the cut-query model; no running-time bound
for the finite choices is asserted.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairs

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Expansion is measured by cardinality inside the block, using actual cross weights. -/
def BlockExpands (K : WeightedGraph V) (τ : ℝ) (W : Finset V) : Prop :=
  ∀ A, A ⊆ W →
    τ * min (A.card : ℝ) ((W \ A).card : ℝ) ≤ K.cross A (W \ A)

private theorem clog_potential_split_le (a b : ℕ) (hab : a ≤ b) :
    a * Nat.clog 2 a + b * Nat.clog 2 b + a ≤
      (a + b) * Nat.clog 2 (a + b) := by
  by_cases ha : a = 0
  · simp [ha]
  have hn : 2 ≤ a + b := by omega
  have hsmall : Nat.clog 2 a + 1 ≤ Nat.clog 2 (a + b) := by
    rw [Nat.clog_of_two_le (show 1 < (2 : ℕ) by decide) hn]
    exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1
  have hlarge : Nat.clog 2 b ≤ Nat.clog 2 (a + b) :=
    Nat.clog_mono_right 2 (by omega)
  calc
    a * Nat.clog 2 a + b * Nat.clog 2 b + a =
        a * (Nat.clog 2 a + 1) + b * Nat.clog 2 b := by ring
    _ ≤ a * Nat.clog 2 (a + b) + b * Nat.clog 2 (a + b) :=
      add_le_add (Nat.mul_le_mul_left a hsmall) (Nat.mul_le_mul_left b hlarge)
    _ = (a + b) * Nat.clog 2 (a + b) := by ring

/-- The ceiling-log potential drops by at least the smaller child's size. -/
theorem clog_potential_split (a b : ℕ) :
    a * Nat.clog 2 a + b * Nat.clog 2 b + min a b ≤
      (a + b) * Nat.clog 2 (a + b) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact clog_potential_split_le a b hab
  · rw [min_eq_right hba]
    simpa [add_comm, add_left_comm, add_assoc] using clog_potential_split_le b a hba

/-- The real-valued cardinality potential used to charge recursive splits. -/
def partitionPotential (W : Finset V) : ℝ :=
  (W.card : ℝ) * (Nat.clog 2 W.card : ℝ)

omit [Fintype V] [DecidableEq V] in
private theorem partitionPotential_nonneg (W : Finset V) : 0 ≤ partitionPotential W :=
  mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [Fintype V] in
private theorem partitionPotential_split {W A : Finset V} (hA : A ⊆ W) :
    partitionPotential A + partitionPotential (W \ A) +
      min (A.card : ℝ) ((W \ A).card : ℝ) ≤ partitionPotential W := by
  have hc : A.card + (W \ A).card = W.card := by
    have := card_sdiff_add_card_eq_card hA
    omega
  have h := clog_potential_split A.card (W \ A).card
  rw [hc] at h
  unfold partitionPotential
  exact_mod_cast h

private def mergePartitions {A B : Finset V}
    (P : Finpartition A) (Q : Finpartition B) (hAB : Disjoint A B) :
    Finpartition (A ∪ B) where
  parts := P.parts ∪ Q.parts
  supIndep := P.supIndep.union Q.supIndep (by
    simpa only [P.sup_parts, Q.sup_parts] using hAB)
  sup_parts := by rw [sup_union, P.sup_parts, Q.sup_parts]; rfl
  bot_notMem := by
    intro h
    rcases mem_union.mp h with h | h
    · exact P.bot_notMem h
    · exact Q.bot_notMem h

omit [Fintype V] in
private theorem disjoint_partition_parts {A B : Finset V}
    (P : Finpartition A) (Q : Finpartition B) (hAB : Disjoint A B) :
    Disjoint P.parts Q.parts := by
  apply disjoint_left.mpr
  intro W hWP hWQ
  have hd : Disjoint W W := hAB.mono (P.subset hWP) (Q.subset hWQ)
  exact P.ne_empty hWP (disjoint_self.mp hd)

/-- Every block has an expanding refinement whose added boundary is charged
to its ceiling-log potential. This proves existence, rather than assuming it. -/
theorem exists_expandingPartition (K : WeightedGraph V) {τ : ℝ} (hτ : 0 ≤ τ)
    (W : Finset V) :
    ∃ P : Finpartition W,
      (∀ U ∈ P.parts, BlockExpands K τ U) ∧
      ∑ U ∈ P.parts, K.cut U ≤ K.cut W + 2 * τ * partitionPotential W := by
  refine Finset.strongInductionOn W ?_
  intro W ih
  by_cases hW : BlockExpands K τ W
  · refine ⟨⊤, ?_, ?_⟩
    · intro U hU
      have he : U = W := mem_singleton.mp (Finpartition.parts_top_subset W hU)
      simpa [he] using hW
    · have hcut : ∑ U ∈ (⊤ : Finpartition W).parts, K.cut U ≤ K.cut W := by
        calc
          _ ≤ ∑ U ∈ ({W} : Finset (Finset V)), K.cut U :=
            sum_le_sum_of_subset_of_nonneg (Finpartition.parts_top_subset W)
              (fun U _ _ => K.cut_nonneg U)
          _ = K.cut W := by simp
      exact hcut.trans (le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (by norm_num) hτ) (partitionPotential_nonneg W)))
  · unfold BlockExpands at hW
    push Not at hW
    obtain ⟨A, hA, hbad⟩ := hW
    have hmin : 0 < min (A.card : ℝ) ((W \ A).card : ℝ) := by
      by_contra hn
      have hm := mul_nonpos_of_nonneg_of_nonpos hτ (le_of_not_gt hn)
      have hc := K.cross_nonneg A (W \ A)
      linarith
    have ha : A.Nonempty := card_pos.mp (by exact_mod_cast (lt_min_iff.mp hmin).1)
    have hb : (W \ A).Nonempty := card_pos.mp (by exact_mod_cast (lt_min_iff.mp hmin).2)
    have hshore : LocalShore W A := ⟨hA, ha, hb⟩
    obtain ⟨P, hP, hPc⟩ := ih A hshore.ssubset
    obtain ⟨Q, hQ, hQc⟩ := ih (W \ A) hshore.compl.ssubset
    have hd : Disjoint A (W \ A) := disjoint_sdiff_self_right
    have hu : A ∪ (W \ A) = W := union_sdiff_of_subset hA
    let R : Finpartition W := (mergePartitions P Q hd).copy hu
    refine ⟨R, ?_, ?_⟩
    · intro U hU
      change U ∈ P.parts ∪ Q.parts at hU
      exact (mem_union.mp hU).elim (hP U) (hQ U)
    · have hs : (∑ U ∈ R.parts, K.cut U) =
          (∑ U ∈ P.parts, K.cut U) + ∑ U ∈ Q.parts, K.cut U := by
        exact sum_union (disjoint_partition_parts P Q hd)
      have hc := K.cross_eq_three_cuts hd
      rw [hu] at hc
      have hp := mul_le_mul_of_nonneg_left (partitionPotential_split hA)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hτ)
      rw [hs]
      nlinarith

private def publicPartition (K : WeightedGraph V) (τ : ℝ) :
    Finpartition (univ : Finset V) :=
  if hτ : 0 ≤ τ then Classical.choose (exists_expandingPartition K hτ univ) else ⊤

private theorem publicPartition_spec (K : WeightedGraph V) {τ : ℝ} (hτ : 0 ≤ τ) :
    (∀ U ∈ (publicPartition K τ).parts, BlockExpands K τ U) ∧
      ∑ U ∈ (publicPartition K τ).parts, K.cut U ≤
        K.cut univ + 2 * τ * partitionPotential (univ : Finset V) := by
  simp only [publicPartition, dite_eq_left hτ]
  exact Classical.choose_spec (exists_expandingPartition K hτ univ)

private def blockLabel (P : Finpartition (univ : Finset V)) (v : V) : V :=
  Classical.choose (P.part_nonempty.mpr (mem_univ v))

private theorem blockLabel_mem (P : Finpartition (univ : Finset V)) (v : V) :
    blockLabel P v ∈ P.part v :=
  Classical.choose_spec (P.part_nonempty.mpr (mem_univ v))

private theorem blockLabel_eq_of_part_eq (P : Finpartition (univ : Finset V))
    {u v : V} (h : P.part u = P.part v) : blockLabel P u = blockLabel P v := by
  simp only [blockLabel, h]

private theorem part_blockLabel (P : Finpartition (univ : Finset V)) (v : V) :
    P.part (blockLabel P v) = P.part v :=
  P.part_eq_of_mem (P.part_mem.mpr (mem_univ v)) (blockLabel_mem P v)

private theorem blockLabel_idempotent (P : Finpartition (univ : Finset V)) (v : V) :
    blockLabel P (blockLabel P v) = blockLabel P v :=
  blockLabel_eq_of_part_eq P (part_blockLabel P v)

private theorem blockLabel_fiber_eq (P : Finpartition (univ : Finset V)) {b : V}
    (hb : blockLabel P b = b) : fiber (blockLabel P) b = P.part b := by
  ext x
  rw [mem_fiber, P.mem_part_iff_part_eq_part (mem_univ x) (mem_univ b)]
  constructor
  · intro hx
    exact (part_blockLabel P x).symm.trans (congrArg P.part hx)
  · intro hx
    exact (blockLabel_eq_of_part_eq P hx).trans hb

private theorem blockLabel_fiber_empty (P : Finpartition (univ : Finset V)) {b : V}
    (hb : blockLabel P b ≠ b) : fiber (blockLabel P) b = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx := (mem_fiber (blockLabel P) b x).mp hx
  apply hb
  calc
    blockLabel P b = blockLabel P (blockLabel P x) := congrArg (blockLabel P) hx.symm
    _ = blockLabel P x := blockLabel_idempotent P x
    _ = b := hx

private theorem blockLabel_cut_sum (K : WeightedGraph V)
    (P : Finpartition (univ : Finset V)) :
    (∑ b, K.cut (fiber (blockLabel P) b)) = ∑ U ∈ P.parts, K.cut U := by
  calc
    _ = ∑ b, if blockLabel P b = b then K.cut (P.part b) else 0 := by
      apply sum_congr rfl
      intro b _
      by_cases hb : blockLabel P b = b
      · simp [hb, blockLabel_fiber_eq P hb]
      · simp [hb, blockLabel_fiber_empty P hb]
    _ = ∑ b ∈ univ.filter (fun b => blockLabel P b = b), K.cut (P.part b) :=
      (sum_filter _ _).symm
    _ = ∑ U ∈ P.parts, K.cut U := by
      apply sum_bij (fun b _ => P.part b)
      · intro b _
        exact P.part_mem.mpr (mem_univ b)
      · intro b hb c hc hbc
        exact ((mem_filter.mp hb).2).symm.trans
          ((blockLabel_eq_of_part_eq P hbc).trans (mem_filter.mp hc).2)
      · intro U hU
        obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hU
        refine ⟨blockLabel P v,
          mem_filter.mpr ⟨mem_univ _, blockLabel_idempotent P v⟩, ?_⟩
        rw [part_blockLabel]
        exact P.part_eq_of_mem hU hv
      · intro _ _
        rfl

private theorem blockLabel_expands (K : WeightedGraph V) (τ : ℝ)
    (P : Finpartition (univ : Finset V))
    (hP : ∀ U ∈ P.parts, BlockExpands K τ U) (b : V) :
    BlockExpands K τ (fiber (blockLabel P) b) := by
  by_cases hb : blockLabel P b = b
  · rw [blockLabel_fiber_eq P hb]
    exact hP _ (P.part_mem.mpr (mem_univ b))
  · rw [blockLabel_fiber_empty P hb]
    intro A hA
    have ha : A = ∅ := by simpa using hA
    simp [ha]

/-- A public block map, constructed from only the explicit graph and threshold. -/
def partitionMap (K : WeightedGraph V) (τ : ℝ) : V → V :=
  blockLabel (publicPartition K τ)

theorem partitionMap_idempotent (K : WeightedGraph V) (τ : ℝ) :
    ∀ v, partitionMap K τ (partitionMap K τ v) = partitionMap K τ v :=
  blockLabel_idempotent (publicPartition K τ)

/-- Every fiber satisfies the requested expansion, including unused empty fibers. -/
theorem partitionMap_expands (K : WeightedGraph V) {τ : ℝ} (hτ : 0 ≤ τ)
    (b : V) (A : Finset V) (hA : A ⊆ fiber (partitionMap K τ) b) :
    τ * min (A.card : ℝ) (((fiber (partitionMap K τ) b) \ A).card : ℝ) ≤
      K.cross A ((fiber (partitionMap K τ) b) \ A) :=
  blockLabel_expands K τ (publicPartition K τ) (publicPartition_spec K hτ).1 b A hA

/-- Total boundary counts every interblock edge twice. The bound requires no
degree, connectedness, integrality, or approximation assumption on K. -/
theorem partitionMap_boundary_le (K : WeightedGraph V) {τ : ℝ} (hτ : 0 ≤ τ) :
    (∑ b, K.cut (fiber (partitionMap K τ) b)) ≤
      2 * τ * (Fintype.card V : ℝ) * (Nat.clog 2 (Fintype.card V) : ℝ) := by
  change (∑ b, K.cut (fiber (blockLabel (publicPartition K τ)) b)) ≤ _
  rw [blockLabel_cut_sum]
  have h := (publicPartition_spec K hτ).2
  simpa [partitionPotential, mul_assoc] using h

#print axioms clog_potential_split
#print axioms exists_expandingPartition
#print axioms partitionMap_idempotent
#print axioms partitionMap_expands
#print axioms partitionMap_boundary_le

#check @partitionMap
#check @partitionMap_idempotent
#check @partitionMap_expands
#check @partitionMap_boundary_le

end
end CutQueryComplexity.AllPairs
