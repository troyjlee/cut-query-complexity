import CutQueryComplexity.AllPairsAudit.CutAlgebra
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic

/-!
# The actual small-cut partition

A block is split only at a proper induced cut of weight below the threshold.
Strong induction on its vertex set constructs the partition. Each split
contributes twice its weight to the sum of block boundaries, giving the strict
interpart estimate. Unit edge weights and minimum degree then bound the actual
number of blocks; the construction does not assume a packing or decomposition.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Counting

noncomputable section
open Finset WeightedGraph AllPairsAudit
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Internal connectivity, vacuous for singleton blocks. -/
def InternallyConnected (J : WeightedGraph V) (τ : ℝ) (U : Finset V) : Prop :=
  ∀ S, LocalShore U S → τ ≤ J.localCut U S

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

private theorem disjoint_partition_parts {A B : Finset V}
    (P : Finpartition A) (Q : Finpartition B) (hAB : Disjoint A B) :
    Disjoint P.parts Q.parts := by
  apply disjoint_left.mpr
  intro U hUP hUQ
  have hd : Disjoint U U := hAB.mono (P.subset hUP) (Q.subset hUQ)
  exact P.ne_empty hUP (disjoint_self.mp hd)

/-- Construct the blocks and charge every split to the final boundary sum. -/
theorem exists_connectedPartition (J : WeightedGraph V) (τ : ℝ)
    (C : Finset V) (hC : C.Nonempty) :
    ∃ P : Finpartition C,
      (∀ U ∈ P.parts, InternallyConnected J τ U) ∧
      (∑ U ∈ P.parts, J.cut U) ≤ J.cut C + 2 * τ * ((P.parts.card : ℝ) - 1) ∧
      (1 < P.parts.card →
        (∑ U ∈ P.parts, J.cut U) < J.cut C + 2 * τ * ((P.parts.card : ℝ) - 1)) := by
  revert hC
  refine Finset.strongInductionOn C ?_
  intro C ih hC
  by_cases hc : InternallyConnected J τ C
  · refine ⟨Finpartition.indiscrete hC.ne_empty, ?_, ?_, ?_⟩
    · intro U hU
      have he : U = C := mem_singleton.mp hU
      simpa only [he] using hc
    · simp [Finpartition.indiscrete]
    · simp [Finpartition.indiscrete]
  · unfold InternallyConnected at hc
    push_neg at hc
    obtain ⟨A, hA, hbad⟩ := hc
    obtain ⟨P, hP, hPc, _⟩ := ih A hA.ssubset hA.2.1
    obtain ⟨Q, hQ, hQc, _⟩ := ih (C \ A) hA.compl.ssubset hA.2.2
    have hd : Disjoint A (C \ A) := disjoint_sdiff_self_right
    have hu : A ∪ (C \ A) = C := union_sdiff_of_subset hA.1
    let R : Finpartition C := (mergePartitions P Q hd).copy hu
    have hpq : Disjoint P.parts Q.parts := disjoint_partition_parts P Q hd
    have hs : (∑ U ∈ R.parts, J.cut U) =
        (∑ U ∈ P.parts, J.cut U) + ∑ U ∈ Q.parts, J.cut U :=
      sum_union hpq
    have hcard : R.parts.card = P.parts.card + Q.parts.card :=
      card_union_of_disjoint hpq
    have hcross := J.cross_eq_three_cuts hd
    rw [hu] at hcross
    rw [J.localCut_of_subset hA.1] at hbad
    have hstrict : (∑ U ∈ R.parts, J.cut U) <
        J.cut C + 2 * τ * ((R.parts.card : ℝ) - 1) := by
      rw [hs, hcard, Nat.cast_add]
      nlinarith
    refine ⟨R, ?_, hstrict.le, fun _ => hstrict⟩
    intro U hU
    change U ∈ P.parts ∪ Q.parts at hU
    exact (mem_union.mp hU).elim (hP U) (hQ U)

/-- For a graph supported on the partitioned core this is exactly the total
weight between blocks: each such edge is counted at both endpoints. -/
def interpartMass (J : WeightedGraph V) {C : Finset V} (P : Finpartition C) : ℝ :=
  (∑ U ∈ P.parts, J.cut U) / 2

theorem supported_cut_eq_cross (J : WeightedGraph V) {C U : Finset V}
    (hJ : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0) (hU : U ⊆ C) :
    J.cut U = J.cross U (C \ U) := by
  apply sum_congr rfl
  intro u hu
  symm
  apply sum_subset (by intro v hv; exact mem_compl.mpr (mem_sdiff.mp hv).2)
  intro v hv hnot
  have hvC : v ∉ C := by
    intro hvC
    exact hnot (mem_sdiff.mpr ⟨hvC, mem_compl.mp hv⟩)
  exact hJ u v (Or.inr hvC)

theorem supported_core_cut_zero (J : WeightedGraph V) (C : Finset V)
    (hJ : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0) : J.cut C = 0 := by
  rw [supported_cut_eq_cross J hJ (Subset.refl C)]
  simp [cross]

theorem interpartMass_eq_cross (J : WeightedGraph V) {C : Finset V}
    (P : Finpartition C)
    (hJ : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0) :
    interpartMass J P = (∑ U ∈ P.parts, J.cross U (C \ U)) / 2 := by
  unfold interpartMass
  congr 1
  exact sum_congr rfl (fun U hU => supported_cut_eq_cross J hJ (P.subset hU))

/-- A single vertex of the block already suffices for this charging inequality. -/
theorem degree_le_block_card_add_cut (J : WeightedGraph V)
    (hJ : Unweighted J) {C U : Finset V} (hU : U ⊆ C) (hne : U.Nonempty)
    {D : ℝ} (hdeg : ∀ v ∈ C, D ≤ J.degree v) :
    D ≤ (U.card : ℝ) + J.cut U := by
  obtain ⟨v, hv⟩ := hne
  have hi : incident J v U ≤ (U.card : ℝ) := by
    calc
      _ ≤ ∑ _u ∈ U, (1 : ℝ) :=
        sum_le_sum (fun u _ => unweighted_edge_le_one hJ v u)
      _ = _ := by simp
  have ho : incident J v Uᶜ ≤ J.cut U := by
    simpa only [crossing, hv, ite_true] using crossing_le_cut J U v
  have he := incident_add_compl J v U
  have hd := hdeg v (hU hv)
  linarith

/-- Boundary mass controls the number of actual blocks, without identifying
the core size with the ambient vertex count. -/
theorem partition_card_le (J : WeightedGraph V) {C : Finset V}
    (P : Finpartition C) (hJ : Unweighted J) {D : ℝ} (hD : 0 < D)
    (hdeg : ∀ v ∈ C, D ≤ J.degree v)
    (hboundary : (∑ U ∈ P.parts, J.cut U) ≤
      D / 4 * ((P.parts.card : ℝ) - 1)) :
    (P.parts.card : ℝ) ≤ 4 * (C.card : ℝ) / D := by
  have hsum := sum_le_sum (s := P.parts) (fun U hU =>
    degree_le_block_card_add_cut J hJ (P.subset hU)
      (P.nonempty_of_mem_parts hU) hdeg)
  have hcards : (∑ U ∈ P.parts, (U.card : ℝ)) = (C.card : ℝ) := by
    exact_mod_cast P.sum_card_parts
  have hcharge : (P.parts.card : ℝ) * D ≤
      (C.card : ℝ) + ∑ U ∈ P.parts, J.cut U := by
    simpa only [sum_add_distrib, sum_const, nsmul_eq_mul, hcards] using hsum
  apply (le_div_iff₀ hD).mpr
  have hnonneg : 0 ≤ (P.parts.card : ℝ) * D :=
    mul_nonneg (Nat.cast_nonneg _) hD.le
  nlinarith

/-- The paper's partition is obtained from public core data alone. -/
theorem exists_corePartition (J : WeightedGraph V) (C : Finset V)
    (hC : C.Nonempty) (hJ : Unweighted J)
    (hsupp : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0)
    {D : ℕ} (hD : 2 ≤ D) (hdeg : ∀ v ∈ C, (D : ℝ) ≤ J.degree v) :
    ∃ P : Finpartition C,
      (∀ U ∈ P.parts, InternallyConnected J ((D : ℝ) / 8) U) ∧
      (P.parts.card : ℝ) ≤ 4 * (C.card : ℝ) / (D : ℝ) ∧
      (P.parts.card = 1 → interpartMass J P = 0) ∧
      (1 < P.parts.card → interpartMass J P <
        (D : ℝ) / 8 * ((P.parts.card : ℝ) - 1)) := by
  obtain ⟨P, hp, hb, hstrict⟩ := exists_connectedPartition J ((D : ℝ) / 8) C hC
  have hz := supported_core_cut_zero J C hsupp
  rw [hz, zero_add] at hb hstrict
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hb' : (∑ U ∈ P.parts, J.cut U) ≤
      (D : ℝ) / 4 * ((P.parts.card : ℝ) - 1) := by nlinarith [hb]
  refine ⟨P, hp, partition_card_le J P hJ hDr hdeg hb', ?_, ?_⟩
  · intro hq
    have hnonneg : 0 ≤ ∑ U ∈ P.parts, J.cut U :=
      sum_nonneg (fun U _ => J.cut_nonneg U)
    rw [hq] at hb
    simp only [Nat.cast_one, sub_self, mul_zero] at hb
    unfold interpartMass
    rw [le_antisymm hb hnonneg]
    norm_num
  · intro hq
    have hs := hstrict hq
    unfold interpartMass
    linarith

end
end CutQueryComplexity.CanonicalST.Counting

#print axioms CutQueryComplexity.CanonicalST.Counting.exists_connectedPartition
#print axioms CutQueryComplexity.CanonicalST.Counting.interpartMass_eq_cross
#print axioms CutQueryComplexity.CanonicalST.Counting.degree_le_block_card_add_cut
#print axioms CutQueryComplexity.CanonicalST.Counting.partition_card_le
#print axioms CutQueryComplexity.CanonicalST.Counting.exists_corePartition
