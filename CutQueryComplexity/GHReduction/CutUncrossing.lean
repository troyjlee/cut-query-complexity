import CutQueryComplexity.GHReduction.ShoreContraction
import CutQueryComplexity.GHReduction.CandidateLifting

/-! # Minimum-cut preservation in the actual guide children

Intersecting a minimum cut with its terminal group's minimum isolating shore
preserves the value and the complete real-terminal trace. No canonicality of
the respected minimum cut is assumed: the cut witnessing respect may differ
from the inclusion-minimal source cut.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem minCut_inter_isolating (G : WeightedGraph V) {R U S C : Finset V} {a b : V}
    (hC : IsSTMinCut G a b C) (hS : IsMinTraceCut G R U S)
    (htrace : C ∩ R ⊆ U) (haU : a ∈ U) :
    IsSTMinCut G a b (C ∩ S) ∧ G.cut (C ∩ S) = G.cut C ∧
      (C ∩ S) ∩ R = C ∩ R := by
  have haS : a ∈ S := by
    have : a ∈ S ∩ R := by rw [hS.1]; exact haU
    exact (Finset.mem_inter.mp this).1
  have haInt : a ∈ C ∩ S := Finset.mem_inter.mpr ⟨hC.1, haS⟩
  have hbInt : b ∉ C ∩ S := fun hb => hC.2.1 (Finset.mem_inter.mp hb).1
  have hUnion : (C ∪ S) ∩ R = U := by
    rw [Finset.union_inter_distrib_right, hS.1, Finset.union_eq_right.mpr htrace]
  have hsub := G.cut_submodular C S
  have hlow := hS.2 (C ∪ S) hUnion
  have hle : G.cut (C ∩ S) ≤ G.cut C := by linarith
  refine ⟨⟨haInt, hbInt, fun X haX hbX => hle.trans (hC.2.2 X haX hbX)⟩,
    le_antisymm hle (hC.2.2 _ haInt hbInt), ?_⟩
  calc
    _ = (C ∩ R) ∩ (S ∩ R) := by ext v; simp [and_assoc, and_left_comm, and_comm]
    _ = C ∩ R := by rw [hS.1, Finset.inter_eq_left.mpr htrace]

/-- A representable original minimum cut remains minimum in the quotient. -/
theorem minCut_contract_of_pull (G : WeightedGraph V) (π : V → W)
    {a b : V} {C : Finset V} (hC : IsSTMinCut G a b C)
    {X : Finset W} (hX : pull π X = C) : IsSTMinCut (G.contract π) (π a) (π b) X := by
  have ha : a ∈ pull π X := by rw [hX]; exact hC.1
  have hb : b ∉ pull π X := by rw [hX]; exact hC.2.1
  refine ⟨(mem_pull _ _ _).mp ha, fun h => hb ((mem_pull _ _ _).mpr h), fun Y haY hbY => ?_⟩
  have h := hC.2.2 (pull π Y) ((mem_pull _ _ _).mpr haY)
    (fun hb => hbY ((mem_pull _ _ _).mp hb))
  simpa only [cut_contract, hX] using h

/-- If at least one original optimum is representable, every quotient optimum
lifts to an original optimum, including its shore rather than merely its value. -/
theorem minCut_pull_of_representable (G : WeightedGraph V) (π : V → W)
    {a b : V} {C : Finset V} (hC : IsSTMinCut G a b C)
    {X Y : Finset W} (hX : pull π X = C)
    (hY : IsSTMinCut (G.contract π) (π a) (π b) Y) :
    IsSTMinCut G a b (pull π Y) := by
  have hXmin := minCut_contract_of_pull G π hC hX
  have hle := hY.2.2 X hXmin.1 hXmin.2.1
  rw [cut_contract, cut_contract, hX] at hle
  exact ⟨(mem_pull _ _ _).mpr hY.1,
    fun hb => hY.2.1 ((mem_pull _ _ _).mp hb),
    fun Z haZ hbZ => hle.trans (hC.2.2 Z haZ hbZ)⟩

theorem minCut_shorePush (G : WeightedGraph V) {S C : Finset V} {a b : V}
    (hC : IsSTMinCut G a b C) (hCS : C ⊆ S) :
    IsSTMinCut (G.contract (shoreMap S)) (shoreMap S a) (shoreMap S b) (shorePush S C) :=
  minCut_contract_of_pull G (shoreMap S) hC (pull_shorePush hCS)

theorem isolating_child_has_minCut (G : WeightedGraph V) {R U S C : Finset V} {a b : V}
    (hC : IsSTMinCut G a b C) (hS : IsMinTraceCut G R U S)
    (htrace : C ∩ R ⊆ U) (haU : a ∈ U) :
    IsSTMinCut (G.contract (shoreMap S)) (shoreMap S a) (shoreMap S b)
      (shorePush S (C ∩ S)) :=
  minCut_shorePush G (minCut_inter_isolating G hC hS htrace haU).1 Finset.inter_subset_right

theorem candidateExact_pull_of_representable (G : WeightedGraph V) (π : V → W)
    {s t : V} {A : Finset V} (hA : IsSTMinCut G t s A)
    {X : Finset W} (hX : pull π X = A) {C : CutCandidate W}
    (hC : CandidateExact (G.contract π) (π s) (π t) C) :
    CandidateExact G s t ⟨pull π C.shore, C.value⟩ :=
  ⟨minCut_pull_of_representable G π hA hX hC.1,
    by simpa only [cut_contract] using hC.2⟩

end
end CutQueryComplexity.GHReduction
