import CutQueryComplexity.Graph.InducedCut
import CutQueryComplexity.Graph.Integral

/-! # Induced edge mass and recursive cut bounds -/

namespace CutQueryComplexity
namespace WeightedGraph

noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Total unordered edge weight induced by `U`. -/
def internalMass (G : WeightedGraph V) (U : Finset V) : ℝ := G.cross U U / 2

theorem internalMass_nonneg (G : WeightedGraph V) (U : Finset V) :
    0 ≤ G.internalMass U := div_nonneg (G.cross_nonneg U U) (by norm_num)

@[simp] theorem internalMass_empty (G : WeightedGraph V) : G.internalMass ∅ = 0 :=
  by simp [internalMass]

@[simp] theorem internalMass_univ (G : WeightedGraph V) :
    G.internalMass Finset.univ = G.edgeMass := rfl

theorem internalMass_of_card_le_one (G : WeightedGraph V) {U : Finset V}
    (hn : U.card ≤ 1) : G.internalMass U = 0 := by
  unfold internalMass cross
  have he : ∑ u ∈ U, ∑ v ∈ U, G.w u v = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    rw [(Finset.card_le_one.mp hn) u hu v hv, G.diag]
  rw [he, zero_div]

theorem internalMass_union (G : WeightedGraph V) {S T : Finset V} (h : Disjoint S T) :
    G.internalMass (S ∪ T) = G.internalMass S + G.internalMass T + G.cross S T := by
  simp only [internalMass, G.cross_union_left S T _ h,
    G.cross_union_right _ S T h, G.cross_comm T S]
  ring

theorem internalMass_split (G : WeightedGraph V) {U S : Finset V} (h : S ⊆ U) :
    G.internalMass U = G.internalMass S + G.internalMass (U \ S) + G.localCut U S := by
  have hd : Disjoint S (U \ S) := Finset.disjoint_left.mpr
    (fun v hv hvs => (Finset.mem_sdiff.mp hvs).2 hv)
  rw [G.localCut_of_subset h, ← G.internalMass_union hd,
    Finset.union_sdiff_of_subset h]

/-- A reusable induction: uniformly cheap induced cuts bound total weight. -/
theorem internalMass_le_card_sub_one (G : WeightedGraph V)
    (hcut : ∀ U : Finset V, 2 ≤ U.card → ∃ S, LocalShore U S ∧ G.localCut U S ≤ 1)
    (U : Finset V) (hne : U.Nonempty) : G.internalMass U ≤ (U.card : ℝ) - 1 := by
  refine Finset.strongInductionOn U (fun U ih hne => ?_) hne
  by_cases hn : 2 ≤ U.card
  · obtain ⟨S, hS, hc⟩ := hcut U hn
    have hleft := ih S hS.ssubset hS.2.1
    have hright := ih (U \ S) (Finset.sdiff_ssubset hS.1 hS.2.1) hS.2.2
    have hcard : ((U \ S).card : ℝ) + S.card = U.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hS.1
    rw [G.internalMass_split hS.1]
    linarith
  · have he : U.card = 1 := by have := hne.card_pos; omega
    rw [G.internalMass_of_card_le_one (by omega), he]
    norm_num

end
end WeightedGraph
end CutQueryComplexity
