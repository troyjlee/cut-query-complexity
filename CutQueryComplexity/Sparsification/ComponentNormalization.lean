import CutQueryComplexity.Sparsification.StrengthCoefficients
import CutQueryComplexity.Sparsification.StrengthSum

/-! # Normalized minimum cuts inside strong components

Normalizing the original edge weights by pair strength gives minimum induced
cut exactly one on every nontrivial strong component. Using induced cuts is
essential: vertices outside the component stay isolated in the public type.
-/

namespace CutQueryComplexity
namespace WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem localCut_induce_self (G : WeightedGraph V) (U S : Finset V) :
    (G.induce U).localCut U S = G.localCut U S := by
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  change (if u ∈ U ∧ v ∈ U then G.w u v else 0) = G.w u v
  exact ite_eq_left ⟨(Finset.mem_inter.mp hu).2, (Finset.mem_sdiff.mp hv).1⟩

theorem inducedMincut_induce_self (G : WeightedGraph V) (U : Finset V) :
    (G.induce U).inducedMincut U = G.inducedMincut U := by
  have he : (G.induce U).localCut U = G.localCut U :=
    funext (G.localCut_induce_self U)
  simp only [inducedMincut, he]

omit [Fintype V] in
theorem localCut_scale (G : WeightedGraph V) (c : ℝ) (hc : 0 ≤ c) (U S : Finset V) :
    (G.scale c hc).localCut U S = c * G.localCut U S := by
  simp only [localCut, cross, scale, Finset.mul_sum]

theorem inducedMincut_scale (G : WeightedGraph V) (c : ℝ) (hc : 0 ≤ c) (U : Finset V) :
    (G.scale c hc).inducedMincut U = c * G.inducedMincut U := by
  by_cases hn : 2 ≤ U.card
  · apply le_antisymm
    · obtain ⟨S, hS, he⟩ := G.exists_inducedMincut hn
      calc
        _ ≤ (G.scale c hc).localCut U S := (G.scale c hc).inducedMincut_le hS
        _ = _ := by rw [G.localCut_scale, he]
    · obtain ⟨S, hS, he⟩ := (G.scale c hc).exists_inducedMincut hn
      rw [← he, G.localCut_scale]
      exact mul_le_mul_of_nonneg_left (G.inducedMincut_le hS) hc
  · have hsmall : U.card ≤ 1 := by omega
    rw [(G.scale c hc).inducedMincut_eq_zero_of_card_le_one hsmall,
      G.inducedMincut_eq_zero_of_card_le_one hsmall, mul_zero]

/-- BK Lemma 4.10 on a component's own vertices, even when the full graph is disconnected. -/
theorem normalized_component_mincut_eq_one (G : WeightedGraph V) {U : Finset V}
    (hU : U ∈ G.strongComponents) : G.strengthNormalized.inducedMincut U = 1 := by
  have hn := ((G.mem_strongComponents U).mp hU).1
  apply le_antisymm
  · obtain ⟨S, hS, hc⟩ := G.exists_normalized_localCut_le_one U hn
    exact (G.strengthNormalized.inducedMincut_le hS).trans hc
  · obtain ⟨S, hS, he⟩ := G.strengthNormalized.exists_inducedMincut hn
    rw [← he]
    have hp : 0 < G.localCut U S :=
      (G.strongComponents_mincut_pos hU).trans_le (G.inducedMincut_le hS)
    calc
      1 = G.localCut U S / G.localCut U S := (div_self (ne_of_gt hp)).symm
      _ = ∑ u ∈ S ∩ U, ∑ v ∈ U \ S, G.w u v / G.localCut U S := by
        simp only [localCut, cross, div_eq_mul_inv, Finset.sum_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        change G.w u v / G.localCut U S ≤ G.w u v / G.strength u v
        by_cases hz : G.w u v = 0
        · simp [hz]
        · exact div_le_div_of_nonneg_left (G.nonneg u v)
            (G.strength_pos_of_weight_pos (lt_of_le_of_ne (G.nonneg u v) (Ne.symm hz)))
            (G.strongComponents_strength_le_localCut hU hu hv)

end
end WeightedGraph
end CutQueryComplexity
