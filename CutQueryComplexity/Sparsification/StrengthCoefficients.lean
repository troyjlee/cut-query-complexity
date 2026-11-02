import CutQueryComplexity.Sparsification.StrengthLevels

/-! # Positive coefficients for the BK strength decomposition

At each positive strength level, distribute its increment to that level's
nontrivial components. Grouping equal vertex sets gives one positive
coefficient per distinct strong component. For every positive-strength pair,
the coefficients of its containing components sum to its strength.
-/

namespace CutQueryComplexity
namespace WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

theorem strongComponents_strength_le_localCut (G : WeightedGraph V) {U S : Finset V}
    (hU : U ∈ G.strongComponents) {u v : V} (hu : u ∈ S ∩ U) (hv : v ∈ U \ S) :
    G.strength u v ≤ G.localCut U S := by
  obtain ⟨_, κ, _, root, rfl⟩ := (G.mem_strongComponents U).mp hU
  rw [← G.strength_induce_component κ root (Finset.mem_inter.mp hu).2
    (Finset.mem_sdiff.mp hv).1]
  simpa only [cut_induce, localCut] using
    (G.induce (G.strongComponent κ root)).strength_le_cut
      (Finset.mem_inter.mp hu).1 (Finset.mem_sdiff.mp hv).2

theorem strongComponents_mincut_mem_levels (G : WeightedGraph V) {U : Finset V}
    (hU : U ∈ G.strongComponents) : G.inducedMincut U ∈ G.positiveStrengths := by
  have hp := G.strongComponents_mincut_pos hU
  obtain ⟨S, _, hc⟩ := G.exists_inducedMincut ((G.mem_strongComponents U).mp hU).1
  have hcut : 0 < G.cross (S ∩ U) (U \ S) := by
    change 0 < G.localCut U S
    rwa [hc]
  obtain ⟨u, hu, v, hv, _⟩ := (G.cross_pos_iff _ _).mp hcut
  have hne : u ≠ v := by
    intro he
    exact (Finset.mem_sdiff.mp hv).2 (he ▸ (Finset.mem_inter.mp hu).1)
  apply (G.mem_positiveStrengths _).mpr
  refine ⟨hp, u, v, le_antisymm ?_ ?_⟩
  · exact (G.strongComponents_strength_le_localCut hU hu hv).trans_eq hc
  · exact G.inducedMincut_le_strength hne (Finset.mem_inter.mp hu).2
      (Finset.mem_sdiff.mp hv).1

/-- Whether a fixed vertex set occurs in the partition at this level. -/
def IsLevelComponent (G : WeightedGraph V) (κ : ℝ) (U : Finset V) : Prop :=
  ∃ root, U = G.strongComponent κ root

theorem IsLevelComponent.eq_component {G : WeightedGraph V} {κ : ℝ} {U : Finset V}
    (h : G.IsLevelComponent κ U) {u : V} (hu : u ∈ U) :
    U = G.strongComponent κ u := by
  obtain ⟨root, rfl⟩ := h
  exact G.strongComponent_eq_of_related ((G.mem_strongComponent κ root u).mp hu)

/-- Each distinct pair is in exactly one component at a level at most its strength. -/
theorem sum_levelComponent_pair (G : WeightedGraph V) {κ : ℝ} (hκ : 0 < κ)
    {u v : V} (hne : u ≠ v) (a : ℝ) :
    (∑ U ∈ G.strongComponents,
      if G.IsLevelComponent κ U ∧ u ∈ U ∧ v ∈ U then a else 0) =
        if κ ≤ G.strength u v then a else 0 := by
  by_cases hle : κ ≤ G.strength u v
  · rw [ite_eq_left hle]
    have hu := G.mem_strongComponent_self κ u
    have hv := (G.mem_strongComponent_iff_le_strength hne κ).mpr hle
    have hn : 2 ≤ (G.strongComponent κ u).card := by
      have hsub : ({u, v} : Finset V) ⊆ G.strongComponent κ u := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hu, hv⟩
      simpa [hne] using Finset.card_le_card hsub
    have hm : G.strongComponent κ u ∈ G.strongComponents :=
      (G.mem_strongComponents _).mpr ⟨hn, κ, hκ, u, rfl⟩
    rw [Finset.sum_eq_single (G.strongComponent κ u)]
    · exact ite_eq_left ⟨⟨u, rfl⟩, hu, hv⟩
    · intro U _ hneU
      apply ite_eq_right
      intro h
      exact hneU (h.1.eq_component h.2.1)
    · exact fun h => (h hm).elim
  · rw [ite_eq_right hle]
    apply Finset.sum_eq_zero
    intro U _
    apply ite_eq_right
    rintro ⟨⟨root, rfl⟩, hu, hv⟩
    exact hle ((G.strongComponent_strong κ root).le_strength hne hu hv)

/-- Total increment assigned to a component over all levels where it occurs. -/
def componentCoefficient (G : WeightedGraph V) (U : Finset V) : ℝ :=
  ∑ κ ∈ G.positiveStrengths,
    if G.IsLevelComponent κ U then κ - levelBelow G.positiveStrengths κ else 0

theorem componentCoefficient_nonneg (G : WeightedGraph V) (U : Finset V) :
    0 ≤ G.componentCoefficient U := by
  apply Finset.sum_nonneg
  intro κ hκ
  split
  · exact (sub_pos.mpr (levelBelow_lt _ ((G.mem_positiveStrengths κ).mp hκ).1)).le
  · exact le_rfl

theorem componentCoefficient_pos (G : WeightedGraph V) {U : Finset V}
    (hU : U ∈ G.strongComponents) : 0 < G.componentCoefficient U := by
  have hk := G.strongComponents_mincut_mem_levels hU
  have hp := G.strongComponents_mincut_pos hU
  have hn := ((G.mem_strongComponents U).mp hU).1
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  have hc : G.IsLevelComponent (G.inducedMincut U) U :=
    ⟨u, (G.strongComponents_at_mincut hU hu).symm⟩
  apply lt_of_lt_of_le (sub_pos.mpr (levelBelow_lt G.positiveStrengths hp))
  have h := Finset.single_le_sum
    (s := G.positiveStrengths)
    (f := fun κ => if G.IsLevelComponent κ U then κ - levelBelow G.positiveStrengths κ else 0)
    (fun κ hκ => by
      split
      · exact (sub_pos.mpr (levelBelow_lt _ ((G.mem_positiveStrengths κ).mp hκ).1)).le
      · exact le_rfl) hk
  simpa only [ite_eq_left hc, componentCoefficient] using h

/-- The decomposition's coefficients telescope simultaneously for all pairs. -/
theorem sum_componentCoefficients_pair (G : WeightedGraph V) {u v : V}
    (hp : 0 < G.strength u v) :
    (∑ U ∈ G.strongComponents, if u ∈ U ∧ v ∈ U then G.componentCoefficient U else 0) =
      G.strength u v := by
  have hne : u ≠ v := by intro he; simp [he] at hp
  calc
    _ = ∑ U ∈ G.strongComponents, ∑ κ ∈ G.positiveStrengths,
        if G.IsLevelComponent κ U ∧ u ∈ U ∧ v ∈ U then
          κ - levelBelow G.positiveStrengths κ else 0 := by
      apply Finset.sum_congr rfl
      intro U _
      by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;>
        simp [hu, hv, componentCoefficient]
    _ = ∑ κ ∈ G.positiveStrengths,
        if κ ≤ G.strength u v then κ - levelBelow G.positiveStrengths κ else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro κ hκ
      exact G.sum_levelComponent_pair ((G.mem_positiveStrengths κ).mp hκ).1 hne _
    _ = G.strength u v := by
      rw [← Finset.sum_filter]
      exact sum_levelIncrements_le _ (fun κ hκ => ((G.mem_positiveStrengths κ).mp hκ).1)
        ((G.mem_positiveStrengths _).mpr ⟨hp, u, v, rfl⟩)

end
end WeightedGraph
end CutQueryComplexity
