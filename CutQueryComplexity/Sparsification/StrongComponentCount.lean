import CutQueryComplexity.Sparsification.StrengthRestriction

/-! # Counting nontrivial strong components

The positive-threshold components, with singletons omitted, form a finite
family of at most `n-1` sets (BK Corollary 4.9). The proof splits an arbitrary
vertex set along a minimum induced cut: every proper strong component inside
that set lies entirely on one side. No connectedness or integrality is used.
-/

namespace CutQueryComplexity
namespace WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Distinct nontrivial components at all positive thresholds. -/
def strongComponents (G : WeightedGraph V) : Finset (Finset V) :=
  Finset.univ.filter fun U => 2 ≤ U.card ∧
    ∃ κ : ℝ, 0 < κ ∧ ∃ u : V, U = G.strongComponent κ u

@[simp] theorem mem_strongComponents (G : WeightedGraph V) (U : Finset V) :
    U ∈ G.strongComponents ↔ 2 ≤ U.card ∧
      ∃ κ : ℝ, 0 < κ ∧ ∃ u : V, U = G.strongComponent κ u := by
  simp [strongComponents]

theorem strongComponents_mincut_pos (G : WeightedGraph V) {U : Finset V}
    (hU : U ∈ G.strongComponents) : 0 < G.inducedMincut U := by
  obtain ⟨hn, κ, hκ, u, rfl⟩ := (G.mem_strongComponents U).mp hU
  exact hκ.trans_le ((G.isStrong_iff_le_inducedMincut hn κ).mp
    (G.strongComponent_strong κ u))

/-- A component is still maximal at its own induced minimum cut. -/
theorem strongComponents_at_mincut (G : WeightedGraph V) {U : Finset V}
    (hU : U ∈ G.strongComponents) {u : V} (hu : u ∈ U) :
    G.strongComponent (G.inducedMincut U) u = U := by
  obtain ⟨hn, κ, _, root, rfl⟩ := (G.mem_strongComponents U).mp hU
  have hκ := (G.isStrong_iff_le_inducedMincut hn κ).mp
    (G.strongComponent_strong κ root)
  apply Finset.Subset.antisymm
  · have he := G.strongComponent_eq_of_related
      ((G.mem_strongComponent κ root u).mp hu)
    simpa only [← he] using G.strongComponent_mono hκ u
  · exact (G.isStrong_inducedMincut _).subset_component hu

/-- A proper global strong component inside `U` cannot cross a minimum cut of `U`. -/
theorem strongComponents_subset_mincut_side (G : WeightedGraph V)
    {U S W : Finset V}
    (hc : G.localCut U S = G.inducedMincut U)
    (hW : W ∈ G.strongComponents) (hWU : W ⊆ U) (hne : W ≠ U) :
    W ⊆ S ∨ W ⊆ U \ S := by
  obtain ⟨_, κ, _, root, he⟩ := (G.mem_strongComponents W).mp hW
  have hr : root ∈ W := he ▸ G.mem_strongComponent_self κ root
  have hs : G.IsStrong κ W := he ▸ G.strongComponent_strong κ root
  have hκ : G.inducedMincut U < κ := by
    by_contra h
    have hsub := ((G.isStrong_inducedMincut U).mono (le_of_not_gt h)).subset_component
      (hWU hr)
    rw [← he] at hsub
    exact hne (Finset.Subset.antisymm hWU hsub)
  by_cases hleft : W ⊆ S
  · exact Or.inl hleft
  · right
    obtain ⟨v, hv, hvS⟩ := Finset.not_subset.mp hleft
    intro u hu
    refine Finset.mem_sdiff.mpr ⟨hWU hu, ?_⟩
    intro huS
    have h := (hs S ⟨u, Finset.mem_inter.mpr ⟨huS, hu⟩⟩
      ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvS⟩⟩).trans (G.localCut_mono hWU S)
    rw [hc] at h
    exact (not_le_of_gt hκ) h

theorem strongComponents_count_subset (G : WeightedGraph V) (U : Finset V)
    (hne : U.Nonempty) :
    (G.strongComponents.filter (fun W => W ⊆ U)).card ≤ U.card - 1 := by
  refine Finset.strongInductionOn U (fun U ih hne => ?_) hne
  by_cases hn : 2 ≤ U.card
  · obtain ⟨S, hS, hc⟩ := G.exists_inducedMincut hn
    have hleft := ih S hS.ssubset hS.2.1
    have hright := ih (U \ S) (Finset.sdiff_ssubset hS.1 hS.2.1) hS.2.2
    have hsub : G.strongComponents.filter (fun W => W ⊆ U) ⊆
        insert U ((G.strongComponents.filter (fun W => W ⊆ S)) ∪
          (G.strongComponents.filter (fun W => W ⊆ U \ S))) := by
      intro W hW
      obtain ⟨hW, hWU⟩ := Finset.mem_filter.mp hW
      by_cases he : W = U
      · simp [he]
      · apply Finset.mem_insert_of_mem
        rcases G.strongComponents_subset_mincut_side hc hW hWU he with hl | hr
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hW, hl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hW, hr⟩)
    have hcount := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hunion := Finset.card_union_le
      (G.strongComponents.filter (fun W => W ⊆ S))
      (G.strongComponents.filter (fun W => W ⊆ U \ S))
    have hcard := Finset.card_sdiff_add_card_eq_card hS.1
    have hlpos := hS.2.1.card_pos
    have hrpos := hS.2.2.card_pos
    omega
  · have he : G.strongComponents.filter (fun W => W ⊆ U) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro W hW
      obtain ⟨hW, hWU⟩ := Finset.mem_filter.mp hW
      have := (G.mem_strongComponents W).mp hW
      have := Finset.card_le_card hWU
      omega
    simp [he]

/-- BK Corollary 4.9, including the empty vertex type. -/
theorem strongComponents_card_le (G : WeightedGraph V) :
    G.strongComponents.card ≤ Fintype.card V - 1 := by
  by_cases hn : (Finset.univ : Finset V).Nonempty
  · simpa using G.strongComponents_count_subset Finset.univ hn
  · have he : (Finset.univ : Finset V) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hempty : G.strongComponents = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro U hU
      have hcard := (G.mem_strongComponents U).mp hU
      have hsub : U ⊆ (∅ : Finset V) := he ▸ Finset.subset_univ U
      have := Finset.card_le_card hsub
      simp only [Finset.card_empty] at this
      omega
    simp [hempty]

/-- Positive pair strength is the induced minimum cut of its own component. -/
theorem strength_component_mincut (G : WeightedGraph V) {u v : V}
    (hp : 0 < G.strength u v) :
    G.inducedMincut (G.strongComponent (G.strength u v) u) = G.strength u v := by
  have hne : u ≠ v := by intro he; simp [he] at hp
  have hv := (G.mem_strongComponent_iff_le_strength hne _).mpr le_rfl
  have hu := G.mem_strongComponent_self (G.strength u v) u
  have hn : 2 ≤ (G.strongComponent (G.strength u v) u).card := by
    have hsub : ({u, v} : Finset V) ⊆ G.strongComponent (G.strength u v) u := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hu, hv⟩
    simpa [hne] using Finset.card_le_card hsub
  exact le_antisymm (G.inducedMincut_le_strength hne hu hv)
    ((G.isStrong_iff_le_inducedMincut hn _).mp (G.strongComponent_strong _ _))

end
end WeightedGraph
end CutQueryComplexity
