import CutQueryComplexity.Sparsification.Strength

/-! # Strength under induced restriction and deletion of weak edges

These are the consistency properties needed by the BK decomposition and PRW
scale windows. In particular, strengths inside a strong component agree with
their original values, despite deleting all vertices outside the component.
-/

namespace CutQueryComplexity
namespace WeightedGraph

noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

theorem IsStrong.congr {G H : WeightedGraph V} {κ : ℝ} {U : Finset V}
    (h : G.IsStrong κ U) (he : ∀ u ∈ U, ∀ v ∈ U, H.w u v = G.w u v) :
    H.IsStrong κ U := by
  intro S hS hT
  have hc : H.localCut U S = G.localCut U S := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    exact he u (Finset.mem_inter.mp hu).2 v (Finset.mem_sdiff.mp hv).1
  rw [hc]
  exact h S hS hT

theorem induce_subgraph (G : WeightedGraph V) (U : Finset V) :
    (G.induce U).IsSubgraph G := by
  intro u v
  change (if u ∈ U ∧ v ∈ U then G.w u v else 0) ≤ G.w u v
  split <;> simp [G.nonneg]

theorem IsStrong.induce {G : WeightedGraph V} {κ : ℝ} {U W : Finset V}
    (h : G.IsStrong κ U) (hsub : U ⊆ W) : (G.induce W).IsStrong κ U :=
  h.congr (fun u hu v hv => by simp [WeightedGraph.induce, hsub hu, hsub hv])

/-- Every pair inside a strong set has at least that strength. -/
theorem IsStrong.le_strength {G : WeightedGraph V} {κ : ℝ} {U : Finset V}
    (h : G.IsStrong κ U) {u v : V} (hne : u ≠ v) (hu : u ∈ U) (hv : v ∈ U) :
    κ ≤ G.strength u v := (G.le_strength_iff hne κ).mpr ⟨U, h, hu, hv⟩

/-- Restricting to a strong component preserves strengths of all its pairs,
including nonedges. The assertion on the diagonal uses the zero convention. -/
theorem strength_induce_component (G : WeightedGraph V) (κ : ℝ) (root : V)
    {u v : V} (hu : u ∈ G.strongComponent κ root) (hv : v ∈ G.strongComponent κ root) :
    (G.induce (G.strongComponent κ root)).strength u v = G.strength u v := by
  apply le_antisymm ((G.induce_subgraph _).strength_le u v)
  by_cases hne : u = v
  · simp [hne]
  · have hs := (G.strongComponent_strong κ root).le_strength hne hu hv
    obtain ⟨U, huU, hvU, he⟩ := G.exists_strength_set hne
    have hU : G.IsStrong (G.strength u v) U := he ▸ G.isStrong_inducedMincut U
    have hsub : U ⊆ G.strongComponent κ root := by
      rw [G.strongComponent_eq_of_related ((G.mem_strongComponent κ root u).mp hu)]
      exact (hU.mono hs).subset_component huU
    exact (hU.induce hsub).le_strength hne huU hvU

/-- Remove every edge whose original strength is below `κ`. -/
def trimWeak (G : WeightedGraph V) (κ : ℝ) : WeightedGraph V where
  w u v := if κ ≤ G.strength u v then G.w u v else 0
  symm u v := by rw [G.strength_symm u v, G.symm u v]
  nonneg u v := by split <;> simp [G.nonneg]
  diag v := by simp [G.diag]

theorem trimWeak_subgraph (G : WeightedGraph V) (κ : ℝ) :
    (G.trimWeak κ).IsSubgraph G := by
  intro u v
  change (if κ ≤ G.strength u v then G.w u v else 0) ≤ G.w u v
  split <;> simp [G.nonneg]

/-- Deleting weak edges preserves every stronger pair strength (BK Lemma 4.5). -/
theorem strength_trimWeak (G : WeightedGraph V) {κ : ℝ} {u v : V}
    (hκ : κ ≤ G.strength u v) : (G.trimWeak κ).strength u v = G.strength u v := by
  apply le_antisymm ((G.trimWeak_subgraph κ).strength_le u v)
  by_cases hne : u = v
  · simp [hne]
  · obtain ⟨U, hu, hv, he⟩ := G.exists_strength_set hne
    have hU : G.IsStrong (G.strength u v) U := he ▸ G.isStrong_inducedMincut U
    have hU' : (G.trimWeak κ).IsStrong (G.strength u v) U := by
      apply hU.congr
      intro a ha b hb
      by_cases hab : a = b
      · subst b; simp [G.diag, trimWeak]
      · simp only [trimWeak, ite_eq_left (hκ.trans (hU.le_strength hab ha hb))]
    exact hU'.le_strength hne hu hv

/-- The threshold partition is unchanged by trimming weaker edges. -/
theorem strongComponent_trimWeak (G : WeightedGraph V) (κ : ℝ) (u : V) :
    (G.trimWeak κ).strongComponent κ u = G.strongComponent κ u := by
  ext v
  by_cases he : u = v
  · subst v; simp only [mem_strongComponent_self]
  · simp only [mem_strongComponent_iff_le_strength _ he]
    constructor
    · intro h
      exact h.trans ((G.trimWeak_subgraph κ).strength_le u v)
    · intro h
      rw [G.strength_trimWeak h]
      exact h

end
end WeightedGraph
end CutQueryComplexity
