import CutQueryComplexity.Graph.Bottleneck
import CutQueryComplexity.Graph.EdgeInsertion
import CutQueryComplexity.Primitive.ForestPartition
import CutQueryComplexity.Sparsification.ResidualStrength

/-! # Approximate Kruskal invariants

While a pair remains separated, every selected edge is heavy relative to
that pair's strength. At the merge that connects the pair, the current forest
therefore supplies a path with the required bottleneck. Later insertions
preserve that path. This proves a factor `n²/2`, also implying PRW's `n⁴/2`
interface, without first constructing an exact maximum spanning forest.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
open WeightedGraph
variable {V : Type} [Fintype V] [DecidableEq V]

/-- An explicit forest with original weights and simultaneous pair-strength estimates. -/
structure IsApproxKruskalForest (G H : WeightedGraph V) : Prop where
  original : H.IsEdgeRestriction G
  forest : IsSpanningForest G H.support
  estimate : ∀ u v, 2 * G.strength u v ≤ (Fintype.card V : ℝ) ^ 2 * H.bottleneck u v

/-- Invariants of the public weighted forest and its block map. -/
structure KruskalInvariant (G H : WeightedGraph V) (π : V → V) : Prop where
  original : H.IsEdgeRestriction G
  acyclic : H.support.IsAcyclic
  partition : ForestPartition H.support π
  connected : ∀ u v, π u = π v →
    2 * G.strength u v ≤ (Fintype.card V : ℝ) ^ 2 * H.bottleneck u v
  pending : ∀ u v, π u ≠ π v → ∀ a b, H.support.Adj a b →
    2 * G.strength u v ≤ (Fintype.card V : ℝ) ^ 2 * H.w a b

theorem kruskalInvariant_initial (G : WeightedGraph V) : KruskalInvariant G 0 id := by
  refine ⟨zero_isEdgeRestriction G, ?_, ?_, ?_, ?_⟩
  · rw [support_zero]; exact _root_.SimpleGraph.isAcyclic_bot
  · intro u v; simp [support_zero, _root_.SimpleGraph.reachable_bot]
  · intro u v he
    change u = v at he
    subst v
    simp
  · intro u v hne a b hab
    simpa [support_zero] using hab

theorem KruskalInvariant.merge {G H : WeightedGraph V} {π : V → V}
    (h : KruskalInvariant G H π) {u v : V} (hdiff : π u ≠ π v)
    (hp : 0 < G.w u v)
    (hheavy : 2 * (G.contract π).internalMass Finset.univ ≤
      (Fintype.card V : ℝ) ^ 2 * G.w u v) :
    KruskalInvariant G (H.withEdge u v (G.w u v)) (pairMerge π u v) := by
  let H' := H.withEdge u v (G.w u v)
  have hne : u ≠ v := fun he => hdiff (congrArg π he)
  have hpart : ForestPartition H'.support (pairMerge π u v) := by
    rw [show H'.support = H.support ⊔ _root_.SimpleGraph.edge u v from support_withEdge H u v hp]
    exact h.partition.merge_pair hne
  have hall {a b : V} (hab : π a ≠ π b) : ∀ x y, H'.support.Adj x y →
      2 * G.strength a b ≤ (Fintype.card V : ℝ) ^ 2 * H'.w x y := by
    intro x y hxy
    have hnew : 2 * G.strength a b ≤ (Fintype.card V : ℝ) ^ 2 * G.w u v :=
      (mul_le_mul_of_nonneg_left (G.strength_le_residualMass π hab) (by norm_num)).trans hheavy
    change 2 * G.strength a b ≤ _ * (H.withEdge u v (G.w u v)).w x y
    rw [withEdge_true_weight]
    by_cases he : (_root_.SimpleGraph.edge u v).Adj x y
    · rw [ite_eq_left he, G.weight_eq_of_edge he]
      exact hnew
    · rw [ite_eq_right he]
      rw [show H'.support = H.support ⊔ _root_.SimpleGraph.edge u v from support_withEdge H u v hp]
        at hxy
      exact h.pending a b hab x y (hxy.resolve_right he)
  refine ⟨h.original.withEdge u v, ?_, hpart, ?_, ?_⟩
  · rw [support_withEdge H u v hp]
    exact h.acyclic.sup_edge_of_not_reachable (fun hr => hdiff ((h.partition u v).mp hr))
  · intro a b hab
    by_cases hold : π a = π b
    · exact (h.connected a b hold).trans
        (mul_le_mul_of_nonneg_left ((h.original.le_withEdge u v).bottleneck_le a b) (sq_nonneg _))
    · have hn : 0 < (Fintype.card V : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
      have hc : 0 < (Fintype.card V : ℝ) ^ 2 := sq_pos_of_pos hn
      have hpath := H'.le_bottleneck_of_edges
        (fun he => hold (congrArg π he)) ((hpart a b).mpr hab)
        (t := (2 * G.strength a b) / (Fintype.card V : ℝ) ^ 2)
        (fun x y hxy => (div_le_iff₀ hc).mpr (by simpa [mul_comm] using hall hold x y hxy))
      simpa [mul_comm] using (div_le_iff₀ hc).mp hpath
  · intro a b hab x y hxy
    exact hall (fun he => hab (pairMerge_coarsens π u v he)) x y hxy

theorem KruskalInvariant.finish {G H : WeightedGraph V} {π : V → V}
    (h : KruskalInvariant G H π)
    (hspan : ∀ u v, G.support.Reachable u v → π u = π v)
    (hzero : ∀ u v, π u ≠ π v → G.strength u v = 0) : IsApproxKruskalForest G H := by
  refine ⟨h.original, ⟨h.original.support_le, h.acyclic, ?_⟩, ?_⟩
  · intro u v hr
    exact (h.partition u v).mpr (hspan u v hr)
  · intro u v
    by_cases he : π u = π v
    · exact h.connected u v he
    · rw [hzero u v he, mul_zero]
      exact mul_nonneg (sq_nonneg _) (H.bottleneck_nonneg u v)

theorem KruskalInvariant.finish_zero {G H : WeightedGraph V} {π : V → V}
    (h : KruskalInvariant G H π) (hz : (G.contract π).internalMass Finset.univ = 0) :
    IsApproxKruskalForest G H := by
  apply h.finish
  · exact fun _ _ hr => G.label_eq_of_residualMass_zero π hz hr
  · intro u v he
    exact le_antisymm (by simpa [hz] using G.strength_le_residualMass π he)
      (G.strength_nonneg u v)

theorem KruskalInvariant.finish_one_block {G H : WeightedGraph V} {π : V → V}
    (h : KruskalInvariant G H π) (hc : (liveBlocks π).card ≤ 1) : IsApproxKruskalForest G H := by
  have hall (u v : V) : π u = π v :=
    (h.partition u v).mp (h.partition.of_one_block hc u v)
  exact h.finish (fun u v _ => hall u v) (fun u v he => (he (hall u v)).elim)

theorem IsApproxKruskalForest.bottleneck_bounds {G H : WeightedGraph V}
    (h : IsApproxKruskalForest G H) (u v : V) :
    H.bottleneck u v ≤ G.strength u v ∧
      G.strength u v ≤ ((Fintype.card V : ℝ) ^ 2 / 2) * H.bottleneck u v := by
  refine ⟨(H.bottleneck_le_strength u v).trans (h.original.subgraph.strength_le u v), ?_⟩
  have he := h.estimate u v
  linarith

/-- The weaker PRW scale interface follows from the direct quadratic estimate. -/
theorem IsApproxKruskalForest.prw_bounds {G H : WeightedGraph V}
    (h : IsApproxKruskalForest G H) (u v : V) :
    H.bottleneck u v ≤ G.strength u v ∧
      G.strength u v ≤ ((Fintype.card V : ℝ) ^ 4 / 2) * H.bottleneck u v := by
  obtain ⟨hl, hu⟩ := h.bottleneck_bounds u v
  have hn : 1 ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨u⟩
  have hs : 1 ≤ (Fintype.card V : ℝ) ^ 2 := by nlinarith
  have hsq : (Fintype.card V : ℝ) ^ 2 ≤ (Fintype.card V : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (Fintype.card V : ℝ)) (sub_nonneg.mpr hs)]
  exact ⟨hl, hu.trans (mul_le_mul_of_nonneg_right (by linarith) (H.bottleneck_nonneg u v))⟩

theorem IsApproxKruskalForest.edge_bound {G H : WeightedGraph V}
    (h : IsApproxKruskalForest G H) : H.edgeCount ≤ Fintype.card V - 1 :=
  forest_card_le H.support h.forest.2.1

end
end CutQueryComplexity
