import CutQueryComplexity.Graph.ForestFacts
import CutQueryComplexity.Graph.Integral

/-! # Inserting an observed weighted edge

The operation is total on arbitrary transcripts. On genuine graph answers it
retains original edge weights and adds exactly the corresponding support edge.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every retained edge has its original weight. -/
def IsEdgeRestriction (H G : WeightedGraph V) : Prop :=
  ∀ u v, H.w u v = 0 ∨ H.w u v = G.w u v

theorem IsEdgeRestriction.subgraph {H G : WeightedGraph V} (h : H.IsEdgeRestriction G) :
    H.IsSubgraph G := by
  intro u v
  rcases h u v with hz | he
  · rw [hz]; exact G.nonneg u v
  · exact he.le

theorem IsEdgeRestriction.support_le {H G : WeightedGraph V} (h : H.IsEdgeRestriction G) :
    H.support ≤ G.support := by
  intro u v huv
  exact fun hz => huv (by rcases h u v with he | he <;> simp_all)

theorem zero_isEdgeRestriction (G : WeightedGraph V) : (0 : WeightedGraph V).IsEdgeRestriction G :=
  fun _ _ => Or.inl rfl

@[simp] theorem support_zero : (0 : WeightedGraph V).support = ⊥ := by
  ext u v; simp [support]

/-- Store an observed edge weight, clipping negative answers and discarding loops. -/
def withEdge (H : WeightedGraph V) (u v : V) (a : ℝ) : WeightedGraph V where
  w x y := if (_root_.SimpleGraph.edge u v).Adj x y then max 0 a else H.w x y
  symm x y := by simp only [_root_.SimpleGraph.adj_comm, H.symm x y]
  nonneg x y := by split <;> simp [H.nonneg]
  diag x := by simp [H.diag]

theorem weight_eq_of_edge (G : WeightedGraph V) {u v x y : V}
    (h : (_root_.SimpleGraph.edge u v).Adj x y) : G.w x y = G.w u v := by
  rcases (_root_.SimpleGraph.edge_adj _ _ _ _).mp h with ⟨h | h, _⟩
  · rcases h with ⟨rfl, rfl⟩; rfl
  · rcases h with ⟨rfl, rfl⟩; exact G.symm _ _

theorem withEdge_true_weight (G H : WeightedGraph V) (u v x y : V) :
    (H.withEdge u v (G.w u v)).w x y =
      if (_root_.SimpleGraph.edge u v).Adj x y then G.w x y else H.w x y := by
  by_cases he : (_root_.SimpleGraph.edge u v).Adj x y
  · simp [withEdge, he, max_eq_right (G.nonneg u v), G.weight_eq_of_edge he]
  · simp [withEdge, he]

theorem IsEdgeRestriction.withEdge {G H : WeightedGraph V} (h : H.IsEdgeRestriction G)
    (u v : V) : (H.withEdge u v (G.w u v)).IsEdgeRestriction G := by
  intro x y
  rw [withEdge_true_weight]
  split
  · exact Or.inr rfl
  · exact h x y

theorem IsEdgeRestriction.le_withEdge {G H : WeightedGraph V} (h : H.IsEdgeRestriction G)
    (u v : V) : H.IsSubgraph (H.withEdge u v (G.w u v)) := by
  intro x y
  rw [withEdge_true_weight]
  split
  · exact h.subgraph x y
  · exact le_rfl

theorem support_withEdge (H : WeightedGraph V) (u v : V) {a : ℝ} (ha : 0 < a) :
    (H.withEdge u v a).support = H.support ⊔ _root_.SimpleGraph.edge u v := by
  ext x y
  change (if (_root_.SimpleGraph.edge u v).Adj x y then max 0 a else H.w x y) ≠ 0 ↔
    H.w x y ≠ 0 ∨ (_root_.SimpleGraph.edge u v).Adj x y
  by_cases he : (_root_.SimpleGraph.edge u v).Adj x y <;>
    simp [he, max_eq_right ha.le, ne_of_gt ha]

end
end CutQueryComplexity.WeightedGraph
