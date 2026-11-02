import CutQueryComplexity.Graph.ForestFacts
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Integral subgraphs and edge multiplicity -/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

namespace WeightedGraph

/-- Pointwise capacity domination. -/
def IsSubgraph (H G : WeightedGraph V) : Prop := ∀ u v, H.w u v ≤ G.w u v

/-- Natural capacities, without imposing a global public bound. -/
def IsIntegral (G : WeightedGraph V) : Prop := ∀ u v, ∃ k : ℕ, G.w u v = k

/-- Add edge capacities on the same labeled vertices. -/
def add (G H : WeightedGraph V) : WeightedGraph V where
  w u v := G.w u v + H.w u v
  symm u v := by rw [G.symm, H.symm]
  nonneg u v := add_nonneg (G.nonneg u v) (H.nonneg u v)
  diag v := by simp [G.diag, H.diag]

@[simp] theorem add_w (G H : WeightedGraph V) (u v : V) :
    (G.add H).w u v = G.w u v + H.w u v := rfl

@[simp] theorem cut_add (G H : WeightedGraph V) (S : Finset V) :
    (G.add H).cut S = G.cut S + H.cut S := by
  simp only [cut, add_w, Finset.sum_add_distrib]

theorem IsSubgraph.cut_le {H G : WeightedGraph V} (h : H.IsSubgraph G) (S : Finset V) :
    H.cut S ≤ G.cut S := Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h u v

@[simp] theorem integral_zero : (0 : WeightedGraph V).IsIntegral := fun _ _ => ⟨0, by simp⟩

theorem IsIntegral.add {G H : WeightedGraph V} (hG : G.IsIntegral) (hH : H.IsIntegral) :
    (G.add H).IsIntegral := by
  intro u v
  obtain ⟨a, ha⟩ := hG u v
  obtain ⟨b, hb⟩ := hH u v
  exact ⟨a + b, by simp [ha, hb]⟩

theorem IsIntegral.subtract {G H : WeightedGraph V} (hG : G.IsIntegral) (hH : H.IsIntegral)
    (hsub : H.IsSubgraph G) : (G.subtract H).IsIntegral := by
  intro u v
  obtain ⟨a, ha⟩ := hG u v
  obtain ⟨b, hb⟩ := hH u v
  have hba : b ≤ a := by exact_mod_cast (ha ▸ hb ▸ hsub u v)
  refine ⟨a - b, ?_⟩
  change max 0 (G.w u v - H.w u v) = _
  rw [max_eq_right (sub_nonneg.mpr (hsub u v)), ha, hb, Nat.cast_sub hba]

/-- For integral graphs this is the number of edge copies, not merely support size. -/
def edgeMass (G : WeightedGraph V) : ℝ := (∑ u, ∑ v, G.w u v) / 2

@[simp] theorem edgeMass_zero : (0 : WeightedGraph V).edgeMass = 0 := by simp [edgeMass]

@[simp] theorem edgeMass_add (G H : WeightedGraph V) :
    (G.add H).edgeMass = G.edgeMass + H.edgeMass := by
  simp only [edgeMass, add_w, Finset.sum_add_distrib, add_div]

end WeightedGraph

theorem CapacityGraph.integral_toWeighted {W : ℕ} (G : CapacityGraph V W) :
    G.toWeighted.IsIntegral := fun u v => ⟨(G.w u v).val, rfl⟩

theorem integral_toWeighted (F : _root_.SimpleGraph V) :
    (SimpleGraph.toWeighted F).IsIntegral := (SimpleGraph.toCapacity F).integral_toWeighted

theorem edgeMass_toWeighted (F : _root_.SimpleGraph V) :
    (SimpleGraph.toWeighted F).edgeMass = (F.edgeFinset.card : ℝ) := by
  have hd (u : V) : (∑ v, (SimpleGraph.toWeighted F).w u v) = (F.degree u : ℝ) := by
    simp only [SimpleGraph.toWeighted_w]
    rw [← F.card_neighborFinset_eq_degree]
    have he : F.neighborFinset u = Finset.univ.filter (F.Adj u) := by ext; simp
    rw [he, Finset.card_filter]
    push_cast
    rfl
  simp only [WeightedGraph.edgeMass, hd, ← Nat.cast_sum]
  rw [F.sum_degrees_eq_twice_card_edges]
  push_cast
  ring

/-- A unit spanning forest fits below a natural-capacity input. -/
theorem IsSpanningForest.toWeighted_subgraph {G : WeightedGraph V} {F : _root_.SimpleGraph V}
    (hF : IsSpanningForest G F) (hG : G.IsIntegral) :
    (SimpleGraph.toWeighted F).IsSubgraph G := by
  intro u v
  rw [SimpleGraph.toWeighted_w]
  split_ifs with h
  · obtain ⟨k, hk⟩ := hG u v
    have hn : k ≠ 0 := by intro hz; exact hF.1 h (by simp [hk, hz])
    rw [hk]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  · exact G.nonneg u v

end
end CutQueryComplexity
