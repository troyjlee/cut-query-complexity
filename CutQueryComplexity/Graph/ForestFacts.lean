import CutQueryComplexity.Graph.Operations
import Mathlib.Combinatorics.SimpleGraph.Operations

/-! # Forest size, closed cuts, and crossing witnesses -/

namespace CutQueryComplexity

noncomputable section
open scoped Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every finite forest has at most `n-1` edges, including the empty graph. -/
theorem forest_card_le (F : _root_.SimpleGraph V) (hF : F.IsAcyclic) :
    F.edgeFinset.card ≤ Fintype.card V - 1 := by
  cases isEmpty_or_nonempty V with
  | inl h =>
      letI := h
      have hbot : F = ⊥ := Subsingleton.elim _ _
      simp [hbot]
  | inr h =>
      letI := h
      obtain ⟨T, hFT, _, hT⟩ := _root_.SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic
        (G := (⊤ : _root_.SimpleGraph V)) (H := F) le_top hF
      have hc := hT.card_edgeFinset
      have hm := Finset.card_mono (_root_.SimpleGraph.edgeFinset_mono hFT)
      omega

/-- Reachability cannot leave a vertex set closed under adjacency. -/
theorem reachable_mem_of_closed (F : _root_.SimpleGraph V) (S : Finset V)
    (hS : ∀ u ∈ S, ∀ v, F.Adj u v → v ∈ S) {u v : V}
    (hu : u ∈ S) (h : F.Reachable u v) : v ∈ S := by
  have hw : ∀ {a b : V}, F.Walk a b → a ∈ S → b ∈ S := by
    intro a b p
    induction p with
    | nil => exact id
    | cons hadj p ih => exact fun ha => ih (hS _ ha _ hadj)
  obtain ⟨p⟩ := h
  exact hw p hu

/-- A zero-weight cut has no positive edge leaving its shore. -/
theorem adj_mem_of_cut_zero (G : WeightedGraph V) (S : Finset V) (hz : G.cut S = 0)
    {u v : V} (hu : u ∈ S) (h : G.support.Adj u v) : v ∈ S := by
  by_contra hv
  have hp : 0 < G.w u v := lt_of_le_of_ne (G.nonneg u v) (Ne.symm h)
  have hc := (G.cross_pos_iff S Sᶜ).mpr ⟨u, hu, v, by simpa using hv, hp⟩
  simpa [hz] using hc

theorem reachable_mem_of_cut_zero (G : WeightedGraph V) (S : Finset V) (hz : G.cut S = 0)
    {u v : V} (hu : u ∈ S) (h : G.support.Reachable u v) : v ∈ S :=
  reachable_mem_of_closed G.support S (fun _ hu _ h => adj_mem_of_cut_zero G S hz hu h) hu h

/-- The connected component of a publicly known partial forest. -/
def forestBlock (F : _root_.SimpleGraph V) (root : V) : Finset V :=
  Finset.univ.filter (F.Reachable root)

@[simp] theorem mem_forestBlock (F : _root_.SimpleGraph V) (root v : V) :
    v ∈ forestBlock F root ↔ F.Reachable root v := by simp [forestBlock]

@[simp] theorem root_mem_forestBlock (F : _root_.SimpleGraph V) (root : V) :
    root ∈ forestBlock F root := by simp

theorem not_reachable_across_block (F : _root_.SimpleGraph V) (root : V) {u v : V}
    (hu : u ∈ forestBlock F root) (hv : v ∉ forestBlock F root) : ¬F.Reachable u v := by
  intro h
  exact hv ((mem_forestBlock _ _ _).mpr (((mem_forestBlock _ _ _).mp hu).trans h))

/-- A closed component of the partial forest already spans its true component. -/
theorem closed_block_spans (G : WeightedGraph V) (F : _root_.SimpleGraph V) (root : V)
    (hz : G.cut (forestBlock F root) = 0) {u v : V} (hu : u ∈ forestBlock F root)
    (h : G.support.Reachable u v) : F.Reachable u v := by
  have hv := reachable_mem_of_cut_zero G _ hz hu h
  exact ((mem_forestBlock _ _ _).mp hu).symm.trans ((mem_forestBlock _ _ _).mp hv)

@[simp] theorem support_toWeighted (F : _root_.SimpleGraph V) :
    (SimpleGraph.toWeighted F).support = F := by
  ext u v
  by_cases h : F.Adj u v <;> simp [WeightedGraph.support, SimpleGraph.toWeighted_w, h]

/-- A spanning forest crosses every cut crossed by the original graph. -/
theorem IsSpanningForest.cut_pos {G : WeightedGraph V} {F : _root_.SimpleGraph V}
    (hF : IsSpanningForest G F) {S : Finset V} (hpos : 0 < G.cut S) :
    0 < (SimpleGraph.toWeighted F).cut S := by
  by_contra hf
  have hz := le_antisymm (le_of_not_gt hf) ((SimpleGraph.toWeighted F).cut_nonneg S)
  obtain ⟨u, hu, v, hv, hw⟩ := (G.cross_pos_iff S Sᶜ).mp hpos
  have hreach := hF.2.2 u v ((_root_.SimpleGraph.Adj.reachable (G := G.support)) (ne_of_gt hw))
  have hv' := reachable_mem_of_cut_zero (SimpleGraph.toWeighted F) S hz hu
    (by simpa using hreach)
  exact (Finset.mem_compl.mp hv) hv'

/-- Unit edge weights make a positive forest cut at least one. -/
theorem IsSpanningForest.one_le_cut {G : WeightedGraph V} {F : _root_.SimpleGraph V}
    (hF : IsSpanningForest G F) {S : Finset V} (hpos : 0 < G.cut S) :
    1 ≤ (SimpleGraph.toWeighted F).cut S := by
  have hp := hF.cut_pos hpos
  change 1 ≤ (SimpleGraph.toCapacity F).toWeighted.cut S
  rw [CapacityGraph.toWeighted_cut]
  change 0 < (SimpleGraph.toCapacity F).toWeighted.cut S at hp
  rw [CapacityGraph.toWeighted_cut] at hp
  have hn : 0 < (SimpleGraph.toCapacity F).cut S := by exact_mod_cast hp
  exact_mod_cast hn

end
end CutQueryComplexity
