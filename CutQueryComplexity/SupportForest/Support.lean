import CutQueryComplexity.Graph.ForestFacts

/-! # The positive support, zero cuts and connectivity

`G.support` (defined in `Problem/Basic.lean`) is the simple graph of positive edges. A cut is
zero exactly when no support edge leaves its shore (`cut_eq_zero_iff_no_support_edge`); a zero
proper shore is a minimum cut of value zero (`isMinCut_of_cut_eq_zero`); a disconnected support
has a zero proper shore, namely a reachability class (`exists_zero_shore_of_not_connected`); and
for at least two vertices the support is connected exactly when the minimum-cut value is
positive (`support_connected_iff_pos`).
-/

namespace CutQueryComplexity
namespace SupportForest

open WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem support_adj_iff (G : WeightedGraph V) (u v : V) : G.support.Adj u v ↔ 0 < G.w u v :=
  ⟨fun h => lt_of_le_of_ne (G.nonneg u v) (Ne.symm h), fun h => h.ne'⟩

/-- A cut is zero exactly when no support edge leaves its shore. -/
theorem cut_eq_zero_iff_no_support_edge (G : WeightedGraph V) (S : Finset V) :
    G.cut S = 0 ↔ ∀ u ∈ S, ∀ v, v ∉ S → ¬ G.support.Adj u v := by
  constructor
  · intro hz u hu v hv hadj
    exact hv (adj_mem_of_cut_zero G S hz hu hadj)
  · intro h
    by_contra hne
    have hpos : 0 < G.cut S := lt_of_le_of_ne (G.cut_nonneg S) (Ne.symm hne)
    obtain ⟨u, hu, v, hv, hw⟩ := (G.cross_pos_iff S Sᶜ).mp hpos
    exact h u hu v (mem_compl.mp hv) ((support_adj_iff G u v).mpr hw)

/-- A zero proper shore is a minimum cut, and the minimum-cut value is zero. -/
theorem isMinCut_of_cut_eq_zero (G : WeightedGraph V) {S : Finset V}
    (hS : ProperShore S) (h0 : G.cut S = 0) : IsMinCut G S ∧ mincutValue G = 0 :=
  ⟨⟨hS, fun T _ => h0 ▸ G.cut_nonneg T⟩, mincutValue_eq_zero_of_cut_eq_zero G hS h0⟩

open scoped Classical in
/-- The reachability class of a vertex in the support. -/
noncomputable def reachClass (G : WeightedGraph V) (u : V) : Finset V :=
  univ.filter fun v => G.support.Reachable u v

omit [DecidableEq V] in
@[simp] theorem mem_reachClass (G : WeightedGraph V) (u v : V) :
    v ∈ reachClass G u ↔ G.support.Reachable u v := by simp [reachClass]

/-- A reachability class of the support is a zero cut. -/
theorem cut_reachClass (G : WeightedGraph V) (u : V) : G.cut (reachClass G u) = 0 := by
  rw [cut_eq_zero_iff_no_support_edge]
  intro a ha b hb hadj
  rw [mem_reachClass] at ha hb
  exact hb (ha.trans hadj.reachable)

/-- A disconnected support on a nonempty vertex set has a zero proper shore. -/
theorem exists_zero_shore_of_not_connected [Nonempty V] (G : WeightedGraph V)
    (h : ¬ G.support.Connected) : ∃ S, ProperShore S ∧ G.cut S = 0 := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at h
  push Not at h
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨w, hw⟩ := h v
  refine ⟨reachClass G v, ⟨⟨v, by simp⟩, fun hall => ?_⟩, cut_reachClass G v⟩
  have : w ∈ reachClass G v := hall ▸ mem_univ w
  exact hw ((mem_reachClass G v w).mp this)

/-- With at least two vertices, the support is connected exactly when the minimum-cut value
is positive. -/
theorem support_connected_iff_pos (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    G.support.Connected ↔ 0 < mincutValue G := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  constructor
  · intro hc
    rcases (mincutValue_nonneg G).lt_or_eq with h | h
    · exact h
    exfalso
    obtain ⟨v⟩ := hne
    obtain ⟨S, hS, hval⟩ :=
      exists_isMinCut G ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
    rw [← h] at hval
    obtain ⟨u, hu⟩ := hS.1.1
    obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
      by_contra hall
      push Not at hall
      exact hS.1.2 (eq_univ_of_forall hall)
    exact hw (reachable_mem_of_cut_zero G S hval hu (hc.preconnected u w))
  · intro hpos
    by_contra hc
    obtain ⟨S, hS, h0⟩ := exists_zero_shore_of_not_connected G hc
    have := mincutValue_le G hS
    linarith

end SupportForest
end CutQueryComplexity
