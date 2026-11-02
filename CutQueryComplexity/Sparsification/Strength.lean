import CutQueryComplexity.Graph.StrongComponent
import CutQueryComplexity.Graph.Integral

/-! # Pair strength in a nonnegative weighted graph

Strength is the largest induced minimum cut containing the two endpoints,
including pairs with no edge. It is not terminal edge connectivity. The
diagonal is assigned zero; all threshold characterizations state distinctness.
See Benczúr–Karger (SICOMP 2015, Definitions 4.2–4.4).
-/

namespace CutQueryComplexity
namespace WeightedGraph

noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

def pairSets (u v : V) : Finset (Finset V) :=
  Finset.univ.filter (fun U => u ∈ U ∧ v ∈ U)

@[simp] theorem mem_pairSets (u v : V) (U : Finset V) :
    U ∈ pairSets u v ↔ u ∈ U ∧ v ∈ U := by simp [pairSets]

theorem pairSets_nonempty (u v : V) : (pairSets u v).Nonempty :=
  ⟨Finset.univ, by simp⟩

def strength (G : WeightedGraph V) (u v : V) : ℝ :=
  if u = v then 0 else (pairSets u v).sup' (pairSets_nonempty u v) G.inducedMincut

@[simp] theorem strength_diag (G : WeightedGraph V) (u : V) : G.strength u u = 0 :=
  by simp [strength]

theorem strength_symm (G : WeightedGraph V) (u v : V) :
    G.strength u v = G.strength v u := by
  have he : pairSets u v = pairSets v u := by ext; simp [and_comm]
  simp only [strength, he, eq_comm]

theorem inducedMincut_le_strength (G : WeightedGraph V) {U : Finset V} {u v : V}
    (hne : u ≠ v) (hu : u ∈ U) (hv : v ∈ U) : G.inducedMincut U ≤ G.strength u v := by
  rw [strength, ite_eq_right hne]
  exact Finset.le_sup' _ ((mem_pairSets _ _ _).mpr ⟨hu, hv⟩)

theorem strength_nonneg (G : WeightedGraph V) (u v : V) : 0 ≤ G.strength u v := by
  by_cases h : u = v
  · simp [h]
  · exact (G.inducedMincut_nonneg Finset.univ).trans
      (G.inducedMincut_le_strength h (Finset.mem_univ _) (Finset.mem_univ _))

theorem exists_strength_set (G : WeightedGraph V) {u v : V} (hne : u ≠ v) :
    ∃ U, u ∈ U ∧ v ∈ U ∧ G.inducedMincut U = G.strength u v := by
  obtain ⟨U, hU, he⟩ := Finset.exists_mem_eq_sup' (pairSets_nonempty u v) G.inducedMincut
  exact ⟨U, ((mem_pairSets _ _ _).mp hU).1, ((mem_pairSets _ _ _).mp hU).2,
    by rw [strength, ite_eq_right hne, he]⟩

/-- The numerical and strong-component definitions agree for every distinct pair. -/
theorem le_strength_iff (G : WeightedGraph V) {u v : V} (hne : u ≠ v) (κ : ℝ) :
    κ ≤ G.strength u v ↔ G.StrongRelated κ u v := by
  constructor
  · intro h
    obtain ⟨U, hu, hv, he⟩ := G.exists_strength_set hne
    exact ⟨U, (G.isStrong_inducedMincut U).mono (he ▸ h), hu, hv⟩
  · rintro ⟨U, hU, hu, hv⟩
    have hn : 2 ≤ U.card := by
      have := Finset.card_le_card (show ({u, v} : Finset V) ⊆ U from
        Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩)
      simpa [Finset.card_pair hne] using this
    exact ((G.isStrong_iff_le_inducedMincut hn κ).mp hU).trans
      (G.inducedMincut_le_strength hne hu hv)

theorem mem_strongComponent_iff_le_strength (G : WeightedGraph V) {u v : V}
    (hne : u ≠ v) (κ : ℝ) : v ∈ G.strongComponent κ u ↔ κ ≤ G.strength u v := by
  rw [mem_strongComponent, G.le_strength_iff hne]

theorem weight_le_cross (G : WeightedGraph V) {S T : Finset V} {u v : V}
    (hu : u ∈ S) (hv : v ∈ T) : G.w u v ≤ G.cross S T := by
  exact (Finset.single_le_sum (fun b _ => G.nonneg u b) hv).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => G.nonneg a b)) hu)

theorem isStrong_pair (G : WeightedGraph V) (u v : V) :
    G.IsStrong (G.w u v) {u, v} := by
  intro S hS hT
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hT
  have hab : a ≠ b := by
    intro he
    exact (Finset.mem_sdiff.mp hb).2 (he ▸ (Finset.mem_inter.mp ha).1)
  have ham := (Finset.mem_inter.mp ha).2
  have hbm := (Finset.mem_sdiff.mp hb).1
  have hweight : G.w u v = G.w a b := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ham hbm
    rcases ham with rfl | rfl <;> rcases hbm with rfl | rfl
    · exact (hab rfl).elim
    · rfl
    · exact G.symm _ _
    · exact (hab rfl).elim
  rw [hweight]
  exact G.weight_le_cross ha hb

/-- Every positive edge has positive strength, even in a disconnected graph. -/
theorem weight_le_strength (G : WeightedGraph V) (u v : V) :
    G.w u v ≤ G.strength u v := by
  by_cases h : u = v
  · subst v; simp [G.diag]
  · exact (G.le_strength_iff h _).mpr ⟨{u, v}, G.isStrong_pair u v, by simp⟩

theorem strength_pos_of_weight_pos (G : WeightedGraph V) {u v : V}
    (h : 0 < G.w u v) : 0 < G.strength u v := h.trans_le (G.weight_le_strength u v)

/-- Any separating cut bounds pair strength from above. -/
theorem strength_le_cut (G : WeightedGraph V) {u v : V} {S : Finset V}
    (hu : u ∈ S) (hv : v ∉ S) : G.strength u v ≤ G.cut S := by
  have hne : u ≠ v := by intro he; exact hv (he ▸ hu)
  obtain ⟨U, huU, hvU, he⟩ := G.exists_strength_set hne
  rw [← he]
  exact (G.isStrong_inducedMincut U S ⟨u, Finset.mem_inter.mpr ⟨hu, huU⟩⟩
    ⟨v, Finset.mem_sdiff.mpr ⟨hvU, hv⟩⟩).trans
    (by simpa using G.localCut_mono (Finset.subset_univ U) S)

theorem mincut_le_strength (G : WeightedGraph V) {u v : V} (hne : u ≠ v) :
    mincutValue G ≤ G.strength u v := by
  simpa using G.inducedMincut_le_strength hne (Finset.mem_univ u) (Finset.mem_univ v)

@[simp] theorem strength_zero (u v : V) : (0 : WeightedGraph V).strength u v = 0 := by
  by_cases h : u = v
  · simp [h]
  · apply le_antisymm ?_ ((0 : WeightedGraph V).strength_nonneg u v)
    have hc := (0 : WeightedGraph V).strength_le_cut
      (Finset.mem_singleton_self u) (by simpa using Ne.symm h : v ∉ ({u} : Finset V))
    simpa only [cut_zero] using hc

/-- A two-vertex induced graph has exactly its edge weight as minimum cut,
regardless of isolated vertices outside the pair. -/
theorem inducedMincut_pair (G : WeightedGraph V) (u v : V) :
    G.inducedMincut {u, v} = G.w u v := by
  by_cases h : u = v
  · subst v; simp [G.diag]
  · apply le_antisymm
    · have hs : LocalShore ({u, v} : Finset V) {u} := by
        refine ⟨by simp, by simp, ⟨v, ?_⟩⟩
        simp [Ne.symm h]
      have hcut : G.localCut {u, v} {u} = G.w u v := by
        rw [G.localCut_of_subset hs.1]
        simp [cross, Finset.sdiff_singleton_eq_erase, h]
      exact hcut ▸ G.inducedMincut_le hs
    · exact (G.isStrong_iff_le_inducedMincut (by simp [h]) _).mp (G.isStrong_pair u v)

theorem IsSubgraph.strong {G H : WeightedGraph V} (h : H.IsSubgraph G)
    {κ : ℝ} {U : Finset V} (hs : H.IsStrong κ U) : G.IsStrong κ U := by
  intro S hS hT
  exact (hs S hS hT).trans (Finset.sum_le_sum fun u _ =>
    Finset.sum_le_sum fun v _ => h u v)

/-- Deleting weight cannot increase strength. -/
theorem IsSubgraph.strength_le {G H : WeightedGraph V} (h : H.IsSubgraph G) (u v : V) :
    H.strength u v ≤ G.strength u v := by
  by_cases he : u = v
  · simp [he]
  · obtain ⟨U, hu, hv, hU⟩ := H.exists_strength_set he
    exact (G.le_strength_iff he _).mpr
      ⟨U, hU ▸ h.strong (H.isStrong_inducedMincut U), hu, hv⟩

/-- BK's normalized edge weights; absent edges and the diagonal remain zero. -/
def strengthNormalized (G : WeightedGraph V) : WeightedGraph V where
  w u v := G.w u v / G.strength u v
  symm u v := by rw [G.symm u v, G.strength_symm u v]
  nonneg u v := div_nonneg (G.nonneg u v) (G.strength_nonneg u v)
  diag v := by simp [G.diag]

@[simp] theorem strengthNormalized_w (G : WeightedGraph V) (u v : V) :
    G.strengthNormalized.w u v = G.w u v / G.strength u v := rfl

theorem strengthNormalized_support (G : WeightedGraph V) :
    G.strengthNormalized.support = G.support := by
  ext u v
  change G.w u v / G.strength u v ≠ 0 ↔ G.w u v ≠ 0
  constructor
  · intro h hz; exact h (by rw [hz, zero_div])
  · intro h
    exact div_ne_zero h (ne_of_gt (G.strength_pos_of_weight_pos
      (lt_of_le_of_ne (G.nonneg u v) (Ne.symm h))))

end
end WeightedGraph
end CutQueryComplexity
