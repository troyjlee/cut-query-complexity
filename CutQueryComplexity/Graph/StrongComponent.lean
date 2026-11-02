import CutQueryComplexity.Graph.InducedCut

/-! # Weighted strong sets and their partitions

The induced-cut definition follows Benczúr–Karger (SICOMP 2015, §4).
Singletons are included as vacuously strong blocks, so every threshold gives
a partition of the entire vertex set, including isolated vertices.
-/

namespace CutQueryComplexity
namespace WeightedGraph

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every proper cut inside `U` has weight at least `κ`. -/
def IsStrong (G : WeightedGraph V) (κ : ℝ) (U : Finset V) : Prop :=
  ∀ S, (S ∩ U).Nonempty → (U \ S).Nonempty → κ ≤ G.localCut U S

theorem IsStrong.mono {G : WeightedGraph V} {κ τ : ℝ} {U : Finset V}
    (h : G.IsStrong κ U) (hle : τ ≤ κ) : G.IsStrong τ U :=
  fun S hS hT => hle.trans (h S hS hT)

theorem isStrong_zero (G : WeightedGraph V) (U : Finset V) : G.IsStrong 0 U :=
  fun S _ _ => G.localCut_nonneg U S

theorem isStrong_singleton (G : WeightedGraph V) (κ : ℝ) (u : V) :
    G.IsStrong κ {u} := by
  intro S hS hT
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hT
  simp only [Finset.mem_inter, Finset.mem_singleton] at ha
  simp only [Finset.mem_sdiff, Finset.mem_singleton] at hb
  exact (hb.2 (hb.1 ▸ ha.2 ▸ ha.1)).elim

theorem isStrong_inducedMincut (G : WeightedGraph V) (U : Finset V) :
    G.IsStrong (G.inducedMincut U) U := by
  intro S hS hT
  have he : U \ (S ∩ U) = U \ S := by ext v; simp
  have hs : LocalShore U (S ∩ U) := ⟨Finset.inter_subset_right, hS, by simpa [he]⟩
  simpa using G.inducedMincut_le hs

theorem isStrong_iff_le_inducedMincut (G : WeightedGraph V) {U : Finset V}
    (hn : 2 ≤ U.card) (κ : ℝ) : G.IsStrong κ U ↔ κ ≤ G.inducedMincut U := by
  constructor
  · intro h
    obtain ⟨S, hS, he⟩ := G.exists_inducedMincut hn
    rw [← he]
    exact h S (by simpa [Finset.inter_eq_left.mpr hS.1] using hS.2.1) hS.2.2
  · intro h
    exact (G.isStrong_inducedMincut U).mono h

/-- Overlapping strong induced subgraphs have a strong union. -/
theorem IsStrong.union {G : WeightedGraph V} {κ : ℝ} {U W : Finset V}
    (hU : G.IsStrong κ U) (hW : G.IsStrong κ W) (hUW : (U ∩ W).Nonempty) :
    G.IsStrong κ (U ∪ W) := by
  intro S hS hT
  obtain ⟨c, hc⟩ := hUW
  obtain ⟨hcU, hcW⟩ := Finset.mem_inter.mp hc
  have useU (hL : (S ∩ U).Nonempty) (hR : (U \ S).Nonempty) :
      κ ≤ G.localCut (U ∪ W) S :=
    (hU S hL hR).trans (G.localCut_mono Finset.subset_union_left S)
  have useW (hL : (S ∩ W).Nonempty) (hR : (W \ S).Nonempty) :
      κ ≤ G.localCut (U ∪ W) S :=
    (hW S hL hR).trans (G.localCut_mono Finset.subset_union_right S)
  by_cases hcS : c ∈ S
  · obtain ⟨b, hb⟩ := hT
    obtain ⟨hb, hbS⟩ := Finset.mem_sdiff.mp hb
    rcases Finset.mem_union.mp hb with hbU | hbW
    · exact useU ⟨c, Finset.mem_inter.mpr ⟨hcS, hcU⟩⟩
        ⟨b, Finset.mem_sdiff.mpr ⟨hbU, hbS⟩⟩
    · exact useW ⟨c, Finset.mem_inter.mpr ⟨hcS, hcW⟩⟩
        ⟨b, Finset.mem_sdiff.mpr ⟨hbW, hbS⟩⟩
  · obtain ⟨a, ha⟩ := hS
    obtain ⟨haS, ha⟩ := Finset.mem_inter.mp ha
    rcases Finset.mem_union.mp ha with haU | haW
    · exact useU ⟨a, Finset.mem_inter.mpr ⟨haS, haU⟩⟩
        ⟨c, Finset.mem_sdiff.mpr ⟨hcU, hcS⟩⟩
    · exact useW ⟨a, Finset.mem_inter.mpr ⟨haS, haW⟩⟩
        ⟨c, Finset.mem_sdiff.mpr ⟨hcW, hcS⟩⟩

/-- Two vertices lie in a common strong induced subgraph. -/
def StrongRelated (G : WeightedGraph V) (κ : ℝ) (u v : V) : Prop :=
  ∃ U, G.IsStrong κ U ∧ u ∈ U ∧ v ∈ U

theorem strongRelated_refl (G : WeightedGraph V) (κ : ℝ) (u : V) :
    G.StrongRelated κ u u := ⟨{u}, G.isStrong_singleton κ u, by simp⟩

theorem StrongRelated.symm {G : WeightedGraph V} {κ : ℝ} {u v : V}
    (h : G.StrongRelated κ u v) : G.StrongRelated κ v u := by
  obtain ⟨U, hU, hu, hv⟩ := h
  exact ⟨U, hU, hv, hu⟩

theorem StrongRelated.trans {G : WeightedGraph V} {κ : ℝ} {u v w : V}
    (h : G.StrongRelated κ u v) (h' : G.StrongRelated κ v w) :
    G.StrongRelated κ u w := by
  obtain ⟨U, hU, hu, hv⟩ := h
  obtain ⟨W, hW, hv', hw⟩ := h'
  exact ⟨U ∪ W, hU.union hW ⟨v, Finset.mem_inter.mpr ⟨hv, hv'⟩⟩,
    Finset.mem_union_left _ hu, Finset.mem_union_right _ hw⟩

theorem StrongRelated.mono {G : WeightedGraph V} {κ τ : ℝ} {u v : V}
    (h : G.StrongRelated κ u v) (hle : τ ≤ κ) : G.StrongRelated τ u v := by
  obtain ⟨U, hU, hu, hv⟩ := h
  exact ⟨U, hU.mono hle, hu, hv⟩

/-- Equivalence relation underlying contraction into strong components. -/
def strongSetoid (G : WeightedGraph V) (κ : ℝ) : Setoid V where
  r := G.StrongRelated κ
  iseqv := ⟨G.strongRelated_refl κ, StrongRelated.symm, StrongRelated.trans⟩

/-- The maximal `κ`-strong vertex set containing `u`. -/
def strongComponent (G : WeightedGraph V) (κ : ℝ) (u : V) : Finset V :=
  Finset.univ.filter (G.StrongRelated κ u)

@[simp] theorem mem_strongComponent (G : WeightedGraph V) (κ : ℝ) (u v : V) :
    v ∈ G.strongComponent κ u ↔ G.StrongRelated κ u v := by simp [strongComponent]

@[simp] theorem mem_strongComponent_self (G : WeightedGraph V) (κ : ℝ) (u : V) :
    u ∈ G.strongComponent κ u := (G.mem_strongComponent κ u u).mpr (G.strongRelated_refl κ u)

theorem strongComponent_nonempty (G : WeightedGraph V) (κ : ℝ) (u : V) :
    (G.strongComponent κ u).Nonempty := ⟨u, G.mem_strongComponent_self κ u⟩

theorem IsStrong.subset_component {G : WeightedGraph V} {κ : ℝ} {U : Finset V}
    (h : G.IsStrong κ U) {u : V} (hu : u ∈ U) : U ⊆ G.strongComponent κ u := by
  intro v hv
  exact (G.mem_strongComponent κ u v).mpr ⟨U, h, hu, hv⟩

theorem strongComponent_eq_of_related {G : WeightedGraph V} {κ : ℝ} {u v : V}
    (h : G.StrongRelated κ u v) : G.strongComponent κ u = G.strongComponent κ v := by
  ext w
  simp only [mem_strongComponent]
  exact ⟨fun hw => h.symm.trans hw, fun hw => h.trans hw⟩

theorem strongComponent_strong (G : WeightedGraph V) (κ : ℝ) (u : V) :
    G.IsStrong κ (G.strongComponent κ u) := by
  intro S hS hT
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hT
  obtain ⟨haS, haU⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbU, hbS⟩ := Finset.mem_sdiff.mp hb
  have hua := (G.mem_strongComponent κ u a).mp haU
  have hub := (G.mem_strongComponent κ u b).mp hbU
  obtain ⟨U, hU, ha, hb⟩ := hua.symm.trans hub
  have hsub : U ⊆ G.strongComponent κ u := by
    rw [G.strongComponent_eq_of_related hua]
    exact hU.subset_component ha
  exact (hU S ⟨a, Finset.mem_inter.mpr ⟨haS, ha⟩⟩
    ⟨b, Finset.mem_sdiff.mpr ⟨hb, hbS⟩⟩).trans (G.localCut_mono hsub S)

/-- At a fixed threshold, components are equal or disjoint. -/
theorem strongComponent_eq_or_disjoint (G : WeightedGraph V) (κ : ℝ) (u v : V) :
    G.strongComponent κ u = G.strongComponent κ v ∨
      Disjoint (G.strongComponent κ u) (G.strongComponent κ v) := by
  by_cases h : G.StrongRelated κ u v
  · exact Or.inl (G.strongComponent_eq_of_related h)
  · right
    apply Finset.disjoint_left.mpr
    intro w huw hvw
    exact h (((G.mem_strongComponent κ u w).mp huw).trans
      ((G.mem_strongComponent κ v w).mp hvw).symm)

/-- Lowering the threshold coarsens the partition. -/
theorem strongComponent_mono (G : WeightedGraph V) {κ τ : ℝ} (h : τ ≤ κ) (u : V) :
    G.strongComponent κ u ⊆ G.strongComponent τ u := by
  intro v hv
  exact (G.mem_strongComponent τ u v).mpr (((G.mem_strongComponent κ u v).mp hv).mono h)

/-- The strong components at all thresholds form a laminar family. -/
theorem strongComponent_laminar (G : WeightedGraph V) (κ τ : ℝ) (u v : V)
    (h : (G.strongComponent κ u ∩ G.strongComponent τ v).Nonempty) :
    G.strongComponent κ u ⊆ G.strongComponent τ v ∨
      G.strongComponent τ v ⊆ G.strongComponent κ u := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨huw, hvw⟩ := Finset.mem_inter.mp hw
  rw [G.strongComponent_eq_of_related ((G.mem_strongComponent κ u w).mp huw),
    G.strongComponent_eq_of_related ((G.mem_strongComponent τ v w).mp hvw)]
  rcases le_total τ κ with ht | hk
  · exact Or.inl (G.strongComponent_mono ht w)
  · exact Or.inr (G.strongComponent_mono hk w)

end
end WeightedGraph
end CutQueryComplexity
