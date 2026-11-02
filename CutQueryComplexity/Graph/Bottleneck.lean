import CutQueryComplexity.Sparsification.Strength
import CutQueryComplexity.Graph.ForestFacts

/-! # Weighted path bottlenecks

The bottleneck is the largest edge-weight threshold that still connects a
distinct pair, or zero when they are disconnected. This finite definition is
available from an explicit graph without queries. On a forest it describes
the minimum weight on the unique path, through threshold connectivity.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Keep exactly the positive edges of weight at least `t`. -/
def threshold (G : WeightedGraph V) (t : ℝ) : _root_.SimpleGraph V where
  Adj u v := 0 < G.w u v ∧ t ≤ G.w u v
  symm := ⟨fun u v h => by simpa only [G.symm v u] using h⟩
  loopless := ⟨fun v h => by simpa [G.diag] using h.1⟩

theorem threshold_le_support (G : WeightedGraph V) (t : ℝ) : G.threshold t ≤ G.support :=
  fun _ _ h => ne_of_gt h.1

@[simp] theorem threshold_zero (G : WeightedGraph V) : G.threshold 0 = G.support := by
  ext u v
  change (0 < G.w u v ∧ 0 ≤ G.w u v) ↔ G.w u v ≠ 0
  exact ⟨fun h => ne_of_gt h.1, fun h =>
    ⟨lt_of_le_of_ne (G.nonneg u v) (Ne.symm h), G.nonneg u v⟩⟩

theorem threshold_antitone (G : WeightedGraph V) {s t : ℝ} (h : s ≤ t) :
    G.threshold t ≤ G.threshold s := fun _ _ hadj => ⟨hadj.1, h.trans hadj.2⟩

theorem IsSubgraph.threshold_le {G H : WeightedGraph V} (h : G.IsSubgraph H) (t : ℝ) :
    G.threshold t ≤ H.threshold t := fun u v hadj =>
  ⟨hadj.1.trans_le (h u v), hadj.2.trans (h u v)⟩

def edgeLevels (G : WeightedGraph V) : Finset ℝ :=
  Finset.univ.image (fun p : V × V => G.w p.1 p.2)

theorem weight_mem_edgeLevels (G : WeightedGraph V) (u v : V) : G.w u v ∈ G.edgeLevels :=
  Finset.mem_image.mpr ⟨(u, v), Finset.mem_univ _, rfl⟩

/-- A nontrivial threshold walk has an attained edge-weight threshold. -/
theorem exists_edgeLevel_of_reachable (G : WeightedGraph V) {t : ℝ} {u v : V}
    (h : (G.threshold t).Reachable u v) (hne : u ≠ v) :
    ∃ a ∈ G.edgeLevels, 0 < a ∧ t ≤ a ∧ (G.threshold a).Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact (hne rfl).elim
  | @cons u x v hux p ih =>
      by_cases hxv : x = v
      · subst v
        exact ⟨G.w u x, G.weight_mem_edgeLevels u x, hux.1, hux.2,
          (_root_.SimpleGraph.Adj.reachable ⟨hux.1, le_rfl⟩)⟩
      · obtain ⟨a, ha, hp, ht, hr⟩ := ih hxv
        refine ⟨min (G.w u x) a, ?_, lt_min hux.1 hp, le_min hux.2 ht, ?_⟩
        · rcases le_total (G.w u x) a with hh | hh
          · simpa [min_eq_left hh] using G.weight_mem_edgeLevels u x
          · simpa [min_eq_right hh] using ha
        · have hedge : (G.threshold (min (G.w u x) a)).Adj u x :=
            ⟨hux.1, min_le_left _ _⟩
          exact hedge.reachable.trans (hr.mono (G.threshold_antitone (min_le_right _ _)))

def bottleneckLevels (G : WeightedGraph V) (u v : V) : Finset ℝ :=
  insert 0 (G.edgeLevels.filter (fun t => (G.threshold t).Reachable u v))

def bottleneck (G : WeightedGraph V) (u v : V) : ℝ :=
  if u = v then 0 else
    (G.bottleneckLevels u v).sup' ⟨0, Finset.mem_insert_self _ _⟩ (fun t : ℝ => t)

@[simp] theorem bottleneck_diag (G : WeightedGraph V) (u : V) : G.bottleneck u u = 0 := by
  simp [bottleneck]

theorem bottleneck_symm (G : WeightedGraph V) (u v : V) :
    G.bottleneck u v = G.bottleneck v u := by
  have he : G.bottleneckLevels u v = G.bottleneckLevels v u := by
    ext a
    simp only [bottleneckLevels, Finset.mem_insert, Finset.mem_filter,
      _root_.SimpleGraph.reachable_comm]
  simp only [bottleneck, he, eq_comm]

theorem bottleneck_nonneg (G : WeightedGraph V) (u v : V) : 0 ≤ G.bottleneck u v := by
  by_cases he : u = v
  · simp [he]
  · rw [bottleneck, ite_eq_right he]
    exact Finset.le_sup' (fun t : ℝ => t)
      (show (0 : ℝ) ∈ G.bottleneckLevels u v from Finset.mem_insert_self _ _)

theorem le_bottleneck_of_reachable (G : WeightedGraph V) {t : ℝ} {u v : V}
    (hne : u ≠ v) (h : (G.threshold t).Reachable u v) : t ≤ G.bottleneck u v := by
  obtain ⟨a, ha, _, ht, hr⟩ := G.exists_edgeLevel_of_reachable h hne
  rw [bottleneck, ite_eq_right hne]
  exact ht.trans (Finset.le_sup' (fun t : ℝ => t)
    (show a ∈ G.bottleneckLevels u v from
      Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ha, hr⟩)))

theorem reachable_bottleneck (G : WeightedGraph V) {u v : V}
    (hp : 0 < G.bottleneck u v) : (G.threshold (G.bottleneck u v)).Reachable u v := by
  have hne : u ≠ v := by intro he; subst v; simpa using hp
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup'
    (show (G.bottleneckLevels u v).Nonempty from ⟨0, Finset.mem_insert_self _ _⟩)
      (f := fun t : ℝ => t)
  have he' : G.bottleneck u v = a := by simpa [bottleneck, hne] using he
  rw [he'] at hp ⊢
  rcases Finset.mem_insert.mp ha with hz | ha
  · exact (ne_of_gt hp hz).elim
  · exact (Finset.mem_filter.mp ha).2

/-- Positive thresholds characterize the bottleneck exactly. -/
theorem le_bottleneck_iff (G : WeightedGraph V) {u v : V} (hne : u ≠ v)
    {t : ℝ} (ht : 0 < t) :
    t ≤ G.bottleneck u v ↔ (G.threshold t).Reachable u v := by
  constructor
  · intro h
    exact (G.reachable_bottleneck (ht.trans_le h)).mono (G.threshold_antitone h)
  · exact G.le_bottleneck_of_reachable hne

theorem bottleneck_pos_iff (G : WeightedGraph V) {u v : V} (hne : u ≠ v) :
    0 < G.bottleneck u v ↔ G.support.Reachable u v := by
  constructor
  · intro hp
    exact (G.reachable_bottleneck hp).mono (G.threshold_le_support _)
  · intro hr
    obtain ⟨a, _, hp, _, ha⟩ := G.exists_edgeLevel_of_reachable
      (t := 0) (by simpa using hr) hne
    exact hp.trans_le (G.le_bottleneck_of_reachable hne ha)

theorem bottleneck_eq_zero_iff (G : WeightedGraph V) {u v : V} (hne : u ≠ v) :
    G.bottleneck u v = 0 ↔ ¬G.support.Reachable u v := by
  rw [← G.bottleneck_pos_iff hne, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h (G.bottleneck_nonneg u v)⟩

/-- Every positive scale returned by the forest is one of its observed edge weights. -/
theorem bottleneck_mem_edgeLevels (G : WeightedGraph V) {u v : V}
    (hp : 0 < G.bottleneck u v) : G.bottleneck u v ∈ G.edgeLevels := by
  have hne : u ≠ v := by intro he; subst v; simpa using hp
  have hm : G.bottleneck u v ∈ G.bottleneckLevels u v := by
    obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup'
      (show (G.bottleneckLevels u v).Nonempty from ⟨0, Finset.mem_insert_self _ _⟩)
        (f := fun t : ℝ => t)
    simpa only [bottleneck, ite_eq_right hne, he] using ha
  rcases Finset.mem_insert.mp hm with he | hm
  · exact (ne_of_gt hp he).elim
  · exact (Finset.mem_filter.mp hm).1

theorem IsSubgraph.bottleneck_le {G H : WeightedGraph V} (h : G.IsSubgraph H) (u v : V) :
    G.bottleneck u v ≤ H.bottleneck u v := by
  by_cases hp : 0 < G.bottleneck u v
  · have hne : u ≠ v := by intro he; subst v; simpa using hp
    exact H.le_bottleneck_of_reachable hne
      ((G.reachable_bottleneck hp).mono (h.threshold_le _))
  · exact (le_of_not_gt hp).trans (H.bottleneck_nonneg u v)

theorem strongRelated_of_threshold_reachable (G : WeightedGraph V) {t : ℝ} {u v : V}
    (h : (G.threshold t).Reachable u v) : G.StrongRelated t u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact G.strongRelated_refl _ _
  | @cons a b c hab p ih =>
      exact (show G.StrongRelated t a b from
        ⟨{a, b}, (G.isStrong_pair a b).mono hab.2, by simp⟩).trans ih

/-- A path's bottleneck lower-bounds pair strength, including nonedges. -/
theorem bottleneck_le_strength (G : WeightedGraph V) (u v : V) :
    G.bottleneck u v ≤ G.strength u v := by
  by_cases hp : 0 < G.bottleneck u v
  · have hne : u ≠ v := by intro he; subst v; simpa using hp
    exact (G.le_strength_iff hne _).mpr
      (G.strongRelated_of_threshold_reachable (G.reachable_bottleneck hp))
  · exact (le_of_not_gt hp).trans (G.strength_nonneg u v)

/-- A uniform edge lower bound transfers to every connected distinct pair. -/
theorem le_bottleneck_of_edges (G : WeightedGraph V) {t : ℝ} {u v : V}
    (hne : u ≠ v) (hr : G.support.Reachable u v)
    (h : ∀ a b, G.support.Adj a b → t ≤ G.w a b) : t ≤ G.bottleneck u v := by
  apply G.le_bottleneck_of_reachable hne
  exact hr.mono (fun a b hab =>
    ⟨lt_of_le_of_ne (G.nonneg a b) (Ne.symm hab), h a b hab⟩)

end
end CutQueryComplexity.WeightedGraph
