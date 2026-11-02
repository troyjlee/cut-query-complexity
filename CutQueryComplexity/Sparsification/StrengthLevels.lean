import CutQueryComplexity.Sparsification.StrongComponentCount
import Mathlib.Data.Finset.Max

/-! # Finite strength levels and telescoping increments

Positive levels have a predecessor in the level set augmented by zero.
Their consecutive differences telescope exactly. This lets the decomposition
group equal components across levels without choosing parent pointers.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical

def levelBelow (levels : Finset ℝ) (t : ℝ) : ℝ :=
  (insert 0 (levels.filter (fun s => s < t))).max' (Finset.insert_nonempty _ _)

theorem levelBelow_nonneg (levels : Finset ℝ) (t : ℝ) : 0 ≤ levelBelow levels t :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem levelBelow_lt (levels : Finset ℝ) {t : ℝ} (ht : 0 < t) :
    levelBelow levels t < t := by
  apply (Finset.max'_lt_iff _ _).mpr
  intro s hs
  rcases Finset.mem_insert.mp hs with rfl | hs
  · exact ht
  · exact (Finset.mem_filter.mp hs).2

theorem levelBelow_filter_le (levels : Finset ℝ) {t k : ℝ} (h : t ≤ k) :
    levelBelow (levels.filter (fun s => s ≤ k)) t = levelBelow levels t := by
  have he : (levels.filter (fun s => s ≤ k)).filter (fun s => s < t) =
      levels.filter (fun s => s < t) := by
    ext s
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun hs => ⟨⟨hs.1, (hs.2.trans_le h).le⟩, hs.2⟩⟩
  simp only [levelBelow, he]

theorem sum_levelIncrements (levels : Finset ℝ) (hpos : ∀ t ∈ levels, 0 < t) :
    (∑ t ∈ levels, (t - levelBelow levels t)) =
      (insert 0 levels).max' (Finset.insert_nonempty _ _) := by
  induction levels using Finset.induction_on_max with
  | empty => simp [levelBelow]
  | insert a s hmax ih =>
      have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
      have ha0 := hpos a (Finset.mem_insert_self _ _)
      have hs0 : ∀ t ∈ s, 0 < t := fun t ht => hpos t (Finset.mem_insert_of_mem ht)
      have he : (insert a s).filter (fun t => t < a) = s := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | ht, hlt⟩
          · exact (lt_irrefl _ hlt).elim
          · exact ht
        · intro ht
          exact ⟨Or.inr ht, hmax t ht⟩
      have hpred : levelBelow (insert a s) a =
          (insert 0 s).max' (Finset.insert_nonempty _ _) := by
        simp only [levelBelow, he]
      have hpreds : ∀ t ∈ s, levelBelow (insert a s) t = levelBelow s t := by
        intro t ht
        have he' : (insert a s).filter (fun r => r < t) = s.filter (fun r => r < t) := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hr, hrt⟩
            · exact ((not_lt_of_ge (hmax t ht).le) hrt).elim
            · exact ⟨hr, hrt⟩
          · exact fun hr => ⟨Or.inr hr.1, hr.2⟩
        simp only [levelBelow, he']
      have htop : (insert 0 (insert a s)).max' (Finset.insert_nonempty _ _) = a := by
        apply (Finset.max'_eq_iff _ _ _).mpr
        refine ⟨by simp, ?_⟩
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact ha0.le
        · rcases Finset.mem_insert.mp ht with rfl | ht
          · exact le_rfl
          · exact (hmax t ht).le
      rw [Finset.sum_insert ha, hpred, htop]
      have heq : (∑ t ∈ s, (t - levelBelow (insert a s) t)) =
          ∑ t ∈ s, (t - levelBelow s t) :=
        Finset.sum_congr rfl fun t ht => by rw [hpreds t ht]
      rw [heq, ih hs0]
      ring

/-- The increments up to an attained level sum to that level. -/
theorem sum_levelIncrements_le (levels : Finset ℝ) (hpos : ∀ t ∈ levels, 0 < t)
    {k : ℝ} (hk : k ∈ levels) :
    (∑ t ∈ levels.filter (fun s => s ≤ k), (t - levelBelow levels t)) = k := by
  have hs : ∀ t ∈ levels.filter (fun s => s ≤ k), 0 < t :=
    fun t ht => hpos t (Finset.mem_filter.mp ht).1
  calc
    _ = ∑ t ∈ levels.filter (fun s => s ≤ k),
        (t - levelBelow (levels.filter (fun s => s ≤ k)) t) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [levelBelow_filter_le levels (Finset.mem_filter.mp ht).2]
    _ = _ := sum_levelIncrements _ hs
    _ = k := by
      apply (Finset.max'_eq_iff _ _ _).mpr
      refine ⟨by simp [hk], ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact (hpos k hk).le
      · exact (Finset.mem_filter.mp ht).2

namespace WeightedGraph
variable {V : Type} [Fintype V] [DecidableEq V]

/-- All positive pair strengths, including those of nonedges. -/
def positiveStrengths (G : WeightedGraph V) : Finset ℝ :=
  ((Finset.univ : Finset (V × V)).image (fun e => G.strength e.1 e.2)).filter (0 < ·)

@[simp] theorem mem_positiveStrengths (G : WeightedGraph V) (k : ℝ) :
    k ∈ G.positiveStrengths ↔ 0 < k ∧ ∃ u v, G.strength u v = k := by
  simp [positiveStrengths, and_comm]

@[simp] theorem positiveStrengths_zero : (0 : WeightedGraph V).positiveStrengths = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨hp, u, v, he⟩ := ((0 : WeightedGraph V).mem_positiveStrengths k).mp hk
  rw [strength_zero] at he
  exact (not_lt_of_ge (le_of_eq he.symm)) hp

theorem positiveStrengths_card_le (G : WeightedGraph V) :
    G.positiveStrengths.card ≤ Fintype.card V - 1 := by
  have hsub : G.positiveStrengths ⊆ G.strongComponents.image G.inducedMincut := by
    intro k hk
    obtain ⟨hp, u, v, rfl⟩ := (G.mem_positiveStrengths k).mp hk
    have hne : u ≠ v := by intro he; simp [he] at hp
    have hu := G.mem_strongComponent_self (G.strength u v) u
    have hv := (G.mem_strongComponent_iff_le_strength hne _).mpr le_rfl
    have hn : 2 ≤ (G.strongComponent (G.strength u v) u).card := by
      have hsub : ({u, v} : Finset V) ⊆ G.strongComponent (G.strength u v) u := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hu, hv⟩
      simpa [hne] using Finset.card_le_card hsub
    exact Finset.mem_image.mpr ⟨G.strongComponent (G.strength u v) u,
      (G.mem_strongComponents _).mpr ⟨hn, G.strength u v, hp, u, rfl⟩,
      G.strength_component_mincut hp⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le).trans G.strongComponents_card_le)

end WeightedGraph
end
end CutQueryComplexity
