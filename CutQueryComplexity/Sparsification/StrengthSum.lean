import CutQueryComplexity.Sparsification.Strength
import CutQueryComplexity.Graph.Mass

/-! # The weighted strength-sum bound

We prove BK Lemma 4.11 for arbitrary nonnegative real weights, including
disconnected graphs. A minimum cut of any induced vertex set has normalized
cost at most one. Splitting recursively along those cuts proves the bound
without an integrality, positive-mincut, or weight-spread assumption.
-/

namespace CutQueryComplexity
namespace WeightedGraph

noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A minimum original induced cut costs at most one after normalization. -/
theorem exists_normalized_localCut_le_one (G : WeightedGraph V) (U : Finset V)
    (hn : 2 ≤ U.card) :
    ∃ S, LocalShore U S ∧ G.strengthNormalized.localCut U S ≤ 1 := by
  obtain ⟨S, hS, he⟩ := G.exists_inducedMincut hn
  refine ⟨S, hS, ?_⟩
  have hmin := G.inducedMincut_nonneg U
  rw [G.strengthNormalized.localCut_of_subset hS.1]
  have hcut : G.cross S (U \ S) = G.inducedMincut U := by
    simpa [G.localCut_of_subset hS.1] using he
  by_cases hzero : G.inducedMincut U = 0
  · have hz : ∀ u ∈ S, ∀ v ∈ U \ S, G.w u v = 0 := by
      intro u hu v hv
      have hw := G.weight_le_cross hu hv
      rw [hcut, hzero] at hw
      exact le_antisymm hw (G.nonneg u v)
    have hz' : G.strengthNormalized.cross S (U \ S) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      simp [hz u hu v hv]
    rw [hz']; norm_num
  · have hp : 0 < G.inducedMincut U := lt_of_le_of_ne hmin (Ne.symm hzero)
    calc
      _ ≤ ∑ u ∈ S, ∑ v ∈ U \ S, G.w u v / G.inducedMincut U := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        have hne : u ≠ v := by intro huv; exact (Finset.mem_sdiff.mp hv).2 (huv ▸ hu)
        exact div_le_div_of_nonneg_left (G.nonneg u v) hp
          (G.inducedMincut_le_strength hne (hS.1 hu) (Finset.mem_sdiff.mp hv).1)
      _ = G.cross S (U \ S) / G.inducedMincut U := by
        simp only [cross, div_eq_mul_inv, Finset.sum_mul]
      _ = 1 := by rw [hcut, div_self hzero]

/-- The strength-sum bound holds inside every nonempty vertex set. -/
theorem strength_sum_subset (G : WeightedGraph V) (U : Finset V) (hne : U.Nonempty) :
    (∑ u ∈ U, ∑ v ∈ U, G.w u v / G.strength u v) / 2 ≤ (U.card : ℝ) - 1 :=
  G.strengthNormalized.internalMass_le_card_sub_one
    (G.exists_normalized_localCut_le_one) U hne

/-- BK's `∑_{unordered positive edges} w(e)/k(e) ≤ n-1`, with natural truncated
subtraction so the empty vertex type is covered too. The double sum counts each
unordered edge twice, and absent edges contribute zero. -/
theorem strength_sum_le (G : WeightedGraph V) :
    (∑ u, ∑ v, G.w u v / G.strength u v) / 2 ≤ (Fintype.card V - 1 : ℕ) := by
  by_cases h : (Finset.univ : Finset V).Nonempty
  · have hn : 1 ≤ Fintype.card V := Nat.succ_le_of_lt (by simpa using h.card_pos)
    simpa [Nat.cast_sub hn] using G.strength_sum_subset Finset.univ h
  · have he : (Finset.univ : Finset V) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

/-- A connected positive-mincut graph has normalized minimum cut exactly one
(BK Lemma 4.10); positivity is explicit and is not imposed on the strength sum. -/
theorem normalized_mincut_eq_one (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hmin : 0 < mincutValue G) :
    mincutValue G.strengthNormalized = 1 := by
  apply le_antisymm
  · obtain ⟨S, hS, hc⟩ := G.exists_normalized_localCut_le_one Finset.univ (by simpa)
    have hp : ProperShore S := by
      refine ⟨hS.2.1, ?_⟩
      intro he
      simpa [he] using hS.2.2
    exact (mincutValue_le _ hp).trans (by simpa using hc)
  · have hproper : (properShores V).Nonempty := by
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
      exact ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
    obtain ⟨S, hS, he⟩ := exists_isMinCut G.strengthNormalized hproper
    rw [← he]
    have hp : 0 < G.cut S := hmin.trans_le (mincutValue_le G hS.1)
    calc
      1 = G.cut S / G.cut S := (div_self (ne_of_gt hp)).symm
      _ = ∑ u ∈ S, ∑ v ∈ Sᶜ, G.w u v / G.cut S := by
        simp only [cut, div_eq_mul_inv, Finset.sum_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        change G.w u v / G.cut S ≤ G.w u v / G.strength u v
        by_cases hz : G.w u v = 0
        · simp [hz]
        · exact div_le_div_of_nonneg_left (G.nonneg u v)
            (G.strength_pos_of_weight_pos (lt_of_le_of_ne (G.nonneg u v) (Ne.symm hz)))
            (G.strength_le_cut hu (Finset.mem_compl.mp hv))

end
end WeightedGraph
end CutQueryComplexity
