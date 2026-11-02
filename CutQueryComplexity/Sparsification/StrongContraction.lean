import CutQueryComplexity.Sparsification.StrengthRestriction

/-! # Strong sets under contraction

Contraction can only increase the strength of a pair whose images remain
distinct. This module keeps the public block map explicit, including empty
fibers; no surjectivity assumption is needed for the monotonicity result.
-/

namespace CutQueryComplexity
namespace WeightedGraph

noncomputable section
open scoped Classical
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

@[simp] theorem pull_inter (π : V → B) (S T : Finset B) :
    pull π (S ∩ T) = pull π S ∩ pull π T := by ext; simp

@[simp] theorem pull_sdiff (π : V → B) (S T : Finset B) :
    pull π (S \ T) = pull π S \ pull π T := by ext; simp

theorem cross_contract (G : WeightedGraph V) (π : V → B) {S T : Finset B}
    (h : Disjoint S T) :
    (G.contract π).cross S T = G.cross (pull π S) (pull π T) := by
  rw [← cross_fibers]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  have hne : b ≠ c := by intro he; exact Finset.disjoint_left.mp h hb (he ▸ hc)
  simp [contract, hne]

/-- Induced quotient cuts lift to induced original cuts on unions of blocks. -/
theorem localCut_contract (G : WeightedGraph V) (π : V → B) (U S : Finset B) :
    (G.contract π).localCut U S = G.localCut (pull π U) (pull π S) := by
  unfold localCut
  rw [cross_contract, pull_inter, pull_sdiff]
  exact Finset.disjoint_left.mpr
    (fun b hb hc => (Finset.mem_sdiff.mp hc).2 (Finset.mem_inter.mp hb).1)

/-- The image of a strong set is strong, even when additional vertices are in
the same blocks. Such additional edges only increase the relevant cuts. -/
theorem IsStrong.contract {G : WeightedGraph V} {κ : ℝ} {U : Finset V}
    (h : G.IsStrong κ U) (π : V → B) : (G.contract π).IsStrong κ (U.image π) := by
  intro S hS hT
  obtain ⟨b, hb⟩ := hS
  obtain ⟨c, hc⟩ := hT
  obtain ⟨hbS, hbU⟩ := Finset.mem_inter.mp hb
  obtain ⟨hcU, hcS⟩ := Finset.mem_sdiff.mp hc
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hbU
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hcU
  have hsub : U ⊆ pull π (U.image π) := by
    intro a ha
    exact (mem_pull _ _ _).mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  rw [localCut_contract]
  exact (h (pull π S)
    ⟨u, Finset.mem_inter.mpr ⟨(mem_pull _ _ _).mpr hbS, hu⟩⟩
    ⟨v, Finset.mem_sdiff.mpr ⟨hv, by simpa using hcS⟩⟩).trans
    (G.localCut_mono hsub (pull π S))

theorem strength_le_contract (G : WeightedGraph V) (π : V → B) {u v : V}
    (hne : π u ≠ π v) : G.strength u v ≤ (G.contract π).strength (π u) (π v) := by
  have huv : u ≠ v := fun h => hne (congrArg π h)
  obtain ⟨U, hu, hv, he⟩ := G.exists_strength_set huv
  have hU : G.IsStrong (G.strength u v) U := he ▸ G.isStrong_inducedMincut U
  exact (hU.contract π).le_strength hne (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
    (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

/-- Lifting a strong quotient set through strong blocks preserves the smaller
of the two thresholds. Every cut either splits a block or descends to the quotient. -/
theorem IsStrong.pullback {G : WeightedGraph V} {κ τ : ℝ} {U : Finset B}
    (π : V → B) (hQ : (G.contract π).IsStrong τ U)
    (hblock : ∀ b ∈ U, G.IsStrong κ (fiber π b)) :
    G.IsStrong (min κ τ) (pull π U) := by
  intro S hS hR
  by_cases hsplit : ∃ b ∈ U, (S ∩ fiber π b).Nonempty ∧ (fiber π b \ S).Nonempty
  · obtain ⟨b, hb, hleft, hright⟩ := hsplit
    have hsub : fiber π b ⊆ pull π U := by
      intro v hv
      exact (mem_pull _ _ _).mpr ((mem_fiber _ _ _).mp hv ▸ hb)
    exact (min_le_left κ τ).trans
      ((hblock b hb S hleft hright).trans (G.localCut_mono hsub S))
  · let T := U.filter (fun b => (S ∩ fiber π b).Nonempty)
    have hm (v : V) (hv : v ∈ pull π U) : π v ∈ T ↔ v ∈ S := by
      constructor
      · intro ht
        have hb := (Finset.mem_filter.mp ht).1
        obtain ⟨a, ha⟩ := (Finset.mem_filter.mp ht).2
        by_contra hn
        exact hsplit ⟨π v, hb, ⟨a, ha⟩,
          ⟨v, Finset.mem_sdiff.mpr ⟨by simp, hn⟩⟩⟩
      · intro hs
        exact Finset.mem_filter.mpr ⟨(mem_pull _ _ _).mp hv,
          ⟨v, Finset.mem_inter.mpr ⟨hs, by simp⟩⟩⟩
    have heL : pull π T ∩ pull π U = S ∩ pull π U := by
      ext v
      by_cases hv : v ∈ pull π U
      · simp only [Finset.mem_inter, hv, and_true, mem_pull]
        exact hm v hv
      · simp [hv]
    have heR : pull π U \ pull π T = pull π U \ S := by
      ext v
      by_cases hv : v ∈ pull π U
      · simp only [Finset.mem_sdiff, hv, true_and, mem_pull]
        exact not_congr (hm v hv)
      · simp [hv]
    have hc : (G.contract π).localCut U T = G.localCut (pull π U) S := by
      rw [localCut_contract, localCut, heL, heR]
      rfl
    obtain ⟨a, ha⟩ := hS
    obtain ⟨b, hb⟩ := hR
    have hT : (T ∩ U).Nonempty := by
      exact ⟨π a, Finset.mem_inter.mpr
        ⟨(hm a (Finset.mem_inter.mp ha).2).mpr (Finset.mem_inter.mp ha).1,
          (mem_pull _ _ _).mp (Finset.mem_inter.mp ha).2⟩⟩
    have hU : (U \ T).Nonempty := by
      exact ⟨π b, Finset.mem_sdiff.mpr
        ⟨(mem_pull _ _ _).mp (Finset.mem_sdiff.mp hb).1,
          fun h => (Finset.mem_sdiff.mp hb).2 ((hm b (Finset.mem_sdiff.mp hb).1).mp h)⟩⟩
    exact (min_le_right κ τ).trans (hc ▸ hQ T hT hU)

/-- Contracting strong blocks preserves every weaker pair strength
(BK Lemma 4.6). The endpoints must remain in distinct blocks. -/
theorem strength_contract_of_lt (G : WeightedGraph V) (π : V → B) {κ : ℝ}
    (hblock : ∀ b, G.IsStrong κ (fiber π b)) {u v : V}
    (hne : π u ≠ π v) (hweak : G.strength u v < κ) :
    (G.contract π).strength (π u) (π v) = G.strength u v := by
  apply le_antisymm ?_ (G.strength_le_contract π hne)
  obtain ⟨U, hu, hv, he⟩ := (G.contract π).exists_strength_set hne
  have hU : (G.contract π).IsStrong ((G.contract π).strength (π u) (π v)) U :=
    he ▸ (G.contract π).isStrong_inducedMincut U
  have hlower := (hU.pullback π (fun b _ => hblock b)).le_strength
    (fun h => hne (congrArg π h)) ((mem_pull _ _ _).mpr hu) ((mem_pull _ _ _).mpr hv)
  rcases le_total κ ((G.contract π).strength (π u) (π v)) with h | h
  · rw [min_eq_left h] at hlower
    exact (not_le_of_gt hweak hlower).elim
  · simpa [min_eq_right h] using hlower

end
end WeightedGraph
end CutQueryComplexity
