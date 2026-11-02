import CutQueryComplexity.Primitive.ResidualCache
import CutQueryComplexity.Graph.InducedCut

/-! # Cut shores that survive block contractions

A shore respects a block map when membership is constant on each fiber.
Such shores are encoded injectively by subsets of the live labels. Merging
two labels retains every respecting shore that puts them on the same side.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
open WeightedGraph
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def RespectsBlocks (π : V → B) (S : Finset V) : Prop :=
  ∀ u v, π u = π v → (u ∈ S ↔ v ∈ S)

@[simp] theorem respectsBlocks_id (S : Finset V) : RespectsBlocks id S := by
  intro u v h
  have he : u = v := h
  subst v
  rfl

theorem RespectsBlocks.mem_image {π : V → B} {S : Finset V} (h : RespectsBlocks π S)
    (v : V) : π v ∈ S.image π ↔ v ∈ S := by
  constructor
  · intro hv
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    exact (h u v he).mp hu
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem RespectsBlocks.pull_image {π : V → B} {S : Finset V} (h : RespectsBlocks π S) :
    pull π (S.image π) = S := by
  ext v
  exact (mem_pull _ _ _).trans (h.mem_image v)

theorem RespectsBlocks.merge_pair {π : V → B} {S : Finset V} (h : RespectsBlocks π S)
    {a b : B} (hab : a ∈ S.image π ↔ b ∈ S.image π) :
    RespectsBlocks (mergeBlocks π {a, b} a) S := by
  have hm (v : V) : mergeBlocks π {a, b} a v ∈ S.image π ↔ v ∈ S := by
    rw [← h.mem_image v]
    by_cases ha : π v = a
    · simp [mergeBlocks, ha]
    · by_cases hb : π v = b
      · simpa [mergeBlocks, hb] using hab
      · simp [mergeBlocks, ha, hb]
  intro u v he
  exact (hm u).symm.trans (he ▸ hm v)

theorem card_respecting_le (π : V → B) (A : Finset (Finset V))
    (hA : ∀ S ∈ A, RespectsBlocks π S) : A.card ≤ 2 ^ (liveBlocks π).card := by
  have hinj : Set.InjOn (fun S : Finset V => S.image π) A := by
    intro S hS T hT he
    change S.image π = T.image π at he
    rw [← (hA S hS).pull_image, ← (hA T hT).pull_image, he]
  calc
    A.card = (A.image (fun S => S.image π)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((liveBlocks π).powerset).card := by
      apply Finset.card_le_card
      intro T hT
      obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hT
      rw [Finset.mem_powerset]
      exact Finset.image_subset_image (Finset.subset_univ S)
    _ = _ := Finset.card_powerset _

theorem liveBlocks_merge_pair_card (π : V → B) {a b : B}
    (ha : a ∈ liveBlocks π) (hb : b ∈ liveBlocks π) (hne : a ≠ b) :
    (liveBlocks (mergeBlocks π {a, b} a)).card = (liveBlocks π).card - 1 := by
  have hs : ({a, b} : Finset B) ⊆ liveBlocks π := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact ha
    · exact hb
  have hn : 2 ≤ (liveBlocks π).card := by
    simpa [hne] using Finset.card_le_card hs
  rw [card_liveBlocks_merge π hs (by simp)]
  simp only [Finset.card_pair hne]
  omega

namespace WeightedGraph

theorem contract_weight_pos_labels (G : WeightedGraph V) (π : V → B) {a b : B}
    (h : 0 < (G.contract π).w a b) : a ∈ liveBlocks π ∧ b ∈ liveBlocks π ∧ a ≠ b := by
  have hne : a ≠ b := by intro he; subst b; simpa [WeightedGraph.diag] using h
  have hc : 0 < G.cross (fiber π a) (fiber π b) := by simpa [contract, hne] using h
  obtain ⟨u, hu, v, hv, _⟩ := (G.cross_pos_iff _ _).mp hc
  exact ⟨(mem_liveBlocks _ _).mpr ⟨u, (mem_fiber _ _ _).mp hu⟩,
    (mem_liveBlocks _ _).mpr ⟨v, (mem_fiber _ _ _).mp hv⟩, hne⟩

theorem fiber_proper_of_two_live (π : V → B) (hn : 2 ≤ (liveBlocks π).card)
    {a : B} (ha : a ∈ liveBlocks π) : ProperShore (fiber π a) := by
  obtain ⟨u, hu⟩ := (mem_liveBlocks _ _).mp ha
  refine ⟨⟨u, (mem_fiber _ _ _).mpr hu⟩, ?_⟩
  intro he
  have hs : liveBlocks π ⊆ {a} := by
    intro b hb
    obtain ⟨v, hv⟩ := (mem_liveBlocks _ _).mp hb
    have hva : v ∈ fiber π a := by rw [he]; simp
    simpa only [Finset.mem_singleton, ← hv] using (mem_fiber _ _ _).mp hva
  have hc := Finset.card_le_card hs
  simp only [Finset.card_singleton] at hc
  omega

/-- Every live block has degree at least the promised global minimum cut. -/
theorem contract_degree_ge (G : WeightedGraph V) (π : V → B) {κ : ℝ}
    (hκ : ∀ S, ProperShore S → κ ≤ G.cut S) (hn : 2 ≤ (liveBlocks π).card)
    {a : B} (ha : a ∈ liveBlocks π) : κ ≤ (G.contract π).degree a := by
  rw [← cut_singleton, cut_contract]
  exact hκ _ (fiber_proper_of_two_live π hn ha)

end WeightedGraph
end
end CutQueryComplexity
