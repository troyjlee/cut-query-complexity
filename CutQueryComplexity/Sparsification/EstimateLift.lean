import CutQueryComplexity.Sparsification.EstimateProgram
import CutQueryComplexity.Sparsification.StrongContraction

/-! # The estimation contract on original vertices

After sampling `X` on the block labels, the call merges the blocks of each
`3κ/4`-strong component of `X`. Two original vertices then share a new block
exactly when `X.StrongRelated (3κ/4) (π u) (π v)`.

* **Soundness.** If each old block of the region lies inside a true `κ/2`-strong
  component of `G`, every newly merged pair is `κ/2`-strongly related in `G`. The
  sampled strong set lies in a `κ/2`-strong quotient set. `IsStrong.pullback_related`
  lifts it: the union of the true components of its vertices is `κ/2`-strong.
* **Completeness.** Each set in a fixed family of `κ`-strong original sets inside the
  region has all its blocks merged.
* **Skip rule.** If the residual mass is below `κ`, every `κ`-strong quotient set in
  the region is a single block. Completeness then holds with no sampling at all.

Samples are supported inside the region, so a sampled strong set meeting the
region lies entirely inside it, and vertices outside stay unmerged.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B]

/-! ### Deterministic facts -/

omit [Fintype B] in
/-- A positive-threshold strong set of a graph supported in `T` stays in `T` once it meets it. -/
theorem IsStrong.subset_of_support [DecidableEq B] {X : WeightedGraph B} {T K : Finset B} {θ : ℝ}
    (hX : X.induce T = X) (hθ : 0 < θ) (hK : X.IsStrong θ K) {b : B} (hb : b ∈ K)
    (hbT : b ∈ T) : K ⊆ T := by
  intro c hc
  by_contra hcT
  have hcut := hK (K ∩ T) ⟨b, by simp [hb, hbT]⟩ ⟨c, by simp [hc, hcT]⟩
  have hz : X.localCut K (K ∩ T) = 0 := by
    unfold localCut cross
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    have hvT : v ∉ T := by
      simp only [Finset.mem_sdiff, Finset.mem_inter, not_and] at hv
      exact fun h => hv.2 hv.1 h
    have e : (X.induce T).w u v = X.w u v := by rw [hX]
    change (if u ∈ T ∧ v ∈ T then X.w u v else 0) = X.w u v at e
    simp only [show ¬(u ∈ T ∧ v ∈ T) from fun h => hvT h.2, ↓reduceIte] at e
    exact e.symm
  linarith

omit [Fintype B] in
/-- Outside the region, a positive-threshold strong relation is trivial. -/
theorem StrongRelated.eq_of_not_mem [DecidableEq B] {X : WeightedGraph B} {T : Finset B} {θ : ℝ}
    (hX : X.induce T = X) (hθ : 0 < θ) {b c : B} (h : X.StrongRelated θ b c)
    (hb : b ∉ T) : b = c := by
  obtain ⟨K, hK, hbK, hcK⟩ := h
  by_contra hbc
  have hcut := hK {b} ⟨b, by simp [hbK]⟩ ⟨c, by simp [hcK, Ne.symm hbc]⟩
  have hz : X.localCut K {b} = 0 := by
    unfold localCut cross
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v _
    have hu' : u = b := by simpa using (Finset.mem_inter.mp hu).1
    have e : (X.induce T).w u v = X.w u v := by rw [hX]
    simp only [induce, hu', hb, false_and, ↓reduceIte] at e
    rw [hu']
    exact e.symm
  linarith

/-- Lifting a strong quotient set whose blocks lie inside true strong components.
The blocks need not be strong themselves: the union of the components of the
lifted vertices is strong. A cut either splits a component or respects all of them,
and then it descends to a quotient cut of the same or smaller weight. -/
theorem IsStrong.pullback_related {G : WeightedGraph V} {κ : ℝ} {W : Finset B} (π : V → B)
    (hQ : (G.contract π).IsStrong κ W)
    (hrel : ∀ u v, π u ∈ W → π u = π v → G.StrongRelated κ u v) :
    ∃ U, pull π W ⊆ U ∧ G.IsStrong κ U := by
  set U := (pull π W).biUnion (G.strongComponent κ)
  refine ⟨U, fun v hv => Finset.mem_biUnion.mpr ⟨v, hv, G.mem_strongComponent_self κ v⟩, ?_⟩
  intro S hS hT
  have hCU {v : V} (hv : v ∈ pull π W) : G.strongComponent κ v ⊆ U :=
    Finset.subset_biUnion_of_mem _ hv
  by_cases hsplit : ∃ v ∈ pull π W, (S ∩ G.strongComponent κ v).Nonempty ∧
      (G.strongComponent κ v \ S).Nonempty
  · obtain ⟨v, hv, h1, h2⟩ := hsplit
    exact (G.strongComponent_strong κ v S h1 h2).trans (G.localCut_mono (hCU hv) S)
  push Not at hsplit
  -- Every component of a lifted vertex lies inside `S` or outside it.
  have hside {v x : V} (hv : v ∈ pull π W) (hx : x ∈ G.strongComponent κ v) :
      x ∈ S ↔ v ∈ S := by
    constructor
    · intro hxS
      have hsub := hsplit v hv ⟨x, Finset.mem_inter.mpr ⟨hxS, hx⟩⟩
      by_contra hvS
      exact (Finset.notMem_empty v) (hsub ▸ Finset.mem_sdiff.mpr
        ⟨G.mem_strongComponent_self κ v, hvS⟩)
    · intro hvS
      have hsub := hsplit v hv ⟨v, Finset.mem_inter.mpr ⟨hvS, G.mem_strongComponent_self κ v⟩⟩
      by_contra hxS
      exact (Finset.notMem_empty x) (hsub ▸ Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
  have hmemU {x : V} (hx : x ∈ U) : ∃ v ∈ pull π W, x ∈ G.strongComponent κ v :=
    Finset.mem_biUnion.mp hx
  set S' := W.filter (fun b => ∃ w, π w = b ∧ w ∈ S)
  have hkey {v : V} (hv : v ∈ pull π W) : π v ∈ S' ↔ v ∈ S := by
    constructor
    · intro h
      obtain ⟨w, hw, hwS⟩ := (Finset.mem_filter.mp h).2
      have hwW : w ∈ pull π W := (mem_pull _ _ _).mpr (hw ▸ (mem_pull _ _ _).mp hv)
      have hrel' := hrel w v ((mem_pull _ _ _).mp hwW) hw
      exact (hside hwW ((G.mem_strongComponent κ w v).mpr hrel')).mpr hwS
    · intro h
      exact Finset.mem_filter.mpr ⟨(mem_pull _ _ _).mp hv, v, rfl, h⟩
  obtain ⟨a, ha⟩ := hS
  obtain ⟨c, hc⟩ := hT
  obtain ⟨va, hva, hav⟩ := hmemU (Finset.mem_inter.mp ha).2
  obtain ⟨vc, hvc, hcv⟩ := hmemU (Finset.mem_sdiff.mp hc).1
  have hvaS : va ∈ S := (hside hva hav).mp (Finset.mem_inter.mp ha).1
  have hvcS : vc ∉ S := fun h => (Finset.mem_sdiff.mp hc).2 ((hside hvc hcv).mpr h)
  have hq := hQ S' ⟨π va, Finset.mem_inter.mpr ⟨(hkey hva).mpr hvaS, (mem_pull _ _ _).mp hva⟩⟩
    ⟨π vc, Finset.mem_sdiff.mpr ⟨(mem_pull _ _ _).mp hvc, fun h => hvcS ((hkey hvc).mp h)⟩⟩
  rw [localCut_contract] at hq
  refine hq.trans (G.cross_mono ?_ ?_)
  · intro x hx
    obtain ⟨hxS', hxW⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨(hkey hxW).mp ((mem_pull _ _ _).mp hxS'),
      Finset.mem_biUnion.mpr ⟨x, hxW, G.mem_strongComponent_self κ x⟩⟩
  · intro x hx
    obtain ⟨hxW, hxS'⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨x, hxW, G.mem_strongComponent_self κ x⟩,
      fun h => hxS' ((mem_pull _ _ _).mpr ((hkey hxW).mpr h))⟩

/-- **Lifted soundness.** Merged pairs are truly `κ₀`-strongly related, provided each
old block of the region lies inside a true `κ₀`-strong component. -/
theorem merged_strongRelated (G : WeightedGraph V) (π : V → B) {T : Finset B}
    {X : WeightedGraph B} {θ κ₀ : ℝ} (hX : X.induce T = X) (hθ : 0 < θ)
    (hsplit : ∀ K ⊆ T, X.IsStrong θ K →
      ∃ W, K ⊆ W ∧ W ⊆ T ∧ (G.contract π).IsStrong κ₀ W)
    (hblocks : ∀ u v, π u ∈ T → π u = π v → G.StrongRelated κ₀ u v) {u v : V}
    (huT : π u ∈ T) (h : X.StrongRelated θ (π u) (π v)) : G.StrongRelated κ₀ u v := by
  obtain ⟨K, hK, hu, hv⟩ := h
  obtain ⟨W, hKW, hWT, hW⟩ := hsplit K (hK.subset_of_support hX hθ hu huT) hK
  obtain ⟨U, hWU, hU⟩ := hW.pullback_related π (fun a b ha hab => hblocks a b (hWT ha) hab)
  exact ⟨U, hU, hWU ((mem_pull _ _ _).mpr (hKW hu)), hWU ((mem_pull _ _ _).mpr (hKW hv))⟩

omit [Fintype V] [DecidableEq V] [Fintype B] in
/-- An original strong set whose image is strong in the sample has all blocks merged. -/
theorem merged_of_image_strong {π : V → B} {X : WeightedGraph B} {θ : ℝ} {U : Finset V}
    (h : X.IsStrong θ (U.image π)) {u v : V} (hu : u ∈ U) (hv : v ∈ U) :
    X.StrongRelated θ (π u) (π v) :=
  ⟨U.image π, h, Finset.mem_image_of_mem π hu, Finset.mem_image_of_mem π hv⟩

theorem cross_le_internalMass (Q : WeightedGraph B) {T S R : Finset B} (hS : S ⊆ T)
    (hR : R ⊆ T) (hd : Disjoint S R) : Q.cross S R ≤ Q.internalMass T := by
  have h1 : Q.cross S R + Q.cross R S ≤ Q.cross (S ∪ R) (S ∪ R) := by
    rw [cross_union_left _ _ _ _ hd, cross_union_right _ _ _ _ hd,
      cross_union_right _ _ _ _ hd]
    linarith [Q.cross_nonneg S S, Q.cross_nonneg R R]
  have h2 := Q.cross_mono (Finset.union_subset hS hR) (Finset.union_subset hS hR)
  rw [Q.cross_comm R S] at h1
  unfold internalMass
  linarith

/-- **Skip rule.** Residual mass below `κ` leaves no `κ`-strong set of two blocks. -/
theorem card_le_one_of_mass_lt {Q : WeightedGraph B} {T C : Finset B} {κ : ℝ}
    (hM : Q.internalMass T < κ) (hCT : C ⊆ T) (hC : Q.IsStrong κ C) : C.card ≤ 1 := by
  by_contra hn
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp (not_le.mp hn)
  have hcut := hC {b} ⟨b, by simp [hb]⟩ ⟨c, by simp [hc, Ne.symm hbc]⟩
  have hle : Q.localCut C {b} ≤ Q.internalMass T :=
    Q.cross_le_internalMass (Finset.inter_subset_right.trans hCT)
      (Finset.sdiff_subset.trans hCT)
      (Finset.disjoint_left.mpr (by intro x hx hx'; simp_all))
  linarith

/-- With residual mass below `κ`, a `κ`-strong original set in the region already
lies in one block. -/
theorem same_block_of_mass_lt (G : WeightedGraph V) (π : V → B) {T : Finset B} {κ : ℝ}
    (hM : (G.contract π).internalMass T < κ) {U : Finset V} (hU : G.IsStrong κ U)
    (hUT : U.image π ⊆ T) {u v : V} (hu : u ∈ U) (hv : v ∈ U) : π u = π v :=
  Finset.card_le_one.mp (card_le_one_of_mass_lt hM hUT (hU.contract π)) _
    (Finset.mem_image_of_mem π hu) _ (Finset.mem_image_of_mem π hv)

/-! ### Probability on original vertices -/

theorem residualDraws_induce (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) (r : ℕ) (hr : 0 < r)
    (hM : 0 < (G.contract π).internalMass T) {X : WeightedGraph B}
    (hX : X ∈ ((residualDraws kb kv π cache T ((G.contract π).internalMass T / r)
      (by positivity) r).eval G.cut).support) : X.induce T = X := by
  rw [CountedBucket.residualDraws_eval_eq_sampleLaw G kb kv π cache hc T hB hV r hr hM] at hX
  have hs := CountedBucket.sampleLaw_support _ hX
  rw [CountedBucket.residualBucket_reference] at hs
  apply induce_eq_self_of_support _ hs
  ext a b
  by_cases h : a ∈ T ∧ b ∈ T <;> simp [induce, h]

/-- **Soundness of one sampled call on original vertices.** -/
theorem residualDraws_merge_sound (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hM : 0 < (G.contract π).internalMass T) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    (hblocks : ∀ u v, π u ∈ T → π u = π v → G.StrongRelated (κ / 2) u v) :
    Probability.mass
      ((residualDraws kb kv π cache T
        ((G.contract π).internalMass T / ⌈ρ * (G.contract π).internalMass T / κ⌉₊)
        (by positivity) ⌈ρ * (G.contract π).internalMass T / κ⌉₊).eval G.cut)
      (fun X => ¬∀ u v, π u ∈ T → X.StrongRelated (3 * κ / 4) (π u) (π v) →
        G.StrongRelated (κ / 2) u v) ≤
      ((T.card - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ρ / 32))) := by
  refine le_trans (mass_mono_on_support _ (fun X hX hbad => ?_))
    (residualDraws_sound G kb kv π cache hc T hB hV hM hκ hρ)
  intro hsplit
  apply hbad
  intro u v huT h
  exact merged_strongRelated G π
    (residualDraws_induce G kb kv π cache hc T hB hV _ (drawCount_pos hρ hM hκ) hM hX)
    (by positivity) hsplit hblocks huT h

/-- **Completeness of one sampled call on original vertices**, for a fixed family of
`κ`-strong sets inside the region. -/
theorem residualDraws_merge_complete (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hM : 0 < (G.contract π).internalMass T) {κ ρ δ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2)
    (hexp : ((2 * Fintype.card B : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ / 4)
    (𝒰 : Finset (Finset V)) (h𝒰 : ∀ U ∈ 𝒰, G.IsStrong κ U ∧ U.image π ⊆ T) :
    Probability.mass
      ((residualDraws kb kv π cache T
        ((G.contract π).internalMass T / ⌈ρ * (G.contract π).internalMass T / κ⌉₊)
        (by positivity) ⌈ρ * (G.contract π).internalMass T / κ⌉₊).eval G.cut)
      (fun X => ¬∀ U ∈ 𝒰, ∀ u ∈ U, ∀ v ∈ U, X.StrongRelated (3 * κ / 4) (π u) (π v)) ≤
      (𝒰.card : ℝ≥0∞) * ENNReal.ofReal ((Fintype.card B - 1 : ℕ) * δ) := by
  apply mass_failure_le_card_mul _ 𝒰 (fun U X => X.IsStrong (3 * κ / 4) (U.image π))
  · intro X _ hall U hU u hu v hv
    exact merged_of_image_strong (hall U hU) hu hv
  · intro U hU
    exact failure_le_of_success _ _ (by positivity)
      (residualDraws_complete G kb kv π cache hc T hB hV hM hκ hρ hδ hδ2 hexp
        (h𝒰 U hU).2 ((h𝒰 U hU).1.contract π))

end
end CutQueryComplexity.WeightedGraph
