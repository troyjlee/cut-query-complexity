import CutQueryComplexity.Sparsification.EstimateLift

/-! # One estimation call as a cut-query program

`estimateCall` makes one query, the cut of the region, and computes the residual
mass `M` from the cached block cuts. Then:

1. If `M < κ/2`, it skips sampling and returns the zero graph, so nothing merges.
2. Otherwise it takes `r = ⌈ρM/κ⌉` residual draws, provided `r ≤ R`.
3. If `r > R`, it aborts with `none`. This hard cap fixes the worst-case budget
   `R · residualDrawCost + 1` independently of the hidden weights.

The returned block graph `X` defines the merge: `u` and `v` share a new block iff
`X.StrongRelated (3κ/4) (π u) (π v)`.

`estimateCall_sound` bounds the probability of a merge that is not truly
`κ/2`-strong, assuming the old region blocks lie in true `κ/2`-components. `estimateCall_complete`
bounds the probability that the call aborts or leaves a fixed `κ`-strong set
unmerged, assuming the cap does not bind for the true mass. Both use the exact
cached-mass formula; neither assumes independence between different calls.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B]

/-- Residual mass computed from the cache and the queried region cut. -/
def cachedMass (cache : B → ℝ) (T : Finset B) (c : ℝ) : ℝ := ((∑ b ∈ T, cache b) - c) / 2

theorem cachedMass_eq (G : WeightedGraph V) (π : V → B) (cache : B → ℝ)
    (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B) :
    cachedMass cache T (G.cut (pull π T)) = (G.contract π).internalMass T := by
  rw [residual_mass_formula, cachedMass]
  simp only [hc]

theorem cachedMass_pos {M κ : ℝ} (hκ : 0 < κ) (h : ¬M < κ / 2) : 0 < M := by
  have := not_lt.mp h
  linarith

/-- One estimation call with skip rule and hard cap `R` on the number of draws. -/
def estimateCall (kb kv : ℕ) (π : V → B) (cache : B → ℝ) (T : Finset B) {κ : ℝ}
    (hκ : 0 < κ) (ρ : ℝ) (R : ℕ) :
    RTree (Finset V) ℝ (Option (WeightedGraph B)) (R * residualDrawCost kb kv + 1) :=
  RTree.query (pull π T) fun c =>
    if hM : cachedMass cache T c < κ / 2 then RTree.pure (PMF.pure (some 0))
    else if hr : ⌈ρ * cachedMass cache T c / κ⌉₊ ≤ R then
      ((residualDraws kb kv π cache T (cachedMass cache T c / ⌈ρ * cachedMass cache T c / κ⌉₊)
        (div_nonneg (cachedMass_pos hκ hM).le (Nat.cast_nonneg _))
        ⌈ρ * cachedMass cache T c / κ⌉₊).weaken (Nat.mul_le_mul_right _ hr)).map some
    else RTree.pure (PMF.pure none)

omit [Fintype V] [DecidableEq V] [Fintype B] in
theorem strongRelated_zero {b c : B} {θ : ℝ} (hθ : 0 < θ)
    (h : (0 : WeightedGraph B).StrongRelated θ b c) : b = c :=
  StrongRelated.eq_of_not_mem (T := ∅) (by ext; simp [induce]) hθ h (Finset.notMem_empty b)

omit [Fintype V] [DecidableEq V] [Fintype B] in
theorem mass_pure_le {α : Type} (a : α) (P : α → Prop) (h : ¬P a) (c : ℝ≥0∞) :
    Probability.mass (PMF.pure a) P ≤ c := by
  simp [mass_pure, h]

/-- The sampling branch, with the computed mass abstracted by an equation. -/
theorem estimateCall_sample_sound (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (hblocks : ∀ u v, π u ∈ T → π u = π v → G.StrongRelated (κ / 2) u v) (m : ℝ)
    (hm : m = (G.contract π).internalMass T) (hM : ¬m < κ / 2) :
    Probability.mass ((residualDraws kb kv π cache T (m / ⌈ρ * m / κ⌉₊)
        (div_nonneg (cachedMass_pos hκ hM).le (Nat.cast_nonneg _)) ⌈ρ * m / κ⌉₊).eval G.cut)
      (fun X => ¬∀ u v, π u ∈ T → X.StrongRelated (3 * κ / 4) (π u) (π v) →
        G.StrongRelated (κ / 2) u v) ≤
      ((T.card - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ρ / 32))) := by
  subst hm
  exact residualDraws_merge_sound G kb kv π cache hc T hB hV (cachedMass_pos hκ hM) hκ hρ hblocks

theorem estimateCall_sample_complete (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) {κ ρ δ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2)
    (hexp : ((2 * Fintype.card B : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ / 4)
    (𝒰 : Finset (Finset V)) (h𝒰 : ∀ U ∈ 𝒰, G.IsStrong κ U ∧ U.image π ⊆ T) (m : ℝ)
    (hm : m = (G.contract π).internalMass T) (hM : ¬m < κ / 2) :
    Probability.mass ((residualDraws kb kv π cache T (m / ⌈ρ * m / κ⌉₊)
        (div_nonneg (cachedMass_pos hκ hM).le (Nat.cast_nonneg _)) ⌈ρ * m / κ⌉₊).eval G.cut)
      (fun X => ¬∀ U ∈ 𝒰, ∀ u ∈ U, ∀ v ∈ U, X.StrongRelated (3 * κ / 4) (π u) (π v)) ≤
      (𝒰.card : ℝ≥0∞) * ENNReal.ofReal ((Fintype.card B - 1 : ℕ) * δ) := by
  subst hm
  exact residualDraws_merge_complete G kb kv π cache hc T hB hV (cachedMass_pos hκ hM) hκ hρ
    hδ hδ2 hexp 𝒰 h𝒰

/-- **Soundness of one call.** -/
theorem estimateCall_sound (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (R : ℕ) (hblocks : ∀ u v, π u ∈ T → π u = π v → G.StrongRelated (κ / 2) u v) :
    Probability.mass ((estimateCall kb kv π cache T hκ ρ R).eval G.cut)
      (fun o => ∃ X, o = some X ∧ ¬∀ u v, π u ∈ T →
        X.StrongRelated (3 * κ / 4) (π u) (π v) → G.StrongRelated (κ / 2) u v) ≤
      ((T.card - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ρ / 32))) := by
  rw [estimateCall, RTree.eval_query]
  have hm := cachedMass_eq G π cache hc T
  split_ifs with hM hr
  · -- Skip: the zero graph merges only equal blocks, which are already strong.
    rw [RTree.eval_pure]
    apply mass_pure_le
    rintro ⟨X, hX, hbad⟩
    cases hX
    apply hbad
    intro u v huT h
    have he := strongRelated_zero (by positivity) h
    exact hblocks u v huT he
  · -- Sample: the event is exactly the residual program's soundness event.
    rw [RTree.eval_map, RTree.eval_weaken, mass_map]
    simp only [Option.some.injEq, exists_eq_left']
    exact estimateCall_sample_sound G kb kv π cache hc T hB hV hκ hρ hblocks _ hm hM
  · rw [RTree.eval_pure]
    apply mass_pure_le
    rintro ⟨X, hX, _⟩
    cases hX

/-- **Completeness of one call**, for a fixed family of `κ`-strong sets in the region,
when the cap does not bind for the true residual mass. -/
theorem estimateCall_complete (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) {κ ρ δ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2)
    (hexp : ((2 * Fintype.card B : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ / 4) (R : ℕ)
    (hR : ⌈ρ * (G.contract π).internalMass T / κ⌉₊ ≤ R)
    (𝒰 : Finset (Finset V)) (h𝒰 : ∀ U ∈ 𝒰, G.IsStrong κ U ∧ U.image π ⊆ T) :
    Probability.mass ((estimateCall kb kv π cache T hκ ρ R).eval G.cut)
      (fun o => ¬∃ X, o = some X ∧
        ∀ U ∈ 𝒰, ∀ u ∈ U, ∀ v ∈ U, X.StrongRelated (3 * κ / 4) (π u) (π v)) ≤
      (𝒰.card : ℝ≥0∞) * ENNReal.ofReal ((Fintype.card B - 1 : ℕ) * δ) := by
  rw [estimateCall, RTree.eval_query]
  have hm := cachedMass_eq G π cache hc T
  split_ifs with hM hr
  · -- Skip: every `κ`-strong set of the region already lies in one block.
    rw [RTree.eval_pure]
    apply mass_pure_le
    push Not
    refine ⟨0, rfl, fun U hU u hu v hv => ?_⟩
    rw [hm] at hM
    have he := same_block_of_mass_lt G π (by linarith) (h𝒰 U hU).1 (h𝒰 U hU).2 hu hv
    rw [he]
    exact (0 : WeightedGraph B).strongRelated_refl _ _
  · rw [RTree.eval_map, RTree.eval_weaken, mass_map]
    simp only [Option.some.injEq, exists_eq_left']
    exact estimateCall_sample_complete G kb kv π cache hc T hB hV hκ hρ hδ hδ2 hexp 𝒰 h𝒰 _ hm hM
  · rw [hm] at hr
    exact absurd hR hr

theorem estimateCall_sample_induce (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (m : ℝ) (hm : m = (G.contract π).internalMass T) (hM : ¬m < κ / 2)
    {X : WeightedGraph B}
    (hX : X ∈ ((residualDraws kb kv π cache T (m / ⌈ρ * m / κ⌉₊)
        (div_nonneg (cachedMass_pos hκ hM).le (Nat.cast_nonneg _)) ⌈ρ * m / κ⌉₊).eval
          G.cut).support) : X.induce T = X := by
  subst hm
  exact residualDraws_induce G kb kv π cache hc T hB hV _
    (drawCount_pos hρ (cachedMass_pos hκ hM) hκ) (cachedMass_pos hκ hM) hX

/-- Every graph returned by a call is supported inside its region. -/
theorem estimateCall_support (G : WeightedGraph V) (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (fiber π b)) (T : Finset B)
    (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (R : ℕ) {X : WeightedGraph B}
    (hX : some X ∈ ((estimateCall kb kv π cache T hκ ρ R).eval G.cut).support) :
    X.induce T = X := by
  rw [estimateCall, RTree.eval_query] at hX
  have hm := cachedMass_eq G π cache hc T
  split_ifs at hX with hM hr
  · rw [RTree.eval_pure, PMF.mem_support_pure_iff] at hX
    cases hX
    ext a b
    simp [induce]
  · rw [RTree.eval_map, RTree.eval_weaken] at hX
    obtain ⟨Y, hY, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hX
    cases he
    exact estimateCall_sample_induce G kb kv π cache hc T hB hV hκ hρ _ hm hM hY
  · rw [RTree.eval_pure, PMF.mem_support_pure_iff] at hX
    cases hX

end
end CutQueryComplexity.WeightedGraph
