import CutQueryComplexity.Sparsification.EstimationRun

/-! # The invariant of a good estimation run

`Good G H s` collects what a run state satisfies when all previous calls succeeded:

* the labeling and the exact block-cut cache;
* a positive scale `κ` with `Refines (κ/2)` and `Separated (2κ)`;
* pending regions that are unions of blocks and pairwise disjoint;
* *coverage*: every true `κ`-component is either inside one block or inside one
  pending region;
* a done state has no remaining pair.

At a batch boundary coverage means `Separated κ`. The boundary step preserves
`Good` deterministically (`boundary_good`). A region step preserves it whenever the
call is sound and complete; see the next module.

Under `Separated (2κ)`, the residual mass of any region is at most `n²κ`
(`internalMass_le`), so a per-call cap `R ≥ ρn²` never binds (`drawCount_le_cap`).
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
open Probability
variable {V : Type} [Fintype V]

/-- The invariant of a run state whose calls have all succeeded. -/
structure Good (G H : WeightedGraph V) (s : EstState V) : Prop where
  labeling : IsLabeling s.π
  cache : ∀ b, s.cache b = G.cut (fiber s.π b)
  pos : 0 < s.κ
  refines : G.Refines s.π (s.κ / 2)
  sep : G.Separated s.π (2 * s.κ)
  closed : ∀ S ∈ s.pending, ∀ u ∈ S, ∀ v, s.π v = s.π u → v ∈ S
  disjoint : s.pending.Pairwise Disjoint
  covered : ∀ u, (∀ v, G.StrongRelated s.κ u v → s.π u = s.π v) ∨
    ∃ S ∈ s.pending, G.strongComponent s.κ u ⊆ S
  notFailed : s.status ≠ .failed
  done : s.status = .done → ¬(remaining H s.π).Nonempty

/-! ### The residual mass under separation -/

theorem cut_fiber_le (G : WeightedGraph V) {π : V → V} {κ : ℝ} (hsep : G.Separated π (2 * κ))
    (hκ : 0 < κ) (b : V) :
    G.cut (fiber π b) ≤ (fiber π b).card * (Fintype.card V * (2 * κ)) := by
  unfold cut
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro u hu
  calc
    ∑ v ∈ (fiber π b)ᶜ, G.w u v ≤ ∑ v ∈ (fiber π b)ᶜ, 2 * κ := by
      apply Finset.sum_le_sum
      intro v hv
      have hne : π u ≠ π v := by
        simp only [Finset.mem_compl, mem_fiber] at hv
        rw [(mem_fiber _ _ _).mp hu]
        exact Ne.symm hv
      exact (G.weight_le_strength u v).trans (hsep u v hne).le
    _ ≤ Fintype.card V * (2 * κ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) (by positivity)

/-- **The residual mass of a region is at most `n²κ`** under `Separated (2κ)`. -/
theorem internalMass_le (G : WeightedGraph V) {π : V → V} {κ : ℝ}
    (hsep : G.Separated π (2 * κ)) (hκ : 0 < κ) (T : Finset V) :
    (G.contract π).internalMass T ≤ (Fintype.card V : ℝ) ^ 2 * κ := by
  rw [residual_mass_formula]
  have hfib : ∑ b ∈ T, ((fiber π b).card : ℝ) ≤ Fintype.card V := by
    have hdisj : Set.PairwiseDisjoint (T : Set V) (fiber π) := by
      intro b _ c _ hbc
      exact Finset.disjoint_left.mpr (fun v hb hc => hbc
        (((mem_fiber _ _ _).mp hb).symm.trans ((mem_fiber _ _ _).mp hc)))
    have := Finset.card_biUnion hdisj
    exact_mod_cast this ▸ Finset.card_le_univ _
  have hsum : ∑ b ∈ T, G.cut (fiber π b) ≤
      ∑ b ∈ T, ((fiber π b).card : ℝ) * (Fintype.card V * (2 * κ)) :=
    Finset.sum_le_sum (fun b _ => cut_fiber_le G hsep hκ b)
  rw [← Finset.sum_mul] at hsum
  have hcut := G.cut_nonneg (pull π T)
  have hle : (∑ b ∈ T, ((fiber π b).card : ℝ)) * (Fintype.card V * (2 * κ)) ≤
      (Fintype.card V : ℝ) * (Fintype.card V * (2 * κ)) :=
    mul_le_mul_of_nonneg_right hfib (by positivity)
  nlinarith

/-- With cap `R ≥ ρn²`, the per-call cap never binds. -/
theorem drawCount_le_cap (G : WeightedGraph V) {π : V → V} {κ ρ : ℝ}
    (hsep : G.Separated π (2 * κ)) (hκ : 0 < κ) (hρ : 0 ≤ ρ) {R : ℕ}
    (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) (T : Finset V) :
    ⌈ρ * (G.contract π).internalMass T / κ⌉₊ ≤ R := by
  apply Nat.ceil_le.mpr
  rw [div_le_iff₀ hκ]
  calc
    ρ * (G.contract π).internalMass T ≤ ρ * ((Fintype.card V : ℝ) ^ 2 * κ) :=
      mul_le_mul_of_nonneg_left (internalMass_le G hsep hκ T) hρ
    _ = ρ * (Fintype.card V : ℝ) ^ 2 * κ := by ring
    _ ≤ R * κ := mul_le_mul_of_nonneg_right hR hκ.le

/-! ### Initial state and batch boundary -/

/-- The initial scale, `n²D₀` when a pair remains and `1` otherwise. -/
def initScale (H : WeightedGraph V) : ℝ :=
  if (remaining H (id : V → V)).Nonempty then
    (Fintype.card V : ℝ) ^ 2 * topLevel H (id : V → V) else 1

def initState (H : WeightedGraph V) (cache : V → ℝ) : EstState V :=
  { π := id, cache := cache, κ := initScale H, pending := [], events := [], calls := [],
    status := .running }

theorem initScale_pos (H : WeightedGraph V) : 0 < initScale H := by
  unfold initScale
  split_ifs with h
  · have : 0 < Fintype.card V := by
      obtain ⟨p, _⟩ := h
      exact Fintype.card_pos_iff.mpr ⟨p.1⟩
    have := topLevel_pos H (id : V → V) h
    positivity
  · exact one_pos

theorem initState_good {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {cache : V → ℝ} (hc : ∀ b, cache b = G.cut (fiber (id : V → V) b)) :
    Good G H (initState H cache) := by
  have hpos := initScale_pos H
  -- Every pair in different singleton blocks has strength below the initial scale.
  have hsep : G.Separated (id : V → V) (initScale H) := by
    intro u v hne
    have hle := strength_le_topLevel hH (id : V → V) hne
    unfold initScale
    split_ifs with h
    · have hD := topLevel_pos H (id : V → V) h
      have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
      have hn : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by positivity
      nlinarith
    · have hz : topLevel H (id : V → V) = 0 := by simp [topLevel, h]
      rw [hz, mul_zero] at hle
      linarith
  refine ⟨fun v => rfl, hc, hpos, refines_of_injective G Function.injective_id _,
    hsep.mono (show initScale H ≤ 2 * initScale H by linarith), by simp [initState], by simp [initState], ?_, by simp [initState],
    by simp [initState]⟩
  intro u
  left
  intro v hr
  exact hsep.eq_of_related hr

theorem mem_forestRegion {H : WeightedGraph V} {t : ℝ} {v w : V} :
    w ∈ forestRegion H t v ↔ (H.threshold t).Reachable v w := by
  simp [forestRegion]

theorem forestRegion_eq {H : WeightedGraph V} {t : ℝ} {v w : V}
    (h : (H.threshold t).Reachable v w) : forestRegion H t v = forestRegion H t w := by
  ext x
  simp only [mem_forestRegion]
  exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩

theorem activeRegions_pairwise (H : WeightedGraph V) (π : V → V) (t : ℝ) :
    (activeRegions H π t).toList.Pairwise Disjoint := by
  apply (Finset.nodup_toList _).pairwise_of_forall_ne
  intro S hS S' hS' hne
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (Finset.mem_toList.mp hS)).1
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (Finset.mem_toList.mp hS')).1
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  apply hne
  rw [forestRegion_eq ((mem_forestRegion.mp hx).trans (mem_forestRegion.mp hx').symm)]

/-- **The batch boundary preserves `Good`.** -/
theorem boundary_good {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {s : EstState V}
    (hs : Good G H s) (hrun : s.status = .running) (hpend : s.pending = []) :
    Good G H (boundary H s) := by
  have hsepκ : G.Separated s.π s.κ := by
    apply separated_of_related G
    intro u v hr
    rcases hs.covered u with h | ⟨S, hS, _⟩
    · exact h v hr
    · rw [hpend] at hS
      exact absurd hS (List.not_mem_nil)
  unfold boundary
  split_ifs with hrem
  · set D := topLevel H s.π
    set κ' := min (s.κ / 2) ((Fintype.card V : ℝ) ^ 2 / 2 * D)
    obtain ⟨hr', hs'⟩ := next_scale_invariant hH hs.refines hsepκ hrem
    have hD := topLevel_pos H s.π hrem
    have hpos' : 0 < κ' := by
      have : 0 < Fintype.card V := by
        obtain ⟨p, _⟩ := hrem
        exact Fintype.card_pos_iff.mpr ⟨p.1⟩
      have := hs.pos
      exact lt_min (by positivity) (by positivity)
    have hlt : D < 2 * κ' := topLevel_lt hH hs' hrem
    have hreach {u v : V} (h : G.StrongRelated κ' u v) :
        (H.threshold (D / (Fintype.card V : ℝ) ^ 2)).Reachable u v :=
      reachable_of_related_top hH hD hlt h
    refine ⟨hs.labeling, hs.cache, hpos', hr'.mono (by linarith), hs', ?_, ?_, ?_,
      hs.notFailed, fun h => by simp only [hrun, reduceCtorEq] at h⟩
    · intro S hS u hu v hv
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp
        (Finset.mem_filter.mp (Finset.mem_toList.mp hS)).1
      exact mem_forestRegion.mpr ((mem_forestRegion.mp hu).trans (hreach (hr' u v hv.symm)))
    · exact activeRegions_pairwise H s.π _
    · intro u
      by_cases hact : forestRegion H (D / (Fintype.card V : ℝ) ^ 2) u ∈
          activeRegions H s.π (D / (Fintype.card V : ℝ) ^ 2)
      · right
        refine ⟨_, Finset.mem_toList.mpr hact, fun v hv => ?_⟩
        exact mem_forestRegion.mpr (hreach ((G.mem_strongComponent _ u v).mp hv))
      · left
        intro v hv
        by_contra hne
        apply hact
        refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ u),
          u, mem_forestRegion.mpr (SimpleGraph.Reachable.refl u), v,
          mem_forestRegion.mpr (hreach hv), hne⟩
  · exact ⟨hs.labeling, hs.cache, hs.pos, hs.refines, hs.sep, by simp [hpend], by simp [hpend],
      fun u => by
        rcases hs.covered u with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [hpend] at h),
      by simp, fun _ => hrem⟩


/-! ### The region step -/

namespace RegionStep

/-- The answers of the cache queries, as a function of the sampled graph. -/
def answers (G : WeightedGraph V) (s : EstState V) (S : Finset V) (X : WeightedGraph V)
    (K : Finset V) : ℝ :=
  if pull s.π K ∈ (nontrivialGroups (S.image s.π) X (3 * s.κ / 4)).toList.map (pull s.π) then
    G.cut (pull s.π K) else 0

/-- The state after the call, as a deterministic function of its output. -/
def next (G : WeightedGraph V) (s : EstState V) (S : Finset V) (rest : List (Finset V)) :
    Option (WeightedGraph V) → EstState V
  | none => { s with status := .failed, calls := s.calls ++ [⟨s.π, s.cache, S.image s.π, s.κ, 0⟩] }
  | some X => afterCall s S rest X (answers G s S X)

end RegionStep

theorem regionStep_eval (G : WeightedGraph V) (ρ : ℝ) (R : ℕ) (s : EstState V) (S : Finset V)
    (rest : List (Finset V)) (hκ : 0 < s.κ) :
    (regionStep ρ R s S rest hκ).eval G.cut =
      ((estimateCall (searchDepth V) (searchDepth V) s.π s.cache (S.image s.π) hκ ρ R).eval
        G.cut).map (RegionStep.next G s S rest) := by
  rw [regionStep, RTree.eval_bind, ← PMF.bind_pure_comp]
  congr 1
  funext o
  cases o with
  | none => simp [RegionStep.next]
  | some X =>
      simp only [RTree.eval_weaken, RTree.eval_map, queryCuts_eval, PMF.pure_map,
        Function.comp_apply, RegionStep.next]
      rfl

/-- The family of true components inside the region, for completeness. -/
def regionComponents (G : WeightedGraph V) (κ : ℝ) (S : Finset V) : Finset (Finset V) :=
  (S.image (G.strongComponent κ)).filter (· ⊆ S)

theorem card_regionComponents_le (G : WeightedGraph V) (κ : ℝ) (S : Finset V) :
    (regionComponents G κ S).card ≤ Fintype.card V :=
  (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (Finset.card_le_univ S))

/-- **A sound and complete call keeps the run good.** -/
theorem afterCall_good {G H : WeightedGraph V} {s : EstState V} (hs : Good G H s)
    {S : Finset V} {rest : List (Finset V)} (hpend : s.pending = S :: rest) {X : WeightedGraph V}
    (hX : X.induce (S.image s.π) = X)
    (hsound : ∀ u v, s.π u ∈ S.image s.π → X.StrongRelated (3 * s.κ / 4) (s.π u) (s.π v) →
      G.StrongRelated (s.κ / 2) u v)
    (hcomplete : ∀ U ∈ regionComponents G s.κ S, ∀ u ∈ U, ∀ v ∈ U,
      X.StrongRelated (3 * s.κ / 4) (s.π u) (s.π v)) :
    Good G H (afterCall s S rest X (RegionStep.answers G s S X)) := by
  set T := S.image s.π
  have hθ : 0 < 3 * s.κ / 4 := by have := hs.pos; positivity
  have hT : ∀ b ∈ T, s.π b = b := image_labels hs.labeling S
  have heq := merge_eq_iff (π := s.π) hX hθ
  have hSclosed := hs.closed S (by rw [hpend]; exact List.mem_cons_self)
  have hdisj := hs.disjoint
  rw [hpend] at hdisj
  -- Vertices of later regions keep their blocks.
  have hout {u : V} {S' : Finset V} (hS' : S' ∈ rest) (hu : u ∈ S') : s.π u ∉ T := by
    intro h
    obtain ⟨w, hw, hwu⟩ := Finset.mem_image.mp h
    have huS := hSclosed w hw u hwu.symm
    exact Finset.disjoint_left.mp ((List.pairwise_cons.mp hdisj).1 S' hS') huS hu
  refine ⟨mergeMap_isLabeling hs.labeling hT hX hθ, ?_, hs.pos, ?_, ?_, ?_, ?_, ?_,
    by simp [afterCall], by simp [afterCall]⟩
  · intro b
    apply mergeCache_correct G hX hθ hs.cache
    intro K hK
    have hm : pull s.π K ∈ (nontrivialGroups T X (3 * s.κ / 4)).toList.map (pull s.π) :=
      List.mem_map.mpr ⟨K, Finset.mem_toList.mpr hK, rfl⟩
    unfold RegionStep.answers
    split_ifs with h
    · rfl
    · exact (h hm).elim
  · intro u v he
    rcases (heq u v).mp he with h | ⟨huT, hr⟩
    · exact (hs.refines u v h)
    · exact hsound u v huT hr
  · intro u v hne
    exact hs.sep u v (fun h => hne (mergeMap_coarsens hX hθ h))
  · intro S' hS' u hu v hv
    have huT := hout hS' hu
    rcases (heq v u).mp hv with h | ⟨hvT, hr⟩
    · exact hs.closed S' (by rw [hpend]; exact List.mem_cons_of_mem _ hS') u hu v h
    · have := component_subset hX hθ hvT ((X.mem_strongComponent _ _ _).mpr hr)
      exact (huT this).elim
  · exact (List.pairwise_cons.mp hdisj).2
  · intro u
    rcases hs.covered u with h | ⟨S'', hS'', hsub⟩
    · exact Or.inl fun v hr => mergeMap_coarsens hX hθ (h v hr)
    · rw [hpend] at hS''
      rcases List.mem_cons.mp hS'' with rfl | hS''
      · left
        intro v hr
        have huS : u ∈ S'' := hsub (G.mem_strongComponent_self _ u)
        have hmem : G.strongComponent s.κ u ∈ regionComponents G s.κ S'' :=
          Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ huS, hsub⟩
        exact (heq u v).mpr (Or.inr ⟨Finset.mem_image_of_mem _ huS,
          hcomplete _ hmem u (G.mem_strongComponent_self _ u) v
            ((G.mem_strongComponent _ u v).mpr hr)⟩)
      · exact Or.inr ⟨S'', hS'', hsub⟩


/-- Failure budget of one call: soundness plus completeness. -/
def callFailure (V : Type) [Fintype V] (ρ δ₀ : ℝ) : ENNReal :=
  (Fintype.card V : ENNReal) * ENNReal.ofReal (Real.exp (-(ρ / 32))) +
    (Fintype.card V : ENNReal) * ENNReal.ofReal ((Fintype.card V - 1 : ℕ) * δ₀)

/-- **One region step breaks the invariant with probability at most `callFailure`.** -/
theorem regionStep_failure {G H : WeightedGraph V} {s : EstState V} (hs : Good G H s)
    {S : Finset V} {rest : List (Finset V)} (hpend : s.pending = S :: rest) (hκ : 0 < s.κ)
    {ρ : ℝ} (hρ : 0 < ρ) {R : ℕ} (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) {δ₀ : ℝ}
    (hδ : 0 ≤ δ₀) (hδ2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4) :
    Probability.mass ((regionStep ρ R s S rest hκ).eval G.cut) (fun s' => ¬Good G H s') ≤
      callFailure V ρ δ₀ := by
  set T := S.image s.π
  have hB : Fintype.card V ≤ 2 ^ searchDepth V := Nat.le_pow_clog (by decide) _
  have hblocks : ∀ u v, s.π u ∈ T → s.π u = s.π v → G.StrongRelated (s.κ / 2) u v :=
    fun u v _ h => hs.refines u v h
  have h𝒰 : ∀ U ∈ regionComponents G s.κ S, G.IsStrong s.κ U ∧ U.image s.π ⊆ T := by
    intro U hU
    obtain ⟨hU, hsub⟩ := Finset.mem_filter.mp hU
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hU
    exact ⟨G.strongComponent_strong _ w, Finset.image_subset_image hsub⟩
  have hsound := estimateCall_sound G (searchDepth V) (searchDepth V) s.π s.cache hs.cache T
    hB hB hκ hρ R hblocks
  have hcomplete := estimateCall_complete G (searchDepth V) (searchDepth V) s.π s.cache
    hs.cache T hB hB hκ hρ hδ hδ2 hexp R (drawCount_le_cap G hs.sep hκ hρ.le hR T)
    (regionComponents G s.κ S) h𝒰
  rw [regionStep_eval, mass_map]
  calc
    _ ≤ Probability.mass ((estimateCall (searchDepth V) (searchDepth V) s.π s.cache T hκ ρ R).eval
          G.cut)
        (fun o => (∃ X, o = some X ∧ ¬∀ u v, s.π u ∈ T →
            X.StrongRelated (3 * s.κ / 4) (s.π u) (s.π v) → G.StrongRelated (s.κ / 2) u v) ∨
          ¬∃ X, o = some X ∧ ∀ U ∈ regionComponents G s.κ S, ∀ u ∈ U, ∀ v ∈ U,
            X.StrongRelated (3 * s.κ / 4) (s.π u) (s.π v)) := by
      apply mass_mono_on_support
      intro o ho hbad
      by_contra hgood
      push Not at hgood
      obtain ⟨hs1, ⟨X, rfl, hc⟩⟩ := hgood
      have hX := estimateCall_support G (searchDepth V) (searchDepth V) s.π s.cache hs.cache T
        hB hB hκ hρ R ho
      exact hbad (afterCall_good hs hpend hX (fun u v hu hr => hs1 X rfl u v hu hr) hc)
    _ ≤ _ := (mass_or_le _ _ _).trans (add_le_add ?_ ?_)
  · refine hsound.trans ?_
    gcongr
    exact_mod_cast (Nat.sub_le _ _).trans (Finset.card_image_le.trans (Finset.card_le_univ S))
  · refine hcomplete.trans ?_
    gcongr
    exact_mod_cast card_regionComponents_le G s.κ S

end
end CutQueryComplexity.WeightedGraph
