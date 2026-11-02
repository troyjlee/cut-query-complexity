import CutQueryComplexity.Sparsification.EstimationTermination

/-! # Merge events and the end-to-end estimation theorem

Each nontrivial merge group `K` is recorded with the labeling and cache before the
merge and the label `β = κ/2`. Its *bucket* consists of the pairs `(u, v)` whose
old blocks differ but both lie in `K`; these are the edges first internalized by
that merge.

`EventsGood` states what output sampling needs:

* every event records a labeling, an exact cache, a group of labels, and `β > 0`;
* every pair in a bucket satisfies `k/4 < β ≤ k`;
* each pair of distinct vertices lies in exactly one bucket if it shares a current
  block, and in none otherwise;
* the number of events plus the number of blocks is at most `n`.

These follow deterministically along the run from `Good`, so they cost no
additional failure probability. `estRun_correct` is the end-to-end statement: with
probability at least `1 − N·callFailure`, the run finishes in a good state with
good events, and every positive-strength pair shares a final block.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
open Probability
variable {V : Type} [Fintype V]

/-- The pair `(u, v)` is first internalized by this merge event. -/
def InBucket (u v : V) (e : MergeEvent V) : Prop :=
  e.π u ≠ e.π v ∧ e.π u ∈ e.group ∧ e.π v ∈ e.group

structure EventsGood (G : WeightedGraph V) (s : EstState V) : Prop where
  exact : ∀ e ∈ s.events, IsLabeling e.π ∧ (∀ b, e.cache b = G.cut (fiber e.π b)) ∧
    (∀ b ∈ e.group, e.π b = b) ∧ 0 < e.β
  label : ∀ e ∈ s.events, ∀ u v, InBucket u v e →
    G.strength u v / 4 < e.β ∧ e.β ≤ G.strength u v
  count : ∀ u v, u ≠ v →
    s.events.countP (fun e => decide (InBucket u v e)) = if s.π u = s.π v then 1 else 0
  length : s.events.length + (liveLabels s.π).card ≤ Fintype.card V

theorem countP_toList {α : Type} (F : Finset α) (p : α → Prop) :
    F.toList.countP (fun a => decide (p a)) = (F.filter p).card := by
  rw [← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter]
  rfl

theorem liveLabels_id : liveLabels (id : V → V) = Finset.univ := by
  ext b
  simp [liveLabels]

theorem initState_events (G H : WeightedGraph V) (cache : V → ℝ) :
    EventsGood G (initState H cache) := by
  refine ⟨by simp [initState], by simp [initState], ?_, ?_⟩
  · intro u v huv
    simp [initState, huv]
  · simp [initState, liveLabels_id]

theorem boundary_events {G H : WeightedGraph V} {s : EstState V} (hs : EventsGood G s) :
    EventsGood G (boundary H s) := by
  unfold boundary
  split_ifs <;> exact ⟨hs.exact, hs.label, hs.count, hs.length⟩

/-- **A good call records good events.** -/
theorem afterCall_events {G H : WeightedGraph V} {s : EstState V} (hs : Good G H s)
    (he : EventsGood G s) {S : Finset V} {rest : List (Finset V)} {X : WeightedGraph V}
    (hX : X.induce (S.image s.π) = X) {ans : Finset V → ℝ}
    (hs' : Good G H (afterCall s S rest X ans)) :
    EventsGood G (afterCall s S rest X ans) := by
  simp only [afterCall] at hs' ⊢
  set T := S.image s.π
  set θ := 3 * s.κ / 4
  have hθ : 0 < θ := by have := hs.pos; positivity
  have hT : ∀ b ∈ T, s.π b = b := image_labels hs.labeling S
  have heq := merge_eq_iff (π := s.π) hX hθ
  -- Membership in a new event.
  have hnew {e : MergeEvent V} (hmem : e ∈ (nontrivialGroups T X θ).toList.map
      (fun K => (⟨s.π, s.cache, K, s.κ / 2⟩ : MergeEvent V))) :
      ∃ K ∈ nontrivialGroups T X θ, e = ⟨s.π, s.cache, K, s.κ / 2⟩ := by
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hmem
    exact ⟨K, Finset.mem_toList.mp hK, rfl⟩
  have hgroup {K : Finset V} (hK : K ∈ nontrivialGroups T X θ) :
      ∃ b ∈ T, K = X.strongComponent θ b := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hK).1
    exact ⟨b, hb, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e hmem
    rcases List.mem_append.mp hmem with h | h
    · exact he.exact e h
    · obtain ⟨K, hK, rfl⟩ := hnew h
      obtain ⟨b, hb, rfl⟩ := hgroup hK
      exact ⟨hs.labeling, hs.cache,
        fun c hc => hT c (component_subset hX hθ hb hc), by have := hs.pos; positivity⟩
  · intro e hmem u v hin
    rcases List.mem_append.mp hmem with h | h
    · exact he.label e h u v hin
    · obtain ⟨K, hK, rfl⟩ := hnew h
      obtain ⟨b, hb, rfl⟩ := hgroup hK
      obtain ⟨hne, hu, hv⟩ := hin
      have huv : u ≠ v := fun h => hne (h ▸ rfl)
      have hrel : X.StrongRelated θ (s.π u) (s.π v) :=
        ((X.mem_strongComponent θ b _).mp hu).symm.trans ((X.mem_strongComponent θ b _).mp hv)
      have hmerge : mergeMap s.π T X θ u = mergeMap s.π T X θ v :=
        (heq u v).mpr (Or.inr ⟨component_subset hX hθ hb hu, hrel⟩)
      refine ⟨by linarith [hs.sep u v hne], ?_⟩
      exact (G.le_strength_iff huv _).mpr (hs'.refines u v hmerge)
  · intro u v huv
    simp only [List.countP_append, List.countP_map]
    rw [he.count u v huv]
    have hc := countP_toList (nontrivialGroups T X θ)
      (fun K => InBucket u v ⟨s.π, s.cache, K, s.κ / 2⟩)
    simp only [Function.comp_def] at hc ⊢
    rw [hc]
    by_cases hπ : s.π u = s.π v
    · have h0 : (nontrivialGroups T X θ).filter
          (fun K => InBucket u v ⟨s.π, s.cache, K, s.κ / 2⟩) = ∅ := by
        apply Finset.filter_false_of_mem
        intro K _ hin
        exact hin.1 hπ
      have hm : mergeMap s.π T X θ u = mergeMap s.π T X θ v := mergeMap_coarsens hX hθ hπ
      simp only [h0, hπ, hm, ↓reduceIte, Finset.card_empty]
    · -- At most one group contains both old labels, and one does iff they merge.
      have hle : ((nontrivialGroups T X θ).filter
          (fun K => InBucket u v ⟨s.π, s.cache, K, s.κ / 2⟩)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro K hK K' hK'
        obtain ⟨hK, ⟨_, hu, _⟩⟩ := Finset.mem_filter.mp hK
        obtain ⟨hK', ⟨_, hu', _⟩⟩ := Finset.mem_filter.mp hK'
        obtain ⟨b, _, rfl⟩ := hgroup hK
        obtain ⟨b', _, rfl⟩ := hgroup hK'
        rw [strongComponent_eq_of_related ((X.mem_strongComponent θ b _).mp hu),
          strongComponent_eq_of_related ((X.mem_strongComponent θ b' _).mp hu')]
      by_cases hm : mergeMap s.π T X θ u = mergeMap s.π T X θ v
      · simp only [hπ, hm, ↓reduceIte, Nat.zero_add]
        rcases (heq u v).mp hm with h | ⟨huT, hrel⟩
        · exact (hπ h).elim
        · apply le_antisymm hle
          apply Finset.card_pos.mpr
          refine ⟨X.strongComponent θ (s.π u), Finset.mem_filter.mpr ⟨?_, hπ,
            X.mem_strongComponent_self θ _, (X.mem_strongComponent θ _ _).mpr hrel⟩⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ huT, ?_⟩
          have hsub : ({s.π u, s.π v} : Finset V) ⊆ X.strongComponent θ (s.π u) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact X.mem_strongComponent_self θ _
            · exact (X.mem_strongComponent θ _ _).mpr hrel
          simpa [Finset.card_pair hπ] using Finset.card_le_card hsub
      · simp only [hπ, hm, ↓reduceIte, Nat.zero_add]
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_false_of_mem
        intro K hK hin
        obtain ⟨b, hb, rfl⟩ := hgroup hK
        obtain ⟨_, hu, hv⟩ := hin
        apply hm
        exact (heq u v).mpr (Or.inr ⟨component_subset hX hθ hb hu,
          ((X.mem_strongComponent θ b _).mp hu).symm.trans
            ((X.mem_strongComponent θ b _).mp hv)⟩)
  · have hcount := card_liveLabels_merge hT hX hθ
    simp only [List.length_append, List.length_map, Finset.length_toList]
    have := he.length
    omega

/-- Event invariants hold along every supported step from a good state. -/
theorem estStep_events {G H : WeightedGraph V} {ρ : ℝ} (hρ : 0 < ρ) {R : ℕ} {s s' : EstState V}
    (hs : Good G H s) (he : EventsGood G s) (hs' : Good G H s')
    (hmem : s' ∈ ((estStep H ρ R s).eval G.cut).support) : EventsGood G s' := by
  unfold estStep at hmem
  rcases hst : s.status with _ | _ | _ <;> rw [hst] at hmem
  · rcases hp : s.pending with _ | ⟨S, rest⟩ <;> rw [hp] at hmem
    · simp only [RTree.eval_pure, PMF.mem_support_pure_iff] at hmem
      subst hmem
      exact boundary_events he
    · simp only [hs.pos, ↓reduceDIte] at hmem
      rw [regionStep_eval] at hmem
      obtain ⟨o, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
      cases o with
      | none => exact absurd rfl hs'.notFailed
      | some X =>
          have hB : Fintype.card V ≤ 2 ^ searchDepth V := Nat.le_pow_clog (by decide) _
          exact afterCall_events hs he
            (estimateCall_support G (searchDepth V) (searchDepth V) s.π s.cache hs.cache _
              hB hB hs.pos hρ R ho) hs'
  · simp only [RTree.eval_pure, PMF.mem_support_pure_iff] at hmem
    subst hmem
    exact he
  · exact absurd hst hs.notFailed

/-- The combined fuel-indexed invariant. -/
def RunInv2 (G H : WeightedGraph V) (N : ℕ) (s : EstState V) : Prop :=
  RunInv G H N s ∧ EventsGood G s

theorem estStep_failure2 {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {ρ : ℝ}
    (hρ : 0 < ρ) {R : ℕ} (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (hδ2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    (N : ℕ) (s : EstState V) (hs : RunInv2 G H (N + 1) s) :
    Probability.mass ((estStep H ρ R s).eval G.cut) (fun s' => ¬RunInv2 G H N s') ≤
      callFailure V ρ δ₀ := by
  refine le_trans (mass_mono_on_support _ (fun s' hs' hbad => ?_))
    (estStep_failure hH hρ hR hδ hδ2 hexp N s hs.1)
  intro hinv
  exact hbad ⟨hinv, estStep_events hρ hs.1.1 hs.2 hinv.1 hs'⟩

/-! ### The end-to-end estimation theorem -/

/-- Good finished state of the estimation phase. -/
def EstSuccess (G H : WeightedGraph V) (s : EstState V) : Prop :=
  Good G H s ∧ EventsGood G s ∧ s.status = .done

/-- **End-to-end estimation guarantee.** -/
theorem estRun_correct {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {ρ : ℝ}
    (hρ : 0 < ρ) {R : ℕ} (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (hδ2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    {cache : V → ℝ} (hc : ∀ b, cache b = G.cut (fiber (id : V → V) b)) {N : ℕ}
    (hN : runPot H (initState H cache) ≤ N) :
    Probability.mass ((estRun H ρ R N (initState H cache)).eval G.cut)
      (fun s => ¬EstSuccess G H s) ≤ N * callFailure V ρ δ₀ := by
  have h := RTree.iterate_failure_le (estStep H ρ R) G.cut (RunInv2 G H) (callFailure V ρ δ₀)
    (estStep_failure2 hH hρ hR hδ hδ2 hexp) N (initState H cache)
    ⟨⟨initState_good hH hc, hN⟩, initState_events G H cache⟩
  unfold estRun
  refine le_trans (mass_mono _ ?_) h
  intro s hbad hinv
  apply hbad
  obtain ⟨⟨hg, hpot⟩, hev⟩ := hinv
  refine ⟨hg, hev, ?_⟩
  rcases hst : s.status with _ | _ | _
  · simp [runPot, hst] at hpot
  · rfl
  · exact absurd hst hg.notFailed

/-- In a successful finished state, every positive-strength pair shares a block. -/
theorem EstSuccess.same_block {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {s : EstState V} (h : EstSuccess G H s) {u v : V} (hk : 0 < G.strength u v) :
    s.π u = s.π v := by
  by_contra hne
  have hrem := h.1.done h.2.2
  have hb := (hH.bottleneck_bounds u v).2
  have hpos : 0 < H.bottleneck u v := by
    by_contra hz
    have : H.bottleneck u v = 0 := le_antisymm (not_lt.mp hz) (H.bottleneck_nonneg u v)
    rw [this, mul_zero] at hb
    linarith
  exact hrem ⟨(u, v), (mem_remaining H s.π (u, v)).mpr ⟨hne, hpos⟩⟩

end
end CutQueryComplexity.WeightedGraph
