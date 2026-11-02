import CutQueryComplexity.Sparsification.OutputBudget

/-! # The number of output edges

Each counted draw is a single edge, and adding graphs at most adds their edge
counts. So every supported outcome of a counted sample has at most as many
edges as draws (`sampleLaw_edgeCount_le`). After a successful estimation run the
output takes at most `4c(n−1) + n` draws, so it is a *sparse* `1 ± ε` cut
sparsifier with at most `⌊4c(n−1) + n⌋` edges (`outRun_sparse`).
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V]

theorem edgeCount_add_le (X Y : WeightedGraph V) : (X + Y).edgeCount ≤ X.edgeCount + Y.edgeCount := by
  unfold edgeCount
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rw [Finset.mem_union, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      change (X + Y).w u v ≠ 0 at he
      change X.w u v ≠ 0 ∨ Y.w u v ≠ 0
      by_contra h
      push Not at h
      exact he (by rw [add_weight, h.1, h.2, _root_.add_zero])

theorem edgeCount_zero : (0 : WeightedGraph V).edgeCount = 0 := by
  unfold edgeCount
  rw [Finset.card_eq_zero, SimpleGraph.edgeFinset_eq_empty]
  ext u v
  change (0 : WeightedGraph V).w u v ≠ 0 ↔ False
  simp

theorem edgeCount_edgeGraph_le (e : EdgeIndex V) (a : ℝ) (ha : 0 ≤ a) :
    (edgeGraph e a ha).edgeCount ≤ 1 := by
  unfold edgeCount
  refine (Finset.card_le_card (s := _) (t := {s(e.val.1, e.val.2)}) ?_).trans (by simp)
  intro x hx
  induction x using Sym2.ind with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hx
      change (edgeGraph e a ha).w u v ≠ 0 at hx
      rw [Finset.mem_singleton]
      simp only [edgeGraph] at hx
      by_cases h1 : (u, v) = e.val
      · rw [← h1]
      · by_cases h2 : (v, u) = e.val
        · rw [← h2, Sym2.eq_swap]
        · simp [h1, h2] at hx

theorem independentGraphSum_edgeCount (L : List (PMF (WeightedGraph V)))
    (hL : ∀ p ∈ L, ∀ X ∈ p.support, X.edgeCount ≤ 1) :
    ∀ X ∈ (independentGraphSum L).support, X.edgeCount ≤ L.length := by
  induction L with
  | nil =>
      intro X hX
      simp only [independentGraphSum, PMF.mem_support_pure_iff] at hX
      subst hX
      simp [edgeCount_zero]
  | cons p L ih =>
      intro X hX
      simp only [independentGraphSum, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hX
      obtain ⟨Y, hY, Z, hZ, rfl⟩ := hX
      have h1 := hL p List.mem_cons_self Y hY
      have h2 := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) Z hZ
      simp only [List.length_cons]
      have := edgeCount_add_le Y Z
      omega

/-- **A counted sample has at most as many edges as draws.** -/
theorem sampleLaw_edgeCount_le (bs : List (CountedBucket V)) {X : WeightedGraph V}
    (hX : X ∈ (CountedBucket.sampleLaw bs).support) :
    X.edgeCount ≤ (bs.map CountedBucket.count).sum := by
  rw [← CountedBucket.expanded_length]
  have := independentGraphSum_edgeCount ((CountedBucket.expanded bs).map CountedBucket.drawLaw)
    (by
      intro p hp Y hY
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
      obtain ⟨e, _, rfl⟩ := (b.mem_support_drawLaw Y).mp hY
      exact edgeCount_edgeGraph_le _ _ _) X hX
  rwa [List.length_map] at this

/-- Bucket draw counts are the recomputed event counts when no cap binds. -/
theorem eventBuckets_count_sum (G : WeightedGraph V) {c : ℝ} (hc : 0 < c) (R₂ : ℕ)
    (L : List (MergeEvent V))
    (hL : ∀ e ∈ L, (∀ b, e.cache b = G.cut (fiber e.π b)) ∧ 0 < e.β ∧
      (0 < (G.contract e.π).internalMass e.group →
        outCount c e ((G.contract e.π).internalMass e.group) ≤ R₂)) :
    ((eventBuckets G c hc L).map CountedBucket.count).sum = (L.map (eventCount G c R₂)).sum := by
  induction L with
  | nil => simp [eventBuckets]
  | cons e L ih =>
      obtain ⟨hcache, hβ, hcap⟩ := hL e List.mem_cons_self
      have ih' := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))
      have hm := cachedMass_eq G e.π e.cache hcache e.group
      unfold eventBuckets at ih' ⊢
      simp only [List.map_cons, List.sum_cons]
      by_cases hM : 0 < (G.contract e.π).internalMass e.group
      · have hb : eventBucket G c hc e = some (outBucket G e.π e.group
            (outCount c e ((G.contract e.π).internalMass e.group)) (outCount_pos hc hβ hM) hM) := by
          simp only [eventBucket, hM, hβ, and_self, ↓reduceDIte]
        have hcount : eventCount G c R₂ e = outCount c e ((G.contract e.π).internalMass e.group) := by
          simp only [eventCount, hm, hM, hcap hM, ↓reduceIte]
        simp only [List.filterMap_cons, hb, List.map_cons, List.sum_cons,
          CountedBucket.outBucket_count, ih', hcount]
      · have hb : eventBucket G c hc e = none := by
          have : ¬(0 < (G.contract e.π).internalMass e.group ∧ 0 < e.β) := fun h => hM h.1
          simp only [eventBucket, this, ↓reduceDIte]
        have hcount : eventCount G c R₂ e = 0 := by
          simp only [eventCount, hm, hM, ↓reduceIte]
        simp only [List.filterMap_cons, hb, ih', hcount, Nat.zero_add]

/-- **Sparse output.** After a successful estimation run, the output is a `1 ± ε` cut
sparsifier with at most `⌊4c(n−1) + n⌋` edges, except with probability `(n−1)δ`. -/
theorem outRun_sparse {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {s : EstState V} (h : EstSuccess G H s) {c ε δ : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hlog : 8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    Probability.mass ((outRun c ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ s.events).eval G.cut)
      (fun o => ¬∃ X, o = some X ∧
        IsSparseCutSparsifier ε ⌊4 * c * (Fintype.card V - 1 : ℕ) + Fintype.card V⌋₊ G X) ≤
      ENNReal.ofReal ((Fintype.card V - 1 : ℕ) * δ) := by
  have hL : ∀ e ∈ s.events, (∀ b, e.cache b = G.cut (fiber e.π b)) ∧ 0 < e.β ∧
      (0 < (G.contract e.π).internalMass e.group →
        outCount c e ((G.contract e.π).internalMass e.group) ≤
          ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊) := fun e he =>
    ⟨(h.2.1.exact e he).2.1, (h.2.1.exact e he).2.2.2, fun _ => outCount_le_cap h hc he⟩
  have hsp := outRun_sparsifier hH h hc hε hε1 hδ hδ2 hlog
  refine le_trans (mass_mono_on_support _ (fun o ho hbad => ?_))
    (failure_le_of_success _ _ (by positivity) hsp)
  intro ⟨X, hX, hXs⟩
  apply hbad
  refine ⟨X, hX, hXs, ?_⟩
  rw [outRun_eval G c hc _ s.events hL] at ho
  obtain ⟨Y, hY, hYX⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  rw [hX] at hYX
  cases hYX
  have hcount := sampleLaw_edgeCount_le _ hY
  rw [eventBuckets_count_sum G hc _ s.events hL] at hcount
  have htot := outDraws_total_le h hc ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊
  apply Nat.le_floor
  exact (Nat.cast_le.mpr hcount).trans htot

end
end CutQueryComplexity.WeightedGraph
