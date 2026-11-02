import CutQueryComplexity.Sparsification.EstimateLift
import CutQueryComplexity.Model.Iterate

/-! # Applying an estimation merge to the partition and the cache

Block labels are vertices, and a *labeling* map `π` sends every label to itself
(`π (π v) = π v`). After a call on the region `T` returns the block graph `X`, each
old label `b ∈ T` joins the group `K = X.strongComponent θ b`; the new label of the
group is its canonical representative, an old label in `K`. Labels outside `T`
are unchanged.

`merge_eq_iff` characterizes the new partition: two vertices share a new block
exactly when they shared an old block or their old blocks are `θ`-related in `X`
inside the region. The new map is again a labeling.

Only *nontrivial* groups, with at least two old labels, need a new cut query.
`mergeCache` reuses the cached cuts of unchanged blocks and sets retired labels to
zero, and `mergeCache_correct` proves that the resulting cache is exact. The number
of nontrivial groups is at most the decrease in the number of blocks.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Labels are members of their own blocks. -/
def IsLabeling (π : V → V) : Prop := ∀ v, π (π v) = π v

/-- A canonical element of a nonempty set, with a default for the empty set. -/
def rep (K : Finset V) (d : V) : V :=
  if h : K.Nonempty then
    (Fintype.equivFin V).symm ((K.image (Fintype.equivFin V)).min' (h.image _))
  else d

omit [DecidableEq V] in
theorem rep_mem {K : Finset V} (h : K.Nonempty) (d : V) : rep K d ∈ K := by
  simp only [rep, h, ↓reduceDIte]
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ((K.image (Fintype.equivFin V)).min'_mem (h.image _))
  rw [← he, Equiv.symm_apply_apply]
  exact hx

omit [DecidableEq V] in
theorem rep_congr {K : Finset V} (h : K.Nonempty) (d d' : V) : rep K d = rep K d' := by
  simp [rep, h]

/-- The new block map after a call on region `T` with sampled block graph `X`. -/
def mergeMap (π : V → V) (T : Finset V) (X : WeightedGraph V) (θ : ℝ) (v : V) : V :=
  if π v ∈ T then rep (X.strongComponent θ (π v)) (π v) else π v

variable {π : V → V} {T : Finset V} {X : WeightedGraph V} {θ : ℝ}

theorem mergeMap_of_mem {v : V} (hv : π v ∈ T) :
    mergeMap π T X θ v = rep (X.strongComponent θ (π v)) (π v) := by
  simp [mergeMap, hv]

theorem mergeMap_of_not_mem {v : V} (hv : π v ∉ T) : mergeMap π T X θ v = π v := by
  simp [mergeMap, hv]

theorem rep_component_mem (b : V) :
    rep (X.strongComponent θ b) b ∈ X.strongComponent θ b :=
  rep_mem (X.strongComponent_nonempty θ b) b

/-- Components are equal exactly when their representatives are. -/
theorem rep_component_eq_iff (b c : V) :
    rep (X.strongComponent θ b) b = rep (X.strongComponent θ c) c ↔
      X.StrongRelated θ b c := by
  constructor
  · intro he
    have hb := (X.mem_strongComponent θ b _).mp (rep_component_mem (X := X) (θ := θ) b)
    have hc := (X.mem_strongComponent θ c _).mp (rep_component_mem (X := X) (θ := θ) c)
    rw [he] at hb
    exact hb.trans hc.symm
  · intro hr
    rw [strongComponent_eq_of_related hr]
    exact rep_congr (X.strongComponent_nonempty θ c) b c

/-- Groups meeting the region stay in the region. -/
theorem component_subset (hX : X.induce T = X) (hθ : 0 < θ) {b : V} (hb : b ∈ T) :
    X.strongComponent θ b ⊆ T :=
  (X.strongComponent_strong θ b).subset_of_support hX hθ (X.mem_strongComponent_self θ b) hb

/-- **Characterization of the merged partition.** -/
theorem merge_eq_iff (hX : X.induce T = X) (hθ : 0 < θ) (u v : V) :
    mergeMap π T X θ u = mergeMap π T X θ v ↔
      π u = π v ∨ (π u ∈ T ∧ X.StrongRelated θ (π u) (π v)) := by
  by_cases hu : π u ∈ T <;> by_cases hv : π v ∈ T
  · rw [mergeMap_of_mem hu, mergeMap_of_mem hv, rep_component_eq_iff]
    constructor
    · exact fun h => Or.inr ⟨hu, h⟩
    · rintro (h | ⟨_, h⟩)
      · rw [h]; exact X.strongRelated_refl θ _
      · exact h
  · rw [mergeMap_of_mem hu, mergeMap_of_not_mem hv]
    constructor
    · intro he
      have hm := component_subset hX hθ hu (rep_component_mem (X := X) (θ := θ) (π u))
      rw [he] at hm
      exact (hv hm).elim
    · rintro (h | ⟨_, h⟩)
      · exact (hv (h ▸ hu)).elim
      · have := StrongRelated.eq_of_not_mem hX hθ h.symm hv
        exact (hv (this ▸ hu)).elim
  · rw [mergeMap_of_not_mem hu, mergeMap_of_mem hv]
    constructor
    · intro he
      have hm := component_subset hX hθ hv (rep_component_mem (X := X) (θ := θ) (π v))
      rw [← he] at hm
      exact (hu hm).elim
    · rintro (h | ⟨h, _⟩)
      · exact (hu (h ▸ hv)).elim
      · exact (hu h).elim
  · rw [mergeMap_of_not_mem hu, mergeMap_of_not_mem hv]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h, _⟩)
      · exact h
      · exact (hu h).elim

theorem mergeMap_coarsens (hX : X.induce T = X) (hθ : 0 < θ) {u v : V}
    (h : π u = π v) : mergeMap π T X θ u = mergeMap π T X θ v :=
  (merge_eq_iff hX hθ u v).mpr (Or.inl h)

/-- The merged map is again a labeling, when the region consists of labels. -/
theorem mergeMap_isLabeling (hπ : IsLabeling π) (hT : ∀ b ∈ T, π b = b)
    (hX : X.induce T = X) (hθ : 0 < θ) : IsLabeling (mergeMap π T X θ) := by
  intro v
  by_cases hv : π v ∈ T
  · set r := rep (X.strongComponent θ (π v)) (π v)
    have hr : r ∈ X.strongComponent θ (π v) := rep_component_mem (π v)
    have hrT : r ∈ T := component_subset hX hθ hv hr
    have hlab : π r = r := hT r hrT
    rw [mergeMap_of_mem hv, mergeMap_of_mem (by rw [hlab]; exact hrT), hlab]
    exact (rep_component_eq_iff (X := X) (θ := θ) r (π v)).mpr
      ((X.mem_strongComponent θ (π v) r).mp hr).symm
  · rw [mergeMap_of_not_mem hv, mergeMap_of_not_mem (by rw [hπ v]; exact hv), hπ v]

omit [Fintype V] in
/-- The labels of a region given by a vertex set. -/
theorem image_labels (hπ : IsLabeling π) (S : Finset V) : ∀ b ∈ S.image π, π b = b := by
  intro b hb
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hb
  exact hπ v

/-! ### Groups and the cache update -/

/-- Groups of old labels merged by the call. -/
def mergeGroups (T : Finset V) (X : WeightedGraph V) (θ : ℝ) : Finset (Finset V) :=
  T.image (X.strongComponent θ)

/-- Groups of at least two old labels; each needs one new cut query. -/
def nontrivialGroups (T : Finset V) (X : WeightedGraph V) (θ : ℝ) : Finset (Finset V) :=
  (mergeGroups T X θ).filter (fun K => 2 ≤ K.card)

/-- Cache after the merge, given the answers `ans K` for the nontrivial groups. -/
def mergeCache (T : Finset V) (X : WeightedGraph V) (θ : ℝ) (cache : V → ℝ)
    (ans : Finset V → ℝ) (b : V) : ℝ :=
  if b ∈ T then
    if rep (X.strongComponent θ b) b = b then
      if 2 ≤ (X.strongComponent θ b).card then ans (X.strongComponent θ b) else cache b
    else 0
  else cache b

theorem card_le_one_component {b : V} (h : ¬2 ≤ (X.strongComponent θ b).card) :
    X.strongComponent θ b = {b} := by
  have hb := X.mem_strongComponent_self θ b
  have hc : (X.strongComponent θ b).card ≤ 1 := by omega
  exact Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hb, fun c hc' => Finset.card_le_one.mp hc c hc' b hb⟩

/-- **The merged cache is exact.** -/
theorem mergeCache_correct (G : WeightedGraph V)
    (hX : X.induce T = X) (hθ : 0 < θ) {cache : V → ℝ}
    (hc : ∀ b, cache b = G.cut (fiber π b)) {ans : Finset V → ℝ}
    (hans : ∀ K ∈ nontrivialGroups T X θ, ans K = G.cut (pull π K)) (b : V) :
    mergeCache T X θ cache ans b = G.cut (fiber (mergeMap π T X θ) b) := by
  by_cases hbT : b ∈ T
  · by_cases hrep : rep (X.strongComponent θ b) b = b
    · -- The fiber of a group representative is the union of the group's old blocks.
      have hfib : fiber (mergeMap π T X θ) b = pull π (X.strongComponent θ b) := by
        ext v
        simp only [mem_fiber, mem_pull]
        constructor
        · intro hv
          by_cases hvT : π v ∈ T
          · rw [mergeMap_of_mem hvT] at hv
            have hr : rep (X.strongComponent θ (π v)) (π v) = rep (X.strongComponent θ b) b := by
              rw [hv, hrep]
            exact (X.mem_strongComponent θ b (π v)).mpr
              ((rep_component_eq_iff (X := X) (θ := θ) (π v) b).mp hr).symm
          · rw [mergeMap_of_not_mem hvT] at hv
            exact (hvT (hv ▸ hbT)).elim
        · intro hv
          have hvT := component_subset hX hθ hbT hv
          rw [mergeMap_of_mem hvT]
          have hr := (rep_component_eq_iff (X := X) (θ := θ) (π v) b).mpr
            ((X.mem_strongComponent θ b (π v)).mp hv).symm
          rw [hr, hrep]
      simp only [mergeCache, hbT, hrep, ↓reduceIte]
      rw [hfib]
      split_ifs with h2
      · exact hans _ (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hbT, h2⟩)
      · rw [card_le_one_component h2, hc]
        rfl
    · -- A retired label has an empty fiber.
      have hfib : fiber (mergeMap π T X θ) b = ∅ := by
        ext v
        simp only [mem_fiber, Finset.notMem_empty, iff_false]
        intro hv
        by_cases hvT : π v ∈ T
        · rw [mergeMap_of_mem hvT] at hv
          have hmem := rep_component_mem (X := X) (θ := θ) (π v)
          rw [hv] at hmem
          have hrel := (X.mem_strongComponent θ (π v) b).mp hmem
          apply hrep
          rw [← strongComponent_eq_of_related hrel,
            rep_congr (X.strongComponent_nonempty θ (π v)) b (π v)]
          exact hv
        · rw [mergeMap_of_not_mem hvT] at hv
          exact hvT (hv ▸ hbT)
      simp only [mergeCache, hbT, hrep, ↓reduceIte]
      rw [hfib, cut_empty]
  · have hfib : fiber (mergeMap π T X θ) b = fiber π b := by
      ext v
      simp only [mem_fiber]
      by_cases hvT : π v ∈ T
      · rw [mergeMap_of_mem hvT]
        constructor
        · intro hv
          have := component_subset hX hθ hvT (rep_component_mem (X := X) (θ := θ) (π v))
          rw [hv] at this
          exact (hbT this).elim
        · intro hv
          exact (hbT (hv ▸ hvT)).elim
      · rw [mergeMap_of_not_mem hvT]
    simp only [mergeCache, hbT, ↓reduceIte]
    rw [hfib, hc]

/-! ### Counting blocks -/

/-- Live labels of a labeling. -/
def liveLabels (π : V → V) : Finset V := Finset.univ.filter (fun b => π b = b)

theorem mem_liveLabels_iff (hπ : IsLabeling π) (b : V) : b ∈ liveLabels π ↔ ∃ v, π v = b := by
  simp only [liveLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨b, h⟩, fun ⟨v, hv⟩ => hv ▸ hπ v⟩

/-- **Each nontrivial group removes at least one block.** -/
theorem card_liveLabels_merge (hT : ∀ b ∈ T, π b = b) (hX : X.induce T = X) (hθ : 0 < θ) :
    (liveLabels (mergeMap π T X θ)).card + (nontrivialGroups T X θ).card ≤
      (liveLabels π).card := by
  -- New labels: old labels outside `T`, and group representatives inside `T`.
  have hsub : liveLabels (mergeMap π T X θ) ⊆ (liveLabels π \ T) ∪
      T.filter (fun b => rep (X.strongComponent θ b) b = b) := by
    intro b hb
    have hb' : mergeMap π T X θ b = b := (Finset.mem_filter.mp hb).2
    by_cases hbT : b ∈ T
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbT, ?_⟩)
      have := mergeMap_of_mem (π := π) (X := X) (θ := θ) (v := b) (by rw [hT b hbT]; exact hbT)
      rw [hT b hbT] at this
      rw [← this]
      exact hb'
    · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, hbT⟩)
      have hπb : π b ∉ T := by
        intro h
        have hm := component_subset hX hθ h (rep_component_mem (X := X) (θ := θ) (π b))
        rw [← mergeMap_of_mem h, hb'] at hm
        exact hbT hm
      have := mergeMap_of_not_mem (π := π) (X := X) (θ := θ) hπb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← this]; exact hb'⟩
  have hreps : (T.filter (fun b => rep (X.strongComponent θ b) b = b)).card ≤
      (mergeGroups T X θ).card := by
    apply Finset.card_le_card_of_injOn (X.strongComponent θ)
    · intro b hb
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hb).1
    · intro b hb c hc he
      have hb' := (Finset.mem_filter.mp hb).2
      have hc' := (Finset.mem_filter.mp hc).2
      rw [← hb', ← hc']
      rw [he]
      exact rep_congr (X.strongComponent_nonempty θ c) b c
  -- Groups partition `T`, so `|T| ≥ |groups| + |nontrivial groups|`.
  have hdisj : Set.PairwiseDisjoint (mergeGroups T X θ : Set (Finset V)) id := by
    intro K hK L hL hne
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hL
    rcases X.strongComponent_eq_or_disjoint θ b c with h | h
    · exact (hne h).elim
    · exact h
  have hunion : (mergeGroups T X θ).biUnion id = T := by
    ext b
    simp only [Finset.mem_biUnion, id]
    constructor
    · rintro ⟨K, hK, hbK⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hK
      exact component_subset hX hθ hc hbK
    · intro hb
      exact ⟨_, Finset.mem_image_of_mem _ hb, X.mem_strongComponent_self θ b⟩
  have hcardT : (mergeGroups T X θ).card + (nontrivialGroups T X θ).card ≤ T.card := by
    have hsum : T.card = ∑ K ∈ mergeGroups T X θ, K.card := by
      have := Finset.card_biUnion hdisj
      rw [hunion] at this
      simpa only [id] using this
    rw [hsum, nontrivialGroups, Finset.card_filter, Finset.card_eq_sum_ones,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro K hK
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hK
    have := (X.strongComponent_nonempty θ c).card_pos
    split_ifs <;> omega
  have hTlive : T ⊆ liveLabels π := fun b hb =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT b hb⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (liveLabels π \ T)
    (T.filter (fun b => rep (X.strongComponent θ b) b = b))
  have h3 := Finset.card_sdiff_add_card_eq_card hTlive
  omega

end
end CutQueryComplexity.WeightedGraph
