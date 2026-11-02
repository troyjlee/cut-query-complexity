import CutQueryComplexity.TwoRespecting.WeakMajority
import CutQueryComplexity.TwoRespecting.AllMinimaRect
import CutQueryComplexity.TwoRespecting.TreeCover
import CutQueryComplexity.TwoRespecting.ProgInterface

/-! # All minimum cuts respecting a fixed tree (all-minima plan, M4)

For an explicit rooted spanning tree `T` and a level `ℓ`, `allTwoRespecting T ℓ`:

1. queries `cut (A e)` for every tree edge `e` and runs the two weak majority searches
   (`edgeInfoW`), giving the weak interest sets `interestW`;
2. for every ordered pair of heavy paths reports the pairs of value `ℓ` of its two Monge
   rectangles (`diffBlockAll`), populated with the weak interest lists;
3. for every heavy path reports its pairs of value `ℓ` (`samePathAll`);
4. returns, as a finite set of shores, every one-edge shore whose queried value is `ℓ` and the
   shore of every reported pair.

No shore is queried again at the end: the values come from step 1 and from the reporting
proofs, and duplicates are removed offline.

`allTwoRespecting_correct_of_le`: if `0 < ℓ` and `ℓ` is at most the cut of every shore crossing
one or two tree edges, the output is exactly the set of these shores whose cut is `ℓ`. Such a
pair is no heavier than either of its one-edge cuts, so its two edges are mutually weakly
interested (`mutual_weak_interest`) and the pair is an entry of one of the rectangles, all of
whose entries are at least `ℓ`. Two levels satisfy the hypothesis:

* `ℓ = λ(G) > 0` (`allTwoRespecting_correct`, `allTwoRespecting_spec`): the global minimum cuts
  that cross at most two tree edges, as used by the cover stage;
* the tree's own minimum, the least cut of a shore crossing one or two tree edges.
  `allMinTwoRespecting T` finds it with the existing search `twoRespectingVal` (no extra
  query) and reports every shore attaining it (`allMinTwoRespecting_spec`), whenever these
  shores all have positive cut, for instance when `0 < λ(G)`.

The cost is at most `250 n (⌈log₂ n⌉ + 1)` on every graph and every level
(`allTwoRespecting_cost`), and `322 n (⌈log₂ n⌉ + 1)` for `allMinTwoRespecting`, independently
of the output size.
-/

set_option autoImplicit false

namespace CutQueryComplexity
namespace TwoRespecting

open Search Search.Comp CutQueryComplexity.TwoRespecting.RootedTree

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- **All shores of value `ℓ` crossing one or two edges of `T`.** -/
noncomputable def allTwoRespecting (T : RootedTree V) (ℓ : ℝ) :
    Comp (Finset V) ℝ (Finset (Finset V)) :=
  (tabulate (edgeInfoW T) T.edgeList).bind fun info =>
    (mapList (fun pq => diffBlockAll T (interestW T info) ℓ pq.1 pq.2) T.headPairs).bind fun d =>
      (mapList (fun P => samePathAll T ℓ (T.sortPre (T.pathEdges P))) T.heads.toList).map
        fun s =>
          ((T.edgeList.filter fun e => decide ((info e).map Prod.fst = some ℓ)).map T.subtree ++
            (d.flatten ++ s.flatten).map fun p => T.pairShore p.1 p.2).toFinset

/-- The pairs reported on the genuine oracle. -/
noncomputable def reportedPairs (T : RootedTree V) (G : WeightedGraph V) (ℓ : ℝ) : List (V × V) :=
  (T.headPairs.map fun pq => (diffBlockAll T (interestW T (infoW T G)) ℓ pq.1 pq.2).eval G.cut).flatten ++
    (T.heads.toList.map fun P => (samePathAll T ℓ (T.sortPre (T.pathEdges P))).eval G.cut).flatten

variable {T : RootedTree V} (G : WeightedGraph V)

theorem eval_allTwoRespecting (ℓ : ℝ) :
    (allTwoRespecting T ℓ).eval G.cut =
      ((T.edgeList.filter fun e => decide ((infoW T G e).map Prod.fst = some ℓ)).map T.subtree ++
        (reportedPairs T G ℓ).map fun p => T.pairShore p.1 p.2).toFinset := by
  simp only [allTwoRespecting, eval_bind, eval_map, eval_mapList, reportedPairs, infoW]
  rfl

/-! ### Correctness -/

omit [LinearOrder V] in
/-- `λ(G)` is at most the cut of every shore crossing one or two tree edges. -/
theorem le_cut_of_eq_mincutValue {ℓ : ℝ} (hℓ : ℓ = mincutValue G) :
    ∀ S, T.IsTwoRespShore S → ℓ ≤ G.cut S :=
  fun _ hS => hℓ ▸ mincutValue_le G (isTwoRespShore_nonempty hS)

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
/-- A lower bound on the two-respecting shores bounds the pair cut of two distinct tree edges. -/
theorem pairCut_lower [Fintype V] [DecidableEq V] {ℓ : ℝ}
    (hlow : ∀ S, T.IsTwoRespShore S → ℓ ≤ G.cut S) {e f : V} (he : e ≠ T.root)
    (hf : f ≠ T.root) (hef : e ≠ f) : ℓ ≤ T.pairCut G e f :=
  hlow _ (Or.inr ⟨e, f, he, hf, hef, rfl⟩)

/-- Every reported pair is a pair of distinct tree edges with pair cut `ℓ`. -/
theorem reportedPairs_valid {ℓ : ℝ} (hlow : ∀ S, T.IsTwoRespShore S → ℓ ≤ G.cut S) {p : V × V}
    (hp : p ∈ reportedPairs T G ℓ) :
    p.1 ≠ T.root ∧ p.2 ≠ T.root ∧ p.1 ≠ p.2 ∧ T.pairCut G p.1 p.2 = ℓ := by
  have hpair := fun e f (he : e ≠ T.root) (hf : f ≠ T.root) (hef : e ≠ f) =>
    pairCut_lower (T := T) G hlow he hf hef
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
    obtain ⟨⟨P, Q⟩, hPQ, rfl⟩ := List.mem_map.mp hl
    have hne := (mem_headPairs.mp hPQ).2.2
    obtain ⟨h1, h2, h3⟩ := (diffBlockAll_spec G _ hne hpair).1 p hpl
    exact ⟨h1.1, h2.1, fun he => hne (h1.2.symm.trans (he ▸ h2.2)), h3⟩
  · obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
    obtain ⟨P, -, rfl⟩ := List.mem_map.mp hl
    have hlow : ∀ x ∈ T.sortPre (T.pathEdges P), ∀ y ∈ T.sortPre (T.pathEdges P), x < y →
        ℓ ≤ T.pairCut G x.val y.val := by
      intro x hx y hy hxy
      rw [mem_sortPre, mem_pathEdges] at hx hy
      exact hpair _ _ hx.1 hy.1 fun h => (ne_of_lt hxy) h
    obtain ⟨x, hx, y, hy, hxy, rfl, hv⟩ :=
      ((samePathAll_spec G ℓ _ _ le_rfl (pathEdges_chain P)).1 hlow p).mp hpl
    rw [mem_sortPre, mem_pathEdges] at hx hy
    exact ⟨hx.1, hy.1, fun h => (ne_of_lt hxy) h, hv⟩

/-- Every pair of distinct tree edges whose pair cut is a positive lower bound `ℓ` on the
two-respecting shores is reported, in one order. -/
theorem reportedPairs_complete {ℓ : ℝ} (hlow : ∀ S, T.IsTwoRespShore S → ℓ ≤ G.cut S)
    (hpos : 0 < ℓ) {e f : V}
    (he : e ≠ T.root) (hf : f ≠ T.root) (hef : e ≠ f) (hv : T.pairCut G e f = ℓ) :
    (e, f) ∈ reportedPairs T G ℓ ∨ (f, e) ∈ reportedPairs T G ℓ := by
  have hpair := fun e f (he : e ≠ T.root) (hf : f ≠ T.root) (hef : e ≠ f) =>
    pairCut_lower (T := T) G hlow he hf hef
  have hone : ∀ g, g ≠ T.root → ℓ ≤ G.cut (T.subtree g) := fun g hg =>
    hlow _ (Or.inl ⟨g, hg, rfl⟩)
  set I := interestW T (infoW T G)
  by_cases hh : T.head e = T.head f
  · -- same heavy path: the halving recursion reports the pair
    set P := T.head e
    have hePE : e ∈ T.pathEdges P := mem_pathEdges.mpr ⟨he, rfl⟩
    have hfPE : f ∈ T.pathEdges P := mem_pathEdges.mpr ⟨hf, hh.symm⟩
    have hlow : ∀ x ∈ T.sortPre (T.pathEdges P), ∀ y ∈ T.sortPre (T.pathEdges P), x < y →
        ℓ ≤ T.pairCut G x.val y.val := by
      intro x hx y hy hxy
      rw [mem_sortPre, mem_pathEdges] at hx hy
      exact hpair _ _ hx.1 hy.1 fun h => (ne_of_lt hxy) h
    have hcov := (samePathAll_spec G ℓ _ _ le_rfl (pathEdges_chain (T := T) P)).1 hlow
    have hmem : (samePathAll T ℓ (T.sortPre (T.pathEdges P))).eval G.cut ∈
        T.heads.toList.map fun P => (samePathAll T ℓ (T.sortPre (T.pathEdges P))).eval G.cut :=
      List.mem_map.mpr ⟨P, Finset.mem_toList.mpr (head_mem_heads he), rfl⟩
    rcases lt_or_gt_of_ne (show Pre.of T e ≠ Pre.of T f from hef) with hlt | hlt
    · left
      exact List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hmem, (hcov (e, f)).mpr
        ⟨Pre.of T e, mem_sortPre.mpr hePE, Pre.of T f, mem_sortPre.mpr hfPE, hlt, rfl, hv⟩⟩)
    · right
      exact List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hmem, (hcov (f, e)).mpr
        ⟨Pre.of T f, mem_sortPre.mpr hfPE, Pre.of T e, mem_sortPre.mpr hePE, hlt, rfl,
          (pairCut_comm G f e).trans hv⟩⟩)
  · -- different heavy paths: mutual weak interest and one of the rectangles
    have hle : ∀ g, g ≠ T.root → T.pairCut G e f ≤ G.cut (T.subtree g) := fun g hg =>
      hv ▸ hone g hg
    obtain ⟨hIe, hIf⟩ := mutual_weak_interest G he hf hh
      (lt_of_lt_of_le hpos (hone e he)) (lt_of_lt_of_le hpos (hone f hf)) (hle e he) (hle f hf)
    set P := T.head e
    set Q := T.head f
    have heL : e ∈ T.lpq I P Q := mem_lpq.mpr ⟨⟨he, rfl⟩, hIe⟩
    have hfL : f ∈ T.lpq I Q P := mem_lpq.mpr ⟨⟨hf, rfl⟩, hIf⟩
    have hPQ : (P, Q) ∈ T.headPairs :=
      mem_headPairs.mpr ⟨head_mem_heads he, head_mem_heads hf, hh⟩
    have hQP : (Q, P) ∈ T.headPairs :=
      mem_headPairs.mpr ⟨head_mem_heads hf, head_mem_heads he, Ne.symm hh⟩
    have hmem : ∀ {P' Q' : V}, (P', Q') ∈ T.headPairs →
        (diffBlockAll T I ℓ P' Q').eval G.cut ∈
          T.headPairs.map fun pq => (diffBlockAll T I ℓ pq.1 pq.2).eval G.cut :=
      fun h => List.mem_map.mpr ⟨_, h, rfl⟩
    by_cases hfP : T.IsAnc f P
    · -- then `e` is not above `Q`, so the block of `(Q, P)` reports `(f, e)`
      have heQ : ¬ T.IsAnc e Q := by
        intro heQ
        have h1 : T.IsAnc P Q := isAnc_trans (isAnc_head he) heQ
        have h2 : T.IsAnc Q P := isAnc_trans (isAnc_head hf) hfP
        exact hh (isAnc_antisymm h1 h2 ▸ rfl)
      right
      exact List.mem_append_left _ (List.mem_flatten.mpr ⟨_, hmem hQP,
        (diffBlockAll_spec G I (Ne.symm hh) hpair).2 f hfL e heL heQ
          ((pairCut_comm G f e).trans hv)⟩)
    · left
      exact List.mem_append_left _ (List.mem_flatten.mpr ⟨_, hmem hPQ,
        (diffBlockAll_spec G I hh hpair).2 e heL f hfL hfP hv⟩)

/-- **All two-respecting shores at a lower level.** If `0 < ℓ` and `ℓ` is at most the cut of
every shore crossing one or two edges of `T`, the output is exactly the set of these shores whose
cut is `ℓ`. -/
theorem allTwoRespecting_correct_of_le {ℓ : ℝ} (hlow : ∀ S, T.IsTwoRespShore S → ℓ ≤ G.cut S)
    (hpos : 0 < ℓ) (S : Finset V) :
    S ∈ (allTwoRespecting T ℓ).eval G.cut ↔ T.IsTwoRespShore S ∧ G.cut S = ℓ := by
  rw [eval_allTwoRespecting, List.mem_toFinset, List.mem_append]
  constructor
  · rintro (h | h)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      rw [List.mem_filter, decide_eq_true_iff] at he
      have her := mem_edgeList.mp he.1
      rw [infoW_eq G her] at he
      simp only [Option.map_some, Option.some.injEq] at he
      exact ⟨Or.inl ⟨e, her, rfl⟩, he.2⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      obtain ⟨h1, h2, h3, h4⟩ := reportedPairs_valid G hlow hp
      exact ⟨Or.inr ⟨p.1, p.2, h1, h2, h3, rfl⟩, h4⟩
  · rintro ⟨⟨e, he, rfl⟩ | ⟨e, f, he, hf, hef, rfl⟩, hv⟩
    · left
      refine List.mem_map.mpr ⟨e, ?_, rfl⟩
      rw [List.mem_filter, decide_eq_true_iff, infoW_eq G he]
      exact ⟨mem_edgeList.mpr he, by simp [hv]⟩
    · right
      rcases reportedPairs_complete G hlow hpos he hf hef hv with h | h
      · exact List.mem_map.mpr ⟨_, h, rfl⟩
      · exact List.mem_map.mpr ⟨_, h, pairShore_comm f e⟩

/-- **All global minimum cuts respecting a tree.** For `ℓ = λ(G) > 0`, the output is exactly the
set of shores crossing one or two edges of `T` whose cut is `ℓ`. -/
theorem allTwoRespecting_correct {ℓ : ℝ} (hℓ : ℓ = mincutValue G) (hpos : 0 < ℓ)
    (S : Finset V) :
    S ∈ (allTwoRespecting T ℓ).eval G.cut ↔ T.IsTwoRespShore S ∧ G.cut S = ℓ :=
  allTwoRespecting_correct_of_le G (le_cut_of_eq_mincutValue G hℓ) hpos S

/-! ### Query count -/

/-- **Query count**: at most `250 n (⌈log₂ n⌉ + 1)` cut queries on every graph and every level,
independently of the number of reported shores. -/
theorem allTwoRespecting_cost (ℓ : ℝ) :
    (allTwoRespecting T ℓ).cost G.cut ≤
      250 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) := by
  set n := Fintype.card V
  set N := T.nonroot.card
  set L := Nat.log 2 n
  set C := Nat.clog 2 n
  set I := interestW T (infoW T G)
  have hN : N ≤ n := by have := card_nonroot (T := T); omega
  have hLC : L ≤ C := Nat.log_le_clog 2 n
  -- the interest sets
  set Y := ∑ e ∈ T.nonroot, (I e).card
  have hY : Y ≤ N * (4 * (L + 1)) := by
    have := Finset.sum_le_card_nsmul T.nonroot (fun e => (I e).card) (4 * (L + 1))
      fun e _ => card_interestW_le _ e
    simpa using this
  set X := ∑ P ∈ T.heads, ∑ Q ∈ T.heads, (T.lpq I P Q).card
  have hX : X ≤ Y := sum_card_lpq_le I
  have hXswap : ∑ P ∈ T.heads, ∑ Q ∈ T.heads, (T.lpq I Q P).card = X := Finset.sum_comm
  -- costs of the three stages
  have htab : (tabulate (edgeInfoW T) T.edgeList).cost G.cut ≤ (16 * (L + 1) + 1) * N := by
    have := cost_tabulate_le G.cut (edgeInfoW T) T.edgeList (c := 16 * (L + 1) + 1)
      fun e _ => edgeInfoW_cost G.cut e
    rwa [length_edgeList] at this
  have hdiff : (mapList (fun pq => diffBlockAll T I ℓ pq.1 pq.2) T.headPairs).cost G.cut ≤
      43 * X := by
    rw [cost_mapList]
    calc (T.headPairs.map fun pq => (diffBlockAll T I ℓ pq.1 pq.2).cost G.cut).sum
        ≤ (T.headPairs.map fun pq =>
            25 * (T.lpq I pq.1 pq.2).card + 18 * (T.lpq I pq.2 pq.1).card).sum := by
          refine List.sum_le_sum fun pq hpq => ?_
          exact diffBlockAll_cost G I ℓ (mem_headPairs.mp hpq).2.2
      _ ≤ ∑ P ∈ T.heads, ∑ Q ∈ T.heads, (25 * (T.lpq I P Q).card + 18 * (T.lpq I Q P).card) :=
          sum_headPairs_le fun P Q => 25 * (T.lpq I P Q).card + 18 * (T.lpq I Q P).card
      _ = 25 * X + 18 * X := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hXswap]; rfl
      _ = 43 * X := by ring
  have hsame : (mapList (fun P => samePathAll T ℓ (T.sortPre (T.pathEdges P)))
      T.heads.toList).cost G.cut ≤ 17 * C * N := by
    rw [cost_mapList, Finset.sum_map_toList]
    calc ∑ P ∈ T.heads, (samePathAll T ℓ (T.sortPre (T.pathEdges P))).cost G.cut
        ≤ ∑ P ∈ T.heads, 17 * C * (T.pathEdges P).card := by
          refine Finset.sum_le_sum fun P _ => ?_
          have h := (samePathAll_spec G ℓ _ _ le_rfl (pathEdges_chain (T := T) P)).2
          rw [length_sortPre] at h
          have hc : Nat.clog 2 (T.pathEdges P).card ≤ C :=
            Nat.clog_mono_right 2 (Finset.card_le_univ _)
          calc _ ≤ 17 * (T.pathEdges P).card * Nat.clog 2 (T.pathEdges P).card := h
            _ ≤ 17 * (T.pathEdges P).card * C := Nat.mul_le_mul_left _ hc
            _ = 17 * C * (T.pathEdges P).card := by ring
      _ = 17 * C * N := by rw [← Finset.mul_sum, sum_card_pathEdges]
  have hcost : (allTwoRespecting T ℓ).cost G.cut =
      (tabulate (edgeInfoW T) T.edgeList).cost G.cut +
        ((mapList (fun pq => diffBlockAll T I ℓ pq.1 pq.2) T.headPairs).cost G.cut +
          (mapList (fun P => samePathAll T ℓ (T.sortPre (T.pathEdges P)))
            T.heads.toList).cost G.cut) := by
    simp [allTwoRespecting, I, infoW]
  -- arithmetic
  have hLN : (L + 1) * N ≤ C * N + N := by
    calc (L + 1) * N ≤ (C + 1) * N := Nat.mul_le_mul_right N (by omega)
      _ = C * N + N := by ring
  have hCN : C * N ≤ C * n := Nat.mul_le_mul_left C hN
  have hY' : Y ≤ 4 * ((L + 1) * N) := by rw [Nat.mul_comm (L + 1) N]; linarith
  have htab' : (16 * (L + 1) + 1) * N = 16 * ((L + 1) * N) + N := by ring
  have hsame' : 17 * C * N = 17 * (C * N) := by ring
  have hgoal : 250 * n * (C + 1) = 250 * (C * n) + 250 * n := by ring
  rw [hcost, hgoal]
  rw [htab'] at htab
  rw [hsame'] at hsame
  omega

/-- **All two-respecting minimum cuts.** For `ℓ = λ(G) > 0`: exact membership and the cost
bound `250 n (⌈log₂ n⌉ + 1)`. -/
theorem allTwoRespecting_spec (T : RootedTree V) (G : WeightedGraph V) {ℓ : ℝ}
    (hℓ : ℓ = mincutValue G) (hpos : 0 < ℓ) :
    (∀ S, S ∈ (allTwoRespecting T ℓ).eval G.cut ↔ T.IsTwoRespShore S ∧ G.cut S = ℓ) ∧
      (allTwoRespecting T ℓ).cost G.cut ≤
        250 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) :=
  ⟨allTwoRespecting_correct G hℓ hpos, allTwoRespecting_cost G ℓ⟩

/-! ### At the minimum value of the tree -/

/-- **All minimum two-respecting cuts of a tree.** The existing search finds the least cut of a
shore crossing one or two edges of `T`, with its value and no extra query; the reporter then
lists every shore attaining it. The output is that value and the family. -/
noncomputable def allMinTwoRespecting (T : RootedTree V) :
    Comp (Finset V) ℝ (ℝ × Finset (Finset V)) :=
  (twoRespectingVal T).bind fun o =>
    match o with
    | none => Comp.pure (0, ∅)
    | some r => (allTwoRespecting T r.1).map fun F => (r.1, F)

/-- The value returned by `twoRespectingVal` is the cut of the shore of `twoRespecting`. -/
theorem eval_twoRespectingVal_eq (hV : ∃ v, v ≠ T.root) :
    (twoRespectingVal T).eval G.cut =
      some (G.cut ((twoRespecting T).eval G.cut), (twoRespecting T).eval G.cut) := by
  obtain ⟨v, hv⟩ := hV
  have hmem : T.subtree v ∈ candidates T (foundPairs T G) :=
    List.mem_append_left _ (List.mem_map.mpr ⟨v, mem_edgeList.mpr hv, rfl⟩)
  have hne : (candidates T (foundPairs T G)).map (fun C => (C, G.cut C)) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; rw [h] at hmem; simp at hmem
  obtain ⟨p, hpm, hb, -⟩ := bestShore_spec _ hne
  obtain ⟨X, -, rfl⟩ := List.mem_map.mp hpm
  rw [eval_twoRespectingVal G, eval_twoRespecting G, hb]
  rfl

/-- The cost of `allMinTwoRespecting` on every graph: the single-cut search and the reporter. -/
theorem allMinTwoRespecting_cost :
    (allMinTwoRespecting T).cost G.cut ≤
      322 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) := by
  have h1 := twoRespecting_cost (T := T) G
  rw [← cost_twoRespectingVal G] at h1
  have hsum : 72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) +
      250 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) =
      322 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) := by ring
  simp only [allMinTwoRespecting, cost_bind]
  split
  · simp only [cost_pure]
    omega
  · rename_i r _
    simp only [cost_map]
    have h2 := allTwoRespecting_cost (T := T) G r.1
    omega

/-- **All minimum two-respecting cuts of a tree.** If every shore crossing one or two edges of
`T` has positive cut (for instance when `0 < λ(G)`), the returned value is attained by such a
shore and is at most the cut of every such shore, and the returned family is exactly the set of
these shores of least cut. The cost is at most `322 n (⌈log₂ n⌉ + 1)` on every graph. -/
theorem allMinTwoRespecting_spec (T : RootedTree V) (G : WeightedGraph V)
    (hV : ∃ v, v ≠ T.root) (hpos : ∀ S, T.IsTwoRespShore S → 0 < G.cut S) :
    (∃ S, T.IsTwoRespShore S ∧ G.cut S = ((allMinTwoRespecting T).eval G.cut).1) ∧
      (∀ S, T.IsTwoRespShore S → ((allMinTwoRespecting T).eval G.cut).1 ≤ G.cut S) ∧
      (∀ S, S ∈ ((allMinTwoRespecting T).eval G.cut).2 ↔
        T.IsTwoRespShore S ∧ ∀ S', T.IsTwoRespShore S' → G.cut S ≤ G.cut S') ∧
      (allMinTwoRespecting T).cost G.cut ≤
        322 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) := by
  obtain ⟨hS₀, hmin⟩ := twoRespecting_correct G hV
  set S₀ := (twoRespecting T).eval G.cut
  have heval : (allMinTwoRespecting T).eval G.cut =
      (G.cut S₀, (allTwoRespecting T (G.cut S₀)).eval G.cut) := by
    simp only [allMinTwoRespecting, eval_bind, eval_twoRespectingVal_eq G hV, eval_map, S₀]
  have hcorr := allTwoRespecting_correct_of_le G hmin (hpos S₀ hS₀)
  rw [heval]
  refine ⟨⟨S₀, hS₀, rfl⟩, hmin, fun S => ?_, allMinTwoRespecting_cost G⟩
  rw [hcorr S]
  constructor
  · rintro ⟨hS, hv⟩
    exact ⟨hS, fun S' hS' => by rw [hv]; exact hmin S' hS'⟩
  · rintro ⟨hS, hle⟩
    exact ⟨hS, le_antisymm (hle S₀ hS₀) (hmin S hS)⟩

omit [LinearOrder V] in
/-- With a positive global minimum cut, every shore crossing one or two tree edges has positive
cut. -/
theorem twoResp_cut_pos_of_mincut_pos (hlam : 0 < mincutValue G) :
    ∀ S, T.IsTwoRespShore S → 0 < G.cut S :=
  fun _ hS => lt_of_lt_of_le hlam (mincutValue_le G (isTwoRespShore_nonempty hS))

/-- **Query bound for all minimum two-respecting cuts.** For every rooted spanning tree `T` with
an edge there is one decision tree with at most `322 n (⌈log₂ n⌉ + 1)` cut queries that, on every
nonnegative weighted graph whose shores crossing one or two edges of `T` all have positive cut,
returns the least cut of these shores and exactly the set of these shores attaining it. -/
theorem allMinTwoRespecting_queryBound (T : RootedTree V) (hV : ∃ v, v ≠ T.root) :
    ∃ D : DTree (Finset V) ℝ (Option (ℝ × Finset (Finset V)))
        (322 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1)),
      ∀ G : WeightedGraph V, (∀ S, T.IsTwoRespShore S → 0 < G.cut S) →
        ∃ out, D.eval G.cut = some out ∧
          (∃ S, T.IsTwoRespShore S ∧ G.cut S = out.1) ∧
          (∀ S, T.IsTwoRespShore S → out.1 ≤ G.cut S) ∧
          ∀ S, S ∈ out.2 ↔ T.IsTwoRespShore S ∧ ∀ S', T.IsTwoRespShore S' → G.cut S ≤ G.cut S' := by
  refine ⟨(allMinTwoRespecting T).toDTree _, fun G hpos => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := allMinTwoRespecting_spec T G hV hpos
  exact ⟨_, Comp.toDTree_eval _ _ h4, h1, h2, h3⟩

end TwoRespecting
end CutQueryComplexity
