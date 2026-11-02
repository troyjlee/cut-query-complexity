import CutQueryComplexity.TwoRespecting.Rect

/-! # Deterministic two-respecting minimum cuts in `O(n log n)` cut queries

Theorem 13 of the deterministic mincut paper. Given an explicit rooted spanning
tree `T` (whose edges need not be graph edges), `twoRespecting T` returns a shore
that crosses one or two tree edges and has minimum cut value among all such
shores, for every nonnegative weighted graph.

The algorithm:
1. for every tree edge `e`, query `cut (A e)` and find the endpoints `c e`, `d e`
   of its two interest paths by majority-subtree searches;
2. form the heavy paths each edge is interested in;
3. for every ordered pair of heavy paths, search two Monge rectangles by SMAWK;
4. search pairs on each heavy path by halving;
5. query all one-edge shores and found pairs and return the lightest.
-/

namespace CutQueryComplexity
namespace TwoRespecting

open Search Search.Comp RootedTree

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace RootedTree

variable (T : RootedTree V)

/-- Tree edges, as their lower endpoints. -/
noncomputable def nonroot : Finset V := Finset.univ.erase T.root

/-- Tree edges in vertex order. -/
noncomputable def edgeList : List V := T.nonroot.sort (· ≤ ·)

/-- Heads of the heavy paths. -/
noncomputable def heads : Finset V := T.nonroot.image T.head

/-- Edges of the heavy path with head `P`. -/
noncomputable def pathEdges (P : V) : Finset V := T.nonroot.filter fun e => T.head e = P

/-- Edges of path `P` interested in path `Q`. -/
noncomputable def lpq (I : V → Finset V) (P Q : V) : Finset V :=
  (T.pathEdges P).filter fun e => Q ∈ I e

/-- Ordered pairs of distinct heavy paths. -/
noncomputable def headPairs : List (V × V) :=
  ((T.heads ×ˢ T.heads).filter fun p => p.1 ≠ p.2).toList

/-- A shore crossing exactly one or two tree edges. -/
def IsTwoRespShore (S : Finset V) : Prop :=
  (∃ e, e ≠ T.root ∧ S = T.subtree e) ∨
    ∃ e f, e ≠ T.root ∧ f ≠ T.root ∧ e ≠ f ∧ S = T.pairShore e f

end RootedTree

section Algorithm

variable (T : RootedTree V)

/-- One cut query and two majority searches for the tree edge above `e`. -/
noncomputable def edgeInfo (e : V) : Comp (Finset V) ℝ (V × V) :=
  (ask (T.subtree e)).bind fun a =>
    (majoritySearch T (measOut (T.subtree e) a) a).bind fun c =>
      (majoritySearch T (measIn (T.subtree e) a) a).map fun d => (c, d)

/-- Heavy paths an edge is interested in, other than its own. -/
noncomputable def interestOf (info : V → Option (V × V)) (e : V) : Finset V :=
  match info e with
  | none => ∅
  | some cd => (T.headsAbove cd.1 ∪ T.headsAbove cd.2).erase (T.head e)

/-- The two Monge rectangles for an ordered pair of distinct heavy paths. -/
noncomputable def diffBlock (I : V → Finset V) (P Q : V) : Comp (Finset V) ℝ (List (V × V)) :=
  (rectMin T (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val)
      (T.sortPre ((T.lpq I P Q).filter fun e => T.IsAnc e Q))
      (T.sortDual (T.lpq I Q P))).bind fun l1 =>
    (rectMin T (fun c : Pre T => c.val)
        (T.sortPre ((T.lpq I P Q).filter fun e => ¬ T.IsAnc e Q))
        (T.sortPre ((T.lpq I Q P).filter fun f => ¬ T.IsAnc f P))).map fun l3 => l1 ++ l3

/-- The lightest candidate shore. -/
noncomputable def bestShore : List (Finset V × ℝ) → Option (Finset V × ℝ)
  | [] => none
  | x :: xs =>
      match bestShore xs with
      | none => some x
      | some y => if y.2 < x.2 then some y else some x

/-- Candidate shores: every one-edge shore and every pair found by the searches. -/
noncomputable def candidates (pairs : List (V × V)) : List (Finset V) :=
  T.edgeList.map T.subtree ++ pairs.map fun p => T.pairShore p.1 p.2

/-- **Deterministic two-respecting minimum cut.** -/
noncomputable def twoRespecting : Comp (Finset V) ℝ (Finset V) :=
  (tabulate (edgeInfo T) T.edgeList).bind fun info =>
    (mapList (fun pq => diffBlock T (interestOf T info) pq.1 pq.2) T.headPairs).bind fun d =>
      (mapList (fun P => samePath T (T.sortPre (T.pathEdges P))) T.heads.toList).bind fun s =>
        (askList (candidates T (d.flatten ++ s.flatten))).map fun vals =>
          ((bestShore ((candidates T (d.flatten ++ s.flatten)).zip vals)).map Prod.fst).getD ∅

end Algorithm

/-! ### Basic facts -/

section Basic

variable {T : RootedTree V}

omit [LinearOrder V] in
theorem mem_nonroot {e : V} : e ∈ T.nonroot ↔ e ≠ T.root := by simp [RootedTree.nonroot]

theorem mem_edgeList {e : V} : e ∈ T.edgeList ↔ e ≠ T.root := by
  simp [RootedTree.edgeList, mem_nonroot]

theorem length_edgeList : T.edgeList.length = T.nonroot.card := by
  simp [RootedTree.edgeList, Finset.length_sort]

omit [LinearOrder V] in
theorem card_nonroot : T.nonroot.card = Fintype.card V - 1 := by
  simp [RootedTree.nonroot, Finset.card_erase_of_mem]

theorem mem_pathEdges {P e : V} : e ∈ T.pathEdges P ↔ e ≠ T.root ∧ T.head e = P := by
  classical
  simp [RootedTree.pathEdges, mem_nonroot]

theorem mem_lpq {I : V → Finset V} {P Q e : V} :
    e ∈ T.lpq I P Q ↔ (e ≠ T.root ∧ T.head e = P) ∧ Q ∈ I e := by
  classical
  simp [RootedTree.lpq, mem_pathEdges]

theorem head_mem_heads {e : V} (he : e ≠ T.root) : T.head e ∈ T.heads :=
  Finset.mem_image.mpr ⟨e, mem_nonroot.mpr he, rfl⟩

theorem mem_headPairs {P Q : V} : (P, Q) ∈ T.headPairs ↔ P ∈ T.heads ∧ Q ∈ T.heads ∧ P ≠ Q := by
  simp [RootedTree.headPairs, and_assoc]

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem bestShore_spec : ∀ L : List (Finset V × ℝ), L ≠ [] →
    ∃ p ∈ L, bestShore L = some p ∧ ∀ q ∈ L, p.2 ≤ q.2
  | [], h => absurd rfl h
  | x :: xs, _ => by
      simp only [bestShore]
      by_cases hxs : xs = []
      · subst hxs
        exact ⟨x, by simp, by simp [bestShore], by simp⟩
      obtain ⟨y, hy, hb, hmin⟩ := bestShore_spec xs hxs
      rw [hb]
      by_cases hlt : y.2 < x.2
      · refine ⟨y, by simp [hy], by simp [hlt], fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact le_of_lt hlt
        · exact hmin q hq
      · refine ⟨x, by simp, by simp [hlt], fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact le_rfl
        · exact le_trans (not_lt.mp hlt) (hmin q hq)

end Basic

/-! ### Interest paths from the edge information -/

section Interest

variable {T : RootedTree V} (G : WeightedGraph V)

/-- The edge information computed on the genuine oracle. -/
noncomputable def infoOf (T : RootedTree V) (G : WeightedGraph V) : V → Option (V × V) :=
  (tabulate (edgeInfo T) T.edgeList).eval G.cut

theorem infoOf_eq {e : V} (he : e ≠ T.root) :
    infoOf T G e = some
      ((majoritySearch T (measOut (T.subtree e) (G.cut (T.subtree e)))
          (G.cut (T.subtree e))).eval G.cut,
        (majoritySearch T (measIn (T.subtree e) (G.cut (T.subtree e)))
          (G.cut (T.subtree e))).eval G.cut) := by
  simp [infoOf, mem_edgeList.mpr he, edgeInfo]

/-- Interest along the out-measure puts the other edge's path in the interest set. -/
theorem head_mem_interest {e f : V} (he : e ≠ T.root) (hf : f ≠ T.root)
    (hhead : T.head f ≠ T.head e) (hpos : 0 < G.cut (T.subtree e))
    (hint : G.cut (T.subtree e) < 2 * muOut G (T.subtree e) (T.subtree f) ∨
      G.cut (T.subtree e) < 2 * muIn G (T.subtree e) (T.subtree f)) :
    T.head f ∈ interestOf T (infoOf T G) e := by
  simp only [interestOf, infoOf_eq G he]
  rw [Finset.mem_erase]
  refine ⟨hhead, ?_⟩
  have hheads : ∀ c : V, T.IsAnc f c → T.head f ∈ T.headsAbove c := fun c hfc => by
    classical
    simp only [RootedTree.headsAbove, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨f, ⟨hf, hfc⟩, rfl⟩
  rcases hint with h | h
  · have hs := (majoritySearch_spec (T := T) G.cut _ (subMeasure_muOut G (T.subtree e))
      (by rwa [muOut_univ]) (measOut_spec G (T.subtree e))).1 f
    rw [muOut_univ] at hs
    exact Finset.mem_union_left _ (hheads _ (hs.mp h))
  · have hs := (majoritySearch_spec (T := T) G.cut _ (subMeasure_muIn G (T.subtree e))
      (by rwa [muIn_univ]) (measIn_spec G (T.subtree e))).1 f
    rw [muIn_univ] at hs
    exact Finset.mem_union_right _ (hheads _ (hs.mp h))

/-- Lemma 35 in interest-set form: an improving pair on different paths puts each
edge in the other's list. -/
theorem mutual_interest {e f : V} (he : e ≠ T.root) (hf : f ≠ T.root)
    (hhead : T.head e ≠ T.head f) (hlte : T.pairCut G e f < G.cut (T.subtree e))
    (hltf : T.pairCut G e f < G.cut (T.subtree f)) :
    T.head f ∈ interestOf T (infoOf T G) e ∧ T.head e ∈ interestOf T (infoOf T G) f := by
  have hK : 0 ≤ T.pairCut G e f := G.cut_nonneg _
  have hpe : 0 < G.cut (T.subtree e) := lt_of_le_of_lt hK hlte
  have hpf : 0 < G.cut (T.subtree f) := lt_of_le_of_lt hK hltf
  have hltf' : G.cut (T.pairShore f e) < G.cut (T.subtree e) := by
    rw [pairShore_comm]; exact hlte
  by_cases hef : T.IsAnc e f
  · exact ⟨head_mem_interest G he hf (Ne.symm hhead) hpe
        (Or.inr (interest_nested_below G hef hltf le_rfl)),
      head_mem_interest G hf he hhead hpf (Or.inr (interest_nested_above G hef hpf))⟩
  · by_cases hfe : T.IsAnc f e
    · exact ⟨head_mem_interest G he hf (Ne.symm hhead) hpe
          (Or.inr (interest_nested_above G hfe hpe)),
        head_mem_interest G hf he hhead hpf
          (Or.inr (interest_nested_below G hfe hltf' le_rfl))⟩
    · exact ⟨head_mem_interest G he hf (Ne.symm hhead) hpe
          (Or.inl (interest_indep G hef hfe hltf le_rfl)),
        head_mem_interest G hf he hhead hpf (Or.inl (interest_indep G hfe hef hltf' le_rfl))⟩

end Interest

/-! ### The two rectangles of a pair of heavy paths -/

section Blocks

variable {T : RootedTree V} (G : WeightedGraph V) (I : V → Finset V)

theorem lpq_chain {P Q x y : V} (hx : x ∈ T.lpq I P Q) (hy : y ∈ T.lpq I P Q) :
    T.IsAnc x y ∨ T.IsAnc y x := by
  rw [mem_lpq] at hx hy
  exact isAnc_total_of_head_eq hx.1.1 hy.1.1 (hx.1.2.trans hy.1.2.symm)

theorem rect1_monge (P Q : V) :
    IsMonge (fun r (c : (Pre T)ᵒᵈ) => T.pairCut G r.val (OrderDual.ofDual c).val)
      (T.sortPre ((T.lpq I P Q).filter fun e => T.IsAnc e Q)) (T.sortDual (T.lpq I Q P)) := by
  classical
  intro r hr r' hr' c hc c' hc' hrr hcc
  rw [mem_sortPre, Finset.mem_filter] at hr hr'
  rw [mem_sortDual] at hc hc'
  have hcc' : OrderDual.ofDual c' < OrderDual.ofDual c := hcc
  have hQc' : T.IsAnc Q (OrderDual.ofDual c').val := by
    have h := mem_lpq.mp hc'
    exact h.1.2 ▸ isAnc_head h.1.1
  exact pairCut_monge_nested G (isAnc_of_lt_of_chain (lpq_chain I hr.1 hr'.1) hrr)
    (isAnc_of_lt_of_chain (lpq_chain I hc' hc) hcc') (isAnc_trans hr'.2 hQc')

/-- Below-head vertices: a member of path `Q` that is not an ancestor of the head `P`
of another path is independent of every member of `P` that is not an ancestor of `Q`. -/
theorem indep_of_not_anc_heads {P Q e f : V} (hPQ : P ≠ Q) (he : e ≠ T.root ∧ T.head e = P)
    (hf : f ≠ T.root ∧ T.head f = Q) (heQ : ¬ T.IsAnc e Q) (hfP : ¬ T.IsAnc f P) :
    ¬ T.IsAnc e f ∧ ¬ T.IsAnc f e := by
  have key : ∀ {x y X Y : V}, X ≠ Y → (x ≠ T.root ∧ T.head x = X) →
      (y ≠ T.root ∧ T.head y = Y) → ¬ T.IsAnc x Y → ¬ T.IsAnc x y := by
    intro x y X Y hXY hx hy hxY hxy
    have hYy : T.IsAnc Y y := hy.2 ▸ isAnc_head hy.1
    rcases isAnc_total_of_common hxy hYy with h | h
    · exact hxY h
    · have := head_eq_of_between hy.1 (hy.2 ▸ h) hxy
      exact hXY (hx.2 ▸ hy.2 ▸ this)
  exact ⟨key hPQ he hf heQ, key (Ne.symm hPQ) hf he hfP⟩

theorem rect3_monge {P Q : V} (hPQ : P ≠ Q) :
    IsMonge (fun r (c : Pre T) => T.pairCut G r.val c.val)
      (T.sortPre ((T.lpq I P Q).filter fun e => ¬ T.IsAnc e Q))
      (T.sortPre ((T.lpq I Q P).filter fun f => ¬ T.IsAnc f P)) := by
  classical
  intro r hr r' hr' c hc c' hc' hrr hcc
  rw [mem_sortPre, Finset.mem_filter] at hr hr' hc hc'
  refine pairCut_monge_indep G (isAnc_of_lt_of_chain (lpq_chain I hr.1 hr'.1) hrr)
    (isAnc_of_lt_of_chain (lpq_chain I hc.1 hc'.1) hcc) ?_
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  have hxs : x ∈ (T.lpq I P Q).filter fun e => ¬ T.IsAnc e Q := by
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr hr
    · exact Finset.mem_filter.mpr hr'
  have hys : y ∈ (T.lpq I Q P).filter fun f => ¬ T.IsAnc f P := by
    rcases hy with rfl | rfl
    · exact Finset.mem_filter.mpr hc
    · exact Finset.mem_filter.mpr hc'
  rw [Finset.mem_filter, mem_lpq] at hxs hys
  exact indep_of_not_anc_heads hPQ hxs.1.1 hys.1.1 hxs.2 hys.2

theorem diffBlock_spec {P Q : V} (hPQ : P ≠ Q) :
    (∀ p ∈ (diffBlock T I P Q).eval G.cut,
        (p.1 ≠ T.root ∧ T.head p.1 = P) ∧ (p.2 ≠ T.root ∧ T.head p.2 = Q)) ∧
      (∀ e ∈ T.lpq I P Q, ∀ f ∈ T.lpq I Q P, ¬ T.IsAnc f P →
        ∃ p ∈ (diffBlock T I P Q).eval G.cut, T.pairCut G p.1 p.2 ≤ T.pairCut G e f) ∧
      ((diffBlock T I P Q).eval G.cut).length ≤ (T.lpq I P Q).card ∧
      (diffBlock T I P Q).cost G.cut ≤ 13 * (T.lpq I P Q).card + 8 * (T.lpq I Q P).card := by
  classical
  obtain ⟨a1, a2, -, a4⟩ := rectMin_spec G (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val)
    (sortPre_pairwise _) (sortDual_pairwise _) (rect1_monge G I P Q)
  obtain ⟨b1, b2, -, b4⟩ := rectMin_spec G (fun c : Pre T => c.val)
    (sortPre_pairwise _) (sortPre_pairwise _) (rect3_monge (T := T) G I hPQ)
  have l1 := (rectMin_length_le (T := T) G.cut (fun c : (Pre T)ᵒᵈ => (OrderDual.ofDual c).val)
    (T.sortPre ((T.lpq I P Q).filter fun e => T.IsAnc e Q)) (T.sortDual (T.lpq I Q P))).1
  have l3 := (rectMin_length_le (T := T) G.cut (fun c : Pre T => c.val)
    (T.sortPre ((T.lpq I P Q).filter fun e => ¬ T.IsAnc e Q))
    (T.sortPre ((T.lpq I Q P).filter fun f => ¬ T.IsAnc f P))).1
  have hpart := Finset.card_filter_add_card_filter_not (s := T.lpq I P Q)
    (p := fun e => T.IsAnc e Q)
  have hsub3 := Finset.card_filter_le (T.lpq I Q P) (fun f => ¬ T.IsAnc f P)
  simp only [diffBlock, eval_bind, eval_map, cost_bind, cost_map]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨⟨r, hr, h1⟩, c, hc, h2⟩ := a1 p hp
      rw [mem_sortPre, Finset.mem_filter, mem_lpq] at hr
      rw [mem_sortDual, mem_lpq] at hc
      exact ⟨h1 ▸ hr.1.1, h2 ▸ hc.1⟩
    · obtain ⟨⟨r, hr, h1⟩, c, hc, h2⟩ := b1 p hp
      rw [mem_sortPre, Finset.mem_filter, mem_lpq] at hr hc
      exact ⟨h1 ▸ hr.1.1, h2 ▸ hc.1.1⟩
  · intro e he f hf hfP
    by_cases heQ : T.IsAnc e Q
    · obtain ⟨p, hp, hle⟩ := a2 (Pre.of T e)
        (mem_sortPre.mpr (Finset.mem_filter.mpr ⟨he, heQ⟩)) (OrderDual.toDual (Pre.of T f))
        (mem_sortDual.mpr hf)
      exact ⟨p, List.mem_append_left _ hp, hle⟩
    · obtain ⟨p, hp, hle⟩ := b2 (Pre.of T e)
        (mem_sortPre.mpr (Finset.mem_filter.mpr ⟨he, heQ⟩)) (Pre.of T f)
        (mem_sortPre.mpr (Finset.mem_filter.mpr ⟨hf, hfP⟩))
      exact ⟨p, List.mem_append_right _ hp, hle⟩
  · rw [List.length_append]
    rw [length_sortPre] at l1 l3
    omega
  · rw [length_sortPre, length_sortDual] at a4
    rw [length_sortPre, length_sortPre] at b4
    omega

end Blocks

/-! ### Correctness -/

section Correct

variable {T : RootedTree V} (G : WeightedGraph V)

theorem pathEdges_chain (P : V) : IsChainList (T.sortPre (T.pathEdges P)) := by
  refine ⟨sortPre_pairwise _, fun x hx y hy => ?_⟩
  rw [mem_sortPre, mem_pathEdges] at hx hy
  exact isAnc_total_of_head_eq hx.1 hy.1 (hx.2.trans hy.2.symm)

/-- The pairs found by all searches on the genuine oracle. -/
noncomputable def foundPairs (T : RootedTree V) (G : WeightedGraph V) : List (V × V) :=
  (T.headPairs.map fun pq => (diffBlock T (interestOf T (infoOf T G)) pq.1 pq.2).eval G.cut).flatten ++
    (T.heads.toList.map fun P => (samePath T (T.sortPre (T.pathEdges P))).eval G.cut).flatten

theorem foundPairs_valid {p : V × V} (hp : p ∈ foundPairs T G) :
    p.1 ≠ T.root ∧ p.2 ≠ T.root ∧ p.1 ≠ p.2 := by
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
    obtain ⟨⟨P, Q⟩, hPQ, rfl⟩ := List.mem_map.mp hl
    have hne := (mem_headPairs.mp hPQ).2.2
    obtain ⟨h1, h2⟩ := (diffBlock_spec G _ hne).1 p hpl
    exact ⟨h1.1, h2.1, fun he => hne (h1.2.symm.trans (he ▸ h2.2))⟩
  · obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
    obtain ⟨P, -, rfl⟩ := List.mem_map.mp hl
    obtain ⟨⟨x, hx, h1⟩, ⟨y, hy, h2⟩, h3⟩ :=
      (samePath_spec G _ _ le_rfl (pathEdges_chain P)).1 p hpl
    rw [mem_sortPre, mem_pathEdges] at hx hy
    exact ⟨h1 ▸ hx.1, h2 ▸ hy.1, h3⟩

omit [LinearOrder V] in
theorem pairCut_comm (e f : V) : T.pairCut G e f = T.pairCut G f e := by
  unfold RootedTree.pairCut; rw [pairShore_comm]

/-- Every pair improving on both of its one-edge cuts is dominated by a found pair. -/
theorem foundPairs_cover {e f : V} (he : e ≠ T.root) (hf : f ≠ T.root) (hef : e ≠ f)
    (hlte : T.pairCut G e f < G.cut (T.subtree e)) (hltf : T.pairCut G e f < G.cut (T.subtree f)) :
    ∃ p ∈ foundPairs T G, T.pairCut G p.1 p.2 ≤ T.pairCut G e f := by
  set I := interestOf T (infoOf T G)
  by_cases hh : T.head e = T.head f
  · -- same heavy path: the halving recursion covers the pair
    set P := T.head e
    have hePE : e ∈ T.pathEdges P := mem_pathEdges.mpr ⟨he, rfl⟩
    have hfPE : f ∈ T.pathEdges P := mem_pathEdges.mpr ⟨hf, hh.symm⟩
    obtain ⟨-, hcov, -⟩ := samePath_spec G _ _ le_rfl (pathEdges_chain (T := T) P)
    have hmem : (samePath T (T.sortPre (T.pathEdges P))).eval G.cut ∈
        T.heads.toList.map fun P => (samePath T (T.sortPre (T.pathEdges P))).eval G.cut :=
      List.mem_map.mpr ⟨P, Finset.mem_toList.mpr (head_mem_heads he), rfl⟩
    rcases lt_or_gt_of_ne (show Pre.of T e ≠ Pre.of T f from hef) with hlt | hlt
    · obtain ⟨p, hp, hle⟩ := hcov (Pre.of T e) (mem_sortPre.mpr hePE) (Pre.of T f)
        (mem_sortPre.mpr hfPE) hlt
      exact ⟨p, List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hmem, hp⟩), hle⟩
    · obtain ⟨p, hp, hle⟩ := hcov (Pre.of T f) (mem_sortPre.mpr hfPE) (Pre.of T e)
        (mem_sortPre.mpr hePE) hlt
      exact ⟨p, List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hmem, hp⟩),
        hle.trans (le_of_eq (pairCut_comm G f e))⟩
  · -- different heavy paths: mutual interest and one of the rectangles
    obtain ⟨hIe, hIf⟩ := mutual_interest G he hf hh hlte hltf
    set P := T.head e
    set Q := T.head f
    have heL : e ∈ T.lpq I P Q := mem_lpq.mpr ⟨⟨he, rfl⟩, hIe⟩
    have hfL : f ∈ T.lpq I Q P := mem_lpq.mpr ⟨⟨hf, rfl⟩, hIf⟩
    have hPQ : (P, Q) ∈ T.headPairs := mem_headPairs.mpr ⟨head_mem_heads he, head_mem_heads hf, hh⟩
    have hQP : (Q, P) ∈ T.headPairs :=
      mem_headPairs.mpr ⟨head_mem_heads hf, head_mem_heads he, Ne.symm hh⟩
    have hmem : ∀ {P' Q' : V}, (P', Q') ∈ T.headPairs →
        (diffBlock T I P' Q').eval G.cut ∈
          T.headPairs.map fun pq => (diffBlock T I pq.1 pq.2).eval G.cut :=
      fun h => List.mem_map.mpr ⟨_, h, rfl⟩
    by_cases hfP : T.IsAnc f P
    · -- then `e` is not above `Q`, so use the block of `(Q, P)` with the roles swapped
      have heQ : ¬ T.IsAnc e Q := by
        intro heQ
        have hPe : T.IsAnc P e := isAnc_head he
        have hQf : T.IsAnc Q f := isAnc_head hf
        have h1 : T.IsAnc P Q := isAnc_trans hPe heQ
        have h2 : T.IsAnc Q P := isAnc_trans hQf hfP
        exact hh (isAnc_antisymm h1 h2 ▸ rfl)
      obtain ⟨p, hp, hle⟩ := (diffBlock_spec G I (Ne.symm hh)).2.1 f hfL e heL heQ
      exact ⟨p, List.mem_append_left _ (List.mem_flatten.mpr ⟨_, hmem hQP, hp⟩),
        hle.trans (le_of_eq (pairCut_comm G f e))⟩
    · obtain ⟨p, hp, hle⟩ := (diffBlock_spec G I hh).2.1 e heL f hfL hfP
      exact ⟨p, List.mem_append_left _ (List.mem_flatten.mpr ⟨_, hmem hPQ, hp⟩), hle⟩

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem zip_map_self {α β : Type} (f : α → β) :
    ∀ l : List α, l.zip (l.map f) = l.map fun x => (x, f x)
  | [] => rfl
  | x :: xs => by simp [zip_map_self f xs]

theorem eval_twoRespecting :
    (twoRespecting T).eval G.cut =
      ((bestShore ((candidates T (foundPairs T G)).map fun C => (C, G.cut C))).map
        Prod.fst).getD ∅ := by
  simp [twoRespecting, foundPairs, infoOf, zip_map_self]

/-- **Correctness of the two-respecting search.** The output crosses one or two tree
edges and is lightest among all such shores. -/
theorem twoRespecting_correct (hV : ∃ v, v ≠ T.root) :
    T.IsTwoRespShore ((twoRespecting T).eval G.cut) ∧
      ∀ S, T.IsTwoRespShore S → G.cut ((twoRespecting T).eval G.cut) ≤ G.cut S := by
  obtain ⟨v, hv⟩ := hV
  set C := candidates T (foundPairs T G)
  have hvC : T.subtree v ∈ C :=
    List.mem_append_left _ (List.mem_map.mpr ⟨v, mem_edgeList.mpr hv, rfl⟩)
  have hne : C.map (fun C => (C, G.cut C)) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; rw [h] at hvC; simp at hvC
  obtain ⟨⟨S, x⟩, hpm, hb, hmin⟩ := bestShore_spec _ hne
  obtain ⟨S', hS'C, hS'⟩ := List.mem_map.mp hpm
  simp only [Prod.mk.injEq] at hS'
  obtain ⟨rfl, rfl⟩ := hS'
  rw [eval_twoRespecting, hb]
  simp only [Option.map_some, Option.getD_some]
  have hle : ∀ D ∈ C, G.cut S' ≤ G.cut D := fun D hD =>
    hmin (D, G.cut D) (List.mem_map.mpr ⟨D, hD, rfl⟩)
  refine ⟨?_, ?_⟩
  · rcases List.mem_append.mp hS'C with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      exact Or.inl ⟨e, mem_edgeList.mp he, rfl⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      obtain ⟨h1, h2, h3⟩ := foundPairs_valid G hp
      exact Or.inr ⟨p.1, p.2, h1, h2, h3, rfl⟩
  · have hsingle : ∀ g, g ≠ T.root → G.cut S' ≤ G.cut (T.subtree g) := fun g hg =>
      hle _ (List.mem_append_left _ (List.mem_map.mpr ⟨g, mem_edgeList.mpr hg, rfl⟩))
    rintro S (⟨e, he, rfl⟩ | ⟨e, f, he, hf, hef, rfl⟩)
    · exact hsingle e he
    · by_cases h1 : G.cut (T.subtree e) ≤ T.pairCut G e f
      · exact (hsingle e he).trans h1
      by_cases h2 : G.cut (T.subtree f) ≤ T.pairCut G e f
      · exact (hsingle f hf).trans h2
      obtain ⟨p, hp, hpe⟩ := foundPairs_cover G he hf hef (lt_of_not_ge h1) (lt_of_not_ge h2)
      exact (hle _ (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))).trans hpe

end Correct

/-! ### Query count -/

section Cost

variable {T : RootedTree V} (G : WeightedGraph V)

omit [Fintype V] [LinearOrder V] in
theorem measOut_cost (o : Finset V → ℝ) (A : Finset V) (a : ℝ) (X : Finset V) :
    (measOut A a X).cost o = 2 := by simp [measOut]

omit [Fintype V] [LinearOrder V] in
theorem measIn_cost (o : Finset V → ℝ) (A : Finset V) (a : ℝ) (X : Finset V) :
    (measIn A a X).cost o = 2 := by simp [measIn]

theorem edgeInfo_cost (o : Finset V → ℝ) (e : V) :
    (edgeInfo T e).cost o ≤ 8 * (Nat.log 2 (Fintype.card V) + 1) + 1 := by
  simp only [edgeInfo, cost_bind, cost_ask, cost_map, eval_ask]
  have h1 := majoritySearch_cost (T := T) o (measOut (T.subtree e) (o (T.subtree e)))
    (o (T.subtree e)) fun X => (measOut_cost o _ _ X).le
  have h2 := majoritySearch_cost (T := T) o (measIn (T.subtree e) (o (T.subtree e)))
    (o (T.subtree e)) fun X => (measIn_cost o _ _ X).le
  omega

theorem card_interest_le (e : V) :
    (interestOf T (infoOf T G) e).card ≤ 2 * (Nat.log 2 (Fintype.card V) + 1) := by
  unfold interestOf
  split
  · simp
  · rename_i cd _
    calc _ ≤ (T.headsAbove cd.1 ∪ T.headsAbove cd.2).card := Finset.card_erase_le
      _ ≤ (T.headsAbove cd.1).card + (T.headsAbove cd.2).card := Finset.card_union_le _ _
      _ ≤ 2 * (Nat.log 2 (Fintype.card V) + 1) := by
          have := card_headsAbove_le (T := T) cd.1
          have := card_headsAbove_le (T := T) cd.2
          omega

theorem card_lpq_eq_sum (I : V → Finset V) (P Q : V) :
    (T.lpq I P Q).card =
      ∑ e ∈ T.nonroot, if T.head e = P then (if Q ∈ I e then 1 else 0) else 0 := by
  unfold RootedTree.lpq RootedTree.pathEdges
  rw [Finset.card_filter, Finset.sum_filter]

/-- Double counting: the interested-edge lists over all pairs of heavy paths have total
size at most the total size of the interest sets. -/
theorem sum_card_lpq_le (I : V → Finset V) :
    ∑ P ∈ T.heads, ∑ Q ∈ T.heads, (T.lpq I P Q).card ≤ ∑ e ∈ T.nonroot, (I e).card := by
  simp only [card_lpq_eq_sum]
  have hswap : ∑ P ∈ T.heads, ∑ Q ∈ T.heads, ∑ e ∈ T.nonroot,
      (if T.head e = P then (if Q ∈ I e then 1 else 0) else 0) =
      ∑ e ∈ T.nonroot, ∑ P ∈ T.heads, ∑ Q ∈ T.heads,
      (if T.head e = P then (if Q ∈ I e then 1 else 0) else 0) := by
    calc _ = ∑ P ∈ T.heads, ∑ e ∈ T.nonroot, ∑ Q ∈ T.heads,
            (if T.head e = P then (if Q ∈ I e then 1 else 0) else 0) :=
          Finset.sum_congr rfl fun P _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  refine Finset.sum_le_sum fun e he => ?_
  calc ∑ P ∈ T.heads, ∑ Q ∈ T.heads,
        (if T.head e = P then (if Q ∈ I e then 1 else 0) else 0)
      = ∑ P ∈ T.heads, (if T.head e = P then ∑ Q ∈ T.heads, (if Q ∈ I e then 1 else 0) else 0) :=
        Finset.sum_congr rfl fun P _ => by split_ifs <;> simp
    _ = ∑ Q ∈ T.heads, (if Q ∈ I e then 1 else 0) := by
        rw [Finset.sum_ite_eq]
        simp [head_mem_heads (mem_nonroot.mp he)]
    _ = (T.heads.filter fun Q => Q ∈ I e).card := by rw [Finset.card_filter]
    _ ≤ (I e).card := Finset.card_le_card fun Q hQ => (Finset.mem_filter.mp hQ).2

theorem sum_headPairs_le (f : V → V → ℕ) :
    (T.headPairs.map fun pq => f pq.1 pq.2).sum ≤ ∑ P ∈ T.heads, ∑ Q ∈ T.heads, f P Q := by
  rw [RootedTree.headPairs, Finset.sum_map_toList, ← Finset.sum_product']
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem sum_card_pathEdges : ∑ P ∈ T.heads, (T.pathEdges P).card = T.nonroot.card :=
  (Finset.card_eq_sum_card_image T.head T.nonroot).symm

/-- **Query count**: `O(n log n)` cut queries with explicit constant. -/
theorem twoRespecting_cost :
    (twoRespecting T).cost G.cut ≤
      72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) := by
  set n := Fintype.card V
  set N := T.nonroot.card
  set L := Nat.log 2 n
  set C := Nat.clog 2 n
  set I := interestOf T (infoOf T G)
  have hN : N ≤ n := by have := card_nonroot (T := T); omega
  have hLC : L ≤ C := Nat.log_le_clog 2 n
  -- the interest sets
  set Y := ∑ e ∈ T.nonroot, (I e).card
  have hY : Y ≤ N * (2 * (L + 1)) := by
    have := Finset.sum_le_card_nsmul T.nonroot (fun e => (I e).card) (2 * (L + 1))
      fun e _ => card_interest_le G e
    simpa using this
  set X := ∑ P ∈ T.heads, ∑ Q ∈ T.heads, (T.lpq I P Q).card
  have hX : X ≤ Y := sum_card_lpq_le I
  have hXswap : ∑ P ∈ T.heads, ∑ Q ∈ T.heads, (T.lpq I Q P).card = X := Finset.sum_comm
  -- costs of the four stages
  have htab : (tabulate (edgeInfo T) T.edgeList).cost G.cut ≤ (8 * (L + 1) + 1) * N := by
    have := cost_tabulate_le G.cut (edgeInfo T) T.edgeList (c := 8 * (L + 1) + 1)
      fun e _ => edgeInfo_cost G.cut e
    rwa [length_edgeList] at this
  have hdiff : (mapList (fun pq => diffBlock T I pq.1 pq.2) T.headPairs).cost G.cut ≤ 21 * X := by
    rw [cost_mapList]
    calc (T.headPairs.map fun pq => (diffBlock T I pq.1 pq.2).cost G.cut).sum
        ≤ (T.headPairs.map fun pq =>
            13 * (T.lpq I pq.1 pq.2).card + 8 * (T.lpq I pq.2 pq.1).card).sum := by
          refine List.sum_le_sum fun pq hpq => ?_
          exact (diffBlock_spec G I (mem_headPairs.mp hpq).2.2).2.2.2
      _ ≤ ∑ P ∈ T.heads, ∑ Q ∈ T.heads, (13 * (T.lpq I P Q).card + 8 * (T.lpq I Q P).card) :=
          sum_headPairs_le fun P Q => 13 * (T.lpq I P Q).card + 8 * (T.lpq I Q P).card
      _ = 13 * X + 8 * X := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hXswap]; rfl
      _ = 21 * X := by ring
  have hsame : (mapList (fun P => samePath T (T.sortPre (T.pathEdges P))) T.heads.toList).cost
      G.cut ≤ 17 * C * N := by
    rw [cost_mapList, Finset.sum_map_toList]
    calc ∑ P ∈ T.heads, (samePath T (T.sortPre (T.pathEdges P))).cost G.cut
        ≤ ∑ P ∈ T.heads, 17 * C * (T.pathEdges P).card := by
          refine Finset.sum_le_sum fun P _ => ?_
          have h := (samePath_spec G _ _ le_rfl (pathEdges_chain (T := T) P)).2.2.2
          rw [length_sortPre] at h
          have hc : Nat.clog 2 (T.pathEdges P).card ≤ C :=
            Nat.clog_mono_right 2 (Finset.card_le_univ _)
          calc _ ≤ 17 * (T.pathEdges P).card * Nat.clog 2 (T.pathEdges P).card := h
            _ ≤ 17 * (T.pathEdges P).card * C := Nat.mul_le_mul_left _ hc
            _ = 17 * C * (T.pathEdges P).card := by ring
      _ = 17 * C * N := by rw [← Finset.mul_sum, sum_card_pathEdges]
  -- the number of candidates
  have hfound : (foundPairs T G).length ≤ X + N := by
    unfold foundPairs
    rw [List.length_append, List.length_flatten, List.length_flatten, List.map_map,
      List.map_map]
    have h1 : (T.headPairs.map ((List.length ∘ fun pq =>
        (diffBlock T (interestOf T (infoOf T G)) pq.1 pq.2).eval G.cut))).sum ≤ X := by
      calc _ ≤ (T.headPairs.map fun pq => (T.lpq I pq.1 pq.2).card).sum := by
            refine List.sum_le_sum fun pq hpq => ?_
            exact (diffBlock_spec G I (mem_headPairs.mp hpq).2.2).2.2.1
        _ ≤ X := sum_headPairs_le fun P Q => (T.lpq I P Q).card
    have h2 : (T.heads.toList.map ((List.length ∘ fun P =>
        (samePath T (T.sortPre (T.pathEdges P))).eval G.cut))).sum ≤ N := by
      rw [Finset.sum_map_toList]
      calc _ ≤ ∑ P ∈ T.heads, (T.pathEdges P).card := by
            refine Finset.sum_le_sum fun P _ => ?_
            have h := (samePath_spec G _ _ le_rfl (pathEdges_chain (T := T) P)).2.2.1
            rw [length_sortPre] at h
            simp only [Function.comp_apply]
            omega
        _ = N := sum_card_pathEdges
    omega
  have hcand : (candidates T (foundPairs T G)).length ≤ N + (X + N) := by
    simp only [candidates, List.length_append, List.length_map, length_edgeList]
    omega
  have hcost : (twoRespecting T).cost G.cut =
      (tabulate (edgeInfo T) T.edgeList).cost G.cut +
        ((mapList (fun pq => diffBlock T I pq.1 pq.2) T.headPairs).cost G.cut +
          ((mapList (fun P => samePath T (T.sortPre (T.pathEdges P))) T.heads.toList).cost G.cut +
            (candidates T (foundPairs T G)).length)) := by
    simp [twoRespecting, foundPairs, infoOf, I]
  -- arithmetic
  have hLN : (L + 1) * N ≤ C * N + N := by
    calc (L + 1) * N ≤ (C + 1) * N := Nat.mul_le_mul_right N (by omega)
      _ = C * N + N := by ring
  have hCN : C * N ≤ C * n := Nat.mul_le_mul_left C hN
  have hY' : Y ≤ 2 * ((L + 1) * N) := by rw [Nat.mul_comm (L + 1) N]; linarith
  have htab' : (8 * (L + 1) + 1) * N = 8 * ((L + 1) * N) + N := by ring
  have hsame' : 17 * C * N = 17 * (C * N) := by ring
  have hgoal : 72 * n * (C + 1) = 72 * (C * n) + 72 * n := by ring
  rw [hcost, hgoal]
  rw [htab'] at htab
  rw [hsame'] at hsame
  omega

end Cost

/-! ### Headline theorem -/

/-- **Theorem 13 (deterministic two-respecting cuts).** For every rooted spanning tree
`T` on `n` vertices there is one deterministic cut-query decision tree with at most
`72 n (⌈log₂ n⌉ + 1)` queries that, on every nonnegative weighted graph, returns a
shore crossing one or two edges of `T` whose cut is minimum among all such shores.
The tree edges need not be edges of the graph. -/
theorem twoRespecting_queryBound (T : RootedTree V) (hV : ∃ v, v ≠ T.root) :
    ∃ D : DTree (Finset V) ℝ (Option (Finset V))
        (72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1)),
      ∀ G : WeightedGraph V, ∃ S, D.eval G.cut = some S ∧ T.IsTwoRespShore S ∧
        ∀ S', T.IsTwoRespShore S' → G.cut S ≤ G.cut S' := by
  refine ⟨(twoRespecting T).toDTree _, fun G => ⟨_, Comp.toDTree_eval _ _ ?_, ?_⟩⟩
  · exact twoRespecting_cost G
  · exact twoRespecting_correct G hV

end TwoRespecting
end CutQueryComplexity
