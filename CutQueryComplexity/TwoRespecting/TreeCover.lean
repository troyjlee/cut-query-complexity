import CutQueryComplexity.TwoRespecting.Packing
import CutQueryComplexity.Model.Composition

/-! # Covering near-minimum cuts by few trees, and Corollary 14

Lemma 12 of the deterministic mincut paper: from an explicit graph `H` with
`λ(H) > 0`, a family of `5 (⌈log₂ n⌉ + 3)` rooted spanning trees can be chosen
offline so that every shore of `H`-weight at most `(5/4) λ(H)` crosses at most two
edges of one of the trees.

Instead of a fractional tree packing we apply `exists_light_spanning` with the
length of a pair equal to the number of still-uncovered near-minimum shores it
crosses. The resulting spanning edge set is crossed `≤ 5/2` times per shore on
average, so it crosses at least a quarter of the shores at most twice
(`exists_tree_covering_quarter`). A greedy iteration finishes the cover.

Corollary 14 (`weakSkeleton_minCut`): given an explicit weak skeleton `H` of the
hidden graph `G`, one cut-query decision tree with `O(n log² n)` queries finds a
minimum cut of `G`.
-/

namespace CutQueryComplexity
namespace TwoRespecting

open Search Search.Comp RootedTree WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The tree `T` two-respects the cut with shore `S`. -/
def Covers (T : RootedTree V) (S : Finset V) : Prop :=
  T.IsTwoRespShore S ∨ T.IsTwoRespShore Sᶜ

noncomputable instance (T : RootedTree V) : DecidablePred (Covers T) :=
  fun _ => Classical.propDecidable _

open Classical in
/-- Proper shores of `H`-weight at most `(5/4) λ(H)`. -/
noncomputable def nearMin (H : WeightedGraph V) : Finset (Finset V) :=
  Finset.univ.filter fun S => S.Nonempty ∧ S ≠ Finset.univ ∧ 4 * H.cut S ≤ 5 * mincutValue H

omit [LinearOrder V] in
theorem mem_nearMin {H : WeightedGraph V} {S : Finset V} :
    S ∈ nearMin H ↔ S.Nonempty ∧ S ≠ Finset.univ ∧ 4 * H.cut S ≤ 5 * mincutValue H := by
  classical
  simp [nearMin]

omit [LinearOrder V] in
/-- Crossing ordered pairs carry twice the cut weight. -/
theorem sum_crossesPair (H : WeightedGraph V) (S : Finset V) :
    (∑ a, ∑ b, if CrossesPair S (a, b) then H.w a b else 0) = 2 * H.cut S := by
  have h1 := H.cut_eq_sum_ite S
  have h2 := H.cut_eq_sum_ite Sᶜ
  rw [H.cut_compl] at h2
  have : (∑ a, ∑ b, if CrossesPair S (a, b) then H.w a b else 0) =
      (∑ a, ∑ b, if a ∈ S ∧ b ∉ S then H.w a b else 0) +
        ∑ a, ∑ b, if a ∈ Sᶜ ∧ b ∉ Sᶜ then H.w a b else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold CrossesPair
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]
  rw [this, ← h1, ← h2]; ring

omit [LinearOrder V] in
theorem isTwoRespShore_nonempty {T : RootedTree V} {S : Finset V} (h : T.IsTwoRespShore S) :
    S.Nonempty ∧ S ≠ Finset.univ := by
  rcases h with ⟨e, he, rfl⟩ | ⟨e, f, he, hf, hef, rfl⟩
  · exact ⟨subtree_nonempty e, subtree_ne_univ he⟩
  · refine ⟨?_, fun h => ?_⟩
    · by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty, RootedTree.pairShore, ← Finset.bot_eq_empty,
        symmDiff_eq_bot] at hne
      have h1 : f ∈ T.subtree e := hne ▸ self_mem_subtree f
      have h2 : e ∈ T.subtree f := hne ▸ self_mem_subtree e
      exact hef (isAnc_antisymm (mem_subtree.mp h1) (mem_subtree.mp h2))
    · have : T.root ∈ T.pairShore e f := h ▸ Finset.mem_univ _
      rw [RootedTree.pairShore, Finset.mem_symmDiff, mem_subtree, mem_subtree] at this
      rcases this with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact he h1.eq_root_of_isAnc_root
      · exact hf h1.eq_root_of_isAnc_root

/-! ### One step of the greedy cover -/

theorem exists_tree_covering_quarter (H : WeightedGraph V) (hlam : 0 < mincutValue H)
    [Nonempty V] (F : Finset (Finset V)) (hF : F ⊆ nearMin H) :
    ∃ T : RootedTree V, F.card ≤ 4 * (F.filter (Covers T)).card := by
  classical
  set lam := mincutValue H
  let ℓ : V → V → ℝ := fun a b => ((F.filter fun S => CrossesPair S (a, b)).card : ℝ)
  obtain ⟨E, hE, -, hbound⟩ := exists_light_spanning H hlam
    (fun S h1 h2 => mincutValue_le H ⟨h1, h2⟩) ℓ (fun _ _ => Nat.cast_nonneg _) inferInstance
  -- both sides of the bound as sums over the shores
  have hleft : ∑ e ∈ E, ℓ e.1 e.2 = ∑ S ∈ F, (crossCount E S : ℝ) := by
    simp only [ℓ, crossCount, Finset.card_filter, Nat.cast_sum]
    rw [Finset.sum_comm]
  have hright : ∑ a, ∑ b, H.w a b * ℓ a b = ∑ S ∈ F, 2 * H.cut S := by
    have e1 : ∀ a b, H.w a b * ℓ a b =
        ∑ S ∈ F, if CrossesPair S (a, b) then H.w a b else 0 := by
      intro a b
      simp only [ℓ, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs <;> simp
    simp only [e1]
    calc ∑ a, ∑ b, ∑ S ∈ F, (if CrossesPair S (a, b) then H.w a b else 0)
        = ∑ a, ∑ S ∈ F, ∑ b, (if CrossesPair S (a, b) then H.w a b else 0) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ S ∈ F, ∑ a, ∑ b, (if CrossesPair S (a, b) then H.w a b else 0) := Finset.sum_comm
      _ = ∑ S ∈ F, 2 * H.cut S := Finset.sum_congr rfl fun S _ => sum_crossesPair H S
  have hcuts : ∑ S ∈ F, 2 * H.cut S ≤ ∑ S ∈ F, (5 / 2 : ℝ) * lam :=
    Finset.sum_le_sum fun S hS => by have := (mem_nearMin.mp (hF hS)).2.2; linarith
  rw [hleft, hright] at hbound
  have htot : (∑ S ∈ F, (crossCount E S : ℝ)) ≤ (5 / 2) * F.card := by
    have h := hbound.trans hcuts
    rw [Finset.sum_const, nsmul_eq_mul] at h
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_right hlt hlam
    nlinarith
  have htotN : 2 * ∑ S ∈ F, crossCount E S ≤ 5 * F.card := by
    have : (2 * ∑ S ∈ F, crossCount E S : ℝ) ≤ 5 * F.card := by
      push_cast; linarith
    exact_mod_cast this
  -- every shore is crossed at least once
  have hpos : ∀ S ∈ F, 1 ≤ crossCount E S := by
    intro S hS
    obtain ⟨h1, h2, -⟩ := mem_nearMin.mp (hF hS)
    obtain ⟨e, he, hc⟩ := hE S h1 h2
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hc⟩⟩
  have hgb := Finset.card_filter_add_card_filter_not (s := F) (p := fun S => crossCount E S ≤ 2)
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun S => crossCount E S ≤ 2)
    (fun S => crossCount E S)
  have hg : (F.filter fun S => crossCount E S ≤ 2).card ≤
      ∑ S ∈ F.filter (fun S => crossCount E S ≤ 2), crossCount E S := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun S hS => hpos S (Finset.mem_filter.mp hS).1
  have hb : 3 * (F.filter fun S => ¬ crossCount E S ≤ 2).card ≤
      ∑ S ∈ F.filter (fun S => ¬ crossCount E S ≤ 2), crossCount E S := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_le_sum fun S hS => by have := (Finset.mem_filter.mp hS).2; omega
  -- the breadth-first tree of `E` covers every good shore
  let T := bfsTree E (Classical.arbitrary V) hE
  refine ⟨T, ?_⟩
  have hsub : F.filter (fun S => crossCount E S ≤ 2) ⊆ F.filter (Covers T) := by
    intro S hS
    rw [Finset.mem_filter] at hS ⊢
    obtain ⟨h1, h2, -⟩ := mem_nearMin.mp (hF hS.1)
    exact ⟨hS.1, isTwoRespShore_of_card_le_two h1 h2
      ((card_crossedEdges_le hE S).trans hS.2)⟩
  have := Finset.card_le_card hsub
  omega

/-! ### Few trees cover everything -/

omit [LinearOrder V] in
theorem card_covers_le (T : RootedTree V) :
    (Finset.univ.filter (Covers T)).card ≤ 2 * (Fintype.card V + Fintype.card V ^ 2) := by
  classical
  let A : Finset (Finset V) := (Finset.univ.image T.subtree) ∪
    ((Finset.univ ×ˢ Finset.univ).image fun p : V × V => T.pairShore p.1 p.2)
  have hA : A.card ≤ Fintype.card V + Fintype.card V ^ 2 := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ?_)
    refine Finset.card_image_le.trans ?_
    simp [sq]
  have hmem : ∀ S, T.IsTwoRespShore S → S ∈ A := by
    rintro S (⟨e, -, rfl⟩ | ⟨e, f, -, -, -, rfl⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(e, f), by simp, rfl⟩)
  have hsub : Finset.univ.filter (Covers T) ⊆ A ∪ A.image compl := by
    intro S hS
    rcases (Finset.mem_filter.mp hS).2 with h | h
    · exact Finset.mem_union_left _ (hmem S h)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Sᶜ, hmem _ h, compl_compl S⟩)
  calc _ ≤ (A ∪ A.image compl).card := Finset.card_le_card hsub
    _ ≤ A.card + (A.image compl).card := Finset.card_union_le _ _
    _ ≤ A.card + A.card := Nat.add_le_add_left Finset.card_image_le _
    _ ≤ 2 * (Fintype.card V + Fintype.card V ^ 2) := by omega

theorem card_nearMin_le (H : WeightedGraph V) (hlam : 0 < mincutValue H) [Nonempty V] :
    (nearMin H).card ≤ 8 * (Fintype.card V + Fintype.card V ^ 2) := by
  obtain ⟨T, hT⟩ := exists_tree_covering_quarter H hlam (nearMin H) le_rfl
  have : ((nearMin H).filter (Covers T)).card ≤ (Finset.univ.filter (Covers T)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have := card_covers_le T
  omega

/-- After `t` greedy steps at most a `(3/4)^t` fraction of the shores is uncovered. -/
theorem greedy_cover (H : WeightedGraph V) (hlam : 0 < mincutValue H) [Nonempty V]
    (F : Finset (Finset V)) (hF : F ⊆ nearMin H) : ∀ t : ℕ, ∃ L : List (RootedTree V),
      L.length = t ∧
        4 ^ t * (F.filter fun S => ∀ T ∈ L, ¬ Covers T S).card ≤ 3 ^ t * F.card
  | 0 => ⟨[], rfl, by simp⟩
  | t + 1 => by
      classical
      obtain ⟨L, hL, hrem⟩ := greedy_cover H hlam F hF t
      set R := F.filter fun S => ∀ T ∈ L, ¬ Covers T S
      obtain ⟨T, hT⟩ := exists_tree_covering_quarter H hlam R
        ((Finset.filter_subset _ _).trans hF)
      refine ⟨T :: L, by simp [hL], ?_⟩
      have heq : (F.filter fun S => ∀ T' ∈ T :: L, ¬ Covers T' S) =
          R.filter fun S => ¬ Covers T S := by
        ext S
        simp only [R, Finset.mem_filter, List.mem_cons, forall_eq_or_imp]
        tauto
      rw [heq]
      have hsplit := Finset.card_filter_add_card_filter_not (s := R) (p := Covers T)
      have h4 : 4 * (R.filter fun S => ¬ Covers T S).card ≤ 3 * R.card := by omega
      calc 4 ^ (t + 1) * (R.filter fun S => ¬ Covers T S).card
          = 4 ^ t * (4 * (R.filter fun S => ¬ Covers T S).card) := by ring
        _ ≤ 4 ^ t * (3 * R.card) := Nat.mul_le_mul_left _ h4
        _ = 3 * (4 ^ t * R.card) := by ring
        _ ≤ 3 * (3 ^ t * F.card) := Nat.mul_le_mul_left _ hrem
        _ = 3 ^ (t + 1) * F.card := by ring

/-- The number of trees used by the cover. -/
def coverSize (n : ℕ) : ℕ := 5 * (Nat.clog 2 n + 3)

/-- **Lemma 12 (deterministic tree cover).** For an explicit graph with positive
minimum cut, `5 (⌈log₂ n⌉ + 3)` rooted spanning trees two-respect every shore of weight
at most `(5/4) λ(H)`. -/
theorem exists_tree_cover (H : WeightedGraph V) (hlam : 0 < mincutValue H) [Nonempty V] :
    ∃ L : List (RootedTree V), L.length = coverSize (Fintype.card V) ∧
      ∀ S ∈ nearMin H, ∃ T ∈ L, Covers T S := by
  classical
  set n := Fintype.card V with hn
  set j := Nat.clog 2 n + 3
  obtain ⟨L, hL, hrem⟩ := greedy_cover H hlam (nearMin H) le_rfl (5 * j)
  refine ⟨L, hL, fun S hS => ?_⟩
  by_contra hnot
  push Not at hnot
  have hpos : 1 ≤ ((nearMin H).filter fun S => ∀ T ∈ L, ¬ Covers T S).card :=
    Finset.card_pos.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, hnot⟩⟩
  -- `|nearMin H| < 4^j`
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hpow : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by decide) n
  have hsize : (nearMin H).card < 4 ^ j := by
    have h1 := card_nearMin_le H hlam
    rw [← hn] at h1
    have h2 : 4 ^ j = 64 * (2 ^ Nat.clog 2 n) ^ 2 := by
      simp only [j]; rw [pow_add, show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, ← pow_mul]; ring
    have h3 : n ^ 2 ≤ (2 ^ Nat.clog 2 n) ^ 2 := Nat.pow_le_pow_left hpow 2
    have h4 : n ≤ n ^ 2 := by nlinarith
    omega
  have hmain : 4 ^ (5 * j) ≤ 3 ^ (5 * j) * (nearMin H).card := le_trans
    (Nat.le_mul_of_pos_right _ hpos) hrem
  have hlt : 3 ^ (5 * j) * (nearMin H).card < 3 ^ (5 * j) * 4 ^ j :=
    Nat.mul_lt_mul_of_pos_left hsize (by positivity)
  have hcmp : 3 ^ (5 * j) * 4 ^ j ≤ 4 ^ (5 * j) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) j
  omega

/-! ### Corollary 14 -/

/-- A weak skeleton of `G`: an explicit graph with positive minimum cut such that some
minimum cut of `G` is a near-minimum cut of the skeleton. -/
def IsWeakSkeleton (G H : WeightedGraph V) : Prop :=
  0 < mincutValue H ∧ ∃ S, IsMinCut G S ∧ 4 * H.cut S ≤ 5 * mincutValue H

open Classical in
/-- Trees covering the near-minimum cuts of `H`, chosen offline. -/
noncomputable def coverTrees (H : WeightedGraph V) : List (RootedTree V) :=
  if h : 0 < mincutValue H ∧ Nonempty V then
    have := h.2
    Classical.choose (exists_tree_cover H h.1)
  else []

theorem length_coverTrees (H : WeightedGraph V) :
    (coverTrees H).length ≤ coverSize (Fintype.card V) := by
  unfold coverTrees
  split
  · rename_i h
    have := h.2
    exact (Classical.choose_spec (exists_tree_cover H h.1)).1.le
  · simp

/-- Search every tree of the cover and keep the lightest result. -/
noncomputable def skeletonMinCut (H : WeightedGraph V) : Comp (Finset V) ℝ (Finset V) :=
  (mapList twoRespecting (coverTrees H)).bind fun outs =>
    (askList outs).map fun vals => ((bestShore (outs.zip vals)).map Prod.fst).getD ∅

theorem skeletonMinCut_correct (G H : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (hH : IsWeakSkeleton G H) : IsMinCut G ((skeletonMinCut H).eval G.cut) := by
  obtain ⟨hlam, S, hS, hSH⟩ := hH
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hspec := Classical.choose_spec (exists_tree_cover H hlam)
  have htrees : coverTrees H = Classical.choose (exists_tree_cover H hlam) := by
    unfold coverTrees
    split_ifs with h
    · rfl
    · exact absurd ⟨hlam, inferInstance⟩ h
  have hSnear : S ∈ nearMin H := mem_nearMin.mpr ⟨hS.1.1, hS.1.2, hSH⟩
  obtain ⟨T, hT, hcov⟩ := hspec.2 S hSnear
  rw [← htrees] at hT
  have hroot : ∀ T' : RootedTree V, ∃ v, v ≠ T'.root := fun T' => by
    by_contra h
    push Not at h
    have : Finset.univ ⊆ {T'.root} := fun x _ => Finset.mem_singleton.mpr (h x)
    have := Finset.card_le_card this
    simp at this; omega
  set outs := (coverTrees H).map fun T' => (twoRespecting T').eval G.cut
  have hO : (twoRespecting T).eval G.cut ∈ outs := List.mem_map.mpr ⟨T, hT, rfl⟩
  have hne : outs.map (fun C => (C, G.cut C)) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; rw [h] at hO; simp at hO
  obtain ⟨⟨X, x⟩, hpm, hb, hmin⟩ := bestShore_spec _ hne
  obtain ⟨X', hX'C, hX'⟩ := List.mem_map.mp hpm
  simp only [Prod.mk.injEq] at hX'
  obtain ⟨rfl, rfl⟩ := hX'
  have heval : (skeletonMinCut H).eval G.cut = X' := by
    simp only [skeletonMinCut, eval_bind, eval_map, eval_askList, eval_mapList]
    rw [zip_map_self, hb]
    rfl
  rw [heval]
  -- the chosen output is a two-respecting shore of some cover tree
  obtain ⟨T', hT', rfl⟩ := List.mem_map.mp hX'C
  obtain ⟨hvalid, -⟩ := twoRespecting_correct G (hroot T')
  refine ⟨isTwoRespShore_nonempty hvalid, fun Y hY => ?_⟩
  -- it is no heavier than the output for `T`, which is no heavier than `S`
  have h1 : G.cut ((twoRespecting T').eval G.cut) ≤ G.cut ((twoRespecting T).eval G.cut) :=
    hmin _ (List.mem_map.mpr ⟨_, hO, rfl⟩)
  have h2 : G.cut ((twoRespecting T).eval G.cut) ≤ G.cut S := by
    obtain ⟨-, hopt⟩ := twoRespecting_correct G (hroot T)
    rcases hcov with h | h
    · exact hopt S h
    · rw [← G.cut_compl S]; exact hopt _ h
  exact h1.trans (h2.trans (hS.2 Y hY))

theorem skeletonMinCut_cost (G H : WeightedGraph V) :
    (skeletonMinCut H).cost G.cut ≤ coverSize (Fintype.card V) *
      (72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) + 1) := by
  simp only [skeletonMinCut, cost_bind, cost_map, cost_askList, eval_mapList, List.length_map]
  have h1 := cost_mapList_le G.cut twoRespecting (coverTrees H)
    (c := 72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1))
    fun T _ => twoRespecting_cost G
  have h2 := length_coverTrees H
  have h3 := Nat.mul_le_mul_left (72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1)) h2
  rw [Nat.mul_add, Nat.mul_one]
  rw [Nat.mul_comm (coverSize _)] at *
  omega

/-- **Corollary 14.** For every explicit graph `H` there is one cut-query decision tree
with `O(n log² n)` queries that returns a minimum cut of every graph `G` of which `H` is
a weak skeleton. -/
theorem weakSkeleton_minCut (H : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    ∃ D : DTree (Finset V) ℝ (Option (Finset V)) (coverSize (Fintype.card V) *
        (72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) + 1)),
      ∀ G : WeightedGraph V, IsWeakSkeleton G H →
        ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  ⟨(skeletonMinCut H).toDTree _, fun G hG =>
    ⟨_, Comp.toDTree_eval _ _ (skeletonMinCut_cost G H), skeletonMinCut_correct G H hn hG⟩⟩

/-- **Corollary 14, composed.** A deterministic weak-skeleton construction with budget
`q` yields a deterministic minimum-cut algorithm with `q + O(n log² n)` queries. -/
theorem minCut_of_weakSkeleton {q : ℕ} (hn : 2 ≤ Fintype.card V)
    (Sk : DTree (Finset V) ℝ (WeightedGraph V) q)
    (hSk : ∀ G : WeightedGraph V, IsWeakSkeleton G (Sk.eval G.cut)) :
    ∃ D : DTree (Finset V) ℝ (Option (Finset V)) (q + coverSize (Fintype.card V) *
        (72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) + 1)),
      ∀ G : WeightedGraph V, ∃ S, D.eval G.cut = some S ∧ IsMinCut G S := by
  refine ⟨Sk.bind fun H => (skeletonMinCut H).toDTree _, fun G =>
    ⟨_, ?_, skeletonMinCut_correct G (Sk.eval G.cut) hn (hSk G)⟩⟩
  rw [DTree.eval, DTree.run_bind]
  exact Comp.toDTree_eval G.cut (skeletonMinCut (Sk.eval G.cut)) (skeletonMinCut_cost G _)

end TwoRespecting
end CutQueryComplexity
