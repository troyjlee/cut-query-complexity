import CutQueryComplexity.Primitive.DirectedReductions
import Mathlib.Data.Nat.Log

/-! # Ordered first-neighbor search (D1; source `lem:search`)

Fix a vertex `v` and a public candidate list `L` (duplicate-free, not containing `v`). Its order
may come from public weights, unique pair IDs, or transcript data; ties are therefore already
broken by the list. `firstNbr v k L` returns the first `u ∈ L` with `sym v u > 0` together with
its multiplicity, or `none` when no candidate is an actual neighbor (`firstNbr_correct`). The
specification is `firstPos (G.sym v) L`.

The retained-interval invariant (`searchFrom_correct`): the retained list `R` is a contiguous
piece of `L`, its known count `a = Σ_{u∈R} sym v u` is positive, and every candidate of `L`
before `R` has multiplicity zero. Testing the left half keeps it when its count is positive and
otherwise keeps the right half, whose count is still `a`. A singleton's count is its
multiplicity, so no extra query is needed. Empty and all-absent lists are covered by the
initial test.

Budget: `3 + 3k` queries for `|L| ≤ 2^k`; `firstNbr_correct_clog` uses
`k = ⌈log₂ |V|⌉`. `firstNbrFilter` applies a public support predicate first.
-/

namespace CutQueryComplexity

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The first candidate with positive value, with that value. -/
def firstPos (p : V → ℕ) (L : List V) : Option (V × ℕ) :=
  (L.find? fun u => decide (0 < p u)).map fun u => (u, p u)

omit [Fintype V] [DecidableEq V] in
theorem firstPos_append_of_exists (p : V → ℕ) {l r : List V} (h : ∃ u ∈ l, 0 < p u) :
    firstPos p (l ++ r) = firstPos p l := by
  unfold firstPos
  rw [List.find?_append]
  obtain ⟨u, hu, hp⟩ := h
  obtain ⟨w, hw⟩ : ∃ w, l.find? (fun u => decide (0 < p u)) = some w := by
    cases hf : l.find? (fun u => decide (0 < p u)) with
    | none =>
        rw [List.find?_eq_none] at hf
        exact absurd (decide_eq_true hp) (hf u hu)
    | some w => exact ⟨w, rfl⟩
  rw [hw]; rfl

omit [Fintype V] [DecidableEq V] in
theorem firstPos_append_of_forall (p : V → ℕ) {l r : List V} (h : ∀ u ∈ l, p u = 0) :
    firstPos p (l ++ r) = firstPos p r := by
  unfold firstPos
  rw [List.find?_append]
  have : l.find? (fun u => decide (0 < p u)) = none := by
    rw [List.find?_eq_none]; intro u hu; simp [h u hu]
  rw [this]; rfl

omit [Fintype V] [DecidableEq V] in
theorem firstPos_eq_none (p : V → ℕ) {L : List V} (h : ∀ u ∈ L, p u = 0) :
    firstPos p L = none := by
  have := firstPos_append_of_forall p (r := []) h
  rw [List.append_nil] at this
  rw [this]; rfl

/-- The retained-interval search, with retained list `R` of known count `a`. -/
def searchFrom (v : V) : (k : ℕ) → List V → ℕ → DTree (Finset V) ℕ (Option (V × ℕ)) (3 * k)
  | 0, R, a => DTree.pure (R.head?.map fun u => (u, a))
  | k + 1, R, a => ((nbrCount v (R.take (2 ^ k)).toFinset).bind fun b =>
      if 0 < b then searchFrom v k (R.take (2 ^ k)) b
      else searchFrom v k (R.drop (2 ^ k)) a).cast (by ring)

omit [Fintype V] in
theorem sum_toFinset_eq (p : V → ℕ) {R : List V} (h : R.Nodup) :
    ∑ u ∈ R.toFinset, p u = (R.map p).sum := List.sum_toFinset p h

omit [Fintype V] [DecidableEq V] in
theorem exists_pos_of_sum_pos (p : V → ℕ) {R : List V} (h : 0 < (R.map p).sum) :
    ∃ u ∈ R, 0 < p u := by
  by_contra hne
  push Not at hne
  have : (R.map p).sum = 0 := List.sum_eq_zero fun x hx => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact Nat.le_zero.mp (hne u hu)
  omega

/-- **The retained-interval invariant.** -/
theorem searchFrom_correct (G : DiGraph V) (v : V) (k : ℕ) {R : List V} (hR : R.Nodup)
    (hv : v ∉ R) (hlen : R.length ≤ 2 ^ k) {a : ℕ} (ha : a = (R.map (G.sym v)).sum)
    (hpos : 0 < a) : (searchFrom v k R a).eval G.out = firstPos (G.sym v) R := by
  induction k generalizing R a with
  | zero =>
      simp only [searchFrom, DTree.eval_pure]
      match R, hlen, hR with
      | [], _, _ => simp at ha; omega
      | [u], _, _ =>
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at ha
          subst ha
          simp [firstPos, hpos]
      | _ :: _ :: _, h, _ => simp at h
  | succ k ih =>
      set l := R.take (2 ^ k)
      set r := R.drop (2 ^ k)
      have hlr : l ++ r = R := List.take_append_drop _ _
      have hl : l.Nodup := hR.sublist (List.take_sublist _ _)
      have hr : r.Nodup := hR.sublist (List.drop_sublist _ _)
      have hvl : v ∉ l := fun h => hv (List.mem_of_mem_take h)
      have hvr : v ∉ r := fun h => hv (List.mem_of_mem_drop h)
      have hll : l.length ≤ 2 ^ k := by simp [l]
      have hrl : r.length ≤ 2 ^ k := by
        simp only [r, List.length_drop]; rw [pow_succ] at hlen; omega
      have hb : (nbrCount v (R.take (2 ^ k)).toFinset).eval G.out = (l.map (G.sym v)).sum := by
        rw [nbrCount_eval G (by simpa using hvl), sum_toFinset_eq _ hl]
      have hsum : a = (l.map (G.sym v)).sum + (r.map (G.sym v)).sum := by
        rw [ha, ← hlr, List.map_append, List.sum_append]
      simp only [searchFrom, DTree.eval_cast, DTree.eval_bind]
      rw [hb]
      split_ifs with hpl
      · rw [ih hl hvl hll rfl hpl, ← hlr,
          firstPos_append_of_exists _ (exists_pos_of_sum_pos _ hpl)]
      · have hzero : (l.map (G.sym v)).sum = 0 := by omega
        have hall : ∀ u ∈ l, G.sym v u = 0 := fun u hu =>
          (List.sum_eq_zero_iff.mp hzero) _ (List.mem_map_of_mem hu)
        rw [ih hr hvr hrl (by omega) hpos, ← hlr, firstPos_append_of_forall _ hall]

/-- **Ordered first-neighbor search.** `3 + 3k` queries for `|L| ≤ 2^k`. -/
def firstNbr (v : V) (k : ℕ) (L : List V) : DTree (Finset V) ℕ (Option (V × ℕ)) (3 + 3 * k) :=
  (nbrCount v L.toFinset).bind fun a =>
    if 0 < a then searchFrom v k L a else DTree.pure none

theorem firstNbr_correct (G : DiGraph V) (v : V) (k : ℕ) {L : List V} (hL : L.Nodup)
    (hv : v ∉ L) (hlen : L.length ≤ 2 ^ k) :
    (firstNbr v k L).eval G.out = firstPos (G.sym v) L := by
  have ha : (nbrCount v L.toFinset).eval G.out = (L.map (G.sym v)).sum := by
    rw [nbrCount_eval G (by simpa using hv), sum_toFinset_eq _ hL]
  simp only [firstNbr, DTree.eval_bind, ha]
  split_ifs with hpos
  · exact searchFrom_correct G v k hL hv hlen rfl hpos
  · rw [DTree.eval_pure, firstPos_eq_none]
    intro u hu
    have hzero : (L.map (G.sym v)).sum = 0 := by omega
    exact (List.sum_eq_zero_iff.mp hzero) _ (List.mem_map_of_mem hu)

/-- The public budget `3 + 3 ⌈log₂ |V|⌉` suffices for every duplicate-free candidate list. -/
theorem firstNbr_correct_clog (G : DiGraph V) (v : V) {L : List V} (hL : L.Nodup)
    (hv : v ∉ L) :
    (firstNbr v (Nat.clog 2 (Fintype.card V)) L).eval G.out = firstPos (G.sym v) L := by
  refine firstNbr_correct G v _ hL hv ?_
  calc L.length = L.toFinset.card := (List.toFinset_card_of_nodup hL).symm
    _ ≤ Fintype.card V := card_le_univ _
    _ ≤ 2 ^ Nat.clog 2 (Fintype.card V) := Nat.le_pow_clog (by norm_num) _

/-- The search restricted by a public support predicate. -/
def firstNbrFilter (v : V) (k : ℕ) (P : V → Bool) (L : List V) :
    DTree (Finset V) ℕ (Option (V × ℕ)) (3 + 3 * k) :=
  firstNbr v k (L.filter P)

theorem firstNbrFilter_correct (G : DiGraph V) (v : V) (k : ℕ) (P : V → Bool) {L : List V}
    (hL : L.Nodup) (hv : v ∉ L) (hlen : L.length ≤ 2 ^ k) :
    (firstNbrFilter v k P L).eval G.out = firstPos (G.sym v) (L.filter P) :=
  firstNbr_correct G v k (hL.filter P) (fun h => hv (List.mem_of_mem_filter h))
    ((List.length_filter_le P L).trans hlen)

end CutQueryComplexity
