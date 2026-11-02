import CutQueryComplexity.Primitive.DirectedReductions
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Dyadic row aggregates (D1; source `lem:aggregate`)

A public signed-digit formula on a common list of bit positions `pos` is

  `q(v, u) = Σ_{b ∈ pos} ([plus b v u] − [minus b v u]) 2^b`  (`DyadicFormula.val`).

For each vertex, bit position, and sign, the public set of candidate endpoints with that digit
is counted by one `nbrCount` (three queries). Summing the counts with their signed powers of two
recovers the row aggregate `y_v = Σ_{u ≠ v, allowed} sym v u · q(v, u)` exactly
(`rowAgg_correct`), in `6 |pos|` queries. All rows cost `6 |pos| |V|` (`allRows_correct`). The
scalar `Σ_{u < v} sym u v · q(u, v)` restricts row `u` to endpoints `v > u`, so canonical pairs are
counted once (`pairAgg_correct`).

`intFormula` writes an integer-valued formula `s(v,u) · 2^e` with `|s| < 2^B` in sign and
magnitude on the positions `e, …, e + B − 1` (`intFormula_val`).

Only outgoing-cut answers are used; no reweighted cut oracle is assumed.
-/

namespace CutQueryComplexity

open Finset

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A public signed-digit dyadic formula on a list of bit positions. -/
structure DyadicFormula (V : Type) where
  pos : List ℤ
  plus : ℤ → V → V → Bool
  minus : ℤ → V → V → Bool

namespace DyadicFormula

variable (q : DyadicFormula V)

/-- The signed digit at position `b`. -/
def digit (b : ℤ) (v u : V) : ℝ := (if q.plus b v u then 1 else 0) - (if q.minus b v u then 1 else 0)

/-- The value on a list of positions. -/
def valOn (bs : List ℤ) (v u : V) : ℝ := (bs.map fun b => q.digit b v u * (2 : ℝ) ^ b).sum

/-- The formula's value. -/
def val (v u : V) : ℝ := q.valOn q.pos v u

omit [Fintype V] [DecidableEq V] in
@[simp] theorem valOn_nil (v u : V) : q.valOn [] v u = 0 := rfl

omit [Fintype V] [DecidableEq V] in
theorem valOn_cons (b : ℤ) (bs : List ℤ) (v u : V) :
    q.valOn (b :: bs) v u = q.digit b v u * (2 : ℝ) ^ b + q.valOn bs v u := by
  simp [valOn]

end DyadicFormula

/-- The candidate endpoints of row `v`. -/
def rowCand (allow : V → V → Bool) (v : V) : Finset V :=
  univ.filter fun u => u ≠ v ∧ allow v u = true

theorem not_mem_rowCand (allow : V → V → Bool) (v : V) : v ∉ rowCand allow v := by
  simp [rowCand]

/-- One row aggregate: two neighbor counts per bit position. -/
def rowAgg (q : DyadicFormula V) (allow : V → V → Bool) (v : V) :
    (bs : List ℤ) → DTree (Finset V) ℕ ℝ (6 * bs.length)
  | [] => DTree.pure 0
  | b :: bs =>
      ((nbrCount v ((rowCand allow v).filter fun u => q.plus b v u = true)).bind fun a =>
        (nbrCount v ((rowCand allow v).filter fun u => q.minus b v u = true)).bind fun c =>
          (rowAgg q allow v bs).map fun s => ((a : ℝ) - c) * (2 : ℝ) ^ b + s).cast
        (by simp only [List.length_cons]; ring)

/-- **One row.** `y_v = Σ_{u ≠ v, allowed} sym v u · q(v, u)`, in `6 |bs|` queries. -/
theorem rowAgg_correct (G : DiGraph V) (q : DyadicFormula V) (allow : V → V → Bool) (v : V)
    (bs : List ℤ) :
    (rowAgg q allow v bs).eval G.out =
      ∑ u ∈ rowCand allow v, (G.sym v u : ℝ) * q.valOn bs v u := by
  induction bs with
  | nil => simp [rowAgg]
  | cons b bs ih =>
      have hv : ∀ P : V → Prop, [DecidablePred P] → v ∉ (rowCand allow v).filter P :=
        fun P _ h => not_mem_rowCand allow v (mem_filter.mp h).1
      simp only [rowAgg, DTree.eval_cast, DTree.eval_bind, DTree.eval_map, ih,
        nbrCount_eval G (hv _)]
      simp only [q.valOn_cons, mul_add, sum_add_distrib]
      congr 1
      simp only [DyadicFormula.digit, Nat.cast_sum, sum_filter, ← sum_sub_distrib, sum_mul]
      refine sum_congr rfl fun u _ => ?_
      split_ifs <;> push_cast <;> ring

/-- All row aggregates over a list of vertices. -/
def allRows (q : DyadicFormula V) (allow : V → V → Bool) :
    (vs : List V) → DTree (Finset V) ℕ (V → ℝ) (6 * q.pos.length * vs.length)
  | [] => DTree.pure 0
  | v :: vs => ((rowAgg q allow v q.pos).bind fun y =>
      (allRows q allow vs).map fun f => Function.update f v y).cast
        (by simp only [List.length_cons]; ring)

theorem allRows_correct (G : DiGraph V) (q : DyadicFormula V) (allow : V → V → Bool)
    (vs : List V) {w : V} (hw : w ∈ vs) :
    (allRows q allow vs).eval G.out w =
      ∑ u ∈ rowCand allow w, (G.sym w u : ℝ) * q.val w u := by
  induction vs with
  | nil => simp at hw
  | cons v vs ih =>
      simp only [allRows, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      by_cases hwv : w = v
      · subst hwv; rw [Function.update_self, rowAgg_correct]; rfl
      · rw [Function.update_of_ne hwv]
        exact ih ((List.mem_cons.mp hw).resolve_left hwv)

/-- **All rows**, in `6 |pos| |V|` queries. -/
def allRowsUniv (q : DyadicFormula V) (allow : V → V → Bool) :
    DTree (Finset V) ℕ (V → ℝ) (6 * q.pos.length * Fintype.card V) :=
  (allRows q allow (univ : Finset V).toList).cast (by rw [length_toList, card_univ])

theorem allRowsUniv_correct (G : DiGraph V) (q : DyadicFormula V) (allow : V → V → Bool)
    (w : V) : (allRowsUniv q allow).eval G.out w =
      ∑ u ∈ rowCand allow w, (G.sym w u : ℝ) * q.val w u := by
  rw [allRowsUniv, DTree.eval_cast]
  exact allRows_correct G q allow _ (mem_toList.mpr (mem_univ w))

/-- **Scalar aggregate** over canonical pairs `u < v`, in `6 |pos| |V|` queries. -/
def pairAgg [LinearOrder V] (q : DyadicFormula V) :
    DTree (Finset V) ℕ ℝ (6 * q.pos.length * Fintype.card V) :=
  (allRowsUniv q fun u v => decide (u < v)).map fun f => ∑ u, f u

theorem pairAgg_correct [LinearOrder V] (G : DiGraph V) (q : DyadicFormula V) :
    (pairAgg q).eval G.out =
      ∑ u, ∑ v ∈ univ.filter (u < ·), (G.sym u v : ℝ) * q.val u v := by
  simp only [pairAgg, DTree.eval_map, allRowsUniv_correct]
  refine sum_congr rfl fun u _ => sum_congr ?_ fun _ _ => rfl
  ext v; simp only [rowCand, mem_filter, mem_univ, true_and, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩

/-! ## Integer formulas in sign and magnitude -/

/-- The binary expansion of a natural number below `2^B`. -/
theorem nat_eq_sum_testBit : ∀ (B n : ℕ), n < 2 ^ B →
    (n : ℝ) = ∑ b ∈ range B, if n.testBit b then (2 : ℝ) ^ b else 0
  | 0, n, h => by simp at h; simp [h]
  | B + 1, n, h => by
      rw [sum_range_succ']
      have hn2 : n / 2 < 2 ^ B := by rw [pow_succ] at h; omega
      have ih := nat_eq_sum_testBit B (n / 2) hn2
      have hsplit : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) := by
        have := Nat.div_add_mod n 2; exact_mod_cast this.symm
      have hbit : ∀ b, n.testBit (b + 1) = (n / 2).testBit b := fun b => by
        rw [Nat.testBit_succ]
      have h0 : (if n.testBit 0 then (2 : ℝ) ^ 0 else 0) = ((n % 2 : ℕ) : ℝ) := by
        rw [Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
      simp only [hbit, pow_succ]
      rw [h0, hsplit, ih, mul_sum]
      congr 1
      refine sum_congr rfl fun b _ => ?_
      split_ifs <;> ring

theorem list_sum_map_range (f : ℕ → ℝ) (B : ℕ) :
    ((List.range B).map f).sum = ∑ j ∈ range B, f j := by
  induction B with
  | zero => simp
  | succ B ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The sign-and-magnitude formula of `s(v, u) · 2^e` on positions `e, …, e + B − 1`. -/
def intFormula (s : V → V → ℤ) (e : ℤ) (B : ℕ) : DyadicFormula V where
  pos := (List.range B).map fun j : ℕ => e + (j : ℤ)
  plus b v u := decide (0 < s v u) && (s v u).natAbs.testBit (b - e).toNat
  minus b v u := decide (s v u < 0) && (s v u).natAbs.testBit (b - e).toNat

omit [Fintype V] [DecidableEq V] in
theorem intFormula_val (s : V → V → ℤ) (e : ℤ) (B : ℕ) {v u : V}
    (hs : (s v u).natAbs < 2 ^ B) :
    (intFormula s e B).val v u = (s v u : ℝ) * (2 : ℝ) ^ e := by
  set n := (s v u).natAbs
  have hexp := nat_eq_sum_testBit B n hs
  have hval : (intFormula s e B).val v u =
      ∑ j ∈ range B, (intFormula s e B).digit (e + j) v u * (2 : ℝ) ^ (e + (j : ℤ)) := by
    simp only [DyadicFormula.val, DyadicFormula.valOn, intFormula, List.map_map]
    exact list_sum_map_range _ B
  have hpow : ∀ j : ℕ, (2 : ℝ) ^ (e + (j : ℤ)) = (2 : ℝ) ^ e * 2 ^ j := fun j => by
    rw [zpow_add₀ two_ne_zero, zpow_natCast]
  rw [hval]
  simp only [DyadicFormula.digit, intFormula, add_sub_cancel_left, Int.toNat_natCast, hpow]
  rcases lt_trichotomy (s v u) 0 with hneg | hzero | hpos
  · have hsn : (s v u : ℝ) = -(n : ℝ) := by
      have : s v u = -(n : ℤ) := by omega
      rw [this]; push_cast; ring
    rw [hsn, hexp, neg_mul, sum_mul, ← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    have h1 : ¬ (0 < s v u) := not_lt.mpr hneg.le
    by_cases ht : (s v u).natAbs.testBit j = true <;> simp [n, ht, hneg, h1]
    ring
  · simp [hzero]
  · have hsn : (s v u : ℝ) = (n : ℝ) := by
      have : s v u = (n : ℤ) := by omega
      rw [this]; push_cast; ring
    rw [hsn, hexp, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    have h1 : ¬ (s v u < 0) := not_lt.mpr hpos.le
    by_cases ht : (s v u).natAbs.testBit j = true <;> simp [n, ht, hpos, h1]
    ring

end

end CutQueryComplexity
