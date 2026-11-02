import CutQueryComplexity.DirectedUnitST.Acceleration.Quantization
import CutQueryComplexity.DirectedUnitST.Acceleration.Lyapunov
import CutQueryComplexity.Primitive.DyadicAggregate
import CutQueryComplexity.DirectedUnitST.SparseBand.Basic
import CutQueryComplexity.DirectedMincut.SmallShore
import Mathlib.Logic.Function.Iterate

/-! # Rational cut-realized gradients

This is a rational-valued implementation of the existing exact dyadic star
aggregate.  Its correctness is proved against `rowAgg`, so the analytic model
never assumes a weighted-query oracle.  Public iterates remain rational.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Acceleration

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

def rationalRow (q : DyadicFormula V) (allow : V → V → Bool) (v : V) :
    (bs : List ℤ) → DTree (Finset V) ℕ ℚ (6 * bs.length)
  | [] => DTree.pure 0
  | b :: bs =>
      ((nbrCount v ((rowCand allow v).filter fun u => q.plus b v u = true)).bind fun a =>
        (nbrCount v ((rowCand allow v).filter fun u => q.minus b v u = true)).bind fun c =>
          (rationalRow q allow v bs).map fun s => ((a : ℚ) - c) * (2 : ℚ) ^ b + s).cast
        (by simp only [List.length_cons]; ring)

theorem rationalRow_cast (G : DiGraph V) (q : DyadicFormula V) (allow : V → V → Bool)
    (v : V) (bs : List ℤ) :
    ((rationalRow q allow v bs).eval G.out : ℝ) = (rowAgg q allow v bs).eval G.out := by
  induction bs with
  | nil => simp [rationalRow, rowAgg, DTree.eval_pure]
  | cons b bs ih =>
      simp [rationalRow, rowAgg, DTree.eval_cast, DTree.eval_bind, DTree.eval_map, ih]

def rationalRows (q : DyadicFormula V) (allow : V → V → Bool) :
    (vs : List V) → DTree (Finset V) ℕ (V → ℚ) (6 * q.pos.length * vs.length)
  | [] => DTree.pure 0
  | v :: vs => ((rationalRow q allow v q.pos).bind fun y =>
      (rationalRows q allow vs).map fun f => Function.update f v y).cast
        (by simp only [List.length_cons]; ring)

theorem rationalRows_correct (G : DiGraph V) (q : DyadicFormula V) (allow : V → V → Bool)
    (vs : List V) {w : V} (hw : w ∈ vs) :
    ((rationalRows q allow vs).eval G.out w : ℝ) =
      ∑ u ∈ rowCand allow w, (G.sym w u : ℝ) * q.val w u := by
  induction vs with
  | nil => simp at hw
  | cons v vs ih =>
      simp only [rationalRows, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
      by_cases hwv : w = v
      · subst w
        rw [Function.update_self, rationalRow_cast, rowAgg_correct]
        rfl
      · rw [Function.update_of_ne hwv]
        exact ih ((List.mem_cons.mp hw).resolve_left hwv)

noncomputable def rationalRowsUniv (q : DyadicFormula V) (allow : V → V → Bool) :
    DTree (Finset V) ℕ (V → ℚ) (6 * q.pos.length * Fintype.card V) :=
  (rationalRows q allow (univ : Finset V).toList).cast (by rw [length_toList, card_univ])

theorem rationalRowsUniv_correct (G : DiGraph V) (q : DyadicFormula V) (allow : V → V → Bool)
    (w : V) : ((rationalRowsUniv q allow).eval G.out w : ℝ) =
      ∑ u ∈ rowCand allow w, (G.sym w u : ℝ) * q.val w u := by
  rw [rationalRowsUniv, DTree.eval_cast]
  exact rationalRows_correct G q allow _ (mem_toList.mpr (mem_univ w))

/-- `Q = 2^b`; one extra bit represents both saturated endpoints exactly. -/
noncomputable def gradientProg (b : ℕ) (s : V → V → ℤ) (beta r : V → ℚ) :
    DTree (Finset V) ℕ (V → ℚ) (6 * (b + 1) * Fintype.card V) :=
  ((rationalRowsUniv (intFormula s (-(b : ℤ)) (b + 1)) fun _ _ => true).map
    fun y i => y i - beta i + r i).cast (by simp [intFormula])

/-- The measured gradient, with the exact public worst-case query budget. -/
theorem gradientProg_correct (G : DiGraph V) (b : ℕ) (s : V → V → ℤ) (beta r : V → ℚ)
    (hs : ∀ i j, (s i j).natAbs ≤ 2 ^ b) (i : V) :
    ((gradientProg b s beta r).eval G.out i : ℝ) =
      (∑ j, (G.sym i j : ℝ) * ((s i j : ℝ) * (2 : ℝ) ^ (-(b : ℤ)))) - beta i + r i := by
  have hbits : ∀ j, (s i j).natAbs < 2 ^ (b + 1) := by
    intro j
    have hpow : 2 ^ b < 2 ^ (b + 1) := by
      rw [pow_succ]
      have : 0 < 2 ^ b := by positivity
      omega
    exact lt_of_le_of_lt (hs i j) hpow
  simp only [gradientProg, DTree.eval_cast, DTree.eval_map, Rat.cast_add, Rat.cast_sub]
  rw [rationalRowsUniv_correct]
  congr 2
  simp only [rowCand, sum_filter, and_true]
  apply sum_congr rfl
  intro j _
  by_cases hij : j = i
  · subst j
    simp
  · simp [hij, intFormula_val s (-(b : ℤ)) (b + 1) (hbits j)]

theorem sum_canonical_dite {n : ℕ} (f : {ij : Fin n × Fin n // ij.1 < ij.2} → ℝ) :
    (∑ e, f e) = ∑ i, ∑ j, if h : i < j then f ⟨(i, j), h⟩ else 0 := by
  have h := sum_canonical (fun ij : Fin n × Fin n => if h : ij.1 < ij.2 then f ⟨ij, h⟩ else 0)
  calc
    (∑ e, f e) = ∑ e : SparseBand.Pair n,
        if h : e.val.1 < e.val.2 then f ⟨e.val, h⟩ else 0 := by
      apply sum_congr rfl
      intro e _
      simp only [dite_eq_left e.property]
    _ = _ := h
    _ = _ := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases hij : i < j <;> simp [hij]

/-- Pair-incidence divergence is the skew-symmetric row formula measured by stars. -/
theorem canonical_divergence_row {n : ℕ}
    (w : {ij : Fin n × Fin n // ij.1 < ij.2} → ℝ) (i : Fin n) :
    divergence (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2) w i =
      ∑ j, if hij : i < j then w ⟨(i, j), hij⟩ else
        if hji : j < i then -w ⟨(j, i), hji⟩ else 0 := by
  let upper : Fin n → Fin n → ℝ := fun a b => if h : a < b then w ⟨(a, b), h⟩ else 0
  have he : divergence (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2) w i =
      (∑ a, ∑ b, ((if a = i then upper a b else 0) - (if b = i then upper a b else 0))) := by
    rw [divergence, sum_canonical_dite]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    by_cases hab : a < b <;> simp [upper, hab]
  have ht : (∑ a, ∑ b, if a = i then upper a b else 0) = ∑ b, upper i b := by
    simp [sum_ite_irrel]
  have hh : (∑ a, ∑ b, if b = i then upper a b else 0) = ∑ a, upper a i := by simp
  simp only [sum_sub_distrib] at he
  rw [ht, hh, ← sum_sub_distrib] at he
  rw [he]
  apply sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [upper, hij, not_lt.mpr (le_of_lt hij)]
  · subst j
    simp [upper]
  · simp [upper, hij, not_lt.mpr (le_of_lt hij)]

/-- The exact measurement equals the canonical-pair incidence formula used in the potential. -/
theorem canonical_gradientProg_correct {n : ℕ} (G : DiGraph (Fin n)) (b : ℕ)
    (h : {ij : Fin n × Fin n // ij.1 < ij.2} → ℤ) (beta r : Fin n → ℚ)
    (hh : ∀ e, -((2 ^ b : ℕ) : ℤ) ≤ h e ∧ h e ≤ ((2 ^ b : ℕ) : ℤ)) (i : Fin n) :
    ((gradientProg b (signedPairs h) beta r).eval G.out i : ℝ) =
      divergence (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2)
        (fun e => (G.sym e.val.1 e.val.2 : ℝ) * ((h e : ℝ) * (2 : ℝ) ^ (-(b : ℤ)))) i -
          beta i + r i := by
  rw [gradientProg_correct G b (signedPairs h) beta r (signedPairs_abs_bound h hh),
    canonical_divergence_row]
  congr 2
  apply sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [signedPairs, hij]
  · subst j
    simp
  · simp [signedPairs, hij, not_lt.mpr (le_of_lt hij), G.sym_comm i j]

omit [DecidableEq V] in
theorem skew_sum_zero (w : V → V → ℝ) (hw : ∀ i j, w j i = -w i j) :
    ∑ i, ∑ j, w i j = 0 := by
  have h : (∑ i, ∑ j, w i j) = -(∑ i, ∑ j, w i j) := by
    calc
      (∑ i, ∑ j, w i j) = ∑ i, ∑ j, w j i := sum_comm
      _ = ∑ i, ∑ j, -w i j :=
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => hw i j
      _ = _ := by simp only [sum_neg_distrib]
  linarith

/-- The rational query result has exactly zero mean on a zero-mean iterate. -/
theorem gradientProg_sum_zero (G : DiGraph V) (b : ℕ) (s : V → V → ℤ) (beta r : V → ℚ)
    (hs : ∀ i j, (s i j).natAbs ≤ 2 ^ b) (hskew : ∀ i j, s j i = -s i j)
    (hbeta : ∑ i, beta i = 0) (hr : ∑ i, r i = 0) :
    ∑ i, (gradientProg b s beta r).eval G.out i = 0 := by
  have hb : ∑ i, (beta i : ℝ) = 0 := by exact_mod_cast hbeta
  have hr' : ∑ i, (r i : ℝ) = 0 := by exact_mod_cast hr
  have hd := skew_sum_zero (fun i j => (G.sym i j : ℝ) *
    ((s i j : ℝ) * (2 : ℝ) ^ (-(b : ℤ)))) (by
      intro i j
      rw [G.sym_comm j i, hskew]
      push_cast
      ring)
  have hzero : ∑ i, ((gradientProg b s beta r).eval G.out i : ℝ) = 0 := by
    simp_rw [gradientProg_correct G b s beta r hs]
    rw [sum_add_distrib, sum_sub_distrib, hd, hb, hr']
    ring
  exact_mod_cast hzero

/-- Rational arithmetic for both accelerated updates, with no access to an optimum. -/
def rationalStep (a : ℚ) (x z g : V → ℚ) : (V → ℚ) × (V → ℚ) :=
  let v := fun i => (x i + a * z i) / (1 + a)
  (fun i => v i - a ^ 2 * g i,
   fun i => (1 - a) * z i + a * v i - a * g i)

omit [DecidableEq V] in
theorem rationalStep_mean_zero (a : ℚ) (x z g : V → ℚ)
    (hx : ∑ i, x i = 0) (hz : ∑ i, z i = 0) (hg : ∑ i, g i = 0) :
    (∑ i, (rationalStep a x z g).1 i = 0) ∧ (∑ i, (rationalStep a x z g).2 i = 0) := by
  have hv : ∑ i, (x i + a * z i) / (1 + a) = 0 := by
    rw [← sum_div, sum_add_distrib, ← mul_sum, hx, hz]
    simp
  simp only [rationalStep, sum_sub_distrib, sum_add_distrib, ← mul_sum, hz, hg, hv]
  simp

/-- All clipping and floor comparisons use the public rational iterate and offsets. -/
def publicCoefficients {n : ℕ} (k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (v : Fin n → ℚ) :
    {ij : Fin n × Fin n // ij.1 < ij.2} → ℤ :=
  fun e => quantizeInt (2 ^ b) (clipRat (k * (v e.val.1 - v e.val.2 - c e)))

/-- The real row coefficient uses the same canonical choice as the rational algorithm. -/
noncomputable def realPairRow {n : ℕ} (h : {ij : Fin n × Fin n // ij.1 < ij.2} → ℝ)
    (i j : Fin n) : ℝ :=
  if hij : i < j then h ⟨(i, j), hij⟩ else
    if hji : j < i then -h ⟨(j, i), hji⟩ else 0

theorem publicCoefficients_row_error {n : ℕ} (k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (v : Fin n → ℚ) (i j : Fin n) :
    |(signedPairs (publicCoefficients k b c v) i j : ℝ) * (2 : ℝ) ^ (-(b : ℤ)) -
      realPairRow (fun e => (clipRat (k * (v e.val.1 - v e.val.2 - c e)) : ℝ)) i j| ≤
        1 / (2 : ℝ) ^ b := by
  have hQ : 0 < (2 : ℕ) ^ b := by positivity
  have herr : ∀ e : {ij : Fin n × Fin n // ij.1 < ij.2},
      |(publicCoefficients k b c v e : ℝ) * (2 : ℝ) ^ (-(b : ℤ)) -
        (clipRat (k * (v e.val.1 - v e.val.2 - c e)) : ℝ)| ≤ 1 / (2 : ℝ) ^ b := by
    intro e
    have h := (quantize_abs_error hQ (clipRat (k * (v e.val.1 - v e.val.2 - c e)))).le
    simpa [publicCoefficients, quantizeRat, zpow_neg, zpow_natCast, div_eq_mul_inv] using h
  rcases lt_trichotomy i j with hij | hij | hij
  · simpa [signedPairs, realPairRow, hij, not_lt.mpr (le_of_lt hij)] using herr ⟨(i, j), hij⟩
  · subst j
    simp [signedPairs, realPairRow]
  · have he := herr ⟨(j, i), hij⟩
    have hneg : ∀ p q : ℝ, |-p - -q| = |p - q| := by
      intro p q
      rw [← abs_neg]
      congr 1
      ring
    simpa only [signedPairs, realPairRow, hij, not_lt.mpr (le_of_lt hij), ↓reduceDIte,
      Int.cast_neg, neg_mul, hneg] using he

theorem publicCoefficients_bounds {n : ℕ} (k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (v : Fin n → ℚ)
    (e : {ij : Fin n × Fin n // ij.1 < ij.2}) :
    -((2 ^ b : ℕ) : ℤ) ≤ publicCoefficients k b c v e ∧
      publicCoefficients k b c v e ≤ ((2 ^ b : ℕ) : ℤ) := by
  apply quantizeInt_bounds
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Fractional pairs in the real query program belong to the shared public sparse band. -/
theorem publicCoefficients_active {n k : ℕ} (hk : 0 < k) (b : ℕ)
    (c : SparseBand.OffsetTable n k) (v : Fin n → ℚ) (e : SparseBand.Pair n)
    (hfrac : -((2 ^ b : ℕ) : ℤ) < publicCoefficients k b (SparseBand.offsetRat c) v e ∧
      publicCoefficients k b (SparseBand.offsetRat c) v e < ((2 ^ b : ℕ) : ℤ)) :
    SparseBand.Active c (fun i => (v i : ℝ)) e := by
  have h := quantized_fractional_offset (show (0 : ℚ) < k by exact_mod_cast hk) hfrac
  simpa only [SparseBand.Active, Rat.cast_sub, Rat.cast_natCast] using h

/-- Any pair coefficient leaving positive forward capacity has bounded upward rise. -/
theorem publicCoefficients_forward_rise {n k : ℕ} (hk : 0 < k) (b : ℕ)
    (c : SparseBand.OffsetTable n k) (v : Fin n → ℚ) (e : SparseBand.Pair n)
    (hforward : -((2 ^ b : ℕ) : ℤ) < publicCoefficients k b (SparseBand.offsetRat c) v e) :
    (v e.val.2 : ℝ) - v e.val.1 ≤ 1 + 1 / (k : ℝ) := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hcq : (-1 : ℚ) ≤ SparseBand.offsetRat c e := by
    exact_mod_cast (abs_le.mp (SparseBand.offsetRat_abs_le_one hk c e)).1
  have hr : v e.val.2 - v e.val.1 ≤ 1 + 1 / (k : ℚ) := by
    by_contra hh
    have hd : v e.val.1 - v e.val.2 < -(1 + 1 / (k : ℚ)) := by
      have := lt_of_not_ge hh
      linarith
    have hs := quantized_opposite_saturation (Q := 2 ^ b) hkq hcq hd
    change publicCoefficients k b (SparseBand.offsetRat c) v e = -((2 ^ b : ℕ) : ℤ) at hs
    omega
  have hcast := (Rat.cast_le (K := ℝ)).mpr hr
  simpa only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hcast

/-- The reverse capacity obeys the same bound, using the same shared coefficient. -/
theorem publicCoefficients_reverse_rise {n k : ℕ} (hk : 0 < k) (b : ℕ)
    (c : SparseBand.OffsetTable n k) (v : Fin n → ℚ) (e : SparseBand.Pair n)
    (hreverse : publicCoefficients k b (SparseBand.offsetRat c) v e < ((2 ^ b : ℕ) : ℤ)) :
    (v e.val.1 : ℝ) - v e.val.2 ≤ 1 + 1 / (k : ℝ) := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hcq : SparseBand.offsetRat c e ≤ (1 : ℚ) := by
    exact_mod_cast (abs_le.mp (SparseBand.offsetRat_abs_le_one hk c e)).2
  have hr : v e.val.1 - v e.val.2 ≤ 1 + 1 / (k : ℚ) := by
    by_contra hh
    have hs := quantized_positive_saturation (Q := 2 ^ b) hkq hcq (lt_of_not_ge hh)
    change publicCoefficients k b (SparseBand.offsetRat c) v e = ((2 ^ b : ℕ) : ℤ) at hs
    omega
  have hcast := (Rat.cast_le (K := ℝ)).mpr hr
  simpa only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hcast

theorem graphGradient_eq_row {n : ℕ} (G : DiGraph (Fin n))
    (k : ℝ) (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℝ) (beta v : Fin n → ℝ) (i : Fin n) :
    graphGradient (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2)
      (fun e => (G.sym e.val.1 e.val.2 : ℝ)) c beta k v i =
      (∑ j, (G.sym i j : ℝ) * realPairRow
        (fun e => clip (k * (v e.val.1 - v e.val.2 - c e))) i j) - beta i + v i := by
  rw [graphGradient, canonical_divergence_row]
  congr 2
  apply sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [realPairRow, hij]
  · subst j
    simp [realPairRow]
  · simp [realPairRow, hij, not_lt.mpr (le_of_lt hij), G.sym_comm i j]

/-- The measured minus analytic gradient is precisely a weighted star of coefficient errors. -/
theorem measured_error_eq_row {n : ℕ} (G : DiGraph (Fin n)) (k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (beta v : Fin n → ℚ) (i : Fin n) :
    ((gradientProg b (signedPairs (publicCoefficients k b c v)) beta v).eval G.out i : ℝ) -
      graphGradient (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2)
        (fun e => (G.sym e.val.1 e.val.2 : ℝ)) (fun e => (c e : ℝ))
        (fun j => (beta j : ℝ)) k (fun j => (v j : ℝ)) i =
      ∑ j, (G.sym i j : ℝ) *
        ((signedPairs (publicCoefficients k b c v) i j : ℝ) * (2 : ℝ) ^ (-(b : ℤ)) -
          realPairRow (fun e => (clipRat (k * (v e.val.1 - v e.val.2 - c e)) : ℝ)) i j) := by
  rw [gradientProg_correct G b _ beta v
      (signedPairs_abs_bound _ (publicCoefficients_bounds k b c v)), graphGradient_eq_row]
  simp only [clipRat_cast, Rat.cast_mul, Rat.cast_sub, mul_sub, sum_sub_distrib]
  ring

theorem simple_pair_cap {n : ℕ} {G : DiGraph (Fin n)} (hG : G.Simple) (i j : Fin n) :
    0 ≤ (G.sym i j : ℝ) ∧ (G.sym i j : ℝ) ≤ 2 := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have h := Nat.add_le_add (hG i j) (hG j i)
  exact_mod_cast h

/-- The actual cut-realized gradient has squared error at most `4 n³ / Q²`. -/
theorem measured_error_sq {n : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple) (k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (beta v : Fin n → ℚ) :
    sqNorm (fun i =>
      ((gradientProg b (signedPairs (publicCoefficients k b c v)) beta v).eval G.out i : ℝ) -
        graphGradient (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2)
          (fun e => (G.sym e.val.1 e.val.2 : ℝ)) (fun e => (c e : ℝ))
          (fun j => (beta j : ℝ)) k (fun j => (v j : ℝ)) i) ≤
      4 * (n : ℝ) ^ 3 * (1 / (2 : ℝ) ^ b) ^ 2 := by
  simp_rw [measured_error_eq_row]
  simpa only [Fintype.card_fin] using star_error_sq_bound (fun i j => (G.sym i j : ℝ))
    (fun i j => (signedPairs (publicCoefficients k b c v) i j : ℝ) * (2 : ℝ) ^ (-(b : ℤ)) -
      realPairRow (fun e => (clipRat (k * (v e.val.1 - v e.val.2 - c e)) : ℝ)) i j)
    (by positivity) (simple_pair_cap hG) (publicCoefficients_row_error k b c v)

/-- The final actual measurement has L1 error at most `2 n² / Q`. -/
theorem measured_error_l1 {n : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple) (k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (beta v : Fin n → ℚ) :
    (∑ i, |((gradientProg b (signedPairs (publicCoefficients k b c v)) beta v).eval G.out i : ℝ) -
      graphGradient (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2)
        (fun e => (G.sym e.val.1 e.val.2 : ℝ)) (fun e => (c e : ℝ))
        (fun j => (beta j : ℝ)) k (fun j => (v j : ℝ)) i|) ≤
      2 * (n : ℝ) ^ 2 * (1 / (2 : ℝ) ^ b) := by
  simp_rw [measured_error_eq_row]
  simpa only [Fintype.card_fin] using star_error_l1_bound (fun i j => (G.sym i j : ℝ))
    (fun i j => (signedPairs (publicCoefficients k b c v) i j : ℝ) * (2 : ℝ) ^ (-(b : ℤ)) -
      realPairRow (fun e => (clipRat (k * (v e.val.1 - v e.val.2 - c e)) : ℝ)) i j)
    (by positivity) (simple_pair_cap hG) (publicCoefficients_row_error k b c v)

noncomputable def acceleratedStepProg {n : ℕ} (a k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (beta x z : Fin n → ℚ) :
    DTree (Finset (Fin n)) ℕ ((Fin n → ℚ) × (Fin n → ℚ)) (6 * (b + 1) * n) :=
  let v := fun i => (x i + a * z i) / (1 + a)
  ((gradientProg b (signedPairs (publicCoefficients k b c v)) beta v).map
    (rationalStep a x z)).cast (by rw [Fintype.card_fin])

theorem acceleratedStepProg_mean_zero {n : ℕ} (G : DiGraph (Fin n)) (a k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (beta x z : Fin n → ℚ)
    (hb : ∑ i, beta i = 0) (hx : ∑ i, x i = 0) (hz : ∑ i, z i = 0) :
    (∑ i, ((acceleratedStepProg a k b c beta x z).eval G.out).1 i = 0) ∧
    (∑ i, ((acceleratedStepProg a k b c beta x z).eval G.out).2 i = 0) := by
  let v := fun i => (x i + a * z i) / (1 + a)
  have hv : ∑ i, v i = 0 := by
    dsimp [v]
    rw [← sum_div, sum_add_distrib, ← mul_sum, hx, hz]
    simp
  have hg := gradientProg_sum_zero G b (signedPairs (publicCoefficients k b c v)) beta v
    (signedPairs_abs_bound _ (publicCoefficients_bounds k b c v))
    (signedPairs_skew _) hb hv
  simpa only [acceleratedStepProg, DTree.eval_cast, DTree.eval_map] using
    rationalStep_mean_zero a x z _ hx hz hg

/-- The rational program implements exactly the two real accelerated updates. -/
theorem acceleratedStepProg_real {n : ℕ} (G : DiGraph (Fin n)) (a k : ℚ) (b : ℕ)
    (c : SparseBand.Pair n → ℚ) (beta x z : Fin n → ℚ) :
    let v := fun i => (x i + a * z i) / (1 + a)
    let g := (gradientProg b (signedPairs (publicCoefficients k b c v)) beta v).eval G.out
    (fun i => (((acceleratedStepProg a k b c beta x z).eval G.out).1 i : ℝ)) =
      nextX a (blend a (fun i => (x i : ℝ)) (fun i => (z i : ℝ))) (fun i => (g i : ℝ)) ∧
    (fun i => (((acceleratedStepProg a k b c beta x z).eval G.out).2 i : ℝ)) =
      nextZ a (fun i => (z i : ℝ))
        (blend a (fun i => (x i : ℝ)) (fun i => (z i : ℝ))) (fun i => (g i : ℝ)) := by
  constructor <;> funext i <;>
    simp [acceleratedStepProg, rationalStep, nextX, nextZ, blend,
      DTree.eval_cast, DTree.eval_map]

/-- The complete finite adaptive loop; the type records its worst-case cut-query cap. -/
noncomputable def acceleratedRun {n : ℕ} (a k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (beta : Fin n → ℚ) :
    (J : ℕ) → (Fin n → ℚ) → (Fin n → ℚ) →
      DTree (Finset (Fin n)) ℕ ((Fin n → ℚ) × (Fin n → ℚ)) (J * (6 * (b + 1) * n))
  | 0, x, z => DTree.pure (x, z)
  | J + 1, x, z =>
      ((acceleratedStepProg a k b c beta x z).bind fun state =>
        acceleratedRun a k b c beta J state.1 state.2).cast (by ring)

theorem acceleratedRun_mean_zero {n : ℕ} (G : DiGraph (Fin n)) (a k : ℚ) (b : ℕ)
    (c : {ij : Fin n × Fin n // ij.1 < ij.2} → ℚ) (beta : Fin n → ℚ)
    (hb : ∑ i, beta i = 0) (J : ℕ) (x z : Fin n → ℚ)
    (hx : ∑ i, x i = 0) (hz : ∑ i, z i = 0) :
    (∑ i, ((acceleratedRun a k b c beta J x z).eval G.out).1 i = 0) ∧
    (∑ i, ((acceleratedRun a k b c beta J x z).eval G.out).2 i = 0) := by
  induction J generalizing x z with
  | zero => simpa [acceleratedRun] using And.intro hx hz
  | succ J ih =>
      have hs := acceleratedStepProg_mean_zero G a k b c beta x z hb hx hz
      simpa only [acceleratedRun, DTree.eval_cast, DTree.eval_bind] using ih _ _ hs.1 hs.2

/-- Evaluating the adaptive query tree gives the ordinary finite trajectory of its step. -/
theorem acceleratedRun_eval_eq_iterate {n : ℕ} (G : DiGraph (Fin n)) (a k : ℚ) (b : ℕ)
    (c : SparseBand.Pair n → ℚ) (beta : Fin n → ℚ) (J : ℕ) (x z : Fin n → ℚ) :
    (acceleratedRun a k b c beta J x z).eval G.out =
      (fun state : (Fin n → ℚ) × (Fin n → ℚ) =>
        (acceleratedStepProg a k b c beta state.1 state.2).eval G.out)^[J] (x, z) := by
  induction J generalizing x z with
  | zero => simp only [acceleratedRun, DTree.eval_pure, Function.iterate_zero_apply]
  | succ J ih =>
      simp only [acceleratedRun, DTree.eval_cast, DTree.eval_bind, Function.iterate_succ_apply]
      exact ih _ _

/-- The error envelope for the actual adaptive query program.  The reference minimizer
is used only in the proof; neither it nor a gradient oracle is supplied to the program. -/
theorem acceleratedRun_energy_error {n : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (a k : ℚ) (b : ℕ) (c : SparseBand.Pair n → ℚ) (beta x₀ z₀ : Fin n → ℚ)
    {L eps : ℝ} (hk : 0 < (k : ℝ)) (hL : (k : ℝ) * (4 * n) + 1 ≤ L)
    (ha : 0 ≤ (a : ℝ)) (ha1 : (a : ℝ) ≤ 1) (haL : L * (a : ℝ) ^ 2 = 1)
    (heps : 0 ≤ eps) (hprecision : 4 * (n : ℝ) ^ 3 * (1 / (2 : ℝ) ^ b) ^ 2 ≤ eps ^ 2)
    (r : Fin n → ℝ)
    (hmin : ∀ w, graphPotential (fun e : SparseBand.Pair n => e.val.1)
      (fun e : SparseBand.Pair n => e.val.2) (fun e => (G.sym e.val.1 e.val.2 : ℝ))
      (fun e => (c e : ℝ)) (fun i => (beta i : ℝ)) k r ≤
        graphPotential (fun e : SparseBand.Pair n => e.val.1)
          (fun e : SparseBand.Pair n => e.val.2) (fun e => (G.sym e.val.1 e.val.2 : ℝ))
          (fun e => (c e : ℝ)) (fun i => (beta i : ℝ)) k w) (J : ℕ) :
    let F := graphPotential (fun e : SparseBand.Pair n => e.val.1)
      (fun e : SparseBand.Pair n => e.val.2) (fun e => (G.sym e.val.1 e.val.2 : ℝ))
      (fun e => (c e : ℝ)) (fun i => (beta i : ℝ)) k
    let out := (acceleratedRun a k b c beta J x₀ z₀).eval G.out
    Real.sqrt (energy F r (fun i => (out.1 i : ℝ)) (fun i => (out.2 i : ℝ))) ≤
      Real.sqrt (1 - (a : ℝ)) ^ J *
        Real.sqrt (energy F r (fun i => (x₀ i : ℝ)) (fun i => (z₀ i : ℝ))) +
          2 * Real.sqrt 2 * eps := by
  let step := fun state : (Fin n → ℚ) × (Fin n → ℚ) =>
    (acceleratedStepProg a k b c beta state.1 state.2).eval G.out
  let state := fun j : ℕ => step^[j] (x₀, z₀)
  let x := fun j i => ((state j).1 i : ℝ)
  let z := fun j i => ((state j).2 i : ℝ)
  let v := fun j i => ((state j).1 i + a * (state j).2 i) / (1 + a)
  let g := fun j => (gradientProg b (signedPairs (publicCoefficients k b c (v j)))
    beta (v j)).eval G.out
  let grad := graphGradient (fun e : SparseBand.Pair n => e.val.1)
    (fun e : SparseBand.Pair n => e.val.2) (fun e => (G.sym e.val.1 e.val.2 : ℝ))
    (fun e => (c e : ℝ)) (fun i => (beta i : ℝ)) k
  let err := fun j i => (g j i : ℝ) - grad (fun i => (v j i : ℝ)) i
  have hsucc (j : ℕ) : state (j + 1) = step (state j) :=
    Function.iterate_succ_apply' step j (x₀, z₀)
  have hzero : state 0 = (x₀, z₀) := rfl
  have hvcast (j : ℕ) : (fun i => (v j i : ℝ)) = blend a (x j) (z j) := by
    funext i
    simp [v, x, z, blend]
  have hgrad (j : ℕ) (i : Fin n) : grad (blend a (x j) (z j)) i + err j i = (g j i : ℝ) := by
    dsimp only [err]
    rw [hvcast]
    ring
  have hx (j : ℕ) : x (j + 1) = nextX a (blend a (x j) (z j))
      (fun i => grad (blend a (x j) (z j)) i + err j i) := by
    simp_rw [hgrad]
    dsimp only [x, z]
    rw [hsucc]
    exact (acceleratedStepProg_real G a k b c beta (state j).1 (state j).2).1
  have hz (j : ℕ) : z (j + 1) = nextZ a (z j) (blend a (x j) (z j))
      (fun i => grad (blend a (x j) (z j)) i + err j i) := by
    simp_rw [hgrad]
    dsimp only [x, z]
    rw [hsucc]
    exact (acceleratedStepProg_real G a k b c beta (state j).1 (state j).2).2
  have herr (j : ℕ) : sqNorm (err j) ≤ eps ^ 2 :=
    (measured_error_sq G hG k b c beta (v j)).trans hprecision
  have hu (e : SparseBand.Pair n) : 0 ≤ (G.sym e.val.1 e.val.2 : ℝ) := Nat.cast_nonneg _
  have hB := canonical_laplacian_bound (fun e : SparseBand.Pair n =>
    (G.sym e.val.1 e.val.2 : ℝ)) (fun e => simple_pair_cap hG e.val.1 e.val.2)
  have hh := huber_trajectory_error (fun e : SparseBand.Pair n => e.val.1)
    (fun e : SparseBand.Pair n => e.val.2) (fun e => (G.sym e.val.1 e.val.2 : ℝ))
    (fun e => (c e : ℝ)) (fun i => (beta i : ℝ)) hk hu hB hL ha ha1 haL heps
    x z err r hmin herr hx hz J
  have hout : (acceleratedRun a k b c beta J x₀ z₀).eval G.out = state J :=
    acceleratedRun_eval_eq_iterate G a k b c beta J x₀ z₀
  simpa only [x, z, ← hout, hzero] using hh

/-- A public quadratic mass bound for all simple directed graphs. -/
theorem simple_pair_mass_le {n : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple) :
    (∑ e : SparseBand.Pair n, (G.sym e.val.1 e.val.2 : ℝ)) ≤ 2 * (n : ℝ) ^ 2 := by
  calc
    (∑ e : SparseBand.Pair n, (G.sym e.val.1 e.val.2 : ℝ)) ≤
        ∑ _e : SparseBand.Pair n, (2 : ℝ) :=
      sum_le_sum fun e _ => (simple_pair_cap hG e.val.1 e.val.2).2
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (2 : ℝ) := by
      rw [sum_canonical (fun _ : Fin n × Fin n => (2 : ℝ))]
      exact sum_le_sum fun i _ => sum_le_sum fun j _ => by split_ifs <;> norm_num
    _ = 2 * (n : ℝ) ^ 2 := by simp; ring

/-- The public precision `2^b ≥ 64 n²` supplies both required error budgets. -/
theorem dyadic_precision {n b : ℕ} (hn : 0 < n) (hb : 64 * n ^ 2 ≤ 2 ^ b) :
    4 * (n : ℝ) ^ 3 * (1 / (2 : ℝ) ^ b) ^ 2 ≤ (1 / 32 : ℝ) ^ 2 ∧
      2 * (n : ℝ) ^ 2 * (1 / (2 : ℝ) ^ b) ≤ 1 / 32 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
  have hQ : 64 * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ b := by exact_mod_cast hb
  have hQpos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hQsq := pow_le_pow_left₀ (show 0 ≤ 64 * (n : ℝ) ^ 2 by positivity) hQ 2
  have hn4 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (show 0 ≤ (n : ℝ) ^ 3 by positivity)]
  constructor
  · rw [div_pow, one_pow, mul_one_div]
    apply (div_le_iff₀ (sq_pos_of_pos hQpos)).mpr
    nlinarith
  · rw [mul_one_div]
    apply (div_le_iff₀ hQpos).mpr
    nlinarith

/-- End-to-end stationarity of the rational query loop under a feasible divergence
promise.  The minimizer, smoothness model, precision and convergence bounds are all
constructed or discharged here; the program starts at the zero public state. -/
theorem acceleratedRun_gradient_bound {n k T b : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hT : 8 * n * k ≤ T ^ 2) (hb : 64 * n ^ 2 ≤ 2 ^ b)
    (c : SparseBand.OffsetTable n k) (beta : Fin n → ℚ) (feasible : SparseBand.Pair n → ℝ)
    (hfeasible : ∀ e, |feasible e| ≤ (G.sym e.val.1 e.val.2 : ℝ))
    (hbeta : (fun i => (beta i : ℝ)) =
      divergence (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2) feasible) :
    let out := (acceleratedRun (1 / (T : ℚ)) k b (SparseBand.offsetRat c) beta
      (2 * T * Nat.clog 2 (16 * n)) (fun _ => 0) (fun _ => 0)).eval G.out
    sqNorm (graphGradient (fun e : SparseBand.Pair n => e.val.1)
      (fun e : SparseBand.Pair n => e.val.2) (fun e => (G.sym e.val.1 e.val.2 : ℝ))
      (fun e => (SparseBand.offsetRat c e : ℝ)) (fun i => (beta i : ℝ)) k
      (fun i => (out.1 i : ℝ))) ≤ 2 * (T : ℝ) ^ 2 := by
  let tail := fun e : SparseBand.Pair n => e.val.1
  let head := fun e : SparseBand.Pair n => e.val.2
  let u := fun e : SparseBand.Pair n => (G.sym e.val.1 e.val.2 : ℝ)
  let cr := fun e : SparseBand.Pair n => (SparseBand.offsetRat c e : ℝ)
  let br := fun i => (beta i : ℝ)
  let F := graphPotential tail head u cr br k
  let grad := graphGradient tail head u cr br k
  let J := 2 * T * Nat.clog 2 (16 * n)
  let out := (acceleratedRun (1 / (T : ℚ)) k b (SparseBand.offsetRat c) beta
    J (fun _ => 0) (fun _ => 0)).eval G.out
  let x := fun i => (out.1 i : ℝ)
  let z := fun i => (out.2 i : ℝ)
  have hnp : 0 < n := by omega
  have hkp : 0 < k := by omega
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkp
  have hu (e : SparseBand.Pair n) : 0 ≤ u e := Nat.cast_nonneg _
  have hc (e : SparseBand.Pair n) : |cr e| ≤ 1 := SparseBand.offsetRat_abs_le_one hkp c e
  obtain ⟨r, hr⟩ := graphPotential_exists_minimizer tail head u cr feasible hkr hu hc hfeasible
  have hmin : ∀ w, F r ≤ F w := by
    intro w
    simpa only [F, br, hbeta] using hr w
  obtain ⟨hTp, hTL, ha, ha1, haL⟩ := integer_schedule hn hk hT
  have hprecision := (dyadic_precision hnp hb).1
  have henv := acceleratedRun_energy_error G hG (1 / (T : ℚ)) k b (SparseBand.offsetRat c)
    beta (fun _ => 0) (fun _ => 0) (by simpa only [Rat.cast_natCast] using hkpos)
    (show ((k : ℚ) : ℝ) * (4 * n) + 1 ≤ (T : ℝ) ^ 2 by
      simp only [Rat.cast_natCast]; nlinarith)
    (by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using ha)
    (by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using ha1)
    (by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using haL)
    (by norm_num : (0 : ℝ) ≤ 1 / 32) hprecision r
    (by simpa only [Rat.cast_natCast] using hmin) J
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_zero] at henv
  change Real.sqrt (energy F r x z) ≤ Real.sqrt (1 - 1 / (T : ℝ)) ^ J *
    Real.sqrt (energy F r (fun _ => 0) (fun _ => 0)) + 2 * Real.sqrt 2 * (1 / 32) at henv
  have hinit := graphPotential_initial_energy tail head u cr feasible hkr hu hc hfeasible r
  have hdist : sqDist (fun _ : Fin n => 0) r = sqNorm r := by
    simp [sqDist, sqNorm]
  have hinit' : energy F r (fun _ => 0) (fun _ => 0) ≤ 5 * (n : ℝ) ^ 2 := by
    have hm := simple_pair_mass_le G hG
    change (∑ e, u e) ≤ 2 * (n : ℝ) ^ 2 at hm
    change graphPotential tail head u cr (divergence tail head feasible) k (fun _ => 0) -
      graphPotential tail head u cr (divergence tail head feasible) k r + sqNorm r / 2 ≤
        (5 / 2) * ∑ e, u e at hinit
    unfold energy F
    rw [hdist, show br = divergence tail head feasible from hbeta]
    linarith
  have hE : 0 ≤ energy F r x z :=
    add_nonneg (sub_nonneg.mpr (hmin _)) (div_nonneg (sqDist_nonneg _ _) (by norm_num))
  have hs0 : Real.sqrt (energy F r (fun _ => 0) (fun _ => 0)) ≤ Real.sqrt 5 * n := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    exact hinit'
  have hcontract := fixed_schedule_contraction hnp hTp
  have hm := mul_le_mul hcontract hs0 (Real.sqrt_nonneg _) (by positivity : 0 ≤ 1 / (16 * (n : ℝ)))
  have hcancel : 1 / (16 * (n : ℝ)) * (Real.sqrt 5 * n) = Real.sqrt 5 / 16 := by
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hnp)]
  rw [hcancel] at hm
  have h5 : Real.sqrt 5 < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 2 < 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hsmall : Real.sqrt (energy F r x z) < 1 := by
    change Real.sqrt (1 - 1 / (T : ℝ)) ^ J *
      Real.sqrt (energy F r (fun _ => 0) (fun _ => 0)) ≤ Real.sqrt 5 / 16 at hm
    nlinarith
  have hEsmall : energy F r x z < 1 := by
    simpa using (Real.sqrt_lt hE (by norm_num : (0 : ℝ) ≤ 1)).mp hsmall
  have hB := canonical_laplacian_bound u (fun e => simple_pair_cap hG e.val.1 e.val.2)
  have hsmooth : F (nextX (1 / (T : ℝ)) x (grad x)) ≤ F x +
      dot (grad x) (fun i => nextX (1 / (T : ℝ)) x (grad x) i - x i) +
        (T : ℝ) ^ 2 / 2 * sqDist (nextX (1 / (T : ℝ)) x (grad x)) x := by
    have hh := graphPotential_upper tail head u cr br hkpos hu hB x (nextX (1 / (T : ℝ)) x (grad x))
    have hmul := mul_nonneg (show 0 ≤ (T : ℝ) ^ 2 - ((k : ℝ) * (4 * n) + 1) by nlinarith)
      (sqDist_nonneg (nextX (1 / (T : ℝ)) x (grad x)) x)
    change F _ ≤ F x + dot (grad x) _ + _ at hh
    nlinarith
  have hgap := gradient_sq_le_gap F (1 / (T : ℝ)) ((T : ℝ) ^ 2) x (grad x) r
    (sq_pos_of_pos (by exact_mod_cast hTp)) haL hmin hsmooth
  have hnonneg := sqDist_nonneg z r
  have hgap1 : F x - F r ≤ 1 := by unfold energy at hEsmall; linarith
  have hmul := mul_le_mul_of_nonneg_left hgap1 (show 0 ≤ 2 * (T : ℝ) ^ 2 by positivity)
  exact hgap.trans (by simpa using hmul)

/-- Public potential and measured regularized discrepancy after the loop and one final measurement. -/
noncomputable def acceleratedOutput {n : ℕ} (a k : ℚ) (b : ℕ)
    (c : SparseBand.Pair n → ℚ) (beta : Fin n → ℚ) (J : ℕ) :
    DTree (Finset (Fin n)) ℕ ((Fin n → ℚ) × (Fin n → ℚ))
      ((J + 1) * (6 * (b + 1) * n)) :=
  ((acceleratedRun a k b c beta J (fun _ => 0) (fun _ => 0)).bind fun state =>
    ((gradientProg b (signedPairs (publicCoefficients k b c state.1)) beta state.1).map
      fun g => (state.1, g))).cast (by rw [Fintype.card_fin]; ring)

theorem acceleratedOutput_mean_zero {n : ℕ} (G : DiGraph (Fin n)) (a k : ℚ) (b : ℕ)
    (c : SparseBand.Pair n → ℚ) (beta : Fin n → ℚ) (J : ℕ) (hb : ∑ i, beta i = 0) :
    (∑ i, ((acceleratedOutput a k b c beta J).eval G.out).1 i = 0) ∧
      (∑ i, ((acceleratedOutput a k b c beta J).eval G.out).2 i = 0) := by
  let out := (acceleratedRun a k b c beta J (fun _ => 0) (fun _ => 0)).eval G.out
  have hz := acceleratedRun_mean_zero G a k b c beta hb J (fun _ => 0) (fun _ => 0)
    (by simp) (by simp)
  have hg := gradientProg_sum_zero G b (signedPairs (publicCoefficients k b c out.1)) beta out.1
    (signedPairs_abs_bound _ (publicCoefficients_bounds k b c out.1))
    (signedPairs_skew _) hb hz.1
  simpa only [acceleratedOutput, DTree.eval_cast, DTree.eval_bind, DTree.eval_map] using
    And.intro hz.1 hg

/-- Exact interpretation of the measured output: it is `y - beta + r`, where
`y` is the divergence of the shared dyadic pair coefficients. -/
theorem acceleratedOutput_regularized_divergence {n : ℕ} (G : DiGraph (Fin n))
    (a k : ℚ) (b : ℕ) (c : SparseBand.Pair n → ℚ) (beta : Fin n → ℚ) (J : ℕ) (i : Fin n) :
    let out := (acceleratedOutput a k b c beta J).eval G.out
    (out.2 i : ℝ) = divergence (fun e : SparseBand.Pair n => e.val.1)
      (fun e : SparseBand.Pair n => e.val.2)
      (fun e => (G.sym e.val.1 e.val.2 : ℝ) *
        ((publicCoefficients k b c out.1 e : ℝ) * (2 : ℝ) ^ (-(b : ℤ)))) i - beta i + out.1 i := by
  let r := ((acceleratedRun a k b c beta J (fun _ => 0) (fun _ => 0)).eval G.out).1
  have h := canonical_gradientProg_correct G b (publicCoefficients k b c r) beta r
    (publicCoefficients_bounds k b c r) i
  simpa only [acceleratedOutput, DTree.eval_cast, DTree.eval_bind, DTree.eval_map] using h

/-- The cut-realized regularized discrepancy `y - beta + r` obeys the source's L1 bound.
The displayed query type of `acceleratedOutput` also accounts for the final measurement. -/
theorem acceleratedOutput_l1 {n k T b : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hT : 8 * n * k ≤ T ^ 2) (hb : 64 * n ^ 2 ≤ 2 ^ b)
    (c : SparseBand.OffsetTable n k) (beta : Fin n → ℚ) (feasible : SparseBand.Pair n → ℝ)
    (hfeasible : ∀ e, |feasible e| ≤ (G.sym e.val.1 e.val.2 : ℝ))
    (hbeta : (fun i => (beta i : ℝ)) =
      divergence (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2) feasible) :
    (∑ i, |(((acceleratedOutput (1 / (T : ℚ)) k b (SparseBand.offsetRat c) beta
      (2 * T * Nat.clog 2 (16 * n))).eval G.out).2 i : ℝ)|) ≤
        Real.sqrt (2 * n) * T + 1 / 32 := by
  let out := (acceleratedRun (1 / (T : ℚ)) k b (SparseBand.offsetRat c) beta
    (2 * T * Nat.clog 2 (16 * n)) (fun _ => 0) (fun _ => 0)).eval G.out
  let grad := graphGradient (fun e : SparseBand.Pair n => e.val.1)
    (fun e : SparseBand.Pair n => e.val.2) (fun e => (G.sym e.val.1 e.val.2 : ℝ))
    (fun e => (SparseBand.offsetRat c e : ℝ)) (fun i => (beta i : ℝ)) k
    (fun i => (out.1 i : ℝ))
  let measured := (gradientProg b (signedPairs (publicCoefficients k b
    (SparseBand.offsetRat c) out.1)) beta out.1).eval G.out
  have hgrad := acceleratedRun_gradient_bound G hG hn hk hT hb c beta feasible hfeasible hbeta
  have herr := (measured_error_l1 G hG k b (SparseBand.offsetRat c) beta out.1).trans
    (dyadic_precision (by omega : 0 < n) hb).2
  simp only [Rat.cast_natCast] at herr
  have hh := final_l1_discrepancy grad (fun i => (measured i : ℝ) - grad i)
    (Nat.cast_nonneg (α := ℝ) T) hgrad herr
  simp only [← add_sub_assoc, add_sub_cancel_left, Fintype.card_fin] at hh
  simpa only [acceleratedOutput, DTree.eval_cast, DTree.eval_bind, DTree.eval_map] using hh

/-- The fixed-`μ = 1` public schedule, including its final query measurement. -/
noncomputable def fixedMuOutput {n : ℕ} (k : ℕ) (c : SparseBand.OffsetTable n k)
    (beta : Fin n → ℚ) :
    DTree (Finset (Fin n)) ℕ ((Fin n → ℚ) × (Fin n → ℚ))
      ((scheduleSteps n k + 1) * (6 * (scheduleBits n + 1) * n)) :=
  acceleratedOutput (1 / (scheduleT n k : ℚ)) k (scheduleBits n)
    (SparseBand.offsetRat c) beta (scheduleSteps n k)

theorem fixedMuOutput_l1 {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (c : SparseBand.OffsetTable n k) (beta : Fin n → ℚ)
    (feasible : SparseBand.Pair n → ℝ)
    (hfeasible : ∀ e, |feasible e| ≤ (G.sym e.val.1 e.val.2 : ℝ))
    (hbeta : (fun i => (beta i : ℝ)) =
      divergence (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2) feasible) :
    (∑ i, |(((fixedMuOutput k c beta).eval G.out).2 i : ℝ)|) ≤
      Real.sqrt (2 * n) * scheduleT n k + 1 / 32 :=
  acceleratedOutput_l1 G hG hn hk (scheduleT_sufficient n k) (scheduleBits_sufficient n)
    c beta feasible hfeasible hbeta

theorem fixedMuOutput_mean_zero {n k : ℕ} (G : DiGraph (Fin n))
    (c : SparseBand.OffsetTable n k) (beta : Fin n → ℚ) (feasible : SparseBand.Pair n → ℝ)
    (hbeta : (fun i => (beta i : ℝ)) =
      divergence (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2) feasible) :
    (∑ i, ((fixedMuOutput k c beta).eval G.out).1 i = 0) ∧
      (∑ i, ((fixedMuOutput k c beta).eval G.out).2 i = 0) := by
  have hsum := congrArg (fun f : Fin n → ℝ => ∑ i, f i) hbeta
  rw [divergence_sum] at hsum
  have hb : ∑ i, beta i = 0 := by exact_mod_cast hsum
  exact acceleratedOutput_mean_zero G _ _ _ _ _ _ hb

/-- The public imbalance uses the existing two-cut-per-vertex degree program. -/
noncomputable def degreeBetaProg (n : ℕ) :
    DTree (Finset (Fin n)) ℕ (Fin n → ℚ) (2 * n) :=
  ((DirectedMincut.degs (univ : Finset (Fin n)).toList).map
    fun ds i => (ds.1 i : ℚ) - ds.2 i).cast (by rw [length_toList, card_univ, Fintype.card_fin])

theorem degreeBetaProg_correct {n : ℕ} (G : DiGraph (Fin n)) (i : Fin n) :
    (degreeBetaProg n).eval G.out i = (G.outdeg i : ℚ) - G.indeg i := by
  have hd := DirectedMincut.degs_correct G (univ : Finset (Fin n)).toList
    (w := i) (mem_toList.mpr (mem_univ i))
  simp only [degreeBetaProg, DTree.eval_cast, DTree.eval_map, hd.1, hd.2]

/-- The original hidden arcs supply a feasibility witness; no witness is queried. -/
theorem degreeBetaProg_feasible {n : ℕ} (G : DiGraph (Fin n)) :
    ∃ feasible : SparseBand.Pair n → ℝ,
      (∀ e, |feasible e| ≤ (G.sym e.val.1 e.val.2 : ℝ)) ∧
      (fun i => ((degreeBetaProg n).eval G.out i : ℝ)) =
        divergence (fun e : SparseBand.Pair n => e.val.1) (fun e : SparseBand.Pair n => e.val.2) feasible := by
  let f := fun e : SparseBand.Pair n => (G.c e.val.1 e.val.2 : ℝ) - G.c e.val.2 e.val.1
  refine ⟨f, ?_, ?_⟩
  · intro e
    dsimp only [f, DiGraph.sym]
    push_cast
    apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (G.c e.val.1 e.val.2),
      Nat.cast_nonneg (α := ℝ) (G.c e.val.2 e.val.1)]
  · funext i
    have hbr : ((degreeBetaProg n).eval G.out i : ℝ) =
        (G.outdeg i : ℝ) - G.indeg i := by
      simpa only [Rat.cast_sub, Rat.cast_natCast] using
        congrArg (fun t : ℚ => (t : ℝ)) (degreeBetaProg_correct G i)
    rw [hbr, canonical_divergence_row]
    simp only [DiGraph.outdeg, DiGraph.indeg, Nat.cast_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [f, hij]
    · subst j
      simp
    · simp [f, hij, not_lt.mpr (le_of_lt hij)]

/-- Full query-realized acceleration, including discovery of the public imbalance.
The output is `(beta, potential, regularized discrepancy)`. -/
noncomputable def queryPotentialProg {n : ℕ} (k : ℕ) (c : SparseBand.OffsetTable n k) :
    DTree (Finset (Fin n)) ℕ ((Fin n → ℚ) × ((Fin n → ℚ) × (Fin n → ℚ)))
      (2 * n + (scheduleSteps n k + 1) * (6 * (scheduleBits n + 1) * n)) :=
  (degreeBetaProg n).bind fun beta => (fixedMuOutput k c beta).map fun out => (beta, out)

/-- The budget holds on every answer sequence, independently of graph promises. -/
theorem queryPotentialProg_cost {n k : ℕ} (c : SparseBand.OffsetTable n k)
    (read : Finset (Fin n) → ℕ) :
    (queryPotentialProg k c).cost read ≤
      2 * n + (scheduleSteps n k + 1) * (6 * (scheduleBits n + 1) * n) :=
  DTree.cost_le _ _

/-- The actual query cap has the required `n sqrt(nk)` dependence and two logarithms. -/
theorem queryPotentialProg_cost_sqrt {n k : ℕ} (hn : 2 ≤ n)
    (c : SparseBand.OffsetTable n k) (read : Finset (Fin n) → ℕ) :
    ((queryPotentialProg k c).cost read : ℝ) ≤
      60 * n * (Real.sqrt ((n : ℝ) * k) + 1) * ((scheduleBits n : ℝ) + 1) ^ 2 := by
  let T : ℝ := scheduleT n k
  let B : ℝ := (scheduleBits n : ℝ) + 1
  let C : ℝ := Nat.clog 2 (16 * n)
  have hT1 : 1 ≤ T := by simp [T, scheduleT]
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    linarith [Nat.cast_nonneg (α := ℝ) (scheduleBits n)]
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have hCB : C ≤ B := by
    have h : Nat.clog 2 (16 * n) ≤ scheduleBits n :=
      Nat.clog_mono_right 2 (by nlinarith)
    have hh : C ≤ (scheduleBits n : ℝ) := by
      dsimp only [C]
      exact_mod_cast h
    dsimp only [B]
    linarith
  have h1 := mul_le_mul_of_nonneg_left hCB (show 0 ≤ T * B by positivity)
  have h2 := mul_le_mul_of_nonneg_left hB1 (show 0 ≤ T * B by positivity)
  have h3 := mul_le_mul_of_nonneg_right hT1 (show 0 ≤ B by positivity)
  have hscalar : 2 + (2 * T * C + 1) * 6 * B ≤ 20 * T * B ^ 2 := by
    nlinarith
  have hcap : ((queryPotentialProg k c).cost read : ℝ) ≤
      2 * n + (2 * T * C + 1) * (6 * B * n) := by
    have hh : ((queryPotentialProg k c).cost read : ℝ) ≤
        ((2 * n + (scheduleSteps n k + 1) * (6 * (scheduleBits n + 1) * n) : ℕ) : ℝ) := by
      exact_mod_cast (queryPotentialProg_cost c read)
    simpa [T, B, C, scheduleSteps] using hh
  have hcost : ((queryPotentialProg k c).cost read : ℝ) ≤ 20 * T * B ^ 2 * n := by
    have hm := mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg (α := ℝ) n)
    nlinarith
  have hs : Real.sqrt (8 * (n : ℝ) * k) ≤ 3 * Real.sqrt ((n : ℝ) * k) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (Nat.cast_nonneg (α := ℝ) k)]
  have hT : T ≤ 3 * (Real.sqrt ((n : ℝ) * k) + 1) := by
    have ht := scheduleT_upper n k
    change T ≤ _ at ht
    linarith
  have hm := mul_le_mul_of_nonneg_right hT (show 0 ≤ 20 * B ^ 2 * n by positivity)
  change ((queryPotentialProg k c).cost read : ℝ) ≤
    60 * n * (Real.sqrt ((n : ℝ) * k) + 1) * B ^ 2
  nlinarith

/-- The true regularized gradient bound at the potential returned by the full query program. -/
theorem queryPotentialProg_gradient {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (c : SparseBand.OffsetTable n k) :
    let out := (queryPotentialProg k c).eval G.out
    sqNorm (graphGradient (fun e : SparseBand.Pair n => e.val.1)
      (fun e : SparseBand.Pair n => e.val.2) (fun e => (G.sym e.val.1 e.val.2 : ℝ))
      (fun e => (SparseBand.offsetRat c e : ℝ)) (fun i => (out.1 i : ℝ)) k
      (fun i => (out.2.1 i : ℝ))) ≤ 2 * (scheduleT n k : ℝ) ^ 2 := by
  obtain ⟨f, hf, hb⟩ := degreeBetaProg_feasible G
  have h := acceleratedRun_gradient_bound G hG hn hk (scheduleT_sufficient n k)
    (scheduleBits_sufficient n) c ((degreeBetaProg n).eval G.out) f hf hb
  simp only [queryPotentialProg, fixedMuOutput, acceleratedOutput,
    DTree.eval_bind, DTree.eval_map, DTree.eval_cast]
  simpa only [scheduleSteps] using h

/-- The public output's last coordinate is precisely the measured regularized divergence. -/
theorem queryPotentialProg_regularized_divergence {n k : ℕ} (G : DiGraph (Fin n))
    (c : SparseBand.OffsetTable n k) (i : Fin n) :
    let out := (queryPotentialProg k c).eval G.out
    (out.2.2 i : ℝ) = divergence (fun e : SparseBand.Pair n => e.val.1)
      (fun e : SparseBand.Pair n => e.val.2)
      (fun e => (G.sym e.val.1 e.val.2 : ℝ) *
        ((publicCoefficients k (scheduleBits n) (SparseBand.offsetRat c) out.2.1 e : ℝ) *
          (2 : ℝ) ^ (-(scheduleBits n : ℤ)))) i - out.1 i + out.2.1 i := by
  have h := acceleratedOutput_regularized_divergence G (1 / (scheduleT n k : ℚ)) k
    (scheduleBits n) (SparseBand.offsetRat c) ((degreeBetaProg n).eval G.out)
    (scheduleSteps n k) i
  simpa only [queryPotentialProg, fixedMuOutput, DTree.eval_bind, DTree.eval_map] using h

/-- An unconditional simple-graph query theorem for the scheduled regularized discrepancy. -/
theorem queryPotentialProg_l1 {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (c : SparseBand.OffsetTable n k) :
    (∑ i, |(((queryPotentialProg k c).eval G.out).2.2 i : ℝ)|) ≤
      Real.sqrt (2 * n) * scheduleT n k + 1 / 32 := by
  obtain ⟨f, hf, hb⟩ := degreeBetaProg_feasible G
  have h := fixedMuOutput_l1 G hG hn hk c ((degreeBetaProg n).eval G.out) f hf hb
  simpa only [queryPotentialProg, DTree.eval_bind, DTree.eval_map] using h

/-- An explicit real bound for composition with the rounding and height estimates. -/
theorem queryPotentialProg_l1_explicit {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (c : SparseBand.OffsetTable n k) :
    (∑ i, |(((queryPotentialProg k c).eval G.out).2.2 i : ℝ)|) ≤
      4 * (n : ℝ) * Real.sqrt k + n + 1 / 32 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (2 * (n : ℝ)) ≤ n := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  have hprod : Real.sqrt (2 * (n : ℝ)) * Real.sqrt (8 * (n : ℝ) * k) =
      4 * n * Real.sqrt k := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (2 * (n : ℝ)) * (8 * (n : ℝ) * k) = (4 * (n : ℝ)) ^ 2 * k by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hT := mul_le_mul_of_nonneg_left (scheduleT_upper n k)
    (Real.sqrt_nonneg (2 * (n : ℝ)))
  rw [mul_add, hprod, mul_one] at hT
  exact (queryPotentialProg_l1 G hG hn hk c).trans (by linarith)

theorem queryPotentialProg_mean_zero {n k : ℕ} (G : DiGraph (Fin n))
    (c : SparseBand.OffsetTable n k) :
    (∑ i, ((queryPotentialProg k c).eval G.out).2.1 i = 0) ∧
      (∑ i, ((queryPotentialProg k c).eval G.out).2.2 i = 0) := by
  obtain ⟨f, _, hb⟩ := degreeBetaProg_feasible G
  have h := fixedMuOutput_mean_zero G c ((degreeBetaProg n).eval G.out) f hb
  simpa only [queryPotentialProg, DTree.eval_bind, DTree.eval_map] using h

#print axioms gradientProg_correct
#print axioms publicCoefficients_active
#print axioms publicCoefficients_forward_rise
#print axioms publicCoefficients_reverse_rise
#print axioms measured_error_sq
#print axioms acceleratedRun_mean_zero
#print axioms acceleratedRun_energy_error
#print axioms acceleratedRun_gradient_bound
#print axioms acceleratedOutput_l1
#print axioms acceleratedOutput_regularized_divergence
#print axioms fixedMuOutput_l1
#print axioms fixedMuOutput_mean_zero
#print axioms queryPotentialProg_l1
#print axioms queryPotentialProg_cost
#print axioms queryPotentialProg_cost_sqrt
#print axioms queryPotentialProg_l1_explicit
#print axioms queryPotentialProg_gradient
#print axioms queryPotentialProg_regularized_divergence
#print axioms queryPotentialProg_mean_zero

end CutQueryComplexity.DirectedUnitST.Acceleration
