import CutQueryComplexity.DirectedUnitST.Acceleration.Huber
import Mathlib.Algebra.Order.Floor.Ring

/-! # Public rational coefficients with one shared integer per pair

Rounding is performed in `ℚ`; its error estimates are then transported to `ℝ`.
The opposite endpoint receives the negative of the *same* rounded integer.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Acceleration

open Finset

def clipRat (t : ℚ) : ℚ := max (-1) (min 1 t)

def quantizeInt (Q : ℕ) (t : ℚ) : ℤ := ⌊(Q : ℚ) * t⌋

def quantizeRat (Q : ℕ) (t : ℚ) : ℚ := (quantizeInt Q t : ℚ) / Q

theorem clipRat_cast (t : ℚ) : (clipRat t : ℝ) = clip (t : ℝ) := by
  simp [clipRat, clip]

theorem quantizeInt_bounds (Q : ℕ) {t : ℚ} (ht : -1 ≤ t ∧ t ≤ 1) :
    -(Q : ℤ) ≤ quantizeInt Q t ∧ quantizeInt Q t ≤ (Q : ℤ) := by
  constructor
  · apply Int.le_floor.mpr
    push_cast
    have hm := mul_le_mul_of_nonneg_left ht.1 (Nat.cast_nonneg (α := ℚ) Q)
    nlinarith
  · apply Int.floor_le_iff.mpr
    push_cast
    have hm := mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg (α := ℚ) Q)
    nlinarith

@[simp] theorem quantizeInt_one (Q : ℕ) : quantizeInt Q 1 = Q := by
  simp [quantizeInt]

@[simp] theorem quantizeInt_neg_one (Q : ℕ) : quantizeInt Q (-1) = -(Q : ℤ) := by
  simpa only [quantizeInt, mul_neg, mul_one, Int.cast_neg, Int.cast_natCast] using
    (Int.floor_intCast (R := ℚ) (-(Q : ℤ)))

theorem quantize_error {Q : ℕ} (hQ : 0 < Q) (t : ℚ) :
    0 ≤ (t : ℝ) - (quantizeRat Q t : ℝ) ∧
      (t : ℝ) - (quantizeRat Q t : ℝ) < 1 / (Q : ℝ) := by
  have hl : (quantizeInt Q t : ℝ) ≤ (Q : ℝ) * (t : ℝ) := by
    exact_mod_cast (Int.floor_le ((Q : ℚ) * t))
  have hu : (Q : ℝ) * (t : ℝ) < (quantizeInt Q t : ℝ) + 1 := by
    exact_mod_cast (Int.lt_floor_add_one ((Q : ℚ) * t))
  have hp : (0 : ℝ) < Q := by exact_mod_cast hQ
  simp only [quantizeRat, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr (by nlinarith))
  · apply (lt_div_iff₀ hp).mpr
    have he : (quantizeInt Q t : ℝ) / Q * Q = quantizeInt Q t := div_mul_cancel₀ _ (ne_of_gt hp)
    nlinarith

theorem quantize_abs_error {Q : ℕ} (hQ : 0 < Q) (t : ℚ) :
    |(quantizeRat Q t : ℝ) - (t : ℝ)| < 1 / (Q : ℝ) := by
  have h := quantize_error hQ t
  rw [abs_sub_comm, abs_of_nonneg h.1]
  exact h.2

/-- A fractional measured coefficient was unsaturated before rounding. -/
theorem quantized_fractional_in_band {Q : ℕ} {t : ℚ}
    (hfrac : -(Q : ℤ) < quantizeInt Q (clipRat t) ∧
      quantizeInt Q (clipRat t) < (Q : ℤ)) : |t| < 1 := by
  apply abs_lt.mpr
  constructor
  · by_contra h
    have ht : t ≤ -1 := le_of_not_gt h
    have hc : clipRat t = -1 := by
      simp [clipRat, min_eq_right (by linarith : t ≤ 1), max_eq_left ht]
    rw [hc, quantizeInt_neg_one] at hfrac
    linarith [hfrac.1]
  · by_contra h
    have ht : 1 ≤ t := le_of_not_gt h
    have hc : clipRat t = 1 := by simp [clipRat, min_eq_left ht]
    rw [hc, quantizeInt_one] at hfrac
    linarith [hfrac.2]

/-- Exact interface to the public sparse band after the offset is subtracted. -/
theorem quantized_fractional_offset {Q : ℕ} {k d c : ℚ} (hk : 0 < k)
    (hfrac : -(Q : ℤ) < quantizeInt Q (clipRat (k * (d - c))) ∧
      quantizeInt Q (clipRat (k * (d - c))) < (Q : ℤ)) :
    |(d : ℝ) - (c : ℝ)| < 1 / (k : ℝ) := by
  have h := quantized_fractional_in_band hfrac
  rw [abs_mul, abs_of_pos hk] at h
  have hr : |d - c| < 1 / k := (lt_div_iff₀ hk).mpr (by nlinarith)
  exact_mod_cast hr

/-- If a canonical arc would rise too far, its rounded forward coefficient is exactly `-Q`. -/
theorem quantized_opposite_saturation {Q : ℕ} {k d c : ℚ} (hk : 0 < k)
    (hc : -1 ≤ c) (hd : d < -(1 + 1 / k)) :
    quantizeInt Q (clipRat (k * (d - c))) = -(Q : ℤ) := by
  have hcancel : k * (1 / k) = 1 := by field_simp [ne_of_gt hk]
  have hm := mul_lt_mul_of_pos_left hd hk
  have hm' := mul_le_mul_of_nonneg_left hc hk.le
  have ht : k * (d - c) ≤ -1 := by nlinarith
  have hclip : clipRat (k * (d - c)) = -1 := by
    simp [clipRat, min_eq_right (show k * (d - c) ≤ 1 by linarith), max_eq_left ht]
  rw [hclip, quantizeInt_neg_one]

/-- The symmetric saturation needed to rule out an excessive rise on a reverse arc. -/
theorem quantized_positive_saturation {Q : ℕ} {k d c : ℚ} (hk : 0 < k)
    (hc : c ≤ 1) (hd : 1 + 1 / k < d) :
    quantizeInt Q (clipRat (k * (d - c))) = (Q : ℤ) := by
  have hcancel : k * (1 / k) = 1 := by field_simp [ne_of_gt hk]
  have hm := mul_lt_mul_of_pos_left hd hk
  have hm' := mul_le_mul_of_nonneg_left hc hk.le
  have ht : 1 ≤ k * (d - c) := by nlinarith
  have hclip : clipRat (k * (d - c)) = 1 := by simp [clipRat, min_eq_left ht]
  rw [hclip, quantizeInt_one]

/-- Lift canonical pair integers to skew-symmetric endpoint coefficients. -/
def signedPairs {n : ℕ} (h : {ij : Fin n × Fin n // ij.1 < ij.2} → ℤ)
    (i j : Fin n) : ℤ :=
  if hij : i < j then h ⟨(i, j), hij⟩ else
  if hji : j < i then -h ⟨(j, i), hji⟩ else 0

@[simp] theorem signedPairs_self {n : ℕ}
    (h : {ij : Fin n × Fin n // ij.1 < ij.2} → ℤ) (i : Fin n) :
    signedPairs h i i = 0 := by simp [signedPairs]

theorem signedPairs_skew {n : ℕ}
    (h : {ij : Fin n × Fin n // ij.1 < ij.2} → ℤ) (i j : Fin n) :
    signedPairs h j i = -signedPairs h i j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [signedPairs, hij, not_lt.mpr (le_of_lt hij)]
  · subst j
    simp
  · simp [signedPairs, hij, not_lt.mpr (le_of_lt hij)]

theorem signedPairs_abs_bound {n Q : ℕ}
    (h : {ij : Fin n × Fin n // ij.1 < ij.2} → ℤ)
    (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ)) (i j : Fin n) :
    (signedPairs h i j).natAbs ≤ Q := by
  unfold signedPairs
  split_ifs with hij hji
  · have hbound := hb ⟨(i, j), hij⟩
    omega
  · rw [Int.natAbs_neg]
    have hbound := hb ⟨(j, i), hji⟩
    omega
  · simp

section Error

variable {V : Type*} [Fintype V]

/-- Coordinate error of a measured star; hidden multiplicities are bounded by two. -/
theorem star_error_bound (u eta : V → ℝ) {eps : ℝ} (heps : 0 ≤ eps)
    (hu : ∀ j, 0 ≤ u j ∧ u j ≤ 2) (heta : ∀ j, |eta j| ≤ eps) :
    |∑ j, u j * eta j| ≤ 2 * Fintype.card V * eps := by
  calc
    |∑ j, u j * eta j| ≤ ∑ j, |u j * eta j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : V, 2 * eps := by
      apply sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hu j).1]
      exact (mul_le_mul_of_nonneg_left (heta j) (hu j).1).trans
        (mul_le_mul_of_nonneg_right (hu j).2 heps)
    _ = 2 * Fintype.card V * eps := by simp; ring

/-- The explicit Euclidean squared error `4 n³ eps²` needs no hidden spectral bound. -/
theorem star_error_sq_bound (u eta : V → V → ℝ) {eps : ℝ} (heps : 0 ≤ eps)
    (hu : ∀ i j, 0 ≤ u i j ∧ u i j ≤ 2) (heta : ∀ i j, |eta i j| ≤ eps) :
    sqNorm (fun i => ∑ j, u i j * eta i j) ≤
      4 * (Fintype.card V : ℝ) ^ 3 * eps ^ 2 := by
  calc
    sqNorm (fun i => ∑ j, u i j * eta i j) ≤
        ∑ _i : V, (2 * Fintype.card V * eps) ^ 2 := by
      apply sum_le_sum
      intro i _
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (star_error_bound (u i) (eta i) heps (hu i) (heta i)) 2
    _ = 4 * (Fintype.card V : ℝ) ^ 3 * eps ^ 2 := by simp; ring

/-- The final extra measurement contributes at most `2 n² eps` in L1. -/
theorem star_error_l1_bound (u eta : V → V → ℝ) {eps : ℝ} (heps : 0 ≤ eps)
    (hu : ∀ i j, 0 ≤ u i j ∧ u i j ≤ 2) (heta : ∀ i j, |eta i j| ≤ eps) :
    (∑ i, |∑ j, u i j * eta i j|) ≤ 2 * (Fintype.card V : ℝ) ^ 2 * eps := by
  calc
    (∑ i, |∑ j, u i j * eta i j|) ≤ ∑ _i : V, 2 * Fintype.card V * eps :=
      sum_le_sum fun i _ => star_error_bound (u i) (eta i) heps (hu i) (heta i)
    _ = 2 * (Fintype.card V : ℝ) ^ 2 * eps := by simp; ring

end Error

#print axioms quantize_error
#print axioms quantized_fractional_offset
#print axioms quantized_opposite_saturation
#print axioms quantized_positive_saturation
#print axioms signedPairs_skew
#print axioms star_error_sq_bound

end CutQueryComplexity.DirectedUnitST.Acceleration
