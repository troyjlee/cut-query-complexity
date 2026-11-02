import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Explicit fuel for multiplicative contraction of a finite family

One block of `ceil(4 / δ)` contractions halves the family. One more block
than its public binary bit bound makes its cardinality strictly less than
one. `Run` supplies the actual witness count and proves every contraction;
neither is an assumed phase oracle in the final program.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Phase

noncomputable section

def blockLength (δ : ℚ) : ℕ := ⌈4 / δ⌉₊

def contractionFuel (δ : ℚ) (bits : ℕ) : ℕ := blockLength δ * (bits + 1)

/-- An elementary reciprocal bound, including the endpoints η=0 and η=1. -/
theorem contraction_reciprocal {η : ℚ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (m : ℕ) :
    (1 - η) ^ m * (1 + (m : ℚ) * η) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
      have hstep : (1 - η) * (1 + ((m : ℚ) + 1) * η) ≤ 1 + (m : ℚ) * η := by
        have hsq := mul_nonneg (show (0 : ℚ) ≤ (m : ℚ) + 1 by positivity) (sq_nonneg η)
        nlinarith
      calc
        (1 - η) ^ (m + 1) * (1 + ((m + 1 : ℕ) : ℚ) * η) =
            (1 - η) ^ m * ((1 - η) * (1 + ((m : ℚ) + 1) * η)) := by
              rw [pow_succ, Nat.cast_add, Nat.cast_one]
              ring
        _ ≤ (1 - η) ^ m * (1 + (m : ℚ) * η) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg (sub_nonneg.mpr hη1) _)
        _ ≤ 1 := ih

theorem contraction_half {η : ℚ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (m : ℕ) (hm : (1 : ℚ) ≤ (m : ℚ) * η) : (1 - η) ^ m ≤ 1 / 2 := by
  have hpow : 0 ≤ (1 - η) ^ m := pow_nonneg (sub_nonneg.mpr hη1) _
  have h := contraction_reciprocal hη0 hη1 m
  have hmul := mul_le_mul_of_nonneg_left hm hpow
  nlinarith

theorem blockLength_mul {δ : ℚ} (hδ : 0 < δ) :
    (1 : ℚ) ≤ (blockLength δ : ℚ) * (δ / 4) := by
  have h : (4 : ℚ) / δ ≤ blockLength δ := Nat.le_ceil _
  have hm := (div_le_iff₀ hδ).mp h
  linarith

theorem blockLength_half {δ : ℚ} (hδ : 0 < δ) (hδ4 : δ ≤ 4) :
    (1 - δ / 4) ^ blockLength δ ≤ 1 / 2 := by
  exact contraction_half (by positivity) (by linarith) (blockLength δ) (blockLength_mul hδ)

theorem blockLength_pos {δ : ℚ} (hδ : 0 < δ) : 0 < blockLength δ := by
  have h := blockLength_mul hδ
  by_contra hn
  have hz : blockLength δ = 0 := by omega
  simp only [hz, Nat.cast_zero, zero_mul] at h
  norm_num at h

/-- The extra block handles equality at the power-of-two upper bound. -/
theorem contractionFuel_lt_one {δ : ℚ} (hδ : 0 < δ) (hδ4 : δ ≤ 4)
    (bits W : ℕ) (hW : W ≤ 2 ^ bits) :
    (1 - δ / 4) ^ contractionFuel δ bits * (W : ℚ) < 1 := by
  have hbase : 0 ≤ 1 - δ / 4 := by linarith
  have hhalf := blockLength_half hδ hδ4
  have hpow : (1 - δ / 4) ^ contractionFuel δ bits ≤ (1 / 2 : ℚ) ^ (bits + 1) := by
    rw [contractionFuel, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hbase _) hhalf _
  have hWQ : (W : ℚ) ≤ (2 : ℚ) ^ bits := by exact_mod_cast hW
  have hprod : (1 / 2 : ℚ) ^ bits * (2 : ℚ) ^ bits = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (1 - δ / 4) ^ contractionFuel δ bits * (W : ℚ) ≤
        (1 / 2 : ℚ) ^ (bits + 1) * (2 : ℚ) ^ bits :=
      mul_le_mul hpow hWQ (Nat.cast_nonneg W) (by positivity)
    _ = 1 / 2 := by
      rw [pow_succ]
      calc
        _ = ((1 / 2 : ℚ) ^ bits * (2 : ℚ) ^ bits) / 2 := by ring
        _ = 1 / 2 := by rw [hprod]
    _ < 1 := by norm_num

theorem contracted_card_eq_zero {δ : ℚ} (hδ : 0 < δ) (hδ4 : δ ≤ 4)
    (bits W T : ℕ) (hW : W ≤ 2 ^ bits)
    (hT : (T : ℚ) ≤ (1 - δ / 4) ^ contractionFuel δ bits * (W : ℚ)) : T = 0 := by
  have hlt : (T : ℚ) < 1 := hT.trans_lt (contractionFuel_lt_one hδ hδ4 bits W hW)
  have hn : T < 1 := by exact_mod_cast hlt
  omega

/-- The public fuel is bounded by the reciprocal contraction scale, with
the ceiling and extra terminal block charged explicitly. -/
theorem contractionFuel_le {δ : ℚ} (hδ : 0 < δ) (bits : ℕ) :
    (contractionFuel δ bits : ℚ) ≤ (4 / δ + 1) * ((bits : ℚ) + 1) := by
  have hceil : (blockLength δ : ℚ) ≤ 4 / δ + 1 :=
    (Nat.ceil_lt_add_one (by positivity : (0 : ℚ) ≤ 4 / δ)).le
  simpa only [contractionFuel, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    mul_le_mul_of_nonneg_right hceil (show (0 : ℚ) ≤ (bits : ℚ) + 1 by positivity)

end
end CutQueryComplexity.CanonicalST.Phase

#print axioms CutQueryComplexity.CanonicalST.Phase.contraction_reciprocal
#print axioms CutQueryComplexity.CanonicalST.Phase.blockLength_half
#print axioms CutQueryComplexity.CanonicalST.Phase.contractionFuel_lt_one
#print axioms CutQueryComplexity.CanonicalST.Phase.contracted_card_eq_zero
#print axioms CutQueryComplexity.CanonicalST.Phase.contractionFuel_le
