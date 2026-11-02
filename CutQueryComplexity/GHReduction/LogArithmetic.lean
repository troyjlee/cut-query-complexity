import CutQueryComplexity.GHReduction.ConfidenceParameters

/-! # Elementary logarithmic bounds for the actual public parameters -/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph OuterPivot

def reductionLog (n M : ℕ) : ℕ := 1 + Nat.clog 2 (n + M + 2)

theorem reductionLog_one_le (n M : ℕ) : 1 ≤ reductionLog n M := by
  unfold reductionLog
  omega

theorem binaryLog_mul_le (a b : ℕ) : Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) a) (Nat.le_pow_clog (by decide) b)

theorem binaryLog_pow_le (a k : ℕ) : Nat.clog 2 (a ^ k) ≤ k * Nat.clog 2 a := by
  apply Nat.clog_le_of_le_pow
  calc
    a ^ k ≤ (2 ^ Nat.clog 2 a) ^ k := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) a) k
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

theorem binaryLog_add_one_le (a : ℕ) : Nat.clog 2 (a + 1) ≤ Nat.clog 2 a + 1 := by
  apply Nat.clog_le_of_le_pow
  have ha := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) a
  have hpos : 1 ≤ 2 ^ Nat.clog 2 a := one_le_pow₀ (by decide)
  rw [pow_succ]
  omega

theorem binaryLog_le_self (a : ℕ) : Nat.clog 2 a ≤ a := by
  apply Nat.clog_le_of_le_pow
  induction a with
  | zero => norm_num
  | succ a ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ a := one_le_pow₀ (by decide)
      omega

theorem binaryLog_scaled_power_le {x C L k : ℕ} (hx : x ≤ C * L ^ k) :
    Nat.clog 2 x ≤ C + k * L := by
  calc
    _ ≤ Nat.clog 2 C + Nat.clog 2 (L ^ k) :=
      (Nat.clog_mono_right 2 hx).trans (binaryLog_mul_le C (L ^ k))
    _ ≤ C + k * L := Nat.add_le_add (binaryLog_le_self C)
      ((binaryLog_pow_le L k).trans (Nat.mul_le_mul_left k (binaryLog_le_self L)))

theorem real_log_nat_le_binaryLog (a : ℕ) (ha : 0 < a) :
    Real.log (a : ℝ) ≤ Nat.clog 2 a := by
  have hp : (a : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 a := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) a
  have h := Real.log_le_log (Nat.cast_pos.mpr ha) hp
  rw [Real.log_pow] at h
  have ht : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact h.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (Nat.clog 2 a)))

theorem reductionLog_controls (n M : ℕ) :
    Nat.clog 2 n ≤ reductionLog n M ∧ Nat.clog 2 (n + 1) ≤ reductionLog n M ∧
    Nat.clog 2 (n + 2) ≤ reductionLog n M ∧ Nat.clog 2 (M + 1) ≤ reductionLog n M ∧
    thresholdLevels n ≤ reductionLog n M ∧ bucketCount M ≤ 300 * reductionLog n M := by
  let L := reductionLog n M
  have hL : 1 ≤ L := reductionLog_one_le n M
  have hn : Nat.clog 2 n ≤ L := (Nat.clog_mono_right 2 (show n ≤ n + M + 2 by omega)).trans (by unfold L reductionLog; omega)
  have hn1 : Nat.clog 2 (n + 1) ≤ L := (Nat.clog_mono_right 2 (show n + 1 ≤ n + M + 2 by omega)).trans (by unfold L reductionLog; omega)
  have hn2 : Nat.clog 2 (n + 2) ≤ L := (Nat.clog_mono_right 2 (show n + 2 ≤ n + M + 2 by omega)).trans (by unfold L reductionLog; omega)
  have hM : Nat.clog 2 (M + 1) ≤ L := (Nat.clog_mono_right 2 (show M + 1 ≤ n + M + 2 by omega)).trans (by unfold L reductionLog; omega)
  have hl : thresholdLevels n ≤ L := by
    unfold thresholdLevels
    have h := binaryLog_mul_le 2 (n + M + 2)
    have hm := Nat.clog_mono_right 2 (show 2 * n ≤ 2 * (n + M + 2) by omega)
    have ht : Nat.clog 2 2 = 1 := by decide
    unfold L reductionLog
    omega
  have hb : bucketCount M ≤ 300 * L := by
    have h := binaryLog_mul_le 4 (M + 1)
    have ht : Nat.clog 2 4 = 2 := by decide
    unfold bucketCount
    omega
  exact ⟨hn, hn1, hn2, hM, hl, hb⟩

def depthCoefficient (b : ℕ) : ℕ := 128 * (b + 6)

theorem confidenceDenominator_log_le (n M b : ℕ) :
    Nat.clog 2 (confidenceDenominator n b) ≤ (b + 3) * reductionLog n M := by
  have hL := reductionLog_one_le n M
  have hn := (reductionLog_controls n M).2.2.1
  have h := binaryLog_mul_le 8 ((n + 2) ^ b)
  have hp := binaryLog_pow_le (n + 2) b
  have he : Nat.clog 2 8 = 3 := by decide
  unfold confidenceDenominator
  nlinarith

theorem confidenceDepth_le (n M b : ℕ) :
    confidenceDepth n b ≤ depthCoefficient b * reductionLog n M ^ 3 := by
  let L := reductionLog n M
  let D := confidenceDenominator n b
  have hL : 1 ≤ L := reductionLog_one_le n M
  have hn := (reductionLog_controls n M).1
  have hl := (reductionLog_controls n M).2.2.2.2.1
  have hD : Nat.clog 2 D ≤ (b + 3) * L := confidenceDenominator_log_le n M b
  have hnlog : Nat.clog 2 (n * n + 1) ≤ 3 * L := by
    have h1 := binaryLog_add_one_le (n * n)
    have h2 := binaryLog_mul_le n n
    omega
  have hlogNat : Nat.clog 2 ((n * n + 1) * D) ≤ (b + 6) * L := by
    have h := binaryLog_mul_le (n * n + 1) D
    nlinarith
  have hlog : Real.log (((n * n + 1) * D : ℕ) : ℝ) ≤ ((b + 6) * L : ℕ) :=
    (real_log_nat_le_binaryLog _ (Nat.mul_pos (by omega) (confidenceDenominator_pos n b))).trans
      (Nat.cast_le.mpr hlogNat)
  have hK : removalDenominator (thresholdLevels n) ≤ 128 * L ^ 2 := by
    have hh : thresholdLevels n + 1 ≤ 2 * L := by omega
    unfold removalDenominator
    calc
      32 * (thresholdLevels n + 1) ^ 2 ≤ 32 * (2 * L) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh 2)
      _ = _ := by ring
  unfold confidenceDepth depthFuel
  apply Nat.ceil_le.mpr
  have harg : (((n * n : ℕ) : ℝ) + 1) / (D : ℝ)⁻¹ = (((n * n + 1) * D : ℕ) : ℝ) := by
    simp only [div_inv_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [harg]
  have hnonneg : 0 ≤ Real.log (((n * n + 1) * D : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos (by omega) (confidenceDenominator_pos n b))
  calc
    _ ≤ ((128 * L ^ 2 : ℕ) : ℝ) * (((b + 6) * L : ℕ) : ℝ) :=
      mul_le_mul (Nat.cast_le.mpr hK) hlog hnonneg (by positivity)
    _ = _ := by simp only [depthCoefficient, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]; ring

end
end CutQueryComplexity.GHReduction
