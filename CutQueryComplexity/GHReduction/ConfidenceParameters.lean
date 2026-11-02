import CutQueryComplexity.GHReduction.OracleReduction

/-! # Explicit finite confidence parameters for the oracle reduction

Repetition counts are chosen after the finite depth and actual invocation
coefficients are known. Each of the three inner error terms is at most one
eighth of the target error. This avoids a circular choice in which the sample
count appears inside its own failure allowance. All logarithms are of public
natural numbers; no probability-dependent query truncation is introduced.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability OuterPivot

def confidenceDenominator (n b : ℕ) : ℕ := 8 * (n + 2) ^ b

theorem confidenceDenominator_pos (n b : ℕ) : 0 < confidenceDenominator n b := by
  unfold confidenceDenominator
  positivity

def confidenceDepth (n b : ℕ) : ℕ :=
  depthFuel (thresholdLevels n) (n * n) ((confidenceDenominator n b : ℝ)⁻¹)

def confidenceGuideCoefficient (M n b : ℕ) : ℕ :=
  confidenceDepth n b * n * bucketCount M

def confidenceSamples (M n b : ℕ) : ℕ :=
  3 * Nat.clog 2 ((confidenceGuideCoefficient M n b * n + 1) * confidenceDenominator n b)

def confidenceBranchCoefficient (M n b : ℕ) : ℕ :=
  confidenceGuideCoefficient M n b * confidenceSamples M n b *
    (2 * Nat.clog 2 (n + 1) * (n - 2))

def confidenceTrials (M n b : ℕ) : ℕ :=
  3 * Nat.clog 2 ((confidenceBranchCoefficient M n b + 1) * confidenceDenominator n b)

def confidenceExponent (M n b : ℕ) : ℕ :=
  Nat.clog 2 ((confidenceBranchCoefficient M n b * Nat.clog 2 (M + 1) + 1) *
    confidenceDenominator n b)

theorem threeQuarter_pow_log (N : ℕ) :
    ENNReal.ofReal (3 / 4 : ℝ) ^ (3 * Nat.clog 2 N) ≤ (N : ℝ≥0∞)⁻¹ := by
  have hblock : ENNReal.ofReal (3 / 4 : ℝ) ^ 3 ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.ofReal_pow (by norm_num), show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 : ℝ)⁻¹) by rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hpow : (N : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ Nat.clog 2 N := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) N
  calc
    _ = (ENNReal.ofReal (3 / 4 : ℝ) ^ 3) ^ Nat.clog 2 N := by rw [pow_mul]
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ Nat.clog 2 N := pow_le_pow_left₀ zero_le hblock _
    _ ≤ _ := by rw [← ENNReal.inv_pow]; exact ENNReal.inv_le_inv.mpr hpow

theorem inverse_pow_log (n N : ℕ) :
    (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ Nat.clog 2 N ≤ (N : ℝ≥0∞)⁻¹ := by
  have hn : (2 : ℝ≥0∞) ≤ (n + 2 : ℕ) := by exact_mod_cast (Nat.le_add_left 2 n)
  have hpow : (N : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ Nat.clog 2 N := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) N
  calc
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ Nat.clog 2 N :=
      pow_le_pow_left₀ zero_le (ENNReal.inv_le_inv.mpr hn) _
    _ ≤ _ := by rw [← ENNReal.inv_pow]; exact ENNReal.inv_le_inv.mpr hpow

theorem weighted_inverse_bound (A D : ℕ) :
    (A : ℝ≥0∞) * (((A + 1) * D : ℕ) : ℝ≥0∞)⁻¹ ≤ (D : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ ((A + 1 : ℕ) : ℝ≥0∞) * (((A + 1) * D : ℕ) : ℝ≥0∞)⁻¹ :=
      mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ A)) le_rfl
    _ = _ := by
      rw [Nat.cast_mul, ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
      exact ENNReal.mul_inv_cancel_left (by simp) (by simp)

theorem confidence_inner_error (M n b : ℕ) :
    (confidenceDepth n b : ℝ≥0∞) * ((n : ℝ≥0∞) *
      singleSourceError M n (confidenceSamples M n b) (confidenceTrials M n b) n
        (confidenceExponent M n b)) ≤ 3 * (confidenceDenominator n b : ℝ≥0∞)⁻¹ := by
  let D := confidenceDenominator n b
  let A := confidenceGuideCoefficient M n b * n
  let B := confidenceBranchCoefficient M n b
  let C := B * Nat.clog 2 (M + 1)
  have hA : (A : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ confidenceSamples M n b ≤ (D : ℝ≥0∞)⁻¹ :=
    (mul_le_mul' le_rfl (threeQuarter_pow_log ((A + 1) * D))).trans (weighted_inverse_bound A D)
  have hB : (B : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ confidenceTrials M n b ≤ (D : ℝ≥0∞)⁻¹ :=
    (mul_le_mul' le_rfl (threeQuarter_pow_log ((B + 1) * D))).trans (weighted_inverse_bound B D)
  have hC : (C : ℝ≥0∞) * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ confidenceExponent M n b ≤ (D : ℝ≥0∞)⁻¹ :=
    (mul_le_mul' le_rfl (inverse_pow_log n ((C + 1) * D))).trans (weighted_inverse_bound C D)
  calc
    _ = (A : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ confidenceSamples M n b +
        (B : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ confidenceTrials M n b +
        (C : ℝ≥0∞) * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ confidenceExponent M n b := by
      simp only [singleSourceError, guideTwoError, A, B, C, confidenceGuideCoefficient,
        confidenceBranchCoefficient, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ (D : ℝ≥0∞)⁻¹ + (D : ℝ≥0∞)⁻¹ + (D : ℝ≥0∞)⁻¹ := add_le_add (add_le_add hA hB) hC
    _ = _ := by ring

theorem confidence_sparsifier_error (V : Type) [Fintype V] (b : ℕ) :
    ENNReal.ofReal (baseB V ^ (-((b + 3 : ℕ) : ℝ))) ≤
      (confidenceDenominator (Fintype.card V) b : ℝ≥0∞)⁻¹ := by
  have hB : 0 < baseB V := by linarith [baseB_ge V]
  have hn : (Fintype.card V + 2 : ℕ) ≤ baseB V := by
    simp only [Nat.cast_add, Nat.cast_ofNat, baseB]
    have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    linarith
  have hcube : (8 : ℝ) ≤ baseB V ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (baseB_ge V) 3
  have hD : (confidenceDenominator (Fintype.card V) b : ℝ) ≤ baseB V ^ (b + 3) := by
    rw [confidenceDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    calc
      _ ≤ baseB V ^ b * baseB V ^ 3 := by
        simpa only [mul_comm] using mul_le_mul hcube (pow_le_pow_left₀ (by positivity) hn b) (by positivity) (by positivity)
      _ = _ := rfl
  have hDpos : (0 : ℝ) < confidenceDenominator (Fintype.card V) b := by
    exact_mod_cast confidenceDenominator_pos (Fintype.card V) b
  rw [Real.rpow_neg hB.le, Real.rpow_natCast]
  calc
    _ ≤ ENNReal.ofReal ((confidenceDenominator (Fintype.card V) b : ℝ)⁻¹) :=
      ENNReal.ofReal_le_ofReal (by simpa only [one_div] using one_div_le_one_div_of_le hDpos hD)
    _ = _ := by rw [ENNReal.ofReal_inv_of_pos hDpos, ENNReal.ofReal_natCast]

theorem confidence_total_error (n b : ℕ) :
    5 * (confidenceDenominator n b : ℝ≥0∞)⁻¹ ≤ (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  calc
    _ ≤ 8 * (confidenceDenominator n b : ℝ≥0∞)⁻¹ := mul_le_mul' (by norm_num) le_rfl
    _ = _ := by
      rw [confidenceDenominator, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
        ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by simp)),
        ENNReal.mul_inv_cancel_left (by norm_num) (by simp), ENNReal.inv_pow]

variable {V : Type} [Fintype V] [DecidableEq V]

def confidenceBudget (V : Type) [Fintype V] (M : ℕ) (Q : ℕ → ℕ) (b : ℕ) : ℕ :=
  reductionBudget V M Q ((b + 3 : ℕ) : ℝ) (confidenceSamples M (Fintype.card V) b)
    (confidenceTrials M (Fintype.card V) b) (thresholdLevels (Fintype.card V)) (Fintype.card V)
    (confidenceExponent M (Fintype.card V) b) (thresholdLevels (Fintype.card V))
    (confidenceDepth (Fintype.card V) b)

def confidenceReduction {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q) (b : ℕ) (r : V) :
    RTree (Finset V) ℝ (Option (CutTree V)) (confidenceBudget V M Q b) :=
  oracleReduction family ((b + 3 : ℕ) : ℝ) (confidenceSamples M (Fintype.card V) b)
    (confidenceTrials M (Fintype.card V) b) (thresholdLevels (Fintype.card V)) (Fintype.card V)
    (confidenceExponent M (Fintype.card V) b) (thresholdLevels (Fintype.card V))
    (confidenceDepth (Fintype.card V) b) r

/-- Finite-parameter endpoint: the full stated failure target, with the
actual explicit hard cap. The polynomial envelope is a separate theorem. -/
theorem confidenceReduction_failure {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hQ : SizeRegular (Fintype.card V) Q) (b : ℕ) (r : V)
    (G : WeightedGraph V) (hG : InputPromise M G) :
    mass ((confidenceReduction family b r).eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
      ((((Fintype.card V + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b) := by
  have hf : (0 : ℝ) < (confidenceDenominator (Fintype.card V) b : ℝ)⁻¹ := by
    exact inv_pos.mpr (Nat.cast_pos.mpr (confidenceDenominator_pos _ _))
  have h := oracleReduction_depthFuel_failure family hQ le_rfl ((b + 3 : ℕ) : ℝ) (by positivity)
    (confidenceSamples M (Fintype.card V) b) (confidenceTrials M (Fintype.card V) b)
    (thresholdLevels (Fintype.card V)) (confidenceExponent M (Fintype.card V) b)
    (thresholdLevels (Fintype.card V)) le_rfl le_rfl r G hG hf
  have hs := confidence_sparsifier_error V b
  have hi := confidence_inner_error M (Fintype.card V) b
  have he : ENNReal.ofReal ((confidenceDenominator (Fintype.card V) b : ℝ)⁻¹) =
      (confidenceDenominator (Fintype.card V) b : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (confidenceDenominator_pos _ _)),
      ENNReal.ofReal_natCast]
  apply h.trans
  apply le_trans (add_le_add hs (add_le_add hi (le_of_eq he)))
  convert confidence_total_error (Fintype.card V) b using 1 <;> ring

theorem confidenceReduction_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (b : ℕ) (r : V) (read : Finset V → ℝ) {out : Option (CutTree V) × ℕ}
    (hout : out ∈ (RTree.run read (confidenceReduction family b r)).support) :
    out.2 ≤ confidenceBudget V M Q b := RTree.cost_le _ read hout

end
end CutQueryComplexity.GHReduction
