import CutQueryComplexity.GHReduction.LogArithmetic

/-! # Logarithmic envelopes for the chosen finite repetition counts -/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section

def sampleCoefficient (b : ℕ) : ℕ := 3 * (depthCoefficient b + b + 310)
def trialCoefficient (b : ℕ) : ℕ := 3 * (depthCoefficient b + sampleCoefficient b + b + 313)
def exponentCoefficient (b : ℕ) : ℕ := depthCoefficient b + sampleCoefficient b + b + 314

theorem confidenceGuideCoefficient_log_le (M n b : ℕ) :
    Nat.clog 2 (confidenceGuideCoefficient M n b) ≤ depthCoefficient b + 300 + 5 * reductionLog n M := by
  let L := reductionLog n M
  have hf := binaryLog_scaled_power_le (confidenceDepth_le n M b)
  have hn := (reductionLog_controls n M).1
  have hb : Nat.clog 2 (bucketCount M) ≤ 300 + L := by
    simpa only [pow_one, one_mul] using
      binaryLog_scaled_power_le (x := bucketCount M) (C := 300) (L := L) (k := 1)
        (by simpa only [pow_one] using (reductionLog_controls n M).2.2.2.2.2)
  have h1 := binaryLog_mul_le (confidenceDepth n b) n
  have h2 := binaryLog_mul_le (confidenceDepth n b * n) (bucketCount M)
  unfold confidenceGuideCoefficient
  omega

theorem confidenceSamples_le (M n b : ℕ) :
    confidenceSamples M n b ≤ sampleCoefficient b * reductionLog n M := by
  let L := reductionLog n M
  have hL : 1 ≤ L := reductionLog_one_le n M
  have hn := (reductionLog_controls n M).1
  have hc := confidenceGuideCoefficient_log_le M n b
  have hD := confidenceDenominator_log_le n M b
  have h1 := binaryLog_mul_le (confidenceGuideCoefficient M n b) n
  have h2 := binaryLog_add_one_le (confidenceGuideCoefficient M n b * n)
  have h3 := binaryLog_mul_le (confidenceGuideCoefficient M n b * n + 1) (confidenceDenominator n b)
  have hconstant : depthCoefficient b + 301 ≤ (depthCoefficient b + 301) * L := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (depthCoefficient b + 301) hL
  unfold confidenceSamples sampleCoefficient
  change _ ≤ 3 * (depthCoefficient b + b + 310) * L
  nlinarith

theorem confidenceBranchCoefficient_log_le (M n b : ℕ) :
    Nat.clog 2 (confidenceBranchCoefficient M n b) ≤
      depthCoefficient b + sampleCoefficient b + 301 + 8 * reductionLog n M := by
  let L := reductionLog n M
  have hc := confidenceGuideCoefficient_log_le M n b
  have hs : Nat.clog 2 (confidenceSamples M n b) ≤ sampleCoefficient b + L := by
    simpa only [pow_one, one_mul] using
      binaryLog_scaled_power_le (x := confidenceSamples M n b) (C := sampleCoefficient b) (L := L) (k := 1)
        (by simpa only [pow_one] using confidenceSamples_le M n b)
  have hn := (reductionLog_controls n M).1
  have hg : Nat.clog 2 (Nat.clog 2 (n + 1)) ≤ L :=
    (binaryLog_le_self _).trans (reductionLog_controls n M).2.1
  have hm : Nat.clog 2 (n - 2) ≤ L := (Nat.clog_mono_right 2 (Nat.sub_le n 2)).trans hn
  have h2 : Nat.clog 2 2 = 1 := by decide
  have hfirst := binaryLog_mul_le (confidenceGuideCoefficient M n b) (confidenceSamples M n b)
  have hinner := binaryLog_mul_le 2 (Nat.clog 2 (n + 1))
  have htail := binaryLog_mul_le (2 * Nat.clog 2 (n + 1)) (n - 2)
  have hall := binaryLog_mul_le (confidenceGuideCoefficient M n b * confidenceSamples M n b)
    (2 * Nat.clog 2 (n + 1) * (n - 2))
  unfold confidenceBranchCoefficient
  omega

theorem confidenceTrials_le (M n b : ℕ) :
    confidenceTrials M n b ≤ trialCoefficient b * reductionLog n M := by
  let L := reductionLog n M
  have hL : 1 ≤ L := reductionLog_one_le n M
  have hB := confidenceBranchCoefficient_log_le M n b
  have hD := confidenceDenominator_log_le n M b
  have h1 := binaryLog_add_one_le (confidenceBranchCoefficient M n b)
  have h2 := binaryLog_mul_le (confidenceBranchCoefficient M n b + 1) (confidenceDenominator n b)
  have hconstant : depthCoefficient b + sampleCoefficient b + 302 ≤
      (depthCoefficient b + sampleCoefficient b + 302) * L := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (depthCoefficient b + sampleCoefficient b + 302) hL
  unfold confidenceTrials trialCoefficient
  change _ ≤ 3 * (depthCoefficient b + sampleCoefficient b + b + 313) * L
  nlinarith

theorem confidenceExponent_le (M n b : ℕ) :
    confidenceExponent M n b ≤ exponentCoefficient b * reductionLog n M := by
  let L := reductionLog n M
  have hL : 1 ≤ L := reductionLog_one_le n M
  have hB := confidenceBranchCoefficient_log_le M n b
  have hD := confidenceDenominator_log_le n M b
  have hM : Nat.clog 2 (Nat.clog 2 (M + 1)) ≤ L :=
    (binaryLog_le_self _).trans (reductionLog_controls n M).2.2.2.1
  have h1 := binaryLog_mul_le (confidenceBranchCoefficient M n b) (Nat.clog 2 (M + 1))
  have h2 := binaryLog_add_one_le (confidenceBranchCoefficient M n b * Nat.clog 2 (M + 1))
  have h3 := binaryLog_mul_le (confidenceBranchCoefficient M n b * Nat.clog 2 (M + 1) + 1)
    (confidenceDenominator n b)
  have hconstant : depthCoefficient b + sampleCoefficient b + 302 ≤
      (depthCoefficient b + sampleCoefficient b + 302) * L := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (depthCoefficient b + sampleCoefficient b + 302) hL
  unfold confidenceExponent exponentCoefficient
  change _ ≤ (depthCoefficient b + sampleCoefficient b + b + 314) * L
  nlinarith

/-- A deliberately generous constant, depending only on confidence. Its
size lets one common integer scale absorb all fixed numerical coefficients. -/
def parameterCoefficient (b : ℕ) : ℕ :=
  400000000 + depthCoefficient b + sampleCoefficient b + trialCoefficient b + exponentCoefficient b + b + 11

def parameterScale (n M b : ℕ) : ℕ := parameterCoefficient b * reductionLog n M

theorem parameterScale_large (n M b : ℕ) : 400000000 ≤ parameterScale n M b := by
  have hL := reductionLog_one_le n M
  have hC : 400000000 ≤ parameterCoefficient b := by unfold parameterCoefficient; omega
  exact hC.trans (by simpa only [Nat.mul_one, parameterScale] using Nat.mul_le_mul_left (parameterCoefficient b) hL)

theorem parameterScale_controls (n M b : ℕ) :
    confidenceDepth n b ≤ parameterScale n M b ^ 3 ∧
    confidenceSamples M n b ≤ parameterScale n M b ∧
    confidenceTrials M n b ≤ parameterScale n M b ∧
    confidenceExponent M n b ≤ parameterScale n M b ∧
    Nat.clog 2 n ≤ parameterScale n M b ∧ Nat.clog 2 (n + 1) ≤ parameterScale n M b ∧
    Nat.clog 2 (n + 2) ≤ parameterScale n M b ∧ Nat.clog 2 (M + 1) ≤ parameterScale n M b ∧
    thresholdLevels n ≤ parameterScale n M b ∧ bucketCount M ≤ parameterScale n M b := by
  let C := parameterCoefficient b
  let L := reductionLog n M
  have hC : 400000000 ≤ C := by unfold C parameterCoefficient; omega
  have hL : 1 ≤ L := reductionLog_one_le n M
  have hd : depthCoefficient b ≤ C := by unfold C parameterCoefficient; omega
  have hs : sampleCoefficient b ≤ C := by unfold C parameterCoefficient; omega
  have ht : trialCoefficient b ≤ C := by unfold C parameterCoefficient; omega
  have he : exponentCoefficient b ≤ C := by unfold C parameterCoefficient; omega
  have hLC : L ≤ C * L := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right L (show 1 ≤ C by omega)
  obtain ⟨hn, hn1, hn2, hM, hl, hb⟩ := reductionLog_controls n M
  refine ⟨?_, (confidenceSamples_le M n b).trans (Nat.mul_le_mul_right L hs),
    (confidenceTrials_le M n b).trans (Nat.mul_le_mul_right L ht),
    (confidenceExponent_le M n b).trans (Nat.mul_le_mul_right L he),
    hn.trans hLC, hn1.trans hLC, hn2.trans hLC, hM.trans hLC, hl.trans hLC,
    hb.trans (Nat.mul_le_mul_right L (by omega : 300 ≤ C))⟩
  have hCC : C ≤ C ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < C) (by decide : 1 ≤ 3)
  calc
    _ ≤ depthCoefficient b * L ^ 3 := confidenceDepth_le n M b
    _ ≤ C ^ 3 * L ^ 3 := Nat.mul_le_mul_right _ (hd.trans hCC)
    _ = _ := by rw [parameterScale, mul_pow]

end
end CutQueryComplexity.GHReduction
