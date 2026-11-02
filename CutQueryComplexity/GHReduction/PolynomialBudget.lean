import CutQueryComplexity.GHReduction.ReductionSparsifierBudget

/-! # Polynomial envelope of the actual counted oracle program

Every term expanded here is part of the program's hard cap: isolating and
threshold queries, guide recursion, all sampled guides, frontier auxiliary
instances, and the initial weighted sparsifier. The deliberately loose degree
22 is independent of all input and confidence parameters. Its coefficient
depends only on the requested confidence exponent.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CutQueryComplexity.GHReduction
noncomputable section
open WeightedGraph OuterPivot

theorem raise_query_envelope {a R K i j : ℕ} (hR : 1 ≤ R) (hij : i ≤ j)
    (ha : a ≤ R ^ i * K) : a ≤ R ^ j * K :=
  ha.trans (Nat.mul_le_mul_right K (Nat.pow_le_pow_right (by omega) hij))

theorem add_query_envelopes {a b R K i : ℕ} (hR : 2 ≤ R)
    (ha : a ≤ R ^ i * K) (hb : b ≤ R ^ i * K) : a + b ≤ R ^ (i + 1) * K := by
  calc
    _ ≤ R ^ i * K + R ^ i * K := Nat.add_le_add ha hb
    _ = 2 * R ^ i * K := by ring
    _ ≤ R * R ^ i * K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right (R ^ i) hR)
    _ = _ := by rw [pow_succ]; ring

theorem mul_query_envelopes {a f R K i j : ℕ} (hf : f ≤ R ^ i)
    (ha : a ≤ R ^ j * K) : f * a ≤ R ^ (i + j) * K := by
  calc
    _ ≤ R ^ i * (R ^ j * K) := Nat.mul_le_mul hf ha
    _ = _ := by rw [pow_add]; ring

theorem unit_query_envelope {R : ℕ} (hR : 1 ≤ R) (K i : ℕ) : K ≤ R ^ i * K := by
  have hp : 1 ≤ R ^ i := one_le_pow₀ hR
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right K hp

theorem confidenceFrontierBudget_envelope (M n b : ℕ) (Q : ℕ → ℕ) :
    frontierRoundBudget M Q n (confidenceSamples M n b) (confidenceTrials M n b)
      (thresholdLevels n) n (confidenceExponent M n b) (thresholdLevels n) ≤
        parameterScale n M b ^ 18 * (Q n + n) := by
  generalize hRdef : parameterScale n M b = R
  let K := Q n + n
  have hR : 400000000 ≤ R := by rw [← hRdef]; exact parameterScale_large n M b
  have hR1 : 1 ≤ R := by omega
  have hR2 : 2 ≤ R := by omega
  obtain ⟨_hf, hs, ht, he, hn, hn1, hn2, hM, hl, hb⟩ := parameterScale_controls n M b
  rw [hRdef] at hs ht he hn hn1 hn2 hM hl hb
  clear _hf hRdef
  have hpow (i j : ℕ) (hij : i ≤ j) : R ^ i ≤ R ^ j := Nat.pow_le_pow_right (by omega) hij
  have hpow1 (i : ℕ) : 1 ≤ R ^ i := one_le_pow₀ hR1
  have hplus : thresholdLevels n + 1 ≤ 2 * R := by omega
  have hnplus : Nat.clog 2 n + 3 ≤ 4 * R := by omega
  have hexp : confidenceExponent M n b + 1 ≤ 2 * R := by omega
  have hround : thresholdRoundBudget Q n (thresholdLevels n) ≤ R ^ 3 * K := by
    unfold thresholdRoundBudget
    calc
      _ ≤ (2 * R) * (4 * R) * K := by gcongr
      _ = 8 * R ^ 2 * K := by ring
      _ ≤ R * R ^ 2 * K := by gcongr; omega
      _ = _ := by ring
  have hpivot : stepBudget Q n (thresholdLevels n) ≤ R ^ 3 * K := hround
  have hrounds : thresholdRounds (thresholdLevels n) n (confidenceExponent M n b) ≤ R ^ 5 := by
    unfold thresholdRounds
    have h32 : 32 ≤ R ^ 2 := (show 32 ≤ R by omega).trans (by simpa only [pow_one] using hpow 1 2 (by decide))
    calc
      _ ≤ 8 * (2 * R) * ((2 * R) * R) := by gcongr
      _ = 32 * R ^ 3 := by ring
      _ ≤ R ^ 2 * R ^ 3 := Nat.mul_le_mul_right _ h32
      _ = _ := by ring
  have hthreshold : sourceThresholdBudget Q n (thresholdLevels n) n (confidenceExponent M n b) ≤ R ^ 8 * K :=
    mul_query_envelopes hrounds hround
  have hone : guideOneGlobalBudget Q n ≤ R ^ 3 * K := by
    have h23 : Nat.clog 2 n + 23 ≤ 24 * R := by omega
    have h10 : 10 ≤ 10 * R ^ 2 := Nat.mul_le_mul_left 10 (hpow1 2)
    have hinner : 10 + 2 * Nat.clog 2 (n + 1) * (Nat.clog 2 n + 23) ≤ 58 * R ^ 2 := by
      have hmul : 2 * Nat.clog 2 (n + 1) * (Nat.clog 2 n + 23) ≤ 2 * R * (24 * R) := by gcongr
      nlinarith
    unfold guideOneGlobalBudget
    calc
      _ ≤ 58 * R ^ 2 * K := Nat.mul_le_mul_right K hinner
      _ ≤ R * R ^ 2 * K := by gcongr; omega
      _ = _ := by ring
  have hsource : sourceSwitchBudget Q n ≤ R ^ 4 * K :=
    add_query_envelopes hR2 (unit_query_envelope hR1 K 3) hone
  have hswitch : guideSwitchBudget M Q n (thresholdLevels n) n (confidenceExponent M n b) ≤ R ^ 10 * K := by
    have hleft : Nat.clog 2 (M + 1) * sourceThresholdBudget Q n (thresholdLevels n) n
        (confidenceExponent M n b) ≤ R ^ 9 * K :=
      mul_query_envelopes (by simpa only [pow_one] using hM) hthreshold
    exact add_query_envelopes hR2 hleft (raise_query_envelope hR1 (by decide : 4 ≤ 9) hsource)
  have hnodeBase : guideNodeBudget Q n ≤ R ^ 2 * K := by
    unfold guideNodeBudget
    calc
      _ ≤ 4 * R * K := Nat.mul_le_mul_right K hnplus
      _ ≤ R * R * K := by gcongr; omega
      _ = _ := by ring
  have hprune : confidenceTrials M n b * guideOneGlobalBudget Q n ≤ R ^ 4 * K :=
    mul_query_envelopes (by simpa only [pow_one] using ht) hone
  have hnode : guideTwoNodeCost M Q n (confidenceTrials M n b) (thresholdLevels n) n
      (confidenceExponent M n b) ≤ R ^ 11 * K := by
    have hfirst : guideNodeBudget Q n + confidenceTrials M n b * guideOneGlobalBudget Q n ≤ R ^ 5 * K :=
      add_query_envelopes hR2 (raise_query_envelope hR1 (by decide : 2 ≤ 4) hnodeBase) hprune
    exact add_query_envelopes hR2 (raise_query_envelope hR1 (by decide : 5 ≤ 10) hfirst) hswitch
  have hnodeTail : guideTwoNodeCost M Q n (confidenceTrials M n b) (thresholdLevels n) n
      (confidenceExponent M n b) + 20 * K ≤ R ^ 12 * K := by
    have h20 : 20 ≤ R ^ 11 := (show 20 ≤ R by omega).trans (by simpa only [pow_one] using hpow 1 11 (by decide))
    exact add_query_envelopes hR2 hnode (Nat.mul_le_mul_right K h20)
  have htwo : guideTwoSharpBudget M Q n (confidenceTrials M n b) (thresholdLevels n) n
      (confidenceExponent M n b) (Nat.clog 2 (n + 1)) ≤ R ^ 14 * K := by
    have hmain : 2 * Nat.clog 2 (n + 1) *
        (guideTwoNodeCost M Q n (confidenceTrials M n b) (thresholdLevels n) n
          (confidenceExponent M n b) + 20 * K) ≤ 2 * R ^ 13 * K := by
      calc
        _ ≤ 2 * R * (R ^ 12 * K) := by gcongr
        _ = _ := by ring
    have h10 : 10 * K ≤ 10 * R ^ 13 * K := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 10 (unit_query_envelope hR1 K 13)
    unfold guideTwoSharpBudget
    calc
      _ ≤ 10 * R ^ 13 * K + 2 * R ^ 13 * K := Nat.add_le_add h10 hmain
      _ = 12 * R ^ 13 * K := by ring
      _ ≤ R * R ^ 13 * K := by gcongr; omega
      _ = _ := by ring
  have hsingle : singleSourceSharpBudget M Q n (confidenceSamples M n b) (confidenceTrials M n b)
      (thresholdLevels n) n (confidenceExponent M n b) ≤ R ^ 16 * K := by
    have hsamples : confidenceSamples M n b * guideTwoSharpBudget M Q n (confidenceTrials M n b)
        (thresholdLevels n) n (confidenceExponent M n b) (Nat.clog 2 (n + 1)) ≤ R ^ 15 * K :=
      mul_query_envelopes (by simpa only [pow_one] using hs) htwo
    exact mul_query_envelopes (by simpa only [pow_one] using hb) hsamples
  have hsourcePivot : sourcePivotSharpBudget M Q n (confidenceSamples M n b) (confidenceTrials M n b)
      (thresholdLevels n) n (confidenceExponent M n b) (thresholdLevels n) ≤ R ^ 17 * K :=
    add_query_envelopes hR2 hsingle (raise_query_envelope hR1 (by decide : 3 ≤ 16) hpivot)
  unfold frontierRoundBudget
  calc
    _ ≤ 3 * (R ^ 17 * K) := Nat.mul_le_mul_left 3 hsourcePivot
    _ ≤ R * (R ^ 17 * K) := Nat.mul_le_mul_right _ (by omega : 3 ≤ R)
    _ = _ := by ring

theorem confidenceBudget_envelope (V : Type) [Fintype V] (hn : 1 ≤ Fintype.card V)
    (M b : ℕ) (Q : ℕ → ℕ) :
    confidenceBudget V M Q b ≤ parameterScale (Fintype.card V) M b ^ 22 *
      (Q (Fintype.card V) + Fintype.card V) := by
  let n := Fintype.card V
  have hdepth := (parameterScale_controls n M b).1
  have hfrontier := confidenceFrontierBudget_envelope M n b Q
  have hsparse := reductionSparsifierBudget_envelope V hn M b Q
  change confidenceBudget V M Q b ≤ parameterScale n M b ^ 22 * (Q n + n)
  generalize hRdef : parameterScale n M b = R at *
  have hR : 400000000 ≤ R := by rw [← hRdef]; exact parameterScale_large n M b
  clear hRdef
  unfold confidenceBudget reductionBudget
  have hwhole : confidenceDepth n b * frontierRoundBudget M Q n (confidenceSamples M n b)
      (confidenceTrials M n b) (thresholdLevels n) n (confidenceExponent M n b) (thresholdLevels n) ≤
        R ^ 21 * (Q n + n) := mul_query_envelopes (i := 3) (j := 18) hdepth hfrontier
  exact add_query_envelopes (by omega : 2 ≤ R)
    (raise_query_envelope (by omega : 1 ≤ R) (by decide : 4 ≤ 21) hsparse) hwhole

def reductionPolynomialConstant (b : ℕ) : ℕ := parameterCoefficient b ^ 22

theorem confidenceBudget_polylog (V : Type) [Fintype V] (hn : 1 ≤ Fintype.card V)
    (M b : ℕ) (Q : ℕ → ℕ) :
    confidenceBudget V M Q b ≤ reductionPolynomialConstant b *
      (Fintype.card V + Q (Fintype.card V)) * (1 + Nat.clog 2 (Fintype.card V + M + 2)) ^ 22 := by
  apply (confidenceBudget_envelope V hn M b Q).trans
  exact le_of_eq (by unfold parameterScale reductionLog reductionPolynomialConstant; ring)

end
end CutQueryComplexity.GHReduction
