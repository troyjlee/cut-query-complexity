import CutQueryComplexity.GlobalSTReduction.Randomized
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Explicit and asymptotic size of the two caps (Phase 7)

With `ℓ(n) = ⌈log₂(n+2)⌉` (`budgetLog`), for every `n ≥ 2`, every `b` and every
charge `Q`:

* `detGlobalBudget n b Q ≤ 32 (b+1) (Q(n) ℓ³ + n ℓ²)` (`detGlobalBudget_le`);
* `repetitions n b ≤ repConst b · ℓ` with `repConst b = ⌈log₂(32(b+1))⌉ + b + 4`
  (`repetitions_le`);
* `randomGlobalBudget n b Q ≤ 32 (b+1) (repConst b + 1) (Q(n) + n) ℓ⁴`
  (`randomGlobalBudget_le`).

Since `ℓ(n) ≤ (3 / ln 2) ln n` for `n ≥ 2` (`budgetLog_le_log`), for fixed `b`
the caps are `O(Q(n) log³ n + n log² n)` and `O((Q(n) + n) log⁴ n)`
(`detGlobalBudget_isBigO`, `randomGlobalBudget_isBigO`). The statements are about
the actual natural-number caps of the public programs; no bound depends on edge
weights.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open Filter Asymptotics GHReduction GHReduction.Randomized

/-- `⌈log₂(n+2)⌉`. -/
def budgetLog (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

theorem le_pow_budgetLog (n : ℕ) : n + 2 ≤ 2 ^ budgetLog n :=
  Nat.le_pow_clog (by norm_num) _

theorem two_le_budgetLog {n : ℕ} (hn : 2 ≤ n) : 2 ≤ budgetLog n := by
  by_contra h
  have hle : 2 ^ budgetLog n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := le_pow_budgetLog n
  omega

theorem clog_le_budgetLog (n : ℕ) : Nat.clog 2 n ≤ budgetLog n :=
  Nat.clog_mono_right _ (by omega)

theorem thresholdLevels_le_budgetLog (n : ℕ) : thresholdLevels n ≤ budgetLog n + 1 := by
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]
  have := le_pow_budgetLog n
  omega

theorem budgetLog_le (n : ℕ) : budgetLog n ≤ n + 2 := by
  apply Nat.clog_le_of_le_pow
  exact (Nat.lt_two_pow_self).le

/-- The search budget, explicitly. -/
theorem searchBudget_le {n : ℕ} (hn : 2 ≤ n) (b : ℕ) (Q : ℕ → ℕ) :
    searchBudget n b Q ≤
      32 * (b + 1) * budgetLog n ^ 3 * Q n + 16 * (b + 1) * budgetLog n ^ 2 * n := by
  set ℓ := budgetLog n
  have h2 : 2 ≤ ℓ := two_le_budgetLog hn
  have hL : thresholdLevels n + 1 ≤ 2 * ℓ := by
    have := thresholdLevels_le_budgetLog n
    omega
  have hH : Nat.clog 2 n + 2 ≤ 2 * ℓ := by
    have := clog_le_budgetLog n
    omega
  have hT : trialCount n b = 8 * (b + 1) * ℓ := rfl
  unfold searchBudget levelBudget
  rw [hT]
  calc
    8 * (b + 1) * ℓ * (thresholdLevels n + 1) * ((Nat.clog 2 n + 2) * Q n + n)
        ≤ 8 * (b + 1) * ℓ * (2 * ℓ) * ((2 * ℓ) * Q n + n) := by gcongr
    _ = 32 * (b + 1) * ℓ ^ 3 * Q n + 16 * (b + 1) * ℓ ^ 2 * n := by ring

/-- `detGlobalBudget n b Q ≤ 32 (b+1) (Q(n) ℓ³ + n ℓ²)` for `n ≥ 2`. -/
theorem detGlobalBudget_le {n : ℕ} (hn : 2 ≤ n) (b : ℕ) (Q : ℕ → ℕ) :
    detGlobalBudget n b Q ≤ 32 * (b + 1) * (Q n * budgetLog n ^ 3 + n * budgetLog n ^ 2) := by
  have hs := searchBudget_le hn b Q
  have h2 := two_le_budgetLog hn
  have h1 : 1 ≤ 16 * (b + 1) * budgetLog n ^ 2 * n := by
    have : 1 ≤ budgetLog n ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : 1 ≤ n := by omega
    have : 1 ≤ 16 * (b + 1) := by omega
    calc 1 = 1 * 1 * 1 := by ring
      _ ≤ 16 * (b + 1) * budgetLog n ^ 2 * n := by gcongr
  unfold detGlobalBudget
  nlinarith

/-- The constant in `repetitions_le`. -/
def repConst (b : ℕ) : ℕ := Nat.clog 2 (32 * (b + 1)) + b + 4

theorem callCount_le {n : ℕ} (hn : 2 ≤ n) (b : ℕ) :
    max 1 (callCount n b) ≤ 32 * (b + 1) * (n + 2) ^ 3 := by
  set ℓ := budgetLog n
  have h2 : 2 ≤ ℓ := two_le_budgetLog hn
  have hℓ : ℓ ≤ n + 2 := budgetLog_le n
  have hL : thresholdLevels n + 1 ≤ 2 * ℓ := by
    have := thresholdLevels_le_budgetLog n
    omega
  have hH : Nat.clog 2 n + n ≤ 2 * (n + 2) := by
    have := clog_le_budgetLog n
    omega
  have hN : callCount n b ≤ 32 * (b + 1) * (n + 2) ^ 3 := by
    unfold callCount
    calc
      trialCount n b * (thresholdLevels n + 1) * (Nat.clog 2 n + n)
          ≤ (8 * (b + 1) * (n + 2)) * (2 * (n + 2)) * (2 * (n + 2)) := by
        unfold trialCount
        gcongr
        · exact hℓ
        · exact hL.trans (by omega)
      _ = 32 * (b + 1) * (n + 2) ^ 3 := by ring
  refine max_le ?_ hN
  have : 1 ≤ (n + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- `repetitions n b ≤ repConst b · ⌈log₂(n+2)⌉` for `n ≥ 2`. -/
theorem repetitions_le {n : ℕ} (hn : 2 ≤ n) (b : ℕ) :
    repetitions n b ≤ repConst b * budgetLog n := by
  set ℓ := budgetLog n
  set c := Nat.clog 2 (32 * (b + 1))
  have h2 : 2 ≤ ℓ := two_le_budgetLog hn
  have hX : max 1 (callCount n b) * (n + 2) ^ b ≤ 2 ^ (c + ℓ * (b + 3)) := by
    calc
      max 1 (callCount n b) * (n + 2) ^ b ≤ 32 * (b + 1) * (n + 2) ^ 3 * (n + 2) ^ b :=
        Nat.mul_le_mul_right _ (callCount_le hn b)
      _ = 32 * (b + 1) * (n + 2) ^ (b + 3) := by ring
      _ ≤ 2 ^ c * (2 ^ ℓ) ^ (b + 3) := by
        gcongr
        · exact Nat.le_pow_clog (by norm_num) _
        · exact le_pow_budgetLog n
      _ = 2 ^ (c + ℓ * (b + 3)) := by rw [← pow_mul, ← pow_add]
  have h3 : Nat.clog 3 (max 1 (callCount n b) * (n + 2) ^ b) ≤ c + ℓ * (b + 3) := by
    apply Nat.clog_le_of_le_pow
    exact hX.trans (Nat.pow_le_pow_left (by norm_num) _)
  unfold repetitions repConst
  have : 1 + c ≤ (1 + c) * ℓ := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-- `randomGlobalBudget n b Q ≤ 32 (b+1) (repConst b + 1) (Q(n) + n) ℓ⁴` for `n ≥ 2`. -/
theorem randomGlobalBudget_le {n : ℕ} (hn : 2 ≤ n) (b : ℕ) (Q : ℕ → ℕ) :
    randomGlobalBudget n b Q ≤
      32 * (b + 1) * (repConst b + 1) * (Q n + n) * budgetLog n ^ 4 := by
  set ℓ := budgetLog n
  have h2 : 2 ≤ ℓ := two_le_budgetLog hn
  have ha := repetitions_le hn b
  have hdet := detGlobalBudget_le hn b (amplifiedCost (repetitions n b) Q)
  have hQa : amplifiedCost (repetitions n b) Q n ≤ repConst b * ℓ * (Q n + n) :=
    Nat.mul_le_mul_right _ ha
  have hnℓ : n * ℓ ^ 2 ≤ (Q n + n) * ℓ ^ 4 := by
    have : ℓ ^ 2 ≤ ℓ ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : n ≤ Q n + n := Nat.le_add_left _ _
    gcongr
  unfold randomGlobalBudget
  calc
    detGlobalBudget n b (amplifiedCost (repetitions n b) Q)
        ≤ 32 * (b + 1) * (amplifiedCost (repetitions n b) Q n * ℓ ^ 3 + n * ℓ ^ 2) := hdet
    _ ≤ 32 * (b + 1) * (repConst b * ℓ * (Q n + n) * ℓ ^ 3 + (Q n + n) * ℓ ^ 4) := by
        gcongr
    _ = 32 * (b + 1) * (repConst b + 1) * (Q n + n) * ℓ ^ 4 := by ring

/-- `⌈log₂(n+2)⌉ ≤ (3 / ln 2) ln n` for `n ≥ 2`. -/
theorem budgetLog_le_log {n : ℕ} (hn : 2 ≤ n) :
    (budgetLog n : ℝ) ≤ (3 / Real.log 2) * Real.log (n : ℝ) := by
  have hn₂ : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog₂ : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM₁ : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hc := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hM₁)
  have hceil := Real.natCeil_logb_natCast 2 (n + 2)
  norm_num only [Nat.cast_ofNat] at hceil
  rw [hceil] at hc
  have hsize : (budgetLog n : ℝ) ≤ Real.logb 2 ((n + 2 : ℕ) : ℝ) + 1 := hc.le
  have hscaled := mul_le_mul_of_nonneg_right hsize hlog₂.le
  simp only [add_mul, one_mul, Real.logb, div_mul_cancel₀ _ hlog₂.ne'] at hscaled
  have hM : ((n + 2 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    linarith
  have hlogM := Real.log_le_log (by positivity) hM
  rw [Real.log_mul (by norm_num) hn₀.ne'] at hlogM
  have hlogn := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn₂
  have hfinal : (budgetLog n : ℝ) * Real.log 2 ≤ 3 * Real.log (n : ℝ) := by linarith
  calc
    _ ≤ (3 * Real.log (n : ℝ)) / Real.log 2 := (le_div_iff₀ hlog₂).mpr hfinal
    _ = _ := by ring

theorem three_div_log_two_ge_one : (1 : ℝ) ≤ 3 / Real.log 2 := by
  have hlog₂ : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [le_div_iff₀ hlog₂]
  linarith

/-- **`O(Q(n) log³ n + n log² n)` queries** with a deterministic family, for fixed `b`. -/
theorem detGlobalBudget_isBigO (b : ℕ) (Q : ℕ → ℕ) :
    (fun n : ℕ => (detGlobalBudget n b Q : ℝ)) =O[atTop]
      (fun n => (Q n : ℝ) * Real.log (n : ℝ) ^ 3 + (n : ℝ) * Real.log (n : ℝ) ^ 2) := by
  set C : ℝ := 3 / Real.log 2
  have hC : 1 ≤ C := three_div_log_two_ge_one
  apply isBigO_iff.mpr
  refine ⟨32 * (b + 1) * C ^ 3, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hℓ := budgetLog_le_log hn
  have hℓ0 : (0 : ℝ) ≤ budgetLog n := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ Q n := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  have hbound : (detGlobalBudget n b Q : ℝ) ≤
      32 * (b + 1) * ((Q n : ℝ) * (budgetLog n : ℝ) ^ 3 + (n : ℝ) * (budgetLog n : ℝ) ^ 2) := by
    exact_mod_cast detGlobalBudget_le hn b Q
  have h3 : (budgetLog n : ℝ) ^ 3 ≤ (C * Real.log n) ^ 3 := pow_le_pow_left₀ hℓ0 hℓ 3
  have h2 : (budgetLog n : ℝ) ^ 2 ≤ (C * Real.log n) ^ 2 := pow_le_pow_left₀ hℓ0 hℓ 2
  have hC2 : C ^ 2 ≤ C ^ 3 := pow_le_pow_right₀ hC (by norm_num)
  have hL2 : 0 ≤ Real.log (n : ℝ) ^ 2 := by positivity
  calc
    (detGlobalBudget n b Q : ℝ)
        ≤ 32 * (b + 1) * ((Q n : ℝ) * (C * Real.log n) ^ 3 + (n : ℝ) * (C * Real.log n) ^ 2) := by
          refine hbound.trans ?_
          gcongr
    _ = 32 * (b + 1) * (C ^ 3 * ((Q n : ℝ) * Real.log n ^ 3) +
          C ^ 2 * ((n : ℝ) * Real.log n ^ 2)) := by ring
    _ ≤ 32 * (b + 1) * (C ^ 3 * ((Q n : ℝ) * Real.log n ^ 3) +
          C ^ 3 * ((n : ℝ) * Real.log n ^ 2)) := by gcongr
    _ = 32 * (b + 1) * C ^ 3 * ((Q n : ℝ) * Real.log n ^ 3 + (n : ℝ) * Real.log n ^ 2) := by
          ring

/-- **`O((Q(n) + n) log⁴ n)` queries** with a randomized family, for fixed `b`. -/
theorem randomGlobalBudget_isBigO (b : ℕ) (Q : ℕ → ℕ) :
    (fun n : ℕ => (randomGlobalBudget n b Q : ℝ)) =O[atTop]
      (fun n => ((Q n : ℝ) + n) * Real.log (n : ℝ) ^ 4) := by
  set C : ℝ := 3 / Real.log 2
  apply isBigO_iff.mpr
  refine ⟨32 * (b + 1) * (repConst b + 1) * C ^ 4, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hℓ := budgetLog_le_log hn
  have hℓ0 : (0 : ℝ) ≤ budgetLog n := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  have hbound : (randomGlobalBudget n b Q : ℝ) ≤
      32 * (b + 1) * (repConst b + 1) * ((Q n : ℝ) + n) * (budgetLog n : ℝ) ^ 4 := by
    exact_mod_cast randomGlobalBudget_le hn b Q
  have h4 : (budgetLog n : ℝ) ^ 4 ≤ (C * Real.log n) ^ 4 := pow_le_pow_left₀ hℓ0 hℓ 4
  calc
    (randomGlobalBudget n b Q : ℝ)
        ≤ 32 * (b + 1) * (repConst b + 1) * ((Q n : ℝ) + n) * (C * Real.log n) ^ 4 := by
          refine hbound.trans ?_
          gcongr
    _ = 32 * (b + 1) * (repConst b + 1) * C ^ 4 * (((Q n : ℝ) + n) * Real.log n ^ 4) := by
          ring

end
end CutQueryComplexity.GlobalSTReduction
