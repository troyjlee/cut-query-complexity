import CutQueryComplexity.ImplicitLP.PathFollowing.Calibration

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! # Public scalar bounds for the actual finite solver

These estimates concern the parameters of `calibratedTerminalSolver` and
`calibratedGlobalMinCut`. Exact local arithmetic is free in this query model.
No full-state word-size premise is needed for their fixed query-tree indices.
-/

namespace CutQueryComplexity.ImplicitLP.PathFollowing

open Real
noncomputable section

/-- A logarithm used only to state estimates, not an additional algorithm input. -/
def queryLog (n : ℕ) : ℝ := Real.logb 2 n

theorem queryLog_one_le {n : ℕ} (hn : 2 ≤ n) : 1 ≤ queryLog n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0 : ℝ) < 2) hn'
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), queryLog] using h

theorem two_pow_ceil_logb_le {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ ≤ 2 * x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  calc (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ = (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ (Real.logb 2 x + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.ceil_lt_add_one hl).le
    _ = 2 * x := by
      rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx0,
        Real.rpow_one]
      ring

theorem publicRows_le {n : ℕ} (hn : 2 ≤ n) : publicRows n ≤ 4 * (n : ℝ) ^ 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold publicRows
  nlinarith

theorem publicLogSize_le {n : ℕ} (hn : 2 ≤ n) : publicLogSize n ≤ 16 * queryLog n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := queryLog_one_le hn
  have hM : 0 < 2 * publicRows n := by unfold publicRows; positivity
  have hrow := publicRows_le hn
  have hlogM : Real.logb 2 (2 * publicRows n) ≤ 3 + 2 * queryLog n := by
    calc _ ≤ Real.logb 2 ((2 : ℝ) ^ 3 * (n : ℝ) ^ 2) :=
        Real.logb_le_logb_of_le (by norm_num) hM (by norm_num; nlinarith)
      _ = 3 + 2 * queryLog n := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
        norm_num [queryLog]
  have hsize : publicLogSize n ≤ 2 * max 2 (Real.logb 2 (2 * publicRows n) + 1) :=
    two_pow_ceil_logb_le (by linarith [le_max_left (2 : ℝ) (Real.logb 2 (2 * publicRows n) + 1)])
  have hmax : max 2 (Real.logb 2 (2 * publicRows n) + 1) ≤ 8 * queryLog n := by
    apply max_le <;> linarith
  linarith

theorem publicEnvelope_le {n : ℕ} (hn : 2 ≤ n) :
    publicEnvelope n ≤ 4096 * Real.sqrt n * queryLog n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := (Real.one_le_sqrt).mpr (by linarith)
  have hl := queryLog_one_le hn
  have hL := publicLogSize_le hn
  have hmul : 1 ≤ Real.sqrt (n : ℝ) * queryLog n := by nlinarith
  have he : Real.sqrt (4 * (n : ℝ)) = 2 * Real.sqrt n := by
    rw [Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      exact (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)]
  unfold publicEnvelope publicMixed
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hL (Real.sqrt_nonneg (n : ℝ))]

/-- The potential-window branch is always the smaller branch of the chosen delta. -/
theorem calibratedDelta_eq_window {L M T : ℝ} (hL : 2 ≤ L) :
    calibratedDelta L M T =
      ((1 / (2 * L) / 2 ^ 20) * (1 / (2 * L)) /
        (96 * (max (Real.log (12 * M * T / (1 / (2 * L) / 8))) 0 + 1))) := by
  let a := 1 / (2 * L)
  let W := max (Real.log (12 * M * T / (a / 8))) 0 + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hW : 1 ≤ W := by dsimp [W]; linarith [le_max_right (Real.log (12 * M * T / (a / 8))) 0]
  apply min_eq_right
  change (a / 2 ^ 20) * a / (96 * W) ≤ a ^ 2 / 2 ^ 16
  apply (div_le_iff₀ (by positivity : 0 < 96 * W)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hW (sq_nonneg a)]

/-- An exact reciprocal formula makes the remaining logarithmic estimate explicit. -/
theorem publicDelta_inv (n : ℕ) :
    1 / publicDelta n = 96 * 2 ^ 20 * (2 * publicLogSize n) ^ 2 *
      (max (Real.log (192 * publicRows n * publicEnvelope n * publicLogSize n)) 0 + 1) := by
  have hL := (publicLogSize_spec n).1
  have hL0 : 0 < publicLogSize n := by linarith
  have he : 12 * publicRows n * publicEnvelope n / (1 / (2 * publicLogSize n) / 8) =
      192 * publicRows n * publicEnvelope n * publicLogSize n := by
    field_simp
    ring
  unfold publicDelta
  rw [calibratedDelta_eq_window hL, he]
  field_simp

theorem queryLog_le {n : ℕ} (hn : 2 ≤ n) : queryLog n ≤ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast n.lt_two_pow_self.le
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hn0 hn2
  simpa only [queryLog, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using h

theorem naturalLog_le_queryLog {n : ℕ} (hn : 2 ≤ n) : Real.log (n : ℝ) ≤ queryLog n := by
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he : Real.log (n : ℝ) = queryLog n * Real.log 2 := by
    unfold queryLog Real.logb
    rw [div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [he]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left htwo (by linarith [queryLog_one_le hn])

/-- The reciprocal batch accuracy is a cubic polynomial in the public logarithm. -/
theorem publicDelta_inv_le {n : ℕ} (hn : 2 ≤ n) :
    1 / publicDelta n ≤ 2 ^ 44 * queryLog n ^ 3 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl := queryLog_one_le hn
  have hln := queryLog_le hn
  have hL := publicLogSize_le hn
  have hL0 : 0 < publicLogSize n := by linarith [(publicLogSize_spec n).1]
  have hM0 : 0 < publicRows n := by unfold publicRows; positivity
  have hT0 : 0 < publicEnvelope n := by
    unfold publicEnvelope publicMixed
    positivity
  have hs : Real.sqrt (n : ℝ) ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hT : publicEnvelope n ≤ 4096 * (n : ℝ) ^ 2 := by
    calc _ ≤ 4096 * Real.sqrt n * queryLog n := publicEnvelope_le hn
      _ ≤ 4096 * (n : ℝ) * n := by gcongr
      _ = _ := by ring
  have hLp : publicLogSize n ≤ 16 * (n : ℝ) := hL.trans (by gcongr)
  have hB : 192 * publicRows n * publicEnvelope n * publicLogSize n ≤
      (2 : ℝ) ^ 26 * (n : ℝ) ^ 5 := by
    calc
      _ ≤ 192 * (4 * (n : ℝ) ^ 2) * (4096 * (n : ℝ) ^ 2) * (16 * (n : ℝ)) := by
        gcongr
        exact publicRows_le hn
      _ ≤ (2 : ℝ) ^ 26 * (n : ℝ) ^ 5 := by nlinarith [pow_nonneg hn0.le 5]
  have hlog : Real.log (192 * publicRows n * publicEnvelope n * publicLogSize n) ≤
      31 * queryLog n := by
    have h := Real.log_le_log (by positivity : 0 < 192 * publicRows n * publicEnvelope n * publicLogSize n) hB
    rw [Real.log_mul (x := (2 : ℝ) ^ 26) (y := (n : ℝ) ^ 5)
      (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
    have htwo : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hnat := naturalLog_le_queryLog hn
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hW : max (Real.log (192 * publicRows n * publicEnvelope n * publicLogSize n)) 0 + 1 ≤
      32 * queryLog n := by
    have hm : max (Real.log (192 * publicRows n * publicEnvelope n * publicLogSize n)) 0 ≤
        31 * queryLog n := max_le hlog (by linarith)
    linarith
  rw [publicDelta_inv]
  calc _ ≤ 96 * 2 ^ 20 * (2 * (16 * queryLog n)) ^ 2 * (32 * queryLog n) := by gcongr
    _ ≤ 2 ^ 44 * queryLog n ^ 3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ queryLog n) 3]

theorem publicEnvelope_one_le (n : ℕ) : 1 ≤ publicEnvelope n := by
  have hL0 : 0 ≤ publicLogSize n := by unfold publicLogSize; positivity
  unfold publicEnvelope publicMixed
  have h := mul_nonneg (by positivity : 0 ≤ 48 * (2 * publicLogSize n))
    (Real.sqrt_nonneg (4 * (n : ℝ)))
  linarith

theorem calibratedStepSize_eq (n : ℕ) (s t : Fin n) (ζ : ℝ) :
    (calibratedParams n s t ζ).stepSize =
      publicDelta n / (32 * publicLogSize n * publicEnvelope n) := by
  have hL := (publicLogSize_spec n).1
  have hL0 : 0 < publicLogSize n := by linarith
  have hT := publicEnvelope_one_le n
  have hT0 : 0 < publicEnvelope n := by linarith
  have hD := publicDelta_spec n
  have ha0 : 0 ≤ 1 / (2 * publicLogSize n) := by positivity
  have hDT : publicDelta n ≤ publicEnvelope n := hD.2.2.trans hT
  have hc : (1 / (2 * publicLogSize n) * publicDelta n) / (16 * publicEnvelope n) ≤
      (1 / (2 * publicLogSize n)) / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hDT ha0]
  change min ((1 / (2 * publicLogSize n) * publicDelta n) / (16 * publicEnvelope n))
    ((1 / (2 * publicLogSize n)) / 16) = _
  rw [min_eq_left hc]
  field_simp
  ring

/-- The fixed step size has reciprocal sqrt(n) times a fifth power of a logarithm. -/
theorem calibratedStepSize_inv_le {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (ζ : ℝ) :
    1 / (calibratedParams n s t ζ).stepSize ≤
      2 ^ 65 * Real.sqrt n * queryLog n ^ 5 := by
  have hL0 : 0 < publicLogSize n := by linarith [(publicLogSize_spec n).1]
  have hT0 : 0 < publicEnvelope n := by linarith [publicEnvelope_one_le n]
  have hD := (publicDelta_spec n).1
  have hl := queryLog_one_le hn
  rw [calibratedStepSize_eq]
  have he : 1 / (publicDelta n / (32 * publicLogSize n * publicEnvelope n)) =
      32 * publicLogSize n * publicEnvelope n * (1 / publicDelta n) := by field_simp
  rw [he]
  calc _ ≤ 32 * (16 * queryLog n) * (4096 * Real.sqrt n * queryLog n) *
      (2 ^ 44 * queryLog n ^ 3) := by
        gcongr
        · exact publicLogSize_le hn
        · exact publicEnvelope_le hn
        · exact publicDelta_inv_le hn
    _ = _ := by ring

theorem calibratedPathScalars {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (ζ : ℝ) :
    let P := calibratedParams n s t ζ
    0 < P.stepSize ∧ P.stepSize ≤ 1 ∧ 0 < P.switchTarget ∧ P.switchTarget ≤ 1 := by
  intro P
  have hL : 2 ≤ P.L := (publicLogSize_spec n).1
  have hT : 1 ≤ P.T := publicEnvelope_one_le n
  have hD : 0 < P.Δ := (publicDelta_spec n).1
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : 0 < (publicEnvironment n).Mbar := by change 0 < publicRows n; unfold publicRows; positivity
  have hU : 0 < (publicEnvironment n).U := by change 0 < publicWidth n; unfold publicWidth; positivity
  have ha : 1 / (2 * P.L) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine ⟨?_, ?_, ?_, min_le_left _ _⟩
  · unfold Params.stepSize
    positivity
  · exact (min_le_right _ _).trans (by linarith)
  · unfold Params.switchTarget
    positivity

theorem one_div_min_le_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / min a b ≤ 1 / a + 1 / b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    have : 0 ≤ 1 / b := by positivity
    linarith
  · rw [min_eq_right h]
    have : 0 ≤ 1 / a := by positivity
    linarith

theorem calibratedSwitch_inv_le {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (ζ : ℝ) :
    1 / (calibratedParams n s t ζ).switchTarget ≤ 2 ^ 80 * (n : ℝ) ^ 10 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL0 : 0 < publicLogSize n := by linarith [(publicLogSize_spec n).1]
  have hM0 : 0 < publicRows n := by unfold publicRows; positivity
  have hT0 : 0 < publicEnvelope n := by linarith [publicEnvelope_one_le n]
  have hU0 : 0 < publicWidth n := by unfold publicWidth; positivity
  have hD0 := (publicDelta_spec n).1
  have hl := queryLog_one_le hn
  have hln := queryLog_le hn
  have hs : Real.sqrt (n : ℝ) ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hL : publicLogSize n ≤ 16 * (n : ℝ) := (publicLogSize_le hn).trans (by gcongr)
  have hT : publicEnvelope n ≤ 4096 * (n : ℝ) ^ 2 := by
    calc _ ≤ 4096 * Real.sqrt n * queryLog n := publicEnvelope_le hn
      _ ≤ 4096 * (n : ℝ) * n := by gcongr
      _ = _ := by ring
  have hD : 1 / publicDelta n ≤ 2 ^ 44 * (n : ℝ) ^ 3 := (publicDelta_inv_le hn).trans (by gcongr)
  have hm := one_div_min_le_add (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 < (1 / (2 * publicLogSize n) * publicDelta n / 2) /
      (publicEnvelope n * (32 * publicRows n * publicWidth n ^ 2)))
  have he : 1 / ((1 / (2 * publicLogSize n) * publicDelta n / 2) /
      (publicEnvelope n * (32 * publicRows n * publicWidth n ^ 2))) =
      128 * publicLogSize n * publicRows n * publicWidth n ^ 2 * publicEnvelope n * (1 / publicDelta n) := by
    field_simp
    ring
  rw [he, div_one] at hm
  change 1 / (calibratedParams n s t ζ).switchTarget ≤ _ at hm
  have hp : 128 * publicLogSize n * publicRows n * publicWidth n ^ 2 * publicEnvelope n * (1 / publicDelta n) ≤
      2 ^ 73 * (n : ℝ) ^ 10 := by
    calc _ ≤ 128 * (16 * (n : ℝ)) * (4 * (n : ℝ) ^ 2) * (4 * (n : ℝ)) ^ 2 *
        (4096 * (n : ℝ) ^ 2) * (2 ^ 44 * (n : ℝ) ^ 3) := by
          unfold publicWidth
          gcongr
          exact publicRows_le hn
      _ = _ := by ring
  refine hm.trans ?_
  have hn10 : 1 ≤ (n : ℝ) ^ 10 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ n)
  nlinarith

/-- The actual initial phase has the required sqrt(n) times polylogarithmic count. -/
theorem calibratedDownSteps_le {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (ζ : ℝ) :
    ((calibratedParams n s t ζ).downSteps : ℝ) ≤
      2 ^ 74 * Real.sqrt n * queryLog n ^ 6 := by
  let P := calibratedParams n s t ζ
  have hs := calibratedPathScalars hn s t ζ
  have hswitch0 : 0 < P.switchTarget := hs.2.2.1
  have hstep0 : 0 < P.stepSize := hs.1
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl := queryLog_one_le hn
  have hr : 1 ≤ 1 / P.switchTarget := (le_div_iff₀ hs.2.2.1).mpr (by linarith [hs.2.2.2])
  have hcount := phaseSteps_bound_step hr hstep0 hs.2.1
  have hlog0 := Real.log_nonneg hr
  have hlog : Real.log (1 / P.switchTarget) ≤ 90 * queryLog n := by
    have hi := calibratedSwitch_inv_le hn s t ζ
    have h := Real.log_le_log (by positivity : 0 < 1 / P.switchTarget) hi
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
    have htwo : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hnat := naturalLog_le_queryLog hn
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hstep : 2 / P.stepSize ≤ 2 ^ 66 * Real.sqrt n * queryLog n ^ 5 := by
    have h := mul_le_mul_of_nonneg_left (calibratedStepSize_inv_le hn s t ζ) (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1 <;> ring
  have hscale : 1 ≤ Real.sqrt (n : ℝ) * queryLog n ^ 6 := by
    have hsq : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by linarith)
    have hp : 1 ≤ queryLog n ^ 6 := one_le_pow₀ hl
    nlinarith
  calc (P.downSteps : ℝ) ≤ (2 / P.stepSize) * Real.log (1 / P.switchTarget) + 1 := hcount
    _ ≤ (2 ^ 66 * Real.sqrt n * queryLog n ^ 5) * (90 * queryLog n) + 1 := by
      gcongr
    _ ≤ 2 ^ 74 * Real.sqrt n * queryLog n ^ 6 := by nlinarith

theorem calibratedInitialPhase_inv_le {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (ζ : ℝ) :
    let P := calibratedParams n s t ζ
    1 / initialPhase P P.downSteps ≤ 2 ^ 81 * (n : ℝ) ^ 10 := by
  intro P
  have hs := calibratedPathScalars hn s t ζ
  have hr : 1 ≤ 1 / P.switchTarget := (le_div_iff₀ hs.2.2.1).mpr (by linarith [hs.2.2.2])
  have h := phaseSteps_overshoot hr hs.1
  have he : 1 / initialPhase P P.downSteps = (1 + P.stepSize) ^ P.downSteps := by
    simp only [initialPhase, downSchedule, min_self, one_div, inv_inv]
  rw [he]
  calc _ ≤ (1 / P.switchTarget) * (1 + P.stepSize) := h
    _ ≤ (2 ^ 80 * (n : ℝ) ^ 10) * 2 := by
      apply mul_le_mul (calibratedSwitch_inv_le hn s t ζ) (by linarith [hs.2.1])
        (by linarith [hs.1]) (by positivity)
    _ = _ := by ring

/-- The true-cost phase has the same sqrt(n) times polylogarithmic count. -/
theorem calibratedUpSteps_le {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (ζ : ℝ) :
    ((calibratedParams n s t ζ).upSteps : ℝ) ≤
      2 ^ 74 * Real.sqrt n * queryLog n ^ 6 := by
  let P := calibratedParams n s t ζ
  have hs := calibratedPathScalars hn s t ζ
  have hstep0 : 0 < P.stepSize := hs.1
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl := queryLog_one_le hn
  have he : 8 * (n : ℝ) / (publicEnvironment n).ε = 2 ^ 10 * (n : ℝ) ^ 3 := by
    change 8 * (n : ℝ) / publicAccuracy n = _
    unfold publicAccuracy publicExtractionScale
    field_simp
    ring
  have hinit0 : 0 < initialPhase P P.downSteps := by
    change 0 < 1 / (1 + P.stepSize) ^ min P.downSteps P.downSteps
    positivity
  have hinit1 : initialPhase P P.downSteps ≤ 1 := by
    change 1 / (1 + P.stepSize) ^ min P.downSteps P.downSteps ≤ 1
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by linarith)
  have hr : 1 ≤ (8 * (n : ℝ) / (publicEnvironment n).ε) / initialPhase P P.downSteps := by
    rw [le_div_iff₀ hinit0, one_mul, he]
    have hp : 1 ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hi : (8 * (n : ℝ) / (publicEnvironment n).ε) / initialPhase P P.downSteps ≤
      2 ^ 91 * (n : ℝ) ^ 13 := by
    rw [div_eq_mul_one_div, he]
    calc
      _ ≤ (2 ^ 10 * (n : ℝ) ^ 3) * (2 ^ 81 * (n : ℝ) ^ 10) := by
        apply mul_le_mul_of_nonneg_left (calibratedInitialPhase_inv_le hn s t ζ) (by positivity)
      _ = _ := by ring
  have hlog : Real.log ((8 * (n : ℝ) / (publicEnvironment n).ε) / initialPhase P P.downSteps) ≤
      104 * queryLog n := by
    have h := Real.log_le_log (by linarith : 0 < (8 * (n : ℝ) / (publicEnvironment n).ε) /
      initialPhase P P.downSteps) hi
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
    have htwo : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hnat := naturalLog_le_queryLog hn
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hstep : 2 / P.stepSize ≤ 2 ^ 66 * Real.sqrt n * queryLog n ^ 5 := by
    have h := mul_le_mul_of_nonneg_left (calibratedStepSize_inv_le hn s t ζ) (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1 <;> ring
  have hscale : 1 ≤ Real.sqrt (n : ℝ) * queryLog n ^ 6 := by
    have hsq : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by linarith)
    have hp : 1 ≤ queryLog n ^ 6 := one_le_pow₀ hl
    nlinarith
  have hlog0 := Real.log_nonneg hr
  calc (P.upSteps : ℝ) ≤ (2 / P.stepSize) *
      Real.log ((8 * (n : ℝ) / (publicEnvironment n).ε) / initialPhase P P.downSteps) + 1 :=
      phaseSteps_bound_step hr hstep0 hs.2.1
    _ ≤ (2 ^ 66 * Real.sqrt n * queryLog n ^ 5) * (104 * queryLog n) + 1 := by gcongr
    _ ≤ 2 ^ 74 * Real.sqrt n * queryLog n ^ 6 := by nlinarith

/-- Uniform control of the dyadic factor used for final centering, also below ratio one. -/
theorem phaseSteps_one_pow_le {x : ℝ} (hx : 0 < x) :
    (2 : ℝ) ^ phaseSteps x 1 ≤ 2 * max 1 x := by
  by_cases hx1 : 1 ≤ x
  · have h := phaseSteps_overshoot hx1 (by norm_num : (0 : ℝ) < 1)
    simpa only [one_add_one_eq_two, max_eq_right hx1, mul_comm] using h
  · have hxle : x ≤ 1 := le_of_lt (lt_of_not_ge hx1)
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.le hxle
    have hzero : phaseSteps x 1 = 0 := by
      unfold phaseSteps
      apply Nat.ceil_eq_zero.mpr
      exact div_nonpos_of_nonpos_of_nonneg hlog (Real.log_nonneg (by norm_num))
    rw [hzero, pow_zero, max_eq_left hxle]
    norm_num

theorem publicFinalCount_pow_le {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) ^ publicFinalCount n ≤ 2 * max 1
      (publicDelta n / (publicAccuracy n / (8 * publicWidth n * (2 * n + 1 / 2)))) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := (publicDelta_spec n).1
  have hθ := (publicExtractionScale_spec hn).1
  apply phaseSteps_one_pow_le
  unfold publicAccuracy publicWidth
  positivity

/-- The final tolerance is an inverse polynomial once the public delta is bounded.
The centering count is eliminated; no repeated rounding error is compounded. -/
theorem publicTolerance_inv_le {n : ℕ} (hn : 2 ≤ n) :
    1 / (publicEnvironment n).η ≤
      2 ^ 17 * publicLogSize n / publicDelta n +
        128 * (1 / publicDelta n +
          8 * publicWidth n * (2 * n + 1 / 2) / publicAccuracy n) := by
  have hL := (publicLogSize_spec n).1
  have hL0 : 0 < publicLogSize n := by linarith
  have hD := (publicDelta_spec n).1
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hθ := (publicExtractionScale_spec hn).1
  have hε : 0 < publicAccuracy n := by unfold publicAccuracy; positivity
  have hU : 0 < publicWidth n := by unfold publicWidth; positivity
  have hgoal : 0 < publicAccuracy n / (8 * publicWidth n * (2 * n + 1 / 2)) := by positivity
  have hpow := publicFinalCount_pow_le hn
  have hratio : 0 ≤ publicDelta n /
      (publicAccuracy n / (8 * publicWidth n * (2 * n + 1 / 2))) := by positivity
  have hmax : max 1 (publicDelta n /
      (publicAccuracy n / (8 * publicWidth n * (2 * n + 1 / 2)))) ≤
      1 + publicDelta n / (publicAccuracy n / (8 * publicWidth n * (2 * n + 1 / 2))) :=
    max_le (by linarith) (by linarith)
  have htail : 1 / ((1 / 2 : ℝ) ^ publicFinalCount n * publicDelta n / 64) ≤
      128 * (1 / publicDelta n + 8 * publicWidth n * (2 * n + 1 / 2) / publicAccuracy n) := by
    have he : 1 / ((1 / 2 : ℝ) ^ publicFinalCount n * publicDelta n / 64) =
        64 * (2 : ℝ) ^ publicFinalCount n / publicDelta n := by
      rw [one_div_pow]
      field_simp
    rw [he]
    have h := mul_le_mul_of_nonneg_left (hpow.trans (mul_le_mul_of_nonneg_left hmax (by norm_num)))
      (by positivity : (0 : ℝ) ≤ 64 / publicDelta n)
    convert h using 1 <;> field_simp
    ring
  have hfirst : 1 / (1 / (2 * publicLogSize n) * publicDelta n / 2 ^ 16) =
      2 ^ 17 * publicLogSize n / publicDelta n := by field_simp
  change 1 / min (1 / (2 * publicLogSize n) * publicDelta n / 2 ^ 16)
    ((1 / 2 : ℝ) ^ publicFinalCount n * publicDelta n / 64) ≤ _
  rcases le_total (1 / (2 * publicLogSize n) * publicDelta n / 2 ^ 16)
    ((1 / 2 : ℝ) ^ publicFinalCount n * publicDelta n / 64) with hmin | hmin
  · rw [min_eq_left hmin, hfirst]
    have : 0 ≤ 128 * (1 / publicDelta n +
        8 * publicWidth n * (2 * n + 1 / 2) / publicAccuracy n) := by positivity
    linarith
  · rw [min_eq_right hmin]
    have : 0 ≤ 2 ^ 17 * publicLogSize n / publicDelta n := by positivity
    linarith

theorem publicGoal_inv_le {n : ℕ} (hn : 2 ≤ n) :
    8 * publicWidth n * (2 * n + 1 / 2) / publicAccuracy n ≤ 2 ^ 14 * (n : ℝ) ^ 4 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he : 8 * publicWidth n * (2 * n + 1 / 2) / publicAccuracy n =
      4096 * (n : ℝ) ^ 3 * (2 * n + 1 / 2) := by
    unfold publicWidth publicAccuracy publicExtractionScale
    field_simp
    ring
  rw [he]
  have h := mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ n) 3)
    (by linarith : (0 : ℝ) ≤ n - 1)
  nlinarith

theorem publicFinalCount_le {n : ℕ} (hn : 2 ≤ n) :
    (publicFinalCount n : ℝ) ≤ 20 * queryLog n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl := queryLog_one_le hn
  have hD := publicDelta_spec n
  have hθ := (publicExtractionScale_spec hn).1
  have hε : 0 < publicAccuracy n := by unfold publicAccuracy; positivity
  have hU : 0 < publicWidth n := by unfold publicWidth; positivity
  have hratio : publicDelta n /
      (publicAccuracy n / (8 * publicWidth n * (2 * n + 1 / 2))) ≤ 2 ^ 14 * (n : ℝ) ^ 4 := by
    calc
      _ = publicDelta n * (8 * publicWidth n * (2 * n + 1 / 2) / publicAccuracy n) := by
        field_simp
      _ ≤ 1 * (2 ^ 14 * (n : ℝ) ^ 4) :=
        mul_le_mul hD.2.2 (publicGoal_inv_le hn) (by positivity) (by norm_num)
      _ = _ := by ring
  have hmax : max 1 (publicDelta n /
      (publicAccuracy n / (8 * publicWidth n * (2 * n + 1 / 2)))) ≤ 2 ^ 14 * (n : ℝ) ^ 4 :=
    max_le (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn' 4]) hratio
  have hpow : (2 : ℝ) ^ publicFinalCount n ≤ (2 : ℝ) ^ 15 * (n : ℝ) ^ 4 := by
    refine (publicFinalCount_pow_le hn).trans ?_
    have h := mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1
    ring
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (by positivity : 0 < (2 : ℝ) ^ publicFinalCount n) hpow
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog
  change (publicFinalCount n : ℝ) ≤ 15 * 1 + 4 * queryLog n at hlog
  linarith

/-- The actual chosen direction tolerance is inverse polynomial in n, including its
final-centering branch. It is not exponentially small in the path length. -/
theorem publicTolerance_inv_polynomial {n : ℕ} (hn : 2 ≤ n) :
    1 / (publicEnvironment n).η ≤ 2 ^ 66 * (n : ℝ) ^ 4 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hl := queryLog_one_le hn
  have hln := queryLog_le hn
  have hL : publicLogSize n ≤ 16 * (n : ℝ) := (publicLogSize_le hn).trans (by gcongr)
  have hD := (publicDelta_spec n).1
  have hi : 1 / publicDelta n ≤ 2 ^ 44 * (n : ℝ) ^ 3 :=
    (publicDelta_inv_le hn).trans (by gcongr)
  have hpow : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg hn0 3) (by linarith : (0 : ℝ) ≤ n - 1)]
  have hfirst : 2 ^ 17 * publicLogSize n / publicDelta n ≤ 2 ^ 65 * (n : ℝ) ^ 4 := by
    calc _ = 2 ^ 17 * publicLogSize n * (1 / publicDelta n) := by ring
      _ ≤ 2 ^ 17 * (16 * (n : ℝ)) * (2 ^ 44 * (n : ℝ) ^ 3) := by
        gcongr
      _ = _ := by ring
  have htail : 128 * (1 / publicDelta n +
      8 * publicWidth n * (2 * n + 1 / 2) / publicAccuracy n) ≤ 2 ^ 52 * (n : ℝ) ^ 4 := by
    have hg := publicGoal_inv_le hn
    have hi' : 1 / publicDelta n ≤ 2 ^ 44 * (n : ℝ) ^ 4 := hi.trans (by gcongr)
    nlinarith [pow_nonneg hn0 4]
  exact (publicTolerance_inv_le hn).trans (by nlinarith [pow_nonneg hn0 4])

/-- The public shore-size balance for the global reduction. -/
def publicShoreSize (n : ℕ) : ℕ := min (n - 1) ⌈(n : ℝ) ^ (3 / 4 : ℝ)⌉₊

theorem publicShoreSize_spec {n : ℕ} (hn : 2 ≤ n) :
    0 < publicShoreSize n ∧ publicShoreSize n ≤ n - 1 ∧ publicShoreSize n ≤ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < ⌈(n : ℝ) ^ (3 / 4 : ℝ)⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn' _)
  unfold publicShoreSize
  exact ⟨lt_min (by omega) hp, min_le_left _ _, (min_le_left _ _).trans (Nat.sub_le _ _)⟩

theorem publicShoreSize_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ (3 / 4 : ℝ) / 2 ≤ publicShoreSize n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (3 / 4 : ℝ) ≤ n := by
    calc _ ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = n := Real.rpow_one _
  rw [publicShoreSize, Nat.cast_min, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  apply le_min
  · linarith
  · have h := Nat.le_ceil ((n : ℝ) ^ (3 / 4 : ℝ))
    have := Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (3 / 4 : ℝ)
    linarith

theorem publicShoreSize_upper {n : ℕ} (hn : 2 ≤ n) :
    (publicShoreSize n : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hceil := (Nat.ceil_lt_add_one (by linarith : 0 ≤ (n : ℝ) ^ (3 / 4 : ℝ))).le
  have hmin : (publicShoreSize n : ℝ) ≤ ⌈(n : ℝ) ^ (3 / 4 : ℝ)⌉₊ := by
    exact_mod_cast (min_le_right (n - 1) ⌈(n : ℝ) ^ (3 / 4 : ℝ)⌉₊)
  linarith

theorem publicShoreSize_ratio {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / publicShoreSize n ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh : (0 : ℝ) < publicShoreSize n := by exact_mod_cast (publicShoreSize_spec hn).1
  rw [div_le_iff₀ hh]
  have h := mul_le_mul_of_nonneg_left (publicShoreSize_lower hn)
    (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ))
  have he : 2 * (n : ℝ) ^ (1 / 4 : ℝ) * ((n : ℝ) ^ (3 / 4 : ℝ) / 2) = n := by
    calc _ = (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) := by ring
      _ = (n : ℝ) ^ ((1 / 4 : ℝ) + 3 / 4) := (Real.rpow_add hn0 _ _).symm
      _ = n := by norm_num
  rwa [he] at h

theorem publicRootCount_balanced {n : ℕ} (hn : 2 ≤ n) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (publicRootCount n (publicShoreSize n) ζ : ℝ) ≤
      2 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log (2 / ζ) + 1 := by
  have hh := publicShoreSize_spec hn
  have h := (publicRootCount_spec (by omega : 0 < n) hh.1 hh.2.2 hζ hζ1).2
  have hlog : 0 ≤ Real.log (2 / ζ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hζ]
    linarith
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right (publicShoreSize_ratio hn) hlog) le_rfl)

theorem publicLearnFuel_balanced {n : ℕ} (hn : 2 ≤ n) :
    (DirectedMincut.learnFuel (V := Fin n) (publicShoreSize n) : ℝ) ≤
      5 * (n : ℝ) ^ (7 / 4 : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have he : (n : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) ^ (7 / 4 : ℝ) := by
    calc _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + 3 / 4) := (Real.rpow_add hn0 _ _).symm
      _ = _ := by norm_num
  have hnPow : (n : ℝ) ≤ (n : ℝ) ^ (7 / 4 : ℝ) := by
    calc _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h := mul_le_mul_of_nonneg_left (publicShoreSize_upper hn) hn0.le
  unfold DirectedMincut.learnFuel
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem extractionSearchFactor_le {n : ℕ} (hn : 2 ≤ n) :
    ((3 + 3 * Sparsify.pK n : ℕ) : ℝ) ≤ 9 * queryLog n := by
  have hl := queryLog_one_le hn
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) := by change 0 ≤ queryLog n; linarith
  have hk : (Sparsify.pK n : ℝ) ≤ queryLog n + 1 := (Nat.ceil_lt_add_one hlog).le
  push_cast
  linarith

/-- The entire small-shore side of the actual global program has the target power. -/
theorem balancedLearningBudget_le {n : ℕ} (hn : 2 ≤ n) :
    ((2 * n +
      (DirectedMincut.learnFuel (V := Fin n) (publicShoreSize n) * (3 + 3 * Sparsify.pK n) +
       (DirectedMincut.learnFuel (V := Fin n) (publicShoreSize n) * (3 + 3 * Sparsify.pK n) + 1)) : ℕ) : ℝ) ≤
      96 * (n : ℝ) ^ (7 / 4 : ℝ) * queryLog n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := queryLog_one_le hn
  have hp : (n : ℝ) ≤ (n : ℝ) ^ (7 / 4 : ℝ) := by
    calc _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hmul := mul_le_mul (publicLearnFuel_balanced hn) (extractionSearchFactor_le hn)
    (Nat.cast_nonneg _) (by positivity : 0 ≤ 5 * (n : ℝ) ^ (7 / 4 : ℝ))
  have hscale : (n : ℝ) ^ (7 / 4 : ℝ) ≤ (n : ℝ) ^ (7 / 4 : ℝ) * queryLog n := by
    nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ n) (7 / 4 : ℝ)]
  push_cast at hmul ⊢
  nlinarith

/-- The global solver with every public tradeoff fixed from n and the failure allowance. -/
def balancedGlobalMinCut (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) :=
  calibratedGlobalMinCut n hn ζ (publicShoreSize n)

theorem balancedGlobalMinCut_success {n : ℕ} (hn : 2 ≤ n) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (G : DiGraph (Fin n)) (hG : G.Simple) :
    1 - ζ ≤ (balancedGlobalMinCut n hn ζ).successProb G.out (DirectedMincut.Opt G) :=
  calibratedGlobalMinCut_success hn hζ hζ1 G hG _
    (publicShoreSize_spec hn).1 (publicShoreSize_spec hn).2.2

/-- The all-oracle cap after balancing. The only unsimplified term here is the actual
terminal cap; no terminal complexity assertion is assumed. -/
theorem balancedGlobalMinCut_cost_split {n : ℕ} (hn : 2 ≤ n) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (read : Finset (Fin n) → ℕ)
    {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run read (balancedGlobalMinCut n hn ζ)).support) :
    let P := calibratedGlobalParams n hn (ζ / 2)
    (out.2 : ℝ) ≤ 96 * (n : ℝ) ^ (7 / 4 : ℝ) * queryLog n +
      (4 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log (2 / ζ) + 2) *
        (((2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
          (2 * n * (3 + 3 * Sparsify.pK n) + 1) : ℕ) : ℝ) := by
  intro P
  have hc := calibratedGlobalMinCut_cost_all_oracles n hn ζ (publicShoreSize n) read ho
  have hc' : (out.2 : ℝ) ≤
      ((2 * n + (DirectedMincut.learnFuel (V := Fin n) (publicShoreSize n) * (3 + 3 * Sparsify.pK n) +
        (DirectedMincut.learnFuel (V := Fin n) (publicShoreSize n) * (3 + 3 * Sparsify.pK n) + 1)) : ℕ) : ℝ) +
      2 * (publicRootCount n (publicShoreSize n) ζ : ℝ) *
        (((2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
          (2 * n * (3 + 3 * Sparsify.pK n) + 1) : ℕ) : ℝ) := by exact_mod_cast hc
  refine hc'.trans (add_le_add (balancedLearningBudget_le hn) ?_)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  have := publicRootCount_balanced hn hζ hζ1
  linarith

end
end CutQueryComplexity.ImplicitLP.PathFollowing

#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicLogSize_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicEnvelope_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicDelta_inv
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicDelta_inv_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedStepSize_inv_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedSwitch_inv_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedDownSteps_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedUpSteps_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicFinalCount_pow_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicFinalCount_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicTolerance_inv_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicTolerance_inv_polynomial
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicShoreSize_spec
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicShoreSize_lower
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicShoreSize_upper
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicShoreSize_ratio
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicRootCount_balanced
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicLearnFuel_balanced
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.balancedLearningBudget_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.balancedGlobalMinCut_success
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.balancedGlobalMinCut_cost_split
