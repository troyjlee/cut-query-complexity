import CutQueryComplexity.ImplicitLP.GenericQuery.PrimitiveBounds

/-! # Public phase and call counts for the executed generic solver -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Real
open PathFollowing (PowerEnvelope one_div_min_le_add)
noncomputable section
variable {n me : ℕ} {D : Data n me} {P : Envelope}

theorem calibratedStepSize_eq (D : Data n me) (P : Envelope) :
    (calibratedParams D P).stepSize =
      publicDelta n P / (32 * publicLogSize P * publicEnvelope n P) := by
  have hL := (publicLogSize_spec P).1
  have hL0 : 0 < publicLogSize P := by linarith
  have hT := publicEnvelope_one_le n P
  have hT0 : 0 < publicEnvelope n P := by linarith
  have hD := publicDelta_spec n P
  have ha0 : 0 ≤ 1 / (2 * publicLogSize P) := by positivity
  have hDT : publicDelta n P ≤ publicEnvelope n P := hD.2.2.trans hT
  have hc : (1 / (2 * publicLogSize P) * publicDelta n P) / (16 * publicEnvelope n P) ≤
      (1 / (2 * publicLogSize P)) / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hDT ha0]
  change min ((1 / (2 * publicLogSize P) * publicDelta n P) / (16 * publicEnvelope n P))
    ((1 / (2 * publicLogSize P)) / 16) = _
  rw [min_eq_left hc]
  field_simp
  all_goals ring

/-- The fixed step size has reciprocal sqrt(n) times a fifth power of a logarithm. -/
theorem calibratedStepSize_inv_le (HP : PublicHyp D P) :
    1 / (calibratedParams D P).stepSize ≤
      2 ^ 65 * Real.sqrt n * logHeight n P ^ 5 := by
  have hL0 : 0 < publicLogSize P := by linarith [(publicLogSize_spec P).1]
  have hT0 : 0 < publicEnvelope n P := by linarith [publicEnvelope_one_le n P]
  have hD := (publicDelta_spec n P).1
  have hl := HP.logHeight_bounds.1
  rw [calibratedStepSize_eq]
  have he : 1 / (publicDelta n P / (32 * publicLogSize P * publicEnvelope n P)) =
      32 * publicLogSize P * publicEnvelope n P * (1 / publicDelta n P) := by field_simp
  rw [he]
  calc _ ≤ 32 * (16 * logHeight n P) * (4096 * Real.sqrt n * logHeight n P) *
      (2 ^ 44 * logHeight n P ^ 3) := by
        gcongr
        · linarith [publicLogSize_le HP]
        · exact publicEnvelope_le HP
        · exact publicDelta_inv_le HP
    _ = _ := by ring

theorem calibratedPathScalars (HP : PublicHyp D P) :
    let Q := calibratedParams D P
    0 < Q.stepSize ∧ Q.stepSize ≤ 1 ∧ 0 < Q.switchTarget ∧ Q.switchTarget ≤ 1 := by
  intro Q
  have hL : 2 ≤ Q.L := (publicLogSize_spec P).1
  have hT : 1 ≤ Q.T := publicEnvelope_one_le n P
  have hD : 0 < Q.Δ := (publicDelta_spec n P).1
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast HP.rank_ge
  have hM : 0 < (publicEnvironment n P).Mbar := by change 0 < P.Mbar; linarith [HP.Mbar_ge_one]
  have hU : 0 < (publicEnvironment n P).U := by change 0 < P.U; linarith [HP.U_ge]
  have ha : 1 / (2 * Q.L) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine ⟨?_, ?_, ?_, min_le_left _ _⟩
  · unfold Params.stepSize
    positivity
  · exact (min_le_right _ _).trans (by linarith)
  · unfold Params.switchTarget
    positivity

/-- The switch target is derived from public parameters before any run. -/
theorem calibratedSwitch_envelope (HP : PublicHyp D P) :
    PowerEnvelope (height n P) (1 / (calibratedParams D P).switchTarget) 84 := by
  let H := height n P
  have hH : 2 ≤ H := HP.height_inputs.1
  obtain ⟨hL, hM, hU, _, _, hT, hΔ, _⟩ := base_scalar_envelopes HP
  have hL0 : 0 < publicLogSize P := by linarith [(publicLogSize_spec P).1]
  have hM0 : 0 < P.Mbar := by linarith [HP.Mbar_ge_one]
  have hU0 : 0 < P.U := by linarith [HP.U_ge]
  have hT0 : 0 < publicEnvelope n P := by linarith [publicEnvelope_one_le n P]
  have hΔ0 := (publicDelta_spec n P).1
  have hp : PowerEnvelope H
      (128 * publicLogSize P * P.Mbar * P.U ^ 2 * publicEnvelope n P * (1 / publicDelta n P)) 83 :=
    (((((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 128)
      (by norm_num : (128 : ℝ) ≤ 2 ^ 7)).mul hL).mul hM).mul (hU.pow 2)).mul hT).mul hΔ
  have hs := (calibratedPathScalars HP).2.2.1
  refine ((PowerEnvelope.one H).add hH hp).of_le (by positivity) ?_
  have hm := one_div_min_le_add (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 < (1 / (2 * publicLogSize P) * publicDelta n P / 2) /
      (publicEnvelope n P * (32 * P.Mbar * P.U ^ 2)))
  have he : 1 / ((1 / (2 * publicLogSize P) * publicDelta n P / 2) /
      (publicEnvelope n P * (32 * P.Mbar * P.U ^ 2))) =
      128 * publicLogSize P * P.Mbar * P.U ^ 2 * publicEnvelope n P * (1 / publicDelta n P) := by
    field_simp
    all_goals ring
  rw [he, div_one] at hm
  exact hm

theorem calibratedDownSteps_le (HP : PublicHyp D P) :
    ((calibratedParams D P).downSteps : ℝ) ≤
      2 ^ 74 * sqrt n * logHeight n P ^ 6 := by
  let Q := calibratedParams D P
  have hs := calibratedPathScalars HP
  have hr : 1 ≤ 1 / Q.switchTarget := (le_div_iff₀ hs.2.2.1).mpr (by linarith [hs.2.2.2])
  have hlog0 := log_nonneg hr
  have hlog : log (1 / Q.switchTarget) ≤ 90 * logHeight n P := by
    have hh := (calibratedSwitch_envelope HP).logarithm HP.height_inputs.1 (by positivity)
    change log (1 / Q.switchTarget) ≤ (84 : ℝ) * logHeight n P at hh
    linarith [HP.logHeight_bounds.1]
  have hstep : 2 / Q.stepSize ≤ 2 ^ 66 * sqrt n * logHeight n P ^ 5 := by
    have h := mul_le_mul_of_nonneg_left (calibratedStepSize_inv_le HP) (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1 <;> ring
  have hscale : 1 ≤ sqrt (n : ℝ) * logHeight n P ^ 6 := by
    have hn : (2 : ℝ) ≤ n := by exact_mod_cast HP.rank_ge
    have hsqrt : 1 ≤ sqrt (n : ℝ) := one_le_sqrt.mpr (by linarith)
    have hp : 1 ≤ logHeight n P ^ 6 := one_le_pow₀ HP.logHeight_bounds.1
    nlinarith
  have hL0 : 0 ≤ logHeight n P := by linarith [HP.logHeight_bounds.1]
  calc (Q.downSteps : ℝ) ≤ (2 / Q.stepSize) * log (1 / Q.switchTarget) + 1 :=
      phaseSteps_bound_step hr hs.1 hs.2.1
    _ ≤ (2 ^ 66 * sqrt n * logHeight n P ^ 5) * (90 * logHeight n P) + 1 := by
      have hbound0 : 0 ≤ (2 : ℝ) ^ 66 * sqrt n * logHeight n P ^ 5 :=
        mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (sqrt_nonneg _))
          (pow_nonneg hL0 _)
      exact add_le_add_left (mul_le_mul hstep hlog hlog0 hbound0) 1
    _ ≤ _ := by nlinarith

theorem calibratedInitialPhase_envelope (HP : PublicHyp D P) :
    let Q := calibratedParams D P
    PowerEnvelope (height n P) (1 / initialPhase Q Q.downSteps) 85 := by
  intro Q
  have hH := HP.height_inputs.1
  have hs := calibratedPathScalars HP
  have hr : 1 ≤ 1 / Q.switchTarget := (le_div_iff₀ hs.2.2.1).mpr (by linarith [hs.2.2.2])
  have he : 1 / initialPhase Q Q.downSteps = (1 + Q.stepSize) ^ Q.downSteps := by
    simp only [initialPhase, downSchedule, min_self, one_div, inv_inv]
  have hi : 1 / initialPhase Q Q.downSteps ≤ (1 / Q.switchTarget) * 2 := by
    rw [he]
    exact (phaseSteps_overshoot hr hs.1).trans
      (mul_le_mul_of_nonneg_left (by linarith [hs.2.1]) (by positivity))
  exact ((calibratedSwitch_envelope HP).mul
    (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) ≤ 2 ^ 1))).of_le
        (by rw [he]; exact pow_nonneg (by linarith [hs.1]) _) hi

theorem calibratedUpSteps_le (HP : PublicHyp D P) :
    ((calibratedParams D P).upSteps : ℝ) ≤
      2 ^ 74 * sqrt n * logHeight n P ^ 6 := by
  let Q := calibratedParams D P
  let H := height n P
  have hH : 2 ≤ H := HP.height_inputs.1
  have hs := calibratedPathScalars HP
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast HP.rank_ge
  have hε := HP.ε_pos
  have hinit0 : 0 < initialPhase Q Q.downSteps := by
    change 0 < 1 / (1 + Q.stepSize) ^ min Q.downSteps Q.downSteps
    have := hs.1
    positivity
  have hinit1 : initialPhase Q Q.downSteps ≤ 1 := by
    change 1 / (1 + Q.stepSize) ^ min Q.downSteps Q.downSteps ≤ 1
    rw [div_le_one (by have := hs.1; positivity)]
    exact one_le_pow₀ (by linarith [hs.1])
  have ht : 1 ≤ 8 * (n : ℝ) / P.ε := by
    rw [le_div_iff₀ hε]
    nlinarith [HP.ε_le]
  have hr : 1 ≤ (8 * (n : ℝ) / P.ε) / initialPhase Q Q.downSteps :=
    (one_le_div hinit0).mpr (hinit1.trans ht)
  obtain ⟨_, _, _, hεinv, _⟩ := base_scalar_envelopes HP
  have hnH : PowerEnvelope H (n : ℝ) 1 :=
    ⟨Nat.cast_nonneg _, by simpa only [pow_one] using HP.height_inputs.2.1⟩
  have hratio : PowerEnvelope H
      ((8 * (n : ℝ) / P.ε) / initialPhase Q Q.downSteps) 98 :=
    (((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 8)
      (by norm_num : (8 : ℝ) ≤ 2 ^ 3)).mul hnH).div hεinv).div
        (calibratedInitialPhase_envelope HP)
  have hlog : log ((8 * (n : ℝ) / P.ε) / initialPhase Q Q.downSteps) ≤
      104 * logHeight n P := by
    have hh := hratio.logarithm hH (by positivity)
    change log ((8 * (n : ℝ) / P.ε) / initialPhase Q Q.downSteps) ≤
      (98 : ℝ) * logHeight n P at hh
    linarith [HP.logHeight_bounds.1]
  have hstep : 2 / Q.stepSize ≤ 2 ^ 66 * sqrt n * logHeight n P ^ 5 := by
    have hh := mul_le_mul_of_nonneg_left (calibratedStepSize_inv_le HP) (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1 <;> ring
  have hscale : 1 ≤ sqrt (n : ℝ) * logHeight n P ^ 6 := by
    have hsqrt : 1 ≤ sqrt (n : ℝ) := one_le_sqrt.mpr (by linarith)
    have hp := one_le_pow₀ HP.logHeight_bounds.1 (n := 6)
    nlinarith
  have hlog0 := log_nonneg hr
  have hL0 : 0 ≤ logHeight n P := by linarith [HP.logHeight_bounds.1]
  calc (Q.upSteps : ℝ) ≤ (2 / Q.stepSize) *
        log ((8 * (n : ℝ) / P.ε) / initialPhase Q Q.downSteps) + 1 :=
      phaseSteps_bound_step hr hs.1 hs.2.1
    _ ≤ (2 ^ 66 * sqrt n * logHeight n P ^ 5) * (104 * logHeight n P) + 1 := by
      have hbound0 : 0 ≤ (2 : ℝ) ^ 66 * sqrt n * logHeight n P ^ 5 :=
        mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (sqrt_nonneg _))
          (pow_nonneg hL0 _)
      exact add_le_add_left (mul_le_mul hstep hlog hlog0 hbound0) 1
    _ ≤ _ := by nlinarith

theorem publicFinalCount_le (HP : PublicHyp D P) :
    (publicFinalCount n P : ℝ) ≤ 32 * logHeight n P := by
  let H := height n P
  have hH : 2 ≤ H := HP.height_inputs.1
  have hH1 : 1 ≤ H := by linarith
  have hM : 0 < P.Mbar := by linarith [HP.Mbar_ge_one]
  have hU : 0 < P.U := by linarith [HP.U_ge]
  have hε := HP.ε_pos
  have hΔ := publicDelta_spec n P
  have hgoal : 0 < P.ε / (8 * P.Mbar * P.U ^ 2) := by positivity
  obtain ⟨_, hMe, hUe, hεe, _⟩ := base_scalar_envelopes HP
  have hg : PowerEnvelope H (8 * P.Mbar * P.U ^ 2 / P.ε) 22 :=
    (((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 8)
      (by norm_num : (8 : ℝ) ≤ 2 ^ 3)).mul hMe).mul (hUe.pow 2)).div hεe
  have hge : 1 / (P.ε / (8 * P.Mbar * P.U ^ 2)) = 8 * P.Mbar * P.U ^ 2 / P.ε := by
    rw [one_div_div]
  have hi : PowerEnvelope H (publicDelta n P / (P.ε / (8 * P.Mbar * P.U ^ 2))) 22 := by
    have hh := ((PowerEnvelope.one H).of_le hΔ.1.le hΔ.2.2).div (hge.symm ▸ hg)
    exact hh
  have hm := ((PowerEnvelope.one H).weaken hH1 (by norm_num : 0 ≤ 22)).max hi
  have hp := PathFollowing.phaseSteps_one_pow_le (div_pos hΔ.1 hgoal)
  have hpow : (2 : ℝ) ^ publicFinalCount n P ≤ H ^ 23 :=
    hp.trans ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) ≤ 2 ^ 1)).mul hm).le_pow
  have hl := logb_le_logb_of_le (b := 2) (by norm_num)
    (by positivity : 0 < (2 : ℝ) ^ publicFinalCount n P) hpow
  rw [logb_pow, logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, logb_pow] at hl
  change (publicFinalCount n P : ℝ) ≤ 23 * logHeight n P at hl
  linarith [HP.logHeight_bounds.1]

/-- The failure allocation is noncircular and polynomial before taking logarithms. -/
theorem publicCallCount_envelope (HP : PublicHyp D P) :
    PowerEnvelope (height n P) (publicCallCount D P : ℝ) 95 := by
  let H := height n P
  let E := publicEnvironment n P
  let Q := calibratedParams D P
  have hH : 2 ≤ H := HP.height_inputs.1
  have hH1 : 1 ≤ H := by linarith
  have hnH : PowerEnvelope H (n : ℝ) 1 :=
    ⟨Nat.cast_nonneg _, by simpa only [pow_one] using HP.height_inputs.2.1⟩
  have hℓ : PowerEnvelope H (logHeight n P) 1 :=
    ⟨by linarith [HP.logHeight_bounds.1], by simpa only [pow_one] using HP.logHeight_bounds.2⟩
  have hJL : PowerEnvelope H (batchJL E P.a0 (publicDelta n P) : ℝ) 9 :=
    ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 256)
      (by norm_num : (256 : ℝ) ≤ 2 ^ 8)).mul hℓ).of_le
      (Nat.cast_nonneg _) (publicLewis_count_le HP)
  have hphase : PowerEnvelope H (2 ^ 74 * sqrt n * logHeight n P ^ 6) 81 :=
    ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 2 ^ 74)
      (le_rfl : (2 : ℝ) ^ 74 ≤ 2 ^ 74)).mul (hnH.sqrt hH1)).mul (hℓ.pow 6)
  have hd : PowerEnvelope H (Q.downSteps : ℝ) 81 :=
    hphase.of_le (Nat.cast_nonneg _) (calibratedDownSteps_le HP)
  have hu : PowerEnvelope H (Q.upSteps : ℝ) 81 :=
    hphase.of_le (Nat.cast_nonneg _) (calibratedUpSteps_le HP)
  have hf : PowerEnvelope H (Q.finalSteps : ℝ) 6 :=
    ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 32)
      (by norm_num : (32 : ℝ) ≤ 2 ^ 5)).mul hℓ).of_le
      (Nat.cast_nonneg _) (publicFinalCount_le HP)
  have h1 := PowerEnvelope.one H
  have hh := (hJL.add hH (((hd.add hH h1).add hH hu).mul (h1.add hH hJL))).add hH hf
  simp only [publicCallCount, solverSpectralCap, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  change PowerEnvelope H ((batchJL E P.a0 (publicDelta n P) : ℝ) +
    ((Q.downSteps : ℝ) + 1 + Q.upSteps) * (1 + (batchJL E P.a0 (publicDelta n P) : ℝ)) +
      (Q.finalSteps : ℝ)) 95
  exact hh

#print axioms calibratedStepSize_inv_le
#print axioms calibratedSwitch_envelope
#print axioms calibratedDownSteps_le
#print axioms calibratedUpSteps_le
#print axioms publicFinalCount_le
#print axioms publicCallCount_envelope

end
end CutQueryComplexity.ImplicitLP.GenericQuery
