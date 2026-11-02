import CutQueryComplexity.ImplicitLP.GenericQuery.ScheduleBounds
import CutQueryComplexity.Sparsify.Asymptotic

/-! # Actual spectral calls and the three executed budget components -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Real
open PathFollowing (PowerEnvelope)
noncomputable section
variable {n me : ℕ} {D : Data n me} {P : Envelope}

/-- The actual spectral logarithm includes the allocated failure and arbitrary C. -/
theorem calibrated_spectral_log_le (HP : PublicHyp D P) :
    Sparsify.Dlog n P.C (publicDelta n P / 4096) (publicCallFailure D P) ≤
      256 * logHeight n P := by
  let H := height n P
  have hH : 2 ≤ H := HP.height_inputs.1
  have hH0 : 0 < H := by linarith
  have hΔ0 := (publicDelta_spec n P).1
  have hcall := (publicCallFailure_spec HP).1
  have hC0 : 0 < P.C := by linarith [HP.C_ge]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := HP.rank_ge; omega : 0 < n)
  have hζ0 := HP.ζ_pos
  obtain ⟨_, _, _, _, _, _, hΔ, _⟩ := base_scalar_envelopes HP
  have hc := publicCallCount_envelope HP
  have h2 : PowerEnvelope H 2 1 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have h4 : PowerEnvelope H 4 2 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have h4096 : PowerEnvelope H 4096 12 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have hnH : PowerEnvelope H (n : ℝ) 1 :=
    ⟨Nat.cast_nonneg _, by simpa only [pow_one] using HP.height_inputs.2.1⟩
  have hC : PowerEnvelope H P.C 1 :=
    ⟨hC0.le, by simpa only [pow_one] using HP.height_inputs.2.2.2.2.2.2.2⟩
  have hζ : PowerEnvelope H (1 / P.ζ) 1 :=
    ⟨by positivity, by simpa only [pow_one] using HP.height_inputs.2.2.2.2.2.2.1⟩
  have hnum : PowerEnvelope H
      (2 * P.C * n * 4096 * (1 / publicDelta n P) * 4 *
        ((publicCallCount D P : ℝ) + 1) * (1 / P.ζ)) 161 :=
    (((((((h2.mul hC).mul hnH).mul h4096).mul hΔ).mul h4).mul
      (hc.add hH (PowerEnvelope.one H))).mul hζ)
  have he : 2 * P.C * n / ((publicDelta n P / 4096) * publicCallFailure D P) =
      2 * P.C * n * 4096 * (1 / publicDelta n P) * 4 *
        ((publicCallCount D P : ℝ) + 1) * (1 / P.ζ) := by
    unfold publicCallFailure
    field_simp
    all_goals ring
  have hp : 0 < 2 * P.C * n / ((publicDelta n P / 4096) * publicCallFailure D P) := by positivity
  have hlog := (he.symm ▸ hnum).logarithm hH hp
  change log (2 * P.C * n / ((publicDelta n P / 4096) * publicCallFailure D P)) ≤
    (161 : ℝ) * logHeight n P at hlog
  change log (2 * P.C * n / ((publicDelta n P / 4096) * publicCallFailure D P)) ≤ _
  linarith [HP.logHeight_bounds.1]

/-- The literal Sparsify budget, not a caller-supplied primitive cap. -/
theorem calibrated_spectral_budget_le (HP : PublicHyp D P) :
    let Q := calibratedParams D P
    ((Q.rounds * Sparsify.levelBudget (n := n) Q.Kd Q.J Q.samples + 3 * n : ℕ) : ℝ) ≤
      2 ^ 216 * P.C * n * logHeight n P ^ 14 := by
  intro Q
  let L := logHeight n P
  have hΔ := publicDelta_spec n P
  have hf := publicCallFailure_spec HP
  have hΔ0 := hΔ.1
  have hs : Sparsify.Hyp n P.C (publicDelta n P / 4096) (publicCallFailure D P) :=
    ⟨HP.rank_ge, HP.C_ge, by positivity, by linarith [hΔ.2.2], hf.1, hf.2.1⟩
  have hb := Sparsify.budget_le hs
  have hL : 1 ≤ L := HP.logHeight_bounds.1
  have hC : 0 ≤ P.C := by linarith [HP.C_ge]
  have hi : 1 / (publicDelta n P / 4096) ≤ 2 ^ 56 * L ^ 3 := by
    have h := mul_le_mul_of_nonneg_left (publicDelta_inv_le HP)
      (by norm_num : (0 : ℝ) ≤ 4096)
    calc _ = 4096 * (1 / publicDelta n P) := by ring
      _ ≤ 4096 * (2 ^ 44 * L ^ 3) := h
      _ = _ := by ring
  have hlog := calibrated_spectral_log_le HP
  have hcost : ((Q.rounds * Sparsify.levelBudget (n := n) Q.Kd Q.J Q.samples + 3 * n : ℕ) : ℝ) ≤
      2 * 10 ^ 10 * P.C * (1 / (publicDelta n P / 4096)) ^ 2 * n *
        Sparsify.Dlog n P.C (publicDelta n P / 4096) (publicCallFailure D P) ^ 8 := by
    change ((Q.rounds * Sparsify.levelBudget (n := n) Q.Kd Q.J Q.samples + 3 * n : ℕ) : ℝ) ≤
      2 * 10 ^ 10 * P.C / (publicDelta n P / 4096) ^ 2 * n *
        Sparsify.Dlog n P.C (publicDelta n P / 4096) (publicCallFailure D P) ^ 8 at hb
    convert hb using 1 <;> ring
  refine hcost.trans ?_
  calc _ ≤ 2 * 10 ^ 10 * P.C * (2 ^ 56 * L ^ 3) ^ 2 * n * (256 * L) ^ 8 := by
        have hlog0 : 0 ≤ Sparsify.Dlog n P.C (publicDelta n P / 4096) (publicCallFailure D P) :=
          le_trans (by norm_num : (0 : ℝ) ≤ 2) hs.D_ge
        gcongr
    _ ≤ 2 ^ 216 * P.C * n * L ^ 14 := by
      have hnonneg : 0 ≤ P.C * (n : ℝ) * L ^ 14 := by positivity
      nlinarith

/-- All three budgets are the actual definitions used by solve on every oracle. -/
theorem calibrated_primitive_budgets (HP : PublicHyp D P) :
    let Q := calibratedParams D P
    (Q.newtonBudget : ℝ) ≤ 2 ^ 217 * P.C * n * logHeight n P ^ 14 ∧
    (Q.initialBudget : ℝ) ≤ 2 ^ 224 * P.C * n * logHeight n P ^ 15 ∧
    (Q.batchBudget : ℝ) ≤ 2 ^ 226 * P.C * n * logHeight n P ^ 15 := by
  intro Q
  let L := logHeight n P
  let E := publicEnvironment n P
  have hL : 1 ≤ L := HP.logHeight_bounds.1
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hC := HP.C_ge
  have hspec := calibrated_spectral_budget_le HP
  change ((Q.rounds * Sparsify.levelBudget (n := n) Q.Kd Q.J Q.samples + 3 * n : ℕ) : ℝ) ≤
    2 ^ 216 * P.C * n * L ^ 14 at hspec
  have hdet := newton_deterministic_budget_le HP
  have hJL := publicLewis_count_le HP
  have hsup := publicSupport_budget_le HP
  have hdet' : ((6 * n * (E.Brhs + E.k * E.Bmv + E.Brep) : ℕ) : ℝ) ≤
      2 ^ 23 * P.C * n * L ^ 14 := by
    refine hdet.trans ?_
    have he2 : L ^ 2 ≤ L ^ 14 := pow_le_pow_right₀ hL (by norm_num)
    calc _ ≤ 2 ^ 23 * n * L ^ 14 := by gcongr
      _ = 2 ^ 23 * 1 * n * L ^ 14 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hC (by norm_num)) (Nat.cast_nonneg n))
        (pow_nonneg hL0 _)
  have hJL' : (batchJL E P.a0 (publicDelta n P) : ℝ) ≤ 256 * L := hJL
  have hsup' : (((2 * (publicSupport n P).N + 2) *
      (((publicSupport n P).m + 3) * (6 * (publicSupport n P).B * n)) : ℕ) : ℝ) ≤
      2 ^ 34 * P.C * n * L ^ 15 := by
    refine hsup.trans ?_
    have he3 : L ^ 3 ≤ L ^ 15 := pow_le_pow_right₀ hL (by norm_num)
    calc _ ≤ 2 ^ 34 * n * L ^ 15 := by gcongr
      _ = 2 ^ 34 * 1 * n * L ^ 15 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hC (by norm_num)) (Nat.cast_nonneg n))
        (pow_nonneg hL0 _)
  have hnewton : (Q.newtonBudget : ℝ) ≤ 2 ^ 217 * P.C * n * L ^ 14 := by
    have hn0 : 0 ≤ P.C * (n : ℝ) * L ^ 14 := by positivity
    have he : Q.newtonBudget =
        (Q.rounds * Sparsify.levelBudget (n := n) Q.Kd Q.J Q.samples + 3 * n) +
          6 * n * (E.Brhs + E.k * E.Bmv + E.Brep) := rfl
    rw [he, Nat.cast_add]
    nlinarith only [hspec, hdet', hn0]
  have hinit : (Q.initialBudget : ℝ) ≤ 2 ^ 224 * P.C * n * L ^ 15 := by
    have hh := mul_le_mul hJL' hspec (Nat.cast_nonneg _) (by positivity : 0 ≤ 256 * L)
    change ((batchJL E P.a0 (publicDelta n P) *
      ((Q.rounds * Sparsify.levelBudget (n := n) Q.Kd Q.J Q.samples + 3 * n) + 0) : ℕ) : ℝ) ≤ _
    push_cast at hh ⊢
    nlinarith
  have hbatch : (Q.batchBudget : ℝ) ≤ 2 ^ 226 * P.C * n * L ^ 15 := by
    have hn0 : 0 ≤ P.C * (n : ℝ) * L ^ 15 := by positivity
    have h14 : L ^ 14 ≤ L ^ 15 := pow_le_pow_right₀ hL (by norm_num)
    have hcoef : 0 ≤ (2 : ℝ) ^ 217 * P.C * (n : ℝ) :=
      mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (le_trans (by norm_num) hC)) (Nat.cast_nonneg n)
    have hnewton' : (Q.newtonBudget : ℝ) ≤ 2 ^ 217 * P.C * n * L ^ 15 :=
      hnewton.trans (mul_le_mul_of_nonneg_left h14 hcoef)
    have he : Q.batchBudget = Q.newtonBudget + Q.initialBudget +
        (2 * (publicSupport n P).N + 2) * (((publicSupport n P).m + 3) *
          (6 * (publicSupport n P).B * n)) := rfl
    rw [he, Nat.cast_add, Nat.cast_add]
    nlinarith only [hnewton', hinit, hsup', hn0]
  exact ⟨hnewton, hinit, hbatch⟩

#print axioms calibrated_spectral_log_le
#print axioms calibrated_spectral_budget_le
#print axioms calibrated_primitive_budgets

end
end CutQueryComplexity.ImplicitLP.GenericQuery
