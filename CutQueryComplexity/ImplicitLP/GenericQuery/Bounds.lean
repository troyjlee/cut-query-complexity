import CutQueryComplexity.ImplicitLP.GenericQuery.Calibration
import CutQueryComplexity.ImplicitLP.PathFollowing.PrimitiveBudget

/-! # Scalar bounds in the original public input envelope

Only logarithms of the magnitude envelope enter the primitive query counts.
The polynomial inequalities here are proved for the chosen scalars, not
accepted as a cost certificate from the caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Real
open PathFollowing (PowerEnvelope two_pow_ceil_logb_le calibratedDelta_eq_window
  one_div_min_le_add phaseSteps_one_pow_le)
noncomputable section
variable {n me : ℕ} {D : Data n me} {P : Envelope}

def height (n : ℕ) (P : Envelope) : ℝ := 2 * P.Npub n
def logHeight (n : ℕ) (P : Envelope) : ℝ := logb 2 (height n P)

theorem PublicHyp.Mbar_ge_one (H : PublicHyp D P) : 1 ≤ P.Mbar := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast H.rank_ge
  have hq : 1 ≤ (n : ℝ) * (n - 1) / 2 := by nlinarith
  have hC : 0 ≤ P.C := by linarith [H.C_ge]
  have hc : P.C ≤ P.C * ((n : ℝ) * (n - 1) / 2) := le_mul_of_one_le_right hC hq
  have hb := H.rows_bound
  have hm : (0 : ℝ) ≤ me := Nat.cast_nonneg _
  nlinarith [H.C_ge]

theorem PublicHyp.height_inputs (H : PublicHyp D P) :
    2 ≤ height n P ∧ (n : ℝ) ≤ height n P ∧ P.Mbar ≤ height n P ∧
      P.U ≤ height n P ∧ 1 / P.ε ≤ height n P ∧ 1 / P.a0 ≤ height n P ∧
      1 / P.ζ ≤ height n P ∧ P.C ≤ height n P := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast H.rank_ge
  have hM := H.Mbar_ge_one
  have he : 0 < P.ε⁻¹ := inv_pos.mpr H.ε_pos
  have ha : 0 < P.a0⁻¹ := inv_pos.mpr H.a0_pos
  have hz : 0 < P.ζ⁻¹ := inv_pos.mpr H.ζ_pos
  have hq : 1 ≤ (n : ℝ) * (n - 1) / 2 := by nlinarith
  have hCM : P.C ≤ P.Mbar := by
    have hC : 0 ≤ P.C := by linarith [H.C_ge]
    have hc := le_mul_of_one_le_right hC hq
    have hm : (0 : ℝ) ≤ me := Nat.cast_nonneg _
    nlinarith [H.rows_bound]
  dsimp [height, Envelope.Npub]
  simp only [one_div]
  constructor <;> try linarith [H.U_ge]
  constructor <;> try linarith [H.U_ge]
  constructor <;> try linarith [H.U_ge]
  constructor <;> try linarith [H.U_ge]
  constructor <;> try linarith [H.U_ge]
  constructor <;> try linarith [H.U_ge]
  constructor <;> linarith [H.U_ge]

theorem PublicHyp.logHeight_bounds (H : PublicHyp D P) :
    1 ≤ logHeight n P ∧ logHeight n P ≤ height n P := by
  have hB := H.height_inputs.1
  have hB0 : 0 < height n P := by linarith
  have htwo0 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  constructor
  · have h := logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0 : ℝ) < 2) hB
    simpa only [logb_self_eq_one (by norm_num : (1 : ℝ) < 2), logHeight] using h
  · have ht : log (2 : ℝ) ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlog := log_le_sub_one_of_pos (div_pos hB0 (by norm_num : (0 : ℝ) < 2))
    rw [log_div hB0.ne' (by norm_num)] at hlog
    unfold logHeight logb
    rw [div_le_iff₀ htwo0]
    nlinarith [Sparsify.log_two_ge, mul_le_mul_of_nonneg_left Sparsify.log_two_ge hB0.le]

theorem publicLogSize_le (H : PublicHyp D P) : publicLogSize P ≤ 8 * logHeight n P := by
  have hM0 : 0 < P.Mbar := by linarith [H.Mbar_ge_one]
  have hB := H.height_inputs
  have hℓ := H.logHeight_bounds.1
  have hlog : logb 2 (2 * P.Mbar) ≤ 1 + logHeight n P := by
    calc _ ≤ logb 2 (2 * height n P) :=
        logb_le_logb_of_le (by norm_num) (by positivity) (by linarith [hB.2.2.1])
      _ = 1 + logHeight n P := by
        rw [logb_mul (by norm_num) (by linarith [hB.1]), logb_self_eq_one (by norm_num)]
        rfl
  have hsize : publicLogSize P ≤ 2 * max 2 (logb 2 (2 * P.Mbar) + 1) :=
    two_pow_ceil_logb_le (by linarith [le_max_left (2 : ℝ) (logb 2 (2 * P.Mbar) + 1)])
  have hmax : max 2 (logb 2 (2 * P.Mbar) + 1) ≤ 4 * logHeight n P := by
    apply max_le <;> linarith
  linarith

theorem publicEnvelope_one_le (n : ℕ) (P : Envelope) : 1 ≤ publicEnvelope n P := by
  have hL : 0 ≤ publicLogSize P := by unfold publicLogSize; positivity
  have hs := sqrt_nonneg (4 * (n : ℝ))
  have hp : 0 ≤ publicMixed P * sqrt (4 * (n : ℝ)) := by
    unfold publicMixed
    positivity
  unfold publicEnvelope
  linarith

theorem publicEnvelope_le (H : PublicHyp D P) :
    publicEnvelope n P ≤ 4096 * sqrt n * logHeight n P := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast H.rank_ge
  have hs : 1 ≤ sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hl := H.logHeight_bounds.1
  have hL := publicLogSize_le H
  have hmul : 1 ≤ sqrt (n : ℝ) * logHeight n P := by nlinarith
  have he : sqrt (4 * (n : ℝ)) = 2 * sqrt n := by
    rw [sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  unfold publicEnvelope publicMixed
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hL (sqrt_nonneg (n : ℝ))]

theorem publicDelta_inv (n : ℕ) (P : Envelope) :
    1 / publicDelta n P = 96 * 2 ^ 20 * (2 * publicLogSize P) ^ 2 *
      (max (log (192 * P.Mbar * publicEnvelope n P * publicLogSize P)) 0 + 1) := by
  have hL := (publicLogSize_spec P).1
  have hL0 : 0 < publicLogSize P := by linarith
  have he : 12 * P.Mbar * publicEnvelope n P / (1 / (2 * publicLogSize P) / 8) =
      192 * P.Mbar * publicEnvelope n P * publicLogSize P := by
    field_simp
    ring
  unfold publicDelta
  rw [calibratedDelta_eq_window hL, he]
  field_simp

/-- The actual batch-accuracy reciprocal is cubic in the public logarithm. -/
theorem publicDelta_inv_le (H : PublicHyp D P) :
    1 / publicDelta n P ≤ 2 ^ 44 * logHeight n P ^ 3 := by
  let B := height n P
  have hB : 2 ≤ B := H.height_inputs.1
  have hB1 : 1 ≤ B := by linarith
  have hnB : (n : ℝ) ≤ B := H.height_inputs.2.1
  have hM : P.Mbar ≤ B := H.height_inputs.2.2.1
  have hM0 : 0 < P.Mbar := by linarith [H.Mbar_ge_one]
  have hℓ := H.logHeight_bounds
  have hℓ0 : 0 ≤ logHeight n P := by linarith [hℓ.1]
  have hℓB : logHeight n P ≤ B := hℓ.2
  have hL := publicLogSize_le H
  have hL16 : publicLogSize P ≤ 16 * logHeight n P := by linarith [hℓ.1]
  have hL0 : 0 < publicLogSize P := by linarith [(publicLogSize_spec P).1]
  have hT0 : 0 < publicEnvelope n P := by linarith [publicEnvelope_one_le n P]
  have hs : sqrt (n : ℝ) ≤ B := (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩)
  have hT : publicEnvelope n P ≤ 4096 * B ^ 2 := by
    calc _ ≤ 4096 * sqrt n * logHeight n P := publicEnvelope_le H
      _ ≤ 4096 * B * B := by gcongr
      _ = _ := by ring
  have hLp : publicLogSize P ≤ 16 * B := by nlinarith [hℓ.2]
  have he : PowerEnvelope B (192 * P.Mbar * publicEnvelope n P * publicLogSize P) 29 := by
    refine ⟨by positivity, ?_⟩
    calc _ ≤ 192 * B * (4096 * B ^ 2) * (16 * B) := by gcongr
      _ ≤ (2 : ℝ) ^ 25 * B ^ 4 := by nlinarith [pow_nonneg (by linarith : 0 ≤ B) 4]
      _ ≤ B ^ 25 * B ^ 4 := by gcongr
      _ = B ^ 29 := by rw [← pow_add]
  have hlog : log (192 * P.Mbar * publicEnvelope n P * publicLogSize P) ≤
      29 * logHeight n P := he.logarithm hB (by positivity)
  have hW : max (log (192 * P.Mbar * publicEnvelope n P * publicLogSize P)) 0 + 1 ≤
      32 * logHeight n P := by
    have hm : max (log (192 * P.Mbar * publicEnvelope n P * publicLogSize P)) 0 ≤
        29 * logHeight n P := max_le hlog (by linarith [hℓ.1])
    linarith [hℓ.1]
  rw [publicDelta_inv]
  calc
    _ ≤ 96 * 2 ^ 20 * (2 * (16 * logHeight n P)) ^ 2 * (32 * logHeight n P) := by
      gcongr
    _ ≤ 2 ^ 44 * logHeight n P ^ 3 := by
      nlinarith [pow_nonneg (by linarith [hℓ.1] : 0 ≤ logHeight n P) 3]

/-- Polynomial domination is used only before taking magnitude logarithms. -/
theorem coefficient_envelope {B x : ℝ} {a b : ℕ} (hB : 2 ≤ B)
    (hx : 0 ≤ x) (h : x ≤ (2 : ℝ) ^ a * B ^ b) : PowerEnvelope B x (a + b) := by
  refine ⟨hx, h.trans ?_⟩
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hB a) (by positivity)

theorem publicTolerance_inv_le (H : PublicHyp D P) :
    1 / (publicEnvironment n P).η ≤
      2 ^ 17 * publicLogSize P / publicDelta n P +
        128 * (1 / publicDelta n P + 8 * P.Mbar * P.U ^ 2 / P.ε) := by
  have hL := (publicLogSize_spec P).1
  have hL0 : 0 < publicLogSize P := by linarith
  have hD := (publicDelta_spec n P).1
  have hM : 0 < P.Mbar := by linarith [H.Mbar_ge_one]
  have hU : 0 < P.U := by linarith [H.U_ge]
  have hε := H.ε_pos
  have hgoal : 0 < P.ε / (8 * P.Mbar * P.U ^ 2) := by positivity
  have hpow : (2 : ℝ) ^ publicFinalCount n P ≤
      2 * max 1 (publicDelta n P / (P.ε / (8 * P.Mbar * P.U ^ 2))) :=
    phaseSteps_one_pow_le (div_pos hD hgoal)
  have hratio : 0 ≤ publicDelta n P / (P.ε / (8 * P.Mbar * P.U ^ 2)) := by positivity
  have hmax : max 1 (publicDelta n P / (P.ε / (8 * P.Mbar * P.U ^ 2))) ≤
      1 + publicDelta n P / (P.ε / (8 * P.Mbar * P.U ^ 2)) :=
    max_le (by linarith) (by linarith)
  have htail : 1 / ((1 / 2 : ℝ) ^ publicFinalCount n P * publicDelta n P / 64) ≤
      128 * (1 / publicDelta n P + 8 * P.Mbar * P.U ^ 2 / P.ε) := by
    have he : 1 / ((1 / 2 : ℝ) ^ publicFinalCount n P * publicDelta n P / 64) =
        64 * (2 : ℝ) ^ publicFinalCount n P / publicDelta n P := by
      rw [_root_.one_div_pow]
      field_simp
    rw [he]
    have h := mul_le_mul_of_nonneg_left (hpow.trans (mul_le_mul_of_nonneg_left hmax (by norm_num)))
      (by positivity : (0 : ℝ) ≤ 64 / publicDelta n P)
    convert h using 1 <;> field_simp
    ring
  have hfirst : 1 / (1 / (2 * publicLogSize P) * publicDelta n P / 2 ^ 16) =
      2 ^ 17 * publicLogSize P / publicDelta n P := by field_simp
  change 1 / min (1 / (2 * publicLogSize P) * publicDelta n P / 2 ^ 16)
    ((1 / 2 : ℝ) ^ publicFinalCount n P * publicDelta n P / 64) ≤ _
  rcases le_total (1 / (2 * publicLogSize P) * publicDelta n P / 2 ^ 16)
    ((1 / 2 : ℝ) ^ publicFinalCount n P * publicDelta n P / 64) with hmin | hmin
  · rw [min_eq_left hmin, hfirst]
    have : 0 ≤ 128 * (1 / publicDelta n P + 8 * P.Mbar * P.U ^ 2 / P.ε) := by positivity
    linarith
  · rw [min_eq_right hmin]
    have : 0 ≤ 2 ^ 17 * publicLogSize P / publicDelta n P := by positivity
    linarith

/-- Proved envelopes for the selected scalars, uniform over original input data. -/
theorem base_scalar_envelopes (HP : PublicHyp D P) :
    let H := height n P
    let E := publicEnvironment n P
    PowerEnvelope H (publicLogSize P) 5 ∧
    PowerEnvelope H E.Mbar 4 ∧ PowerEnvelope H E.U 3 ∧
    PowerEnvelope H (1 / E.ε) 9 ∧ PowerEnvelope H E.C 12 ∧
    PowerEnvelope H (publicEnvelope n P) 14 ∧
    PowerEnvelope H (1 / publicDelta n P) 47 ∧ PowerEnvelope H (1 / E.η) 70 := by
  intro H E
  have hH : 2 ≤ H := HP.height_inputs.1
  have hH1 : 1 ≤ H := by linarith
  have hHp : PowerEnvelope H H 1 := ⟨by linarith, by simp⟩
  have hℓ := HP.logHeight_bounds
  have hℓ0 : 0 ≤ logHeight n P := by linarith [hℓ.1]
  have hℓH : logHeight n P ≤ H := hℓ.2
  have hnH : (n : ℝ) ≤ H := HP.height_inputs.2.1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hL0 : 0 < publicLogSize P := by linarith [(publicLogSize_spec P).1]
  have hD := (publicDelta_spec n P).1
  have hη : 0 < E.η :=
    (PathFollowing.calibratedTolerance_spec (publicLogSize_spec P).1 hD (publicFinalCount n P)).1
  have hL : PowerEnvelope H (publicLogSize P) 5 := by
    apply coefficient_envelope hH hL0.le (a := 4) (b := 1)
    have hh := publicLogSize_le HP
    norm_num only [pow_one, show (2 : ℝ) ^ 4 = 16 by norm_num]
    linarith
  have hM : PowerEnvelope H E.Mbar 4 :=
    (hHp.of_le (by change 0 ≤ P.Mbar; linarith [HP.Mbar_ge_one])
      HP.height_inputs.2.2.1).weaken hH1 (by norm_num)
  have hU : PowerEnvelope H E.U 3 :=
    (hHp.of_le (by change 0 ≤ P.U; linarith [HP.U_ge])
      HP.height_inputs.2.2.2.1).weaken hH1 (by norm_num)
  have hε : PowerEnvelope H (1 / E.ε) 9 :=
    (hHp.of_le (by change 0 ≤ 1 / P.ε; have := HP.ε_pos; positivity)
      HP.height_inputs.2.2.2.2.1).weaken hH1 (by norm_num)
  have hC : PowerEnvelope H E.C 12 := by
    convert (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 96)
      (by norm_num : (96 : ℝ) ≤ 2 ^ 7)).mul hL using 1
    change 48 * (2 * publicLogSize P) = 96 * publicLogSize P
    ring
  have hT : PowerEnvelope H (publicEnvelope n P) 14 := by
    apply coefficient_envelope hH (by linarith [publicEnvelope_one_le n P]) (a := 12) (b := 2)
    have hs : sqrt (n : ℝ) ≤ H := sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    calc _ ≤ 4096 * sqrt n * logHeight n P := publicEnvelope_le HP
      _ ≤ 4096 * H * H := by gcongr
      _ = _ := by ring
  have hΔ : PowerEnvelope H (1 / publicDelta n P) 47 := by
    apply coefficient_envelope hH (by positivity) (a := 44) (b := 3)
    exact (publicDelta_inv_le HP).trans (by gcongr)
  have hη' : PowerEnvelope H (1 / E.η) 70 := by
    have hfirst : PowerEnvelope H (2 ^ 17 * publicLogSize P / publicDelta n P) 69 :=
      ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 2 ^ 17)
        (le_rfl : (2 : ℝ) ^ 17 ≤ 2 ^ 17)).mul hL).div hΔ
    have hgoal : PowerEnvelope H (8 * E.Mbar * E.U ^ 2 / E.ε) 22 :=
      (((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 8)
        (by norm_num : (8 : ℝ) ≤ 2 ^ 3)).mul hM).mul (hU.pow 2)).div hε
    have hsecond : PowerEnvelope H
        (128 * (1 / publicDelta n P + 8 * E.Mbar * E.U ^ 2 / E.ε)) 55 :=
      (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 128)
        (by norm_num : (128 : ℝ) ≤ 2 ^ 7)).mul (hΔ.add hH hgoal)
    exact (hfirst.add hH hsecond).of_le (by positivity) (publicTolerance_inv_le HP)
  exact ⟨hL, hM, hU, hε, hC, hT, hΔ, hη'⟩

#print axioms PublicHyp.height_inputs
#print axioms PublicHyp.logHeight_bounds
#print axioms publicLogSize_le
#print axioms publicEnvelope_le
#print axioms publicDelta_inv_le
#print axioms publicTolerance_inv_le
#print axioms base_scalar_envelopes

end
end CutQueryComplexity.ImplicitLP.GenericQuery
