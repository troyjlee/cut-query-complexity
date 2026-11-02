import CutQueryComplexity.Sparsify.Params
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Query and size bounds of the spectral primitive (D4; source `thm:main`)

With `D = ln(2Cn/(εζ))`, for `0 < ε, ζ ≤ 1/2`, `C ≥ 1`, `n ≥ 2`:

* `K ≤ 3D`, `R ≤ 6D`, `t ≤ 181441 C ε⁻² D⁴`, `J ≤ 45D` (`bounds`);
* `budget_le`: the worst-case query budget is at most `2·10^10 · C ε⁻² n D⁸`;
* `size_le`: every output has at most `2·10^7 · C ε⁻² n D⁶` pairs.

The constants are explicit and crude. Each of `n`, `C`, `1/ε`, `1/ζ` is at most `e^D`, and
`D ≥ 2`.
-/

namespace CutQueryComplexity
namespace Sparsify

open Finset Real Spanner

noncomputable section

/-- `D = ln(2Cn/(εζ))`. -/
def Dlog (n : ℕ) (C ε ζ : ℝ) : ℝ := log (2 * C * n / (ε * ζ))

/-- The standing hypotheses. -/
structure Hyp (n : ℕ) (C ε ζ : ℝ) : Prop where
  hn : 2 ≤ n
  hC : 1 ≤ C
  hε : 0 < ε
  hε2 : ε ≤ 1 / 2
  hζ : 0 < ζ
  hζ2 : ζ ≤ 1 / 2

variable {n : ℕ} {C ε ζ : ℝ}

theorem Hyp.n_ge (h : Hyp n C ε ζ) : (2 : ℝ) ≤ n := by exact_mod_cast h.hn

theorem Hyp.M_ge (h : Hyp n C ε ζ) : 16 ≤ 2 * C * n / (ε * ζ) := by
  have := h.n_ge; have := h.hC; have := h.hε; have := h.hζ; have := h.hε2; have := h.hζ2
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul h.hε2 h.hζ2 h.hζ.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem Hyp.D_ge (h : Hyp n C ε ζ) : 2 ≤ Dlog n C ε ζ := by
  have hM := h.M_ge
  unfold Dlog
  rw [le_log_iff_exp_le (by linarith)]
  have h1 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
  have h2 := exp_one_lt_three
  have h3 := exp_pos 1
  nlinarith

/-- A quantity at most `2Cn/(εζ)` has logarithm at most `D`. -/
theorem Hyp.log_le (_h : Hyp n C ε ζ) {y : ℝ} (hy : 0 < y) (hyM : y ≤ 2 * C * n / (ε * ζ)) :
    log y ≤ Dlog n C ε ζ := log_le_log hy hyM

theorem Hyp.factors (h : Hyp n C ε ζ) :
    (n : ℝ) ≤ 2 * C * n / (ε * ζ) ∧ 1 / ζ ≤ 2 * C * n / (ε * ζ) ∧
      1 / ε ≤ 2 * C * n / (ε * ζ) ∧ C ≤ 2 * C * n / (ε * ζ) := by
  have := h.n_ge; have := h.hC; have := h.hε; have := h.hζ; have := h.hε2; have := h.hζ2
  have hεζ : ε * ζ ≤ 1 := by nlinarith
  have hpos : 0 < ε * ζ := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hpos]; nlinarith
  · have h2 : ε ≤ 2 * C * n := by nlinarith
    rw [div_le_div_iff₀ (by positivity) hpos]
    nlinarith [mul_le_mul_of_nonneg_right h2 h.hζ.le]
  · have h2 : ζ ≤ 2 * C * n := by nlinarith
    rw [div_le_div_iff₀ (by positivity) hpos]
    nlinarith [mul_le_mul_of_nonneg_right h2 h.hε.le]
  · rw [le_div_iff₀ hpos]; nlinarith

theorem ceil_le_add_one {y : ℝ} (hy : 0 ≤ y) : (⌈y⌉₊ : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one hy).le

theorem log_two_ge : (1 / 2 : ℝ) ≤ log 2 := by have := log_two_gt_d9; linarith

theorem log_four_ge : (1 : ℝ) ≤ log 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; have := log_two_ge; push_cast; linarith

theorem log_four_le : log 4 ≤ 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; have := log_two_lt_d9; push_cast; linarith

theorem log_eight_le : log 8 ≤ 3 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; have := log_two_lt_d9; push_cast; linarith

/-- **Parameter bounds.** -/
theorem bounds (h : Hyp n C ε ζ) :
    (pK n : ℝ) ≤ 3 * Dlog n C ε ζ ∧ (pR n ζ : ℝ) ≤ 6 * Dlog n C ε ζ ∧
      (pt n C ε ζ : ℝ) ≤ 181441 * C / ε ^ 2 * Dlog n C ε ζ ^ 4 ∧
      (pJ n C ε ζ : ℝ) ≤ 45 * Dlog n C ε ζ := by
  set D := Dlog n C ε ζ
  have hD := h.D_ge
  have hn' := h.n_ge
  have hC := h.hC; have hε := h.hε; have hζ := h.hζ; have hε2 := h.hε2; have hζ2 := h.hζ2
  obtain ⟨fn, fζ, fε, fC⟩ := h.factors
  have lnn : log n ≤ D := h.log_le (by linarith) fn
  have lnζ : log (1 / ζ) ≤ D := h.log_le (by positivity) fζ
  have lnε : log (1 / ε) ≤ D := h.log_le (by positivity) fε
  have lnC : log C ≤ D := h.log_le (by linarith) fC
  have lnn0 : 0 ≤ log n := log_nonneg (by linarith)
  have lnζ0 : 0 ≤ log (1 / ζ) := log_nonneg (by rw [le_div_iff₀ hζ]; linarith)
  have lnε0 : 0 ≤ log (1 / ε) := log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have lnC0 : 0 ≤ log C := log_nonneg hC
  -- `K`
  have hK : (pK n : ℝ) ≤ 3 * D := by
    have h0 : 0 ≤ logb 2 n := logb_nonneg (by norm_num) (by linarith)
    have h1 := ceil_le_add_one h0
    have h2 : logb 2 n ≤ 2 * log n := by
      rw [logb, div_le_iff₀ (by have := log_two_ge; linarith)]
      have := log_two_ge; nlinarith
    unfold pK; linarith
  -- `R`
  have hR1 := pR_pos h.hn hζ hζ2
  have hRr : (1 : ℝ) ≤ pR n ζ := by exact_mod_cast hR1
  have hR : (pR n ζ : ℝ) ≤ 6 * D := by
    have hx : 0 < 4 * (n : ℝ) ^ 2 / ζ := by positivity
    have hl : log (4 * (n : ℝ) ^ 2 / ζ) = log 4 + 2 * log n + log (1 / ζ) := by
      rw [div_eq_mul_one_div, log_mul (by positivity) (by positivity),
        log_mul (by norm_num) (by positivity), log_pow]; push_cast; ring
    have h0 : 0 ≤ logb 4 (4 * (n : ℝ) ^ 2 / ζ) := by
      rw [logb]; exact div_nonneg (by rw [hl]; have := log_four_ge; linarith)
        (by have := log_four_ge; linarith)
    have h1 := ceil_le_add_one h0
    have h2 : logb 4 (4 * (n : ℝ) ^ 2 / ζ) ≤ log (4 * (n : ℝ) ^ 2 / ζ) := by
      rw [logb]; exact div_le_self (by rw [hl]; have := log_four_ge; linarith) log_four_ge
    unfold pR
    have := log_four_le
    linarith
  -- `t`
  have hL1 : log (8 * n * pR n ζ / ζ) ≤ 10 * D := by
    rw [div_eq_mul_one_div, log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity)]
    have hlR : log (pR n ζ) ≤ pR n ζ := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have := log_eight_le
    linarith
  have hL10 : 0 ≤ log (8 * n * pR n ζ / ζ) := log_nonneg (by rw [le_div_iff₀ hζ]; nlinarith)
  have ht : (pt n C ε ζ : ℝ) ≤ 181441 * C / ε ^ 2 * D ^ 4 := by
    have hK' : ((2 * pK n + 1 : ℕ) : ℝ) ≤ 7 * D := by push_cast; linarith
    have hδ : 1 / pδ n ε ζ ^ 2 = 9 * (pR n ζ : ℝ) ^ 2 / ε ^ 2 := by unfold pδ; field_simp; ring
    have hinner : 0 ≤ 8 * C * (2 * pK n + 1 : ℕ) / pδ n ε ζ ^ 2 * log (8 * n * pR n ζ / ζ) := by
      have : 0 < pδ n ε ζ := by unfold pδ; positivity
      positivity
    have h1 := ceil_le_add_one hinner
    have h2 : 8 * C * (2 * pK n + 1 : ℕ) / pδ n ε ζ ^ 2 * log (8 * n * pR n ζ / ζ) ≤
        181440 * C / ε ^ 2 * D ^ 4 := by
      rw [div_eq_mul_one_div (8 * C * _), hδ]
      have e1 : 8 * C * ((2 * pK n + 1 : ℕ) : ℝ) ≤ 8 * C * (7 * D) := by gcongr
      have e2 : 9 * (pR n ζ : ℝ) ^ 2 / ε ^ 2 ≤ 9 * (6 * D) ^ 2 / ε ^ 2 := by
        gcongr
      calc 8 * C * ((2 * pK n + 1 : ℕ) : ℝ) * (9 * (pR n ζ : ℝ) ^ 2 / ε ^ 2) *
            log (8 * n * pR n ζ / ζ)
          ≤ 8 * C * (7 * D) * (9 * (6 * D) ^ 2 / ε ^ 2) * (10 * D) := by gcongr
        _ = 181440 * C / ε ^ 2 * D ^ 4 := by ring
    have h3 : (1 : ℝ) ≤ C / ε ^ 2 * D ^ 4 := by
      have : (1 : ℝ) ≤ D ^ 4 := one_le_pow₀ (by linarith)
      have : (1 : ℝ) ≤ C / ε ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      nlinarith
    have h4 : 181441 * C / ε ^ 2 * D ^ 4 = 181440 * C / ε ^ 2 * D ^ 4 + C / ε ^ 2 * D ^ 4 := by
      ring
    unfold pt
    linarith
  -- `J`
  have ht1 : (1 : ℝ) ≤ pt n C ε ζ := by
    have := (params_ok h.hn hC hε hε2 hζ hζ2).2.1
    exact_mod_cast this
  have hJ : (pJ n C ε ζ : ℝ) ≤ 45 * D := by
    have hlt : log (pt n C ε ζ) ≤ 14 * D := by
      have hpos : (0 : ℝ) < 181441 * C / ε ^ 2 * D ^ 4 := by positivity
      calc log (pt n C ε ζ) ≤ log (181441 * C / ε ^ 2 * D ^ 4) :=
            log_le_log (by linarith) ht
        _ = log 181441 + log C + 2 * log (1 / ε) + 4 * log D := by
            rw [log_mul (by positivity) (by positivity), log_div (by positivity) (by positivity),
              log_mul (by norm_num) (by positivity), log_pow, log_pow]
            rw [one_div, log_inv]; push_cast; ring
        _ ≤ 13 + D + 2 * D + 4 * D := by
            have h13 : log 181441 ≤ 13 := by
              rw [log_le_iff_le_exp (by norm_num)]
              have : (181441 : ℝ) ≤ exp 1 ^ 13 := by
                have := exp_one_gt_d9
                calc (181441 : ℝ) ≤ (2.7182818283 : ℝ) ^ 13 := by norm_num
                  _ ≤ exp 1 ^ 13 := pow_le_pow_left₀ (by norm_num) this.le 13
              calc (181441 : ℝ) ≤ exp 1 ^ 13 := this
                _ = exp 13 := by rw [← exp_nat_mul]; norm_num
            have hlD : log D ≤ D := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
            linarith
        _ ≤ 14 * D := by linarith
    have hx : 0 < 4 * (pR n ζ : ℝ) * pt n C ε ζ / ζ := by positivity
    have hl : log (4 * (pR n ζ : ℝ) * pt n C ε ζ / ζ) =
        log 4 + log (pR n ζ) + log (pt n C ε ζ) + log (1 / ζ) := by
      rw [div_eq_mul_one_div, log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity)]
    have hlR : log (pR n ζ) ≤ pR n ζ := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hl0 : 0 ≤ log (4 * (pR n ζ : ℝ) * pt n C ε ζ / ζ) := by
      rw [hl]
      have := log_four_ge
      have := log_nonneg hRr; have := log_nonneg ht1
      linarith
    have h0 : 0 ≤ logb 2 (4 * (pR n ζ : ℝ) * pt n C ε ζ / ζ) := by
      rw [logb]; exact div_nonneg hl0 (by have := log_two_ge; linarith)
    have h1 := ceil_le_add_one h0
    have h2 : logb 2 (4 * (pR n ζ : ℝ) * pt n C ε ζ / ζ) ≤
        2 * log (4 * (pR n ζ : ℝ) * pt n C ε ζ / ζ) := by
      rw [logb, div_le_iff₀ (by have := log_two_ge; linarith)]
      have := log_two_ge; nlinarith
    unfold pJ
    have := log_four_le
    rw [hl] at h2
    linarith
  exact ⟨hK, hR, ht, hJ⟩

/-- **The worst-case query budget is `O(C ε⁻² n D⁸)`.** -/
theorem budget_le (h : Hyp n C ε ζ) :
    ((pR n ζ * levelBudget (n := n) (pK n) (pJ n C ε ζ) (pt n C ε ζ) + 3 * n : ℕ) : ℝ) ≤
      2 * 10 ^ 10 * C / ε ^ 2 * n * Dlog n C ε ζ ^ 8 := by
  obtain ⟨hK, hR, ht, hJ⟩ := bounds h
  set D := Dlog n C ε ζ
  have hD := h.D_ge
  have hn' := h.n_ge
  have hC := h.hC; have hε := h.hε
  have hK0 : (0 : ℝ) ≤ pK n := Nat.cast_nonneg _
  have hX : (1 : ℝ) ≤ C / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [h.hε2]
  have hD8 : (1 : ℝ) ≤ D ^ 8 := one_le_pow₀ (by linarith)
  have hcapQ : ((capQ (Fin n) (pK n) (pK n) : ℕ) : ℝ) ≤ 264 * n * D ^ 2 := by
    simp only [capQ, Fintype.card_fin]; push_cast
    have h1 : 3 + 3 * (pK n : ℝ) ≤ 11 * D := by linarith
    have h2 : (pK n : ℝ) + 1 ≤ 4 * D := by linarith
    calc (3 + 3 * (pK n : ℝ)) * (6 * n * ((pK n : ℝ) + 1)) ≤ (11 * D) * (6 * n * (4 * D)) := by
          gcongr
      _ = 264 * n * D ^ 2 := by ring
  have hcapH : ((capH (Fin n) (pK n) : ℕ) : ℝ) ≤ 16 * n * D := by
    simp only [capH, Fintype.card_fin]; push_cast
    have h2 : (pK n : ℝ) + 1 ≤ 4 * D := by linarith
    calc 4 * (n : ℝ) * ((pK n : ℝ) + 1) ≤ 4 * n * (4 * D) := by gcongr
      _ = 16 * n * D := by ring
  have hlev : ((levelBudget (n := n) (pK n) (pJ n C ε ζ) (pt n C ε ζ) : ℕ) : ℝ) ≤
      11928 * (pt n C ε ζ : ℝ) * n * D ^ 3 := by
    simp only [levelBudget]; push_cast
    have ht0 : (0 : ℝ) ≤ pt n C ε ζ := Nat.cast_nonneg _
    have hJ0 : (0 : ℝ) ≤ pJ n C ε ζ := Nat.cast_nonneg _
    calc (pt n C ε ζ : ℝ) * ((pJ n C ε ζ : ℝ) * (capQ (Fin n) (pK n) (pK n) : ℕ)) +
          3 * ((pt n C ε ζ : ℝ) * (capH (Fin n) (pK n) : ℕ))
        ≤ (pt n C ε ζ : ℝ) * ((45 * D) * (264 * n * D ^ 2)) + 3 * ((pt n C ε ζ : ℝ) * (16 * n * D)) := by
          gcongr
      _ = (pt n C ε ζ : ℝ) * n * (11880 * D ^ 3 + 48 * D) := by ring
      _ ≤ (pt n C ε ζ : ℝ) * n * (11928 * D ^ 3) := by
          gcongr
          nlinarith [pow_le_pow_right₀ (show (1 : ℝ) ≤ D by linarith) (show 1 ≤ 3 by norm_num)]
      _ = 11928 * (pt n C ε ζ : ℝ) * n * D ^ 3 := by ring
  have hcast : ((pR n ζ * levelBudget (n := n) (pK n) (pJ n C ε ζ) (pt n C ε ζ) + 3 * n : ℕ) : ℝ) =
      (pR n ζ : ℝ) * ((levelBudget (n := n) (pK n) (pJ n C ε ζ) (pt n C ε ζ) : ℕ) : ℝ) + 3 * n := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
  rw [hcast]
  calc (pR n ζ : ℝ) * ((levelBudget (n := n) (pK n) (pJ n C ε ζ) (pt n C ε ζ) : ℕ) : ℝ) + 3 * n
      ≤ (6 * D) * (11928 * (181441 * C / ε ^ 2 * D ^ 4) * n * D ^ 3) + 3 * (C / ε ^ 2 * n * D ^ 8) := by
        gcongr
        · exact hlev.trans (by gcongr)
        · nlinarith [mul_le_mul hX hD8 zero_le_one (by positivity)]
    _ = (6 * 11928 * 181441 + 3) * (C / ε ^ 2) * n * D ^ 8 := by ring
    _ ≤ _ := by
        have : (0 : ℝ) ≤ C / ε ^ 2 * n * D ^ 8 := by positivity
        rw [show 2 * 10 ^ 10 * C / ε ^ 2 * n * D ^ 8 = 2 * 10 ^ 10 * (C / ε ^ 2) * n * D ^ 8 by ring]
        nlinarith

/-- **Every output has `O(C ε⁻² n D⁶)` pairs.** -/
theorem size_le (h : Hyp n C ε ζ) :
    ((pR n ζ * (pt n C ε ζ * capH (Fin n) (pK n)) : ℕ) : ℝ) ≤
      2 * 10 ^ 7 * C / ε ^ 2 * n * Dlog n C ε ζ ^ 6 := by
  obtain ⟨hK, hR, ht, -⟩ := bounds h
  set D := Dlog n C ε ζ
  have hD := h.D_ge
  have hn' := h.n_ge
  have hcapH : ((capH (Fin n) (pK n) : ℕ) : ℝ) ≤ 16 * n * D := by
    simp only [capH, Fintype.card_fin]; push_cast
    have h2 : (pK n : ℝ) + 1 ≤ 4 * D := by linarith
    calc 4 * (n : ℝ) * ((pK n : ℝ) + 1) ≤ 4 * n * (4 * D) := by gcongr
      _ = 16 * n * D := by ring
  rw [Nat.cast_mul, Nat.cast_mul]
  calc (pR n ζ : ℝ) * ((pt n C ε ζ : ℝ) * ((capH (Fin n) (pK n) : ℕ) : ℝ))
      ≤ (6 * D) * ((181441 * C / ε ^ 2 * D ^ 4) * (16 * n * D)) := by
        have := h.hC; have := h.hε
        gcongr
    _ = 17418336 * C / ε ^ 2 * n * D ^ 6 := by ring
    _ ≤ _ := by
        have : (0 : ℝ) ≤ C / ε ^ 2 * n * D ^ 6 := by
          have := h.hε; have := h.hC; positivity
        rw [show 17418336 * C / ε ^ 2 * n * D ^ 6 = 17418336 * (C / ε ^ 2 * n * D ^ 6) by ring,
          show 2 * 10 ^ 7 * C / ε ^ 2 * n * D ^ 6 = 2 * 10 ^ 7 * (C / ε ^ 2 * n * D ^ 6) by ring]
        nlinarith

end

end Sparsify
end CutQueryComplexity
