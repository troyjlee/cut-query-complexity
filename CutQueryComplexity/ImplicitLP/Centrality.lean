import CutQueryComplexity.ImplicitLP.Movement

/-! # Centrality under weight and path-parameter changes (`eq:wmove`, `eq:tchange`; Lee–Sidford audit)

The centrality is `δ_t(x, w) = inf_ν N_w((tc + wφ' − Aν)/(wS))` (`cent`), with `S = √φ''`. The
barrier enters only through `|φ'ᵢ| ≤ Sᵢ`, the first inequality of `eq:barrier`.

* `eq_wmove` (Lee–Sidford Lemma 17): if `a = N_w(log w' − log w) ≤ 1/10`, then
  `δ_t(x, w') ≤ (1 + 4a)(δ_t(x, w) + a)`.
* `eq_tchange` (Lee–Sidford Lemma 14, two-sided, audit G6): if `|t'/t − 1| ≤ α`, then
  `δ_{t'}(x, w) ≤ (1 + α) δ_t(x, w) + α N_w(φ'/S)`, and
  `N_w(φ'/S) ≤ 1 + C (Σ w)^{1/2}` (`mixed_dphi_le`).

Both hold for any `C > 0` and any positive weights. They use no Lewis-weight fact.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ}

/-- The centrality `δ_t(x, w) = inf_ν N_w((tc + wφ' − Aν)/(wS))`. -/
def cent (C : ℝ) (A : Matrix (Fin M) (Fin r) ℝ) (S dφ c : Fin M → ℝ) (t : ℝ)
    (w : Fin M → ℝ) : ℝ :=
  ⨅ ν, mixed C w (fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i))

variable {C : ℝ} {A : Matrix (Fin M) (Fin r) ℝ} {S dφ c : Fin M → ℝ}

theorem cent_bdd (hC : 0 ≤ C) (t : ℝ) (w : Fin M → ℝ) :
    BddBelow (Set.range fun ν : Fin r → ℝ =>
      mixed C w (fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i))) :=
  ⟨0, fun _ ⟨_, h⟩ => h ▸ mixed_nonneg hC _⟩

theorem cent_nonneg (hC : 0 ≤ C) (t : ℝ) (w : Fin M → ℝ) : 0 ≤ cent C A S dφ c t w :=
  le_ciInf fun _ => mixed_nonneg hC _

/-- `|1 − e^{−d}| ≤ |d| e^{|d|}`. -/
theorem abs_one_sub_exp_neg_le (d : ℝ) : |1 - exp (-d)| ≤ |d| * exp |d| := by
  rcases le_total 0 d with hd | hd
  · rw [abs_of_nonneg hd, abs_of_nonneg (by
      have : exp (-d) ≤ 1 := exp_le_one_iff.mpr (by linarith)
      linarith)]
    have h1 := add_one_le_exp (-d)
    have h2 : d ≤ d * exp d := le_mul_of_one_le_right hd (one_le_exp hd)
    linarith
  · rw [abs_of_nonpos hd, abs_of_nonpos (by
      have : 1 ≤ exp (-d) := one_le_exp (by linarith)
      linarith)]
    -- `e^{−d} − 1 ≤ (−d) e^{−d}`
    have h1 := add_one_le_exp d
    have h2 : 0 < exp (-d) := exp_pos _
    have : exp d * exp (-d) = 1 := by rw [← exp_add]; simp
    nlinarith

/-- **`eq:wmove`** (Lee–Sidford Lemma 17). -/
theorem eq_wmove (hC : 0 < C) (hS : ∀ i, 0 < S i) (hdφ : ∀ i, |dφ i| ≤ S i) (t : ℝ)
    {w w' : Fin M → ℝ} (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    (ha : mixed C w (fun i => Real.log (w' i) - Real.log (w i)) ≤ 1 / 10) :
    cent C A S dφ c t w' ≤ (1 + 4 * mixed C w (fun i => Real.log (w' i) - Real.log (w i))) *
      (cent C A S dφ c t w + mixed C w (fun i => Real.log (w' i) - Real.log (w i))) := by
  set d : Fin M → ℝ := fun i => Real.log (w' i) - Real.log (w i)
  set a := mixed C w d
  have ha0 : 0 ≤ a := mixed_nonneg hC.le d
  have hdi : ∀ i, |d i| ≤ a := fun i => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm d i).trans (norm_le_mixed hC.le d)
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  -- `w' = w e^{d}`
  have hw'e : ∀ i, w' i = w i * exp (d i) := fun i => by
    simp only [d]; rw [exp_sub, exp_log (hw' i), exp_log (hw i), mul_div_assoc', mul_comm,
      mul_div_assoc, div_self (hw i).ne', mul_one]
  have hcmp : ∀ i, w' i ≤ exp a * w i := fun i => by
    rw [hw'e, mul_comm]
    exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr ((le_abs_self _).trans (hdi i))) (hw0 i)
  -- `e^{3a/2} ≤ 1 + 4a`
  have hexp : exp (a / 2) * exp a ≤ 1 + 4 * a := by
    rw [← exp_add]
    have h := abs_exp_sub_one_sub_id_le (x := a / 2 + a) (by
      rw [abs_of_nonneg (by positivity)]; linarith)
    rw [abs_le] at h
    nlinarith
  -- per-`ν` comparison
  have key : ∀ ν : Fin r → ℝ,
      mixed C w' (fun i => (t * c i + w' i * dφ i - (A *ᵥ ν) i) / (w' i * S i)) ≤
        (1 + 4 * a) * (mixed C w (fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i)) +
          a) := by
    intro ν
    set R := fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i)
    have hsplit : (fun i => (t * c i + w' i * dφ i - (A *ᵥ ν) i) / (w' i * S i)) =
        (fun i => w i / w' i * R i) + fun i => (1 - exp (-d i)) * (dφ i / S i) := by
      funext i
      simp only [Pi.add_apply, R]
      have he : exp (-d i) = w i / w' i := by
        rw [exp_neg, hw'e]; field_simp [(hw i).ne', (exp_pos (d i)).ne']
      rw [he]
      field_simp [(hw i).ne', (hw' i).ne', (hS i).ne']
      ring
    rw [hsplit]
    have h1 : mixed C w (fun i => w i / w' i * R i) ≤ exp a * mixed C w R := by
      rw [show exp a * mixed C w R = |exp a| * mixed C w R by rw [abs_of_pos (exp_pos a)],
        ← mixed_smul]
      refine mixed_mono hC.le hw0 fun i => ?_
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [abs_of_pos (div_pos (hw i) (hw' i)), abs_of_pos (exp_pos _), hw'e,
        div_mul_cancel_left₀ (hw i).ne', ← exp_neg]
      exact exp_le_exp.mpr ((neg_le_abs _).trans (hdi i))
    have h2 : mixed C w (fun i => (1 - exp (-d i)) * (dφ i / S i)) ≤ exp a * a := by
      rw [show exp a * a = |exp a| * mixed C w d by rw [abs_of_pos (exp_pos a)], ← mixed_smul]
      refine mixed_mono hC.le hw0 fun i => ?_
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (exp_pos a)]
      have hq : |dφ i / S i| ≤ 1 := by
        rw [abs_div, abs_of_pos (hS i), div_le_one (hS i)]; exact hdφ i
      calc |1 - exp (-d i)| * |dφ i / S i| ≤ |1 - exp (-d i)| * 1 :=
            mul_le_mul_of_nonneg_left hq (abs_nonneg _)
        _ ≤ |d i| * exp |d i| := by rw [mul_one]; exact abs_one_sub_exp_neg_le _
        _ ≤ exp a * |d i| := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (hdi i)) (abs_nonneg _)
    have hR0 := mixed_nonneg (g := w) hC.le R
    calc mixed C w' ((fun i => w i / w' i * R i) + fun i => (1 - exp (-d i)) * (dφ i / S i))
        ≤ exp (a / 2) * mixed C w
            ((fun i => w i / w' i * R i) + fun i => (1 - exp (-d i)) * (dφ i / S i)) :=
          mixed_le_of_le_exp hC.le ha0 hcmp _
      _ ≤ exp (a / 2) * (exp a * mixed C w R + exp a * a) :=
          mul_le_mul_of_nonneg_left ((mixed_add_le hC.le hw0 _ _).trans (add_le_add h1 h2))
            (exp_pos _).le
      _ = exp (a / 2) * exp a * (mixed C w R + a) := by ring
      _ ≤ (1 + 4 * a) * (mixed C w R + a) :=
          mul_le_mul_of_nonneg_right hexp (by linarith)
  -- take the infimum
  have hpos : 0 < 1 + 4 * a := by linarith
  have : cent C A S dφ c t w' / (1 + 4 * a) - a ≤ cent C A S dφ c t w := by
    refine le_ciInf fun ν => ?_
    have h : cent C A S dφ c t w' ≤ _ :=
      (ciInf_le (cent_bdd (A := A) (S := S) (dφ := dφ) (c := c) hC.le t w') ν).trans (key ν)
    rw [sub_le_iff_le_add, div_le_iff₀ hpos]
    nlinarith
  rw [div_sub' hpos.ne', div_le_iff₀ hpos] at this
  nlinarith

/-- **`eq:tchange`** (Lee–Sidford Lemma 14, two-sided): if `t > 0` and `|t'/t − 1| ≤ α`, then
`δ_{t'}(x, w) ≤ (1 + α) δ_t(x, w) + α N_w(φ'/S)`. -/
theorem eq_tchange (hC : 0 < C) (hS : ∀ i, 0 < S i) {w : Fin M → ℝ} (hw : ∀ i, 0 < w i)
    {t t' α : ℝ} (ht : 0 < t) (hα : |t' / t - 1| ≤ α) :
    cent C A S dφ c t' w ≤
      (1 + α) * cent C A S dφ c t w + α * mixed C w (fun i => dφ i / S i) := by
  set lam := t' / t
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hα0 : 0 ≤ α := (abs_nonneg _).trans hα
  have hlam : |lam| ≤ 1 + α := by
    have := abs_sub_abs_le_abs_sub lam 1
    rw [abs_one] at this; linarith
  have key : ∀ ν : Fin r → ℝ, cent C A S dφ c t' w ≤
      (1 + α) * mixed C w (fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i)) +
        α * mixed C w (fun i => dφ i / S i) := by
    intro ν
    set R := fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i)
    have hsplit : (fun i => (t' * c i + w i * dφ i - (A *ᵥ (lam • ν)) i) / (w i * S i)) =
        lam • R + (1 - lam) • fun i => dφ i / S i := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, R, mulVec_smul, lam]
      field_simp [(hw i).ne', (hS i).ne', ht.ne']
      ring
    refine (ciInf_le (cent_bdd hC.le t' w) (lam • ν)).trans ?_
    rw [hsplit]
    refine (mixed_add_le hC.le hw0 _ _).trans ?_
    rw [mixed_smul, mixed_smul, abs_sub_comm]
    exact add_le_add (mul_le_mul_of_nonneg_right hlam (mixed_nonneg hC.le _))
      (mul_le_mul_of_nonneg_right hα (mixed_nonneg hC.le _))
  have hpos : 0 < 1 + α := by linarith
  have : (cent C A S dφ c t' w - α * mixed C w (fun i => dφ i / S i)) / (1 + α) ≤
      cent C A S dφ c t w := by
    refine le_ciInf fun ν => ?_
    rw [div_le_iff₀ hpos]
    have := key ν
    linarith
  rw [div_le_iff₀ hpos] at this
  linarith

/-- `N_w(φ'/S) ≤ 1 + C (Σ w)^{1/2}` when `|φ'| ≤ S`. -/
theorem mixed_dphi_le (hC : 0 ≤ C) (hS : ∀ i, 0 < S i) (hdφ : ∀ i, |dφ i| ≤ S i)
    {w : Fin M → ℝ} (hw : ∀ i, 0 ≤ w i) :
    mixed C w (fun i => dφ i / S i) ≤ 1 + C * Real.sqrt (∑ i, w i) := by
  have hq : ∀ i, |dφ i / S i| ≤ 1 := fun i => by
    rw [abs_div, abs_of_pos (hS i), div_le_one (hS i)]; exact hdφ i
  unfold mixed
  have h1 : ‖fun i => dφ i / S i‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by rw [Real.norm_eq_abs]; exact hq i
  have h2 : wnorm w (fun i => dφ i / S i) ≤ Real.sqrt (∑ i, w i) := by
    unfold wnorm
    apply Real.sqrt_le_sqrt
    refine sum_le_sum fun i _ => ?_
    have : (dφ i / S i) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [hq i, abs_nonneg (dφ i / S i)]
    nlinarith [hw i]
  linarith [mul_le_mul_of_nonneg_left h2 hC]

end

end ImplicitLP
end CutQueryComplexity
