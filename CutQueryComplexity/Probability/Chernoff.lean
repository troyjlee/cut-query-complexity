import CutQueryComplexity.Probability.BoundedDraw
import CutQueryComplexity.Probability.FiniteEvents

/-! # Multiplicative concentration from bounded-draw moments

For `0 ≤ ε ≤ 1`, each tail is at most `exp (-ε² μ / 4)` and failure of
the relative-error interval is at most twice this quantity. The general
theorems require only the exponential-moment bounds; independent bounded
draws supply them through `BoundedDraw.expMoment_sumLaw_le`.
-/

namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical ENNReal
variable {α : Type*}

theorem exp_sub_one_le_add_sq {t : ℝ} (ht : |t| ≤ 1) : Real.exp t - 1 ≤ t + t ^ 2 := by
  have h := (le_abs_self (Real.exp t - 1 - t)).trans (Real.abs_exp_sub_one_sub_id_le ht)
  linarith

theorem chernoff_upper (p : PMF α) (f : α → ℝ) {μ ε : ℝ}
    (hμ : 0 ≤ μ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hm : expMoment p f (ε / 2) ≤
      ENNReal.ofReal (Real.exp ((Real.exp (ε / 2) - 1) * μ))) :
    mass p (fun x => (1 + ε) * μ ≤ f x) ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * μ / 4))) := by
  apply (upper_tail_le_exp p f ((1 + ε) * μ) (by positivity) hm).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have he := exp_sub_one_le_add_sq (t := ε / 2) (by rw [abs_of_nonneg (by positivity)]; linarith)
  have hh := mul_le_mul_of_nonneg_right he hμ
  nlinarith

theorem chernoff_lower (p : PMF α) (f : α → ℝ) {μ ε : ℝ}
    (hμ : 0 ≤ μ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hm : expMoment p f (-ε / 2) ≤
      ENNReal.ofReal (Real.exp ((Real.exp (-ε / 2) - 1) * μ))) :
    mass p (fun x => f x ≤ (1 - ε) * μ) ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * μ / 4))) := by
  apply (lower_tail_le_exp p f ((1 - ε) * μ) (by linarith) hm).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have he := exp_sub_one_le_add_sq (t := -ε / 2) (by rw [abs_of_nonpos (by linarith)]; linarith)
  have hh := mul_le_mul_of_nonneg_right he hμ
  nlinarith

/-- No independence premise is added here: it is accounted for by the moment estimates. -/
theorem chernoff_two_sided (p : PMF α) (f : α → ℝ) {μ ε : ℝ}
    (hμ : 0 ≤ μ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hm : ∀ t : ℝ, expMoment p f t ≤ ENNReal.ofReal (Real.exp ((Real.exp t - 1) * μ))) :
    mass p (fun x => ¬((1 - ε) * μ ≤ f x ∧ f x ≤ (1 + ε) * μ)) ≤
      2 * ENNReal.ofReal (Real.exp (-(ε ^ 2 * μ / 4))) := by
  calc
    _ ≤ mass p (fun x => f x ≤ (1 - ε) * μ ∨ (1 + ε) * μ ≤ f x) := by
      apply mass_mono
      intro x hx
      rcases not_and_or.mp hx with h | h
      · exact Or.inl (le_of_lt (lt_of_not_ge h))
      · exact Or.inr (le_of_lt (lt_of_not_ge h))
    _ ≤ mass p (fun x => f x ≤ (1 - ε) * μ) +
        mass p (fun x => (1 + ε) * μ ≤ f x) := mass_or_le p _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * μ / 4))) +
        ENNReal.ofReal (Real.exp (-(ε ^ 2 * μ / 4))) :=
      add_le_add (chernoff_lower p f hμ hε hε1 (hm _)) (chernoff_upper p f hμ hε hε1 (hm _))
    _ = _ := (two_mul _).symm

namespace BoundedDraw

theorem sum_upper_tail (ds : List BoundedDraw) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mass (sumLaw ds) (fun x => (1 + ε) * sumMean ds ≤ x) ≤
      ENNReal.ofReal (Real.exp (-(ε ^ 2 * sumMean ds / 4))) :=
  chernoff_upper (sumLaw ds) id (sumMean_nonneg ds) hε hε1 (expMoment_sumLaw_le ds _)

theorem sum_lower_tail (ds : List BoundedDraw) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mass (sumLaw ds) (fun x => x ≤ (1 - ε) * sumMean ds) ≤
      ENNReal.ofReal (Real.exp (-(ε ^ 2 * sumMean ds / 4))) :=
  chernoff_lower (sumLaw ds) id (sumMean_nonneg ds) hε hε1 (expMoment_sumLaw_le ds _)

theorem sum_two_sided (ds : List BoundedDraw) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mass (sumLaw ds) (fun x => ¬((1 - ε) * sumMean ds ≤ x ∧ x ≤ (1 + ε) * sumMean ds)) ≤
      2 * ENNReal.ofReal (Real.exp (-(ε ^ 2 * sumMean ds / 4))) :=
  chernoff_two_sided (sumLaw ds) id (sumMean_nonneg ds) hε hε1 (expMoment_sumLaw_le ds)

end BoundedDraw
end
end CutQueryComplexity.Probability
