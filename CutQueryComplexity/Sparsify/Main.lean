import CutQueryComplexity.Sparsify.Recursion
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # The spectral primitive (D4; source `thm:main`)

`spectral_of_params`: suppose the public parameters satisfy

* `R t 2^{-J} ≤ ζ/4` (spanner failures),
* `R · 2n exp(−δ² t / (8 C (2K + 1))) ≤ ζ/4` (one-round failures),
* `|E(P₀)| 4^{-R} ≤ ζ/4` (terminal residual),
* `R δ ≤ ε/3`, with `0 < ε ≤ 1/2`.

Then, with probability at least `1 − ζ`, the output `Q` satisfies
`(1 − ε) xᵀLx ≤ xᵀL_Q x ≤ (1 + ε) xᵀLx` for every real vector. Its pairs are actual pairs of
positive weight, and it has at most `R t capH` pairs. The bounds `(1 − δ)^R ≥ 1 − Rδ` and
`(1 + δ)^R ≤ exp(Rδ) ≤ 1 + 2Rδ` give the factors `1 ± ε`.
-/

namespace CutQueryComplexity
namespace Sparsify

open Finset Probability Spanner Spectral
open scoped ENNReal

noncomputable section

variable {n : ℕ} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ}

/-- `(1 + δ)^R ≤ 1 + 2Rδ` when `Rδ ≤ 1`. -/
theorem one_add_pow_le {δ : ℝ} (hδ : 0 ≤ δ) (R : ℕ) (h : R * δ ≤ 1) :
    (1 + δ) ^ R ≤ 1 + 2 * (R * δ) := by
  have h1 : (1 + δ) ^ R ≤ Real.exp (R * δ) := by
    calc (1 + δ) ^ R ≤ Real.exp δ ^ R :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp δ]) R
      _ = Real.exp (R * δ) := by rw [← Real.exp_nat_mul]
  have hx : 0 ≤ (R : ℝ) * δ := by positivity
  have h2 : Real.exp (R * δ) ≤ 1 + 2 * (R * δ) := by
    have := Real.abs_exp_sub_one_sub_id_le (x := (R : ℝ) * δ) (by rw [abs_of_nonneg hx]; exact h)
    rw [abs_le] at this
    nlinarith
  linarith

/-- **The spectral primitive from explicit parameter conditions.** -/
theorem spectral_of_params {K J t R : ℕ} {C ε ζ δ : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ e, (symS G e : ℝ) ≤ C) (hw0 : ∀ e, 0 ≤ w e) (hK : n ≤ 2 ^ K) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hζ : 0 ≤ ζ) (hRδ : (R : ℝ) * δ ≤ ε / 3)
    (hJ : (R : ℝ≥0∞) * (t * (2⁻¹ : ℝ≥0∞) ^ J) ≤ ENNReal.ofReal (ζ / 4))
    (hγ : (R : ℝ) * (2 * n * Real.exp (-(δ ^ 2) / (8 * (C * (2 * K + 1 : ℕ) / t)))) ≤ ζ / 4)
    (hres : ((resid G (P0 w)).card : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ R ≤ ENNReal.ofReal (ζ / 4)) :
    mass ((sparsify w K J t R).eval G.out) (fun o => ¬ ∃ out, o = some out ∧
      (∀ x, (1 - ε) * E0 G w x ≤ Eo out x ∧ Eo out x ≤ (1 + ε) * E0 G w x) ∧
      (∀ e, out e ≠ 0 → 0 < symS G e ∧ 0 < w e) ∧
      (univ.filter fun e => out e ≠ 0).card ≤ R * (t * capH (Fin n) K) ∧
      (∀ e, out e ≠ 0 → ∃ r' < R, out e = (symS G e : ℝ) * (4 : ℝ) ^ r' * w e)) ≤
        ENNReal.ofReal ζ := by
  have hRpos : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hfail := sparsify_fail_le (J := J) hC0 hC hw0 hK ht hδ hδ1 R
  refine le_trans (mass_mono (Q := fun o => ¬ ∃ out, o = some out ∧ Good G w K t δ R out) _
    fun o ho hgood => ho ?_) (hfail.trans ?_)
  · obtain ⟨out, rfl, ⟨happ, -, hsupp, hsize, hform⟩⟩ := hgood
    refine ⟨out, rfl, fun x => ?_, hsupp, hsize, hform⟩
    have hE0 : 0 ≤ E0 G w x := by
      unfold E0 Er; exact energy_nonneg (omegaR_nonneg (G := G) hw0 0) _ x
    obtain ⟨hlo, hhi⟩ := happ x
    have hb1 : 1 - ε ≤ (1 - δ) ^ R := by
      have := one_add_mul_le_pow (a := -δ) (by linarith) R
      have : (1 : ℝ) + R * -δ ≤ (1 - δ) ^ R := by simpa [sub_eq_add_neg] using this
      linarith
    have hb2 : (1 + δ) ^ R ≤ 1 + ε := by
      have := one_add_pow_le hδ.le R (by linarith)
      linarith
    exact ⟨(mul_le_mul_of_nonneg_right hb1 hE0).trans hlo,
      hhi.trans (mul_le_mul_of_nonneg_right hb2 hE0)⟩
  · have hγ0 : 0 ≤ 2 * n * Real.exp (-(δ ^ 2) / (8 * (C * (2 * K + 1 : ℕ) / t))) := by positivity
    rw [mul_add]
    have h2 : (R : ℝ≥0∞) * ENNReal.ofReal (2 * n * Real.exp (-(δ ^ 2) / (8 * (C * (2 * K + 1 : ℕ) / t)))) ≤
        ENNReal.ofReal (ζ / 4) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hRpos]
      exact ENNReal.ofReal_le_ofReal hγ
    calc _ ≤ ENNReal.ofReal (ζ / 4) + ENNReal.ofReal (ζ / 4) + ENNReal.ofReal (ζ / 4) :=
          add_le_add (add_le_add hJ h2) hres
      _ = ENNReal.ofReal (3 * ζ / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
      _ ≤ ENNReal.ofReal ζ := ENNReal.ofReal_le_ofReal (by linarith)

end

end Sparsify
end CutQueryComplexity
