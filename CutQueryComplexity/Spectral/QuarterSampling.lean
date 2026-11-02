import CutQueryComplexity.Spectral.MatrixNorm
import CutQueryComplexity.Probability.Events
import SLT.RMT.MatBern
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # One round of quarter sampling (D3; source `lem:bernstein`)

Each of `N` items is kept independently with probability `1/4` (`quarter`). The masks form the
finite product PMF `maskPMF N`, whose measure is the product of the coin measures
(`maskPMF_toMeasure`). For matrices `A_e`, the centered sample is

  `Z(ξ) = Σ_e (4 ξ_e − 1) A_e`  (`qsign b = 4 [b] − 1 ∈ {3, −1}`).

`quarter_tail`: if every `A_e` is symmetric positive semidefinite with `‖A_e‖ ≤ λ`, and
`Σ_e A_e ⪯ I`, then for `0 < δ ≤ 1`

  `P[‖Z‖ ≥ δ] ≤ 2 n exp(−δ² / (8λ))`.

This instantiates the vendored matrix Bernstein inequality
(`RMT.matrix_bernstein_inequality_hdp_all`) with `K = 3λ`. Independence comes from the product
measure (`iIndepFun_pi`), integrability from the finite sample space, and the means
`E(4ξ − 1) = 0` and `E(4ξ − 1)² = 3` from the coin. The variance is
`Σ_e E Z_e² = 3 Σ_e A_e² ⪯ 3λ Σ_e A_e ⪯ 3λ I` by `A² ⪯ ‖A‖ A`, so `σ² ≤ 3λ`. The tail
`2n exp(−(δ²/2)/(σ² + λδ))` is then at most `2n exp(−δ²/(8λ))` for `δ ≤ 1`.

The zero cases are included: `n = 0` (the event is empty), `N = 0`, and `λ = 0`, where every
`A_e` vanishes. `quarter_tail_pmf` is the same bound stated as a `mass` of the mask PMF.
-/

namespace CutQueryComplexity
namespace Spectral

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped Matrix.Norms.L2Operator ENNReal NNReal

noncomputable section

/-- A coin that is `true` with probability `1/4`. -/
def quarter : PMF Bool :=
  PMF.ofFintype (fun b => if b then (1 / 4 : ℝ≥0∞) else 3 / 4) (by
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 3 = 4 by norm_num]
    exact ENNReal.div_self (by norm_num) (by norm_num))

theorem quarter_sum : quarter true + quarter false = 1 := by
  have := PMF.tsum_coe quarter
  rwa [tsum_fintype, Fintype.sum_bool] at this

theorem quarter_true : (quarter true).toReal = 1 / 4 := by
  simp [quarter]

theorem quarter_false : (quarter false).toReal = 3 / 4 := by
  simp [quarter, ENNReal.toReal_div]

/-- `4 [b] − 1`. -/
def qsign (b : Bool) : ℝ := if b then 3 else -1

theorem abs_qsign_le (b : Bool) : |qsign b| ≤ 3 := by
  cases b <;> simp [qsign]

theorem integral_quarter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Bool → E) :
    ∫ b, f b ∂quarter.toMeasure = (1 / 4 : ℝ) • f true + (3 / 4 : ℝ) • f false := by
  rw [PMF.integral_eq_sum, Fintype.sum_bool, quarter_true, quarter_false]

/-- The product measure of `N` independent quarter coins. -/
def maskMeasure (N : ℕ) : Measure (Fin N → Bool) := Measure.pi fun _ => quarter.toMeasure

instance (N : ℕ) : IsProbabilityMeasure (maskMeasure N) := by
  unfold maskMeasure; infer_instance

/-- The mask PMF: `P(ξ) = Π_e P(ξ_e)`. -/
def maskPMF (N : ℕ) : PMF (Fin N → Bool) :=
  PMF.ofFintype (fun ξ => ∏ e, quarter (ξ e)) (by
    rw [← Fintype.prod_sum (fun _ b => quarter b)]
    simp [quarter_sum])

theorem maskPMF_toMeasure (N : ℕ) : (maskPMF N).toMeasure = maskMeasure N := by
  classical
  symm
  refine Measure.pi_eq fun s _ => ?_
  rw [PMF.toMeasure_apply_fintype]
  have hset : (Set.univ.pi s) = ↑(Fintype.piFinset fun e => (s e).toFinset) := by
    ext ξ; simp
  rw [hset]
  have : ∀ ξ, (↑(Fintype.piFinset fun e => (s e).toFinset) : Set (Fin N → Bool)).indicator
      (maskPMF N) ξ = if ξ ∈ Fintype.piFinset (fun e => (s e).toFinset) then
        ∏ e, quarter (ξ e) else 0 := fun ξ => by
    simp only [Set.indicator, Finset.mem_coe]; rfl
  simp only [this, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.prod_univ_sum]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [PMF.toMeasure_apply_fintype]
  simp only [Set.indicator, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b; simp

/-- The centered sample `Z_e(ξ) = (4 ξ_e − 1) A_e`. -/
def qsample {n N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) ℝ) (e : Fin N) (ξ : Fin N → Bool) :
    Matrix (Fin n) (Fin n) ℝ := qsign (ξ e) • A e

theorem integral_eval {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : Bool → E) (e : Fin N) :
    ∫ ξ, f (ξ e) ∂maskMeasure N = ∫ b, f b ∂quarter.toMeasure := by
  have hmp := measurePreserving_eval (fun _ : Fin N => quarter.toMeasure) e
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable StronglyMeasurable.of_discrete.aestronglyMeasurable]
  rfl

theorem isHermitian_smul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (c : ℝ) :
    (c • A).IsHermitian := by
  rw [IsHermitian, conjTranspose_smul, hA.eq, star_trivial]

/-- **One round of quarter sampling** (source `lem:bernstein`). -/
theorem quarter_tail {n N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) ℝ) {lam δ : ℝ}
    (hsym : ∀ e, (A e).IsHermitian) (hpsd : ∀ e x, 0 ≤ x ⬝ᵥ (A e *ᵥ x))
    (hnorm : ∀ e, ‖A e‖ ≤ lam) (hsum : ∀ x, ∑ e, x ⬝ᵥ (A e *ᵥ x) ≤ x ⬝ᵥ x)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (maskMeasure N {ξ | δ ≤ ‖∑ e, qsample A e ξ‖}).toReal ≤
      2 * n * Real.exp (-(δ ^ 2) / (8 * lam)) := by
  have hrhs : 0 ≤ 2 * (n : ℝ) * Real.exp (-(δ ^ 2) / (8 * lam)) := by positivity
  -- degenerate cases: the event is empty
  by_cases hdeg : n = 0 ∨ lam ≤ 0
  · have hempty : {ξ : Fin N → Bool | δ ≤ ‖∑ e, qsample A e ξ‖} = ∅ := by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have hz : ∑ e, qsample A e ξ = 0 := by
        rcases hdeg with hn | hlam
        · subst hn; exact Subsingleton.elim _ _
        · refine sum_eq_zero fun e _ => ?_
          have : ‖A e‖ = 0 := le_antisymm ((hnorm e).trans hlam) (norm_nonneg _)
          simp [qsample, norm_eq_zero.mp this]
      rw [hz, norm_zero]; exact hδ
    rw [hempty, measure_empty, ENNReal.toReal_zero]; exact hrhs
  push Not at hdeg
  obtain ⟨hn, hlam⟩ := hdeg
  -- the Bernstein hypotheses
  have hindep : RMT.MatrixBernsteinIndependent (qsample A) (maskMeasure N) := by
    let _ : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
    unfold RMT.MatrixBernsteinIndependent maskMeasure qsample
    exact iIndepFun_pi (X := fun e (b : Bool) => qsign b • A e)
      fun e => (Measurable.of_discrete).aemeasurable
  have hint : ∀ e, Integrable (qsample A e) (maskMeasure N) := fun e => Integrable.of_finite
  have hint2 : ∀ e, Integrable (fun ξ => (qsample A e ξ) ^ 2) (maskMeasure N) :=
    fun e => Integrable.of_finite
  have hmean : ∀ e, ∫ ξ, qsample A e ξ ∂maskMeasure N = 0 := by
    intro e
    rw [show (fun ξ => qsample A e ξ) = fun ξ => (fun b => qsign b • A e) (ξ e) from rfl,
      integral_eval (fun b => qsign b • A e), integral_quarter]
    simp only [qsign, ↓reduceIte, Bool.false_eq_true, smul_smul]
    rw [← add_smul]; norm_num
  have hherm : ∀ e, ∀ᵐ ξ ∂maskMeasure N, (qsample A e ξ).IsHermitian :=
    fun e => Filter.Eventually.of_forall fun ξ => isHermitian_smul (hsym e) _
  have hK : ∀ e, ∀ᵐ ξ ∂maskMeasure N, ‖qsample A e ξ‖ ≤ 3 * lam :=
    fun e => Filter.Eventually.of_forall fun ξ => by
      rw [qsample, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (abs_qsign_le _) (hnorm e) (norm_nonneg _) (by norm_num)
  have hbern := RMT.matrix_bernstein_inequality_hdp_all (qsample A) (maskMeasure N) (3 * lam)
    (Nat.pos_of_ne_zero hn) hindep hint hint2 hmean hherm hK δ hδ.le
  -- the variance proxy is at most `3λ`
  have hvar : RMT.matrixBernsteinVarianceMatrix (maskMeasure N) (qsample A) =
      ∑ e, (3 : ℝ) • (A e * A e) := by
    unfold RMT.matrixBernsteinVarianceMatrix
    refine sum_congr rfl fun e _ => ?_
    rw [show (fun ξ => (qsample A e ξ) ^ 2) = fun ξ => (fun b => (qsign b • A e) ^ 2) (ξ e)
      from rfl, integral_eval (fun b => (qsign b • A e) ^ 2), integral_quarter]
    simp only [qsign, ↓reduceIte, Bool.false_eq_true, pow_two]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, smul_smul, smul_smul, ← add_smul]; norm_num
  have hσ : RMT.matrixBernsteinVarianceProxy (maskMeasure N) (qsample A) ≤ 3 * lam := by
    unfold RMT.matrixBernsteinVarianceProxy
    rw [hvar]
    have hH : (∑ e, (3 : ℝ) • (A e * A e)).IsHermitian := by
      rw [IsHermitian, conjTranspose_sum]
      refine sum_congr rfl fun e _ => ?_
      rw [conjTranspose_smul, conjTranspose_mul, (hsym e).eq, star_trivial]
    refine norm_le_of_abs_quad_le hH (by positivity) fun x => ?_
    have hquad : x ⬝ᵥ ((∑ e, (3 : ℝ) • (A e * A e)) *ᵥ x) =
        ∑ e, 3 * (x ⬝ᵥ ((A e * A e) *ᵥ x)) := by
      rw [sum_mulVec, dotProduct_sum]
      exact sum_congr rfl fun e _ => by rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hlow : ∀ e, 0 ≤ x ⬝ᵥ ((A e * A e) *ᵥ x) := fun e => by
      rw [← mulVec_mulVec, dot_mulVec_symm (hsym e)]; exact dot_self_nonneg _
    have hup : ∀ e, x ⬝ᵥ ((A e * A e) *ᵥ x) ≤ lam * (x ⬝ᵥ (A e *ᵥ x)) := fun e =>
      (quad_sq_le (hsym e) (hpsd e) x).trans
        (mul_le_mul_of_nonneg_right (hnorm e) (hpsd e x))
    rw [hquad, abs_of_nonneg (sum_nonneg fun e _ => by have := hlow e; positivity)]
    calc ∑ e, 3 * (x ⬝ᵥ ((A e * A e) *ᵥ x)) ≤ ∑ e, 3 * (lam * (x ⬝ᵥ (A e *ᵥ x))) :=
          sum_le_sum fun e _ => by have := hup e; linarith
      _ = 3 * lam * ∑ e, x ⬝ᵥ (A e *ᵥ x) := by rw [mul_sum]; exact sum_congr rfl fun e _ => by ring
      _ ≤ 3 * lam * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left (hsum x) (by positivity)
  -- compare the Bernstein tail with the target
  have hσ0 := RMT.matrixBernsteinVarianceProxy_nonneg (maskMeasure N) (qsample A)
  set σ2 := RMT.matrixBernsteinVarianceProxy (maskMeasure N) (qsample A)
  have hD : 0 < σ2 + 3 * lam * δ / 3 := by positivity
  have hD4 : σ2 + 3 * lam * δ / 3 ≤ 4 * lam := by nlinarith
  have hexp : -(δ ^ 2 / 2) / (σ2 + 3 * lam * δ / 3) ≤ -(δ ^ 2) / (8 * lam) := by
    have h1 : δ ^ 2 / 2 / (4 * lam) ≤ δ ^ 2 / 2 / (σ2 + 3 * lam * δ / 3) :=
      div_le_div_of_nonneg_left (by positivity) hD hD4
    have h2 : -(δ ^ 2) / (8 * lam) = -(δ ^ 2 / 2 / (4 * lam)) := by field_simp; ring
    rw [h2, neg_div]
    linarith
  have hevent : {ξ : Fin N → Bool | δ ≤ ‖∑ e, qsample A e ξ‖} =
      {ω | ‖RMT.matrixBernsteinSum (qsample A) ω‖ ≥ δ} := rfl
  rw [hevent]
  refine hbern.trans ?_
  unfold RMT.matrixBernsteinTailBound
  gcongr

/-- **The PMF form.** -/
theorem quarter_tail_pmf {n N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) ℝ) {lam δ : ℝ}
    (hsym : ∀ e, (A e).IsHermitian) (hpsd : ∀ e x, 0 ≤ x ⬝ᵥ (A e *ᵥ x))
    (hnorm : ∀ e, ‖A e‖ ≤ lam) (hsum : ∀ x, ∑ e, x ⬝ᵥ (A e *ᵥ x) ≤ x ⬝ᵥ x)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Probability.mass (maskPMF N) fun ξ => δ ≤ ‖∑ e, qsample A e ξ‖).toReal ≤
      2 * n * Real.exp (-(δ ^ 2) / (8 * lam)) := by
  have h := quarter_tail A hsym hpsd hnorm hsum hδ hδ1
  rw [← maskPMF_toMeasure, PMF.toMeasure_apply_eq_toOuterMeasure] at h
  exact h

end

end Spectral
end CutQueryComplexity
