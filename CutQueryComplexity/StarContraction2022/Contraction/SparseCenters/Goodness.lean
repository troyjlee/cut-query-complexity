import CutQueryComplexity.StarContraction2022.Contraction.SparseCenters
import CutQueryComplexity.StarContraction2022.Common.Constants
import CutQueryComplexity.StarContraction2022.Common.Basic
import CutQueryComplexity.CanonicalST.Rows
import CutQueryComplexity.Model.RandomizedComposition
import CutQueryComplexity.Probability.Chernoff
import CutQueryComplexity.Probability.FiniteEvents
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Good sparse centers from the actual public Bernoulli sampler

The input rows and crossing subsets occur only in the probability analysis.
The sampler receives just the public center probability. All overlapping row
statistics use the same center set, and are combined by expectation and union
bounds without an independence assumption on the rows.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.SparseCenters

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

private theorem ofReal_nat_fraction (a b : ℕ) (hb : 0 < b) :
    ENNReal.ofReal ((a : ℝ) / b) = (a : ℝ≥0∞) / b := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb),
    ENNReal.ofReal_natCast,ENNReal.ofReal_natCast]

private theorem ofReal_thousandth :
    ENNReal.ofReal (1 / 1000 : ℝ) = (1 / 1000 : ℝ≥0∞) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using
    ofReal_nat_fraction 1 1000 (by norm_num)

private theorem ofReal_quarter :
    ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ℝ≥0∞) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using
    ofReal_nat_fraction 1 4 (by norm_num)

private theorem ofReal_253_thousandths :
    ENNReal.ofReal (253 / 1000 : ℝ) = (253 / 1000 : ℝ≥0∞) := by
  simpa only [Nat.cast_ofNat] using
    ofReal_nat_fraction 253 1000 (by norm_num)

/-- The finite generating function is obtained directly from the actual
Bernoulli point masses and the powerset product identity. -/
theorem bernoulli_power_moment (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1)
    (r : ℝ≥0∞) :
    expect (Probability.bernoulliSubset N p hp) (fun S => r ^ S.card) =
      (p * r + (1 - p)) ^ N.card := by
  rw [CutQueryComplexity.Probability.expect, tsum_fintype]
  have hfilter : univ.filter (fun S : Finset V => S ⊆ N) = N.powerset := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_powerset]
  calc
    _ = ∑ S ∈ univ.filter (fun S : Finset V => S ⊆ N),
        (p * r) ^ S.card * (1 - p) ^ (N.card - S.card) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S ⊆ N
      · simp only [Probability.bernoulliSubset_apply, hS, ite_true, mul_pow]
        ring
      · simp only [Probability.bernoulliSubset_apply, hS, ite_false, zero_mul]
    _ = ∑ S ∈ N.powerset, (∏ _v ∈ S, p * r) * ∏ _v ∈ N \ S, (1 - p) := by
      rw [hfilter]
      apply Finset.sum_congr rfl
      intro S hS
      simp only [Finset.prod_const, card_sdiff_of_subset (mem_powerset.mp hS)]
    _ = ∏ _v ∈ N, (p * r + (1 - p)) :=
      (Finset.prod_add (fun _ : V => p * r) (fun _ => 1 - p) N).symm
    _ = _ := by simp only [Finset.prod_const]

/-- The actual Bernoulli count has its exact exponential moment, derived
from the finite generating function rather than an assumed independent law. -/
theorem bernoulli_expMoment (N : Finset V) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    expMoment (Probability.bernoulliSubset N (ENNReal.ofReal p)
      (ENNReal.ofReal_le_one.mpr hp1)) (fun S => (S.card : ℝ)) t =
      ENNReal.ofReal ((p * Real.exp t + (1 - p)) ^ N.card) := by
  have hb0 : 0 ≤ p * Real.exp t + (1 - p) :=
    add_nonneg (mul_nonneg hp0 (Real.exp_pos t).le) (sub_nonneg.mpr hp1)
  have he (S : Finset V) : ENNReal.ofReal (Real.exp (t * (S.card : ℝ))) =
      ENNReal.ofReal (Real.exp t) ^ S.card := by
    rw [mul_comm, Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos t).le]
  calc
    _ = expect (Probability.bernoulliSubset N (ENNReal.ofReal p)
        (ENNReal.ofReal_le_one.mpr hp1)) (fun S => ENNReal.ofReal (Real.exp t) ^ S.card) :=
      expect_congr_on_support _ (fun S _ => he S)
    _ = (ENNReal.ofReal p * ENNReal.ofReal (Real.exp t) + (1 - ENNReal.ofReal p)) ^ N.card :=
      bernoulli_power_moment _ _ _ _
    _ = _ := by
      rw [ENNReal.ofReal_pow hb0,
        ENNReal.ofReal_add (mul_nonneg hp0 (Real.exp_pos t).le) (sub_nonneg.mpr hp1),
        ENNReal.ofReal_mul hp0, ENNReal.ofReal_sub 1 hp0, ENNReal.ofReal_one]

/-- The usual exponential envelope is proved for this concrete finite law. -/
theorem bernoulli_expMoment_le (N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    expMoment (Probability.bernoulliSubset N (ENNReal.ofReal p)
      (ENNReal.ofReal_le_one.mpr hp1)) (fun S => (S.card : ℝ)) t ≤
      ENNReal.ofReal (Real.exp ((Real.exp t - 1) * (p * N.card))) := by
  rw [bernoulli_expMoment N p hp0 hp1 t]
  apply ENNReal.ofReal_le_ofReal
  have hb : p * Real.exp t + (1 - p) ≤ Real.exp (p * (Real.exp t - 1)) := by
    calc
      p * Real.exp t + (1 - p) = p * (Real.exp t - 1) + 1 := by ring
      _ ≤ _ := Real.add_one_le_exp _
  calc
    _ ≤ Real.exp (p * (Real.exp t - 1)) ^ N.card :=
      pow_le_pow_left₀ (add_nonneg (mul_nonneg hp0 (Real.exp_pos t).le)
        (sub_nonneg.mpr hp1)) hb _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The sharper half-mean lower tail required for sparse centers. -/
theorem bernoulli_half_lower_tail (N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mass (Probability.bernoulliSubset N (ENNReal.ofReal p)
      (ENNReal.ofReal_le_one.mpr hp1)) (fun S => (S.card : ℝ) ≤ p * N.card / 2) ≤
      ENNReal.ofReal (Real.exp (-(p * N.card) / 8)) := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have he : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hm := bernoulli_expMoment_le N p hp0 hp1 (-Real.log 2)
  have heq : (Real.exp (-Real.log 2) - 1) * (p * N.card) = -(p * N.card) / 2 := by
    rw [he]
    ring
  rw [heq] at hm
  apply (lower_tail_le_exp
    (Probability.bernoulliSubset N (ENNReal.ofReal p) (ENNReal.ofReal_le_one.mpr hp1))
    (fun S => (S.card : ℝ)) (p * N.card / 2) (neg_nonpos.mpr hlog0) hm).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ p * (N.card : ℝ) by positivity)
  nlinarith

/-- A factor-three center-count guard is covered by the actual factor-two
upper tail. This statement includes the deterministic probability endpoints. -/
theorem bernoulli_triple_upper_tail (N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mass (Probability.bernoulliSubset N (ENNReal.ofReal p)
      (ENNReal.ofReal_le_one.mpr hp1)) (fun S => 3 * (p * N.card) < (S.card : ℝ)) ≤
      ENNReal.ofReal (Real.exp (-(p * N.card) / 4)) := by
  have hmean : 0 ≤ p * (N.card : ℝ) := by positivity
  have hbound := chernoff_upper
    (Probability.bernoulliSubset N (ENNReal.ofReal p) (ENNReal.ofReal_le_one.mpr hp1))
    (fun S => (S.card : ℝ)) (μ := p * N.card) (ε := 1)
    hmean (by norm_num) (by norm_num) (bernoulli_expMoment_le N p hp0 hp1 (1 / 2))
  apply (mass_mono _ (Q := fun S : Finset V => (1 + (1 : ℝ)) * (p * N.card) ≤ S.card) ?_).trans
  · simpa only [one_pow, one_mul, neg_div] using hbound
  · intro S hS
    linarith

/-- The actual center law depends only on the public degree parameter. -/
def centerLaw (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) : PMF (Finset V) :=
  sampleCenters (ENNReal.ofReal (Schedule.centerProbability d))
    (ENNReal.ofReal_le_one.mpr (Schedule.centerProbability_le_one d hd))

/-- The bad set is the measured low center-degree set. It contains all
vertices, including centers, so its eventual inside/outside split is exact. -/
def badRows (N : V → Finset V) (d : ℕ) (R : Finset V) : Finset V :=
  univ.filter fun v => ((N v ∩ R).card : ℝ) ≤ 50000 * Real.log d

def GoodCenters (N C : V → Finset V) (d : ℕ) (R : Finset V) : Prop :=
  Schedule.CenterGuard (Fintype.card V) d R.card ∧
  Schedule.BadGuard (Fintype.card V) d (badRows N d R).card ∧
  (∀ v, Probability.crossingRatio (C v) (N v ∩ R) ≤ 3 / 5) ∧
  (∑ v, Probability.crossingRatio (C v) (N v ∩ R)) ≤ 8

theorem degree_pos (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) : 0 < d := by
  have := Schedule.degreeCutoff_ge.trans hd
  omega

theorem centerProbability_mul_degree (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    Schedule.centerProbability d * d = 100000 * Real.log d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (degree_pos d hd).ne'
  unfold Schedule.centerProbability
  field_simp

theorem center_mean_lower (d m : ℕ) (hd : Schedule.degreeCutoff ≤ d) (hm : d ≤ m) :
    100000 * Real.log d ≤ Schedule.centerProbability d * m := by
  rw [← centerProbability_mul_degree d hd]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hm)
    (Schedule.centerProbability_pos d hd).le

/-- The numerical cutoff is strong enough for the later first-moment clock. -/
theorem degree_million (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) : 1000000 ≤ d := by
  have he : (1000000 : ℝ) ≤ Real.exp 17 := by
    calc
      (1000000 : ℝ) ≤ (5 / 2 : ℝ) ^ 17 := by norm_num
      _ ≤ (Real.exp 1) ^ 17 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 17
      _ = Real.exp 17 := by rw [← Real.exp_nat_mul]; norm_num
  have hdR : Real.exp 17 ≤ (d : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hd)
  exact_mod_cast he.trans hdR

/-- A single row's bad-center event is bounded in its actual marginal law.
The argument does not condition on any other row or on a later query guard. -/
theorem bad_row_mass_le (N : V → Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hdegree : ∀ v, d ≤ (N v).card) (v : V) :
    mass (centerLaw (V := V) d hd) (fun R => v ∈ badRows N d R) ≤
      ENNReal.ofReal (Real.exp (-12500 * Real.log d)) := by
  have hp0 := (Schedule.centerProbability_pos d hd).le
  have hmean := center_mean_lower d (N v).card hd (hdegree v)
  calc
    _ ≤ mass (centerLaw (V := V) d hd) (fun R =>
        ((N v ∩ R).card : ℝ) ≤ Schedule.centerProbability d * (N v).card / 2) := by
      apply mass_mono
      intro R hR
      have hv := (mem_filter.mp hR).2
      linarith
    _ = mass (Probability.bernoulliSubset (N v) (ENNReal.ofReal (Schedule.centerProbability d))
        (ENNReal.ofReal_le_one.mpr (Schedule.centerProbability_le_one d hd)))
        (fun S => (S.card : ℝ) ≤ Schedule.centerProbability d * (N v).card / 2) := by
      rw [centerLaw,
        ← mass_map (sampleCenters (V := V) (ENNReal.ofReal (Schedule.centerProbability d))
          (ENNReal.ofReal_le_one.mpr (Schedule.centerProbability_le_one d hd)))
          (fun R => N v ∩ R)
          (fun T => (T.card : ℝ) ≤ Schedule.centerProbability d * (N v).card / 2),
        sampleCenters_restriction]
    _ ≤ ENNReal.ofReal (Real.exp (-(Schedule.centerProbability d * (N v).card) / 8)) :=
      bernoulli_half_lower_tail _ _ hp0 (Schedule.centerProbability_le_one d hd)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith

theorem expect_badRows_le (N : V → Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hdegree : ∀ v, d ≤ (N v).card) :
    expect (centerLaw (V := V) d hd) (fun R => ((badRows N d R).card : ℝ≥0∞)) ≤
      (Fintype.card V : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-12500 * Real.log d)) := by
  have he (R : Finset V) : ((badRows N d R).card : ℝ≥0∞) =
      ∑ v : V, if v ∈ badRows N d R then (1 : ℝ≥0∞) else 0 := by simp
  calc
    _ = expect (centerLaw (V := V) d hd)
        (fun R => ∑ v : V, if v ∈ badRows N d R then (1 : ℝ≥0∞) else 0) :=
      expect_congr_on_support _ (fun R _ => he R)
    _ = ∑ v : V, mass (centerLaw (V := V) d hd) (fun R => v ∈ badRows N d R) := by
      calc
        _ = ∑ v : V, expect (centerLaw (V := V) d hd)
            (fun R => if v ∈ badRows N d R then (1 : ℝ≥0∞) else 0) := expect_sum _ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro v _
          calc
            _ = expect (centerLaw (V := V) d hd)
                (fun R => @ite ℝ≥0∞ (v ∈ badRows N d R) (Classical.propDecidable _) 1 0) := by
              apply expect_congr_on_support
              intro R _
              by_cases hv : v ∈ badRows N d R <;> simp only [hv, ite_true, ite_false]
            _ = _ := by
              simpa only [one_mul] using CutQueryComplexity.Probability.expect_indicator
                (centerLaw (V := V) d hd) (fun R => v ∈ badRows N d R) 1
    _ ≤ ∑ _v : V, ENNReal.ofReal (Real.exp (-12500 * Real.log d)) :=
      Finset.sum_le_sum (fun v _ => bad_row_mass_le N d hd hdegree v)
    _ = _ := by simp only [Finset.sum_const, card_univ, nsmul_eq_mul]

/-- The small-row exponent pays for the full shared bad-set count. -/
theorem bad_exponential_debit (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    1000 * (d : ℝ) * Real.exp (-12500 * Real.log d) ≤ 1 / 1000 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast degree_pos d hd
  have hlog : 0 ≤ Real.log (d : ℝ) := by linarith [Schedule.log_degree_ge d hd]
  have htail : Real.exp (-12500 * Real.log d) ≤ 1 / (d : ℝ) ^ 2 := by
    calc
      _ ≤ Real.exp (-2 * Real.log d) := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 / (d : ℝ) ^ 2 := by
        rw [show -2 * Real.log (d : ℝ) = -(2 * Real.log (d : ℝ)) by ring,
          Real.exp_neg]
        have he : Real.exp (2 * Real.log (d : ℝ)) = (d : ℝ) ^ 2 := by
          simpa only [Nat.cast_ofNat, Real.exp_log hdR] using Real.exp_nat_mul (Real.log (d : ℝ)) 2
        simp only [he, one_div]
  calc
    _ ≤ 1000 * (d : ℝ) * (1 / (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 1000 / (d : ℝ) := by field_simp [hdR.ne']
    _ ≤ 1 / 1000 := by
      rw [div_le_iff₀ hdR]
      have hm : (1000000 : ℝ) ≤ d := by exact_mod_cast degree_million d hd
      linarith

/-- Markov on the shared bad-set cardinality. No independence between the
row indicators is asserted or needed. -/
theorem bad_guard_failure_le (N : V → Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hn : d ≤ Fintype.card V)
    (hdegree : ∀ v, d ≤ (N v).card) :
    mass (centerLaw (V := V) d hd)
      (fun R => ¬ Schedule.BadGuard (Fintype.card V) d (badRows N d R).card) ≤
        (1 / 1000 : ℝ≥0∞) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast degree_pos d hd
  have hnR : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (degree_pos d hd).trans_le hn
  let a := ENNReal.ofReal ((Fintype.card V : ℝ) / (1000 * d))
  have ha0 : a ≠ 0 := by dsimp [a]; positivity
  have hm := mul_mass_le_expect (centerLaw (V := V) d hd)
    (fun R => ¬ Schedule.BadGuard (Fintype.card V) d (badRows N d R).card)
    (fun R => ((badRows N d R).card : ℝ≥0∞)) a (by
      intro R _ hR
      have hlt : Fintype.card V < 1000 * (badRows N d R).card * d := Nat.lt_of_not_ge hR
      have hltR : (Fintype.card V : ℝ) < 1000 * (badRows N d R).card * d := by
        exact_mod_cast hlt
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * d)).mpr
      nlinarith)
  calc
    _ ≤ expect (centerLaw (V := V) d hd)
        (fun R => ((badRows N d R).card : ℝ≥0∞)) / a := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl ha0)
        (Or.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm] using hm
    _ ≤ ((Fintype.card V : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-12500 * Real.log d))) / a :=
      ENNReal.div_le_div (expect_badRows_le N d hd hdegree) le_rfl
    _ = ENNReal.ofReal (1000 * (d : ℝ) * Real.exp (-12500 * Real.log d)) := by
      rw [show (Fintype.card V : ℝ≥0∞) = ENNReal.ofReal (Fintype.card V : ℝ) by simp,
        ← ENNReal.ofReal_mul hnR.le]
      change ENNReal.ofReal ((Fintype.card V : ℝ) * Real.exp (-12500 * Real.log d)) /
        ENNReal.ofReal ((Fintype.card V : ℝ) / (1000 * d)) = _
      rw [← ENNReal.ofReal_div_of_pos (by positivity :
        (0 : ℝ) < (Fintype.card V : ℝ) / (1000 * d))]
      congr 1
      field_simp [hnR.ne', hdR.ne'] <;> ring
    _ ≤ ENNReal.ofReal (1 / 1000 : ℝ) :=
      ENNReal.ofReal_le_ofReal (bad_exponential_debit d hd)
    _ = _ := ofReal_thousandth

theorem center_guard_failure_le (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (hn : d ≤ Fintype.card V) :
    mass (centerLaw (V := V) d hd)
      (fun R => ¬ Schedule.CenterGuard (Fintype.card V) d R.card) ≤ (1 / 1000 : ℝ≥0∞) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast degree_pos d hd
  have hp0 := (Schedule.centerProbability_pos d hd).le
  have hm := center_mean_lower d (Fintype.card V) hd hn
  have he : (3 * (Schedule.centerProbability d * (Fintype.card V : ℝ))) * d =
      300000 * Fintype.card V * Real.log d := by
    calc
      _ = 3 * Fintype.card V * (Schedule.centerProbability d * d) := by ring
      _ = _ := by rw [centerProbability_mul_degree d hd]; ring
  calc
    _ ≤ mass (centerLaw (V := V) d hd) (fun R =>
        3 * (Schedule.centerProbability d * (Fintype.card V : ℝ)) < R.card) := by
      apply mass_mono
      intro R hR
      have hlt : 300000 * (Fintype.card V : ℝ) * Real.log d < (R.card : ℝ) * d := by
        apply lt_of_not_ge
        intro hle
        exact hR ⟨card_le_univ R, hle⟩
      rw [← he] at hlt
      nlinarith
    _ ≤ ENNReal.ofReal (Real.exp (-(Schedule.centerProbability d * Fintype.card V) / 4)) := by
      simpa only [centerLaw, sampleCenters, card_univ] using
        bernoulli_triple_upper_tail (univ : Finset V) (Schedule.centerProbability d)
          hp0 (Schedule.centerProbability_le_one d hd)
    _ ≤ ENNReal.ofReal (1 / 1000 : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      have hlarge : 1000 ≤ Real.exp (Schedule.centerProbability d * Fintype.card V / 4) := by
        have hlog := Schedule.log_degree_ge d hd
        have hx := Real.add_one_le_exp (Schedule.centerProbability d * Fintype.card V / 4)
        linarith
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000) hlarge
      simpa only [neg_div, Real.exp_neg, one_div] using hh
    _ = _ := ofReal_thousandth

/-- Linearity of expectation transfers the total cut-ratio budget to the
single shared center set. -/
theorem ratio_sum_mean_le (N C : V → Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hC : ∀ v, C v ⊆ N v)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2) :
    expect (centerLaw (V := V) d hd)
      (fun R => ENNReal.ofReal (∑ v, Probability.crossingRatio (C v) (N v ∩ R))) ≤ 2 := by
  have he (R : Finset V) : ENNReal.ofReal (∑ v, Probability.crossingRatio (C v) (N v ∩ R)) =
      ∑ v, ENNReal.ofReal (Probability.crossingRatio (C v) (N v ∩ R)) :=
    ENNReal.ofReal_sum_of_nonneg (fun v _ => Probability.crossingRatio_nonneg _ _)
  calc
    _ = expect (centerLaw (V := V) d hd)
        (fun R => ∑ v, ENNReal.ofReal (Probability.crossingRatio (C v) (N v ∩ R))) :=
      expect_congr_on_support _ (fun R _ => he R)
    _ = ∑ v, expect (centerLaw (V := V) d hd)
        (fun R => ENNReal.ofReal (Probability.crossingRatio (C v) (N v ∩ R))) :=
      expect_sum _ _ _
    _ ≤ ∑ v, ENNReal.ofReal ((C v).card / ((N v).card : ℝ)) :=
      Finset.sum_le_sum (fun v _ => sampleCenters_ratio_mean_le _ _ _ _ (hC v))
    _ = ENNReal.ofReal (∑ v, (C v).card / ((N v).card : ℝ)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun v _ => by positivity)).symm
    _ ≤ ENNReal.ofReal (2 : ℝ) := ENNReal.ofReal_le_ofReal hsum
    _ = _ := by norm_num

theorem ratio_sum_failure_le (N C : V → Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hC : ∀ v, C v ⊆ N v)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2) :
    mass (centerLaw (V := V) d hd)
      (fun R => 8 < ∑ v, Probability.crossingRatio (C v) (N v ∩ R)) ≤ (1 / 4 : ℝ≥0∞) := by
  have hm := mul_mass_le_expect (centerLaw (V := V) d hd)
    (fun R => 8 < ∑ v, Probability.crossingRatio (C v) (N v ∩ R))
    (fun R => ENNReal.ofReal (∑ v, Probability.crossingRatio (C v) (N v ∩ R)))
    8 (by
      intro R _ hR
      simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hR.le)
  calc
    _ ≤ expect (centerLaw (V := V) d hd)
        (fun R => ENNReal.ofReal (∑ v, Probability.crossingRatio (C v) (N v ∩ R))) / 8 := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
      simpa only [mul_comm] using hm
    _ ≤ 2 / 8 := ENNReal.div_le_div (ratio_sum_mean_le N C d hd hC hsum) le_rfl
    _ = _ := by
      calc
        (2 : ℝ≥0∞) / 8 = ENNReal.ofReal ((2 : ℝ) / 8) :=
          (ofReal_nat_fraction 2 8 (by norm_num)).symm
        _ = ENNReal.ofReal ((1 : ℝ) / 4) := by congr 1; norm_num
        _ = _ := ofReal_quarter

/-- The maximum ratio bound uses the proved tenth-tail for each row and a
union bound. Overlapping sampled rows need not be independent. -/
theorem ratio_max_failure_le (N C : V → Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hdegree : ∀ v, d ≤ (N v).card)
    (hC : ∀ v, C v ⊆ N v)
    (hmax : ∀ v, (C v).card / ((N v).card : ℝ) ≤ 1 / 2)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2) :
    mass (centerLaw (V := V) d hd)
      (fun R => ∃ v, 3 / 5 < Probability.crossingRatio (C v) (N v ∩ R)) ≤ (1 / 1000 : ℝ≥0∞) := by
  let p := ENNReal.ofReal (Schedule.centerProbability d)
  have hp0 : 0 < p := ENNReal.ofReal_pos.mpr (Schedule.centerProbability_pos d hd)
  have hp1 : p ≤ 1 := ENNReal.ofReal_le_one.mpr (Schedule.centerProbability_le_one d hd)
  have hrow (v : V) : mass (centerLaw (V := V) d hd)
      (fun R => 3 / 5 < Probability.crossingRatio (C v) (N v ∩ R)) ≤
        (200 * ENNReal.ofReal ((C v).card / ((N v).card : ℝ))) / ((d : ℝ≥0∞) * p) := by
    calc
      _ ≤ mass (centerLaw (V := V) d hd) (fun R =>
          (C v).card / ((N v).card : ℝ) + 1 / 10 < Probability.crossingRatio (C v) (N v ∩ R)) := by
        apply mass_mono
        intro R hR
        linarith [hmax v]
      _ ≤ (200 * ENNReal.ofReal ((C v).card / ((N v).card : ℝ))) /
          (((N v).card : ℝ≥0∞) * p) :=
        sampleCenters_ratio_tenth_tail _ _ p hp0 hp1 (hC v)
      _ ≤ _ := by
        apply ENNReal.div_le_div le_rfl
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree v) (by positivity)
  have he : (fun R => ∃ v, 3 / 5 < Probability.crossingRatio (C v) (N v ∩ R)) =
      (fun R => ∃ v ∈ (univ : Finset V),
        3 / 5 < Probability.crossingRatio (C v) (N v ∩ R)) := by
    funext R
    simp only [mem_univ, true_and]
  rw [he]
  have hdR : (0 : ℝ) < d := by exact_mod_cast degree_pos d hd
  have hdp0 : 0 < (d : ℝ) * Schedule.centerProbability d :=
    mul_pos hdR (Schedule.centerProbability_pos d hd)
  calc
    _ ≤ ∑ v : V, mass (centerLaw (V := V) d hd)
        (fun R => 3 / 5 < Probability.crossingRatio (C v) (N v ∩ R)) :=
      mass_exists_finset_le _ _ _
    _ ≤ ∑ v : V, (200 * ENNReal.ofReal ((C v).card / ((N v).card : ℝ))) /
        ((d : ℝ≥0∞) * p) := Finset.sum_le_sum (fun v _ => hrow v)
    _ = 200 * (∑ v, ENNReal.ofReal ((C v).card / ((N v).card : ℝ))) / ((d : ℝ≥0∞) * p) := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul,← Finset.mul_sum]
    _ ≤ 200 * ENNReal.ofReal (2 : ℝ) / ((d : ℝ≥0∞) * p) := by
      apply ENNReal.div_le_div _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => by positivity)]
      exact ENNReal.ofReal_le_ofReal hsum
    _ = ENNReal.ofReal (400 / ((d : ℝ) * Schedule.centerProbability d)) := by
      dsimp [p]
      rw [ENNReal.ofReal_div_of_pos hdp0, ENNReal.ofReal_mul hdR.le, ENNReal.ofReal_natCast]
      norm_num
    _ ≤ ENNReal.ofReal (1 / 1000 : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ hdp0).mpr
      have heq := centerProbability_mul_degree d hd
      have hlog := Schedule.log_degree_ge d hd
      nlinarith
    _ = _ := ofReal_thousandth

/-- All four actual center-sampling failures are combined additively. The
result is stronger than the two-thirds success probability used downstream. -/
theorem goodCenters_failure_le (N C : V → Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hn : d ≤ Fintype.card V)
    (hdegree : ∀ v, d ≤ (N v).card) (hC : ∀ v, C v ⊆ N v)
    (hmax : ∀ v, (C v).card / ((N v).card : ℝ) ≤ 1 / 2)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2) :
    mass (centerLaw (V := V) d hd) (fun R => ¬ GoodCenters N C d R) ≤ (253 / 1000 : ℝ≥0∞) := by
  let A := fun R : Finset V => ¬ Schedule.CenterGuard (Fintype.card V) d R.card
  let B := fun R : Finset V => ¬ Schedule.BadGuard (Fintype.card V) d (badRows N d R).card
  let Cbad := fun R : Finset V => ∃ v, 3 / 5 < Probability.crossingRatio (C v) (N v ∩ R)
  let D := fun R : Finset V => 8 < ∑ v, Probability.crossingRatio (C v) (N v ∩ R)
  calc
    _ ≤ mass (centerLaw (V := V) d hd) (fun R => A R ∨ B R ∨ Cbad R ∨ D R) := by
      apply mass_mono
      intro R hR
      by_contra hfail
      apply hR
      refine ⟨?_, ?_, ?_, ?_⟩
      · by_contra hA
        exact hfail (Or.inl hA)
      · by_contra hB
        exact hfail (Or.inr (Or.inl hB))
      · intro v
        by_contra hv
        exact hfail (Or.inr (Or.inr (Or.inl ⟨v, lt_of_not_ge hv⟩)))
      · by_contra hD
        exact hfail (Or.inr (Or.inr (Or.inr (lt_of_not_ge hD))))
    _ ≤ mass (centerLaw (V := V) d hd) A +
        (mass (centerLaw (V := V) d hd) B +
          (mass (centerLaw (V := V) d hd) Cbad + mass (centerLaw (V := V) d hd) D)) := by
      apply (mass_or_le _ _ _).trans
      apply add_le_add le_rfl
      apply (mass_or_le _ _ _).trans
      exact add_le_add le_rfl (mass_or_le _ _ _)
    _ ≤ 1 / 1000 + (1 / 1000 + (1 / 1000 + (1 / 4 : ℝ≥0∞))) :=
      add_le_add (center_guard_failure_le d hd hn)
        (add_le_add (bad_guard_failure_le N d hd hn hdegree)
          (add_le_add (ratio_max_failure_le N C d hd hdegree hC hmax hsum)
            (ratio_sum_failure_le N C d hd hC hsum)))
    _ = _ := by
      calc
        (1 / 1000 : ℝ≥0∞) + (1 / 1000 + (1 / 1000 + 1 / 4)) =
            ENNReal.ofReal ((1 / 1000 : ℝ) + (1 / 1000 + (1 / 1000 + 1 / 4))) := by
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num),
            ENNReal.ofReal_add (by norm_num) (by norm_num),
            ENNReal.ofReal_add (by norm_num) (by norm_num)]
          simp only [ofReal_thousandth, ofReal_quarter]
        _ = ENNReal.ofReal ((253 : ℝ) / 1000) := by congr 1; norm_num
        _ = _ := ofReal_253_thousandths

/-- The probability of a genuinely good sampled center set is at least
two thirds. Only original row-degree and cut-ratio bounds are premises. -/
theorem goodCenters_success (N C : V → Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hn : d ≤ Fintype.card V)
    (hdegree : ∀ v, d ≤ (N v).card) (hC : ∀ v, C v ⊆ N v)
    (hmax : ∀ v, (C v).card / ((N v).card : ℝ) ≤ 1 / 2)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2) :
    (2 / 3 : ℝ) ≤ (mass (centerLaw (V := V) d hd) (GoodCenters N C d)).toReal := by
  have hf : mass (centerLaw (V := V) d hd) (fun R => ¬ GoodCenters N C d R) ≤
      ENNReal.ofReal (253 / 1000 : ℝ) := by
    rw [ofReal_253_thousandths]
    exact goodCenters_failure_le N C d hd hn hdegree hC hmax hsum
  have hs := success_of_failure_le (centerLaw (V := V) d hd) (GoodCenters N C d)
    (by norm_num : (0 : ℝ) ≤ 253 / 1000) hf
  linarith

/-- Analysis-only row tables reuse the existing positive-support definition.
They are never passed to the public center sampler. -/
def inputRows (G : SimpleInput V) (v : V) : Finset V :=
  AllPairs.rowSupport G.toWeighted v univ

def inputCrossRows (G : SimpleInput V) (S : Finset V) (v : V) : Finset V :=
  AllPairs.rowSupport G.toWeighted v (if v ∈ S then Sᶜ else S)

theorem input_unweighted (G : SimpleInput V) : AllPairsAudit.Unweighted G.toWeighted := by
  intro u v
  have hb := (G.w u v).isLt
  have hv : (G.w u v : ℕ) = 0 ∨ (G.w u v : ℕ) = 1 := by omega
  rcases hv with h | h
  · left
    change ((G.w u v : ℕ) : ℝ) = 0
    exact_mod_cast h
  · right
    change ((G.w u v : ℕ) : ℝ) = 1
    exact_mod_cast h

theorem inputRows_card (G : SimpleInput V) (v : V) :
    ((inputRows G v).card : ℝ) = G.toWeighted.degree v := by
  rw [inputRows, CanonicalST.rowSupport_card_eq_sum G.toWeighted (input_unweighted G)]
  rfl

theorem inputCrossRows_card (G : SimpleInput V) (S : Finset V) (v : V) :
    ((inputCrossRows G S v).card : ℝ) = AllPairsAudit.crossing G.toWeighted S v := by
  by_cases hv : v ∈ S <;>
    simp only [inputCrossRows, AllPairsAudit.crossing, hv, ite_true, ite_false] <;>
    exact CanonicalST.rowSupport_card_eq_sum G.toWeighted (input_unweighted G) v _

theorem inputCrossRows_subset (G : SimpleInput V) (S : Finset V) (v : V) :
    inputCrossRows G S v ⊆ inputRows G v := by
  intro w hw
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hw).2⟩

theorem inputRatio_eq (G : SimpleInput V) (S : Finset V) (v : V) :
    (inputCrossRows G S v).card / ((inputRows G v).card : ℝ) =
      crossingFraction G.toWeighted S v := by
  rw [inputCrossRows_card, inputRows_card]
  rfl

/-- An original minimum cut strictly below the measured degree lower bound
supplies all ratio premises internally. The sampler itself has only d as an
input; the fixed original shore appears solely in this probability theorem. -/
theorem minimum_center_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hS : IsMinCut G.toWeighted S)
    (hdegree : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v) (hcut : G.toWeighted.cut S < d) :
    (2 / 3 : ℝ) ≤ (mass (centerLaw (V := V) d hd)
      (GoodCenters (inputRows G) (inputCrossRows G S) d)).toReal := by
  have hdeg : ∀ v, d ≤ (inputRows G v).card := by
    intro v
    have hv := hdegree v
    rw [← inputRows_card G v] at hv
    exact_mod_cast hv
  have hn : d ≤ Fintype.card V := by
    obtain ⟨v, _⟩ := hS.1.1
    exact (hdeg v).trans (card_le_univ (inputRows G v))
  have hdR : (0 : ℝ) < d := by exact_mod_cast degree_pos d hd
  have hfrac := minimum_fractions hS hdR hdegree hcut
  apply goodCenters_success (inputRows G) (inputCrossRows G S) d hd hn hdeg
    (inputCrossRows_subset G S)
  · intro v
    rw [inputRatio_eq]
    exact hfrac.1 v
  · simp_rw [inputRatio_eq]
    exact hfrac.2

/-- The actual public answers determine the tested bad set. -/
def measuredBadSet (d : ℕ) (answers : V → ℝ) : Finset V :=
  univ.filter fun v => answers v ≤ 50000 * Real.log d

theorem centerStatistics_input_eval (G : SimpleInput V) (R : Finset V) :
    (centerStatistics R).eval G.toWeighted.cut =
      fun v => ((inputRows G v ∩ R).card : ℝ) := by
  rw [centerStatistics_eval]
  funext v
  have he : inputRows G v ∩ R = AllPairs.rowSupport G.toWeighted v R := by
    ext w
    simp [inputRows, AllPairs.rowSupport, and_comm]
  rw [he, CanonicalST.rowSupport_card_eq_sum G.toWeighted (input_unweighted G)]
  rfl

theorem measuredBadSet_eval (G : SimpleInput V) (d : ℕ) (R : Finset V) :
    measuredBadSet d ((centerStatistics R).eval G.toWeighted.cut) = badRows (inputRows G) d R := by
  rw [centerStatistics_input_eval]
  rfl

/-- Measure the center rows and test the two literal public guards. The
returned tuple contains only the sampled centers, computed bad set and answers. -/
def checkedCenterStatistics (d : ℕ) (R : Finset V) :
    DTree (Finset V) ℝ (Option (Finset V × Finset V × (V → ℝ))) (3 * Fintype.card V) :=
  (centerStatistics R).map fun answers =>
    if Schedule.CenterGuard (Fintype.card V) d R.card ∧
        Schedule.BadGuard (Fintype.card V) d (measuredBadSet d answers).card then
      some (R, measuredBadSet d answers, answers)
    else none

theorem checkedCenterStatistics_eval (G : SimpleInput V) (d : ℕ) (R : Finset V) :
    (checkedCenterStatistics d R).eval G.toWeighted.cut =
      if Schedule.CenterGuard (Fintype.card V) d R.card ∧
          Schedule.BadGuard (Fintype.card V) d (badRows (inputRows G) d R).card then
        some (R, badRows (inputRows G) d R, fun v => ((inputRows G v ∩ R).card : ℝ))
      else none := by
  simp only [checkedCenterStatistics, DTree.eval_map, centerStatistics_input_eval]
  rfl

/-- The complete public center stage: independent sampling followed by the
three original cut families. No hidden graph or fixed cut is an argument. -/
def centersProgram (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    RTree (Finset V) ℝ (Option (Finset V × Finset V × (V → ℝ))) (3 * Fintype.card V) :=
  RTree.mix ((centerLaw (V := V) d hd).map fun R =>
    RTree.ofDeterministic (checkedCenterStatistics d R))

theorem centersProgram_eval (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) :
    (centersProgram (V := V) d hd).eval read =
      (centerLaw (V := V) d hd).map (fun R => (checkedCenterStatistics d R).eval read) := by
  have he (R : Finset V) : (RTree.ofDeterministic (checkedCenterStatistics d R)).eval read =
      PMF.pure ((checkedCenterStatistics d R).eval read) := by
    simp [RTree.eval, DTree.eval,PMF.pure_map]
  rw [centersProgram, RTree.eval_mix, PMF.bind_map]
  simp only [Function.comp_def, he]
  rfl

theorem centersProgram_every_oracle (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) {out : Option (Finset V × Finset V × (V → ℝ)) × ℕ}
    (hout : out ∈ (RTree.run read (centersProgram (V := V) d hd)).support) :
    out.2 ≤ 3 * Fintype.card V := RTree.cost_le _ _ hout

/-- Original-input success for the actual checked query program. Its result
retains the measured counts needed by the later public learning routines. -/
theorem centersProgram_minimum_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hS : IsMinCut G.toWeighted S)
    (hdegree : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v) (hcut : G.toWeighted.cut S < d) :
    (2 / 3 : ℝ) ≤ (mass ((centersProgram (V := V) d hd).eval G.toWeighted.cut)
      (fun out => ∃ R, GoodCenters (inputRows G) (inputCrossRows G S) d R ∧
        out = some (R, badRows (inputRows G) d R, fun v => ((inputRows G v ∩ R).card : ℝ)))).toReal := by
  rw [centersProgram_eval, mass_map]
  apply (minimum_center_success G S d hd hS hdegree hcut).trans
  apply ENNReal.toReal_mono (mass_ne_top _ _)
  apply mass_mono
  intro R hR
  refine ⟨R, hR, ?_⟩
  rw [checkedCenterStatistics_eval, if_pos ⟨hR.1, hR.2.1⟩]


#print axioms bernoulli_power_moment
#print axioms bernoulli_expMoment
#print axioms bernoulli_expMoment_le
#print axioms bernoulli_half_lower_tail
#print axioms bernoulli_triple_upper_tail
#print axioms bad_row_mass_le
#print axioms expect_badRows_le
#print axioms bad_exponential_debit
#print axioms bad_guard_failure_le
#print axioms center_guard_failure_le
#print axioms ratio_sum_mean_le
#print axioms ratio_sum_failure_le
#print axioms ratio_max_failure_le
#print axioms goodCenters_failure_le
#print axioms goodCenters_success
#print axioms inputRatio_eq
#print axioms minimum_center_success
#print axioms centerStatistics_input_eval
#print axioms measuredBadSet_eval
#print axioms checkedCenterStatistics_eval
#print axioms centersProgram_eval
#print axioms centersProgram_every_oracle
#print axioms centersProgram_minimum_success

end
end CutQueryComplexity.StarContraction2022.Contraction.SparseCenters
