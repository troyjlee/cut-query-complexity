import CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Sampling
import CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.Goodness

/-!
# Quality of public Bernoulli centers for uniform star contraction

The center probability is arbitrary public data. All graph rows and crossing
subsets occur only in probability theorems. The sixth-tail estimate follows
from the checked fixed-size variance and the actual binomial inverse moment;
overlapping neighborhood rows are combined by a union bound, not independence.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.UniformStars

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def GoodRows (N C : V → Finset V) (R : Finset V) : Prop :=
  (∀ v, Probability.crossingRatio (C v) (N v ∩ R) ≤ 2 / 3) ∧
    (∑ v, Probability.crossingRatio (C v) (N v ∩ R)) ≤ 8

/-- The deviation needed for original crossing density at most one half. -/
theorem fixedSize_ratio_sixth_tail (N C : Finset V) (j : ℕ)
    (hC : C ⊆ N) (hj : 0 < j) (hjN : j ≤ N.card) :
    mass (Probability.fixedSize N j hjN)
        (fun S => (C.card : ℝ) / N.card + 1 / 6 < Probability.crossingRatio C S) ≤
      ENNReal.ofReal (36 * ((C.card : ℝ) / N.card) / j) := by
  have h := Probability.fixedSize_ratio_tail N C j hC hj hjN (1 / 6) (by norm_num)
  convert h using 1
  congr 1
  ring

/-- The zero-size sample has ratio zero. For all positive sizes integrate
the fixed-size tail against the actual binomial size law. -/
theorem bernoulli_ratio_sixth_tail (N C : Finset V) (p : ℝ≥0∞)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hC : C ⊆ N) :
    mass (Probability.bernoulliSubset N p hp1)
        (fun S => (C.card : ℝ) / N.card + 1 / 6 < Probability.crossingRatio C S) ≤
      (72 * ENNReal.ofReal ((C.card : ℝ) / N.card)) / ((N.card : ℝ≥0∞) * p) := by
  let rho : ℝ := (C.card : ℝ) / N.card
  have hrho : 0 ≤ rho := by dsimp [rho]; positivity
  rw [Probability.bernoulliSubset_eq_sizeMixture, Probability.sizeMixture, mass_bind]
  change expect (Probability.binomialSize N.card p hp1) (fun j =>
    mass (Probability.fixedSize N j.val (Nat.le_of_lt_succ j.isLt))
      (fun S => rho + 1 / 6 < Probability.crossingRatio C S)) ≤ _
  calc
    _ ≤ expect (Probability.binomialSize N.card p hp1)
        (fun j => (36 * ENNReal.ofReal rho) * Probability.positiveInverse j.val) := by
      apply expect_mono_on_support
      intro j _
      by_cases hj : j.val = 0
      · have hnot : ¬ rho + 1 / 6 < 0 := by linarith
        simp only [hj, Probability.fixedSize_zero, mass_pure, Probability.crossingRatio_empty,
          Probability.positiveInverse, ite_true, mul_zero, hnot, ite_false, le_refl]
      · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
        have ht := fixedSize_ratio_sixth_tail N C j.val hC hjpos (Nat.le_of_lt_succ j.isLt)
        have hjR : (0 : ℝ) < j.val := by exact_mod_cast hjpos
        change mass (Probability.fixedSize N j.val (Nat.le_of_lt_succ j.isLt))
          (fun S => rho + 1 / 6 < Probability.crossingRatio C S) ≤
          ENNReal.ofReal (36 * rho / j.val) at ht
        rw [ENNReal.ofReal_div_of_pos hjR,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 36),
          show ENNReal.ofReal (36 : ℝ) = 36 by norm_num, ENNReal.ofReal_natCast] at ht
        simpa only [Probability.positiveInverse, hj, ite_false, div_eq_mul_inv] using ht
    _ = (36 * ENNReal.ofReal rho) *
        expect (Probability.binomialSize N.card p hp1)
          (fun j => Probability.positiveInverse j.val) := expect_const_mul _ _ _
    _ ≤ (36 * ENNReal.ofReal rho) * (2 / (((N.card + 1 : ℕ) : ℝ≥0∞) * p)) :=
      mul_le_mul le_rfl (Probability.binomialSize_positiveInverse_le N.card p hp0 hp1)
        (by positivity) (by positivity)
    _ = (72 * ENNReal.ofReal rho) / (((N.card + 1 : ℕ) : ℝ≥0∞) * p) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := ENNReal.div_le_div_left
      (mul_le_mul (by exact_mod_cast Nat.le_succ N.card) le_rfl
        (by positivity) (by positivity)) _

/-- Restrict the same globally sampled center set to this particular row. -/
theorem center_ratio_sixth_tail (N C : Finset V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hC : C ⊆ N) :
    mass (centerLaw p hp1)
        (fun R => (C.card : ℝ) / N.card + 1 / 6 < Probability.crossingRatio C (N ∩ R)) ≤
      (72 * ENNReal.ofReal ((C.card : ℝ) / N.card)) /
        ((N.card : ℝ≥0∞) * ENNReal.ofReal p) := by
  rw [← mass_map (centerLaw p hp1) (fun R => N ∩ R)
    (fun T => (C.card : ℝ) / N.card + 1 / 6 < Probability.crossingRatio C T),
    centerLaw_restriction]
  exact bernoulli_ratio_sixth_tail N C (ENNReal.ofReal p)
    (ENNReal.ofReal_pos.mpr hp0) (ENNReal.ofReal_le_one.mpr hp1) hC

theorem ratio_sum_mean_le (N C : V → Finset V) (p : ℝ) (hp1 : p ≤ 1)
    (hC : ∀ v, C v ⊆ N v)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2) :
    expect (centerLaw p hp1)
      (fun R => ENNReal.ofReal (∑ v, Probability.crossingRatio (C v) (N v ∩ R))) ≤ 2 := by
  have he (R : Finset V) : ENNReal.ofReal (∑ v, Probability.crossingRatio (C v) (N v ∩ R)) =
      ∑ v, ENNReal.ofReal (Probability.crossingRatio (C v) (N v ∩ R)) :=
    ENNReal.ofReal_sum_of_nonneg (fun v _ => Probability.crossingRatio_nonneg _ _)
  calc
    _ = expect (centerLaw p hp1)
        (fun R => ∑ v, ENNReal.ofReal (Probability.crossingRatio (C v) (N v ∩ R))) :=
      expect_congr_on_support _ (fun R _ => he R)
    _ = ∑ v, expect (centerLaw p hp1)
        (fun R => ENNReal.ofReal (Probability.crossingRatio (C v) (N v ∩ R))) :=
      expect_sum _ _ _
    _ ≤ ∑ v, ENNReal.ofReal ((C v).card / ((N v).card : ℝ)) :=
      Finset.sum_le_sum (fun v _ => Contraction.sampleCenters_ratio_mean_le _ _ _ _ (hC v))
    _ = ENNReal.ofReal (∑ v, (C v).card / ((N v).card : ℝ)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun v _ => by positivity)).symm
    _ ≤ ENNReal.ofReal (2 : ℝ) := ENNReal.ofReal_le_ofReal hsum
    _ = _ := by norm_num

theorem ratio_sum_failure_le (N C : V → Finset V) (p : ℝ) (hp1 : p ≤ 1)
    (hC : ∀ v, C v ⊆ N v)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2) :
    mass (centerLaw p hp1)
      (fun R => 8 < ∑ v, Probability.crossingRatio (C v) (N v ∩ R)) ≤
        ENNReal.ofReal (1 / 4 : ℝ) := by
  have hm := mul_mass_le_expect (centerLaw p hp1)
    (fun R => 8 < ∑ v, Probability.crossingRatio (C v) (N v ∩ R))
    (fun R => ENNReal.ofReal (∑ v, Probability.crossingRatio (C v) (N v ∩ R))) 8 (by
      intro R _ hR
      simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hR.le)
  calc
    _ ≤ expect (centerLaw p hp1)
        (fun R => ENNReal.ofReal (∑ v, Probability.crossingRatio (C v) (N v ∩ R))) / 8 := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
      simpa only [mul_comm] using hm
    _ ≤ 2 / 8 := ENNReal.div_le_div (ratio_sum_mean_le N C p hp1 hC hsum) le_rfl
    _ = _ := by
      rw [show (1 / 4 : ℝ) = 2 / 8 by norm_num,
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8)]
      norm_num

/-- A first-moment threshold of 1728 makes the union of all large-ratio
events cost at most one twelfth. This is derived from the original densities. -/
theorem ratio_max_failure_le (N C : V → Finset V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hC : ∀ v, C v ⊆ N v)
    (hmax : ∀ v, (C v).card / ((N v).card : ℝ) ≤ 1 / 2)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2)
    (hmean : ∀ v, 1728 ≤ p * (N v).card) :
    mass (centerLaw p hp1)
      (fun R => ∃ v, 2 / 3 < Probability.crossingRatio (C v) (N v ∩ R)) ≤
        ENNReal.ofReal (1 / 12 : ℝ) := by
  have hrow (v : V) : mass (centerLaw p hp1)
      (fun R => 2 / 3 < Probability.crossingRatio (C v) (N v ∩ R)) ≤
        ENNReal.ofReal (((C v).card / ((N v).card : ℝ)) / 24) := by
    have hden : 0 < ((N v).card : ℝ) * p := by nlinarith [hmean v]
    have hrho : 0 ≤ (C v).card / ((N v).card : ℝ) := by positivity
    calc
      _ ≤ mass (centerLaw p hp1) (fun R =>
          (C v).card / ((N v).card : ℝ) + 1 / 6 <
            Probability.crossingRatio (C v) (N v ∩ R)) := by
        apply mass_mono
        intro R hR
        linarith [hmax v]
      _ ≤ (72 * ENNReal.ofReal ((C v).card / ((N v).card : ℝ))) /
          (((N v).card : ℝ≥0∞) * ENNReal.ofReal p) :=
        center_ratio_sixth_tail _ _ p hp0 hp1 (hC v)
      _ = ENNReal.ofReal
          (72 * ((C v).card / ((N v).card : ℝ)) / (((N v).card : ℝ) * p)) := by
        rw [ENNReal.ofReal_div_of_pos hden,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 72),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        norm_num
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply (div_le_iff₀ hden).mpr
        have hm := mul_le_mul_of_nonneg_left (hmean v) hrho
        nlinarith
  have he : (fun R => ∃ v, 2 / 3 < Probability.crossingRatio (C v) (N v ∩ R)) =
      (fun R => ∃ v ∈ (univ : Finset V),
        2 / 3 < Probability.crossingRatio (C v) (N v ∩ R)) := by
    funext R
    simp only [mem_univ, true_and]
  rw [he]
  calc
    _ ≤ ∑ v : V, mass (centerLaw p hp1)
        (fun R => 2 / 3 < Probability.crossingRatio (C v) (N v ∩ R)) :=
      mass_exists_finset_le _ _ _
    _ ≤ ∑ v : V, ENNReal.ofReal (((C v).card / ((N v).card : ℝ)) / 24) :=
      Finset.sum_le_sum (fun v _ => hrow v)
    _ = ENNReal.ofReal ((∑ v, (C v).card / ((N v).card : ℝ)) / 24) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => by positivity), Finset.sum_div]
    _ ≤ ENNReal.ofReal (2 / 24 : ℝ) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hsum (by norm_num))
    _ = _ := by congr 1; norm_num

theorem quality_failure_le (N C : V → Finset V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hC : ∀ v, C v ⊆ N v)
    (hmax : ∀ v, (C v).card / ((N v).card : ℝ) ≤ 1 / 2)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2)
    (hmean : ∀ v, 1728 ≤ p * (N v).card) :
    mass (centerLaw p hp1) (fun R => ¬ GoodRows N C R) ≤ ENNReal.ofReal (1 / 3 : ℝ) := by
  calc
    _ ≤ mass (centerLaw p hp1) (fun R =>
        (∃ v, 2 / 3 < Probability.crossingRatio (C v) (N v ∩ R)) ∨
          8 < ∑ v, Probability.crossingRatio (C v) (N v ∩ R)) := by
      apply mass_mono
      intro R hR
      by_contra hbad
      apply hR
      refine ⟨?_, ?_⟩
      · intro v
        by_contra hv
        exact hbad (Or.inl ⟨v, lt_of_not_ge hv⟩)
      · by_contra hs
        exact hbad (Or.inr (lt_of_not_ge hs))
    _ ≤ mass (centerLaw p hp1)
        (fun R => ∃ v, 2 / 3 < Probability.crossingRatio (C v) (N v ∩ R)) +
        mass (centerLaw p hp1) (fun R => 8 < ∑ v, Probability.crossingRatio (C v) (N v ∩ R)) :=
      mass_or_le _ _ _
    _ ≤ ENNReal.ofReal (1 / 12 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) :=
      add_le_add (ratio_max_failure_le N C p hp0 hp1 hC hmax hsum hmean)
        (ratio_sum_failure_le N C p hp1 hC hsum)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 12) (by norm_num)]
      congr 1
      norm_num

theorem quality_success (N C : V → Finset V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hC : ∀ v, C v ⊆ N v)
    (hmax : ∀ v, (C v).card / ((N v).card : ℝ) ≤ 1 / 2)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2)
    (hmean : ∀ v, 1728 ≤ p * (N v).card) :
    (2 / 3 : ℝ) ≤ (mass (centerLaw p hp1) (GoodRows N C)).toReal := by
  have h := success_of_failure_le (centerLaw p hp1) (GoodRows N C)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (quality_failure_le N C p hp0 hp1 hC hmax hsum hmean)
  linarith

/-- The pinned 1200 log n condition already forces n at least 16 when
sampling probabilities are at most one and a row has at most n entries. -/
theorem logarithmic_mean_large (n m : ℕ) (p : ℝ) (hn : 2 ≤ n) (hm : m ≤ n)
    (hp1 : p ≤ 1) (hmean : 1200 * Real.log n ≤ p * m) :
    1728 ≤ p * m := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hpm : p * m ≤ (n : ℝ) := by
    calc
      p * m ≤ 1 * (m : ℝ) := mul_le_mul_of_nonneg_right hp1 (Nat.cast_nonneg _)
      _ ≤ n := by simpa only [one_mul] using hmR
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hn16 : (16 : ℝ) ≤ n := by nlinarith
  have hlog16 : (2 : ℝ) ≤ Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hnlog : Real.log 16 ≤ Real.log n := Real.log_le_log (by norm_num) hn16
  nlinarith

/-- Generic public-p quality at the paper's literal logarithmic threshold. -/
theorem quality_success_log (N C : V → Finset V) (p : ℝ)
    (hn : 2 ≤ Fintype.card V) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC : ∀ v, C v ⊆ N v)
    (hmax : ∀ v, (C v).card / ((N v).card : ℝ) ≤ 1 / 2)
    (hsum : (∑ v, (C v).card / ((N v).card : ℝ)) ≤ 2)
    (hmean : ∀ v, 1200 * Real.log (Fintype.card V) ≤ p * (N v).card) :
    (2 / 3 : ℝ) ≤ (mass (centerLaw p hp1) (GoodRows N C)).toReal := by
  have hppos : 0 < p := by
    by_contra hpos
    have hpz : p = 0 := le_antisymm (le_of_not_gt hpos) hp0
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
    have hm := hmean v
    rw [hpz, zero_mul] at hm
    have hlog : 0 < Real.log (Fintype.card V) := Real.log_pos (by exact_mod_cast (by omega : 1 < Fintype.card V))
    nlinarith
  apply quality_success N C p hppos hp1 hC hmax hsum
  intro v
  exact logarithmic_mean_large _ _ p hn (card_le_univ (N v)) hp1 (hmean v)

/-- Suppressing outgoing choices at centers can only improve both quality
statistics. This is the row table that the actual star kernel receives. -/
theorem goodRows_star_quality (N C : V → Finset V) (R : Finset V)
    (h : GoodRows N C R) :
    (∀ v, Probability.crossingRatio (C v) (starRows R N v) ≤ 2 / 3) ∧
      (∑ v, Probability.crossingRatio (C v) (starRows R N v)) ≤ 8 := by
  have hrow (v : V) : Probability.crossingRatio (C v) (starRows R N v) ≤
      Probability.crossingRatio (C v) (N v ∩ R) := by
    by_cases hv : v ∈ R
    · simpa only [starRows, hv, ite_true, Probability.crossingRatio_empty] using
        Probability.crossingRatio_nonneg (C v) (N v ∩ R)
    · simp only [starRows, hv, ite_false, le_refl]
  exact ⟨fun v => (hrow v).trans (h.1 v), (Finset.sum_le_sum (fun v _ => hrow v)).trans h.2⟩

section MinimumCut

open Contraction.SparseCenters (inputRows inputCrossRows inputCrossRows_subset inputRatio_eq inputRows_card)

/-- An actual nontrivial original minimum cut discharges the original-row
density premises. Neither the input graph nor this shore selects the sampler. -/
theorem minimum_quality_success (G : SimpleInput V) (S : Finset V) (p δ : ℝ)
    (hn : 2 ≤ Fintype.card V) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    (hS : IsMinCut G.toWeighted S) (hdegree : ∀ v, δ ≤ G.toWeighted.degree v)
    (hcut : G.toWeighted.cut S < δ)
    (hmean : 1200 * Real.log (Fintype.card V) ≤ p * δ) :
    (2 / 3 : ℝ) ≤ (mass (centerLaw p hp1)
      (GoodRows (inputRows G) (inputCrossRows G S))).toReal := by
  have hfrac := Contraction.minimum_fractions hS hδ hdegree hcut
  apply quality_success_log (inputRows G) (inputCrossRows G S) p hn hp0 hp1
    (inputCrossRows_subset G S)
  · intro v
    rw [inputRatio_eq]
    exact hfrac.1 v
  · simp_rw [inputRatio_eq]
    exact hfrac.2
  · intro v
    apply hmean.trans
    apply mul_le_mul_of_nonneg_left _ hp0
    rw [inputRows_card]
    exact hdegree v

end MinimumCut

#print axioms fixedSize_ratio_sixth_tail
#print axioms bernoulli_ratio_sixth_tail
#print axioms center_ratio_sixth_tail
#print axioms ratio_sum_mean_le
#print axioms ratio_max_failure_le
#print axioms quality_failure_le
#print axioms quality_success_log
#print axioms goodRows_star_quality
#print axioms minimum_quality_success

end
end CutQueryComplexity.StarContraction2022.Quantum.UniformStars
