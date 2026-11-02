import CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Budget
import CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Quality
import CutQueryComplexity.StarContraction2022.Contraction.Joint.Attachments

/-!
# Survival under the original uniform-star law

The complete row table is fixed before invoking the product-law theorem.
Center-size and coverage failures are removed additively from the original
joint law. No sampler here is conditioned on acceptance by a guard.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.UniformStars

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every selected edge avoids its fixed forbidden row. -/
def Avoids (C : V → Finset V) (f : V → Option V) : Prop :=
  ∀ v, (f v).elim True (fun w => w ∉ C v)

theorem choiceLaw_avoids_mass (N C : V → Finset V) :
    mass (choiceLaw N) (Avoids C) =
      ENNReal.ofReal (∏ v, (1 - Probability.crossingRatio (C v) (N v))) := by
  change mass (choiceLaw N) (fun f => ∀ v, (f v).elim True (fun w => w ∉ C v)) = _
  rw [choiceLaw_rectangle N (fun v o => o.elim True (fun w => w ∉ C v))]
  simp_rw [Contraction.Joint.CenterAttachment.list_survival_factor]
  exact (ENNReal.ofReal_prod_of_nonneg (fun v _ =>
    sub_nonneg.mpr (Probability.crossingRatio_le_one _ _))).symm

/-- The literal one-star survival constant for each complete fixed table. -/
theorem starChoiceLaw_survival (N C : V → Finset V) (R : Finset V)
    (hgood : GoodRows N C R) :
    ENNReal.ofReal ((3 : ℝ) ^ (-12 : ℤ)) ≤ mass (starChoiceLaw R N) (Avoids C) := by
  rw [starChoiceLaw, choiceLaw_avoids_mass]
  apply ENNReal.ofReal_le_ofReal
  have h := goodRows_star_quality N C R hgood
  have hprod := Contraction.Joint.product_survival_lower
    (fun v => Probability.crossingRatio (C v) (starRows R N v)) (2 / 3) 8
    (by norm_num) (by norm_num) (fun v => Probability.crossingRatio_nonneg _ _) h.1 h.2
  norm_num at hprod ⊢
  exact hprod

/-- Integrate the actual conditional kernel, after fixing all centers and rows. -/
theorem centerChoiceLaw_survival (N C : V → Finset V) (p : ℝ) (hp1 : p ≤ 1)
    (hquality : (2 / 3 : ℝ) ≤ (mass (centerLaw p hp1) (GoodRows N C)).toReal) :
    ENNReal.ofReal (2 * (3 : ℝ) ^ (-13 : ℤ)) ≤
      mass (centerChoiceLaw p hp1 (fun _ => N)) (fun x => Avoids C x.2) := by
  have h := centerChoiceLaw_integrate p hp1 (fun _ => N) (GoodRows N C)
    (fun x => Avoids C x.2) (ENNReal.ofReal ((3 : ℝ) ^ (-12 : ℤ)))
    (fun R _ hR => starChoiceLaw_survival N C R hR)
  have hq := ENNReal.ofReal_le_of_le_toReal hquality
  calc
    _ = ENNReal.ofReal (2 / 3 : ℝ) * ENNReal.ofReal ((3 : ℝ) ^ (-12 : ℤ)) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
      congr 1
      norm_num
    _ ≤ mass (centerLaw p hp1) (GoodRows N C) *
        ENNReal.ofReal ((3 : ℝ) ^ (-12 : ℤ)) :=
      mul_le_mul hq le_rfl (by positivity) (by positivity)
    _ ≤ _ := h

/-- The factor-two tail is proved at t = log 2 for the actual Bernoulli law. -/
theorem bernoulli_double_upper_tail (N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mass (Probability.bernoulliSubset N (ENNReal.ofReal p)
      (ENNReal.ofReal_le_one.mpr hp1)) (fun R => 2 * p * N.card ≤ (R.card : ℝ)) ≤
      ENNReal.ofReal (Real.exp (-p * N.card / 3)) := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := Contraction.SparseCenters.bernoulli_expMoment_le N p hp0 hp1 (Real.log 2)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hm
  apply (upper_tail_le_exp
    (Probability.bernoulliSubset N (ENNReal.ofReal p) (ENNReal.ofReal_le_one.mpr hp1))
    (fun R : Finset V => (R.card : ℝ)) (2 * p * N.card) hlog0 hm).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ p * (N.card : ℝ) by positivity)
  nlinarith

theorem center_size_failure_le (n : ℕ) :
    mass (centerLaw (V := Fin n) (centerProbability n) (centerProbability_le_one n))
      (fun R => kcap n < R.card) ≤
      ENNReal.ofReal (Real.exp (-centerProbability n * n / 3)) := by
  apply (mass_mono _ (Q := fun R : Finset (Fin n) =>
    2 * centerProbability n * n ≤ (R.card : ℝ)) ?_).trans
  · simpa only [centerLaw, Contraction.sampleCenters, card_univ, Fintype.card_fin] using
      bernoulli_double_upper_tail (univ : Finset (Fin n)) (centerProbability n)
        (centerProbability_nonneg n) (centerProbability_le_one n)
  · intro R hR
    have hRn : R.card ≤ n := by simpa only [Fintype.card_fin] using card_le_univ R
    have hceil : ⌈2 * centerProbability n * (n : ℝ)⌉₊ < R.card := by
      unfold kcap at hR
      omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast hceil.le)

theorem center_empty_row_mass (N : Finset V) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mass (centerLaw p hp1) (fun R => N ∩ R = ∅) =
      ENNReal.ofReal ((1 - p) ^ N.card) := by
  rw [← mass_map (centerLaw p hp1) (fun R => N ∩ R) (fun S => S = ∅),
    centerLaw_restriction, mass_eq_tsum]
  rw [tsum_eq_single (∅ : Finset V) (by intro S hS; simp [hS])]
  simp only [ite_true, Probability.bernoulliSubset_apply, empty_subset,
    card_empty, pow_zero, Nat.sub_zero, one_mul]
  rw [ENNReal.ofReal_pow (sub_nonneg.mpr hp1), ENNReal.ofReal_sub 1 hp0,
    ENNReal.ofReal_one]

theorem center_empty_row_le (N : Finset V) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mass (centerLaw p hp1) (fun R => N ∩ R = ∅) ≤
      ENNReal.ofReal (Real.exp (-p * N.card)) := by
  rw [center_empty_row_mass N p hp0 hp1]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp (-p) ^ N.card :=
      pow_le_pow_left₀ (sub_nonneg.mpr hp1)
        (by linarith [Real.add_one_le_exp (-p)]) _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Only noncenters need a nonempty row in order to join a center. -/
def Covered (N : V → Finset V) (R : Finset V) : Prop :=
  ∀ v, v ∉ R → (N v ∩ R).Nonempty

theorem center_coverage_failure_le (N : V → Finset V) (p δ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hdegree : ∀ v, δ ≤ (N v).card) :
    mass (centerLaw p hp1) (fun R => ¬ Covered N R) ≤
      ENNReal.ofReal ((Fintype.card V : ℝ) * Real.exp (-p * δ)) := by
  have h := mass_failure_le_card_mul (centerLaw p hp1) (univ : Finset V)
    (fun v R => (N v ∩ R).Nonempty) (Covered N) (ENNReal.ofReal (Real.exp (-p * δ)))
    (by intro R _ hR v _; exact hR v (mem_univ v)) (by
      intro v _
      calc
        _ = mass (centerLaw p hp1) (fun R => N v ∩ R = ∅) := by
          congr 1
          funext R
          exact propext Finset.not_nonempty_iff_eq_empty
        _ ≤ ENNReal.ofReal (Real.exp (-p * (N v).card)) :=
          center_empty_row_le _ p hp0 hp1
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left (hdegree v) (neg_nonpos.mpr hp0))
  simpa only [card_univ, ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card V)),
    ENNReal.ofReal_natCast] using h

def BadCenters {n : ℕ} (N : Fin n → Finset (Fin n)) (R : Finset (Fin n)) : Prop :=
  kcap n < R.card ∨ ¬ Covered N R

theorem badCenters_mass_le {n : ℕ} (N : Fin n → Finset (Fin n)) (δ : ℝ)
    (hn : 2 ≤ n) (hp : centerProbability n < 1)
    (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ)
    (hdegree : ∀ v, δ ≤ (N v).card) :
    mass (centerLaw (centerProbability n) (centerProbability_le_one n)) (BadCenters N) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-13 : ℤ)) := by
  calc
    _ ≤ mass (centerLaw (centerProbability n) (centerProbability_le_one n))
        (fun R => kcap n < R.card) +
        mass (centerLaw (centerProbability n) (centerProbability_le_one n))
          (fun R => ¬ Covered N R) := mass_or_le _ _ _
    _ ≤ ENNReal.ofReal (Real.exp (-centerProbability n * n / 3)) +
        ENNReal.ofReal ((n : ℝ) * Real.exp (-centerProbability n * δ)) :=
      add_le_add (center_size_failure_le n) (by
        simpa only [Fintype.card_fin] using center_coverage_failure_le N
          (centerProbability n) δ (centerProbability_nonneg n)
          (centerProbability_le_one n) hdegree)
    _ = ENNReal.ofReal (Real.exp (-centerProbability n * n / 3) +
        (n : ℝ) * Real.exp (-centerProbability n * δ)) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (bad_mass_envelope hn hp hδ)

/-- The graph enters only the proof of quality and coverage. The actual joint
law remains the original Bernoulli sample followed by its fixed-table kernel. -/
theorem minimum_guarded_survival {n : ℕ} (G : SimpleInput (Fin n))
    (S : Finset (Fin n)) (δ : ℝ) (hn : 2 ≤ n) (hp : centerProbability n < 1)
    (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ)
    (hS : IsMinCut G.toWeighted S) (hdegree : ∀ v, δ ≤ G.toWeighted.degree v)
    (hcut : G.toWeighted.cut S < δ) :
    ENNReal.ofReal ((3 : ℝ) ^ (-13 : ℤ)) ≤
      mass (centerChoiceLaw (centerProbability n) (centerProbability_le_one n)
        (fun _ => Contraction.SparseCenters.inputRows G)) (fun x =>
          Avoids (Contraction.SparseCenters.inputCrossRows G S) x.2 ∧
            ¬ BadCenters (Contraction.SparseCenters.inputRows G) x.1) := by
  let N := Contraction.SparseCenters.inputRows G
  let C := Contraction.SparseCenters.inputCrossRows G S
  have hδ0 : 0 < δ := lt_of_lt_of_le (by
    exact_mod_cast ProductPrograms.rootThreshold_pos (show 0 < n by omega)) hδ
  have hquality := minimum_quality_success G S (centerProbability n) δ
    (by simpa only [Fintype.card_fin] using hn) (centerProbability_nonneg n)
    (centerProbability_le_one n) hδ0 hS hdegree hcut
    (by simpa only [Fintype.card_fin] using quality_mean_bound hn hp hδ)
  have hsurv := centerChoiceLaw_survival N C (centerProbability n)
    (centerProbability_le_one n) hquality
  have hbad := badCenters_mass_le N δ hn hp hδ (by
    intro v
    simpa only [N, Contraction.SparseCenters.inputRows_card] using hdegree v)
  have hsub := centerChoiceLaw_subtract_bad (centerProbability n)
    (centerProbability_le_one n) (fun _ => N) (fun x => Avoids C x.2) (BadCenters N)
  apply le_trans _ hsub
  calc
    _ = ENNReal.ofReal (2 * (3 : ℝ) ^ (-13 : ℤ)) -
        ENNReal.ofReal ((3 : ℝ) ^ (-13 : ℤ)) := by
      rw [← ENNReal.ofReal_sub _ (by positivity)]
      congr 1
      ring
    _ ≤ _ := tsub_le_tsub hsurv hbad

#print axioms choiceLaw_avoids_mass
#print axioms starChoiceLaw_survival
#print axioms centerChoiceLaw_survival
#print axioms bernoulli_double_upper_tail
#print axioms center_size_failure_le
#print axioms center_empty_row_mass
#print axioms center_empty_row_le
#print axioms center_coverage_failure_le
#print axioms badCenters_mass_le
#print axioms minimum_guarded_survival

end
end CutQueryComplexity.StarContraction2022.Quantum.UniformStars
