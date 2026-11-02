import CutQueryComplexity.StarContraction2022.Contraction.SparseCenters
import CutQueryComplexity.Probability.FiniteEvents
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! # Actual shared-sample row isolation

One public Bernoulli subset is shared by all rows in a trial. Restriction to
a fixed row has the exact binomial law; no independence between rows is
claimed. Fresh trials are the actual finite product PMF. The dyadic range,
singleton boundary and uniform one-eighth isolation bound are proved here.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest

noncomputable section
open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Public sampling law, including probabilities zero and one. -/
def sampleBlue (blue : Finset V) (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    PMF (Finset V) :=
  Probability.bernoulliSubset blue (ENNReal.ofReal p) (ENNReal.ofReal_le_one.mpr hp1)

theorem sampleBlue_supported_subset (blue : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {S : Finset V}
    (hS : S ∈ (sampleBlue blue p hp0 hp1).support) : S ⊆ blue := by
  by_contra h
  have hz : sampleBlue blue p hp0 hp1 S = 0 := by
    simp [sampleBlue, Probability.bernoulliSubset_apply, h]
  exact ((PMF.mem_support_iff _ _).mp hS) hz

/-- Restriction integrates all bits outside the row out of the same law. -/
theorem sampleBlue_restriction (blue N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : N ⊆ blue) :
    (sampleBlue blue p hp0 hp1).map (fun S => N ∩ S) =
      Probability.bernoulliSubset N (ENNReal.ofReal p)
        (ENNReal.ofReal_le_one.mpr hp1) := by
  unfold sampleBlue
  rw [← Contraction.sampleCenters_restriction blue, PMF.map_comp]
  have he : (fun S : Finset V => N ∩ S) ∘ (fun S => blue ∩ S) =
      (fun S => N ∩ S) := by
    funext S
    ext v
    simp only [Function.comp_apply, mem_inter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hN h.1, h.2⟩⟩
  rw [he, Contraction.sampleCenters_restriction]

theorem isolation_mass_ennreal (blue N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : N ⊆ blue) :
    mass (sampleBlue blue p hp0 hp1) (fun S => (N ∩ S).card = 1) =
      (N.card : ℝ≥0∞) *
        (ENNReal.ofReal p * (1 - ENNReal.ofReal p) ^ (N.card - 1)) := by
  rw [← mass_map (sampleBlue blue p hp0 hp1) (fun S => N ∩ S)
    (fun S => S.card = 1), sampleBlue_restriction blue N p hp0 hp1 hN,
    Probability.bernoulliSubset_size_mass]
  simp only [Nat.choose_one_right, pow_one]

theorem isolation_mass (blue N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : N ⊆ blue) :
    (mass (sampleBlue blue p hp0 hp1) (fun S => (N ∩ S).card = 1)).toReal =
      (N.card : ℝ) * p * (1 - p) ^ (N.card - 1) := by
  rw [isolation_mass_ennreal blue N p hp0 hp1 hN]
  have hsub : 1 - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    rw [ENNReal.ofReal_sub 1 hp0, ENNReal.ofReal_one]
  rw [hsub]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]
  ring

/-- The analytic estimate includes d=1 and p=1. For d≥2, the logarithmic
bound gives (1-p)^(d-1)≥exp(-1)>1/4. -/
theorem isolation_polynomial_lower (d : ℕ) (hd : 0 < d) (p : ℝ)
    (hlo : 1 / (2 * (d : ℝ)) ≤ p) (hhi : p ≤ 1 / (d : ℝ)) :
    (1 / 8 : ℝ) ≤ (d : ℝ) * p * (1 - p) ^ (d - 1) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp0 : 0 ≤ p := (by positivity : (0 : ℝ) ≤ 1 / (2 * (d : ℝ))).trans hlo
  by_cases hd1 : d = 1
  · subst d
    norm_num at hlo ⊢
    linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
  have hpHalf : p ≤ 1 / 2 := hhi.trans
    (one_div_le_one_div_of_le (by norm_num) hd2)
  have hq : 0 < 1 - p := by linarith
  have hdp : (d : ℝ) * p ≤ 1 := by
    have h := (le_div_iff₀ hdR).mp hhi
    nlinarith
  have hdpLo : (1 / 2 : ℝ) ≤ (d : ℝ) * p := by
    have h := (div_le_iff₀ (show 0 < 2 * (d : ℝ) by positivity)).mp hlo
    nlinarith
  have hlog : -p / (1 - p) ≤ Real.log (1 - p) := by
    have h := Real.one_sub_inv_le_log_of_pos hq
    have he : 1 - (1 - p)⁻¹ = -p / (1 - p) := by
      field_simp [hq.ne']
      <;> ring
    rwa [he] at h
  have hratio : ((d : ℝ) - 1) * p / (1 - p) ≤ 1 := by
    apply (div_le_iff₀ hq).mpr
    nlinarith
  have hneg : -1 ≤ ((d : ℝ) - 1) * (-p / (1 - p)) := by
    convert neg_le_neg hratio using 1 <;> ring
  have hpowlog : -1 ≤ ((d : ℝ) - 1) * Real.log (1 - p) :=
    hneg.trans (mul_le_mul_of_nonneg_left hlog (by linarith))
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  have hexp : Real.exp (-1) ≤ (1 - p) ^ (d - 1) := by
    have h := Real.exp_le_exp.mpr hpowlog
    rw [← hcast, ← Real.log_pow, Real.exp_log (pow_pos hq _)] at h
    exact h
  have hquarter : (1 / 4 : ℝ) ≤ (1 - p) ^ (d - 1) := by
    have hbound := Real.exp_neg_one_gt_d9
    exact (show (1 / 4 : ℝ) ≤ Real.exp (-1) by linarith).trans hexp
  calc
    (1 / 8 : ℝ) = (1 / 2 : ℝ) * (1 / 4 : ℝ) := by norm_num
    _ ≤ ((d : ℝ) * p) * (1 - p) ^ (d - 1) :=
      mul_le_mul hdpLo hquarter (by norm_num) (by positivity)

theorem isolation_lower (blue N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : N ⊆ blue) (hne : N.Nonempty)
    (hlo : 1 / (2 * (N.card : ℝ)) ≤ p) (hhi : p ≤ 1 / (N.card : ℝ)) :
    (1 / 8 : ℝ) ≤
      (mass (sampleBlue blue p hp0 hp1) (fun S => (N ∩ S).card = 1)).toReal := by
  rw [isolation_mass blue N p hp0 hp1 hN]
  exact isolation_polynomial_lower N.card (card_pos.mpr hne) p hlo hhi

theorem isolation_failure_le (blue N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : N ⊆ blue) (hne : N.Nonempty)
    (hlo : 1 / (2 * (N.card : ℝ)) ≤ p) (hhi : p ≤ 1 / (N.card : ℝ)) :
    mass (sampleBlue blue p hp0 hp1) (fun S => (N ∩ S).card ≠ 1) ≤
      (7 / 8 : ℝ≥0∞) := by
  have hl := isolation_lower blue N p hp0 hp1 hN hne hlo hhi
  have h := failure_le_of_success (sampleBlue blue p hp0 hp1)
    (fun S => (N ∩ S).card = 1) (by norm_num : (0 : ℝ) ≤ 7 / 8) (by linarith)
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8),
    ENNReal.ofReal_ofNat] using h

/-- Fresh trials, each retaining its shared sample for all row/mask queries. -/
def isolationTrials (blue : Finset V) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (K : ℕ) : PMF (Fin K → Finset V) :=
  Probability.product fun _ : Fin K => sampleBlue blue p hp0 hp1

theorem isolationTrials_failure_mass (blue N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (K : ℕ) :
    mass (isolationTrials blue p hp0 hp1 K)
        (fun tape => ∀ k, (N ∩ tape k).card ≠ 1) =
      mass (sampleBlue blue p hp0 hp1) (fun S => (N ∩ S).card ≠ 1) ^ K := by
  simpa only [isolationTrials, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (Probability.mass_product (fun _ : Fin K => sampleBlue blue p hp0 hp1)
      (fun _ : Fin K => fun S : Finset V => (N ∩ S).card ≠ 1))

theorem isolationTrials_failure_le (blue N : Finset V) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : N ⊆ blue) (hne : N.Nonempty)
    (hlo : 1 / (2 * (N.card : ℝ)) ≤ p) (hhi : p ≤ 1 / (N.card : ℝ)) (K : ℕ) :
    mass (isolationTrials blue p hp0 hp1 K)
        (fun tape => ∀ k, (N ∩ tape k).card ≠ 1) ≤ (7 / 8 : ℝ≥0∞) ^ K := by
  rw [isolationTrials_failure_mass]
  exact pow_le_pow_left₀ (by positivity) (isolation_failure_le blue N p hp0 hp1 hN hne hlo hhi) K

def dyadicProbability (j : ℕ) : ℝ := (2 ^ j : ℝ)⁻¹

theorem dyadicProbability_pos (j : ℕ) : 0 < dyadicProbability j := by
  unfold dyadicProbability
  positivity

theorem dyadicProbability_le_one (j : ℕ) : dyadicProbability j ≤ 1 := by
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ j)
  simpa [dyadicProbability] using h

theorem pow_clog_le_twice (d : ℕ) (hd : 0 < d) : 2 ^ Nat.clog 2 d ≤ 2 * d := by
  by_cases h1 : d = 1
  · simp [h1]
  have hj : 0 < Nat.clog 2 d := Nat.clog_pos (by decide) (by omega)
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < d)
  calc
    2 ^ Nat.clog 2 d = 2 ^ ((Nat.clog 2 d).pred + 1) := by
      have he : (Nat.clog 2 d).pred + 1 = Nat.clog 2 d := by
        simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hj)
      rw [he]
    _ = 2 ^ (Nat.clog 2 d).pred * 2 := pow_succ _ _
    _ ≤ d * 2 := Nat.mul_le_mul_right 2 hpred.le
    _ = 2 * d := Nat.mul_comm _ _

/-- A nonempty row has an eligible public scale. The upper endpoint d=1
uses j=0 and sampling probability one. -/
theorem dyadic_scale {d n : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    Nat.clog 2 d < 1 + Nat.clog 2 (n + 2) ∧
      1 / (2 * (d : ℝ)) ≤ dyadicProbability (Nat.clog 2 d) ∧
      dyadicProbability (Nat.clog 2 d) ≤ 1 / (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : (d : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 d := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) d
  have hhi : (2 : ℝ) ^ Nat.clog 2 d ≤ 2 * (d : ℝ) := by
    exact_mod_cast pow_clog_le_twice d hd
  refine ⟨?_, ?_, ?_⟩
  · have h := Nat.clog_mono_right 2 (hdn.trans (by omega : n ≤ n + 2))
    omega
  · simpa [dyadicProbability] using
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ Nat.clog 2 d) hhi
  · simpa [dyadicProbability] using one_div_le_one_div_of_le hdR hlo

#print axioms sampleBlue_supported_subset
#print axioms sampleBlue_restriction
#print axioms isolation_mass_ennreal
#print axioms isolation_mass
#print axioms isolation_polynomial_lower
#print axioms isolation_lower
#print axioms isolation_failure_le
#print axioms isolationTrials_failure_mass
#print axioms isolationTrials_failure_le
#print axioms dyadicProbability_pos
#print axioms dyadicProbability_le_one
#print axioms pow_clog_le_twice
#print axioms dyadic_scale

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
