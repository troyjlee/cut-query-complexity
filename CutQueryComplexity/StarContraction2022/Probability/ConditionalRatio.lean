import CutQueryComplexity.StarContraction2022.Probability.Product
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Actual uniform-subset laws and crossing-ratio moments

Fixed-size rows are sampled from the explicit finite family of subsets. The
incidence counts below are double-counting identities, not assumed moment laws.
The empty sample has crossing ratio zero; full sampling is deterministic.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Probability

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V X : Type*} [Fintype V]

/-- Actual uniform choice of a j-element subset, including j=0 and full rows. -/
def fixedSize (N : Finset V) (j : ℕ) (hj : j ≤ N.card) : PMF (Finset V) :=
  PMF.uniformOfFinset (N.powersetCard j) (powersetCard_nonempty.mpr hj)

@[simp] theorem fixedSize_support (N : Finset V) (j : ℕ) (hj : j ≤ N.card)
    (S : Finset V) :
    S ∈ (fixedSize N j hj).support ↔ S ⊆ N ∧ S.card = j := by
  simp only [fixedSize, PMF.mem_support_uniformOfFinset_iff, mem_powersetCard]

@[simp] theorem fixedSize_zero (N : Finset V) : fixedSize N 0 (Nat.zero_le _) =
    PMF.pure ∅ := by
  ext S : 1
  simp [fixedSize, PMF.uniformOfFinset_apply, PMF.pure_apply, eq_comm]

@[simp] theorem fixedSize_full (N : Finset V) : fixedSize N N.card le_rfl =
    PMF.pure N := by
  ext S : 1
  simp [fixedSize, PMF.uniformOfFinset_apply, PMF.pure_apply, eq_comm]

/-- Exact inclusion probability for any fixed collection of distinct labels. -/
theorem fixedSize_contains (N U : Finset V) (j : ℕ) (hj : j ≤ N.card)
    (hU : U ⊆ N) (hUj : U.card ≤ j) :
    mass (fixedSize N j hj) (fun S => U ⊆ S) =
      ((N.card - U.card).choose (j - U.card) : ℝ≥0∞) / N.card.choose j := by
  rw [fixedSize, mass_uniform, card_powersetCard]
  apply congrArg (fun k : ℕ => (k : ℝ≥0∞) / (N.card.choose j : ℝ≥0∞))
  convert card_filter_powersetCard_subset U N j hU hUj using 1 <;>
    congr 1 <;> ext S <;> simp

/-- A finite real average, identified below with the actual PMF expectation
for every nonnegative integrand. Negative values are allowed in algebraic steps. -/
def uniformMean (s : Finset X) (f : X → ℝ) : ℝ := (∑ x ∈ s, f x) / s.card

theorem uniformMean_congr (s : Finset X) {f g : X → ℝ}
    (h : ∀ x ∈ s, f x = g x) : uniformMean s f = uniformMean s g := by
  unfold uniformMean
  rw [Finset.sum_congr rfl h]

theorem uniformMean_const (s : Finset X) (hs : s.Nonempty) (c : ℝ) :
    uniformMean s (fun _ => c) = c := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast (card_ne_zero.mpr hs)
  simp only [uniformMean, sum_const, nsmul_eq_mul]
  field_simp

theorem uniformMean_add (s : Finset X) (f g : X → ℝ) :
    uniformMean s (fun x => f x + g x) = uniformMean s f + uniformMean s g := by
  simp only [uniformMean, sum_add_distrib, add_div]

theorem uniformMean_sub (s : Finset X) (f g : X → ℝ) :
    uniformMean s (fun x => f x - g x) = uniformMean s f - uniformMean s g := by
  simp only [uniformMean, sum_sub_distrib, sub_div]

theorem uniformMean_mul_const (s : Finset X) (f : X → ℝ) (c : ℝ) :
    uniformMean s (fun x => f x * c) = uniformMean s f * c := by
  simp only [uniformMean, ← sum_mul]
  ring

theorem uniformMean_div_const (s : Finset X) (f : X → ℝ) (c : ℝ) :
    uniformMean s (fun x => f x / c) = uniformMean s f / c := by
  simp only [div_eq_mul_inv, uniformMean_mul_const]

theorem expect_uniform_eq (s : Finset X) (hs : s.Nonempty) (f : X → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    expect (PMF.uniformOfFinset s hs) (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal (uniformMean s f) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast (card_pos.mpr hs)
  rw [CutQueryComplexity.Probability.expect, tsum_eq_sum (s := s) (fun x hx => by
    rw [PMF.uniformOfFinset_apply_of_notMem hs hx, zero_mul])]
  rw [uniformMean, ENNReal.ofReal_div_of_pos hc,
    ENNReal.ofReal_sum_of_nonneg hf, ENNReal.ofReal_natCast,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [PMF.uniformOfFinset_apply_of_mem hs hx, mul_comm]

/-- Count r-label incidences in all j-subsets by swapping the two finite sums. -/
theorem sum_inter_choose (N C : Finset V) (j r : ℕ)
    (hC : C ⊆ N) (hrj : r ≤ j) :
    (∑ S ∈ N.powersetCard j, (C ∩ S).card.choose r) =
      C.card.choose r * (N.card - r).choose (j - r) := by
  have hf (S : Finset V) :
      (C.powersetCard r).filter (fun U => U ⊆ S) = (C ∩ S).powersetCard r := by
    ext U
    simp only [mem_filter, mem_powersetCard, subset_inter_iff]
    tauto
  calc
    (∑ S ∈ N.powersetCard j, (C ∩ S).card.choose r) =
        ∑ S ∈ N.powersetCard j, ∑ U ∈ C.powersetCard r, if U ⊆ S then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← card_powersetCard, ← hf, card_eq_sum_ones, sum_filter]
    _ = ∑ U ∈ C.powersetCard r, ∑ S ∈ N.powersetCard j, if U ⊆ S then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ _U ∈ C.powersetCard r, (N.card - r).choose (j - r) := by
      apply Finset.sum_congr rfl
      intro U hU
      obtain ⟨hUC, hcard⟩ := mem_powersetCard.mp hU
      rw [← sum_filter, ← card_eq_sum_ones,
        card_filter_powersetCard_subset U N j (hUC.trans hC) (by omega), hcard]
    _ = _ := by simp [card_powersetCard]

theorem sum_inter_card (N C : Finset V) (j : ℕ) (hC : C ⊆ N) (hj : 0 < j) :
    (∑ S ∈ N.powersetCard j, (C ∩ S).card) =
      C.card * (N.card - 1).choose (j - 1) := by
  simpa only [Nat.choose_one_right] using sum_inter_choose N C j 1 hC hj

theorem choose_ratio_one {D j : ℕ} (hj : 0 < j) (hjD : j ≤ D) :
    ((D - 1).choose (j - 1) : ℝ) / D.choose j = (j : ℝ) / D := by
  have hD : 0 < D := hj.trans_le hjD
  have hDn : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hq : (D.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_ne_zero hjD)
  have hh := Nat.add_one_mul_choose_eq (D - 1) (j - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ D), Nat.sub_add_cancel (by omega : 1 ≤ j)] at hh
  have hhR : (D : ℝ) * (D - 1).choose (j - 1) = (D.choose j : ℝ) * j := by
    exact_mod_cast hh
  field_simp
  nlinarith [hhR]

/-- The true first hypergeometric moment. -/
theorem uniformMean_crossingCount (N C : Finset V) (j : ℕ)
    (hC : C ⊆ N) (hj : 0 < j) (hjN : j ≤ N.card) :
    uniformMean (N.powersetCard j) (fun S => ((C ∩ S).card : ℝ)) =
      (C.card : ℝ) * j / N.card := by
  have hsum : (∑ S ∈ N.powersetCard j, ((C ∩ S).card : ℝ)) =
      (C.card : ℝ) * (N.card - 1).choose (j - 1) := by
    exact_mod_cast sum_inter_card N C j hC hj
  rw [uniformMean, hsum, card_powersetCard, mul_div_assoc, choose_ratio_one hj hjN]
  ring

/-- The ordinary zero-denominator convention gives ratio zero on an empty row. -/
def crossingRatio (C S : Finset V) : ℝ := ((C ∩ S).card : ℝ) / S.card

@[simp] theorem crossingRatio_empty (C : Finset V) : crossingRatio C ∅ = 0 := by
  simp [crossingRatio]

theorem crossingRatio_nonneg (C S : Finset V) : 0 ≤ crossingRatio C S := by
  unfold crossingRatio
  positivity

theorem crossingRatio_le_one (C S : Finset V) : crossingRatio C S ≤ 1 := by
  by_cases hS : S = ∅
  · simp [hS]
  · have hs : (0 : ℝ) < S.card := by
      exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hS)
    unfold crossingRatio
    apply (div_le_iff₀ hs).mpr
    simpa only [one_mul] using
      (show ((C ∩ S).card : ℝ) ≤ S.card by exact_mod_cast card_le_card inter_subset_right)

theorem uniformMean_crossingRatio (N C : Finset V) (j : ℕ)
    (hC : C ⊆ N) (hj : 0 < j) (hjN : j ≤ N.card) :
    uniformMean (N.powersetCard j) (crossingRatio C) = (C.card : ℝ) / N.card := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  calc
    uniformMean (N.powersetCard j) (crossingRatio C) =
        uniformMean (N.powersetCard j) (fun S => ((C ∩ S).card : ℝ) / j) := by
      apply uniformMean_congr
      intro S hS
      rw [crossingRatio, (mem_powersetCard.mp hS).2]
    _ = uniformMean (N.powersetCard j) (fun S => ((C ∩ S).card : ℝ)) / j :=
      uniformMean_div_const _ _ _
    _ = ((C.card : ℝ) * j / N.card) / j := by
      rw [uniformMean_crossingCount N C j hC hj hjN]
    _ = (C.card : ℝ) / N.card := by field_simp

/-- The first ratio moment concerns the actual uniform-subset PMF. -/
theorem fixedSize_ratio_mean (N C : Finset V) (j : ℕ)
    (hC : C ⊆ N) (hj : 0 < j) (hjN : j ≤ N.card) :
    expect (fixedSize N j hjN) (fun S => ENNReal.ofReal (crossingRatio C S)) =
      ENNReal.ofReal ((C.card : ℝ) / N.card) := by
  rw [fixedSize, expect_uniform_eq _ _ _ (fun S _ => crossingRatio_nonneg C S),
    uniformMean_crossingRatio N C j hC hj hjN]

theorem fixedSize_full_ratio (N C : Finset V) :
    expect (fixedSize N N.card le_rfl) (fun S => ENNReal.ofReal (crossingRatio C S)) =
      ENNReal.ofReal (crossingRatio C N) := by
  rw [fixedSize_full, expect_pure]

theorem uniformMean_choose (N C : Finset V) (j r : ℕ)
    (hC : C ⊆ N) (hrj : r ≤ j) :
    uniformMean (N.powersetCard j) (fun S => ((C ∩ S).card.choose r : ℝ)) =
      (C.card.choose r : ℝ) * (N.card - r).choose (j - r) / N.card.choose j := by
  have hsum : (∑ S ∈ N.powersetCard j, ((C ∩ S).card.choose r : ℝ)) =
      (C.card.choose r : ℝ) * (N.card - r).choose (j - r) := by
    exact_mod_cast sum_inter_choose N C j r hC hrj
  rw [uniformMean, hsum, card_powersetCard]

theorem choose_ratio_two {D j : ℕ} (hj : 2 ≤ j) (hjD : j ≤ D) :
    ((D - 2).choose (j - 2) : ℝ) / D.choose j =
      (j : ℝ) * (j - 1) / ((D : ℝ) * (D - 1)) := by
  have hD : 2 ≤ D := hj.trans hjD
  have hDn : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hDm : (D : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  have hq : (D.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_ne_zero hjD)
  have hh : (D.choose j : ℝ) * (j.choose 2 : ℝ) =
      (D.choose 2 : ℝ) * (D - 2).choose (j - 2) := by
    exact_mod_cast (Nat.choose_mul (n := D) (k := j) (s := 2) hj)
  rw [Nat.cast_choose_two ℝ j, Nat.cast_choose_two ℝ D] at hh
  field_simp
  nlinarith [hh]

/-- The second hypergeometric moment follows from the two-label incidences. -/
theorem uniformMean_crossingCount_sq (N C : Finset V) (j : ℕ)
    (hC : C ⊆ N) (hj : 0 < j) (hjN : j ≤ N.card) :
    uniformMean (N.powersetCard j) (fun S => ((C ∩ S).card : ℝ) ^ 2) =
      (C.card : ℝ) * j / N.card +
        (C.card : ℝ) * (C.card - 1) * j * (j - 1) /
          ((N.card : ℝ) * (N.card - 1)) := by
  have hidentity (a : ℕ) : (a : ℝ) ^ 2 = a + (a.choose 2 : ℝ) * 2 := by
    rw [Nat.cast_choose_two ℝ a]
    ring
  calc
    uniformMean (N.powersetCard j) (fun S => ((C ∩ S).card : ℝ) ^ 2) =
        uniformMean (N.powersetCard j)
          (fun S => ((C ∩ S).card : ℝ) + ((C ∩ S).card.choose 2 : ℝ) * 2) :=
      uniformMean_congr _ (fun S _ => hidentity _)
    _ = uniformMean (N.powersetCard j) (fun S => ((C ∩ S).card : ℝ)) +
        uniformMean (N.powersetCard j) (fun S => ((C ∩ S).card.choose 2 : ℝ)) * 2 := by
      rw [uniformMean_add, uniformMean_mul_const]
    _ = _ := by
      rw [uniformMean_crossingCount N C j hC hj hjN]
      by_cases hj2 : 2 ≤ j
      · rw [uniformMean_choose N C j 2 hC hj2,
          mul_div_assoc (C.card.choose 2 : ℝ) ((N.card - 2).choose (j - 2) : ℝ)
            (N.card.choose j : ℝ),
          choose_ratio_two hj2 hjN, Nat.cast_choose_two ℝ C.card]
        ring
      · have hj1 : j = 1 := by omega
        have hz : uniformMean (N.powersetCard j)
            (fun S => ((C ∩ S).card.choose 2 : ℝ)) = 0 := by
          have hh : ∀ S ∈ N.powersetCard j, (C ∩ S).card.choose 2 = 0 := by
            intro S hS
            apply Nat.choose_eq_zero_of_lt
            have hi := card_le_card (inter_subset_right : C ∩ S ⊆ S)
            have hc := (mem_powersetCard.mp hS).2
            omega
          simp only [uniformMean]
          rw [Finset.sum_eq_zero (fun S hS => by rw [hh S hS]; simp)]
          simp
        rw [hz, hj1]
        norm_num

theorem uniformMean_square_sub (s : Finset X) (hs : s.Nonempty) (f : X → ℝ) (c : ℝ) :
    uniformMean s (fun x => (f x - c) ^ 2) =
      uniformMean s (fun x => f x ^ 2) - uniformMean s f * (2 * c) + c ^ 2 := by
  calc
    uniformMean s (fun x => (f x - c) ^ 2) =
        uniformMean s (fun x => (f x ^ 2 - f x * (2 * c)) + c ^ 2) :=
      uniformMean_congr s (fun x _ => by ring)
    _ = _ := by
      rw [uniformMean_add, uniformMean_sub, uniformMean_mul_const, uniformMean_const s hs]

/-- Exact hypergeometric ratio variance, including the singleton/full cases. -/
theorem uniformMean_ratio_variance (N C : Finset V) (j : ℕ)
    (hC : C ⊆ N) (hj : 0 < j) (hjN : j ≤ N.card) :
    uniformMean (N.powersetCard j)
        (fun S => (crossingRatio C S - (C.card : ℝ) / N.card) ^ 2) =
      ((C.card : ℝ) / N.card) * (1 - (C.card : ℝ) / N.card) *
        ((N.card : ℝ) - j) / ((j : ℝ) * ((N.card : ℝ) - 1)) := by
  have hD : 0 < N.card := hj.trans_le hjN
  have hDn : (N.card : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hjn : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  by_cases hD2 : 2 ≤ N.card
  · have hDm : (N.card : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ N.card := by exact_mod_cast hD2
      linarith
    rw [uniformMean_square_sub _ (powersetCard_nonempty.mpr hjN),
      uniformMean_crossingRatio N C j hC hj hjN]
    have hsq : uniformMean (N.powersetCard j) (fun S => crossingRatio C S ^ 2) =
        uniformMean (N.powersetCard j) (fun S => ((C ∩ S).card : ℝ) ^ 2) / (j : ℝ) ^ 2 := by
      calc
        _ = uniformMean (N.powersetCard j)
            (fun S => ((C ∩ S).card : ℝ) ^ 2 / (j : ℝ) ^ 2) := by
          apply uniformMean_congr
          intro S hS
          rw [crossingRatio, (mem_powersetCard.mp hS).2, div_pow]
        _ = _ := uniformMean_div_const _ _ _
    rw [hsq, uniformMean_crossingCount_sq N C j hC hj hjN]
    field_simp
    ring
  · have hDc : N.card = 1 := by omega
    have hjc : j = N.card := by omega
    rw [hjc, powersetCard_self]
    simp [uniformMean, crossingRatio, inter_eq_left.mpr hC]

theorem uniformMean_ratio_variance_le (N C : Finset V) (j : ℕ)
    (hC : C ⊆ N) (hj : 0 < j) (hjN : j ≤ N.card) :
    uniformMean (N.powersetCard j)
        (fun S => (crossingRatio C S - (C.card : ℝ) / N.card) ^ 2) ≤
      ((C.card : ℝ) / N.card) / j := by
  rw [uniformMean_ratio_variance N C j hC hj hjN]
  have hD : (0 : ℝ) < N.card := by exact_mod_cast (hj.trans_le hjN)
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjD : (j : ℝ) ≤ N.card := by exact_mod_cast hjN
  have hcD : (C.card : ℝ) ≤ N.card := by exact_mod_cast card_le_card hC
  have hr0 : 0 ≤ (C.card : ℝ) / N.card := by positivity
  have hr1 : (C.card : ℝ) / N.card ≤ 1 := (div_le_iff₀ hD).mpr (by simpa using hcD)
  by_cases hD1 : (N.card : ℝ) = 1
  · simp only [hD1, sub_self, mul_zero, div_zero]
    positivity
  · have hDm : 0 < (N.card : ℝ) - 1 := by
      have : (1 : ℝ) ≤ N.card := hjR.trans hjD
      exact sub_pos.mpr (lt_of_le_of_ne this (Ne.symm hD1))
    have hfac : ((N.card : ℝ) - j) / ((N.card : ℝ) - 1) ≤ 1 :=
      (div_le_iff₀ hDm).mpr (by linarith)
    calc
      _ = (((C.card : ℝ) / N.card) / j) * (1 - (C.card : ℝ) / N.card) *
          (((N.card : ℝ) - j) / ((N.card : ℝ) - 1)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
      _ ≤ (((C.card : ℝ) / N.card) / j) * (1 - (C.card : ℝ) / N.card) * 1 := by
        apply mul_le_mul_of_nonneg_left hfac
        exact mul_nonneg (div_nonneg hr0 (by linarith)) (sub_nonneg.mpr hr1)
      _ ≤ ((C.card : ℝ) / N.card) / j := by
        rw [mul_one]
        exact mul_le_of_le_one_right (div_nonneg hr0 (by linarith)) (by linarith)

/-- One-sided Chebyshev for the actual sampler, with the row's true density. -/
theorem fixedSize_ratio_tail (N C : Finset V) (j : ℕ)
    (hC : C ⊆ N) (hj : 0 < j) (hjN : j ≤ N.card) (eps : ℝ) (heps : 0 < eps) :
    mass (fixedSize N j hjN)
        (fun S => (C.card : ℝ) / N.card + eps < crossingRatio C S) ≤
      ENNReal.ofReal (((C.card : ℝ) / N.card) / j / eps ^ 2) := by
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hden : ENNReal.ofReal (eps ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr heps2).ne'
  rw [ENNReal.ofReal_div_of_pos heps2]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden) (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [mul_comm]
  have hm := mul_mass_le_expect (fixedSize N j hjN)
    (fun S => (C.card : ℝ) / N.card + eps < crossingRatio C S)
    (fun S => ENNReal.ofReal ((crossingRatio C S - (C.card : ℝ) / N.card) ^ 2))
    (ENNReal.ofReal (eps ^ 2)) (by
      intro S _ hS
      apply ENNReal.ofReal_le_ofReal
      have hx : eps < crossingRatio C S - (C.card : ℝ) / N.card := by linarith
      nlinarith)
  apply hm.trans
  rw [fixedSize, expect_uniform_eq _ _ _ (fun S _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (uniformMean_ratio_variance_le N C j hC hj hjN)

theorem fixedSize_ratio_tenth_tail (N C : Finset V) (j : ℕ)
    (hC : C ⊆ N) (hj : 0 < j) (hjN : j ≤ N.card) :
    mass (fixedSize N j hjN)
        (fun S => (C.card : ℝ) / N.card + 1 / 10 < crossingRatio C S) ≤
      ENNReal.ofReal (100 * ((C.card : ℝ) / N.card) / j) := by
  have h := fixedSize_ratio_tail N C j hC hj hjN (1 / 10) (by norm_num)
  convert h using 1
  congr 1
  ring

/-- Draw a size first and then an actual uniform subset of that size. This
is a probability law, not an assumed conditional uniformity statement. -/
def sizeMixture (N : Finset V) (q : PMF (Fin (N.card + 1))) : PMF (Finset V) :=
  q.bind fun j => fixedSize N j.val (Nat.le_of_lt_succ j.isLt)

/-- Every positive-size mixture has the same first ratio moment. In later
applications q is the actual size distribution conditioned on acceptance. -/
theorem sizeMixture_ratio_mean (N C : Finset V) (q : PMF (Fin (N.card + 1)))
    (hC : C ⊆ N) (hpos : ∀ j ∈ q.support, 0 < j.val) :
    expect (sizeMixture N q) (fun S => ENNReal.ofReal (crossingRatio C S)) =
      ENNReal.ofReal ((C.card : ℝ) / N.card) := by
  rw [sizeMixture, expect_bind]
  calc
    _ = expect q (fun _ => ENNReal.ofReal ((C.card : ℝ) / N.card)) := by
      apply expect_congr_on_support
      intro j hj
      exact fixedSize_ratio_mean N C j.val hC (hpos j hj) _
    _ = _ := expect_const _ _

/-- The exact variance bound survives arbitrary mixing over accepted sizes.
No independence of the acceptance event and the ratio is asserted. -/
theorem sizeMixture_ratio_variance_le (N C : Finset V)
    (q : PMF (Fin (N.card + 1))) (k : ℕ) (hk : 0 < k)
    (hC : C ⊆ N) (hsize : ∀ j ∈ q.support, k ≤ j.val) :
    expect (sizeMixture N q)
        (fun S => ENNReal.ofReal ((crossingRatio C S - (C.card : ℝ) / N.card) ^ 2)) ≤
      ENNReal.ofReal (((C.card : ℝ) / N.card) / k) := by
  rw [sizeMixture, expect_bind]
  apply expect_le_of_le_on_support
  intro j hj
  rw [fixedSize, expect_uniform_eq _ _ _ (fun S _ => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  apply (uniformMean_ratio_variance_le N C j.val hC (hk.trans_le (hsize j hj))
    (Nat.le_of_lt_succ j.isLt)).trans
  apply div_le_div_of_nonneg_left (by positivity)
    (by exact_mod_cast hk)
  exact_mod_cast hsize j hj

theorem sizeMixture_ratio_tail (N C : Finset V) (q : PMF (Fin (N.card + 1)))
    (k : ℕ) (hk : 0 < k) (hC : C ⊆ N)
    (hsize : ∀ j ∈ q.support, k ≤ j.val) (eps : ℝ) (heps : 0 < eps) :
    mass (sizeMixture N q)
        (fun S => (C.card : ℝ) / N.card + eps < crossingRatio C S) ≤
      ENNReal.ofReal (((C.card : ℝ) / N.card) / k / eps ^ 2) := by
  rw [sizeMixture, mass_bind]
  change expect q (fun j => mass (fixedSize N j.val (Nat.le_of_lt_succ j.isLt))
    (fun S => (C.card : ℝ) / N.card + eps < crossingRatio C S)) ≤ _
  apply expect_le_of_le_on_support
  intro j hj
  apply (fixedSize_ratio_tail N C j.val hC (hk.trans_le (hsize j hj)) _ eps heps).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (sq_nonneg eps)
  apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hk)
  exact_mod_cast hsize j hj

/-- Conditioning the public size law on any positive accepted window suffices
for the same tail estimate; no uniform weighting across accepted sizes is needed. -/
theorem acceptedSize_ratio_tail (N C : Finset V) (q : PMF (Fin (N.card + 1)))
    (W : Fin (N.card + 1) → Prop) (hW : ∃ j, W j ∧ j ∈ q.support)
    (k : ℕ) (hk : 0 < k) (hC : C ⊆ N) (hsize : ∀ j, W j → k ≤ j.val)
    (eps : ℝ) (heps : 0 < eps) :
    mass (sizeMixture N (q.filter {j | W j} hW))
        (fun S => (C.card : ℝ) / N.card + eps < crossingRatio C S) ≤
      ENNReal.ofReal (((C.card : ℝ) / N.card) / k / eps ^ 2) := by
  apply sizeMixture_ratio_tail N C _ k hk hC _ eps heps
  intro j hj
  exact hsize j ((PMF.mem_support_filter_iff hW).mp hj).1

/-- Inclusion and exclusion are independent Bernoulli factors. Summing these
actual subset weights is the finite product expansion of (p+(1-p))^|N|. -/
theorem bernoulliSubset_sum (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1) :
    (∑ S ∈ N.powerset, p ^ S.card * (1 - p) ^ (N.card - S.card)) = 1 := by
  calc
    _ = ∑ S ∈ N.powerset, (∏ _v ∈ S, p) * ∏ _v ∈ N \ S, (1 - p) := by
      apply Finset.sum_congr rfl
      intro S hS
      simp only [Finset.prod_const, card_sdiff_of_subset (mem_powerset.mp hS)]
    _ = ∏ _v ∈ N, (p + (1 - p)) :=
      (Finset.prod_add (fun _ : V => p) (fun _ => 1 - p) N).symm
    _ = 1 := by simp [add_tsub_cancel_of_le hp]

/-- An actual independent Bernoulli subset law. No lower-bound oracle or
assumed conditional-subset distribution is an argument. -/
def bernoulliSubset (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1) : PMF (Finset V) :=
  PMF.ofFintype
    (fun S => if S ⊆ N then p ^ S.card * (1 - p) ^ (N.card - S.card) else 0) (by
      rw [← Finset.sum_filter]
      have hs : univ.filter (fun S : Finset V => S ⊆ N) = N.powerset := by
        ext S
        simp only [mem_filter, mem_univ, true_and, mem_powerset]
      rw [hs]
      exact bernoulliSubset_sum N p hp)

@[simp] theorem bernoulliSubset_apply (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1)
    (S : Finset V) :
    bernoulliSubset N p hp S =
      if S ⊆ N then p ^ S.card * (1 - p) ^ (N.card - S.card) else 0 := rfl

theorem bernoulliSubset_support (N : Finset V) (p : ℝ≥0∞)
    (hp0 : 0 < p) (hp1 : p < 1) (S : Finset V) :
    S ∈ (bernoulliSubset N p hp1.le).support ↔ S ⊆ N := by
  have hp : p ≠ 0 := hp0.ne'
  have hq : 1 - p ≠ 0 := (tsub_pos_iff_lt.mpr hp1).ne'
  simp only [PMF.mem_support_iff, bernoulliSubset_apply]
  by_cases hS : S ⊆ N <;> simp [hS, hp, hq]

/-- This is the actual binomial size mass, obtained by counting all equal
weight j-element subsets. It also covers j=0 and j=|N|. -/
theorem bernoulliSubset_size_mass (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1) (j : ℕ) :
    mass (bernoulliSubset N p hp) (fun S => S.card = j) =
      (N.card.choose j : ℝ≥0∞) * (p ^ j * (1 - p) ^ (N.card - j)) := by
  rw [mass_eq_tsum, tsum_fintype]
  have hs : univ.filter (fun S : Finset V => S ⊆ N ∧ S.card = j) =
      N.powersetCard j := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard]
  calc
    _ = ∑ _S ∈ univ.filter (fun S : Finset V => S ⊆ N ∧ S.card = j),
        p ^ j * (1 - p) ^ (N.card - j) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hSN : S ⊆ N <;> by_cases hSj : S.card = j <;>
        simp [bernoulliSubset_apply, hSN, hSj]
    _ = _ := by simp [hs, card_powersetCard, nsmul_eq_mul]

theorem bernoulliSubset_size_supported (N : Finset V) (p : ℝ≥0∞)
    (hp0 : 0 < p) (hp1 : p < 1) (j : ℕ) (hj : j ≤ N.card) :
    ∃ S, S.card = j ∧ S ∈ (bernoulliSubset N p hp1.le).support := by
  obtain ⟨S, hS⟩ := powersetCard_nonempty.mpr hj
  obtain ⟨hSN, hcard⟩ := mem_powersetCard.mp hS
  exact ⟨S, hcard, (bernoulliSubset_support N p hp0 hp1 S).mpr hSN⟩

/-- Exact PMF equality after conditioning on the size. Uniformity is derived
from the Bernoulli point masses, including the empty and full samples. -/
theorem condition_bernoulliSubset_size (N : Finset V) (p : ℝ≥0∞)
    (hp0 : 0 < p) (hp1 : p < 1) (j : ℕ) (hj : j ≤ N.card) :
    (bernoulliSubset N p hp1.le).filter {S | S.card = j}
        (bernoulliSubset_size_supported N p hp0 hp1 j hj) = fixedSize N j hj := by
  have hw0 : p ^ j * (1 - p) ^ (N.card - j) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp0.ne')
      (pow_ne_zero _ (tsub_pos_iff_lt.mpr hp1).ne')
  have hwt : p ^ j * (1 - p) ^ (N.card - j) ≠ ∞ := by
    obtain ⟨S, hS⟩ := powersetCard_nonempty.mpr hj
    obtain ⟨hSN, hcard⟩ := mem_powersetCard.mp hS
    simpa only [bernoulliSubset_apply, hSN, ite_true, hcard] using
      (bernoulliSubset N p hp1.le).apply_ne_top S
  ext S : 1
  rw [filter_apply_mass, bernoulliSubset_size_mass]
  by_cases hSj : S.card = j
  · by_cases hSN : S ⊆ N
    · rw [if_pos hSj, bernoulliSubset_apply, if_pos hSN, hSj]
      have hmem : S ∈ N.powersetCard j := mem_powersetCard.mpr ⟨hSN, hSj⟩
      rw [fixedSize, PMF.uniformOfFinset_apply_of_mem _ hmem, card_powersetCard]
      simpa only [one_mul, one_div] using
        (ENNReal.mul_div_mul_right 1 (N.card.choose j : ℝ≥0∞) hw0 hwt)
    · have hmem : S ∉ N.powersetCard j := fun h => hSN (mem_powersetCard.mp h).1
      simp [hSj, bernoulliSubset_apply, hSN, fixedSize,
        PMF.uniformOfFinset_apply_of_notMem _ hmem]
  · have hmem : S ∉ N.powersetCard j := fun h => hSj (mem_powersetCard.mp h).2
    simp [hSj, fixedSize, PMF.uniformOfFinset_apply_of_notMem _ hmem]

/-- The binomial size distribution is constructed from its normalized finite
mass function, including p=0 and p=1. -/
def binomialSize (D : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1) : PMF (Fin (D + 1)) :=
  PMF.ofFintype
    (fun j : Fin (D + 1) => (D.choose j.val : ℝ≥0∞) * (p ^ j.val * (1 - p) ^ (D - j.val))) (by
      calc
        _ = ∑ j ∈ range (D + 1), p ^ j * (1 - p) ^ (D - j) * (D.choose j : ℝ≥0∞) := by
          rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
            (D.choose j : ℝ≥0∞) * (p ^ j * (1 - p) ^ (D - j)))]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (p + (1 - p)) ^ D := (add_pow p (1 - p) D).symm
        _ = 1 := by simp [add_tsub_cancel_of_le hp])

@[simp] theorem binomialSize_apply (D : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1)
    (j : Fin (D + 1)) :
    binomialSize D p hp j =
      (D.choose j.val : ℝ≥0∞) * (p ^ j.val * (1 - p) ^ (D - j.val)) := rfl

/-- Actual disintegration of independent inclusion by its size. This joins
the Bernoulli sampler to the uniform-subset moment theorems. -/
theorem bernoulliSubset_eq_sizeMixture (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1) :
    bernoulliSubset N p hp = sizeMixture N (binomialSize N.card p hp) := by
  ext S : 1
  rw [sizeMixture, PMF.bind_apply, tsum_fintype]
  by_cases hSN : S ⊆ N
  · let j : Fin (N.card + 1) := ⟨S.card, Nat.lt_succ_of_le (card_le_card hSN)⟩
    rw [Finset.sum_eq_single j]
    · have hmem : S ∈ N.powersetCard j.val := mem_powersetCard.mpr ⟨hSN, rfl⟩
      have hc : (N.card.choose j.val : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast Nat.choose_ne_zero (Nat.le_of_lt_succ j.isLt)
      rw [bernoulliSubset_apply, if_pos hSN, binomialSize_apply, fixedSize,
        PMF.uniformOfFinset_apply_of_mem _ hmem, card_powersetCard]
      change p ^ S.card * (1 - p) ^ (N.card - S.card) =
        (N.card.choose j.val : ℝ≥0∞) *
          (p ^ S.card * (1 - p) ^ (N.card - S.card)) * (N.card.choose j.val : ℝ≥0∞)⁻¹
      rw [mul_right_comm, ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), one_mul]
    · intro i _ hij
      have hcard : S.card ≠ i.val := by
        intro he
        apply hij
        exact Fin.ext he.symm
      have hmem : S ∉ N.powersetCard i.val := fun h => hcard (mem_powersetCard.mp h).2
      rw [fixedSize, PMF.uniformOfFinset_apply_of_notMem _ hmem, mul_zero]
    · exact fun hj => (hj (mem_univ _)).elim
  · rw [bernoulliSubset_apply, if_neg hSN]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hmem : S ∉ N.powersetCard j.val := fun h => hSN (mem_powersetCard.mp h).1
    rw [fixedSize, PMF.uniformOfFinset_apply_of_notMem _ hmem, mul_zero]

/-- Zero-size samples contribute zero, so unconditional Bernoulli sampling
can only decrease the expected crossing fraction. -/
theorem bernoulliSubset_ratio_mean_le (N C : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1)
    (hC : C ⊆ N) :
    expect (bernoulliSubset N p hp) (fun S => ENNReal.ofReal (crossingRatio C S)) ≤
      ENNReal.ofReal ((C.card : ℝ) / N.card) := by
  rw [bernoulliSubset_eq_sizeMixture, sizeMixture, expect_bind]
  apply expect_le_of_le_on_support
  intro j _
  by_cases hj : 0 < j.val
  · exact (fixedSize_ratio_mean N C j.val hC hj _).le
  · have hj0 : j.val = 0 := by omega
    simp [hj0]

theorem sizeMixture_card_mass (N : Finset V) (q : PMF (Fin (N.card + 1)))
    (W : ℕ → Prop) :
    mass (sizeMixture N q) (fun S => W S.card) = mass q (fun j => W j.val) := by
  have hm (j : Fin (N.card + 1)) :
      mass (fixedSize N j.val (Nat.le_of_lt_succ j.isLt)) (fun S => W S.card) = if W j.val then 1 else 0 := by
    calc
      _ = expect (fixedSize N j.val (Nat.le_of_lt_succ j.isLt)) (fun S => if W S.card then 1 else 0) := by
        rw [expect_indicator, one_mul]
      _ = expect (fixedSize N j.val (Nat.le_of_lt_succ j.isLt)) (fun _ => if W j.val then 1 else 0) := by
        apply expect_congr_on_support
        intro S hS
        have hcard := ((fixedSize_support N j.val _ S).mp hS).2
        rw [hcard]
      _ = _ := expect_const _ _
  rw [sizeMixture, mass_bind, mass_eq_tsum]
  apply tsum_congr
  intro j
  rw [hm j]
  by_cases hj : W j.val <;> simp [hj]

theorem sizeMixture_window_supported (N : Finset V) (q : PMF (Fin (N.card + 1)))
    (W : ℕ → Prop) (hW : ∃ j : Fin (N.card + 1), W j.val ∧ j ∈ q.support) :
    ∃ S, W S.card ∧ S ∈ (sizeMixture N q).support := by
  obtain ⟨j, hjW, hjq⟩ := hW
  obtain ⟨S, hS⟩ := powersetCard_nonempty.mpr (Nat.le_of_lt_succ j.isLt)
  obtain ⟨hSN, hcard⟩ := mem_powersetCard.mp hS
  refine ⟨S, by simpa only [hcard] using hjW, ?_⟩
  rw [sizeMixture, PMF.mem_support_bind_iff]
  exact ⟨j, hjq, (fixedSize_support N j.val _ S).mpr ⟨hSN, hcard⟩⟩

/-- Conditioning the subset law on a count window is exactly conditioning
its size law first, followed by uniform sampling at that size. -/
theorem condition_sizeMixture_window (N : Finset V) (q : PMF (Fin (N.card + 1)))
    (W : ℕ → Prop) (hW : ∃ j : Fin (N.card + 1), W j.val ∧ j ∈ q.support) :
    (sizeMixture N q).filter {S | W S.card} (sizeMixture_window_supported N q W hW) =
      sizeMixture N (q.filter {j : Fin (N.card + 1) | W j.val} hW) := by
  ext S : 1
  rw [filter_apply_mass, sizeMixture_card_mass]
  simp only [sizeMixture, PMF.bind_apply, filter_apply_mass]
  calc
    _ = ∑' j : Fin (N.card + 1),
        (if W S.card then q j * fixedSize N j.val (Nat.le_of_lt_succ j.isLt) S else 0) /
          mass q (fun i => W i.val) := by
      by_cases hS : W S.card <;>
        simp only [hS, ite_true, ite_false, div_eq_mul_inv, ENNReal.tsum_mul_right,
          zero_mul, tsum_zero]
    _ = _ := by
      apply tsum_congr
      intro j
      by_cases hS : S ∈ (fixedSize N j.val (Nat.le_of_lt_succ j.isLt)).support
      · have hcard := ((fixedSize_support N j.val _ S).mp hS).2
        rw [hcard]
        by_cases hj : W j.val
        · simp only [hj, ite_true]
          exact ENNReal.mul_div_right_comm
        · simp [hj]
      · have hz : fixedSize N j.val (Nat.le_of_lt_succ j.isLt) S = 0 := by
          simpa only [PMF.mem_support_iff, not_not] using hS
        simp [hz]

/-- The public finite law for an accepted Bernoulli sample. Its definition
uses the actual filtered binomial law and the actual uniform subset law. -/
def acceptedBernoulli (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1) (W : ℕ → Prop)
    (hW : ∃ j : Fin (N.card + 1), W j.val ∧ j ∈ (binomialSize N.card p hp).support) : PMF (Finset V) :=
  sizeMixture N ((binomialSize N.card p hp).filter {j : Fin (N.card + 1) | W j.val} hW)

theorem bernoulliSubset_window_supported (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1)
    (W : ℕ → Prop) (hW : ∃ j : Fin (N.card + 1), W j.val ∧ j ∈ (binomialSize N.card p hp).support) :
    ∃ S, W S.card ∧ S ∈ (bernoulliSubset N p hp).support := by
  rw [bernoulliSubset_eq_sizeMixture]
  exact sizeMixture_window_supported N _ W hW

theorem condition_bernoulliSubset_window (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1)
    (W : ℕ → Prop) (hW : ∃ j : Fin (N.card + 1), W j.val ∧ j ∈ (binomialSize N.card p hp).support) :
    (bernoulliSubset N p hp).filter {S | W S.card}
        (bernoulliSubset_window_supported N p hp W hW) = acceptedBernoulli N p hp W hW := by
  ext S : 1
  rw [filter_apply_mass, bernoulliSubset_eq_sizeMixture]
  simpa only [filter_apply_mass, acceptedBernoulli] using
    congrArg (fun q : PMF (Finset V) => q S)
      (condition_sizeMixture_window N (binomialSize N.card p hp) W hW)

theorem acceptedBernoulli_ratio_tail (N C : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1)
    (W : ℕ → Prop) (hW : ∃ j : Fin (N.card + 1), W j.val ∧ j ∈ (binomialSize N.card p hp).support)
    (k : ℕ) (hk : 0 < k) (hC : C ⊆ N) (hsize : ∀ j, W j → k ≤ j)
    (eps : ℝ) (heps : 0 < eps) :
    mass (acceptedBernoulli N p hp W hW)
        (fun S => (C.card : ℝ) / N.card + eps < crossingRatio C S) ≤
      ENNReal.ofReal (((C.card : ℝ) / N.card) / k / eps ^ 2) := by
  exact acceptedSize_ratio_tail N C _ (fun j => W j.val) hW k hk hC
    (fun j => hsize j.val) eps heps

theorem binomialSize_inverse_shift (D : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1)
    (j : Fin (D + 1)) :
    ((D + 1 : ℕ) : ℝ≥0∞) * p *
        (binomialSize D p hp j / ((j.val + 1 : ℕ) : ℝ≥0∞)) =
      binomialSize (D + 1) p hp j.succ := by
  have hj0 : ((j.val + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hcoeff : ((D + 1 : ℕ) : ℝ≥0∞) * (D.choose j.val : ℝ≥0∞) /
      ((j.val + 1 : ℕ) : ℝ≥0∞) = ((D + 1).choose (j.val + 1) : ℝ≥0∞) := by
    have hh : ((D + 1 : ℕ) : ℝ≥0∞) * (D.choose j.val : ℝ≥0∞) =
        ((D + 1).choose (j.val + 1) : ℝ≥0∞) * ((j.val + 1 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Nat.add_one_mul_choose_eq D j.val
    rw [hh]
    exact ENNReal.mul_div_cancel_right hj0 (ENNReal.natCast_ne_top _)
  simp only [binomialSize_apply, Fin.val_succ, Nat.add_sub_add_right, pow_succ]
  calc
    _ = (((D + 1 : ℕ) : ℝ≥0∞) * (D.choose j.val : ℝ≥0∞) /
        ((j.val + 1 : ℕ) : ℝ≥0∞)) * (p ^ j.val * p * (1 - p) ^ (D - j.val)) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [hcoeff]

/-- The shifted inverse-size identity is bounded by the total mass of a
genuine (D+1)-trial binomial distribution. -/
theorem binomialSize_inverse_succ_le (D : ℕ) (p : ℝ≥0∞)
    (hp0 : 0 < p) (hp : p ≤ 1) :
    expect (binomialSize D p hp) (fun j => (((j.val + 1 : ℕ) : ℝ≥0∞))⁻¹) ≤
      1 / (((D + 1 : ℕ) : ℝ≥0∞) * p) := by
  have hden0 : ((D + 1 : ℕ) : ℝ≥0∞) * p ≠ 0 := mul_ne_zero (by simp) hp0.ne'
  have hdent : ((D + 1 : ℕ) : ℝ≥0∞) * p ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ne_top_of_le_ne_top ENNReal.one_ne_top hp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)).mpr
  rw [mul_comm, CutQueryComplexity.Probability.expect, ← ENNReal.tsum_mul_left, tsum_fintype]
  calc
    _ = ∑ j : Fin (D + 1), binomialSize (D + 1) p hp j.succ := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [div_eq_mul_inv] using binomialSize_inverse_shift D p hp j
    _ ≤ binomialSize (D + 1) p hp 0 +
        ∑ j : Fin (D + 1), binomialSize (D + 1) p hp j.succ :=
      le_add_of_nonneg_left (by positivity)
    _ = 1 := by
      rw [← Fin.sum_univ_succ]
      simpa only [tsum_fintype] using (binomialSize (D + 1) p hp).tsum_coe

def positiveInverse (j : ℕ) : ℝ≥0∞ := if j = 0 then 0 else (j : ℝ≥0∞)⁻¹

theorem positiveInverse_le (j : ℕ) : positiveInverse j ≤ 2 / ((j + 1 : ℕ) : ℝ≥0∞) := by
  by_cases hj : j = 0
  · simp [positiveInverse, hj]
  · have hj0 : (j : ℝ≥0∞) ≠ 0 := by exact_mod_cast hj
    have hj1 : (1 : ℝ≥0∞) ≤ j := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj)
    have hinv : (j : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hj1
    rw [positiveInverse, if_neg hj]
    apply (ENNReal.le_div_iff_mul_le (b := ((j + 1 : ℕ) : ℝ≥0∞)) (c := 2) (Or.inl (by simp))
      (Or.inl (ENNReal.natCast_ne_top _))).mpr
    rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one,
      ENNReal.inv_mul_cancel hj0 (ENNReal.natCast_ne_top _)]
    calc
      1 + (j : ℝ≥0∞)⁻¹ ≤ 1 + 1 := add_le_add le_rfl hinv
      _ = 2 := by norm_num

/-- Empty samples contribute zero; positive inverse sizes cost at most
2/((D+1)p). This proves the binomial estimate used in the sparse-center bound. -/
theorem binomialSize_positiveInverse_le (D : ℕ) (p : ℝ≥0∞)
    (hp0 : 0 < p) (hp : p ≤ 1) :
    expect (binomialSize D p hp) (fun j => positiveInverse j.val) ≤
      2 / (((D + 1 : ℕ) : ℝ≥0∞) * p) := by
  calc
    _ ≤ expect (binomialSize D p hp) (fun j => 2 / ((j.val + 1 : ℕ) : ℝ≥0∞)) :=
      expect_mono_on_support _ (fun j _ => positiveInverse_le j.val)
    _ = 2 * expect (binomialSize D p hp)
        (fun j => (((j.val + 1 : ℕ) : ℝ≥0∞))⁻¹) := by
      simp only [div_eq_mul_inv, expect_const_mul]
    _ ≤ 2 * (1 / (((D + 1 : ℕ) : ℝ≥0∞) * p)) :=
      mul_le_mul le_rfl (binomialSize_inverse_succ_le D p hp0 hp) (by positivity) (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, one_mul]

/-- The zero-allowed Bernoulli ratio estimate is for the actual sampled
subset. It is derived by size disintegration and the proved inverse moment. -/
theorem bernoulliSubset_ratio_tenth_tail (N C : Finset V) (p : ℝ≥0∞)
    (hp0 : 0 < p) (hp : p ≤ 1) (hC : C ⊆ N) :
    mass (bernoulliSubset N p hp)
        (fun S => (C.card : ℝ) / N.card + 1 / 10 < crossingRatio C S) ≤
      (200 * ENNReal.ofReal ((C.card : ℝ) / N.card)) / ((N.card : ℝ≥0∞) * p) := by
  let rho : ℝ := (C.card : ℝ) / N.card
  have hrho : 0 ≤ rho := by dsimp [rho]; positivity
  rw [bernoulliSubset_eq_sizeMixture, sizeMixture, mass_bind]
  change expect (binomialSize N.card p hp) (fun j =>
    mass (fixedSize N j.val (Nat.le_of_lt_succ j.isLt)) (fun S => rho + 1 / 10 < crossingRatio C S)) ≤ _
  calc
    _ ≤ expect (binomialSize N.card p hp)
        (fun j => (100 * ENNReal.ofReal rho) * positiveInverse j.val) := by
      apply expect_mono_on_support
      intro j _
      by_cases hj : j.val = 0
      · have hnot : ¬ rho + 1 / 10 < 0 := by linarith
        simp only [hj, fixedSize_zero, mass_pure, crossingRatio_empty,
          positiveInverse, ite_true, mul_zero, hnot, ite_false, le_refl]
      · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
        have ht := fixedSize_ratio_tenth_tail N C j.val hC hjpos (Nat.le_of_lt_succ j.isLt)
        have hjR : (0 : ℝ) < j.val := by exact_mod_cast hjpos
        change mass (fixedSize N j.val (Nat.le_of_lt_succ j.isLt))
          (fun S => rho + 1 / 10 < crossingRatio C S) ≤
          ENNReal.ofReal (100 * rho / j.val) at ht
        rw [ENNReal.ofReal_div_of_pos hjR,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100),
          show ENNReal.ofReal (100 : ℝ) = 100 by norm_num, ENNReal.ofReal_natCast] at ht
        simpa only [positiveInverse, hj, ite_false, div_eq_mul_inv] using ht
    _ = (100 * ENNReal.ofReal rho) *
        expect (binomialSize N.card p hp) (fun j => positiveInverse j.val) := expect_const_mul _ _ _
    _ ≤ (100 * ENNReal.ofReal rho) * (2 / (((N.card + 1 : ℕ) : ℝ≥0∞) * p)) :=
      mul_le_mul le_rfl (binomialSize_positiveInverse_le N.card p hp0 hp) (by positivity) (by positivity)
    _ = (200 * ENNReal.ofReal rho) / (((N.card + 1 : ℕ) : ℝ≥0∞) * p) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := ENNReal.div_le_div_left
      (mul_le_mul (by exact_mod_cast Nat.le_succ N.card) le_rfl (by positivity) (by positivity)) _

#print axioms fixedSize_contains
#print axioms expect_uniform_eq
#print axioms sum_inter_choose
#print axioms uniformMean_crossingCount
#print axioms fixedSize_ratio_mean
#print axioms fixedSize_full_ratio
#print axioms uniformMean_crossingCount_sq
#print axioms uniformMean_ratio_variance
#print axioms uniformMean_ratio_variance_le
#print axioms fixedSize_ratio_tail
#print axioms sizeMixture_ratio_mean
#print axioms sizeMixture_ratio_variance_le
#print axioms sizeMixture_ratio_tail
#print axioms acceptedSize_ratio_tail
#print axioms bernoulliSubset
#print axioms bernoulliSubset_size_mass
#print axioms condition_bernoulliSubset_size
#print axioms bernoulliSubset_eq_sizeMixture
#print axioms bernoulliSubset_ratio_mean_le
#print axioms condition_bernoulliSubset_window
#print axioms acceptedBernoulli_ratio_tail
#print axioms binomialSize_inverse_succ_le
#print axioms binomialSize_positiveInverse_le
#print axioms bernoulliSubset_ratio_tenth_tail

end
end CutQueryComplexity.StarContraction2022.Probability
