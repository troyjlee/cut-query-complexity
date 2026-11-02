import CutQueryComplexity.DetMinCut.Parameters
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Logarithmic parameters and the harmonic product bound (Räcke–Shah, M4a)

`KK n = L(L(n))` with `L = DetMinCut.logL`, so that `L(n) K(n) = O(log n log log n)`. The
expansion factor of a cluster of size `m` in a context of size `p` is
`expFactor n p m = κ K(n) log₂(p / m)` with `κ = 64`; a cluster at index `j`
(`2^j m ≤ p`) has factor at least `κ K(n) j`.

`Bprod n j = ∏_{i=j}^{L(n)} (1 + 8 / (κ i K(n)))` controls the receiving factors of the weighted
refinement. `Bprod_le_two` is the harmonic bound: the exponent sum is at most
`(8 / (κ K)) (1 + log L) ≤ 8 / κ = 1/8`, using `∏ (1 + x_i) ≤ 1 / (1 − ∑ x_i)`.
`Bprod_step_ineq` is the one-step inequality `B_{j+1} + ρ (B_{j+1} + B_j) ≤ B_j` for
`ρ κ K j ≤ 2`.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace RackeShah

open DetMinCut Finset

/-- `K(n) = L(L(n))`. -/
def KK (n : ℕ) : ℕ := logL (logL n)

theorem one_le_KK (n : ℕ) : 1 ≤ KK n := one_le_logL' _

/-- The refinement constant. -/
def kappa : ℝ := 64

theorem kappa_pos : 0 < kappa := by norm_num [kappa]

/-- `f(p, m) = κ K(n) log₂(p / m)`. -/
noncomputable def expFactor (n p m : ℕ) : ℝ := kappa * KK n * Real.logb 2 ((p : ℝ) / m)

theorem logb_div_ge_of_pow_mul_le {p m j : ℕ} (hm : 1 ≤ m) (hj : 2 ^ j * m ≤ p) :
    (j : ℝ) ≤ Real.logb 2 ((p : ℝ) / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < p := by
    have : 1 ≤ p := le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) hj
    exact_mod_cast this
  have hle : (2 : ℝ) ^ j ≤ (p : ℝ) / m := by
    rw [le_div_iff₀ hm']; exact_mod_cast hj
  calc (j : ℝ) = Real.logb 2 ((2 : ℝ) ^ j) := by
        rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
    _ ≤ Real.logb 2 ((p : ℝ) / m) :=
        (Real.logb_le_logb one_lt_two (by positivity) (div_pos hp hm')).mpr hle

theorem expFactor_ge {n p m j : ℕ} (hm : 1 ≤ m) (hj : 2 ^ j * m ≤ p) :
    kappa * KK n * j ≤ expFactor n p m :=
  mul_le_mul_of_nonneg_left (logb_div_ge_of_pow_mul_le hm hj)
    (mul_nonneg kappa_pos.le (Nat.cast_nonneg _))

theorem four_le_expFactor {n p m : ℕ} (hm : 1 ≤ m) (h : 2 * m ≤ p) : 4 ≤ expFactor n p m := by
  have h1 := expFactor_ge (n := n) hm (j := 1) (by simpa using h)
  rw [Nat.cast_one, mul_one] at h1
  have hK : (1 : ℝ) ≤ KK n := by exact_mod_cast one_le_KK n
  have : (4 : ℝ) ≤ kappa * KK n := by unfold kappa; nlinarith
  linarith

theorem expFactor_nonneg {n p m : ℕ} (hm : 1 ≤ m) (h : m ≤ p) : 0 ≤ expFactor n p m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (1 : ℝ) ≤ (p : ℝ) / m := by rw [le_div_iff₀ hm', one_mul]; exact_mod_cast h
  exact mul_nonneg (mul_nonneg kappa_pos.le (Nat.cast_nonneg _)) (Real.logb_nonneg one_lt_two h1)

/-- `f(p, m) = κ K (log₂ p − log₂ m)`. -/
theorem expFactor_eq_sub {n p m : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) :
    expFactor n p m = kappa * KK n * (Real.logb 2 p - Real.logb 2 m) := by
  unfold expFactor
  rw [Real.logb_div (by exact_mod_cast (by omega : p ≠ 0)) (by exact_mod_cast (by omega : m ≠ 0))]

/-! ## The product bound -/

/-- `B_j = ∏_{i=j}^{L(n)} (1 + 8 / (κ i K(n)))`. -/
noncomputable def Bprod (n j : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico j (logL n + 1), (1 + 8 / (kappa * i * KK n))

theorem Bprod_term_nonneg (n i : ℕ) : 0 ≤ 8 / (kappa * i * KK n) := by
  have := kappa_pos; positivity

theorem one_le_Bprod (n j : ℕ) : 1 ≤ Bprod n j := by
  unfold Bprod
  refine one_le_prod₀ fun i _ => ?_
  have := Bprod_term_nonneg n i
  linarith

theorem Bprod_step {n j : ℕ} (hjL : j ≤ logL n) :
    Bprod n j = (1 + 8 / (kappa * j * KK n)) * Bprod n (j + 1) := by
  unfold Bprod
  rw [Finset.prod_eq_prod_Ico_succ_bot (by omega)]

theorem Bprod_succ_le (n j : ℕ) : Bprod n (j + 1) ≤ Bprod n j := by
  by_cases hjL : j ≤ logL n
  · rw [Bprod_step hjL]
    have h1 := one_le_Bprod n (j + 1)
    have h2 := Bprod_term_nonneg n j
    nlinarith
  · unfold Bprod
    rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]

theorem Bprod_antitone {n j k : ℕ} (hjk : j ≤ k) : Bprod n k ≤ Bprod n j := by
  induction k with
  | zero => rw [Nat.le_zero.mp hjk]
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact (Bprod_succ_le n k).trans (ih (by omega))
      · rw [le_antisymm hjk h]

/-- `∏ (1 + x_i) ≤ 1 / (1 − ∑ x_i)` for nonnegative `x_i` of sum below one. -/
theorem prod_one_add_le_one_div {ι : Type} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hs : ∑ i ∈ s, x i < 1) : ∏ i ∈ s, (1 + x i) ≤ 1 / (1 - ∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha]
      rw [sum_insert ha] at hs
      have hxa := hx a (mem_insert_self _ _)
      have hx' : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
      have hs0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hx'
      have hs' : ∑ i ∈ s, x i < 1 := by linarith
      have ih' := ih hx' hs'
      have hpos : 0 < 1 - ∑ i ∈ s, x i := by linarith
      have hpos' : 0 < 1 - (x a + ∑ i ∈ s, x i) := by linarith
      calc (1 + x a) * ∏ i ∈ s, (1 + x i) ≤ (1 + x a) * (1 / (1 - ∑ i ∈ s, x i)) := by
            gcongr
        _ ≤ 1 / (1 - (x a + ∑ i ∈ s, x i)) := by
            rw [mul_one_div, div_le_div_iff₀ hpos hpos']
            nlinarith

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith

/-- `1 + log L ≤ K` for `L = L(n)`, `K = L(L)`. -/
theorem one_add_log_logL_le_KK (n : ℕ) : 1 + Real.log (logL n) ≤ KK n := by
  set L := logL n
  have hL1 : 1 ≤ L := one_le_logL' n
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hK1 : 1 ≤ KK n := one_le_KK n
  have hKr : (1 : ℝ) ≤ KK n := by exact_mod_cast hK1
  have hpow : ((2 * L : ℕ) : ℝ) ≤ (2 : ℝ) ^ KK n := by
    exact_mod_cast le_two_pow_logL L
  have hlog : Real.log ((2 * L : ℕ) : ℝ) ≤ KK n * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)] at hlog
  have hl2 := log_two_le_one
  have hl2pos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

theorem sum_inv_Ico_le_harmonic (L j : ℕ) (hj : 1 ≤ j) :
    ∑ i ∈ Finset.Ico j (L + 1), (1 : ℝ) / i ≤ 1 + Real.log L := by
  have h1 : ∑ i ∈ Finset.Ico j (L + 1), (1 : ℝ) / i ≤ ∑ i ∈ Finset.Ico 1 (L + 1), (1 : ℝ) / i :=
    sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left hj) fun i _ _ => by positivity
  have h2 : ∑ i ∈ Finset.Ico 1 (L + 1), (1 : ℝ) / i = (harmonic L : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    unfold harmonic
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [one_div, add_comm]
  have h3 := harmonic_le_one_add_log L
  linarith

/-- **The harmonic product bound.** -/
theorem Bprod_le_two (n : ℕ) {j : ℕ} (hj : 1 ≤ j) : Bprod n j ≤ 2 := by
  set L := logL n
  have hK : (1 : ℝ) ≤ KK n := by exact_mod_cast one_le_KK n
  have hκ := kappa_pos
  have hterm : ∀ i : ℕ, 8 / (kappa * i * KK n) = 8 / (kappa * KK n) * (1 / i) := by
    intro i; field_simp
  have hsum : ∑ i ∈ Finset.Ico j (L + 1), 8 / (kappa * i * KK n) ≤ 1 / 8 := by
    simp only [hterm]
    rw [← mul_sum]
    have h1 := sum_inv_Ico_le_harmonic L j hj
    have h2 := one_add_log_logL_le_KK n
    have h3 : 8 / (kappa * KK n) * (KK n : ℝ) = 8 / kappa := by
      field_simp
    calc 8 / (kappa * KK n) * ∑ i ∈ Finset.Ico j (L + 1), (1 : ℝ) / i
        ≤ 8 / (kappa * KK n) * (KK n : ℝ) := by
          gcongr
          exact h1.trans h2
      _ = 8 / kappa := h3
      _ = 1 / 8 := by norm_num [kappa]
  have hnn : ∀ i ∈ Finset.Ico j (L + 1), 0 ≤ 8 / (kappa * i * KK n) :=
    fun i _ => Bprod_term_nonneg n i
  have := prod_one_add_le_one_div (Finset.Ico j (L + 1)) (fun i => 8 / (kappa * i * KK n)) hnn
    (by linarith)
  unfold Bprod
  refine this.trans ?_
  have hpos : (0 : ℝ) < 1 - ∑ i ∈ Finset.Ico j (L + 1), 8 / (kappa * i * KK n) := by linarith
  rw [div_le_iff₀ hpos]
  linarith

/-- **The one-step inequality.** -/
theorem Bprod_step_ineq {n j : ℕ} (hj : 1 ≤ j) (hjL : j ≤ logL n) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ * (kappa * KK n * j) ≤ 2) :
    Bprod n (j + 1) + ρ * (Bprod n (j + 1) + Bprod n j) ≤ Bprod n j := by
  have hstep := Bprod_step (n := n) hjL
  set B' := Bprod n (j + 1)
  have hB'1 := one_le_Bprod n (j + 1)
  have hB2 := Bprod_le_two n hj
  set c := kappa * KK n * j with hc_def
  have hK : (1 : ℝ) ≤ KK n := by exact_mod_cast one_le_KK n
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hc4 : 4 ≤ c := by
    rw [hc_def]; unfold kappa; nlinarith
  have hcpos : 0 < c := by linarith
  have hterm : 8 / (kappa * j * KK n) = 8 / c := by
    rw [hc_def]; ring_nf
  rw [hterm] at hstep
  set t := 1 / c with ht
  have htpos : 0 < t := by positivity
  have ht4 : t ≤ 1 / 4 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hc4
  have hρt : ρ ≤ 2 * t := by
    rw [ht, mul_one_div, le_div_iff₀ hcpos]; linarith
  have h8 : 8 / c = 8 * t := by rw [ht]; ring
  rw [h8] at hstep
  rw [hstep]
  -- `ρ (2 + 8 t) ≤ 8 t` because `ρ ≤ 2 t` and `t ≤ 1/4`
  have hkey : ρ * (2 + 8 * t) ≤ 8 * t := by nlinarith
  nlinarith

end RackeShah
end Hierarchy
end CutQueryComplexity
