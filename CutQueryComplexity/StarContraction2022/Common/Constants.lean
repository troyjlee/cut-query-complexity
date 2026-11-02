import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Public guards and the classical numerical schedule

The coefficients for bucket recovery and parallel certificates are numeric
parameters only. Nothing here asserts the existence of either query program.
All budget envelopes depend on public dimensions and tested count guards.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Schedule

noncomputable section

def bucketCoefficient (CB : ℕ) : ℕ := 3 * (1 + 400 * CB)
def recoveryCoefficient (CB : ℕ) : ℕ := 100 * bucketCoefficient CB + 12
def insideCoefficient : ℕ := 1500300000
def weightedCoefficient : ℕ := 6000020000000
def degreeCutoff : ℕ := ⌈Real.exp 17⌉₊
def sizeCutoff : ℕ := ⌈Real.exp 1000⌉₊
def height (d : ℕ) : ℕ := ⌈5000 * Real.log d⌉₊
def centerProbability (d : ℕ) : ℝ := 100000 * Real.log d / d

def pStar : ℝ :=
  (1 / 6) * (3 / 10) ^ 115 * (1 / 5) ^ 2000 * (199 / 200) * (99 / 100)

def repetitions : ℕ := ⌈Real.log 3 / pStar⌉₊

def attemptCoefficient (CB CP : ℕ) : ℕ :=
  3 * sizeCutoff + 10 + 5000 * recoveryCoefficient CB +
    2 * insideCoefficient * recoveryCoefficient CB +
    100 * (CP * degreeCutoff + 1) + 100 * (160001 * CP + 1) +
    12 + weightedCoefficient

theorem attemptCoefficient_expand (CB CP : ℕ) :
    attemptCoefficient CB CP = 3 * sizeCutoff + 6936208760222 +
      360072600000000 * CB + (100 * degreeCutoff + 16000100) * CP := by
  unfold attemptCoefficient recoveryCoefficient bucketCoefficient insideCoefficient
    weightedCoefficient
  ring

/-- Range validation precedes every use of a measured minimum degree. -/
def DegreeGuard (n d : ℕ) : Prop := 1 ≤ d ∧ d < n

def CenterGuard (n d centers : ℕ) : Prop :=
  centers ≤ n ∧ (centers : ℝ) * d ≤ 300000 * n * Real.log d

def BadGuard (n d bad : ℕ) : Prop := 1000 * bad * d ≤ n

def MiddleGuard (n d q : ℕ) : Prop :=
  DegreeGuard n d ∧ 2 ≤ q ∧ q ≤ n ∧ q * d ≤ 80000 * n ∧
    (d : ℝ) ≤ (Real.log n) ^ 10

def HighGuard (n d q : ℕ) : Prop :=
  DegreeGuard n d ∧ 2 ≤ q ∧ q ≤ n ∧ (Real.log n) ^ 10 < (d : ℝ) ∧
    (q : ℝ) * d ≤ 300001 * n * Real.log d

def ParallelEligible (n q : ℕ) : Prop :=
  2 ≤ q ∧ q ≤ n ∧ (Real.logb 2 n) ^ ((5 : ℝ) / 2) ≤ q

/-- A scalar ledger entry, not a certificate algorithm or an expected-cost premise. -/
def parallelEstimate (CP n d q : ℕ) : ℝ :=
  CP * ((n : ℝ) + d * q * Real.log n / Real.log q)

def parallelClock (CP n d q : ℕ) : ℕ := 100 * ⌈parallelEstimate CP n d q⌉₊

theorem degreeCutoff_ge : 18 ≤ degreeCutoff := by
  have he : (18 : ℝ) ≤ Real.exp 17 := by
    linarith [Real.add_one_le_exp 17]
  have hc : Real.exp 17 ≤ (degreeCutoff : ℝ) := Nat.le_ceil _
  exact_mod_cast he.trans hc

theorem sizeCutoff_ge : 1001 ≤ sizeCutoff := by
  have he : (1001 : ℝ) ≤ Real.exp 1000 := by
    linarith [Real.add_one_le_exp 1000]
  have hc : Real.exp 1000 ≤ (sizeCutoff : ℝ) := Nat.le_ceil _
  exact_mod_cast he.trans hc

theorem log_degree_ge (d : ℕ) (hd : degreeCutoff ≤ d) :
    17 ≤ Real.log d := by
  have hc : Real.exp 17 ≤ (d : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hd)
  simpa using Real.log_le_log (Real.exp_pos 17) hc

theorem log_size_ge (n : ℕ) (hn : sizeCutoff ≤ n) :
    1000 ≤ Real.log n := by
  have hc : Real.exp 1000 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  simpa using Real.log_le_log (Real.exp_pos 1000) hc

theorem centerProbability_pos (d : ℕ) (hd : degreeCutoff ≤ d) :
    0 < centerProbability d := by
  have ht := log_degree_ge d hd
  have hd18 := degreeCutoff_ge.trans hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold centerProbability
  exact div_pos (mul_pos (by norm_num) (by linarith)) hd0

/-- The public degree cutoff makes the literal sampling parameter a probability. -/
theorem centerProbability_le_half (d : ℕ) (hd : degreeCutoff ≤ d) :
    centerProbability d ≤ 1 / 2 := by
  have hc : Real.exp 17 ≤ (d : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hd)
  have he : (3400000 : ℝ) ≤ Real.exp 17 := by
    calc
      (3400000 : ℝ) ≤ (5 / 2 : ℝ) ^ 17 := by norm_num
      _ ≤ (Real.exp 1) ^ 17 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 17
      _ = Real.exp 17 := by rw [← Real.exp_nat_mul]; norm_num
  have hexp : Real.exp 1 ≤ Real.exp 17 := Real.exp_le_exp.mpr (by norm_num)
  have hfrac := Real.log_div_self_antitoneOn
    (show Real.exp 17 ∈ Set.Ici (Real.exp 1) from hexp)
    (show (d : ℝ) ∈ Set.Ici (Real.exp 1) from hexp.trans hc) hc
  change Real.log (d : ℝ) / d ≤ Real.log (Real.exp 17) / Real.exp 17 at hfrac
  rw [Real.log_exp] at hfrac
  unfold centerProbability
  calc
    100000 * Real.log (d : ℝ) / d = 100000 * (Real.log (d : ℝ) / d) := by ring
    _ ≤ 100000 * (17 / Real.exp 17) := mul_le_mul_of_nonneg_left hfrac (by norm_num)
    _ ≤ 1 / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (Real.exp_pos 17)]
      linarith

theorem centerProbability_le_one (d : ℕ) (hd : degreeCutoff ≤ d) :
    centerProbability d ≤ 1 := (centerProbability_le_half d hd).trans (by norm_num)

theorem height_ge (d : ℕ) (hd : degreeCutoff ≤ d) : 85000 ≤ height d := by
  have ht := log_degree_ge d hd
  have hc : 5000 * Real.log d ≤ (height d : ℝ) := Nat.le_ceil _
  have hh : (85000 : ℝ) ≤ height d := by linarith
  exact_mod_cast hh

theorem twoOut_degree_envelope (d : ℕ) (hd : degreeCutoff ≤ d) :
    40 ≤ height d / 5 ∧ height d ≤ 6 * (height d / 5) := by
  have hh := height_ge d hd
  omega

theorem log_le_half {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / 2 by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h
  have h2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem square_le_exp {x : ℝ} (hx : 0 < x) : x ^ 2 ≤ Real.exp x := by
  apply (Real.log_le_log_iff (pow_pos hx 2) (Real.exp_pos x)).mp
  rw [Real.log_pow, Real.log_exp]
  have := log_le_half hx
  norm_num
  linarith

theorem log_le_twentieth {z : ℝ} (hz : 1000 ≤ z) : Real.log z ≤ z / 20 := by
  have hz0 : 0 < z := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < z / 40 by positivity)
  rw [Real.log_div hz0.ne' (by norm_num)] at h
  have h40 : Real.log 40 ≤ 6 := by
    have hle : Real.log 40 ≤ Real.log ((2 : ℝ) ^ 6) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hle
    have h2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num at hle
    linarith
  linarith

theorem power_fourteen_le_exp {z : ℝ} (hz : 1000 ≤ z) :
    z ^ 14 ≤ Real.exp z := by
  have hz0 : 0 < z := by linarith
  apply (Real.log_le_log_iff (pow_pos hz0 14) (Real.exp_pos z)).mp
  rw [Real.log_pow, Real.log_exp]
  have := log_le_twentieth hz
  norm_num
  linarith

theorem clog_le_twice_log_add_one (n : ℕ) (hn : 1 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 2 * Real.log n + 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hb : Real.logb 2 n ≤ 2 * Real.log n := by
    rw [Real.logb, div_le_iff₀ (by linarith : 0 < Real.log 2)]
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlog2.le)]
  have hc : (Nat.clog 2 n : ℝ) ≤ Real.logb 2 n + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hnR)).le
  linarith

theorem log_base_ge_one (q : ℕ) (hq : 2 ≤ q) :
    1 ≤ Real.log (2 * (q : ℝ) + 2) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  linarith [Real.exp_one_lt_three]

theorem clog_le_three_log_base (q : ℕ) (hq : 2 ≤ q) :
    (Nat.clog 2 q : ℝ) ≤ 3 * Real.log (2 * (q : ℝ) + 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hl := Real.log_le_log hq0 (show (q : ℝ) ≤ 2 * q + 2 by linarith)
  have hc := clog_le_twice_log_add_one q (by omega)
  have hb := log_base_ge_one q hq
  linarith

theorem log_base_le_twice_log (n q : ℕ) (hn : 3 ≤ n) (hq : q ≤ n) :
    Real.log (2 * (q : ℝ) + 2) ≤ 2 * Real.log n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (q : ℝ) ≤ n := by exact_mod_cast hq
  have hp : 0 < 2 * (q : ℝ) + 2 := by positivity
  have h : 2 * (q : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hl := Real.log_le_log hp h
  simpa [Real.log_pow] using hl

/-- The actual center-count guard absorbs the learned inside degree. -/
theorem height_centers_le (n d centers : ℕ) (hd : degreeCutoff ≤ d)
    (h : CenterGuard n d centers) :
    height d * centers ≤ insideCoefficient * n := by
  have ht : 17 ≤ Real.log d := log_degree_ge d hd
  have hd0 : 0 < d := lt_of_lt_of_le (by omega : 0 < 18) (degreeCutoff_ge.trans hd)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have ht0 : 0 < Real.log (d : ℝ) := by linarith
  have hsq : (Real.log (d : ℝ)) ^ 2 ≤ d := by
    simpa [Real.exp_log hdR] using square_le_exp ht0
  have hlog : Real.log (d : ℝ) ≤ d := by
    linarith [Real.add_one_le_exp (Real.log (d : ℝ)), Real.exp_log hdR]
  have hh : (height d : ℝ) ≤ 5000 * Real.log d + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hc : (centers : ℝ) ≤ 300000 * n * Real.log d / d :=
    (le_div_iff₀ hdR).mpr h.2
  have hprod : (height d : ℝ) * centers ≤ (insideCoefficient : ℝ) * n := by
    calc
      (height d : ℝ) * centers ≤
          (5000 * Real.log d + 1) * (300000 * n * Real.log d / d) := by
            gcongr
      _ = 300000 * n * (5000 * (Real.log (d : ℝ)) ^ 2 + Real.log d) / d := by ring
      _ ≤ 300000 * n * (5000 * (d : ℝ) + d) / d := by gcongr
      _ = (insideCoefficient : ℝ) * n := by
        unfold insideCoefficient
        push_cast
        field_simp [hdR.ne'] <;> ring
  exact_mod_cast hprod

theorem centers_div_height_le (n d centers : ℕ) (hd : degreeCutoff ≤ d)
    (h : CenterGuard n d centers) :
    (centers : ℝ) / height d ≤ 60 * n / d := by
  have hd18 := degreeCutoff_ge.trans hd
  have hh85 := height_ge d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hh0 : (0 : ℝ) < height d := by exact_mod_cast (show 0 < height d by omega)
  have hh : 5000 * Real.log d ≤ (height d : ℝ) := Nat.le_ceil _
  apply (div_le_div_iff₀ hh0 hd0).mpr
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 60 * (n : ℝ) by positivity)
  exact h.2.trans (by nlinarith)

theorem inside_omission_threshold (d : ℕ) (hd : degreeCutoff ≤ d) :
    8 * (height d : ℝ) < 50000 * Real.log d := by
  have ht := log_degree_ge d hd
  have hh : (height d : ℝ) ≤ 5000 * Real.log d + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  linarith

theorem badGuard_real (n d bad : ℕ) (h : BadGuard n d bad) :
    (bad : ℝ) * d ≤ n / 1000 := by
  have hr : (1000 : ℝ) * bad * d ≤ n := by exact_mod_cast h
  linarith

/-- Arithmetic after the actual two-out component estimate; no stochastic claim is assumed here. -/
theorem middle_component_guard (n d centers bad q : ℕ) (hd : degreeCutoff ≤ d)
    (hc : CenterGuard n d centers) (hb : BadGuard n d bad)
    (hq : (q : ℝ) ≤ bad + (7 + 48 * (Real.exp 1) ^ 3) * ((centers : ℝ) / height d)) :
    q * d ≤ 80000 * n := by
  have hd18 := degreeCutoff_ge.trans hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hratio := centers_div_height_le n d centers hd hc
  have hbad := badGuard_real n d bad hb
  have he3 : (Real.exp 1) ^ 3 ≤ 27 := by
    calc
      (Real.exp 1) ^ 3 ≤ (3 : ℝ) ^ 3 :=
        pow_le_pow_left₀ (Real.exp_nonneg 1) Real.exp_one_lt_three.le 3
      _ = 27 := by norm_num
  have hcoeff : (1 / 1000 : ℝ) + 60 * (7 + 48 * (Real.exp 1) ^ 3) ≤ 80000 := by
    linarith
  have hqd : (q : ℝ) * d ≤ 80000 * n := by
    calc
      (q : ℝ) * d ≤ (bad + (7 + 48 * (Real.exp 1) ^ 3) *
          ((centers : ℝ) / height d)) * d := mul_le_mul_of_nonneg_right hq hd0.le
      _ = (bad : ℝ) * d + (7 + 48 * (Real.exp 1) ^ 3) *
          ((centers : ℝ) / height d) * d := by ring
      _ ≤ (n : ℝ) / 1000 + (7 + 48 * (Real.exp 1) ^ 3) * (60 * n / d) * d := by
        gcongr
      _ = ((1 / 1000 : ℝ) + 60 * (7 + 48 * (Real.exp 1) ^ 3)) * n := by
        field_simp [hd0.ne'] <;> ring
      _ ≤ 80000 * n := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)
  exact_mod_cast hqd

/-- Arithmetic after outside attachment, for the guarded high-degree quotient. -/
theorem high_component_guard (n d centers bad q : ℕ) (hd : degreeCutoff ≤ d)
    (hc : CenterGuard n d centers) (hb : BadGuard n d bad)
    (hq : q ≤ centers + bad) :
    (q : ℝ) * d ≤ 300001 * n * Real.log d := by
  have ht := log_degree_ge d hd
  have hqR : (q : ℝ) ≤ centers + bad := by exact_mod_cast hq
  have hbad := badGuard_real n d bad hb
  calc
    (q : ℝ) * d ≤ (centers + bad : ℝ) * d :=
      mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg d)
    _ = (centers : ℝ) * d + (bad : ℝ) * d := by ring
    _ ≤ 300000 * n * Real.log d + (n : ℝ) / 1000 := add_le_add hc.2 hbad
    _ ≤ 300001 * n * Real.log d := by
      have hm := mul_nonneg (Nat.cast_nonneg n)
        (sub_nonneg.mpr (show (1 / 1000 : ℝ) ≤ Real.log d by linarith))
      nlinarith

/-- Public high-degree guards imply the reviewed linear weighted-solver envelope. -/
theorem high_weighted_envelope (n d q : ℕ) (hn : sizeCutoff ≤ n)
    (h : HighGuard n d q) :
    5000000 * (q : ℝ) * (Real.log (2 * (q : ℝ) + 2)) ^ 2 ≤
      (weightedCoefficient : ℝ) * n := by
  have hz := log_size_ge n hn
  have hn1001 := sizeCutoff_ge.trans hn
  have hd1 := h.1.1
  have hn3 : 3 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdn : (d : ℝ) ≤ n := by exact_mod_cast h.1.2.le
  have ht : Real.log (d : ℝ) ≤ Real.log n := Real.log_le_log hdR hdn
  have hz1 : 1 ≤ Real.log (n : ℝ) := by linarith
  have hz0 : 0 < Real.log (n : ℝ) := by linarith
  have hp : (Real.log (n : ℝ)) ^ 3 ≤ (Real.log n) ^ 10 :=
    pow_le_pow_right₀ hz1 (by omega)
  have hqd : (q : ℝ) * (Real.log (n : ℝ)) ^ 3 ≤
      300001 * n * Real.log n := by
    calc
      (q : ℝ) * (Real.log (n : ℝ)) ^ 3 ≤ (q : ℝ) * d := by gcongr; exact hp.trans h.2.2.2.1.le
      _ ≤ 300001 * n * Real.log d := h.2.2.2.2
      _ ≤ 300001 * n * Real.log n := by gcongr
  have hqz : (q : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ 300001 * n := by
    apply (mul_le_mul_iff_right₀ hz0).mp
    convert hqd using 1 <;> ring
  have hu := log_base_le_twice_log n q hn3 h.2.2.1
  have hu0 : 0 ≤ Real.log (2 * (q : ℝ) + 2) :=
    (by linarith [log_base_ge_one q h.2.1])
  calc
    5000000 * (q : ℝ) * (Real.log (2 * (q : ℝ) + 2)) ^ 2 ≤
        5000000 * q * (2 * Real.log n) ^ 2 := by gcongr
    _ = 20000000 * ((q : ℝ) * (Real.log (n : ℝ)) ^ 2) := by ring
    _ ≤ 20000000 * (300001 * (n : ℝ)) := by gcongr
    _ = (weightedCoefficient : ℝ) * n := by norm_num [weightedCoefficient]; ring

/-- The small-quotient sequential fallback fits its linear allowance. -/
theorem middle_small_envelope (n d q : ℕ) (hn : sizeCutoff ≤ n)
    (h : MiddleGuard n d q) (hq : (q : ℝ) ≤ (Real.log n) ^ 3) :
    12 * (d : ℝ) * q * ((Nat.clog 2 q : ℝ) + 1) ≤ 12 * n := by
  have hz := log_size_ge n hn
  have hn1001 := sizeCutoff_ge.trans hn
  have hq2 := h.2.1
  have hz0 : 0 < Real.log (n : ℝ) := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogq : Real.log (q : ℝ) ≤ 3 * Real.log (Real.log n) := by
    have hl := Real.log_le_log hq0 hq
    simpa [Real.log_pow] using hl
  have hc := clog_le_twice_log_add_one q (by omega)
  have hclog : (Nat.clog 2 q : ℝ) + 1 ≤ Real.log n := by
    have := log_le_twentieth hz
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    12 * (d : ℝ) * q * ((Nat.clog 2 q : ℝ) + 1) ≤
        12 * (Real.log n) ^ 10 * (Real.log n) ^ 3 * Real.log n := by
          gcongr
          exact h.2.2.2.2
    _ = 12 * (Real.log (n : ℝ)) ^ 14 := by ring
    _ ≤ 12 * Real.exp (Real.log (n : ℝ)) := by gcongr; exact power_fourteen_le_exp hz
    _ = 12 * n := by rw [Real.exp_log hnR]

/-- The parallel certificate's logarithmic domain holds in the large-quotient branch. -/
theorem parallelEligible_of_cube (n q : ℕ) (hn : sizeCutoff ≤ n)
    (hq2 : 2 ≤ q) (hqn : q ≤ n) (hq : (Real.log n) ^ 3 ≤ (q : ℝ)) :
    ParallelEligible n q := by
  refine ⟨hq2, hqn, ?_⟩
  have hz := log_size_ge n hn
  have hn1001 := sizeCutoff_ge.trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hz0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hb0 : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hn1
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hb : Real.logb 2 n ≤ 2 * Real.log n := by
    rw [Real.logb, div_le_iff₀ (by linarith : 0 < Real.log 2)]
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr h2.le)]
  have hpow : ((Real.logb 2 n) ^ ((5 : ℝ) / 2)) ^ 2 = (Real.logb 2 n) ^ 5 := by
    rw [← Real.rpow_mul_natCast hb0]
    norm_num
  have hsq : ((Real.logb 2 n) ^ ((5 : ℝ) / 2)) ^ 2 ≤ ((Real.log (n : ℝ)) ^ 3) ^ 2 := by
    rw [hpow]
    calc
      (Real.logb 2 n) ^ 5 ≤ (2 * Real.log n) ^ 5 := pow_le_pow_left₀ hb0 hb 5
      _ ≤ ((Real.log (n : ℝ)) ^ 3) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right (show (32 : ℝ) ≤ Real.log n by linarith)
          (pow_nonneg hz0 5)
        nlinarith
  have ha0 : 0 ≤ (Real.logb 2 n) ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hb0 _
  have hcube0 : 0 ≤ (Real.log (n : ℝ)) ^ 3 := pow_nonneg hz0 _
  have hle : (Real.logb 2 n) ^ ((5 : ℝ) / 2) ≤ (Real.log (n : ℝ)) ^ 3 := by
    nlinarith
  exact hle.trans hq

private theorem middle_large_real {z d q : ℝ} (hz : 1000 ≤ z) (hd : 0 < d)
    (hdz : d ≤ z ^ 10) (hq : z ^ 3 ≤ q) (hqd : q * d ≤ 80000 * Real.exp z) :
    d * q * z / Real.log q ≤ 160000 * Real.exp z := by
  let M := 80000 * Real.exp z / d
  have hz0 : 0 < z := by linarith
  have h8 : (8 : ℝ) ≤ z ^ 3 := by
    calc
      (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ z ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have hq0 : 0 < q := by linarith
  have hqM : q ≤ M := (le_div_iff₀ hd).mpr hqd
  have hM0 : 0 < M := hq0.trans_le hqM
  have hlogd : Real.log d ≤ 10 * Real.log z := by
    have h := Real.log_le_log hd hdz
    simpa [Real.log_pow] using h
  have hlogM : z / 2 ≤ Real.log M := by
    dsimp [M]
    rw [Real.log_div (by positivity) hd.ne',
      Real.log_mul (by norm_num) (Real.exp_pos z).ne', Real.log_exp]
    have hconst : 0 ≤ Real.log (80000 : ℝ) := Real.log_nonneg (by norm_num)
    have hsmall := log_le_twentieth hz
    linarith
  have hlogq0 : 0 < Real.log q := Real.log_pos (by linarith)
  have hlogM0 : 0 < Real.log M := by linarith
  have hqexp : Real.exp 1 ≤ q := Real.exp_one_lt_three.le.trans
    ((by norm_num : (3 : ℝ) ≤ 8).trans (h8.trans hq))
  have hanti := Real.log_div_self_antitoneOn
    (show q ∈ Set.Ici (Real.exp 1) from hqexp)
    (show M ∈ Set.Ici (Real.exp 1) from hqexp.trans hqM) hqM
  change Real.log M / M ≤ Real.log q / q at hanti
  have hratio : q / Real.log q ≤ M / Real.log M := by
    rw [div_le_div_iff₀ hM0 hq0] at hanti
    apply (div_le_div_iff₀ hlogq0 hlogM0).mpr
    nlinarith
  calc
    d * q * z / Real.log q = d * z * (q / Real.log q) := by ring
    _ ≤ d * z * (M / Real.log M) := by gcongr
    _ = 80000 * Real.exp z * z / Real.log M := by
      dsimp [M]
      field_simp [hd.ne', hlogM0.ne'] <;> ring
    _ ≤ 160000 * Real.exp z := by
      rw [div_le_iff₀ hlogM0]
      have hm := mul_le_mul_of_nonneg_left hlogM (show 0 ≤ 160000 * Real.exp z by positivity)
      nlinarith

/-- The actual public middle-degree product guard gives the parallel cost envelope. -/
theorem middle_large_envelope (n d q : ℕ) (hn : sizeCutoff ≤ n)
    (h : MiddleGuard n d q) (hq : (Real.log n) ^ 3 ≤ (q : ℝ)) :
    (d : ℝ) * q * Real.log n / Real.log q ≤ 160000 * n := by
  have hz := log_size_ge n hn
  have hn1001 := sizeCutoff_ge.trans hn
  have hd1 := h.1.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqd : (q : ℝ) * d ≤ 80000 * n := by exact_mod_cast h.2.2.2.1
  have he := middle_large_real hz hd0 h.2.2.2.2 hq (by simpa [Real.exp_log hn0] using hqd)
  simpa [Real.exp_log hn0] using he

theorem parallelEligible_identity (n : ℕ) (hn : sizeCutoff ≤ n) :
    ParallelEligible n n := by
  have hn1001 := sizeCutoff_ge.trans hn
  have hz := log_size_ge n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply parallelEligible_of_cube n n hn (by omega) le_rfl
  calc
    (Real.log (n : ℝ)) ^ 3 ≤ (Real.log n) ^ 14 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    _ ≤ Real.exp (Real.log (n : ℝ)) := power_fourteen_le_exp hz
    _ = n := Real.exp_log hn0

theorem small_degree_envelope (n d : ℕ) (hn : sizeCutoff ≤ n)
    (hd : d < degreeCutoff) :
    (n : ℝ) + d * n * Real.log n / Real.log n ≤ (degreeCutoff : ℝ) * n := by
  have hz := log_size_ge n hn
  have hl : Real.log (n : ℝ) ≠ 0 := by linarith
  have hdR : (d : ℝ) + 1 ≤ degreeCutoff := by exact_mod_cast Nat.succ_le_of_lt hd
  rw [mul_div_cancel_right₀ _ hl]
  have hm := mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg n)
  nlinarith

theorem small_input_envelope (n : ℕ) (hn : n < sizeCutoff) :
    3 * n ^ 2 ≤ 3 * sizeCutoff * n := by
  have hm := Nat.mul_le_mul_right n hn.le
  nlinarith

theorem inside_recovery_envelope (CB n d centers : ℕ) (hd : degreeCutoff ≤ d)
    (h : CenterGuard n d centers) :
    recoveryCoefficient CB * height d * (centers + centers) ≤
      2 * insideCoefficient * recoveryCoefficient CB * n := by
  have hm := Nat.mul_le_mul_left (2 * recoveryCoefficient CB) (height_centers_le n d centers hd h)
  nlinarith

/-- Ceilings of public real budgets cost at most one extra query per attempt. -/
theorem capped_linear_envelope (n C : ℕ) {B : ℝ} (hn : 1 ≤ n)
    (hB0 : 0 ≤ B) (hB : B ≤ (C : ℝ) * n) :
    100 * ⌈B⌉₊ ≤ 100 * (C + 1) * n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc := (Nat.ceil_lt_add_one hB0).le
  have he : (⌈B⌉₊ : ℝ) ≤ ((C + 1) * n : ℕ) := by
    push_cast
    nlinarith
  have hNat : ⌈B⌉₊ ≤ (C + 1) * n := by exact_mod_cast he
  nlinarith

theorem middle_parallelClock_le (CP n d q : ℕ) (hn : sizeCutoff ≤ n)
    (h : MiddleGuard n d q) (hq : (Real.log n) ^ 3 ≤ (q : ℝ)) :
    parallelClock CP n d q ≤ 100 * (160001 * CP + 1) * n := by
  have hn1001 := sizeCutoff_ge.trans hn
  have hn1 : 1 ≤ n := by omega
  have hq2 := h.2.1
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hlq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hB0 : 0 ≤ parallelEstimate CP n d q := by
    unfold parallelEstimate
    positivity
  have hbound := middle_large_envelope n d q hn h hq
  have hB : parallelEstimate CP n d q ≤ ((160001 * CP : ℕ) : ℝ) * n := by
    unfold parallelEstimate
    push_cast
    calc
      (CP : ℝ) * ((n : ℝ) + d * q * Real.log n / Real.log q) ≤
          CP * (160001 * (n : ℝ)) := by gcongr; linarith
      _ = _ := by ring
  exact capped_linear_envelope n (160001 * CP) hn1 hB0 hB

theorem small_degree_parallelClock_le (CP n d : ℕ) (hn : sizeCutoff ≤ n)
    (hd : d < degreeCutoff) :
    parallelClock CP n d n ≤ 100 * (CP * degreeCutoff + 1) * n := by
  have hn1001 := sizeCutoff_ge.trans hn
  have hn1 : 1 ≤ n := by omega
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hB0 : 0 ≤ parallelEstimate CP n d n := by
    unfold parallelEstimate
    positivity
  have hB : parallelEstimate CP n d n ≤ ((CP * degreeCutoff : ℕ) : ℝ) * n := by
    unfold parallelEstimate
    push_cast
    calc
      (CP : ℝ) * ((n : ℝ) + d * n * Real.log n / Real.log n) ≤
          CP * ((degreeCutoff : ℝ) * n) := by
            gcongr
            exact small_degree_envelope n d hn hd
      _ = _ := by ring
  exact capped_linear_envelope n (CP * degreeCutoff) hn1 hB0 hB

theorem pStar_pos : 0 < pStar := by unfold pStar; positivity

theorem pStar_le_one : pStar ≤ 1 := by
  have h3 : (3 / 10 : ℝ) ^ 115 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h5 : (1 / 5 : ℝ) ^ 2000 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h30 : 0 ≤ (3 / 10 : ℝ) ^ 115 := by positivity
  have h50 : 0 ≤ (1 / 5 : ℝ) ^ 2000 := by positivity
  unfold pStar
  calc
    (1 / 6 : ℝ) * (3 / 10) ^ 115 * (1 / 5) ^ 2000 * (199 / 200) * (99 / 100) ≤
        (1 / 6 : ℝ) * 1 * 1 * (199 / 200) * (99 / 100) := by gcongr
    _ ≤ 1 := by norm_num

theorem repetitions_mul_pStar : Real.log 3 ≤ (repetitions : ℝ) * pStar := by
  exact (div_le_iff₀ pStar_pos).mp (Nat.le_ceil _)

/-- Arithmetic amplification; a probability application still needs independent attempts. -/
theorem repetition_failure_le : (1 - pStar) ^ repetitions ≤ (1 / 3 : ℝ) := by
  have h0 : 0 ≤ 1 - pStar := by linarith [pStar_le_one]
  have hstep : 1 - pStar ≤ Real.exp (-pStar) := by
    linarith [Real.add_one_le_exp (-pStar)]
  calc
    (1 - pStar) ^ repetitions ≤ (Real.exp (-pStar)) ^ repetitions :=
      pow_le_pow_left₀ h0 hstep _
    _ = Real.exp (-((repetitions : ℝ) * pStar)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log 3) := by
      apply Real.exp_le_exp.mpr
      linarith [repetitions_mul_pStar]
    _ = 1 / 3 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

#print axioms attemptCoefficient_expand
#print axioms log_degree_ge
#print axioms log_size_ge
#print axioms centerProbability_le_one
#print axioms centerProbability_le_half
#print axioms twoOut_degree_envelope
#print axioms height_centers_le
#print axioms middle_component_guard
#print axioms high_component_guard
#print axioms high_weighted_envelope
#print axioms middle_small_envelope
#print axioms parallelEligible_of_cube
#print axioms middle_large_envelope
#print axioms capped_linear_envelope
#print axioms middle_parallelClock_le
#print axioms small_degree_parallelClock_le
#print axioms repetition_failure_le

end
end CutQueryComplexity.StarContraction2022.Schedule
