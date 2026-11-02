import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Size parameters of the deterministic algorithm

`logL n = max 1 ⌈log₂ 2n⌉` and its elementary bounds, the eventual inequality
`L(N)^7 ≤ ⌊√N⌋` (`exists_logL7_threshold`), and the tuned center parameter
`kLog7 N = max 2 ⌈⌊√N⌋ / L(N)^6⌉` with `⌊√N⌋ / L⁶ ≤ kLog7 N ≤ 2⌊√N⌋ / L⁶` above the threshold.

This module is below the main algorithm in the import graph, so that the algorithm can use
the tuned parameter.
-/

namespace CutQueryComplexity
namespace DetMinCut

open Filter Topology

/-- `L(n) = max 1 ⌈log₂ 2n⌉`; this is `⌈log₂ 2n⌉` for `n ≥ 1`, and `L(0) = 1` so that
polylogarithmic bounds `a(r) ≤ A₀ L(r)^p` are satisfiable at `r = 0`. -/
def logL (n : ℕ) : ℕ := max 1 (Nat.clog 2 (2 * n))

theorem one_le_logL' (n : ℕ) : 1 ≤ logL n := le_max_left _ _

theorem one_le_logL {n : ℕ} (_hn : 1 ≤ n) : 1 ≤ logL n := one_le_logL' n

theorem logL_eq {n : ℕ} (hn : 1 ≤ n) : logL n = Nat.clog 2 (2 * n) := by
  unfold logL
  refine max_eq_right ?_
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have := Nat.le_pow_clog one_lt_two (2 * n)
  rw [h0] at this; omega

theorem clog_le_logL' (n : ℕ) : Nat.clog 2 (2 * n) ≤ logL n := le_max_right _ _

theorem le_two_pow_logL (n : ℕ) : 2 * n ≤ 2 ^ logL n :=
  (Nat.le_pow_clog one_lt_two _).trans (Nat.pow_le_pow_right (by norm_num) (clog_le_logL' n))

theorem clog_le_logL {N n : ℕ} (hN : N ≤ n) : Nat.clog 2 N ≤ logL n :=
  (Nat.clog_mono_right 2 (by omega)).trans (clog_le_logL' n)

theorem clog_pred_le_logL {N n : ℕ} (hN : N ≤ n) : Nat.clog 2 (N - 1) ≤ logL n :=
  (Nat.clog_mono_right 2 (by omega)).trans (clog_le_logL' n)

theorem log_le_logL {N n : ℕ} (hN : N ≤ n) : Nat.log 2 N ≤ logL n :=
  (Nat.log_le_clog 2 N).trans (clog_le_logL hN)

theorem logL_mono {N n : ℕ} (hN : N ≤ n) : logL N ≤ logL n :=
  max_le_max le_rfl (Nat.clog_mono_right 2 (by omega))

theorem logL_three {N n : ℕ} (hN : N ≤ n) (_hn : 1 ≤ n) : logL (3 * N + 1) ≤ 3 * logL n := by
  have h1 := one_le_logL' n
  have h2 : Nat.clog 2 (2 * (3 * N + 1)) ≤ logL n + 2 := by
    rw [Nat.clog_le_iff_le_pow one_lt_two]
    have := le_two_pow_logL n
    rw [pow_add]; omega
  unfold logL at h2 ⊢
  omega

theorem realLog_le_logL {N n : ℕ} (hN : N ≤ n) : Real.log (2 * N) ≤ logL n := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  have h2 : (2 * N : ℝ) ≤ 2 ^ logL n := by
    have := le_two_pow_logL n
    exact_mod_cast (show 2 * N ≤ 2 ^ logL n by omega)
  calc Real.log (2 * N) ≤ Real.log (2 ^ logL n) := Real.log_le_log (by positivity) h2
    _ = logL n * Real.log 2 := by rw [Real.log_pow]
    _ ≤ logL n * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    _ = logL n := mul_one _

/-! ## The eventual inequality `L(N)^7 ≤ ⌊√N⌋` -/

theorem eventually_pow14_le_two_pow : ∃ J : ℕ, 4 ≤ J ∧ ∀ j, J ≤ j → (j + 3) ^ 14 ≤ 2 ^ j := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 14 (one_lt_two : (1 : ℝ) < 2)
  have hev : ∀ᶠ j : ℕ in atTop, (j : ℝ) ^ 14 / 2 ^ j ≤ 1 / 2 ^ 14 :=
    ht.eventually (ge_mem_nhds (by positivity))
  obtain ⟨J1, hJ1⟩ := eventually_atTop.mp hev
  refine ⟨max J1 4, le_max_right _ _, fun j hj => ?_⟩
  have h1 := hJ1 j (le_of_max_le_left hj)
  have hj4 : 4 ≤ j := le_of_max_le_right hj
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul] at h1
  have h2 : ((j : ℝ) + 3) ^ 14 ≤ (2 * j) ^ 14 := by
    have : (4 : ℝ) ≤ j := by exact_mod_cast hj4
    exact pow_le_pow_left₀ (by positivity) (by linarith) 14
  have h3 : ((j : ℝ) + 3) ^ 14 ≤ 2 ^ j := by
    calc ((j : ℝ) + 3) ^ 14 ≤ (2 * j) ^ 14 := h2
      _ = 2 ^ 14 * (j : ℝ) ^ 14 := by ring
      _ ≤ 2 ^ j := by linarith
  exact_mod_cast h3

/-- **The finite-size threshold.** Above `N₀`, `L(N)^7 ≤ ⌊√N⌋`. -/
theorem exists_logL7_threshold :
    ∃ N0 : ℕ, 16 ≤ N0 ∧ ∀ N, N0 ≤ N → logL N ^ 7 ≤ Nat.sqrt N := by
  obtain ⟨J, hJ4, hJ⟩ := eventually_pow14_le_two_pow
  refine ⟨2 ^ J, ?_, fun N hN => ?_⟩
  · calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ4
  have hN0 : N ≠ 0 := by have : 0 < 2 ^ J := by positivity
                         omega
  set j := Nat.log 2 N
  have hjJ : J ≤ j := Nat.le_log_of_pow_le one_lt_two hN
  have hpow : 2 ^ j ≤ N := Nat.pow_log_le_self 2 hN0
  have hlt : N < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self one_lt_two N
  have hL : logL N ≤ j + 2 := by
    unfold logL
    refine max_le (by omega) ?_
    rw [Nat.clog_le_iff_le_pow one_lt_two, pow_succ]
    omega
  have hs : (j + 3) ^ 7 ≤ Nat.sqrt N := by
    have h1 : (j + 3) ^ 14 ≤ N := (hJ j hjJ).trans hpow
    have h2 := Nat.lt_succ_sqrt N
    have h3 : (j + 3) ^ 7 * (j + 3) ^ 7 < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := by
      rw [← pow_add]; exact lt_of_le_of_lt h1 h2
    have h4 : (j + 3) ^ 7 < Nat.sqrt N + 1 := by
      by_contra hc; push Not at hc
      exact absurd h3 (not_lt.mpr (Nat.mul_le_mul hc hc))
    omega
  calc logL N ^ 7 ≤ (j + 2) ^ 7 := Nat.pow_le_pow_left hL 7
    _ ≤ (j + 3) ^ 7 := Nat.pow_le_pow_left (by omega) 7
    _ ≤ Nat.sqrt N := hs

/-! ## The tuned center parameter -/

/-- `kLog7 N = max 2 ⌈⌊√N⌋ / L(N)^6⌉`. -/
noncomputable def kLog7 (N : ℕ) : ℕ :=
  max 2 ⌈(Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 6⌉₊

theorem two_le_kLog7 (N : ℕ) : 2 ≤ kLog7 N := le_max_left _ _

theorem sqrt_div_le_kLog7 (N : ℕ) : (Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 6 ≤ kLog7 N :=
  (Nat.le_ceil _).trans (by
    have : ⌈(Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 6⌉₊ ≤ kLog7 N := le_max_right _ _
    exact_mod_cast this)

theorem kLog7_le_sqrt {N : ℕ} (h2 : 2 ≤ Nat.sqrt N) : kLog7 N ≤ Nat.sqrt N := by
  unfold kLog7
  refine max_le h2 ?_
  rw [Nat.ceil_le]
  have hL : (1 : ℝ) ≤ (logL N : ℝ) ^ 6 := one_le_pow₀ (by exact_mod_cast one_le_logL' N)
  exact div_le_self (Nat.cast_nonneg _) hL

theorem kLog7_le_two_mul {N : ℕ} (h7 : logL N ^ 7 ≤ Nat.sqrt N) :
    (kLog7 N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 6 := by
  have hL1 : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hL6 : (0 : ℝ) < (logL N : ℝ) ^ 6 := by positivity
  have hx : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 6 := by
    rw [le_div_iff₀ hL6, one_mul]
    have h67 : (logL N : ℝ) ^ 6 ≤ (logL N : ℝ) ^ 7 := pow_le_pow_right₀ hL1 (by norm_num)
    have : ((logL N ^ 7 : ℕ) : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast h7
    push_cast at this; linarith
  unfold kLog7
  push_cast
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 6 by positivity)
  rw [mul_div_assoc]
  refine max_le (by linarith) (by linarith)

end DetMinCut
end CutQueryComplexity
