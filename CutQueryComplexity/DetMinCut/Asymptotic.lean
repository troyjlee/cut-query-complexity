import CutQueryComplexity.DetMinCut.Main
import CutQueryComplexity.DetMinCut.Parameters

/-! # The conditional bound is `Õ(n^{3/2})` (Theorem 1)

Write `L(n) = max 1 ⌈log₂ 2n⌉`, which is `⌈log₂ 2n⌉` for `n ≥ 1`. If the hierarchy
distortion and height are polylogarithmic,
`a(r) ≤ A₀ L(r)^p` and `h(r) ≤ H₀ L(r)`, then the budget of the conditional deterministic
algorithm is at most `C · n · (⌊√n⌋ + 1) · L(n)^(4p + 8)` for a constant `C` depending only on
`A₀`, `H₀` and `p` (`detBudget_le`). With `⌊√n⌋ + 1 ≤ 2√n` this is `O(n^{3/2} log^{4p+8} n)`.

The proof bounds every term of one phase on `N ≤ n` classes with `k = ⌊√N⌋ + 1`:
residual preparation `O(n q L²)`, center selection `O(n q L³)`, the quotient `O(n L²)`, and
the certification `O(n q L a⁴ ρ⁴)` with `q = ⌊√n⌋ + 1`, `a ≤ A₀ (3L)^p` and `ρ = O(L)`.
-/

namespace CutQueryComplexity
namespace DetMinCut

open Discovery Hierarchy Finset

/-- `N / (⌊√N⌋ + 1) < ⌊√N⌋ + 1`. -/
theorem div_kOf_le {N n : ℕ} (hN : N ≤ n) : (N : ℝ) / kOf N ≤ Nat.sqrt n + 1 := by
  have hk : (0 : ℝ) < kOf N := by unfold kOf; positivity
  rw [div_le_iff₀ hk]
  have h1 : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  have h2 : Nat.sqrt N ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hN
  have h3 : N ≤ (Nat.sqrt n + 1) * kOf N := by
    unfold kOf; nlinarith
  exact_mod_cast h3

theorem kOf_le {N n : ℕ} (hN : N ≤ n) : kOf N ≤ Nat.sqrt n + 1 := by
  unfold kOf; have := Nat.sqrt_le_sqrt hN; omega

/-- `|C| ≤ 8 q L + 1`. -/
theorem selectionBudget_le {N n : ℕ} (hN : N ≤ n) :
    (selectionBudget N (kOf N) : ℝ) ≤ 8 * (Nat.sqrt n + 1) * logL n + 1 := by
  unfold selectionBudget
  have hk : (0 : ℝ) < kOf N := by unfold kOf; positivity
  have hlog0 : 0 ≤ Real.log (2 * N) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    · have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hpos
      exact Real.log_nonneg (by linarith)
  have h1 : 8 * (N : ℝ) / kOf N * Real.log (2 * N) ≤ 8 * (Nat.sqrt n + 1) * logL n := by
    rw [mul_div_assoc]
    have := div_kOf_le hN
    have := realLog_le_logL hN
    have : (0 : ℝ) ≤ N / kOf N := by positivity
    calc 8 * ((N : ℝ) / kOf N) * Real.log (2 * N)
        ≤ 8 * ((Nat.sqrt n : ℝ) + 1) * Real.log (2 * N) := by gcongr
      _ ≤ 8 * ((Nat.sqrt n : ℝ) + 1) * logL n := by gcongr
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ 8 * (N : ℝ) / kOf N * Real.log (2 * N) by positivity)
  linarith

section Bound

/-- The arithmetic of one phase, with every quantity abstracted to a real number. -/
theorem phase_algebra {n q L a' ρ' N K cN cN1 lN Nm1 s aN a3 ρ γ : ℝ}
    (hn : 1 ≤ n) (hq : 1 ≤ q) (hq2 : q ^ 2 ≤ 4 * n) (hL : 1 ≤ L) (ha' : 1 ≤ a') (hρ' : 1 ≤ ρ')
    (_hN0 : 0 ≤ N) (hN : N ≤ n) (hK0 : 0 ≤ K) (hK : K ≤ q) (hcN0 : 0 ≤ cN) (hcN : cN ≤ L)
    (hcN10 : 0 ≤ cN1) (hcN1 : cN1 ≤ L) (hlN0 : 0 ≤ lN) (hlN : lN ≤ L) (hNm10 : 0 ≤ Nm1)
    (hNm1 : Nm1 ≤ n) (hs0 : 0 ≤ s) (hs : s ≤ 9 * q * L) (haN1 : 1 ≤ aN) (haN : aN ≤ a')
    (ha31 : 1 ≤ a3) (ha3 : a3 ≤ a') (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ ρ') (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hinvγ : 1 / γ ≤ 100 * a' ^ 2 * ρ' ^ 2) :
    N * (4 + 3 * cN) * (4 * K * cN1) + s * (6 * (6 + 3 * cN) * (cN + 1) + Nm1) +
        (2 * (s + 1) + 2 * (s + 1) * (2 * (s + 1))) +
      ((6 * N + 3) * (γ * (2 * a3 * ((1 + aN) * (2 * K + 1))) + 2) +
        (6 * N + 3) * (lN + 3) * (16 + 800 * ρ ^ 2) * (2 * a3 * ((1 + aN) * (2 * K + 1))) / γ + 1)
      ≤ 35255536 * n * q * L ^ 3 * a' ^ 4 * ρ' ^ 4 := by
  have hL2 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by norm_num)
  have hL21 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have t1 : N * (4 + 3 * cN) * (4 * K * cN1) ≤ 28 * n * q * L ^ 3 := by
    calc _ ≤ n * (4 + 3 * L) * (4 * q * L) := by gcongr
      _ ≤ n * (7 * L) * (4 * q * L) := by gcongr; linarith
      _ = 28 * n * q * L ^ 2 := by ring
      _ ≤ 28 * n * q * L ^ 3 := by gcongr
  have t2 : s * (6 * (6 + 3 * cN) * (cN + 1) + Nm1) ≤ 981 * n * q * L ^ 3 := by
    have hnL : n ≤ n * L ^ 2 := le_mul_of_one_le_right (by linarith) hL21
    have h108 : 6 * (6 + 3 * L) * (L + 1) ≤ 108 * L ^ 2 := by nlinarith
    have h108n : 108 * L ^ 2 ≤ 108 * (n * L ^ 2) := by nlinarith
    calc _ ≤ (9 * q * L) * (6 * (6 + 3 * L) * (L + 1) + n) := by gcongr
      _ ≤ (9 * q * L) * (109 * n * L ^ 2) := by gcongr; linarith
      _ = 981 * n * q * L ^ 3 := by ring
  have t3 : 2 * (s + 1) + 2 * (s + 1) * (2 * (s + 1)) ≤ 3200 * n * q * L ^ 3 := by
    have hqL : 1 ≤ q * L := one_le_mul_of_one_le_of_one_le hq hL
    have hp : 2 * (s + 1) ≤ 20 * q * L := by linarith
    have hp0 : 0 ≤ 2 * (s + 1) := by positivity
    have hp1 : 1 ≤ 2 * (s + 1) := by linarith
    have hpp : 2 * (s + 1) ≤ 2 * (s + 1) * (2 * (s + 1)) := le_mul_of_one_le_right hp0 hp1
    have hsq : 2 * (s + 1) * (2 * (s + 1)) ≤ (20 * q * L) * (20 * q * L) :=
      mul_le_mul hp hp hp0 (by positivity)
    have hnq : n * L ^ 2 ≤ n * q * L ^ 3 := by
      calc n * L ^ 2 ≤ n * 1 * L ^ 3 := by rw [mul_one]; gcongr
        _ ≤ n * q * L ^ 3 := by gcongr
    calc _ ≤ 2 * ((20 * q * L) * (20 * q * L)) := by linarith
      _ = 800 * q ^ 2 * L ^ 2 := by ring
      _ ≤ 800 * (4 * n) * L ^ 2 := by gcongr
      _ = 3200 * (n * L ^ 2) := by ring
      _ ≤ 3200 * (n * q * L ^ 3) := by gcongr
      _ = 3200 * n * q * L ^ 3 := by ring
  set Bs := 2 * a3 * ((1 + aN) * (2 * K + 1))
  have hBs0 : 0 ≤ Bs := by positivity
  have hBs : Bs ≤ 12 * a' ^ 2 * q := by
    calc Bs ≤ 2 * a' * ((1 + a') * (2 * q + 1)) := by
          show 2 * a3 * ((1 + aN) * (2 * K + 1)) ≤ _; gcongr
      _ ≤ 2 * a' * ((2 * a') * (3 * q)) := by gcongr <;> linarith
      _ = 12 * a' ^ 2 * q := by ring
  have hN9 : 6 * N + 3 ≤ 9 * n := by linarith
  have t4 : (6 * N + 3) * (γ * Bs + 2) ≤ 126 * n * q * a' ^ 2 := by
    have h1 : 1 ≤ a' ^ 2 * q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ha') hq
    have hγB : γ * Bs ≤ 12 * a' ^ 2 * q := by
      calc γ * Bs ≤ 1 * Bs := by gcongr
        _ ≤ 12 * a' ^ 2 * q := by linarith
    calc _ ≤ (9 * n) * (14 * a' ^ 2 * q) := by
          apply mul_le_mul hN9 (by linarith) (by positivity) (by linarith)
      _ = 126 * n * q * a' ^ 2 := by ring
  have t5 : (6 * N + 3) * (lN + 3) * (16 + 800 * ρ ^ 2) * Bs / γ ≤
      35251200 * n * q * L * a' ^ 4 * ρ' ^ 4 := by
    have hρsq : 16 + 800 * ρ ^ 2 ≤ 816 * ρ' ^ 2 := by
      have : ρ ^ 2 ≤ ρ' ^ 2 := pow_le_pow_left₀ (by linarith) hρ 2
      have : 1 ≤ ρ' ^ 2 := one_le_pow₀ hρ'
      linarith
    rw [div_eq_mul_one_div]
    calc _ ≤ (9 * n) * (4 * L) * (816 * ρ' ^ 2) * (12 * a' ^ 2 * q) *
          (100 * a' ^ 2 * ρ' ^ 2) := by
          gcongr
          linarith
      _ = 35251200 * n * q * L * a' ^ 4 * ρ' ^ 4 := by ring
  -- every term is at most a constant times `X = n q L³ a'⁴ ρ'⁴`
  have ha41 : 1 ≤ a' ^ 4 := one_le_pow₀ ha'
  have hρ4 : 1 ≤ ρ' ^ 4 := one_le_pow₀ hρ'
  have hnq : 1 ≤ n * q := one_le_mul_of_one_le_of_one_le hn hq
  have hY : 1 ≤ L ^ 3 * a' ^ 4 * ρ' ^ 4 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hL3 ha41) hρ4
  have hnq0 : 0 ≤ n * q := by linarith
  have e1 : n * q * L ^ 3 ≤ n * q * (L ^ 3 * a' ^ 4 * ρ' ^ 4) := by
    have : L ^ 3 ≤ L ^ 3 * a' ^ 4 * ρ' ^ 4 := by
      have h1 : L ^ 3 ≤ L ^ 3 * a' ^ 4 := le_mul_of_one_le_right (by positivity) ha41
      exact h1.trans (le_mul_of_one_le_right (by positivity) hρ4)
    gcongr
  have e2 : n * q * a' ^ 2 ≤ n * q * (L ^ 3 * a' ^ 4 * ρ' ^ 4) := by
    have : a' ^ 2 ≤ L ^ 3 * a' ^ 4 * ρ' ^ 4 := by
      calc a' ^ 2 ≤ a' ^ 4 := pow_le_pow_right₀ ha' (by norm_num)
        _ ≤ L ^ 3 * a' ^ 4 := le_mul_of_one_le_left (by positivity) hL3
        _ ≤ L ^ 3 * a' ^ 4 * ρ' ^ 4 := le_mul_of_one_le_right (by positivity) hρ4
    gcongr
  have e3 : n * q * L * a' ^ 4 * ρ' ^ 4 ≤ n * q * (L ^ 3 * a' ^ 4 * ρ' ^ 4) := by
    have hLL : L ≤ L ^ 3 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 3 := pow_le_pow_right₀ hL (by norm_num)
    have : n * q * L * a' ^ 4 * ρ' ^ 4 = n * q * (L * a' ^ 4 * ρ' ^ 4) := by ring
    rw [this]; gcongr
  have e4 : 1 ≤ n * q * (L ^ 3 * a' ^ 4 * ρ' ^ 4) := one_le_mul_of_one_le_of_one_le hnq hY
  have e5 : 28 * n * q * L ^ 3 + 981 * n * q * L ^ 3 + 3200 * n * q * L ^ 3 =
      4209 * (n * q * L ^ 3) := by ring
  have e6 : 35251200 * n * q * L * a' ^ 4 * ρ' ^ 4 = 35251200 * (n * q * L * a' ^ 4 * ρ' ^ 4) := by
    ring
  have e7 : 126 * n * q * a' ^ 2 = 126 * (n * q * a' ^ 2) := by ring
  have e8 : 35255536 * n * q * L ^ 3 * a' ^ 4 * ρ' ^ 4 =
      35255536 * (n * q * (L ^ 3 * a' ^ 4 * ρ' ^ 4)) := by ring
  rw [e8]
  linarith

variable {a : ℕ → ℝ} {h : ℕ → ℕ}

/-- **One phase is `O(n q L³ a'⁴ ρ'⁴)`** for `N ≤ n`, with `q = ⌊√n⌋ + 1`,
`a' = A₀ (3L)^p` and `ρ' = (1 + 6H₀) L`. -/
theorem phaseBound_le (ha : ∀ r, 1 ≤ a r) {A0 H0 : ℝ} {p : ℕ}
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ p) (hH : ∀ r, (h r : ℝ) ≤ H0 * logL r)
    (hH0 : 0 ≤ H0) {N n : ℕ} (hN : N ≤ n) (hn : 1 ≤ n) :
    phaseBound a h N (kOf N) ≤
      35255536 * n * (Nat.sqrt n + 1) * (logL n : ℝ) ^ 3 *
        (A0 * (3 * logL n) ^ p) ^ 4 * ((1 + 6 * H0) * logL n) ^ 4 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL hn
  have hq : (1 : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ Nat.sqrt n)]
  have hq2 : ((Nat.sqrt n : ℝ) + 1) ^ 2 ≤ 4 * n := by
    have h1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have h3 : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ 4 * n := by nlinarith
    have : (((Nat.sqrt n + 1) * (Nat.sqrt n + 1) : ℕ) : ℝ) ≤ ((4 * n : ℕ) : ℝ) := by
      exact_mod_cast h3
    push_cast at this; nlinarith
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hN
  have hK : (kOf N : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by exact_mod_cast kOf_le hN
  have hcN : (Nat.clog 2 N : ℝ) ≤ logL n := by exact_mod_cast clog_le_logL hN
  have hcN1 : (Nat.clog 2 (N - 1) : ℝ) ≤ logL n := by exact_mod_cast clog_pred_le_logL hN
  have hlogN : (Nat.log 2 N : ℝ) ≤ logL n := by exact_mod_cast log_le_logL hN
  have hNm1 : ((N - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show N - 1 ≤ n by omega)
  have hsel := selectionBudget_le hN
  have hsel' : (selectionBudget N (kOf N) : ℝ) ≤ 9 * ((Nat.sqrt n : ℝ) + 1) * logL n := by
    have : 1 ≤ ((Nat.sqrt n : ℝ) + 1) * logL n := one_le_mul_of_one_le_of_one_le hq hL
    nlinarith
  have hA0 : 1 ≤ A0 := by
    have h1 := ha 0; have h2 := hA 0
    have h0 : logL 0 = 1 := by simp [logL]
    rw [h0, Nat.cast_one, one_pow, mul_one] at h2
    linarith
  have h3L : (1 : ℝ) ≤ 3 * logL n := by linarith
  have ha'1 : 1 ≤ A0 * (3 * (logL n : ℝ)) ^ p :=
    one_le_mul_of_one_le_of_one_le hA0 (one_le_pow₀ h3L)
  have haN : a N ≤ A0 * (3 * (logL n : ℝ)) ^ p := by
    refine (hA N).trans ?_
    have h1 : (logL N : ℝ) ≤ 3 * logL n := by
      have : (logL N : ℝ) ≤ logL n := by exact_mod_cast logL_mono hN
      linarith
    gcongr
  have ha3 : a (3 * N + 1) ≤ A0 * (3 * (logL n : ℝ)) ^ p := by
    refine (hA _).trans ?_
    have : (logL (3 * N + 1) : ℝ) ≤ 3 * logL n := by exact_mod_cast logL_three hN hn
    gcongr
  have hρ'1 : 1 ≤ (1 + 6 * H0) * (logL n : ℝ) := by nlinarith
  have hρ : rhoOf h N ≤ (1 + 6 * H0) * logL n := by
    unfold rhoOf
    have h3 : (h (3 * N + 1) : ℝ) ≤ H0 * (3 * logL n) := by
      refine (hH _).trans ?_
      have : (logL (3 * N + 1) : ℝ) ≤ 3 * logL n := by exact_mod_cast logL_three hN hn
      exact mul_le_mul_of_nonneg_left this hH0
    refine max_le hρ'1 ?_
    nlinarith
  have hρ0 := one_le_rhoOf h N
  have hγ := gammaOf_pos ha h N
  have hγ1 : gammaOf a h N ≤ 1 := by
    unfold gammaOf gammaR
    rw [div_le_one (by have := ha N; positivity)]
    have : 1 ≤ a N ^ 2 := one_le_pow₀ (ha N)
    have : 1 ≤ rhoOf h N ^ 2 := one_le_pow₀ hρ0
    nlinarith
  have hinvγ : 1 / gammaOf a h N ≤
      100 * (A0 * (3 * (logL n : ℝ)) ^ p) ^ 2 * ((1 + 6 * H0) * logL n) ^ 2 := by
    unfold gammaOf gammaR
    rw [one_div_one_div]
    have := ha N
    gcongr
  unfold phaseBound phaseBoundR
  simp only [prepS]
  push_cast
  have key := phase_algebra hn1 hq hq2 hL ha'1 hρ'1 (Nat.cast_nonneg N) hNn (Nat.cast_nonneg _) hK
    (Nat.cast_nonneg _) hcN (Nat.cast_nonneg _) hcN1 (Nat.cast_nonneg _) hlogN
    (Nat.cast_nonneg _) hNm1 (Nat.cast_nonneg _) hsel' (ha N) haN (ha _) ha3 hρ0 hρ hγ hγ1 hinvγ
  exact key

/-- The phase maximum is `O(n q L^(4p+7))`. -/
theorem phaseMax_le (ha : ∀ r, 1 ≤ a r) {A0 H0 : ℝ} {p : ℕ}
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ p) (hH : ∀ r, (h r : ℝ) ≤ H0 * logL r)
    (hH0 : 0 ≤ H0) {n : ℕ} (hn : 1 ≤ n) :
    phaseMax a h n ≤ 35255536 * A0 ^ 4 * 3 ^ (4 * p) * (1 + 6 * H0) ^ 4 *
      (n * (Nat.sqrt n + 1) * (logL n : ℝ) ^ (4 * p + 7)) := by
  unfold phaseMax
  refine sup'_le _ _ fun N hN => ?_
  refine (phaseBound_le ha hA hH hH0 (by simpa [Nat.lt_succ_iff] using mem_range.mp hN) hn).trans
    (le_of_eq ?_)
  ring

/-- **Theorem 1, conditional bound.** With polylogarithmic hierarchy distortion
`a(r) ≤ A₀ L(r)^p` and height `h(r) ≤ H₀ L(r)`, the budget is
`O(n (⌊√n⌋ + 1) L(n)^(4p + 8))`, that is `Õ(n^{3/2})`. -/
theorem detBudget_le (ha : ∀ r, 1 ≤ a r) {A0 H0 : ℝ} {p : ℕ}
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ p) (hH : ∀ r, (h r : ℝ) ≤ H0 * logL r)
    (hH0 : 0 ≤ H0) :
    ∃ C : ℝ, ∀ n, 2 ≤ n →
      (detBudget a h n : ℝ) ≤ C * n * (Nat.sqrt n + 1) * (logL n : ℝ) ^ (4 * p + 8) := by
  set P := 35255536 * A0 ^ 4 * 3 ^ (4 * p) * (1 + 6 * H0) ^ 4 with hP
  have hP0 : 0 ≤ P := by positivity
  refine ⟨2 * P + 2906, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set L : ℝ := (logL n : ℝ) with hLdef
  set q : ℝ := (Nat.sqrt n : ℝ) + 1 with hqdef
  have hL : 1 ≤ L := by simp only [hLdef]; exact_mod_cast one_le_logL (by omega : 1 ≤ n)
  have hq : 1 ≤ q := by simp only [hqdef]; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ Nat.sqrt n)]
  set Z : ℝ := n * q * L ^ (4 * p + 8) with hZ
  have hL1 : 1 ≤ L ^ (4 * p + 7) := one_le_pow₀ hL
  have hZ1 : 1 ≤ Z := by
    simp only [hZ]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hq) (one_le_pow₀ hL)
  have hnZ : (n : ℝ) ≤ Z := by
    simp only [hZ]
    calc (n : ℝ) = n * 1 * 1 := by ring
      _ ≤ n * q * L ^ (4 * p + 8) := by gcongr; exact one_le_pow₀ hL
  have hnLZ : (n : ℝ) * L ≤ Z := by
    simp only [hZ]
    have : L ≤ L ^ (4 * p + 8) := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ (4 * p + 8) := pow_le_pow_right₀ hL (by omega)
    calc (n : ℝ) * L = n * 1 * L := by ring
      _ ≤ n * q * L ^ (4 * p + 8) := by gcongr
  have hnL2Z : (n : ℝ) * L ^ 2 ≤ Z := by
    simp only [hZ]
    have : L ^ 2 ≤ L ^ (4 * p + 8) := pow_le_pow_right₀ hL (by omega)
    calc (n : ℝ) * L ^ 2 = n * 1 * L ^ 2 := by ring
      _ ≤ n * q * L ^ (4 * p + 8) := by gcongr
  -- the parts of the budget
  have hc : (Nat.clog 2 n : ℝ) ≤ L := by simp only [hLdef]; exact_mod_cast clog_le_logL le_rfl
  have hlog : (Nat.log 2 n : ℝ) ≤ L := by simp only [hLdef]; exact_mod_cast log_le_logL le_rfl
  have hPM := phaseMax_le ha hA hH hH0 (n := n) (by omega)
  rw [← hP, ← hqdef, ← hLdef] at hPM
  have hPM0 : 0 ≤ phaseMax a h n := phaseMax_nonneg ha n
  have hlogPM : ((Nat.log 2 n + 1 : ℕ) : ℝ) * phaseMax a h n ≤ 2 * P * Z := by
    push_cast
    have h2L : (Nat.log 2 n : ℝ) + 1 ≤ 2 * L := by linarith
    calc ((Nat.log 2 n : ℝ) + 1) * phaseMax a h n
        ≤ (2 * L) * (P * (n * q * L ^ (4 * p + 7))) := by gcongr
      _ = 2 * P * Z := by simp only [hZ]; ring
  have hsk : (skelBound n : ℝ) ≤ 2900 * Z := by
    unfold skelBound TwoRespecting.coverSize
    push_cast
    have : (5 : ℝ) * ((Nat.clog 2 n : ℝ) + 3) * (72 * n * ((Nat.clog 2 n : ℝ) + 1) + 1) ≤
        5 * (4 * L) * (145 * n * L) := by
      gcongr
      · linarith
      · nlinarith
    nlinarith
  have hcn : ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n ≤ 3 * Z := by
    push_cast
    nlinarith
  have hX0 : (0 : ℝ) ≤ (n : ℝ) + ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n +
      (Nat.log 2 n + 1 : ℕ) * phaseMax a h n + skelBound n := by positivity
  have hceil := Nat.ceil_lt_add_one hX0
  unfold detBudget
  have : (2 * P + 2906) * n * q * L ^ (4 * p + 8) = (2 * P + 2906) * Z := by
    simp only [hZ]; ring
  rw [this]
  nlinarith

/-- **Theorem 1 (T2), conditional on `HierarchyBound`.** If Lemma 21 holds with monotone
polylogarithmic distortion `a(r) ≤ A₀ L(r)^p` (`a ≥ 1`) and monotone height
`h(r) ≤ H₀ L(r)`, there is a constant `C` such that for every `n ≥ 2` one deterministic
cut-query decision tree with at most `C n (⌊√n⌋ + 1) L(n)^(4p + 8)` queries returns a minimum
cut of every nonnegative weighted graph on `n` vertices. -/
theorem deterministic_mincut_upper_of_hierarchyBound (hb : HierarchyBound a h)
    (ha : ∀ r, 1 ≤ a r) (hma : Monotone a) (hh : Monotone h) {A0 H0 : ℝ} {p : ℕ}
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ p) (hH : ∀ r, (h r : ℝ) ≤ H0 * logL r)
    (hH0 : 0 ≤ H0) :
    ∃ C : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∃ q : ℕ, (q : ℝ) ≤ C * Fintype.card V * (Nat.sqrt (Fintype.card V) + 1) *
          (logL (Fintype.card V) : ℝ) ^ (4 * p + 8) ∧
        ∃ D : DTree (Finset V) ℝ (Option (Finset V)) q,
          ∀ G : WeightedGraph V, ∃ S, D.eval G.cut = some S ∧ IsMinCut G S := by
  obtain ⟨C, hC⟩ := detBudget_le ha hA hH hH0
  exact ⟨C, fun V _ _ hn => ⟨_, hC _ hn, deterministic_mincut_of_hierarchyBound hb ha hma hh hn⟩⟩

end Bound

end DetMinCut
end CutQueryComplexity
