import CutQueryComplexity.DetMinCut.Main
import CutQueryComplexity.DetMinCut.Parameters

/-! # Sharp phase bounds with a constant guard (log-seven plan, Milestones 3–4)

With guard quality `ρ₀` and distortion `a(r) ≤ A₀ L(r)³`, one phase on `N` classes with center
parameter `k ≥ 1` costs at most the sum of four separate terms (`phaseBoundR_const_le`):

| Stage | Bound |
| --- | --- |
| residual preparation | `28 N k L²` |
| center selection | `(8NL/k + 1)(108L² + N)` |
| quotient | `2 (2 (8NL/k + 2))²` |
| refinement and completion | `9N(12a'²k + 2) + 35251200 ρ₀⁴ N L a'⁴ k + 1`, `a' = 27 A₀ L³` |

where `L = L(N)`. With `k = kLog7 N` and `L(N)^7 ≤ ⌊√N⌋` every term is `O(N ⌊√N⌋ L(N)^7)`
(`phaseBound_log7`).
-/

namespace CutQueryComplexity
namespace DetMinCut

open Discovery Hierarchy Finset

/-- `|C| ≤ 8 N L / k + 1` for any `k ≥ 1`. -/
theorem selectionBudget_le_gen {N k : ℕ} (hk : 1 ≤ k) :
    (selectionBudget N k : ℝ) ≤ 8 * N * logL N / k + 1 := by
  unfold selectionBudget
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog0 : 0 ≤ Real.log (2 * N) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    · have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hpos
      exact Real.log_nonneg (by linarith)
  have h1 : 8 * (N : ℝ) / k * Real.log (2 * N) ≤ 8 * N * logL N / k := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hk0.le
    have := realLog_le_logL (le_refl N)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ 8 * (N : ℝ) / k * Real.log (2 * N) by positivity)
  linarith

/-- The arithmetic of one phase with constant guard quality, for a general parameter. -/
theorem phase_terms {N K L a' ρ0 cN cN1 lN Nm1 s aN a3 γ : ℝ}
    (hN0 : 0 ≤ N) (hK1 : 1 ≤ K) (hL : 1 ≤ L) (ha' : 1 ≤ a') (hρ0 : 1 ≤ ρ0)
    (hcN0 : 0 ≤ cN) (hcN : cN ≤ L) (hcN10 : 0 ≤ cN1) (hcN1 : cN1 ≤ L) (hlN0 : 0 ≤ lN)
    (hlN : lN ≤ L) (hNm10 : 0 ≤ Nm1) (hNm1 : Nm1 ≤ N) (hs0 : 0 ≤ s)
    (hs : s ≤ 8 * N * L / K + 1) (haN1 : 1 ≤ aN) (haN : aN ≤ a') (ha31 : 1 ≤ a3) (ha3 : a3 ≤ a')
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hinvγ : 1 / γ ≤ 100 * a' ^ 2 * ρ0 ^ 2) :
    N * (4 + 3 * cN) * (4 * K * cN1) + s * (6 * (6 + 3 * cN) * (cN + 1) + Nm1) +
        (2 * (s + 1) + 2 * (s + 1) * (2 * (s + 1))) +
      ((6 * N + 3) * (γ * (2 * a3 * ((1 + aN) * (2 * K + 1))) + 2) +
        (6 * N + 3) * (lN + 3) * (16 + 800 * ρ0 ^ 2) * (2 * a3 * ((1 + aN) * (2 * K + 1))) / γ + 1)
      ≤ 28 * N * K * L ^ 2 + (8 * N * L / K + 1) * (108 * L ^ 2 + N) +
          2 * (2 * (8 * N * L / K + 2)) ^ 2 +
        (9 * (N + 1) * (12 * a' ^ 2 * K + 2) + 35251200 * ρ0 ^ 4 * (N + 1) * L * a' ^ 4 * K + 1) := by
  have hK0 : 0 < K := by linarith
  have hX0 : 0 ≤ 8 * N * L / K := by positivity
  have t1 : N * (4 + 3 * cN) * (4 * K * cN1) ≤ 28 * N * K * L ^ 2 := by
    calc _ ≤ N * (4 + 3 * L) * (4 * K * L) := by gcongr
      _ ≤ N * (7 * L) * (4 * K * L) := by gcongr; linarith
      _ = 28 * N * K * L ^ 2 := by ring
  have t2 : s * (6 * (6 + 3 * cN) * (cN + 1) + Nm1) ≤ (8 * N * L / K + 1) * (108 * L ^ 2 + N) := by
    have h108 : 6 * (6 + 3 * L) * (L + 1) ≤ 108 * L ^ 2 := by nlinarith
    calc _ ≤ (8 * N * L / K + 1) * (6 * (6 + 3 * L) * (L + 1) + N) := by gcongr
      _ ≤ (8 * N * L / K + 1) * (108 * L ^ 2 + N) := by gcongr
  have t3 : 2 * (s + 1) + 2 * (s + 1) * (2 * (s + 1)) ≤ 2 * (2 * (8 * N * L / K + 2)) ^ 2 := by
    have hp : 2 * (s + 1) ≤ 2 * (8 * N * L / K + 2) := by linarith
    have hp0 : 0 ≤ 2 * (s + 1) := by positivity
    have hp1 : 1 ≤ 2 * (s + 1) := by linarith
    have hpp : 2 * (s + 1) ≤ 2 * (s + 1) * (2 * (s + 1)) := le_mul_of_one_le_right hp0 hp1
    have hsq : 2 * (s + 1) * (2 * (s + 1)) ≤ (2 * (8 * N * L / K + 2)) * (2 * (8 * N * L / K + 2)) :=
      mul_le_mul hp hp hp0 (by positivity)
    rw [sq]; linarith
  set Bs := 2 * a3 * ((1 + aN) * (2 * K + 1))
  have hBs0 : 0 ≤ Bs := by positivity
  have hBs : Bs ≤ 12 * a' ^ 2 * K := by
    calc Bs ≤ 2 * a' * ((1 + a') * (2 * K + 1)) := by
          show 2 * a3 * ((1 + aN) * (2 * K + 1)) ≤ _; gcongr
      _ ≤ 2 * a' * ((2 * a') * (3 * K)) := by gcongr <;> linarith
      _ = 12 * a' ^ 2 * K := by ring
  have hN9 : 6 * N + 3 ≤ 9 * (N + 1) := by linarith
  have t4 : (6 * N + 3) * (γ * Bs + 2) ≤ 9 * (N + 1) * (12 * a' ^ 2 * K + 2) := by
    have hγB : γ * Bs ≤ 12 * a' ^ 2 * K := by
      calc γ * Bs ≤ 1 * Bs := by gcongr
        _ ≤ 12 * a' ^ 2 * K := by linarith
    apply mul_le_mul hN9 (by linarith) (by positivity) (by positivity)
  have t5 : (6 * N + 3) * (lN + 3) * (16 + 800 * ρ0 ^ 2) * Bs / γ ≤
      35251200 * ρ0 ^ 4 * (N + 1) * L * a' ^ 4 * K := by
    have hρsq : 16 + 800 * ρ0 ^ 2 ≤ 816 * ρ0 ^ 2 := by
      have : 1 ≤ ρ0 ^ 2 := one_le_pow₀ hρ0
      linarith
    rw [div_eq_mul_one_div]
    calc _ ≤ (9 * (N + 1)) * (4 * L) * (816 * ρ0 ^ 2) * (12 * a' ^ 2 * K) *
          (100 * a' ^ 2 * ρ0 ^ 2) := by
          gcongr
          linarith
      _ = 35251200 * ρ0 ^ 4 * (N + 1) * L * a' ^ 4 * K := by ring
  linarith

variable {a : ℕ → ℝ}

/-- **Milestone 3: one phase with constant guard quality, for a general parameter `k ≥ 1`.** -/
theorem phaseBoundR_const_le (ha : ∀ r, 1 ≤ a r) {A0 ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ 3) {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    phaseBoundR a (fun _ => ρ0) N k ≤
      28 * N * k * (logL N : ℝ) ^ 2 +
        (8 * N * logL N / k + 1) * (108 * (logL N : ℝ) ^ 2 + N) +
        2 * (2 * (8 * N * logL N / k + 2)) ^ 2 +
      (9 * (N + 1) * (12 * (27 * A0 * (logL N : ℝ) ^ 3) ^ 2 * k + 2) +
        35251200 * ρ0 ^ 4 * (N + 1) * logL N * (27 * A0 * (logL N : ℝ) ^ 3) ^ 4 * k + 1) := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcN : (Nat.clog 2 N : ℝ) ≤ logL N := by exact_mod_cast clog_le_logL (le_refl N)
  have hcN1 : (Nat.clog 2 (N - 1) : ℝ) ≤ logL N := by
    exact_mod_cast clog_pred_le_logL (le_refl N)
  have hlogN : (Nat.log 2 N : ℝ) ≤ logL N := by exact_mod_cast log_le_logL (le_refl N)
  have hNm1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N - 1 ≤ N by omega)
  have hsel := selectionBudget_le_gen (N := N) hk
  have hA0 : 1 ≤ A0 := by
    have h1 := ha 0; have h2 := hA 0
    have h0 : logL 0 = 1 := by simp [logL]
    rw [h0, Nat.cast_one, one_pow, mul_one] at h2
    linarith
  have ha'1 : 1 ≤ 27 * A0 * (logL N : ℝ) ^ 3 := by
    have : 1 ≤ (logL N : ℝ) ^ 3 := one_le_pow₀ hL
    nlinarith
  have haN : a N ≤ 27 * A0 * (logL N : ℝ) ^ 3 := by
    refine (hA N).trans ?_
    have : 0 ≤ A0 * (logL N : ℝ) ^ 3 := by positivity
    linarith
  have ha3 : a (3 * N + 1) ≤ 27 * A0 * (logL N : ℝ) ^ 3 := by
    refine (hA _).trans ?_
    have h3 : (logL (3 * N + 1) : ℝ) ≤ 3 * logL N := by exact_mod_cast logL_three (le_refl N) hN
    calc A0 * (logL (3 * N + 1) : ℝ) ^ 3 ≤ A0 * (3 * logL N) ^ 3 := by gcongr
      _ = 27 * A0 * (logL N : ℝ) ^ 3 := by ring
  have hρf : ∀ M : ℕ, 1 ≤ (fun _ : ℕ => ρ0) M := fun _ => hρ0
  have hγ := gammaR_pos ha hρf N
  have hγ1 : gammaR a (fun _ => ρ0) N ≤ 1 := by
    unfold gammaR
    rw [div_le_one (by have := ha N; positivity)]
    have : 1 ≤ a N ^ 2 := one_le_pow₀ (ha N)
    have : 1 ≤ ρ0 ^ 2 := one_le_pow₀ hρ0
    nlinarith
  have hinvγ : 1 / gammaR a (fun _ => ρ0) N ≤
      100 * (27 * A0 * (logL N : ℝ) ^ 3) ^ 2 * ρ0 ^ 2 := by
    unfold gammaR
    rw [one_div_one_div]
    have := ha N
    gcongr
  unfold phaseBoundR
  simp only [prepS]
  push_cast
  exact phase_terms (Nat.cast_nonneg N) hk1 hL ha'1 hρ0 (Nat.cast_nonneg _) hcN (Nat.cast_nonneg _)
    hcN1 (Nat.cast_nonneg _) hlogN (Nat.cast_nonneg _) hNm1 (Nat.cast_nonneg _) hsel (ha N) haN
    (ha _) ha3 hγ hγ1 hinvγ

/-- The log-seven phase constant. -/
noncomputable def cLog7 (A0 ρ0 : ℝ) : ℝ :=
  12903 + 18 * (17496 * A0 ^ 2 + 2) + 4 * 35251200 * 531441 * (A0 ^ 4 * ρ0 ^ 4)

/-- The arithmetic of the tuned parameter, with every quantity abstracted to a real number. -/
theorem log7_algebra {N s L k A0 ρ0 : ℝ} (hs4 : 4 ≤ s) (hsN : s ^ 2 ≤ N) (hNs : N ≤ 4 * s ^ 2)
    (hL : 1 ≤ L) (hL7 : L ^ 7 ≤ s) (hklo : s ≤ k * L ^ 6) (hkhi : k * L ^ 6 ≤ 2 * s)
    (hk1 : 1 ≤ k) (hA0 : 1 ≤ A0) (hρ0 : 1 ≤ ρ0) :
    28 * N * k * L ^ 2 + (8 * N * L / k + 1) * (108 * L ^ 2 + N) +
        2 * (2 * (8 * N * L / k + 2)) ^ 2 +
      (9 * (N + 1) * (12 * (27 * A0 * L ^ 3) ^ 2 * k + 2) +
        35251200 * ρ0 ^ 4 * (N + 1) * L * (27 * A0 * L ^ 3) ^ 4 * k + 1)
      ≤ cLog7 A0 ρ0 * (N * s * L ^ 7) := by
  have hk0 : 0 < k := by linarith
  have hs0 : 0 < s := by linarith
  have hN1 : 16 ≤ N := by nlinarith
  have hL7' : 1 ≤ L ^ 7 := one_le_pow₀ hL
  have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ hL
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hX : 1 ≤ N * s * L ^ 7 := by
    have : 1 ≤ N * s := by nlinarith
    nlinarith
  have hsL : s * L ^ 7 ≤ N := by nlinarith
  have hL2N : L ^ 2 ≤ N := by
    have h14 : L ^ 2 ≤ L ^ 14 := pow_le_pow_right₀ hL (by norm_num)
    have : L ^ 14 ≤ s ^ 2 := by
      calc L ^ 14 = (L ^ 7) ^ 2 := by ring
        _ ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hL7 2
    linarith
  -- `8 N L / k ≤ 32 s L^7`
  have hNk : 8 * N * L / k ≤ 32 * s * L ^ 7 := by
    rw [div_le_iff₀ hk0]
    have h1 : N ≤ 4 * s * (k * L ^ 6) := by nlinarith
    have h2 : 8 * N * L ≤ 8 * (4 * s * (k * L ^ 6)) * L := by nlinarith
    calc 8 * N * L ≤ 8 * (4 * s * (k * L ^ 6)) * L := h2
      _ = 32 * s * L ^ 7 * k := by ring
  have hNk0 : 0 ≤ 8 * N * L / k := by positivity
  -- the four terms
  have t1 : 28 * N * k * L ^ 2 ≤ 56 * (N * s * L ^ 7) := by
    have h1 : k * L ^ 2 ≤ k * L ^ 6 := by
      have : L ^ 2 ≤ L ^ 6 := pow_le_pow_right₀ hL (by norm_num)
      exact mul_le_mul_of_nonneg_left this hk0.le
    have h2 : k * L ^ 2 ≤ 2 * s * L ^ 7 := by nlinarith
    calc 28 * N * k * L ^ 2 = 28 * N * (k * L ^ 2) := by ring
      _ ≤ 28 * N * (2 * s * L ^ 7) := by gcongr
      _ = 56 * (N * s * L ^ 7) := by ring
  have t2 : (8 * N * L / k + 1) * (108 * L ^ 2 + N) ≤ 3597 * (N * s * L ^ 7) := by
    have h1 : 8 * N * L / k + 1 ≤ 33 * s * L ^ 7 := by nlinarith
    have h2 : 108 * L ^ 2 + N ≤ 109 * N := by linarith
    calc _ ≤ (33 * s * L ^ 7) * (109 * N) := by gcongr
      _ = 3597 * (N * s * L ^ 7) := by ring
  have t3 : 2 * (2 * (8 * N * L / k + 2)) ^ 2 ≤ 9248 * (N * s * L ^ 7) := by
    have h1 : 2 * (8 * N * L / k + 2) ≤ 68 * (s * L ^ 7) := by nlinarith
    have h0 : 0 ≤ 2 * (8 * N * L / k + 2) := by positivity
    have h2 : (2 * (8 * N * L / k + 2)) ^ 2 ≤ (68 * (s * L ^ 7)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have h3 : (s * L ^ 7) * (s * L ^ 7) ≤ N * (s * L ^ 7) :=
      mul_le_mul_of_nonneg_right hsL (by positivity)
    calc _ ≤ 2 * (68 * (s * L ^ 7)) ^ 2 := by linarith
      _ = 9248 * ((s * L ^ 7) * (s * L ^ 7)) := by ring
      _ ≤ 9248 * (N * (s * L ^ 7)) := by gcongr
      _ = 9248 * (N * s * L ^ 7) := by ring
  have t4 : 9 * (N + 1) * (12 * (27 * A0 * L ^ 3) ^ 2 * k + 2) ≤
      18 * (17496 * A0 ^ 2 + 2) * (N * s * L ^ 7) := by
    have h1 : (27 * A0 * L ^ 3) ^ 2 * k ≤ 1458 * A0 ^ 2 * s := by
      calc (27 * A0 * L ^ 3) ^ 2 * k = 729 * A0 ^ 2 * (k * L ^ 6) := by ring
        _ ≤ 729 * A0 ^ 2 * (2 * s) := by gcongr
        _ = 1458 * A0 ^ 2 * s := by ring
    have h2 : 12 * (27 * A0 * L ^ 3) ^ 2 * k + 2 ≤ (17496 * A0 ^ 2 + 2) * s := by nlinarith
    have h3 : N + 1 ≤ 2 * N := by linarith
    have h4 : s ≤ s * L ^ 7 := le_mul_of_one_le_right hs0.le hL7'
    calc _ ≤ 9 * (2 * N) * ((17496 * A0 ^ 2 + 2) * s) := by gcongr
      _ = 18 * (17496 * A0 ^ 2 + 2) * (N * s) := by ring
      _ ≤ 18 * (17496 * A0 ^ 2 + 2) * (N * s * L ^ 7) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hL7') (by positivity)
  have t5 : 35251200 * ρ0 ^ 4 * (N + 1) * L * (27 * A0 * L ^ 3) ^ 4 * k ≤
      4 * 35251200 * 531441 * (A0 ^ 4 * ρ0 ^ 4) * (N * s * L ^ 7) := by
    have h1 : L * (27 * A0 * L ^ 3) ^ 4 * k = 531441 * A0 ^ 4 * (L ^ 7 * (k * L ^ 6)) := by ring
    have h2 : L ^ 7 * (k * L ^ 6) ≤ L ^ 7 * (2 * s) := by gcongr
    have h3 : N + 1 ≤ 2 * N := by linarith
    calc 35251200 * ρ0 ^ 4 * (N + 1) * L * (27 * A0 * L ^ 3) ^ 4 * k
        = 35251200 * ρ0 ^ 4 * (N + 1) * (L * (27 * A0 * L ^ 3) ^ 4 * k) := by ring
      _ = 35251200 * ρ0 ^ 4 * (N + 1) * (531441 * A0 ^ 4 * (L ^ 7 * (k * L ^ 6))) := by rw [h1]
      _ ≤ 35251200 * ρ0 ^ 4 * (2 * N) * (531441 * A0 ^ 4 * (L ^ 7 * (2 * s))) := by gcongr
      _ = 4 * 35251200 * 531441 * (A0 ^ 4 * ρ0 ^ 4) * (N * s * L ^ 7) := by ring
  unfold cLog7
  nlinarith

variable {a : ℕ → ℝ}

/-- **Milestone 4: a tuned phase above the threshold costs `O(N ⌊√N⌋ L(N)^7)`.** -/
theorem phaseBound_log7 (ha : ∀ r, 1 ≤ a r) {A0 ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ 3) {N : ℕ} (h16 : 16 ≤ N)
    (h7 : logL N ^ 7 ≤ Nat.sqrt N) :
    phaseBoundR a (fun _ => ρ0) N (kLog7 N) ≤
      cLog7 A0 ρ0 * (N * Nat.sqrt N * (logL N : ℝ) ^ 7) := by
  have hA0 : 1 ≤ A0 := by
    have h1 := ha 0; have h2 := hA 0
    have h0 : logL 0 = 1 := by simp [logL]
    rw [h0, Nat.cast_one, one_pow, mul_one] at h2
    linarith
  have hk1 : 1 ≤ kLog7 N := le_trans (by norm_num) (two_le_kLog7 N)
  refine (phaseBoundR_const_le ha hρ0 hA (by omega) hk1).trans ?_
  have hs4 : 4 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hL6 : (0 : ℝ) < (logL N : ℝ) ^ 6 := by positivity
  have hklo : (Nat.sqrt N : ℝ) ≤ kLog7 N * (logL N : ℝ) ^ 6 := by
    have := sqrt_div_le_kLog7 N
    rwa [div_le_iff₀ hL6] at this
  have hkhi : (kLog7 N : ℝ) * (logL N : ℝ) ^ 6 ≤ 2 * Nat.sqrt N := by
    have := kLog7_le_two_mul h7
    rwa [le_div_iff₀ hL6] at this
  have hsN : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ N := by
    have := Nat.sqrt_le N
    have : ((Nat.sqrt N * Nat.sqrt N : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    push_cast at this; nlinarith
  have hNs : (N : ℝ) ≤ 4 * ((Nat.sqrt N : ℕ) : ℝ) ^ 2 := by
    have h1 := Nat.lt_succ_sqrt N
    have h2 : N ≤ 4 * (Nat.sqrt N * Nat.sqrt N) := by nlinarith
    have : (N : ℝ) ≤ ((4 * (Nat.sqrt N * Nat.sqrt N) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this; nlinarith
  have hL7 : (logL N : ℝ) ^ 7 ≤ Nat.sqrt N := by exact_mod_cast h7
  exact log7_algebra (by exact_mod_cast hs4) hsN hNs hL hL7 hklo hkhi (by exact_mod_cast hk1) hA0 hρ0

end DetMinCut
end CutQueryComplexity
