import CutQueryComplexity.DetMinCut.Budget
import CutQueryComplexity.DetMinCut.ParametersLog5

/-! # Sharp phase bounds with quadratic distortion (log-five plan, A2)

With guard quality `ρ₀` and distortion `a(r) ≤ A₀ L(r)²`, the generic `phase_terms` applies
with `a' = 9 A₀ L²` (`phaseBoundR_const_sq_le`). With `k = kLog5 N` and `L(N)^5 ≤ ⌊√N⌋`, every
term is `O(N ⌊√N⌋ L(N)^5)` (`log5_algebra`, `phaseBound_log5`).
-/

namespace CutQueryComplexity
namespace DetMinCut

open Discovery Hierarchy Finset

variable {a : ℕ → ℝ}

/-- One phase with constant guard quality and quadratic distortion, for any `k ≥ 1`. -/
theorem phaseBoundR_const_sq_le (ha : ∀ r, 1 ≤ a r) {A0 ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ 2) {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    phaseBoundR a (fun _ => ρ0) N k ≤
      28 * N * k * (logL N : ℝ) ^ 2 +
        (8 * N * logL N / k + 1) * (108 * (logL N : ℝ) ^ 2 + N) +
        2 * (2 * (8 * N * logL N / k + 2)) ^ 2 +
      (9 * (N + 1) * (12 * (9 * A0 * (logL N : ℝ) ^ 2) ^ 2 * k + 2) +
        35251200 * ρ0 ^ 4 * (N + 1) * logL N * (9 * A0 * (logL N : ℝ) ^ 2) ^ 4 * k + 1) := by
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
  have ha'1 : 1 ≤ 9 * A0 * (logL N : ℝ) ^ 2 := by
    have : 1 ≤ (logL N : ℝ) ^ 2 := one_le_pow₀ hL
    nlinarith
  have haN : a N ≤ 9 * A0 * (logL N : ℝ) ^ 2 := by
    refine (hA N).trans ?_
    have : 0 ≤ A0 * (logL N : ℝ) ^ 2 := by positivity
    linarith
  have ha3 : a (3 * N + 1) ≤ 9 * A0 * (logL N : ℝ) ^ 2 := by
    refine (hA _).trans ?_
    have h3 : (logL (3 * N + 1) : ℝ) ≤ 3 * logL N := by exact_mod_cast logL_three (le_refl N) hN
    calc A0 * (logL (3 * N + 1) : ℝ) ^ 2 ≤ A0 * (3 * logL N) ^ 2 := by gcongr
      _ = 9 * A0 * (logL N : ℝ) ^ 2 := by ring
  have hρf : ∀ M : ℕ, 1 ≤ (fun _ : ℕ => ρ0) M := fun _ => hρ0
  have hγ := gammaR_pos ha hρf N
  have hγ1 : gammaR a (fun _ => ρ0) N ≤ 1 := by
    unfold gammaR
    rw [div_le_one (by have := ha N; positivity)]
    have : 1 ≤ a N ^ 2 := one_le_pow₀ (ha N)
    have : 1 ≤ ρ0 ^ 2 := one_le_pow₀ hρ0
    nlinarith
  have hinvγ : 1 / gammaR a (fun _ => ρ0) N ≤
      100 * (9 * A0 * (logL N : ℝ) ^ 2) ^ 2 * ρ0 ^ 2 := by
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

/-- The log-five phase constant. -/
noncomputable def cLog5 (A0 ρ0 : ℝ) : ℝ :=
  12903 + 18 * (1944 * A0 ^ 2 + 2) + 4 * 35251200 * 6561 * (A0 ^ 4 * ρ0 ^ 4)

/-- The arithmetic of the tuned parameter, with every quantity abstracted to a real number. -/
theorem log5_algebra {N s L k A0 ρ0 : ℝ} (hs4 : 4 ≤ s) (hsN : s ^ 2 ≤ N) (hNs : N ≤ 4 * s ^ 2)
    (hL : 1 ≤ L) (hL5 : L ^ 5 ≤ s) (hklo : s ≤ k * L ^ 4) (hkhi : k * L ^ 4 ≤ 2 * s)
    (hk1 : 1 ≤ k) (hA0 : 1 ≤ A0) (hρ0 : 1 ≤ ρ0) :
    28 * N * k * L ^ 2 + (8 * N * L / k + 1) * (108 * L ^ 2 + N) +
        2 * (2 * (8 * N * L / k + 2)) ^ 2 +
      (9 * (N + 1) * (12 * (9 * A0 * L ^ 2) ^ 2 * k + 2) +
        35251200 * ρ0 ^ 4 * (N + 1) * L * (9 * A0 * L ^ 2) ^ 4 * k + 1)
      ≤ cLog5 A0 ρ0 * (N * s * L ^ 5) := by
  have hk0 : 0 < k := by linarith
  have hs0 : 0 < s := by linarith
  have hN1 : 16 ≤ N := by nlinarith
  have hL5' : 1 ≤ L ^ 5 := one_le_pow₀ hL
  have hL6 : 1 ≤ L ^ 4 := one_le_pow₀ hL
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hX : 1 ≤ N * s * L ^ 5 := by
    have : 1 ≤ N * s := by nlinarith
    nlinarith
  have hsL : s * L ^ 5 ≤ N := by nlinarith
  have hL2N : L ^ 2 ≤ N := by
    have h14 : L ^ 2 ≤ L ^ 10 := pow_le_pow_right₀ hL (by norm_num)
    have : L ^ 10 ≤ s ^ 2 := by
      calc L ^ 10 = (L ^ 5) ^ 2 := by ring
        _ ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hL5 2
    linarith
  -- `8 N L / k ≤ 32 s L^7`
  have hNk : 8 * N * L / k ≤ 32 * s * L ^ 5 := by
    rw [div_le_iff₀ hk0]
    have h1 : N ≤ 4 * s * (k * L ^ 4) := by nlinarith
    have h2 : 8 * N * L ≤ 8 * (4 * s * (k * L ^ 4)) * L := by nlinarith
    calc 8 * N * L ≤ 8 * (4 * s * (k * L ^ 4)) * L := h2
      _ = 32 * s * L ^ 5 * k := by ring
  have hNk0 : 0 ≤ 8 * N * L / k := by positivity
  -- the four terms
  have t1 : 28 * N * k * L ^ 2 ≤ 56 * (N * s * L ^ 5) := by
    have h1 : k * L ^ 2 ≤ k * L ^ 4 := by
      have : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
      exact mul_le_mul_of_nonneg_left this hk0.le
    have h2 : k * L ^ 2 ≤ 2 * s * L ^ 5 := by nlinarith
    calc 28 * N * k * L ^ 2 = 28 * N * (k * L ^ 2) := by ring
      _ ≤ 28 * N * (2 * s * L ^ 5) := by gcongr
      _ = 56 * (N * s * L ^ 5) := by ring
  have t2 : (8 * N * L / k + 1) * (108 * L ^ 2 + N) ≤ 3597 * (N * s * L ^ 5) := by
    have h1 : 8 * N * L / k + 1 ≤ 33 * s * L ^ 5 := by nlinarith
    have h2 : 108 * L ^ 2 + N ≤ 109 * N := by linarith
    calc _ ≤ (33 * s * L ^ 5) * (109 * N) := by gcongr
      _ = 3597 * (N * s * L ^ 5) := by ring
  have t3 : 2 * (2 * (8 * N * L / k + 2)) ^ 2 ≤ 9248 * (N * s * L ^ 5) := by
    have h1 : 2 * (8 * N * L / k + 2) ≤ 68 * (s * L ^ 5) := by nlinarith
    have h0 : 0 ≤ 2 * (8 * N * L / k + 2) := by positivity
    have h2 : (2 * (8 * N * L / k + 2)) ^ 2 ≤ (68 * (s * L ^ 5)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have h3 : (s * L ^ 5) * (s * L ^ 5) ≤ N * (s * L ^ 5) :=
      mul_le_mul_of_nonneg_right hsL (by positivity)
    calc _ ≤ 2 * (68 * (s * L ^ 5)) ^ 2 := by linarith
      _ = 9248 * ((s * L ^ 5) * (s * L ^ 5)) := by ring
      _ ≤ 9248 * (N * (s * L ^ 5)) := by gcongr
      _ = 9248 * (N * s * L ^ 5) := by ring
  have t4 : 9 * (N + 1) * (12 * (9 * A0 * L ^ 2) ^ 2 * k + 2) ≤
      18 * (1944 * A0 ^ 2 + 2) * (N * s * L ^ 5) := by
    have h1 : (9 * A0 * L ^ 2) ^ 2 * k ≤ 162 * A0 ^ 2 * s := by
      calc (9 * A0 * L ^ 2) ^ 2 * k = 81 * A0 ^ 2 * (k * L ^ 4) := by ring
        _ ≤ 81 * A0 ^ 2 * (2 * s) := by gcongr
        _ = 162 * A0 ^ 2 * s := by ring
    have h2 : 12 * (9 * A0 * L ^ 2) ^ 2 * k + 2 ≤ (1944 * A0 ^ 2 + 2) * s := by nlinarith
    have h3 : N + 1 ≤ 2 * N := by linarith
    have h4 : s ≤ s * L ^ 5 := le_mul_of_one_le_right hs0.le hL5'
    calc _ ≤ 9 * (2 * N) * ((1944 * A0 ^ 2 + 2) * s) := by gcongr
      _ = 18 * (1944 * A0 ^ 2 + 2) * (N * s) := by ring
      _ ≤ 18 * (1944 * A0 ^ 2 + 2) * (N * s * L ^ 5) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hL5') (by positivity)
  have t5 : 35251200 * ρ0 ^ 4 * (N + 1) * L * (9 * A0 * L ^ 2) ^ 4 * k ≤
      4 * 35251200 * 6561 * (A0 ^ 4 * ρ0 ^ 4) * (N * s * L ^ 5) := by
    have h1 : L * (9 * A0 * L ^ 2) ^ 4 * k = 6561 * A0 ^ 4 * (L ^ 5 * (k * L ^ 4)) := by ring
    have h2 : L ^ 5 * (k * L ^ 4) ≤ L ^ 5 * (2 * s) := by gcongr
    have h3 : N + 1 ≤ 2 * N := by linarith
    calc 35251200 * ρ0 ^ 4 * (N + 1) * L * (9 * A0 * L ^ 2) ^ 4 * k
        = 35251200 * ρ0 ^ 4 * (N + 1) * (L * (9 * A0 * L ^ 2) ^ 4 * k) := by ring
      _ = 35251200 * ρ0 ^ 4 * (N + 1) * (6561 * A0 ^ 4 * (L ^ 5 * (k * L ^ 4))) := by rw [h1]
      _ ≤ 35251200 * ρ0 ^ 4 * (2 * N) * (6561 * A0 ^ 4 * (L ^ 5 * (2 * s))) := by gcongr
      _ = 4 * 35251200 * 6561 * (A0 ^ 4 * ρ0 ^ 4) * (N * s * L ^ 5) := by ring
  unfold cLog5
  nlinarith

/-- **A2: a tuned phase above the threshold costs `O(N ⌊√N⌋ L(N)^5)`.** -/
theorem phaseBound_log5 (ha : ∀ r, 1 ≤ a r) {A0 ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) ^ 2) {N : ℕ} (h16 : 16 ≤ N)
    (h5 : logL N ^ 5 ≤ Nat.sqrt N) :
    phaseBoundR a (fun _ => ρ0) N (kLog5 N) ≤
      cLog5 A0 ρ0 * (N * Nat.sqrt N * (logL N : ℝ) ^ 5) := by
  have hA0 : 1 ≤ A0 := by
    have h1 := ha 0; have h2 := hA 0
    have h0 : logL 0 = 1 := by simp [logL]
    rw [h0, Nat.cast_one, one_pow, mul_one] at h2
    linarith
  have hk1 : 1 ≤ kLog5 N := le_trans (by norm_num) (two_le_kLog5 N)
  refine (phaseBoundR_const_sq_le ha hρ0 hA (by omega) hk1).trans ?_
  have hs4 : 4 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hL6 : (0 : ℝ) < (logL N : ℝ) ^ 4 := by positivity
  have hklo : (Nat.sqrt N : ℝ) ≤ kLog5 N * (logL N : ℝ) ^ 4 := by
    have := sqrt_div_le_kLog5 N
    rwa [div_le_iff₀ hL6] at this
  have hkhi : (kLog5 N : ℝ) * (logL N : ℝ) ^ 4 ≤ 2 * Nat.sqrt N := by
    have := kLog5_le_two_mul h5
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
  have hL5 : (logL N : ℝ) ^ 5 ≤ Nat.sqrt N := by exact_mod_cast h5
  exact log5_algebra (by exact_mod_cast hs4) hsN hNs hL hL5 hklo hkhi (by exact_mod_cast hk1) hA0 hρ0

end DetMinCut
end CutQueryComplexity
