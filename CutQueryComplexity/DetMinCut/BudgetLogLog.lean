import CutQueryComplexity.DetMinCut.BudgetLog5
import CutQueryComplexity.DetMinCut.ParametersLogLog

/-! # Sharp phase bounds with distortion `L K` (log-log plan, M1)

With guard quality `ρ₀` and distortion `a(r) ≤ A₀ L(r) K(r)`, the generic `phase_terms`
applies with `a' = 9 A₀ L K` (`phaseBoundR_const_LK_le`), using `L(3N + 1) ≤ 3 L(N)` and
`K(3N + 1) ≤ 3 K(N)`. The arithmetic of the tuned parameter is the log-five one with `L⁴`
abstracted to `M²` and `L⁵` to `L M²` (`phase_algebra_gen`): with `M = L K`, `k = kLL N` and
`L(N)^7 ≤ ⌊√N⌋`, every term is `O(N ⌊√N⌋ L(N)³ K(N)²)` (`phaseBound_LL`), with the same
constant `cLog5 A₀ ρ₀` as the log-five bound.
-/

namespace CutQueryComplexity
namespace DetMinCut

open Discovery Hierarchy Finset
open Hierarchy.RackeShah (KK)

variable {a : ℕ → ℝ}

/-- One phase with constant guard quality and distortion `A₀ L K`, for any `k ≥ 1`. -/
theorem phaseBoundR_const_LK_le (ha : ∀ r, 1 ≤ a r) {A0 ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) * (KK r : ℝ)) {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    phaseBoundR a (fun _ => ρ0) N k ≤
      28 * N * k * (logL N : ℝ) ^ 2 +
        (8 * N * logL N / k + 1) * (108 * (logL N : ℝ) ^ 2 + N) +
        2 * (2 * (8 * N * logL N / k + 2)) ^ 2 +
      (9 * (N + 1) * (12 * (9 * A0 * ((logL N : ℝ) * (KK N : ℝ))) ^ 2 * k + 2) +
        35251200 * ρ0 ^ 4 * (N + 1) * logL N *
          (9 * A0 * ((logL N : ℝ) * (KK N : ℝ))) ^ 4 * k + 1) := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hK : (1 : ℝ) ≤ KK N := by exact_mod_cast one_le_KK' N
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
    rw [h0, KK_zero, Nat.cast_one, mul_one, mul_one] at h2
    linarith
  set M : ℝ := (logL N : ℝ) * (KK N : ℝ) with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; nlinarith
  have ha'1 : 1 ≤ 9 * A0 * M := by nlinarith
  have haN : a N ≤ 9 * A0 * M := by
    refine (hA N).trans ?_
    rw [hMdef]
    have : 0 ≤ A0 * (logL N : ℝ) * (KK N : ℝ) := by positivity
    linarith
  have ha3 : a (3 * N + 1) ≤ 9 * A0 * M := by
    refine (hA _).trans ?_
    have h3 : (logL (3 * N + 1) : ℝ) ≤ 3 * logL N := by exact_mod_cast logL_three (le_refl N) hN
    have h3' : (KK (3 * N + 1) : ℝ) ≤ 3 * KK N := by exact_mod_cast KK_three (le_refl N) hN
    rw [hMdef]
    calc A0 * (logL (3 * N + 1) : ℝ) * (KK (3 * N + 1) : ℝ)
        ≤ A0 * (3 * logL N) * (3 * KK N) := by gcongr
      _ = 9 * A0 * ((logL N : ℝ) * (KK N : ℝ)) := by ring
  have hρf : ∀ M : ℕ, 1 ≤ (fun _ : ℕ => ρ0) M := fun _ => hρ0
  have hγ := gammaR_pos ha hρf N
  have hγ1 : gammaR a (fun _ => ρ0) N ≤ 1 := by
    unfold gammaR
    rw [div_le_one (by have := ha N; positivity)]
    have : 1 ≤ a N ^ 2 := one_le_pow₀ (ha N)
    have : 1 ≤ ρ0 ^ 2 := one_le_pow₀ hρ0
    nlinarith
  have hinvγ : 1 / gammaR a (fun _ => ρ0) N ≤ 100 * (9 * A0 * M) ^ 2 * ρ0 ^ 2 := by
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

/-- The arithmetic of the tuned parameter, with `L⁴` abstracted to `M²` and `L⁵` to `L M²`.
With `M = L²` this is `log5_algebra`; with `M = L K` it is the log-log bound. -/
theorem phase_algebra_gen {N s L k A0 ρ0 M : ℝ} (hs4 : 4 ≤ s) (hsN : s ^ 2 ≤ N)
    (hNs : N ≤ 4 * s ^ 2) (hL : 1 ≤ L) (hLM : L ≤ M) (hLM2 : L * M ^ 2 ≤ s)
    (hklo : s ≤ k * M ^ 2) (hkhi : k * M ^ 2 ≤ 2 * s) (hk1 : 1 ≤ k) (hA0 : 1 ≤ A0)
    (hρ0 : 1 ≤ ρ0) :
    28 * N * k * L ^ 2 + (8 * N * L / k + 1) * (108 * L ^ 2 + N) +
        2 * (2 * (8 * N * L / k + 2)) ^ 2 +
      (9 * (N + 1) * (12 * (9 * A0 * M) ^ 2 * k + 2) +
        35251200 * ρ0 ^ 4 * (N + 1) * L * (9 * A0 * M) ^ 4 * k + 1)
      ≤ cLog5 A0 ρ0 * (N * s * (L * M ^ 2)) := by
  have hk0 : 0 < k := by linarith
  have hs0 : 0 < s := by linarith
  have hM1 : 1 ≤ M := hL.trans hLM
  have hN1 : 16 ≤ N := by nlinarith
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
  have hW1 : 1 ≤ L * M ^ 2 := one_le_mul_of_one_le_of_one_le hL hM2
  have hL2M : L ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by linarith) hLM 2
  have hX : 1 ≤ N * s * (L * M ^ 2) := by
    have : 1 ≤ N * s := by nlinarith
    nlinarith
  have hsW : s * (L * M ^ 2) ≤ N := by nlinarith
  have hL2N : L ^ 2 ≤ N := by
    have h1 : L ^ 2 ≤ L * M ^ 2 := by nlinarith
    have h2 : s ≤ s ^ 2 := by nlinarith
    linarith
  -- `8 N L / k ≤ 32 s L M²`
  have hNk : 8 * N * L / k ≤ 32 * s * (L * M ^ 2) := by
    rw [div_le_iff₀ hk0]
    have h1 : N ≤ 4 * s * (k * M ^ 2) := by nlinarith
    have h2 : 8 * N * L ≤ 8 * (4 * s * (k * M ^ 2)) * L := by nlinarith
    calc 8 * N * L ≤ 8 * (4 * s * (k * M ^ 2)) * L := h2
      _ = 32 * s * (L * M ^ 2) * k := by ring
  have hNk0 : 0 ≤ 8 * N * L / k := by positivity
  set W := L * M ^ 2 with hW
  -- the four terms
  have t1 : 28 * N * k * L ^ 2 ≤ 56 * (N * s * W) := by
    have h1 : k * L ^ 2 ≤ k * M ^ 2 := mul_le_mul_of_nonneg_left hL2M hk0.le
    have h2 : k * L ^ 2 ≤ 2 * s * W := by
      have : 2 * s ≤ 2 * s * W := le_mul_of_one_le_right (by linarith) hW1
      linarith
    calc 28 * N * k * L ^ 2 = 28 * N * (k * L ^ 2) := by ring
      _ ≤ 28 * N * (2 * s * W) := by gcongr
      _ = 56 * (N * s * W) := by ring
  have t2 : (8 * N * L / k + 1) * (108 * L ^ 2 + N) ≤ 3597 * (N * s * W) := by
    have h1 : 8 * N * L / k + 1 ≤ 33 * s * W := by nlinarith
    have h2 : 108 * L ^ 2 + N ≤ 109 * N := by linarith
    calc _ ≤ (33 * s * W) * (109 * N) := by gcongr
      _ = 3597 * (N * s * W) := by ring
  have t3 : 2 * (2 * (8 * N * L / k + 2)) ^ 2 ≤ 9248 * (N * s * W) := by
    have h1 : 2 * (8 * N * L / k + 2) ≤ 68 * (s * W) := by nlinarith
    have h0 : 0 ≤ 2 * (8 * N * L / k + 2) := by positivity
    have h2 : (2 * (8 * N * L / k + 2)) ^ 2 ≤ (68 * (s * W)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have h3 : (s * W) * (s * W) ≤ N * (s * W) :=
      mul_le_mul_of_nonneg_right hsW (by positivity)
    calc _ ≤ 2 * (68 * (s * W)) ^ 2 := by linarith
      _ = 9248 * ((s * W) * (s * W)) := by ring
      _ ≤ 9248 * (N * (s * W)) := by gcongr
      _ = 9248 * (N * s * W) := by ring
  have t4 : 9 * (N + 1) * (12 * (9 * A0 * M) ^ 2 * k + 2) ≤
      18 * (1944 * A0 ^ 2 + 2) * (N * s * W) := by
    have h1 : (9 * A0 * M) ^ 2 * k ≤ 162 * A0 ^ 2 * s := by
      calc (9 * A0 * M) ^ 2 * k = 81 * A0 ^ 2 * (k * M ^ 2) := by ring
        _ ≤ 81 * A0 ^ 2 * (2 * s) := by gcongr
        _ = 162 * A0 ^ 2 * s := by ring
    have h2 : 12 * (9 * A0 * M) ^ 2 * k + 2 ≤ (1944 * A0 ^ 2 + 2) * s := by nlinarith
    have h3 : N + 1 ≤ 2 * N := by linarith
    calc _ ≤ 9 * (2 * N) * ((1944 * A0 ^ 2 + 2) * s) := by gcongr
      _ = 18 * (1944 * A0 ^ 2 + 2) * (N * s) := by ring
      _ ≤ 18 * (1944 * A0 ^ 2 + 2) * (N * s * W) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hW1) (by positivity)
  have t5 : 35251200 * ρ0 ^ 4 * (N + 1) * L * (9 * A0 * M) ^ 4 * k ≤
      4 * 35251200 * 6561 * (A0 ^ 4 * ρ0 ^ 4) * (N * s * W) := by
    have h1 : L * (9 * A0 * M) ^ 4 * k = 6561 * A0 ^ 4 * (W * (k * M ^ 2)) := by
      rw [hW]; ring
    have h2 : W * (k * M ^ 2) ≤ W * (2 * s) := by gcongr
    have h3 : N + 1 ≤ 2 * N := by linarith
    calc 35251200 * ρ0 ^ 4 * (N + 1) * L * (9 * A0 * M) ^ 4 * k
        = 35251200 * ρ0 ^ 4 * (N + 1) * (L * (9 * A0 * M) ^ 4 * k) := by ring
      _ = 35251200 * ρ0 ^ 4 * (N + 1) * (6561 * A0 ^ 4 * (W * (k * M ^ 2))) := by rw [h1]
      _ ≤ 35251200 * ρ0 ^ 4 * (2 * N) * (6561 * A0 ^ 4 * (W * (2 * s))) := by gcongr
      _ = 4 * 35251200 * 6561 * (A0 ^ 4 * ρ0 ^ 4) * (N * s * W) := by ring
  unfold cLog5
  nlinarith

/-- **A tuned phase above the threshold costs `O(N ⌊√N⌋ L(N)³ K(N)²)`.** -/
theorem phaseBound_LL (ha : ∀ r, 1 ≤ a r) {A0 ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hA : ∀ r, a r ≤ A0 * (logL r : ℝ) * (KK r : ℝ)) {N : ℕ} (h16 : 16 ≤ N)
    (h7 : logL N ^ 7 ≤ Nat.sqrt N) :
    phaseBoundR a (fun _ => ρ0) N (kLL N) ≤
      cLog5 A0 ρ0 * (N * Nat.sqrt N * ((logL N : ℝ) ^ 3 * (KK N : ℝ) ^ 2)) := by
  have hA0 : 1 ≤ A0 := by
    have h1 := ha 0; have h2 := hA 0
    have h0 : logL 0 = 1 := by simp [logL]
    rw [h0, KK_zero, Nat.cast_one, mul_one, mul_one] at h2
    linarith
  have hk1 : 1 ≤ kLL N := le_trans (by norm_num) (two_le_kLL N)
  refine (phaseBoundR_const_LK_le ha hρ0 hA (by omega) hk1).trans ?_
  have hs4 : 4 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hK : (1 : ℝ) ≤ KK N := by exact_mod_cast one_le_KK' N
  have hD : (0 : ℝ) < (logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2 := by positivity
  have h2 := logL2_KK2_le_of_pow7 h7
  have h3 := logL3_KK2_le_of_pow7 h7
  have hklo : (Nat.sqrt N : ℝ) ≤ kLL N * ((logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2) := by
    have := sqrt_div_le_kLL N
    rwa [div_le_iff₀ hD] at this
  have hkhi : (kLL N : ℝ) * ((logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2) ≤ 2 * Nat.sqrt N := by
    have := kLL_le_two_mul h2
    rwa [le_div_iff₀ hD] at this
  have hsN : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ N := by
    have := Nat.sqrt_le N
    have : ((Nat.sqrt N * Nat.sqrt N : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    push_cast at this; nlinarith
  have hNs : (N : ℝ) ≤ 4 * ((Nat.sqrt N : ℕ) : ℝ) ^ 2 := by
    have h1 := Nat.lt_succ_sqrt N
    have h2 : N ≤ 4 * (Nat.sqrt N * Nat.sqrt N) := by nlinarith
    have : (N : ℝ) ≤ ((4 * (Nat.sqrt N * Nat.sqrt N) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this; nlinarith
  have hLM2 : (logL N : ℝ) * ((logL N : ℝ) * (KK N : ℝ)) ^ 2 ≤ Nat.sqrt N := by
    have : ((logL N ^ 3 * KK N ^ 2 : ℕ) : ℝ) ≤ Nat.sqrt N := by exact_mod_cast h3
    push_cast at this
    linarith [show (logL N : ℝ) * ((logL N : ℝ) * (KK N : ℝ)) ^ 2 =
      (logL N : ℝ) ^ 3 * (KK N : ℝ) ^ 2 by ring]
  have hLM : (logL N : ℝ) ≤ (logL N : ℝ) * (KK N : ℝ) := le_mul_of_one_le_right (by linarith) hK
  have key := phase_algebra_gen (M := (logL N : ℝ) * (KK N : ℝ)) (by exact_mod_cast hs4) hsN hNs
    hL hLM hLM2 (by rw [mul_pow]; exact hklo) (by rw [mul_pow]; exact hkhi)
    (by exact_mod_cast hk1) hA0 hρ0
  refine key.trans (le_of_eq ?_)
  ring

end DetMinCut
end CutQueryComplexity
