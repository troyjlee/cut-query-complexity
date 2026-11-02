import CutQueryComplexity.TreeCutSparsifier.Parameters

/-! # Query accounting for learning the tree

Each phase is bounded by a constant times its current number of vertices.
The coefficient uses the original size and the supplied distortion; geometric
halving therefore pays for all phases without an extra logarithmic factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CutQueryComplexity.TreeCutSparsifier

open DetMinCut Discovery

theorem admissible_bounds {n : ℕ} {α : ℝ} (h : Admissible n α) :
    1 ≤ α ∧ (logL n : ℝ)^2 ≤ α ∧ (logL n : ℝ)^2 ≤ n := by
  have hL : (1 : ℝ) ≤ (logL n : ℝ)^2 := one_le_pow₀ (by exact_mod_cast one_le_logL' n)
  have ho := offline_quality h (le_refl n)
  unfold distortion at ho
  have hα1 : 1 ≤ α := by linarith
  exact ⟨hα1, by linarith, by nlinarith [h.2]⟩

theorem phaseBudget_terms {N k : ℕ} (hk : 1 ≤ k) :
    (phaseBudget N k : ℝ) ≤
      28 * N * k * (logL N : ℝ)^2 +
      (8 * N * logL N / k + 1) * (108 * (logL N : ℝ)^2 + N) +
      (N + 1) * 2 * (8 * N * logL N / k + 2) + 8 * N + 1 := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hc : (Nat.clog 2 N : ℝ) ≤ logL N := by exact_mod_cast clog_le_logL (le_refl N)
  have hp : (Nat.clog 2 (N - 1) : ℝ) ≤ logL N := by
    exact_mod_cast clog_pred_le_logL (le_refl N)
  have hn : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hs := selectionBudget_le_gen (N := N) hk
  have hprep : (N : ℝ) * (4 + 3 * Nat.clog 2 N) * (4 * k * Nat.clog 2 (N - 1)) ≤
      28 * N * k * (logL N : ℝ)^2 := by
    calc _ ≤ (N : ℝ) * (7 * logL N) * (4 * k * logL N) := by gcongr; linarith
      _ = _ := by ring
  have hcsel : 6 * (6 + 3 * (Nat.clog 2 N : ℝ)) * (Nat.clog 2 N + 1) + (N - 1 : ℕ) ≤
      108 * (logL N : ℝ)^2 + N := by
    calc _ ≤ 6 * (9 * (logL N : ℝ)) * (2 * logL N) + N := by gcongr <;> linarith
      _ = _ := by ring
  have hselect : (selectionBudget N k : ℝ) *
      (6 * (6 + 3 * (Nat.clog 2 N : ℝ)) * (Nat.clog 2 N + 1) + (N - 1 : ℕ)) ≤
      (8 * N * logL N / k + 1) * (108 * (logL N : ℝ)^2 + N) := by gcongr
  have hquot : ((N : ℝ) + 1) * (2 * ((selectionBudget N k : ℝ) + 1)) ≤
      (N + 1) * 2 * (8 * N * logL N / k + 2) := by
    calc _ ≤ ((N : ℝ) + 1) * (2 * (8 * N * logL N / k + 2)) := by
          have hh : (selectionBudget N k : ℝ) + 1 ≤ 8 * N * logL N / k + 2 := by linarith
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by norm_num)) (by positivity)
      _ = _ := by ring
  unfold phaseBudget prepS
  push_cast
  linarith

/-- The real-variable arithmetic of the phase bound. -/
theorem phase_algebra {N n k L M α d : ℝ}
    (hN : 1 ≤ N) (hNn : N ≤ n) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLM : L ≤ M)
    (hd : 1 ≤ d) (hα : 1 ≤ α) (hLα : L^2 ≤ α) (hMn : M^2 ≤ n)
    (hlo : α ≤ 2 * d * k * L^4) (hhi : d * k * L^4 ≤ α) :
    28 * N * k * L^2 + (8 * N * L / k + 1) * (108 * L^2 + N) +
      (N + 1) * 2 * (8 * N * L / k + 2) + 8 * N + 1 ≤
      2000 * d * (α + n * M^5 / α) * N := by
  have hk0 : 0 < k := by linarith
  have hα0 : 0 < α := by linarith
  have hM : 1 ≤ M := hL.trans hLM
  have hn0 : 0 ≤ n := by linarith
  have hLn : L^2 ≤ n := (pow_le_pow_left₀ (by linarith) hLM 2).trans hMn
  have h24 : L^2 ≤ L^4 := pow_le_pow_right₀ hL (by norm_num)
  have hkL : k * L^2 ≤ α := by
    calc k * L^2 = 1 * k * L^2 := by ring
      _ ≤ d * k * L^4 := by gcongr
      _ ≤ α := hhi
  have hr : 8 * N * L / k ≤ 16 * d * N * M^5 / α := by
    rw [div_le_div_iff₀ hk0 hα0]
    calc 8 * N * L * α ≤ 8 * N * L * (2 * d * k * L^4) := by gcongr
      _ = 16 * d * N * L^5 * k := by ring
      _ ≤ 16 * d * N * M^5 * k := by gcongr
  have hscore : 108 * L^2 + N ≤ 109 * n := by linarith
  have hscore' : 108 * L^2 + N ≤ 109 * (N * α) := by
    have hNA : α ≤ N * α := le_mul_of_one_le_left (by linarith) hN
    have hNN : N ≤ N * α := le_mul_of_one_le_right (by linarith) hα
    linarith
  have t1 : 28 * N * k * L^2 ≤ 28 * (N * α) := by nlinarith
  have t2 : (8 * N * L / k + 1) * (108 * L^2 + N) ≤
      1744 * d * (N * n * M^5 / α) + 109 * (N * α) := by
    calc _ = (8 * N * L / k) * (108 * L^2 + N) + (108 * L^2 + N) := by ring
      _ ≤ (16 * d * N * M^5 / α) * (109 * n) + 109 * (N * α) := by gcongr
      _ = _ := by ring
  have t3 : (N + 1) * 2 * (8 * N * L / k + 2) ≤
      64 * d * (N * n * M^5 / α) + 8 * (N * α) := by
    calc _ ≤ (2 * N) * 2 * (16 * d * N * M^5 / α + 2) := by gcongr; linarith
      _ = 64 * d * N * (N * M^5) / α + 8 * N := by ring
      _ ≤ 64 * d * N * (n * M^5) / α + 8 * (N * α) := by gcongr; nlinarith
      _ = _ := by ring
  have t4 : 8 * N + 1 ≤ 9 * (N * α) := by nlinarith
  have hX : 0 ≤ N * α := by positivity
  have hZ : 0 ≤ N * n * M^5 / α := by positivity
  have hsum := add_le_add (add_le_add t1 t2) (add_le_add t3 t4)
  have hscale : N * α ≤ d * (N * α) := le_mul_of_one_le_left hX hd
  have hend : 154 * (N * α) + 1808 * d * (N * n * M^5 / α) ≤
      2000 * d * (N * α) + 2000 * d * (N * n * M^5 / α) := by nlinarith
  calc _ ≤ 154 * (N * α) + 1808 * d * (N * n * M^5 / α) := by linarith
    _ ≤ _ := hend
    _ = _ := by ring

noncomputable def phaseK (n : ℕ) (α : ℝ) : ℝ :=
  2000 * discoveryConstant * (α + n * (logL n : ℝ)^5 / α)

theorem phaseK_ge {n : ℕ} {α : ℝ} (h : Admissible n α) : α ≤ phaseK n α := by
  have hα := admissible_pos h
  have hpos : 0 ≤ n * (logL n : ℝ)^5 / α := by positivity
  unfold phaseK discoveryConstant
  nlinarith

theorem phaseK_pos {n : ℕ} {α : ℝ} (h : Admissible n α) : 0 < phaseK n α :=
  (admissible_pos h).trans_le (phaseK_ge h)

theorem phaseBudget_le {n N : ℕ} {α : ℝ} (h : Admissible n α)
    (hN : 1 ≤ N) (hNn : N ≤ n) :
    (phaseBudget N (parameter N α) : ℝ) ≤ phaseK n α * N := by
  obtain ⟨hk, hhi, hlo⟩ := parameter_spec h hNn
  obtain ⟨hα, hLα, hLn⟩ := admissible_bounds h
  have hLM : (logL N : ℝ) ≤ logL n := by exact_mod_cast logL_mono hNn
  have hL2 : (logL N : ℝ)^2 ≤ (logL n : ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hLM 2
  exact (phaseBudget_terms (by omega)).trans (phase_algebra
    (by exact_mod_cast hN) (by exact_mod_cast hNn) (by exact_mod_cast (by omega : 1 ≤ parameter N α))
    (by exact_mod_cast one_le_logL' N) hLM (by norm_num [discoveryConstant]) hα
    (hL2.trans hLα) hLn hlo hhi)

end CutQueryComplexity.TreeCutSparsifier
