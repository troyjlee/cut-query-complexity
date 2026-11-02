import CutQueryComplexity.TreeCutSparsifier.ParametersLL
import CutQueryComplexity.TreeCutSparsifier.Budget

/-! # Query accounting for learning the tree with the log-log quality (log-log plan, M5)

The phase budget `phaseBudget` is unchanged; only the center parameter is. With
`parameterLL N α ≈ α / (D' L(N)² K(N)²)`, each phase costs at most
`phaseCoefLL n α · N` where `phaseCoefLL n α = 2000 D' (α + n L(n)³ K(n)² / α)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CutQueryComplexity.TreeCutSparsifier

open DetMinCut Discovery
open Hierarchy.RackeShah (KK)

theorem admissibleLL_bounds {n : ℕ} {α : ℝ} (h : AdmissibleLL n α) :
    1 ≤ α ∧ (logL n : ℝ)^2 ≤ α ∧ (logL n : ℝ)^2 ≤ n := by
  have hL : (logL n : ℝ)^2 ≤ unitLL n := logL_sq_le_unitLL n
  have hU := one_le_unitLL n
  have hD : 1 ≤ discoveryConstantLL := by norm_num [discoveryConstantLL]
  have h1 := h.1
  have hα1 : 1 ≤ α := by nlinarith
  have hLα : (logL n : ℝ)^2 ≤ α := by nlinarith
  exact ⟨hα1, hLα, by nlinarith [h.2]⟩

/-- The real-variable arithmetic of the phase bound with the quality unit `L² K²`. -/
theorem phase_algebraLL {N n k L K M MK α d : ℝ}
    (hN : 1 ≤ N) (hNn : N ≤ n) (hk : 1 ≤ k) (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hLM : L ≤ M) (hKM : K ≤ MK)
    (hd : 1 ≤ d) (hα : 1 ≤ α) (hLα : L^2 ≤ α) (hMn : M^2 ≤ n)
    (hlo : α ≤ 2 * d * k * (L^2 * K^2)) (hhi : d * k * (L^2 * K^2) ≤ α) :
    28 * N * k * L^2 + (8 * N * L / k + 1) * (108 * L^2 + N) +
      (N + 1) * 2 * (8 * N * L / k + 2) + 8 * N + 1 ≤
      2000 * d * (α + n * (M^3 * MK^2) / α) * N := by
  have hk0 : 0 < k := by linarith
  have hα0 : 0 < α := by linarith
  have hM : 1 ≤ M := hL.trans hLM
  have hMK : 1 ≤ MK := hK.trans hKM
  have hn0 : 0 ≤ n := by linarith
  have hLn : L^2 ≤ n := (pow_le_pow_left₀ (by linarith) hLM 2).trans hMn
  have hK2 : 1 ≤ K^2 := one_le_pow₀ hK
  have hkL : k * L^2 ≤ α := by
    calc k * L^2 = 1 * k * (L^2 * 1) := by ring
      _ ≤ d * k * (L^2 * K^2) := by gcongr
      _ ≤ α := hhi
  set W : ℝ := M^3 * MK^2 with hW
  have hr : 8 * N * L / k ≤ 16 * d * N * W / α := by
    rw [div_le_div_iff₀ hk0 hα0]
    calc 8 * N * L * α ≤ 8 * N * L * (2 * d * k * (L^2 * K^2)) := by gcongr
      _ = 16 * d * N * (L^3 * K^2) * k := by ring
      _ ≤ 16 * d * N * (M^3 * MK^2) * k := by gcongr
  have hscore : 108 * L^2 + N ≤ 109 * n := by linarith
  have hscore' : 108 * L^2 + N ≤ 109 * (N * α) := by
    have hNA : α ≤ N * α := le_mul_of_one_le_left (by linarith) hN
    have hNN : N ≤ N * α := le_mul_of_one_le_right (by linarith) hα
    linarith
  have t1 : 28 * N * k * L^2 ≤ 28 * (N * α) := by nlinarith
  have hW0 : 0 ≤ W := by positivity
  have t2 : (8 * N * L / k + 1) * (108 * L^2 + N) ≤
      1744 * d * (N * n * W / α) + 109 * (N * α) := by
    calc _ = (8 * N * L / k) * (108 * L^2 + N) + (108 * L^2 + N) := by ring
      _ ≤ (16 * d * N * W / α) * (109 * n) + 109 * (N * α) := by gcongr
      _ = _ := by ring
  have t3 : (N + 1) * 2 * (8 * N * L / k + 2) ≤
      64 * d * (N * n * W / α) + 8 * (N * α) := by
    calc _ ≤ (2 * N) * 2 * (16 * d * N * W / α + 2) := by gcongr; linarith
      _ = 64 * d * N * (N * W) / α + 8 * N := by ring
      _ ≤ 64 * d * N * (n * W) / α + 8 * (N * α) := by gcongr; nlinarith
      _ = _ := by ring
  have t4 : 8 * N + 1 ≤ 9 * (N * α) := by nlinarith
  have hX : 0 ≤ N * α := by positivity
  have hZ : 0 ≤ N * n * W / α := by positivity
  have hsum := add_le_add (add_le_add t1 t2) (add_le_add t3 t4)
  have hscale : N * α ≤ d * (N * α) := le_mul_of_one_le_left hX hd
  have hend : 154 * (N * α) + 1808 * d * (N * n * W / α) ≤
      2000 * d * (N * α) + 2000 * d * (N * n * W / α) := by nlinarith
  calc _ ≤ 154 * (N * α) + 1808 * d * (N * n * W / α) := by linarith
    _ ≤ _ := hend
    _ = _ := by rw [hW]; ring

/-- The per-vertex phase coefficient `2000 D' (α + n L(n)³ K(n)² / α)`. -/
noncomputable def phaseCoefLL (n : ℕ) (α : ℝ) : ℝ :=
  2000 * discoveryConstantLL * (α + n * ((logL n : ℝ)^3 * (KK n : ℝ)^2) / α)

theorem phaseCoefLL_ge {n : ℕ} {α : ℝ} (h : AdmissibleLL n α) : α ≤ phaseCoefLL n α := by
  have hα := admissibleLL_pos h
  have hpos : 0 ≤ n * ((logL n : ℝ)^3 * (KK n : ℝ)^2) / α := by positivity
  unfold phaseCoefLL discoveryConstantLL
  nlinarith

theorem phaseCoefLL_pos {n : ℕ} {α : ℝ} (h : AdmissibleLL n α) : 0 < phaseCoefLL n α :=
  (admissibleLL_pos h).trans_le (phaseCoefLL_ge h)

theorem phaseBudgetLL_le {n N : ℕ} {α : ℝ} (h : AdmissibleLL n α)
    (hN : 1 ≤ N) (hNn : N ≤ n) :
    (phaseBudget N (parameterLL N α) : ℝ) ≤ phaseCoefLL n α * N := by
  obtain ⟨hk, hhi, hlo⟩ := parameterLL_spec h hNn
  obtain ⟨hα, hLα, hLn⟩ := admissibleLL_bounds h
  have hLM : (logL N : ℝ) ≤ logL n := by exact_mod_cast logL_mono hNn
  have hKM : (KK N : ℝ) ≤ KK n := by exact_mod_cast KK_mono hNn
  have hL2 : (logL N : ℝ)^2 ≤ (logL n : ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hLM 2
  have hlo' : α ≤ 2 * discoveryConstantLL * (parameterLL N α : ℝ) *
      ((logL N : ℝ)^2 * (KK N : ℝ)^2) := by unfold unitLL at hlo; exact hlo
  have hhi' : discoveryConstantLL * (parameterLL N α : ℝ) *
      ((logL N : ℝ)^2 * (KK N : ℝ)^2) ≤ α := by unfold unitLL at hhi; exact hhi
  exact (phaseBudget_terms (by omega)).trans (phase_algebraLL
    (by exact_mod_cast hN) (by exact_mod_cast hNn)
    (by exact_mod_cast (by omega : 1 ≤ parameterLL N α))
    (by exact_mod_cast one_le_logL' N) (by exact_mod_cast one_le_KK' N) hLM hKM
    (by norm_num [discoveryConstantLL]) hα (hL2.trans hLα) hLn hlo' hhi')

end CutQueryComplexity.TreeCutSparsifier
