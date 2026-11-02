import CutQueryComplexity.TreeCutSparsifier.Phase
import CutQueryComplexity.DetMinCut.Budget

/-! # The supplied distortion parameter and the center parameter -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CutQueryComplexity.TreeCutSparsifier

open DetMinCut

def discoveryConstant : ℝ := 154320660

theorem discoveryConstant_ge : 1690 ≤ discoveryConstant := by norm_num [discoveryConstant]

def Admissible (n : ℕ) (α : ℝ) : Prop :=
  2 * discoveryConstant * (logL n : ℝ)^4 ≤ α ∧ α^2 ≤ n

noncomputable def parameter (N : ℕ) (α : ℝ) : ℕ :=
  ⌊α / (discoveryConstant * (logL N : ℝ)^4)⌋₊

theorem admissible_lower {n N : ℕ} {α : ℝ} (h : Admissible n α) (hN : N ≤ n) :
    2 * discoveryConstant * (logL N : ℝ)^4 ≤ α := by
  refine le_trans ?_ h.1
  have hL : (logL N : ℝ) ≤ logL n := by exact_mod_cast logL_mono hN
  have : 0 ≤ discoveryConstant := by norm_num [discoveryConstant]
  gcongr

theorem admissible_pos {n : ℕ} {α : ℝ} (h : Admissible n α) : 0 < α := by
  have hL : (1 : ℝ) ≤ (logL n : ℝ)^4 :=
    one_le_pow₀ (by exact_mod_cast one_le_logL' n)
  have := h.1
  norm_num [discoveryConstant] at this
  linarith

theorem parameter_spec {n N : ℕ} {α : ℝ} (h : Admissible n α) (hN : N ≤ n) :
    2 ≤ parameter N α ∧
      discoveryConstant * (parameter N α : ℝ) * (logL N : ℝ)^4 ≤ α ∧
      α ≤ 2 * discoveryConstant * (parameter N α : ℝ) * (logL N : ℝ)^4 := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hD : 0 < discoveryConstant := by norm_num [discoveryConstant]
  have hd : 0 < discoveryConstant * (logL N : ℝ)^4 := by positivity
  have hx : 2 ≤ α / (discoveryConstant * (logL N : ℝ)^4) := by
    rw [le_div_iff₀ hd]
    nlinarith [admissible_lower h hN]
  have hk : 2 ≤ parameter N α := Nat.le_floor hx
  have hf := Nat.floor_le (show 0 ≤ α / (discoveryConstant * (logL N : ℝ)^4) by linarith)
  have hg := Nat.lt_floor_add_one (α / (discoveryConstant * (logL N : ℝ)^4))
  change (parameter N α : ℝ) ≤ _ at hf
  change _ < (parameter N α : ℝ) + 1 at hg
  rw [le_div_iff₀ hd] at hf
  rw [div_lt_iff₀ hd] at hg
  have hkR : (2 : ℝ) ≤ parameter N α := by exact_mod_cast hk
  refine ⟨hk, by nlinarith, ?_⟩
  have : ((parameter N α : ℝ) + 1) * (discoveryConstant * (logL N : ℝ)^4) ≤
      (2 * parameter N α) * (discoveryConstant * (logL N : ℝ)^4) := by gcongr; linarith
  nlinarith

theorem quality_le {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    quality N k ≤ discoveryConstant * k * (logL N : ℝ)^4 := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hL2 : (1 : ℝ) ≤ (logL N : ℝ)^2 := one_le_pow₀ hL
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h3 : (logL (3 * N + 1) : ℝ) ≤ 3 * logL N := by
    exact_mod_cast logL_three (le_refl N) hN
  have ha : distortion (3 * N + 1) ≤ 9 * 1690 * (logL N : ℝ)^2 := by
    unfold distortion
    calc 1690 * (logL (3 * N + 1) : ℝ)^2 ≤ 1690 * (3 * logL N)^2 := by gcongr
      _ = _ := by ring
  have hb : 1 + distortion N ≤ 1691 * (logL N : ℝ)^2 := by
    unfold distortion
    nlinarith
  have hc : 2 * (k : ℝ) + 1 ≤ 3 * k := by linarith
  unfold quality promiseB
  have hidx : N + (2 * N + 1) = 3 * N + 1 := by omega
  rw [hidx]
  calc 2 * distortion (3 * N + 1) * ((1 + distortion N) * (2 * k + 1))
      ≤ 2 * (9 * 1690 * (logL N : ℝ)^2) *
          ((1691 * (logL N : ℝ)^2) * (3 * k)) := by
            have := distortion_one N
            have := distortion_one (3 * N + 1)
            gcongr
    _ = discoveryConstant * k * (logL N : ℝ)^4 := by norm_num [discoveryConstant]; ring

theorem parameter_quality {n N : ℕ} {α : ℝ} (h : Admissible n α)
    (hN0 : 1 ≤ N) (hN : N ≤ n) : quality N (parameter N α) ≤ α :=
  (quality_le hN0 (by have := (parameter_spec h hN).1; omega)).trans
    (parameter_spec h hN).2.1

theorem offline_quality {n N : ℕ} {α : ℝ} (h : Admissible n α) (hN : N ≤ n) :
    distortion N ≤ α := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have h24 : (logL N : ℝ)^2 ≤ (logL N : ℝ)^4 := pow_le_pow_right₀ hL (by norm_num)
  have hlow := admissible_lower h hN
  have hD := discoveryConstant_ge
  unfold distortion
  nlinarith [sq_nonneg (logL N : ℝ)]

theorem reconstruct_size {n N : ℕ} {α : ℝ} (h : Admissible n α) (hN : N ≤ n)
    (hk : N ≤ parameter N α) : (N : ℝ) ≤ α := by
  have hparam := (parameter_spec h hN).2.1
  have hkR : (N : ℝ) ≤ parameter N α := by exact_mod_cast hk
  have hL : (1 : ℝ) ≤ (logL N : ℝ)^4 := one_le_pow₀ (by exact_mod_cast one_le_logL' N)
  have hD : 1 ≤ discoveryConstant := by norm_num [discoveryConstant]
  have : (parameter N α : ℝ) ≤ discoveryConstant * (parameter N α : ℝ) * (logL N : ℝ)^4 := by
    calc (parameter N α : ℝ) = 1 * (parameter N α : ℝ) * 1 := by ring
      _ ≤ _ := by gcongr
  linarith

end CutQueryComplexity.TreeCutSparsifier
