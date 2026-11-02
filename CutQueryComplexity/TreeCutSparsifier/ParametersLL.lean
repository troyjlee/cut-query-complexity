import CutQueryComplexity.TreeCutSparsifier.PhaseLL
import CutQueryComplexity.DetMinCut.Budget

/-! # The log-log distortion parameter and the center parameter (log-log plan, M5)

With the Räcke–Shah distortion `distortionLL N = 268 L(N) K(N)`, the quality of a phase
with center parameter `k` is `qualityLL N k ≤ discoveryConstantLL · k · L(N)² K(N)²`, where
`discoveryConstantLL = 54 · 268 · 269`. The quality unit `unitLL N = L(N)² K(N)²` replaces
`L(N)⁴` of the quadratic distortion. The input promise `AdmissibleLL n α` is
`2 discoveryConstantLL L(n)² K(n)² ≤ α ∧ α² ≤ n`, and the center parameter is
`parameterLL N α = ⌊α / (discoveryConstantLL L(N)² K(N)²)⌋₊`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CutQueryComplexity.TreeCutSparsifier

open DetMinCut
open Hierarchy.RackeShah (KK rsConstant)

/-- `54 · 268 · 269`. -/
def discoveryConstantLL : ℝ := 3892968

theorem discoveryConstantLL_eq : discoveryConstantLL = 54 * rsConstant * (rsConstant + 1) := by
  norm_num [discoveryConstantLL, rsConstant]

theorem discoveryConstantLL_ge : rsConstant ≤ discoveryConstantLL := by
  norm_num [discoveryConstantLL, rsConstant]

/-- The quality unit `L(N)² K(N)²`. -/
noncomputable def unitLL (N : ℕ) : ℝ := (logL N : ℝ)^2 * (KK N : ℝ)^2

theorem one_le_unitLL (N : ℕ) : 1 ≤ unitLL N := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hK : (1 : ℝ) ≤ KK N := by exact_mod_cast one_le_KK' N
  unfold unitLL
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL) (one_le_pow₀ hK)

theorem unitLL_pos (N : ℕ) : 0 < unitLL N := lt_of_lt_of_le one_pos (one_le_unitLL N)

theorem unitLL_mono {N n : ℕ} (h : N ≤ n) : unitLL N ≤ unitLL n := by
  have hL : (logL N : ℝ) ≤ logL n := by exact_mod_cast logL_mono h
  have hK : (KK N : ℝ) ≤ KK n := by exact_mod_cast KK_mono h
  unfold unitLL
  gcongr

/-- `L(N) K(N) ≤ L(N)² K(N)²`. -/
theorem logL_mul_KK_le_unitLL (N : ℕ) : (logL N : ℝ) * KK N ≤ unitLL N := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hK : (1 : ℝ) ≤ KK N := by exact_mod_cast one_le_KK' N
  have hX : 1 ≤ (logL N : ℝ) * KK N := one_le_mul_of_one_le_of_one_le hL hK
  have : unitLL N = ((logL N : ℝ) * KK N)^2 := by unfold unitLL; ring
  rw [this]
  nlinarith

theorem logL_sq_le_unitLL (N : ℕ) : (logL N : ℝ)^2 ≤ unitLL N := by
  have hK : (1 : ℝ) ≤ (KK N : ℝ)^2 := one_le_pow₀ (by exact_mod_cast one_le_KK' N)
  unfold unitLL
  nlinarith [sq_nonneg (logL N : ℝ)]

def AdmissibleLL (n : ℕ) (α : ℝ) : Prop :=
  2 * discoveryConstantLL * unitLL n ≤ α ∧ α^2 ≤ n

noncomputable def parameterLL (N : ℕ) (α : ℝ) : ℕ :=
  ⌊α / (discoveryConstantLL * unitLL N)⌋₊

theorem admissibleLL_lower {n N : ℕ} {α : ℝ} (h : AdmissibleLL n α) (hN : N ≤ n) :
    2 * discoveryConstantLL * unitLL N ≤ α := by
  refine le_trans ?_ h.1
  have hU := unitLL_mono hN
  have : 0 ≤ discoveryConstantLL := by norm_num [discoveryConstantLL]
  gcongr

theorem admissibleLL_pos {n : ℕ} {α : ℝ} (h : AdmissibleLL n α) : 0 < α := by
  have hU := one_le_unitLL n
  have := h.1
  norm_num [discoveryConstantLL] at this
  linarith

theorem parameterLL_spec {n N : ℕ} {α : ℝ} (h : AdmissibleLL n α) (hN : N ≤ n) :
    2 ≤ parameterLL N α ∧
      discoveryConstantLL * (parameterLL N α : ℝ) * unitLL N ≤ α ∧
      α ≤ 2 * discoveryConstantLL * (parameterLL N α : ℝ) * unitLL N := by
  have hU : (1 : ℝ) ≤ unitLL N := one_le_unitLL N
  have hD : 0 < discoveryConstantLL := by norm_num [discoveryConstantLL]
  have hd : 0 < discoveryConstantLL * unitLL N := by positivity
  have hx : 2 ≤ α / (discoveryConstantLL * unitLL N) := by
    rw [le_div_iff₀ hd]
    nlinarith [admissibleLL_lower h hN]
  have hk : 2 ≤ parameterLL N α := Nat.le_floor hx
  have hf := Nat.floor_le (show 0 ≤ α / (discoveryConstantLL * unitLL N) by linarith)
  have hg := Nat.lt_floor_add_one (α / (discoveryConstantLL * unitLL N))
  change (parameterLL N α : ℝ) ≤ _ at hf
  change _ < (parameterLL N α : ℝ) + 1 at hg
  rw [le_div_iff₀ hd] at hf
  rw [div_lt_iff₀ hd] at hg
  have hkR : (2 : ℝ) ≤ parameterLL N α := by exact_mod_cast hk
  refine ⟨hk, by nlinarith, ?_⟩
  have : ((parameterLL N α : ℝ) + 1) * (discoveryConstantLL * unitLL N) ≤
      (2 * parameterLL N α) * (discoveryConstantLL * unitLL N) := by gcongr; linarith
  nlinarith

theorem qualityLL_le {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    qualityLL N k ≤ discoveryConstantLL * k * unitLL N := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hK : (1 : ℝ) ≤ KK N := by exact_mod_cast one_le_KK' N
  set X : ℝ := (logL N : ℝ) * KK N with hX
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le hL hK
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h3 : (logL (3 * N + 1) : ℝ) ≤ 3 * logL N := by
    exact_mod_cast logL_three (le_refl N) hN
  have h3K : (KK (3 * N + 1) : ℝ) ≤ 3 * KK N := by
    exact_mod_cast KK_three (le_refl N) hN
  have hprod : (logL (3 * N + 1) : ℝ) * KK (3 * N + 1) ≤ (3 * logL N) * (3 * KK N) :=
    mul_le_mul h3 h3K (Nat.cast_nonneg _) (by positivity)
  have ha : distortionLL (3 * N + 1) ≤ 9 * rsConstant * X := by
    unfold distortionLL rsConstant
    rw [hX]
    norm_num
    nlinarith [hprod]
  have hb : 1 + distortionLL N ≤ (rsConstant + 1) * X := by
    unfold distortionLL
    rw [hX]
    nlinarith
  have hc : 2 * (k : ℝ) + 1 ≤ 3 * k := by linarith
  have h1 : (1 + distortionLL N) * (2 * k + 1) ≤ ((rsConstant + 1) * X) * (3 * k) :=
    mul_le_mul hb hc (by positivity) (by unfold rsConstant; positivity)
  have hA : 0 ≤ (1 + distortionLL N) * (2 * k + 1) := by
    have := distortionLL_one N
    exact mul_nonneg (by linarith) (by positivity)
  have h2 : 2 * distortionLL (3 * N + 1) * ((1 + distortionLL N) * (2 * k + 1)) ≤
      2 * (9 * rsConstant * X) * (((rsConstant + 1) * X) * (3 * k)) :=
    mul_le_mul (by linarith) h1 hA (by unfold rsConstant; positivity)
  unfold qualityLL promiseB
  have hidx : N + (2 * N + 1) = 3 * N + 1 := by omega
  rw [hidx]
  calc 2 * distortionLL (3 * N + 1) * ((1 + distortionLL N) * (2 * k + 1))
      ≤ 2 * (9 * rsConstant * X) * (((rsConstant + 1) * X) * (3 * k)) := h2
    _ = discoveryConstantLL * k * unitLL N := by
        rw [discoveryConstantLL_eq, hX]; unfold unitLL; ring

theorem parameterLL_quality {n N : ℕ} {α : ℝ} (h : AdmissibleLL n α)
    (hN0 : 1 ≤ N) (hN : N ≤ n) : qualityLL N (parameterLL N α) ≤ α :=
  (qualityLL_le hN0 (by have := (parameterLL_spec h hN).1; omega)).trans
    (parameterLL_spec h hN).2.1

theorem offlineLL_quality {n N : ℕ} {α : ℝ} (h : AdmissibleLL n α) (hN : N ≤ n) :
    distortionLL N ≤ α := by
  have hlow := admissibleLL_lower h hN
  have hD := discoveryConstantLL_ge
  have hX := logL_mul_KK_le_unitLL N
  have hc : (0 : ℝ) ≤ rsConstant := by norm_num [rsConstant]
  have hU : 0 ≤ unitLL N := (unitLL_pos N).le
  unfold distortionLL
  calc rsConstant * (logL N : ℝ) * KK N = rsConstant * ((logL N : ℝ) * KK N) := by ring
    _ ≤ discoveryConstantLL * unitLL N := mul_le_mul hD hX (by positivity) (by linarith)
    _ ≤ 2 * discoveryConstantLL * unitLL N := by nlinarith
    _ ≤ α := hlow

theorem reconstructLL_size {n N : ℕ} {α : ℝ} (h : AdmissibleLL n α) (hN : N ≤ n)
    (hk : N ≤ parameterLL N α) : (N : ℝ) ≤ α := by
  have hparam := (parameterLL_spec h hN).2.1
  have hkR : (N : ℝ) ≤ parameterLL N α := by exact_mod_cast hk
  have hU : (1 : ℝ) ≤ unitLL N := one_le_unitLL N
  have hD : 1 ≤ discoveryConstantLL := by norm_num [discoveryConstantLL]
  have : (parameterLL N α : ℝ) ≤ discoveryConstantLL * (parameterLL N α : ℝ) * unitLL N := by
    calc (parameterLL N α : ℝ) = 1 * (parameterLL N α : ℝ) * 1 := by ring
      _ ≤ _ := by gcongr
  linarith

end CutQueryComplexity.TreeCutSparsifier
