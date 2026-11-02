import CutQueryComplexity.DetMinCut.ParametersLog5
import CutQueryComplexity.Hierarchy.RackeShah.LogBounds

/-! # The log-log center parameter (log-log plan, M0)

With the Räcke–Shah distortion `a(r) ≤ A₀ L(r) K(r)`, `K = Hierarchy.RackeShah.KK = L ∘ L`,
the tuned center parameter is `kLL N = max 2 ⌈⌊√N⌋ / (L(N)² K(N)²)⌉`, with
`⌊√N⌋ / (L² K²) ≤ kLL N`, `kLL N ≤ ⌊√N⌋` when `2 ≤ ⌊√N⌋`, and `kLL N ≤ 2⌊√N⌋ / (L² K²)`
when `L(N)² K(N)² ≤ ⌊√N⌋`. The existing threshold `L(N)^7 ≤ ⌊√N⌋` implies both
`L² K² ≤ ⌊√N⌋` and `L³ K² ≤ ⌊√N⌋`, since `K ≤ L` (`KK_le_logL`), and
`K(3N + 1) ≤ 3 K(N)` (`KK_three`) plays the role of `logL_three` for the distortion of the
auxiliary graph.
-/

namespace CutQueryComplexity
namespace DetMinCut

open Hierarchy.RackeShah (KK)

/-! ## Facts about `K = L ∘ L` -/

theorem KK_eq (n : ℕ) : KK n = logL (logL n) := rfl

theorem one_le_KK' (n : ℕ) : 1 ≤ KK n := Hierarchy.RackeShah.one_le_KK n

theorem KK_mono {N n : ℕ} (h : N ≤ n) : KK N ≤ KK n := logL_mono (logL_mono h)

/-- `L(m) ≤ m` for `m ≥ 1`. -/
theorem logL_le_self {m : ℕ} (hm : 1 ≤ m) : logL m ≤ m := by
  rw [logL_eq hm]
  have h2 : 2 * m ≤ 2 ^ m := by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
        rw [pow_succ]
        have : 2 ≤ 2 ^ m := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        omega
  exact (Nat.clog_le_iff_le_pow one_lt_two).mpr h2

theorem KK_le_logL (n : ℕ) : KK n ≤ logL n := logL_le_self (one_le_logL' n)

theorem KK_zero : KK 0 = 1 := by
  have h0 : logL 0 = 1 := by simp [logL]
  rw [KK_eq, h0]
  exact le_antisymm (logL_le_self le_rfl) (one_le_logL' 1)

theorem KK_three {N n : ℕ} (hN : N ≤ n) (hn : 1 ≤ n) : KK (3 * N + 1) ≤ 3 * KK n := by
  rw [KK_eq, KK_eq]
  calc logL (logL (3 * N + 1)) ≤ logL (3 * logL n) := logL_mono (logL_three hN hn)
    _ ≤ logL (3 * logL n + 1) := logL_mono (by omega)
    _ ≤ 3 * logL (logL n) := logL_three le_rfl (one_le_logL' n)

/-! ## The tuned center parameter -/

/-- `kLL N = max 2 ⌈⌊√N⌋ / (L(N)² K(N)²)⌉`. -/
noncomputable def kLL (N : ℕ) : ℕ :=
  max 2 ⌈(Nat.sqrt N : ℝ) / ((logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2)⌉₊

theorem two_le_kLL (N : ℕ) : 2 ≤ kLL N := le_max_left _ _

theorem one_le_LK2 (N : ℕ) : (1 : ℝ) ≤ (logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2 := by
  have hL : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hK : (1 : ℝ) ≤ KK N := by exact_mod_cast one_le_KK' N
  have := one_le_pow₀ (n := 2) hL
  have := one_le_pow₀ (n := 2) hK
  nlinarith

theorem sqrt_div_le_kLL (N : ℕ) :
    (Nat.sqrt N : ℝ) / ((logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2) ≤ kLL N :=
  (Nat.le_ceil _).trans (by
    have : ⌈(Nat.sqrt N : ℝ) / ((logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2)⌉₊ ≤ kLL N := le_max_right _ _
    exact_mod_cast this)

theorem kLL_le_sqrt {N : ℕ} (h2 : 2 ≤ Nat.sqrt N) : kLL N ≤ Nat.sqrt N := by
  unfold kLL
  refine max_le h2 ?_
  rw [Nat.ceil_le]
  exact div_le_self (Nat.cast_nonneg _) (one_le_LK2 N)

theorem kLL_le_two_mul {N : ℕ} (h : logL N ^ 2 * KK N ^ 2 ≤ Nat.sqrt N) :
    (kLL N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) / ((logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2) := by
  have hD : (0 : ℝ) < (logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2 := by linarith [one_le_LK2 N]
  have hx : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) / ((logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2) := by
    rw [le_div_iff₀ hD, one_mul]
    have : ((logL N ^ 2 * KK N ^ 2 : ℕ) : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  unfold kLL
  push_cast
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤
    (Nat.sqrt N : ℝ) / ((logL N : ℝ) ^ 2 * (KK N : ℝ) ^ 2) by positivity)
  rw [mul_div_assoc]
  refine max_le (by linarith) (by linarith)

/-! ## The threshold -/

theorem logL2_KK2_le_of_pow7 {N : ℕ} (h7 : logL N ^ 7 ≤ Nat.sqrt N) :
    logL N ^ 2 * KK N ^ 2 ≤ Nat.sqrt N := by
  have hK := KK_le_logL N
  calc logL N ^ 2 * KK N ^ 2 ≤ logL N ^ 2 * logL N ^ 2 := by gcongr
    _ = logL N ^ 4 := by ring
    _ ≤ logL N ^ 7 := Nat.pow_le_pow_right (one_le_logL' N) (by norm_num)
    _ ≤ Nat.sqrt N := h7

theorem logL3_KK2_le_of_pow7 {N : ℕ} (h7 : logL N ^ 7 ≤ Nat.sqrt N) :
    logL N ^ 3 * KK N ^ 2 ≤ Nat.sqrt N := by
  have hK := KK_le_logL N
  calc logL N ^ 3 * KK N ^ 2 ≤ logL N ^ 3 * logL N ^ 2 := by gcongr
    _ = logL N ^ 5 := by ring
    _ ≤ logL N ^ 7 := Nat.pow_le_pow_right (one_le_logL' N) (by norm_num)
    _ ≤ Nat.sqrt N := h7

end DetMinCut
end CutQueryComplexity
