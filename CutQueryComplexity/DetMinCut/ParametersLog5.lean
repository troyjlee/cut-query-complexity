import CutQueryComplexity.DetMinCut.Parameters

/-! # The log-five center parameter (log-five plan, A1)

`kLog5 N = max 2 ⌈⌊√N⌋ / L(N)^4⌉`, with `⌊√N⌋ / L⁴ ≤ kLog5 N`, `kLog5 N ≤ ⌊√N⌋` when
`2 ≤ ⌊√N⌋`, and `kLog5 N ≤ 2⌊√N⌋ / L⁴` when `L(N)^5 ≤ ⌊√N⌋`. The existing threshold
`L(N)^7 ≤ ⌊√N⌋` implies the last condition (`logL_pow5_le_of_pow7`).
-/

namespace CutQueryComplexity
namespace DetMinCut

/-! ## The tuned center parameter -/

/-- `kLog5 N = max 2 ⌈⌊√N⌋ / L(N)^4⌉`. -/
noncomputable def kLog5 (N : ℕ) : ℕ :=
  max 2 ⌈(Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 4⌉₊

theorem two_le_kLog5 (N : ℕ) : 2 ≤ kLog5 N := le_max_left _ _

theorem sqrt_div_le_kLog5 (N : ℕ) : (Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 4 ≤ kLog5 N :=
  (Nat.le_ceil _).trans (by
    have : ⌈(Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 4⌉₊ ≤ kLog5 N := le_max_right _ _
    exact_mod_cast this)

theorem kLog5_le_sqrt {N : ℕ} (h2 : 2 ≤ Nat.sqrt N) : kLog5 N ≤ Nat.sqrt N := by
  unfold kLog5
  refine max_le h2 ?_
  rw [Nat.ceil_le]
  have hL : (1 : ℝ) ≤ (logL N : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast one_le_logL' N)
  exact div_le_self (Nat.cast_nonneg _) hL

theorem kLog5_le_two_mul {N : ℕ} (h5 : logL N ^ 5 ≤ Nat.sqrt N) :
    (kLog5 N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 4 := by
  have hL1 : (1 : ℝ) ≤ logL N := by exact_mod_cast one_le_logL' N
  have hL6 : (0 : ℝ) < (logL N : ℝ) ^ 4 := by positivity
  have hx : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 4 := by
    rw [le_div_iff₀ hL6, one_mul]
    have h45 : (logL N : ℝ) ^ 4 ≤ (logL N : ℝ) ^ 5 := pow_le_pow_right₀ hL1 (by norm_num)
    have : ((logL N ^ 5 : ℕ) : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast h5
    push_cast at this; linarith
  unfold kLog5
  push_cast
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (Nat.sqrt N : ℝ) / (logL N : ℝ) ^ 4 by positivity)
  rw [mul_div_assoc]
  refine max_le (by linarith) (by linarith)

theorem logL_pow5_le_of_pow7 {N : ℕ} (h7 : logL N ^ 7 ≤ Nat.sqrt N) :
    logL N ^ 5 ≤ Nat.sqrt N :=
  (Nat.pow_le_pow_right (one_le_logL' N) (by norm_num)).trans h7

end DetMinCut
end CutQueryComplexity
