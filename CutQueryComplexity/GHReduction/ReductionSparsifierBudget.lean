import CutQueryComplexity.GHReduction.ConfidenceLogBounds
import CutQueryComplexity.AllPairs.Budget

/-! # Counted one-percent sparsification fits the reduction envelope

Only arithmetic for the existing weighted sparsifier cap is reused from
`AllPairs.Budget`; no direct all-pairs algorithm is a premise of this reduction.
Changing accuracy from one half to one hundredth multiplies `paramc` by 2500.
The estimate below includes both natural ceilings and the sparsifier's own
hard cap, including failed executions.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open WeightedGraph

theorem paramc_onePercent (V : Type) [Fintype V] (s : ℝ) :
    paramc V s (1 / 100) = 2500 * paramc V s (1 / 2) := by
  unfold paramc
  ring

theorem outBound_onePercent_le (V : Type) [Fintype V] (s : ℝ) :
    outBound V (paramc V s (1 / 100)) ≤ 2500 * outBound V (paramc V s (1 / 2)) := by
  rw [paramc_onePercent]
  unfold outBound
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ residualDrawCost (searchDepth V) (searchDepth V) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hn hd]

theorem capQ_onePercent_le (V : Type) [Fintype V] (s : ℝ) :
    capQ V (paramρ V s) (paramc V s (1 / 100)) ≤
      2500 * capQ V (paramρ V s) (paramc V s (1 / 2)) := by
  have hceil : ⌈outBound V (paramc V s (1 / 100))⌉₊ ≤
      2500 * ⌈outBound V (paramc V s (1 / 2))⌉₊ := by
    apply Nat.ceil_le.mpr
    calc
      _ ≤ 2500 * outBound V (paramc V s (1 / 2)) := outBound_onePercent_le V s
      _ ≤ 2500 * (⌈outBound V (paramc V s (1 / 2))⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)
      _ = _ := by push_cast; rfl
  unfold capQ
  omega

theorem reductionSparsifierBudget_le (V : Type) [Fintype V] (hn : 1 ≤ Fintype.card V)
    (b : ℕ) : reductionSparsifierBudget V ((b + 3 : ℕ) : ℝ) ≤
      100000000 * (b + 11) * Fintype.card V * AllPairs.budgetLog (Fintype.card V) ^ 2 := by
  have hsmall : (reductionSparsifierBudget V ((b + 3 : ℕ) : ℝ) : ℝ) ≤
      2500 * (capQ V (paramρ V ((b + 3 : ℕ) : ℝ)) (paramc V ((b + 3 : ℕ) : ℝ) (1 / 2)) : ℝ) := by
    exact_mod_cast capQ_onePercent_le V ((b + 3 : ℕ) : ℝ)
  have hlarge := AllPairs.capQ_public_le V hn (by positivity : (0 : ℝ) ≤ ((b + 3 : ℕ) : ℝ))
  have hbound : (reductionSparsifierBudget V ((b + 3 : ℕ) : ℝ) : ℝ) ≤
      (100000000 * (b + 11) * Fintype.card V * AllPairs.budgetLog (Fintype.card V) ^ 2 : ℕ) := by
    calc
      _ ≤ 2500 * (40000 * (((b + 3 : ℕ) : ℝ) + 8) * Fintype.card V *
          (AllPairs.budgetLog (Fintype.card V) : ℝ) ^ 2) :=
        hsmall.trans (mul_le_mul_of_nonneg_left hlarge (by norm_num))
      _ = _ := by push_cast; ring
  exact_mod_cast hbound

theorem sparsifierLog_le (n M : ℕ) : AllPairs.budgetLog n ≤ 2 * reductionLog n M := by
  have hL := reductionLog_one_le n M
  have h1 := Nat.clog_mono_right 2 (show 2 * n + 2 ≤ 2 * (n + M + 2) by omega)
  have h2 := binaryLog_mul_le 2 (n + M + 2)
  have ht : Nat.clog 2 2 = 1 := by decide
  unfold AllPairs.budgetLog reductionLog at *
  omega

theorem reductionSparsifierBudget_envelope (V : Type) [Fintype V]
    (hn : 1 ≤ Fintype.card V) (M b : ℕ) (Q : ℕ → ℕ) :
    reductionSparsifierBudget V ((b + 3 : ℕ) : ℝ) ≤
      parameterScale (Fintype.card V) M b ^ 4 * (Q (Fintype.card V) + Fintype.card V) := by
  let n := Fintype.card V
  let R := parameterScale n M b
  let L := reductionLog n M
  have hR : 400000000 ≤ R := parameterScale_large n M b
  have hC : parameterCoefficient b ≤ R := by
    simpa only [Nat.mul_one, R, parameterScale] using Nat.mul_le_mul_left (parameterCoefficient b) (reductionLog_one_le n M)
  have hb : b + 11 ≤ R := (show b + 11 ≤ parameterCoefficient b by unfold parameterCoefficient; omega).trans hC
  have hLR : L ≤ R := by
    have hcoef : 1 ≤ parameterCoefficient b := by unfold parameterCoefficient; omega
    simpa only [Nat.one_mul, R, parameterScale, L] using Nat.mul_le_mul_right L hcoef
  have hlog : AllPairs.budgetLog n ≤ 2 * R := (sparsifierLog_le n M).trans (Nat.mul_le_mul_left 2 hLR)
  calc
    _ ≤ 100000000 * (b + 11) * n * AllPairs.budgetLog n ^ 2 := reductionSparsifierBudget_le V hn b
    _ ≤ 100000000 * R * n * (2 * R) ^ 2 := by gcongr
    _ = 400000000 * R ^ 3 * n := by ring
    _ ≤ R * R ^ 3 * (Q n + n) := by gcongr; omega
    _ = _ := by ring

end
end CutQueryComplexity.GHReduction
