import CutQueryComplexity.TreeCutSparsifier.Main
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Theorem 5: learning a tree cut sparsifier

The deterministic decision tree is chosen from `n` and `α` before the graph.
Its query cap holds on all transcripts. On every nonnegative graph with positive
minimum cut it returns a safe partition and explicit canonical tree capacities,
with an all-cut approximation guarantee and at most eight times as many nodes.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CutQueryComplexity.TreeCutSparsifier

open DetMinCut Search Search.Comp

def queryConstant : ℝ := 8000 * discoveryConstant + 5

theorem budget_le {n : ℕ} {α : ℝ} (hn : 1 ≤ n) (hα : Admissible n α) :
    (budget n α : ℝ) ≤ queryConstant * ((n : ℝ)^2 / α) * (logL n : ℝ)^5 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα0 := admissible_pos hα
  have hα1 := (admissible_bounds hα).1
  have hαn : α ≤ n := by nlinarith [hα.2]
  have hL : (1 : ℝ) ≤ logL n := by exact_mod_cast one_le_logL' n
  have hL5 : (1 : ℝ) ≤ (logL n : ℝ)^5 := one_le_pow₀ hL
  have hL15 : (logL n : ℝ) ≤ (logL n : ℝ)^5 := by
    simpa using pow_le_pow_right₀ hL (show 1 ≤ 5 by norm_num)
  set Z : ℝ := (n : ℝ)^2 * (logL n : ℝ)^5 / α with hZ
  have hnα : (n : ℝ) * α ≤ Z := by
    rw [hZ, le_div_iff₀ hα0]
    calc (n : ℝ) * α * α = n * α^2 := by ring
      _ ≤ n * n := mul_le_mul_of_nonneg_left hα.2 (by positivity)
      _ ≤ n^2 * (logL n : ℝ)^5 := by nlinarith [sq_nonneg (n : ℝ)]
  have hnL : (n : ℝ) * logL n ≤ Z := by
    rw [hZ, le_div_iff₀ hα0]
    calc (n : ℝ) * logL n * α ≤ n * logL n * n := by gcongr
      _ = n^2 * (logL n : ℝ) := by ring
      _ ≤ n^2 * (logL n : ℝ)^5 := by gcongr
  have hnZ : (n : ℝ) ≤ Z := by nlinarith
  have hZ1 : 1 ≤ Z := hn1.trans hnZ
  have hc : (Nat.clog 2 n : ℝ) ≤ logL n := by exact_mod_cast clog_le_logL (le_refl n)
  have hcn : ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n ≤ 3 * Z := by
    push_cast
    have hfac : 2 * (Nat.clog 2 n : ℝ) + 1 ≤ 3 * logL n := by linarith
    have := mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hK : 2 * phaseK n α * n ≤ 8000 * discoveryConstant * Z := by
    have hD : 0 ≤ discoveryConstant := by norm_num [discoveryConstant]
    calc 2 * phaseK n α * n = 4000 * discoveryConstant * ((n : ℝ) * α + Z) := by
          unfold phaseK; rw [hZ]; ring
      _ ≤ 4000 * discoveryConstant * (Z + Z) := by gcongr
      _ = _ := by ring
  have hX : 0 ≤ (n : ℝ) + ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n + 2 * phaseK n α * n := by
    have := phaseK_pos hα
    positivity
  have hceil := Nat.ceil_lt_add_one hX
  unfold budget queryConstant
  have heq : (8000 * discoveryConstant + 5) * ((n : ℝ)^2 / α) * (logL n : ℝ)^5 =
      (8000 * discoveryConstant + 5) * Z := by rw [hZ]; ring
  rw [heq]
  nlinarith

/-- Theorem 5 with the library's integer logarithm. -/
theorem learn_tree_cut_sparsifier :
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ, Admissible n α →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) * (logL n : ℝ)^5 ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), 0 < mincutValue G →
          ∃ out, D.eval G.cut = some out ∧ Correct G α out := by
  refine ⟨queryConstant, by norm_num [queryConstant, discoveryConstant], fun n hn α hα => ?_⟩
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨budget n α, budget_le (by omega) hα, (learn α).toDTree (budget n α),
    fun read => DTree.cost_le _ read, fun G hpos => ?_⟩
  have hs := learn_spec (V := Fin n) (by simpa using hα) G (by simpa using hn) hpos
  refine ⟨(learn α).eval G.cut, ?_, hs.1⟩
  exact toDTree_eval _ _ (by simpa using hs.2)

theorem real_log_one {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.log (2 * (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  linarith [Real.exp_one_lt_three]

/-- Conversion from the integer logarithm to the paper's natural logarithm. -/
theorem logL_le_real_log {n : ℕ} (hn : 2 ≤ n) :
    (logL n : ℝ) ≤ 3 * Real.log (2 * (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ (2 * n : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * n)
  have hlog0 : 0 ≤ Real.log ((2 * n : ℕ) : ℝ) := Real.log_nonneg hnR
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hb : Real.logb 2 ((2 * n : ℕ) : ℝ) ≤ 2 * Real.log ((2 * n : ℕ) : ℝ) := by
    rw [Real.logb, div_le_iff₀ (by linarith : 0 < Real.log 2)]
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlog2.le)]
  have hc : (Nat.clog 2 (2 * n) : ℝ) ≤ Real.logb 2 ((2 * n : ℕ) : ℝ) + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hnR)).le
  rw [logL_eq (by omega)]
  push_cast at hb hc
  linarith [real_log_one hn]

/-- **Theorem 5**, in the paper's parameter range and query-bound notation. -/
theorem theorem5 :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * (Real.log (2 * (n : ℝ)))^4 ≤ α → α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) * (Real.log (2 * (n : ℝ)))^5 ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), 0 < mincutValue G →
          ∃ out, D.eval G.cut = some out ∧ Correct G α out := by
  obtain ⟨Cq, hCq, hall⟩ := learn_tree_cut_sparsifier
  refine ⟨2 * discoveryConstant * 3^4, Cq * 3^5,
    by norm_num [discoveryConstant], by positivity, fun n hn α hlo hhi => ?_⟩
  have hL := logL_le_real_log hn
  have hD : 0 < discoveryConstant := by norm_num [discoveryConstant]
  have hlower : 2 * discoveryConstant * (logL n : ℝ)^4 ≤ α := by
    calc _ ≤ 2 * discoveryConstant * (3 * Real.log (2 * (n : ℝ)))^4 := by gcongr
      _ = (2 * discoveryConstant * 3^4) * (Real.log (2 * (n : ℝ)))^4 := by ring
      _ ≤ α := hlo
  have hα0 : 0 ≤ α := by
    have : 0 ≤ 2 * discoveryConstant * (logL n : ℝ)^4 := by positivity
    linarith
  have hα : Admissible n α := ⟨hlower, by nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]⟩
  obtain ⟨q, hq, D, hcost, hcorrect⟩ := hall n hn α hα
  refine ⟨q, hq.trans ?_, D, hcost, hcorrect⟩
  have hapos := admissible_pos hα
  calc Cq * ((n : ℝ)^2 / α) * (logL n : ℝ)^5
      ≤ Cq * ((n : ℝ)^2 / α) * (3 * Real.log (2 * (n : ℝ)))^5 := by gcongr
    _ = (Cq * 3^5) * ((n : ℝ)^2 / α) * (Real.log (2 * (n : ℝ)))^5 := by ring

end CutQueryComplexity.TreeCutSparsifier
