import CutQueryComplexity.TreeCutSparsifier.MainLL
import CutQueryComplexity.TreeCutSparsifier.Endpoint
import CutQueryComplexity.DetMinCut.UnconditionalLogLog

/-! # Theorem 5 with the Räcke–Shah quality (log-log plan, M5)

`learn_tree_cut_sparsifier_LL` and `theorem5LL` are `learn_tree_cut_sparsifier` and
`theorem5` with the learning stage re-instantiated on the Räcke–Shah hierarchy: for
`n ≥ 2` and `C log(2n)² log(6 log(2n))² ≤ α ≤ √n`, one deterministic decision tree uses
`O((n² / α) log(2n)³ log(6 log(2n))²)` cut queries and, on every nonnegative weighted graph
with positive minimum-cut value, returns a safe partition and an explicit `α`-tree cut
sparsifier of its quotient (`Correct`, unchanged). The log-five theorems are unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CutQueryComplexity.TreeCutSparsifier

open DetMinCut Search Search.Comp
open Hierarchy.RackeShah (KK)

def queryConstantLL : ℝ := 8000 * discoveryConstantLL + 5

theorem budgetLL_le {n : ℕ} {α : ℝ} (hn : 1 ≤ n) (hα : AdmissibleLL n α) :
    (budgetLL n α : ℝ) ≤
      queryConstantLL * ((n : ℝ)^2 / α) * ((logL n : ℝ)^3 * (KK n : ℝ)^2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα0 := admissibleLL_pos hα
  have hα1 := (admissibleLL_bounds hα).1
  have hαn : α ≤ n := by nlinarith [hα.2]
  have hL : (1 : ℝ) ≤ logL n := by exact_mod_cast one_le_logL' n
  have hK : (1 : ℝ) ≤ KK n := by exact_mod_cast one_le_KK' n
  set P : ℝ := (logL n : ℝ)^3 * (KK n : ℝ)^2 with hP
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL) (one_le_pow₀ hK)
  have hLP : (logL n : ℝ) ≤ P := by
    have h13 : (logL n : ℝ) ≤ (logL n : ℝ)^3 := by
      simpa using pow_le_pow_right₀ hL (show 1 ≤ 3 by norm_num)
    have hK2 : 1 ≤ (KK n : ℝ)^2 := one_le_pow₀ hK
    have h3 : 0 ≤ (logL n : ℝ)^3 := by positivity
    rw [hP]
    nlinarith
  set Z : ℝ := (n : ℝ)^2 * P / α with hZ
  have hnα : (n : ℝ) * α ≤ Z := by
    rw [hZ, le_div_iff₀ hα0]
    calc (n : ℝ) * α * α = n * α^2 := by ring
      _ ≤ n * n := mul_le_mul_of_nonneg_left hα.2 (by positivity)
      _ ≤ n^2 * P := by nlinarith [sq_nonneg (n : ℝ)]
  have hnL : (n : ℝ) * logL n ≤ Z := by
    rw [hZ, le_div_iff₀ hα0]
    calc (n : ℝ) * logL n * α ≤ n * logL n * n := by gcongr
      _ = n^2 * (logL n : ℝ) := by ring
      _ ≤ n^2 * P := by gcongr
  have hnZ : (n : ℝ) ≤ Z := by nlinarith
  have hZ1 : 1 ≤ Z := hn1.trans hnZ
  have hc : (Nat.clog 2 n : ℝ) ≤ logL n := by exact_mod_cast clog_le_logL (le_refl n)
  have hcn : ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n ≤ 3 * Z := by
    push_cast
    have hfac : 2 * (Nat.clog 2 n : ℝ) + 1 ≤ 3 * logL n := by linarith
    have := mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hKc : 2 * phaseCoefLL n α * n ≤ 8000 * discoveryConstantLL * Z := by
    have hD : 0 ≤ discoveryConstantLL := by norm_num [discoveryConstantLL]
    calc 2 * phaseCoefLL n α * n = 4000 * discoveryConstantLL * ((n : ℝ) * α + Z) := by
          unfold phaseCoefLL; rw [hZ, hP]; ring
      _ ≤ 4000 * discoveryConstantLL * (Z + Z) := by gcongr
      _ = _ := by ring
  have hX : 0 ≤ (n : ℝ) + ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ) * n + 2 * phaseCoefLL n α * n := by
    have := phaseCoefLL_pos hα
    positivity
  have hceil := Nat.ceil_lt_add_one hX
  unfold budgetLL queryConstantLL
  have heq : (8000 * discoveryConstantLL + 5) * ((n : ℝ)^2 / α) * P =
      (8000 * discoveryConstantLL + 5) * Z := by rw [hZ]; ring
  rw [heq]
  nlinarith

/-- Theorem 5 with the Räcke–Shah quality and the library's integer logarithm. -/
theorem learn_tree_cut_sparsifier_LL :
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ, AdmissibleLL n α →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) * ((logL n : ℝ)^3 * (logL (logL n) : ℝ)^2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), 0 < mincutValue G →
          ∃ out, D.eval G.cut = some out ∧ Correct G α out := by
  refine ⟨queryConstantLL, by norm_num [queryConstantLL, discoveryConstantLL],
    fun n hn α hα => ?_⟩
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨budgetLL n α, budgetLL_le (by omega) hα, (learnLL α).toDTree (budgetLL n α),
    fun read => DTree.cost_le _ read, fun G hpos => ?_⟩
  have hs := learnLL_spec (V := Fin n) (by simpa using hα) G (by simpa using hn) hpos
  refine ⟨(learnLL α).eval G.cut, ?_, hs.1⟩
  exact toDTree_eval _ _ (by simpa using hs.2)

/-- The log-log quality unit in the paper's notation. -/
theorem unitLL_le_real_log {n : ℕ} (hn : 2 ≤ n) :
    unitLL n ≤ 3^4 * ((Real.log (2 * (n : ℝ)))^2 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) := by
  have hL := logL_le_real_log hn
  have hK : (KK n : ℝ) ≤ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) := by
    rw [KK_eq]; exact logL_logL_le_real_log hn
  unfold unitLL
  calc (logL n : ℝ)^2 * (KK n : ℝ)^2
      ≤ (3 * Real.log (2 * (n : ℝ)))^2 * (3 * Real.log (6 * Real.log (2 * (n : ℝ))))^2 := by
        gcongr
    _ = _ := by ring

/-- **Theorem 5 with the Räcke–Shah quality**, in the paper's parameter range and query-bound
notation: for `C log(2n)² log(6 log(2n))² ≤ α ≤ √n`, the cap is
`Cq (n² / α) log(2n)³ log(6 log(2n))²`. -/
theorem theorem5LL :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * ((Real.log (2 * (n : ℝ)))^2 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ≤ α →
        α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) *
          ((Real.log (2 * (n : ℝ)))^3 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), 0 < mincutValue G →
          ∃ out, D.eval G.cut = some out ∧ Correct G α out := by
  obtain ⟨Cq, hCq, hall⟩ := learn_tree_cut_sparsifier_LL
  refine ⟨2 * discoveryConstantLL * 3^4, Cq * 3^5,
    by norm_num [discoveryConstantLL], by positivity, fun n hn α hlo hhi => ?_⟩
  have hL := logL_le_real_log hn
  have hK : (logL (logL n) : ℝ) ≤ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) :=
    logL_logL_le_real_log hn
  have hD : 0 < discoveryConstantLL := by norm_num [discoveryConstantLL]
  have hlower : 2 * discoveryConstantLL * unitLL n ≤ α := by
    calc _ ≤ 2 * discoveryConstantLL * (3^4 *
          ((Real.log (2 * (n : ℝ)))^2 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2)) := by
          gcongr; exact unitLL_le_real_log hn
      _ = (2 * discoveryConstantLL * 3^4) *
          ((Real.log (2 * (n : ℝ)))^2 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) := by ring
      _ ≤ α := hlo
  have hα0 : 0 ≤ α := by
    have : 0 ≤ 2 * discoveryConstantLL * unitLL n := by
      have := unitLL_pos n
      positivity
    linarith
  have hα : AdmissibleLL n α := ⟨hlower, by nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]⟩
  obtain ⟨q, hq, D, hcost, hcorrect⟩ := hall n hn α hα
  refine ⟨q, hq.trans ?_, D, hcost, hcorrect⟩
  have hapos := admissibleLL_pos hα
  have hlog1 := real_log_one hn
  calc Cq * ((n : ℝ)^2 / α) * ((logL n : ℝ)^3 * (logL (logL n) : ℝ)^2)
      ≤ Cq * ((n : ℝ)^2 / α) * ((3 * Real.log (2 * (n : ℝ)))^3 *
          (3 * Real.log (6 * Real.log (2 * (n : ℝ))))^2) := by gcongr
    _ = (Cq * 3^5) * ((n : ℝ)^2 / α) *
          ((Real.log (2 * (n : ℝ)))^3 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) := by ring

end CutQueryComplexity.TreeCutSparsifier
