import CutQueryComplexity.TreeCutSparsifier.EndpointLL
import CutQueryComplexity.TreeCutSparsifier.Unconditional

/-! # Theorem 5 with the Räcke–Shah quality, without the positivity promise

`unconditionalLL α x₀` runs the positive-support forest program and then either returns a
proper shore of cut value zero or runs `learnLL α`; `theorem5LL_or_zero_cut` is
`theorem5_or_zero_cut` with the log-log cap `O((n² / α) log(2n)³ log(6 log(2n))²)`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open DetMinCut Search Search.Comp SupportForest
open Hierarchy.RackeShah (KK)

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Run the forest routine, then either report a zero proper shore or learn the sparsifier. -/
noncomputable def unconditionalLL [Nonempty V] (α : ℝ) (x₀ : V) :
    Comp (Finset V) ℝ (Finset V ⊕ Output V) :=
  (SupportForest.program (V := V)).bind fun out =>
    match out.test x₀ with
    | none => (learnLL α).map Sum.inr
    | some S => Comp.pure (Sum.inl S)

theorem unconditionalLL_spec [Nonempty V] {α : ℝ} (hα : AdmissibleLL (Fintype.card V) α)
    (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (x₀ : V) :
    Sum.elim (fun S => ProperShore S ∧ G.cut S = 0) (Correct G α)
      ((unconditionalLL α x₀).eval G.cut) ∧
    (unconditionalLL α x₀).cost G.cut ≤
      forestBudget (Fintype.card V) + budgetLL (Fintype.card V) α := by
  obtain ⟨hc, hcost⟩ := SupportForest.program_spec (V := V) G
  simp only [unconditionalLL, eval_bind, cost_bind]
  by_cases hconn : G.support.Connected
  · rw [hc.test_of_connected x₀ hconn]
    have hpos : 0 < mincutValue G := (support_connected_iff_pos G hn).mp hconn
    obtain ⟨hl, hlcost⟩ := learnLL_spec hα G hn hpos
    simp only [eval_map, cost_map, Sum.elim_inr]
    refine ⟨hl, ?_⟩
    unfold forestBudget
    omega
  · obtain ⟨S, hS, hprop, hzero⟩ := hc.test_of_not_connected x₀ hconn
    rw [hS]
    simp only [eval_pure, cost_pure, Sum.elim_inl, add_zero]
    refine ⟨⟨hprop, hzero⟩, ?_⟩
    unfold forestBudget
    omega

/-- The forest cap is within the log-log Theorem 5 cap. -/
theorem forestBudget_le_budgetLL {n : ℕ} {α : ℝ} (hn : 1 ≤ n) (hα : AdmissibleLL n α) :
    (forestBudget n : ℝ) ≤ 7 * ((n : ℝ)^2 / α) * ((logL n : ℝ)^3 * (KK n : ℝ)^2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα0 := admissibleLL_pos hα
  have hαn : α ≤ n := by nlinarith [hα.2]
  have hL : (1 : ℝ) ≤ logL n := by exact_mod_cast one_le_logL' n
  have hK : (1 : ℝ) ≤ KK n := by exact_mod_cast one_le_KK' n
  have hLP : (logL n : ℝ) ≤ (logL n : ℝ)^3 * (KK n : ℝ)^2 := by
    have h13 : (logL n : ℝ) ≤ (logL n : ℝ)^3 := by
      simpa using pow_le_pow_right₀ hL (show 1 ≤ 3 by norm_num)
    have hK2 : 1 ≤ (KK n : ℝ)^2 := one_le_pow₀ hK
    have h3 : 0 ≤ (logL n : ℝ)^3 := by positivity
    nlinarith
  have h1 : (forestBudget n : ℝ) ≤ 7 * n * logL n := by
    exact_mod_cast forestBudget_le_linear_log n
  have h2 : (n : ℝ) * logL n ≤ (n : ℝ)^2 / α * ((logL n : ℝ)^3 * (KK n : ℝ)^2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hα0]
    calc (n : ℝ) * logL n * α ≤ n * logL n * n := by gcongr
      _ = (n : ℝ)^2 * logL n := by ring
      _ ≤ (n : ℝ)^2 * ((logL n : ℝ)^3 * (KK n : ℝ)^2) := by gcongr
  linarith

/-- **Theorem 5 with the Räcke–Shah quality, without the positivity promise.** -/
theorem theorem5LL_or_zero_cut :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * ((Real.log (2 * (n : ℝ)))^2 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ≤ α →
        α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) *
          ((Real.log (2 * (n : ℝ)))^3 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n) ⊕ Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), ∃ res, D.eval G.cut = some res ∧
          Sum.elim (fun S => ProperShore S ∧ G.cut S = 0) (Correct G α) res := by
  refine ⟨2 * discoveryConstantLL * 3^4, (queryConstantLL + 7) * 3^5,
    by norm_num [discoveryConstantLL], by norm_num [queryConstantLL, discoveryConstantLL],
    fun n hn α hlo hhi => ?_⟩
  have hL := logL_le_real_log hn
  have hK : (KK n : ℝ) ≤ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) := by
    rw [KK_eq]; exact logL_logL_le_real_log hn
  have hlog1 := real_log_one hn
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
  have hapos := admissibleLL_pos hα
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨forestBudget n + budgetLL n α, ?_,
    (unconditionalLL (V := Fin n) α ⟨0, by omega⟩).toDTree (forestBudget n + budgetLL n α),
    fun read => DTree.cost_le _ read, fun G => ?_⟩
  · have h1 := forestBudget_le_budgetLL (by omega) hα
    have h2 := budgetLL_le (by omega) hα
    have hq : (queryConstantLL + 7) * ((n : ℝ)^2 / α) * ((logL n : ℝ)^3 * (KK n : ℝ)^2) ≤
        ((queryConstantLL + 7) * 3^5) * ((n : ℝ)^2 / α) *
          ((Real.log (2 * (n : ℝ)))^3 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) := by
      have hqc : 0 ≤ queryConstantLL + 7 := by norm_num [queryConstantLL, discoveryConstantLL]
      calc (queryConstantLL + 7) * ((n : ℝ)^2 / α) * ((logL n : ℝ)^3 * (KK n : ℝ)^2)
          ≤ (queryConstantLL + 7) * ((n : ℝ)^2 / α) * ((3 * Real.log (2 * (n : ℝ)))^3 *
              (3 * Real.log (6 * Real.log (2 * (n : ℝ))))^2) := by gcongr
        _ = _ := by ring
    push_cast
    linarith
  · have hs := unconditionalLL_spec (V := Fin n) (by simpa using hα) G (by simpa using hn)
      ⟨0, by omega⟩
    refine ⟨_, toDTree_eval _ _ ?_, hs.1⟩
    simpa using hs.2

end CutQueryComplexity.TreeCutSparsifier
