import CutQueryComplexity.TreeCutSparsifier.Endpoint
import CutQueryComplexity.SupportForest.Endpoint

/-! # Theorem 5 without the positivity promise

`theorem5` assumes `0 < mincutValue G`. Running the positive-support forest first removes the
promise: `unconditional α x₀` runs the forest program, returns a proper shore of cut value zero
when the support is disconnected (`Sum.inl`), and otherwise runs `learn α` (`Sum.inr`), whose
promise is then satisfied by `support_connected_iff_pos`. The cap is
`forestBudget n + budget n α`, still `O(n² log⁵(2n) / α)` (`theorem5_or_zero_cut`).
-/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open DetMinCut Search Search.Comp SupportForest

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Run the forest routine, then either report a zero proper shore or learn the sparsifier. -/
noncomputable def unconditional [Nonempty V] (α : ℝ) (x₀ : V) :
    Comp (Finset V) ℝ (Finset V ⊕ Output V) :=
  (SupportForest.program (V := V)).bind fun out =>
    match out.test x₀ with
    | none => (learn α).map Sum.inr
    | some S => Comp.pure (Sum.inl S)

theorem unconditional_spec [Nonempty V] {α : ℝ} (hα : Admissible (Fintype.card V) α)
    (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (x₀ : V) :
    Sum.elim (fun S => ProperShore S ∧ G.cut S = 0) (Correct G α)
      ((unconditional α x₀).eval G.cut) ∧
    (unconditional α x₀).cost G.cut ≤ forestBudget (Fintype.card V) + budget (Fintype.card V) α := by
  obtain ⟨hc, hcost⟩ := SupportForest.program_spec (V := V) G
  simp only [unconditional, eval_bind, cost_bind]
  by_cases hconn : G.support.Connected
  · rw [hc.test_of_connected x₀ hconn]
    have hpos : 0 < mincutValue G := (support_connected_iff_pos G hn).mp hconn
    obtain ⟨hl, hlcost⟩ := learn_spec hα G hn hpos
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

/-- The forest cap is within the Theorem 5 cap: `forestBudget n ≤ 7 (n² / α) L(n)⁵`. -/
theorem forestBudget_le_budget {n : ℕ} {α : ℝ} (hn : 1 ≤ n) (hα : Admissible n α) :
    (forestBudget n : ℝ) ≤ 7 * ((n : ℝ)^2 / α) * (logL n : ℝ)^5 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα0 := admissible_pos hα
  have hαn : α ≤ n := by nlinarith [hα.2]
  have hL : (1 : ℝ) ≤ logL n := by exact_mod_cast one_le_logL' n
  have hL5 : (logL n : ℝ) ≤ (logL n : ℝ)^5 := by
    simpa using pow_le_pow_right₀ hL (show 1 ≤ 5 by norm_num)
  have h1 : (forestBudget n : ℝ) ≤ 7 * n * logL n := by
    exact_mod_cast forestBudget_le_linear_log n
  have h2 : (n : ℝ) * logL n ≤ (n : ℝ)^2 / α * (logL n : ℝ)^5 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hα0]
    calc (n : ℝ) * logL n * α ≤ n * logL n * n := by gcongr
      _ = (n : ℝ)^2 * logL n := by ring
      _ ≤ (n : ℝ)^2 * (logL n : ℝ)^5 := by gcongr
  linarith

/-- **Theorem 5 without the positivity promise.** One decision tree per `n ≥ 2` and `α` in
the paper's range, with cap `O(n² log⁵(2n) / α)`, that on every graph returns either a proper
shore of cut value zero (so the minimum-cut value is zero) or a correct tree cut sparsifier
output. -/
theorem theorem5_or_zero_cut :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * (Real.log (2 * (n : ℝ)))^4 ≤ α → α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) * (Real.log (2 * (n : ℝ)))^5 ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n) ⊕ Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), ∃ res, D.eval G.cut = some res ∧
          Sum.elim (fun S => ProperShore S ∧ G.cut S = 0) (Correct G α) res := by
  refine ⟨2 * discoveryConstant * 3^4, (queryConstant + 7) * 3^5,
    by norm_num [discoveryConstant], by norm_num [queryConstant, discoveryConstant],
    fun n hn α hlo hhi => ?_⟩
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
  have hapos := admissible_pos hα
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨forestBudget n + budget n α, ?_,
    (unconditional (V := Fin n) α ⟨0, by omega⟩).toDTree (forestBudget n + budget n α),
    fun read => DTree.cost_le _ read, fun G => ?_⟩
  · have h1 := forestBudget_le_budget (by omega) hα
    have h2 := budget_le (by omega) hα
    have hq : (queryConstant + 7) * ((n : ℝ)^2 / α) * (logL n : ℝ)^5 ≤
        ((queryConstant + 7) * 3^5) * ((n : ℝ)^2 / α) * (Real.log (2 * (n : ℝ)))^5 := by
      have hqc : 0 ≤ queryConstant + 7 := by norm_num [queryConstant, discoveryConstant]
      calc (queryConstant + 7) * ((n : ℝ)^2 / α) * (logL n : ℝ)^5
          ≤ (queryConstant + 7) * ((n : ℝ)^2 / α) * (3 * Real.log (2 * (n : ℝ)))^5 := by gcongr
        _ = _ := by ring
    push_cast
    linarith
  · have hs := unconditional_spec (V := Fin n) (by simpa using hα) G (by simpa using hn)
      ⟨0, by omega⟩
    refine ⟨_, toDTree_eval _ _ ?_, hs.1⟩
    simpa using hs.2

end CutQueryComplexity.TreeCutSparsifier
