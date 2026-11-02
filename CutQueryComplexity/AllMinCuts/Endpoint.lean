import CutQueryComplexity.AllMinCuts.TwoStage

/-! # Deterministic reporting of all global minimum cuts (all-minima plan, M7)

`deterministic_all_mincuts_log3loglog2`: one deterministic cut-query decision tree per `n ≥ 2`,
selected before the graph, with cap `q = O(n (⌊√n⌋ + 1) L(n)³ L(L(n))²)` on every answer function
(`DTree.cost_le`). On the cut oracle of every nonnegative weighted graph on `Fin n`, including
graphs with zero minimum cut and isolated vertices, it returns `some out` where `out.value` is
`λ(G)` and `out.cuts` is exactly the set of all global minimum-cut shores (both `S` and `Sᶜ`).
The tree is `Comp.toDTree` of `allTwoStageAuto` at the public cap `allBudget n`; the honest-oracle
cost bound (`allTwoStageAuto_spec`) shows that compiled evaluation does not truncate.

Only oracle calls are charged. The family can be exponentially large (`2^n − 2` shores for the
zero graph); enumerating it from learned data costs no queries, and no polynomial running-time
or output-size claim is made.

`deterministic_all_mincuts_log3loglog2_real_log` states the cap with the natural logarithm:
`C n (⌊√n⌋ + 1) log(2n)³ log(6 log(2n))²`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllMinCuts

open Search Search.Comp DetMinCut

/-- **All global minimum cuts in `O(n^{3/2} log³ n (log log n)²)` deterministic cut queries.** -/
theorem deterministic_all_mincuts_log3loglog2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((DetMinCut.logL n : ℝ) ^ 3 *
            (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), ∃ out,
            D.eval G.cut = some out ∧ Correct G out := by
  refine ⟨allConstant + 1, by linarith [allConstant_pos], fun n hn => ?_⟩
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨allBudget n, allBudget_le hn,
    (allTwoStageAuto (V := Fin n) ⟨0, by omega⟩).toDTree (allBudget n),
    fun read => DTree.cost_le _ read, fun G => ?_⟩
  have hs := allTwoStageAuto_spec (V := Fin n) G (by simpa using hn) ⟨0, by omega⟩
  exact ⟨_, toDTree_eval _ _ (by simpa using hs.2), hs.1⟩

/-- **The all-minimum-cut cap in the paper's notation**: `O(n^{3/2} log³ n (log log n)²)`. -/
theorem deterministic_all_mincuts_log3loglog2_real_log :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), ∃ out,
            D.eval G.cut = some out ∧ Correct G out := by
  obtain ⟨C, hC, hall⟩ := deterministic_all_mincuts_log3loglog2
  refine ⟨C * 3 ^ 5, by positivity, fun n hn => ?_⟩
  obtain ⟨q, hq, D, hcost, hD⟩ := hall n hn
  refine ⟨q, hq.trans ?_, D, hcost, hD⟩
  have hL := TreeCutSparsifier.logL_le_real_log hn
  have hK := DetMinCut.logL_logL_le_real_log hn
  have hlog1 := TreeCutSparsifier.real_log_one hn
  have hlog6 : 0 ≤ Real.log (6 * Real.log (2 * (n : ℝ))) := by
    apply Real.log_nonneg; linarith
  have hL0 : (0 : ℝ) ≤ logL n := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ logL (logL n) := Nat.cast_nonneg _
  have hs : (0 : ℝ) ≤ (n : ℝ) * (Nat.sqrt n + 1) := by positivity
  have h3 : (logL n : ℝ) ^ 3 ≤ (3 * Real.log (2 * (n : ℝ))) ^ 3 := pow_le_pow_left₀ hL0 hL 3
  have h2 : (logL (logL n) : ℝ) ^ 2 ≤ (3 * Real.log (6 * Real.log (2 * (n : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ hK0 hK 2
  calc C * (n : ℝ) * (Nat.sqrt n + 1) * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2)
      ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * ((3 * Real.log (2 * (n : ℝ))) ^ 3 *
          (3 * Real.log (6 * Real.log (2 * (n : ℝ)))) ^ 2) := by
        gcongr
    _ = C * 3 ^ 5 * (n : ℝ) * (Nat.sqrt n + 1) *
          (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) := by ring

end CutQueryComplexity.AllMinCuts
