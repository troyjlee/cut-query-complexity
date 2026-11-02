import CutQueryComplexity.GHReduction.Randomized.Frontier
import CutQueryComplexity.GHReduction.Randomized.Target

/-! # Phase 4: the Gomory-Hu reduction with a randomized s-t family

The public program runs the call-language reduction `Twin.weightedGHProgram`
at the amplified charge `Q' k = r (Q k + k)`, with
`r = amplificationRounds n M b Q`, and answers each call with a fresh run of the
amplified family. Its budget index is `randomizedGHBudget n M b Q`.

Failure, on a promised graph:

* G2 (`CallTree.mass_interpRand_le`) bounds it by the failure of the ideal law
  plus `3^{-r}` times the budget, since the amplified family fails with
  probability at most `3^{-r}` per call;
* the ideal law is the law of the deterministic `weightedGHProgram` run with
  the reference family (`Twin.weightedGHProgram_eq`), whose failure is at most
  `(n+2)^{-b}` (`weightedGHProgram_failure`);
* `amplification_slack` bounds the second term by `(n+2)^{-b}`.

`randomizedGHTarget` proves `RandomizedGHTarget`, and `unweightedAllPairsTarget`
the all-pairs specialization to unweighted graphs. The deterministic theorem is
the zero-error case (`exists_weighted_gh_reduction_via_calls`), with its own
budget.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability

attribute [local irreducible] RTree reductionPolynomialConstant confidenceBudget

/-- The public randomized reduction. -/
def randomizedGHProgram {n M : ℕ} {Q : ℕ → ℕ} (family : RandomCanonicalSTFamily M Q)
    (hn : 2 ≤ n) (b : ℕ) :
    RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) (randomizedGHBudget n M b Q) :=
  CallTree.interpRand (family.program.amplify (amplificationRounds n M b Q))
    (Twin.weightedGHProgram M (amplifiedCost (amplificationRounds n M b Q) Q) hn b)

theorem randomizedGHProgram_cost {n M : ℕ} {Q : ℕ → ℕ} (family : RandomCanonicalSTFamily M Q)
    (hn : 2 ≤ n) (b : ℕ) (read : Finset (Fin n) → ℝ) {out : Option (CutTree (Fin n)) × ℕ}
    (hout : out ∈ (RTree.run read (randomizedGHProgram family hn b)).support) :
    out.2 ≤ randomizedGHBudget n M b Q := RTree.cost_le _ read hout

/-- Failure of the ideal law plus the union bound over the calls. -/
theorem randomizedGHProgram_failure_le {n M : ℕ} {Q : ℕ → ℕ}
    (family : RandomCanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ)
    (G : WeightedGraph (Fin n)) (hG : InputPromise M G) (Bad : Option (CutTree (Fin n)) → Prop) :
    mass ((randomizedGHProgram family hn b).eval G.cut) Bad ≤
      mass ((weightedGHProgram (refFamily M) hn b).eval G.cut) Bad +
        (3⁻¹ : ℝ≥0∞) ^ amplificationRounds n M b Q * (randomizedGHBudget n M b Q : ℝ≥0∞) := by
  have hr : 1 ≤ amplificationRounds n M b Q := by
    simp only [amplificationRounds]
    omega
  have h := CallTree.mass_interpRand_le (family.amplify_failsAtMost (amplificationRounds n M b Q))
    (fun k hk => one_le_amplifiedCost hr Q hk) G hG
    (Twin.weightedGHProgram M (amplifiedCost (amplificationRounds n M b Q) Q) hn b) Bad
  rwa [Twin.weightedGHProgram_eq (refFamily M) (sizeRegular_amplifiedCost hQ _)
    (sizeRegular_refCost n) hn b G hG] at h

theorem randomizedGHProgram_failure {n M : ℕ} {Q : ℕ → ℕ}
    (family : RandomCanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ)
    (G : WeightedGraph (Fin n)) (hG : InputPromise M G) :
    mass ((randomizedGHProgram family hn b).eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
      2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  calc
    _ ≤ _ := randomizedGHProgram_failure_le family hQ hn b G hG _
    _ ≤ (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b :=
      add_le_add (weightedGHProgram_failure (refFamily M) (sizeRegular_refCost n) hn b G hG)
        (amplification_slack n M b Q)
    _ = _ := by ring

theorem randomizedGHProgram_allPairs {n M : ℕ} {Q : ℕ → ℕ}
    (family : RandomCanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ)
    (G : WeightedGraph (Fin n)) (hG : InputPromise M G) :
    mass ((randomizedGHProgram family hn b).eval G.cut) (fun output => ¬AllPairsTreeSuccess G output) ≤
      2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  apply le_trans (mass_mono _ ?_) (randomizedGHProgram_failure family hQ hn b G hG)
  intro output hbad hgood
  exact hbad (hgood.allPairs G)

/-- The Gomory-Hu reduction with a randomized canonical s-t family: one public
program, chosen before the graph, with budget `randomizedGHBudget n M b Q`; on
every graph with integral weights of total at most `M` it returns a Gomory-Hu
tree except with probability at most `2 (n+2)^{-b}`. -/
theorem exists_randomized_gh_reduction {n M : ℕ} {Q : ℕ → ℕ}
    (family : RandomCanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) (randomizedGHBudget n M b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ randomizedGHBudget n M b Q) ∧
      ∀ G : WeightedGraph (Fin n), InputPromise M G →
        mass (program.eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
          2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b :=
  ⟨randomizedGHProgram family hn b, fun read _ hout => randomizedGHProgram_cost family hn b read hout,
    fun G hG => randomizedGHProgram_failure family hQ hn b G hG⟩

/-- The Phase 0 target holds. -/
theorem randomizedGHTarget : RandomizedGHTarget :=
  fun _ _ _ family hQ hn b => exists_randomized_gh_reduction family hQ hn b

/-- All-pairs minimum cuts of unweighted graphs from a randomized canonical s-t
family on weighted graphs of edge weight at most `n * n`. -/
theorem unweightedAllPairsTarget : UnweightedAllPairsTarget :=
  unweightedAllPairs_of_randomizedGH randomizedGHTarget

/-- `unweightedAllPairsTarget`, spelled out. -/
theorem exists_randomized_unweighted_allPairs {n : ℕ} {Q : ℕ → ℕ}
    (family : RandomCanonicalSTFamily (n * n) Q) (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n)))
        (randomizedGHBudget n (n * n) b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support,
        out.2 ≤ randomizedGHBudget n (n * n) b Q) ∧
      ∀ G : WeightedGraph (Fin n), AllPairsAudit.Unweighted G →
        mass (program.eval G.cut) (fun output => ¬AllPairsTreeSuccess G output) ≤
          2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b :=
  unweightedAllPairsTarget n Q family hQ hn b

/-- The deterministic reduction as the zero-error case: an exact family, run
through the call language, gives the deterministic program's law, with the
deterministic budget. -/
theorem exists_weighted_gh_reduction_via_calls {n M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) (weightedGHBudget n M b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ weightedGHBudget n M b Q) ∧
      ∀ G : WeightedGraph (Fin n), InputPromise M G →
        mass (program.eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
          (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  refine ⟨CallTree.interpRand family.toRandom.program (Twin.weightedGHProgram M Q hn b),
    fun read _ hout => RTree.cost_le _ read hout, fun G hG => ?_⟩
  rw [CallTree.eval_interpRand_of_exact family.toRandom_failsAtMost_zero G hG,
    Twin.weightedGHProgram_eq family hQ hQ hn b G hG]
  exact weightedGHProgram_failure family hQ hn b G hG

end
end CutQueryComplexity.GHReduction.Randomized
