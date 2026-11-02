import CutQueryComplexity.GHReduction.PolynomialBudget

/-! # Relative weighted Gomory-Hu cut-query reduction

One public bounded randomized program is chosen before the hidden graph. Its
only algorithmic input is the exact canonical weighted s-t family on actual
compact instance sizes. The fixed total-capacity promise is preserved by every
weighted contraction. The output has fundamental minimum-cut shores and exact
weights, and hence supplies all-pairs bottleneck values and minimum shores.

Its public statement and axiom audit are in `CutQueryComplexityChecks/Endpoints.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability

attribute [local irreducible] RTree reductionPolynomialConstant confidenceBudget

def weightedGHBudget (n M b : ℕ) (Q : ℕ → ℕ) : ℕ :=
  reductionPolynomialConstant b * (n + Q n) * (1 + Nat.clog 2 (n + M + 2)) ^ 22

def weightedGHProgram {n M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hn : 2 ≤ n) (b : ℕ) :
    RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) (weightedGHBudget n M b Q) :=
  (confidenceReduction family b (⟨0, by omega⟩ : Fin n)).weaken (by
    simpa only [Fintype.card_fin, weightedGHBudget] using
      confidenceBudget_polylog (Fin n) (by simpa only [Fintype.card_fin] using (show 1 ≤ n by omega)) M b Q)

theorem weightedGHProgram_cost {n M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hn : 2 ≤ n) (b : ℕ) (read : Finset (Fin n) → ℝ)
    {out : Option (CutTree (Fin n)) × ℕ}
    (hout : out ∈ (RTree.run read (weightedGHProgram family hn b)).support) :
    out.2 ≤ weightedGHBudget n M b Q := RTree.cost_le _ read hout

theorem weightedGHProgram_failure {n M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) (G : WeightedGraph (Fin n))
    (hG : InputPromise M G) :
    mass ((weightedGHProgram family hn b).eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
      (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  rw [weightedGHProgram, RTree.eval_weaken]
  simpa only [Fintype.card_fin] using confidenceReduction_failure family
    (by simpa only [Fintype.card_fin] using hQ) b (⟨0, by omega⟩ : Fin n) G hG

def AllPairsTreeSuccess {V : Type} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (output : Option (CutTree V)) : Prop :=
  ∃ tree, output = some tree ∧ ∀ s t : V, s ≠ t →
    ∃ v ∈ pathEdges tree.topology s t,
      (∀ e ∈ pathEdges tree.topology s t, tree.weight v ≤ tree.weight e) ∧
      IsSTMinCut G s t (pathShore tree.topology s v) ∧
      G.cut (pathShore tree.topology s v) = tree.weight v

theorem weightedGHProgram_allPairs {n M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) (G : WeightedGraph (Fin n))
    (hG : InputPromise M G) :
    mass ((weightedGHProgram family hn b).eval G.cut) (fun output => ¬AllPairsTreeSuccess G output) ≤
      (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  apply le_trans (mass_mono _ ?_) (weightedGHProgram_failure family hQ hn b G hG)
  intro output hbad hgood
  exact hbad (hgood.allPairs G)

/-- Quantifier order is part of the conclusion: one public program, then all
promised hidden graphs. There is no guide solver, approximation oracle, outer
reduction, or successful-assembly field among the hypotheses. -/
theorem exists_weighted_gh_reduction {n M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) (weightedGHBudget n M b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ weightedGHBudget n M b Q) ∧
      ∀ G : WeightedGraph (Fin n), InputPromise M G →
        mass (program.eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
          (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  exact ⟨weightedGHProgram family hn b,
    fun read _ hout => weightedGHProgram_cost family hn b read hout,
    fun G hG => weightedGHProgram_failure family hQ hn b G hG⟩

#print axioms weightedGHProgram_cost
#print axioms weightedGHProgram_failure
#print axioms weightedGHProgram_allPairs
#print axioms exists_weighted_gh_reduction

end
end CutQueryComplexity.GHReduction
