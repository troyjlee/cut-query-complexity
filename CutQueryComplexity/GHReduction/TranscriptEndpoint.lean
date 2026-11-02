import CutQueryComplexity.GHReduction.Main
import CutQueryComplexity.GHReduction.TranscriptCap

/-! # The weighted reduction's cap on arbitrary answer transcripts

The same public program as `Main` has a hard cap against arbitrary randomized
transcript-dependent answers. Its graph-correctness claim retains the ordinary
honest weighted cut oracle. These two claims concern the very same program;
no successful-execution premise is used for the cost bound.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped ENNReal
open WeightedGraph Probability

attribute [local irreducible] RTree reductionPolynomialConstant confidenceBudget

theorem weightedGHProgram_transcript_cost {n M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hn : 2 ≤ n) (b : ℕ)
    (answer : TranscriptOracle.AnswerPolicy (Finset (Fin n)) ℝ)
    (history : List (Finset (Fin n) × ℝ)) {out : Option (CutTree (Fin n)) × ℕ}
    (hout : out ∈ (TranscriptOracle.run answer (weightedGHProgram family hn b) history).support) :
    out.2 ≤ weightedGHBudget n M b Q :=
  TranscriptOracle.cost_le _ answer history hout

theorem weightedGHProgram_transcript_fixed {n M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hn : 2 ≤ n) (b : ℕ)
    (read : Finset (Fin n) → ℝ) (history : List (Finset (Fin n) × ℝ)) :
    TranscriptOracle.run (fun _ i => PMF.pure (read i)) (weightedGHProgram family hn b) history =
      RTree.run read (weightedGHProgram family hn b) :=
  TranscriptOracle.run_fixed _ read history

/-- The universal cap includes all randomized response policies and all
starting histories. The one chosen program still returns a witnessed GH tree
with the stated probability for every promised hidden graph. -/
theorem exists_weighted_gh_reduction_transcript {n M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) (weightedGHBudget n M b Q),
      (∀ answer history, ∀ out ∈ (TranscriptOracle.run answer program history).support,
        out.2 ≤ weightedGHBudget n M b Q) ∧
      ∀ G : WeightedGraph (Fin n), InputPromise M G →
        mass (program.eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
          (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  exact ⟨weightedGHProgram family hn b,
    fun answer history _ hout => weightedGHProgram_transcript_cost family hn b answer history hout,
    fun G hG => weightedGHProgram_failure family hQ hn b G hG⟩

#print axioms weightedGHProgram_transcript_cost
#print axioms weightedGHProgram_transcript_fixed
#print axioms exists_weighted_gh_reduction_transcript

end
end CutQueryComplexity.GHReduction
