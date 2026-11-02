import CutQueryComplexity.GHReduction.GuideOneBudget

/-! # A witnessed, hard-capped one-respecting endpoint

The bounded decision tree is chosen before the hidden graph. It reports failure
if its query cap is exhausted, so every oracle-answer history obeys the same
budget. The repaired aggregate-cost theorem shows that exhaustion does not occur
on a promised weighted graph. This is the `k = 1` component used by the
weighted Gomory–Hu reduction.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def guideOneBudget (Q : ℕ → ℕ) (T : GuideTree V N) : ℕ :=
  (10 + 2 * Nat.clog 2 (T.real.card + 1) * (Nat.clog 2 (Fintype.card V) + 23)) *
    (Q (Fintype.card V) + Fintype.card V)

def guideOneTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q) (T : GuideTree V N) :
    DTree (Finset V) ℝ (Option (V → Option (CutCandidate V))) (guideOneBudget Q T) :=
  Prog.toDTree (guideOneProgram family (Nat.clog 2 (T.real.card + 1)) T) (guideOneBudget Q T)

theorem guideOneTree_eval {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hQ : SizeRegular (Fintype.card V) Q) :
    (guideOneTree family T).eval G.cut =
      some (Prog.eval G.cut (guideOneProgram family (Nat.clog 2 (T.real.card + 1)) T)) :=
  Prog.toDTree_eval _ _ _ (guideOneProgram_root_cost family G hG T hQ _)

theorem guideOneTree_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hQ : SizeRegular (Fintype.card V) Q) :
    ∃ output, (guideOneTree family T).eval G.cut = some output ∧
      (∀ t C, output t = some C → CandidateValid G T.source t C) ∧
      ∀ t ∈ T.realVertices, (∃ C, IsSTMinCut G t T.source C ∧ T.RespectsCut C 1) →
        ∃ C, output t = some C ∧ CandidateExact G T.source t C := by
  refine ⟨Prog.eval G.cut (guideOneProgram family (Nat.clog 2 (T.real.card + 1)) T),
    guideOneTree_eval family G hG T hQ, ?_, ?_⟩
  · intro t C hC
    exact guideOneProgram_valid family _ G T t C hC
  · intro t ht hrespect
    exact guideOneProgram_clog_complete family T G hG ht hrespect

/-- The quantifier order is part of the endpoint: the program is fixed before
the graph and its respected minimum-cut witnesses. -/
theorem exists_guideOneTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) (hQ : SizeRegular (Fintype.card V) Q) :
    ∃ program : DTree (Finset V) ℝ (Option (V → Option (CutCandidate V))) (guideOneBudget Q T),
      (∀ read, program.cost read ≤ guideOneBudget Q T) ∧
      ∀ G : WeightedGraph V, InputPromise M G →
        ∃ output, program.eval G.cut = some output ∧
          (∀ t C, output t = some C → CandidateValid G T.source t C) ∧
          ∀ t ∈ T.realVertices, (∃ C, IsSTMinCut G t T.source C ∧ T.RespectsCut C 1) →
            ∃ C, output t = some C ∧ CandidateExact G T.source t C := by
  exact ⟨guideOneTree family T, fun read => DTree.cost_le _ read,
    fun G hG => guideOneTree_correct family G hG T hQ⟩

end
end CutQueryComplexity.GHReduction
