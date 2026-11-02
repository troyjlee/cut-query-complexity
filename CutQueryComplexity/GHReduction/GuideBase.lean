import CutQueryComplexity.GHReduction.Candidates
import CutQueryComplexity.GHReduction.GuideStructure

/-! # The exact constant-terminal guide-solver base case

The program executes the supplied weighted primitive once for each requested
target other than the source. Feasible returned shores receive one explicit
value query. The bound counts these auxiliary queries and is independent of
the hidden graph and of the oracle-answer history.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def sourceBaseProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (s : V) (R : Finset V) : Prog (Finset V) ℝ (V → Option (CutCandidate V)) :=
  finiteTable (fun t : V => if t ∈ R then pairCandidateProgram family s t else Prog.pure none)

theorem sourceBaseProgram_valid {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (s : V) (R : Finset V) (t : V) {C : CutCandidate V}
    (h : Prog.eval G.cut (sourceBaseProgram family s R) t = some C) :
    CandidateValid G s t C := by
  by_cases ht : t ∈ R
  · simp only [sourceBaseProgram, finiteTable_eval, ht, ite_true] at h
    exact pairCandidateProgram_valid family G s t h
  · simp [sourceBaseProgram, ht] at h

theorem sourceBaseProgram_exact {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (s : V) (R : Finset V)
    {t : V} (ht : t ∈ R) (hst : s ≠ t) :
    ∃ C, Prog.eval G.cut (sourceBaseProgram family s R) t = some C ∧ CandidateExact G s t C := by
  simpa only [sourceBaseProgram, finiteTable_eval, ht, ite_true] using
    pairCandidateProgram_exact family G hG hst

theorem sourceBaseProgram_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (s : V) (R : Finset V) (read : Finset V → ℝ) :
    Prog.cost read (sourceBaseProgram family s R) ≤ R.card * (Q (Fintype.card V) + 1) := by
  rw [sourceBaseProgram, finiteTable_cost]
  calc
    _ ≤ ∑ t : V, if t ∈ R then Q (Fintype.card V) + 1 else 0 := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : t ∈ R
      · simpa only [ht, ite_true] using pairCandidateProgram_cost family s t read
      · simp [ht]
    _ = ∑ _t ∈ R, (Q (Fintype.card V) + 1) := by
      have hfilter : Finset.univ.filter (fun t : V => t ∈ R) = R := by
        ext t
        simp
      rw [← Finset.sum_filter, hfilter]
    _ = _ := by simp

theorem sourceBaseProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (s : V) (R : Finset V)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    n * Prog.cost read (sourceBaseProgram family s R) ≤
      R.card * (Fintype.card V * Q n + n) := by
  haveI : Nonempty V := ⟨s⟩
  have hreg := hQ (Fintype.card V) Fintype.card_pos hvn
  calc
    _ ≤ n * (R.card * (Q (Fintype.card V) + 1)) :=
      Nat.mul_le_mul_left n (sourceBaseProgram_cost family s R read)
    _ = R.card * (n * Q (Fintype.card V) + n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left R.card (Nat.add_le_add_right hreg n)

def guideBaseProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) : Prog (Finset V) ℝ (V → Option (CutCandidate V)) :=
  sourceBaseProgram family T.source T.realVertices

theorem guideBaseProgram_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) (hsmall : T.real.card ≤ 10) (read : Finset V → ℝ) :
    Prog.cost read (guideBaseProgram family T) ≤ 10 * (Q (Fintype.card V) + 1) := by
  have h := sourceBaseProgram_cost family T.source T.realVertices read
  rw [T.realVertices_card] at h
  exact h.trans (Nat.mul_le_mul_right _ hsmall)

def guideBaseTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) :
    DTree (Finset V) ℝ (Option (V → Option (CutCandidate V))) (10 * (Q (Fintype.card V) + 1)) :=
  Prog.toDTree (guideBaseProgram family T) _

theorem guideBaseTree_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hsmall : T.real.card ≤ 10) :
    ∃ output, (guideBaseTree family T).eval G.cut = some output ∧
      (∀ t C, output t = some C → CandidateValid G T.source t C) ∧
      ∀ t ∈ T.realVertices, T.source ≠ t →
        ∃ C, output t = some C ∧ CandidateExact G T.source t C := by
  refine ⟨Prog.eval G.cut (guideBaseProgram family T), ?_, ?_, ?_⟩
  · exact Prog.toDTree_eval _ _ _ (guideBaseProgram_cost family T hsmall G.cut)
  · intro t C h
    exact sourceBaseProgram_valid family G T.source T.realVertices t h
  · intro t ht hst
    exact sourceBaseProgram_exact family G hG T.source T.realVertices ht hst

end
end CutQueryComplexity.GHReduction
