import CutQueryComplexity.GHReduction.TerminalContraction
import CutQueryComplexity.GHReduction.Programs
import Mathlib.Tactic.Linarith

/-! # Guarded terminal-group separator calls

Empty terminal classes are handled without a primitive call. All executed
contractions have nonempty fibers, so their compact vertex counts do not exceed
the parent count. This bound is independent of oracle answers.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

theorem regular_cost_mono {n s : ℕ} {Q : ℕ → ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (hsn : s ≤ n) (hQ : SizeRegular n Q) : Q s ≤ Q n := by
  have h := hQ s hs hsn
  have hmul := Nat.mul_le_mul_right (Q n) hsn
  by_contra hnot
  have hstrict : Q n + 1 ≤ Q s := by omega
  have hscaled := Nat.mul_le_mul_left n hstrict
  nlinarith

def groupSeparator {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (A B : Finset V) : Prog (Finset V) ℝ (Finset V) :=
  if A = ∅ then Prog.pure ∅ else
    if B = ∅ then Prog.pure Finset.univ else liftDTree (setCutProgram family A B)

theorem groupSeparator_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {A B : Finset V}
    (hAB : Disjoint A B) :
    IsMinTraceCut G (A ∪ B) A (Prog.eval G.cut (groupSeparator family A B)) := by
  by_cases hA : A = ∅
  · simp only [groupSeparator, hA, ite_true, Prog.eval_pure]
    refine ⟨by simp, fun T _ => ?_⟩
    simpa using G.cut_nonneg T
  · by_cases hB : B = ∅
    · simp only [groupSeparator, hA, ite_false, hB, ite_true, Prog.eval_pure]
      refine ⟨by simp, fun T _ => ?_⟩
      simpa using G.cut_nonneg T
    · simp only [groupSeparator, hA, hB, ite_false, liftDTree_eval]
      exact (setCutProgram_correct family G hG hAB).1

theorem groupSeparator_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    {A B : Finset V} (hAB : Disjoint A B) (hQ : SizeRegular (Fintype.card V) Q)
    (read : Finset V → ℝ) :
    Prog.cost read (groupSeparator family A B) ≤ Q (Fintype.card V) := by
  by_cases hA : A = ∅
  · simp [groupSeparator, hA]
  · by_cases hB : B = ∅
    · simp [groupSeparator, hA, hB]
    · have hAn : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
      have hBn : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
      have hn : 0 < Fintype.card V := hAn.card_pos.trans_le (Finset.card_le_univ A)
      have hs : 1 ≤ Fintype.card (SetCutVertex A B) := by
        haveI : Nonempty (SetCutVertex A B) := ⟨Sum.inl 0⟩
        exact Fintype.card_pos
      simp only [groupSeparator, hA, hB, ite_false]
      exact (liftDTree_cost_le _ read).trans
        (regular_cost_mono hn hs (setCutVertex_card_le hAB hAn hBn) hQ)

/-- The reference size stays equal to the original input size throughout all
recursive contractions; no regularity at the smaller parent size is assumed. -/
theorem groupSeparator_cost_scaled {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    {A B : Finset V} (hAB : Disjoint A B) (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    n * Prog.cost read (groupSeparator family A B) ≤ Fintype.card V * Q n := by
  by_cases hA : A = ∅
  · simp [groupSeparator, hA]
  · by_cases hB : B = ∅
    · simp [groupSeparator, hA, hB]
    · have hAn : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
      have hBn : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
      have hs : 1 ≤ Fintype.card (SetCutVertex A B) := by
        haveI : Nonempty (SetCutVertex A B) := ⟨Sum.inl 0⟩
        exact Fintype.card_pos
      have hsm := setCutVertex_card_le hAB hAn hBn
      simp only [groupSeparator, hA, hB, ite_false]
      calc
        _ ≤ n * Q (Fintype.card (SetCutVertex A B)) :=
          Nat.mul_le_mul_left n (liftDTree_cost_le _ read)
        _ ≤ Fintype.card (SetCutVertex A B) * Q n := hQ _ hs (hsm.trans hvn)
        _ ≤ _ := Nat.mul_le_mul_right (Q n) hsm

end
end CutQueryComplexity.GHReduction
