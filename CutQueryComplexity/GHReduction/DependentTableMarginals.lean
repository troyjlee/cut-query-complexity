import CutQueryComplexity.GHReduction.DependentRandomTable
import CutQueryComplexity.Probability.Expectation
import CutQueryComplexity.Probability.Truncation

/-! # Exact marginals of executed dependent tables

The actual finite bind sequence has the expected law at every named entry.
The argument does not replace the executed table by an assumed product law.
Truncation can only decrease a nonnegative potential that is zero on abort.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {I A J : Type} {O : J → Type} {q : ℕ} [DecidableEq J]

theorem dependentRandomTableAux_expect_entry (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (L : List J) (read : I → A)
    (j : J) (hj : j ∈ L) (potential : O j → ℝ≥0∞) :
    expect ((dependentRandomTableAux fallback f L).eval read) (fun table => potential (table j)) =
      expect ((f j).eval read) potential := by
  induction L with
  | nil => simp at hj
  | cons k L ih =>
      simp only [dependentRandomTableAux, RTree.eval_cast, RTree.eval_bind, expect_bind,
        RTree.eval_map, expect_map]
      by_cases hjk : j = k
      · subst k
        simp only [Function.update_self, expect_const]
      · simp only [Function.update_of_ne hjk]
        rw [ih ((List.mem_cons.mp hj).resolve_left hjk), expect_const]

theorem dependentRandomTable_expect_entry [Fintype J] (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (read : I → A) (j : J) (potential : O j → ℝ≥0∞) :
    expect ((dependentRandomTable fallback f).eval read) (fun table => potential (table j)) =
      expect ((f j).eval read) potential := by
  rw [dependentRandomTable, RTree.eval_cast]
  exact dependentRandomTableAux_expect_entry fallback f Finset.univ.toList read j (by simp) potential

theorem truncate_expect_zero_le {X : Type} (program : RTree I A X q) (cap : ℕ)
    (read : I → A) (potential : X → ℝ≥0∞) :
    expect ((program.truncate cap).eval read) (fun out => out.elim 0 potential) ≤
      expect (program.eval read) potential := by
  rw [RTree.eval_truncate, expect_map, RTree.eval, expect_map]
  apply expect_mono_on_support
  intro out _
  by_cases h : out.2 ≤ cap
  · simp only [if_pos h, Option.elim_some, le_refl]
  · simp only [if_neg h, Option.elim_none]
    exact zero_le

end
end CutQueryComplexity.GHReduction
