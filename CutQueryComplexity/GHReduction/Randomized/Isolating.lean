import CutQueryComplexity.GHReduction.Randomized.Primitives
import CutQueryComplexity.GHReduction.Randomized.Interpret

/-! # Milestone: randomized isolating cuts

The isolating-cuts subroutine with a randomized s-t family, end to end:

1. the twin `isolatingValuesCall R` is compiled at the amplified charge
   `r (Q k + k)` with the old budget, and run with the amplified family;
2. the ideal run fits the budget (`isolatingValuesCall_idealCost`), so the
   compiled tree's ideal law is the point mass at the ideal output
   (`interpIdeal_compile`);
3. the ideal output is what the old program computes with the reference exact
   family (`isolatingValues_idealEval`), so `isolatingValuesProgram_correct`
   says it is correct;
4. the union bound G2 adds `3^{-r}` per unit of budget.

This validates the Phase 3 design on one complete subroutine.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The old `isolatingTree` budget at charge `Q`. -/
def isolatingBudget (V : Type) [Fintype V] (Q : ℕ → ℕ) (R : Finset V) : ℕ :=
  (Nat.clog 2 R.card + 2) * Q (Fintype.card V) + R.card

/-- Every `v ∈ R` receives its canonical isolating shore and the shore's exact value. -/
def IsolatingSuccess (G : WeightedGraph V) (R : Finset V)
    (out : Option (R → Finset V × ℝ)) : Prop :=
  ∃ output, out = some output ∧
    ∀ v : R, IsCanonicalTraceCut G R {v.val} (output v).1 ∧ (output v).2 = G.cut (output v).1

/-- The public program: the twin compiled at the amplified charge, run with the
amplified family. -/
def randomizedIsolating {M : ℕ} {Q : ℕ → ℕ} (family : RandomCanonicalSTFamily M Q) (r : ℕ)
    (R : Finset V) :
    RTree (Finset V) ℝ (Option (R → Finset V × ℝ)) (isolatingBudget V (amplifiedCost r Q) R) :=
  CallTree.interpRand (family.program.amplify r)
    (CallProg.compile (amplifiedCost r Q) (CallProg.isolatingValuesCall R) _)

theorem randomizedIsolating_failure {M : ℕ} {Q : ℕ → ℕ} (family : RandomCanonicalSTFamily M Q)
    {r : ℕ} (hr : 1 ≤ r) (R : Finset V) (hR : 2 ≤ R.card) (hQ : SizeRegular (Fintype.card V) Q)
    (G : WeightedGraph V) (hG : InputPromise M G) :
    mass ((randomizedIsolating family r R).eval G.cut) (fun out => ¬IsolatingSuccess G R out) ≤
      3⁻¹ ^ r * (isolatingBudget V (amplifiedCost r Q) R : ℝ≥0∞) := by
  have hn : 0 < Fintype.card V := by have := Finset.card_le_univ R; omega
  have hcost := CallProg.isolatingValuesCall_idealCost R hn (sizeRegular_amplifiedCost hQ r) G
  have hideal := CallProg.interpIdeal_compile G (amplifiedCost r Q)
    (CallProg.isolatingValuesCall R) (isolatingBudget V (amplifiedCost r Q) R) hcost
  have hgood : IsolatingSuccess G R (some (CallProg.idealEval G (CallProg.isolatingValuesCall R))) := by
    refine ⟨_, rfl, fun v => ?_⟩
    rw [← CallProg.isolatingValues_idealEval (refFamily M) G hG R]
    exact isolatingValuesProgram_correct (refFamily M) G hG R hR v
  have h := CallTree.mass_interpRand_le (family.amplify_failsAtMost r)
    (fun k hk => one_le_amplifiedCost hr Q hk) G hG
    (CallProg.compile (amplifiedCost r Q) (CallProg.isolatingValuesCall R)
      (isolatingBudget V (amplifiedCost r Q) R)) (fun out => ¬IsolatingSuccess G R out)
  rw [hideal, mass_pure, ite_eq_right (not_not.mpr hgood), zero_add] at h
  exact h

/-- Milestone: one public randomized program, chosen before the graph, whose
budget is the old isolating budget at the amplified charge. On every promised
graph it returns every canonical isolating shore with its value, except with
probability at most `3^{-r}` times the budget. -/
theorem exists_randomized_isolating {M : ℕ} {Q : ℕ → ℕ} (family : RandomCanonicalSTFamily M Q)
    {r : ℕ} (hr : 1 ≤ r) (R : Finset V) (hR : 2 ≤ R.card) (hQ : SizeRegular (Fintype.card V) Q) :
    ∃ program : RTree (Finset V) ℝ (Option (R → Finset V × ℝ))
        ((Nat.clog 2 R.card + 2) * amplifiedCost r Q (Fintype.card V) + R.card),
      (∀ read, ∀ out ∈ (RTree.run read program).support,
        out.2 ≤ (Nat.clog 2 R.card + 2) * amplifiedCost r Q (Fintype.card V) + R.card) ∧
      ∀ G : WeightedGraph V, InputPromise M G →
        mass (program.eval G.cut) (fun out => ¬∃ output, out = some output ∧
          ∀ v : R, IsCanonicalTraceCut G R {v.val} (output v).1 ∧
            (output v).2 = G.cut (output v).1) ≤
          3⁻¹ ^ r *
            (((Nat.clog 2 R.card + 2) * amplifiedCost r Q (Fintype.card V) + R.card : ℕ) : ℝ≥0∞) :=
  ⟨randomizedIsolating family r R, fun read _ hout => RTree.cost_le _ read hout,
    fun G hG => randomizedIsolating_failure family hr R hR hQ G hG⟩

end
end CutQueryComplexity.GHReduction.Randomized
