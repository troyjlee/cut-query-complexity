import CutQueryComplexity.GlobalSTReduction.Deterministic
import CutQueryComplexity.GlobalSTReduction.Amplification

/-! # Global minimum cut from a randomized s-t family (Phase 6)

Every call runs the family `a = repetitions n b` times with fresh randomness
(`STPrograms.amplify`), at the charge `amplifiedCost a Q k = a (Q k + k)`,
which is size-regular whenever `Q` is (`sizeRegular_amplifiedCost`). The
program is the deterministic-primitive construction at that charge, so its cap
is `randomGlobalBudget n b Q = detGlobalBudget n b (amplifiedCost a Q)`.

Failure is bounded by the sum of two events (`globalTree_failure`): no trial
isolates a vertex of a fixed optimum, `(7/8)^{trialCount} ≤ (n+2)^{-b}`, and
some amplified call returns a non-minimum shore, at most
`callCount · 3^{-a} ≤ (n+2)^{-b}` (`callFailure_le`). The choice of `a` depends
only on `n` and `b`, not on `Q` or on any weight.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical ENNReal
open Probability GHReduction GHReduction.Randomized

/-- The public global program built from a randomized s-t family. -/
def randomGlobalProgram {Q : ℕ → ℕ} (family : RandomRealSTFamily Q) (n : ℕ) (hn : 2 ≤ n)
    (b : ℕ) : RTree (Finset (Fin n)) ℝ (Finset (Fin n) × ℝ) (randomGlobalBudget n b Q) :=
  globalTree (STPrograms.amplify (Q := Q) family.program (repetitions n b)) ⟨0, by omega⟩
    (thresholdLevels n) (trialCount n b) (searchBudget n b (amplifiedCost (repetitions n b) Q))

theorem exists_global_from_randomized_st {n : ℕ} {Q : ℕ → ℕ} (family : RandomRealSTFamily Q)
    (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Finset (Fin n) × ℝ) (randomGlobalBudget n b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ randomGlobalBudget n b Q) ∧
      (∀ G : WeightedGraph (Fin n), ∀ out ∈ (program.eval G.cut).support,
        ValidOutput G out) ∧
      ∀ G : WeightedGraph (Fin n),
        mass (program.eval G.cut) (fun out => ¬GlobalSuccess G out) ≤
          2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  refine ⟨randomGlobalProgram family n hn b, fun read out hout => RTree.cost_le _ read hout,
    fun G => globalTree_valid _ G (by rw [hcard]; exact hn) _ _ _ _, fun G => ?_⟩
  have h := globalTree_failure (STPrograms.amplify (Q := Q) family.program (repetitions n b))
    (family.amplify_optFailsAtMost (repetitions n b)) G (by rw [hcard]; exact hn)
    (by rw [hcard]; exact sizeRegular_amplifiedCost hQ (repetitions n b)) ⟨0, by omega⟩
    (levels := thresholdLevels n) (trials := trialCount n b)
    (B := searchBudget n b (amplifiedCost (repetitions n b) Q))
    (by rw [hcard]) (by rw [hcard]; exact le_rfl)
  have hN : ((trialCount n b * (thresholdLevels n + 1) *
      (Nat.clog 2 (Fintype.card (Fin n)) + Fintype.card (Fin n)) : ℕ) : ℝ≥0∞) =
      (callCount n b : ℝ≥0∞) := by
    rw [hcard, callCount]
  rw [hN, mul_comm] at h
  rw [two_mul]
  exact h.trans (add_le_add (trialFailure_le n b) (callFailure_le n b))

/-- The Phase 0 target for randomized s-t families holds. -/
theorem randomGlobalTarget : RandomGlobalTarget :=
  fun _ _ family hQ hn b => exists_global_from_randomized_st family hQ hn b

end
end CutQueryComplexity.GlobalSTReduction
