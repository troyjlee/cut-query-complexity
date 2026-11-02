import CutQueryComplexity.GlobalSTReduction.Program

/-! # Global minimum cut from a deterministic s-t family (Phase 4)

On `Fin n` with `n ≥ 2` and public root `0`, `detGlobalProgram` runs
`globalTree` with the family's programs as zero-error randomized programs,
`thresholdLevels n` levels, `trialCount n b` trials and search budget
`searchBudget n b Q`. Its cap is `detGlobalBudget n b Q = 1 + searchBudget`,
with no amplification of the primitive. The only randomness is the terminal
sampling, and a call never fails, so the failure probability is at most
`(7/8)^{trialCount n b} ≤ (n+2)^{-b}` (`trialFailure_le`).
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical ENNReal
open Probability GHReduction GHReduction.Randomized

/-- The public global program built from a deterministic s-t family. -/
def detGlobalProgram {Q : ℕ → ℕ} (family : RealSTFamily Q) (n : ℕ) (hn : 2 ≤ n) (b : ℕ) :
    RTree (Finset (Fin n)) ℝ (Finset (Fin n) × ℝ) (detGlobalBudget n b Q) :=
  globalTree family.toPrograms ⟨0, by omega⟩ (thresholdLevels n) (trialCount n b)
    (searchBudget n b Q)

theorem exists_global_from_st {n : ℕ} {Q : ℕ → ℕ} (family : RealSTFamily Q)
    (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Finset (Fin n) × ℝ) (detGlobalBudget n b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ detGlobalBudget n b Q) ∧
      (∀ G : WeightedGraph (Fin n), ∀ out ∈ (program.eval G.cut).support,
        ValidOutput G out) ∧
      ∀ G : WeightedGraph (Fin n),
        mass (program.eval G.cut) (fun out => ¬GlobalSuccess G out) ≤
          (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  refine ⟨detGlobalProgram family n hn b, fun read out hout => RTree.cost_le _ read hout,
    fun G => globalTree_valid _ G (by rw [hcard]; exact hn) _ _ _ _, fun G => ?_⟩
  have h := globalTree_failure family.toPrograms family.optFailsAtMost_zero G
    (by rw [hcard]; exact hn) (by rw [hcard]; exact hQ) ⟨0, by omega⟩
    (levels := thresholdLevels n) (trials := trialCount n b) (B := searchBudget n b Q)
    (by rw [hcard]) (by rw [hcard]; exact le_rfl)
  rw [zero_mul, add_zero] at h
  exact h.trans (trialFailure_le n b)

/-- The Phase 0 target for deterministic s-t families holds. -/
theorem detGlobalTarget : DetGlobalTarget :=
  fun _ _ family hQ hn b => exists_global_from_st family hQ hn b

end
end CutQueryComplexity.GlobalSTReduction
