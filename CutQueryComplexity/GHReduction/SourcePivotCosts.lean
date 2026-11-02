import CutQueryComplexity.GHReduction.SourcePivot
import CutQueryComplexity.GHReduction.SingleSourceBudget

/-! # Realized costs of the actual source-pivot call

The fixed public cap may be much larger than a call's realized cost. These
bounds retain the actual graph cardinality until a complete frontier is summed.
The isolating step includes its returned-shore value queries. No expected-cost
argument or independence assumption is used.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open OuterPivot

variable {V : Type} [Fintype V] [DecidableEq V]

theorem randomStepTree_run {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ) (read : Finset V → ℝ) :
    RTree.run read (randomStepTree family n U s values levels) =
      (thresholdSeedPMF V levels).map (fun seed =>
        (Prog.eval read (stepProgram family U s values levels seed),
          Prog.cost read (stepProgram family U s values levels seed))) := by
  simp only [randomStepTree, RTree.run_mix, PMF.bind_map, Function.comp_def]
  have he (seed : ThresholdSeed V levels) :
      RTree.run read (RTree.ofDeterministic ((stepTree family n U s values levels seed).map
        (fun output => output.getD (Output.empty levels)))) =
      PMF.pure (Prog.eval read (stepProgram family U s values levels seed),
        Prog.cost read (stepProgram family U s values levels seed)) := by
    simp only [RTree.run_ofDeterministic, DTree.run_map, stepTree,
      Prog.toDTree_run read _ _ (stepProgram_cost family hvn hQ U s values levels seed read),
      Option.getD_some]
  simp_rw [he]
  rfl

theorem randomStepTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ) (read : Finset V → ℝ)
    {out : Output V levels × ℕ}
    (hout : out ∈ (RTree.run read (randomStepTree family n U s values levels)).support) :
    n * out.2 ≤ Fintype.card V * stepBudget Q n levels := by
  rw [randomStepTree_run family hvn hQ] at hout
  obtain ⟨seed, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  simpa only [stepBudget, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    stepProgram_cost_scaled family hvn hQ U s values levels seed read

def sourcePivotSharpBudget (M : ℕ) (Q : ℕ → ℕ)
    (n samples trials guideLevels scale exponent pivotLevels : ℕ) : ℕ :=
  singleSourceSharpBudget M Q n samples trials guideLevels scale exponent +
    stepBudget Q n pivotLevels

theorem sourcePivotFor_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V)
    (hvn : Fintype.card V ≤ n) {out : SourcePivotOutput V levels × ℕ}
    (hout : out ∈ (RTree.run G.cut
      (sourcePivotFor family n samples trials guideLevels scale exponent levels K U s hvn)).support) :
    n * out.2 ≤ Fintype.card V *
      sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels := by
  unfold sourcePivotFor at hout
  have h := random_bind_cost _ _ G.cut n
    (Fintype.card V * singleSourceSharpBudget M Q n samples trials guideLevels scale exponent)
    (Fintype.card V * stepBudget Q n levels)
    (fun first hfirst => singleSourceTree_cost_scaled family hQ samples trials guideLevels scale exponent
      G K hG U s hvn hfirst)
    (fun first _ next hnext => random_map_cost _ _ G.cut n _
      (fun step hstep => randomStepTree_cost_scaled family hvn hQ U s first.1 levels G.cut hstep)
      hnext) hout
  simpa only [sourcePivotSharpBudget, Nat.mul_add] using h

/-- The pivot choice is free, and the bound holds for every supported actual
query count, even if the returned source values are incorrect. -/
theorem sourcePivotTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (hU : U.Nonempty)
    (hvn : Fintype.card V ≤ n) {out : SourcePivotOutput V levels × ℕ}
    (hout : out ∈ (RTree.run G.cut
      (sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn)).support) :
    n * out.2 ≤ Fintype.card V *
      sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels := by
  simp only [sourcePivotTree, RTree.run_mix, PMF.bind_map, Function.comp_def] at hout
  obtain ⟨s, _, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  exact sourcePivotFor_cost_scaled family hQ samples trials guideLevels scale exponent levels
    G K hG U s hvn hs

end
end CutQueryComplexity.GHReduction
