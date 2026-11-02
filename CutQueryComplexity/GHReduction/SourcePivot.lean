import CutQueryComplexity.GHReduction.SingleSource
import CutQueryComplexity.GHReduction.OuterPivot.Step
import CutQueryComplexity.Probability.FiniteEvents

/-! # A pivot step using the actual single-source solver

The program draws a public pivot, computes its source values with
`singleSourceTree`, and then invokes the fresh randomized isolating step.
Only the one returned value vector is passed to that step. Neither the graph
nor a family of exact vectors is an algorithmic argument.

The conditional error bound follows these actual binds. A good source vector
implies correct returned cut shores and queried values on every supported
isolating-step outcome. This module does not yet identify the full outer
recursive execution or prove its depth and frontier ledger.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Public outputs retain the selected pivot and the vector actually returned
by its single-source call. There are no correctness fields. -/
structure SourcePivotOutput (V : Type) (levels : ℕ) where
  pivot : V
  values : V → Option ℝ
  step : OuterPivot.Output V levels

def sourcePivotBudget (M : ℕ) (Q : ℕ → ℕ)
    (n samples trials guideLevels scale exponent pivotLevels : ℕ) : ℕ :=
  singleSourceBudget M Q n samples trials guideLevels scale exponent +
    OuterPivot.stepBudget Q n pivotLevels

def sourcePivotFor {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent pivotLevels : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (SourcePivotOutput V pivotLevels)
      (sourcePivotBudget M Q n samples trials guideLevels scale exponent pivotLevels) :=
  (singleSourceTree family n samples trials guideLevels scale exponent K U s hvn).bind
    (fun values => (OuterPivot.randomStepTree family n U s values pivotLevels).map
      (fun output => ⟨s, values, output⟩))

def sourcePivotTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent pivotLevels : ℕ)
    (K : WeightedGraph V) (U : Finset V) (hU : U.Nonempty) (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (SourcePivotOutput V pivotLevels)
      (sourcePivotBudget M Q n samples trials guideLevels scale exponent pivotLevels) :=
  RTree.mix ((PMF.uniformOfFinset U hU).map (fun s =>
    sourcePivotFor family n samples trials guideLevels scale exponent pivotLevels K U s hvn))

theorem sourcePivotFor_eval {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent pivotLevels : ℕ)
    (K : WeightedGraph V) (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n)
    (read : Finset V → ℝ) :
    (sourcePivotFor family n samples trials guideLevels scale exponent pivotLevels K U s hvn).eval read =
      ((singleSourceTree family n samples trials guideLevels scale exponent K U s hvn).eval read).bind
        (fun values => ((OuterPivot.randomStepTree family n U s values pivotLevels).eval read).map
          (fun output => (SourcePivotOutput.mk s values output))) := by
  unfold sourcePivotFor sourcePivotBudget
  rw [RTree.eval_bind]
  simp only [RTree.eval_map]

theorem sourcePivotTree_eval {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent pivotLevels : ℕ)
    (K : WeightedGraph V) (U : Finset V) (hU : U.Nonempty) (hvn : Fintype.card V ≤ n)
    (read : Finset V → ℝ) :
    (sourcePivotTree family n samples trials guideLevels scale exponent pivotLevels K U hU hvn).eval read =
      (PMF.uniformOfFinset U hU).bind (fun s =>
        (sourcePivotFor family n samples trials guideLevels scale exponent pivotLevels K U s hvn).eval read) := by
  simp only [sourcePivotTree, RTree.eval_mix, PMF.bind_map, Function.comp_def]

/-- Both the stored vector and the step come from the actual supported
execution, with the latter selected adaptively from that same vector. -/
theorem sourcePivotTree_support {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent pivotLevels : ℕ)
    (K : WeightedGraph V) (U : Finset V) (hU : U.Nonempty) (hvn : Fintype.card V ≤ n)
    (read : Finset V → ℝ) {out : SourcePivotOutput V pivotLevels}
    (hout : out ∈ ((sourcePivotTree family n samples trials guideLevels scale exponent pivotLevels
      K U hU hvn).eval read).support) :
    out.pivot ∈ U ∧
    out.values ∈ ((singleSourceTree family n samples trials guideLevels scale exponent K U
      out.pivot hvn).eval read).support ∧
    out.step ∈ ((OuterPivot.randomStepTree family n U out.pivot out.values pivotLevels).eval read).support := by
  rw [sourcePivotTree_eval] at hout
  obtain ⟨s, hs, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  rw [sourcePivotFor_eval] at hnext
  obtain ⟨values, hvalues, hmapped⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
  obtain ⟨step, hstepSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmapped
  exact ⟨(PMF.mem_support_uniformOfFinset_iff _ _).mp hs, hvalues, hstepSupported⟩

def SourcePivotGood (G : WeightedGraph V) (U : Finset V) {levels : ℕ}
    (out : SourcePivotOutput V levels) : Prop :=
  out.pivot ∈ U ∧ SourceValuesSuccess G U out.pivot out.values ∧
  OuterPivot.WellFormed U out.pivot out.values out.step.batch ∧
  ∀ v ∈ out.step.batch.accepted,
    IsSTMinCut G v out.pivot (out.step.batch.shore v) ∧
      out.step.batch.value v = G.cut (out.step.batch.shore v)

theorem sourcePivot_good_of_values {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (U : Finset V) (s : V) (hs : s ∈ U)
    (values : V → Option ℝ) (levels : ℕ) (hvalues : SourceValuesSuccess G U s values)
    {step : OuterPivot.Output V levels}
    (hstep : step ∈ ((OuterPivot.randomStepTree family n U s values levels).eval G.cut).support) :
    SourcePivotGood G U (SourcePivotOutput.mk s values step) := by
  have hexact : ∀ v ∈ U.erase s, values v = some (stValue G v s) := by
    intro v hv
    exact hvalues.2 v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1
  obtain ⟨hform, hcuts⟩ := OuterPivot.randomStepTree_correct family hvn hQ
    G U s values levels hexact hstep
  exact ⟨hs, hvalues, hform, hcuts⟩

/-- The isolating continuation introduces no additional correctness error
after a good value output. Its fresh samples still affect progress. -/
theorem sourcePivotFor_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent pivotLevels : ℕ)
    (hlevels : thresholdLevels n ≤ guideLevels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V) (hs : s ∈ U)
    (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    mass ((sourcePivotFor family n samples trials guideLevels scale exponent pivotLevels K U s hvn).eval G.cut)
      (fun out => ¬SourcePivotGood G U out) ≤ singleSourceError M n samples trials scale exponent := by
  rw [sourcePivotFor_eval]
  have hsource := singleSourceTree_failure_le family hQ hnscale samples trials guideLevels exponent
    hlevels G K hG U s hs hvn happrox
  calc
    _ ≤ singleSourceError M n samples trials scale exponent + 0 := by
      apply mass_bind_le_add _ _ (fun values => ¬SourceValuesSuccess G U s values) _ hsource
      intro values hvalues
      have hvalues' : SourceValuesSuccess G U s values := not_not.mp hvalues
      rw [mass_map]
      have hzero := mass_mono_on_support
        ((OuterPivot.randomStepTree family n U s values pivotLevels).eval G.cut)
        (P := fun step => ¬SourcePivotGood G U (SourcePivotOutput.mk s values step))
        (Q := fun _ => False) (fun step hstep hbad =>
          hbad (sourcePivot_good_of_values family hvn hQ G U s hs values pivotLevels hvalues' hstep))
      simpa only [mass_false] using hzero
    _ = _ := add_zero _

/-- Error is charged to the actual single-source call for the sampled pivot;
there is no union bound over an unqueried vector for every possible pivot. -/
theorem sourcePivotTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent pivotLevels : ℕ)
    (hlevels : thresholdLevels n ≤ guideLevels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (hU : U.Nonempty)
    (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    mass ((sourcePivotTree family n samples trials guideLevels scale exponent pivotLevels K U hU hvn).eval G.cut)
      (fun out => ¬SourcePivotGood G U out) ≤ singleSourceError M n samples trials scale exponent := by
  rw [sourcePivotTree_eval]
  have hpivot : mass (PMF.uniformOfFinset U hU) (fun s => s ∉ U) ≤ 0 := by
    have hzero := mass_mono_on_support (PMF.uniformOfFinset U hU)
      (P := fun s => s ∉ U) (Q := fun _ => False)
      (fun s hs hbad => hbad ((PMF.mem_support_uniformOfFinset_iff _ _).mp hs))
    simpa only [mass_false] using hzero
  have hbound := mass_bind_le_add (PMF.uniformOfFinset U hU)
    (fun s => (sourcePivotFor family n samples trials guideLevels scale exponent pivotLevels K U s hvn).eval G.cut)
    (fun s => s ∉ U) (fun out => ¬SourcePivotGood G U out)
    (δ := 0) (ε := singleSourceError M n samples trials scale exponent) hpivot
    (fun s hs => sourcePivotFor_failure_le family hQ hnscale samples trials guideLevels exponent
      pivotLevels hlevels G K hG U s (not_not.mp hs) hvn happrox)
  simpa only [zero_add] using hbound

end
end CutQueryComplexity.GHReduction
