import CutQueryComplexity.GHReduction.FrontierTermination
import CutQueryComplexity.GHReduction.FrontierAssemblyCorrectness
import CutQueryComplexity.GHReduction.CutTree

/-! # The actual frontier reduction with an explicit public approximator

The bounded program executes the adaptive frontier process and then performs
the proved backward assembly on its own transcript. Correctness means a full
cut-equivalent tree, including original-graph minimum shores. This intermediate
endpoint keeps the explicit approximator visible; the separate initial
sparsification program removes that premise from the oracle reduction.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability OuterPivot

variable {V : Type} [Fintype V] [DecidableEq V]

def TreeOutputSuccess (G : WeightedGraph V) (output : Option (CutTree V)) : Prop :=
  ∃ tree, output = some tree ∧ IsGomoryHuTree G tree

/-- `G` is absent: the only graph argument is the explicitly returned
approximator, and all hidden information comes from executed cut queries. -/
def frontierReduction {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent levels fuel : ℕ)
    (K : WeightedGraph V) (hvn : Fintype.card V ≤ n) (r : V) :
    RTree (Finset V) ℝ (Option (CutTree V))
      (fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels) :=
  (frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel
    (initialFrontierState r)).map assembleFrontierTrace

theorem frontierReduction_cost {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels fuel : ℕ)
    (K : WeightedGraph V) (hvn : Fintype.card V ≤ n) (r : V) (read : Finset V → ℝ)
    {out : Option (CutTree V) × ℕ}
    (hout : out ∈ (RTree.run read (frontierReduction family n samples trials guideLevels
      scale exponent levels fuel K hvn r)).support) :
    out.2 ≤ fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels :=
  RTree.cost_le _ read hout

theorem frontierReduction_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 0 < n) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent levels fuel : ℕ)
    (hguideLevels : thresholdLevels n ≤ guideLevels) (hpivotLevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n) (r : V)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    mass ((frontierReduction family n samples trials guideLevels scale exponent levels fuel
      K hvn r).eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
      (fuel : ℝ≥0∞) * ((n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent) +
        (n : ℝ≥0∞) * (contractionRate levels ^ fuel * (n : ℝ≥0∞)) := by
  rw [frontierReduction, RTree.eval_map, mass_map]
  apply le_trans (mass_mono_on_support _ ?_)
    (frontierExecution_termination_failure family hQ hn hnscale samples trials guideLevels exponent
      levels hguideLevels hpivotLevels G K hG hvn happrox fuel (initialFrontierState r))
  intro trace htrace hbad hgood
  apply hbad
  exact assembleFrontierTrace_success G r trace
    (frontierExecution_support family samples trials guideLevels scale exponent levels K hvn fuel
      (initialFrontierState r) G.cut htrace).2 hgood.1 hgood.2

/-- An explicit real target is permitted for depth; it is converted to the
finite public fuel before executing the program. -/
theorem frontierReduction_depthFuel_failure {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 0 < n) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent levels : ℕ)
    (hguideLevels : thresholdLevels n ≤ guideLevels) (hpivotLevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n) (r : V)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) {failure : ℝ} (hf : 0 < failure) :
    mass ((frontierReduction family n samples trials guideLevels scale exponent levels
      (depthFuel levels (n * n) failure) K hvn r).eval G.cut)
      (fun output => ¬TreeOutputSuccess G output) ≤
      (depthFuel levels (n * n) failure : ℝ≥0∞) *
        ((n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent) + ENNReal.ofReal failure := by
  rw [frontierReduction, RTree.eval_map, mass_map]
  let P := (frontierExecution family n samples trials guideLevels scale exponent levels K hvn
    (depthFuel levels (n * n) failure) (initialFrontierState r)).eval G.cut
  calc
    _ ≤ mass P (fun trace => ¬trace.Good G ∨ (trace.Good G ∧ ¬trace.endState.Discrete)) := by
      apply mass_mono_on_support
      intro trace htrace hbad
      by_cases hg : trace.Good G
      · right
        refine ⟨hg, fun hd => hbad ?_⟩
        exact assembleFrontierTrace_success G r trace
          (frontierExecution_support family samples trials guideLevels scale exponent levels K hvn
            (depthFuel levels (n * n) failure) (initialFrontierState r) G.cut htrace).2 hg hd
      · exact Or.inl hg
    _ ≤ mass P (fun trace => ¬trace.Good G) +
        mass P (fun trace => trace.Good G ∧ ¬trace.endState.Discrete) := mass_or_le P _ _
    _ ≤ _ := add_le_add
      (frontierExecution_failure_le family hQ hn hnscale samples trials guideLevels exponent levels
        hguideLevels G K hG hvn happrox _ (initialFrontierState r))
      (frontierExecution_depthFuel family hQ samples trials guideLevels scale exponent levels
        hpivotLevels G K hG hvn (initialFrontierState r) hf)

/-- Success delivers both a bottleneck value and an original minimum-cut
shore for every requested pair, including pairs of value zero. -/
theorem TreeOutputSuccess.allPairs (G : WeightedGraph V) {output : Option (CutTree V)}
    (h : TreeOutputSuccess G output) :
    ∃ tree, output = some tree ∧ ∀ s t : V, s ≠ t →
      ∃ v ∈ pathEdges tree.topology s t,
        (∀ e ∈ pathEdges tree.topology s t, tree.weight v ≤ tree.weight e) ∧
        IsSTMinCut G s t (pathShore tree.topology s v) ∧
        G.cut (pathShore tree.topology s v) = tree.weight v := by
  obtain ⟨tree, htree, hcorrect⟩ := h
  exact ⟨tree, htree, fun _ _ hst => cutTree_allPairs G tree hcorrect hst⟩

end
end CutQueryComplexity.GHReduction
