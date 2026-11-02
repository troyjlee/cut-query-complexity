import CutQueryComplexity.GHReduction.GuidePruneSampling
import CutQueryComplexity.GHReduction.RandomRepetition
import CutQueryComplexity.GHReduction.Estimates

/-! # Repeated pruning with value-only output

The minimum over fresh actual calls has a per-target miss probability at most
`(3/4)^h`. All returned finite estimates remain upper bounds on every supported
history. Neither claim assumes a pre-existing two-respecting solver.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def guidePruneTrialsTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials : ℕ) (T : GuideTree V N) :
    RTree (Finset V) ℝ (V → Option ℝ) (trials * guideOneGlobalBudget Q n) :=
  (randomRepeat (guidePruneTree family n T) trials).map
    (fun L t => bestEstimates (L.map (fun output => candidateEstimate (output t))))

theorem pruneTrials_above {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (trials : ℕ)
    {L : List (V → Option (CutCandidate V))}
    (hL : L ∈ ((randomRepeat (guidePruneTree family n T) trials).eval G.cut).support)
    (t : V) :
    EstimateAbove (stValue G t T.source)
      (bestEstimates (L.map (fun output => candidateEstimate (output t)))) := by
  apply bestEstimates_above
  intro a ha
  obtain ⟨output, hout, rfl⟩ := List.mem_map.mp ha
  apply candidateEstimate_above G
  intro C hC
  exact guidePruneTree_valid family G hG T hvn hQ
    (randomRepeat_member _ trials G.cut hL hout) hC

theorem guidePruneTrialsTree_above {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (trials : ℕ)
    {output : V → Option ℝ}
    (hout : output ∈ ((guidePruneTrialsTree family n trials T).eval G.cut).support)
    (t : V) : EstimateAbove (stValue G t T.source) (output t) := by
  rw [guidePruneTrialsTree, RTree.eval_map] at hout
  obtain ⟨L, hL, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact pruneTrials_above family G hG T hvn hQ trials hL t

theorem guidePruneTrialsTree_failure_le {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (trials : ℕ)
    (keep delete : frontierProxies T.tree T.centroid) (hne : keep ≠ delete)
    (hs : T.sourceNode ∉ frontierBranch T.tree T.centroid delete)
    (t : N) (ht : t ∈ T.real) (htkeep : t ∈ frontierBranch T.tree T.centroid keep)
    (S : Finset V) (hS : IsSTMinCut G (T.label t) T.source S)
    (A : Finset N) (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S)
    (hcross : (T.tree.crossSet A).card ≤ 2)
    (e : N) (he : e ∈ T.tree.crossSet A)
    (heB : e ∈ frontierBranch T.tree T.centroid delete ∨
      T.tree.parent e ∈ frontierBranch T.tree T.centroid delete) :
    mass ((guidePruneTrialsTree family n trials T).eval G.cut)
      (fun output => output (T.label t) ≠ some (stValue G (T.label t) T.source)) ≤
        ENNReal.ofReal (3 / 4 : ℝ) ^ trials := by
  let Bad := fun output : V → Option (CutCandidate V) =>
    ¬∃ C, output (T.label t) = some C ∧ CandidateExact G T.source (T.label t) C
  have hsingle := guidePruneTree_failure_le family G hG T hvn hQ keep delete hne hs
    t ht htkeep S hS A hA hcross e he heB
  have hall := randomRepeat_failure_le (guidePruneTree family n T) trials G.cut Bad hsingle
  rw [guidePruneTrialsTree, RTree.eval_map, mass_map]
  apply le_trans (mass_mono_on_support _ ?_) hall
  intro L hL hfail output hout
  intro hgood
  obtain ⟨C, hC, hCexact⟩ := hgood
  apply hfail
  apply bestEstimates_exact
  · intro a ha
    obtain ⟨trial, htrial, rfl⟩ := List.mem_map.mp ha
    apply candidateEstimate_above G
    intro D hD
    exact guidePruneTree_valid family G hG T hvn hQ
      (randomRepeat_member _ trials G.cut hL htrial) hD
  · apply List.mem_map.mpr
    refine ⟨output, hout, ?_⟩
    rw [hC]
    exact candidateEstimate_exact G hCexact

end
end CutQueryComplexity.GHReduction
