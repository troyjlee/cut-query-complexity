import CutQueryComplexity.Graph.CutConcentration
import CutQueryComplexity.Sparsification.RandomDecomposition

/-! # From bounded component cuts to sparsifier failure bounds

Per-cut bounded-draw representations supply concentration on each BK piece.
The failure bound is a sum over positive proper shores inside each component,
followed by the existing union bound over at most `n-1` components. Cut counting
must still bound these deterministic exponential sums. No independence of
different cuts, pieces, or aggregated edge weights is assumed.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V] [DecidableEq V]

theorem scaled_strengthPiece_induce (G X : WeightedGraph V) (U : Finset V)
    (c : ℝ) (hc : 0 ≤ c) :
    ((G.strengthPiece X U).scale c hc).induce U = (G.strengthPiece X U).scale c hc := by
  ext u v
  by_cases hm : u ∈ U ∧ v ∈ U <;> simp [induce, scale, strengthPiece, hm]

theorem HasMean.sparsifier_failure_le_strength_cut_sum
    {p : PMF (WeightedGraph V)} {G : WeightedGraph V} (h : HasMean p G)
    {ε c : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c)
    (hd : ∀ U ∈ G.strongComponents,
      ∀ S ∈ ((G.strengthPiece G U).scale c hc.le).positiveLocalShores U,
        HasBoundedCutLaw (G.strengthPieceLaw p U c hc.le) S) :
    mass p (fun X => ¬IsCutSparsifier ε G X) ≤
      ∑ U ∈ G.strongComponents, ((G.strengthPiece G U).scale c hc.le).cutTailSum U ε := by
  apply h.sparsifier_failure_le_sum_bounds ε hc
  intro U hU
  exact (h.strengthPieceLaw U c hc.le).sparsifier_failure_le_local_cut_sum U
    (G.scaled_strengthPiece_induce G U c hc.le) hε hε1 (hd U hU)

/-- A cut-counting bound for each reference piece completes the probability reduction. -/
theorem HasMean.sparsifier_success_of_cut_tail_bounds
    {p : PMF (WeightedGraph V)} {G : WeightedGraph V} (h : HasMean p G)
    {ε c δ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hd : ∀ U ∈ G.strongComponents,
      ∀ S ∈ ((G.strengthPiece G U).scale c hc.le).positiveLocalShores U,
        HasBoundedCutLaw (G.strengthPieceLaw p U c hc.le) S)
    (hcount : ∀ U ∈ G.strongComponents,
      ((G.strengthPiece G U).scale c hc.le).cutTailSum U ε ≤ ENNReal.ofReal δ) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤ (mass p (IsCutSparsifier ε G)).toReal := by
  apply h.sparsifier_success ε hc hδ
  intro U hU
  exact ((h.strengthPieceLaw U c hc.le).sparsifier_failure_le_local_cut_sum U
    (G.scaled_strengthPiece_induce G U c hc.le) hε hε1 (hd U hU)).trans (hcount U hU)

end
end CutQueryComplexity.WeightedGraph
