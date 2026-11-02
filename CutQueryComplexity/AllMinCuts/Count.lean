import CutQueryComplexity.AllMinCuts.Basic
import CutQueryComplexity.TwoRespecting.TreeCover

/-! # A quadratic bound on the number of minimum cuts

With `0 < λ(G)`, every minimum-cut shore of `G` is a `5/4`-near-minimum shore of `G` itself, and
the tree-cover argument bounds the near-minimum shores of a graph with positive minimum cut by
`8 (n + n²)` (`TwoRespecting.card_nearMin_le`). Hence every family of minimum-cut shores has at
most `8 (n + n²)` members (`card_le_of_isMinCut`), and so does a correct output
(`Correct.card_cuts_le`): the complete family reported by the deterministic algorithm is
polynomial whenever the minimum cut is positive. With `λ(G) = 0` the family can be exponential.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllMinCuts

open WeightedGraph TwoRespecting DetMinCut Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **At most `8 (n + n²)` minimum-cut shores.** If `0 < λ(G)`, every finite family of
minimum-cut shores of `G` has at most `8 (n + n²)` members. -/
theorem card_le_of_isMinCut (G : WeightedGraph V) (hpos : 0 < mincutValue G)
    (F : Finset (Finset V)) (hF : ∀ S ∈ F, IsMinCut G S) :
    F.card ≤ 8 * (Fintype.card V + Fintype.card V ^ 2) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · -- with no vertices there is no proper shore, so the family is empty
    have hFe : F = ∅ := by
      refine eq_empty_of_forall_notMem fun S hS => ?_
      obtain ⟨x, -⟩ := (hF S hS).1.1
      exact hV.false x
    simp [hFe]
  · -- an order on `V` for the tree-cover count; the count itself does not depend on it
    let _ : LinearOrder V :=
      LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
    have hsub : F ⊆ nearMin G := by
      intro S hS
      have hmin := hF S hS
      refine mem_nearMin.mpr ⟨hmin.1.1, hmin.1.2, ?_⟩
      rw [isMinCut_of_sat hmin]
      linarith
    exact (card_le_card hsub).trans (card_nearMin_le G hpos)

/-- A correct family of a graph with positive minimum cut has at most `8 (n + n²)` shores. -/
theorem Correct.card_cuts_le {G : WeightedGraph V} {out : Output V} (h : Correct G out)
    (hpos : 0 < mincutValue G) : out.cuts.card ≤ 8 * (Fintype.card V + Fintype.card V ^ 2) :=
  card_le_of_isMinCut G hpos out.cuts fun S hS => (h.2 S).mp hS

end CutQueryComplexity.AllMinCuts
