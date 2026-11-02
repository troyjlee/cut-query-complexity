import CutQueryComplexity.TwoRespecting.Main

/-! Axiom checks for the deterministic two-respecting minimum-cut search.

Run with `lake env lean tests/two-respecting/TwoRespectingCheck.lean`.
-/

open CutQueryComplexity.TwoRespecting

#print axioms twoRespecting_queryBound
#print axioms twoRespecting_correct
#print axioms twoRespecting_cost
#print axioms majoritySearch_spec
#print axioms RootedTree.card_headsAbove_le
#print axioms samePath_spec
#print axioms foundPairs_cover

/-- The statement of the headline theorem, restated for review. -/
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (T : RootedTree V)
    (hV : ∃ v, v ≠ T.root) :
    ∃ D : CutQueryComplexity.DTree (Finset V) ℝ (Option (Finset V))
        (72 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1)),
      ∀ G : CutQueryComplexity.WeightedGraph V, ∃ S, D.eval G.cut = some S ∧
        T.IsTwoRespShore S ∧ ∀ S', T.IsTwoRespShore S' → G.cut S ≤ G.cut S' :=
  twoRespecting_queryBound T hV
