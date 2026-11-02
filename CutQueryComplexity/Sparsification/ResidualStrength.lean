import CutQueryComplexity.Sparsification.Strength
import CutQueryComplexity.Primitive.Residual
import CutQueryComplexity.Graph.ForestFacts

/-! # Separating pairs costs residual mass

Every original block cut is bounded by the total surviving edge mass. Thus
pair strength is bounded by residual mass whenever its endpoints still lie
in distinct blocks. This gives a direct approximate-Kruskal estimate.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

theorem cut_le_edgeMass (G : WeightedGraph V) (S : Finset V) : G.cut S ≤ G.edgeMass := by
  have h := G.internalMass_union (S := S) (T := Sᶜ) disjoint_compl_right
  have hs := G.internalMass_nonneg S
  have ht := G.internalMass_nonneg Sᶜ
  simp only [Finset.union_compl, internalMass_univ, cross_compl] at h
  linarith

theorem blockCut_le_residualMass (G : WeightedGraph V) (π : V → B) (b : B) :
    G.cut (fiber π b) ≤ (G.contract π).internalMass Finset.univ := by
  calc
    G.cut (fiber π b) = (G.contract π).cut {b} := (G.cut_contract π {b}).symm
    _ ≤ _ := (G.contract π).cut_le_edgeMass {b}

theorem strength_le_residualMass (G : WeightedGraph V) (π : V → B) {u v : V}
    (hne : π u ≠ π v) : G.strength u v ≤ (G.contract π).internalMass Finset.univ := by
  exact (G.strength_le_cut (S := fiber π (π u)) (by simp) (by simpa using Ne.symm hne)).trans
    (G.blockCut_le_residualMass π (π u))

theorem label_eq_of_residualMass_zero (G : WeightedGraph V) (π : V → B)
    (hz : (G.contract π).internalMass Finset.univ = 0) {u v : V}
    (hr : G.support.Reachable u v) : π u = π v := by
  have hc : G.cut (fiber π (π u)) = 0 := le_antisymm
    (by simpa [hz] using G.blockCut_le_residualMass π (π u)) (G.cut_nonneg _)
  have hv := reachable_mem_of_cut_zero G (fiber π (π u)) hc (by simp) hr
  exact ((mem_fiber _ _ _).mp hv).symm

end
end CutQueryComplexity.WeightedGraph
