import CutQueryComplexity.BoundedFlowMinCut.Basic
import CutQueryComplexity.Primitive.Reductions

/-! # The incidence oracle of a residual graph

For an explicitly known subgraph `K ≤ G`, the graph `H = G.subtract K` and two
public sets `P, A` (which may overlap), the incidence sum
`Σ_{v ∈ A} Σ_{p ∈ P} H.w v p` is computed from seven cut queries of `G`, given
the degrees of `G`. With `B = A ∩ P` and `C = A \ P`,

`Σ_{v∈A} Σ_{p∈P} H.w v p = H.cross C P + H.cross B (P \ B) + Σ_{v∈B} deg_H v - H.cut B`.

Both cross sums have disjoint arguments (three queries each), and every cut of
`H` costs one cut of `G` (`deletionQuery`). Applying a disjoint-cross formula to
the overlapping pair `A, P` directly would be wrong; the identity handles the
overlap through the internal weight of `B`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A cross sum of `G.subtract K`, in three queries of `G`. -/
def residualCross (K : WeightedGraph V) (S T : Finset V) : DTree (Finset V) ℝ ℝ 3 :=
  ((crossQuery S T).substitute (deletionQuery K)).cast (by norm_num)

theorem residualCross_eval (G K : WeightedGraph V) (hK : ∀ u v, K.w u v ≤ G.w u v)
    {S T : Finset V} (h : Disjoint S T) :
    (residualCross K S T).eval G.cut = (G.subtract K).cross S T := by
  rw [residualCross, DTree.eval_cast, DTree.eval_substitute]
  have hread : (fun j => (deletionQuery K j).eval G.cut) = (G.subtract K).cut :=
    funext (deletionQuery_eval G K hK)
  rw [hread, crossQuery_eval _ h]

/-- The incidence sum of `G.subtract K` over `A × P`, in seven queries of `G`;
`deg` is the degree vector of `G`. -/
def incidenceTree (K : WeightedGraph V) (deg : V → ℝ) (P A : Finset V) :
    DTree (Finset V) ℝ ℝ 7 :=
  ((residualCross K (A \ P) P).bind fun c₁ =>
    (residualCross K (A ∩ P) (P \ (A ∩ P))).bind fun c₂ =>
      (deletionQuery K (A ∩ P)).map fun c₃ =>
        c₁ + c₂ + (∑ v ∈ A ∩ P, (deg v - K.degree v)) - c₃).cast (by norm_num)

omit [DecidableEq V] in
theorem degree_subtract (G K : WeightedGraph V) (hK : ∀ u v, K.w u v ≤ G.w u v) (v : V) :
    (G.subtract K).degree v = G.degree v - K.degree v := by
  simp only [WeightedGraph.degree, subtract, max_eq_right (sub_nonneg.mpr (hK _ _)),
    Finset.sum_sub_distrib]

/-- Internal weight of a set, through its degrees and its cut. -/
theorem internal_eq_degree_sub_cut (H : WeightedGraph V) (B : Finset V) :
    ∑ v ∈ B, ∑ p ∈ B, H.w v p = ∑ v ∈ B, H.degree v - H.cut B := by
  have h : ∀ v, H.degree v = ∑ p ∈ B, H.w v p + ∑ p ∈ Bᶜ, H.w v p := fun v =>
    (Finset.sum_add_sum_compl B (H.w v)).symm
  simp only [h, Finset.sum_add_distrib, WeightedGraph.cut]
  ring

/-- The incidence identity, for overlapping sets. -/
theorem incidence_identity (H : WeightedGraph V) (P A : Finset V) :
    ∑ v ∈ A, ∑ p ∈ P, H.w v p =
      H.cross (A \ P) P + H.cross (A ∩ P) (P \ (A ∩ P)) +
        ∑ v ∈ A ∩ P, H.degree v - H.cut (A ∩ P) := by
  have hA : ∑ v ∈ A, ∑ p ∈ P, H.w v p =
      ∑ v ∈ A \ P, ∑ p ∈ P, H.w v p + ∑ v ∈ A ∩ P, ∑ p ∈ P, H.w v p := by
    rw [← Finset.sum_sdiff (Finset.inter_subset_left : A ∩ P ⊆ A), Finset.sdiff_inter_self_left]
  have hP : ∀ v, ∑ p ∈ P, H.w v p = ∑ p ∈ P \ (A ∩ P), H.w v p + ∑ p ∈ A ∩ P, H.w v p :=
    fun v => (Finset.sum_sdiff (Finset.inter_subset_right : A ∩ P ⊆ P)).symm
  rw [hA, WeightedGraph.cross, WeightedGraph.cross]
  simp only [hP, Finset.sum_add_distrib, internal_eq_degree_sub_cut]
  ring

theorem incidenceTree_eval (G K : WeightedGraph V) (hK : ∀ u v, K.w u v ≤ G.w u v)
    (deg : V → ℝ) (hdeg : ∀ v, deg v = G.degree v) (P A : Finset V) :
    (incidenceTree K deg P A).eval G.cut = ∑ v ∈ A, ∑ p ∈ P, (G.subtract K).w v p := by
  rw [incidence_identity, incidenceTree, DTree.eval_cast, DTree.eval_bind, DTree.eval_bind,
    DTree.eval_map, residualCross_eval G K hK (Finset.sdiff_disjoint : Disjoint (A \ P) P),
    residualCross_eval G K hK (Finset.disjoint_sdiff : Disjoint (A ∩ P) (P \ (A ∩ P))),
    deletionQuery_eval G K hK]
  simp only [hdeg, degree_subtract G K hK]

end
end CutQueryComplexity.BoundedFlowMinCut
