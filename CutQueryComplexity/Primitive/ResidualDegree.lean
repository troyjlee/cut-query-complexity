import CutQueryComplexity.Primitive.Residual
import CutQueryComplexity.Primitive.BinarySearch
import CutQueryComplexity.Sparsification.StrongContraction

/-! # Subset sums of residual block degrees

Inside a public union of contraction blocks, the sum of degrees over a subset
is determined by three original cuts and the cached block cuts. This gives
an additive oracle for selecting the first block of a residual edge.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

namespace WeightedGraph

/-- Residual degree inside `T`, extended by zero outside `T`. -/
def residualDegree (G : WeightedGraph V) (π : V → B) (T : Finset B) (b : B) : ℝ :=
  if b ∈ T then (G.contract π).cross {b} T else 0

theorem residualDegree_nonneg (G : WeightedGraph V) (π : V → B) (T : Finset B) (b : B) :
    0 ≤ G.residualDegree π T b := by
  unfold residualDegree
  split <;> simp [cross_nonneg]

theorem residualDegree_sum (G : WeightedGraph V) (π : V → B) (T A : Finset B) :
    subsetSum (G.residualDegree π T) A = (G.contract π).cross (A ∩ T) T := by
  simp only [subsetSum, residualDegree, cross, Finset.sum_singleton]
  rw [← Finset.sum_filter]
  congr 1

/-- Total residual degree is twice the surviving unordered edge mass. -/
theorem residualDegree_total (G : WeightedGraph V) (π : V → B) (T : Finset B) :
    subsetSum (G.residualDegree π T) Finset.univ = 2 * (G.contract π).internalMass T := by
  rw [residualDegree_sum, Finset.univ_inter, internalMass]
  ring

/-- A block's degree is the mass of the original edges eligible after choosing it. -/
theorem residualDegree_cross (G : WeightedGraph V) (π : V → B) {T : Finset B} {b : B}
    (hb : b ∈ T) :
    G.residualDegree π T b = G.cross (fiber π b) (pull π (T \ {b})) := by
  rw [residualDegree, ite_eq_left hb]
  have he : (G.contract π).cross {b} T = (G.contract π).cross {b} (T \ {b}) := by
    simp only [cross, Finset.sum_singleton]
    symm
    apply Finset.sum_subset Finset.sdiff_subset
    intro c hc hnot
    have hcb : c = b := by simpa [hc] using hnot
    subst c
    exact (G.contract π).diag b
  rw [he, cross_contract]
  · rfl
  · exact Finset.disjoint_left.mpr (fun c hc hd => (Finset.mem_sdiff.mp hd).2 hc)

/-- The additive degree oracle is a difference of three internal masses. -/
theorem residualDegree_sum_mass (G : WeightedGraph V) (π : V → B) (T A : Finset B) :
    subsetSum (G.residualDegree π T) A =
      (G.contract π).internalMass T + (G.contract π).internalMass (A ∩ T) -
        (G.contract π).internalMass (T \ (A ∩ T)) := by
  rw [residualDegree_sum]
  have hs : A ∩ T ⊆ T := Finset.inter_subset_right
  have hd : Disjoint (A ∩ T) (T \ (A ∩ T)) :=
    Finset.disjoint_left.mpr (fun b hb hr => (Finset.mem_sdiff.mp hr).2 hb)
  have hm := (G.contract π).internalMass_split hs
  rw [localCut_of_subset _ hs] at hm
  have hc : (G.contract π).cross (A ∩ T) T =
      (G.contract π).cross (A ∩ T) (A ∩ T) +
        (G.contract π).cross (A ∩ T) (T \ (A ∩ T)) := by
    rw [← cross_union_right _ _ _ _ hd, Finset.union_sdiff_of_subset hs]
  rw [hc]
  unfold internalMass at *
  linarith

end WeightedGraph

/-- A virtual subset-degree query uses exactly three original cut queries.
The cache contains original block cuts, not degrees of an induced quotient. -/
def residualDegreeQuery (π : V → B) (cache : B → ℝ) (T A : Finset B) :
    DTree (Finset V) ℝ ℝ 3 :=
  DTree.query (WeightedGraph.pull π (A ∩ T)) fun s =>
    DTree.query (WeightedGraph.pull π (T \ (A ∩ T))) fun r =>
      DTree.query (WeightedGraph.pull π T) fun t =>
        DTree.pure ((∑ b ∈ A ∩ T, cache b) + (r - s - t) / 2)

theorem residualDegreeQuery_run (G : WeightedGraph V) (π : V → B) (cache : B → ℝ)
    (hcache : ∀ b, cache b = G.cut (WeightedGraph.fiber π b)) (T A : Finset B) :
    (residualDegreeQuery π cache T A).run G.cut =
      (subsetSum (G.residualDegree π T) A, 3) := by
  simp only [residualDegreeQuery, DTree.run_query, DTree.run_pure, hcache]
  congr 1
  rw [WeightedGraph.residualDegree_sum_mass, WeightedGraph.residual_mass_formula,
    WeightedGraph.residual_mass_formula, WeightedGraph.residual_mass_formula]
  have hs : A ∩ T ⊆ T := Finset.inter_subset_right
  have hd : Disjoint (A ∩ T) (T \ (A ∩ T)) :=
    Finset.disjoint_left.mpr (fun b hb hr => (Finset.mem_sdiff.mp hr).2 hb)
  have he := Finset.sum_union hd (f := fun b => G.cut (WeightedGraph.fiber π b))
  rw [Finset.union_sdiff_of_subset hs] at he
  linarith

theorem residualDegreeQuery_eval (G : WeightedGraph V) (π : V → B) (cache : B → ℝ)
    (hcache : ∀ b, cache b = G.cut (WeightedGraph.fiber π b)) (T A : Finset B) :
    (residualDegreeQuery π cache T A).eval G.cut = subsetSum (G.residualDegree π T) A := by
  rw [DTree.eval, residualDegreeQuery_run G π cache hcache]

end
end CutQueryComplexity
