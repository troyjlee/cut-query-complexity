import CutQueryComplexity.UndirectedClosure.HierarchyBudget
import CutQueryComplexity.TreeCutSparsifier.Canonicalization
import CutQueryComplexity.TreeCutSparsifier.Endpoint

/-! # The conversion theorem for an arbitrary input tree

`supplied_hierarchy_log5` needs a hierarchy with childless terminal nodes and at most `2n + 1`
nodes whose canonical representation cost of some minimum cut is at most `B λ(G)`. An input
`B`-tree cut sparsifier with arbitrary terminal locations does not satisfy this directly;
normalizing its topology (`normalTopology`) does, by `normalTopology_rep_le`, with no loss in
`B`. `exists_conversion` passes the normalized topology to the supplied-hierarchy program, whose
cap `hierarchyBudget n B = O(n B L(n)⁵)` is independent of the input tree's size, and
`exists_conversion_log` restates the cap with the natural logarithm.

The output is the weak skeleton of `TwoRespecting.IsWeakSkeleton` (positive minimum cut and
`4 c_H(S*) ≤ 5 λ(H)` for some minimum shore `S*` of `G`), as exported by the existing
refinement endpoints.
-/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open WeightedGraph Hierarchy DetMinCut TwoRespecting UndirectedClosure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A `B`-approximating input tree supplies the promise of the supplied-hierarchy program on
its normalized topology. -/
theorem approximates_promise [Nonempty V] (input : TreeData V) (G : WeightedGraph V) {B : ℝ}
    (hn : 2 ≤ Fintype.card V) (h : input.Approximates G B) :
    ∃ S, IsMinCut G S ∧ (normalTopology input.tree).H.rep ((normalTopology input.tree).H.canon G) S ≤
      B * mincutValue G := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨S, hS, hval⟩ :=
    exists_isMinCut G ⟨{v}, (mem_properShores _).mpr (properShore_singleton v hn)⟩
  refine ⟨S, hS, ?_⟩
  rw [← hval]
  exact (input.normalTopology_rep_le G h.dom S).2.trans (h S).2

/-- **Conversion.** One decision tree per `n ≥ 2`, input tree and `B ≥ 1`, with cap
`hierarchyBudget n B ≤ C n B L(n)⁵` on every answer function, returning a weak skeleton of every
graph with positive minimum cut that the input tree approximates within `B`. -/
theorem exists_conversion :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B * (logL n : ℝ) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ IsWeakSkeleton G F := by
  refine ⟨hierarchyConstant + 1, by linarith [hierarchyConstant_pos],
    fun n input B hn hB => ?_⟩
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn' : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  refine ⟨hierarchyBudget (Fintype.card (Fin n)) B, by simpa using hierarchyBudget_le hn' hB,
    suppliedHierarchyTree (normalTopology input.tree) B, fun read => DTree.cost_le _ read,
    fun G hpos h => ?_⟩
  have hN := normalTopology_normal input.tree
  exact suppliedHierarchyTree_correct _ B G hn' hpos hB hN.leaves (by have := hN.size; omega)
    (approximates_promise input G hn' h)

/-- The conversion cap in the paper's notation: `O(n B log⁵(2n))`. -/
theorem exists_conversion_log :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B * (Real.log (2 * (n : ℝ))) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ IsWeakSkeleton G F := by
  obtain ⟨C, hC, hall⟩ := exists_conversion
  refine ⟨C * 3 ^ 5, by positivity, fun n input B hn hB => ?_⟩
  obtain ⟨q, hq, D, hcost, hcorrect⟩ := hall n input B hn hB
  refine ⟨q, hq.trans ?_, D, hcost, hcorrect⟩
  have hL := logL_le_real_log hn
  have hB0 : 0 ≤ B := by linarith
  calc C * n * B * (logL n : ℝ) ^ 5 ≤ C * n * B * (3 * Real.log (2 * (n : ℝ))) ^ 5 := by
        gcongr
    _ = C * 3 ^ 5 * n * B * (Real.log (2 * (n : ℝ))) ^ 5 := by ring

end CutQueryComplexity.TreeCutSparsifier
