import CutQueryComplexity.AllMinCuts.Skeleton
import CutQueryComplexity.TreeCutSparsifier.ConversionLogLog

/-! # Conversion of an explicit tree for all minimum cuts (all-minima plan, M1)

An explicit tree approximating *every* cut of `G` within `B` gives the universal promise of
`suppliedHierarchyProgLL_allMinCuts` on its normalized topology (`approximates_all_promise`):
`normalTopology_rep_le` makes the normalized representation cost no larger than the input's,
which is at most `B c_G(S) = B λ(G)` on every minimum cut `S`. A raw learned tree does not by
itself meet the size and leaf hypotheses of the supplied program; its normalized topology does.

`conversion_allMinCuts` runs the existing supplied-hierarchy program on the normalized topology
and returns an `AllMinCutSkeleton`, within the existing cost bound; `exists_conversion_allMinCuts`
is the capped decision-tree form, with the cap of `exists_conversion_log3loglog2`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllMinCuts

open WeightedGraph Hierarchy DetMinCut TwoRespecting UndirectedClosure TreeCutSparsifier

variable {V : Type} [Fintype V] [DecidableEq V]

/-- An input tree approximating every cut within `B` supplies the universal promise on its
normalized topology. -/
theorem approximates_all_promise [Nonempty V] (input : TreeData V) (G : WeightedGraph V) {B : ℝ}
    (h : input.Approximates G B) :
    ∀ S, IsMinCut G S → (normalTopology input.tree).H.rep
      ((normalTopology input.tree).H.canon G) S ≤ B * mincutValue G := by
  intro S hS
  rw [← isMinCut_of_sat hS]
  exact (input.normalTopology_rep_le G h.dom S).2.trans (h S).2

/-- **Conversion for all minimum cuts.** The supplied-hierarchy program on the normalized
topology of an input tree that approximates `G` within `B` returns an `AllMinCutSkeleton`, with
the existing cost bound. -/
theorem conversion_allMinCuts [Nonempty V] (input : TreeData V) {B : ℝ} (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) (hB : 1 ≤ B)
    (h : input.Approximates G B) :
    AllMinCutSkeleton G ((suppliedHierarchyProgLL (normalTopology input.tree) B).eval G.cut) ∧
      ((suppliedHierarchyProgLL (normalTopology input.tree) B).cost G.cut : ℝ) ≤
        hierarchyConstantLL * Fintype.card V * B *
          ((logL (Fintype.card V) : ℝ) ^ 3 * (logL (logL (Fintype.card V)) : ℝ) ^ 2) := by
  have hN := normalTopology_normal input.tree
  exact suppliedHierarchyProgLL_allMinCuts _ B G hn hpos hB hN.leaves
    (by have := hN.size; omega) (approximates_all_promise input G h)

/-- **Conversion for all minimum cuts, capped.** One decision tree per `n ≥ 2`, input tree and
`B ≥ 1`, with cap `O(n B L(n)³ L(L(n))²)` on every answer function, returning an
`AllMinCutSkeleton` of every graph with positive minimum cut that the input approximates within
`B`. -/
theorem exists_conversion_allMinCuts :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ AllMinCutSkeleton G F := by
  refine ⟨hierarchyConstantLL + 1, by linarith [hierarchyConstantLL_pos],
    fun n input B hn hB => ?_⟩
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn' : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  refine ⟨hierarchyBudgetLL (Fintype.card (Fin n)) B, by simpa using hierarchyBudgetLL_le hn' hB,
    suppliedHierarchyTreeLL (normalTopology input.tree) B, fun read => DTree.cost_le _ read,
    fun G hpos h => ?_⟩
  have hN := normalTopology_normal input.tree
  exact (suppliedHierarchyTreeLL_allMinCuts _ B G hn' hpos hB hN.leaves
    (by have := hN.size; omega) (approximates_all_promise input G h)).2

end CutQueryComplexity.AllMinCuts
