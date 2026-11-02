import CutQueryComplexity.Graph.Operations
import CutQueryComplexity.Model.Reduction

/-! # Concrete cut-query implementations of graph reductions -/

namespace CutQueryComplexity

noncomputable section
open scoped Classical

variable {V B : Type} [Fintype V] [DecidableEq V]

/-- A whole cross-weight answer from three cuts. -/
def crossQuery (S T : Finset V) : DTree (Finset V) ℝ ℝ 3 :=
  DTree.query S fun a => DTree.query T fun b =>
    DTree.query (S ∪ T) fun c => DTree.pure ((a + b - c) / 2)

theorem crossQuery_run (G : WeightedGraph V) {S T : Finset V} (h : Disjoint S T) :
    DTree.run G.cut (crossQuery S T) = (G.cross S T, 3) := by
  simp only [crossQuery, DTree.run_query, DTree.run_pure]
  rw [G.cross_eq_three_cuts h]

@[simp] theorem crossQuery_eval (G : WeightedGraph V) {S T : Finset V} (h : Disjoint S T) :
    (crossQuery S T).eval G.cut = G.cross S T := by rw [DTree.eval, crossQuery_run G h]

/-- Bipartite independent-set access, with the same three-query cost. -/
def bisQuery (S T : Finset V) : DTree (Finset V) ℝ Bool 3 :=
  (crossQuery S T).map (fun w => decide (0 < w))

theorem bisQuery_correct (G : WeightedGraph V) {S T : Finset V} (h : Disjoint S T) :
    (bisQuery S T).eval G.cut = true ↔ ∃ u ∈ S, ∃ v ∈ T, 0 < G.w u v := by
  simp only [bisQuery, DTree.eval_map, crossQuery_eval G h, decide_eq_true_eq]
  exact G.cross_pos_iff S T

/-- Query the induced graph while using only the original oracle. -/
def inducedQuery (U S : Finset V) : DTree (Finset V) ℝ ℝ 3 :=
  crossQuery (S ∩ U) (U \ S)

theorem inducedQuery_eval (G : WeightedGraph V) (U S : Finset V) :
    (inducedQuery U S).eval G.cut = (G.induce U).cut S := by
  rw [inducedQuery, crossQuery_eval, G.cut_induce]
  exact Finset.disjoint_left.mpr (fun x hx hy =>
    (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hx).1)

/-- Subtract the known contribution locally; one original cut query is charged. -/
def deletionQuery (K : WeightedGraph V) (S : Finset V) : DTree (Finset V) ℝ ℝ 1 :=
  DTree.query S fun w => DTree.pure (w - K.cut S)

theorem deletionQuery_eval (G K : WeightedGraph V) (h : ∀ u v, K.w u v ≤ G.w u v)
    (S : Finset V) : (deletionQuery K S).eval G.cut = (G.subtract K).cut S := by
  simp only [deletionQuery, DTree.eval_query, DTree.eval_pure, G.cut_subtract K h]

variable [Fintype B] [DecidableEq B]

/-- A public quotient query lifts to one shore of the original graph. -/
def contractionQuery (π : V → B) (T : Finset B) : DTree (Finset V) ℝ ℝ 1 :=
  DTree.query (WeightedGraph.pull π T) fun w => DTree.pure w

theorem contractionQuery_eval (G : WeightedGraph V) (π : V → B) (T : Finset B) :
    (contractionQuery π T).eval G.cut = (G.contract π).cut T := by
  simp only [contractionQuery, DTree.eval_query, DTree.eval_pure, G.cut_contract]

/-- Every adaptive `q`-query induced-graph program costs at most `3*q` original queries. -/
theorem induced_program {O : Type} {q : ℕ} (T : DTree (Finset V) ℝ O q)
    (U : Finset V) (G : WeightedGraph V) :
    (T.substitute (inducedQuery U)).eval G.cut = T.eval (G.induce U).cut := by
  simp only [DTree.eval_substitute, inducedQuery_eval]

/-- Every adaptive quotient program is implemented with one original query per call. -/
theorem contraction_program {O : Type} {q : ℕ} (T : DTree (Finset B) ℝ O q)
    (π : V → B) (G : WeightedGraph V) :
    (T.substitute (contractionQuery π)).eval G.cut = T.eval (G.contract π).cut := by
  simp only [DTree.eval_substitute, contractionQuery_eval]

end
end CutQueryComplexity
