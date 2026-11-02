import CutQueryComplexity.Graph.Directed
import CutQueryComplexity.Model.Reduction

/-! # Directed pair counts from three outgoing-cut queries (D1)

`pairQuery A B` asks `F(A)`, `F(B)`, `F(A ∪ B)` and returns `F(A) + F(B) − F(A ∪ B)`, which for
disjoint shores is the pair count `Σ_{u∈A, v∈B} sym u v` (`pairQuery_eval`). With `A = {v}`,
`nbrCount v Y` is the filtered neighbor count `N(v, Y) = Σ_{u∈Y} sym v u` for `v ∉ Y`; it is
zero exactly when no actual pair joins `v` to `Y`.
-/

namespace CutQueryComplexity

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The pair count between two shores, from three outgoing-cut queries. -/
def pairQuery (A B : Finset V) : DTree (Finset V) ℕ ℕ 3 :=
  DTree.query A fun a => DTree.query B fun b =>
    DTree.query (A ∪ B) fun c => DTree.pure (a + b - c)

theorem pairQuery_run (G : DiGraph V) {A B : Finset V} (h : Disjoint A B) :
    DTree.run G.out (pairQuery A B) = (G.pairs A B, 3) := by
  simp only [pairQuery, DTree.run_query, DTree.run_pure]
  rw [G.pairs_eq_out h]

@[simp] theorem pairQuery_eval (G : DiGraph V) {A B : Finset V} (h : Disjoint A B) :
    (pairQuery A B).eval G.out = G.pairs A B := by
  rw [DTree.eval, pairQuery_run G h]

/-- The filtered neighbor count `N(v, Y)`. -/
def nbrCount (v : V) (Y : Finset V) : DTree (Finset V) ℕ ℕ 3 := pairQuery {v} Y

theorem nbrCount_eval (G : DiGraph V) {v : V} {Y : Finset V} (hv : v ∉ Y) :
    (nbrCount v Y).eval G.out = ∑ u ∈ Y, G.sym v u := by
  rw [nbrCount, pairQuery_eval G (disjoint_singleton_left.mpr hv), DiGraph.pairs,
    sum_singleton]

theorem nbrCount_eq_zero_iff (G : DiGraph V) {v : V} {Y : Finset V} (hv : v ∉ Y) :
    (nbrCount v Y).eval G.out = 0 ↔ ∀ u ∈ Y, G.sym v u = 0 := by
  rw [nbrCount_eval G hv, sum_eq_zero_iff]

end CutQueryComplexity
