import CutQueryComplexity.DeterministicAPMCExpansion.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.GroupTheory.Perm.Basic

/-!
# Public perfect matchings and their multigraph history

Repeated edges in different rounds are added with multiplicity. Lazy walks
are an analysis device on the explicit history; they introduce no randomized
choice into the input-query program. The logarithmic strategy is not assumed
or claimed in this foundation module.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

structure Matching (V : Type) where
  mate : Equiv.Perm V
  involutive : Function.Involutive mate
  no_fixed : ∀ v, mate v ≠ v

namespace Matching

theorem paired_iff (M : Matching V) (u v : V) : M.mate u = v ↔ M.mate v = u := by
  constructor
  · intro h
    rw [← h, M.involutive]
  · intro h
    rw [← h, M.involutive]

def graph (M : Matching V) : WeightedGraph V where
  w u v := if M.mate u = v then 1 else 0
  symm u v := by simp only [M.paired_iff u v]
  nonneg u v := by split <;> norm_num
  diag u := by simp [M.no_fixed u]

/-- Every matched pair crosses the supplied public shore. -/
def Crosses (M : Matching V) (S : Finset V) : Prop :=
  ∀ v, v ∈ S ↔ M.mate v ∉ S

end Matching

structure Bisection (V : Type) [Fintype V] [DecidableEq V] where
  shore : Finset V
  balanced : shore.card = shoreᶜ.card

def graphAdd (G H : WeightedGraph V) : WeightedGraph V where
  w u v := G.w u v + H.w u v
  symm u v := by rw [G.symm u v, H.symm u v]
  nonneg u v := add_nonneg (G.nonneg u v) (H.nonneg u v)
  diag u := by rw [G.diag, H.diag, add_zero]

theorem graphAdd_cut (G H : WeightedGraph V) (S : Finset V) :
    (graphAdd G H).cut S = G.cut S + H.cut S := by
  simp only [cut, graphAdd, sum_add_distrib]

/-- The head is the newest round, so adjoining a matching is a public cons. -/
def historyGraph : List (Matching V) → WeightedGraph V
  | [] => 0
  | M :: history => graphAdd M.graph (historyGraph history)

@[simp] theorem historyGraph_nil_cut (S : Finset V) :
    (historyGraph ([] : List (Matching V))).cut S = 0 := by simp [historyGraph]

@[simp] theorem historyGraph_cons_cut (M : Matching V) (history : List (Matching V))
    (S : Finset V) :
    (historyGraph (M :: history)).cut S = M.graph.cut S + (historyGraph history).cut S :=
  graphAdd_cut _ _ _

theorem historyGraph_append_cut (left right : List (Matching V)) (S : Finset V) :
    (historyGraph (left ++ right)).cut S =
      (historyGraph left).cut S + (historyGraph right).cut S := by
  induction left with
  | nil => simp
  | cons M history ih => simp only [List.cons_append, historyGraph_cons_cut, ih]; ring

def average (M : Matching V) (p : V → ℝ) (v : V) : ℝ :=
  (p v + p (M.mate v)) / 2

theorem sum_average (M : Matching V) (p : V → ℝ) :
    (∑ v, average M p v) = ∑ v, p v := by
  simp only [average, ← sum_div, sum_add_distrib]
  rw [Equiv.sum_comp M.mate p]
  ring

def walk : List (Matching V) → V → V → ℝ
  | [], u, v => if u = v then 1 else 0
  | M :: history, u, v => average M (walk history u) v

theorem walk_nonneg (history : List (Matching V)) (u v : V) : 0 ≤ walk history u v := by
  induction history generalizing u v with
  | nil => simp only [walk]; split <;> norm_num
  | cons M history ih =>
      change 0 ≤ (walk history u v + walk history u (M.mate v)) / 2
      exact div_nonneg (add_nonneg (ih u v) (ih u (M.mate v))) (by norm_num)

theorem walk_row_sum (history : List (Matching V)) (u : V) :
    (∑ v, walk history u v) = 1 := by
  induction history with
  | nil => simp [walk]
  | cons M history ih => simpa only [walk, sum_average] using ih

theorem walk_column_sum (history : List (Matching V)) (v : V) :
    (∑ u, walk history u v) = 1 := by
  induction history generalizing v with
  | nil => simp [walk]
  | cons M history ih =>
      simp only [walk, average, ← sum_div, sum_add_distrib, ih]
      norm_num

/-- Conservative repair of the final pruning normalization. Here `x` counts
the shore vertices in the surviving graph; its expansion is only one-half.
The final matching contributes at least `w-2*x`. The two contributions together
give expansion one-quarter, sufficient after four fresh full runs. -/
theorem pruning_finish_quarter (n removed w x internal matching : ℝ)
    (hw : 2 * w ≤ n) (hremoved : 4 * removed ≤ n) (hx : x ≤ w)
    (hi : 0 ≤ internal) (hm : 0 ≤ matching)
    (hcut : min x (n - removed - x) ≤ 2 * internal)
    (hmatch : w - 2 * x ≤ matching) :
    w ≤ 4 * (internal + matching) := by
  by_cases hmin : x ≤ n - removed - x
  · rw [min_eq_left hmin] at hcut
    by_cases hhalf : w ≤ 2 * x
    · linarith
    · linarith
  · rw [min_eq_right (le_of_not_ge hmin)] at hcut
    linarith

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.historyGraph_append_cut
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.walk_row_sum
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.walk_column_sum
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pruning_finish_quarter
