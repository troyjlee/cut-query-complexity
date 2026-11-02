import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nonnegative weighted graphs and exact cut values

The basic representation and the complement/singleton proofs are adapted from
`ALW.WGraph` in the sibling `tcs-formalizations/ApersLeeWeighted.lean`.
An edge of weight zero is absent. A cut counts each crossing edge once.
-/

namespace CutQueryComplexity

/-- An undirected, loopless graph with nonnegative real weights. -/
@[ext] structure WeightedGraph (V : Type*) where
  w : V → V → ℝ
  symm : ∀ u v, w u v = w v u
  nonneg : ∀ u v, 0 ≤ w u v
  diag : ∀ v, w v v = 0

namespace WeightedGraph

variable {V : Type*}

/-- The graph with no positive edges. -/
instance : Zero (WeightedGraph V) := ⟨⟨fun _ _ => 0, by simp, by simp, by simp⟩⟩

@[simp] theorem zero_w (u v : V) : (0 : WeightedGraph V).w u v = 0 := rfl

/-- Multiplying all weights by a nonnegative real. -/
def scale (G : WeightedGraph V) (c : ℝ) (hc : 0 ≤ c) : WeightedGraph V where
  w u v := c * G.w u v
  symm u v := by rw [G.symm u v]
  nonneg u v := mul_nonneg hc (G.nonneg u v)
  diag v := by rw [G.diag, mul_zero]

variable [Fintype V] [DecidableEq V]

/-- Weight of the cut with shore `S`. -/
def cut (G : WeightedGraph V) (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, G.w u v

/-- Weighted degree, with the zero diagonal included in the sum. -/
def degree (G : WeightedGraph V) (v : V) : ℝ := ∑ u, G.w v u

theorem cut_nonneg (G : WeightedGraph V) (S : Finset V) : 0 ≤ G.cut S :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => G.nonneg _ _

@[simp] theorem cut_empty (G : WeightedGraph V) : G.cut ∅ = 0 := by simp [cut]

@[simp] theorem cut_univ (G : WeightedGraph V) : G.cut Finset.univ = 0 := by simp [cut]

@[simp] theorem cut_zero (S : Finset V) : (0 : WeightedGraph V).cut S = 0 := by
  simp [cut]

/-- Complementary shores name the same undirected cut. -/
@[simp] theorem cut_compl (G : WeightedGraph V) (S : Finset V) : G.cut Sᶜ = G.cut S := by
  rw [cut, cut, compl_compl, Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => G.symm v u

@[simp] theorem cut_singleton (G : WeightedGraph V) (v : V) :
    G.cut {v} = G.degree v := by
  rw [cut, Finset.sum_singleton, degree]
  have h := Finset.sum_add_sum_compl ({v} : Finset V) (fun u => G.w v u)
  simpa [G.diag] using h

@[simp] theorem cut_scale (G : WeightedGraph V) (c : ℝ) (hc : 0 ≤ c) (S : Finset V) :
    (G.scale c hc).cut S = c * G.cut S := by
  simp only [cut, scale, Finset.mul_sum]

/-- Degree mass equals cut mass plus twice the internal edge mass. -/
theorem cut_add_internal (G : WeightedGraph V) (S : Finset V) :
    G.cut S + (∑ u ∈ S, ∑ v ∈ S, G.w u v) = ∑ u ∈ S, G.degree u := by
  rw [cut, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => by
    rw [add_comm]
    exact Finset.sum_add_sum_compl S (fun v => G.w u v)

/-- The three-cut identity that recovers an individual edge weight. -/
theorem edge_eq_three_cuts (G : WeightedGraph V) {u v : V} (huv : u ≠ v) :
    G.w u v = (G.cut {u} + G.cut {v} - G.cut {u, v}) / 2 := by
  have h := G.cut_add_internal {u, v}
  simp [Finset.sum_pair huv, G.diag, G.symm v u] at h
  rw [G.cut_singleton, G.cut_singleton]
  linarith

/-- Express a cut as a sum over a fixed domain, useful for cut inequalities. -/
theorem cut_eq_sum_ite (G : WeightedGraph V) (S : Finset V) :
    G.cut S = ∑ u, ∑ v, if u ∈ S ∧ v ∉ S then G.w u v else 0 := by
  classical
  have hcomp : Sᶜ = Finset.univ.filter (fun v => v ∉ S) := by ext; simp
  simp only [cut, Finset.sum_ite_irrel, ite_and]
  simp only [hcomp, Finset.sum_filter]
  simp

/-- Nonnegative undirected cut functions are submodular. -/
theorem cut_submodular (G : WeightedGraph V) (S T : Finset V) :
    G.cut (S ∪ T) + G.cut (S ∩ T) ≤ G.cut S + G.cut T := by
  simp only [cut_eq_sum_ite, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  by_cases huS : u ∈ S <;> by_cases huT : u ∈ T <;>
    by_cases hvS : v ∈ S <;> by_cases hvT : v ∈ T <;>
    simp [huS, huT, hvS, hvT, G.nonneg u v]

end WeightedGraph
end CutQueryComplexity
