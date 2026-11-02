import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Weighted directed graphs

The shared base for the directed weighted global-mincut certificates: a directed graph with nonnegative real
capacities and zero diagonal, and its outgoing cut function `F_G(S) = Σ_{u ∈ S, v ∉ S} c u v`, and reversal
(`rev_out : F_{rev G}(S) = F_G(Sᶜ)`).
-/

namespace CutQueryComplexity.DirectedCertificate

/-- A directed graph with nonnegative real capacities and zero diagonal. -/
structure WeightedDiGraph (V : Type*) where
  c : V → V → ℝ
  nonneg : ∀ u v, 0 ≤ c u v
  diag : ∀ v, c v v = 0

namespace WeightedDiGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedDiGraph V)
/-- Outgoing cut `F_G(S) = Σ_{u ∈ S, v ∉ S} c u v`. -/
def out (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, G.c u v

/-- Reversal of every arc. -/
def rev : WeightedDiGraph V where
  c u v := G.c v u
  nonneg u v := G.nonneg v u
  diag v := G.diag v

theorem rev_out (S : Finset V) : G.rev.out S = G.out Sᶜ := by
  simp only [out, rev, compl_compl]
  exact Finset.sum_comm
end WeightedDiGraph

end CutQueryComplexity.DirectedCertificate
