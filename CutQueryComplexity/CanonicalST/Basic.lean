import CutQueryComplexity.AllPairsAudit.CutAlgebra
import CutQueryComplexity.Graph.Integral
import Mathlib.Tactic

/-!
# Public core data and its proof-only interpretation

`CoreData` contains explicit unit graphs and the cached current induced degrees.
The hidden input appears only in `CoreSpec`; neither a query algorithm nor a
canonical-optimum theorem is a field of either record.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Public output of degree peeling and seed discovery. The degree cache is
obtained from measured degrees by subtracting learned incidences. -/
structure CoreData (V : Type) [Fintype V] where
  C : Finset V
  K : WeightedGraph V
  J : WeightedGraph V
  K_unit : AllPairsAudit.Unweighted K
  J_unit : AllPairsAudit.Unweighted J
  coreDegrees : V → ℝ

/-- Recover the original measured degree from the learned outside graph and
the maintained core degree, without another oracle call. -/
def CoreData.measuredDegree (A : CoreData V) (v : V) : ℝ :=
  A.K.degree v + A.coreDegrees v

/-- Semantic invariant for the actual input. Bounds concern undirected edge
mass, which equals the number of edges for these explicit unit graphs. -/
structure CoreSpec (G : WeightedGraph V) (D : ℕ) (A : CoreData V) : Prop where
  K_exact : ∀ u v, A.K.w u v = if u ∈ A.C ∧ v ∈ A.C then 0 else G.w u v
  J_le : A.J.IsSubgraph G
  J_supported : ∀ u v, u ∉ A.C ∨ v ∉ A.C → A.J.w u v = 0
  degrees_eq : ∀ v, A.coreDegrees v = (G.induce A.C).degree v
  min_degree : ∀ v ∈ A.C, (D : ℝ) ≤ A.J.degree v
  K_size : A.K.edgeMass < (Fintype.card V : ℝ) * D
  J_size : A.J.edgeMass ≤ (A.C.card : ℝ) * D

namespace CoreSpec

variable {G : WeightedGraph V} {D : ℕ} {A : CoreData V} (h : CoreSpec G D A)

include h

theorem K_le : A.K.IsSubgraph G := by
  intro u v
  rw [h.K_exact]
  split_ifs
  · exact G.nonneg u v
  · exact le_rfl

theorem J_core_le : A.J.IsSubgraph (G.induce A.C) := by
  intro u v
  by_cases hu : u ∈ A.C
  · by_cases hv : v ∈ A.C
    · simpa [WeightedGraph.induce, hu, hv] using h.J_le u v
    · simp [WeightedGraph.induce, hu, hv, h.J_supported u v (Or.inr hv)]
  · simp [WeightedGraph.induce, hu, h.J_supported u v (Or.inl hu)]

theorem K_J_disjoint (u v : V) : A.K.w u v = 0 ∨ A.J.w u v = 0 := by
  by_cases hu : u ∈ A.C
  · by_cases hv : v ∈ A.C
    · exact Or.inl (by rw [h.K_exact]; simp [hu, hv])
    · exact Or.inr (h.J_supported u v (Or.inr hv))
  · exact Or.inr (h.J_supported u v (Or.inl hu))

/-- The actual initial learned graph remains below the hidden input. -/
theorem K_add_J_le : (A.K.add A.J).IsSubgraph G := by
  intro u v
  rcases h.K_J_disjoint u v with hk | hj
  · simpa only [add_w, hk, zero_add] using h.J_le u v
  · simpa only [add_w, hj, add_zero] using h.K_le u v

theorem K_add_J_unit : AllPairsAudit.Unweighted (A.K.add A.J) := by
  intro u v
  rcases h.K_J_disjoint u v with hk | hj
  · simpa only [add_w, hk, zero_add] using A.J_unit u v
  · simpa only [add_w, hj, add_zero] using A.K_unit u v

/-- This is the exact original-graph identity used by canonical extension. -/
theorem K_add_induce_eq : A.K.add (G.induce A.C) = G := by
  ext u v
  rw [add_w, h.K_exact]
  by_cases huv : u ∈ A.C ∧ v ∈ A.C <;> simp [WeightedGraph.induce, huv]

theorem measuredDegree_eq (v : V) : A.measuredDegree v = G.degree v := by
  calc
    A.measuredDegree v = (A.K.add (G.induce A.C)).degree v := by
      simp [CoreData.measuredDegree, h.degrees_eq, WeightedGraph.degree,
        sum_add_distrib]
    _ = G.degree v := congrArg (fun H : WeightedGraph V => H.degree v) h.K_add_induce_eq

theorem empty_core_learns_all (hC : A.C = ∅) : A.K = G := by
  ext u v
  simpa [hC] using h.K_exact u v

end CoreSpec

end
end CutQueryComplexity.CanonicalST

#print axioms CutQueryComplexity.CanonicalST.CoreSpec.K_le
#print axioms CutQueryComplexity.CanonicalST.CoreSpec.J_core_le
#print axioms CutQueryComplexity.CanonicalST.CoreSpec.K_J_disjoint
#print axioms CutQueryComplexity.CanonicalST.CoreSpec.K_add_J_le
#print axioms CutQueryComplexity.CanonicalST.CoreSpec.K_add_J_unit
#print axioms CutQueryComplexity.CanonicalST.CoreSpec.K_add_induce_eq
#print axioms CutQueryComplexity.CanonicalST.CoreSpec.measuredDegree_eq
#print axioms CutQueryComplexity.CanonicalST.CoreSpec.empty_core_learns_all
