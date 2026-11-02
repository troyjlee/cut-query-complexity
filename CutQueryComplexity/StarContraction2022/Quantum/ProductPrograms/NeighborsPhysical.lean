import CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Neighbors

/-! # Physical correctness of the public center-neighborhood program

These are specializations of the accepted physical compiler to the actual
validated center-neighborhood tree. The routine remains normalized for every
finite physical reply table. Exact neighborhood recovery is asserted on honest
unit-capacity graph replies, using the proved validation and output laws.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms

noncomputable section
open QuantumQueryComplexity
open scoped Classical Matrix

attribute [local instance] basisDecidableEq workspaceDecidableEq

variable {n : ℕ}

/-- The concrete routine implements the concrete compiled algorithm for every
physical reply table, including tables that do not describe a graph. -/
theorem centerNeighborhoods_physical_state (R : Finset (Fin n))
    (read : Finset (Fin n) → CutAnswer n 1) :
    (productTreeRoutine (centerNeighborhoods R)).run read *ᵥ
        (productTreeAlg (centerNeighborhoods R)).init =
      (productTreeAlg (centerNeighborhoods R)).state read
        (12 * productBits n 1 * R.card) :=
  productTreeRoutine_state (centerNeighborhoods R) read

theorem centerNeighborhoods_physical_normalized (R : Finset (Fin n))
    (read : Finset (Fin n) → CutAnswer n 1) :
    IsQState ((productTreeRoutine (centerNeighborhoods R)).run read *ᵥ
      (productTreeAlg (centerNeighborhoods R)).init) :=
  productTreeRoutine_isQState (centerNeighborhoods R) read

/-- An exact Born-probability law for every possible neighborhood output. -/
theorem centerNeighborhoods_physical_prob (R : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) (out : Option (NeighborhoodTable n)) :
    (productTreeAlg (centerNeighborhoods R)).prob (capacityRead G)
        (12 * productBits n 1 * R.card) out =
      (PMF.pure (some (exactCenterNeighborhoodTable G R)) out).toReal := by
  rw [show 12 * productBits n 1 * R.card = physicalQueries n R.card from rfl,
    productTreeAlg_prob, centerNeighborhoods_run_honest, PMF.pure_map]

/-- The compiled public program recovers all requested rows with probability one. -/
theorem centerNeighborhoods_physical_successProb (R : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) :
    goodProb (productTreeAlg (centerNeighborhoods R)).readout
        (fun out => out = some (exactCenterNeighborhoodTable G R))
        ((productTreeAlg (centerNeighborhoods R)).state (capacityRead G)
          (12 * productBits n 1 * R.card)) = 1 := by
  rw [show 12 * productBits n 1 * R.card = physicalQueries n R.card from rfl,
    productTreeAlg_successProb, centerNeighborhoods_successProb_honest]

/-- The same success statement at the state produced by the actual routine. -/
theorem centerNeighborhoods_physical_run_successProb (R : Finset (Fin n))
    (G : CapacityGraph (Fin n) 1) :
    goodProb (productTreeAlg (centerNeighborhoods R)).readout
        (fun out => out = some (exactCenterNeighborhoodTable G R))
        ((productTreeRoutine (centerNeighborhoods R)).run (capacityRead G) *ᵥ
          (productTreeAlg (centerNeighborhoods R)).init) = 1 := by
  rw [centerNeighborhoods_physical_state, centerNeighborhoods_physical_successProb]

/-- A public center-cardinality guard bounds the actual physical schedule. -/
theorem centerNeighborhoods_physical_cap (R : Finset (Fin n))
    (k : ℕ) (hR : R.card ≤ k) :
    (productTreeRoutine (centerNeighborhoods R)).len ≤ 12 * logWidth n * k := by
  rw [centerNeighborhoods_physical_length]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 12 (productBits_le_logWidth n)) hR

#print axioms centerNeighborhoods_physical_state
#print axioms centerNeighborhoods_physical_normalized
#print axioms centerNeighborhoods_physical_prob
#print axioms centerNeighborhoods_physical_successProb
#print axioms centerNeighborhoods_physical_run_successProb
#print axioms centerNeighborhoods_physical_cap

end
end CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms
