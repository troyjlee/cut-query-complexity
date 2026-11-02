import CutQueryComplexity.Quantum.LinearReconstruction.Graph
import CutQueryComplexityChecks.AxiomAudit

namespace CutQueryComplexityChecks.CoverageQuantumReconstruction
open CutQueryComplexity
open CutQueryComplexity.Quantum.LinearReconstruction
open CutQueryComplexity.StarContraction2022.Quantum
open QuantumQueryComplexity
open scoped Classical Matrix
noncomputable section
attribute [local instance]
  CutQueryComplexity.Quantum.LinearReconstruction.graphAnswerDecidableEq
  CutQueryComplexity.Quantum.LinearReconstruction.graphWorkDecidableEq
  CutQueryComplexity.Quantum.LinearReconstruction.basisDecidableEq

/-- The physical circuit is fixed before the bounded graph; its schedule counts
every native cut-oracle call and the final state contains the entire graph. -/
theorem physical_public_reconstruction (n W : ℕ) :
    ∃ R : QRoutine (Finset (Fin n)) (CutAnswer n W) (GraphWork n W),
      R = recoverGraph n W ∧ R.len = n * (6 * Nat.clog 2 (W + 1)) ∧
      ∀ G : CapacityGraph (Fin n) W,
        R.run (capacityRead G) *ᵥ
          qBasis (none, none, graphZero n W, rowZero n W) =
          qBasis (none, none, graphRead G, rowZero n W) := by
  exact ⟨recoverGraph n W, rfl, recoverGraph_len n W, fun G => recoverGraph_run G⟩

theorem unit_and_symmetrized_counts (n : ℕ) :
    (recoverGraph n 1).len = 6 * n ∧ (recoverGraph n 2).len = 12 * n :=
  ⟨recoverGraph_len_unit n, recoverGraph_len_two n⟩

theorem no_honesty_needed_for_normalization (n W : ℕ)
    (read : Finset (Fin n) → CutAnswer n W) :
    ∑ y, (recoverGraphAlg n W).prob read (n * (6 * rowBits W)) y = 1 :=
  recoverGraphAlg_normalized n W read _

end
end CutQueryComplexityChecks.CoverageQuantumReconstruction

#audit_cut_axioms [CutQueryComplexity.Quantum.LinearReconstruction.Row,
  CutQueryComplexity.Quantum.LinearReconstruction.Graph] pins [
  CutQueryComplexity.Quantum.LinearReconstruction.recoverRow_len,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverRow_run_coherent,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraph_run,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraphAlg_born,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraphAlg_normalized,
  CutQueryComplexity.Quantum.LinearReconstruction.graphToCapacity_read,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraph_len_unit,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraph_len_two]
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantumReconstruction.physical_public_reconstruction
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantumReconstruction.unit_and_symmetrized_counts
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantumReconstruction.no_honesty_needed_for_normalization
