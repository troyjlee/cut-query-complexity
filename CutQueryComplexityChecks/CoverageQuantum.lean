import CutQueryComplexity.Coverage.Quantum
import CutQueryComplexityChecks.AxiomAudit

namespace CutQueryComplexityChecks.CoverageQuantum
open CutQueryComplexity QuantumQueryComplexity
open CutQueryComplexity.StarContraction2022.Quantum
open scoped Classical Matrix
noncomputable section

namespace Undirected
open CutQueryComplexity.Quantum.LinearReconstruction
attribute [local instance]
  CutQueryComplexity.Quantum.LinearReconstruction.graphAnswerDecidableEq
  CutQueryComplexity.Quantum.LinearReconstruction.graphWorkDecidableEq
  CutQueryComplexity.Quantum.LinearReconstruction.basisDecidableEq

/-- The native circuit and its public postprocessor are fixed before the graph.
Every oracle table normalizes, and the counted routine is the executed routine. -/
theorem public_physical_allPairs (n : ℕ) :
    ∃ (T : CutQAlg n 1 (AllPairs.Answers (Fin n)) (GraphWork n 1))
      (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) (GraphWork n 1)),
      T = allPairsAlg n 1 ∧ R = endpointRoutine n 1 ∧ R.len ≤ 6 * n ∧
      (∀ read, R.run read *ᵥ T.init = T.state read R.len) ∧
      (∀ read k, IsQState (T.state read k)) ∧
      ∀ G : CapacityGraph (Fin n) 1,
        successProbOn T R.len capacityRead
          (fun G a => ∀ s t, s ≠ t →
            (s ∈ (a s t).shore ∧ t ∉ (a s t).shore ∧
              ∀ S, s ∈ S → t ∉ S → G.toWeighted.cut (a s t).shore ≤ G.toWeighted.cut S) ∧
            (a s t).value = G.toWeighted.cut (a s t).shore) G = 1 := by
  refine ⟨allPairsAlg n 1, endpointRoutine n 1, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [endpointRoutine_len]
    exact endpointBudget_unit n
  · intro read
    exact (QRoutine.toAlg_state_len _ _ _ _ read).symm
  · intro read k
    exact (allPairsAlg n 1).state_isQState read k
  · intro G
    rw [endpointRoutine_len]
    exact reconstructAlg_good _ G _ (graphAnswers_good G)

/-- Literal original terminal shore and value, with the equal-terminal convention. -/
theorem original_terminal (n : ℕ) (s t : Fin n) (G : CapacityGraph (Fin n) 1) :
    successProbOn (terminalAlg n 1 s t) (endpointBudget n 1) capacityRead
      (fun G o => (if s = t then o.shore = ∅ else
        s ∈ o.shore ∧ t ∉ o.shore ∧
          ∀ S, s ∈ S → t ∉ S → G.toWeighted.cut o.shore ≤ G.toWeighted.cut S) ∧
        o.value = G.toWeighted.cut o.shore) G = 1 :=
  reconstructAlg_good _ G _ (terminalAnswer_good G s t)

theorem tiny_has_zero_native_calls (n : ℕ) (hn : n ≤ 1) :
    (endpointRoutine n 1).len = 0 := by
  rw [endpointRoutine_len, endpointBudget_tiny hn]

/-- Integral capacities at most `W`: the literal native budget, and probability-one
original global shores and values. -/
theorem capacity_global (n W : ℕ) (hn : 2 ≤ n) (G : CapacityGraph (Fin n) W) :
    endpointBudget n W ≤ n * (6 * Nat.clog 2 (W + 1)) ∧
    successProbOn (globalReconstructAlg n W) (endpointBudget n W) capacityRead
      (fun G o => IsMinCut G.toWeighted o.shore ∧ o.value = G.toWeighted.cut o.shore) G = 1 :=
  ⟨endpointBudget_le n W, by convert globalReconstructAlg_success hn G; exact Iff.rfl⟩

end Undirected

namespace Directed
open CutQueryComplexity.Quantum.DirectedReconstruction
open CutQueryComplexity.DirectedCertificate
attribute [local instance]
  CutQueryComplexity.Quantum.DirectedReconstruction.basisDecidableEq
  CutQueryComplexity.Quantum.DirectedReconstruction.directedWorkDecidableEq

/-- This is the same physical circuit, with the four symmetrization calls and
two singleton/complement calls per vertex charged explicitly. -/
theorem public_physical_allPairs (n : ℕ) :
    ∃ (T : CutQAlg n 1 (AllPairs.Answers (Fin n)) (DirectedWork n))
      (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) (DirectedWork n)),
      T = allPairsAlg n ∧ R = allPairsRoutine n ∧
      R.len = (if n ≤ 1 then 0 else 4 * (12 * n) + 2 * n) ∧
      (∀ read, R.run read *ᵥ T.init = T.state read R.len) ∧
      (∀ read k, IsQState (T.state read k)) ∧
      ∀ (G : DiGraph (Fin n)) (hG : G.Simple),
        goodProb T.readout (AllPairsGood G) (T.state (unitRead G hG) R.len) = 1 := by
  refine ⟨allPairsAlg n, allPairsRoutine n, rfl, rfl, ?_,
    allPairsRoutine_state n, fun read k => (allPairsAlg n).state_isQState read k,
    allPairs_correct n⟩
  rw [allPairsRoutine_len]
  split_ifs <;> omega

theorem original_global (n : ℕ) (G : DiGraph (Fin n)) (hG : G.Simple) :
    @goodProb _ _ _ (globalAlg n).readout
      (fun o => if n ≤ 1 then o = (⟨∅, 0⟩ : AllPairs.STAnswer (Fin n)) else
        (ProperShore o.shore ∧ ∀ S, ProperShore S →
          (realGraph G).out o.shore ≤ (realGraph G).out S) ∧
          o.value = (G.out o.shore : ℝ) ∧ o.value = (realGraph G).minValue)
      (fun _ => Classical.propDecidable _)
      ((globalAlg n).state (unitRead G hG) (if n ≤ 1 then 0 else 50 * n)) = 1 :=
  global_correct n G hG

theorem original_terminal (n : ℕ) (s t : Fin n) (G : DiGraph (Fin n)) (hG : G.Simple) :
    @goodProb _ _ _ (terminalAlg s t).readout
      (fun o => if s = t then o = (⟨∅, 0⟩ : AllPairs.STAnswer (Fin n)) else
        s ∈ o.shore ∧ t ∉ o.shore ∧ o.value = (G.out o.shore : ℝ) ∧
          ∀ S, s ∈ S → t ∉ S → (G.out o.shore : ℝ) ≤ G.out S)
      (fun _ => Classical.propDecidable _)
      ((terminalAlg s t).state (unitRead G hG) (if s = t then 0 else 50 * n)) = 1 :=
  terminal_correct s t G hG

theorem original_allPairs (n : ℕ) (G : DiGraph (Fin n)) (hG : G.Simple) :
    @goodProb _ _ _ (allPairsAlg n).readout
      (fun a => ∀ s t, if s = t then a s t = (⟨∅, 0⟩ : AllPairs.STAnswer (Fin n)) else
        s ∈ (a s t).shore ∧ t ∉ (a s t).shore ∧ (a s t).value = (G.out (a s t).shore : ℝ) ∧
          ∀ S, s ∈ S → t ∉ S → (G.out (a s t).shore : ℝ) ≤ G.out S)
      (fun _ => Classical.propDecidable _)
      ((allPairsAlg n).state (unitRead G hG) (if n ≤ 1 then 0 else 50 * n)) = 1 :=
  allPairs_correct n G hG

end Directed
end
end CutQueryComplexityChecks.CoverageQuantum

#audit_cut_axioms [CutQueryComplexity.Quantum.LinearReconstruction.Row,
  CutQueryComplexity.Quantum.LinearReconstruction.Graph,
  CutQueryComplexity.Quantum.LinearReconstruction.Endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.Oracle,
  CutQueryComplexity.Quantum.DirectedReconstruction.Program,
  CutQueryComplexity.Quantum.DirectedReconstruction.Endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.Capacity] pins [
  CutQueryComplexity.Quantum.LinearReconstruction.recoverRow_run_coherent,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraph_run,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraphAlg_born,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_unit_terminal,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_unit_allPairs,
  CutQueryComplexity.Quantum.LinearReconstruction.allPairsAlg_simple_success,
  CutQueryComplexity.Quantum.LinearReconstruction.globalReconstructAlg_success,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_capacity_global,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_capacity_terminal,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_capacity_allPairs,
  CutQueryComplexity.Quantum.DirectedReconstruction.symCall_run_honest,
  CutQueryComplexity.Quantum.DirectedReconstruction.symAlg_prob,
  CutQueryComplexity.Quantum.DirectedReconstruction.withImbalance_prob,
  CutQueryComplexity.Quantum.DirectedReconstruction.recoverDirected_out_prob,
  CutQueryComplexity.Quantum.DirectedReconstruction.recoverDirectedRoutine_len,
  CutQueryComplexity.Quantum.DirectedReconstruction.physical_global_endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.physical_terminal_endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.physical_allPairs_endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.symAlgW_prob,
  CutQueryComplexity.Quantum.DirectedReconstruction.recoverDirectedW_prob,
  CutQueryComplexity.Quantum.DirectedReconstruction.directedBudget_le,
  CutQueryComplexity.Quantum.DirectedReconstruction.directedBudget_unit,
  CutQueryComplexity.Quantum.DirectedReconstruction.exists_capacity_global,
  CutQueryComplexity.Quantum.DirectedReconstruction.exists_capacity_terminal,
  CutQueryComplexity.Quantum.DirectedReconstruction.exists_capacity_allPairs]
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantum.Undirected.public_physical_allPairs
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantum.Undirected.original_terminal
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantum.Undirected.tiny_has_zero_native_calls
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantum.Undirected.capacity_global
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantum.Directed.public_physical_allPairs
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantum.Directed.original_global
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantum.Directed.original_terminal
#audit_cut_decl CutQueryComplexityChecks.CoverageQuantum.Directed.original_allPairs
