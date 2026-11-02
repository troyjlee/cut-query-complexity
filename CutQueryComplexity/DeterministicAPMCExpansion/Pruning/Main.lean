import CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.PartitionMap
import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Parameters
import CutQueryComplexity.DeterministicAPMCExpansion.AdditiveShaving
import CutQueryComplexity.DeterministicAPMCExpansion.Padding

/-!
# Uniform deterministic all-pairs program from the pruning construction

The definitions choose every public parameter and every query procedure
before the hidden graph. Decomposition supplies its representative map;
the existing shaving and star-recovery programs then produce exact answers.
The triangle-padding adapter removes the minimum-degree precondition.

This file gives the operational endpoint and its correctness composition.
The explicit five-thirds asymptotic bound is in `Pruning/Budget.lean`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open Finset AllPairs AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def coreBudget (V : Type) [Fintype V] : ℕ :=
  Decomposition.queryBudget (Fintype.card V) (roundBudget (Fintype.card V)) (cubeRoot (Fintype.card V)) +
    partitionRecoveryBudget V (2 * cubeRoot (Fintype.card V))
      (8 * roundBudget (Fintype.card V)) (cubeRoot (Fintype.card V) ^ 2)

def minimumDegreeProgram : DTree (Finset V) ℝ (Answers V) (coreBudget V) :=
  (Decomposition.decomposition (roundBudget (Fintype.card V)) (cubeRoot (Fintype.card V))
    (by have h := roundBudget_ge_two (Fintype.card V); omega)).bind fun result =>
      totalPartitionAnswers result.representativeMap (2 * cubeRoot (Fintype.card V))
        (8 * roundBudget (Fintype.card V)) (cubeRoot (Fintype.card V) ^ 2)

theorem minimumDegreeProgram_correct (G : WeightedGraph V) (hG : Unweighted G)
    (hdegree : ∀ v, 2 ≤ G.degree v) :
    allPairsGood G ((minimumDegreeProgram (V := V)).eval G.cut) := by
  let N := Fintype.card V
  let R := roundBudget N
  let t := cubeRoot N
  have hR : 1 ≤ R := by have h := roundBudget_ge_two N; omega
  have ht : 0 < t := cubeRoot_pos N
  let result := (Decomposition.decomposition (V := V) R t hR).eval G.cut
  have hc : result.Correct G t := Decomposition.decomposition_correct G hG R t hR
    (by omega) (le_cubeRoot_pow N) (fun q hq => local_rounds_le hq)
  have hexpand := result.representativeMap_additive G t hc
  have hboundary := result.representativeMap_boundary G t hc
  have hN : Fintype.card V ≤ (2 * t) * t ^ 2 := by
    have h := le_cubeRoot_pow N
    change N ≤ t ^ 3 at h
    change N ≤ (2 * t) * t ^ 2
    nlinarith
  simp only [minimumDegreeProgram, coreBudget, DTree.eval_bind]
  exact totalPartitionAnswers_correct hG hdegree result.representativeMap
    (by omega : 0 < 2 * t) (by omega : 0 < 8 * R) (pow_pos ht 2)
    hN hexpand hboundary

def budget (n : ℕ) : ℕ := coreBudget (Padded (Fin n))

def program (n : ℕ) : DTree (Finset (Fin n)) ℝ (Answers (Fin n)) (budget n) :=
  unpadProgram (minimumDegreeProgram (V := Padded (Fin n)))

theorem program_correct (n : ℕ) (G : WeightedGraph (Fin n)) (hG : Unweighted G) :
    allPairsGood G ((program n).eval G.cut) := by
  apply unpadProgram_correct
  apply minimumDegreeProgram_correct (paddedGraph G) (padded_unweighted hG)
  exact padded_min_degree G

theorem program_cost (n : ℕ) (read : Finset (Fin n) → ℝ) :
    (program n).cost read ≤ budget n := DTree.cost_le _ _

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.minimumDegreeProgram_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_cost
