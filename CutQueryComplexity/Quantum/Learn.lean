import CutQueryComplexity.Primitive.Learn
import CutQueryComplexity.Quantum.ClassicalCompiler

/-! # End-to-end edge recovery in the three query models -/

namespace CutQueryComplexity

open QuantumQueryComplexity
open scoped Classical

noncomputable section

variable {n W : ℕ}

/-- The same three-query edge program, reading finite capacity answers. -/
def capacityEdgeRecovery (u v : Fin n) : DTree (Finset (Fin n)) (CutAnswer n W) ℝ 3 :=
  (edgeRecovery u v).mapAnswers (fun a => (a.val : ℝ))

theorem capacityEdgeRecovery_run (G : CapacityGraph (Fin n) W) {u v : Fin n}
    (huv : u ≠ v) : DTree.run (capacityRead G) (capacityEdgeRecovery u v) =
      (((G.w u v : ℕ) : ℝ), 3) := by
  have hread : (fun a : CutAnswer n W => (a.val : ℝ)) ∘ capacityRead G = G.toWeighted.cut := by
    funext S
    simp [Function.comp_def]
  rw [capacityEdgeRecovery, DTree.run_mapAnswers, hread, edgeRecovery_run G.toWeighted huv]
  rfl

/-- The finite-answer deterministic program solves edge recovery exactly. -/
theorem capacityEdgeRecovery_solves {u v : Fin n} (huv : u ≠ v) :
    (capacityEdgeRecovery (W := W) u v).Solves capacityRead
      (fun G w => w = (G.w u v : ℕ)) := by
  intro G
  simp [DTree.eval, capacityEdgeRecovery_run G huv]

/-- The randomized embedding preserves the three queries and has zero error. -/
theorem capacityEdgeRecovery_randomized {u v : Fin n} (huv : u ≠ v) :
    (RTree.ofDeterministic (capacityEdgeRecovery (W := W) u v)).SolvesWithError capacityRead
      (fun G w => w = (G.w u v : ℕ)) 0 :=
  RTree.ofDeterministic_solves (capacityEdgeRecovery_solves huv)

/-- An actual finite-workspace quantum algorithm recovers the edge in three queries. -/
theorem capacityEdgeRecovery_quantum {u v : Fin n} (huv : u ≠ v) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work) (T : CutQAlg n W ℝ Work),
      SolvesWithErrorOn T 3 capacityRead (fun G w => w = (G.w u v : ℕ)) 0 := by
  obtain ⟨Work, hWork, hWorkEq, T, hT⟩ :=
    DTree.exists_quantum (capacityEdgeRecovery (W := W) u v) capacityRead
  refine ⟨Work, hWork, hWorkEq, T, solvesWithErrorOn_eq_iff.mpr ?_⟩
  have heval : (fun G => (capacityEdgeRecovery (W := W) u v).eval (capacityRead G)) =
      (fun G : CapacityGraph (Fin n) W => ((G.w u v : ℕ) : ℝ)) := by
    funext G
    simp [DTree.eval, capacityEdgeRecovery_run G huv]
  rwa [heval] at hT

/-- The three-query witness bounds relational quantum edge-recovery complexity. -/
theorem quantum_edgeRecovery_le {u v : Fin n} (huv : u ≠ v) :
    quantumComplexity (capacityRead (n := n) (W := W))
      (fun G (w : ℝ) => w = (G.w u v : ℕ)) 0 ≤ 3 := by
  obtain ⟨Work, hWork, hWorkEq, T, hT⟩ := capacityEdgeRecovery_quantum (W := W) huv
  exact quantumComplexity_le hT

/-- The reconstruction program also accepts a finite cut alphabet without extra queries. -/
def capacityReconstruct :
    DTree (Finset (Fin n)) (CutAnswer n W) (WeightedGraph (Fin n)) (n + n.choose 2) :=
  ((reconstruct (V := Fin n)).mapAnswers (fun a : CutAnswer n W => (a.val : ℝ))).cast
    (by simp only [Fintype.card_fin])

theorem capacityReconstruct_run (G : CapacityGraph (Fin n) W) :
    DTree.run (capacityRead G) capacityReconstruct = (G.toWeighted, n + n.choose 2) := by
  have hread : (fun a : CutAnswer n W => (a.val : ℝ)) ∘ capacityRead G = G.toWeighted.cut := by
    funext S
    simp [Function.comp_def]
  simp only [capacityReconstruct, DTree.run_cast, DTree.run_mapAnswers, hread,
    reconstruct_run, Fintype.card_fin]

/-- Exact quantum reconstruction with the same public `n + binom(n,2)` schedule. -/
theorem capacityReconstruct_quantum :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : CutQAlg n W (WeightedGraph (Fin n)) Work),
      ComputesWithErrorOn T (n + n.choose 2) capacityRead CapacityGraph.toWeighted 0 := by
  obtain ⟨Work, hWork, hWorkEq, T, hT⟩ :=
    DTree.exists_quantum (capacityReconstruct (n := n) (W := W)) capacityRead
  refine ⟨Work, hWork, hWorkEq, T, ?_⟩
  have heval : (fun G => (capacityReconstruct (n := n) (W := W)).eval (capacityRead G)) =
      CapacityGraph.toWeighted := by
    funext G
    simp [DTree.eval, capacityReconstruct_run]
  rwa [heval] at hT

end
end CutQueryComplexity
