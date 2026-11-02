import CutQueryComplexity.GHReduction.Contractions

/-! # Contraction simulation preserves realized query counts

Every substituted virtual query makes exactly one original query. This upgrades
the cap-preservation interface to equality of the joint output/cost law, which
is needed when many differently sized contracted instances are added together.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {I A J B O : Type} {q : ℕ}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem run_substitute_unit (call : J → DTree I A B 1) (T : RTree J B O q)
    (read : I → A) (hcall : ∀ j, (call j).cost read = 1) :
    RTree.run read (T.substitute call) =
      RTree.run (fun j => (call j).eval read) T := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [RTree.substitute, RTree.run_mix, PMF.bind_map]
    conv_rhs => rw [RTree.run]
    simp only [Function.comp_def]
    congr 1
    funext action
    rcases action with output | ⟨j, next⟩
    · simp only [RTree.run_pure, PMF.pure_map]
    · simp only [RTree.run_cast, RTree.run_bind, RTree.run_ofDeterministic, PMF.pure_bind]
      have hrun : DTree.run read (call j) = ((call j).eval read, 1) := by
        exact Prod.ext rfl (hcall j)
      rw [hrun, ih]
      congr 1
      funext p
      exact Prod.ext rfl (Nat.add_comm 1 p.2)

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem contractProgram_run (π : V → W) (T : RTree (Finset W) ℝ O q)
    (read : Finset V → ℝ) :
    RTree.run read (contractProgram π T) = RTree.run (read ∘ WeightedGraph.pull π) T := by
  rw [contractProgram, RTree.run_cast, run_substitute_unit _ _ _ (fun S => contractQuery_cost π S read)]
  rfl

theorem contractProgram_graph_run (G : WeightedGraph V) (π : V → W)
    (T : RTree (Finset W) ℝ O q) :
    RTree.run G.cut (contractProgram π T) = RTree.run (G.contract π).cut T := by
  rw [contractProgram_run]
  congr 1
  funext S
  exact (WeightedGraph.cut_contract G π S).symm

end
end CutQueryComplexity.GHReduction
