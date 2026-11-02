import CutQueryComplexity.GHReduction.GuidePruneAmplification
import CutQueryComplexity.GHReduction.GuideSwitchTree
import CutQueryComplexity.GHReduction.GuideTwoCases

/-! # The finite two-respecting randomized query program

This definition combines the supplied terminal primitive, actual canonical
centroid isolating queries, guarded same-parameter child calls, fresh pruning
trials, and the threshold-based source switch. Only public data and previous
answers select its branches. The deliberately generous recursive hard cap is
separate from the sharp realized-cost ledger needed for final truncation.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def guideBaseGlobalBudget (Q : ℕ → ℕ) (n : ℕ) : ℕ := 10 * (Q n + n)

def guideBaseValueTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (T : GuideTree V N) :
    RTree (Finset V) ℝ (V → Option ℝ) (guideBaseGlobalBudget Q n) :=
  RTree.ofDeterministic
    ((Prog.toDTree (guideBaseProgram family T) (guideBaseGlobalBudget Q n)).map
      (fun output t => candidateEstimate (output.getD (fun _ => none) t)))

theorem guideBaseValueTree_eval {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N) (hsmall : T.real.card ≤ 10)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    (guideBaseValueTree family n T).eval read =
      PMF.pure (fun t => candidateEstimate (Prog.eval read (guideBaseProgram family T) t)) := by
  haveI : Nonempty V := ⟨T.source⟩
  have hcost := guideBaseProgram_cost_scaled family T hsmall hvn hQ read
  have hcost' : Prog.cost read (guideBaseProgram family T) ≤ guideBaseGlobalBudget Q n :=
    cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
      (by simpa only [guideBaseGlobalBudget, Nat.mul_assoc, Nat.mul_left_comm] using hcost)
  simp only [guideBaseValueTree, RTree.eval_ofDeterministic, DTree.eval_map,
    Prog.toDTree_eval _ _ _ hcost', Option.getD_some]

abbrev GuideNodeOutput (T : GuideTree V N) := Option (CutCandidate V) × (T.parts → Finset V)

def guideNodeProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) : Prog (Finset V) ℝ (GuideNodeOutput T) :=
  (centroidPairProgram family T).bind (fun initial =>
    (centroidShoreProgram family T).map (fun shores => (initial, shores)))

def guideNodeBudget (Q : ℕ → ℕ) (n : ℕ) : ℕ := (Nat.clog 2 n + 3) * (Q n + n)

theorem guideNodeProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    n * Prog.cost read (guideNodeProgram family T) ≤ Fintype.card V * guideNodeBudget Q n := by
  have hpair := centroidPairProgram_cost_scaled family T hvn hQ read
  have hshores := centroidShoreProgram_cost_scaled family T hvn hQ read
  simp only [guideNodeProgram, Prog.cost_bind, Prog.cost_map, Nat.mul_add]
  unfold guideNodeBudget
  calc
    _ ≤ Fintype.card V * (Q n + n) + (Nat.clog 2 n + 2) * Fintype.card V * Q n :=
      add_le_add hpair hshores
    _ ≤ Fintype.card V * (Q n + n) + (Nat.clog 2 n + 2) * Fintype.card V * (Q n + n) :=
      add_le_add le_rfl (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

def guideNodeTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (T : GuideTree V N) :
    RTree (Finset V) ℝ (GuideNodeOutput T) (guideNodeBudget Q n) :=
  RTree.ofDeterministic ((Prog.toDTree (guideNodeProgram family T) (guideNodeBudget Q n)).map
    (fun output => output.getD (none, fun _ => ∅)))

theorem guideNodeTree_eval {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    (guideNodeTree family n T).eval read = PMF.pure (Prog.eval read (guideNodeProgram family T)) := by
  haveI : Nonempty V := ⟨T.source⟩
  have hcost := cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
    (guideNodeProgram_cost_scaled family T hvn hQ read)
  simp only [guideNodeTree, RTree.eval_ofDeterministic, DTree.eval_map,
    Prog.toDTree_eval _ _ _ hcost, Option.getD_some]

def guideSwitchBudget (M : ℕ) (Q : ℕ → ℕ) (n levels scale exponent : ℕ) : ℕ :=
  Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent + sourceSwitchBudget Q n

def guideSourceBranchTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (T : GuideTree V N) (levels scale exponent : ℕ) :
    RTree (Finset V) ℝ (V → Option ℝ) (guideSwitchBudget M Q n levels scale exponent) :=
  if hs : T.sourceNode ≠ T.centroid then
    guideSwitchTree family n T (frontierBranch T.tree T.centroid (T.sourceBranch hs))
      levels scale exponent
  else RTree.pure (PMF.pure (fun _ => none))

def guideTwoCombine (T : GuideTree V N) (initial : Option (CutCandidate V))
    (children : T.parts → V → Option ℝ) (pruned switched : V → Option ℝ) (t : V) : Option ℝ :=
  bestEstimates (candidateEstimate (filterCandidate T.source t initial) ::
    pruned t :: switched t :: (Finset.univ.toList.map (fun P : T.parts => children P t)))

theorem guideTwoCombine_above (G : WeightedGraph V) (T : GuideTree V N)
    (initial : Option (CutCandidate V)) (children : T.parts → V → Option ℝ)
    (pruned switched : V → Option ℝ) (t : V)
    (hi : ∀ C, initial = some C → C.value = G.cut C.shore)
    (hc : ∀ P, EstimateAbove (stValue G t T.source) (children P t))
    (hp : EstimateAbove (stValue G t T.source) (pruned t))
    (hs : EstimateAbove (stValue G t T.source) (switched t)) :
    EstimateAbove (stValue G t T.source) (guideTwoCombine T initial children pruned switched t) := by
  apply bestEstimates_above
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact candidateEstimate_above G (fun C hC => filterCandidate_valid G T.source t hi hC)
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact hp
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hs
      · obtain ⟨P, _, rfl⟩ := List.mem_map.mp ha
        exact hc P

theorem guideParts_card_le (T : GuideTree V N) : Fintype.card T.parts ≤ Fintype.card V := by
  have hp : T.parts ⊆ T.isolationParts := fun _ h => T.part_mem_isolationParts h
  have hiso : T.isolationParts.card ≤ Fintype.card V := by
    simpa only [Fintype.card_coe] using T.isolationParts_card_le.trans T.real_card_le
  simpa only [Fintype.card_coe] using
    (Finset.card_le_card hp).trans hiso

def guideTwoBudget (M : ℕ) (Q : ℕ → ℕ) (n trials levels scale exponent : ℕ) : ℕ → ℕ
  | 0 => guideBaseGlobalBudget Q n
  | fuel + 1 => guideBaseGlobalBudget Q n + guideNodeBudget Q n +
      n * guideTwoBudget M Q n trials levels scale exponent fuel +
      trials * guideOneGlobalBudget Q n + guideSwitchBudget M Q n levels scale exponent

def guideTwoTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials levels scale exponent : ℕ) (fuel : ℕ)
    {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (V → Option ℝ) (guideTwoBudget M Q n trials levels scale exponent fuel) :=
  match fuel with
  | 0 => if T.real.card ≤ 10 then guideBaseValueTree family n T
      else RTree.pure (PMF.pure (fun _ => none))
  | fuel + 1 => if T.real.card ≤ 10 then
      (guideBaseValueTree family n T).weaken (by unfold guideTwoBudget; omega)
    else
      ((guideNodeTree family n T).bind (fun node =>
        ((randomTable (fun _ => none) (fun P : T.parts =>
          let S := node.2 P
          if htrace : S ∩ T.realVertices = T.graphGroup P.val then
            (contractProgram (shoreMap S)
              (guideTwoTree family n trials levels scale exponent fuel
                (childGuide T P S htrace) ((childGuide_graph_size_le T P S htrace).trans hvn))).map
                  (fun output t => pullEstimate (shoreMap S) T.source t output)
          else RTree.pure (PMF.pure (fun _ => none)))).weaken
            (Nat.mul_le_mul_right _ ((guideParts_card_le T).trans hvn))).bind (fun children =>
          (guidePruneTrialsTree family n trials T).bind (fun pruned =>
            (guideSourceBranchTree family n T levels scale exponent).map
              (guideTwoCombine T node.1 children pruned))))).weaken
                (by simp only [guideTwoBudget]; omega)
termination_by fuel

end
end CutQueryComplexity.GHReduction
