import CutQueryComplexity.GHReduction.Randomized.GuideCalls
import CutQueryComplexity.GHReduction.Randomized.Thresholds
import CutQueryComplexity.GHReduction.GuideTwoBudget

/-! # Phase 3c, randomized part: the guide solvers as call trees

Twins, in the namespace `Twin` and under their old names, of the randomized
guide pieces: pruning (`GuidePruneSampling`, `GuidePruneAmplification`), the
guide maximum and source switch (`GuideMaximum`, `GuideSwitchTree`), the base
and node trees and the two-respecting recursion `guideTwoTree`
(`GuideTwoProgram`), and the helper trees of its cost ledger
(`GuideTwoExecution`, `GuideTwoLedger`).

Each has its bridge `foo_eq` (ideal law equals the old law under any exact
family with size-regular cost, on promised graphs) and its realized charged cost,
mirroring `GuideBranchCosts`, `GuideTwoLedger` and `GuideTwoBudget`. The guide
recursion's cost uses the centroid facts transferred by `centroidShoreCall_facts`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal BigOperators
open WeightedGraph Probability

namespace Twin

open CallTree

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

/-- Twin of `guidePruneTree`. -/
def guidePruneTree (Q : ℕ → ℕ) (n : ℕ) (T : GuideTree V N) :
    CallTree V Q (V → Option (CutCandidate V)) (guideOneGlobalBudget Q n) :=
  random (Spanner.coinPMF (frontierProxies T.tree T.centroid)) (fun seed =>
    (CallProg.compile Q (CallProg.guideOneCall (Nat.clog 2 (n + 1)) (T.pruned seed))
      (guideOneGlobalBudget Q n)).map (fun output => output.getD (fun _ => none)))

/-- Twin of `guidePruneTrialsTree`. -/
def guidePruneTrialsTree (Q : ℕ → ℕ) (n trials : ℕ) (T : GuideTree V N) :
    CallTree V Q (V → Option ℝ) (trials * guideOneGlobalBudget Q n) :=
  (CallTree.randomRepeat (guidePruneTree Q n T) trials).map
    (fun L t => bestEstimates (L.map (fun output => candidateEstimate (output t))))

/-- Twin of `guideMaximumTree`. -/
def guideMaximumTree (M : ℕ) (Q : ℕ → ℕ) (n : ℕ) (T : GuideTree V N) (C : Finset N)
    (levels scale exponent : ℕ) :
    CallTree V Q (Option N) (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent) :=
  (sourceMaxTree M Q n (T.graphGroup (outsideGuideNodes T C)) T.source
    levels scale exponent).map (fun out => out.bind (T.nodeOfLabel (outsideGuideNodes T C)))

/-- Twin of `guideSwitchContinuation`; the leaf is the twin of `sourceSwitchGlobalTree`. -/
def guideSwitchContinuation (Q : ℕ → ℕ) (n : ℕ) (T : GuideTree V N) (C : Finset N)
    (choice : Option N) : CallTree V Q (V → Option ℝ) (sourceSwitchBudget Q n) :=
  match choice with
  | none => up (Nat.zero_le _) (CallTree.pure (PMF.pure (fun _ => none)))
  | some a => if ha : a ∈ outsideGuideNodes T C then
      (CallProg.compile Q (CallProg.sourceSwitchCall T C a ha) (sourceSwitchBudget Q n)).map
        (fun out => out.getD (fun _ => none))
    else up (Nat.zero_le _) (CallTree.pure (PMF.pure (fun _ => none)))

/-- Twin of `guideSwitchTree`. -/
def guideSwitchTree (M : ℕ) (Q : ℕ → ℕ) (n : ℕ) (T : GuideTree V N) (C : Finset N)
    (levels scale exponent : ℕ) :
    CallTree V Q (V → Option ℝ)
      (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent + sourceSwitchBudget Q n) :=
  (guideMaximumTree M Q n T C levels scale exponent).bind (guideSwitchContinuation Q n T C)

/-- Twin of `guideBaseValueTree`. -/
def guideBaseValueTree (Q : ℕ → ℕ) (n : ℕ) (T : GuideTree V N) :
    CallTree V Q (V → Option ℝ) (guideBaseGlobalBudget Q n) :=
  (CallProg.compile Q (CallProg.guideBaseCall T) (guideBaseGlobalBudget Q n)).map
    (fun output t => candidateEstimate (output.getD (fun _ => none) t))

/-- Twin of `guideNodeTree`. -/
def guideNodeTree (Q : ℕ → ℕ) (n : ℕ) (T : GuideTree V N) :
    CallTree V Q (GuideNodeOutput T) (guideNodeBudget Q n) :=
  (CallProg.compile Q (CallProg.guideNodeCall T) (guideNodeBudget Q n)).map
    (fun output => output.getD (none, fun _ => ∅))

/-- Twin of `guideSourceBranchTree`. -/
def guideSourceBranchTree (M : ℕ) (Q : ℕ → ℕ) (n : ℕ) (T : GuideTree V N)
    (levels scale exponent : ℕ) :
    CallTree V Q (V → Option ℝ) (guideSwitchBudget M Q n levels scale exponent) :=
  if hs : T.sourceNode ≠ T.centroid then
    guideSwitchTree M Q n T (frontierBranch T.tree T.centroid (T.sourceBranch hs))
      levels scale exponent
  else up (Nat.zero_le _) (CallTree.pure (PMF.pure (fun _ => none)))

/-- Twin of `guideTwoTree`: the two-respecting guide recursion. -/
def guideTwoTree (M : ℕ) (Q : ℕ → ℕ) (n trials levels scale exponent : ℕ) (fuel : ℕ)
    {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) :
    CallTree V Q (V → Option ℝ) (guideTwoBudget M Q n trials levels scale exponent fuel) :=
  match fuel with
  | 0 => if T.real.card ≤ 10 then guideBaseValueTree Q n T
      else up (Nat.zero_le _) (CallTree.pure (PMF.pure (fun _ => none)))
  | fuel + 1 => if T.real.card ≤ 10 then
      up (by unfold guideTwoBudget; omega) (guideBaseValueTree Q n T)
    else
      up (by simp only [guideTwoBudget]; omega)
        ((guideNodeTree Q n T).bind (fun node =>
          (up (Nat.mul_le_mul_right _ ((guideParts_card_le T).trans hvn))
            (CallTree.randomTable (fun _ => none) (fun P : T.parts =>
              let S := node.2 P
              if htrace : S ∩ T.realVertices = T.graphGroup P.val then
                (CallTree.contract (shoreMap S)
                  (guideTwoTree M Q n trials levels scale exponent fuel
                    (childGuide T P S htrace) ((childGuide_graph_size_le T P S htrace).trans hvn))).map
                      (fun output t => pullEstimate (shoreMap S) T.source t output)
              else up (Nat.zero_le _) (CallTree.pure (PMF.pure (fun _ => none)))))).bind
            (fun children =>
              (guidePruneTrialsTree Q n trials T).bind (fun pruned =>
                (guideSourceBranchTree M Q n T levels scale exponent).map
                  (guideTwoCombine T node.1 children pruned)))))
termination_by fuel

/-- Twin of `guideTwoChildTree`. -/
def guideTwoChildTree (M : ℕ) (Q : ℕ → ℕ) (n trials levels scale exponent fuel : ℕ)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (shores : T.parts → Finset V) (P : T.parts) :
    CallTree V Q (V → Option ℝ) (guideTwoBudget M Q n trials levels scale exponent fuel) :=
  let S := shores P
  if htrace : S ∩ T.realVertices = T.graphGroup P.val then
    (CallTree.contract (shoreMap S)
      (guideTwoTree M Q n trials levels scale exponent fuel
        (childGuide T P S htrace) ((childGuide_graph_size_le T P S htrace).trans hvn))).map
          (fun output t => pullEstimate (shoreMap S) T.source t output)
  else up (Nat.zero_le _) (CallTree.pure (PMF.pure (fun _ => none)))

/-- Twin of `guideTwoTailTree`. -/
def guideTwoTailTree (M : ℕ) (Q : ℕ → ℕ) (n trials levels scale exponent fuel : ℕ)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n)
    (initial : Option (CutCandidate V)) (shores : T.parts → Finset V) :
    CallTree V Q (V → Option ℝ)
      (Fintype.card T.parts * guideTwoBudget M Q n trials levels scale exponent fuel +
        (trials * guideOneGlobalBudget Q n + guideSwitchBudget M Q n levels scale exponent)) :=
  (CallTree.randomTable (fun _ => none)
    (guideTwoChildTree M Q n trials levels scale exponent fuel T hvn shores)).bind (fun children =>
      (guidePruneTrialsTree Q n trials T).bind (fun pruned =>
        (guideSourceBranchTree M Q n T levels scale exponent).map
          (guideTwoCombine T initial children pruned)))

/-! ### Bridges -/

section Bridges

variable {M n : ℕ} {Q QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)

/-- A compiled leaf whose ideal run fits its budget is a point mass. -/
theorem interpIdeal_compile_map {P : Type} (G : WeightedGraph V) {O : Type}
    (p : CallProg V O) (q : ℕ) (g : Option O → P) (h : CallProg.idealCost G Q p ≤ q) :
    interpIdeal G ((CallProg.compile Q p q).map g) = PMF.pure (g (some (CallProg.idealEval G p))) := by
  rw [interpIdeal_map, CallProg.interpIdeal_compile G Q p q h, PMF.pure_map]

theorem guidePruneTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) :
    interpIdeal G (guidePruneTree Q n T) = (GHReduction.guidePruneTree E n T).eval G.cut := by
  rw [guidePruneTree_eval E G hG T hvn hQE, guidePruneTree, interpIdeal_random,
    ← PMF.bind_pure_comp]
  congr 1
  funext seed
  rw [interpIdeal_compile_map G _ _ _ (CallProg.guideOneCall_global_cost G hG _ hvn hQ),
    Option.getD_some, Function.comp_apply, CallProg.guideOne_idealEval E _ G hG]

theorem guidePruneTrialsTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G) (trials : ℕ)
    (T : GuideTree V N) :
    interpIdeal G (guidePruneTrialsTree Q n trials T) =
      (GHReduction.guidePruneTrialsTree E n trials T).eval G.cut :=
  map_eq _ (randomRepeat_eq (guidePruneTree_eq E hvn hQ hQE G hG T) trials)

theorem guideMaximumTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (C : Finset N) (levels scale exponent : ℕ) :
    interpIdeal G (guideMaximumTree M Q n T C levels scale exponent) =
      (GHReduction.guideMaximumTree E n T C levels scale exponent).eval G.cut :=
  map_eq _ (sourceMaxTree_eq E hvn hQ hQE G hG _ _ levels scale exponent)

theorem sourceSwitchCall_global_cost (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    CallProg.idealCost G Q (CallProg.sourceSwitchCall T C a ha) ≤ sourceSwitchBudget Q n := by
  have : Nonempty V := ⟨T.source⟩
  exact cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
    (CallProg.sourceSwitchCall_idealCost_scaled G hG T C a ha hvn hQ)

theorem guideSwitchContinuation_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (C : Finset N) (choice : Option N) :
    interpIdeal G (guideSwitchContinuation Q n T C choice) =
      (GHReduction.guideSwitchContinuation E n T C choice).eval G.cut := by
  cases choice with
  | none => simp [guideSwitchContinuation, GHReduction.guideSwitchContinuation]
  | some a =>
      by_cases ha : a ∈ outsideGuideNodes T C
      · simp only [guideSwitchContinuation, GHReduction.guideSwitchContinuation, ha, dite_true,
          RTree.eval_ofDeterministic, sourceSwitchGlobalTree_eval E G hG T C a ha hvn hQE]
        rw [interpIdeal_compile_map G _ _ _ (sourceSwitchCall_global_cost G hG T C a ha hvn hQ),
          Option.getD_some]
        exact congrArg PMF.pure (CallProg.sourceSwitch_idealEval E G hG T C a ha).symm
      · simp [guideSwitchContinuation, GHReduction.guideSwitchContinuation, ha]

theorem guideSwitchTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (C : Finset N) (levels scale exponent : ℕ) :
    interpIdeal G (guideSwitchTree M Q n T C levels scale exponent) =
      (GHReduction.guideSwitchTree E n T C levels scale exponent).eval G.cut :=
  bind_eq (guideMaximumTree_eq E hvn hQ hQE G hG T C levels scale exponent)
    (fun choice _ => guideSwitchContinuation_eq E hvn hQ hQE G hG T C choice)

theorem guideBaseCall_global_cost (G : WeightedGraph V) (T : GuideTree V N)
    (hsmall : T.real.card ≤ 10) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    CallProg.idealCost G Q (CallProg.guideBaseCall T) ≤ guideBaseGlobalBudget Q n := by
  have : Nonempty V := ⟨T.source⟩
  have hscaled := CallProg.guideBaseCall_idealCost_scaled T hsmall hvn hQ G
  exact cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
    (by simpa only [guideBaseGlobalBudget, Nat.mul_assoc, Nat.mul_left_comm] using hscaled)

theorem guideBaseValueTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hsmall : T.real.card ≤ 10) :
    interpIdeal G (guideBaseValueTree Q n T) = (GHReduction.guideBaseValueTree E n T).eval G.cut := by
  rw [guideBaseValueTree_eval E T hsmall hvn hQE G.cut, guideBaseValueTree,
    interpIdeal_compile_map G _ _ _ (guideBaseCall_global_cost G T hsmall hvn hQ),
    Option.getD_some, CallProg.guideBase_idealEval E G hG]

theorem guideNodeCall_global_cost (G : WeightedGraph V) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    CallProg.idealCost G Q (CallProg.guideNodeCall T) ≤ guideNodeBudget Q n := by
  have : Nonempty V := ⟨T.source⟩
  exact cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
    (CallProg.guideNodeCall_idealCost_scaled T hvn hQ G)

theorem guideNodeTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) :
    interpIdeal G (guideNodeTree Q n T) = (GHReduction.guideNodeTree E n T).eval G.cut := by
  rw [guideNodeTree_eval E T hvn hQE G.cut, guideNodeTree,
    interpIdeal_compile_map G _ _ _ (guideNodeCall_global_cost G T hvn hQ),
    Option.getD_some, CallProg.guideNode_idealEval E G hG]

theorem guideSourceBranchTree_eq (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hQE : SizeRegular n QE) (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (levels scale exponent : ℕ) :
    interpIdeal G (guideSourceBranchTree M Q n T levels scale exponent) =
      (GHReduction.guideSourceBranchTree E n T levels scale exponent).eval G.cut := by
  by_cases hs : T.sourceNode ≠ T.centroid
  · unfold guideSourceBranchTree GHReduction.guideSourceBranchTree guideSwitchBudget
    rw [dite_eq_left hs, dite_eq_left hs]
    exact guideSwitchTree_eq E hvn hQ hQE G hG T _ levels scale exponent
  · unfold guideSourceBranchTree GHReduction.guideSourceBranchTree guideSwitchBudget
    rw [dite_eq_right hs, dite_eq_right hs, RTree.eval_pure]
    exact interpIdeal_pure G _

theorem guideTwoTree_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (trials levels scale exponent fuel : ℕ) :
    ∀ {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
      (G : WeightedGraph V), InputPromise M G → ∀ (T : GuideTree V N)
      (hvn : Fintype.card V ≤ n),
      interpIdeal G (guideTwoTree M Q n trials levels scale exponent fuel T hvn) =
        (GHReduction.guideTwoTree E n trials levels scale exponent fuel T hvn).eval G.cut := by
  induction fuel with
  | zero =>
      intro V N _ _ _ _ G hG T hvn
      by_cases hsmall : T.real.card ≤ 10
      · simp only [guideTwoTree, GHReduction.guideTwoTree, hsmall]
        exact guideBaseValueTree_eq E hvn hQ hQE G hG T hsmall
      · simp [guideTwoTree, GHReduction.guideTwoTree, hsmall]
  | succ fuel ih =>
      intro V N _ _ _ _ G hG T hvn
      by_cases hsmall : T.real.card ≤ 10
      · simp only [guideTwoTree, GHReduction.guideTwoTree, hsmall, ite_true, interpIdeal_up,
          RTree.eval_weaken]
        exact guideBaseValueTree_eq E hvn hQ hQE G hG T hsmall
      · simp only [guideTwoTree, GHReduction.guideTwoTree, hsmall, ite_false, interpIdeal_up,
          RTree.eval_weaken]
        refine bind_eq (guideNodeTree_eq E hvn hQ hQE G hG T) (fun node _ => ?_)
        refine bind_eq ?_ (fun children _ =>
          bind_eq (guidePruneTrialsTree_eq E hvn hQ hQE G hG trials T) (fun pruned _ =>
            map_eq _ (guideSourceBranchTree_eq E hvn hQ hQE G hG T levels scale exponent)))
        rw [interpIdeal_up, RTree.eval_weaken]
        refine randomTable_eq _ (fun P => ?_)
        split
        · exact map_eq _ (contract_eq _ (ih _ (inputPromise_contract G hG _) _ _))
        · simp

theorem guideTwoChildTree_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (trials levels scale exponent fuel : ℕ) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (shores : T.parts → Finset V) (P : T.parts) :
    interpIdeal G (guideTwoChildTree M Q n trials levels scale exponent fuel T hvn shores P) =
      (GHReduction.guideTwoChildTree E n trials levels scale exponent fuel T hvn shores P).eval
        G.cut := by
  unfold guideTwoChildTree GHReduction.guideTwoChildTree
  dsimp only
  split
  · exact map_eq _ (contract_eq _ (guideTwoTree_eq E hQ hQE trials levels scale exponent fuel
      _ (inputPromise_contract G hG _) _ _))
  · simp

theorem guideTwoTailTree_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (trials levels scale exponent fuel : ℕ) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (initial : Option (CutCandidate V))
    (shores : T.parts → Finset V) :
    interpIdeal G (guideTwoTailTree M Q n trials levels scale exponent fuel T hvn initial shores) =
      (GHReduction.guideTwoTailTree E n trials levels scale exponent fuel T hvn initial
        shores).eval G.cut := by
  unfold guideTwoTailTree GHReduction.guideTwoTailTree
  exact bind_eq (randomTable_eq _ (fun P =>
    guideTwoChildTree_eq E hQ hQE trials levels scale exponent fuel G hG T hvn shores P))
    (fun _ _ => bind_eq (guidePruneTrialsTree_eq E hvn hQ hQE G hG trials T)
      (fun _ _ => map_eq _ (guideSourceBranchTree_eq E hvn hQ hQE G hG T levels scale exponent)))

end Bridges

end Twin
end
end CutQueryComplexity.GHReduction.Randomized
