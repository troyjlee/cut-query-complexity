import CutQueryComplexity.GHReduction.Randomized.GuideTrees

/-! # Realized charged costs of the guide twins

The ideal-run analogues of `GuideBranchCosts`, `GuideTwoLedger` and
`GuideTwoBudget`: on a promised graph, every supported ideal run of a guide twin
has charged cost (one per cut query, `Q k` per call) within the old sharp bound at
charge `Q`. The proofs follow the old ones step for step, with `idealRun` in place
of `RTree.run`; the centroid facts come from `centroidShoreCall_facts`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal BigOperators
open WeightedGraph Probability

namespace Twin

open CallTree

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
variable {M n : ℕ} {Q : ℕ → ℕ}

theorem guidePruneTree_cost_scaled (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    {p : (V → Option (CutCandidate V)) × ℕ}
    (hp : p ∈ (idealRun G (guidePruneTree Q n T)).support) :
    n * p.2 ≤ Fintype.card V * guideOneGlobalBudget Q n := by
  simp only [guidePruneTree, idealRun_random, idealRun_map] at hp
  obtain ⟨seed, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  rw [idealRun_compile G _ _ (CallProg.guideOneCall_global_cost G hG (T.pruned seed) hvn hQ),
    PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hrun
  rw [hrun]
  exact CallProg.guideOneCall_cost_linear G hG (T.pruned seed) hvn hQ _

theorem guidePruneTrialsTree_cost_scaled (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (trials : ℕ)
    {p : (V → Option ℝ) × ℕ} (hp : p ∈ (idealRun G (guidePruneTrialsTree Q n trials T)).support) :
    n * p.2 ≤ Fintype.card V * (trials * guideOneGlobalBudget Q n) := by
  apply idealRun_map_cost G _ _ n _ ?_ hp
  intro out hout
  have h := CallTree.randomRepeat_cost G (guidePruneTree Q n T) trials n
    (Fintype.card V * guideOneGlobalBudget Q n)
    (fun p hp => guidePruneTree_cost_scaled G hG T hvn hQ hp) hout
  simpa only [Nat.mul_assoc, Nat.mul_left_comm] using h

theorem guideMaximumTree_cost_scaled (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (T : GuideTree V N) (C : Finset N) (levels scale exponent : ℕ)
    {p : Option N × ℕ}
    (hp : p ∈ (idealRun G (guideMaximumTree M Q n T C levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V *
      (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent) :=
  idealRun_map_cost G _ _ n _
    (fun _ hr => sourceMaxTree_cost_scaled hvn hQ G _ _ levels scale exponent hr) hp

theorem guideSwitchContinuation_cost_scaled (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (choice : Option N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G (guideSwitchContinuation Q n T C choice)).support) :
    n * p.2 ≤ Fintype.card V * sourceSwitchBudget Q n := by
  cases choice with
  | none =>
      simp only [guideSwitchContinuation, idealRun_up] at hp
      simp [idealRun_pure_cost G _ hp]
  | some a =>
      by_cases ha : a ∈ outsideGuideNodes T C
      · simp only [guideSwitchContinuation, ha, dite_true, idealRun_map] at hp
        rw [idealRun_compile G _ _ (sourceSwitchCall_global_cost G hG T C a ha hvn hQ),
          PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hp
        rw [hp]
        exact CallProg.sourceSwitchCall_idealCost_scaled G hG T C a ha hvn hQ
      · simp only [guideSwitchContinuation, ha, dite_false, idealRun_up] at hp
        simp [idealRun_pure_cost G _ hp]

theorem guideSwitchTree_cost_scaled (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (levels scale exponent : ℕ)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G (guideSwitchTree M Q n T C levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V * guideSwitchBudget M Q n levels scale exponent := by
  unfold guideSwitchBudget
  rw [Nat.mul_add]
  exact idealRun_bind_cost G _ _ n _ _
    (fun p hp => guideMaximumTree_cost_scaled hvn hQ G T C levels scale exponent hp)
    (fun first _ p hp => guideSwitchContinuation_cost_scaled G hG T C first.1 hvn hQ hp) hp

theorem guideSourceBranchTree_cost_scaled (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (levels scale exponent : ℕ)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G (guideSourceBranchTree M Q n T levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V * guideSwitchBudget M Q n levels scale exponent := by
  by_cases hs : T.sourceNode ≠ T.centroid
  · unfold guideSourceBranchTree guideSwitchBudget at hp
    rw [dite_eq_left hs] at hp
    exact guideSwitchTree_cost_scaled G hG T _ levels scale exponent hvn hQ hp
  · unfold guideSourceBranchTree guideSwitchBudget at hp
    rw [dite_eq_right hs] at hp
    have h0 := idealRun_pure_cost G _ (show p ∈ (idealRun G (CallTree.pure (V := V) (Q := Q)
      (PMF.pure (fun _ => none)))).support from hp)
    simp [h0]

theorem guideNodeTree_idealRun (G : WeightedGraph V) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    idealRun G (guideNodeTree Q n T) =
      PMF.pure (CallProg.idealEval G (CallProg.guideNodeCall T),
        CallProg.idealCost G Q (CallProg.guideNodeCall T)) := by
  rw [guideNodeTree, idealRun_map, idealRun_compile G _ _ (guideNodeCall_global_cost G T hvn hQ),
    PMF.pure_map, Option.getD_some]

theorem guideBaseValueTree_cost_scaled (G : WeightedGraph V) (T : GuideTree V N)
    (hsmall : T.real.card ≤ 10) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    {p : (V → Option ℝ) × ℕ} (hp : p ∈ (idealRun G (guideBaseValueTree Q n T)).support) :
    n * p.2 ≤ 10 * Fintype.card V * (Q n + n) := by
  rw [guideBaseValueTree, idealRun_map,
    idealRun_compile G _ _ (guideBaseCall_global_cost G T hsmall hvn hQ),
    PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hp
  rw [hp]
  exact CallProg.guideBaseCall_idealCost_scaled T hsmall hvn hQ G

theorem guideTwoTree_step_run (trials levels scale exponent fuel : ℕ) (G : WeightedGraph V)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hlarge : ¬T.real.card ≤ 10) :
    idealRun G (guideTwoTree M Q n trials levels scale exponent (fuel + 1) T hvn) =
      (idealRun G (guideTwoTailTree M Q n trials levels scale exponent fuel T hvn
        (CallProg.idealEval G (CallProg.centroidPairCall T))
        (CallProg.idealEval G (CallProg.centroidShoreCall T)))).map
          (fun p => (p.1, CallProg.idealCost G Q (CallProg.guideNodeCall T) + p.2)) := by
  have hnode : CallProg.idealEval G (CallProg.guideNodeCall T) =
      (CallProg.idealEval G (CallProg.centroidPairCall T),
        CallProg.idealEval G (CallProg.centroidShoreCall T)) := by
    simp [CallProg.guideNodeCall]
  rw [guideTwoTree, ite_eq_right hlarge, idealRun_up, idealRun_bind,
    guideNodeTree_idealRun G T hvn hQ, hnode, PMF.pure_bind]
  simp only [guideTwoTailTree, idealRun_bind, idealRun_up]
  unfold guideTwoChildTree
  rfl

theorem guideTwoTailTree_cost_scaled (trials levels scale exponent fuel : ℕ)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (initial : Option (CutCandidate V)) (shores : T.parts → Finset V) (budget : T.parts → ℕ)
    (hchildren : ∀ P, ∀ p ∈ (idealRun G
      (guideTwoChildTree M Q n trials levels scale exponent fuel T hvn shores P)).support,
      n * p.2 ≤ budget P) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G
      (guideTwoTailTree M Q n trials levels scale exponent fuel T hvn initial shores)).support) :
    n * p.2 ≤ (∑ P, budget P) + Fintype.card V *
      (trials * guideOneGlobalBudget Q n + guideSwitchBudget M Q n levels scale exponent) := by
  apply idealRun_bind_cost G _ _ n _ _ ?_ ?_ hp
  · intro out hout
    exact CallTree.randomTable_cost G _ _ n budget hchildren hout
  · intro children _ out hout
    rw [Nat.mul_add]
    apply idealRun_bind_cost G _ _ n _ _ ?_ ?_ hout
    · intro p hp
      exact guidePruneTrialsTree_cost_scaled G hG T hvn hQ trials hp
    · intro pruned _ p hp
      exact idealRun_map_cost G _ _ n _
        (fun p hp => guideSourceBranchTree_cost_scaled G hG T levels scale exponent hvn hQ hp) hp

theorem guideTwoTree_step_cost_scaled (trials levels scale exponent fuel : ℕ)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (hlarge : ¬T.real.card ≤ 10)
    (budget : T.parts → ℕ)
    (hchildren : ∀ P, ∀ p ∈ (idealRun G
      (guideTwoChildTree M Q n trials levels scale exponent fuel T hvn
        (CallProg.idealEval G (CallProg.centroidShoreCall T)) P)).support, n * p.2 ≤ budget P)
    {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G
      (guideTwoTree M Q n trials levels scale exponent (fuel + 1) T hvn)).support) :
    n * p.2 ≤ (∑ P, budget P) + Fintype.card V *
      guideTwoNodeCost M Q n trials levels scale exponent := by
  rw [guideTwoTree_step_run trials levels scale exponent fuel G T hvn hQ hlarge] at hp
  obtain ⟨tail, htail, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  have htailCost := guideTwoTailTree_cost_scaled trials levels scale exponent fuel G hG
    T hvn hQ _ _ budget hchildren htail
  have hnode := CallProg.guideNodeCall_idealCost_scaled T hvn hQ G
  rw [← heq, Nat.mul_add]
  unfold guideTwoNodeCost
  nlinarith

theorem guideTwoTree_cost_scaled (hQ : SizeRegular n Q) (trials levels scale exponent fuel : ℕ) :
    ∀ {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
      (G : WeightedGraph V), InputPromise M G → ∀ (T : GuideTree V N)
      (hvn : Fintype.card V ≤ n), ∀ p ∈ (idealRun G
        (guideTwoTree M Q n trials levels scale exponent fuel T hvn)).support,
      n * p.2 ≤ 10 * Fintype.card V * (Q n + n) +
        fuel * (guideTwoNodeCost M Q n trials levels scale exponent + 20 * (Q n + n)) *
          guideWork (Fintype.card V) T.real.card := by
  induction fuel with
  | zero =>
    intro V N _ _ _ _ G hG T hvn p hp
    by_cases hsmall : T.real.card ≤ 10
    · simp only [guideTwoTree, hsmall] at hp
      simpa only [zero_mul, Nat.zero_mul, add_zero, Nat.add_zero] using
        guideBaseValueTree_cost_scaled G T hsmall hvn hQ hp
    · simp only [guideTwoTree, hsmall] at hp
      simp [idealRun_pure_cost G _ hp]
  | succ fuel ih =>
    intro V N _ _ _ _ G hG T hvn p hp
    by_cases hsmall : T.real.card ≤ 10
    · simp only [guideTwoTree, hsmall, ite_true, idealRun_up] at hp
      exact (guideBaseValueTree_cost_scaled G T hsmall hvn hQ hp).trans (Nat.le_add_right _ _)
    · have hlarge : 2 < T.real.card := by omega
      obtain ⟨hcorrect, htotal, hguide⟩ := CallProg.centroidShoreCall_facts G hG T hlarge
      let S := CallProg.idealEval G (CallProg.centroidShoreCall T)
      have htrace (P : T.parts) : S P ∩ T.realVertices = T.graphGroup P.val := (hcorrect P).1.1
      let size : T.parts → ℕ := fun P => (S P).card + 1
      let work : T.parts → ℕ := fun P => guideWork (size P) (P.val.card + 1)
      let H := guideTwoNodeCost M Q n trials levels scale exponent
      let K := Q n + n
      let budget : T.parts → ℕ := fun P => 10 * size P * K + fuel * (H + 20 * K) * work P
      have hchildren (P : T.parts) : ∀ out ∈ (idealRun G
          (guideTwoChildTree M Q n trials levels scale exponent fuel T hvn S P)).support,
          n * out.2 ≤ budget P := by
        intro out hout
        simp only [guideTwoChildTree, htrace P, dite_true, idealRun_map, idealRun_contract] at hout
        obtain ⟨childOut, hchildOut, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
        rw [← heq]
        have h := ih (G.contract (shoreMap (S P))) (inputPromise_contract G hG (shoreMap (S P)))
          (childGuide T P (S P) (htrace P))
          ((childGuide_graph_size_le T P (S P) (htrace P)).trans hvn) childOut hchildOut
        simpa only [budget, size, work, H, K, shoreVertex_card, childGuide_real_card] using h
      have hsize : (∑ P, size P) ≤ 2 * Fintype.card V := by
        have hr := T.real_card_le
        exact htotal.trans (by omega)
      have hwork : (∑ P, work P) ≤ guideWork (Fintype.card V) T.real.card := by
        have hcards : ∀ P : T.parts, (T.graphGroup P.val).card = P.val.card :=
          fun P => T.graphGroup_card (T.part_subset P.property)
        simpa only [work, size, hcards] using hguide
      have hsw : Fintype.card V ≤ guideWork (Fintype.card V) T.real.card :=
        size_le_guideWork T.real_card_le (by omega)
      have hstep := guideTwoTree_step_cost_scaled trials levels scale exponent fuel G hG T
        hvn hQ hsmall budget hchildren hp
      exact hstep.trans (guide_two_cost_recurrence size work hsize hwork hsw)

theorem guideTwoTree_cost_linear (hQ : SizeRegular n Q) (trials levels scale exponent fuel : ℕ)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) (hvn : Fintype.card V ≤ n)
    {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (idealRun G (guideTwoTree M Q n trials levels scale exponent fuel T hvn)).support) :
    n * p.2 ≤ Fintype.card V * guideTwoSharpBudget M Q n trials levels scale exponent fuel := by
  have h := guideTwoTree_cost_scaled hQ trials levels scale exponent fuel G hG T hvn p hp
  have hw := guideWork_le_twice_size T.real_card_le
  calc
    _ ≤ 10 * Fintype.card V * (Q n + n) +
        fuel * (guideTwoNodeCost M Q n trials levels scale exponent + 20 * (Q n + n)) *
          guideWork (Fintype.card V) T.real.card := h
    _ ≤ 10 * Fintype.card V * (Q n + n) +
        fuel * (guideTwoNodeCost M Q n trials levels scale exponent + 20 * (Q n + n)) *
          (2 * Fintype.card V) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hw) _
    _ = _ := by unfold guideTwoSharpBudget; ring

end Twin
end
end CutQueryComplexity.GHReduction.Randomized
