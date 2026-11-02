import CutQueryComplexity.GHReduction.GuideTwoComplete
import CutQueryComplexity.GHReduction.RealizedCosts
import CutQueryComplexity.GHReduction.RandomContractionCost

/-! # Actual-size costs of both randomized guide branches

The threshold maximum search, its extra exact pair/value query, and every
pruning repetition are included. These bounds hold for every supported random
outcome on a promised graph, even if a randomized value estimate is incorrect.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

theorem guidePruneTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    {p : (V → Option (CutCandidate V)) × ℕ}
    (hp : p ∈ (RTree.run G.cut (guidePruneTree family n T)).support) :
    n * p.2 ≤ Fintype.card V * guideOneGlobalBudget Q n := by
  simp only [guidePruneTree, RTree.run_mix, PMF.bind_map, Function.comp_def] at hp
  obtain ⟨seed, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  have hcap := guideOneProgram_global_cost family G hG (T.pruned seed) hvn hQ
  simp only [RTree.run_ofDeterministic, DTree.run_map, guideOneGlobalTree,
    Prog.toDTree_run G.cut _ _ hcap, Option.getD_some] at hrun
  have heq := (PMF.mem_support_pure_iff _ _).mp hrun
  rw [heq]
  exact guideOneProgram_cost_linear family G hG (T.pruned seed) hvn hQ _

theorem guidePruneTrialsTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (trials : ℕ)
    {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut (guidePruneTrialsTree family n trials T)).support) :
    n * p.2 ≤ Fintype.card V * (trials * guideOneGlobalBudget Q n) := by
  apply random_map_cost _ _ G.cut n _ ?_ hp
  intro out hout
  have h := randomRepeat_cost (guidePruneTree family n T) trials G.cut n
    (Fintype.card V * guideOneGlobalBudget Q n)
    (fun p hp => guidePruneTree_cost_scaled family G hG T hvn hQ hp) hout
  simpa only [Nat.mul_assoc, Nat.mul_left_comm] using h

theorem sourceSwitchGlobalTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    n * (sourceSwitchGlobalTree family n T C a ha).cost G.cut ≤
      Fintype.card V * sourceSwitchBudget Q n := by
  haveI : Nonempty V := ⟨T.source⟩
  have hscaled := sourceSwitchProgram_cost_scaled family G hG T C a ha hvn hQ
  have hcap := cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn hscaled
  simpa only [sourceSwitchGlobalTree, DTree.cost, DTree.run_map,
    Prog.toDTree_run G.cut _ _ hcap] using hscaled

theorem guideSwitchContinuation_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (choice : Option N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut (guideSwitchContinuation family n T C choice)).support) :
    n * p.2 ≤ Fintype.card V * sourceSwitchBudget Q n := by
  cases choice with
  | none =>
    simp only [guideSwitchContinuation, RTree.run_pure, PMF.pure_map] at hp
    have heq := (PMF.mem_support_pure_iff _ _).mp hp
    rw [heq]
    simp
  | some a =>
    by_cases ha : a ∈ outsideGuideNodes T C
    · simp only [guideSwitchContinuation, ha, dite_true, RTree.run_ofDeterministic] at hp
      have heq := (PMF.mem_support_pure_iff _ _).mp hp
      rw [heq]
      exact sourceSwitchGlobalTree_cost_scaled family G hG T C a ha hvn hQ
    · simp only [guideSwitchContinuation, ha, dite_false, RTree.run_pure, PMF.pure_map] at hp
      have heq := (PMF.mem_support_pure_iff _ _).mp hp
      rw [heq]
      simp

theorem guideSwitchTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (levels scale exponent : ℕ)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut (guideSwitchTree family n T C levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V * guideSwitchBudget M Q n levels scale exponent := by
  unfold guideSwitchBudget
  rw [Nat.mul_add]
  exact random_bind_cost _ _ G.cut n _ _
    (fun p hp => guideMaximumTree_cost_scaled family hvn hQ T C levels scale exponent G.cut hp)
    (fun first _ p hp => guideSwitchContinuation_cost_scaled family G hG T C first.1 hvn hQ hp) hp

theorem guideSourceBranchTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (levels scale exponent : ℕ)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut (guideSourceBranchTree family n T levels scale exponent)).support) :
    n * p.2 ≤ Fintype.card V * guideSwitchBudget M Q n levels scale exponent := by
  by_cases hs : T.sourceNode ≠ T.centroid
  · unfold guideSourceBranchTree guideSwitchBudget at hp
    rw [dite_eq_left hs] at hp
    exact guideSwitchTree_cost_scaled family G hG T _ levels scale exponent hvn hQ hp
  · unfold guideSourceBranchTree guideSwitchBudget at hp
    rw [dite_eq_right hs] at hp
    simp only [RTree.run_pure, PMF.pure_map] at hp
    have heq := (PMF.mem_support_pure_iff _ _).mp hp
    rw [heq]
    simp

theorem guideNodeTree_run {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    RTree.run read (guideNodeTree family n T) =
      PMF.pure (Prog.eval read (guideNodeProgram family T), Prog.cost read (guideNodeProgram family T)) := by
  haveI : Nonempty V := ⟨T.source⟩
  have hcap := cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
    (guideNodeProgram_cost_scaled family T hvn hQ read)
  simp only [guideNodeTree, RTree.run_ofDeterministic, DTree.run_map,
    Prog.toDTree_run read _ _ hcap, Option.getD_some]

theorem guideBaseValueTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N) (hsmall : T.real.card ≤ 10)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ)
    {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run read (guideBaseValueTree family n T)).support) :
    n * p.2 ≤ 10 * Fintype.card V * (Q n + n) := by
  haveI : Nonempty V := ⟨T.source⟩
  have hscaled := guideBaseProgram_cost_scaled family T hsmall hvn hQ read
  have hcap : Prog.cost read (guideBaseProgram family T) ≤ guideBaseGlobalBudget Q n :=
    cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
      (by simpa only [guideBaseGlobalBudget, Nat.mul_assoc, Nat.mul_left_comm] using hscaled)
  simp only [guideBaseValueTree, RTree.run_ofDeterministic, DTree.run_map,
    Prog.toDTree_run read _ _ hcap, Option.getD_some] at hp
  have heq := (PMF.mem_support_pure_iff _ _).mp hp
  rw [heq]
  exact hscaled

end
end CutQueryComplexity.GHReduction
