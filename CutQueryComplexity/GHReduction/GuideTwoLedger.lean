import CutQueryComplexity.GHReduction.GuideBranchCosts

/-! # A realized-query ledger for the concrete two-respecting program

Recursive child costs are summed on their actual contracted vertex types. The
other branches keep the current graph and are charged once per actual call.
No size-partition equality, random cost expectation, or Markov cutoff is used.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators

variable {V N J : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
  [Fintype J] [DecidableEq J]

def guideTwoNodeCost (M : ℕ) (Q : ℕ → ℕ) (n trials levels scale exponent : ℕ) : ℕ :=
  guideNodeBudget Q n + trials * guideOneGlobalBudget Q n + guideSwitchBudget M Q n levels scale exponent

def guideTwoTailTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials levels scale exponent fuel : ℕ) (T : GuideTree V N) (hvn : Fintype.card V ≤ n)
    (initial : Option (CutCandidate V)) (shores : T.parts → Finset V) :
    RTree (Finset V) ℝ (V → Option ℝ)
      (Fintype.card T.parts * guideTwoBudget M Q n trials levels scale exponent fuel +
        (trials * guideOneGlobalBudget Q n + guideSwitchBudget M Q n levels scale exponent)) :=
  (randomTable (fun _ => none)
    (guideTwoChildTree family n trials levels scale exponent fuel T hvn shores)).bind (fun children =>
      (guidePruneTrialsTree family n trials T).bind (fun pruned =>
        (guideSourceBranchTree family n T levels scale exponent).map
          (guideTwoCombine T initial children pruned)))

theorem guideTwoTree_step_run {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (trials levels scale exponent fuel : ℕ)
    (G : WeightedGraph V) (T : GuideTree V N) (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (hlarge : ¬T.real.card ≤ 10) :
    RTree.run G.cut (guideTwoTree family n trials levels scale exponent (fuel + 1) T hvn) =
      (RTree.run G.cut (guideTwoTailTree family n trials levels scale exponent fuel T hvn
        (Prog.eval G.cut (centroidPairProgram family T))
        (Prog.eval G.cut (centroidShoreProgram family T)))).map
          (fun p => (p.1, Prog.cost G.cut (guideNodeProgram family T) + p.2)) := by
  have hnode : Prog.eval G.cut (guideNodeProgram family T) =
      (Prog.eval G.cut (centroidPairProgram family T),
        Prog.eval G.cut (centroidShoreProgram family T)) := by
    rw [guideNodeProgram, Prog.eval_bind, Prog.eval_map]
  rw [guideTwoTree, ite_eq_right hlarge, RTree.run_weaken, RTree.run_bind,
    guideNodeTree_run family T hvn hQ, hnode, PMF.pure_bind]
  simp only [guideTwoTailTree, RTree.run_bind, RTree.run_weaken]
  unfold guideTwoChildTree
  rfl

theorem guideTwoTailTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (trials levels scale exponent fuel : ℕ)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (initial : Option (CutCandidate V)) (shores : T.parts → Finset V) (budget : T.parts → ℕ)
    (hchildren : ∀ P, ∀ p ∈ (RTree.run G.cut
      (guideTwoChildTree family n trials levels scale exponent fuel T hvn shores P)).support,
      n * p.2 ≤ budget P) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut
      (guideTwoTailTree family n trials levels scale exponent fuel T hvn initial shores)).support) :
    n * p.2 ≤ (∑ P, budget P) + Fintype.card V *
      (trials * guideOneGlobalBudget Q n + guideSwitchBudget M Q n levels scale exponent) := by
  apply random_bind_cost _ _ G.cut n _ _ ?_ ?_ hp
  · intro out hout
    exact randomTable_cost _ _ G.cut n budget hchildren hout
  · intro children _ out hout
    rw [Nat.mul_add]
    apply random_bind_cost _ _ G.cut n _ _ ?_ ?_ hout
    · intro p hp
      exact guidePruneTrialsTree_cost_scaled family G hG T hvn hQ trials hp
    · intro pruned _ p hp
      exact random_map_cost _ _ G.cut n _
        (fun p hp => guideSourceBranchTree_cost_scaled family G hG T levels scale exponent hvn hQ hp) hp

theorem guideTwoTree_step_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (trials levels scale exponent fuel : ℕ)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (hlarge : ¬T.real.card ≤ 10)
    (budget : T.parts → ℕ)
    (hchildren : ∀ P, ∀ p ∈ (RTree.run G.cut
      (guideTwoChildTree family n trials levels scale exponent fuel T hvn
        (Prog.eval G.cut (centroidShoreProgram family T)) P)).support, n * p.2 ≤ budget P)
    {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut
      (guideTwoTree family n trials levels scale exponent (fuel + 1) T hvn)).support) :
    n * p.2 ≤ (∑ P, budget P) + Fintype.card V *
      guideTwoNodeCost M Q n trials levels scale exponent := by
  rw [guideTwoTree_step_run family trials levels scale exponent fuel G T hvn hQ hlarge] at hp
  obtain ⟨tail, htail, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  have htailCost := guideTwoTailTree_cost_scaled family trials levels scale exponent fuel G hG
    T hvn hQ _ _ budget hchildren htail
  have hnode := guideNodeProgram_cost_scaled family T hvn hQ G.cut
  rw [← heq, Nat.mul_add]
  unfold guideTwoNodeCost
  nlinarith

/-- The base-child charge is separate from the conserved internal work. -/
theorem guide_two_cost_recurrence (size work : J → ℕ) {s w fuel K H : ℕ}
    (hsize : (∑ j, size j) ≤ 2 * s) (hwork : (∑ j, work j) ≤ w) (hsw : s ≤ w) :
    (∑ j, (10 * size j * K + fuel * (H + 20 * K) * work j)) + s * H ≤
      10 * s * K + (fuel + 1) * (H + 20 * K) * w := by
  have hsum : (∑ j, (10 * size j * K + fuel * (H + 20 * K) * work j)) =
      10 * (∑ j, size j) * K + fuel * (H + 20 * K) * (∑ j, work j) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsum]
  have hs := Nat.mul_le_mul_right K (Nat.mul_le_mul_left 10 hsize)
  have hw := Nat.mul_le_mul_left (fuel * (H + 20 * K)) hwork
  have hlevel := Nat.mul_le_mul_right (H + 20 * K) hsw
  nlinarith

end
end CutQueryComplexity.GHReduction
