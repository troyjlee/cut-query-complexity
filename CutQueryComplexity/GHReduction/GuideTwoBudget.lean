import CutQueryComplexity.GHReduction.GuideTwoLedger

/-! # Sharp aggregate budget for the implemented two-respecting routine

The proof uses the actual isolating outputs and both repaired potentials.
Whole-graph pruning and source-switch calls occur in the local coefficient;
same-parameter children use conserved work. Zero-potential base children are
paid by their parent's total child-size bound.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

theorem guideTwoTree_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (trials levels scale exponent fuel : ℕ) :
    ∀ {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
      (G : WeightedGraph V), InputPromise M G → ∀ (T : GuideTree V N)
      (hvn : Fintype.card V ≤ n), ∀ p ∈ (RTree.run G.cut
        (guideTwoTree family n trials levels scale exponent fuel T hvn)).support,
      n * p.2 ≤ 10 * Fintype.card V * (Q n + n) +
        fuel * (guideTwoNodeCost M Q n trials levels scale exponent + 20 * (Q n + n)) *
          guideWork (Fintype.card V) T.real.card := by
  induction fuel with
  | zero =>
    intro V N _ _ _ _ G hG T hvn p hp
    by_cases hsmall : T.real.card ≤ 10
    · simp only [guideTwoTree, guideTwoBudget, hsmall, ite_true] at hp
      simpa only [zero_mul, add_zero] using
        guideBaseValueTree_cost_scaled family T hsmall hvn hQ G.cut hp
    · simp only [guideTwoTree, guideTwoBudget, hsmall, ite_false, RTree.run_pure, PMF.pure_map] at hp
      have heq := (PMF.mem_support_pure_iff _ _).mp hp
      rw [heq]
      simp
  | succ fuel ih =>
    intro V N _ _ _ _ G hG T hvn p hp
    by_cases hsmall : T.real.card ≤ 10
    · simp only [guideTwoTree, hsmall, ite_true, RTree.run_weaken] at hp
      exact (guideBaseValueTree_cost_scaled family T hsmall hvn hQ G.cut hp).trans
        (Nat.le_add_right _ _)
    · have hlarge : 2 < T.real.card := by omega
      let S := Prog.eval G.cut (centroidShoreProgram family T)
      have htrace (P : T.parts) : S P ∩ T.realVertices = T.graphGroup P.val :=
        (centroidShoreProgram_correct family G hG T hlarge P).1.1
      let size : T.parts → ℕ := fun P => (S P).card + 1
      let work : T.parts → ℕ := fun P => guideWork (size P) (P.val.card + 1)
      let H := guideTwoNodeCost M Q n trials levels scale exponent
      let K := Q n + n
      let budget : T.parts → ℕ := fun P => 10 * size P * K + fuel * (H + 20 * K) * work P
      have hchildren (P : T.parts) : ∀ out ∈ (RTree.run G.cut
          (guideTwoChildTree family n trials levels scale exponent fuel T hvn S P)).support,
          n * out.2 ≤ budget P := by
        intro out hout
        simp only [guideTwoChildTree, htrace P, dite_true, random_run_map,
          contractProgram_graph_run] at hout
        obtain ⟨childOut, hchildOut, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
        rw [← heq]
        have h := ih (G.contract (shoreMap (S P))) (shore_contraction_promise G hG (S P))
          (childGuide T P (S P) (htrace P))
          ((childGuide_graph_size_le T P (S P) (htrace P)).trans hvn) childOut hchildOut
        simpa only [budget, size, work, H, K, shoreVertex_card, childGuide_real_card] using h
      have hsize : (∑ P, size P) ≤ 2 * Fintype.card V := by
        have h := centroid_children_total_size family G hG T hlarge
        have hr := T.real_card_le
        exact h.trans (by omega)
      have hwork : (∑ P, work P) ≤ guideWork (Fintype.card V) T.real.card := by
        have h := centroid_children_guideWork family G hG T hlarge
        have hcards : ∀ P : T.parts, (T.graphGroup P.val).card = P.val.card :=
          fun P => T.graphGroup_card (T.part_subset P.property)
        simpa only [work, size, hcards] using h
      have hsw : Fintype.card V ≤ guideWork (Fintype.card V) T.real.card :=
        size_le_guideWork T.real_card_le (by omega)
      have hstep := guideTwoTree_step_cost_scaled family trials levels scale exponent fuel G hG T
        hvn hQ hsmall budget hchildren hp
      exact hstep.trans (guide_two_cost_recurrence size work hsize hwork hsw)

def guideTwoSharpBudget (M : ℕ) (Q : ℕ → ℕ) (n trials levels scale exponent fuel : ℕ) : ℕ :=
  10 * (Q n + n) + 2 * fuel *
    (guideTwoNodeCost M Q n trials levels scale exponent + 20 * (Q n + n))

theorem guideTwoTree_cost_linear {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (trials levels scale exponent fuel : ℕ) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut
      (guideTwoTree family n trials levels scale exponent fuel T hvn)).support) :
    n * p.2 ≤ Fintype.card V * guideTwoSharpBudget M Q n trials levels scale exponent fuel := by
  have h := guideTwoTree_cost_scaled family hQ trials levels scale exponent fuel G hG T hvn p hp
  have hw := guideWork_le_twice_size T.real_card_le
  calc
    _ ≤ 10 * Fintype.card V * (Q n + n) +
        fuel * (guideTwoNodeCost M Q n trials levels scale exponent + 20 * (Q n + n)) *
          guideWork (Fintype.card V) T.real.card := h
    _ ≤ 10 * Fintype.card V * (Q n + n) +
        fuel * (guideTwoNodeCost M Q n trials levels scale exponent + 20 * (Q n + n)) *
          (2 * Fintype.card V) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hw) _
    _ = _ := by unfold guideTwoSharpBudget; ring

theorem guideTwoTree_cost_le_sharp {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (trials levels scale exponent fuel : ℕ) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut
      (guideTwoTree family n trials levels scale exponent fuel T hvn)).support) :
    p.2 ≤ guideTwoSharpBudget M Q n trials levels scale exponent fuel := by
  haveI : Nonempty V := ⟨T.source⟩
  exact cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
    (guideTwoTree_cost_linear family hQ trials levels scale exponent fuel G hG T hvn hp)

end
end CutQueryComplexity.GHReduction
