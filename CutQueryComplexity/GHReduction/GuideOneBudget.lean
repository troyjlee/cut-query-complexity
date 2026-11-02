import CutQueryComplexity.GHReduction.GuideOneComplete

/-! # Aggregate query bound for the concrete one-respecting recursion

All costs are multiplied by the original reference size `n`. The primitive's
capacity parameter and size regularity stay fixed at that reference. The sharp
bound uses the two conserved potentials of the actual isolating outputs.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

theorem centroidPairProgram_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) (read : Finset V → ℝ) :
    Prog.cost read (centroidPairProgram family T) ≤ Q (Fintype.card V) + 1 := by
  unfold centroidPairProgram
  split
  · exact pairCandidateProgram_cost family _ _ read
  · simp

theorem centroidPairProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    n * Prog.cost read (centroidPairProgram family T) ≤ Fintype.card V * (Q n + n) := by
  haveI : Nonempty V := ⟨T.source⟩
  have hs : 1 ≤ Fintype.card V := Fintype.card_pos
  have hreg := hQ _ hs hvn
  have hsmall := Nat.mul_le_mul_left n (centroidPairProgram_cost family T read)
  have hn := Nat.mul_le_mul_right n hs
  nlinarith

theorem guideBaseProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N) (hsmall : T.real.card ≤ 10)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    n * Prog.cost read (guideBaseProgram family T) ≤ (10 * Fintype.card V) * (Q n + n) := by
  have h := sourceBaseProgram_cost_scaled family T.source T.realVertices hvn hQ read
  rw [T.realVertices_card] at h
  have h1 := Nat.mul_le_mul_right (Fintype.card V * Q n) hsmall
  have h2 := Nat.mul_le_mul_right n T.real_card_le
  change n * Prog.cost read (sourceBaseProgram family T.source T.realVertices) ≤ _
  nlinarith

theorem childGuide_graph_size_le (T : GuideTree V N) (P : T.parts) (S : Finset V)
    (htrace : S ∩ T.realVertices = T.graphGroup P.val) :
    Fintype.card (ShoreVertex S) ≤ Fintype.card V := by
  rw [shoreVertex_card]
  apply child_size_le_parent S T.realVertices
  · rw [htrace]
    exact T.graphGroup_half P.property
  · exact ⟨T.source, T.source_mem⟩

theorem guideOneProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (fuel : ℕ) :
    ∀ {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
      (G : WeightedGraph V), InputPromise M G → ∀ T : GuideTree V N,
      Fintype.card V ≤ n →
      n * Prog.cost G.cut (guideOneProgram family fuel T) ≤
        (10 * Fintype.card V + fuel * (Nat.clog 2 n + 23) *
          guideWork (Fintype.card V) T.real.card) * (Q n + n) := by
  induction fuel with
  | zero =>
    intro V N _ _ _ _ G hG T hvn
    by_cases hsmall : T.real.card ≤ 10
    · simpa only [guideOneProgram, hsmall, ite_true, zero_mul, add_zero] using
        guideBaseProgram_cost_scaled family T hsmall hvn hQ G.cut
    · simp [guideOneProgram, hsmall]
  | succ fuel ih =>
    intro V N _ _ _ _ G hG T hvn
    by_cases hsmall : T.real.card ≤ 10
    · simp only [guideOneProgram, hsmall, ite_true]
      exact (guideBaseProgram_cost_scaled family T hsmall hvn hQ G.cut).trans
        (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    · have hlarge : 2 < T.real.card := by omega
      let S : T.parts → Finset V := Prog.eval G.cut (centroidShoreProgram family T)
      have htrace : ∀ P : T.parts, S P ∩ T.realVertices = T.graphGroup P.val :=
        fun P => (centroidShoreProgram_correct family G hG T hlarge P).1.1
      let child (P : T.parts) := childGuide T P (S P) (htrace P)
      let size (P : T.parts) := Fintype.card (ShoreVertex (S P))
      let work (P : T.parts) := guideWork (size P) (child P).real.card
      let cost (P : T.parts) := Prog.cost (G.contract (shoreMap (S P))).cut
        (guideOneProgram family fuel (child P))
      let overhead := Prog.cost G.cut (centroidPairProgram family T) +
        Prog.cost G.cut (centroidShoreProgram family T)
      have hchild : ∀ P, n * cost P ≤ (10 * size P + fuel * (Nat.clog 2 n + 23) * work P) * (Q n + n) := by
        intro P
        exact ih _ (shore_contraction_promise G hG (S P)) (child P)
          ((childGuide_graph_size_le T P (S P) (htrace P)).trans hvn)
      have hsize : (∑ P, size P) ≤ 2 * Fintype.card V := by
        have h := centroid_children_total_size family G hG T hlarge
        have hr := T.real_card_le
        simp only [size, shoreVertex_card]
        exact h.trans (by omega)
      have hwork : (∑ P, work P) ≤ guideWork (Fintype.card V) T.real.card := by
        have h := centroid_children_guideWork family G hG T hlarge
        have hcards : ∀ P : T.parts, (T.graphGroup P.val).card = P.val.card :=
          fun P => T.graphGroup_card (T.part_subset P.property)
        simpa only [work, size, child, shoreVertex_card, childGuide_real_card, hcards] using h
      have hsw : Fintype.card V ≤ guideWork (Fintype.card V) T.real.card :=
        size_le_guideWork T.real_card_le (by omega)
      have hoverhead : n * overhead ≤ ((Nat.clog 2 n + 3) * Fintype.card V) * (Q n + n) := by
        have hp := centroidPairProgram_cost_scaled family T hvn hQ G.cut
        have hi := centroidShoreProgram_cost_scaled family T hvn hQ G.cut
        have hi' : n * Prog.cost G.cut (centroidShoreProgram family T) ≤
            ((Nat.clog 2 n + 2) * Fintype.card V) * (Q n + n) :=
          hi.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
        change n * (Prog.cost G.cut (centroidPairProgram family T) +
          Prog.cost G.cut (centroidShoreProgram family T)) ≤ _
        nlinarith
      have hread : ∀ P : T.parts, G.cut ∘ pull (shoreMap (S P)) = (G.contract (shoreMap (S P))).cut := by
        intro P
        funext X
        exact (cut_contract G _ X).symm
      have hstep : Prog.cost G.cut (guideOneProgram family (fuel + 1) T) = overhead + ∑ P, cost P := by
        simp only [guideOneProgram, hsmall, ite_false, Prog.cost_bind, Prog.cost_map,
          finiteTable_cost]
        rw [show Prog.eval G.cut (centroidShoreProgram family T) = S from rfl]
        simp only [htrace, dite_true, Prog.cost_map, queryMap_cost, hread]
        change _ = (Prog.cost G.cut (centroidPairProgram family T) +
          Prog.cost G.cut (centroidShoreProgram family T)) + ∑ P, cost P
        exact (Nat.add_assoc _ _ _).symm
      rw [hstep]
      exact guide_cost_recurrence cost size work hsize hwork hsw hoverhead hchild

theorem guideOneProgram_root_cost {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hQ : SizeRegular (Fintype.card V) Q) (fuel : ℕ) :
    Prog.cost G.cut (guideOneProgram family fuel T) ≤
      (10 + 2 * fuel * (Nat.clog 2 (Fintype.card V) + 23)) * (Q (Fintype.card V) + Fintype.card V) := by
  haveI : Nonempty V := ⟨T.source⟩
  exact guide_root_budget Fintype.card_pos T.real_card_le
    (guideOneProgram_cost_scaled family hQ fuel G hG T le_rfl)

end
end CutQueryComplexity.GHReduction
