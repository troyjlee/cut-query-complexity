import CutQueryComplexity.GHReduction.GuideTwoExecution

/-! # Completeness and adaptive failure of the actual two-respecting routine

An internal level is charged by real-terminal potential `r - 2`. Its conservation
in the actual canonical children gives a linear-in-depth union bound, including
all pruning targets and all threshold searches. Every statement is conditional
on the current contracted graph; fresh calls are composed with `PMF.bind`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal BigOperators
open Probability

variable {V N J : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
  [Fintype J] [DecidableEq J]

theorem guide_two_error_recurrence (work : J → ℕ) {r fuel : ℕ}
    (hr : 4 ≤ r) (hwork : (∑ j, work j) ≤ r - 2) (α β : ℝ≥0∞) :
    (∑ j, (2 * fuel * work j : ℕ) * (α + β)) + ((r : ℝ≥0∞) * α + β) ≤
      (2 * (fuel + 1) * (r - 2) : ℕ) * (α + β) := by
  have hchildren : (∑ j, (2 * fuel * work j : ℕ) * (α + β)) ≤
      (2 * fuel * (r - 2) : ℕ) * (α + β) := by
    calc
      _ = ((∑ j, 2 * fuel * work j : ℕ) : ℝ≥0∞) * (α + β) := by
        rw [Nat.cast_sum, Finset.sum_mul]
      _ ≤ _ := by
        have hsum : (∑ j, 2 * fuel * work j) ≤ 2 * fuel * (r - 2) := by
          rw [← Finset.mul_sum]
          exact Nat.mul_le_mul_left (2 * fuel) hwork
        gcongr
  have hr1 : (1 : ℝ≥0∞) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hr2 : (r : ℝ≥0∞) ≤ (2 * (r - 2) : ℕ) := by
    exact_mod_cast (show r ≤ 2 * (r - 2) by omega)
  have hlocal : (r : ℝ≥0∞) * α + β ≤ (2 * (r - 2) : ℕ) * (α + β) := by
    calc
      _ ≤ (r : ℝ≥0∞) * α + (r : ℝ≥0∞) * β := by
        gcongr
        simpa only [one_mul] using mul_le_mul' hr1 (le_rfl : β ≤ β)
      _ = (r : ℝ≥0∞) * (α + β) := (mul_add _ _ _).symm
      _ ≤ _ := mul_le_mul' hr2 le_rfl
  calc
    _ ≤ (2 * fuel * (r - 2) : ℕ) * (α + β) +
        (2 * (r - 2) : ℕ) * (α + β) := add_le_add hchildren hlocal
    _ = _ := by
      rw [← add_mul, ← Nat.cast_add]
      congr 2
      ring

def guideTwoError (M trials scale exponent fuel r : ℕ) : ℝ≥0∞ :=
  (2 * fuel * (r - 2) : ℕ) *
    (ENNReal.ofReal (3 / 4 : ℝ) ^ trials +
      (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent))

theorem guideBaseValueTree_success {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hsmall : T.real.card ≤ 10)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    mass ((guideBaseValueTree family n T).eval G.cut) (fun output => ¬GuideTwoSuccess G T output) = 0 := by
  rw [guideBaseValueTree_eval family T hsmall hvn hQ]
  have hsuccess : GuideTwoSuccess G T
      (fun t => candidateEstimate (Prog.eval G.cut (guideBaseProgram family T) t)) := by
    refine ⟨?_, ?_⟩
    · intro t
      exact candidateEstimate_above G (fun C hC => sourceBaseProgram_valid family G T.source
        T.realVertices t hC)
    · intro t ht hrespect
      obtain ⟨S, hS, _⟩ := hrespect
      have hst : T.source ≠ t := fun he => hS.2.1 (he.symm ▸ hS.1)
      obtain ⟨C, hC, hCexact⟩ := sourceBaseProgram_exact family G hG T.source T.realVertices ht hst
      change candidateEstimate (Prog.eval G.cut (sourceBaseProgram family T.source T.realVertices) t) = _
      rw [hC]
      exact candidateEstimate_exact G hCexact
  simp [hsuccess]

theorem guideTwoTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (trials levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels) (fuel : ℕ) :
    ∀ {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
      (G : WeightedGraph V), InputPromise M G → ∀ (T : GuideTree V N)
      (hvn : Fintype.card V ≤ n), T.real.card ≤ 8 * 2 ^ fuel + 2 →
      mass ((guideTwoTree family n trials levels scale exponent fuel T hvn).eval G.cut)
        (fun output => ¬GuideTwoSuccess G T output) ≤
        guideTwoError M trials scale exponent fuel T.real.card := by
  induction fuel with
  | zero =>
    intro V N _ _ _ _ G hG T hvn hdepth
    have hsmall : T.real.card ≤ 10 := by simpa using hdepth
    simp only [guideTwoTree, guideTwoBudget, hsmall, ite_true]
    rw [guideBaseValueTree_success family G hG T hsmall hvn hQ]
    exact zero_le
  | succ fuel ih =>
    intro V N _ _ _ _ G hG T hvn hdepth
    by_cases hsmall : T.real.card ≤ 10
    · rw [guideTwoTree, if_pos hsmall, RTree.eval_weaken,
        guideBaseValueTree_success family G hG T hsmall hvn hQ]
      exact zero_le
    · have hlarge : 2 < T.real.card := by omega
      let δ : T.parts → ℝ≥0∞ := fun P => guideTwoError M trials scale exponent fuel (P.val.card + 1)
      have hchildren (P : T.parts) :
          mass ((guideTwoChildTree family n trials levels scale exponent fuel T hvn
            (Prog.eval G.cut (centroidShoreProgram family T)) P).eval G.cut)
            (fun output => ¬GuideChildSuccess family G T P output) ≤ δ P := by
        apply guideTwoChildTree_failure_le family trials levels scale exponent fuel G hG T hvn hlarge P
        intro htrace
        let S := Prog.eval G.cut (centroidShoreProgram family T) P
        have hchildDepth : (childGuide T P S htrace).real.card ≤ 8 * 2 ^ fuel + 2 := by
          rw [childGuide_real_card]
          exact child_fuel_bound (T.part_half P.property) hdepth
        have h := ih (G.contract (shoreMap S)) (shore_contraction_promise G hG S)
          (childGuide T P S htrace) ((childGuide_graph_size_le T P S htrace).trans hvn) hchildDepth
        simpa only [δ, childGuide_real_card] using h
      have hstep := guideTwoTree_step_failure_le family trials levels exponent fuel G hG T hvn
        hQ hnscale hlevels hsmall δ hchildren
      have hp : (∑ P : T.parts, (P.val.card + 1 - 2)) ≤ T.real.card - 2 := by
        have h := centroid_children_real_potential family G hG T hlarge
        have heq : (∑ P : T.parts, ((T.graphGroup P.val).card + 1 - 2)) =
            ∑ P : T.parts, (P.val.card + 1 - 2) := by
          apply Finset.sum_congr rfl
          intro P _
          rw [T.graphGroup_card (T.part_subset P.property)]
        rwa [heq] at h
      exact hstep.trans (guide_two_error_recurrence (fun P : T.parts => P.val.card + 1 - 2)
        (by omega) hp _ _)

/-- One public logarithmic fuel works on every compact instance of size at most
the original reference size. The failure statement is simultaneous in targets. -/
theorem guideTwoTree_clog_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (trials levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N) (hvn : Fintype.card V ≤ n) :
    mass ((guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1)) T hvn).eval G.cut)
      (fun output => ¬GuideTwoSuccess G T output) ≤
      guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) T.real.card :=
  guideTwoTree_failure_le family hQ hnscale trials levels exponent hlevels _ G hG T hvn
    ((T.real_card_le.trans hvn).trans (initial_fuel_bound n))

end
end CutQueryComplexity.GHReduction
