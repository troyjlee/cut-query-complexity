import CutQueryComplexity.GHReduction.ThresholdProgram
import CutQueryComplexity.Probability.Expectation

/-! # Expected progress of the concrete sampled threshold routine

A hidden canonical shore is used only as a correctness witness. A hit earns
its shore's terminal count. At a fixed level, hit shores are disjoint; across
levels, a covered terminal is charged at most once per level. This avoids an
incorrect claim that the events for different target shores are independent.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators ENNReal
open WeightedGraph Probability

variable {V : Type} [Fintype V] [DecidableEq V]

theorem uniqueSurvivor_canonical_disjoint (G : WeightedGraph V) (U : Finset V)
    {s u v : V} {C D : Finset V} (hC : IsCanonicalSTCut G u s C)
    (hD : IsCanonicalSTCut G v s D) (huU : u ∈ U) (hvU : v ∈ U) (huv : u ≠ v)
    {levels i : ℕ} (seed : ThresholdSeed V levels)
    (hu : UniqueSurvivor (C ∩ U) u i seed)
    (hv : UniqueSurvivor (D ∩ U) v i seed) : Disjoint (C ∩ U) (D ∩ U) := by
  rcases canonicalST_laminar G hC hD with hCD | hDC | hdisj
  · have huD : u ∈ (D ∩ U).erase v :=
      Finset.mem_erase.mpr ⟨huv, Finset.mem_inter.mpr ⟨hCD hC.1.1, huU⟩⟩
    exact (hv.2 u huD hu.1).elim
  · have hvC : v ∈ (C ∩ U).erase u :=
      Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_inter.mpr ⟨hDC hD.1.1, hvU⟩⟩
    exact (hu.2 v hvC hv.1).elim
  · exact hdisj.mono Finset.inter_subset_left Finset.inter_subset_left

def successfulTargets {levels : ℕ} (D U : Finset V) (C : V → Finset V)
    (index : V → Fin (levels + 1)) (i : Fin (levels + 1)) (seed : ThresholdSeed V levels) :
    Finset V :=
  D.filter (fun v => index v = i ∧ UniqueSurvivor (C v ∩ U) v (index v).val seed)

theorem successfulTargets_charge {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (D U : Finset V) (s : V)
    (W : ℝ) (z levels : ℕ) (C : V → Finset V) (index : V → Fin (levels + 1))
    (hDU : D ⊆ U) (hsU : s ∈ U)
    (hC : ∀ v ∈ D, IsCanonicalSTCut G v s (C v))
    (hvalue : ∀ v ∈ D, stValue G v s ≤ W)
    (hsize : ∀ v ∈ D, (C v ∩ U).card ≤ z)
    (seed : ThresholdSeed V levels) (i : Fin (levels + 1)) :
    (∑ v ∈ successfulTargets D U C index i seed, (C v ∩ U).card) ≤
      (Prog.eval G.cut (thresholdLevelProgram family U
        (levelSample U s i.val seed) s W z)).card := by
  let A := successfulTargets D U C index i seed
  have hA (v : V) (hv : v ∈ A) :
      v ∈ D ∧ index v = i ∧ UniqueSurvivor (C v ∩ U) v i.val seed := by
    obtain ⟨hvD, hindex, hhit⟩ := Finset.mem_filter.mp hv
    exact ⟨hvD, hindex, hindex ▸ hhit⟩
  have hdisj : (A : Set V).PairwiseDisjoint (fun v => C v ∩ U) := by
    intro v hv w hw hvw
    exact uniqueSurvivor_canonical_disjoint G U (hC v (hA v hv).1) (hC w (hA w hw).1)
      (hDU (hA v hv).1) (hDU (hA w hw).1) hvw seed (hA v hv).2.2 (hA w hw).2.2
  have hsub : A.biUnion (fun v => C v ∩ U) ⊆
      Prog.eval G.cut (thresholdLevelProgram family U (levelSample U s i.val seed) s W z) := by
    intro x hx
    obtain ⟨v, hv, hx⟩ := Finset.mem_biUnion.mp hx
    have hcanon := hC v (hA v hv).1
    have htrace : C v ∩ levelSample U s i.val seed = {v} := by
      rw [Finset.inter_comm]
      exact uniqueSurvivor_trace U (C v) s seed
        (Finset.mem_inter.mpr ⟨hcanon.1.1, hDU (hA v hv).1⟩) hcanon.1.2.1 (hA v hv).2.2
    exact thresholdLevelProgram_hit family G hG (source_mem_levelSample hsU i.val seed)
      hcanon htrace (hvalue v (hA v hv).1) (hsize v (hA v hv).1) hx
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card hsub

theorem thresholdRoundProgram_charge {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (D U : Finset V) (s : V)
    (W : ℝ) (z levels : ℕ) (C : V → Finset V) (index : V → Fin (levels + 1))
    (hDU : D ⊆ U) (hsU : s ∈ U)
    (hC : ∀ v ∈ D, IsCanonicalSTCut G v s (C v))
    (hvalue : ∀ v ∈ D, stValue G v s ≤ W)
    (hsize : ∀ v ∈ D, (C v ∩ U).card ≤ z) (seed : ThresholdSeed V levels) :
    (∑ v ∈ D, if UniqueSurvivor (C v ∩ U) v (index v).val seed
      then (C v ∩ U).card else 0) ≤
        (levels + 1) * (Prog.eval G.cut (thresholdRoundProgram family U s W z levels seed)).card := by
  have he : (∑ v ∈ D, if UniqueSurvivor (C v ∩ U) v (index v).val seed
        then (C v ∩ U).card else 0) =
      ∑ i : Fin (levels + 1), ∑ v ∈ successfulTargets D U C index i seed, (C v ∩ U).card := by
    simp only [successfulTargets, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hh : UniqueSurvivor (C v ∩ U) v (index v).val seed
    · simp [hh]
    · simp [hh]
  rw [he]
  calc
    _ ≤ ∑ i : Fin (levels + 1), (Prog.eval G.cut
        (thresholdLevelProgram family U (levelSample U s i.val seed) s W z)).card :=
      Finset.sum_le_sum (fun i _ =>
        successfulTargets_charge family G hG D U s W z levels C index hDU hsU hC hvalue hsize seed i)
    _ ≤ ∑ _i : Fin (levels + 1),
        (Prog.eval G.cut (thresholdRoundProgram family U s W z levels seed)).card := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.card_le_card
      intro x hx
      exact (mem_thresholdRoundProgram family U s W z levels seed G.cut x).mpr ⟨i, hx⟩
    _ = _ := by simp

/-- Expected coverage is at least the number of relevant terminals divided by
eight times the number of levels. All randomness is the actual public seed. -/
theorem thresholdRoundProgram_expected_progress {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (D U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) (C : V → Finset V)
    (hlevels : thresholdLevels U.card ≤ levels) (hDU : D ⊆ U) (hsU : s ∈ U)
    (hC : ∀ v ∈ D, IsCanonicalSTCut G v s (C v))
    (hvalue : ∀ v ∈ D, stValue G v s ≤ W)
    (hsize : ∀ v ∈ D, (C v ∩ U).card ≤ z) :
    (D.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) ≤ (levels + 1 : ℕ) *
      expect (thresholdSeedPMF V levels) (fun seed =>
        ((Prog.eval G.cut (thresholdRoundProgram family U s W z levels seed)).card : ℝ≥0∞)) := by
  let index : V → Fin (levels + 1) := fun v =>
    ⟨hitLevel (C v ∩ U).card, Nat.lt_succ_of_le
      ((hitLevel_le (Finset.card_le_card Finset.inter_subset_right)).trans hlevels)⟩
  let score (seed : ThresholdSeed V levels) : ℝ≥0∞ :=
    ∑ v ∈ D, if UniqueSurvivor (C v ∩ U) v (index v).val seed
      then ((C v ∩ U).card : ℝ≥0∞) else 0
  have hlower : (D.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) ≤
      expect (thresholdSeedPMF V levels) score := by
    rw [show score = (fun seed => ∑ v ∈ D,
      if UniqueSurvivor (C v ∩ U) v (index v).val seed
        then ((C v ∩ U).card : ℝ≥0∞) else 0) from rfl, expect_sum]
    calc
      _ = ∑ _v ∈ D, ENNReal.ofReal (1 / 8 : ℝ) := by simp [nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        rw [expect_indicator]
        exact uniqueSurvivor_hitLevel (C v ∩ U)
          (Finset.mem_inter.mpr ⟨(hC v hv).1.1, hDU hv⟩) (by exact Nat.le_of_lt_succ (index v).isLt)
  have hupper : expect (thresholdSeedPMF V levels) score ≤
      expect (thresholdSeedPMF V levels) (fun seed => (levels + 1 : ℕ) *
        ((Prog.eval G.cut (thresholdRoundProgram family U s W z levels seed)).card : ℝ≥0∞)) := by
    apply expect_mono_on_support
    intro seed hseed
    have h := thresholdRoundProgram_charge family G hG D U s W z levels C index
      hDU hsU hC hvalue hsize seed
    have hcast := (Nat.cast_le (α := ℝ≥0∞)).mpr h
    simpa only [score, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul] using hcast
  exact hlower.trans (hupper.trans_eq (expect_const_mul _ _ _))

end
end CutQueryComplexity.GHReduction
