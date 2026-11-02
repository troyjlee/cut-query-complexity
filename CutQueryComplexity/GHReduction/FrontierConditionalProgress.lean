import CutQueryComplexity.GHReduction.FrontierTrackedFibers
import CutQueryComplexity.GHReduction.DependentTableMarginals

/-! # Conditional progress of the actual capped frontier step

A failed round kills its analysis potential. On a good round the tracked
fiber is exactly its auxiliary sampled child. The actual executed table has
that entry's marginal law, and truncation cannot increase a potential that
is zero on abort. Thus progress holds at every adaptively chosen public state,
without assuming the state was fixed in advance or conditioning on success.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability OuterPivot

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def frontierVertexExcess (state : PublicFrontierState V) (v : V) : ℕ :=
  excess (fiber state.block (state.block v))

def frontierEntryPotential (G : WeightedGraph V) (p : V → B) (T : RootedTree B)
    (b : B) (v : V) {levels : ℕ}
    (out : Option (SourcePivotOutput (FrontierVertex p T b) levels)) : ℕ :=
  out.elim 0 (trackedPivotPotential (G.contract (frontierMap p T b))
    (frontierTerminals p T b) (frontierMap p T b v))

def frontierRoundPotential (G : WeightedGraph V) {levels : ℕ}
    (record : FrontierRoundRecord V levels) (v : V) : ℕ :=
  if record.Good G then frontierVertexExcess record.after v else 0

theorem frontierRoundPotential_none (G : WeightedGraph V) {levels : ℕ}
    (state : PublicFrontierState V) (v : V) :
    frontierRoundPotential G (⟨state, none⟩ : FrontierRoundRecord V levels) v = 0 := by
  simp [frontierRoundPotential, FrontierRoundRecord.Good]

theorem frontierRoundPotential_le_entry (G : WeightedGraph V) {levels : ℕ}
    (record : FrontierRoundRecord V levels)
    (table : (b : Fin record.before.size) → Option
      (SourcePivotOutput (FrontierVertex record.before.block record.before.tree b) levels))
    (hresult : record.result = some table) (v : V) :
    frontierRoundPotential G record v ≤ frontierEntryPotential G record.before.block record.before.tree
      (record.before.block v) v (table (record.before.block v)) := by
  by_cases hgood : record.Good G
  · rw [frontierRoundPotential, if_pos hgood]
    let b := record.before.block v
    have hg : FrontierPivotGood G record.before.block record.before.tree b (table b) := by
      exact (show ∀ c, FrontierPivotGood G record.before.block record.before.tree c (table c) from
        by simpa only [FrontierRoundRecord.Good, hresult, Option.elim_some] using hgood) b
    by_cases hactive : 2 ≤ (fiber record.before.block b).card
    · have hg' : (table b).elim False
          (SourcePivotGood (G.contract (frontierMap record.before.block record.before.tree b))
            (frontierTerminals record.before.block record.before.tree b)) := by
        simpa only [FrontierPivotGood, hactive, ite_true] using hg
      cases hout : table b with
      | none => simp only [hout, Option.elim_none] at hg'
      | some out =>
          have houtgood : SourcePivotGood (G.contract (frontierMap record.before.block record.before.tree b))
              (frontierTerminals record.before.block record.before.tree b) out := by
            simpa only [hout, Option.elim_some] using hg'
          have hsplit : record.split b = checkedFrontierSplit record.before.block record.before.onto
              record.before.tree b (some out) := by
            simp only [FrontierRoundRecord.split, hresult, Option.elim_some, hout]
          have hcard := advanceFrontierState_tracked_card record.before record.split record.split_valid
            b out houtgood.1 houtgood.2.2.1 hsplit v rfl
          change (fiber record.after.block (record.after.block v)).card = _ at hcard
          change excess (fiber record.after.block (record.after.block v)) ≤
            frontierEntryPotential G record.before.block record.before.tree b v (some out)
          rw [frontierEntryPotential, Option.elim_some, trackedPivotPotential,
            if_pos houtgood.2.1]
          exact (congrArg (fun k => k - 1) hcard).le
    · have hsubset := advanceFrontierState_fiber_subset record.before record.split record.split_valid v
      have hcard := Finset.card_le_card hsubset
      change (fiber record.after.block (record.after.block v)).card ≤
        (fiber record.before.block b).card at hcard
      have hz : frontierVertexExcess record.after v = 0 := by
        unfold frontierVertexExcess excess
        omega
      rw [hz]
      exact Nat.zero_le _
  · rw [frontierRoundPotential, if_neg hgood]
    exact Nat.zero_le _

theorem frontierPivotCall_expected_entry {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (b : B) (v : V) (hvn : Fintype.card V ≤ n) :
    expect ((frontierPivotCall family n samples trials guideLevels scale exponent levels
      K p hp T b hvn).eval G.cut)
      (fun out => (frontierEntryPotential G p T b v out : ℝ≥0∞)) ≤
      contractionRate levels * (excess (fiber p b) : ℝ≥0∞) := by
  by_cases hactive : 2 ≤ (fiber p b).card
  · rw [frontierPivotCall, if_pos hactive, RTree.eval_map, contractProgram_eval, expect_map]
    have hlocalLevels : thresholdLevels (frontierTerminals p T b).card ≤ levels := by
      rw [frontierTerminals_card]
      exact (Nat.clog_mono_right 2
        (Nat.mul_le_mul_left 2 ((Finset.card_le_univ (fiber p b)).trans hvn))).trans hlevels
    have h := sourcePivotTree_expected_tracked_potential family
      ((frontierVertex_card_le p hp T b).trans hvn) hQ
      (G.contract (frontierMap p T b)) (K.contract (frontierMap p T b))
      (frontier_contraction_promise G hG p T b) (frontierTerminals p T b)
      (frontierTerminals_nonempty p hp T b) (frontierMap p T b v)
      samples trials guideLevels scale exponent levels hlocalLevels
    simpa only [frontierEntryPotential, Option.elim_some, excess, frontierTerminals_card] using h
  · simp only [frontierPivotCall, if_neg hactive, RTree.eval_pure, expect_pure,
      frontierEntryPotential, Option.elim_none, Nat.cast_zero]
    exact zero_le

theorem frontierStateStep_expected_potential {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (state : PublicFrontierState V) (v : V) :
    expect ((frontierStateStep family n samples trials guideLevels scale exponent levels K hvn state).eval G.cut)
      (fun record => (frontierRoundPotential G record v : ℝ≥0∞)) ≤
      contractionRate levels * (frontierVertexExcess state v : ℝ≥0∞) := by
  let localPotential := fun (out : Option
      (SourcePivotOutput (FrontierVertex state.block state.tree (state.block v)) levels)) =>
    (frontierEntryPotential G state.block state.tree (state.block v) v out : ℝ≥0∞)
  unfold frontierStateStep frontierRoundBudget
  rw [RTree.eval_map, expect_map]
  calc
    _ ≤ expect ((frontierPivotRoundCapped family n samples trials guideLevels scale exponent levels
        K state.block state.onto state.tree hvn).eval G.cut)
        (fun out => out.elim 0 (fun table => localPotential (table (state.block v)))) := by
      apply expect_mono_on_support
      intro out _
      cases out with
      | none => simp only [frontierRoundPotential_none, Nat.cast_zero, Option.elim_none, le_refl]
      | some table =>
          change (frontierRoundPotential G (⟨state, some table⟩ : FrontierRoundRecord V levels) v : ℝ≥0∞) ≤
            (frontierEntryPotential G state.block state.tree (state.block v) v (table (state.block v)) : ℝ≥0∞)
          exact (Nat.cast_le (α := ℝ≥0∞)).mpr (frontierRoundPotential_le_entry G
            (⟨state, some table⟩ : FrontierRoundRecord V levels) table rfl v)
    _ ≤ expect ((frontierPivotRound family n samples trials guideLevels scale exponent levels
        K state.block state.onto state.tree hvn).eval G.cut)
        (fun table => localPotential (table (state.block v))) :=
      truncate_expect_zero_le _ _ G.cut _
    _ = expect ((frontierPivotCall family n samples trials guideLevels scale exponent levels
        K state.block state.onto state.tree (state.block v) hvn).eval G.cut) localPotential := by
      unfold frontierPivotRound
      exact dependentRandomTable_expect_entry (fun _ => none)
        (fun b => frontierPivotCall family n samples trials guideLevels scale exponent levels
          K state.block state.onto state.tree b hvn) G.cut (state.block v) localPotential
    _ ≤ _ := frontierPivotCall_expected_entry family hQ samples trials guideLevels scale exponent levels
      hlevels G K hG state.block state.onto state.tree (state.block v) v hvn

end
end CutQueryComplexity.GHReduction
