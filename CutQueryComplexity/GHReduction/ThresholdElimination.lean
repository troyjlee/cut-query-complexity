import CutQueryComplexity.GHReduction.ThresholdEndpoint

/-! # Conditional progress and failure of adaptive threshold elimination

Every iteration is analyzed after fixing the earlier transcript. The terminal
set may depend on that transcript, and only the next seed is fresh. The failure
bound below concerns missed terminals, not a tail bound on query cost: the
query cap is already present in the executable randomized tree.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V : Type} [Fintype V] [DecidableEq V]

def lowTargets (G : WeightedGraph V) (U : Finset V) (s : V) (W : ℝ) : Finset V :=
  U.filter (fun v => v ≠ s ∧ stValue G v s ≤ W)

@[simp] theorem mem_lowTargets (G : WeightedGraph V) (U : Finset V) (s : V) (W : ℝ) (v : V) :
    v ∈ lowTargets G U s W ↔ v ∈ U ∧ v ≠ s ∧ stValue G v s ≤ W := by simp [lowTargets]

theorem lowTargets_sdiff (G : WeightedGraph V) (U D : Finset V) (s : V) (W : ℝ) :
    lowTargets G (U \ D) s W = lowTargets G U s W \ D := by
  ext v
  simp only [mem_lowTargets, Finset.mem_sdiff]
  tauto

def thresholdRate (levels : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - (8 * (levels + 1 : ℝ))⁻¹)

theorem thresholdRate_arg_nonneg (levels : ℕ) : 0 ≤ 1 - (8 * (levels + 1 : ℝ))⁻¹ := by
  have hK : (1 : ℝ) ≤ 8 * (levels + 1 : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) levels
    linarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hK
  simp only [one_div, inv_one] at hi
  linarith

theorem expect_finset_card_ne_top {α : Type} (P : PMF α) (F : α → Finset V) :
    expect P (fun a => ((F a).card : ℝ≥0∞)) ≠ ∞ := by
  have hbound : expect P (fun a => ((F a).card : ℝ≥0∞)) ≤ (Fintype.card V : ℝ≥0∞) :=
    expect_le_of_le_on_support P (fun a _ => Nat.cast_le.mpr (Finset.card_le_univ (F a)))
  exact ne_of_lt (hbound.trans_lt (by simp))

/-- A finite-set accounting lemma. It applies to any conditional distribution
of actually covered subsets; no independence between covered vertices is used. -/
theorem expected_remainder_of_progress (P : PMF (Finset V)) (D : Finset V) (levels : ℕ)
    (hsub : ∀ C ∈ P.support, C ⊆ D)
    (hprogress : (D.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) ≤
      (levels + 1 : ℕ) * expect P (fun C => (C.card : ℝ≥0∞))) :
    expect P (fun C => ((D \ C).card : ℝ≥0∞)) ≤ thresholdRate levels * (D.card : ℝ≥0∞) := by
  let erased := expect P (fun C => (C.card : ℝ≥0∞))
  let remain := expect P (fun C => ((D \ C).card : ℝ≥0∞))
  let K : ℝ≥0∞ := ((8 * (levels + 1) : ℕ) : ℝ≥0∞)
  have herased : erased ≠ ∞ := expect_finset_card_ne_top P id
  have hremain : remain ≠ ∞ := expect_finset_card_ne_top P (fun C => D \ C)
  have hK : K ≠ ∞ := ENNReal.natCast_ne_top _
  have hsum : remain + erased = (D.card : ℝ≥0∞) := by
    rw [show remain + erased = expect P (fun C => ((D \ C).card : ℝ≥0∞)) +
      expect P (fun C => (C.card : ℝ≥0∞)) from rfl, ← expect_add]
    calc
      _ = expect P (fun _ => (D.card : ℝ≥0∞)) := by
        apply expect_congr_on_support
        intro C hC
        exact_mod_cast Finset.card_sdiff_add_card_eq_card (hsub C hC)
      _ = _ := expect_const _ _
  have hcharge : (D.card : ℝ≥0∞) ≤ K * erased := by
    have hconst : (8 : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) = 1 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8)]
      norm_num [div_eq_mul_inv]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      _ = 8 * ((D.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ)) := by
        rw [mul_left_comm, hconst, mul_one]
      _ ≤ 8 * ((levels + 1 : ℕ) * erased) := mul_le_mul' le_rfl hprogress
      _ = K * erased := by simp only [K, Nat.cast_mul, Nat.cast_ofNat]; ring
  have hlinear : K * remain + (D.card : ℝ≥0∞) ≤ K * (D.card : ℝ≥0∞) := by
    calc
      _ ≤ K * remain + K * erased := add_le_add le_rfl hcharge
      _ = K * (D.card : ℝ≥0∞) := by rw [← mul_add, hsum]
  have hKreal : K.toReal = 8 * (levels + 1 : ℝ) := by
    change ((8 * (levels + 1) : ℕ) : ℝ≥0∞).toReal = _
    rw [ENNReal.toReal_natCast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hK (by simp)) hlinear
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hK hremain) (ENNReal.natCast_ne_top D.card),
    ENNReal.toReal_mul, hKreal, ENNReal.toReal_mul, hKreal] at hreal
  simp only [ENNReal.toReal_natCast] at hreal
  apply (ENNReal.toReal_le_toReal hremain
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (thresholdRate_arg_nonneg levels),
    ENNReal.toReal_natCast]
  have hpos : (0 : ℝ) < 8 * (levels + 1 : ℝ) := by positivity
  have hcancel : (8 * (levels + 1 : ℝ)) * (1 - (8 * (levels + 1 : ℝ))⁻¹) =
      8 * (levels + 1 : ℝ) - 1 := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ (ne_of_gt hpos)]
  apply (mul_le_mul_iff_of_pos_left hpos).mp
  rw [← mul_assoc, hcancel]
  nlinarith

theorem thresholdRoundTree_expected_remainder {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V) (W : ℝ)
    (levels : ℕ) (hlevels : thresholdLevels n ≤ levels) (hsU : s ∈ U) :
    expect ((thresholdRoundTree family n U s W n levels).eval G.cut)
      (fun C => ((lowTargets G (U \ C) s W).card : ℝ≥0∞)) ≤
        thresholdRate levels * ((lowTargets G U s W).card : ℝ≥0∞) := by
  let D := lowTargets G U s W
  let C (v : V) : Finset V := if hv : v ∈ D then
    Classical.choose (exists_canonicalSTCut G ((mem_lowTargets G U s W v).mp hv).2.1) else ∅
  have hC (v : V) (hv : v ∈ D) : IsCanonicalSTCut G v s (C v) := by
    simpa only [C, hv, dite_true] using
      Classical.choose_spec (exists_canonicalSTCut G ((mem_lowTargets G U s W v).mp hv).2.1)
  have hDU : D ⊆ U := Finset.filter_subset _ _
  have hW (v : V) (hv : v ∈ D) : stValue G v s ≤ W :=
    ((mem_lowTargets G U s W v).mp hv).2.2
  have hsize (v : V) (_hv : v ∈ D) : (C v ∩ U).card ≤ n :=
    (Finset.card_le_univ _).trans hvn
  have hlevU : thresholdLevels U.card ≤ levels :=
    (Nat.clog_mono_right 2 (Nat.mul_le_mul_left 2 ((Finset.card_le_univ U).trans hvn))).trans hlevels
  have hprog := thresholdRoundTree_expected_progress family hvn hQ G hG D U s W n levels C
    hlevU hDU hsU hC hW hsize
  have hsub : ∀ covered ∈ ((thresholdRoundTree family n U s W n levels).eval G.cut).support,
      covered ⊆ D := by
    intro covered hc v hv
    exact (mem_lowTargets G U s W v).mpr
      (thresholdRoundTree_sound family hvn hQ G U s W n levels hc v hv)
  simpa only [lowTargets_sdiff] using expected_remainder_of_progress _ D levels hsub hprog

/-- Fresh conditional progress multiplies through the actual `RTree.bind`
recursion. The previously selected terminal set may be arbitrary. -/
theorem thresholdRemainingTree_expected_low {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (s : V) (W : ℝ)
    (levels : ℕ) (hlevels : thresholdLevels n ≤ levels) (rounds : ℕ) (U : Finset V)
    (hsU : s ∈ U) :
    expect ((thresholdRemainingTree family n s W levels rounds U).eval G.cut)
      (fun R => ((lowTargets G R s W).card : ℝ≥0∞)) ≤
        thresholdRate levels ^ rounds * ((lowTargets G U s W).card : ℝ≥0∞) := by
  induction rounds generalizing U with
  | zero => simp [thresholdRemainingTree]
  | succ rounds ih =>
    simp only [thresholdRemainingTree, RTree.eval_cast, RTree.eval_bind, expect_bind]
    calc
      _ ≤ expect ((thresholdRoundTree family n U s W n levels).eval G.cut) (fun covered =>
          thresholdRate levels ^ rounds * ((lowTargets G (U \ covered) s W).card : ℝ≥0∞)) := by
        apply expect_mono_on_support
        intro covered hc
        have hsound := thresholdRoundTree_sound family hvn hQ G U s W n levels hc
        exact ih _ (Finset.mem_sdiff.mpr ⟨hsU, fun hs => (hsound s hs).2.1 rfl⟩)
      _ = thresholdRate levels ^ rounds *
          expect ((thresholdRoundTree family n U s W n levels).eval G.cut)
            (fun covered => ((lowTargets G (U \ covered) s W).card : ℝ≥0∞)) := expect_const_mul _ _ _
      _ ≤ thresholdRate levels ^ rounds *
          (thresholdRate levels * ((lowTargets G U s W).card : ℝ≥0∞)) :=
        mul_le_mul' le_rfl (thresholdRoundTree_expected_remainder family hvn hQ G hG U s W
          levels hlevels hsU)
      _ = _ := by rw [pow_succ, mul_assoc]

theorem thresholdRemainingTree_failure_le {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (s : V) (W : ℝ)
    (levels : ℕ) (hlevels : thresholdLevels n ≤ levels) (rounds : ℕ) (U : Finset V)
    (hsU : s ∈ U) :
    mass ((thresholdRemainingTree family n s W levels rounds U).eval G.cut)
      (fun R => (lowTargets G R s W).Nonempty) ≤
        thresholdRate levels ^ rounds * ((lowTargets G U s W).card : ℝ≥0∞) := by
  have hcount := mul_mass_le_expect
    ((thresholdRemainingTree family n s W levels rounds U).eval G.cut)
    (fun R => (lowTargets G R s W).Nonempty)
    (fun R => ((lowTargets G R s W).card : ℝ≥0∞)) 1 (by
      intro R _ hR
      exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hR))
  simp only [one_mul] at hcount
  exact hcount.trans (thresholdRemainingTree_expected_low family hvn hQ G hG s W
    levels hlevels rounds U hsU)

end
end CutQueryComplexity.GHReduction
