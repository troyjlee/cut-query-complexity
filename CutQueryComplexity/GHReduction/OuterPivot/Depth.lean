import CutQueryComplexity.GHReduction.OuterPivot.Progress
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! # Conditional large-child contraction and finite fuel

The actual pivot step supplies the one-step excess contraction. A separate
conditional PMF lemma propagates such a bound through fresh adaptive steps.
Its invariant and transition remain explicit: no tree assembly, frontier, or
outer-solver correctness record is assumed. Even a self-loop consumes fuel.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.OuterPivot
noncomputable section
open scoped Classical BigOperators ENNReal
open WeightedGraph Probability

variable {V : Type} [Fintype V] [DecidableEq V]

def excess (U : Finset V) : ℕ := U.card - 1

def remaining (U : Finset V) {levels : ℕ} (output : Output V levels) : Finset V :=
  U \ output.batch.covered U

theorem remaining_subset (U : Finset V) {levels : ℕ} (output : Output V levels) :
    remaining U output ⊆ U := Finset.sdiff_subset

theorem source_mem_remaining {U : Finset V} {s : V} {values : V → Option ℝ}
    {levels : ℕ} {output : Output V levels} (hs : s ∈ U)
    (h : WellFormed U s values output.batch) : s ∈ remaining U output :=
  Finset.mem_sdiff.mpr ⟨hs, h.source_not_covered⟩

theorem remaining_accounting {U : Finset V} {s : V} {values : V → Option ℝ}
    {levels : ℕ} {output : Output V levels} (hs : s ∈ U)
    (h : WellFormed U s values output.batch) :
    excess (remaining U output) + (output.batch.covered U).card = excess U := by
  have hc := Finset.card_sdiff_add_card_eq_card (output.batch.covered_subset U)
  have hpos := Finset.card_pos.mpr ⟨s, source_mem_remaining hs h⟩
  change (remaining U output).card - 1 + (output.batch.covered U).card = U.card - 1
  change (remaining U output).card + (output.batch.covered U).card = U.card at hc
  omega

theorem step_small_child {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (read : Finset V → ℝ) {v : V}
    (hv : v ∈ (Prog.eval read (stepProgram family U s values levels seed)).batch.accepted) :
    2 * ((Prog.eval read (stepProgram family U s values levels seed)).batch.shore v ∩ U).card ≤ U.card :=
  (stepProgram_wellFormed family U s values levels seed read).small v hv

theorem pivotOutputLaw_wellFormed {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (read : Finset V → ℝ) {output : Output V levels}
    (hout : output ∈ (pivotOutputLaw family U hU values levels read).support) :
    ∃ s ∈ U, WellFormed U s (values s) output.batch := by
  rw [pivotOutputLaw] at hout
  obtain ⟨s, hs, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨seed, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact ⟨s, (PMF.mem_support_uniformOfFinset_iff _ _).mp hs,
    stepProgram_wellFormed family U s (values s) levels seed read⟩

private theorem expect_card_ne_top {α : Type} (P : PMF α) (F : α → Finset V) :
    expect P (fun a => ((F a).card : ℝ≥0∞)) ≠ ∞ := by
  have hbound : expect P (fun a => ((F a).card : ℝ≥0∞)) ≤ (Fintype.card V : ℝ≥0∞) :=
    expect_le_of_le_on_support P (fun a _ => Nat.cast_le.mpr (Finset.card_le_univ (F a)))
  exact ne_of_lt (hbound.trans_lt (by simp))

private theorem expect_excess_ne_top {α : Type} (P : PMF α) (F : α → Finset V) :
    expect P (fun a => (excess (F a) : ℝ≥0∞)) ≠ ∞ := by
  have hbound : expect P (fun a => (excess (F a) : ℝ≥0∞)) ≤ (Fintype.card V : ℝ≥0∞) := by
    apply expect_le_of_le_on_support
    intro a ha
    exact_mod_cast (Nat.sub_le (F a).card 1).trans (Finset.card_le_univ (F a))
  exact ne_of_lt (hbound.trans_lt (by simp))

theorem removalDenominator_pos (levels : ℕ) : 0 < removalDenominator levels := by
  unfold removalDenominator
  positivity

def contractionRate (levels : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - (removalDenominator levels : ℝ)⁻¹)

theorem contractionRate_arg_nonneg (levels : ℕ) :
    0 ≤ 1 - (removalDenominator levels : ℝ)⁻¹ := by
  have hK : (1 : ℝ) ≤ removalDenominator levels := by
    exact_mod_cast (Nat.succ_le_of_lt (removalDenominator_pos levels))
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hK
  simp only [one_div, inv_one] at hi
  linarith

theorem contractionRate_le_one (levels : ℕ) : contractionRate levels ≤ 1 := by
  unfold contractionRate
  apply ENNReal.ofReal_le_one.mpr
  have hi : 0 ≤ (removalDenominator levels : ℝ)⁻¹ := by positivity
  linarith

/-- The literal expected-removal target, normalized in real arithmetic. -/
theorem pivot_expected_removal_real {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels)
    (hvalues : ∀ s ∈ U, ∀ v ∈ U.erase s, values s v = some (stValue G v s)) :
    ((excess U : ℕ) : ℝ) / (32 * (levels + 1 : ℝ) ^ 2) ≤
      (expect (pivotOutputLaw family U hU values levels G.cut)
        (fun output => ((output.batch.covered U).card : ℝ≥0∞))).toReal := by
  have hfinite := expect_card_ne_top (pivotOutputLaw family U hU values levels G.cut)
    (fun output => output.batch.covered U)
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfinite)
    (pivot_expected_removal_literal family G hG U hU values levels hlevels hvalues)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at h
  have hK : (removalDenominator levels : ℝ) = 32 * (levels + 1 : ℝ) ^ 2 := by
    simp [removalDenominator]
  rw [hK] at h
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * (levels + 1 : ℝ) ^ 2)).mpr
  simpa only [excess, mul_comm] using h

/-- An actual large-child remainder contracts its terminal excess. Source
retention accounts for the subtraction of one, including a zero-removal step. -/
theorem largeChild_expected_excess {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels)
    (hvalues : ∀ s ∈ U, ∀ v ∈ U.erase s, values s v = some (stValue G v s)) :
    expect (pivotOutputLaw family U hU values levels G.cut)
      (fun output => (excess (remaining U output) : ℝ≥0∞)) ≤
        contractionRate levels * (excess U : ℝ≥0∞) := by
  let P := pivotOutputLaw family U hU values levels G.cut
  let erased := expect P (fun output => ((output.batch.covered U).card : ℝ≥0∞))
  let remain := expect P (fun output => (excess (remaining U output) : ℝ≥0∞))
  let K : ℝ≥0∞ := removalDenominator levels
  have herased : erased ≠ ∞ := expect_card_ne_top P (fun output => output.batch.covered U)
  have hremain : remain ≠ ∞ := expect_excess_ne_top P (remaining U)
  have hK : K ≠ ∞ := by simp [K]
  have hsum : remain + erased = (excess U : ℝ≥0∞) := by
    rw [show remain + erased =
      expect P (fun output => (excess (remaining U output) : ℝ≥0∞)) +
      expect P (fun output => ((output.batch.covered U).card : ℝ≥0∞)) from rfl, ← expect_add]
    calc
      _ = expect P (fun _ => (excess U : ℝ≥0∞)) := by
        apply expect_congr_on_support
        intro output hout
        obtain ⟨s, hs, hform⟩ := pivotOutputLaw_wellFormed family U hU values levels G.cut hout
        exact_mod_cast remaining_accounting hs hform
      _ = _ := expect_const _ _
  have hcharge : (excess U : ℝ≥0∞) ≤ K * erased :=
    pivot_expected_removal_literal family G hG U hU values levels hlevels hvalues
  have hlinear : K * remain + (excess U : ℝ≥0∞) ≤ K * (excess U : ℝ≥0∞) := by
    calc
      _ ≤ K * remain + K * erased := add_le_add le_rfl hcharge
      _ = _ := by rw [← mul_add, hsum]
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hK (by simp)) hlinear
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hK hremain) (by simp),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  simp only [ENNReal.toReal_natCast] at hreal
  apply (ENNReal.toReal_le_toReal hremain
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))).mp
  simp only [ENNReal.toReal_mul, contractionRate,
    ENNReal.toReal_ofReal (contractionRate_arg_nonneg levels), ENNReal.toReal_natCast]
  have hpos : (0 : ℝ) < removalDenominator levels := by
    exact_mod_cast removalDenominator_pos levels
  have hcancel : (removalDenominator levels : ℝ) *
      (1 - (removalDenominator levels : ℝ)⁻¹) = (removalDenominator levels : ℝ) - 1 := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ (ne_of_gt hpos)]
  apply (mul_le_mul_iff_right₀ hpos).mp
  rw [← mul_assoc, hcancel]
  nlinarith

/-- The public remaining-set law is semantic composition of the step. It does
not compute a source-value family: root supplies those branch correctness facts
when applying the conditional theorem below to its own execution. -/
def remainingLaw {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (read : Finset V → ℝ) : PMF (Finset V) :=
  (pivotOutputLaw family U hU values levels read).map (remaining U)

theorem remainingLaw_expected_excess {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels)
    (hvalues : ∀ s ∈ U, ∀ v ∈ U.erase s, values s v = some (stValue G v s)) :
    expect (remainingLaw family U hU values levels G.cut) (fun R => (excess R : ℝ≥0∞)) ≤
      contractionRate levels * (excess U : ℝ≥0∞) := by
  rw [remainingLaw, expect_map]
  exact largeChild_expected_excess family G hG U hU values levels hlevels hvalues

section ConditionalFuel
variable {X : Type}

/-- Exactly `fuel` conditional transitions, including transitions that return
the same state. This is a finite probability recursion, not a GH solver. -/
def fuelChain (next : X → PMF X) : ℕ → X → PMF X
  | 0, x => PMF.pure x
  | fuel + 1, x => (next x).bind (fun y => fuelChain next fuel y)

@[simp] theorem fuelChain_zero (next : X → PMF X) (x : X) :
    fuelChain next 0 x = PMF.pure x := rfl

theorem fuelChain_succ (next : X → PMF X) (fuel : ℕ) (x : X) :
    fuelChain next (fuel + 1) x = (next x).bind (fun y => fuelChain next fuel y) := rfl

/-- Empty steps are not silently retried at the same fuel. -/
theorem fuelChain_self_loop_consumes (next : X → PMF X) (fuel : ℕ) (x : X)
    (h : next x = PMF.pure x) : fuelChain next (fuel + 1) x = fuelChain next fuel x := by
  simp [fuelChain, h]

/-- Conditional drift after every valid supported history is sufficient.
No independence of previously selected states is assumed. -/
theorem fuelChain_expected_of_conditional (next : X → PMF X) (Inv : X → Prop)
    (potential : X → ℕ) (rate : ℝ≥0∞)
    (hpreserve : ∀ x, Inv x → ∀ y ∈ (next x).support, Inv y)
    (hstep : ∀ x, Inv x → expect (next x) (fun y => (potential y : ℝ≥0∞)) ≤
      rate * (potential x : ℝ≥0∞))
    (fuel : ℕ) (x : X) (hx : Inv x) :
    expect (fuelChain next fuel x) (fun y => (potential y : ℝ≥0∞)) ≤
      rate ^ fuel * (potential x : ℝ≥0∞) := by
  induction fuel generalizing x with
  | zero => simp [fuelChain]
  | succ fuel ih =>
    rw [fuelChain_succ, expect_bind]
    calc
      _ ≤ expect (next x) (fun y => rate ^ fuel * (potential y : ℝ≥0∞)) := by
        apply expect_mono_on_support
        intro y hy
        exact ih y (hpreserve x hx y hy)
      _ = rate ^ fuel * expect (next x) (fun y => (potential y : ℝ≥0∞)) :=
        expect_const_mul _ _ _
      _ ≤ rate ^ fuel * (rate * (potential x : ℝ≥0∞)) :=
        mul_le_mul_right (hstep x hx) _
      _ = _ := by rw [pow_succ, mul_assoc]

theorem fuelChain_depth_tail (next : X → PMF X) (Inv : X → Prop)
    (potential : X → ℕ) (rate : ℝ≥0∞)
    (hpreserve : ∀ x, Inv x → ∀ y ∈ (next x).support, Inv y)
    (hstep : ∀ x, Inv x → expect (next x) (fun y => (potential y : ℝ≥0∞)) ≤
      rate * (potential x : ℝ≥0∞))
    (fuel : ℕ) (x : X) (hx : Inv x) :
    mass (fuelChain next fuel x) (fun y => 0 < potential y) ≤
      rate ^ fuel * (potential x : ℝ≥0∞) := by
  have h := mul_mass_le_expect (fuelChain next fuel x) (fun y => 0 < potential y)
    (fun y => (potential y : ℝ≥0∞)) 1 (by
      intro y hy hpos
      exact_mod_cast Nat.succ_le_of_lt hpos)
  rw [one_mul] at h
  exact h.trans (fuelChain_expected_of_conditional next Inv potential rate hpreserve hstep fuel x hx)

end ConditionalFuel

/-- Exponential decay makes the public fuel logarithmic in the inverse
failure target; no inverse-probability query cutoff is used. -/
theorem contractionRate_pow_le_exp (levels fuel : ℕ) :
    contractionRate levels ^ fuel ≤
      ENNReal.ofReal (Real.exp (-(fuel : ℝ) / (removalDenominator levels : ℝ))) := by
  have hbase : 1 - (removalDenominator levels : ℝ)⁻¹ ≤
      Real.exp (-(removalDenominator levels : ℝ)⁻¹) := by
    have h := Real.add_one_le_exp (-(removalDenominator levels : ℝ)⁻¹)
    linarith
  have hpow := pow_le_pow_left₀ (contractionRate_arg_nonneg levels) hbase fuel
  have hexp : (Real.exp (-(removalDenominator levels : ℝ)⁻¹)) ^ fuel =
      Real.exp (-(fuel : ℝ) / (removalDenominator levels : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp [div_eq_mul_inv]
  rw [hexp] at hpow
  simpa only [contractionRate, ENNReal.ofReal_pow (contractionRate_arg_nonneg levels)] using
    ENNReal.ofReal_le_ofReal hpow

theorem fuelChain_exp_depth_tail {X : Type} (next : X → PMF X) (Inv : X → Prop)
    (potential : X → ℕ) (levels : ℕ)
    (hpreserve : ∀ x, Inv x → ∀ y ∈ (next x).support, Inv y)
    (hstep : ∀ x, Inv x → expect (next x) (fun y => (potential y : ℝ≥0∞)) ≤
      contractionRate levels * (potential x : ℝ≥0∞))
    (fuel : ℕ) (x : X) (hx : Inv x) :
    mass (fuelChain next fuel x) (fun y => 0 < potential y) ≤
      ENNReal.ofReal (Real.exp (-(fuel : ℝ) / (removalDenominator levels : ℝ))) *
        (potential x : ℝ≥0∞) :=
  (fuelChain_depth_tail next Inv potential (contractionRate levels) hpreserve hstep fuel x hx).trans
    (mul_le_mul_left (contractionRate_pow_le_exp levels fuel) _)

/-- Public logarithmic fuel, with `initial + 1` handling zero initial excess. -/
def depthFuel (levels initial : ℕ) (failure : ℝ) : ℕ :=
  ⌈(removalDenominator levels : ℝ) * Real.log (((initial : ℝ) + 1) / failure)⌉₊

theorem depthFuel_error_le (levels initial : ℕ) {failure : ℝ} (hf : 0 < failure) :
    Real.exp (-(depthFuel levels initial failure : ℝ) /
      (removalDenominator levels : ℝ)) * (initial : ℝ) ≤ failure := by
  have hK : (0 : ℝ) < removalDenominator levels := by
    exact_mod_cast removalDenominator_pos levels
  have hN : (0 : ℝ) < (initial : ℝ) + 1 := by positivity
  have hceil : (removalDenominator levels : ℝ) *
      Real.log (((initial : ℝ) + 1) / failure) ≤ depthFuel levels initial failure := Nat.le_ceil _
  have hlog : Real.log (((initial : ℝ) + 1) / failure) ≤
      (depthFuel levels initial failure : ℝ) / (removalDenominator levels : ℝ) := by
    apply (le_div_iff₀ hK).mpr
    simpa only [mul_comm] using hceil
  have hexp : Real.exp (-(depthFuel levels initial failure : ℝ) /
      (removalDenominator levels : ℝ)) ≤ failure / ((initial : ℝ) + 1) := by
    calc
      _ = Real.exp (-((depthFuel levels initial failure : ℝ) /
          (removalDenominator levels : ℝ))) := by rw [neg_div]
      _ ≤ Real.exp (-Real.log (((initial : ℝ) + 1) / failure)) :=
        Real.exp_le_exp.mpr (neg_le_neg hlog)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (div_pos hN hf), inv_div]
  have hfrac : (initial : ℝ) / ((initial : ℝ) + 1) ≤ 1 :=
    (div_le_iff₀ hN).mpr (by linarith)
  calc
    _ ≤ (failure / ((initial : ℝ) + 1)) * (initial : ℝ) :=
      mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg initial)
    _ = failure * ((initial : ℝ) / ((initial : ℝ) + 1)) := by ring
    _ ≤ failure := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac hf.le

theorem fuelChain_depthFuel_tail {X : Type} (next : X → PMF X) (Inv : X → Prop)
    (potential : X → ℕ) (levels : ℕ)
    (hpreserve : ∀ x, Inv x → ∀ y ∈ (next x).support, Inv y)
    (hstep : ∀ x, Inv x → expect (next x) (fun y => (potential y : ℝ≥0∞)) ≤
      contractionRate levels * (potential x : ℝ≥0∞))
    {failure : ℝ} (hf : 0 < failure) (x : X) (hx : Inv x) :
    mass (fuelChain next (depthFuel levels (potential x) failure) x)
      (fun y => 0 < potential y) ≤ ENNReal.ofReal failure := by
  apply (fuelChain_exp_depth_tail next Inv potential levels hpreserve hstep
    (depthFuel levels (potential x) failure) x hx).trans
  rw [show (potential x : ℝ≥0∞) = ENNReal.ofReal (potential x : ℝ) by simp,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (depthFuel_error_le levels (potential x) hf)

#print axioms remaining_accounting
#print axioms step_small_child
#print axioms pivot_expected_removal_real
#print axioms largeChild_expected_excess
#print axioms remainingLaw_expected_excess
#print axioms fuelChain_self_loop_consumes
#print axioms fuelChain_expected_of_conditional
#print axioms fuelChain_depth_tail
#print axioms fuelChain_exp_depth_tail
#print axioms depthFuel_error_le
#print axioms fuelChain_depthFuel_tail

end
end CutQueryComplexity.GHReduction.OuterPivot
