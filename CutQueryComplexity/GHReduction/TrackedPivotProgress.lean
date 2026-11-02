import CutQueryComplexity.GHReduction.SourcePivotProgress
import CutQueryComplexity.GHReduction.BlockRefinement

/-! # Progress for the child containing any tracked vertex

Residual-child progress alone does not bound the depth of a vertex that moves
into a small child. The public selected cell below identifies either case.
Its excess is bounded by the average of the residual and parent excesses.
This transfers the actual source-pivot progress bound to every tracked vertex
without conditioning its pivot on future success. Failed source computations
kill only the analysis potential and are charged separately as failures.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability OuterPivot

variable {V : Type} [Fintype V] [DecidableEq V]

def trackedPivotChild (U : Finset V) {levels : ℕ} (out : Output V levels) (v : V) : Finset V :=
  match refinementCell out.batch.accepted out.batch.shore v with
  | none => remaining U out
  | some i => out.batch.shore i.val ∩ U

theorem trackedPivotChild_subset (U : Finset V) {levels : ℕ} (out : Output V levels) (v : V) :
    trackedPivotChild U out v ⊆ U := by
  unfold trackedPivotChild
  split
  · exact remaining_subset U out
  · exact Finset.inter_subset_right

theorem trackedPivotChild_excess_le (U : Finset V) {levels : ℕ} (out : Output V levels) (v : V) :
    excess (trackedPivotChild U out v) ≤ excess U :=
  Nat.sub_le_sub_right (Finset.card_le_card (trackedPivotChild_subset U out v)) 1

/-- This deterministic inequality treats both possible child kinds. -/
theorem trackedPivotChild_residual_bound (U : Finset V) (s : V) (values : V → Option ℝ)
    {levels : ℕ} (out : Output V levels) (hform : WellFormed U s values out.batch) (v : V) :
    2 * excess (trackedPivotChild U out v) ≤ excess (remaining U out) + excess U := by
  cases hcell : refinementCell out.batch.accepted out.batch.shore v with
  | none =>
      have hle : excess (remaining U out) ≤ excess U :=
        Nat.sub_le_sub_right (Finset.card_le_card (remaining_subset U out)) 1
      simp only [trackedPivotChild, hcell]
      omega
  | some i =>
      have hsmall := hform.small i.val i.property
      simp only [trackedPivotChild, hcell, excess]
      omega

/-- The same finite cell used by the public partition update. -/
theorem mem_trackedPivotChild (U : Finset V) (s : V) (values : V → Option ℝ)
    {levels : ℕ} (out : Output V levels) (hform : WellFormed U s values out.batch)
    (v x : V) : x ∈ trackedPivotChild U out v ↔
      x ∈ U ∧ refinementCell out.batch.accepted out.batch.shore x =
        refinementCell out.batch.accepted out.batch.shore v := by
  have hdisj : ∀ i ∈ out.batch.accepted, ∀ j ∈ out.batch.accepted,
      i ≠ j → Disjoint (out.batch.shore i) (out.batch.shore j) :=
    fun i hi j hj hij => hform.disjoint hi hj hij
  cases hcell : refinementCell out.batch.accepted out.batch.shore v with
  | none =>
      simp only [trackedPivotChild, hcell, remaining, Finset.mem_sdiff,
        refinementCell_eq_none, Batch.mem_covered, not_exists, not_and]
      constructor
      · rintro ⟨hxU, hx⟩
        exact ⟨hxU, fun i hi hxi => hx i hi (Finset.mem_inter.mpr ⟨hxi, hxU⟩)⟩
      · rintro ⟨hxU, hx⟩
        exact ⟨hxU, fun i hi hxi => hx i hi (Finset.mem_inter.mp hxi).1⟩
  | some i =>
      simp only [trackedPivotChild, hcell, Finset.mem_inter,
        refinementCell_eq_some _ _ hdisj, and_comm]

def trackedPivotPotential (G : WeightedGraph V) (U : Finset V) (v : V) {levels : ℕ}
    (out : SourcePivotOutput V levels) : ℕ :=
  if SourceValuesSuccess G U out.pivot out.values then excess (trackedPivotChild U out.step v) else 0

theorem trackedPivotPotential_le (G : WeightedGraph V) (U : Finset V) (v : V)
    {levels : ℕ} (out : SourcePivotOutput V levels) : trackedPivotPotential G U v out ≤ excess U := by
  unfold trackedPivotPotential
  split
  · exact trackedPivotChild_excess_le U out.step v
  · exact Nat.zero_le _

theorem trackedPivotPotential_of_good (G : WeightedGraph V) (U : Finset V) (v : V)
    {levels : ℕ} (out : SourcePivotOutput V levels) (hgood : SourcePivotGood G U out) :
    trackedPivotPotential G U v out = excess (trackedPivotChild U out.step v) := by
  rw [trackedPivotPotential, if_pos hgood.2.1]

theorem sourcePivotTree_tracked_residual_bound {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G K : WeightedGraph V) (U : Finset V) (hU : U.Nonempty) (v : V)
    (samples trials guideLevels scale exponent levels : ℕ) :
    2 * expect ((sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn).eval G.cut)
      (fun out => (trackedPivotPotential G U v out : ℝ≥0∞)) ≤
    expect ((sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn).eval G.cut)
      (fun out => (sourcePivotPotential G U out : ℝ≥0∞)) + (excess U : ℝ≥0∞) := by
  let P := (sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn).eval G.cut
  calc
    _ = expect P (fun out => 2 * (trackedPivotPotential G U v out : ℝ≥0∞)) :=
      (expect_const_mul P 2 _).symm
    _ ≤ expect P (fun out => (sourcePivotPotential G U out : ℝ≥0∞) + (excess U : ℝ≥0∞)) := by
      apply expect_mono_on_support
      intro out hout
      by_cases hvalues : SourceValuesSuccess G U out.pivot out.values
      · have hs := sourcePivotTree_support family n samples trials guideLevels scale exponent levels
          K U hU hvn G.cut hout
        have hgood := sourcePivot_good_of_values family hvn hQ G U out.pivot hs.1
          out.values levels hvalues hs.2.2
        rw [trackedPivotPotential, if_pos hvalues, sourcePivotPotential, if_pos hvalues]
        exact_mod_cast trackedPivotChild_residual_bound U out.pivot out.values out.step hgood.2.2.1 v
      · simp only [trackedPivotPotential, if_neg hvalues, Nat.cast_zero, mul_zero]
        exact zero_le
    _ = _ := by rw [expect_add, expect_const]

/-- Every tracked child has the same depth contraction rate, including a
vertex that leaves the residual child at this very step. -/
theorem sourcePivotTree_expected_tracked_potential {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (hU : U.Nonempty) (v : V)
    (samples trials guideLevels scale exponent levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels) :
    expect ((sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn).eval G.cut)
      (fun out => (trackedPivotPotential G U v out : ℝ≥0∞)) ≤
        contractionRate levels * (excess U : ℝ≥0∞) := by
  let P := (sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn).eval G.cut
  let r := expect P (fun out => (sourcePivotPotential G U out : ℝ≥0∞))
  let c := expect P (fun out => (trackedPivotPotential G U v out : ℝ≥0∞))
  have hrle : r ≤ (excess U : ℝ≥0∞) := expect_le_of_le_on_support P (fun out _ =>
    (Nat.cast_le (α := ℝ≥0∞)).mpr (sourcePivotPotential_le G U out))
  have hcle : c ≤ (excess U : ℝ≥0∞) := expect_le_of_le_on_support P (fun out _ =>
    (Nat.cast_le (α := ℝ≥0∞)).mpr (trackedPivotPotential_le G U v out))
  have hr : r ≠ ∞ := ne_of_lt (hrle.trans_lt (by simp))
  have hc : c ≠ ∞ := ne_of_lt (hcle.trans_lt (by simp))
  have hres := sourcePivotTree_potential_charge family hvn hQ G K hG U hU
    samples trials guideLevels scale exponent levels hlevels
  have hchild := sourcePivotTree_tracked_residual_bound family hvn hQ G K U hU v
    samples trials guideLevels scale exponent levels
  have hK : ((16 * (levels + 1) : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  change ((16 * (levels + 1) : ℕ) : ℝ≥0∞) * r + (excess U : ℝ≥0∞) ≤
    ((16 * (levels + 1) : ℕ) : ℝ≥0∞) * (excess U : ℝ≥0∞) at hres
  change 2 * c ≤ r + (excess U : ℝ≥0∞) at hchild
  have hresReal := ENNReal.toReal_mono (ENNReal.mul_ne_top hK (by simp)) hres
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hK hr) (by simp)] at hresReal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hresReal
  have hchildReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hr, by simp⟩) hchild
  rw [ENNReal.toReal_add hr (by simp)] at hchildReal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast] at hchildReal
  change 2 * c.toReal ≤ r.toReal + (excess U : ℝ) at hchildReal
  change ((16 * (levels + 1) : ℕ) : ℝ) * r.toReal + (excess U : ℝ) ≤
    ((16 * (levels + 1) : ℕ) : ℝ) * (excess U : ℝ) at hresReal
  have hcleReal := ENNReal.toReal_mono (by simp) hcle
  simp only [ENNReal.toReal_natCast] at hcleReal
  have hden : (32 * (levels + 1) : ℕ) ≤ removalDenominator levels := by
    unfold removalDenominator
    nlinarith [Nat.zero_le levels]
  have hdenReal : ((32 * (levels + 1) : ℕ) : ℝ) ≤ (removalDenominator levels : ℝ) := by
    exact_mod_cast hden
  have hscaledChild := mul_le_mul_of_nonneg_left hchildReal
    (by positivity : (0 : ℝ) ≤ ((16 * (levels + 1) : ℕ) : ℝ))
  have hsmallCharge : ((32 * (levels + 1) : ℕ) : ℝ) * c.toReal + (excess U : ℝ) ≤
      ((32 * (levels + 1) : ℕ) : ℝ) * (excess U : ℝ) := by
    push_cast at hresReal hscaledChild ⊢
    nlinarith
  have hcharge : (removalDenominator levels : ℝ) * c.toReal + (excess U : ℝ) ≤
      (removalDenominator levels : ℝ) * (excess U : ℝ) := by
    have hslack := mul_nonneg (sub_nonneg.mpr hdenReal) (sub_nonneg.mpr hcleReal)
    nlinarith
  apply (ENNReal.toReal_le_toReal hc
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))).mp
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (contractionRate_arg_nonneg levels), ENNReal.toReal_natCast]
  have hpos : (0 : ℝ) < removalDenominator levels := by exact_mod_cast removalDenominator_pos levels
  have hcancel : (removalDenominator levels : ℝ) *
      (1 - (removalDenominator levels : ℝ)⁻¹) = (removalDenominator levels : ℝ) - 1 := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ (ne_of_gt hpos)]
  apply (mul_le_mul_iff_of_pos_left hpos).mp
  rw [← mul_assoc, hcancel]
  nlinarith

end
end CutQueryComplexity.GHReduction
