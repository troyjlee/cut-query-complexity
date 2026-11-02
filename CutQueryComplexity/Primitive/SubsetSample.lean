import CutQueryComplexity.Probability.WeightedChoice
import CutQueryComplexity.Primitive.BinarySearch

/-! # Exact logarithmic sampling from a nonnegative subset-sum oracle -/
namespace CutQueryComplexity
noncomputable section
open scoped Classical NNReal ENNReal
open Probability
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V : Type} [DecidableEq V]

/-- Interpret a valid subset sum as a nonnegative mass. Invalid answers are clipped. -/
def sampleMass (w : V → ℝ) (U : Finset V) : ℝ≥0 := (subsetSum w U).toNNReal

theorem sampleMass_split (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (m : ℕ) (U : Finset V) :
    sampleMass w (Split.left m U) + sampleMass w (U \ Split.left m U) = sampleMass w U := by
  apply NNReal.coe_injective
  have hn (A : Finset V) : 0 ≤ subsetSum w A := Finset.sum_nonneg (fun v _ => hw v)
  simp only [NNReal.coe_add, sampleMass]
  rw [Real.coe_toNNReal _ (hn _), Real.coe_toNNReal _ (hn _), Real.coe_toNNReal _ (hn _)]
  exact Split.sum_split w m U

/-- Leaf mass at a specified possible output. Absence carries no positive mass. -/
def outputMass (w : V → ℝ) (U : Finset V) : Option V → ℝ≥0∞
  | none => 0
  | some v => if v ∈ U then ENNReal.ofReal (w v) else 0

theorem outputMass_split (w : V → ℝ) (m : ℕ) (U : Finset V) (o : Option V) :
    outputMass w (Split.left m U) o + outputMass w (U \ Split.left m U) o = outputMass w U o := by
  cases o with
  | none => simp [outputMass]
  | some v =>
      have h := Split.left_subset m U
      by_cases hl : v ∈ Split.left m U
      · simp [outputMass, hl, h hl]
      · by_cases hv : v ∈ U <;> simp [outputMass, hv, hl]

/-- Two subset queries per level, followed by a mass-proportional random branch. -/
def samplePositive : (k : ℕ) → Finset V → RTree (Finset V) ℝ (Option V) (2 * k)
  | 0, U => RTree.pure (PMF.pure U.toList.head?)
  | k + 1, U =>
      (RTree.query (Split.left (2 ^ k) U) fun l =>
        RTree.query (U \ Split.left (2 ^ k) U) fun r =>
          RTree.mix ((chooseWeight l.toNNReal r.toNNReal).map fun b =>
            if b then samplePositive k (Split.left (2 ^ k) U)
            else samplePositive k (U \ Split.left (2 ^ k) U))).cast (by omega)

/-- The exact unnormalized law makes zero-mass recursive calls harmless. -/
theorem samplePositive_scaled (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (k : ℕ) (U : Finset V)
    (hcard : U.card ≤ 2 ^ k) (o : Option V) :
    (sampleMass w U : ℝ≥0∞) * ((samplePositive k U).eval (subsetSum w)) o = outputMass w U o := by
  induction k generalizing U with
  | zero =>
      by_cases he : U = ∅
      · subst U; cases o <;> simp [samplePositive, sampleMass, subsetSum, outputMass]
      · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
        have hU : U = {v} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hv, fun u hu => (Finset.card_le_one.mp (by simpa using hcard)) u hu v hv⟩
        subst U
        cases o with
        | none => simp [samplePositive, sampleMass, subsetSum, outputMass]
        | some u =>
            by_cases hu : u = v
            · subst u; simp [samplePositive, sampleMass, subsetSum, outputMass, PMF.pure_apply, ENNReal.ofReal]
            · simp [samplePositive, sampleMass, subsetSum, outputMass, hu, Ne.symm hu,
                PMF.pure_apply, ENNReal.ofReal]
  | succ k ih =>
      have hr : (U \ Split.left (2 ^ k) U).card ≤ 2 ^ k :=
        Split.card_right_le (by simpa [pow_succ, Nat.mul_comm] using hcard)
      simp only [samplePositive, RTree.eval_cast, RTree.eval_query, RTree.eval_mix,
        PMF.bind_map, Function.comp_def]
      have he : (fun b : Bool =>
          (if b then samplePositive k (Split.left (2 ^ k) U)
            else samplePositive k (U \ Split.left (2 ^ k) U)).eval (subsetSum w)) =
          (fun b => if b then (samplePositive k (Split.left (2 ^ k) U)).eval (subsetSum w)
            else (samplePositive k (U \ Split.left (2 ^ k) U)).eval (subsetSum w)) := by
        funext b; cases b <;> rfl
      rw [he]
      change (sampleMass w U : ℝ≥0∞) *
        ((chooseWeight (sampleMass w (Split.left (2 ^ k) U))
          (sampleMass w (U \ Split.left (2 ^ k) U))).bind
            (fun b => if b then _ else _)) o = _
      rw [← sampleMass_split w hw (2 ^ k) U, chooseWeight_bind_scaled,
        ih _ (Split.card_left_le _ _), ih _ hr, outputMass_split]

/-- Zero total weight returns `none`; otherwise sample in `2*k+1` subset queries. -/
def sampleSubset (k : ℕ) (U : Finset V) : RTree (Finset V) ℝ (Option V) (2 * k + 1) :=
  RTree.query U fun total =>
    if 0 < total then samplePositive k U else RTree.pure (PMF.pure none)

/-- All-zero candidate sets are detected exactly. -/
theorem sampleSubset_zero (w : V → ℝ) (k : ℕ) (U : Finset V)
    (hz : subsetSum w U = 0) :
    (sampleSubset k U).eval (subsetSum w) = PMF.pure none := by
  simp [sampleSubset, hz]

/-- Unnormalized sampling law, valid even when the total weight is zero. -/
theorem sampleSubset_scaled (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (k : ℕ) (U : Finset V)
    (hcard : U.card ≤ 2 ^ k) (o : Option V) :
    ENNReal.ofReal (subsetSum w U) * ((sampleSubset k U).eval (subsetSum w)) o =
      outputMass w U o := by
  by_cases hp : 0 < subsetSum w U
  · simpa only [sampleSubset, RTree.eval_query, ite_eq_left hp, sampleMass, ENNReal.ofReal] using
      samplePositive_scaled w hw k U hcard o
  · have hz : subsetSum w U = 0 := le_antisymm (le_of_not_gt hp)
        (Finset.sum_nonneg (fun v _ => hw v))
    have hweights := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hw v)).mp hz
    cases o with
    | none => simp [hz, outputMass]
    | some v => by_cases hv : v ∈ U <;> simp [hz, outputMass, hv, hweights]

/-- Every outcome has exactly its weight divided by the total; `none` has probability zero. -/
theorem sampleSubset_law (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (k : ℕ) (U : Finset V)
    (hcard : U.card ≤ 2 ^ k) (hpos : 0 < subsetSum w U) (o : Option V) :
    ((sampleSubset k U).eval (subsetSum w)) o =
      outputMass w U o / ENNReal.ofReal (subsetSum w U) := by
  have h := samplePositive_scaled w hw k U hcard o
  have hn : ENNReal.ofReal (subsetSum w U) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  simp only [sampleSubset, RTree.eval_query, if_pos hpos]
  change ENNReal.ofReal (subsetSum w U) * _ = _ at h
  apply (ENNReal.mul_right_inj hn ENNReal.ofReal_ne_top).mp
  rw [h, div_eq_mul_inv, mul_left_comm,
    ENNReal.mul_inv_cancel hn ENNReal.ofReal_ne_top, mul_one]

end
end CutQueryComplexity
