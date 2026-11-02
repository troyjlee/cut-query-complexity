import CutQueryComplexity.DirectedUnitST.SparseBand.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! # Finite counting for a public sparse-band certificate

The exponential moment is a finite distributivity identity. No probabilistic
oracle or graph-dependent seed is supplied to the existence theorem.

For one grid difference, at most five of the `2*k+1` offsets are active. The
exponential sum over tables factors over canonical pairs, with normalized bound
`exp (6 * (n.choose 2) / k)`. There are `(8*n*k+1)^n` grid potentials. The public
budget makes the sum of these bounds strictly less than `exp bandBudget`.
If every table failed a grid check, each table would contribute at least that
much to the total sum, a contradiction.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.SparseBand

open Finset

theorem offsetInt_injective {k : ℕ} : Function.Injective (@offsetInt k) := by
  intro a b hab
  apply Fin.ext
  dsimp [offsetInt] at hab
  omega

/-- An expanded band contains at most five choices from the integer offset grid. -/
theorem offset_band_card_le_five (k : ℕ) (d : ℤ) :
    (univ.filter (fun a : Offset k => |d - 4 * offsetInt a| ≤ 8)).card ≤ 5 := by
  let s := univ.filter (fun a : Offset k => |d - 4 * offsetInt a| ≤ 8)
  have hs : s.image offsetInt ⊆ Icc (d / 4 - 2) (d / 4 + 2) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
    have ha' := abs_le.mp (mem_filter.mp ha).2
    apply mem_Icc.mpr
    constructor <;> omega
  calc
    s.card = (s.image offsetInt).card :=
      (Finset.card_image_of_injective s offsetInt_injective).symm
    _ ≤ (Icc (d / 4 - 2) (d / 4 + 2)).card := card_le_card hs
    _ = 5 := by
      rw [Int.card_Icc]
      have hcalc : d / 4 + 2 + 1 - (d / 4 - 2) = 5 := by omega
      rw [hcalc]
      rfl

/-- Exact one-coordinate exponential sum; the active subset is counted once. -/
theorem sum_exp_indicator {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] :
    (∑ a : A, Real.exp (if P a then 1 else 0)) =
      Fintype.card A + ((univ.filter P).card : ℝ) * (Real.exp 1 - 1) := by
  have h (a : A) : Real.exp (if P a then 1 else 0) =
      1 + if P a then Real.exp 1 - 1 else 0 := by
    by_cases ha : P a
    · simp only [ha, ↓reduceIte]
      ring
    · simp [ha]
  simp_rw [h]
  rw [sum_add_distrib]
  simp [sum_ite]
  ring

-- Elaborating finite function spaces exceeded the default heartbeat budget.
set_option maxHeartbeats 600000 in
/-- Finite independence is just the product-of-sums identity. -/
theorem finite_exp_moment {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (P : I → A → Prop) [∀ i, DecidablePred (P i)] (b : ℝ)
    (h : ∀ i, (∑ a : A, Real.exp (if P i a then 1 else 0)) ≤
      (Fintype.card A : ℝ) * Real.exp b) :
    (∑ c : I → A, Real.exp ((univ.filter (fun i => P i (c i))).card : ℝ)) ≤
      (Fintype.card (I → A) : ℝ) * Real.exp ((Fintype.card I : ℝ) * b) := by
  calc
    _ = ∑ c : I → A, ∏ i : I, Real.exp (if P i (c i) then 1 else 0) := by
      apply sum_congr rfl
      intro c hc
      rw [← Real.exp_sum]
      congr 1
      simp
    _ = ∏ i : I, ∑ a : A, Real.exp (if P i a then 1 else 0) :=
      (Fintype.prod_sum (fun (i : I) (a : A) => Real.exp (if P i a then 1 else 0))).symm
    _ ≤ ∏ _i : I, (Fintype.card A : ℝ) * Real.exp b := by
      apply prod_le_prod₀
      · intro i hi
        exact sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      · intro i hi
        exact h i
    _ = _ := by simp [Real.exp_nat_mul, mul_pow]

theorem single_band_exp_bound {k : ℕ} (hk : 0 < k) (d : ℤ) :
    (∑ a : Offset k, Real.exp (if |d - 4 * offsetInt a| ≤ 8 then 1 else 0)) ≤
      ((2 * k + 1 : ℕ) : ℝ) * Real.exp (6 / (k : ℝ)) := by
  have hcard : ((univ.filter (fun a : Offset k =>
      |d - 4 * offsetInt a| ≤ 8)).card : ℝ) ≤ 5 := by
    exact_mod_cast offset_band_card_le_five k d
  have hcard₀ : (0 : ℝ) ≤ (univ.filter (fun a : Offset k =>
      |d - 4 * offsetInt a| ≤ 8)).card := Nat.cast_nonneg _
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have he : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_three]
  have hmul := mul_le_mul_of_nonneg_left he hcard₀
  have hten := mul_le_mul_of_nonneg_right hcard (by norm_num : (0 : ℝ) ≤ 2)
  rw [sum_exp_indicator (fun a : Offset k => |d - 4 * offsetInt a| ≤ 8)]
  have hfirst : ((2 * k + 1 : ℕ) : ℝ) + 10 ≤
      ((2 * k + 1 : ℕ) : ℝ) * (1 + 6 / (k : ℝ)) := by
    have hk6 : (6 / (k : ℝ)) * k = 6 := div_mul_cancel₀ 6 (ne_of_gt hkR)
    have hdiv₀ : (0 : ℝ) ≤ 6 / k := by positivity
    push_cast
    nlinarith
  calc
    _ ≤ ((2 * k + 1 : ℕ) : ℝ) + 10 := by
      simp only [Fintype.card_fin]
      linarith
    _ ≤ ((2 * k + 1 : ℕ) : ℝ) * (1 + 6 / (k : ℝ)) := hfirst
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (6 / (k : ℝ))])
      (Nat.cast_nonneg _)

theorem grid_exp_moment {n k : ℕ} (hk : 0 < k) (g : GridPoint n k) :
    (∑ c : OffsetTable n k, Real.exp ((gridActivePairs c g).card : ℝ)) ≤
      (Fintype.card (OffsetTable n k) : ℝ) *
        Real.exp ((n.choose 2 : ℝ) * (6 / (k : ℝ))) := by
  have hset (c : OffsetTable n k) : gridActivePairs c g =
      univ.filter (fun e : Pair n =>
        |(g e.val.1 : ℤ) - (g e.val.2 : ℤ) - 4 * offsetInt (c e)| ≤ 8) := by
    ext e
    simp only [gridActivePairs, mem_filter, mem_univ, true_and, GridActive]
  simp_rw [hset]
  simpa only [card_pair] using
    finite_exp_moment (I := Pair n) (A := Offset k)
      (fun e a => |(g e.val.1 : ℤ) - (g e.val.2 : ℤ) - 4 * offsetInt a| ≤ 8)
      (6 / (k : ℝ)) (fun e => by
        simpa only [Fintype.card_fin] using
          single_band_exp_bound hk ((g e.val.1 : ℤ) - (g e.val.2 : ℤ)))

theorem nat_ceil_div_bound (a k : ℕ) (hk : 0 < k) :
    (a : ℝ) / k ≤ ((a + k - 1) / k : ℕ) := by
  have hdiv := Nat.div_add_mod (a + k - 1) k
  have hmod := Nat.mod_lt (a + k - 1) hk
  have hsub : a + k - 1 + 1 = a + k := Nat.sub_add_cancel (by omega)
  have hmul : a ≤ k * ((a + k - 1) / k) := by omega
  have hmul' : a ≤ ((a + k - 1) / k) * k := by simpa [Nat.mul_comm] using hmul
  apply (div_le_iff₀ (Nat.cast_pos.mpr hk)).mpr
  exact_mod_cast hmul'

theorem log_le_clog (a : ℕ) (ha : 0 < a) : Real.log (a : ℝ) ≤ Nat.clog 2 a := by
  have hp : (a : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 a := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) a
  have hl := Real.log_le_log (Nat.cast_pos.mpr ha) hp
  rw [Real.log_pow] at hl
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_left htwo
    (Nat.cast_nonneg (Nat.clog 2 a) : (0 : ℝ) ≤ Nat.clog 2 a)
  exact hl.trans (by simpa only [mul_one] using hmul)

theorem grid_count_exp_lt_budget {n k : ℕ} (hk : 0 < k) :
    (Fintype.card (GridPoint n k) : ℝ) *
      Real.exp ((n.choose 2 : ℝ) * (6 / (k : ℝ))) < Real.exp (bandBudget n k : ℝ) := by
  have hbase : (0 : ℝ) < (8 * n * k + 1 : ℕ) := by positivity
  have hlog := log_le_clog (8 * n * k + 1) (by omega)
  have hceil := nat_ceil_div_bound (6 * (n.choose 2)) k hk
  have hceil' : (n.choose 2 : ℝ) * (6 / (k : ℝ)) ≤
      ((6 * (n.choose 2) + k - 1) / k : ℕ) := by
    calc
      _ = ((6 * (n.choose 2) : ℕ) : ℝ) / k := by push_cast; ring
      _ ≤ _ := hceil
  have hnonneg : (0 : ℝ) ≤ n * Nat.clog 2 (8 * n * k + 1) := by positivity
  have hlogn := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)
  have hpow : (((8 * n * k + 1 : ℕ) : ℝ) ^ n) =
      Real.exp ((n : ℝ) * Real.log ((8 * n * k + 1 : ℕ) : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hbase]
  rw [show Fintype.card (GridPoint n k) = (8 * n * k + 1) ^ n by
    simp [GridPoint], Nat.cast_pow, hpow, ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  dsimp [bandBudget]
  push_cast at hlogn ⊢
  nlinarith only [hceil', hlogn, hnonneg]

-- Both nested finite function spaces occur in the same double-sum argument.
set_option maxHeartbeats 600000 in
/-- Some finite offset table passes every finite grid check. This theorem has
no sparse-band, concentration, graph, or seed hypothesis. -/
theorem exists_gridAccept (n k : ℕ) (hk : 0 < k) :
    ∃ c : OffsetTable n k, GridAccept c := by
  let W (c : OffsetTable n k) : ℝ :=
    ∑ g : GridPoint n k, Real.exp ((gridActivePairs c g).card : ℝ)
  have htotal : (∑ c : OffsetTable n k, W c) <
      (Fintype.card (OffsetTable n k) : ℝ) * Real.exp (bandBudget n k : ℝ) := by
    calc
      _ = ∑ g : GridPoint n k, ∑ c : OffsetTable n k,
          Real.exp ((gridActivePairs c g).card : ℝ) := sum_comm
      _ ≤ ∑ _g : GridPoint n k, (Fintype.card (OffsetTable n k) : ℝ) *
          Real.exp ((n.choose 2 : ℝ) * (6 / (k : ℝ))) :=
        sum_le_sum (fun g hg => grid_exp_moment hk g)
      _ = (Fintype.card (OffsetTable n k) : ℝ) *
          ((Fintype.card (GridPoint n k) : ℝ) *
            Real.exp ((n.choose 2 : ℝ) * (6 / (k : ℝ)))) := by
        simp only [sum_const, nsmul_eq_mul, card_univ]
        ring
      _ < _ := mul_lt_mul_of_pos_left (grid_count_exp_lt_budget hk) (by
        let : Nonempty (OffsetTable n k) := ⟨fun _ => ⟨0, by omega⟩⟩
        exact Nat.cast_pos.mpr Fintype.card_pos)
  by_contra hnone
  have hlower : (Fintype.card (OffsetTable n k) : ℝ) * Real.exp (bandBudget n k : ℝ) ≤
      ∑ c : OffsetTable n k, W c := by
    calc
      _ = ∑ _c : OffsetTable n k, Real.exp (bandBudget n k : ℝ) := by
        simp only [sum_const, nsmul_eq_mul, card_univ]
      _ ≤ ∑ c : OffsetTable n k, W c := by
        apply sum_le_sum
        intro c hc
        have hbad : ¬GridAccept c := fun h => hnone ⟨c, h⟩
        obtain ⟨g, hg⟩ : ∃ g : GridPoint n k, bandBudget n k < (gridActivePairs c g).card := by
          simpa [GridAccept, not_forall, not_le] using hbad
        have hcomp : Real.exp (bandBudget n k : ℝ) ≤
            Real.exp ((gridActivePairs c g).card : ℝ) :=
          Real.exp_le_exp.mpr (by exact_mod_cast hg.le)
        refine hcomp.trans ?_
        dsimp only [W]
        exact single_le_sum
          (f := fun x : GridPoint n k => Real.exp ((gridActivePairs c x).card : ℝ))
          (fun _ _ => (Real.exp_pos _).le) (mem_univ g)
  linarith

#print axioms offset_band_card_le_five
#print axioms finite_exp_moment
#print axioms exists_gridAccept

end CutQueryComplexity.DirectedUnitST.SparseBand
