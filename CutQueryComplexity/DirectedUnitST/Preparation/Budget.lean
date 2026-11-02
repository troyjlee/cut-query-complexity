import CutQueryComplexity.DirectedUnitST.Preparation.Query
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Cast.Order.Field

/-! # An explicit public five-thirds preparation budget

The scale uses an executable integer cube root. The final inequality bounds
the actual program for every answer sequence; it has no graph-dependent
budget or stationarity premise.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Preparation

open Finset Acceleration

def cubicScale (n : ℕ) : ℕ := Nat.nthRoot 3 n + 1

theorem cubicScale_pos (n : ℕ) : 0 < cubicScale n := Nat.succ_pos _

theorem cubicScale_bounds (n : ℕ) :
    (n : ℝ) ^ (1 / 3 : ℝ) ≤ cubicScale n ∧
      (cubicScale n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) + 1 := by
  have hlow : (Nat.nthRoot 3 n : ℝ) ^ 3 ≤ n := by
    exact_mod_cast (Nat.pow_nthRoot_le (n := 3) (a := n) (Or.inl (by decide : 3 ≠ 0)))
  have hupp : (n : ℝ) ≤ (cubicScale n : ℝ) ^ 3 := by
    exact_mod_cast (Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) n).le
  have hroot (x : ℝ) (hx : 0 ≤ x) : (x ^ 3) ^ (1 / 3 : ℝ) = x := by
    simpa using Real.pow_rpow_inv_natCast hx (by decide : (3 : ℕ) ≠ 0)
  constructor
  · have h := Real.rpow_le_rpow (Nat.cast_nonneg n) hupp (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [hroot _ (Nat.cast_nonneg _)] at h
  · have h := Real.rpow_le_rpow (by positivity) hlow (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [hroot _ (Nat.cast_nonneg _)] at h
    simp only [cubicScale, Nat.cast_add, Nat.cast_one]
    linarith

theorem cubicScale_le_twice_root {n : ℕ} (hn : 1 ≤ n) :
    (cubicScale n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := Real.one_le_rpow hnR (by norm_num : (0 : ℝ) ≤ 1 / 3)
  linarith [(cubicScale_bounds n).2]

theorem cubicScale_le_twice {n : ℕ} (hn : 1 ≤ n) : cubicScale n ≤ 2 * n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : (n : ℝ) ^ (1 / 3 : ℝ) ≤ n := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have h : (cubicScale n : ℝ) ≤ 2 * n := by linarith [cubicScale_le_twice_root hn]
  exact_mod_cast h

theorem cubicScale_sqrt_le {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (cubicScale n) ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha1 := Real.one_le_rpow hnR (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hk := cubicScale_le_twice_root hn
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith

theorem n_mul_cuberoot {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) ^ (4 / 3 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by rw [Real.rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) + 1 / 3) := (Real.rpow_add hnR _ _).symm
    _ = _ := by norm_num

/-- Cast the rounded-up mask budget to an ordinary real expression. -/
theorem bandBudget_real {n k : ℕ} (hk : 0 < k) :
    (SparseBand.bandBudget n k : ℝ) ≤
      6 * (n : ℝ) ^ 2 / k + 2 * n * Nat.clog 2 (8 * n * k + 1) + 2 := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow n 2
  have hnum : ((6 * n.choose 2 + k - 1 : ℕ) : ℝ) ≤ 6 * (n : ℝ) ^ 2 + k := by
    have hsub : ((6 * n.choose 2 + k - 1 : ℕ) : ℝ) ≤ ((6 * n.choose 2 + k : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le (6 * n.choose 2 + k) 1
    push_cast at hsub
    linarith
  have hdiv : (((6 * n.choose 2 + k - 1) / k : ℕ) : ℝ) ≤ 6 * (n : ℝ) ^ 2 / k + 1 := by
    calc
      _ ≤ ((6 * n.choose 2 + k - 1 : ℕ) : ℝ) / k := Nat.cast_div_le
      _ ≤ (6 * (n : ℝ) ^ 2 + k) / k := div_le_div_of_nonneg_right hnum hkr.le
      _ = _ := by rw [add_div, div_self (ne_of_gt hkr)]
  simp only [SparseBand.bandBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith

theorem cubic_band_log_le {n : ℕ} (hn : 1 ≤ n) :
    Nat.clog 2 (8 * n * cubicScale n + 1) ≤ scheduleBits n := by
  dsimp only [scheduleBits]
  apply Nat.clog_mono_right
  have hk := cubicScale_le_twice hn
  have hm := Nat.mul_le_mul_left (8 * n) hk
  nlinarith

/-- The actual preparation program at the executable cubic scale. -/
noncomputable def fiveThirdsProg (n : ℕ) :
    DTree (Finset (Fin n)) ℕ (Data n) (queryBudget n (cubicScale n)) :=
  preparationProg (cubicScale_pos n)

theorem fiveThirdsProg_cost {n : ℕ} (hn : 2 ≤ n) (read : Finset (Fin n) → ℕ) :
    ((fiveThirdsProg n).cost read : ℝ) ≤
      256 * (n : ℝ) ^ (5 / 3 : ℝ) * ((scheduleBits n : ℝ) + 1) ^ 2 := by
  let a : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  let B : ℝ := (scheduleBits n : ℝ) + 1
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have ha1 : 1 ≤ a := Real.one_le_rpow hnR (by norm_num)
  have ha0 : 0 < a := by linarith
  have ha3 : a ^ 3 = n := by
    dsimp only [a]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    norm_num
  have ht : (n : ℝ) * a ^ 2 = (n : ℝ) ^ (5 / 3 : ℝ) := by
    dsimp only [a]
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((1 / 3 : ℝ) * (2 : ℕ)) := by
        rw [Real.rpow_one, Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      _ = (n : ℝ) ^ ((1 : ℝ) + (1 / 3 : ℝ) * (2 : ℕ)) :=
        (Real.rpow_add hnpos _ _).symm
      _ = _ := by norm_num
  have hB1 : 1 ≤ B := by dsimp only [B]; linarith [Nat.cast_nonneg (α := ℝ) (scheduleBits n)]
  have hBs : 1 ≤ B ^ 2 := by nlinarith only [hB1]
  have ha2 : 1 ≤ a ^ 2 := by nlinarith only [ha1]
  have hk0 : (0 : ℝ) < cubicScale n := by exact_mod_cast cubicScale_pos n
  have hklo : a ≤ cubicScale n := (cubicScale_bounds n).1
  have hkhi : (cubicScale n : ℝ) ≤ 2 * a := cubicScale_le_twice_root hn1
  have hsqrt : Real.sqrt ((n : ℝ) * cubicScale n) ≤ 2 * a ^ 2 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    calc
      (n : ℝ) * cubicScale n ≤ n * (2 * a) :=
        mul_le_mul_of_nonneg_left hkhi (Nat.cast_nonneg n)
      _ = 2 * (a ^ 2) ^ 2 := by rw [← ha3]; ring
      _ ≤ (2 * a ^ 2) ^ 2 := by nlinarith only [sq_nonneg (a ^ 2)]
  have hfrac : 6 * (n : ℝ) ^ 2 / cubicScale n ≤ 6 * n * a ^ 2 := by
    apply (div_le_iff₀ hk0).mpr
    calc
      6 * (n : ℝ) ^ 2 = (6 * n * a ^ 2) * a := by rw [← ha3]; ring
      _ ≤ (6 * n * a ^ 2) * cubicScale n :=
        mul_le_mul_of_nonneg_left hklo (by positivity)
  have hlog : (Nat.clog 2 (8 * n * cubicScale n + 1) : ℝ) ≤ B := by
    have hh : (Nat.clog 2 (8 * n * cubicScale n + 1) : ℝ) ≤ scheduleBits n := by
      exact_mod_cast cubic_band_log_le hn1
    dsimp only [B]
    linarith
  have hband : (SparseBand.bandBudget n (cubicScale n) : ℝ) ≤ 10 * n * a ^ 2 * B ^ 2 := by
    have hraw := bandBudget_real (n := n) (cubicScale_pos n)
    have hlog' := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * (n : ℝ) by positivity)
    have hterm1 : 6 * (n : ℝ) * a ^ 2 ≤ 6 * n * a ^ 2 * B ^ 2 :=
      le_mul_of_one_le_right (by positivity) hBs
    have hterm2 : 2 * (n : ℝ) * B ≤ 2 * n * a ^ 2 * B ^ 2 := by
      have hBb : B ≤ B ^ 2 := by nlinarith only [hB1]
      calc
        _ ≤ 2 * (n : ℝ) * B ^ 2 := mul_le_mul_of_nonneg_left hBb (by positivity)
        _ ≤ _ := by
          have hm := mul_le_mul_of_nonneg_left ha2
            (show 0 ≤ 2 * (n : ℝ) * B ^ 2 by positivity)
          nlinarith only [hm]
    have hterm3 : (2 : ℝ) ≤ 2 * n * a ^ 2 * B ^ 2 := by
      have hprod : 1 ≤ (n : ℝ) * a ^ 2 * B ^ 2 :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hnR ha2) hBs
      linarith
    calc
      _ ≤ 6 * (n : ℝ) ^ 2 / cubicScale n +
          2 * n * Nat.clog 2 (8 * n * cubicScale n + 1) + 2 := hraw
      _ ≤ 6 * n * a ^ 2 + 2 * n * B + 2 :=
        add_le_add (add_le_add hfrac hlog') le_rfl
      _ ≤ 6 * n * a ^ 2 * B ^ 2 + 2 * n * a ^ 2 * B ^ 2 +
          2 * n * a ^ 2 * B ^ 2 := add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = _ := by ring
  have hmain : 60 * (n : ℝ) * (Real.sqrt ((n : ℝ) * cubicScale n) + 1) * B ^ 2 ≤
      180 * n * a ^ 2 * B ^ 2 := by
    have hsmall : Real.sqrt ((n : ℝ) * cubicScale n) + 1 ≤ 3 * a ^ 2 := by linarith
    calc
      _ ≤ 60 * (n : ℝ) * (3 * a ^ 2) * B ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall (by positivity)) (sq_nonneg B)
      _ = _ := by ring
  have hc := preparationProg_cost_sqrt hn (cubicScale_pos n) read
  change ((fiveThirdsProg n).cost read : ℝ) ≤ _ at hc
  change ((fiveThirdsProg n).cost read : ℝ) ≤ 256 * (n : ℝ) ^ (5 / 3 : ℝ) * B ^ 2
  rw [← ht]
  change ((fiveThirdsProg n).cost read : ℝ) ≤
    n + (60 * n * (Real.sqrt ((n : ℝ) * cubicScale n) + 1) * B ^ 2 +
      3 * SparseBand.bandBudget n (cubicScale n)) at hc
  have hunit := mul_le_mul_of_nonneg_left
    (one_le_mul_of_one_le_of_one_le ha2 hBs) (Nat.cast_nonneg (α := ℝ) n)
  have hnonneg : 0 ≤ (n : ℝ) * a ^ 2 * B ^ 2 := by positivity
  nlinarith only [hc, hband, hmain, hunit, hnonneg]

#print axioms cubicScale_bounds
#print axioms bandBudget_real
#print axioms fiveThirdsProg_cost

end CutQueryComplexity.DirectedUnitST.Preparation
