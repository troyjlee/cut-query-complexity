import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Public supply guards and final directed unit query arithmetic

This module has no dependency on the unfinished operational program. Its
repair formula is the literal numerical expression used by Blocking; the
adapter to that implementation belongs to Program after Blocking is checked.
In particular, monotonicity and the public cap hold without any hypothesis
that an oracle is an honest graph oracle.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Endpoint

noncomputable section

def logScale (n : ℕ) : ℕ := Nat.clog 2 n + 4

def edgeFactor (n : ℕ) : ℕ := 2 * Nat.clog 2 n + 4

/-- The guard is public even when the preceding oracle replies are inconsistent. -/
def supplyCap (n : ℕ) : ℕ := min (n ^ 2) ⌈24 * (n : ℝ) ^ (4 / 3 : ℝ)⌉₊

/-- Closed numerical form of Blocking's full-network repair bound. -/
def repairFormula (n R : ℕ) : ℝ :=
  (2 * ((n : ℝ) + 2) +
    4 * ((n : ℝ) + 2) * min (R : ℝ) (6 * (n : ℝ) ^ (2 / 3 : ℝ)) +
    7 * (n : ℝ) * Real.sqrt R) * edgeFactor n

def repairQueries (n R : ℕ) : ℕ :=
  if R = 0 then 0 else ⌈repairFormula n R⌉₊

def headlineQueries (n : ℕ) : ℕ :=
  ⌈2048 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2⌉₊

theorem logScale_pos (n : ℕ) : 0 < logScale n := by
  unfold logScale
  omega

theorem logScale_one_le (n : ℕ) : (1 : ℝ) ≤ logScale n := by
  exact_mod_cast (show 1 ≤ logScale n from logScale_pos n)

theorem edgeFactor_le (n : ℕ) : edgeFactor n ≤ 2 * logScale n := by
  unfold edgeFactor logScale
  omega

theorem supplyCap_le_square (n : ℕ) : supplyCap n ≤ n ^ 2 := Nat.min_le_left _ _

/-- Honest supply bounds imply the guard; this lemma is not used to bound
the cost of an arbitrary answer history. -/
theorem supply_le_cap {n R : ℕ}
    (hquad : (R : ℝ) ≤ (n : ℝ) ^ 2)
    (hheight : (R : ℝ) ≤ 24 * (n : ℝ) ^ (4 / 3 : ℝ)) : R ≤ supplyCap n := by
  apply le_min
  · exact_mod_cast hquad
  · have h := hheight.trans (Nat.le_ceil _)
    exact_mod_cast h

theorem repairFormula_nonneg (n R : ℕ) : 0 ≤ repairFormula n R := by
  unfold repairFormula
  positivity

theorem repairFormula_mono (n : ℕ) {R S : ℕ} (h : R ≤ S) :
    repairFormula n R ≤ repairFormula n S := by
  unfold repairFormula
  have hR : (R : ℝ) ≤ S := by exact_mod_cast h
  have hm := min_le_min_right (6 * (n : ℝ) ^ (2 / 3 : ℝ)) hR
  have hs := Real.sqrt_le_sqrt hR
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  have hp := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ 4 * ((n : ℝ) + 2) by positivity)
  have hq := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 7 * (n : ℝ) by positivity)
  linarith

/-- Monotonicity supplies a fixed tree index after a public supply guard. -/
theorem repairQueries_mono (n : ℕ) {R S : ℕ} (h : R ≤ S) :
    repairQueries n R ≤ repairQueries n S := by
  by_cases hR : R = 0
  · simp [repairQueries, hR]
  · have hS : S ≠ 0 := by omega
    simp only [repairQueries, hR, hS, ↓reduceIte]
    exact Nat.ceil_mono (repairFormula_mono n h)

theorem repairQueries_le_add_one (n R : ℕ) :
    (repairQueries n R : ℝ) ≤ repairFormula n R + 1 := by
  by_cases hR : R = 0
  · subst R
    simp only [repairQueries, ↓reduceIte, Nat.cast_zero]
    linarith [repairFormula_nonneg n 0]
  · simp only [repairQueries, hR, ↓reduceIte]
    exact (Nat.ceil_lt_add_one (repairFormula_nonneg n R)).le

theorem two_thirds_sq (n : ℕ) :
    ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = (n : ℝ) ^ (4 / 3 : ℝ) := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

theorem n_mul_two_thirds {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (5 / 3 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by rw [Real.rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) + 2 / 3) := (Real.rpow_add hnR _ _).symm
    _ = _ := by norm_num

theorem supplyCap_le_height {n : ℕ} (hn : 1 ≤ n) :
    (supplyCap n : ℝ) ≤ 25 * (n : ℝ) ^ (4 / 3 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ (4 / 3 : ℝ) :=
    Real.one_le_rpow hnR (by norm_num)
  have hcap : (supplyCap n : ℝ) ≤ ⌈24 * (n : ℝ) ^ (4 / 3 : ℝ)⌉₊ := by
    exact_mod_cast (Nat.min_le_right (n ^ 2) ⌈24 * (n : ℝ) ^ (4 / 3 : ℝ)⌉₊)
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 24 * (n : ℝ) ^ (4 / 3 : ℝ))
  linarith

theorem sqrt_supplyCap_le {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (supplyCap n) ≤ 5 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  have h := supplyCap_le_height hn
  rw [← two_thirds_sq n] at h
  nlinarith

theorem sqrt_n_le {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) ≤ 5 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ≤ (n : ℝ) ^ (4 / 3 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1 : ℝ) ≤ 4 / 3)
  apply (Real.sqrt_le_left (by positivity)).mpr
  rw [← two_thirds_sq n] at hp
  nlinarith [sq_nonneg ((n : ℝ) ^ (2 / 3 : ℝ))]

/-- This inequality applies both to the guarded discrepancy repair and to
the second terminal solve, which has public bound R=n. -/
theorem repairFormula_bound {n R : ℕ} (hn : 2 ≤ n)
    (hs : Real.sqrt R ≤ 5 * (n : ℝ) ^ (2 / 3 : ℝ)) :
    repairFormula n R ≤
      174 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) := by
  let b := (n : ℝ) ^ (2 / 3 : ℝ)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb : 1 ≤ b := Real.one_le_rpow (by linarith) (by norm_num)
  have hnb : (n : ℝ) ≤ n * b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hn0
  have hfirst : 2 * ((n : ℝ) + 2) ≤ 4 * n * b := by nlinarith
  have hmid : 4 * ((n : ℝ) + 2) * min (R : ℝ) (6 * b) ≤ 48 * n * b := by
    have h := mul_le_mul (show 4 * ((n : ℝ) + 2) ≤ 8 * n by linarith)
      (min_le_right (R : ℝ) (6 * b))
      (show 0 ≤ min (R : ℝ) (6 * b) by positivity)
      (show 0 ≤ 8 * (n : ℝ) by positivity)
    nlinarith
  have hlast : 7 * (n : ℝ) * Real.sqrt R ≤ 35 * n * b := by
    have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 7 * (n : ℝ) by positivity)
    change Real.sqrt R ≤ 5 * b at hs
    nlinarith
  have hcore : 2 * ((n : ℝ) + 2) +
      4 * ((n : ℝ) + 2) * min (R : ℝ) (6 * b) +
      7 * (n : ℝ) * Real.sqrt R ≤ 87 * n * b := by linarith
  have hedge : (edgeFactor n : ℝ) ≤ 2 * (logScale n : ℝ) := by
    exact_mod_cast edgeFactor_le n
  have h := mul_le_mul hcore hedge (Nat.cast_nonneg (edgeFactor n))
    (show 0 ≤ 87 * (n : ℝ) * b by positivity)
  have heq := n_mul_two_thirds (show 0 < n by omega)
  change (n : ℝ) * b = (n : ℝ) ^ (5 / 3 : ℝ) at heq
  have hend : (87 * (n : ℝ) * b) * (2 * (logScale n : ℝ)) =
      174 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) := by
    rw [← heq]
    ring
  unfold repairFormula
  change (2 * ((n : ℝ) + 2) + 4 * ((n : ℝ) + 2) * min (R : ℝ) (6 * b) +
    7 * (n : ℝ) * Real.sqrt R) * edgeFactor n ≤ _
  exact h.trans_eq hend

theorem repairQueries_bound {n R : ℕ} (hn : 2 ≤ n)
    (hs : Real.sqrt R ≤ 5 * (n : ℝ) ^ (2 / 3 : ℝ)) :
    (repairQueries n R : ℝ) ≤
      175 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) := by
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ (5 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  have hunit := one_le_mul_of_one_le_of_one_le hp (logScale_one_le n)
  linarith [repairQueries_le_add_one n R, repairFormula_bound hn hs]

theorem repairStages_bound {n : ℕ} (hn : 2 ≤ n) :
    ((repairQueries n (supplyCap n) + (repairQueries n n + 1) : ℕ) : ℝ) ≤
      351 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) := by
  have ha := repairQueries_bound hn (sqrt_supplyCap_le (show 1 ≤ n by omega))
  have hb := repairQueries_bound hn (sqrt_n_le (show 1 ≤ n by omega))
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ (5 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  have hunit := one_le_mul_of_one_le_of_one_le hp (logScale_one_le n)
  push_cast
  linarith

/-- The actual acceleration precision is at most twice the final log factor. -/
theorem precision_log_bound (n : ℕ) :
    Nat.clog 2 (64 * n ^ 2) + 1 ≤ 2 * logScale n := by
  have hn : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) _
  have hp : 64 * n ^ 2 ≤ 2 ^ (6 + 2 * Nat.clog 2 n) := by
    calc
      _ ≤ 64 * (2 ^ Nat.clog 2 n) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2)
      _ = 2 ^ (6 + Nat.clog 2 n * 2) := by rw [pow_add, pow_mul]; norm_num
      _ = _ := by congr 1; omega
  have hc := Nat.clog_le_of_le_pow hp
  unfold logScale
  omega

/-- Final arithmetic uses the preparation cost on arbitrary answers and the
two fixed repair indices. No graph-realization or honest-supply premise occurs. -/
theorem combined_cost_bound {n : ℕ} (hn : 2 ≤ n) (preparationCost : ℕ)
    (hp : (preparationCost : ℝ) ≤ 256 * (n : ℝ) ^ (5 / 3 : ℝ) *
      ((Nat.clog 2 (64 * n ^ 2) : ℝ) + 1) ^ 2) :
    ((preparationCost + (repairQueries n (supplyCap n) +
      (repairQueries n n + 1)) : ℕ) : ℝ) ≤
      2048 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2 := by
  have hlog : (Nat.clog 2 (64 * n ^ 2) : ℝ) + 1 ≤ 2 * (logScale n : ℝ) := by
    exact_mod_cast precision_log_bound n
  have hsq := mul_self_le_mul_self
    (by positivity : 0 ≤ (Nat.clog 2 (64 * n ^ 2) : ℝ) + 1) hlog
  have hpm := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 256 * (n : ℝ) ^ (5 / 3 : ℝ) by positivity)
  have hl := logScale_one_le n
  have hll : (logScale n : ℝ) ≤ (logScale n : ℝ) ^ 2 := by nlinarith
  have hrs := mul_le_mul_of_nonneg_left hll
    (show 0 ≤ 351 * (n : ℝ) ^ (5 / 3 : ℝ) by positivity)
  have hr := repairStages_bound hn
  have hnonneg : 0 ≤ (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2 := by positivity
  push_cast at hr ⊢
  nlinarith

theorem combined_cost_le_headline {n : ℕ} (hn : 2 ≤ n) (preparationCost : ℕ)
    (hp : (preparationCost : ℝ) ≤ 256 * (n : ℝ) ^ (5 / 3 : ℝ) *
      ((Nat.clog 2 (64 * n ^ 2) : ℝ) + 1) ^ 2) :
    preparationCost + (repairQueries n (supplyCap n) + (repairQueries n n + 1)) ≤
      headlineQueries n := by
  have h : ((preparationCost + (repairQueries n (supplyCap n) +
      (repairQueries n n + 1)) : ℕ) : ℝ) ≤ (headlineQueries n : ℝ) :=
    (combined_cost_bound hn preparationCost hp).trans (Nat.le_ceil _)
  exact Nat.cast_le.mp h

end
end CutQueryComplexity.DirectedUnitST.Endpoint

#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.supply_le_cap
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.repairQueries_mono
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.sqrt_supplyCap_le
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.repairStages_bound
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.precision_log_bound
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.combined_cost_bound
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.combined_cost_le_headline
