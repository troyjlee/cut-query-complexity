import CutQueryComplexity.ImplicitLP.FrozenQuery

/-! # Certified hidden aggregates of public real pair formulas (D7)

Many numerical primitives need hidden sums `Σ_{u ≠ v} sym(v,u) φ(v,u)` or
`Σ_{u < v} sym(u,v) φ(u,v)` of a public real formula `φ`, such as norms, objective values,
leverage totals, and support sums. A real `φ` need not be dyadic, so round it to the grid
`2^{−p}ℤ` (`roundFormula`) and aggregate the rounded values exactly with `allRowsUniv` or
`pairAgg`. Then
* the row aggregate is within `deg(v)·2^{−p}` of the true value (`certRow_err`);
* the scalar pair aggregate is within `(Σ_{u<v} sym)·2^{−p}` of it (`certPair_err`);
* the costs are `6Bn` queries, with `B` the magnitude bit bound
  (`|⌊φ 2^p⌋| < 2^B` on the relevant pairs).

So every hidden sum used by a primitive is available as a certified interval of width
`2·(total multiplicity)·2^{−p}`, at a query cost linear in the bit length.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Finset

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `φ` rounded down to `2^{−p}ℤ`, as a dyadic formula on `B` magnitude bits. -/
def roundFormula (φ : V → V → ℝ) (p B : ℕ) : DyadicFormula V :=
  intFormula (fun v u => ⌊φ v u * 2 ^ p⌋) (-(p : ℤ)) B

omit [Fintype V] [DecidableEq V] in
theorem roundFormula_val {φ : V → V → ℝ} {p B : ℕ} {v u : V}
    (hB : (⌊φ v u * 2 ^ p⌋).natAbs < 2 ^ B) :
    (roundFormula φ p B).val v u = (⌊φ v u * 2 ^ p⌋ : ℝ) / 2 ^ p := by
  rw [roundFormula, intFormula_val _ _ B hB, zpow_neg, zpow_natCast, div_eq_mul_inv]

omit [Fintype V] [DecidableEq V] in
theorem roundFormula_err {φ : V → V → ℝ} {p B : ℕ} {v u : V}
    (hB : (⌊φ v u * 2 ^ p⌋).natAbs < 2 ^ B) :
    |(roundFormula φ p B).val v u - φ v u| ≤ 1 / 2 ^ p := by
  rw [roundFormula_val hB]
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have h1 := Int.floor_le (φ v u * 2 ^ p)
  have h3 := Int.lt_floor_add_one (φ v u * 2 ^ p)
  have he : (⌊φ v u * 2 ^ p⌋ : ℝ) / 2 ^ p - φ v u = ((⌊φ v u * 2 ^ p⌋ : ℝ) - φ v u * 2 ^ p) / 2 ^ p := by
    field_simp
  rw [he, abs_div, abs_of_pos h2, div_le_div_iff_of_pos_right h2, abs_le]
  constructor <;> linarith

/-- **Certified row aggregate.** The rounded row aggregate is within `Σ_u sym(v,u) · 2^{−p}`
of the hidden row sum of `φ`. -/
theorem certRow_err (G : DiGraph V) {φ : V → V → ℝ} {p B : ℕ} (allow : V → V → Bool) (v : V)
    (hB : ∀ u ∈ rowCand allow v, (⌊φ v u * 2 ^ p⌋).natAbs < 2 ^ B) :
    |(allRowsUniv (roundFormula φ p B) allow).eval G.out v -
        ∑ u ∈ rowCand allow v, (G.sym v u : ℝ) * φ v u| ≤
      (∑ u ∈ rowCand allow v, (G.sym v u : ℝ)) * (1 / 2 ^ p) := by
  rw [allRowsUniv_correct, ← sum_sub_distrib, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u hu => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (roundFormula_err (hB u hu)) (Nat.cast_nonneg _)

/-- **Certified scalar aggregate** over canonical pairs. -/
theorem certPair_err [LinearOrder V] (G : DiGraph V) {φ : V → V → ℝ} {p B : ℕ}
    (hB : ∀ u v, u < v → (⌊φ u v * 2 ^ p⌋).natAbs < 2 ^ B) :
    |(pairAgg (roundFormula φ p B)).eval G.out -
        ∑ u, ∑ v ∈ univ.filter (u < ·), (G.sym u v : ℝ) * φ u v| ≤
      (∑ u, ∑ v ∈ univ.filter (u < ·), (G.sym u v : ℝ)) * (1 / 2 ^ p) := by
  rw [pairAgg_correct, ← sum_sub_distrib, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u _ => ?_)
  rw [← sum_sub_distrib, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v hv => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (roundFormula_err (hB u v (mem_filter.mp hv).2))
    (Nat.cast_nonneg _)

/-- The bit bound from a public magnitude bound: `|φ| ≤ Φ` and `Φ 2^p + 1 ≤ 2^B`. -/
theorem floor_natAbs_lt {x : ℝ} {Φ : ℝ} {p B : ℕ} (hx : |x| ≤ Φ)
    (hB : Φ * 2 ^ p + 1 ≤ 2 ^ B) : (⌊x * 2 ^ p⌋).natAbs < 2 ^ B := by
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have h1 := Int.floor_le (x * 2 ^ p)
  have h3 := Int.lt_floor_add_one (x * 2 ^ p)
  have hxa := abs_le.mp hx
  have hlo : -(2 ^ B : ℝ) < ⌊x * 2 ^ p⌋ := by nlinarith
  have hhi : (⌊x * 2 ^ p⌋ : ℝ) < 2 ^ B := by nlinarith
  have hlo' : -(2 ^ B : ℤ) < ⌊x * 2 ^ p⌋ := by exact_mod_cast hlo
  have hhi' : ⌊x * 2 ^ p⌋ < (2 ^ B : ℤ) := by exact_mod_cast hhi
  rw [← Int.ofNat_lt, Int.natCast_natAbs]
  push_cast
  exact abs_lt.mpr ⟨hlo', hhi'⟩

end

end ImplicitLP
end CutQueryComplexity
