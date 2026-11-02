import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Public superincreasing costs for tree-pattern certificates

Every potential unordered pair has its own fixed power of two. A nonempty
signed sum of distinct such costs is nonzero: the largest term strictly
dominates all smaller terms. These costs contain no graph or divergence.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset

/-- The canonical orientation of a potential unordered pair. -/
abbrev Pair (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

/-- A public injective index; unused exponents are harmless. -/
def pairIndex {n : ℕ} (e : Pair n) : ℕ := e.val.1.val * n + e.val.2.val

theorem pairIndex_injective {n : ℕ} : Function.Injective (@pairIndex n) := by
  intro e f hef
  have heq : e.val.1.val * n + e.val.2.val =
      f.val.1.val * n + f.val.2.val := hef
  have hfst : e.val.1.val = f.val.1.val := by
    rcases lt_trichotomy e.val.1.val f.val.1.val with h | h | h
    · have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h)
      have he := e.val.2.isLt
      nlinarith
    · exact h
    · have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h)
      have hf := f.val.2.isLt
      nlinarith
  have hsnd : e.val.2.val = f.val.2.val := by
    rw [hfst] at heq
    exact Nat.add_left_cancel heq
  exact Subtype.ext (Prod.ext (Fin.ext hfst) (Fin.ext hsnd))

def pairCost {n : ℕ} (e : Pair n) : ℤ := 2 ^ pairIndex e

theorem pairCost_pos {n : ℕ} (e : Pair n) : 0 < pairCost e := by
  exact pow_pos (by norm_num) _

/-- Integral antisymmetric costs on ordered potential pairs. -/
def publicCost {n : ℕ} (u v : Fin n) : ℤ :=
  if u < v then 2 ^ (u.val * n + v.val)
  else if v < u then -(2 ^ (v.val * n + u.val)) else 0

@[simp] theorem publicCost_self {n : ℕ} (u : Fin n) : publicCost u u = 0 := by
  simp [publicCost]

theorem publicCost_reverse {n : ℕ} (u v : Fin n) :
    publicCost v u = -publicCost u v := by
  rcases lt_trichotomy u v with h | h | h
  · simp [publicCost, h, not_lt.mpr h.le]
  · subst v
    simp
  · simp [publicCost, h, not_lt.mpr h.le]

theorem publicCost_pair {n : ℕ} (e : Pair n) :
    publicCost e.val.1 e.val.2 = pairCost e := by
  simp [publicCost, e.property, pairCost, pairIndex]

theorem publicCost_ne_zero {n : ℕ} {u v : Fin n} (h : u ≠ v) :
    publicCost u v ≠ 0 := by
  rcases lt_or_gt_of_ne h with huv | hvu
  · simp [publicCost, huv]
  · simp [publicCost, hvu, not_lt.mpr hvu.le]

theorem sum_two_pow_range (m : ℕ) :
    ∑ i ∈ range m, (2 : ℤ) ^ i = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ih, pow_succ]
      ring

/-- A signed sum of distinct powers below m has magnitude less than 2^m. -/
theorem abs_sum_signed_two_pow_lt {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (index : ι → ℕ) (sign : ι → ℤ) (m : ℕ)
    (hinj : Set.InjOn index S) (hindex : ∀ i ∈ S, index i < m)
    (hsign : ∀ i ∈ S, |sign i| ≤ 1) :
    |∑ i ∈ S, sign i * 2 ^ index i| < (2 : ℤ) ^ m := by
  have hsub : S.image index ⊆ range m := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (hindex i hi)
  calc
    |∑ i ∈ S, sign i * 2 ^ index i| ≤
        ∑ i ∈ S, |sign i * 2 ^ index i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, (2 : ℤ) ^ index i := by
      apply sum_le_sum
      intro i hi
      have hpow : 0 ≤ (2 : ℤ) ^ index i := by positivity
      rw [abs_mul, abs_of_nonneg hpow]
      exact mul_le_of_le_one_left hpow (hsign i hi)
    _ = ∑ k ∈ S.image index, (2 : ℤ) ^ k := (sum_image hinj).symm
    _ ≤ ∑ k ∈ range m, (2 : ℤ) ^ k := by
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg (by norm_num) _)
    _ = (2 : ℤ) ^ m - 1 := sum_two_pow_range m
    _ < (2 : ℤ) ^ m := by omega

/-- Superincreasing public costs exclude every nonempty signed cancellation. -/
theorem signed_two_pow_sum_ne_zero {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (hne : S.Nonempty) (index : ι → ℕ) (sign : ι → ℤ)
    (hinj : Set.InjOn index S) (hsign : ∀ i ∈ S, |sign i| = 1) :
    ∑ i ∈ S, sign i * (2 : ℤ) ^ index i ≠ 0 := by
  obtain ⟨j, hj, hmax⟩ := exists_max_image S index hne
  have hlt : ∀ i ∈ S.erase j, index i < index j := by
    intro i hi
    have hiS := mem_of_mem_erase hi
    have hneij := (mem_erase.mp hi).1
    have hle := hmax i hiS
    have hne' : index i ≠ index j := fun h => hneij (hinj hiS hj h)
    omega
  have hsmall := abs_sum_signed_two_pow_lt (S.erase j) index sign (index j)
    (hinj.mono (erase_subset _ _)) hlt
    (fun i hi => (hsign i (mem_of_mem_erase hi)).le)
  have htop : |sign j * (2 : ℤ) ^ index j| = 2 ^ index j := by
    rw [abs_mul, hsign j hj, one_mul, abs_of_nonneg (pow_nonneg (by norm_num) _)]
  intro hz
  have heq := sum_erase_add S (fun i => sign i * (2 : ℤ) ^ index i) hj
  rw [hz] at heq
  have hrest : ∑ i ∈ S.erase j, sign i * (2 : ℤ) ^ index i =
      -(sign j * (2 : ℤ) ^ index j) := by linarith
  rw [hrest, abs_neg, htop] at hsmall
  exact lt_irrefl _ hsmall

theorem signed_pairCost_sum_ne_zero {n : ℕ} (S : Finset (Pair n))
    (hne : S.Nonempty) (sign : Pair n → ℤ) (hsign : ∀ e ∈ S, |sign e| = 1) :
    ∑ e ∈ S, sign e * pairCost e ≠ 0 :=
  signed_two_pow_sum_ne_zero S hne pairIndex sign pairIndex_injective.injOn hsign

end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.pairIndex_injective
#print axioms CutQueryComplexity.Certificate.TreePattern.publicCost_reverse
#print axioms CutQueryComplexity.Certificate.TreePattern.abs_sum_signed_two_pow_lt
#print axioms CutQueryComplexity.Certificate.TreePattern.signed_two_pow_sum_ne_zero
#print axioms CutQueryComplexity.Certificate.TreePattern.signed_pairCost_sum_ne_zero
