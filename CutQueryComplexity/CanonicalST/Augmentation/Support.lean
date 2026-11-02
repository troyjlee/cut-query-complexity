import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# The support bound for an integral flow in topological order

The input is an actual nonnegative integer arc flow. An injective topological
numbering supplies distinct positive outgoing lengths. Their triangular lower
bound, divergence telescoping, and Cauchy--Schwarz prove the support estimate.
The later circulation-deletion module constructs the required numbering.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Augmentation

open Finset
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def outSupport (a : V → V → ℕ) (u : V) : Finset V := univ.filter fun v => 0 < a u v

def supportSize (a : V → V → ℕ) : ℕ :=
  (univ.filter fun e : V × V => 0 < a e.1 e.2).card

def arcDiv (a : V → V → ℕ) (u : V) : ℝ :=
  (∑ v, (a u v : ℝ)) - ∑ v, (a v u : ℝ)

def lengthEnergy (a : V → V → ℕ) {n : ℕ} (p : V → Fin n) : ℝ :=
  ∑ u, ∑ v, (a u v : ℝ) * ((p v : ℝ) - (p u : ℝ))

theorem supportSize_eq_sum (a : V → V → ℕ) :
    supportSize a = ∑ u, (outSupport a u).card := by
  simp only [supportSize, outSupport, card_filter, Fintype.sum_prod_type]

/-- Distinct positive integers have at least triangular total size. -/
theorem positive_sum_lower (T : Finset ℕ) (hT : ∀ x ∈ T, 1 ≤ x) :
    T.card * (T.card + 1) ≤ 2 * ∑ x ∈ T, x := by
  revert hT
  refine Finset.strongInductionOn T ?_
  intro T ih hT
  by_cases hn : T.Nonempty
  · let m := T.max' hn
    have hm : m ∈ T := max'_mem T hn
    have hcard : T.card ≤ m := by
      have hsub : T ⊆ Icc 1 m := by
        intro x hx
        exact mem_Icc.mpr ⟨hT x hx, le_max' T x hx⟩
      simpa using card_le_card hsub
    have hi := ih (T.erase m) (erase_ssubset hm)
      (fun x hx => hT x (mem_of_mem_erase hx))
    have he := sum_erase_add T (fun x : ℕ => x) hm
    have hc := card_erase_add_one hm
    nlinarith
  · simp [not_nonempty_iff_eq_empty.mp hn]

theorem row_length_lower (a : V → V → ℕ) {n : ℕ} (p : V → Fin n)
    (hinj : Function.Injective p) (horder : ∀ u v, 0 < a u v → p u < p v) (u : V) :
    ((outSupport a u).card : ℝ) ^ 2 ≤
      2 * ∑ v, (a u v : ℝ) * ((p v : ℝ) - (p u : ℝ)) := by
  let N := outSupport a u
  let d : V → ℕ := fun v => (p v).val - (p u).val
  have hlt (v : V) (hv : v ∈ N) : (p u).val < (p v).val :=
    horder u v (mem_filter.mp hv).2
  have hd (v : V) (hv : v ∈ N) : 1 ≤ d v := by dsimp [d]; have := hlt v hv; omega
  have hdinj : Set.InjOn d (N : Set V) := by
    intro v hv w hw he
    apply hinj
    apply Fin.ext
    have hvp := hlt v hv
    have hwp := hlt w hw
    dsimp [d] at he
    omega
  have hi := positive_sum_lower (N.image d) (by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    exact hd v hv)
  rw [card_image_of_injOn hdinj, sum_image hdinj] at hi
  have hiR : (N.card : ℝ) * ((N.card : ℝ) + 1) ≤ 2 * ∑ v ∈ N, (d v : ℝ) := by
    exact_mod_cast hi
  have hdeq (v : V) (hv : v ∈ N) : (d v : ℝ) = (p v : ℝ) - (p u : ℝ) := by
    exact Nat.cast_sub (Nat.le_of_lt (hlt v hv))
  have heq : (∑ v ∈ N, (d v : ℝ)) = ∑ v ∈ N, ((p v : ℝ) - (p u : ℝ)) :=
    sum_congr rfl hdeq
  rw [heq] at hiR
  have hmul : (∑ v ∈ N, ((p v : ℝ) - (p u : ℝ))) ≤
      ∑ v ∈ N, (a u v : ℝ) * ((p v : ℝ) - (p u : ℝ)) := by
    apply sum_le_sum
    intro v hv
    have ha : (1 : ℝ) ≤ a u v := by
      exact_mod_cast (Nat.succ_le_of_lt (mem_filter.mp hv).2)
    have hpos : (0 : ℝ) ≤ (p v : ℝ) - (p u : ℝ) := by
      have h : (p u : ℝ) < (p v : ℝ) := by exact_mod_cast hlt v hv
      linarith
    nlinarith
  have hfull : (∑ v ∈ N, (a u v : ℝ) * ((p v : ℝ) - (p u : ℝ))) =
      ∑ v, (a u v : ℝ) * ((p v : ℝ) - (p u : ℝ)) := by
    apply sum_subset (subset_univ N)
    intro v _ hv
    have hz : a u v = 0 := by
      have : ¬ 0 < a u v := by simpa [N, outSupport] using hv
      omega
    simp [hz]
  rw [hfull] at hmul
  change (N.card : ℝ) ^ 2 ≤ _
  nlinarith [Nat.cast_nonneg (α := ℝ) N.card]

theorem lengthEnergy_divergence (a : V → V → ℕ) {n : ℕ} (p : V → Fin n) :
    lengthEnergy a p = -∑ u, (p u : ℝ) * arcDiv a u := by
  have hswap : (∑ u, ∑ v, (a u v : ℝ) * (p v : ℝ)) =
      ∑ v, (p v : ℝ) * ∑ u, (a u v : ℝ) := by
    rw [sum_comm]
    simp only [mul_sum]
    apply sum_congr rfl
    intro v _
    apply sum_congr rfl
    intro u _
    ring
  have hrow : (∑ u, ∑ v, (a u v : ℝ) * (p u : ℝ)) =
      ∑ u, (p u : ℝ) * ∑ v, (a u v : ℝ) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    ring
  simp only [lengthEnergy, mul_sub, sum_sub_distrib, hswap, hrow, arcDiv]
  ring

theorem lengthEnergy_st (a : V → V → ℕ) {n : ℕ} (p : V → Fin n)
    (s t : V) (r : ℝ)
    (hdiv : ∀ u, arcDiv a u = (if u = s then r else 0) - (if u = t then r else 0)) :
    lengthEnergy a p = r * ((p t : ℝ) - (p s : ℝ)) := by
  rw [lengthEnergy_divergence]
  simp only [hdiv, mul_sub, mul_ite, mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ,
    ↓reduceIte]
  ring

/-- Squared form, avoiding any asymptotic notation or hidden support premise. -/
theorem supportSize_sq_le (a : V → V → ℕ)
    (p : V → Fin (Fintype.card V)) (hinj : Function.Injective p)
    (horder : ∀ u v, 0 < a u v → p u < p v) (s t : V) {r : ℝ} (hr : 0 ≤ r)
    (hdiv : ∀ u, arcDiv a u = (if u = s then r else 0) - (if u = t then r else 0)) :
    (supportSize a : ℝ) ^ 2 ≤ 2 * (Fintype.card V : ℝ) ^ 2 * r := by
  have hrows : (∑ u, ((outSupport a u).card : ℝ) ^ 2) ≤ 2 * lengthEnergy a p := by
    rw [lengthEnergy, mul_sum]
    exact sum_le_sum fun u _ => row_length_lower a p hinj horder u
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset V)
    (fun u => ((outSupport a u).card : ℝ)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at hcs
  have hmass : (∑ u, ((outSupport a u).card : ℝ)) = (supportSize a : ℝ) := by
    rw [supportSize_eq_sum, Nat.cast_sum]
  rw [hmass] at hcs
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hlen : (p t : ℝ) - (p s : ℝ) ≤ Fintype.card V := by
    have ht : (p t : ℝ) < Fintype.card V := by exact_mod_cast (p t).isLt
    have hs : (0 : ℝ) ≤ (p s : ℝ) := Nat.cast_nonneg _
    linarith
  have he : lengthEnergy a p ≤ r * Fintype.card V := by
    rw [lengthEnergy_st a p s t r hdiv]
    exact mul_le_mul_of_nonneg_left hlen hr
  have hh := mul_le_mul_of_nonneg_right (hrows.trans (mul_le_mul_of_nonneg_left he
    (by norm_num : (0 : ℝ) ≤ 2))) hn
  nlinarith

/-- The paper's literal acyclic integral support estimate. -/
theorem supportSize_le (a : V → V → ℕ)
    (p : V → Fin (Fintype.card V)) (hinj : Function.Injective p)
    (horder : ∀ u v, 0 < a u v → p u < p v) (s t : V) {r : ℝ} (hr : 0 ≤ r)
    (hdiv : ∀ u, arcDiv a u = (if u = s then r else 0) - (if u = t then r else 0)) :
    (supportSize a : ℝ) ≤ Real.sqrt 2 * Fintype.card V * Real.sqrt r := by
  have h := supportSize_sq_le a p hinj horder s t hr hdiv
  have he : (Real.sqrt 2 * (Fintype.card V : ℝ) * Real.sqrt r) ^ 2 =
      2 * (Fintype.card V : ℝ) ^ 2 * r := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hr]
  have hnonneg : 0 ≤ Real.sqrt 2 * (Fintype.card V : ℝ) * Real.sqrt r := by positivity
  nlinarith [Nat.cast_nonneg (α := ℝ) (supportSize a)]

end
end CutQueryComplexity.CanonicalST.Augmentation

#print axioms CutQueryComplexity.CanonicalST.Augmentation.positive_sum_lower
#print axioms CutQueryComplexity.CanonicalST.Augmentation.row_length_lower
#print axioms CutQueryComplexity.CanonicalST.Augmentation.lengthEnergy_divergence
#print axioms CutQueryComplexity.CanonicalST.Augmentation.lengthEnergy_st
#print axioms CutQueryComplexity.CanonicalST.Augmentation.supportSize_sq_le
#print axioms CutQueryComplexity.CanonicalST.Augmentation.supportSize_le
