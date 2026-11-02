import CutQueryComplexity.DirectedUnitST.Repair.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Finite layer-cake and inverse-square tail accounting

These are numerical summation lemmas, not an assumed operational Dinic bound.
An implementation must separately connect its phase values to residual cuts
and its discovery count to nonnegative integral phase usage.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Repair

open Finset

variable {I : Type*} [Fintype I]

/-- Zero-based tail: phases of distance at least `k+1`. -/
def tailMass (distance : I → ℕ) (amount : I → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if k < distance i then amount i else 0

/-- Nonnegative phase values bound every tail by the total sent value. -/
theorem tailMass_le_total (distance : I → ℕ) (amount : I → ℝ)
    (ha : ∀ i, 0 ≤ amount i) (k : ℕ) :
    tailMass distance amount k ≤ ∑ i, amount i := by
  apply sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact ha i

/-- A residual deficit bound before each phase implies the numerical tail
bound used in layer-cake accounting. Pick the first phase above the threshold;
monotonicity identifies its remaining value with the entire tail. -/
theorem tailMass_of_remaining_deficit {P : ℕ} (distance : Fin P → ℕ)
    (amount : Fin P → ℝ) (hd : Monotone distance) (C : ℝ) (hC : 0 ≤ C)
    (hremaining : ∀ i, 4 ≤ distance i →
      (∑ j, if i ≤ j then amount j else 0) ≤ C / (distance i : ℝ) ^ 2)
    (k : ℕ) (hk : 3 ≤ k) :
    tailMass distance amount k ≤ C / ((k : ℝ) + 1) ^ 2 := by
  classical
  let S : Finset (Fin P) := univ.filter fun i => k < distance i
  by_cases hS : S.Nonempty
  · let i := S.min' hS
    have hi : i ∈ S := min'_mem S hS
    have hik : k < distance i := (mem_filter.mp hi).2
    have hiff (j : Fin P) : i ≤ j ↔ k < distance j := by
      constructor
      · intro hij
        exact hik.trans_le (hd hij)
      · intro hj
        exact min'_le S j (mem_filter.mpr ⟨mem_univ j, hj⟩)
    have heq : tailMass distance amount k = ∑ j, if i ≤ j then amount j else 0 := by
      apply sum_congr rfl
      intro j _
      simp only [hiff j]
    rw [heq]
    have hs := hremaining i (by omega)
    have hdR : (k : ℝ) + 1 ≤ distance i := by
      exact_mod_cast (show k + 1 ≤ distance i by omega)
    have hden : ((k : ℝ) + 1) ^ 2 ≤ (distance i : ℝ) ^ 2 := by
      have h := mul_self_le_mul_self (by positivity : 0 ≤ (k : ℝ) + 1) hdR
      nlinarith
    have hinv := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2) hden
    have hscale := mul_le_mul_of_nonneg_left hinv hC
    have hquot : C / (distance i : ℝ) ^ 2 ≤ C / ((k : ℝ) + 1) ^ 2 := by
      simpa only [mul_one_div] using hscale
    exact hs.trans hquot
  · have hnone (i : Fin P) : ¬ k < distance i := by
      intro hi
      exact hS ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
    simp only [tailMass, hnone, ↓reduceIte, sum_const_zero]
    positivity

/-- Finite layer-cake identity, with all summation bounds explicit. -/
theorem phase_layercake (distance : I → ℕ) (amount : I → ℝ) (M : ℕ)
    (hM : ∀ i, distance i ≤ M) :
    ∑ i, (distance i : ℝ) * amount i = ∑ k ∈ range M, tailMass distance amount k := by
  simp only [tailMass]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  have hfilter : (range M).filter (fun k => k < distance i) = range (distance i) := by
    ext k
    simp only [mem_filter, mem_range]
    have := hM i
    omega
  rw [← sum_filter, hfilter]
  simp

omit [Fintype I] in
/-- The elementary telescoping majorant for an inverse-square tail. -/
theorem inverse_square_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have heq : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp [ne_of_gt hx, ne_of_gt (show 0 < x + 1 by linarith)]
    ring
  rw [heq]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

omit [Fintype I] in
/-- A finite inverse-square tail bound, proved by telescoping; no infinite
series or asymptotic summation theorem is assumed. -/
theorem inverse_square_tail (K : ℕ) (hK : 0 < K) (M : ℕ) :
    ∑ j ∈ range M, 1 / ((K : ℝ) + j + 1) ^ 2 ≤ 1 / (K : ℝ) := by
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hstrong : ∀ m : ℕ,
      ∑ j ∈ range m, 1 / ((K : ℝ) + j + 1) ^ 2 ≤
        1 / (K : ℝ) - 1 / ((K : ℝ) + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      have hstep := inverse_square_step ((K : ℝ) + m) (by positivity)
      push_cast
      simp only [add_assoc] at ih hstep ⊢
      linarith
  have hlast : 0 ≤ 1 / ((K : ℝ) + M) := by positivity
  linarith [hstrong M]

/-- Splitting phase lengths into a uniform head and inverse-square tail.
The tail premises are numerical quantities to be supplied by residual-cut
invariants of a future operational implementation. -/
theorem phase_length_split (distance : I → ℕ) (amount : I → ℝ)
    (M K : ℕ) (hM : ∀ i, distance i ≤ M) (hK : 0 < K)
    (R C : ℝ) (hC : 0 ≤ C)
    (hhead : ∀ k, tailMass distance amount k ≤ R)
    (htail : ∀ k, K ≤ k → tailMass distance amount k ≤ C / ((k : ℝ) + 1) ^ 2) :
    ∑ i, (distance i : ℝ) * amount i ≤ (K : ℝ) * R + C / (K : ℝ) := by
  rw [phase_layercake distance amount (K + M) (fun i => by have := hM i; omega)]
  rw [sum_range_add]
  have hfirst : ∑ k ∈ range K, tailMass distance amount k ≤ (K : ℝ) * R := by
    calc
      _ ≤ ∑ _ ∈ range K, R := sum_le_sum fun k _ => hhead k
      _ = _ := by simp
  have hlast : ∑ j ∈ range M, tailMass distance amount (K + j) ≤ C / (K : ℝ) := by
    calc
      _ ≤ ∑ j ∈ range M, C / (((K + j : ℕ) : ℝ) + 1) ^ 2 :=
        sum_le_sum fun j _ => htail (K + j) (by omega)
      _ = C * ∑ j ∈ range M, 1 / ((K : ℝ) + j + 1) ^ 2 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        push_cast
        ring
      _ ≤ C * (1 / (K : ℝ)) :=
        mul_le_mul_of_nonneg_left (inverse_square_tail K hK M) hC
      _ = _ := by ring
  exact add_le_add hfirst hlast

/-- The accepted repair-length constant follows from the actual tail
inequalities with cutoff `ceil (4*n/sqrt R)`. This theorem only sums numeric
phase data; the operational run must establish those tails. -/
theorem phase_length_sqrt (distance : I → ℕ) (amount : I → ℝ)
    (M : ℕ) (hM : ∀ i, distance i ≤ M) (n R : ℝ)
    (hn : 1 ≤ n) (hR : 1 ≤ R) (hRn : R ≤ n ^ 2)
    (hhead : ∀ k, tailMass distance amount k ≤ R)
    (htail : ∀ k, 3 ≤ k → tailMass distance amount k ≤
      8 * n ^ 2 / ((k : ℝ) + 1) ^ 2) :
    ∑ i, (distance i : ℝ) * amount i ≤ 7 * n * Real.sqrt R := by
  let s := Real.sqrt R
  have hn0 : 0 < n := by linarith
  have hR0 : 0 < R := by linarith
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hR
  have hs0 : 0 < s := by linarith
  have hsq : s ^ 2 = R := Real.sq_sqrt hR0.le
  have hsn : s ≤ n := (Real.sqrt_le_left hn0.le).mpr hRn
  have hratio : 4 ≤ 4 * n / s := (le_div_iff₀ hs0).mpr (by nlinarith)
  let K : ℕ := ⌈4 * n / s⌉₊
  have hKlo : 4 * n / s ≤ (K : ℝ) := Nat.le_ceil _
  have hKfourR : (4 : ℝ) ≤ K := hratio.trans hKlo
  have hKfour : 4 ≤ K := by exact_mod_cast hKfourR
  have hK : 0 < K := by omega
  have hK0 : 0 < (K : ℝ) := by exact_mod_cast hK
  have hKhi : (K : ℝ) ≤ 4 * n / s + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * n / s)).le
  have hidentity : (4 * n / s) * R = 4 * n * s := by
    rw [← hsq]
    field_simp [ne_of_gt hs0]
  have hfirst : (K : ℝ) * R ≤ 5 * n * s := by
    have h := mul_le_mul_of_nonneg_right hKhi hR0.le
    rw [add_mul, hidentity, one_mul] at h
    have hsmall : R ≤ n * s := by
      have hm := mul_le_mul_of_nonneg_right hsn hs0.le
      nlinarith
    linarith
  have hlast : 8 * n ^ 2 / (K : ℝ) ≤ 2 * n * s := by
    apply (div_le_iff₀ hK0).mpr
    have hproduct : 4 * n ≤ (K : ℝ) * s := (div_le_iff₀ hs0).mp hKlo
    nlinarith [mul_le_mul_of_nonneg_left hproduct (show 0 ≤ 2 * n by positivity)]
  have htotal := phase_length_split distance amount M K hM hK R (8 * n ^ 2)
    (by positivity) hhead (fun k hk => htail k (by omega))
  change (∑ i, (distance i : ℝ) * amount i) ≤ 7 * n * s
  linarith

/-- Combine the learned-pair rounding error with the regularized oracle
discrepancy. The exact identity uses `g=y-beta+r`, not `y-beta`. -/
theorem regularized_rounding_error (b y beta r g : I → ℝ) (n k : ℝ)
    (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hg : ∀ v, g v = y v - beta v + r v)
    (hround : l1 (fun v => b v - y v) ≤ 2 * n)
    (horacle : l1 g ≤ 4 * n * Real.sqrt k + n + 1 / 32) :
    l1 (fun v => b v - beta v + r v) ≤ 8 * n * Real.sqrt k := by
  have hs : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr hk
  have htri : l1 (fun v => b v - beta v + r v) ≤
      l1 (fun v => b v - y v) + l1 g := by
    simp only [l1, ← sum_add_distrib]
    apply sum_le_sum
    intro v _
    have heq : b v - beta v + r v = (b v - y v) + g v := by rw [hg]; ring
    rw [heq]
    exact abs_add_le _ _
  nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ n by linarith)]

/-- Distinct positive phase distances give at most `K` early phases. Every
later phase uses at least one unit, so its count is bounded by the remaining
flow mass. This is the separate overhead count needed in addition to `d*r`.
An operational implementation must prove the distance and positive-amount
premises from its actual blocking phases. -/
theorem phase_count_le_head_add_tail (distance : I → ℕ) (amount : I → ℝ)
    (hdpos : ∀ i, 0 < distance i) (hdinj : Function.Injective distance)
    (ha : ∀ i, 1 ≤ amount i) (K : ℕ) :
    (Fintype.card I : ℝ) ≤ K + tailMass distance amount K := by
  classical
  let head : Finset I := univ.filter fun i => distance i ≤ K
  have hhead : head.card ≤ K := by
    have hsub : head.image distance ⊆ Icc 1 K := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
      exact mem_Icc.mpr ⟨hdpos i, (mem_filter.mp hi).2⟩
    have hc := card_le_card hsub
    rw [card_image_of_injective head hdinj] at hc
    simpa using hc
  have htail : ((headᶜ).card : ℝ) ≤ tailMass distance amount K := by
    calc
      _ = ∑ _ ∈ headᶜ, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ headᶜ, amount i := sum_le_sum fun i _ => ha i
      _ = tailMass distance amount K := by
        have heq : headᶜ = univ.filter fun i => K < distance i := by
          ext i
          simp [head]
        simp only [heq, sum_filter, tailMass]
  have htotal : (head.card : ℝ) + (headᶜ).card = Fintype.card I := by
    exact_mod_cast card_add_card_compl head
  have hheadR : (head.card : ℝ) ≤ K := by exact_mod_cast hhead
  linarith

/-- Numerical phase overhead from the heavy-terminal inverse-square tail.
This does not postulate the number of phases or an operational query bound. -/
theorem phase_count_split (distance : I → ℕ) (amount : I → ℝ)
    (hdpos : ∀ i, 0 < distance i) (hdinj : Function.Injective distance)
    (ha : ∀ i, 1 ≤ amount i) (K : ℕ) (C : ℝ)
    (htail : tailMass distance amount K ≤ C / ((K : ℝ) + 1) ^ 2) :
    (Fintype.card I : ℝ) ≤ K + C / ((K : ℝ) + 1) ^ 2 := by
  have h := phase_count_le_head_add_tail distance amount hdpos hdinj ha K
  linarith

/-- Explicit phase-overhead bound from integer phase amounts and the
heavy-terminal deficit tail. The cutoff is `ceil (4*n^(2/3))`. -/
theorem phase_count_two_thirds (distance : I → ℕ) (amount : I → ℝ)
    (hdpos : ∀ i, 0 < distance i) (hdinj : Function.Injective distance)
    (ha : ∀ i, 1 ≤ amount i) (n : ℝ) (hn : 1 ≤ n)
    (htail : ∀ k, 3 ≤ k → tailMass distance amount k ≤
      8 * n ^ 2 / ((k : ℝ) + 1) ^ 2) :
    (Fintype.card I : ℝ) ≤ 6 * n ^ (2 / 3 : ℝ) := by
  let a := n ^ (2 / 3 : ℝ)
  have hn0 : 0 < n := by linarith
  have ha1 : 1 ≤ a := Real.one_le_rpow hn (by norm_num)
  have ha0 : 0 < a := by linarith
  have hcube : a ^ 3 = n ^ 2 := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  let K : ℕ := ⌈4 * a⌉₊
  have hKlo : 4 * a ≤ (K : ℝ) := Nat.le_ceil _
  have hKfourR : (4 : ℝ) ≤ K := by linarith
  have hKfour : 4 ≤ K := by exact_mod_cast hKfourR
  have hKhi : (K : ℝ) ≤ 5 * a := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * a)
    change (K : ℝ) < 4 * a + 1 at h
    linarith
  have hden : 16 * a ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := by
    have h := mul_self_le_mul_self (show 0 ≤ 4 * a by positivity)
      (show 4 * a ≤ (K : ℝ) + 1 by linarith)
    nlinarith
  have hlast : 8 * n ^ 2 / ((K : ℝ) + 1) ^ 2 ≤ a / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hden (show 0 ≤ a / 2 by positivity)
    rw [← hcube]
    nlinarith
  have h := phase_count_split distance amount hdpos hdinj ha K (8 * n ^ 2)
    (htail K (by omega))
  change (Fintype.card I : ℝ) ≤ 6 * a
  linarith

end CutQueryComplexity.DirectedUnitST.Repair

#print axioms CutQueryComplexity.DirectedUnitST.Repair.phase_layercake
#print axioms CutQueryComplexity.DirectedUnitST.Repair.tailMass_of_remaining_deficit
#print axioms CutQueryComplexity.DirectedUnitST.Repair.inverse_square_tail
#print axioms CutQueryComplexity.DirectedUnitST.Repair.phase_length_split
#print axioms CutQueryComplexity.DirectedUnitST.Repair.phase_length_sqrt
#print axioms CutQueryComplexity.DirectedUnitST.Repair.regularized_rounding_error
#print axioms CutQueryComplexity.DirectedUnitST.Repair.phase_count_split
#print axioms CutQueryComplexity.DirectedUnitST.Repair.phase_count_two_thirds
