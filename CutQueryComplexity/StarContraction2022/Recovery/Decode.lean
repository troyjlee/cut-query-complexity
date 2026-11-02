import CutQueryComplexity.StarContraction2022.Recovery.Separating
import CutQueryComplexity.StarContraction2022.Common.Basic
import CutQueryComplexity.Model.Reduction
import CutQueryComplexity.Primitive.Learn
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Sparse bilinear recovery: finite measurements and counting bounds

The efficient family-size proof uses a finite union bound over vector
differences. Its anti-concentration ingredient is proved from Sperner's theorem
and an elementary central-binomial recurrence, rather than supplied as a
separating-matrix or sparse-recovery assumption.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Recovery

open Finset
open scoped Classical
noncomputable section

variable {C : Type} [Fintype C] [DecidableEq C]

def positiveLevel (w : C → ℤ) (a : ℤ) : Finset (Finset C) :=
  univ.filter fun S => ∑ c ∈ S, w c = a

/-- A positive weighted subset-sum level is an antichain. -/
theorem positiveLevel_antichain (w : C → ℤ) (hw : ∀ c, 0 < w c) (a : ℤ) :
    IsAntichain (· ⊆ ·) (positiveLevel w a : Set (Finset C)) := by
  intro S hS T hT hne hST
  have hs : ∑ c ∈ S, w c = a := (mem_filter.mp hS).2
  have ht : ∑ c ∈ T, w c = a := (mem_filter.mp hT).2
  have hnot : ¬T ⊆ S := fun hTS => hne (Subset.antisymm hST hTS)
  obtain ⟨c, hcT, hcS⟩ := not_subset.mp hnot
  have hlt : ∑ c ∈ S, w c < ∑ c ∈ T, w c :=
    sum_lt_sum_of_subset hST hcT hcS (hw c) (fun j _ _ => (hw j).le)
  exact (ne_of_lt hlt) (hs.trans ht.symm)

theorem positiveLevel_card_le (w : C → ℤ) (hw : ∀ c, 0 < w c) (a : ℤ) :
    (positiveLevel w a).card ≤ (Fintype.card C).choose (Fintype.card C / 2) :=
  (positiveLevel_antichain w hw a).sperner

/-- A uniform elementary bound, including the zero-dimensional case. -/
theorem centralBinom_square_bound (n : ℕ) :
    (Nat.centralBinom n : ℝ)^2 * (3 * (n : ℝ) + 1) ≤ (16 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have he : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
          2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ n
      have ha : (2 * (n : ℝ) + 1)^2 * (3 * (n : ℝ) + 4) ≤
          4 * ((n : ℝ) + 1)^2 * (3 * (n : ℝ) + 1) := by
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h : ((n : ℝ) + 1)^2 *
          ((Nat.centralBinom (n + 1) : ℝ)^2 * (3 * ((n : ℝ) + 1) + 1)) ≤
          ((n : ℝ) + 1)^2 * ((16 : ℝ)^n * 16) := by
        calc
          _ = (((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ))^2 *
              (3 * (n : ℝ) + 4) := by ring
          _ = (2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ))^2 *
              (3 * (n : ℝ) + 4) := by rw [he]
          _ = (4 * (Nat.centralBinom n : ℝ)^2) *
              ((2 * (n : ℝ) + 1)^2 * (3 * (n : ℝ) + 4)) := by ring
          _ ≤ (4 * (Nat.centralBinom n : ℝ)^2) *
              (4 * ((n : ℝ) + 1)^2 * (3 * (n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left ha (by positivity)
          _ = (16 * ((n : ℝ) + 1)^2) *
              ((Nat.centralBinom n : ℝ)^2 * (3 * (n : ℝ) + 1)) := by ring
          _ ≤ (16 * ((n : ℝ) + 1)^2) * (16 : ℝ)^n :=
            mul_le_mul_of_nonneg_left ih (by positivity)
          _ = _ := by ring
      have hp : (0 : ℝ) < ((n : ℝ) + 1)^2 := by positivity
      have h' := (mul_le_mul_iff_right₀ hp).mp h
      simpa only [Nat.cast_add, Nat.cast_one, pow_succ] using h'

private theorem centralBinom_odd (m : ℕ) :
    Nat.centralBinom (m + 1) = 2 * (2 * m + 1).choose m := by
  rw [Nat.centralBinom, show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
    Nat.choose_succ_succ', Nat.choose_symm_half]
  omega

theorem middle_choose_square_bound (n : ℕ) :
    ((n.choose (n / 2) : ℕ) : ℝ)^2 * ((n : ℝ) + 1) ≤ (4 : ℝ)^n := by
  have hcases : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
  rcases hcases with hn | hn
  · set m := n / 2
    have h := centralBinom_square_bound m
    have hc : (2 * m).choose m = Nat.centralBinom m := rfl
    have hpow : (4 : ℝ)^(2 * m) = (16 : ℝ)^m := by
      rw [pow_mul]
      norm_num
    rw [hn, hc, hpow]
    push_cast
    exact (mul_le_mul_of_nonneg_left
      (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) (sq_nonneg _)).trans h
  · set m := n / 2
    have h := centralBinom_square_bound (m + 1)
    have hc := centralBinom_odd m
    have hcR : (Nat.centralBinom (m + 1) : ℝ) =
        2 * ((2 * m + 1).choose m : ℝ) := by exact_mod_cast hc
    have hdiv : (2 * m + 1) / 2 = m := by omega
    have hpow : (4 : ℝ)^(2 * m + 1) = 4 * (16 : ℝ)^m := by
      rw [pow_succ, pow_mul]
      norm_num
      ring
    rw [hn]
    change (((2*m+1).choose m : ℝ)^2 * (((2*m+1 : ℕ) : ℝ)+1)) ≤ (4 : ℝ)^(2*m+1)
    rw [hpow]
    rw [hcR, pow_succ (16 : ℝ) m] at h
    push_cast at h ⊢
    have hs : 0 ≤ (((2 * m + 1).choose m : ℕ) : ℝ)^2 := sq_nonneg _
    nlinarith [mul_nonneg hs (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- Squared anti-concentration, avoiding square roots and all asymptotic notation. -/
theorem positiveLevel_square_bound (w : C → ℤ) (hw : ∀ c, 0 < w c) (a : ℤ) :
    ((positiveLevel w a).card : ℝ)^2 * ((Fintype.card C : ℝ) + 1) ≤
      (4 : ℝ)^(Fintype.card C) := by
  have hc : ((positiveLevel w a).card : ℝ) ≤
      ((Fintype.card C).choose (Fintype.card C / 2) : ℝ) := by
    exact_mod_cast positiveLevel_card_le w hw a
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  exact (mul_le_mul_of_nonneg_right hs (by positivity)).trans
    (middle_choose_square_bound (Fintype.card C))

/-- Complement precisely the coordinates with negative coefficient. -/
def flipNegative (z : C → ℤ) (S : Finset C) : Finset C :=
  univ.filter fun c => if z c < 0 then c ∉ S else c ∈ S

@[simp] theorem mem_flipNegative (z : C → ℤ) (S : Finset C) (c : C) :
    c ∈ flipNegative z S ↔ if z c < 0 then c ∉ S else c ∈ S := by
  simp only [flipNegative, mem_filter, mem_univ, true_and]

theorem flipNegative_involutive (z : C → ℤ) :
    Function.Involutive (flipNegative z) := by
  intro S
  ext c
  by_cases hc : z c < 0 <;> simp [hc]

/-- Changing signs is a bijection of the public Boolean sample space. -/
theorem flipNegative_sum (z : C → ℤ) (S : Finset C) :
    (∑ c ∈ flipNegative z S, |z c|) =
      (∑ c ∈ S, z c) - ∑ c, if z c < 0 then z c else 0 := by
  have hS : (∑ c ∈ S, z c) = ∑ c, if c ∈ S then z c else 0 :=
    (Finset.sum_ite_mem_eq S z).symm
  rw [flipNegative, sum_filter, hS, ← sum_sub_distrib]
  apply sum_congr rfl
  intro c _
  by_cases hz : z c < 0
  · by_cases hc : c ∈ S <;> simp [hz, hc, abs_of_neg hz]
  · by_cases hc : c ∈ S <;> simp [hz, hc, abs_of_nonneg (le_of_not_gt hz)]

/-- Littlewood--Offord counting for arbitrary nonzero integer coefficients,
proved by the explicit sign-changing bijection and Sperner's theorem. -/
theorem signedLevel_card_le (z : C → ℤ) (hz : ∀ c, z c ≠ 0) (a : ℤ) :
    (positiveLevel z a).card ≤ (Fintype.card C).choose (Fintype.card C / 2) := by
  have hmap : Set.MapsTo (flipNegative z) (positiveLevel z a)
      (positiveLevel (fun c => |z c|) (a - ∑ c, if z c < 0 then z c else 0)) := by
    intro S hS
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [flipNegative_sum, (mem_filter.mp hS).2]
  exact (card_le_card_of_injOn _ hmap
    (flipNegative_involutive z).injective.injOn).trans
      (positiveLevel_card_le _ (fun c => abs_pos.mpr (hz c)) _)

def nonzeroPart (z : C → ℤ) (S : Finset C) : Finset {c // z c ≠ 0} :=
  univ.filter fun c => c.1 ∈ S

def zeroPart (z : C → ℤ) (S : Finset C) : Finset {c // ¬z c ≠ 0} :=
  univ.filter fun c => c.1 ∈ S

theorem parts_injective (z : C → ℤ) :
    Function.Injective (fun S => (nonzeroPart z S, zeroPart z S)) := by
  intro S T h
  ext c
  by_cases hz : z c ≠ 0
  · have he := congrArg (fun p => (⟨c, hz⟩ : {c // z c ≠ 0}) ∈ p.1) h
    exact eq_iff_iff.mp (by simpa only [nonzeroPart, mem_filter, mem_univ, true_and] using he)
  · have he := congrArg (fun p => (⟨c, hz⟩ : {c // ¬z c ≠ 0}) ∈ p.2) h
    exact eq_iff_iff.mp (by simpa only [zeroPart, mem_filter, mem_univ, true_and] using he)

theorem nonzeroPart_sum (z : C → ℤ) (S : Finset C) :
    (∑ c ∈ nonzeroPart z S, z c.1) = ∑ c ∈ S, z c := by
  rw [nonzeroPart, sum_filter]
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun c => z c ≠ 0)
    (fun c => if c ∈ S then z c else (0 : ℤ))
  have hzero : (∑ c : {c // ¬z c ≠ 0}, if c.1 ∈ S then z c.1 else (0 : ℤ)) = 0 := by
    apply sum_eq_zero
    intro c _
    have hc : z c.1 = 0 := not_ne_iff.mp c.2
    simp [hc]
  rw [hzero, add_zero, Finset.sum_ite_mem_eq] at hsplit
  exact hsplit

/-- The unconstrained zero coordinates contribute exactly the Boolean
sample-space factor needed by the later finite union bound. -/
theorem collision_card_le (z : C → ℤ) (a : ℤ) :
    (positiveLevel z a).card ≤
      2 ^ (Fintype.card C - Fintype.card {c // z c ≠ 0}) *
        (Fintype.card {c // z c ≠ 0}).choose
          (Fintype.card {c // z c ≠ 0} / 2) := by
  let A := positiveLevel (fun c : {c // z c ≠ 0} => z c.1) a
  have hmap : Set.MapsTo (fun S => (nonzeroPart z S, zeroPart z S))
      (positiveLevel z a)
      (↑(A.product (univ : Finset (Finset {c // ¬z c ≠ 0}))) :
        Set (Finset {c // z c ≠ 0} × Finset {c // ¬z c ≠ 0})) := by
    intro S hS
    apply mem_product.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, mem_univ _⟩
    rw [nonzeroPart_sum]
    exact (mem_filter.mp hS).2
  have hi := card_le_card_of_injOn _ hmap (parts_injective z).injOn
  have hA : A.card ≤ (Fintype.card {c // z c ≠ 0}).choose
      (Fintype.card {c // z c ≠ 0} / 2) := signedLevel_card_le _ (fun c => c.2) a
  rw [Finset.product_eq_sprod, card_product, card_univ, Fintype.card_finset,
    Fintype.card_subtype_compl] at hi
  exact hi.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right _ hA)

/-- An exact normalized squared collision inequality. -/
theorem collision_square_bound (z : C → ℤ) (a : ℤ) :
    ((positiveLevel z a).card : ℝ)^2 *
        ((Fintype.card {c // z c ≠ 0} : ℝ) + 1) ≤
      (4 : ℝ)^(Fintype.card C) := by
  let r := Fintype.card {c // z c ≠ 0}
  let n := Fintype.card C
  have hrn : r ≤ n := Fintype.card_subtype_le _
  have hc : ((positiveLevel z a).card : ℝ) ≤
      (2 : ℝ)^(n-r) * (r.choose (r/2) : ℝ) := by
    exact_mod_cast collision_card_le z a
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  calc
    _ ≤ ((2 : ℝ)^(n-r) * (r.choose (r/2) : ℝ))^2 * ((r : ℝ)+1) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (4 : ℝ)^(n-r) * ((r.choose (r/2) : ℝ)^2 * ((r : ℝ)+1)) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm (n-r) 2, pow_mul]
      norm_num
      ring
    _ ≤ (4 : ℝ)^(n-r) * (4 : ℝ)^r :=
      mul_le_mul_of_nonneg_left (middle_choose_square_bound r) (by positivity)
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hrn]

private theorem sum_erase_indicator (z : C → ℤ) (S : Finset C) (c : C) :
    (∑ d ∈ S.erase c, z d) + (if c ∈ S then z c else 0) = ∑ d ∈ S, z d := by
  by_cases hc : c ∈ S
  · simpa only [if_pos hc] using sum_erase_add S z hc
  · simp [hc]

/-- Even a support of size one cuts the number of colliding tests in half. -/
theorem collision_card_le_half (z : C → ℤ) {c : C} (hc : z c ≠ 0) (a : ℤ) :
    (positiveLevel z a).card ≤ 2 ^ (Fintype.card C - 1) := by
  have hmap : Set.MapsTo (fun S : Finset C => S.erase c) (positiveLevel z a)
      ((univ.erase c).powerset) := by
    intro S _
    apply mem_powerset.mpr
    intro d hd
    exact mem_erase.mpr ⟨(mem_erase.mp hd).1, mem_univ _⟩
  have hinj : Set.InjOn (fun S : Finset C => S.erase c) (positiveLevel z a) := by
    intro S hS T hT he
    change S.erase c = T.erase c at he
    have hs := sum_erase_indicator z S c
    have ht := sum_erase_indicator z T c
    rw [(mem_filter.mp hS).2] at hs
    rw [(mem_filter.mp hT).2, ← he] at ht
    have hi : (if c ∈ S then z c else 0) = (if c ∈ T then z c else 0) := by
      linarith
    have hmem : c ∈ S ↔ c ∈ T := by
      by_cases hcS : c ∈ S <;> by_cases hcT : c ∈ T <;> simp_all
    ext d
    by_cases hd : d = c
    · simpa only [hd] using hmem
    · constructor
      · intro hdS
        have hm := mem_erase.mpr ⟨hd, hdS⟩
        rw [he] at hm
        exact (mem_erase.mp hm).2
      · intro hdT
        have hm := mem_erase.mpr ⟨hd, hdT⟩
        rw [← he] at hm
        exact (mem_erase.mp hm).2
  simpa only [card_powerset, card_erase_of_mem (mem_univ c), card_univ] using
    card_le_card_of_injOn _ hmap hinj

/-- Difference vectors, with duplicate pairs removed before the union bound. -/
def differences (A : Finset (C → ℕ)) : Finset (C → ℤ) :=
  ((A.product A).image fun p c => (p.1 c : ℤ) - (p.2 c : ℤ)).filter (· ≠ 0)

def badSchedules (z : C → ℤ) (q : ℕ) : Finset (Fin q → Finset C) :=
  Fintype.piFinset fun _ => positiveLevel z 0

@[simp] theorem badSchedules_card (z : C → ℤ) (q : ℕ) :
    (badSchedules z q).card = (positiveLevel z 0).card ^ q := by
  simp [badSchedules, Fintype.card_piFinset]

def scheduleFamily {q : ℕ} (T : Fin q → Finset C) : TestFamily C := univ.image T

theorem scheduleFamily_card_le {q : ℕ} (T : Fin q → Finset C) :
    (scheduleFamily T).card ≤ q := by
  exact (card_image_le).trans_eq (by simp)

/-- The finite union-bound step constructs an actual schedule, then deletes
duplicate tests. The premise is a concrete natural-number inequality, not a
separation or recovery oracle. -/
theorem exists_separating_of_collision_sum (A : Finset (C → ℕ)) (q : ℕ)
    (hcount : (∑ z ∈ differences A, (positiveLevel z 0).card ^ q) <
      (2 ^ Fintype.card C)^q) :
    ∃ F : TestFamily C, Separates F A ∧ F.card ≤ q := by
  let bad := (differences A).biUnion fun z => badSchedules z q
  have hb : bad.card < (univ : Finset (Fin q → Finset C)).card := by
    calc
      bad.card ≤ ∑ z ∈ differences A, (badSchedules z q).card := card_biUnion_le
      _ = ∑ z ∈ differences A, (positiveLevel z 0).card ^ q := by
        simp only [badSchedules_card]
      _ < (2 ^ Fintype.card C)^q := hcount
      _ = _ := by simp only [card_univ, Fintype.card_fun,
        Fintype.card_finset, Fintype.card_fin]
  obtain ⟨T, _, hT⟩ := exists_mem_notMem_of_card_lt_card hb
  refine ⟨scheduleFamily T, ?_, scheduleFamily_card_le T⟩
  intro x hx y hy he
  by_contra hxy
  let z : C → ℤ := fun c => (x c : ℤ) - (y c : ℤ)
  have hz0 : z ≠ 0 := by
    intro hz
    apply hxy
    funext c
    have hc : (x c : ℤ) - (y c : ℤ) = 0 := congrFun hz c
    exact_mod_cast sub_eq_zero.mp hc
  have hz : z ∈ differences A := mem_filter.mpr
    ⟨mem_image.mpr ⟨(x,y), mem_product.mpr ⟨hx,hy⟩, rfl⟩, hz0⟩
  apply hT
  apply mem_biUnion.mpr
  refine ⟨z, hz, Fintype.mem_piFinset.mpr ?_⟩
  intro j
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  have hj : T j ∈ scheduleFamily T := mem_image_of_mem _ (mem_univ j)
  have hsum : measure (T j) x = measure (T j) y := congrFun he ⟨T j,hj⟩
  change (∑ c ∈ T j, ((x c : ℤ) - (y c : ℤ))) = 0
  rw [sum_sub_distrib, sub_eq_zero]
  exact_mod_cast hsum

theorem minimumFamily_card_le_of_collision_sum (A : Finset (C → ℕ)) (q : ℕ)
    (hcount : (∑ z ∈ differences A, (positiveLevel z 0).card ^ q) <
      (2 ^ Fintype.card C)^q) : (minimumFamily A).card ≤ q := by
  obtain ⟨F,hF,hq⟩ := exists_separating_of_collision_sum A q hcount
  exact (minimumFamily_card_le hF).trans hq

def collisionRate (z : C → ℤ) : ℝ :=
  (positiveLevel z 0).card / (2 : ℝ)^(Fintype.card C)

theorem collisionRate_nonneg (z : C → ℤ) : 0 ≤ collisionRate z := by
  unfold collisionRate
  positivity

theorem collisionRate_le_half {z : C → ℤ} (hz : z ≠ 0) : collisionRate z ≤ 1/2 := by
  obtain ⟨c,hc⟩ : ∃ c, z c ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hz (funext hall)
  have hn : 1 ≤ Fintype.card C := Fintype.card_pos_iff.mpr ⟨c⟩
  have hcount := collision_card_le_half z hc 0
  have hnat : 2 * (positiveLevel z 0).card ≤ 2 ^ Fintype.card C := by
    calc
      _ ≤ 2 * 2^(Fintype.card C-1) := Nat.mul_le_mul_left _ hcount
      _ = 2^((Fintype.card C-1)+1) := by rw [pow_succ, Nat.mul_comm]
      _ = _ := by rw [Nat.sub_add_cancel hn]
  have hR : 2 * ((positiveLevel z 0).card : ℝ) ≤ (2 : ℝ)^Fintype.card C := by
    exact_mod_cast hnat
  apply (div_le_iff₀ (show (0 : ℝ) < 2^Fintype.card C by positivity)).mpr
  nlinarith

theorem collisionRate_square_bound (z : C → ℤ) :
    collisionRate z ^ 2 * ((Fintype.card {c // z c ≠ 0} : ℝ)+1) ≤ 1 := by
  have hp : (0 : ℝ) < 2^Fintype.card C := by positivity
  have he : ((2 : ℝ)^Fintype.card C)^2 = (4 : ℝ)^Fintype.card C := by
    rw [← pow_mul, Nat.mul_comm (Fintype.card C) 2, pow_mul]
    norm_num
  calc
    _ = (((positiveLevel z 0).card : ℝ)^2 *
          ((Fintype.card {c // z c ≠ 0} : ℝ)+1)) / ((2 : ℝ)^Fintype.card C)^2 := by
      unfold collisionRate
      ring
    _ ≤ (4 : ℝ)^Fintype.card C / ((2 : ℝ)^Fintype.card C)^2 :=
      div_le_div_of_nonneg_right (collision_square_bound z 0) (sq_nonneg _)
    _ = 1 := by rw [he]; exact div_self (by positivity)

theorem collisionRate_pow_le_half {z : C → ℤ} (hz : z ≠ 0) (q : ℕ) :
    collisionRate z ^ q ≤ Real.exp (-(q : ℝ)*Real.log 2) := by
  have he : Real.exp (-Real.log 2) = (1 : ℝ)/2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ)<2)]
    norm_num
  calc
    _ ≤ ((1 : ℝ)/2)^q := pow_le_pow_left₀ (collisionRate_nonneg z) (collisionRate_le_half hz) q
    _ = _ := by rw [← he, ← Real.exp_nat_mul]; congr 1; ring

theorem collisionRate_pow_le_support (z : C → ℤ) (q : ℕ) :
    collisionRate z ^ q ≤ Real.exp
      (-(q : ℝ)*Real.log ((Fintype.card {c // z c ≠ 0} : ℝ)+1)/2) := by
  let r := (Fintype.card {c // z c ≠ 0} : ℝ)+1
  let e := Real.exp (-Real.log r/2)
  have hr : 0 < r := by dsimp [r]; positivity
  have he : e^2 * r = 1 := by
    dsimp [e]
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show 2*(-Real.log r/2) = -Real.log r by ring, Real.exp_neg, Real.exp_log hr]
    exact inv_mul_cancel₀ hr.ne'
  have hc := collisionRate_square_bound z
  have hs : collisionRate z ^ 2 ≤ e^2 :=
    (mul_le_mul_iff_of_pos_right hr).mp (by simpa only [he] using hc)
  have hle : collisionRate z ≤ e := by
    have he0 : 0 < e := Real.exp_pos _
    nlinarith [collisionRate_nonneg z]
  calc
    _ ≤ e^q := pow_le_pow_left₀ (collisionRate_nonneg z) hle q
    _ = _ := by dsimp [e,r]; rw [← Real.exp_nat_mul]; congr 1; ring

theorem minimumFamily_card_le_of_rate_sum (A : Finset (C → ℕ)) (q : ℕ)
    (h : (∑ z ∈ differences A, collisionRate z ^ q) < 1) :
    (minimumFamily A).card ≤ q := by
  apply minimumFamily_card_le_of_collision_sum A q
  have he : (∑ z ∈ differences A, collisionRate z ^ q) =
      ((∑ z ∈ differences A, (positiveLevel z 0).card ^ q : ℕ) : ℝ) /
        ((2 : ℝ)^Fintype.card C)^q := by
    simp only [collisionRate, div_pow, sum_div, Nat.cast_sum, Nat.cast_pow]
  rw [he] at h
  have hh := (div_lt_one (show (0 : ℝ) < ((2 : ℝ)^Fintype.card C)^q by positivity)).mp h
  exact_mod_cast hh

/-- The explicit two-scale union estimate used for both dense and sparse
alphabets. Cardinality and arithmetic premises are discharged separately from
the real measurement construction; no hidden graph appears. -/
theorem collisionRate_sum_split (A : Finset (C → ℕ)) (q b S L : ℕ)
    (hsmall : ((differences A).filter
      (fun z => Fintype.card {c // z c ≠ 0} ≤ b)).card ≤ S)
    (hlarge : (differences A).card ≤ L) :
    (∑ z ∈ differences A, collisionRate z ^ q) ≤
      (S : ℝ)*Real.exp (-(q : ℝ)*Real.log 2) +
        (L : ℝ)*Real.exp (-(q : ℝ)*Real.log ((b : ℝ)+2)/2) := by
  let D := differences A
  let P := fun z : C → ℤ => Fintype.card {c // z c ≠ 0} ≤ b
  have hs : (∑ z ∈ D.filter P, collisionRate z ^ q) ≤
      (S : ℝ)*Real.exp (-(q : ℝ)*Real.log 2) := by
    calc
      _ ≤ ∑ _z ∈ D.filter P, Real.exp (-(q : ℝ)*Real.log 2) := by
        apply sum_le_sum
        intro z hz
        exact collisionRate_pow_le_half (mem_filter.mp (mem_filter.mp hz).1).2 q
      _ = ((D.filter P).card : ℝ)*Real.exp (-(q : ℝ)*Real.log 2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall) (Real.exp_pos _).le
  have hl : (∑ z ∈ D.filter (fun z => ¬P z), collisionRate z ^ q) ≤
      (L : ℝ)*Real.exp (-(q : ℝ)*Real.log ((b : ℝ)+2)/2) := by
    calc
      _ ≤ ∑ _z ∈ D.filter (fun z => ¬P z),
          Real.exp (-(q : ℝ)*Real.log ((b : ℝ)+2)/2) := by
        apply sum_le_sum
        intro z hz
        have hr : b+1 ≤ Fintype.card {c // z c ≠ 0} := by
          exact Nat.succ_le_iff.mpr (lt_of_not_ge
            (show ¬Fintype.card {c // z c ≠ 0} ≤ b from (mem_filter.mp hz).2))
        have hrR : (b : ℝ)+2 ≤ (Fintype.card {c // z c ≠ 0} : ℝ)+1 := by
          exact_mod_cast Nat.add_le_add_right hr 1
        apply (collisionRate_pow_le_support z q).trans
        apply Real.exp_le_exp.mpr
        have hlog := Real.log_le_log (by positivity : (0 : ℝ)<(b : ℝ)+2) hrR
        have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg q : (0 : ℝ)≤q)
        linarith
      _ = ((D.filter (fun z => ¬P z)).card : ℝ)*
          Real.exp (-(q : ℝ)*Real.log ((b : ℝ)+2)/2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (card_filter_le D (fun z => ¬P z)).trans hlarge)
        (Real.exp_pos _).le
  rw [← sum_filter_add_sum_filter_not D P]
  exact add_le_add hs hl

def signedAlphabet (d : ℕ) : Finset ℤ := Icc (-(d : ℤ)) d

@[simp] theorem signedAlphabet_card (d : ℕ) : (signedAlphabet d).card = 2*d+1 := by
  rw [signedAlphabet, Int.card_Icc]
  have he : (d : ℤ) + 1 - -(d : ℤ) = ((2*d+1 : ℕ) : ℤ) := by omega
  rw [he, Int.toNat_natCast]

def signedBox (C : Type) [Fintype C] [DecidableEq C] (d : ℕ) : Finset (C → ℤ) :=
  Fintype.piFinset fun _ => signedAlphabet d

@[simp] theorem signedBox_card (d : ℕ) :
    (signedBox C d).card = (2*d+1)^(Fintype.card C) := by
  simp [signedBox, Fintype.card_piFinset]

def signedOn (S : Finset C) (d : ℕ) : Finset (C → ℤ) :=
  Fintype.piFinset fun c => if c ∈ S then signedAlphabet d else {0}

theorem signedOn_card (S : Finset C) (d : ℕ) :
    (signedOn S d).card = (2*d+1)^S.card := by
  rw [signedOn, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, signedAlphabet_card, card_singleton]
  rw [Finset.prod_ite_mem_eq]
  simp only [prod_const]

def signedSmall (C : Type) [Fintype C] [DecidableEq C] (d b : ℕ) : Finset (C → ℤ) :=
  (range (b+1)).biUnion fun r =>
    ((univ : Finset C).powersetCard r).biUnion fun S => signedOn S d

theorem mem_signedSmall {d b : ℕ} {z : C → ℤ}
    (hz : z ∈ signedBox C d) (hs : Fintype.card {c // z c ≠ 0} ≤ b) :
    z ∈ signedSmall C d b := by
  let S := univ.filter fun c => z c ≠ 0
  have hc : S.card = Fintype.card {c // z c ≠ 0} := (Fintype.card_subtype _).symm
  apply mem_biUnion.mpr
  refine ⟨S.card, mem_range.mpr (by omega), mem_biUnion.mpr ?_⟩
  refine ⟨S, mem_powersetCard.mpr ⟨subset_univ _, rfl⟩, Fintype.mem_piFinset.mpr ?_⟩
  intro c
  by_cases hcS : c ∈ S
  · simpa only [if_pos hcS] using Fintype.mem_piFinset.mp hz c
  · have hzero : z c = 0 := by simpa only [S, mem_filter, mem_univ, true_and, not_not] using hcS
    simp only [if_neg hcS, mem_singleton, hzero]

/-- A support-sensitive finite enumeration bound. The alphabet includes zero;
overcounting it is harmless and avoids any implicit coding oracle. -/
theorem signedSmall_card_le (d b : ℕ) (hn : 1 ≤ Fintype.card C) :
    (signedSmall C d b).card ≤ (b+1) * (Fintype.card C * (2*d+1))^b := by
  let n := Fintype.card C
  have hbase : 1 ≤ n * (2*d+1) := by dsimp [n]; nlinarith
  calc
    _ ≤ ∑ r ∈ range (b+1),
        (((univ : Finset C).powersetCard r).biUnion fun S => signedOn S d).card :=
      card_biUnion_le
    _ ≤ ∑ r ∈ range (b+1),
        ∑ S ∈ (univ : Finset C).powersetCard r, (signedOn S d).card := by
      apply sum_le_sum
      intro r _
      exact card_biUnion_le
    _ = ∑ r ∈ range (b+1), n.choose r * (2*d+1)^r := by
      apply sum_congr rfl
      intro r _
      calc
        _ = ∑ _S ∈ (univ : Finset C).powersetCard r, (2*d+1)^r := by
          apply sum_congr rfl
          intro S hS
          rw [signedOn_card, (mem_powersetCard.mp hS).2]
        _ = _ := by simp [n, Nat.mul_comm]
    _ ≤ ∑ r ∈ range (b+1), (n * (2*d+1))^b := by
      apply sum_le_sum
      intro r hr
      calc
        n.choose r * (2*d+1)^r ≤ n^r * (2*d+1)^r :=
          Nat.mul_le_mul_right _ (Nat.choose_le_pow n r)
        _ = (n * (2*d+1))^r := (Nat.mul_pow _ _ _).symm
        _ ≤ _ := Nat.pow_le_pow_right hbase (Nat.le_of_lt_succ (mem_range.mp hr))
    _ = _ := by simp [n, Nat.mul_comm]

theorem differences_box_subset (d : ℕ) :
    differences (box C d) ⊆ signedBox C d := by
  intro z hz
  obtain ⟨p,hp,rfl⟩ := mem_image.mp (mem_filter.mp hz).1
  have hx := mem_box.mp (mem_product.mp hp).1
  have hy := mem_box.mp (mem_product.mp hp).2
  apply Fintype.mem_piFinset.mpr
  intro c
  apply mem_Icc.mpr
  constructor <;> have := hx c <;> have := hy c <;> omega

theorem differences_box_card_le (d : ℕ) :
    (differences (box C d)).card ≤ (2*d+1)^(Fintype.card C) := by
  simpa only [signedBox_card] using card_le_card (differences_box_subset (C := C) d)

theorem boolean_support_card {x : C → ℕ} (hx : ∀ c, x c ≤ 1) :
    (univ.filter fun c => x c ≠ 0).card = measure univ x := by
  rw [card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro c _
  by_cases hc : x c = 0
  · simp [hc]
  · have hc1 : x c = 1 := by have := hx c; omega
    simp [hc1]

theorem differences_sparse_support {ell : ℕ} {z : C → ℤ}
    (hz : z ∈ differences (sparse C ell)) :
    z ∈ signedBox C 1 ∧ Fintype.card {c // z c ≠ 0} ≤ min (2*ell) (Fintype.card C) := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp (mem_filter.mp hz).1
  obtain ⟨hx,hxm⟩ := mem_sparse.mp (mem_product.mp hp).1
  obtain ⟨hy,hym⟩ := mem_sparse.mp (mem_product.mp hp).2
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro c
    apply mem_Icc.mpr
    constructor <;> have := hx c <;> have := hy c <;> omega
  · apply le_min
    · rw [Fintype.card_subtype]
      have hsub : (univ.filter fun c => (p.1 c : ℤ) - (p.2 c : ℤ) ≠ 0) ⊆
          (univ.filter fun c => p.1 c ≠ 0) ∪ (univ.filter fun c => p.2 c ≠ 0) := by
        intro c hc
        have hz := (mem_filter.mp hc).2
        by_cases hc1 : p.1 c = 0
        · apply mem_union_right
          apply mem_filter.mpr
          refine ⟨mem_univ _, ?_⟩
          intro hc2
          simp [hc1,hc2] at hz
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hc1⟩)
      calc
        _ ≤ ((univ.filter fun c => p.1 c ≠ 0) ∪
            (univ.filter fun c => p.2 c ≠ 0)).card := card_le_card hsub
        _ ≤ (univ.filter fun c => p.1 c ≠ 0).card +
            (univ.filter fun c => p.2 c ≠ 0).card := card_union_le _ _
        _ = measure univ p.1 + measure univ p.2 := by
          rw [boolean_support_card hx, boolean_support_card hy]
        _ ≤ _ := by omega
    · exact Fintype.card_subtype_le _

theorem differences_sparse_card_le (ell : ℕ) (hn : 1 ≤ Fintype.card C) :
    (differences (sparse C ell)).card ≤
      (min (2*ell) (Fintype.card C)+1) *
        (3*Fintype.card C)^(min (2*ell) (Fintype.card C)) := by
  have hsub : differences (sparse C ell) ⊆
      signedSmall C 1 (min (2*ell) (Fintype.card C)) := by
    intro z hz
    obtain ⟨hbox,hs⟩ := differences_sparse_support hz
    exact mem_signedSmall hbox hs
  exact (card_le_card hsub).trans (by
    simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.mul_comm] using
      signedSmall_card_le (C := C) 1 (min (2*ell) (Fintype.card C)) hn)

/-- Explicit constants for the logarithmic estimates: no unnamed asymptotic
threshold is used to handle a bounded number of rows. -/
theorem log_double_bounds {x : ℝ} (hx : 1 ≤ x) :
    (Real.log (2*x))^2 ≤ 16 * Real.sqrt x ∧
      Real.log (2*x) ≤ 4 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have h2x : 0 < 2*x := by linarith
  have hl : 0 ≤ Real.log (2*x) := Real.log_nonneg (by linarith)
  have hh : 0 ≤ Real.log (2*x)/2 := by positivity
  have hsq := Real.pow_div_factorial_le_exp (Real.log (2*x)/2) hh 2
  have hlin := Real.pow_div_factorial_le_exp (Real.log (2*x)/2) hh 1
  rw [Real.exp_half, Real.exp_log h2x] at hsq hlin
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, pow_one,
    div_one] at hsq hlin
  have hs0 := Real.sqrt_nonneg x
  have hs20 := Real.sqrt_nonneg (2*x)
  have hs := Real.sq_sqrt hx0
  have hs2 := Real.sq_sqrt h2x.le
  have hbound : Real.sqrt (2*x) ≤ 2 * Real.sqrt x := by nlinarith
  constructor <;> nlinarith

theorem log_double_mixed_bound {x u : ℝ} (hx : 1 ≤ x) (hu : 1/2 ≤ u) :
    Real.log (2*x) * (Real.log (2*x) + u) ≤ 36 * Real.sqrt x * u := by
  obtain ⟨hs,hl⟩ := log_double_bounds hx
  have hsqrt := Real.sqrt_nonneg x
  have hmul := mul_le_mul_of_nonneg_right hl (show 0 ≤ u by linarith)
  have hscale := mul_nonneg hsqrt (show 0 ≤ u - 1/2 by linarith)
  nlinarith

def denseSampleCount (n d : ℕ) : ℕ :=
  ⌈4096 * (n : ℝ) * Real.log (2*(d : ℝ)+1) / Real.log (2*(n : ℝ))⌉₊

theorem denseSampleCount_mul_log (n d : ℕ) (hn : 1 ≤ n) :
    4096 * (n : ℝ) * Real.log (2*(d : ℝ)+1) ≤
      (denseSampleCount n d : ℝ) * Real.log (2*(n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log (2*(n : ℝ)) := Real.log_pos (by linarith)
  exact (div_le_iff₀ hl).mp (Nat.le_ceil _)

/-- The small-support entropy is paid for by half the dense sample exponent. -/
theorem denseSampleCount_small_entropy (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    4 * Real.sqrt (n : ℝ) *
        (Real.log (2*(n : ℝ)) + Real.log (2*(d : ℝ)+1)) ≤
      (denseSampleCount n d : ℝ) * Real.log 2 := by
  let w := Real.log (2*(n : ℝ))
  let u := Real.log (2*(d : ℝ)+1)
  let q := (denseSampleCount n d : ℝ)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hw : 0 < w := Real.log_pos (by linarith)
  have hu : 1/2 ≤ u := by
    have h2 : Real.log 2 ≤ u := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  have hnu : 0 ≤ (n : ℝ)*u := mul_nonneg (by positivity) (by linarith)
  have hm := log_double_mixed_bound hnR hu
  have hms := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4*Real.sqrt (n : ℝ) by positivity)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hq := denseSampleCount_mul_log n d hn
  change 4096 * (n : ℝ) * u ≤ q*w at hq
  have he : (4*Real.sqrt (n : ℝ)*(w+u))*w ≤ (q/2)*w := by
    dsimp only [w, u] at hq ⊢
    nlinarith
  have hhalf : 4*Real.sqrt (n : ℝ)*(w+u) ≤ q/2 :=
    (mul_le_mul_iff_of_pos_right hw).mp he
  have hlog2 : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  exact hhalf.trans (by nlinarith [mul_le_mul_of_nonneg_left hlog2 hq0])

theorem small_count_exponential (n d : ℕ) (hn : 1 ≤ n) :
    (((n.sqrt+1)*(n*(2*d+1))^n.sqrt : ℕ) : ℝ) ≤
      Real.exp (2*Real.sqrt (n : ℝ)*
        (Real.log (2*(n : ℝ)) + Real.log (2*(d : ℝ)+1))) := by
  have hs := Nat.sqrt_le_self n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : n*(2*d+1) ≤ 2*n*(2*d+1) := by nlinarith
  have hfac : n.sqrt+1 ≤ 2*n*(2*d+1) := by nlinarith
  have hcount : (n.sqrt+1)*(n*(2*d+1))^n.sqrt ≤
      (2*n*(2*d+1))^(n.sqrt+1) := by
    calc
      _ ≤ (2*n*(2*d+1))*(2*n*(2*d+1))^n.sqrt :=
        Nat.mul_le_mul hfac (Nat.pow_le_pow_left hbase _)
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  have hsr : (n.sqrt : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n)
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hnR
  have hlog : Real.log (2*(n : ℝ)*(2*(d : ℝ)+1)) =
      Real.log (2*(n : ℝ)) + Real.log (2*(d : ℝ)+1) :=
    Real.log_mul (by positivity) (by positivity)
  have hbpos : 0 < 2*(n : ℝ)*(2*(d : ℝ)+1) := by positivity
  have hlnpos : 0 ≤ Real.log (2*(n : ℝ)*(2*(d : ℝ)+1)) :=
    Real.log_nonneg (by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  calc
    _ ≤ (2*(n : ℝ)*(2*(d : ℝ)+1))^(n.sqrt+1) := by exact_mod_cast hcount
    _ = Real.exp (((n.sqrt+1 : ℕ) : ℝ)*Real.log (2*(n : ℝ)*(2*(d : ℝ)+1))) := by
      rw [Real.exp_nat_mul, Real.exp_log hbpos]
    _ ≤ Real.exp (2*Real.sqrt (n : ℝ)*Real.log (2*(n : ℝ)*(2*(d : ℝ)+1))) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ hlnpos
      push_cast
      linarith
    _ = _ := by rw [hlog]

theorem sqrt_support_log_lower (n : ℕ) (hn : 2 ≤ n) :
    Real.log (2*(n : ℝ)) ≤ 4*Real.log ((n.sqrt : ℝ)+2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpower : (n : ℝ) ≤ ((n.sqrt : ℝ)+2)^2 := by
    have h := Nat.lt_succ_sqrt' n
    have hR : (n : ℝ) < ((n.sqrt : ℝ)+1)^2 := by exact_mod_cast h
    nlinarith [(Nat.cast_nonneg n.sqrt : (0 : ℝ) ≤ n.sqrt)]
  have hl := Real.log_le_log (by linarith : (0 : ℝ)<n) hpower
  rw [Real.log_pow] at hl
  have h2 := Real.log_le_log (by norm_num : (0 : ℝ)<2) hnR
  rw [Real.log_mul (by norm_num) (by positivity)]
  norm_num only [Nat.cast_ofNat] at hl
  linarith

/-- A completely specified finite sample count suffices for dense bounded
vectors. The proof constructs the good family through the collision sum. -/
theorem minimumFamily_box_card_le_samples (d : ℕ)
    (hn : 2 ≤ Fintype.card C) (hd : 1 ≤ d) :
    (minimumFamily (box C d)).card ≤ denseSampleCount (Fintype.card C) d := by
  let n := Fintype.card C
  let q := denseSampleCount n d
  let b := n.sqrt
  let S := (b+1)*(n*(2*d+1))^b
  let L := (2*d+1)^n
  let w := Real.log (2*(n : ℝ))
  let u := Real.log (2*(d : ℝ)+1)
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hw : 1/2 ≤ w := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ)<2) (show 2 ≤ 2*(n : ℝ) by linarith)
    linarith [Real.log_two_gt_d9]
  have hu : 1/2 ≤ u := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ)<2) (show 2 ≤ 2*(d : ℝ)+1 by linarith)
    linarith [Real.log_two_gt_d9]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ)≤n by linarith)
  have hnu : 1 ≤ (n : ℝ)*u := by nlinarith
  have hsmall : ((differences (box C d)).filter
      (fun z => Fintype.card {c // z c ≠ 0} ≤ b)).card ≤ S := by
    have hsub : (differences (box C d)).filter
        (fun z => Fintype.card {c // z c ≠ 0} ≤ b) ⊆ signedSmall C d b := by
      intro z hz
      exact mem_signedSmall (differences_box_subset d (mem_filter.mp hz).1) (mem_filter.mp hz).2
    exact (card_le_card hsub).trans (signedSmall_card_le d b hn1)
  have hsmallExp : (S : ℝ)*Real.exp (-(q : ℝ)*Real.log 2) ≤ Real.exp (-2) := by
    have he := small_count_exponential n d hn1
    have hq := denseSampleCount_small_entropy n d hn1 hd
    calc
      _ ≤ Real.exp (2*Real.sqrt (n : ℝ)*(w+u))*Real.exp (-(q : ℝ)*Real.log 2) :=
        mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = Real.exp (2*Real.sqrt (n : ℝ)*(w+u)-(q : ℝ)*Real.log 2) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        change 4*Real.sqrt (n : ℝ)*(w+u) ≤ (q : ℝ)*Real.log 2 at hq
        nlinarith
  have hlargeExp : (L : ℝ)*Real.exp (-(q : ℝ)*Real.log ((b : ℝ)+2)/2) ≤
      Real.exp (-2) := by
    have hq := denseSampleCount_mul_log n d hn1
    have hb := sqrt_support_log_lower n hn
    have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg q : (0 : ℝ)≤q)
    have hLe : (L : ℝ) = Real.exp ((n : ℝ)*u) := by
      dsimp [L,u]
      push_cast
      rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    rw [hLe, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change 4096*(n : ℝ)*u ≤ (q : ℝ)*w at hq
    change (q : ℝ)*w ≤ (q : ℝ)*(4*Real.log ((b : ℝ)+2)) at hm
    nlinarith
  have he : 2*Real.exp (-2) < 1 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    rw [Real.exp_neg]
    have he2 := Real.exp_pos (2 : ℝ)
    have hhalf : (Real.exp (2 : ℝ))⁻¹ < 1/2 := by
      rw [inv_eq_one_div]
      apply (div_lt_iff₀ he2).mpr
      linarith
    linarith
  apply minimumFamily_card_le_of_rate_sum (box C d) q
  exact (collisionRate_sum_split (box C d) q b S L hsmall
    (differences_box_card_le d)).trans_lt
      ((add_le_add hsmallExp hlargeExp).trans_lt (by simpa only [two_mul] using he))

theorem denseSampleCount_bound (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (denseSampleCount n d : ℝ) ≤
      16384*(n : ℝ)*Real.log ((d : ℝ)+1)/Real.log (2*(n : ℝ)) := by
  let w := Real.log (2*(n : ℝ))
  let v := Real.log ((d : ℝ)+1)
  let F := (n : ℝ)*v/w
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hw : 0 < w := Real.log_pos (by linarith)
  have hv : 1/2 ≤ v := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ)<2) (show 2 ≤ (d : ℝ)+1 by linarith)
    linarith [Real.log_two_gt_d9]
  have hwle : w ≤ 2*(n : ℝ) := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hF : 1/4 ≤ F := by
    apply (le_div_iff₀ hw).mpr
    nlinarith
  have hlog : Real.log (2*(d : ℝ)+1) ≤ 2*v := by
    have h := Real.log_le_log (by positivity : (0 : ℝ)<2*(d : ℝ)+1)
      (show 2*(d : ℝ)+1 ≤ ((d : ℝ)+1)^2 by nlinarith)
    rw [Real.log_pow] at h
    exact h
  have hceil := (Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ 4096*(n : ℝ)*Real.log (2*(d : ℝ)+1)/w by
      apply div_nonneg
      · exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
      · exact hw.le)).le
  change (denseSampleCount n d : ℝ) ≤
    4096*(n : ℝ)*Real.log (2*(d : ℝ)+1)/w+1 at hceil
  have hratio : 4096*(n : ℝ)*Real.log (2*(d : ℝ)+1)/w ≤ 8192*F := by
    calc
      _ ≤ 4096*(n : ℝ)*(2*v)/w :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) hw.le
      _ = _ := by dsimp [F]; ring
  have hfinal : (denseSampleCount n d : ℝ) ≤ 16384*F := by linarith
  simpa only [F, w, v, mul_div_assoc, mul_assoc] using hfinal

def sparseSampleCount (n K : ℕ) : ℕ :=
  ⌈64*(K : ℝ)*Real.log (6*(n : ℝ))/Real.log ((K : ℝ)+1)⌉₊

theorem sparseSampleCount_mul_log (n K : ℕ) (hK : 1 ≤ K) :
    64*(K : ℝ)*Real.log (6*(n : ℝ)) ≤
      (sparseSampleCount n K : ℝ)*Real.log ((K : ℝ)+1) := by
  have hKR : (1 : ℝ)≤K := by exact_mod_cast hK
  exact (div_le_iff₀ (Real.log_pos (by linarith))).mp (Nat.le_ceil _)

theorem sparseSampleCount_small_entropy (n K : ℕ) (hn : 1 ≤ n) (hK : 1 ≤ K) :
    4*Real.sqrt (K : ℝ)*Real.log (6*(n : ℝ)) ≤
      (sparseSampleCount n K : ℝ)*Real.log 2 := by
  let v := Real.log ((K : ℝ)+1)
  let h := Real.log (6*(n : ℝ))
  let q := (sparseSampleCount n K : ℝ)
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn
  have hKR : (1 : ℝ)≤K := by exact_mod_cast hK
  have hv : 0 < v := Real.log_pos (by linarith)
  have hh : 0 ≤ h := Real.log_nonneg (by linarith)
  have hvl : v ≤ 4*Real.sqrt (K : ℝ) := by
    exact (Real.log_le_log (by positivity) (show (K : ℝ)+1 ≤ 2*K by linarith)).trans
      (log_double_bounds hKR).2
  have hq := sparseSampleCount_mul_log n K hK
  change 64*(K : ℝ)*h ≤ q*v at hq
  have hm := mul_le_mul_of_nonneg_left hvl
    (show 0 ≤ 4*Real.sqrt (K : ℝ)*h by positivity)
  have hs := Real.sq_sqrt (Nat.cast_nonneg K : (0 : ℝ)≤K)
  have hKh : 0 ≤ (K : ℝ)*h := mul_nonneg (Nat.cast_nonneg _) hh
  have he : (4*Real.sqrt (K : ℝ)*h)*v ≤ (q/2)*v := by nlinarith
  have hhalf := (mul_le_mul_iff_of_pos_right hv).mp he
  have hlog2 : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  exact hhalf.trans (by nlinarith [mul_le_mul_of_nonneg_left hlog2 hq0])

theorem support_log_plus_one_lower (K : ℕ) :
    Real.log ((K : ℝ)+1) ≤ 2*Real.log ((K.sqrt : ℝ)+2) := by
  have hK : K+1 ≤ (K.sqrt+2)^2 := by
    have h := Nat.lt_succ_sqrt' K
    simp only [Nat.succ_eq_add_one] at h
    exact (Nat.succ_le_of_lt h).trans
      (Nat.pow_le_pow_left (show K.sqrt+1 ≤ K.sqrt+2 by omega) 2)
  have h := Real.log_le_log (by positivity : (0 : ℝ)<(K : ℝ)+1)
    (show (K : ℝ)+1 ≤ ((K.sqrt : ℝ)+2)^2 by exact_mod_cast hK)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem sparse_count_exponential (n b : ℕ) (hn : 1 ≤ n) (hb : b ≤ n) :
    (((b+1)*(3*n)^b : ℕ) : ℝ) ≤ Real.exp (((b+1 : ℕ) : ℝ)*Real.log (6*(n : ℝ))) := by
  have hnat : (b+1)*(3*n)^b ≤ (6*n)^(b+1) := by
    calc
      _ ≤ (6*n)*(6*n)^b := Nat.mul_le_mul (by omega)
        (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by rw [pow_succ,Nat.mul_comm]
  calc
    _ ≤ (6*(n : ℝ))^(b+1) := by exact_mod_cast hnat
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by positivity)]

/-- The sparse efficient family is also a consequence of a finite good-schedule
count. All row/column dimensions and the support cap are public parameters. -/
theorem minimumFamily_sparse_card_le_samples (ell : ℕ)
    (hn : 1 ≤ Fintype.card C) (hell : 1 ≤ ell) :
    (minimumFamily (sparse C ell)).card ≤
      sparseSampleCount (Fintype.card C) (min (2*ell) (Fintype.card C)) := by
  let n := Fintype.card C
  let K := min (2*ell) n
  let b := K.sqrt
  let q := sparseSampleCount n K
  let S := (b+1)*(3*n)^b
  let L := (K+1)*(3*n)^K
  let h := Real.log (6*(n : ℝ))
  let v := Real.log ((K : ℝ)+1)
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hKn : K ≤ n := min_le_right _ _
  have hbn : b ≤ n := (Nat.sqrt_le_self K).trans hKn
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn
  have hKR : (1 : ℝ)≤K := by exact_mod_cast hK
  have hh : 1 ≤ h := by
    have he : Real.exp 1 ≤ 6*(n : ℝ) := by linarith [Real.exp_one_lt_three]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr he
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (K : ℝ) := by simpa using Real.sqrt_le_sqrt hKR
  have hbr : (b : ℝ)+1 ≤ 2*Real.sqrt (K : ℝ) := by
    have hb0 : (b : ℝ) ≤ Real.sqrt (K : ℝ) :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' K)
    linarith
  have hsmall : ((differences (sparse C ell)).filter
      (fun z => Fintype.card {c // z c ≠ 0} ≤ b)).card ≤ S := by
    have hsub : (differences (sparse C ell)).filter
        (fun z => Fintype.card {c // z c ≠ 0} ≤ b) ⊆ signedSmall C 1 b := by
      intro z hz
      exact mem_signedSmall (differences_sparse_support (mem_filter.mp hz).1).1
        (mem_filter.mp hz).2
    exact (card_le_card hsub).trans (by
      simpa only [S,n,Nat.reduceMul,Nat.reduceAdd,Nat.mul_comm] using signedSmall_card_le (C := C) 1 b hn)
  have hsmallExp : (S : ℝ)*Real.exp (-(q : ℝ)*Real.log 2) ≤ Real.exp (-2) := by
    have he := sparse_count_exponential n b hn hbn
    have hq := sparseSampleCount_small_entropy n K hn hK
    have hbc : ((b+1 : ℕ) : ℝ)*h ≤ 2*Real.sqrt (K : ℝ)*h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hbr) (by linarith)
    calc
      _ ≤ Real.exp (((b+1 : ℕ) : ℝ)*h)*Real.exp (-(q : ℝ)*Real.log 2) :=
        mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = Real.exp (((b+1 : ℕ) : ℝ)*h-(q : ℝ)*Real.log 2) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        change 4*Real.sqrt (K : ℝ)*h ≤ (q : ℝ)*Real.log 2 at hq
        nlinarith
  have hlargeExp : (L : ℝ)*Real.exp (-(q : ℝ)*Real.log ((b : ℝ)+2)/2) ≤ Real.exp (-2) := by
    have he := sparse_count_exponential n K hn hKn
    have hq := sparseSampleCount_mul_log n K hK
    have hl := support_log_plus_one_lower K
    have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg q : (0 : ℝ)≤q)
    calc
      _ ≤ Real.exp (((K+1 : ℕ) : ℝ)*h)*Real.exp (-(q : ℝ)*Real.log ((b : ℝ)+2)/2) :=
        mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = Real.exp (((K+1 : ℕ) : ℝ)*h-(q : ℝ)*Real.log ((b : ℝ)+2)/2) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        change 64*(K : ℝ)*h ≤ (q : ℝ)*v at hq
        change (q : ℝ)*v ≤ (q : ℝ)*(2*Real.log ((b : ℝ)+2)) at hm
        push_cast
        nlinarith
  have he : 2*Real.exp (-2) < 1 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    rw [Real.exp_neg]
    have hhalf : (Real.exp (2 : ℝ))⁻¹ < 1/2 := by
      rw [inv_eq_one_div]
      apply (div_lt_iff₀ (Real.exp_pos _)).mpr
      linarith
    linarith
  apply minimumFamily_card_le_of_rate_sum (sparse C ell) q
  exact (collisionRate_sum_split (sparse C ell) q b S L hsmall
    (differences_sparse_card_le ell hn)).trans_lt
      ((add_le_add hsmallExp hlargeExp).trans_lt (by simpa only [two_mul] using he))

/-- Monotonicity needed when the sparsity cap is clipped to the dimension.
This algebraic logarithm proof avoids an asymptotic comparison or derivative
assumption in the public family-size theorem. -/
theorem log_one_add_ratio {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    b*Real.log (a+1) ≤ a*Real.log (b+1) := by
  have hb1 : 0 < b+1 := by linarith
  have ha1 : 0 < a+1 := by linarith
  have hlow : b/(b+1) ≤ Real.log (b+1) := by
    have h := Real.one_sub_inv_le_log_of_pos hb1
    have he : 1-(b+1)⁻¹ = b/(b+1) := by field_simp; ring
    rwa [he] at h
  have hdiff : Real.log (a+1)-Real.log (b+1) ≤ (a-b)/(b+1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos ha1 hb1)
    rw [Real.log_div ha1.ne' hb1.ne'] at h
    have he : (a+1)/(b+1)-1 = (a-b)/(b+1) := by field_simp; ring
    rwa [he] at h
  have h1 := mul_le_mul_of_nonneg_left hdiff hb
  have h2 := mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr hab)
  have he : b*((a-b)/(b+1)) = (a-b)*(b/(b+1)) := by ring
  rw [he] at h1
  nlinarith

theorem sparseSampleCount_bound (n ell : ℕ) (hell : 1 ≤ ell) (heln : ell ≤ n) :
    (sparseSampleCount n (min (2*ell) n) : ℝ) ≤
      1024*(ell : ℝ)*Real.log (2*(n : ℝ))/Real.log (2*(ell : ℝ)) := by
  let K := min (2*ell) n
  let v := Real.log ((K : ℝ)+1)
  let w := Real.log (2*(ell : ℝ))
  let h := Real.log (2*(n : ℝ))
  let F := (ell : ℝ)*h/w
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hKR : (1 : ℝ)≤K := by exact_mod_cast hK
  have hellR : (1 : ℝ)≤ell := by exact_mod_cast hell
  have hnR : (ell : ℝ)≤n := by exact_mod_cast heln
  have hv : 0 < v := Real.log_pos (by linarith)
  have hw : 0 < w := Real.log_pos (by linarith)
  have hh : w ≤ h := Real.log_le_log (by positivity) (by linarith)
  have hF : 1 ≤ F := by
    apply (le_div_iff₀ hw).mpr
    nlinarith
  have hKle : (K : ℝ)≤2*(ell : ℝ) := by exact_mod_cast min_le_left (2*ell) n
  have hratio : (K : ℝ)*w ≤ 2*(ell : ℝ)*v := by
    have hlog := Real.log_le_log (by positivity : (0 : ℝ)<2*(ell : ℝ))
      (show 2*(ell : ℝ)≤2*(ell : ℝ)+1 by linarith)
    exact (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
      (log_one_add_ratio (by positivity) hKle)
  have hquot : (K : ℝ)/v ≤ 2*(ell : ℝ)/w :=
    (div_le_div_iff₀ hv hw).mpr hratio
  have hlog6 : Real.log (6*(n : ℝ)) ≤ 3*h := by
    have hn1 : (1 : ℝ) ≤ n := hellR.trans hnR
    have hn2 : (1 : ℝ) ≤ (n : ℝ)^2 := one_le_pow₀ hn1
    have hn3 := mul_le_mul_of_nonneg_left hn2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hpow : 6*(n : ℝ) ≤ (2*(n : ℝ))^3 := by nlinarith
    have he := Real.log_le_log (by linarith : (0 : ℝ)<6*(n : ℝ)) hpow
    simpa only [Real.log_pow, Nat.cast_ofNat] using he
  have hlog60 : 0 ≤ Real.log (6*(n : ℝ)) := Real.log_nonneg (by linarith)
  have hc := (Nat.ceil_lt_add_one
    (show (0 : ℝ)≤64*(K : ℝ)*Real.log (6*(n : ℝ))/v by positivity)).le
  change (sparseSampleCount n K : ℝ) ≤ 64*(K : ℝ)*Real.log (6*(n : ℝ))/v+1 at hc
  have hmain : 64*(K : ℝ)*Real.log (6*(n : ℝ))/v ≤ 384*F := by
    calc
      _ = 64*((K : ℝ)/v)*Real.log (6*(n : ℝ)) := by ring
      _ ≤ 64*(2*(ell : ℝ)/w)*Real.log (6*(n : ℝ)) := by gcongr
      _ ≤ 64*(2*(ell : ℝ)/w)*(3*h) := by gcongr
      _ = _ := by dsimp [F]; ring
  have hf : (sparseSampleCount n K : ℝ) ≤ 1024*F := by linarith
  simpa only [K,F,h,w,mul_div_assoc,mul_assoc] using hf

/-- Public row and column labels, with no graph stored in the measurement type. -/
abbrev BooleanMatrix (R C : Type) := R → C → Bool

abbrev BipartiteQuery (R C : Type) := Finset R × Finset C

def bilinear {R : Type} (M : BooleanMatrix R C) (q : BipartiteQuery R C) : ℕ :=
  ∑ r ∈ q.1, ∑ c ∈ q.2, if M r c then 1 else 0

def rowVector {R : Type} (M : BooleanMatrix R C) (r : R) : C → ℕ :=
  fun c => if M r c then 1 else 0

def RowSparse {R : Type} (ell : ℕ) (M : BooleanMatrix R C) : Prop :=
  ∀ r, measure univ (rowVector M r) ≤ ell

def denseFamily (R : Type) [Fintype R] [DecidableEq R] (ell : ℕ) : TestFamily R :=
  minimumFamily (box R ell)

def sparseFamily (C : Type) [Fintype C] [DecidableEq C] (ell : ℕ) : TestFamily C :=
  minimumFamily (sparse C ell)

theorem denseFamily_card_bound (R : Type) [Fintype R] [DecidableEq R] (ell : ℕ)
    (hR : 1 ≤ Fintype.card R) (hell : 1 ≤ ell) :
    ((denseFamily R ell).card : ℝ) ≤
      16384*(Fintype.card R : ℝ)*Real.log ((ell : ℝ)+1)/
        Real.log (2*(Fintype.card R : ℝ)) := by
  by_cases hR2 : 2 ≤ Fintype.card R
  · have hnat := minimumFamily_box_card_le_samples (C := R) ell hR2 hell
    exact (show ((denseFamily R ell).card : ℝ) ≤ denseSampleCount (Fintype.card R) ell by
      exact_mod_cast hnat).trans (denseSampleCount_bound _ _ hR hell)
  · have hcard : Fintype.card R = 1 := by omega
    have hdim : ((denseFamily R ell).card : ℝ) ≤ 1 := by
      exact_mod_cast (minimumFamily_card_le_dimension (box R ell)).trans_eq hcard
    have hellR : (1 : ℝ)≤ell := by exact_mod_cast hell
    have hlog : Real.log 2 ≤ Real.log ((ell : ℝ)+1) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hcard]
    norm_num only [Nat.cast_one, mul_one]
    apply hdim.trans
    apply (le_div_iff₀ hlpos).mpr
    nlinarith

theorem sparseFamily_card_bound (ell : ℕ) (hell : 1 ≤ ell) (heln : ell ≤ Fintype.card C) :
    ((sparseFamily C ell).card : ℝ) ≤
      1024*(ell : ℝ)*Real.log (2*(Fintype.card C : ℝ))/Real.log (2*(ell : ℝ)) := by
  have hn := hell.trans heln
  have hnat := minimumFamily_sparse_card_le_samples (C := C) ell hn hell
  exact (show ((sparseFamily C ell).card : ℝ) ≤
      sparseSampleCount (Fintype.card C) (min (2*ell) (Fintype.card C)) by
    exact_mod_cast hnat).trans (sparseSampleCount_bound _ _ hell heln)

abbrev SparseMeasurementIndex (R C : Type) [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C] (ell : ℕ) :=
  (denseFamily R ell) × (sparseFamily C ell)

def sparseSchedule {R : Type} [Fintype R] [DecidableEq R] (ell : ℕ)
    (i : SparseMeasurementIndex R C ell) : BipartiteQuery R C := (i.1.1,i.2.1)

def matrixSignature {R : Type} [Fintype R] [DecidableEq R] (ell : ℕ)
    (M : BooleanMatrix R C) : SparseMeasurementIndex R C ell → ℕ :=
  fun i => bilinear M (sparseSchedule ell i)

variable {R : Type} [Fintype R] [DecidableEq R]

theorem rowVector_mem_sparse {ell : ℕ} {M : BooleanMatrix R C}
    (hM : RowSparse ell M) (r : R) : rowVector M r ∈ sparse C ell := by
  apply mem_sparse.mpr
  refine ⟨?_, hM r⟩
  intro c
  simp only [rowVector]
  split <;> omega

theorem row_measure_le {ell : ℕ} {M : BooleanMatrix R C}
    (hM : RowSparse ell M) (r : R) (Y : Finset C) :
    measure Y (rowVector M r) ≤ ell := by
  exact (sum_le_sum_of_subset_of_nonneg (subset_univ Y)
    (fun _ _ _ => Nat.zero_le _)).trans (hM r)

/-- Two actual separating families make their Cartesian bilinear measurements
injective on all row-sparse Boolean matrices. -/
theorem matrixSignature_injective {ell : ℕ} {M N : BooleanMatrix R C}
    (hM : RowSparse ell M) (hN : RowSparse ell N)
    (he : matrixSignature ell M = matrixSignature ell N) : M = N := by
  have hcol : ∀ Y : sparseFamily C ell,
      (fun r => measure Y.1 (rowVector M r)) =
        (fun r => measure Y.1 (rowVector N r)) := by
    intro Y
    apply minimumFamily_separates (box R ell)
      (mem_box.mpr (fun r => row_measure_le hM r Y.1))
      (mem_box.mpr (fun r => row_measure_le hN r Y.1))
    funext X
    exact congrFun he (X,Y)
  have hrow : ∀ r, rowVector M r = rowVector N r := by
    intro r
    apply minimumFamily_separates (sparse C ell)
      (rowVector_mem_sparse hM r) (rowVector_mem_sparse hN r)
    funext Y
    exact congrFun (hcol Y) r
  funext r c
  have hc := congrFun (hrow r) c
  cases hm : M r c <;> cases hn : N r c <;> simp_all [rowVector]

/-- A finite decoder over explicit Boolean matrices. Running time is unrestricted;
the measurement schedule and query count are both concrete public objects. -/
def matrixCandidates (ell : ℕ) : Finset (BooleanMatrix R C) :=
  univ.filter (RowSparse ell)

def matrixDecode (ell : ℕ) (answers : SparseMeasurementIndex R C ell → ℕ) :
    Option (BooleanMatrix R C) :=
  ((matrixCandidates ell).filter (fun M => matrixSignature ell M = answers)).toList.head?

theorem matrixDecode_sound {ell : ℕ} {answers : SparseMeasurementIndex R C ell → ℕ}
    {M : BooleanMatrix R C} (h : matrixDecode ell answers = some M) :
    RowSparse ell M ∧ matrixSignature ell M = answers := by
  have hm := mem_toList.mp (List.mem_of_head? h)
  exact ⟨(mem_filter.mp (mem_filter.mp hm).1).2, (mem_filter.mp hm).2⟩

theorem matrixDecode_correct {ell : ℕ} {M : BooleanMatrix R C} (hM : RowSparse ell M) :
    matrixDecode ell (matrixSignature ell M) = some M := by
  have hc : (matrixCandidates ell).filter
      (fun N => matrixSignature ell N = matrixSignature ell M) = {M} := by
    ext N
    simp only [matrixCandidates, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hN,he⟩
      exact matrixSignature_injective hN hM he
    · rintro rfl
      exact ⟨hM,rfl⟩
  simp only [matrixDecode, hc, toList_singleton, List.head?_cons]

/-- The exact query count before proving its sharp numerical estimate. -/
def sparseRawBudget (R C : Type) [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C] (ell : ℕ) : ℕ :=
  (denseFamily R ell).card * (sparseFamily C ell).card

/-- The efficient deterministic decoder bound with a proved fixed coefficient.
This statement concerns the concrete queried family, not an oracle premise. -/
theorem sparseRawBudget_bound (ell : ℕ) (hR : 1 ≤ Fintype.card R)
    (hell : 1 ≤ ell) (heln : ell ≤ Fintype.card C) :
    (sparseRawBudget R C ell : ℝ) ≤
      16777216*(ell : ℝ)*(Fintype.card R : ℝ)*
        Real.log (2*(Fintype.card C : ℝ))/Real.log (2*(Fintype.card R : ℝ)) := by
  have hs := denseFamily_card_bound R ell hR hell
  have ht := sparseFamily_card_bound (C := C) ell hell heln
  have hRpos : (0 : ℝ)<Fintype.card R := by exact_mod_cast hR
  have hRR : (1 : ℝ)≤Fintype.card R := by exact_mod_cast hR
  have hellR : (1 : ℝ)≤ell := by exact_mod_cast hell
  have hCpos : (1 : ℝ)≤Fintype.card C := by exact_mod_cast hell.trans heln
  have hlogR : 0 < Real.log (2*(Fintype.card R : ℝ)) := Real.log_pos (by linarith)
  have hlogell : 0 < Real.log (2*(ell : ℝ)) := Real.log_pos (by linarith)
  have hlogC : 0 ≤ Real.log (2*(Fintype.card C : ℝ)) := Real.log_nonneg (by linarith)
  have hlogle : Real.log ((ell : ℝ)+1) ≤ Real.log (2*(ell : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hs0 : 0 ≤ 16384*(Fintype.card R : ℝ)*Real.log ((ell : ℝ)+1)/
      Real.log (2*(Fintype.card R : ℝ)) := by
    apply div_nonneg
    · exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    · exact hlogR.le
  have ht0 : 0 ≤ 1024*(ell : ℝ)*Real.log (2*(Fintype.card C : ℝ))/Real.log (2*(ell : ℝ)) := by
    positivity
  have hp := mul_le_mul hs ht (Nat.cast_nonneg _) hs0
  simp only [sparseRawBudget,Nat.cast_mul]
  apply hp.trans
  calc
    _ = (16777216*(ell : ℝ)*(Fintype.card R : ℝ)*
        Real.log (2*(Fintype.card C : ℝ))/Real.log (2*(Fintype.card R : ℝ))) *
          (Real.log ((ell : ℝ)+1)/Real.log (2*(ell : ℝ))) := by ring
    _ ≤ (16777216*(ell : ℝ)*(Fintype.card R : ℝ)*
        Real.log (2*(Fintype.card C : ℝ))/Real.log (2*(Fintype.card R : ℝ))) * 1 :=
      mul_le_mul_of_nonneg_left ((div_le_one hlogell).mpr hlogle) (by positivity)
    _ = _ := by rw [mul_one]

/-- This natural-answer program really asks every Cartesian pair of the public
tests. Real-answer range validation is the separate Common adapter. -/
def sparseBilinearNat (ell : ℕ) :
    DTree (BipartiteQuery R C) ℕ (Option (BooleanMatrix R C))
      (sparseRawBudget R C ell) :=
  ((DTree.queryAll (sparseSchedule (R := R) (C := C) ell) (fun _ => 0)).map
    (matrixDecode ell)).cast (by simp [sparseRawBudget])

set_option backward.isDefEq.respectTransparency false in
theorem sparseBilinearNat_run (ell : ℕ) (read : BipartiteQuery R C → ℕ) :
    DTree.run read (sparseBilinearNat (R := R) (C := C) ell) =
      (matrixDecode ell (fun i => read (sparseSchedule ell i)), sparseRawBudget R C ell) := by
  simp only [sparseBilinearNat, DTree.run_cast, DTree.run_map, DTree.queryAll_run]
  simp only [Fintype.card_prod, Fintype.card_coe, sparseRawBudget]

theorem sparseBilinearNat_correct {ell : ℕ} (M : BooleanMatrix R C)
    (hM : RowSparse ell M) :
    (sparseBilinearNat (R := R) (C := C) ell).eval (bilinear M) = some M := by
  rw [DTree.eval, sparseBilinearNat_run]
  exact matrixDecode_correct hM

theorem sparseBilinearNat_cost (ell : ℕ) (read : BipartiteQuery R C → ℕ) :
    (sparseBilinearNat (R := R) (C := C) ell).cost read = sparseRawBudget R C ell := by
  rw [DTree.cost, sparseBilinearNat_run]

theorem bilinear_le (M : BooleanMatrix R C) (q : BipartiteQuery R C) :
    bilinear M q ≤ q.1.card*q.2.card := by
  calc
    _ ≤ ∑ _r ∈ q.1, ∑ _c ∈ q.2, (1 : ℕ) := by
      apply sum_le_sum
      intro r _
      apply sum_le_sum
      intro c _
      split <;> omega
    _ = _ := by simp

def measurementBound (ell : ℕ) (i : SparseMeasurementIndex R C ell) : ℕ :=
  i.1.1.card*i.2.1.card

/-- Validate the virtual bilinear replies, after any original-cut simulation.
The raw original cut replies never receive these smaller row-column bounds. -/
def validateMeasurements (ell : ℕ) (answers : SparseMeasurementIndex R C ell → ℝ) :
    Option (SparseMeasurementIndex R C ell → ℕ) :=
  if h : ∀ i, ∃ k : Fin (measurementBound ell i+1),
      validateCount (measurementBound ell i) (answers i) = some k then
    some (fun i => (Classical.choose (h i)).val)
  else none

theorem validateMeasurements_sound {ell : ℕ}
    {answers : SparseMeasurementIndex R C ell → ℝ}
    {counts : SparseMeasurementIndex R C ell → ℕ}
    (hout : validateMeasurements ell answers = some counts) :
    ∀ i, (counts i : ℝ) = answers i ∧ counts i ≤ measurementBound ell i := by
  unfold validateMeasurements at hout
  split_ifs at hout with h
  · have he := Option.some.inj hout
    intro i
    rw [← congrFun he i]
    exact validateCount_spec (Classical.choose_spec (h i))

theorem validateMeasurements_of_nat (ell : ℕ) (counts : SparseMeasurementIndex R C ell → ℕ)
    (hc : ∀ i, counts i ≤ measurementBound ell i) :
    validateMeasurements ell (fun i => (counts i : ℝ)) = some counts := by
  have hex : ∀ i, ∃ k : Fin (measurementBound ell i+1),
      validateCount (measurementBound ell i) (counts i : ℝ) = some k := by
    intro i
    exact ⟨⟨counts i, Nat.lt_succ_of_le (hc i)⟩,validateCount_of_nat _ _ (hc i)⟩
  rw [validateMeasurements,dif_pos hex]
  congr 1
  funext i
  have he := (validateCount_spec (Classical.choose_spec (hex i))).1
  exact_mod_cast he

theorem validateMeasurements_reject {ell : ℕ}
    {answers : SparseMeasurementIndex R C ell → ℝ}
    (hbad : ∃ i, validateCount (measurementBound ell i) (answers i) = none) :
    validateMeasurements ell answers = none := by
  unfold validateMeasurements
  apply dif_neg
  rintro hall
  obtain ⟨i,hi⟩ := hbad
  obtain ⟨k,hk⟩ := hall i
  rw [hi] at hk
  cases hk

def matrixDecodeReal (ell : ℕ) (answers : SparseMeasurementIndex R C ell → ℝ) :
    Option (BooleanMatrix R C) :=
  (validateMeasurements ell answers).bind (matrixDecode ell)

theorem matrixDecodeReal_correct {ell : ℕ} (M : BooleanMatrix R C) (hM : RowSparse ell M) :
    matrixDecodeReal ell (fun i => (matrixSignature ell M i : ℝ)) = some M := by
  rw [matrixDecodeReal,validateMeasurements_of_nat ell (matrixSignature ell M)
    (fun i => bilinear_le M (sparseSchedule ell i))]
  exact matrixDecode_correct hM

/-- Actual real-answer measurement program. Every answer path uses this fixed
public schedule; an invalid derived bilinear table is rejected before decoding. -/
def sparseBilinearProgram (ell : ℕ) :
    DTree (BipartiteQuery R C) ℝ (Option (BooleanMatrix R C)) (sparseRawBudget R C ell) :=
  ((DTree.queryAll (sparseSchedule (R := R) (C := C) ell) (fun _ => (0 : ℝ))).map
    (matrixDecodeReal ell)).cast (by simp [sparseRawBudget])

set_option backward.isDefEq.respectTransparency false in
theorem sparseBilinearProgram_run (ell : ℕ) (read : BipartiteQuery R C → ℝ) :
    DTree.run read (sparseBilinearProgram (R := R) (C := C) ell) =
      (matrixDecodeReal ell (fun i => read (sparseSchedule ell i)), sparseRawBudget R C ell) := by
  simp only [sparseBilinearProgram,DTree.run_cast,DTree.run_map,DTree.queryAll_run]
  simp only [Fintype.card_prod,Fintype.card_coe,sparseRawBudget]

theorem sparseBilinearProgram_correct {ell : ℕ} (M : BooleanMatrix R C)
    (hM : RowSparse ell M) :
    (sparseBilinearProgram (R := R) (C := C) ell).eval (fun q => (bilinear M q : ℝ)) = some M := by
  rw [DTree.eval,sparseBilinearProgram_run]
  exact matrixDecodeReal_correct M hM

theorem sparseBilinearProgram_cost (ell : ℕ) (read : BipartiteQuery R C → ℝ) :
    (sparseBilinearProgram (R := R) (C := C) ell).cost read = sparseRawBudget R C ell := by
  rw [DTree.cost,sparseBilinearProgram_run]

end
end CutQueryComplexity.StarContraction2022.Recovery

#print axioms CutQueryComplexity.StarContraction2022.Recovery.positiveLevel_antichain
#print axioms CutQueryComplexity.StarContraction2022.Recovery.centralBinom_square_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.middle_choose_square_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.positiveLevel_square_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.collision_card_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.collision_square_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.collision_card_le_half
#print axioms CutQueryComplexity.StarContraction2022.Recovery.exists_separating_of_collision_sum
#print axioms CutQueryComplexity.StarContraction2022.Recovery.signedSmall_card_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.differences_sparse_card_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_box_card_le_samples
#print axioms CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_sparse_card_le_samples
#print axioms CutQueryComplexity.StarContraction2022.Recovery.denseFamily_card_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.sparseFamily_card_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.sparseRawBudget_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.matrixSignature_injective
#print axioms CutQueryComplexity.StarContraction2022.Recovery.validateMeasurements_sound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.sparseBilinearProgram_correct
#print axioms CutQueryComplexity.StarContraction2022.Recovery.sparseBilinearProgram_cost
