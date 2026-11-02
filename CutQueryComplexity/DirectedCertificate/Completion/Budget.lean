import CutQueryComplexity.DirectedCertificate.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push

set_option autoImplicit false

/-! # Finite cover size for the small-shore construction

Every nonempty shore of size at most `k` is the image of a `k`-tuple, so a
family of such shores has size at most `n^k`. A proved one-step halving rule
therefore produces a fixed cover in `k ceil(log₂ n) + 1` steps. This module
does not import the undirected tree-packing theorem.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Count all nonempty shores of size at most `k`, without a factor `k`.
Repetitions in a `k`-tuple pad the smaller shores. -/
theorem small_family_card_le_pow (F : Finset (Finset V)) (k : ℕ)
    (hne : ∀ S ∈ F, S.Nonempty) (hsize : ∀ S ∈ F, S.card ≤ k) :
    F.card ≤ Fintype.card V ^ k := by
  classical
  let images : Finset (Finset V) := univ.image fun f : Fin k → V => univ.image f
  have hsub : F ⊆ images := by
    intro S hS
    obtain ⟨v, hv⟩ := hne S hS
    have hemb : Nonempty (S ↪ Fin k) := Function.Embedding.nonempty_of_card_le
      (by simpa using hsize S hS)
    obtain ⟨f, hf⟩ := Function.exists_surjective_iff.mpr
      (show Nonempty (Fin k → S) ∧ Nonempty (S ↪ Fin k) from ⟨⟨fun _ => ⟨v, hv⟩⟩, hemb⟩)
    apply mem_image.mpr
    refine ⟨fun i => (f i).val, mem_univ _, ?_⟩
    ext w
    constructor
    · rintro hw
      obtain ⟨i, -, hi⟩ := mem_image.mp hw
      exact hi ▸ (f i).property
    · intro hw
      obtain ⟨i, hi⟩ := hf ⟨w, hw⟩
      exact mem_image.mpr ⟨i, mem_univ i, congrArg Subtype.val hi⟩
  calc F.card ≤ images.card := card_le_card hsub
    _ ≤ Fintype.card (Fin k → V) := card_image_le
    _ = Fintype.card V ^ k := by simp

section Halving

variable {ι σ : Type*} [DecidableEq σ]

/-- Iterated deterministic halving. The family being covered is fixed in advance. -/
theorem greedy_halving_cover (F : Finset σ) (covers : ι → σ → Prop)
    (hstep : ∀ R ⊆ F, ∃ i : ι, 2 * (R.filter fun s => ¬ covers i s).card ≤ R.card) :
    ∀ t : ℕ, ∃ L : List ι, L.length = t ∧
      2 ^ t * (F.filter fun s => ∀ i ∈ L, ¬ covers i s).card ≤ F.card
  | 0 => by
      classical
      exact ⟨[], rfl, by simp⟩
  | t + 1 => by
      classical
      obtain ⟨L, hL, hrem⟩ := greedy_halving_cover F covers hstep t
      let R := F.filter fun s => ∀ i ∈ L, ¬ covers i s
      obtain ⟨i, hi⟩ := hstep R (filter_subset _ _)
      refine ⟨i :: L, by simp [hL], ?_⟩
      have heq : (F.filter fun s => ∀ j ∈ i :: L, ¬ covers j s) =
          R.filter fun s => ¬ covers i s := by
        ext s
        simp only [R, mem_filter, List.mem_cons, forall_eq_or_imp]
        tauto
      rw [heq]
      calc 2 ^ (t + 1) * (R.filter fun s => ¬ covers i s).card
          = 2 ^ t * (2 * (R.filter fun s => ¬ covers i s).card) := by
            rw [pow_succ]
            ring
        _ ≤ 2 ^ t * R.card := Nat.mul_le_mul_left _ hi
        _ ≤ F.card := hrem

/-- A finite halving rule yields one fixed complete cover of logarithmic length. -/
theorem exists_halving_cover (F : Finset σ) (covers : ι → σ → Prop)
    (hstep : ∀ R ⊆ F, ∃ i : ι, 2 * (R.filter fun s => ¬ covers i s).card ≤ R.card) :
    ∃ L : List ι, L.length = Nat.clog 2 (F.card + 1) ∧
      ∀ s ∈ F, ∃ i ∈ L, covers i s := by
  classical
  obtain ⟨L, hL, hrem⟩ := greedy_halving_cover F covers hstep (Nat.clog 2 (F.card + 1))
  refine ⟨L, hL, fun s hs => ?_⟩
  by_contra hn
  push Not at hn
  have hpos : 1 ≤ (F.filter fun s => ∀ i ∈ L, ¬ covers i s).card :=
    card_pos.mpr ⟨s, mem_filter.mpr ⟨hs, hn⟩⟩
  have hle : 2 ^ Nat.clog 2 (F.card + 1) ≤ F.card :=
    (Nat.le_mul_of_pos_right _ hpos).trans hrem
  have hpow := Nat.le_pow_clog (by decide : 1 < 2) (F.card + 1)
  omega

end Halving

/-- Absorb the logarithm of the number of small shores into `k log₂ n`. -/
theorem small_family_clog_le (F : Finset (Finset V)) (k : ℕ)
    (hn : 1 ≤ Fintype.card V) (hne : ∀ S ∈ F, S.Nonempty)
    (hsize : ∀ S ∈ F, S.card ≤ k) :
    Nat.clog 2 (F.card + 1) ≤ k * Nat.clog 2 (Fintype.card V) + 1 := by
  apply Nat.clog_le_of_le_pow
  have hF := small_family_card_le_pow F k hne hsize
  have hpos : 1 ≤ Fintype.card V ^ k := one_le_pow₀ hn
  have hnlog := Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card V)
  have hpow := Nat.pow_le_pow_left hnlog k
  calc F.card + 1 ≤ 2 * Fintype.card V ^ k := by omega
    _ ≤ 2 * (2 ^ Nat.clog 2 (Fintype.card V)) ^ k := Nat.mul_le_mul_left 2 hpow
    _ = 2 ^ (Nat.clog 2 (Fintype.card V) * k + 1) := by
      rw [pow_add, pow_mul, pow_one]
      exact Nat.mul_comm _ _
    _ = 2 ^ (k * Nat.clog 2 (Fintype.card V) + 1) := by
      rw [Nat.mul_comm (Nat.clog 2 (Fintype.card V)) k]

/-- An explicit power bound on the binary ceiling logarithm. -/
theorem clog_le_sixth_root (n : ℕ) (hn : 1 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ (6 / Real.log 2 + 1) * (n : ℝ) ^ ((1 : ℝ) / 6) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : (0 : ℝ) ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hnR
  have hceil : (Nat.clog 2 n : ℝ) ≤ Real.logb 2 n + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact (Nat.ceil_lt_add_one hlogb).le
  have hlog : Real.log (n : ℝ) ≤ 6 * (n : ℝ) ^ ((1 : ℝ) / 6) := by
    have h := Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1 / 6)
    convert h using 1 <;> ring
  have hquot : Real.logb 2 n ≤
      (6 / Real.log 2) * (n : ℝ) ^ ((1 : ℝ) / 6) := by
    unfold Real.logb
    exact (div_le_div_of_nonneg_right hlog hlog2.le).trans_eq (by ring)
  have hone : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := Real.one_le_rpow hnR (by norm_num)
  calc (Nat.clog 2 n : ℝ) ≤ Real.logb 2 n + 1 := hceil
    _ ≤ (6 / Real.log 2) * (n : ℝ) ^ ((1 : ℝ) / 6) +
        (n : ℝ) ^ ((1 : ℝ) / 6) := add_le_add hquot hone
    _ = (6 / Real.log 2 + 1) * (n : ℝ) ^ ((1 : ℝ) / 6) := by ring

/-- Squaring yields the one-third power needed to absorb the W6 logarithms. -/
theorem clog_sq_le_cube_root (n : ℕ) (hn : 1 ≤ n) :
    (Nat.clog 2 n : ℝ) ^ 2 ≤
      (6 / Real.log 2 + 1) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have h := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.clog 2 n)) (clog_le_sixth_root n hn) 2
  calc (Nat.clog 2 n : ℝ) ^ 2 ≤
      ((6 / Real.log 2 + 1) * (n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := h
    _ = (6 / Real.log 2 + 1) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      norm_num

/-- The exact logarithm in the repository's W-track budget is absorbed by
`n^(1/3)` with a universal real constant. -/
theorem logL_sq_le_cube_root (n : ℕ) (hn : 1 ≤ n) :
    (logL n : ℝ) ^ 2 ≤
      ((6 / Real.log 2 + 1) ^ 2 * (2 : ℝ) ^ ((1 : ℝ) / 3)) *
        (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have h := clog_sq_le_cube_root (2 * n) (by omega)
  simpa only [logL, Nat.cast_mul, Nat.cast_ofNat,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n), mul_assoc] using h

/-- The explicit preparation, two tree covers and terminal costs fit the
small-shore part of the repository's uniform budget. -/
theorem small_certificate_arithmetic (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    39 * (n : ℝ) + 192 * n * (k : ℝ) ^ 2 +
      30 * n * (Nat.clog 2 n : ℝ) * (k * (Nat.clog 2 n : ℝ) + 1) +
      60 * n * (k + 1 : ℝ) ≤
    400 * n * (k : ℝ) ^ 2 + 60 * n * k * (logL n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog : Nat.clog 2 n ≤ logL n := Nat.clog_monotone 2 (by omega : n ≤ 2 * n)
  have hL : 1 ≤ logL n := by
    have hpow := Nat.le_pow_clog (by decide : 1 < 2) (2 * n)
    by_contra h
    have hz : logL n = 0 := by omega
    change 2 * n ≤ 2 ^ logL n at hpow
    rw [hz] at hpow
    norm_num at hpow
    omega
  have hL1 : (1 : ℝ) ≤ logL n := by exact_mod_cast hL
  have hlogR : (Nat.clog 2 n : ℝ) ≤ logL n := by exact_mod_cast hlog
  have hlog0 : (0 : ℝ) ≤ Nat.clog 2 n := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ logL n := Nat.cast_nonneg _
  have hlogsq : (Nat.clog 2 n : ℝ) ^ 2 ≤ (logL n : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlogR 2
  have hklogsq := mul_le_mul_of_nonneg_left hlogsq hk0
  have hLsq : (logL n : ℝ) ≤ k * (logL n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (sq_nonneg (logL n : ℝ)),
      mul_nonneg hL0 (sub_nonneg.mpr hL1)]
  have htree : (Nat.clog 2 n : ℝ) * (k * (Nat.clog 2 n : ℝ) + 1) ≤
      2 * k * (logL n : ℝ) ^ 2 := by nlinarith
  have htreeN := mul_le_mul_of_nonneg_left htree (mul_nonneg (by norm_num : (0 : ℝ) ≤ 30) hn0)
  have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hnk : (n : ℝ) * k ≤ n * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hk2 hn0
  have hn2 : (n : ℝ) ≤ n * (k : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hn0 (show 0 ≤ (k : ℝ) ^ 2 - 1 by nlinarith)]
  nlinarith [mul_nonneg hn0 (sq_nonneg (k : ℝ))]

/-- Choose the integer part of `n^(1/3)`. This proves every admissibility and
ceiling-division estimate needed to turn the uniform certificate budget into
the headline `O(n^(5/3))` bound. -/
theorem exists_optimized_budget (C n : ℕ) (hn : 2 ≤ n) :
    ∃ k : ℕ, 1 ≤ k ∧ k < n ∧
      (budget C n k : ℝ) ≤
        (C : ℝ) * (5 + (6 / Real.log 2 + 1) ^ 2 * (2 : ℝ) ^ ((1 : ℝ) / 3)) *
          (n : ℝ) ^ ((5 : ℝ) / 3) := by
  let a : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3)
  let k : ℕ := ⌊a⌋₊
  let D : ℝ := (6 / Real.log 2 + 1) ^ 2 * (2 : ℝ) ^ ((1 : ℝ) / 3)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := by linarith
  have ha1 : 1 ≤ a := Real.one_le_rpow hn1 (by norm_num)
  have ha0 : 0 < a := by linarith
  have hk : 1 ≤ k := Nat.floor_pos.mpr ha1
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hka : (k : ℝ) ≤ a := Nat.floor_le ha0.le
  have han : a < n := Real.rpow_lt_self_of_one_lt hn2 (by norm_num)
  have hkn : k < n := by exact_mod_cast hka.trans_lt han
  have hhalf : a ≤ 2 * (k : ℝ) := by
    have h := Nat.lt_floor_add_one a
    change a < (k : ℝ) + 1 at h
    linarith
  have hcube : a ^ 3 = (n : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hpower : (n : ℝ) * a ^ 2 = (n : ℝ) ^ ((5 : ℝ) / 3) := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast hn0.le]
    calc (n : ℝ) * (n : ℝ) ^ (((1 : ℝ) / 3) * 2)
        = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (((1 : ℝ) / 3) * 2) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + ((1 : ℝ) / 3) * 2) := (Real.rpow_add hn0 _ _).symm
      _ = (n : ℝ) ^ ((5 : ℝ) / 3) := by norm_num
  have hquotN : ceilDiv n k * k ≤ n + k :=
    (Nat.div_mul_le_self (n + k - 1) k).trans (Nat.sub_le _ _)
  have hquot : (ceilDiv n k : ℝ) * (k : ℝ) ≤ n + k := by exact_mod_cast hquotN
  have hnk : (n : ℝ) ≤ 2 * a ^ 2 * k := by
    rw [← hcube]
    nlinarith [mul_le_mul_of_nonneg_left hhalf (sq_nonneg a)]
  have hceil : (ceilDiv n k : ℝ) ≤ 2 * a ^ 2 + 1 := by
    apply le_of_mul_le_mul_right (a := (k : ℝ)) ?_ hkR
    nlinarith
  have hceil' : (ceilDiv n k : ℝ) + 1 ≤ 4 * a ^ 2 := by
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr ha1)]
  have hsquare : (k : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hka 2
  have hlog : (logL n : ℝ) ^ 2 ≤ D * a := logL_sq_le_cube_root n (by omega)
  have hlogterm : (k : ℝ) * (logL n : ℝ) ^ 2 ≤ D * a ^ 2 := by
    calc (k : ℝ) * (logL n : ℝ) ^ 2 ≤ a * (logL n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hka (sq_nonneg _)
      _ ≤ a * (D * a) := mul_le_mul_of_nonneg_left hlog ha0.le
      _ = D * a ^ 2 := by ring
  have hfirst := mul_le_mul_of_nonneg_left hsquare hn0.le
  have hsecond := mul_le_mul_of_nonneg_left hlogterm hn0.le
  have hthird := mul_le_mul_of_nonneg_left hceil' hn0.le
  refine ⟨k, hk, hkn, ?_⟩
  calc (budget C n k : ℝ)
      = (C : ℝ) * ((n : ℝ) * (k : ℝ) ^ 2 +
        n * k * (logL n : ℝ) ^ 2 + n * ((ceilDiv n k : ℝ) + 1)) := by
          simp only [budget, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    _ ≤ (C : ℝ) * ((5 + D) * n * a ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg C)
      nlinarith
    _ = (C : ℝ) * (5 + D) * (n : ℝ) ^ ((5 : ℝ) / 3) := by
      rw [← hpower]
      ring

/-- The square-root parameter for the unit-input degree-cap construction.
The output includes all finite-size and ceiling-division obligations. -/
theorem exists_unit_parameter (n : ℕ) (hn : 2 ≤ n) :
    ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ (k : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) ∧
      39 * (n : ℝ) + 12 * n * k +
        120 * n * ((ceilDiv n k : ℝ) + 1) + 1 ≤
          600 * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  let a : ℝ := (n : ℝ) ^ ((1 : ℝ) / 2)
  let k : ℕ := ⌊a⌋₊
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := by linarith
  have ha1 : 1 ≤ a := Real.one_le_rpow hn1 (by norm_num)
  have ha0 : 0 < a := by linarith
  have hk : 1 ≤ k := Nat.floor_pos.mpr ha1
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hka : (k : ℝ) ≤ a := Nat.floor_le ha0.le
  have han : a < n := Real.rpow_lt_self_of_one_lt hn2 (by norm_num)
  have hkn : k < n := by exact_mod_cast hka.trans_lt han
  have hhalf : a ≤ 2 * (k : ℝ) := by
    have h := Nat.lt_floor_add_one a
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    change a < (k : ℝ) + 1 at h
    linarith
  have hsquare : a ^ 2 = (n : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hpower : (n : ℝ) * a = (n : ℝ) ^ ((3 : ℝ) / 2) := by
    dsimp [a]
    calc (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2)
        = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (1 : ℝ) / 2) := (Real.rpow_add hn0 _ _).symm
      _ = (n : ℝ) ^ ((3 : ℝ) / 2) := by norm_num
  have hquotN : ceilDiv n k * k ≤ n + k :=
    (Nat.div_mul_le_self (n + k - 1) k).trans (Nat.sub_le _ _)
  have hquot : (ceilDiv n k : ℝ) * (k : ℝ) ≤ n + k := by exact_mod_cast hquotN
  have hnk : (n : ℝ) ≤ 2 * a * k := by
    rw [← hsquare]
    nlinarith [mul_le_mul_of_nonneg_left hhalf ha0.le]
  have hceil : (ceilDiv n k : ℝ) ≤ 2 * a + 1 := by
    apply le_of_mul_le_mul_right (a := (k : ℝ)) ?_ hkR
    nlinarith
  have hceil' : (ceilDiv n k : ℝ) + 1 ≤ 4 * a := by linarith
  have htermK := mul_le_mul_of_nonneg_left hka hn0.le
  have htermQ := mul_le_mul_of_nonneg_left hceil' hn0.le
  have hnA := mul_le_mul_of_nonneg_left ha1 hn0.le
  refine ⟨k, hk, hkn, hka, ?_⟩
  rw [← hpower]
  nlinarith

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.small_family_card_le_pow
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_halving_cover
#print axioms CutQueryComplexity.DirectedCertificate.Completion.small_family_clog_le

#print axioms CutQueryComplexity.DirectedCertificate.Completion.logL_sq_le_cube_root

#print axioms CutQueryComplexity.DirectedCertificate.Completion.small_certificate_arithmetic

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_optimized_budget

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_unit_parameter
