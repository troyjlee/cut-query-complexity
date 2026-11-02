import CutQueryComplexity.DirectedUnitST.Acceleration.Huber
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.LinearCombination

/-! # Fixed-regularization inexact accelerated descent

Exact algebra from paper 4, Appendix C.  The error is retained as one inner
product against the *next* auxiliary iterate.  Only local lower and upper
quadratic models are needed; the reference point need not be stationary.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Acceleration

open Finset

noncomputable section

variable {V : Type*} [Fintype V]

def nextX (a : ℝ) (v g : V → ℝ) : V → ℝ := fun i => v i - a ^ 2 * g i
def nextZ (a : ℝ) (z v g : V → ℝ) : V → ℝ :=
  fun i => (1 - a) * z i + a * v i - a * g i
def blend (a : ℝ) (x z : V → ℝ) : V → ℝ := fun i => (x i + a * z i) / (1 + a)

def energy (F : (V → ℝ) → ℝ) (r x z : V → ℝ) : ℝ :=
  F x - F r + sqDist z r / 2

omit [Fintype V] in
theorem blend_relation {a : ℝ} (ha : 0 ≤ a) (x z : V → ℝ) (i : V) :
    (1 + a) * blend a x z i = x i + a * z i := by
  unfold blend
  field_simp [show 1 + a ≠ 0 by linarith]

private theorem coordinate_identity (a x z v g e r : ℝ)
    (hmix : (1 + a) * v = x + a * z) :
    ((1 - a) * z + a * v - a * g - r) ^ 2 / 2 - (1 - a) * (z - r) ^ 2 / 2 -
      (1 - a) * ((g - e) * (x - v) + (x - v) ^ 2 / 2) -
      a * ((g - e) * (r - v) + (r - v) ^ 2 / 2) - a ^ 2 * g ^ 2 / 2 + a ^ 2 * e * g =
    -a * e * ((1 - a) * z + a * v - a * g - r) -
      (1 - a) * (x - v) ^ 2 / 2 - a * (1 - a) * (z - v) ^ 2 / 2 := by
  have hx : x = (1 + a) * v - a * z := by linarith
  rw [hx]
  ring

/-- The exact one-step estimate, with both dissipative squared distances. -/
theorem energy_step_exact (F : (V → ℝ) → ℝ) (a : ℝ) (x z v g err r : V → ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hmix : ∀ i, (1 + a) * v i = x i + a * z i)
    (hx : F v + dot (fun i => g i - err i) (fun i => x i - v i) + sqDist x v / 2 ≤ F x)
    (hr : F v + dot (fun i => g i - err i) (fun i => r i - v i) + sqDist r v / 2 ≤ F r)
    (hs : F (nextX a v g) ≤ F v - a ^ 2 * sqNorm g / 2 + a ^ 2 * dot err g) :
    energy F r (nextX a v g) (nextZ a z v g) ≤
      (1 - a) * energy F r x z - a * dot err (fun i => nextZ a z v g i - r i) -
      (1 - a) * sqDist x v / 2 - a * (1 - a) * sqDist z v / 2 := by
  have he := sum_congr (s₁ := (univ : Finset V)) rfl
    (fun i _ => coordinate_identity a (x i) (z i) (v i) (g i) (err i) (r i) (hmix i))
  simp only [mul_assoc, sum_add_distrib, sum_sub_distrib, ← sum_div, ← mul_sum] at he
  have hxs := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ha1)
  have hrs := mul_le_mul_of_nonneg_left hr ha
  unfold energy sqDist sqNorm dot nextZ at *
  linear_combination hxs + hrs + hs + he

/-- Dropping only nonpositive terms gives the error inner product recurrence. -/
theorem energy_step (F : (V → ℝ) → ℝ) (a : ℝ) (x z v g err r : V → ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hmix : ∀ i, (1 + a) * v i = x i + a * z i)
    (hx : F v + dot (fun i => g i - err i) (fun i => x i - v i) + sqDist x v / 2 ≤ F x)
    (hr : F v + dot (fun i => g i - err i) (fun i => r i - v i) + sqDist r v / 2 ≤ F r)
    (hs : F (nextX a v g) ≤ F v - a ^ 2 * sqNorm g / 2 + a ^ 2 * dot err g) :
    energy F r (nextX a v g) (nextZ a z v g) ≤
      (1 - a) * energy F r x z - a * dot err (fun i => nextZ a z v g i - r i) := by
  have h := energy_step_exact F a x z v g err r ha ha1 hmix hx hr hs
  have h1 : 0 ≤ (1 - a) * sqDist x v / 2 := by
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha1) (sqDist_nonneg _ _)) (by norm_num)
  have h2 : 0 ≤ a * (1 - a) * sqDist z v / 2 := by
    exact div_nonneg (mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1))
      (sqDist_nonneg _ _)) (by norm_num)
  linarith

/-- The smooth quadratic model discharges the local descent premise. -/
theorem smooth_step (F : (V → ℝ) → ℝ) (a L : ℝ) (v g err : V → ℝ)
    (haL : L * a ^ 2 = 1)
    (hs : F (nextX a v g) ≤ F v +
      dot (fun i => g i - err i) (fun i => nextX a v g i - v i) +
      L / 2 * sqDist (nextX a v g) v) :
    F (nextX a v g) ≤ F v - a ^ 2 * sqNorm g / 2 + a ^ 2 * dot err g := by
  have he : dot (fun i => g i - err i) (fun i => nextX a v g i - v i) +
      L / 2 * sqDist (nextX a v g) v = -a ^ 2 * sqNorm g / 2 + a ^ 2 * dot err g := by
    unfold dot sqDist sqNorm nextX
    simp only [mul_sum, sum_div, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    linear_combination (a ^ 2 * (g i) ^ 2 / 2) * haL
  linarith

/-- The recurrence instantiated at the actual Huber graph potential. -/
theorem huber_energy_step {E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (u c : E → ℝ) (beta : V → ℝ)
    {k B a L : ℝ} (hk : 0 < k) (hu : ∀ e, 0 ≤ u e)
    (hB : ∀ d : V → ℝ, (∑ e, u e * (d (tail e) - d (head e)) ^ 2) ≤ B * sqNorm d)
    (hL : k * B + 1 ≤ L) (ha : 0 ≤ a) (ha1 : a ≤ 1) (haL : L * a ^ 2 = 1)
    (x z err r : V → ℝ) :
    let F := graphPotential tail head u c beta k
    let v := blend a x z
    let g := fun i => graphGradient tail head u c beta k v i + err i
    energy F r (nextX a v g) (nextZ a z v g) ≤
      (1 - a) * energy F r x z - a * dot err (fun i => nextZ a z v g i - r i) := by
  dsimp only
  apply energy_step _ _ _ _ _ _ _ _ ha ha1 (blend_relation ha x z)
  · simpa only [add_sub_cancel_right] using
      graphPotential_lower tail head u c beta hk hu (blend a x z) x
  · simpa only [add_sub_cancel_right] using
      graphPotential_lower tail head u c beta hk hu (blend a x z) r
  · apply smooth_step _ _ _ _ _ _ haL
    simp only [add_sub_cancel_right]
    have hh := graphPotential_upper tail head u c beta hk hu hB (blend a x z)
      (nextX a (blend a x z) (fun i => graphGradient tail head u c beta k (blend a x z) i + err i))
    have hm := mul_nonneg (sub_nonneg.mpr hL)
      (sqDist_nonneg (nextX a (blend a x z)
        (fun i => graphGradient tail head u c beta k (blend a x z) i + err i)) (blend a x z))
    nlinarith

theorem blend_sum_zero (a : ℝ) {x z : V → ℝ}
    (hx : ∑ i, x i = 0) (hz : ∑ i, z i = 0) : ∑ i, blend a x z i = 0 := by
  simp only [blend, ← sum_div, sum_add_distrib, ← mul_sum, hx, hz]
  simp

/-- Shared pair coefficients give exact mean preservation in both updates. -/
theorem next_sum_zero (a : ℝ) {z v g : V → ℝ}
    (hz : ∑ i, z i = 0) (hv : ∑ i, v i = 0) (hg : ∑ i, g i = 0) :
    (∑ i, nextX a v g i = 0) ∧ (∑ i, nextZ a z v g i = 0) := by
  simp [nextX, nextZ, sum_sub_distrib, sum_add_distrib, ← mul_sum, hz, hv, hg]

/-- Cauchy--Schwarz in the coordinate convention used by the algorithm. -/
theorem dot_sq_le (x y : V → ℝ) : dot x y ^ 2 ≤ sqNorm x * sqNorm y :=
  sum_mul_sq_le_sq_mul_sq univ x y

private theorem quadratic_root_bound {X C b : ℝ} (_hX : 0 ≤ X) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (h : X ^ 2 ≤ C ^ 2 + b * X) : X ≤ C + b := by
  by_contra hn
  have hn' : C + b < X := lt_of_not_ge hn
  have hprod := mul_pos (show 0 < X - C - b by linarith) (show 0 < X + C by linarith)
  nlinarith [mul_nonneg hC hb]

/-- Convert the signed error recurrence into the square-root energy contraction. -/
theorem sqrt_energy_step {A B a eps : ℝ} (err w : V → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1) (heps : 0 ≤ eps)
    (herr : sqNorm err ≤ eps ^ 2) (hw : sqNorm w ≤ 2 * A)
    (hstep : A ≤ (1 - a) * B - a * dot err w) :
    Real.sqrt A ≤ Real.sqrt (1 - a) * Real.sqrt B + a * eps * Real.sqrt 2 := by
  have hd := dot_sq_le err w
  have hd' : dot err w ^ 2 ≤ (eps * Real.sqrt 2 * Real.sqrt A) ^ 2 := by
    have he : (eps * Real.sqrt 2 * Real.sqrt A) ^ 2 = eps ^ 2 * (2 * A) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hA]
      ring
    rw [he]
    exact hd.trans ((mul_le_mul_of_nonneg_right herr (sqNorm_nonneg w)).trans
      (mul_le_mul_of_nonneg_left hw (sq_nonneg eps)))
  have hdlo : -(eps * Real.sqrt 2 * Real.sqrt A) ≤ dot err w :=
    (abs_le_of_sq_le_sq' hd' (by positivity)).1
  have hmul := mul_le_mul_of_nonneg_left hdlo ha
  apply quadratic_root_bound (Real.sqrt_nonneg A) (by positivity) (by positivity)
  rw [Real.sq_sqrt hA, mul_pow, Real.sq_sqrt (sub_nonneg.mpr ha1), Real.sq_sqrt hB]
  nlinarith

/-- A finite error envelope, proved by induction rather than an assumed convergence theorem. -/
theorem iterate_error_bound (s : ℕ → ℝ) {q b C : ℝ}
    (hq : 0 ≤ q) (hC : 0 ≤ C) (hb : b ≤ (1 - q) * C)
    (hstep : ∀ j, s (j + 1) ≤ q * s j + b) (j : ℕ) :
    s j ≤ q ^ j * s 0 + C := by
  induction j with
  | zero => simpa using (le_add_of_nonneg_right hC : s 0 ≤ s 0 + C)
  | succ j ih =>
      have hm := mul_le_mul_of_nonneg_left ih hq
      have hs := hstep j
      rw [pow_succ]
      nlinarith

/-- The fixed `μ = 1` error floor is `2 sqrt(2) eps`. -/
theorem accelerated_error_bound (s : ℕ → ℝ) {a eps : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (heps : 0 ≤ eps)
    (hstep : ∀ j, s (j + 1) ≤ Real.sqrt (1 - a) * s j + a * eps * Real.sqrt 2)
    (j : ℕ) :
    s j ≤ Real.sqrt (1 - a) ^ j * s 0 + 2 * Real.sqrt 2 * eps := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr ha1)
  have hroot : Real.sqrt (1 - a) ≤ 1 := (Real.sqrt_le_one).mpr (by linarith)
  have hgap : a ≤ 2 * (1 - Real.sqrt (1 - a)) := by
    nlinarith [sq_nonneg (1 - Real.sqrt (1 - a))]
  apply iterate_error_bound s (Real.sqrt_nonneg _) (by positivity) _ hstep j
  have hm := mul_le_mul_of_nonneg_right hgap (show 0 ≤ eps * Real.sqrt 2 by positivity)
  nlinarith

/-- Finite iteration bound for the actual Huber objective and its explicit updates.
The hypotheses specify the algorithmic recurrence and coefficient error, not convergence. -/
theorem huber_trajectory_error {E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (u c : E → ℝ) (beta : V → ℝ)
    {k B a L eps : ℝ} (hk : 0 < k) (hu : ∀ e, 0 ≤ u e)
    (hB : ∀ d : V → ℝ, (∑ e, u e * (d (tail e) - d (head e)) ^ 2) ≤ B * sqNorm d)
    (hL : k * B + 1 ≤ L) (ha : 0 ≤ a) (ha1 : a ≤ 1) (haL : L * a ^ 2 = 1)
    (heps : 0 ≤ eps) (x z err : ℕ → V → ℝ) (r : V → ℝ)
    (hmin : ∀ w, graphPotential tail head u c beta k r ≤ graphPotential tail head u c beta k w)
    (herr : ∀ j, sqNorm (err j) ≤ eps ^ 2)
    (hx : ∀ j, x (j + 1) = nextX a (blend a (x j) (z j))
      (fun i => graphGradient tail head u c beta k (blend a (x j) (z j)) i + err j i))
    (hz : ∀ j, z (j + 1) = nextZ a (z j) (blend a (x j) (z j))
      (fun i => graphGradient tail head u c beta k (blend a (x j) (z j)) i + err j i)) (J : ℕ) :
    Real.sqrt (energy (graphPotential tail head u c beta k) r (x J) (z J)) ≤
      Real.sqrt (1 - a) ^ J *
        Real.sqrt (energy (graphPotential tail head u c beta k) r (x 0) (z 0)) +
          2 * Real.sqrt 2 * eps := by
  have hnonneg : ∀ j, 0 ≤ energy (graphPotential tail head u c beta k) r (x j) (z j) := by
    intro j
    unfold energy
    exact add_nonneg (sub_nonneg.mpr (hmin _)) (div_nonneg (sqDist_nonneg _ _) (by norm_num))
  apply accelerated_error_bound _ ha ha1 heps _ J
  intro j
  apply sqrt_energy_step (err j) (fun i => z (j + 1) i - r i)
    (hnonneg (j + 1)) (hnonneg j) ha ha1 heps (herr j)
  · have hm := hmin (x (j + 1))
    unfold energy sqDist
    linarith
  · have hs := huber_energy_step tail head u c beta hk hu hB hL ha ha1 haL (x j) (z j) (err j) r
    dsimp only at hs
    rw [hx j, hz j]
    exact hs

/-- The gradient-gap inequality follows by comparing with one exact gradient step. -/
theorem gradient_sq_le_gap (F : (V → ℝ) → ℝ) (a L : ℝ) (x g r : V → ℝ)
    (hL : 0 < L) (haL : L * a ^ 2 = 1) (hmin : ∀ w, F r ≤ F w)
    (hs : F (nextX a x g) ≤ F x + dot g (fun i => nextX a x g i - x i) +
      L / 2 * sqDist (nextX a x g) x) :
    sqNorm g ≤ 2 * L * (F x - F r) := by
  have hh := smooth_step F a L x g (fun _ => 0) haL (by simpa only [sub_zero] using hs)
  simp only [dot, zero_mul, sum_const_zero, mul_zero, add_zero] at hh
  have hmul := mul_le_mul_of_nonneg_left (hmin (nextX a x g)) hL.le
  have hmul' := mul_le_mul_of_nonneg_left hh hL.le
  have hcancel : L * (a ^ 2 * sqNorm g) = sqNorm g := by rw [← mul_assoc, haL, one_mul]
  nlinarith

/-- Elementary Bernoulli estimate for a full block of `2T` accelerated steps. -/
theorem contraction_block {T : ℕ} (hT : 0 < T) :
    Real.sqrt (1 - 1 / (T : ℝ)) ^ (2 * T) ≤ 1 / 2 := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hTone : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_of_lt hT)
  have hi : 0 ≤ 1 / (T : ℝ) := by positivity
  have hi1 : 1 / (T : ℝ) ≤ 1 := (div_le_one hTpos).mpr hTone
  have hq : 0 ≤ 1 - 1 / (T : ℝ) := by linarith
  have hb := one_add_mul_le_pow (a := 1 / (T : ℝ)) (by linarith : -2 ≤ 1 / (T : ℝ)) T
  have hcancel : (T : ℝ) * (1 / T) = 1 := by field_simp [ne_of_gt hTpos]
  rw [hcancel] at hb
  have hp : ((1 - 1 / (T : ℝ)) * (1 + 1 / (T : ℝ))) ^ T ≤ 1 := by
    apply pow_le_one₀ (mul_nonneg hq (by positivity))
    nlinarith [sq_nonneg (1 / (T : ℝ))]
  rw [mul_pow] at hp
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg hq T)
  rw [pow_mul, Real.sq_sqrt hq]
  nlinarith

/-- The public logarithmic schedule contracts the initial term by `16n`. -/
theorem fixed_schedule_contraction {n T : ℕ} (hn : 0 < n) (hT : 0 < T) :
    Real.sqrt (1 - 1 / (T : ℝ)) ^ (2 * T * Nat.clog 2 (16 * n)) ≤ 1 / (16 * (n : ℝ)) := by
  rw [pow_mul]
  calc
    (Real.sqrt (1 - 1 / (T : ℝ)) ^ (2 * T)) ^ Nat.clog 2 (16 * n) ≤
        ((1 : ℝ) / 2) ^ Nat.clog 2 (16 * n) :=
      pow_le_pow_left₀ (by positivity) (contraction_block hT) _
    _ = 1 / (2 : ℝ) ^ Nat.clog 2 (16 * n) := by rw [div_pow, one_pow]
    _ ≤ 1 / (16 * (n : ℝ)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (16 * n)

/-- The integer public smoothness schedule supplies all exact scalar step relations. -/
theorem integer_schedule {n k T : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hT : 8 * n * k ≤ T ^ 2) :
    0 < T ∧ 4 * (n : ℝ) * k + 1 ≤ (T : ℝ) ^ 2 ∧
      0 ≤ 1 / (T : ℝ) ∧ 1 / (T : ℝ) ≤ 1 ∧
        (T : ℝ) ^ 2 * (1 / (T : ℝ)) ^ 2 = 1 := by
  have hnk : 2 ≤ n * k := by simpa using Nat.mul_le_mul hn hk
  have hTp : 0 < T := by
    by_contra h
    have ht0 : T = 0 := by omega
    subst T
    nlinarith
  have htpos : (0 : ℝ) < T := by exact_mod_cast hTp
  have htone : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_of_lt hTp)
  have hnk' : (2 : ℝ) ≤ n * k := by exact_mod_cast hnk
  have hT' : 8 * (n : ℝ) * k ≤ (T : ℝ) ^ 2 := by exact_mod_cast hT
  refine ⟨hTp, by nlinarith, by positivity, (div_le_one htpos).mpr htone, ?_⟩
  field_simp [ne_of_gt htpos]

/-- Entirely public integer choices; no graph value or unknown optimum occurs. -/
def scheduleT (n k : ℕ) : ℕ := Nat.sqrt (8 * n * k) + 1
def scheduleBits (n : ℕ) : ℕ := Nat.clog 2 (64 * n ^ 2)
def scheduleSteps (n k : ℕ) : ℕ := 2 * scheduleT n k * Nat.clog 2 (16 * n)

theorem scheduleT_sufficient (n k : ℕ) : 8 * n * k ≤ scheduleT n k ^ 2 :=
  (Nat.lt_succ_sqrt' (8 * n * k)).le

theorem scheduleBits_sufficient (n : ℕ) : 64 * n ^ 2 ≤ 2 ^ scheduleBits n :=
  Nat.le_pow_clog (by norm_num) _

theorem scheduleT_upper (n k : ℕ) :
    (scheduleT n k : ℝ) ≤ Real.sqrt (8 * (n : ℝ) * k) + 1 := by
  have hs : (Nat.sqrt (8 * n * k) : ℝ) ^ 2 ≤ 8 * (n : ℝ) * k := by
    exact_mod_cast Nat.sqrt_le' (8 * n * k)
  have h := Real.le_sqrt_of_sq_le hs
  simpa [scheduleT] using add_le_add_right h 1

/-- The selected schedule and even the weaker error `eps ≤ 1/32` give energy below one. -/
theorem fixed_schedule_below_one (s : ℕ → ℝ) {n T : ℕ} {eps : ℝ}
    (hn : 0 < n) (hT : 0 < T) (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 32)
    (hs0 : 0 ≤ s 0) (hinit : s 0 ≤ Real.sqrt 5 * n)
    (hstep : ∀ j, s (j + 1) ≤ Real.sqrt (1 - 1 / (T : ℝ)) * s j +
      (1 / (T : ℝ)) * eps * Real.sqrt 2) :
    s (2 * T * Nat.clog 2 (16 * n)) < 1 := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hTone : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_of_lt hT)
  have hs := accelerated_error_bound s (by positivity : 0 ≤ 1 / (T : ℝ))
    ((div_le_one hTp).mpr hTone) heps hstep (2 * T * Nat.clog 2 (16 * n))
  have hc := fixed_schedule_contraction hn hT
  have hm := mul_le_mul hc hinit hs0 (by positivity : 0 ≤ 1 / (16 * (n : ℝ)))
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 1 / (16 * (n : ℝ)) * (Real.sqrt 5 * n) = Real.sqrt 5 / 16 := by
    field_simp [ne_of_gt hnp] <;> ring
  rw [he] at hm
  have he' := mul_le_mul_of_nonneg_left heps' (show 0 ≤ 2 * Real.sqrt 2 by positivity)
  have h5 : Real.sqrt 5 < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 2 < 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  nlinarith

/-- L1 conversion at the output, using the coordinate Euclidean norm. -/
theorem l1_le_of_gradient_sq (g : V → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hg : sqNorm g ≤ 2 * T ^ 2) :
    (∑ i, |g i|) ≤ Real.sqrt (2 * Fintype.card V) * T := by
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset V) (fun _ => (1 : ℝ)) (fun i => |g i|)
  simp only [one_mul, one_pow, sq_abs, sum_const, card_univ, nsmul_eq_mul, mul_one] at hc
  have hm := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
  have hs : (Real.sqrt (2 * Fintype.card V) * T) ^ 2 = (2 * Fintype.card V) * T ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hb : (∑ i, |g i|) ^ 2 ≤ (Real.sqrt (2 * Fintype.card V) * T) ^ 2 := by
    rw [hs]
    change (∑ i, |g i|) ^ 2 ≤ (Fintype.card V : ℝ) * sqNorm g at hc
    nlinarith
  exact (abs_le_of_sq_le_sq' hb (by positivity)).2

theorem final_l1_discrepancy (grad err : V → ℝ) {T eps : ℝ} (hT : 0 ≤ T)
    (hgrad : sqNorm grad ≤ 2 * T ^ 2) (herr : (∑ i, |err i|) ≤ eps) :
    (∑ i, |grad i + err i|) ≤ Real.sqrt (2 * Fintype.card V) * T + eps := by
  have h := sum_le_sum (s := (univ : Finset V)) fun i _ => abs_add_le (grad i) (err i)
  rw [sum_add_distrib] at h
  linarith [l1_le_of_gradient_sq grad hT hgrad]

end

#print axioms energy_step_exact
#print axioms huber_energy_step
#print axioms huber_trajectory_error
#print axioms fixed_schedule_below_one
#print axioms gradient_sq_le_gap
#print axioms final_l1_discrepancy

end CutQueryComplexity.DirectedUnitST.Acceleration
