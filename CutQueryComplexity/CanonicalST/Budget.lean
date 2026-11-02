import CutQueryComplexity.CanonicalST.Main

/-!
# Literal every-oracle bound for the canonical terminal program

The geometric estimates below are applied to the actual `stagesBudget`
recursion. In particular, a decision pays a geometric sum of phase costs,
not a uniform worst phase multiplied by the number of phases. The final
bound includes the public core, binary search, original residual reachability,
and its one original value query.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST

open Finset
open scoped Classical
noncomputable section

def logFactor (n : ℕ) : ℕ := Nat.clog 2 (2 * n)

theorem logFactor_two_le {n : ℕ} (hn : 2 ≤ n) : 2 ≤ logFactor n := by
  have h := Nat.clog_mono_right 2 (show 4 ≤ 2 * n by omega)
  norm_num at h
  exact h

theorem clog_le_logFactor (n : ℕ) : Nat.clog 2 n ≤ logFactor n :=
  Nat.clog_mono_right 2 (by omega)

theorem sqrt_nat_one_le {k : ℕ} (hk : 1 ≤ k) : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
  have h : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simpa using Real.sqrt_le_sqrt h

theorem sqrt_nat_le {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) :
    Real.sqrt (k : ℝ) ≤ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hs := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hn2 := mul_nonneg (show (0 : ℝ) ≤ n by positivity) (sub_nonneg.mpr hnR)
  have hp := Real.sqrt_nonneg (k : ℝ)
  nlinarith

theorem phaseCountBits_le {n D k : ℕ} (hn : 2 ≤ n) (hD : 1 ≤ D) (hDn : D ≤ n) :
    (Witness.phaseCountBits n D k : ℝ) + 1 ≤
      (66 * (n : ℝ) / D + 2 * k) * logFactor n := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hDnR : (D : ℝ) ≤ n := by exact_mod_cast hDn
  have hratio : (1 : ℝ) ≤ (n : ℝ) / D := (le_div_iff₀ hDR).mpr (by simpa using hDnR)
  have hell : (1 : ℝ) ≤ logFactor n := by exact_mod_cast (show 1 ≤ logFactor n from
    (by omega : 1 ≤ 2).trans (logFactor_two_le hn))
  have hc := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 64 * (n : ℝ) / D by positivity)).le
  have hcoeff : (⌈64 * (n : ℝ) / D⌉₊ : ℝ) + 2 * k + 1 ≤
      66 * (n : ℝ) / D + 2 * k := by
    simp only [div_eq_mul_inv] at hc hratio ⊢
    nlinarith
  calc
    (Witness.phaseCountBits n D k : ℝ) + 1 ≤
        ((⌈64 * (n : ℝ) / D⌉₊ : ℝ) + 2 * k + 1) * logFactor n := by
      unfold Witness.phaseCountBits Witness.phaseCountExponent logFactor at *
      push_cast
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)

theorem phase_binCount_le {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    LongEdge.binCount (Augmentation.phaseDelta n k) ≤ 32 * n := by
  have hn1 : 1 ≤ n := by omega
  have hδ := Augmentation.phaseDelta_pos hn1 hk
  have hrec := Augmentation.phaseDelta_ge_reciprocal hn1 hk
  have hn8 : (0 : ℚ) < 8 * n := by positivity
  have hm := (div_le_iff₀ hn8).mp hrec
  have hinv : (2 : ℚ) / Augmentation.phaseDelta n k ≤ 16 * n := by
    apply (div_le_iff₀ hδ).mpr
    nlinarith
  have hfl : (⌊1 / (Augmentation.phaseDelta n k / 2)⌋₊ : ℚ) ≤
      2 / Augmentation.phaseDelta n k := by
    have h := Nat.floor_le (show (0 : ℚ) ≤ 1 / (Augmentation.phaseDelta n k / 2)
      by positivity)
    simpa only [one_div_div] using h
  have hfloor : ⌊1 / (Augmentation.phaseDelta n k / 2)⌋₊ ≤ 16 * n := by
    exact_mod_cast hfl.trans hinv
  unfold LongEdge.binCount
  omega

theorem phase_binCount_clog_le {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    Nat.clog 2 (LongEdge.binCount (Augmentation.phaseDelta n k)) ≤ logFactor n + 4 := by
  apply (Nat.clog_mono_right 2 (phase_binCount_le hn hk)).trans
  apply Nat.clog_le_of_le_pow
  calc
    32 * n = 16 * (2 * n) := by ring
    _ ≤ 16 * 2 ^ logFactor n := Nat.mul_le_mul_left 16 (Nat.le_pow_clog (by decide) _)
    _ = 2 ^ (logFactor n + 4) := by rw [pow_add]; norm_num; ring

theorem phaseStepBudget_le (V : Type) [Fintype V] {k : ℕ}
    (hn : 2 ≤ Fintype.card V) (hk : 1 ≤ k) :
    Phase.stepBudget V k ≤ 228 * logFactor (Fintype.card V) := by
  have hb := phase_binCount_clog_le hn hk
  have hl := clog_le_logFactor (Fintype.card V)
  have h2 := logFactor_two_le hn
  unfold Phase.stepBudget Phase.threshold LongEdge.longEdgeBudget
  omega

theorem phaseFuel_le (V : Type) [Fintype V] {D k : ℕ}
    (hn : 2 ≤ Fintype.card V) (hD : 1 ≤ D) (hDn : D ≤ Fintype.card V)
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    (Phase.fuel V D k : ℝ) ≤
      2200 * ((Fintype.card V : ℝ)^2 / (D * Real.sqrt (k : ℝ)) +
        Fintype.card V * Real.sqrt (k : ℝ)) * logFactor (Fintype.card V) := by
  let n := Fintype.card V
  have hn1 : 1 ≤ n := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hs : (0 : ℝ) < Real.sqrt (k : ℝ) := lt_of_lt_of_le (by norm_num) (sqrt_nat_one_le hk)
  have hsn : Real.sqrt (k : ℝ) ≤ n := sqrt_nat_le hn1 hkn
  have hratio : (1 : ℝ) ≤ n / Real.sqrt (k : ℝ) := (le_div_iff₀ hs).mpr (by simpa using hsn)
  have hd := Augmentation.phaseDelta_pos hn1 hk
  have hf : (Phase.fuel V D k : ℝ) ≤
      (4 / (Augmentation.phaseDelta n k : ℝ) + 1) *
        ((Witness.phaseCountBits n D k : ℝ) + 1) := by
    exact_mod_cast Phase.contractionFuel_le hd (Witness.phaseCountBits n D k)
  have hi : 4 / (Augmentation.phaseDelta n k : ℝ) + 1 ≤ 33 * n / Real.sqrt (k : ℝ) := by
    have h := Augmentation.phaseDelta_four_div_le hn1 hk
    simp only [div_eq_mul_inv] at h hratio ⊢
    nlinarith
  have hb := phaseCountBits_le hn hD hDn (k := k)
  have hsdiv : (k : ℝ) / Real.sqrt (k : ℝ) = Real.sqrt (k : ℝ) := by
    apply (div_eq_iff hs.ne').mpr
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  calc
    (Phase.fuel V D k : ℝ) ≤ (33 * n / Real.sqrt (k : ℝ)) *
        ((66 * (n : ℝ) / D + 2 * k) * logFactor n) :=
      hf.trans (mul_le_mul hi hb (by positivity) (by positivity))
    _ = (2178 * ((n : ℝ)^2 / (D * Real.sqrt (k : ℝ))) +
        66 * n * ((k : ℝ) / Real.sqrt (k : ℝ))) * logFactor n := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (2178 * ((n : ℝ)^2 / (D * Real.sqrt (k : ℝ))) +
        66 * n * Real.sqrt (k : ℝ)) * logFactor n := by rw [hsdiv]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      have ha : 0 ≤ (n : ℝ)^2 / (D * Real.sqrt (k : ℝ)) := by positivity
      have hb' : 0 ≤ (n : ℝ) * Real.sqrt (k : ℝ) := by positivity
      nlinarith

theorem phaseQueryBudget_le (V : Type) [Fintype V] {D k : ℕ}
    (hn : 2 ≤ Fintype.card V) (hD : 1 ≤ D) (hDn : D ≤ Fintype.card V)
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    (Phase.queryBudget V D k : ℝ) ≤
      2^19 * ((Fintype.card V : ℝ)^2 / (D * Real.sqrt (k : ℝ)) +
        Fintype.card V * Real.sqrt (k : ℝ)) * (logFactor (Fintype.card V) : ℝ)^2 := by
  have hf := phaseFuel_le V hn hD hDn hk hkn
  have hs : (Phase.stepBudget V k : ℝ) ≤ 228 * logFactor (Fintype.card V) := by
    exact_mod_cast phaseStepBudget_le V hn hk
  rw [Phase.queryBudget, Nat.cast_mul]
  calc
    _ ≤ (2200 * ((Fintype.card V : ℝ)^2 / (D * Real.sqrt (k : ℝ)) +
        Fintype.card V * Real.sqrt (k : ℝ)) * logFactor (Fintype.card V)) *
        (228 * logFactor (Fintype.card V)) := mul_le_mul hf hs (by positivity) (by positivity)
    _ ≤ _ := by
      have hx : 0 ≤ ((Fintype.card V : ℝ)^2 / (D * Real.sqrt (k : ℝ)) +
          Fintype.card V * Real.sqrt (k : ℝ)) * (logFactor (Fintype.card V) : ℝ)^2 := by
        positivity
      nlinarith

def sqrtSum : ℕ → ℕ → ℝ
  | 0, _ => 0
  | r + 1, k => if k = 0 then 0 else Real.sqrt (k : ℝ) + sqrtSum r (k / 2)

def reciprocalSqrtSum : ℕ → ℕ → ℝ
  | 0, _ => 0
  | r + 1, k => if k = 0 then 0 else 1 / Real.sqrt (k : ℝ) + reciprocalSqrtSum r (k / 2)

theorem sqrtSum_nonneg (r k : ℕ) : 0 ≤ sqrtSum r k := by
  induction r generalizing k with
  | zero => simp [sqrtSum]
  | succ r ih =>
      rw [sqrtSum]
      split_ifs
      · exact le_rfl
      · exact add_nonneg (Real.sqrt_nonneg _) (ih _)

theorem reciprocalSqrtSum_nonneg (r k : ℕ) : 0 ≤ reciprocalSqrtSum r k := by
  induction r generalizing k with
  | zero => simp [reciprocalSqrtSum]
  | succ r ih =>
      rw [reciprocalSqrtSum]
      split_ifs
      · exact le_rfl
      · exact add_nonneg (by positivity) (ih _)

theorem sqrt_half_le (k : ℕ) : Real.sqrt ((k / 2 : ℕ) : ℝ) ≤ (3 / 4 : ℝ) * Real.sqrt (k : ℝ) := by
  have h : 2 * ((k / 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast (show 2 * (k / 2) ≤ k by omega)
  have hk := Real.sqrt_nonneg (k : ℝ)
  have hm := Real.sqrt_nonneg ((k / 2 : ℕ) : ℝ)
  have hksq := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hmsq := Real.sq_sqrt (Nat.cast_nonneg (k / 2) : (0 : ℝ) ≤ (k / 2 : ℕ))
  apply (sq_le_sq₀ hm (by positivity)).mp
  nlinarith

theorem sqrtSum_le (r k : ℕ) : sqrtSum r k ≤ 4 * Real.sqrt (k : ℝ) := by
  induction r generalizing k with
  | zero => exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  | succ r ih =>
      rw [sqrtSum]
      split_ifs with hk
      · positivity
      · have h := ih (k / 2)
        have hh := sqrt_half_le k
        linarith

/-- The stronger induction invariant removes one reciprocal tail. -/
theorem reciprocalSqrtSum_le_tail (r : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    reciprocalSqrtSum r k ≤ 4 - 3 / Real.sqrt (k : ℝ) := by
  induction r generalizing k with
  | zero =>
      have hs1 := sqrt_nat_one_le hk
      have hs : (0 : ℝ) < Real.sqrt (k : ℝ) := by linarith
      rw [reciprocalSqrtSum]
      have h : (3 : ℝ) / Real.sqrt (k : ℝ) ≤ 3 := (div_le_iff₀ hs).mpr (by linarith)
      linarith
  | succ r ih =>
      have hs1 := sqrt_nat_one_le hk
      have hs : (0 : ℝ) < Real.sqrt (k : ℝ) := by linarith
      rw [reciprocalSqrtSum, ite_eq_right (by omega : k ≠ 0)]
      by_cases hm : k / 2 = 0
      · have hk1 : k = 1 := by omega
        subst k
        cases r <;> norm_num [reciprocalSqrtSum]
      · have hm1 : 1 ≤ k / 2 := by omega
        have hms : (0 : ℝ) < Real.sqrt ((k / 2 : ℕ) : ℝ) :=
          lt_of_lt_of_le (by norm_num) (sqrt_nat_one_le hm1)
        have hi := ih hm1
        have hh := sqrt_half_le k
        have hdiv : (4 : ℝ) / Real.sqrt (k : ℝ) ≤ 3 / Real.sqrt ((k / 2 : ℕ) : ℝ) :=
          (div_le_div_iff₀ hs hms).mpr (by linarith)
        simp only [div_eq_mul_inv] at hi hdiv ⊢
        linarith

theorem reciprocalSqrtSum_le (r k : ℕ) : reciprocalSqrtSum r k ≤ 4 := by
  by_cases hk : k = 0
  · subst k
    cases r <;> simp [reciprocalSqrtSum]
  · exact (reciprocalSqrtSum_le_tail r (by omega : 1 ≤ k)).trans (sub_le_self _ (by positivity))

theorem stagesBudget_le_sums (V : Type) [Fintype V] {D : ℕ}
    (hn : 2 ≤ Fintype.card V) (hD : 1 ≤ D) (hDn : D ≤ Fintype.card V)
    (r k : ℕ) (hkn : k ≤ Fintype.card V) :
    (Decision.stagesBudget V D r k : ℝ) ≤
      2^19 * ((Fintype.card V : ℝ)^2 / D * reciprocalSqrtSum r k +
        Fintype.card V * sqrtSum r k) * (logFactor (Fintype.card V) : ℝ)^2 := by
  induction r generalizing k with
  | zero => simp [Decision.stagesBudget, sqrtSum, reciprocalSqrtSum]
  | succ r ih =>
      rw [Decision.stagesBudget, sqrtSum, reciprocalSqrtSum]
      by_cases hk : k = 0
      · simp [hk]
      · simp only [hk, ite_false, Nat.cast_add]
        have hp := phaseQueryBudget_le V hn hD hDn (by omega : 1 ≤ k) hkn
        have ht := ih (k / 2) ((Nat.div_le_self _ _).trans hkn)
        have ha := add_le_add hp ht
        convert ha using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

theorem decisionQueryBudget_le (V : Type) [Fintype V] {D f : ℕ}
    (hn : 2 ≤ Fintype.card V) (hD : 1 ≤ D) (hDn : D ≤ Fintype.card V)
    (hfn : f ≤ Fintype.card V) :
    (Decision.queryBudget V D f : ℝ) ≤
      2^21 * ((Fintype.card V : ℝ)^2 / D + Fintype.card V * Real.sqrt (f : ℝ)) *
        (logFactor (Fintype.card V) : ℝ)^2 := by
  have h := stagesBudget_le_sums V hn hD hDn (Decision.rounds V) f hfn
  have hi := reciprocalSqrtSum_le (Decision.rounds V) f
  have hs := sqrtSum_le (Decision.rounds V) f
  have hai := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ (Fintype.card V : ℝ)^2 / D by positivity)
  have has := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)
  have hsum := add_le_add hai has
  calc
    (Decision.queryBudget V D f : ℝ) ≤ _ := h
    _ ≤ 2^19 * ((Fintype.card V : ℝ)^2 / D * 4 +
        Fintype.card V * (4 * Real.sqrt (f : ℝ))) * (logFactor (Fintype.card V) : ℝ)^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity)) (sq_nonneg _)
    _ = _ := by ring

theorem degreeThreshold_le_card {n : ℕ} (hn : 2 ≤ n) : degreeThreshold n ≤ n := by
  apply max_le hn
  apply Nat.ceil_le.mpr
  exact sqrt_nat_le (by omega) le_rfl

theorem degreeThreshold_sqrt_le (n : ℕ) : Real.sqrt (n : ℝ) ≤ degreeThreshold n :=
  (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 2 ⌈Real.sqrt (n : ℝ)⌉₊))

theorem degreeThreshold_le_two_sqrt {n : ℕ} (hn : 2 ≤ n) :
    (degreeThreshold n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  rw [degreeThreshold, Nat.cast_max]
  apply max_le
  · have h := sqrt_nat_one_le (show 1 ≤ n by omega)
    norm_num
    linarith
  · exact Augmentation.ceil_sqrt_le_two_sqrt (by omega)

theorem uniformBudget_le (V : Type) [Fintype V] (hn : 2 ≤ Fintype.card V) :
    (Decision.uniformBudget V (degreeThreshold (Fintype.card V)) : ℝ) ≤
      2^22 * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) *
        (logFactor (Fintype.card V) : ℝ)^2 := by
  let n := Fintype.card V
  let D := degreeThreshold n
  have hD : 1 ≤ D := (by omega : 1 ≤ 2).trans (degreeThreshold_two_le n)
  have hDn : D ≤ n := degreeThreshold_le_card hn
  have hs : (0 : ℝ) < Real.sqrt (n : ℝ) :=
    lt_of_lt_of_le (by norm_num) (sqrt_nat_one_le (by omega : 1 ≤ n))
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hdiv : (n : ℝ)^2 / D ≤ n * Real.sqrt (n : ℝ) := by
    apply (div_le_iff₀ hDR).mpr
    have hmul := mul_le_mul_of_nonneg_left (degreeThreshold_sqrt_le n)
      (show (0 : ℝ) ≤ n * Real.sqrt (n : ℝ) by positivity)
    have hid : (n : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ)^2 := by
      nlinarith [congrArg (fun x : ℝ => (n : ℝ) * x) hsq]
    nlinarith
  have hbound : ∀ f ∈ range n, (Decision.queryBudget V D f : ℝ) ≤
      2^22 * n * Real.sqrt (n : ℝ) * (logFactor n : ℝ)^2 := by
    intro f hf
    have hfn : f ≤ n := (mem_range.mp hf).le
    have hq := decisionQueryBudget_le V hn hD hDn hfn
    have hsqrt := Real.sqrt_le_sqrt (show (f : ℝ) ≤ n by exact_mod_cast hfn)
    have hm := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hsum : (n : ℝ)^2 / D + n * Real.sqrt (f : ℝ) ≤ 2 * n * Real.sqrt (n : ℝ) := by
      linarith
    calc
      (Decision.queryBudget V D f : ℝ) ≤ _ := hq
      _ ≤ 2^21 * (2 * n * Real.sqrt (n : ℝ)) * (logFactor n : ℝ)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity)) (sq_nonneg _)
      _ = _ := by ring
  have hnat : (range n).sup (Decision.queryBudget V D) ≤
      ⌊2^22 * (n : ℝ) * Real.sqrt (n : ℝ) * (logFactor n : ℝ)^2⌋₊ := by
    apply Finset.sup_le
    intro f hf
    exact Nat.le_floor (hbound f hf)
  exact (by exact_mod_cast hnat :
    (((range n).sup (Decision.queryBudget V D) : ℕ) : ℝ) ≤
      (⌊2^22 * (n : ℝ) * Real.sqrt (n : ℝ) * (logFactor n : ℝ)^2⌋₊ : ℝ)).trans
    (Nat.floor_le (by positivity))

theorem searchBudget_le (V : Type) [Fintype V] (hn : 2 ≤ Fintype.card V) :
    (Decision.searchBudget V (degreeThreshold (Fintype.card V)) : ℝ) ≤
      2^22 * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) *
        (logFactor (Fintype.card V) : ℝ)^3 := by
  have hu := uniformBudget_le V hn
  have hr : (Decision.rounds V : ℝ) ≤ logFactor (Fintype.card V) := by
    exact_mod_cast clog_le_logFactor (Fintype.card V)
  rw [Decision.searchBudget, Nat.cast_mul]
  calc
    _ ≤ (logFactor (Fintype.card V) : ℝ) *
        (2^22 * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) *
          (logFactor (Fintype.card V) : ℝ)^2) := mul_le_mul hr hu (by positivity) (by positivity)
    _ = _ := by ring

theorem coreBudget_sqrt_le (V : Type) [Fintype V] (hn : 2 ≤ Fintype.card V) :
    (coreBudget V (degreeThreshold (Fintype.card V)) : ℝ) ≤
      25 * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) * logFactor (Fintype.card V) := by
  let n := Fintype.card V
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs := sqrt_nat_one_le (show 1 ≤ n by omega)
  have hD := degreeThreshold_le_two_sqrt hn
  have hl : (Nat.clog 2 n : ℝ) ≤ logFactor n := by exact_mod_cast clog_le_logFactor n
  have hell : (1 : ℝ) ≤ logFactor n := by
    exact_mod_cast ((by decide : 1 ≤ 2).trans (logFactor_two_le hn))
  have htail : (Nat.clog 2 n : ℝ) + 1 ≤ 2 * logFactor n := by linarith
  have hm := mul_le_mul hD htail (by positivity) (by positivity)
  have hm' := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 6 * n by positivity)
  have hbase : (n : ℝ) ≤ n * Real.sqrt (n : ℝ) * logFactor n := by
    calc
      (n : ℝ) = n * 1 := by ring
      _ ≤ n * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
      _ = (n * Real.sqrt (n : ℝ)) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hell (by positivity)
  unfold coreBudget searchDepth
  push_cast
  nlinarith

theorem finishBudget_le (V : Type) [Fintype V] (hn : 2 ≤ Fintype.card V) :
    (finishBudget V : ℝ) ≤
      13 * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) * logFactor (Fintype.card V) := by
  let n := Fintype.card V
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs := sqrt_nat_one_le (show 1 ≤ n by omega)
  have hl : (Nat.clog 2 n : ℝ) ≤ logFactor n := by exact_mod_cast clog_le_logFactor n
  have hell : (1 : ℝ) ≤ logFactor n := by
    exact_mod_cast ((by decide : 1 ≤ 2).trans (logFactor_two_le hn))
  have htail : (Nat.clog 2 n : ℝ) + 1 ≤ 2 * logFactor n := by linarith
  have hm := mul_le_mul_of_nonneg_left htail (show (0 : ℝ) ≤ 6 * n by positivity)
  have hns : (1 : ℝ) ≤ n * Real.sqrt (n : ℝ) := by
    simpa only [one_mul] using mul_le_mul hnR hs (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  have hbase : (1 : ℝ) ≤ n * Real.sqrt (n : ℝ) * logFactor n := by
    simpa only [one_mul] using mul_le_mul hns hell (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  have hexpand : (n : ℝ) * logFactor n ≤ n * Real.sqrt (n : ℝ) * logFactor n := by
    have h := mul_le_mul_of_nonneg_right hs (show (0 : ℝ) ≤ n * logFactor n by positivity)
    nlinarith
  unfold finishBudget Reachability.queryBudget Reachability.stepBudget searchDepth
  push_cast
  nlinarith

/-- Numerical bound on the exact recursive public cap, including all output queries. -/
theorem queryBudget_le (V : Type) [Fintype V] (hn : 2 ≤ Fintype.card V) :
    (queryBudget V : ℝ) ≤
      2^23 * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) *
        (logFactor (Fintype.card V) : ℝ)^3 := by
  have hc := coreBudget_sqrt_le V hn
  have hs := searchBudget_le V hn
  have hf := finishBudget_le V hn
  have hell : (1 : ℝ) ≤ logFactor (Fintype.card V) := by exact_mod_cast
    (show 1 ≤ logFactor (Fintype.card V) by have := logFactor_two_le hn; omega)
  have hp : (logFactor (Fintype.card V) : ℝ) ≤ (logFactor (Fintype.card V) : ℝ)^3 := by
    have hsquare : (1 : ℝ) ≤ (logFactor (Fintype.card V) : ℝ)^2 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hell 2
    calc
      (logFactor (Fintype.card V) : ℝ) = (logFactor (Fintype.card V) : ℝ) * 1 := by ring
      _ ≤ (logFactor (Fintype.card V) : ℝ) * (logFactor (Fintype.card V) : ℝ)^2 :=
        mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg _)
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hp
    (show (0 : ℝ) ≤ Fintype.card V * Real.sqrt (Fintype.card V : ℝ) by positivity)
  have hb : 0 ≤ (Fintype.card V : ℝ) * Real.sqrt (Fintype.card V : ℝ) *
      (logFactor (Fintype.card V) : ℝ)^3 := by positivity
  unfold queryBudget continuationBudget
  push_cast
  nlinarith

def headlineBudget (n : ℕ) : ℕ :=
  ⌈2^23 * (n : ℝ) * Real.sqrt (n : ℝ) * (logFactor n : ℝ)^3⌉₊

theorem queryBudget_le_headline (V : Type) [Fintype V] (hn : 2 ≤ Fintype.card V) :
    queryBudget V ≤ headlineBudget (Fintype.card V) := by
  apply (Nat.cast_le (α := ℝ)).mp
  exact (queryBudget_le V hn).trans (Nat.le_ceil _)

variable {V : Type} [Fintype V] [DecidableEq V]

def headlineProgram (hn : 2 ≤ Fintype.card V) (s t : V) :
    DTree (Finset V) ℝ (Option (Output V)) (headlineBudget (Fintype.card V)) :=
  (terminalProgram s t).weaken (queryBudget_le_headline V hn)

theorem headlineProgram_cost (hn : 2 ≤ Fintype.card V) (s t : V) (read : Finset V → ℝ) :
    (headlineProgram hn s t).cost read ≤ headlineBudget (Fintype.card V) := DTree.cost_le _ _

theorem headlineProgram_correct (hn : 2 ≤ Fintype.card V) (G : WeightedGraph V)
    (hG : AllPairsAudit.Unweighted G) {s t : V} (hst : s ≠ t) :
    ∃ out, (headlineProgram hn s t).eval G.cut = some out ∧ OutputSpec G s t out := by
  obtain ⟨out, he, hs⟩ := terminalProgram_correct G hG hst
  refine ⟨out, ?_, hs⟩
  change (DTree.run G.cut ((terminalProgram s t).weaken (queryBudget_le_headline V hn))).1 = some out
  rw [DTree.run_weaken]
  exact he

/-- A graph-independent deterministic tree with the literal Õ(n^(3/2)) cap,
valid on every answer oracle and correct for every original unit graph. -/
theorem exists_terminal_sqrt_program (hn : 2 ≤ Fintype.card V) (s t : V) (hst : s ≠ t) :
    ∃ T : DTree (Finset V) ℝ (Option (Output V)) (headlineBudget (Fintype.card V)),
      (∀ read : Finset V → ℝ, T.cost read ≤ headlineBudget (Fintype.card V)) ∧
      ∀ G : WeightedGraph V, AllPairsAudit.Unweighted G →
        ∃ out, T.eval G.cut = some out ∧ OutputSpec G s t out := by
  exact ⟨headlineProgram hn s t, headlineProgram_cost hn s t,
    fun G hG => headlineProgram_correct hn G hG hst⟩

end
end CutQueryComplexity.CanonicalST

#print axioms CutQueryComplexity.CanonicalST.phaseFuel_le
#print axioms CutQueryComplexity.CanonicalST.phaseQueryBudget_le
#print axioms CutQueryComplexity.CanonicalST.sqrtSum_le
#print axioms CutQueryComplexity.CanonicalST.reciprocalSqrtSum_le
#print axioms CutQueryComplexity.CanonicalST.decisionQueryBudget_le
#print axioms CutQueryComplexity.CanonicalST.uniformBudget_le
#print axioms CutQueryComplexity.CanonicalST.queryBudget_le
#print axioms CutQueryComplexity.CanonicalST.headlineProgram_cost
#print axioms CutQueryComplexity.CanonicalST.headlineProgram_correct
#print axioms CutQueryComplexity.CanonicalST.exists_terminal_sqrt_program
