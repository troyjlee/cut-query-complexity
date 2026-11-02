import CutQueryComplexity.ImplicitLP.PathFollowing.QueryBound
import CutQueryComplexity.Sparsify.Asymptotic

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! # Explicit costs of the calibrated primitives

All envelopes below are proved for the actual definitions. The arithmetic helper
`PowerEnvelope` stores an elementary inequality, never a supplied algorithmic
cost or solver guarantee. Exact arithmetic has no query charge.
-/

namespace CutQueryComplexity.ImplicitLP.PathFollowing

open Real
noncomputable section

/-- A convenient polynomial base, determined solely by the vertex count. -/
def queryHeight (n : ℕ) : ℝ := 2 * n

def envelopeLog (n : ℕ) : ℝ := Real.logb 2 (queryHeight n)

theorem queryHeight_two_le {n : ℕ} (hn : 2 ≤ n) : 2 ≤ queryHeight n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold queryHeight
  linarith

theorem envelopeLog_eq (n : ℕ) (hn : 0 < n) : envelopeLog n = 1 + queryLog n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold envelopeLog queryHeight queryLog
  rw [Real.logb_mul (by norm_num) hn'.ne',
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]

theorem envelopeLog_one_le {n : ℕ} (hn : 2 ≤ n) : 1 ≤ envelopeLog n := by
  rw [envelopeLog_eq n (by omega)]
  linarith [queryLog_one_le hn]

/-- A scalar estimate used only inside the explicit arithmetic derivation. -/
structure PowerEnvelope (H x : ℝ) (k : ℕ) : Prop where
  nonneg : 0 ≤ x
  le_pow : x ≤ H ^ k

namespace PowerEnvelope

variable {H x y : ℝ} {a b : ℕ}

theorem of_le (hy : PowerEnvelope H y a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    PowerEnvelope H x a := ⟨hx, hxy.trans hy.le_pow⟩

theorem constant (hH : 2 ≤ H) (hx : 0 ≤ x) (h : x ≤ (2 : ℝ) ^ a) :
    PowerEnvelope H x a :=
  ⟨hx, h.trans (pow_le_pow_left₀ (by norm_num) hH a)⟩

theorem one (H : ℝ) : PowerEnvelope H 1 0 := ⟨by norm_num, by simp⟩

theorem weaken (hx : PowerEnvelope H x a) (hH : 1 ≤ H) (hab : a ≤ b) :
    PowerEnvelope H x b :=
  ⟨hx.nonneg, hx.le_pow.trans (pow_le_pow_right₀ hH hab)⟩

theorem mul (hx : PowerEnvelope H x a) (hy : PowerEnvelope H y b) :
    PowerEnvelope H (x * y) (a + b) := by
  refine ⟨mul_nonneg hx.nonneg hy.nonneg, ?_⟩
  rw [pow_add]
  exact mul_le_mul hx.le_pow hy.le_pow hy.nonneg (hx.nonneg.trans hx.le_pow)

theorem pow (hx : PowerEnvelope H x a) (k : ℕ) :
    PowerEnvelope H (x ^ k) (a * k) := by
  refine ⟨pow_nonneg hx.nonneg _, ?_⟩
  rw [pow_mul]
  exact pow_le_pow_left₀ hx.nonneg hx.le_pow k

theorem add (hx : PowerEnvelope H x a) (hH : 2 ≤ H)
    (hy : PowerEnvelope H y b) : PowerEnvelope H (x + y) (max a b + 1) := by
  have hH1 : 1 ≤ H := by linarith
  have hx' := (hx.weaken hH1 (Nat.le_max_left a b)).le_pow
  have hy' := (hy.weaken hH1 (Nat.le_max_right a b)).le_pow
  refine ⟨add_nonneg hx.nonneg hy.nonneg, ?_⟩
  calc x + y ≤ 2 * H ^ max a b := by linarith
    _ ≤ H * H ^ max a b := mul_le_mul_of_nonneg_right hH (by positivity)
    _ = H ^ (max a b + 1) := by rw [pow_succ]; ring

theorem max (hx : PowerEnvelope H x a) (hy : PowerEnvelope H y a) :
    PowerEnvelope H (max x y) a :=
  ⟨hx.nonneg.trans (le_max_left _ _), max_le hx.le_pow hy.le_pow⟩

theorem sqrt (hx : PowerEnvelope H x a) (hH : 1 ≤ H) :
    PowerEnvelope H (Real.sqrt x) a := by
  have hp : 1 ≤ H ^ a := one_le_pow₀ hH
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩⟩
  nlinarith [hx.le_pow]

theorem div (hx : PowerEnvelope H x a) (hy : PowerEnvelope H (1 / y) b) :
    PowerEnvelope H (x / y) (a + b) := by
  simpa only [div_eq_mul_inv, one_mul] using hx.mul hy

theorem clog (hx : PowerEnvelope H x a) (hH : 2 ≤ H) :
    (Nat.clog 2 ⌈x⌉₊ : ℝ) ≤ a * Real.logb 2 H + 2 := by
  have hm : (Nat.clog 2 ⌈x⌉₊ : ℝ) ≤ Nat.clog 2 ⌈H ^ a⌉₊ := by
    exact_mod_cast clog_ceil_mono hx.le_pow
  calc (Nat.clog 2 ⌈x⌉₊ : ℝ) ≤ Nat.clog 2 ⌈H ^ a⌉₊ := hm
    _ ≤ Real.logb 2 (H ^ a) + 2 := clog_le_log_add_one (one_le_pow₀ (by linarith))
    _ = a * Real.logb 2 H + 2 := by rw [Real.logb_pow]

theorem magBits (hx : PowerEnvelope H x a) (hH : 2 ≤ H) :
    (ImplicitLP.magBits x : ℝ) ≤ a * Real.logb 2 H + 3 := by
  have h := hx.clog hH
  unfold ImplicitLP.magBits
  push_cast
  linarith

theorem logarithm (hx : PowerEnvelope H x a) (hH : 2 ≤ H) (hx0 : 0 < x) :
    Real.log x ≤ a * Real.logb 2 H := by
  have hh : 0 ≤ Real.logb 2 H := Real.logb_nonneg (by norm_num) (by linarith)
  have hl : Real.log H ≤ Real.logb 2 H := by
    have htwo : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have he : Real.log H = Real.logb 2 H * Real.log 2 := by
      rw [Real.logb, div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    rw [he]
    nlinarith
  calc Real.log x ≤ Real.log (H ^ a) := Real.log_le_log hx0 hx.le_pow
    _ = a * Real.log H := by rw [Real.log_pow]
    _ ≤ a * Real.logb 2 H := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)

end PowerEnvelope

/-- Convert a crude polynomial estimate to the common public base. -/
theorem polynomial_envelope {n : ℕ} (hn : 2 ≤ n) {x : ℝ} {a b : ℕ}
    (hx : 0 ≤ x) (hb : x ≤ (2 : ℝ) ^ a * (n : ℝ) ^ b) :
    PowerEnvelope (queryHeight n) x (a + b) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hH := queryHeight_two_le hn
  have hnH : (n : ℝ) ≤ queryHeight n := by unfold queryHeight; linarith
  refine ⟨hx, hb.trans ?_⟩
  rw [pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (by norm_num) hH a)
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hnH b) (by positivity) (by positivity)

private theorem base_scalar_envelopes {n : ℕ} (hn : 2 ≤ n) :
    let H := queryHeight n
    let E := publicEnvironment n
    PowerEnvelope H (publicLogSize n) 5 ∧
    PowerEnvelope H E.Mbar 4 ∧ PowerEnvelope H E.U 3 ∧
    PowerEnvelope H (1 / E.ε) 9 ∧ PowerEnvelope H E.C 12 ∧
    PowerEnvelope H (publicEnvelope n) 14 ∧
    PowerEnvelope H (1 / publicDelta n) 47 ∧ PowerEnvelope H (1 / E.η) 70 := by
  intro H E
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hH : 2 ≤ H := queryHeight_two_le hn
  have hL0 : 0 < publicLogSize n := by linarith [(publicLogSize_spec n).1]
  have hΔ := (publicDelta_spec n).1
  have hη : 0 < E.η :=
    (calibratedTolerance_spec (publicLogSize_spec n).1 hΔ (publicFinalCount n)).1
  have hL : PowerEnvelope H (publicLogSize n) 5 := by
    apply polynomial_envelope hn (by positivity) (a := 4) (b := 1)
    have h := (publicLogSize_le hn).trans
      (mul_le_mul_of_nonneg_left (queryLog_le hn) (by norm_num : (0 : ℝ) ≤ 16))
    simpa only [pow_one, show (2 : ℝ) ^ 4 = 16 by norm_num] using h
  have hM : PowerEnvelope H E.Mbar 4 :=
    polynomial_envelope hn (by change 0 ≤ publicRows n; unfold publicRows; positivity)
      (a := 2) (b := 2) (by
        change publicRows n ≤ (2 : ℝ) ^ 2 * (n : ℝ) ^ 2
        norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
        exact publicRows_le hn)
  have hU : PowerEnvelope H E.U 3 :=
    polynomial_envelope hn (by change 0 ≤ publicWidth n; unfold publicWidth; positivity)
      (a := 2) (b := 1) (by change 4 * (n : ℝ) ≤ _; norm_num)
  have hε : PowerEnvelope H (1 / E.ε) 9 := by
    have he : 1 / E.ε = 128 * (n : ℝ) ^ 2 := by
      change 1 / publicAccuracy n = _
      unfold publicAccuracy publicExtractionScale
      field_simp
      all_goals norm_num
    rw [he]
    exact polynomial_envelope hn (by positivity) (a := 7) (b := 2) (by norm_num)
  have hC : PowerEnvelope H E.C 12 := by
    convert (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 96)
      (by norm_num : (96 : ℝ) ≤ 2 ^ 7)).mul hL using 1
    change 48 * (2 * publicLogSize n) = 96 * publicLogSize n
    ring
  have hqn := queryLog_le hn
  have hq0 : 0 ≤ queryLog n := by linarith [queryLog_one_le hn]
  have hT : PowerEnvelope H (publicEnvelope n) 14 := by
    apply polynomial_envelope hn (by linarith [publicEnvelope_one_le n]) (a := 12) (b := 2)
    have hs : Real.sqrt (n : ℝ) ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
    calc publicEnvelope n ≤ 4096 * Real.sqrt n * queryLog n := publicEnvelope_le hn
      _ ≤ 4096 * (n : ℝ) * n := by gcongr
      _ = _ := by ring
  have hD : PowerEnvelope H (1 / publicDelta n) 47 := by
    apply polynomial_envelope hn (by positivity) (a := 44) (b := 3)
    exact (publicDelta_inv_le hn).trans (by gcongr)
  have hE : PowerEnvelope H (1 / E.η) 70 :=
    polynomial_envelope hn (by positivity) (publicTolerance_inv_polynomial hn)
  exact ⟨hL, hM, hU, hε, hC, hT, hD, hE⟩

/-- Explicit polynomial bounds for the real numerical envelopes of Newton.
Only logarithms of these magnitudes enter the query count. -/
theorem newton_scalar_envelopes {n : ℕ} (hn : 2 ≤ n) :
    let H := queryHeight n
    let E := publicEnvironment n
    PowerEnvelope H (1 / E.sst) 39 ∧ PowerEnvelope H E.dp 12 ∧
    PowerEnvelope H (1 / E.ell) 82 ∧ PowerEnvelope H E.Q 42 ∧
    PowerEnvelope H E.X 148 ∧ PowerEnvelope H (E.Epi E.Mbar) 256 ∧
    PowerEnvelope H (E.P1 E.Mbar) 272 ∧ PowerEnvelope H E.Ppub 334 ∧
    PowerEnvelope H (1 / E.β) 405 ∧ PowerEnvelope H E.Λ 18 ∧
    PowerEnvelope H E.Xk 251 ∧ PowerEnvelope H E.W 13 := by
  intro H E
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hH : 2 ≤ H := queryHeight_two_le hn
  have hH1 : 1 ≤ H := by linarith
  obtain ⟨hL, hM, hU, hε, hC, hT, hΔ, hη⟩ := base_scalar_envelopes hn
  have hEn : E.n = n := rfl
  change PowerEnvelope H E.Mbar 4 at hM
  change PowerEnvelope H E.U 3 at hU
  change PowerEnvelope H (1 / E.ε) 9 at hε
  change PowerEnvelope H E.C 12 at hC
  change PowerEnvelope H (1 / E.η) 70 at hη
  have hnH : PowerEnvelope H (n : ℝ) 1 := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    change (n : ℝ) ≤ (2 * n) ^ 1
    nlinarith
  have h1 := PowerEnvelope.one H
  have h2 : PowerEnvelope H 2 1 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have h4 : PowerEnvelope H 4 2 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have hε0 : 0 < E.ε := by
    change 0 < publicAccuracy n
    unfold publicAccuracy publicExtractionScale
    positivity
  have hM0 : 0 < E.Mbar := by change 0 < publicRows n; unfold publicRows; positivity
  have hU0 : 0 < E.U := by change 0 < publicWidth n; unfold publicWidth; positivity
  have hs0 : 0 < E.sst := by unfold NewtonPub.sst; positivity
  have he0 : 0 < E.ell := by unfold NewtonPub.ell; positivity
  have hη0 : 0 < E.η :=
    (calibratedTolerance_spec (publicLogSize_spec n).1 (publicDelta_spec n).1 (publicFinalCount n)).1
  have hs : PowerEnvelope H (1 / E.sst) 39 := by
    have hh := (((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 2 ^ 12)
      (le_rfl : (2 : ℝ) ^ 12 ≤ 2 ^ 12)).mul hnH).mul (hM.pow 2)).mul (hU.pow 3)
    convert hh.mul hε using 1
    change 1 / (E.ε / (2 ^ 12 * E.n * E.Mbar ^ 2 * E.U ^ 3)) =
      2 ^ 12 * (n : ℝ) * E.Mbar ^ 2 * E.U ^ 3 * (1 / E.ε)
    rw [one_div_div, hEn]
    ring
  have hd : PowerEnvelope H E.dp 12 := (h4.mul hM).mul (hU.pow 2)
  have he : PowerEnvelope H (1 / E.ell) 82 := by
    have hh := (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 16)
      (by norm_num : (16 : ℝ) ≤ 2 ^ 4)).mul (hs.pow 2)
    convert hh using 1
    change 1 / (E.sst ^ 2 / 16) = 16 * (1 / E.sst) ^ 2
    rw [one_div_div, one_div_pow]
    ring
  have hQ : PowerEnvelope H E.Q 42 := by
    have hfirst := (((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 64)
      (by norm_num : (64 : ℝ) ≤ 2 ^ 6)).mul hnH).mul hU).mul hε
    have hsecond := h4.mul hs
    convert hfirst.add hH hsecond using 1 <;>
      (try simp only [NewtonPub.Q, hEn, div_eq_mul_inv, one_mul]) <;> norm_num
  have hsM : PowerEnvelope H (Real.sqrt (2 * E.Mbar)) 5 := (h2.mul hM).sqrt hH1
  have hsM' : PowerEnvelope H (Real.sqrt E.Mbar) 4 := hM.sqrt hH1
  have hπ : PowerEnvelope H (E.Ppi E.Mbar) 148 := by
    exact ((((h4.mul hsM).mul hsM').mul hd).mul (hQ.add hH h1)).div he
  have hEπ : PowerEnvelope H (E.Epi E.Mbar) 256 := by
    have hpart1 := (h2.mul he).mul
      ((((hsM.mul hsM').mul hd).mul (hQ.add hH h2)).add hH
        (((hsM.pow 2).mul hd).mul hπ))
    have hsℓ : PowerEnvelope H (Real.sqrt (2 / E.ell)) 83 := (h2.div he).sqrt hH1
    have hsd : PowerEnvelope H (Real.sqrt (3 / 2 * E.dp)) 13 :=
      ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 3 / 2)
        (by norm_num : (3 / 2 : ℝ) ≤ 2 ^ 1)).mul hd).sqrt hH1
    have hpart2 := ((hsℓ.mul (hsd.mul hsM)).mul hπ).add hH hsℓ
    have hpart3 := hnH.sqrt hH1
    convert (hpart1.add hH hpart2).add hH hpart3 using 1 <;>
      (try simp only [NewtonPub.Epi, hEn, div_eq_mul_inv, one_mul]) <;> norm_num
  have hs2 : PowerEnvelope H (Real.sqrt 2) 1 := h2.sqrt hH1
  have hP1 : PowerEnvelope H (E.P1 E.Mbar) 272 := by
    have hpart1 := hd.mul (hQ.add hH (hs2.mul hπ))
    have hpart2 := (h2.mul hd).mul (h1.add hH (hs2.mul hEπ))
    exact hpart1.add hH hpart2
  have hceil : PowerEnvelope H (⌈Real.sqrt n⌉₊ : ℝ) 2 := by
    have hsqrt : Real.sqrt (n : ℝ) ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
    exact (hnH.add hH h1).of_le (Nat.cast_nonneg _)
      ((Nat.ceil_lt_add_one (Real.sqrt_nonneg (n : ℝ))).le.trans (by linarith))
  have hP : PowerEnvelope H E.Ppub 334 := by
    have hleft := (h2.mul (h1.add hH ((h2.mul hC).mul hceil))).div hs
    have hright := h1.add hH (hs2.mul hM)
    exact (hleft.mul hright).mul hP1
  have hβ : PowerEnvelope H (1 / E.β) 405 := by
    have hpmax := hP.max (h1.weaken hH1 (by omega : 0 ≤ 334))
    have hsum := h4.add hH (hpmax.mul hη)
    have hb0 := NewtonPub.β_pos hη0
    refine hsum.of_le (by positivity) ?_
    change 1 / min (1 / 4 : ℝ) (E.η / max E.Ppub 1) ≤ _
    have h := one_div_min_le_add (by norm_num : (0 : ℝ) < 1 / 4)
      (div_pos hη0 (lt_of_lt_of_le one_pos (le_max_right E.Ppub 1)))
    simp only [one_div_div, div_one] at h
    simpa only [div_eq_mul_inv, one_mul] using h
  have hΛ : PowerEnvelope H E.Λ 18 := by
    have hthree : PowerEnvelope H 3 2 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
    convert (hthree.mul hd).mul hM using 1
    unfold NewtonPub.Λ
    ring
  have htiny : PowerEnvelope H (1 / (2 : ℝ) ^ E.p) 0 := by
    refine ⟨by positivity, ?_⟩
    simp only [pow_zero]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ E.p)
  have hXk : PowerEnvelope H E.Xk 251 := by
    have hs32 : PowerEnvelope H (Real.sqrt (1 / (E.sst ^ 2 / 16 / 2))) 83 := by
      have hh := ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 32)
        (by norm_num : (32 : ℝ) ≤ 2 ^ 5)).mul (hs.pow 2)).sqrt hH1
      convert hh using 1
      congr 1
      field_simp
      all_goals norm_num
    have hsΛ := hΛ.sqrt hH1
    have hinner := (hsΛ.mul hπ).add hH (h2.mul (hsΛ.mul ((hnH.sqrt hH1).mul htiny)))
    exact hπ.add hH (hs32.mul hinner)
  have hW : PowerEnvelope H E.W 13 := by
    have hfactor : PowerEnvelope H (1 + E.β) 1 :=
      h2.of_le (by linarith [(NewtonPub.β_pos hη0).le]) (by linarith [NewtonPub.β_le (E := E)])
    exact hfactor.mul hd
  exact ⟨hs, hd, he, hQ, hπ, hEπ, hP1, hP, hβ, hΛ, hXk, hW⟩

/-- The actual fixed Newton iteration and aggregate magnitude counts are logarithmic. -/
theorem newton_iteration_bits_le {n : ℕ} (hn : 2 ≤ n) :
    let E := publicEnvironment n
    (E.k : ℝ) ≤ 512 * envelopeLog n ∧
    (E.Brhs : ℝ) ≤ 1024 * envelopeLog n ∧
    (E.Bmv : ℝ) ≤ 2048 * envelopeLog n ∧
    (E.Brep : ℝ) ≤ 2048 * envelopeLog n := by
  intro E
  let H := queryHeight n
  let L := envelopeLog n
  have hH : 2 ≤ H := queryHeight_two_le hn
  have hH1 : 1 ≤ H := by linarith
  have hL : 1 ≤ L := envelopeLog_one_le hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨_, _, he, hQ, _, _, _, _, hβ, hΛ, hX, hW⟩ := newton_scalar_envelopes hn
  have h2 : PowerEnvelope H 2 1 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have hnH : PowerEnvelope H (n : ℝ) 1 := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    change (n : ℝ) ≤ (2 * n) ^ 1
    nlinarith
  have hk : (E.k : ℝ) ≤ 405 * L + 2 := hβ.clog hH
  have hp : (E.p : ℝ) ≤ 425 * L + 2 := by
    exact (((h2.mul (hΛ.sqrt hH1)).mul (hnH.sqrt hH1)).div hβ).clog hH
  have hpD : (E.pD : ℝ) ≤ 487 * L + 2 := by
    have hratio : PowerEnvelope H (1 / (E.β * E.ell)) 487 := by
      convert hβ.mul he using 1 <;> simp only [one_div, mul_inv_rev] <;> ring
    exact hratio.clog hH
  have hpq : (E.pq : ℝ) ≤ 425 * L + 2 := by
    change ((max E.p (bits 1 E.β) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max]
    apply max_le hp
    have hh : (bits 1 E.β : ℝ) ≤ 405 * L + 2 := hβ.clog hH
    linarith
  have hrhs : (magBits (E.W * E.Qz) : ℝ) ≤ 55 * L + 3 := (hW.mul hQ).magBits hH
  have hmv : (magBits (E.W * (2 * E.Xk)) : ℝ) ≤ 265 * L + 3 :=
    (hW.mul (h2.mul hX)).magBits hH
  have hrep : (magBits (E.W * (E.Qz + 2 * E.Xk)) : ℝ) ≤ 266 * L + 3 :=
    (hW.mul (hQ.add hH (h2.mul hX))).magBits hH
  have hBrhs : (E.Brhs : ℝ) ≤ (magBits (E.W * E.Qz) : ℝ) + (E.pD + E.pq) := by
    have hh := E.Brhs_le
    exact_mod_cast hh
  have hBmv : (E.Bmv : ℝ) ≤ (magBits (E.W * (2 * E.Xk)) : ℝ) + (E.pD + E.p) := by
    have hh := E.Bmv_le
    exact_mod_cast hh
  have hBrep : (E.Brep : ℝ) ≤ (magBits (E.W * (E.Qz + 2 * E.Xk)) : ℝ) + (E.pD + E.pq) := by
    have hh := E.Brep_le
    exact_mod_cast hh
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Deterministic queries in the actual Newton primitive, excluding its spectral call. -/
theorem newton_deterministic_budget_le {n : ℕ} (hn : 2 ≤ n) :
    let E := publicEnvironment n
    ((6 * n * (E.Brhs + E.k * E.Bmv + E.Brep) : ℕ) : ℝ) ≤
      2 ^ 23 * n * envelopeLog n ^ 2 := by
  intro E
  obtain ⟨hk, hrhs, hmv, hrep⟩ := newton_iteration_bits_le hn
  have hL := envelopeLog_one_le hn
  have hprod := mul_le_mul hk hmv (Nat.cast_nonneg _) (by positivity : 0 ≤ 512 * envelopeLog n)
  have hinner : (E.Brhs : ℝ) + (E.k : ℝ) * E.Bmv + E.Brep ≤
      1051648 * envelopeLog n ^ 2 := by nlinarith
  push_cast
  calc 6 * (n : ℝ) * ((E.Brhs : ℝ) + (E.k : ℝ) * E.Bmv + E.Brep) ≤
      6 * n * (1051648 * envelopeLog n ^ 2) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ 2 ^ 23 * n * envelopeLog n ^ 2 := by
      have : 0 ≤ (n : ℝ) * envelopeLog n ^ 2 := by positivity
      nlinarith

/-- The actual restarted Lewis loop has a logarithmic public length. -/
theorem publicLewis_count_le {n : ℕ} (hn : 2 ≤ n) :
    (batchJL (publicEnvironment n) (publicDelta n) : ℝ) ≤ 256 * envelopeLog n := by
  let H := queryHeight n
  let E := publicEnvironment n
  let L := envelopeLog n
  have hH : 2 ≤ H := queryHeight_two_le hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 1 ≤ L := envelopeLog_one_le hn
  obtain ⟨_, hM, hU, _, _, _, hΔ, _⟩ := base_scalar_envelopes hn
  obtain ⟨hs, _⟩ := newton_scalar_envelopes hn
  change PowerEnvelope H E.Mbar 4 at hM
  change PowerEnvelope H E.U 3 at hU
  change PowerEnvelope H (1 / E.sst) 39 at hs
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hM1 : 1 ≤ E.Mbar := by change 1 ≤ publicRows n; unfold publicRows; nlinarith [sq_nonneg (n : ℝ)]
  have hU1 : 1 ≤ E.U := by change 1 ≤ 4 * (n : ℝ); linarith
  have hε0 : 0 < E.ε := by
    change 0 < publicAccuracy n
    unfold publicAccuracy publicExtractionScale
    positivity
  have hε1 : E.ε ≤ 1 := by
    change publicExtractionScale n / 16 ≤ 1
    linarith [(publicExtractionScale_spec hn).2.1]
  have hs0 : 0 < E.sst := by unfold NewtonPub.sst; positivity
  have hs1 : E.sst ≤ 1 := by
    have hden : 1 ≤ (2 : ℝ) ^ 12 * n * E.Mbar ^ 2 * E.U ^ 3 := by
      calc (1 : ℝ) ≤ 2 ^ 12 * 1 * 1 ^ 2 * 1 ^ 3 := by norm_num
        _ ≤ 2 ^ 12 * n * E.Mbar ^ 2 * E.U ^ 3 := by gcongr
    change E.ε / (2 ^ 12 * n * E.Mbar ^ 2 * E.U ^ 3) ≤ 1
    exact (div_le_one (by positivity)).mpr (hε1.trans hden)
  have hq0 : 0 < lewisQ E.Mbar E.U E.sst := by unfold lewisQ; positivity
  have hq1 : lewisQ E.Mbar E.U E.sst ≤ 1 := by
    have hden : 1 ≤ 8 * E.Mbar * E.U ^ 2 := by
      calc (1 : ℝ) ≤ 8 * 1 * 1 ^ 2 := by norm_num
        _ ≤ 8 * E.Mbar * E.U ^ 2 := by gcongr
    unfold lewisQ
    rw [div_le_one (by positivity)]
    exact (pow_le_one₀ hs0.le hs1).trans hden
  have hi : PowerEnvelope H (1 / lewisQ E.Mbar E.U E.sst) 91 := by
    have hh := (((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 8)
      (by norm_num : (8 : ℝ) ≤ 2 ^ 3)).mul hM).mul (hU.pow 2)).mul (hs.pow 2)
    convert hh using 1
    change 1 / (E.sst ^ 2 / (8 * E.Mbar * E.U ^ 2)) =
      8 * E.Mbar * E.U ^ 2 * (1 / E.sst) ^ 2
    rw [one_div_div, one_div_pow]
    ring
  have hE0 : 0 ≤ lewisE0 E.Mbar E.U E.sst :=
    Real.log_nonneg ((le_div_iff₀ hq0).mpr (by simpa using hq1))
  have hE : lewisE0 E.Mbar E.U E.sst ≤ 91 * L := hi.logarithm hH (by positivity)
  have hLH : L ≤ H := by
    change envelopeLog n ≤ queryHeight n
    rw [envelopeLog_eq n (by omega)]
    unfold queryHeight
    linarith [queryLog_le hn]
  have hHp : PowerEnvelope H H 1 := ⟨by linarith, by simp⟩
  have hEp : PowerEnvelope H (lewisE0 E.Mbar E.U E.sst + 1) 8 :=
    ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 128)
      (by norm_num : (128 : ℝ) ≤ 2 ^ 7)).mul hHp).of_le (by linarith) (by linarith)
  have hratio : PowerEnvelope H
      (1 / (publicDelta n / (32 * (lewisE0 E.Mbar E.U E.sst + 1)))) 60 := by
    have hh := ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 32)
      (by norm_num : (32 : ℝ) ≤ 2 ^ 5)).mul hEp).mul hΔ
    convert hh using 1
    rw [one_div_div]
    ring
  have hh : (Nat.clog 2 ⌈1 / (publicDelta n /
      (32 * (lewisE0 E.Mbar E.U E.sst + 1)))⌉₊ : ℝ) ≤ 60 * L + 2 := hratio.clog hH
  change ((3 * Nat.clog 2 ⌈1 / (publicDelta n /
    (32 * (lewisE0 E.Mbar E.U E.sst + 1)))⌉₊ : ℕ) : ℝ) ≤ _
  push_cast
  linarith

/-- The full public spectral-call allocation is inverse polynomial before taking logs. -/
theorem publicCallCount_envelope {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) :
    PowerEnvelope (queryHeight n) (publicCallCount n s t : ℝ) 95 := by
  let H := queryHeight n
  let E := publicEnvironment n
  let P := calibratedParams n s t 1
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hH : 2 ≤ H := queryHeight_two_le hn
  have hnH : PowerEnvelope H (n : ℝ) 1 := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    change (n : ℝ) ≤ (2 * n) ^ 1
    nlinarith
  have hq : PowerEnvelope H (queryLog n) 1 :=
    hnH.of_le (by linarith [queryLog_one_le hn]) (queryLog_le hn)
  have hL : PowerEnvelope H (envelopeLog n) 1 := by
    refine ⟨by linarith [envelopeLog_one_le hn], ?_⟩
    change envelopeLog n ≤ (2 * n) ^ 1
    rw [envelopeLog_eq n (by omega), pow_one]
    linarith [queryLog_le hn]
  have hJL : PowerEnvelope H (batchJL E (publicDelta n) : ℝ) 9 :=
    ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 256)
      (by norm_num : (256 : ℝ) ≤ 2 ^ 8)).mul hL).of_le
      (Nat.cast_nonneg _) (publicLewis_count_le hn)
  have hphase : PowerEnvelope H (2 ^ 74 * Real.sqrt n * queryLog n ^ 6) 81 :=
    ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 2 ^ 74)
      (le_rfl : (2 : ℝ) ^ 74 ≤ 2 ^ 74)).mul (hnH.sqrt (by linarith))).mul (hq.pow 6)
  have hdown : PowerEnvelope H (P.downSteps : ℝ) 81 :=
    hphase.of_le (Nat.cast_nonneg _) (calibratedDownSteps_le hn s t 1)
  have hup : PowerEnvelope H (P.upSteps : ℝ) 81 :=
    hphase.of_le (Nat.cast_nonneg _) (calibratedUpSteps_le hn s t 1)
  have hfinal : PowerEnvelope H (P.finalSteps : ℝ) 6 :=
    ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 20)
      (by norm_num : (20 : ℝ) ≤ 2 ^ 5)).mul hq).of_le
      (Nat.cast_nonneg _) (publicFinalCount_le hn)
  have h1 := PowerEnvelope.one H
  have hh := (hJL.add hH (((hdown.add hH h1).add hH hup).mul (h1.add hH hJL))).add hH hfinal
  simp only [publicCallCount, solverSpectralCap, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  change PowerEnvelope H ((batchJL E (publicDelta n) : ℝ) +
    ((P.downSteps : ℝ) + 1 + P.upSteps) * (1 + (batchJL E (publicDelta n) : ℝ)) +
      (P.finalSteps : ℝ)) 95
  exact hh

/-- The support parameters already used by every calibrated batch. -/
def publicSupport (n : ℕ) : SupPub :=
  batchSup (publicRows n) (publicLogSize n) (1 / (2 * publicRows n))
    (publicDelta n) (publicEnvelope n)

private theorem support_scalar_envelopes {n : ℕ} (hn : 2 ≤ n) :
    let H := queryHeight n
    let S := publicSupport n
    PowerEnvelope H (S.Λ ^ 2 * S.Ap / S.ρ ^ 2 / (S.σ / 54)) 597 ∧
    PowerEnvelope H (1 / (S.σ / (6 * (S.Lb + 1)))) 99 ∧
    PowerEnvelope H (S.Mbar / S.δt) 210 ∧ PowerEnvelope H S.Φ 189 := by
  intro H S
  have hH : 2 ≤ H := queryHeight_two_le hn
  have hH1 : 1 ≤ H := by linarith
  obtain ⟨hL, hM, _, _, hCpub, hT, hΔ, _⟩ := base_scalar_envelopes hn
  let L := publicLogSize n
  let M := publicRows n
  change PowerEnvelope H M 4 at hM
  let T := publicEnvelope n
  let Δ := publicDelta n
  let Q := 2 * M * T / Δ
  let wmin := 2 / (5 * M)
  let C := 96 * L
  let Cs := (1 - 3 * (1 / (2 * L)) / 4) * Δ
  let σ := 1 / (16000 * L)
  have hL2 : 2 ≤ L := (publicLogSize_spec n).1
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by dsimp [M, publicRows]; positivity
  have hT0 : 0 < T := by linarith [publicEnvelope_one_le n]
  have hD0 : 0 < Δ := (publicDelta_spec n).1
  have hD1 : Δ ≤ 1 := (publicDelta_spec n).2.2
  have ha0 : 0 < 1 / (2 * L) := by positivity
  have ha1 : 1 / (2 * L) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hCs0 : 0 < Cs := by
    dsimp [Cs]
    exact mul_pos (by linarith) hD0
  have hCs1 : Cs ≤ 1 := by
    dsimp [Cs]
    nlinarith [mul_nonneg ha0.le hD0.le]
  have hσ0 : 0 < σ := by dsimp [σ]; positivity
  have hσ1 : σ ≤ 1 := by dsimp [σ]; rw [div_le_one (by positivity)]; linarith
  have hw0 : 0 < wmin := by dsimp [wmin]; positivity
  have hC0 : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hqeq :
      2 * (1 / (2 * L) / 8 / (12 * Δ)) * (12 * M * T / (1 / (2 * L) / 8)) = Q := by
    dsimp [Q]
    field_simp
    all_goals ring
  have hweq : (4 / 5 : ℝ) * (1 / (2 * M)) = wmin := by dsimp [wmin]; ring
  have hceq : 48 * (2 * L) = C := by dsimp [C]; ring
  have hσeq : 1 / (2 * L) / 8 / 1000 = σ := by dsimp [σ]; ring
  have hS : S = envSup M Q wmin C Cs σ := by
    change batchSup M L (1 / (2 * M)) Δ T = _
    unfold batchSup
    rw [hqeq, hweq, hceq, hσeq]
  have h1 := PowerEnvelope.one H
  have h2 : PowerEnvelope H 2 1 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have h4 : PowerEnvelope H 4 2 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have hQ : PowerEnvelope H Q 66 := ((h2.mul hM).mul hT).div hΔ
  have hCinv : PowerEnvelope H (1 / C) 0 := by
    refine h1.of_le (by positivity) ?_
    exact (div_le_one hC0).mpr hC1
  have hwInv : PowerEnvelope H (1 / wmin) 6 := by
    convert (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 2 ^ 2)).mul hM using 1
    dsimp [wmin]
    field_simp
  have hwSqrt : PowerEnvelope H (1 / Real.sqrt wmin) 6 := by
    simpa only [one_div, Real.sqrt_inv] using hwInv.sqrt hH1
  have hCs : PowerEnvelope H Cs 0 := h1.of_le hCs0.le hCs1
  have hAbar : PowerEnvelope H S.Abar 72 := by
    have hh := (hCs.mul hQ).mul (hCinv.mul hwSqrt)
    convert hh using 1
    rw [hS]
    dsimp [envSup]
    field_simp
  have hAp : PowerEnvelope H S.Ap 76 := by
    have hh := (hM.sqrt hH1).mul hAbar
    simpa only [hS, envSup] using hh
  have hSq : PowerEnvelope H S.Sq 70 := by
    simpa only [hS, envSup] using hM.mul hQ
  have hLb : PowerEnvelope H S.Lb 76 := by
    have hh := hAp.max ((hCs.mul hSq).weaken hH1 (by norm_num : 70 ≤ 76))
    simpa only [hS, envSup] using hh
  have hσInv : PowerEnvelope H (1 / S.σ) 19 := by
    have hh := (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 16000)
      (by norm_num : (16000 : ℝ) ≤ 2 ^ 14)).mul hL
    simpa only [hS, envSup, σ, one_div_one_div] using hh
  have hSσ0 : 0 < S.σ := by simpa only [hS, envSup] using hσ0
  have hSσ1 : S.σ ≤ 1 := by simpa only [hS, envSup] using hσ1
  have hρInv : PowerEnvelope H (1 / S.ρ) 22 := by
    have hh := (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 6)
      (by norm_num : (6 : ℝ) ≤ 2 ^ 3)).mul hσInv
    convert hh using 1
    change 1 / (S.σ / 6) = 6 * (1 / S.σ)
    rw [one_div_div]
    ring
  have hρ0 : 0 < S.ρ := by unfold SupPub.ρ; positivity
  have hρ : PowerEnvelope H S.ρ 0 := by
    refine h1.of_le hρ0.le ?_
    unfold SupPub.ρ
    linarith
  have hratio : PowerEnvelope H (1 / (S.σ / (6 * (S.Lb + 1)))) 99 := by
    have hh := ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 6)
      (by norm_num : (6 : ℝ) ≤ 2 ^ 3)).mul (hLb.add hH h1)).mul hσInv
    convert hh using 1
    rw [one_div_div]
    ring
    all_goals norm_num
  have hh0 : 0 < S.h := by
    unfold SupPub.h
    have := hLb.nonneg
    positivity
  have hhInv : PowerEnvelope H (1 / S.h) 100 := by
    refine (h4.add hH hratio).of_le (by positivity) ?_
    change 1 / min (1 / 4 : ℝ) (S.σ / (6 * (S.Lb + 1))) ≤ _
    have h := one_div_min_le_add (by norm_num : (0 : ℝ) < 1 / 4)
      (by have := hLb.nonneg; positivity : 0 < S.σ / (6 * (S.Lb + 1)))
    simpa only [one_div_div, div_one] using h
  have hΛ : PowerEnvelope H S.Λ 176 := hAp.div hhInv
  have hm : PowerEnvelope H (S.Λ ^ 2 * S.Ap / S.ρ ^ 2 / (S.σ / 54)) 597 := by
    have hh := ((((hΛ.pow 2).mul hAp).mul (hρInv.pow 2)).mul
      (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 54)
        (by norm_num : (54 : ℝ) ≤ 2 ^ 6))).mul hσInv
    have hh' : PowerEnvelope H (S.Λ ^ 2 * S.Ap * (1 / S.ρ) ^ 2 * 54 * (1 / S.σ)) 497 := hh
    convert hh'.weaken hH1 (by norm_num : 497 ≤ 597) using 1
    field_simp
    all_goals ring
  have hcδ : PowerEnvelope H S.cδ 181 := by
    have hfirst := (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (3 : ℝ) ≤ 2 ^ 2)).mul hΛ
    have hsecond := h4.mul hρ
    have hthird : PowerEnvelope H (S.Ap / (2 * S.h)) 176 := by
      convert (hAp.mul hhInv).mul (PowerEnvelope.constant hH
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 2 ^ 0)) using 1
      field_simp
      all_goals ring
    exact ((hfirst.add hH hsecond).add hH hthird).add hH h4
  have hcδ0 : 0 < S.cδ := by
    unfold SupPub.cδ
    have := hΛ.nonneg
    have := hAp.nonneg
    positivity
  have hδInv : PowerEnvelope H (1 / S.δt) 206 := by
    have hfirst : PowerEnvelope H (1 / (S.σ / (27 * S.cδ))) 205 := by
      have hh := ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 27)
        (by norm_num : (27 : ℝ) ≤ 2 ^ 5)).mul hcδ).mul hσInv
      convert hh using 1
      rw [one_div_div]
      ring
    have hsecond : PowerEnvelope H (1 / (3 * S.h ^ 2 / 4)) 202 := by
      have hh := ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 4 / 3)
        (by norm_num : (4 / 3 : ℝ) ≤ 2 ^ 2)).mul (hhInv.pow 2))
      convert hh using 1
      field_simp
      all_goals ring
    have hδ0 : 0 < S.δt := by unfold SupPub.δt; positivity
    refine (hfirst.add hH hsecond).of_le (by positivity) ?_
    exact one_div_min_le_add (by positivity) (by positivity)
  have hp : PowerEnvelope H (S.Mbar / S.δt) 210 := by
    have hh := hM.div hδInv
    simpa only [hS, envSup] using hh
  have hΦ : PowerEnvelope H S.Φ 189 := by
    have hfirst : PowerEnvelope H (S.Abar ^ 2 / (4 * S.ρ ^ 2)) 188 := by
      have hh := (((hAbar.pow 2).mul (hρInv.pow 2)).mul
        (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) ≤ 2 ^ 0)))
      convert hh using 1
      field_simp
      all_goals ring
    have hsecond : PowerEnvelope H (S.Abar ^ 2 / (2 * S.ρ)) 166 := by
      have hh := (((hAbar.pow 2).mul hρInv).mul
        (PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) ≤ 2 ^ 0)))
      convert hh using 1
      field_simp
      all_goals ring
    exact hfirst.add hH hsecond
  exact ⟨hm, hratio, hp, hΦ⟩

/-- All three search/aggregate counts in the actual support query cap are logarithmic. -/
theorem publicSupport_bits_le {n : ℕ} (hn : 2 ≤ n) :
    let S := publicSupport n
    (S.m : ℝ) ≤ 1024 * envelopeLog n ∧
    (S.N : ℝ) ≤ 256 * envelopeLog n ∧
    (S.B : ℝ) ≤ 512 * envelopeLog n := by
  intro S
  let H := queryHeight n
  let L := envelopeLog n
  have hH : 2 ≤ H := queryHeight_two_le hn
  have hL : 1 ≤ L := envelopeLog_one_le hn
  obtain ⟨hm, hN, hp, hΦ⟩ := support_scalar_envelopes hn
  have hmc : (S.m : ℝ) ≤ 597 * L + 2 := hm.clog hH
  have hNc : (S.N : ℝ) ≤ 2 * (99 * L + 2) := by
    have hh : (Nat.clog 2 ⌈1 / (S.σ / (6 * (S.Lb + 1)))⌉₊ : ℝ) ≤ 99 * L + 2 := hN.clog hH
    change ((2 * Nat.clog 2 ⌈1 / (S.σ / (6 * (S.Lb + 1)))⌉₊ : ℕ) : ℝ) ≤ _
    push_cast
    linarith
  have hpc : (S.p : ℝ) ≤ 210 * L + 2 := hp.clog hH
  have hplus : (magBits (S.Φ + 1) : ℝ) ≤ 190 * L + 3 :=
    (hΦ.add hH (PowerEnvelope.one H)).magBits hH
  have hBnat : S.B ≤ magBits (S.Φ + 1) + S.p := by
    have hi : S.Φ * (2 : ℝ) ^ S.p + 1 ≤ (S.Φ + 1) * 2 ^ S.p := by
      nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := S.p)]
    have hmono : magBits (S.Φ * (2 : ℝ) ^ S.p + 1) ≤ magBits ((S.Φ + 1) * 2 ^ S.p) :=
      Nat.add_le_add_right (clog_ceil_mono hi) 1
    exact hmono.trans (magBits_mul_pow _ _)
  have hB : (S.B : ℝ) ≤ (magBits (S.Φ + 1) : ℝ) + S.p := by exact_mod_cast hBnat
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Actual support query cost, uniformly over every input state and every oracle. -/
theorem publicSupport_budget_le {n : ℕ} (hn : 2 ≤ n) :
    let S := publicSupport n
    (((2 * S.N + 2) * ((S.m + 3) * (6 * S.B * n)) : ℕ) : ℝ) ≤
      2 ^ 34 * n * envelopeLog n ^ 3 := by
  intro S
  obtain ⟨hm, hN, hB⟩ := publicSupport_bits_le hn
  have hL := envelopeLog_one_le hn
  have hN' : 2 * (S.N : ℝ) + 2 ≤ 514 * envelopeLog n := by linarith
  have hm' : (S.m : ℝ) + 3 ≤ 1027 * envelopeLog n := by linarith
  push_cast
  calc (2 * (S.N : ℝ) + 2) * (((S.m : ℝ) + 3) * (6 * (S.B : ℝ) * n)) ≤
      (514 * envelopeLog n) * ((1027 * envelopeLog n) * (6 * (512 * envelopeLog n) * n)) := by
        gcongr
    _ ≤ 2 ^ 34 * n * envelopeLog n ^ 3 := by
      have : 0 ≤ (n : ℝ) * envelopeLog n ^ 3 := by positivity
      nlinarith

/-- The single logarithm in the final uniform query bounds. -/
def failureLog (n : ℕ) (ζ : ℝ) : ℝ := Real.logb 2 (queryHeight n / ζ)

private theorem log_le_logb_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ Real.logb 2 x := by
  have hb : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hxlog : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  have he : Real.log x = Real.logb 2 x * Real.log 2 := by
    rw [Real.logb, div_mul_cancel₀ _ hb.ne']
  rw [he]
  nlinarith

theorem failureLog_spec {n : ℕ} (hn : 2 ≤ n) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    1 ≤ failureLog n ζ ∧ envelopeLog n ≤ failureLog n ζ ∧
      Real.log (2 / ζ) ≤ failureLog n ζ := by
  have hH : 2 ≤ queryHeight n := queryHeight_two_le hn
  have hdiv : queryHeight n ≤ queryHeight n / ζ := by
    rw [le_div_iff₀ hζ]
    nlinarith
  have hmain : envelopeLog n ≤ failureLog n ζ :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hdiv
  refine ⟨(envelopeLog_one_le hn).trans hmain, hmain, ?_⟩
  have h2 : (1 : ℝ) ≤ 2 / ζ := (le_div_iff₀ hζ).mpr (by linarith)
  refine (log_le_logb_two h2).trans ?_
  exact Real.logb_le_logb_of_le (by norm_num) (by positivity)
    (div_le_div_of_nonneg_right hH hζ.le)

/-- The actual spectral logarithm after the noncircular call allocation. -/
theorem calibrated_spectral_log_le {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    Sparsify.Dlog n 2 (publicDelta n / 4096) (publicCallFailure n s t ζ) ≤
      160 * failureLog n ζ := by
  let H := queryHeight n
  have hH : 2 ≤ H := queryHeight_two_le hn
  have hH0 : 0 < H := by linarith
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔ0 := (publicDelta_spec n).1
  have hcall := publicCallFailure_spec s t hζ hζ1
  have hcall0 := hcall.1
  obtain ⟨_, _, _, _, _, _, hΔ, _⟩ := base_scalar_envelopes hn
  have hc := publicCallCount_envelope hn s t
  have h4 : PowerEnvelope H 4 2 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have h4096 : PowerEnvelope H 4096 12 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have hnH : PowerEnvelope H (n : ℝ) 1 := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    change (n : ℝ) ≤ (2 * n) ^ 1
    nlinarith
  have hnum : PowerEnvelope H
      (4 * n * 4096 * (1 / publicDelta n) * 4 * ((publicCallCount n s t : ℝ) + 1)) 160 :=
    (((((h4.mul hnH).mul h4096).mul hΔ).mul h4).mul
      (hc.add hH (PowerEnvelope.one H)))
  have he : 2 * 2 * n / ((publicDelta n / 4096) * publicCallFailure n s t ζ) =
      (4 * n * 4096 * (1 / publicDelta n) * 4 * ((publicCallCount n s t : ℝ) + 1)) / ζ := by
    unfold publicCallFailure
    field_simp
    all_goals ring
  have hb : 2 * 2 * n / ((publicDelta n / 4096) * publicCallFailure n s t ζ) ≤ H ^ 160 / ζ := by
    rw [he]
    exact div_le_div_of_nonneg_right hnum.le_pow hζ.le
  have hlog := Real.log_le_log
    (by positivity : 0 < 2 * 2 * n / ((publicDelta n / 4096) * publicCallFailure n s t ζ)) hb
  have hid : Real.log (H ^ 160 / ζ) = 160 * Real.log H + Real.log (1 / ζ) := by
    rw [div_eq_mul_one_div, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  rw [hid] at hlog
  have hi1 : (1 : ℝ) ≤ 1 / ζ := (le_div_iff₀ hζ).mpr (by simpa using hζ1)
  have hi0 : 0 ≤ Real.logb 2 (1 / ζ) := Real.logb_nonneg (by norm_num) hi1
  have hnlog := log_le_logb_two (by linarith : (1 : ℝ) ≤ H)
  have hilog := log_le_logb_two hi1
  have heq : failureLog n ζ = Real.logb 2 H + Real.logb 2 (1 / ζ) := by
    unfold failureLog
    rw [div_eq_mul_one_div, Real.logb_mul hH0.ne' (by positivity)]
  change Real.log (2 * 2 * n / ((publicDelta n / 4096) * publicCallFailure n s t ζ)) ≤ _
  rw [heq]
  linarith

/-- The literal calibrated spectral cap, using the checked production cost theorem. -/
theorem calibrated_spectral_budget_le {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    let P := calibratedParams n s t ζ
    ((P.rounds * Sparsify.levelBudget (n := n) P.Kd P.J P.samples + 3 * n : ℕ) : ℝ) ≤
      2 ^ 216 * n * failureLog n ζ ^ 14 := by
  intro P
  let L := failureLog n ζ
  have hD := publicDelta_spec n
  have hf := publicCallFailure_spec s t hζ hζ1
  have hΔ0 := hD.1
  have hΔ1 := hD.2.2
  have hs : Sparsify.Hyp n 2 (publicDelta n / 4096) (publicCallFailure n s t ζ) :=
    ⟨hn, by norm_num, by positivity, by linarith, hf.1, hf.2.1⟩
  have hb := Sparsify.budget_le hs
  have hL := (failureLog_spec hn hζ hζ1).1
  have hq : queryLog n ≤ L := by
    have he := envelopeLog_eq n (by omega : 0 < n)
    have hh := (failureLog_spec hn hζ hζ1).2.1
    linarith
  have hi : 1 / (publicDelta n / 4096) ≤ 2 ^ 56 * L ^ 3 := by
    have h := mul_le_mul_of_nonneg_left (publicDelta_inv_le hn)
      (by norm_num : (0 : ℝ) ≤ 4096)
    calc 1 / (publicDelta n / 4096) = 4096 * (1 / publicDelta n) := by ring
      _ ≤ 4096 * (2 ^ 44 * queryLog n ^ 3) := h
      _ ≤ 2 ^ 56 * L ^ 3 := by nlinarith [pow_le_pow_left₀ (by linarith [queryLog_one_le hn]) hq 3]
  have hlog := calibrated_spectral_log_le hn s t hζ hζ1
  have hcost : ((P.rounds * Sparsify.levelBudget (n := n) P.Kd P.J P.samples + 3 * n : ℕ) : ℝ) ≤
      4 * 10 ^ 10 * (1 / (publicDelta n / 4096)) ^ 2 * n *
        Sparsify.Dlog n 2 (publicDelta n / 4096) (publicCallFailure n s t ζ) ^ 8 := by
    change ((P.rounds * Sparsify.levelBudget (n := n) P.Kd P.J P.samples + 3 * n : ℕ) : ℝ) ≤
      2 * 10 ^ 10 * 2 / (publicDelta n / 4096) ^ 2 * n *
        Sparsify.Dlog n 2 (publicDelta n / 4096) (publicCallFailure n s t ζ) ^ 8 at hb
    convert hb using 1 <;> ring
  refine hcost.trans ?_
  calc 4 * 10 ^ 10 * (1 / (publicDelta n / 4096)) ^ 2 * n *
      Sparsify.Dlog n 2 (publicDelta n / 4096) (publicCallFailure n s t ζ) ^ 8 ≤
      4 * 10 ^ 10 * (2 ^ 56 * L ^ 3) ^ 2 * n * (160 * L) ^ 8 := by
        have hlog0 : 0 ≤ Sparsify.Dlog n 2 (publicDelta n / 4096) (publicCallFailure n s t ζ) :=
          le_trans (by norm_num : (0 : ℝ) ≤ 2) hs.D_ge
        gcongr
    _ ≤ 2 ^ 216 * n * L ^ 14 := by
      have hnonneg : 0 ≤ (n : ℝ) * L ^ 14 := by positivity
      nlinarith

/-- Bounds for all three actual budget components used by the solver. -/
theorem calibrated_primitive_budgets {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    let P := calibratedParams n s t ζ
    (P.newtonBudget : ℝ) ≤ 2 ^ 217 * n * failureLog n ζ ^ 14 ∧
    (P.initialBudget : ℝ) ≤ 2 ^ 224 * n * failureLog n ζ ^ 15 ∧
    (P.batchBudget : ℝ) ≤ 2 ^ 226 * n * failureLog n ζ ^ 15 := by
  intro P
  let L := failureLog n ζ
  let E := publicEnvironment n
  have hL := (failureLog_spec hn hζ hζ1).1
  have heL := (failureLog_spec hn hζ hζ1).2.1
  have hspec := calibrated_spectral_budget_le hn s t hζ hζ1
  change ((P.rounds * Sparsify.levelBudget (n := n) P.Kd P.J P.samples + 3 * n : ℕ) : ℝ) ≤
    2 ^ 216 * n * L ^ 14 at hspec
  have hdet := newton_deterministic_budget_le hn
  have hJL := publicLewis_count_le hn
  have hsup := publicSupport_budget_le hn
  have hdet' : ((6 * n * (E.Brhs + E.k * E.Bmv + E.Brep) : ℕ) : ℝ) ≤
      2 ^ 23 * n * L ^ 14 := by
    refine hdet.trans ?_
    have he2 : envelopeLog n ^ 2 ≤ L ^ 14 :=
      (pow_le_pow_left₀ (by linarith [envelopeLog_one_le hn]) heL 2).trans
        (pow_le_pow_right₀ hL (by norm_num))
    gcongr
  have hJL' : (batchJL E (publicDelta n) : ℝ) ≤ 256 * L := hJL.trans (by gcongr)
  have hsup' : (((2 * (publicSupport n).N + 2) *
      (((publicSupport n).m + 3) * (6 * (publicSupport n).B * n)) : ℕ) : ℝ) ≤
      2 ^ 34 * n * L ^ 15 := by
    refine hsup.trans ?_
    have he3 : envelopeLog n ^ 3 ≤ L ^ 15 :=
      (pow_le_pow_left₀ (by linarith [envelopeLog_one_le hn]) heL 3).trans
        (pow_le_pow_right₀ hL (by norm_num))
    gcongr
  have hnewton : (P.newtonBudget : ℝ) ≤ 2 ^ 217 * n * L ^ 14 := by
    have hn0 : 0 ≤ (n : ℝ) * L ^ 14 := by positivity
    have he : P.newtonBudget =
        (P.rounds * Sparsify.levelBudget (n := n) P.Kd P.J P.samples + 3 * n) +
          6 * n * (E.Brhs + E.k * E.Bmv + E.Brep) := rfl
    rw [he, Nat.cast_add]
    nlinarith only [hspec, hdet', hn0]
  have hinit : (P.initialBudget : ℝ) ≤ 2 ^ 224 * n * L ^ 15 := by
    have hh := mul_le_mul hJL' hspec (Nat.cast_nonneg _) (by positivity : 0 ≤ 256 * L)
    change ((batchJL E (publicDelta n) *
      ((P.rounds * Sparsify.levelBudget (n := n) P.Kd P.J P.samples + 3 * n) + 0) : ℕ) : ℝ) ≤ _
    push_cast at hh ⊢
    nlinarith
  have hbatch : (P.batchBudget : ℝ) ≤ 2 ^ 226 * n * L ^ 15 := by
    have hn0 : 0 ≤ (n : ℝ) * L ^ 15 := by positivity
    have h14 : L ^ 14 ≤ L ^ 15 := pow_le_pow_right₀ hL (by norm_num)
    have hnewton' : (P.newtonBudget : ℝ) ≤ 2 ^ 217 * n * L ^ 15 := hnewton.trans (by gcongr)
    have he : P.batchBudget = P.newtonBudget + P.initialBudget +
        (2 * (publicSupport n).N + 2) * (((publicSupport n).m + 3) * (6 * (publicSupport n).B * n)) := by
      rfl
    rw [he, Nat.cast_add, Nat.cast_add]
    nlinarith only [hnewton', hinit, hsup', hn0]
  exact ⟨hnewton, hinit, hbatch⟩

end
end CutQueryComplexity.ImplicitLP.PathFollowing

#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.newton_scalar_envelopes
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.newton_iteration_bits_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.newton_deterministic_budget_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicLewis_count_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicCallCount_envelope
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicSupport_bits_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicSupport_budget_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibrated_spectral_log_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibrated_spectral_budget_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibrated_primitive_budgets
