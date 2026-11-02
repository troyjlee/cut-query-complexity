import CutQueryComplexity.ImplicitLP.GenericQuery.Bounds

/-! # Logarithmic counts of the actual generic Newton and support primitives

Every estimate is derived from the original public input envelope. Explicit
coordinates are evaluated offline; the queried hidden pair coordinates retain
the production aggregate precision bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Real
open PathFollowing (PowerEnvelope one_div_min_le_add)
noncomputable section
variable {n me : ℕ} {D : Data n me} {P : Envelope}

theorem newton_scalar_envelopes (HP : PublicHyp D P) :
    let H := height n P
    let E := publicEnvironment n P
    PowerEnvelope H (1 / E.sst) 39 ∧ PowerEnvelope H E.dp 12 ∧
    PowerEnvelope H (1 / E.ell) 82 ∧ PowerEnvelope H E.Q 42 ∧
    PowerEnvelope H E.X 148 ∧ PowerEnvelope H (E.Epi E.Mbar) 256 ∧
    PowerEnvelope H (E.P1 E.Mbar) 272 ∧ PowerEnvelope H E.Ppub 334 ∧
    PowerEnvelope H (1 / E.β) 405 ∧ PowerEnvelope H E.Λ 18 ∧
    PowerEnvelope H E.Xk 251 ∧ PowerEnvelope H E.W 13 := by
  intro H E
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast HP.rank_ge
  have hH : 2 ≤ H := HP.height_inputs.1
  have hH1 : 1 ≤ H := by linarith
  obtain ⟨hL, hM, hU, hε, hC, hT, hΔ, hη⟩ := base_scalar_envelopes HP
  have hEn : E.n = n := rfl
  change PowerEnvelope H E.Mbar 4 at hM
  change PowerEnvelope H E.U 3 at hU
  change PowerEnvelope H (1 / E.ε) 9 at hε
  change PowerEnvelope H E.C 12 at hC
  change PowerEnvelope H (1 / E.η) 70 at hη
  have hnH : PowerEnvelope H (n : ℝ) 1 := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    simpa only [pow_one] using HP.height_inputs.2.1
  have h1 := PowerEnvelope.one H
  have h2 : PowerEnvelope H 2 1 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have h4 : PowerEnvelope H 4 2 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have hε0 : 0 < E.ε := HP.ε_pos
  have hM0 : 0 < E.Mbar := by change 0 < P.Mbar; linarith [HP.Mbar_ge_one]
  have hU0 : 0 < E.U := by change 0 < P.U; linarith [HP.U_ge]
  have hs0 : 0 < E.sst := by unfold NewtonPub.sst; positivity
  have he0 : 0 < E.ell := by unfold NewtonPub.ell; positivity
  have hη0 : 0 < E.η :=
    (PathFollowing.calibratedTolerance_spec (publicLogSize_spec P).1 (publicDelta_spec n P).1 (publicFinalCount n P)).1
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
theorem newton_iteration_bits_le (HP : PublicHyp D P) :
    let E := publicEnvironment n P
    (E.k : ℝ) ≤ 512 * logHeight n P ∧
    (E.Brhs : ℝ) ≤ 1024 * logHeight n P ∧
    (E.Bmv : ℝ) ≤ 2048 * logHeight n P ∧
    (E.Brep : ℝ) ≤ 2048 * logHeight n P := by
  intro E
  let H := height n P
  let L := logHeight n P
  have hH : 2 ≤ H := HP.height_inputs.1
  have hH1 : 1 ≤ H := by linarith
  have hL : 1 ≤ L := HP.logHeight_bounds.1
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast HP.rank_ge
  obtain ⟨_, _, he, hQ, _, _, _, _, hβ, hΛ, hX, hW⟩ := newton_scalar_envelopes HP
  have h2 : PowerEnvelope H 2 1 := PowerEnvelope.constant hH (by norm_num) (by norm_num)
  have hnH : PowerEnvelope H (n : ℝ) 1 := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    simpa only [pow_one] using HP.height_inputs.2.1
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
theorem newton_deterministic_budget_le (HP : PublicHyp D P) :
    let E := publicEnvironment n P
    ((6 * n * (E.Brhs + E.k * E.Bmv + E.Brep) : ℕ) : ℝ) ≤
      2 ^ 23 * n * logHeight n P ^ 2 := by
  intro E
  obtain ⟨hk, hrhs, hmv, hrep⟩ := newton_iteration_bits_le HP
  have hL := HP.logHeight_bounds.1
  have hprod := mul_le_mul hk hmv (Nat.cast_nonneg _) (by positivity : 0 ≤ 512 * logHeight n P)
  have hinner : (E.Brhs : ℝ) + (E.k : ℝ) * E.Bmv + E.Brep ≤
      1051648 * logHeight n P ^ 2 := by nlinarith
  push_cast
  calc 6 * (n : ℝ) * ((E.Brhs : ℝ) + (E.k : ℝ) * E.Bmv + E.Brep) ≤
      6 * n * (1051648 * logHeight n P ^ 2) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ 2 ^ 23 * n * logHeight n P ^ 2 := by
      have : 0 ≤ (n : ℝ) * logHeight n P ^ 2 := by positivity
      nlinarith

def publicSupport (n : ℕ) (P : Envelope) : SupPub :=
  batchSup (P.Mbar) (publicLogSize P) (1 / (2 * P.Mbar))
    (publicDelta n P) (publicEnvelope n P)

private theorem support_scalar_envelopes (HP : PublicHyp D P) :
    let H := height n P
    let S := publicSupport n P
    PowerEnvelope H (S.Λ ^ 2 * S.Ap / S.ρ ^ 2 / (S.σ / 54)) 597 ∧
    PowerEnvelope H (1 / (S.σ / (6 * (S.Lb + 1)))) 99 ∧
    PowerEnvelope H (S.Mbar / S.δt) 210 ∧ PowerEnvelope H S.Φ 189 := by
  intro H S
  have hH : 2 ≤ H := HP.height_inputs.1
  have hH1 : 1 ≤ H := by linarith
  obtain ⟨hL, hM, _, _, hCpub, hT, hΔ, _⟩ := base_scalar_envelopes HP
  let L := publicLogSize P
  let M := P.Mbar
  change PowerEnvelope H M 4 at hM
  let T := publicEnvelope n P
  let Δ := publicDelta n P
  let Q := 2 * M * T / Δ
  let wmin := 2 / (5 * M)
  let C := 96 * L
  let Cs := (1 - 3 * (1 / (2 * L)) / 4) * Δ
  let σ := 1 / (16000 * L)
  have hL2 : 2 ≤ L := (publicLogSize_spec P).1
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by dsimp [M]; linarith [HP.Mbar_ge_one]
  have hT0 : 0 < T := by linarith [publicEnvelope_one_le n P]
  have hD0 : 0 < Δ := (publicDelta_spec n P).1
  have hD1 : Δ ≤ 1 := (publicDelta_spec n P).2.2
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
theorem publicSupport_bits_le (HP : PublicHyp D P) :
    let S := publicSupport n P
    (S.m : ℝ) ≤ 1024 * logHeight n P ∧
    (S.N : ℝ) ≤ 256 * logHeight n P ∧
    (S.B : ℝ) ≤ 512 * logHeight n P := by
  intro S
  let H := height n P
  let L := logHeight n P
  have hH : 2 ≤ H := HP.height_inputs.1
  have hL : 1 ≤ L := HP.logHeight_bounds.1
  obtain ⟨hm, hN, hp, hΦ⟩ := support_scalar_envelopes HP
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
theorem publicSupport_budget_le (HP : PublicHyp D P) :
    let S := publicSupport n P
    (((2 * S.N + 2) * ((S.m + 3) * (6 * S.B * n)) : ℕ) : ℝ) ≤
      2 ^ 34 * n * logHeight n P ^ 3 := by
  intro S
  obtain ⟨hm, hN, hB⟩ := publicSupport_bits_le HP
  have hL := HP.logHeight_bounds.1
  have hN' : 2 * (S.N : ℝ) + 2 ≤ 514 * logHeight n P := by linarith
  have hm' : (S.m : ℝ) + 3 ≤ 1027 * logHeight n P := by linarith
  push_cast
  calc (2 * (S.N : ℝ) + 2) * (((S.m : ℝ) + 3) * (6 * (S.B : ℝ) * n)) ≤
      (514 * logHeight n P) * ((1027 * logHeight n P) * (6 * (512 * logHeight n P) * n)) := by
        gcongr
    _ ≤ 2 ^ 34 * n * logHeight n P ^ 3 := by
      have : 0 ≤ (n : ℝ) * logHeight n P ^ 3 := by positivity
      nlinarith


theorem publicLewis_count_le (HP : PublicHyp D P) :
    (batchJL (publicEnvironment n P) P.a0 (publicDelta n P) : ℝ) ≤ 256 * logHeight n P := by
  let H := height n P
  let E := publicEnvironment n P
  let L := logHeight n P
  have hH : 2 ≤ H := HP.height_inputs.1
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast HP.rank_ge
  have hL : 1 ≤ L := HP.logHeight_bounds.1
  obtain ⟨_, hM, hU, _, _, _, hΔ, _⟩ := base_scalar_envelopes HP
  obtain ⟨hs, _⟩ := newton_scalar_envelopes HP
  change PowerEnvelope H E.Mbar 4 at hM
  change PowerEnvelope H E.U 3 at hU
  change PowerEnvelope H (1 / E.sst) 39 at hs
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hM1 : 1 ≤ E.Mbar := HP.Mbar_ge_one
  have hU1 : 1 ≤ E.U := by change 1 ≤ P.U; linarith [HP.U_ge]
  have hε0 : 0 < E.ε := HP.ε_pos
  have hε1 : E.ε ≤ 1 := HP.ε_le
  have ha0 := HP.a0_pos
  have ha1 := HP.a0_le
  have hs0 : 0 < E.sst := by unfold NewtonPub.sst; positivity
  have hs1 : E.sst ≤ 1 := by
    have hden : 1 ≤ (2 : ℝ) ^ 12 * n * E.Mbar ^ 2 * E.U ^ 3 := by
      calc (1 : ℝ) ≤ 2 ^ 12 * 1 * 1 ^ 2 * 1 ^ 3 := by norm_num
        _ ≤ 2 ^ 12 * n * E.Mbar ^ 2 * E.U ^ 3 := by gcongr
    change E.ε / (2 ^ 12 * n * E.Mbar ^ 2 * E.U ^ 3) ≤ 1
    exact (div_le_one (by positivity)).mpr (hε1.trans hden)
  have hq0 : 0 < qStar P.a0 E.Mbar E.U E.sst := by unfold qStar; positivity
  have hq1 : qStar P.a0 E.Mbar E.U E.sst ≤ 1 := by
    have hden : 1 ≤ 8 * E.Mbar * E.U ^ 2 := by
      calc (1 : ℝ) ≤ 8 * 1 * 1 ^ 2 := by norm_num
        _ ≤ 8 * E.Mbar * E.U ^ 2 := by gcongr
    unfold qStar
    rw [div_le_one (by positivity)]
    exact (mul_le_one₀ (pow_le_one₀ ha0.le ha1)
      (pow_nonneg hs0.le 2) (pow_le_one₀ hs0.le hs1)).trans hden
  have ha : PowerEnvelope H (1 / P.a0) 1 :=
    ⟨by positivity, by simpa only [pow_one] using HP.height_inputs.2.2.2.2.2.1⟩
  have hi : PowerEnvelope H (1 / qStar P.a0 E.Mbar E.U E.sst) 93 := by
    have hh := (((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 8)
      (by norm_num : (8 : ℝ) ≤ 2 ^ 3)).mul hM).mul (hU.pow 2)).mul (hs.pow 2)
    convert hh.mul (ha.pow 2) using 1
    change 1 / (P.a0 ^ 2 * E.sst ^ 2 / (8 * E.Mbar * E.U ^ 2)) =
      (8 * E.Mbar * E.U ^ 2 * (1 / E.sst) ^ 2) * (1 / P.a0) ^ 2
    field_simp
  have hE0 : 0 ≤ restartLog P.a0 E.Mbar E.U E.sst :=
    Real.log_nonneg ((le_div_iff₀ hq0).mpr (by simpa using hq1))
  have hE : restartLog P.a0 E.Mbar E.U E.sst ≤ 93 * L := hi.logarithm hH (by positivity)
  have hLH : L ≤ H := HP.logHeight_bounds.2
  have hHp : PowerEnvelope H H 1 := ⟨by linarith, by simp⟩
  have hEp : PowerEnvelope H (restartLog P.a0 E.Mbar E.U E.sst + 1) 8 :=
    ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 128)
      (by norm_num : (128 : ℝ) ≤ 2 ^ 7)).mul hHp).of_le (by linarith) (by linarith)
  have hratio : PowerEnvelope H
      (1 / (publicDelta n P / (32 * (restartLog P.a0 E.Mbar E.U E.sst + 1)))) 60 := by
    have hh := ((PowerEnvelope.constant hH (by norm_num : (0 : ℝ) ≤ 32)
      (by norm_num : (32 : ℝ) ≤ 2 ^ 5)).mul hEp).mul hΔ
    convert hh using 1
    rw [one_div_div]
    ring
  have hh : (Nat.clog 2 ⌈1 / (publicDelta n P /
      (32 * (restartLog P.a0 E.Mbar E.U E.sst + 1)))⌉₊ : ℝ) ≤ 60 * L + 2 := hratio.clog hH
  change ((3 * Nat.clog 2 ⌈1 / (publicDelta n P /
    (32 * (restartLog P.a0 E.Mbar E.U E.sst + 1)))⌉₊ : ℕ) : ℝ) ≤ _
  push_cast
  linarith


#print axioms publicLewis_count_le
#print axioms newton_scalar_envelopes
#print axioms newton_iteration_bits_le
#print axioms newton_deterministic_budget_le
#print axioms publicSupport_bits_le
#print axioms publicSupport_budget_le

end
end CutQueryComplexity.ImplicitLP.GenericQuery
