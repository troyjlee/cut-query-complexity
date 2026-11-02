import CutQueryComplexity.ImplicitLP.NewtonStep
import CutQueryComplexity.ImplicitLP.SupportRound
import CutQueryComplexity.ImplicitLP.Precision
import CutQueryComplexity.ImplicitLP.LewisLev

/-! # Grid freezing of `D̂` and `q̂` (D7)

The public pair formulas are clipped to their envelopes (`D° ∈ [d₋, d₊]`, `q° ∈ [−Q, Q]`), which
leaves the values on actual hidden copies unchanged and bounds the formulas on non-edges with no
adjacency test. Then `D̂ = dyadicUp p_D D°` and `q̂ = truncDyadic p_q q°`. On actual copies
`0 ≤ D̂ − D ≤ 2^{−p_D} ≤ βd₋ ≤ βD` and `|q̂ − q| ≤ 2^{−p_q} ≤ β`; uniformly `D̂ ≥ d₋`,
`D̂ ≤ d₊ + 2^{−p_D}`, `|q̂| ≤ Q`. Explicit entries stay exact. No queries.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset

noncomputable section

variable {n : ℕ}

/-- Clip to `[lo, hi]`. -/
def clipTo (lo hi y : ℝ) : ℝ := max lo (min hi y)

theorem clipTo_of_mem {lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) : clipTo lo hi y = y := by
  simp only [clipTo, min_eq_right h2, max_eq_right h1]

theorem clipTo_le {lo hi : ℝ} (h : lo ≤ hi) (y : ℝ) : clipTo lo hi y ≤ hi :=
  max_le h (min_le_left _ _)

theorem le_clipTo (lo hi y : ℝ) : lo ≤ clipTo lo hi y := le_max_left _ _

/-- **Relative freezing** `D̂ = dyadicUp p (clip_{[lo,hi]} D)`. -/
def freezeW (p : ℕ) (lo hi : ℝ) (Dw : Sym2 (Fin n) → ℝ) : Sym2 (Fin n) → ℝ :=
  fun s => dyadicUp p (clipTo lo hi (Dw s))

/-- **Absolute freezing** `q̂_z = truncDyadic p (clip_{[−Q,Q]} q_z)`, explicit parts exact. -/
def freezeQ (p : ℕ) (Q : ℝ) (qt : DirectedMincut.LPPoint (Fin n)) :
    DirectedMincut.LPPoint (Fin n) :=
  ⟨fun u v => truncDyadic p (clipTo (-Q) Q (qt.z u v)), qt.q, qt.yp, qt.ym⟩

theorem freezeW_grid (p : ℕ) (lo hi : ℝ) (Dw : Sym2 (Fin n) → ℝ) :
    ∀ s, ∃ m : ℤ, freezeW p lo hi Dw s = m * (2 : ℝ) ^ (-(p : ℤ)) := fun s => by
  obtain ⟨m, hm⟩ := dyadicUp_int p (clipTo lo hi (Dw s))
  exact ⟨m, by rw [freezeW, hm, _root_.zpow_neg, zpow_natCast, div_eq_mul_inv]⟩

theorem freezeQ_grid (p : ℕ) (Q : ℝ) (qt : DirectedMincut.LPPoint (Fin n)) :
    ∀ u v, ∃ m : ℤ, (freezeQ p Q qt).z u v = m * (2 : ℝ) ^ (-(p : ℤ)) := fun u v => by
  obtain ⟨m, hm⟩ := (truncDyadic_props p (clipTo (-Q) Q (qt.z u v))).2.2.2
  exact ⟨m, by simp only [freezeQ]; rw [hm, _root_.zpow_neg, zpow_natCast, div_eq_mul_inv]⟩

theorem le_freezeW (p : ℕ) (lo hi : ℝ) (Dw : Sym2 (Fin n) → ℝ) (s) : lo ≤ freezeW p lo hi Dw s :=
  (le_clipTo _ _ _).trans (le_dyadicUp _ _)

theorem freezeW_le {p : ℕ} {lo hi : ℝ} (h : lo ≤ hi) (Dw : Sym2 (Fin n) → ℝ) (s) :
    freezeW p lo hi Dw s ≤ hi + (1 / 2) ^ p := by
  have h1 := abs_dyadicUp_sub_le p (clipTo lo hi (Dw s))
  have h2 := clipTo_le h (Dw s)
  have := (abs_le.mp h1).1
  unfold freezeW; linarith

theorem abs_freezeW {p : ℕ} {lo hi : ℝ} (h0 : 0 ≤ lo) (h : lo ≤ hi) (Dw : Sym2 (Fin n) → ℝ) (s) :
    |freezeW p lo hi Dw s| ≤ hi + (1 / 2) ^ p := by
  rw [abs_of_nonneg (h0.trans (le_freezeW p lo hi Dw s))]; exact freezeW_le h Dw s

theorem abs_freezeQ {p : ℕ} {Q : ℝ} (hQ : 0 ≤ Q) (qt : DirectedMincut.LPPoint (Fin n)) (u v) :
    |(freezeQ p Q qt).z u v| ≤ Q := by
  have h1 := (truncDyadic_props p (clipTo (-Q) Q (qt.z u v))).1
  have h2 : |clipTo (-Q) Q (qt.z u v)| ≤ Q :=
    abs_le.mpr ⟨le_clipTo _ _ _, clipTo_le (by linarith) _⟩
  exact h1.trans h2

variable (G : DiGraph (Fin n))

/-- Each row of `lpD` is either a hidden copy (the pair formula) or explicit (the same value
for both pair formulas). -/
theorem lpD_cases (w w' : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ) (i : Fin (lpM G)) :
    (∃ e, lpHidF G i = some e ∧ lpD G w dq dp dm i = w e ∧ lpD G w' dq dp dm i = w' e) ∨
      lpD G w dq dp dm i = lpD G w' dq dp dm i := by
  simp only [lpD, lpHidF]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j))
  · exact Or.inl ⟨_, rfl, rfl, rfl⟩
  all_goals exact Or.inr rfl

/-- Each row of `lpVec` is either a hidden copy (`z u v`) or explicit. -/
theorem lpVec_cases (pt pt' : DirectedMincut.LPPoint (Fin n)) (hq : pt.q = pt'.q)
    (hp : pt.yp = pt'.yp) (hm : pt.ym = pt'.ym) (i : Fin (lpM G)) :
    (∃ u v, lpVec G pt i = pt.z u v ∧ lpVec G pt' i = pt'.z u v) ∨
      lpVec G pt i = lpVec G pt' i := by
  simp only [lpVec]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j))
  · exact Or.inl ⟨_, _, rfl, rfl⟩
  · exact Or.inr (by simp [lpVal, hq])
  · exact Or.inr (by simp [lpVal, hp])
  · exact Or.inr (by simp [lpVal, hm])

/-- **Relative error of the frozen `D̂`.** If the target `D = lpD Dw dq dp dm` is copy-constant
(a pair formula `Dw` on hidden rows) with `lo ≤ D ≤ hi` on the rows, and `2^{−p} ≤ β·lo`, then
`D̂ = lpD (freezeW p lo hi Dw) dq dp dm` satisfies `0 ≤ D̂ − D ≤ βD` on every row. -/
theorem freezeW_rel {p : ℕ} {lo hi β : ℝ} (hβ0 : 0 ≤ β) (he : (1 / 2 : ℝ) ^ p ≤ β * lo)
    (Dw : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ)
    (hlo : ∀ i, lo ≤ lpD G Dw dq dp dm i) (hhi : ∀ i, lpD G Dw dq dp dm i ≤ hi) (i : Fin (lpM G)) :
    0 ≤ lpD G (freezeW p lo hi Dw) dq dp dm i - lpD G Dw dq dp dm i ∧
      |lpD G (freezeW p lo hi Dw) dq dp dm i - lpD G Dw dq dp dm i| ≤
        β * lpD G Dw dq dp dm i := by
  have hD0 : 0 ≤ β * lpD G Dw dq dp dm i := by
    have : 0 ≤ β * lo := ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p)).trans he
    nlinarith [hlo i]
  rcases lpD_cases G (freezeW p lo hi Dw) Dw dq dp dm i with ⟨s, -, h1, h2⟩ | h
  · rw [h1, h2]
    have hl := hlo i; have hh := hhi i
    rw [h2] at hl hh
    unfold freezeW
    rw [clipTo_of_mem hl hh]
    refine ⟨sub_nonneg.mpr (le_dyadicUp _ _), ?_⟩
    rw [abs_sub_comm]
    refine (abs_dyadicUp_sub_le p _).trans (he.trans ?_)
    exact mul_le_mul_of_nonneg_left hl hβ0
  · rw [h, sub_self, abs_zero]; exact ⟨le_rfl, hD0⟩

/-- **Absolute error of the frozen `q̂`.** If the target `q = lpVec qt` has `|q| ≤ Q` on the rows
and `2^{−p} ≤ β`, then `q̂ = lpVec (freezeQ p Q qt)` has absolute error `≤ β` on every row. -/
theorem freezeQ_abs {p : ℕ} {Q β : ℝ} (he : (1 / 2 : ℝ) ^ p ≤ β)
    (qt : DirectedMincut.LPPoint (Fin n)) (hQ : ∀ i, |lpVec G qt i| ≤ Q) (i : Fin (lpM G)) :
    |lpVec G (freezeQ p Q qt) i - lpVec G qt i| ≤ β := by
  rcases lpVec_cases G (freezeQ p Q qt) qt rfl rfl rfl i with ⟨u, v, h1, h2⟩ | h
  · rw [h1, h2]
    have hq := hQ i
    rw [h2] at hq
    simp only [freezeQ]
    rw [clipTo_of_mem (neg_le_of_abs_le hq) (le_of_abs_le hq), abs_sub_comm]
    exact (truncDyadic_props p _).2.2.1.trans he
  · rw [h, sub_self, abs_zero]; exact ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p)).trans he

end

end ImplicitLP
end CutQueryComplexity
namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Spectral

noncomputable section

/-! ## Public Newton parameters -/

/-- The public envelope of one Newton step: the vertex count `n`, the row-count bound `M̄`,
`U`, the path accuracy `ε`, the mixed-norm weight `C`, and the target Newton error `η`. -/
structure NewtonPub where
  n : ℕ
  Mbar : ℝ
  U : ℝ
  ε : ℝ
  C : ℝ
  η : ℝ

namespace NewtonPub

variable (E : NewtonPub)

/-- Repaired slack floor `s_* = ε/(2¹² n M̄² U³)`. -/
def sst : ℝ := E.ε / (2 ^ 12 * E.n * E.Mbar ^ 2 * E.U ^ 3)
/-- `d₊ = 4M̄U²`. -/
def dp : ℝ := 4 * E.Mbar * E.U ^ 2
/-- `ℓ = s_*²/16`. -/
def ell : ℝ := E.sst ^ 2 / 16
/-- `Q = 64nU/ε + 4/s_*`. -/
def Q : ℝ := 64 * E.n * E.U / E.ε + 4 / E.sst

/-- The audited draft's `P_π` with row count `Mv`. -/
def Ppi (Mv : ℝ) : ℝ := 4 * Real.sqrt (2 * Mv) * Real.sqrt Mv * E.dp * (E.Q + 1) / E.ell
/-- The audited draft's `E_π` with row count `Mv`. -/
def Epi (Mv : ℝ) : ℝ :=
  2 / E.ell * (Real.sqrt (2 * Mv) * Real.sqrt Mv * E.dp * (E.Q + 2) +
      Real.sqrt (2 * Mv) ^ 2 * E.dp * E.Ppi Mv) +
    (Real.sqrt (2 / E.ell) * (Real.sqrt (3 / 2 * E.dp) * Real.sqrt (2 * Mv)) * E.Ppi Mv +
      Real.sqrt (2 / E.ell)) + Real.sqrt E.n
/-- The audited draft's `P₁`. -/
def P1 (Mv : ℝ) : ℝ :=
  E.dp * (E.Q + Real.sqrt 2 * E.Ppi Mv) + 2 * E.dp * (1 + Real.sqrt 2 * E.Epi Mv)
/-- `lem:numeric`'s envelope `P = (2T₀/s_*)(1 + √2 M)P₁`. -/
def P (Mv : ℝ) : ℝ := 2 * (1 + 2 * E.C * (⌈Real.sqrt E.n⌉₊ : ℝ)) / E.sst * (1 + Real.sqrt 2 * Mv) * E.P1 Mv

/-- The public envelope at `M̄`. -/
def Ppub : ℝ := E.P E.Mbar

/-- **Accuracy** `β = min(1/4, η / max(P, 1))`, so `Pβ ≤ η`. -/
def β : ℝ := min (1 / 4) (E.η / max E.Ppub 1)
/-- `Λ = (3/2)d₊ · 2M̄`. -/
def Λ : ℝ := 3 / 2 * E.dp * (2 * E.Mbar)
/-- `X = P_π(M̄)`, the solution bound. -/
def X : ℝ := E.Ppi E.Mbar
/-- Refinement steps `k = iters β`, so `2^{−k} ≤ β`. -/
def k : ℕ := iters E.β
/-- Fractional bits `p = bits(2√Λ√n, β)`, so `2τ ≤ β`. -/
def p : ℕ := bits (2 * Real.sqrt E.Λ * Real.sqrt E.n) E.β
/-- The public bound on the frozen-solve output. -/
def Xk : ℝ := E.X + Real.sqrt (1 / (E.sst ^ 2 / 16 / 2)) *
  (Real.sqrt E.Λ * E.X + 2 * (Real.sqrt E.Λ * (Real.sqrt E.n * (1 / 2 ^ E.p))))
/-- `W = (1 + β)d₊` bounds the frozen hidden weights. -/
def W : ℝ := (1 + E.β) * E.dp
/-- `Q_z = Q` bounds the frozen hidden `q̂`. -/
def Qz : ℝ := E.Q
/-- Weight precision `p_D = bits(1, βd₋)`, so `2^{−p_D} ≤ βd₋`. -/
def pD : ℕ := bits 1 (E.β * E.ell)
/-- `q̂` precision `p_q = max(p, bits(1, β))`. -/
def pq : ℕ := max E.p (bits 1 E.β)
/-- Weight grid `e_w = −p_D`. -/
def ew : ℤ := -(E.pD : ℤ)
/-- `q̂` grid `e_q = −p_q ≤ −p`. -/
def eq : ℤ := -(E.pq : ℤ)
/-- Magnitude bits of the right-hand side aggregate. -/
def Brhs : ℕ := magBits (E.W * E.Qz / (2 : ℝ) ^ (E.ew + E.eq))
/-- Magnitude bits of each refinement mat-vec. -/
def Bmv : ℕ := magBits (E.W * (2 * E.Xk) / (2 : ℝ) ^ (E.ew - E.p))
/-- Magnitude bits of the repair residual aggregate. -/
def Brep : ℕ := magBits (E.W * (E.Qz + 2 * E.Xk) / (2 : ℝ) ^ (E.ew + E.eq))

/-! ### Elementary facts -/

variable {E}

theorem β_pos (hη : 0 < E.η) : 0 < E.β :=
  lt_min (by norm_num) (div_pos hη (lt_of_lt_of_le one_pos (le_max_right _ _)))

theorem β_le : E.β ≤ 1 / 4 := min_le_left _ _

theorem Ppub_mul_β_le (hη : 0 < E.η) (hP : 0 ≤ E.Ppub) : E.Ppub * E.β ≤ E.η := by
  have hm : 0 < max E.Ppub 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc E.Ppub * E.β ≤ E.Ppub * (E.η / max E.Ppub 1) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hP
    _ = E.Ppub / max E.Ppub 1 * E.η := by ring
    _ ≤ 1 * E.η := by
        gcongr
        exact (div_le_one hm).mpr (le_max_left _ _)
    _ = E.η := one_mul _

theorem half_pow_pD_le (hη : 0 < E.η) (hℓ : 0 < E.ell) : (1 / 2 : ℝ) ^ E.pD ≤ E.β * E.ell := by
  have h := div_two_pow_bits_le (c := 1) (mul_pos (β_pos hη) hℓ)
  rw [_root_.one_div_pow]; exact h

theorem ew_grid (Dw : Sym2 (Fin E.n) → ℝ) :
    ∀ e, ∃ z : ℤ, freezeW E.pD E.ell E.dp Dw e = z * (2 : ℝ) ^ E.ew := freezeW_grid _ _ _ _

theorem eq_le : E.eq ≤ -(E.p : ℤ) := by
  simp only [eq, pq]; push_cast; omega

theorem half_pow_pq_le (hη : 0 < E.η) : (1 / 2 : ℝ) ^ E.pq ≤ E.β := by
  have h := div_two_pow_bits_le (c := 1) (β_pos hη)
  rw [_root_.one_div_pow]
  exact (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))).trans h

theorem hk (hη : 0 < E.η) : (1 / 2 : ℝ) ^ E.k ≤ E.β := half_pow_iters_le (β_pos hη)

theorem hτβ (hη : 0 < E.η) :
    2 * (Real.sqrt E.Λ * (Real.sqrt E.n * (1 / 2 ^ E.p))) ≤ E.β := by
  have h := div_two_pow_bits_le (c := 2 * Real.sqrt E.Λ * Real.sqrt E.n) (β_pos hη)
  calc _ = 2 * Real.sqrt E.Λ * Real.sqrt E.n / 2 ^ E.p := by ring
    _ ≤ E.β := h

theorem lt_magBits_mul (X : ℝ) (e : ℤ) : X < (2 : ℝ) ^ magBits (X / (2 : ℝ) ^ e) * (2 : ℝ) ^ e := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have := lt_two_pow_magBits (X / (2 : ℝ) ^ e)
  rwa [div_lt_iff₀ h2] at this

theorem hBrhs : E.W * E.Qz < (2 : ℝ) ^ E.Brhs * (2 : ℝ) ^ (E.ew + E.eq) := lt_magBits_mul _ _

theorem hBmv : E.W * (2 * E.Xk) < (2 : ℝ) ^ E.Bmv * (2 : ℝ) ^ (E.ew - E.p) := lt_magBits_mul _ _

theorem hBrep : E.W * (E.Qz + 2 * E.Xk) < (2 : ℝ) ^ E.Brep * (2 : ℝ) ^ (E.ew + E.eq) :=
  lt_magBits_mul _ _

/-- The envelope `P` is monotone in the row count. -/
theorem P_mono (hC : 0 ≤ E.C) (hsst : 0 < E.sst) (hdp : 0 ≤ E.dp) (hQ : 0 ≤ E.Q)
    (hℓ : 0 < E.ell) {M₁ M₂ : ℝ} (h0 : 0 ≤ M₁) (h : M₁ ≤ M₂) : E.P M₁ ≤ E.P M₂ := by
  have hPpi : E.Ppi M₁ ≤ E.Ppi M₂ := by
    unfold Ppi; gcongr
  have hPpi0 : 0 ≤ E.Ppi M₁ := by unfold Ppi; positivity
  have hEpi : E.Epi M₁ ≤ E.Epi M₂ := by
    unfold Epi; gcongr
  have hEpi0 : 0 ≤ E.Epi M₁ := by unfold Epi; positivity
  have hP1 : E.P1 M₁ ≤ E.P1 M₂ := by unfold P1; gcongr
  have hP10 : 0 ≤ E.P1 M₁ := by unfold P1; positivity
  have hM2 : 0 ≤ M₂ := h0.trans h
  have hT : 0 ≤ 2 * (1 + 2 * E.C * (⌈Real.sqrt E.n⌉₊ : ℝ)) / E.sst * (1 + Real.sqrt 2 * M₂) :=
    mul_nonneg (div_nonneg (by positivity) hsst.le)
      (by have := Real.sqrt_nonneg 2; positivity)
  unfold P; gcongr

theorem P_nonneg (hC : 0 ≤ E.C) (hsst : 0 < E.sst) (hdp : 0 ≤ E.dp) (hQ : 0 ≤ E.Q)
    (hℓ : 0 < E.ell) {Mv : ℝ} (h0 : 0 ≤ Mv) : 0 ≤ E.P Mv := by
  have hPpi0 : 0 ≤ E.Ppi Mv := by unfold Ppi; positivity
  have hEpi0 : 0 ≤ E.Epi Mv := by unfold Epi; positivity
  have hP10 : 0 ≤ E.P1 Mv := by unfold P1; positivity
  unfold P
  exact mul_nonneg (mul_nonneg (div_nonneg (by positivity) hsst.le)
    (by have := Real.sqrt_nonneg 2; positivity)) hP10

end NewtonPub

/-- **The public D4 accuracy for solves.** `δ = 1/(16(R+1))` gives `2Rδ ≤ ε_solve = 1/8`, hence
the energy factors of `sparsify_factor_bounds`. -/
def solveDelta (R : ℕ) : ℝ := 1 / (16 * (R + 1))

theorem solveDelta_spec (R : ℕ) :
    0 < solveDelta R ∧ solveDelta R ≤ 1 ∧ 1 - 1 / 8 ≤ (1 - solveDelta R) ^ R ∧
      (1 + solveDelta R) ^ R ≤ 1 + 1 / 8 := by
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have h0 : 0 < solveDelta R := by unfold solveDelta; positivity
  have h1 : solveDelta R ≤ 1 := by
    unfold solveDelta; rw [div_le_one (by positivity)]; linarith
  have h2 : 2 * R * solveDelta R ≤ 1 / 8 := by
    unfold solveDelta
    rw [show 2 * (R : ℝ) * (1 / (16 * (R + 1))) = R / (8 * (R + 1)) by field_simp; ring,
      div_le_iff₀ (by positivity)]
    linarith
  exact ⟨h0, h1, sparsify_factor_bounds h0.le (by norm_num) h2⟩

end

end ImplicitLP
end CutQueryComplexity
namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Spectral

noncomputable section

open DirectedMincut (LPPoint)

/-- The frozen hidden weights `ŵ` of the public parameter set. -/
def NewtonPub.wf (E : NewtonPub) (Dw : Sym2 (Fin E.n) → ℝ) : Sym2 (Fin E.n) → ℝ :=
  freezeW E.pD E.ell E.dp Dw

/-- The frozen `q̂` of the public parameter set. -/
def NewtonPub.qp (E : NewtonPub) (qt : LPPoint (Fin E.n)) : LPPoint (Fin E.n) :=
  freezeQ E.pq E.Q qt

/-- **The Newton step with the public parameters.** -/
def newtonStepPub (E : NewtonPub) (s t : Fin E.n) (Dw : Sym2 (Fin E.n) → ℝ) (dq : ℝ)
    (dp dm : Fin E.n → ℝ) (qt : LPPoint (Fin E.n)) (out : Sym2 (Fin E.n) → ℝ) :=
  newtonStepProg s t (E.wf Dw) dq dp dm (E.qp qt) out E.ew E.eq E.p E.Brhs E.Bmv E.Brep E.k

/-- **Deterministic budget** `6n(B_rhs + k·B_mv + B_rep)` with the public parameters, on every
execution and for every oracle. -/
theorem newtonStepPub_cost (E : NewtonPub) (G : DiGraph (Fin E.n)) (s t : Fin E.n)
    (Dw : Sym2 (Fin E.n) → ℝ) (dq : ℝ) (dp dm : Fin E.n → ℝ) (qt : LPPoint (Fin E.n))
    (out : Sym2 (Fin E.n) → ℝ) :
    (newtonStepPub E s t Dw dq dp dm qt out).cost G.out ≤
      6 * E.n * (E.Brhs + E.k * E.Bmv + E.Brep) :=
  newtonStepProg_cost G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

variable {E : NewtonPub} (G : DiGraph (Fin E.n))

open Spectral in
set_option maxHeartbeats 6400000 in
/-- **`lem:numeric` with every numerical premise discharged.** Under the path-following
invariants, with the frozen targets copy-constant (`D = lpD Dw dq d₊ d₋`, `q = lpVec qt`: D8's
state invariant) and one successful D4 call at the public accuracy `δ = 1/(16(R+1))`
(`ε_solve = 1/8`), the public-parameter Newton step outputs `d` with `Aᵀd = 0` exactly and
mixed error `≤ η`. All of `β, k, p, e_w, e_q, B_rhs, B_mv, B_rep` are the public choices of
`NewtonPub`; the grid, refinement, rounding and bit premises are proved here. -/
theorem newtonStep_public (s t₀ : Fin E.n) (hst : s ≠ t₀) {bc : Fin E.n → ℝ}
    {κ m w c : Fin (lpM G) → ℝ} {t : ℝ}
    {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * lpM G) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀lo : 1 / (2 * E.Mbar) ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * lpM G)) (hU1 : 1 ≤ E.U) (hU : ∀ i, Real.pi / κ i ≤ E.U)
    {x x₀ : Fin (lpM G) → ℝ}
    (hx : x ∈ Feasible (lpA G s t₀) bc κ m) (hx₀ : x₀ ∈ Feasible (lpA G s t₀) bc κ m)
    (hMbar : (lpM G : ℝ) ≤ E.Mbar) (hr : (1 : ℝ) ≤ E.n) (hε : 0 < E.ε) (hε1 : E.ε ≤ 1)
    (hw : ∀ i, 0 < w i) (ht : |t| ≤ 16 * E.n / E.ε) (hc : ‖c‖ ≤ 4 * E.U)
    (hwin : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (lpA G s t₀) x i)| ≤ 1 / 20)
    (hδc : cent (48 * (2 * L₀)) (lpA G s t₀) (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs0 : ∀ i, 1 / E.U ≤ slk κ m x₀ i) (hC : 0 ≤ E.C) (hη : 0 < E.η)
    -- copy-constant targets (D8's state invariant)
    {Dw : Sym2 (Fin E.n) → ℝ} {dq : ℝ} {dpv dmv : Fin E.n → ℝ}
    (hDcopy : normD w (barS κ m x) = lpD G Dw dq dpv dmv)
    {qt : LPPoint (Fin E.n)} (hqcopy : normQ t c w (barDphi κ m x) = lpVec G qt)
    -- the exact Newton solution
    {p0 : Fin E.n → ℝ}
    (hp : gram (lpA G s t₀) (normD w (barS κ m x)) *ᵥ p0 =
      (lpA G s t₀)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    -- one successful spectral call
    {K t' R : ℕ} {out : Sym2 (Fin E.n) → ℝ}
    (hgood : Sparsify.Good G (E.wf Dw) K t' (solveDelta R) R out) :
    let A := lpA G s t₀
    let h : Fin (lpM G) → ℝ := fun i =>
      -normD w (barS κ m x) i * (normQ t c w (barDphi κ m x) i - (A *ᵥ p0) i)
    let d := (newtonStepPub E s t₀ Dw dq dpv dmv qt out).eval G.out
    Aᵀ *ᵥ lpVec G d = 0 ∧ mixed E.C w (fun i => barS κ m x i * (lpVec G d - h) i) ≤ E.η := by
  intro A h d
  -- invariants → weight and slack windows
  have hA := det_ne_zero_of_idRows (lpA_idRows G s t₀)
  have hrowne := lpA_row_ne_zero G hst
  have hwin5 : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (lpA G s t₀) x i)| ≤ 1 / 5 :=
    fun i => (hwin i).trans (by norm_num)
  obtain ⟨hwlo, hwhi, hwsum⟩ := weight_invariants hA hrowne hL hc₀lo hcM hMbar hr hw hwin5
  have hM1 : (1 : ℝ) ≤ lpM G := by
    have hr0 : 0 < E.n := by exact_mod_cast (show (0 : ℝ) < E.n by linarith)
    exact_mod_cast Fin.pos (lpIota G ⟨0, hr0⟩)
  have hr0 : 0 < E.n := by exact_mod_cast (show (0 : ℝ) < E.n by linarith)
  have hMb : 0 < E.Mbar := by linarith
  have hc₀ : 0 ≤ c₀ := (by positivity : (0 : ℝ) ≤ 1 / (2 * E.Mbar)).trans hc₀lo
  have hs : ∀ i, E.sst ≤ slk κ m x i := fun i =>
    slack_floor_note hA hrowne hL hLM hκ hc₀ hcM hU1 hU hx hx₀ hMbar hr hε hε1 hwlo hwsum ht
      hc hwin hδc hs0 i
  have hU0 : 0 < E.U := by linarith
  have hsst0 : 0 < E.sst := by unfold NewtonPub.sst; positivity
  have hℓ : 0 < E.ell := by unfold NewtonPub.ell; positivity
  have hdp0 : 0 < E.dp := by unfold NewtonPub.dp; positivity
  have hQ0 : 0 ≤ E.Q := by unfold NewtonPub.Q; positivity
  -- envelope bounds on the rows
  have hwpos : ∀ i, 0 < w i := hw
  have hS := fun i => barrier_env hκ hx.2 hU1 hU i
  have hDlo : ∀ i, E.ell ≤ normD w (barS κ m x) i := fun i => by
    have := normD_ge hwpos hwhi (barS_pos hκ hx.2) (fun i => (hS i).2.1) hsst0 hs i
    unfold NewtonPub.ell; convert this using 2; norm_num
  have hDhi : ∀ i, normD w (barS κ m x) i ≤ E.dp := fun i => by
    have := normD_le (by positivity : (0 : ℝ) < 1 / (4 * E.Mbar)) hwlo hU0 (fun i => (hS i).1) i
    unfold NewtonPub.dp; convert this using 1; field_simp
  have hqb : ∀ i, |normQ t c w (barDphi κ m x) i| ≤ E.Q := fun i => by
    have h1 := normQ_le (t := t) (c := c) hwpos hwhi (fun i => (hS i).2.2) hsst0 hs i
    have h2 : |t| * ‖c‖ ≤ 16 * E.n / E.ε * (4 * E.U) :=
      mul_le_mul ht hc (norm_nonneg _) (by positivity)
    unfold NewtonPub.Q
    calc _ ≤ _ := h1
      _ ≤ 16 * E.n / E.ε * (4 * E.U) + 4 / E.sst := by linarith
      _ = _ := by ring
  have hβ0 : 0 < E.β := NewtonPub.β_pos hη
  have hβ4 := NewtonPub.β_le (E := E)
  have hew := NewtonPub.half_pow_pD_le hη hℓ
  have hℓdp : E.ell ≤ E.dp := (hDlo (lpIota G ⟨0, hr0⟩)).trans (hDhi _)
  -- grid freezing
  have hDlo' : ∀ i, E.ell ≤ lpD G Dw dq dpv dmv i := fun i => hDcopy ▸ hDlo i
  have hDhi' : ∀ i, lpD G Dw dq dpv dmv i ≤ E.dp := fun i => hDcopy ▸ hDhi i
  have hDh : ∀ i, |lpD G (E.wf Dw) dq dpv dmv i - normD w (barS κ m x) i| ≤
      E.β * normD w (barS κ m x) i := fun i => by
    rw [hDcopy]; exact (freezeW_rel G hβ0.le hew Dw dq dpv dmv hDlo' hDhi' i).2
  have hqh : ∀ i, |lpVec G (E.qp qt) i - normQ t c w (barDphi κ m x) i| ≤ E.β := fun i => by
    rw [hqcopy]
    exact freezeQ_abs G (NewtonPub.half_pow_pq_le hη) qt (fun i => hqcopy ▸ hqb i) i
  have hdpv : ∀ j, E.ell ≤ dpv j := fun j => by
    have := hDlo' (lpIota G j); simpa [lpD, lpIota, lpWeight] using this
  have hwf0 : ∀ e, 0 ≤ E.wf Dw e := fun e => hℓ.le.trans (le_freezeW _ _ _ Dw e)
  have hW : ∀ e, |E.wf Dw e| ≤ E.W := fun e => by
    refine (abs_freezeW hℓ.le hℓdp Dw e).trans ?_
    unfold NewtonPub.W
    nlinarith [hew, hℓdp]
  have hQz : ∀ u v, |(E.qp qt).z u v| ≤ E.Qz := fun u v => abs_freezeQ hQ0 qt u v
  -- envelope at the public row bound
  have hX : 4 * Real.sqrt (2 * lpM G) * Real.sqrt (lpM G) * E.dp *
      (64 * E.n * E.U / E.ε + 4 / E.sst + 1) / (E.sst ^ 2 / 16) ≤ E.X := by
    show _ ≤ 4 * Real.sqrt (2 * E.Mbar) * Real.sqrt E.Mbar * E.dp * (E.Q + 1) / E.ell
    unfold NewtonPub.Q NewtonPub.ell
    gcongr
  have hΛ : 3 / 2 * E.dp * (2 * lpM G) ≤ E.Λ := by unfold NewtonPub.Λ; gcongr
  obtain ⟨hδ0, -, hδlo, hδhi⟩ := solveDelta_spec R
  obtain ⟨-, -, H3, H4⟩ := newtonStep_numeric_lp_inv G s t₀ hst hL hLM hκ hc₀lo hcM hU1 hU hx
    hx₀ hMbar hr hε hε1 hw ht hc hwin hδc hs0 (sst := E.sst) (dp := E.dp) rfl rfl hC hDh hqh
    hβ0.le (by linarith) hp hℓ hdpv hwf0 hgood (by norm_num) le_rfl hδlo hδhi hX hΛ hW hQz
    (NewtonPub.ew_grid (E := E) Dw) (freezeQ_grid _ _ _) E.p E.Brhs E.Bmv E.Brep
    NewtonPub.eq_le NewtonPub.hBmv NewtonPub.hBrhs NewtonPub.hBrep (NewtonPub.hτβ hη) E.k
    (NewtonPub.hk hη)
  refine ⟨H3, H4.trans ?_⟩
  have hmono := NewtonPub.P_mono hC hsst0 hdp0.le hQ0 hℓ (by linarith) hMbar
  have hpub := NewtonPub.P_nonneg hC hsst0 hdp0.le hQ0 hℓ (hMb.le)
  calc E.P (lpM G) * E.β ≤ E.Ppub * E.β := mul_le_mul_of_nonneg_right hmono hβ0.le
    _ ≤ E.η := NewtonPub.Ppub_mul_β_le hη hpub

end

end ImplicitLP
end CutQueryComplexity
namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Spectral

noncomputable section

open DirectedMincut (LPPoint)

/-! ## Logarithmic size of the public parameters -/

theorem clog_ceil_mono {x y : ℝ} (h : x ≤ y) : Nat.clog 2 ⌈x⌉₊ ≤ Nat.clog 2 ⌈y⌉₊ :=
  Nat.clog_mono_right _ (Nat.ceil_mono h)

/-- `magBits X ≤ log₂ max(X, 1) + 3`. -/
theorem magBits_le_log (X : ℝ) : (magBits X : ℝ) ≤ Real.logb 2 (max X 1) + 3 := by
  have h1 := clog_le_log_add_one (le_max_right X 1)
  have h2 : (Nat.clog 2 ⌈X⌉₊ : ℝ) ≤ Nat.clog 2 ⌈max X 1⌉₊ := by
    exact_mod_cast clog_ceil_mono (le_max_left X 1)
  simp only [magBits]; push_cast; linarith

/-- `iters β ≤ log₂(1/β) + 2` for `0 < β ≤ 1`. -/
theorem iters_le_log {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 1) :
    (iters β : ℝ) ≤ Real.logb 2 (1 / β) + 2 :=
  clog_le_log_add_one (by rw [le_div_iff₀ h0]; linarith)

/-- `bits c β ≤ log₂(c/β) + 2` for `0 < β ≤ c`. -/
theorem bits_le_log {c β : ℝ} (h0 : 0 < β) (h1 : β ≤ c) :
    (bits c β : ℝ) ≤ Real.logb 2 (c / β) + 2 :=
  clog_le_log_add_one (by rw [le_div_iff₀ h0]; linarith)

/-- Scaling a magnitude by `2^k` adds `k` bits: `magBits (X·2^k) ≤ magBits X + k`. -/
theorem magBits_mul_pow (X : ℝ) (k : ℕ) : magBits (X * 2 ^ k) ≤ magBits X + k := by
  have h1 : ⌈X * 2 ^ k⌉₊ ≤ ⌈X⌉₊ * 2 ^ k := by
    apply Nat.ceil_le.mpr
    push_cast
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil X) (by positivity)
  have h2 : ⌈X⌉₊ * 2 ^ k ≤ 2 ^ (Nat.clog 2 ⌈X⌉₊ + k) := by
    rw [pow_add]; exact Nat.mul_le_mul_right _ (Nat.le_pow_clog one_lt_two _)
  have h3 : Nat.clog 2 ⌈X * 2 ^ k⌉₊ ≤ Nat.clog 2 ⌈X⌉₊ + k :=
    Nat.clog_le_of_le_pow (h1.trans h2)
  simp only [magBits]; omega

theorem div_zpow_neg_add (X : ℝ) (a b : ℕ) :
    X / (2 : ℝ) ^ (-(a : ℤ) + -(b : ℤ)) = X * 2 ^ (a + b) := by
  rw [← neg_add, _root_.zpow_neg, div_inv_eq_mul, ← Nat.cast_add, zpow_natCast]

namespace NewtonPub

variable (E : NewtonPub)

/-- `B_rhs ≤ magBits(WQ_z) + p_D + p_q`. -/
theorem Brhs_le : E.Brhs ≤ magBits (E.W * E.Qz) + (E.pD + E.pq) := by
  unfold Brhs; rw [ew, eq, div_zpow_neg_add]; exact magBits_mul_pow _ _

/-- `B_rep ≤ magBits(W(Q_z + 2X_k)) + p_D + p_q`. -/
theorem Brep_le : E.Brep ≤ magBits (E.W * (E.Qz + 2 * E.Xk)) + (E.pD + E.pq) := by
  unfold Brep; rw [ew, eq, div_zpow_neg_add]; exact magBits_mul_pow _ _

/-- `B_mv ≤ magBits(2WX_k) + p_D + p`. -/
theorem Bmv_le : E.Bmv ≤ magBits (E.W * (2 * E.Xk)) + (E.pD + E.p) := by
  unfold Bmv
  rw [ew, sub_eq_add_neg, div_zpow_neg_add]; exact magBits_mul_pow _ _

end NewtonPub

/-! ## D4 + the public Newton step -/

open scoped ENNReal

/-- **D4 then the public Newton step**, at the D4 accuracy `solveDelta R` (only the analysis
uses `δ`; the program is `newtonProg` with the public parameters). -/
def newtonProgPub (E : NewtonPub) (s t : Fin E.n) (Dw : Sym2 (Fin E.n) → ℝ) (dq : ℝ)
    (dp dm : Fin E.n → ℝ) (qt : LPPoint (Fin E.n)) (K J t' R : ℕ) :=
  newtonProg s t (E.wf Dw) dq dp dm (E.qp qt) K J t' R E.ew E.eq E.p E.Brhs E.Bmv E.Brep E.k

/-- **Budget on every execution:** `q_D4 + 6n(B_rhs + k·B_mv + B_rep)`. -/
theorem newtonProgPub_cost (E : NewtonPub) (G : DiGraph (Fin E.n)) (s t : Fin E.n)
    (Dw : Sym2 (Fin E.n) → ℝ) (dq : ℝ) (dp dm : Fin E.n → ℝ) (qt : LPPoint (Fin E.n))
    (K J t' R : ℕ) {o : LPPoint (Fin E.n) × ℕ}
    (ho : o ∈ (RTree.run G.out (newtonProgPub E s t Dw dq dp dm qt K J t' R)).support) :
    o.2 ≤ (R * Sparsify.levelBudget (n := E.n) K J t' + 3 * E.n) +
      6 * E.n * (E.Brhs + E.k * E.Bmv + E.Brep) :=
  newtonProg_cost G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho

/-- **The budget is logarithmic in the public envelope:** with `L(X) = log₂ max(X,1)`, it is at
most `q_D4 + 6n(B₁ + k·B₂ + B₃)` with `B₁ ≤ L(WQ_z) + 3 + p_D + p_q`,
`B₂ ≤ L(2WX_k) + 3 + p_D + p`, `B₃ ≤ L(W(Q_z + 2X_k)) + 3 + p_D + p_q`,
`k ≤ log₂(1/β) + 2`. -/
theorem newtonPub_bits_log (E : NewtonPub) (hη : 0 < E.η) :
    (E.Brhs : ℝ) ≤ Real.logb 2 (max (E.W * E.Qz) 1) + 3 + (E.pD + E.pq) ∧
    (E.Bmv : ℝ) ≤ Real.logb 2 (max (E.W * (2 * E.Xk)) 1) + 3 + (E.pD + E.p) ∧
    (E.Brep : ℝ) ≤ Real.logb 2 (max (E.W * (E.Qz + 2 * E.Xk)) 1) + 3 + (E.pD + E.pq) ∧
    (E.k : ℝ) ≤ Real.logb 2 (1 / E.β) + 2 := by
  have h1 : (E.Brhs : ℝ) ≤ (magBits (E.W * E.Qz) : ℝ) + (E.pD + E.pq) := by
    exact_mod_cast E.Brhs_le
  have h2 : (E.Bmv : ℝ) ≤ (magBits (E.W * (2 * E.Xk)) : ℝ) + (E.pD + E.p) := by
    exact_mod_cast E.Bmv_le
  have h3 : (E.Brep : ℝ) ≤ (magBits (E.W * (E.Qz + 2 * E.Xk)) : ℝ) + (E.pD + E.pq) := by
    exact_mod_cast E.Brep_le
  refine ⟨?_, ?_, ?_, iters_le_log (NewtonPub.β_pos hη) (NewtonPub.β_le.trans (by norm_num))⟩
  · linarith [magBits_le_log (E.W * E.Qz)]
  · linarith [magBits_le_log (E.W * (2 * E.Xk))]
  · linarith [magBits_le_log (E.W * (E.Qz + 2 * E.Xk))]

variable {E : NewtonPub} (G : DiGraph (Fin E.n))

open Probability Spectral in
set_option maxHeartbeats 6400000 in
/-- **`lem:numeric` for D4 + the public Newton step, with probability.** Under the invariants
and the copy-constant frozen targets, outside the failure mass of one D4 call at
`δ = solveDelta R` (`ε_solve = 1/8`), the output `d` has `Aᵀd = 0` and mixed error `≤ η`. -/
theorem newtonProgPub_numeric (s t₀ : Fin E.n) (hst : s ≠ t₀) {bc : Fin E.n → ℝ}
    {κ m w c : Fin (lpM G) → ℝ} {t : ℝ}
    {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * lpM G) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀lo : 1 / (2 * E.Mbar) ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * lpM G)) (hU1 : 1 ≤ E.U) (hU : ∀ i, Real.pi / κ i ≤ E.U)
    {x x₀ : Fin (lpM G) → ℝ}
    (hx : x ∈ Feasible (lpA G s t₀) bc κ m) (hx₀ : x₀ ∈ Feasible (lpA G s t₀) bc κ m)
    (hMbar : (lpM G : ℝ) ≤ E.Mbar) (hr : (1 : ℝ) ≤ E.n) (hε : 0 < E.ε) (hε1 : E.ε ≤ 1)
    (hw : ∀ i, 0 < w i) (ht : |t| ≤ 16 * E.n / E.ε) (hc : ‖c‖ ≤ 4 * E.U)
    (hwin : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (lpA G s t₀) x i)| ≤ 1 / 20)
    (hδc : cent (48 * (2 * L₀)) (lpA G s t₀) (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs0 : ∀ i, 1 / E.U ≤ slk κ m x₀ i) (hC : 0 ≤ E.C) (hη : 0 < E.η)
    {Dw : Sym2 (Fin E.n) → ℝ} {dq : ℝ} {dpv dmv : Fin E.n → ℝ}
    (hDcopy : normD w (barS κ m x) = lpD G Dw dq dpv dmv)
    {qt : LPPoint (Fin E.n)} (hqcopy : normQ t c w (barDphi κ m x) = lpVec G qt)
    {p0 : Fin E.n → ℝ}
    (hp : gram (lpA G s t₀) (normD w (barS κ m x)) *ᵥ p0 =
      (lpA G s t₀)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {K J t' : ℕ} (R : ℕ) {Cs : ℝ} (hCs0 : 0 ≤ Cs) (hCs : ∀ e, (Spanner.symS G e : ℝ) ≤ Cs)
    (hK : E.n ≤ 2 ^ K) (ht' : 0 < t') :
    let A := lpA G s t₀
    let h : Fin (lpM G) → ℝ := fun i =>
      -normD w (barS κ m x) i * (normQ t c w (barDphi κ m x) i - (A *ᵥ p0) i)
    mass ((newtonProgPub E s t₀ Dw dq dpv dmv qt K J t' R).eval G.out)
        (fun d => ¬ (Aᵀ *ᵥ lpVec G d = 0 ∧
          mixed E.C w (fun i => barS κ m x i * (lpVec G d - h) i) ≤ E.η)) ≤
      R * (t' * (2⁻¹ : ℝ≥0∞) ^ J + ENNReal.ofReal (2 * E.n *
          Real.exp (-(solveDelta R ^ 2) / (8 * (Cs * (2 * K + 1 : ℕ) / t'))))) +
        (Sparsify.resid G (Sparsify.P0 (E.wf Dw))).card * (4⁻¹ : ℝ≥0∞) ^ R := by
  intro A h
  obtain ⟨hδ0, hδ1, -, -⟩ := solveDelta_spec R
  have hwf0 : ∀ e, 0 ≤ E.wf Dw e := fun e => by
    have hU0 : 0 < E.U := by linarith
    have hr0 : 0 < E.n := by exact_mod_cast (show (0 : ℝ) < E.n by linarith)
    have hM1 : (1 : ℝ) ≤ lpM G := by exact_mod_cast Fin.pos (lpIota G ⟨0, hr0⟩)
    have hMb : 0 < E.Mbar := by linarith
    have : 0 < E.ell := by
      unfold NewtonPub.ell NewtonPub.sst; positivity
    exact this.le.trans (le_freezeW _ _ _ Dw e)
  exact newtonProg_fail_le G s t₀ dq dpv dmv (E.qp qt) J E.ew E.eq E.p E.Brhs E.Bmv E.Brep E.k
    hCs0 hCs hwf0 hK ht' hδ0 hδ1 R _ fun out hgood =>
      newtonStep_public G s t₀ hst hL hLM hκ hc₀lo hcM hU1 hU hx hx₀ hMbar hr hε hε1 hw ht hc
        hwin hδc hs0 hC hη hDcopy hqcopy hp hgood

end

end ImplicitLP
end CutQueryComplexity
/-! # The support oracle with a public certified error allowance (D7)

`support_hidden`, `supportProg_hidden` and `supportRoundProg_hidden` with the evaluator's error
allowance `δ` any public number `≥ M·2^{−p}` (e.g. `δ = M̄·2^{−p}`), in place of the hidden
`M·2^{−p}`. -/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

section HiddenGen

variable {M n : ℕ}

/-- `support_hidden` with any certified allowance `δ ≥ M·2^{−p}`. -/
theorem support_hidden_gen (G : DiGraph (Fin n)) (hid : Fin M → Option (Sym2 (Fin n)))
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {C Cs : ℝ} {w q : Fin M → ℝ} {wb qb : Sym2 (Fin n) → ℝ}
    (hwb : ∀ i e, hid i = some e → w i = wb e) (hqb : ∀ i e, hid i = some e → q i = qb e)
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < w i) {ρ h Ap Abar Φ : ℝ} (hρ : 0 < ρ)
    (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * q i / (C * Real.sqrt (w i))) ≤ Ap)
    (hAbar : ∀ e, |Cs * qb e / (C * Real.sqrt (wb e))| ≤ Abar)
    (hΦ1 : Abar ^ 2 / (4 * ρ ^ 2) ≤ Φ) (hΦ2 : Abar ^ 2 / (2 * ρ) ≤ Φ)
    {p B : ℕ} (hB : Φ * 2 ^ p + 1 ≤ 2 ^ B) {δ : ℝ} (hδM : (M : ℝ) / 2 ^ p ≤ δ)
    (hp : δ ≤ 3 * h ^ 2 / 4) (N m : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let ab : Sym2 (Fin n) → ℝ := fun e => Cs * qb e / (C * Real.sqrt (wb e))
    let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (wb e)
    let Nt : ℝ → ℝ → ℝ := fun τ lm =>
      (hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), zlam a κ ρ τ lm i ^ 2)
        (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B).eval G.out
    let Pt : ℝ → ℝ → ℝ := fun τ lm =>
      (hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), a i * zlam a κ ρ τ lm i)
        (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B).eval G.out
    let Λ := Ap / h
    let ε := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ m) + (3 * Λ + 4 * ρ + euc a / (2 * h)) * δ + 4 * δ
    let ev : ℝ → ℝ × ℝ × ℝ × ℝ := fun τ => ieval (Nt τ) (Pt τ) δ δ ρ (1 - τ) Λ m
    let zf : ℝ → Fin M → ℝ := fun τ => (ev τ).2.1 • zlam a κ ρ τ (ev τ).1
    let best := (trisect (fun τ => (ev τ).2.2.1) (fun τ => (ev τ).2.2.2) h (1 - h) N).best
    (∃ t₀ ∈ Icc h (1 - h), best = (ev t₀).2.2.1) ∧
    ∀ t₀ ∈ Icc h (1 - h), best ≤ (ev t₀).2.2.1 →
      let vh : Fin M → ℝ := fun i => Cs * zf t₀ i / (C * Real.sqrt (w i))
      mixed C w vh ≤ Cs ∧ (∀ i, 0 ≤ q i * vh i) ∧
      ∀ v, mixed C w v ≤ Cs →
        q ⬝ᵥ v ≤ q ⬝ᵥ vh + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N)) := by
  intro κ a L ab κb Nt Pt Λ ε ev zf best
  have hδ : 0 ≤ δ := le_trans (by positivity) hδM
  -- data are constant on copies
  have ha : ∀ i e, hid i = some e → a i = ab e := fun i e he => by
    simp only [a, ab, hwb i e he, hqb i e he]
  have hκe : ∀ i e, hid i = some e → κ i = κb e := fun i e he => by
    simp only [κ, κb, hwb i e he]
  have hz : ∀ τ lm i e, hid i = some e →
      zlam a κ ρ τ lm i = clip (ab e) (τ * κb e) (ρ + lm) := fun τ lm i e he => by
    simp only [zlam, ha i e he, hκe i e he]
  have hNP : ∀ τ ∈ Icc h (1 - h), ∀ lm, 0 ≤ lm →
      |Nt τ lm - euc (zlam a κ ρ τ lm) ^ 2| ≤ δ ∧
        |Pt τ lm - a ⬝ᵥ zlam a κ ρ τ lm| ≤ δ := by
    intro τ hτ lm hlm
    have hτ0 : 0 ≤ τ := by linarith [hτ.1]
    have hbd : ∀ u v : Fin n, u < v →
        |clip (ab s(u, v)) (τ * κb s(u, v)) (ρ + lm) ^ 2| ≤ Φ ∧
          |ab s(u, v) * clip (ab s(u, v)) (τ * κb s(u, v)) (ρ + lm)| ≤ Φ := fun u v _ => by
      have := clip_formula_bounds (B := τ * κb s(u, v)) (lm := lm)
        (mul_nonneg hτ0 (mul_nonneg hC.le (Real.sqrt_nonneg _))) hρ hlm (hAbar s(u, v))
      exact ⟨this.1.trans hΦ1, this.2.trans hΦ2⟩
    constructor
    · rw [euc_sq]
      exact (hiddenSumProg_err hid G hcount (fun i e he => by rw [hz τ lm i e he])
        (fun u v huv => floor_natAbs_lt (hbd u v huv).1 hB)).trans hδM
    · have := hiddenSumProg_err hid G hcount
        (ψ := fun i => a i * zlam a κ ρ τ lm i)
        (ψb := fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm))
        (fun i e he => by simp only [ha i e he, hz τ lm i e he])
        (fun u v huv => floor_natAbs_lt (hbd u v huv).2 hB)
      exact this.trans hδM
  exact support_inexact hC hCs hw hρ hh0 hh hAp hδ hδ hp Nt Pt N m hNP

/-- `supportProg_hidden` with any certified allowance `δ ≥ M·2^{−p}`. -/
theorem supportProg_hidden_gen (G : DiGraph (Fin n)) (hid : Fin M → Option (Sym2 (Fin n)))
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {C Cs : ℝ} {w q : Fin M → ℝ} {wb qb : Sym2 (Fin n) → ℝ}
    (hwb : ∀ i e, hid i = some e → w i = wb e) (hqb : ∀ i e, hid i = some e → q i = qb e)
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < w i) {ρ h Ap Abar Φ : ℝ} (hρ : 0 < ρ)
    (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * q i / (C * Real.sqrt (w i))) ≤ Ap)
    (hAbar : ∀ e, |Cs * qb e / (C * Real.sqrt (wb e))| ≤ Abar)
    (hΦ1 : Abar ^ 2 / (4 * ρ ^ 2) ≤ Φ) (hΦ2 : Abar ^ 2 / (2 * ρ) ≤ Φ)
    {p B : ℕ} (hB : Φ * 2 ^ p + 1 ≤ 2 ^ B) {δ : ℝ} (hδM : (M : ℝ) / 2 ^ p ≤ δ)
    (hp : δ ≤ 3 * h ^ 2 / 4) (N m : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let ab : Sym2 (Fin n) → ℝ := fun e => Cs * qb e / (C * Real.sqrt (wb e))
    let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (wb e)
    let NP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), zlam a κ ρ τ lm i ^ 2)
        (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B
    let PP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), a i * zlam a κ ρ τ lm i)
        (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B
    let Λ := Ap / h
    let ε := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ m) + (3 * Λ + 4 * ρ + euc a / (2 * h)) * δ + 4 * δ
    let EV := fun τ => ievalProg (NP τ) (PP τ) δ δ ρ (1 - τ) Λ m
    let out := (supportProg EV h N).eval G.out
    let vh : Fin M → ℝ := fun i =>
      Cs * (out.2.2.1 • zlam a κ ρ out.1 out.2.1) i / (C * Real.sqrt (w i))
    out.1 ∈ Icc h (1 - h) ∧ mixed C w vh ≤ Cs ∧ (∀ i, 0 ≤ q i * vh i) ∧
      (∀ v, mixed C w v ≤ Cs →
        q ⬝ᵥ v ≤ q ⬝ᵥ vh + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N))) ∧
      (supportProg EV h N).cost G.out ≤ (2 * N + 2) * ((m + 3) * (6 * B * n)) := by
  intro κ a L ab κb NP PP Λ ε EV out vh
  have hmain := support_hidden_gen G hid hcount hwb hqb hC hCs hw hρ hh0 hh hAp hAbar hΦ1 hΦ2 hB hδM hp
    N m
  have hEV : ∀ τ, (EV τ).eval G.out =
      ieval (fun lm => (NP τ lm).eval G.out) (fun lm => (PP τ lm).eval G.out) δ δ ρ (1 - τ) Λ m :=
    fun τ => ievalProg_eval _ _ _ _ _ _ _ _ _
  obtain ⟨htr, harg, hval⟩ := trisectProg_eval EV (by linarith : h ≤ 1 - h) G.out N
  have hout : out = (((trisectProg EV h (1 - h) N).eval G.out).2,
      (EV ((trisectProg EV h (1 - h) N).eval G.out).2).eval G.out) := by
    simp only [out, supportProg, DTree.eval_cast, DTree.eval_bind, DTree.eval_map]
  set t₀ := ((trisectProg EV h (1 - h) N).eval G.out).2
  have hℓ : (fun τ => ((EV τ).eval G.out).2.2.1) =
      (fun τ => (ieval (fun lm => (NP τ lm).eval G.out) (fun lm => (PP τ lm).eval G.out)
        δ δ ρ (1 - τ) Λ m).2.2.1) := funext fun τ => by rw [hEV]
  have hu : (fun τ => ((EV τ).eval G.out).2.2.2) =
      (fun τ => (ieval (fun lm => (NP τ lm).eval G.out) (fun lm => (PP τ lm).eval G.out)
        δ δ ρ (1 - τ) Λ m).2.2.2) := funext fun τ => by rw [hEV]
  rw [hℓ, hu] at hval
  have hval' : (trisect (fun τ => (ieval (fun lm => (NP τ lm).eval G.out)
      (fun lm => (PP τ lm).eval G.out) δ δ ρ (1 - τ) Λ m).2.2.1)
      (fun τ => (ieval (fun lm => (NP τ lm).eval G.out) (fun lm => (PP τ lm).eval G.out)
        δ δ ρ (1 - τ) Λ m).2.2.2) h (1 - h) N).best ≤
      (ieval (fun lm => (NP t₀ lm).eval G.out) (fun lm => (PP t₀ lm).eval G.out)
        δ δ ρ (1 - t₀) Λ m).2.2.1 := hval.ge
  obtain ⟨h1, h2, h3⟩ := hmain.2 t₀ harg hval'
  have hvh : vh = fun i => Cs * ((ieval (fun lm => (NP t₀ lm).eval G.out)
      (fun lm => (PP t₀ lm).eval G.out) δ δ ρ (1 - t₀) Λ m).2.1 •
        zlam a κ ρ t₀ (ieval (fun lm => (NP t₀ lm).eval G.out)
          (fun lm => (PP t₀ lm).eval G.out) δ δ ρ (1 - t₀) Λ m).1) i /
        (C * Real.sqrt (w i)) := by
    simp only [vh, hout, hEV]
  refine ⟨by rw [hout]; exact harg, ?_, ?_, ?_, ?_⟩
  · rw [hvh]; exact h1
  · rw [hvh]; exact h2
  · rw [hvh]; exact h3
  · exact DTree.cost_le _ _

/-- `supportRoundProg_hidden` with any certified allowance `δ ≥ M·2^{−p}`. -/
theorem supportRoundProg_hidden_gen (G : DiGraph (Fin n)) (hid : Fin M → Option (Sym2 (Fin n)))
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {C Cs : ℝ} {w q : Fin M → ℝ} {wb qb : Sym2 (Fin n) → ℝ}
    (hwb : ∀ i e, hid i = some e → w i = wb e) (hqb : ∀ i e, hid i = some e → q i = qb e)
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < w i) {ρ h Ap Abar Φ : ℝ} (hρ : 0 < ρ)
    (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * q i / (C * Real.sqrt (w i))) ≤ Ap)
    (hAbar : ∀ e, |Cs * qb e / (C * Real.sqrt (wb e))| ≤ Abar)
    (hΦ1 : Abar ^ 2 / (4 * ρ ^ 2) ≤ Φ) (hΦ2 : Abar ^ 2 / (2 * ρ) ≤ Φ)
    {p B : ℕ} (hB : Φ * 2 ^ p + 1 ≤ 2 ^ B) {δ : ℝ} (hδM : (M : ℝ) / 2 ^ p ≤ δ)
    (hp : δ ≤ 3 * h ^ 2 / 4) (N m : ℕ)
    (kτ kl kc po : ℕ) :
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let ab : Sym2 (Fin n) → ℝ := fun e => Cs * qb e / (C * Real.sqrt (wb e))
    let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (wb e)
    let NP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), zlam a κ ρ τ lm i ^ 2)
        (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B
    let PP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), a i * zlam a κ ρ τ lm i)
        (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B
    let Λ := Ap / h
    let ε := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ m) + (3 * Λ + 4 * ρ + euc a / (2 * h)) * δ + 4 * δ
    let EV := fun τ => ievalProg (NP τ) (PP τ) δ δ ρ (1 - τ) Λ m
    let out := (supportProg EV h N).eval G.out
    let vh : Fin M → ℝ := fun i =>
      Cs * (out.2.2.1 • zlam a κ ρ out.1 out.2.1) i / (C * Real.sqrt (w i))
    let R := (1 / 2) ^ kτ * L + euc a ^ 2 * ((1 / 2) ^ kc / (2 * ρ) + (1 / 2) ^ kl / (2 * ρ ^ 2)) +
      (∑ i, |q i|) * (1 / 2) ^ po
    let res := (supportRoundProg EV h N C Cs ρ kτ kl kc po q w).eval G.out
    let v := res.2
    res.1 = roundScalars kτ kl kc out ∧
      (∃ m₁ : ℤ, res.1.1 = m₁ / 2 ^ kτ) ∧ (∃ m₂ : ℤ, res.1.2.1 = m₂ / 2 ^ kl) ∧
      (∃ m₃ : ℤ, res.1.2.2 = m₃ / 2 ^ kc) ∧
      0 ≤ res.1.1 ∧ 0 ≤ res.1.2.1 ∧ 0 ≤ res.1.2.2 ∧ res.1.2.2 ≤ 1 ∧
      (∀ i, v i = roundCoord C Cs ρ po res.1.1 res.1.2.1 res.1.2.2 (q i) (w i)) ∧
      (∀ i e, hid i = some e →
        v i = roundCoord C Cs ρ po res.1.1 res.1.2.1 res.1.2.2 (qb e) (wb e)) ∧
      (∀ i, ∃ m : ℤ, v i = m / 2 ^ po) ∧
      mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ q i * v i) ∧
      q ⬝ᵥ vh - R ≤ q ⬝ᵥ v ∧
      (∀ v₀, mixed C w v₀ ≤ Cs →
        q ⬝ᵥ v₀ ≤ q ⬝ᵥ v + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N) + R)) ∧
      (supportRoundProg EV h N C Cs ρ kτ kl kc po q w).cost G.out ≤
        (2 * N + 2) * ((m + 3) * (6 * B * n)) := by
  intro κ a L ab κb NP PP Λ ε EV out vh R res v
  obtain ⟨hτ, hball, hal, hsupp, -⟩ :=
    supportProg_hidden_gen G hid hcount hwb hqb hC hCs hw hρ hh0 hh hAp hAbar hΦ1 hΦ2 hB hδM hp N m
  replace hτ : out.1 ∈ Icc h (1 - h) := hτ
  have hres : res = (roundScalars kτ kl kc out,
      fun i => roundCoord C Cs ρ po (roundScalars kτ kl kc out).1
        (roundScalars kτ kl kc out).2.1 (roundScalars kτ kl kc out).2.2 (q i) (w i)) := by
    simp only [res, supportRoundProg, DTree.eval_map]; rfl
  -- the scalars of the unrounded output
  have hΛ0 : 0 ≤ Λ := div_nonneg ((euc_nonneg a).trans hAp) hh0.le
  have hout2 : out.2 = ieval (fun lm => (NP out.1 lm).eval G.out)
      (fun lm => (PP out.1 lm).eval G.out) δ δ ρ (1 - out.1) Λ m := by
    have e := supportProg_eval EV h N G.out
    have e1 : out.2 = (EV out.1).eval G.out := by simp only [out, e]
    rw [e1]; exact ievalProg_eval _ _ _ _ _ _ _ _ _
  have hlm0 : 0 ≤ out.2.1 := by rw [hout2]; simp only [ieval]; exact ilam_nonneg hΛ0 m
  have hc : 0 ≤ out.2.2.1 ∧ out.2.2.1 ≤ 1 := by
    rw [hout2]; exact iscale_mem (by linarith [hτ.2])
  have hτ0 : 0 ≤ out.1 := by linarith [hτ.1]
  obtain ⟨hdy, hball', hal', hloss⟩ :=
    round_support (Cs := Cs) (q := q) hC hw hρ hτ0 hlm0 hc.1 hc.2 kτ kl kc po hball hal
  have hsL : ∑ i, |a i| * κ i ≤ L := le_max_right _ _
  have hR : (1 / 2) ^ kτ * ∑ i, |a i| * κ i +
      euc a ^ 2 * ((1 / 2) ^ kc / (2 * ρ) + (1 / 2) ^ kl / (2 * ρ ^ 2)) +
      (∑ i, |q i|) * (1 / 2) ^ po ≤ R :=
    by have := mul_le_mul_of_nonneg_left hsL (by positivity : (0 : ℝ) ≤ (1 / 2) ^ kτ)
       simp only [R]; linarith
  have hv : v = fun i => roundCoord C Cs ρ po (roundScalars kτ kl kc out).1
      (roundScalars kτ kl kc out).2.1 (roundScalars kτ kl kc out).2.2 (q i) (w i) := by
    simp only [v, hres]
  have hres1 : res.1 = roundScalars kτ kl kc out := by rw [hres]
  have hcopy : ∀ i e, hid i = some e →
      roundCoord C Cs ρ po (roundScalars kτ kl kc out).1 (roundScalars kτ kl kc out).2.1
        (roundScalars kτ kl kc out).2.2 (q i) (w i) =
      roundCoord C Cs ρ po (roundScalars kτ kl kc out).1 (roundScalars kτ kl kc out).2.1
        (roundScalars kτ kl kc out).2.2 (qb e) (wb e) := fun i e he => by
    rw [hqb i e he, hwb i e he]
  set vr : Fin M → ℝ := fun i => roundCoord C Cs ρ po (roundScalars kτ kl kc out).1
      (roundScalars kτ kl kc out).2.1 (roundScalars kτ kl kc out).2.2 (q i) (w i) with hvr
  have hloss' : q ⬝ᵥ vh - ((1 / 2) ^ kτ * ∑ i, |a i| * κ i +
      euc a ^ 2 * ((1 / 2) ^ kc / (2 * ρ) + (1 / 2) ^ kl / (2 * ρ ^ 2)) +
      (∑ i, |q i|) * (1 / 2) ^ po) ≤ q ⬝ᵥ vr := hloss
  have hsupp' : ∀ v₀, mixed C w v₀ ≤ Cs →
      q ⬝ᵥ v₀ ≤ q ⬝ᵥ vh + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N)) := hsupp
  rw [hv, hres1]
  refine ⟨rfl, dyadicRound_int _ _, dyadicUp_int _ _, dyadicRound_int _ _,
    dyadicRound_nonneg _ hτ0, hlm0.trans (le_dyadicUp _ _), dyadicRound_nonneg _ hc.1,
    (dyadicRound_le _ _).trans hc.2, fun i => rfl, hcopy, hdy, hball', hal', by linarith,
    fun v₀ hv₀ => by have := hsupp' v₀ hv₀; linarith, ?_⟩
  exact DTree.cost_le _ _

end HiddenGen

end

end ImplicitLP
end CutQueryComplexity
/-! # The public support wrapper (D7)

`supportPubProg` takes the support data as public LP points (`q`, `w` copy-constant), expands the
explicit-row sums publicly (`explSum`: the `q` row and the `y⁺`, `y⁻` rows), uses the public
allowance `δ = M̄·2^{−p}`, and returns a public LP point. Its copies are the vector of
`supportRoundProg_hidden_gen` (`supportPub_eval`), so it inherits the guarantee
(`supportPub_hidden`). -/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

open DirectedMincut (LPPoint)

variable {n : ℕ}

/-- The pair formula `s(u, v) ↦ z(min, max)` of an LP point's hidden field. -/
def pairOf (z : Fin n → Fin n → ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun u v => if u ≤ v then z u v else z v u, fun u v => by
    rcases lt_trichotomy u v with h | rfl | h
    · simp [h.le, not_le.mpr h]
    · rfl
    · simp [h.le, not_le.mpr h]⟩

theorem pairOf_mk_lt (z : Fin n → Fin n → ℝ) {u v : Fin n} (h : u < v) :
    pairOf z s(u, v) = z u v := by
  simp [pairOf, h.le]

variable (G : DiGraph (Fin n))

theorem lpVec_hid (pt : LPPoint (Fin n)) (i : Fin (lpM G)) (e : Sym2 (Fin n))
    (h : lpHidF G i = some e) : lpVec G pt i = pairOf pt.z e := by
  simp only [lpHidF] at h
  simp only [lpVec]
  generalize (lpEquiv G).symm i = x at h ⊢
  rcases x with ⟨p, _⟩ | _
  · simp only [lpHid, Option.some.injEq] at h
    subst h
    simp only [lpVal]
    rw [pairOf_mk_lt _ p.2]
  · simp [lpHid] at h

/-- The explicit rows' sum of a formula `g(qᵢ, wᵢ)`, computed from the public points. -/
def explSum (g : ℝ → ℝ → ℝ) (qp wp : LPPoint (Fin n)) : ℝ :=
  g qp.q wp.q + ∑ j, g (qp.yp j) (wp.yp j) + ∑ j, g (qp.ym j) (wp.ym j)

/-- **The explicit-row sum is public.** -/
theorem explSum_eq (g : ℝ → ℝ → ℝ) (qp wp : LPPoint (Fin n)) :
    ∑ i ∈ univ.filter (fun i => lpHidF G i = none), g (lpVec G qp i) (lpVec G wp i) =
      explSum g qp wp := by
  rw [sum_filter, ← (lpEquiv G).sum_comp]
  simp only [lpHidF, lpVec, Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [lpHid, lpVal, explSum, add_assoc]

/-- The rounded output as a public point. -/
def roundPt (C Cs ρ : ℝ) (po : ℕ) (s : ℝ × ℝ × ℝ) (qp wp : LPPoint (Fin n)) : LPPoint (Fin n) :=
  ⟨fun u v => roundCoord C Cs ρ po s.1 s.2.1 s.2.2 (qp.z u v) (wp.z u v),
    roundCoord C Cs ρ po s.1 s.2.1 s.2.2 qp.q wp.q,
    fun j => roundCoord C Cs ρ po s.1 s.2.1 s.2.2 (qp.yp j) (wp.yp j),
    fun j => roundCoord C Cs ρ po s.1 s.2.1 s.2.2 (qp.ym j) (wp.ym j)⟩

theorem lpVec_roundPt (C Cs ρ : ℝ) (po : ℕ) (s : ℝ × ℝ × ℝ) (qp wp : LPPoint (Fin n))
    (i : Fin (lpM G)) :
    lpVec G (roundPt C Cs ρ po s qp wp) i =
      roundCoord C Cs ρ po s.1 s.2.1 s.2.2 (lpVec G qp i) (lpVec G wp i) := by
  simp only [lpVec]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j)) <;> rfl

/-- The coordinate formulas `z(λ)ᵢ²` and `aᵢ z(λ)ᵢ` as functions of `(qᵢ, wᵢ)`. -/
def zsqF (C Cs ρ τ lm : ℝ) (qi wi : ℝ) : ℝ :=
  clip (Cs * qi / (C * Real.sqrt wi)) (τ * (C * Real.sqrt wi)) (ρ + lm) ^ 2

def zdotF (C Cs ρ τ lm : ℝ) (qi wi : ℝ) : ℝ :=
  Cs * qi / (C * Real.sqrt wi) * clip (Cs * qi / (C * Real.sqrt wi)) (τ * (C * Real.sqrt wi)) (ρ + lm)

/-- The public evaluator: hidden sums as pair aggregates, explicit sums expanded publicly,
allowance `δ = M̄·2^{−p}`. -/
def evPub (C Cs ρ : ℝ) (qp wp : LPPoint (Fin n)) (Mbar Ap h : ℝ) (p B m : ℕ) (τ : ℝ) :
    DTree (Finset (Fin n)) ℕ (ℝ × ℝ × ℝ × ℝ) ((m + 3) * (6 * B * n)) :=
  let ab : Sym2 (Fin n) → ℝ := fun e => Cs * pairOf qp.z e / (C * Real.sqrt (pairOf wp.z e))
  let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (pairOf wp.z e)
  ievalProg
    (fun lm => hiddenSumProg (explSum (zsqF C Cs ρ τ lm) qp wp)
      (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B)
    (fun lm => hiddenSumProg (explSum (zdotF C Cs ρ τ lm) qp wp)
      (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B)
    (Mbar / 2 ^ p) (Mbar / 2 ^ p) ρ (1 - τ) (Ap / h) m

/-- **The public support program.** Trisection with the public evaluator, then the offline
conservative rounding; output the rounded scalars and a public LP point. -/
def supportPubProg (C Cs ρ : ℝ) (qp wp : LPPoint (Fin n)) (Mbar Ap h : ℝ) (p B m N : ℕ)
    (kτ kl kc po : ℕ) :
    DTree (Finset (Fin n)) ℕ ((ℝ × ℝ × ℝ) × LPPoint (Fin n)) ((2 * N + 2) * ((m + 3) * (6 * B * n))) :=
  (supportProg (evPub C Cs ρ qp wp Mbar Ap h p B m) h N).map fun out =>
    let s := roundScalars kτ kl kc out
    (s, roundPt C Cs ρ po s qp wp)

/-- **Budget on every execution:** `(2N + 2)(m + 3)·6Bn`. -/
theorem supportPubProg_cost (C Cs ρ : ℝ) (qp wp : LPPoint (Fin n)) (Mbar Ap h : ℝ)
    (p B m N kτ kl kc po : ℕ) :
    (supportPubProg C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po).cost G.out ≤
      (2 * N + 2) * ((m + 3) * (6 * B * n)) := DTree.cost_le _ _

/-- **The public program computes `supportRoundProg`'s output** with `q = lpVec qp`,
`w = lpVec wp`, `δ = M̄·2^{−p}`: same scalars, and the output point's copies are its vector. -/
theorem supportPub_eval (C Cs ρ : ℝ) (qp wp : LPPoint (Fin n)) (Mbar Ap h : ℝ)
    (p B m N kτ kl kc po : ℕ) :
    let q := lpVec G qp
    let w := lpVec G wp
    let hid := lpHidF G
    let κ : Fin (lpM G) → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin (lpM G) → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let ab : Sym2 (Fin n) → ℝ := fun e => Cs * pairOf qp.z e / (C * Real.sqrt (pairOf wp.z e))
    let κb : Sym2 (Fin n) → ℝ := fun e => C * Real.sqrt (pairOf wp.z e)
    let δ : ℝ := Mbar / 2 ^ p
    let NP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), zlam a κ ρ τ lm i ^ 2)
        (fun e => clip (ab e) (τ * κb e) (ρ + lm) ^ 2) p B
    let PP : ℝ → ℝ → DTree (Finset (Fin n)) ℕ ℝ (6 * B * n) := fun τ lm =>
      hiddenSumProg (∑ i ∈ univ.filter (fun i => hid i = none), a i * zlam a κ ρ τ lm i)
        (fun e => ab e * clip (ab e) (τ * κb e) (ρ + lm)) p B
    let Λ := Ap / h
    let EV := fun τ => ievalProg (NP τ) (PP τ) δ δ ρ (1 - τ) Λ m
    let res := (supportPubProg C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po).eval G.out
    let resM := (supportRoundProg EV h N C Cs ρ kτ kl kc po q w).eval G.out
    res.1 = resM.1 ∧ lpVec G res.2 = resM.2 := by
  intro q w hid κ a ab κb δ NP PP Λ EV res resM
  have hEV : evPub C Cs ρ qp wp Mbar Ap h p B m = EV := by
    funext τ
    simp only [evPub, EV, NP, PP]
    congr 2
    · funext lm
      rw [← explSum_eq G]; rfl
    · funext lm
      rw [← explSum_eq G]; rfl
  have h1 : res = (roundScalars kτ kl kc ((supportProg EV h N).eval G.out),
      roundPt C Cs ρ po (roundScalars kτ kl kc ((supportProg EV h N).eval G.out)) qp wp) := by
    simp only [res, supportPubProg, DTree.eval_map, hEV]
  have h2 : resM = (roundScalars kτ kl kc ((supportProg EV h N).eval G.out),
      fun i => roundCoord C Cs ρ po (roundScalars kτ kl kc ((supportProg EV h N).eval G.out)).1
        (roundScalars kτ kl kc ((supportProg EV h N).eval G.out)).2.1
        (roundScalars kτ kl kc ((supportProg EV h N).eval G.out)).2.2 (q i) (w i)) := by
    simp only [resM, supportRoundProg, DTree.eval_map]
  rw [h1, h2]
  exact ⟨rfl, funext fun i => lpVec_roundPt G _ _ _ _ _ _ _ i⟩

/-- **The public support oracle's guarantee.** With copy-constant data `q = lpVec qp`,
`w = lpVec wp` (`w > 0`), a public row bound `M ≤ M̄`, and the public allowance
`δ = M̄·2^{−p} ≤ 3h²/4`, the output point `v` (copies `lpVec v`) has dyadic coordinates, lies in
the ball, is sign-aligned with `q`, and satisfies the support inequality with loss
`ρ + Lh + 3ε + L(1 − 2h)(2/3)ᴺ + R`; budget `(2N + 2)(m + 3)·6Bn`. -/
theorem supportPub_hidden (qp wp : LPPoint (Fin n)) {C Cs : ℝ}
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < lpVec G wp i) {ρ h Ap Abar Φ Mbar : ℝ}
    (hρ : 0 < ρ) (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hAp : euc (fun i => Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))) ≤ Ap)
    (hAbar : ∀ e, |Cs * pairOf qp.z e / (C * Real.sqrt (pairOf wp.z e))| ≤ Abar)
    (hΦ1 : Abar ^ 2 / (4 * ρ ^ 2) ≤ Φ) (hΦ2 : Abar ^ 2 / (2 * ρ) ≤ Φ)
    {p B : ℕ} (hB : Φ * 2 ^ p + 1 ≤ 2 ^ B) (hMbar : (lpM G : ℝ) ≤ Mbar)
    (hp : Mbar / 2 ^ p ≤ 3 * h ^ 2 / 4) (N m : ℕ) (kτ kl kc po : ℕ) :
    let q := lpVec G qp
    let w := lpVec G wp
    let κ : Fin (lpM G) → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin (lpM G) → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    let L := max (euc a) (∑ i, |a i| * κ i)
    let δ : ℝ := Mbar / 2 ^ p
    let Λ := Ap / h
    let ε := Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ m) + (3 * Λ + 4 * ρ + euc a / (2 * h)) * δ + 4 * δ
    let R := (1 / 2) ^ kτ * L + euc a ^ 2 * ((1 / 2) ^ kc / (2 * ρ) + (1 / 2) ^ kl / (2 * ρ ^ 2)) +
      (∑ i, |q i|) * (1 / 2) ^ po
    let res := (supportPubProg C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po).eval G.out
    let v := lpVec G res.2
    (∃ m₁ : ℤ, res.1.1 = m₁ / 2 ^ kτ) ∧ (∃ m₂ : ℤ, res.1.2.1 = m₂ / 2 ^ kl) ∧
      (∃ m₃ : ℤ, res.1.2.2 = m₃ / 2 ^ kc) ∧
      0 ≤ res.1.1 ∧ 0 ≤ res.1.2.1 ∧ 0 ≤ res.1.2.2 ∧ res.1.2.2 ≤ 1 ∧
      (∀ i, ∃ m : ℤ, v i = m / 2 ^ po) ∧
      mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ q i * v i) ∧
      (∀ v₀, mixed C w v₀ ≤ Cs →
        q ⬝ᵥ v₀ ≤ q ⬝ᵥ v + (ρ + L * h + 3 * ε + L * ((1 - 2 * h) * (2 / 3) ^ N) + R)) ∧
      (supportPubProg C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po).cost G.out ≤
        (2 * N + 2) * ((m + 3) * (6 * B * n)) := by
  intro q w κ a L δ Λ ε R res v
  have hδM : ((lpM G : ℕ) : ℝ) / 2 ^ p ≤ δ := div_le_div_of_nonneg_right hMbar (by positivity)
  obtain ⟨e1, e2⟩ := supportPub_eval G C Cs ρ qp wp Mbar Ap h p B m N kτ kl kc po
  obtain ⟨-, d1, d2, d3, n1, n2, n3, n4, -, -, hdy, hball, hal, -, hsupp, -⟩ :=
    supportRoundProg_hidden_gen G (lpHidF G) (lp_hcount G) (wb := pairOf wp.z)
      (qb := pairOf qp.z) (fun i e he => lpVec_hid G wp i e he)
      (fun i e he => lpVec_hid G qp i e he) hC hCs hw hρ hh0 hh hAp hAbar hΦ1 hΦ2 hB hδM hp N m
      kτ kl kc po
  have hv : v = _ := e2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, DTree.cost_le _ _⟩
  · rw [show res.1 = _ from e1]; exact d1
  · rw [show res.1 = _ from e1]; exact d2
  · rw [show res.1 = _ from e1]; exact d3
  · rw [show res.1 = _ from e1]; exact n1
  · rw [show res.1 = _ from e1]; exact n2
  · rw [show res.1 = _ from e1]; exact n3
  · rw [show res.1 = _ from e1]; exact n4
  · rw [hv]; exact hdy
  · rw [hv]; exact hball
  · rw [hv]; exact hal
  · rw [hv]; exact hsupp

end

end ImplicitLP
end CutQueryComplexity
/-! # Public support parameters (D7)

Given public bounds `‖a‖₂ ≤ A₊`, `L ≤ L₊`, `Σ|qᵢ| ≤ S₊`, `|ā_e| ≤ Ā`, `M ≤ M̄` and a target loss
`σ > 0`, `SupPub` chooses `ρ, h, m, N, p, B, k_τ, k_λ, k_c, p_o` so that the total additive loss
of the public support oracle is `≤ σ` (`supportPub_public`). -/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

open DirectedMincut (LPPoint)

/-- Public envelope of one support call. -/
structure SupPub where
  Mbar : ℝ
  Ap : ℝ
  Lb : ℝ
  Sq : ℝ
  Abar : ℝ
  σ : ℝ

namespace SupPub

variable (S : SupPub)

def ρ : ℝ := S.σ / 6
def h : ℝ := min (1 / 4) (S.σ / (6 * (S.Lb + 1)))
def Λ : ℝ := S.Ap / S.h
def m : ℕ := bits (S.Λ ^ 2 * S.Ap / S.ρ ^ 2) (S.σ / 54)
def cδ : ℝ := 3 * S.Λ + 4 * S.ρ + S.Ap / (2 * S.h) + 4
def δt : ℝ := min (S.σ / (27 * S.cδ)) (3 * S.h ^ 2 / 4)
def p : ℕ := bits S.Mbar S.δt
def N : ℕ := 2 * iters (S.σ / (6 * (S.Lb + 1)))
def kτ : ℕ := bits S.Lb (S.σ / 24)
def kc : ℕ := bits (S.Ap ^ 2 / (2 * S.ρ)) (S.σ / 24)
def kl : ℕ := bits (S.Ap ^ 2 / (2 * S.ρ ^ 2)) (S.σ / 24)
def po : ℕ := bits S.Sq (S.σ / 24)
def Φ : ℝ := S.Abar ^ 2 / (4 * S.ρ ^ 2) + S.Abar ^ 2 / (2 * S.ρ)
def B : ℕ := magBits (S.Φ * 2 ^ S.p + 1)

end SupPub

/-- `x · 2^{−bits c β} ≤ β` whenever `x ≤ c`. -/
theorem mul_half_pow_bits_le {x c β : ℝ} (hβ : 0 < β) (hx : x ≤ c) :
    x * (1 / 2) ^ bits c β ≤ β := by
  have h := div_two_pow_bits_le (c := c) hβ
  have h0 : (0 : ℝ) ≤ (1 / 2) ^ bits c β := by positivity
  calc x * (1 / 2) ^ bits c β ≤ c * (1 / 2) ^ bits c β := mul_le_mul_of_nonneg_right hx h0
    _ = c / 2 ^ bits c β := by rw [_root_.one_div_pow, mul_one_div]
    _ ≤ β := h

variable {n : ℕ} (G : DiGraph (Fin n))

set_option maxHeartbeats 3200000 in
/-- **The public support oracle with total loss `≤ σ`.** With the public parameters of `SupPub`
and copy-constant data, the output point `v` has dyadic coordinates, lies in the ball, is
sign-aligned with `q`, and `⟨q, v₀⟩ ≤ ⟨q, v⟩ + σ` for every `v₀` in the ball; budget
`(2N + 2)(m + 3)·6Bn` on every execution. -/
theorem supportPub_public (S : SupPub) (qp wp : LPPoint (Fin n)) {C Cs : ℝ}
    (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < lpVec G wp i) (hσ : 0 < S.σ)
    (hAp : euc (fun i => Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))) ≤ S.Ap)
    (hL : max (euc (fun i => Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))))
      (∑ i, |Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))| *
        (C * Real.sqrt (lpVec G wp i))) ≤ S.Lb)
    (hSq : ∑ i, |lpVec G qp i| ≤ S.Sq)
    (hAbar : ∀ e, |Cs * pairOf qp.z e / (C * Real.sqrt (pairOf wp.z e))| ≤ S.Abar)
    (hMbar : (lpM G : ℝ) ≤ S.Mbar) :
    let q := lpVec G qp
    let w := lpVec G wp
    let res := (supportPubProg C Cs S.ρ qp wp S.Mbar S.Ap S.h S.p S.B S.m S.N
      S.kτ S.kl S.kc S.po).eval G.out
    let v := lpVec G res.2
    (∀ i, ∃ m : ℤ, v i = m / 2 ^ S.po) ∧ mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ q i * v i) ∧
      (∀ v₀, mixed C w v₀ ≤ Cs → q ⬝ᵥ v₀ ≤ q ⬝ᵥ v + S.σ) ∧
      (supportPubProg C Cs S.ρ qp wp S.Mbar S.Ap S.h S.p S.B S.m S.N
        S.kτ S.kl S.kc S.po).cost G.out ≤ (2 * S.N + 2) * ((S.m + 3) * (6 * S.B * n)) := by
  intro q w res v
  set a : Fin (lpM G) → ℝ := fun i => Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))
  set κ : Fin (lpM G) → ℝ := fun i => C * Real.sqrt (lpVec G wp i)
  set L := max (euc a) (∑ i, |a i| * κ i)
  have hA0 : 0 ≤ S.Ap := (euc_nonneg _).trans hAp
  have hL0 : 0 ≤ L := (euc_nonneg _).trans (le_max_left _ _)
  have hLb0 : 0 ≤ S.Lb := hL0.trans hL
  have hρ : 0 < S.ρ := by unfold SupPub.ρ; positivity
  have hh0 : 0 < S.h := lt_min (by norm_num) (by positivity)
  have hh4 : S.h ≤ 1 / 4 := min_le_left _ _
  have hhσ : S.h ≤ S.σ / (6 * (S.Lb + 1)) := min_le_right _ _
  have hΛ0 : 0 ≤ S.Λ := by unfold SupPub.Λ; positivity
  have hcδ : 0 < S.cδ := by unfold SupPub.cδ; positivity
  have hδt0 : 0 < S.δt := lt_min (by positivity) (by positivity)
  have hδ : S.Mbar / 2 ^ S.p ≤ S.δt := div_two_pow_bits_le hδt0
  have hδ0 : 0 ≤ S.Mbar / 2 ^ S.p := by
    have : (0 : ℝ) ≤ lpM G := Nat.cast_nonneg _
    have : 0 ≤ S.Mbar := by linarith
    positivity
  have hp : S.Mbar / 2 ^ S.p ≤ 3 * S.h ^ 2 / 4 := hδ.trans (min_le_right _ _)
  have hB : S.Φ * 2 ^ S.p + 1 ≤ 2 ^ S.B := by
    exact (lt_two_pow_magBits (S.Φ * 2 ^ S.p + 1)).le
  have hΦ1 : S.Abar ^ 2 / (4 * S.ρ ^ 2) ≤ S.Φ := by
    unfold SupPub.Φ; have : 0 ≤ S.Abar ^ 2 / (2 * S.ρ) := by positivity
    linarith
  have hΦ2 : S.Abar ^ 2 / (2 * S.ρ) ≤ S.Φ := by
    unfold SupPub.Φ; have : 0 ≤ S.Abar ^ 2 / (4 * S.ρ ^ 2) := by positivity
    linarith
  obtain ⟨-, -, -, -, -, -, -, hdy, hball, hal, hsupp, hcost⟩ :=
    supportPub_hidden G qp wp hC hCs hw hρ hh0 (by linarith) hAp hAbar hΦ1 hΦ2 hB hMbar hp
      S.N S.m S.kτ S.kl S.kc S.po
  refine ⟨hdy, hball, hal, fun v₀ hv₀ => (hsupp v₀ hv₀).trans ?_, hcost⟩
  -- the loss is at most `σ`
  have hea : euc a ≤ S.Ap := hAp
  have hea0 : 0 ≤ euc a := euc_nonneg _
  set δ := S.Mbar / 2 ^ S.p
  -- term 2
  have t2 : L * S.h ≤ S.σ / 6 := by
    calc L * S.h ≤ S.Lb * (S.σ / (6 * (S.Lb + 1))) :=
          mul_le_mul hL hhσ hh0.le hLb0
      _ ≤ S.σ / 6 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- term 3
  have e1 : S.Λ ^ 2 * euc a / (S.ρ ^ 2 * 2 ^ S.m) ≤ S.σ / 54 := by
    have := div_two_pow_bits_le (c := S.Λ ^ 2 * S.Ap / S.ρ ^ 2) (by positivity : 0 < S.σ / 54)
    calc S.Λ ^ 2 * euc a / (S.ρ ^ 2 * 2 ^ S.m) ≤ S.Λ ^ 2 * S.Ap / (S.ρ ^ 2 * 2 ^ S.m) := by
          gcongr
      _ = S.Λ ^ 2 * S.Ap / S.ρ ^ 2 / 2 ^ S.m := by ring
      _ ≤ S.σ / 54 := this
  have e2 : (3 * S.Λ + 4 * S.ρ + euc a / (2 * S.h)) * δ + 4 * δ ≤ S.σ / 27 := by
    have h1 : (3 * S.Λ + 4 * S.ρ + euc a / (2 * S.h)) * δ + 4 * δ ≤ S.cδ * δ := by
      unfold SupPub.cδ
      have : euc a / (2 * S.h) ≤ S.Ap / (2 * S.h) := by gcongr
      nlinarith
    have h2 : S.cδ * δ ≤ S.cδ * (S.σ / (27 * S.cδ)) :=
      mul_le_mul_of_nonneg_left (hδ.trans (min_le_left _ _)) hcδ.le
    have h3 : S.cδ * (S.σ / (27 * S.cδ)) = S.σ / 27 := by field_simp
    linarith
  -- term 4
  have t4 : L * ((1 - 2 * S.h) * (2 / 3) ^ S.N) ≤ S.σ / 6 := by
    have hk := half_pow_iters_le (by positivity : 0 < S.σ / (6 * (S.Lb + 1)))
    have hN : (2 / 3 : ℝ) ^ S.N ≤ S.σ / (6 * (S.Lb + 1)) := by
      unfold SupPub.N
      rw [pow_mul]
      refine le_trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 / 3 : ℝ) ^ 2 ≤ 1 / 2) _) hk
    have h1 : (1 - 2 * S.h) * (2 / 3) ^ S.N ≤ S.σ / (6 * (S.Lb + 1)) := by
      have : (0 : ℝ) ≤ (2 / 3) ^ S.N := by positivity
      nlinarith
    have h10 : 0 ≤ (1 - 2 * S.h) * (2 / 3) ^ S.N := by
      have : (0 : ℝ) ≤ (2 / 3) ^ S.N := by positivity
      have : 0 ≤ 1 - 2 * S.h := by linarith
      positivity
    calc L * ((1 - 2 * S.h) * (2 / 3) ^ S.N) ≤ S.Lb * (S.σ / (6 * (S.Lb + 1))) :=
          mul_le_mul hL h1 h10 hLb0
      _ ≤ S.σ / 6 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- term 5
  have r1 : (1 / 2) ^ S.kτ * L ≤ S.σ / 24 := by
    rw [mul_comm]; exact mul_half_pow_bits_le (by positivity) hL
  have r2 : euc a ^ 2 * ((1 / 2) ^ S.kc / (2 * S.ρ)) ≤ S.σ / 24 := by
    have := mul_half_pow_bits_le (x := euc a ^ 2 / (2 * S.ρ)) (by positivity : 0 < S.σ / 24)
      (by gcongr : euc a ^ 2 / (2 * S.ρ) ≤ S.Ap ^ 2 / (2 * S.ρ))
    calc _ = euc a ^ 2 / (2 * S.ρ) * (1 / 2) ^ S.kc := by ring
      _ ≤ _ := this
  have r3 : euc a ^ 2 * ((1 / 2) ^ S.kl / (2 * S.ρ ^ 2)) ≤ S.σ / 24 := by
    have := mul_half_pow_bits_le (x := euc a ^ 2 / (2 * S.ρ ^ 2)) (by positivity : 0 < S.σ / 24)
      (by gcongr : euc a ^ 2 / (2 * S.ρ ^ 2) ≤ S.Ap ^ 2 / (2 * S.ρ ^ 2))
    calc _ = euc a ^ 2 / (2 * S.ρ ^ 2) * (1 / 2) ^ S.kl := by ring
      _ ≤ _ := this
  have r4 : (∑ i, |q i|) * (1 / 2) ^ S.po ≤ S.σ / 24 :=
    mul_half_pow_bits_le (by positivity) hSq
  have hρσ : S.ρ = S.σ / 6 := rfl
  show q ⬝ᵥ v + (S.ρ + L * S.h + 3 * (S.Λ ^ 2 * euc a / (S.ρ ^ 2 * 2 ^ S.m) +
      (3 * S.Λ + 4 * S.ρ + euc a / (2 * S.h)) * δ + 4 * δ) +
      L * ((1 - 2 * S.h) * (2 / 3) ^ S.N) +
      ((1 / 2) ^ S.kτ * L + euc a ^ 2 * ((1 / 2) ^ S.kc / (2 * S.ρ) +
        (1 / 2) ^ S.kl / (2 * S.ρ ^ 2)) + (∑ i, |q i|) * (1 / 2) ^ S.po)) ≤ q ⬝ᵥ v + S.σ
  have : euc a ^ 2 * ((1 / 2) ^ S.kc / (2 * S.ρ) + (1 / 2) ^ S.kl / (2 * S.ρ ^ 2)) =
      euc a ^ 2 * ((1 / 2) ^ S.kc / (2 * S.ρ)) + euc a ^ 2 * ((1 / 2) ^ S.kl / (2 * S.ρ ^ 2)) := by
    ring
  rw [this]
  linarith

end

end ImplicitLP
end CutQueryComplexity
/-! # The finite Lewis query loop (D7)

`lewisLoop` runs `J_L` Lewis iterations as a bounded randomized program. Iteration `j` calls
D4 (`Sparsify.sparsify`) on the current public pair weights `s²e^{(1−2/p)y}`, forms the explicit
preconditioner `P = lap(out) + E` (`E` the public explicit part), computes the approximate
leverages offline from `P⁻¹` (pair formulas `pairLev`), and rounds `(p/2) log σ̃` with
`dyadicRound k_μ`; the state is a public LP point. Budget `J_L · q_D4` (`lewisLoop_cost`).
With the leverage accuracy `ε_lev = Δ/1024` (D4 accuracy `δ = ε_lev/(2(R+1))`, separate from
`ε_solve = 1/8`) and `μ = 2^{−k_μ} ≤ Δ/256`, outside `J_L` times one D4 failure bound the output
satisfies `‖y_{J_L} − y*‖_∞ ≤ (3/4)^{J_L}‖y₀ − y*‖_∞ + Δ/32` (`lewisLoop_fail_le`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Spectral

noncomputable section

open DirectedMincut (LPPoint chi)
open scoped ENNReal

variable {n : ℕ}

/-! ## Public data of one Lewis iteration -/

/-- The hidden pair weights of the Lewis Gram: `s(e)² e^{a y(e)}`. -/
def lewisW (a : ℝ) (spt ypt : LPPoint (Fin n)) : Sym2 (Fin n) → ℝ :=
  fun e => pairOf spt.z e ^ 2 * Real.exp (a * pairOf ypt.z e)

def lewisDq (a : ℝ) (spt ypt : LPPoint (Fin n)) : ℝ := spt.q ^ 2 * Real.exp (a * ypt.q)
def lewisDp (a : ℝ) (spt ypt : LPPoint (Fin n)) : Fin n → ℝ :=
  fun j => spt.yp j ^ 2 * Real.exp (a * ypt.yp j)
def lewisDm (a : ℝ) (spt ypt : LPPoint (Fin n)) : Fin n → ℝ :=
  fun j => spt.ym j ^ 2 * Real.exp (a * ypt.ym j)

/-- The public explicit part of the Lewis Gram. -/
def lewisE (s t : Fin n) (a : ℝ) (spt ypt : LPPoint (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  lpE s t (lewisDq a spt ypt) (lewisDp a spt ypt) (lewisDm a spt ypt)

/-- The rounded approximate update as a public point: `⌊(p/2) log(s² aᵀQa)⌋_{k}` per row. -/
def lewisNewY (s t : Fin n) (p : ℝ) (k : ℕ) (spt : LPPoint (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) : LPPoint (Fin n) :=
  ⟨fun u v => dyadicRound k (p / 2 * Real.log (spt.z u v ^ 2 * pairLev Q s(u, v))),
    dyadicRound k (p / 2 * Real.log (spt.q ^ 2 * (chi s t ⬝ᵥ (Q *ᵥ chi s t)))),
    fun j => dyadicRound k (p / 2 * Real.log (spt.yp j ^ 2 *
      ((Pi.single j 1 : Fin n → ℝ) ⬝ᵥ (Q *ᵥ Pi.single j 1)))),
    fun j => dyadicRound k (p / 2 * Real.log (spt.ym j ^ 2 *
      (-(Pi.single j 1 : Fin n → ℝ) ⬝ᵥ (Q *ᵥ -Pi.single j 1))))⟩

variable (G : DiGraph (Fin n))

theorem lpD_lewis (a : ℝ) (spt ypt : LPPoint (Fin n)) :
    lpD G (lewisW a spt ypt) (lewisDq a spt ypt) (lewisDp a spt ypt) (lewisDm a spt ypt) =
      fun k => lpVec G spt k ^ 2 * Real.exp (a * lpVec G ypt k) := by
  funext i
  simp only [lpD, lpVec]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j))
  · simp only [lpWeight, lpVal, lewisW, pairOf_mk_lt _ p.2]
  all_goals rfl

theorem explicitGram_lewis (s t : Fin n) (a : ℝ) (spt ypt : LPPoint (Fin n)) :
    explicitGram (lpA G s t) (fun k => lpVec G spt k ^ 2 * Real.exp (a * lpVec G ypt k))
      (lpHidF G) = lewisE s t a spt ypt := by
  rw [← lpD_lewis, explicitGram_lp]; rfl

theorem lpVec_lewisNewY (s t : Fin n) (p : ℝ) (k : ℕ) (spt : LPPoint (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (i : Fin (lpM G)) :
    lpVec G (lewisNewY s t p k spt Q) i =
      dyadicRound k (p / 2 * Real.log (lpLev (lpA G s t) (lpVec G spt) (lpHidF G) Q i)) := by
  simp only [lpVec, lpLev, lpHidF, lpA]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j)) <;> rfl

/-! ## One step: Good D4 output ⇒ per-step error `p(2ε) + μ` -/

theorem lewis_step_err (s t : Fin n) (hst : s ≠ t) {spt ypt : LPPoint (Fin n)}
    (hs : ∀ i, 0 < lpVec G spt i) {p : ℝ} (hp0 : 0 < p) (k : ℕ)
    {K t' R : ℕ} {δ ε : ℝ} {out : Sym2 (Fin n) → ℝ}
    (hgood : Sparsify.Good G (lewisW (1 - 2 / p) spt ypt) K t' δ R out)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε) :
    let B := diagonal (lpVec G spt) * lpA G s t
    let Q := (lap out univ + lewisE s t (1 - 2 / p) spt ypt)⁻¹
    dist (lpVec G (lewisNewY s t p k spt Q)) (lewisMap p B (lpVec G ypt)) ≤
      p * (2 * ε) + (1 / 2) ^ k := by
  intro B Q
  set A := lpA G s t
  set sv := lpVec G spt
  set y := lpVec G ypt
  set a := 1 - 2 / p
  set D : Fin (lpM G) → ℝ := fun k => sv k ^ 2 * Real.exp (a * y k) with hDdef
  have hDpos : ∀ k, 0 < D k := fun k => mul_pos (pow_pos (hs k) 2) (Real.exp_pos _)
  have hA := det_ne_zero_of_idRows (lpA_idRows G s t)
  have hB : (Bᵀ * B).det ≠ 0 := diag_det hA fun j => (hs j).ne'
  have hrowB : ∀ i, B i ≠ 0 := fun i h0 => by
    apply lpA_row_ne_zero G hst i
    funext j
    have := congrFun h0 j
    simp only [B, diagonal_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (hs i).ne'
  have hw0 : ∀ e, 0 ≤ lewisW a spt ypt e := fun e => by
    unfold lewisW; positivity
  have hD : ∀ i e, lpHidF G i = some e → sv i ^ 2 * Real.exp (a * y i) = lewisW a spt ypt e :=
    fun i e he => by
      simp only [sv, y, lewisW, lpVec_hid G spt i e he, lpVec_hid G ypt i e he]
  set P := lap out univ + explicitGram A D (lpHidF G)
  have hPQ : Q = P⁻¹ := by
    simp only [Q, P, D, A]; rw [explicitGram_lewis]
  have hPs : Pᵀ = P := by
    simp only [P, transpose_add, lap_transpose, explicitGram_symm]
  have hsplit : gram B (fun k => Real.exp (a * y k)) =
      lap (Sparsify.omegaR G (lewisW a spt ypt) 0)
          (univ.filter fun e => Sparsify.P0 (lewisW a spt ypt) e = true) +
        explicitGram A D (lpHidF G) := by
    simp only [B]
    rw [gram_diag_mul]
    exact gram_split (lpHidF G) G (lewisW a spt ypt) (lpA_hrow G s t) hD hDpos (lp_hcount G)
  have hbd : ∀ x, (1 - 2 * ε) * (x ⬝ᵥ (P *ᵥ x)) ≤
        x ⬝ᵥ (gram B (fun k => Real.exp (a * y k)) *ᵥ x) ∧
      x ⬝ᵥ (gram B (fun k => Real.exp (a * y k)) *ᵥ x) ≤ (1 + 2 * ε) * (x ⬝ᵥ (P *ᵥ x)) :=
    fun x => by
      have h := frozen_precond hgood hw0 hε0 hε hδlo hδhi (1 : Matrix (Fin n) (Fin n) ℝ)
        (explicitGram_psd A (fun k => (hDpos k).le) (lpHidF G)) x
      simp only [pullLap_one] at h
      rw [hsplit]
      exact h
  have hζ : 0 ≤ p * (2 * ε) + (1 / 2) ^ k := by positivity
  refine (dist_pi_le_iff hζ).mpr fun i => ?_
  rw [Real.dist_eq]
  have h1 : |lpVec G (lewisNewY s t p k spt Q) i - lewisMapApprox p B P i| ≤ (1 / 2) ^ k := by
    rw [lpVec_lewisNewY, hPQ, lpLev_eq (lpA_hrow G s t)]
    exact abs_dyadicRound_sub_le k _
  have h2 := lewisMapApprox_err hB hrowB hp0 hPs (η := 2 * ε) (by linarith) (by linarith) y
    (fun x => (hbd x).1) (fun x => (hbd x).2) i
  calc _ ≤ |lpVec G (lewisNewY s t p k spt Q) i - lewisMapApprox p B P i| +
        |lewisMapApprox p B P i - lewisMap p B y i| := abs_sub_le _ _ _
    _ ≤ (1 / 2) ^ k + p * (2 * ε) := add_le_add h1 h2
    _ = _ := add_comm _ _

/-! ## The program -/

/-- One Lewis iteration: D4 on the current weights, then the offline update. -/
def lewisStepProg (s t : Fin n) (p : ℝ) (k : ℕ) (spt ypt : LPPoint (Fin n)) (K J t' R : ℕ) :
    RTree (Finset (Fin n)) ℕ (Option (LPPoint (Fin n)))
      ((R * Sparsify.levelBudget (n := n) K J t' + 3 * n) + 0) :=
  (Sparsify.sparsify (lewisW (1 - 2 / p) spt ypt) K J t' R).bind fun o => match o with
  | none => RTree.pure (PMF.pure none)
  | some out => RTree.pure (PMF.pure (some (lewisNewY s t p k spt
      (lap out univ + lewisE s t (1 - 2 / p) spt ypt)⁻¹)))

/-- **The Lewis loop**: `J_L` iterations from `y₀`; `none` once a D4 call aborts. -/
def lewisLoop (s t : Fin n) (p : ℝ) (k : ℕ) (spt y0 : LPPoint (Fin n)) (K J t' R : ℕ) :
    (JL : ℕ) → RTree (Finset (Fin n)) ℕ (Option (LPPoint (Fin n)))
      (JL * ((R * Sparsify.levelBudget (n := n) K J t' + 3 * n) + 0))
  | 0 => RTree.pure (PMF.pure (some y0))
  | JL + 1 => ((lewisLoop s t p k spt y0 K J t' R JL).bind fun o => match o with
      | none => RTree.pure (PMF.pure none)
      | some y => lewisStepProg s t p k spt y K J t' R).cast (by ring)

/-- **Budget on every execution:** `J_L · q_D4`. -/
theorem lewisLoop_cost (s t : Fin n) (p : ℝ) (k : ℕ) (spt y0 : LPPoint (Fin n))
    (K J t' R JL : ℕ) {o : Option (LPPoint (Fin n)) × ℕ}
    (ho : o ∈ (RTree.run G.out (lewisLoop s t p k spt y0 K J t' R JL)).support) :
    o.2 ≤ JL * (R * Sparsify.levelBudget (n := n) K J t' + 3 * n) := by
  have := RTree.cost_le _ _ ho
  simpa using this

/-! ## Public Lewis parameters and the guarantee -/

/-- Leverage accuracy `ε_lev = Δ/1024`. -/
def levEps (Δ : ℝ) : ℝ := Δ / 1024
/-- D4 accuracy for leverages: `δ = ε_lev/(2(R+1))`, so `2Rδ ≤ ε_lev`. -/
def levDelta (Δ : ℝ) (R : ℕ) : ℝ := levEps Δ / (2 * (R + 1))
/-- Mesh precision `k_μ = bits(1, Δ/256)`, so `μ = 2^{−k_μ} ≤ Δ/256`. -/
def levBits (Δ : ℝ) : ℕ := bits 1 (Δ / 256)

theorem levDelta_spec {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 256) (R : ℕ) :
    0 < levDelta Δ R ∧ levDelta Δ R ≤ 1 ∧ 1 - levEps Δ ≤ (1 - levDelta Δ R) ^ R ∧
      (1 + levDelta Δ R) ^ R ≤ 1 + levEps Δ := by
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have he0 : 0 < levEps Δ := by unfold levEps; positivity
  have he1 : levEps Δ ≤ 1 / 4 := by unfold levEps; linarith
  have h0 : 0 < levDelta Δ R := by unfold levDelta; positivity
  have h2 : 2 * R * levDelta Δ R ≤ levEps Δ := by
    unfold levDelta
    rw [show 2 * (R : ℝ) * (levEps Δ / (2 * (R + 1))) = levEps Δ * (R / (R + 1)) by
      field_simp]
    have : (R : ℝ) / (R + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  have h1 : levDelta Δ R ≤ 1 := by
    unfold levDelta
    rw [div_le_one (by positivity)]
    nlinarith
  exact ⟨h0, h1, sparsify_factor_bounds h0.le (by linarith) h2⟩

theorem levBits_spec {Δ : ℝ} (hΔ0 : 0 < Δ) : (1 / 2 : ℝ) ^ levBits Δ ≤ Δ / 256 := by
  have h := div_two_pow_bits_le (c := 1) (by positivity : (0 : ℝ) < Δ / 256)
  rw [_root_.one_div_pow]; exact h

open Probability in
set_option maxHeartbeats 3200000 in
/-- **The Lewis loop's guarantee.** With `1/2 ≤ p < 2`, `0 < Δ ≤ 256`, positive copy-constant
inverse slacks `s = lpVec spt`, the public precisions `k_μ = levBits Δ` and the D4 accuracy
`levDelta Δ R` (leverage accuracy `ε_lev = Δ/1024`), the loop's output after `J_L` iterations
satisfies `‖y − y*‖_∞ ≤ (3/4)^{J_L}‖y₀ − y*‖_∞ + Δ/32` outside probability `J_L · F`, where `F`
is `sparsify_fail_le`'s bound with the residual count bounded by the number of pairs. Only the
`J_L` D4 calls made need to succeed. -/
theorem lewisLoop_fail_le (s t : Fin n) (hst : s ≠ t) {spt : LPPoint (Fin n)}
    (hs : ∀ i, 0 < lpVec G spt i) {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp2 : p < 2)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 256) (y0 : LPPoint (Fin n))
    {K : ℕ} (J : ℕ) {t' : ℕ} (R : ℕ) {Cs : ℝ} (hCs0 : 0 ≤ Cs)
    (hCs : ∀ e, (Spanner.symS G e : ℝ) ≤ Cs) (hK : n ≤ 2 ^ K) (ht' : 0 < t')
    {ystar : Fin (lpM G) → ℝ}
    (hfix : lewisMap p (diagonal (lpVec G spt) * lpA G s t) ystar = ystar) (JL : ℕ) :
    mass ((lewisLoop s t p (levBits Δ) spt y0 K J t' R JL).eval G.out)
        (fun o => ¬ ∃ y, o = some y ∧
          dist (lpVec G y) ystar ≤ (3 / 4) ^ JL * dist (lpVec G y0) ystar + Δ / 32) ≤
      JL * (R * (t' * (2⁻¹ : ℝ≥0∞) ^ J + ENNReal.ofReal (2 * n *
          Real.exp (-(levDelta Δ R ^ 2) / (8 * (Cs * (2 * K + 1 : ℕ) / t'))))) +
        (Fintype.card (Sym2 (Fin n)) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ R) := by
  set F : ℝ≥0∞ := R * (t' * (2⁻¹ : ℝ≥0∞) ^ J + ENNReal.ofReal (2 * n *
      Real.exp (-(levDelta Δ R ^ 2) / (8 * (Cs * (2 * K + 1 : ℕ) / t'))))) +
    (Fintype.card (Sym2 (Fin n)) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ R with hF
  set E := dist (lpVec G y0) ystar
  set Inv : ℕ → Option (LPPoint (Fin n)) → Prop := fun j o => ∃ y, o = some y ∧
    dist (lpVec G y) ystar ≤ (3 / 4) ^ j * E + Δ / 32 with hInv
  obtain ⟨hδ0, hδ1, hδlo, hδhi⟩ := levDelta_spec hΔ0 hΔ R
  have hμ := levBits_spec hΔ0
  have hε0 : 0 ≤ levEps Δ := by unfold levEps; positivity
  have hε : levEps Δ ≤ 1 / 4 := by unfold levEps; linarith
  -- one step preserves the invariant on D4 success
  have hstep : ∀ j (y : LPPoint (Fin n)), Inv j (some y) → ∀ out,
      Sparsify.Good G (lewisW (1 - 2 / p) spt y) K t' (levDelta Δ R) R out →
      Inv (j + 1) (some (lewisNewY s t p (levBits Δ) spt
        (lap out univ + lewisE s t (1 - 2 / p) spt y)⁻¹)) := by
    rintro j y ⟨y', hy', hd⟩ out hg
    cases hy'
    refine ⟨_, rfl, ?_⟩
    set B := diagonal (lpVec G spt) * lpA G s t
    have h1 := lewis_step_err G s t hst hs (by linarith : 0 < p) (levBits Δ) hg hε0 hε
      hδlo hδhi
    have hA := det_ne_zero_of_idRows (lpA_idRows G s t)
    have hB : (Bᵀ * B).det ≠ 0 := diag_det hA fun j => (hs j).ne'
    have hrowB : ∀ i, B i ≠ 0 := fun i h0 => by
      apply lpA_row_ne_zero G hst i
      funext j
      have := congrFun h0 j
      simp only [B, diagonal_mul, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left (hs i).ne'
    have h2 := lewisMap_dist_le hB hrowB (by linarith : 0 < p) hp2 (lpVec G y) ystar
    rw [hfix] at h2
    have hζ : p * (2 * levEps Δ) + (1 / 2) ^ levBits Δ ≤ Δ / 128 := by
      unfold levEps; nlinarith
    have hc : 1 - p / 2 ≤ 3 / 4 := by linarith
    have hE0 : 0 ≤ E := dist_nonneg
    have hd0 : 0 ≤ dist (lpVec G y) ystar := dist_nonneg
    calc _ ≤ dist (lpVec G (lewisNewY s t p (levBits Δ) spt
            (lap out univ + lewisE s t (1 - 2 / p) spt y)⁻¹)) (lewisMap p B (lpVec G y)) +
          dist (lewisMap p B (lpVec G y)) ystar := dist_triangle _ _ _
      _ ≤ Δ / 128 + 3 / 4 * dist (lpVec G y) ystar := by
          refine add_le_add (h1.trans hζ) (h2.trans ?_)
          exact mul_le_mul_of_nonneg_right hc hd0
      _ ≤ Δ / 128 + 3 / 4 * ((3 / 4) ^ j * E + Δ / 32) := by gcongr
      _ = (3 / 4) ^ (j + 1) * E + Δ / 32 := by ring
  -- induction over the iterations
  have hmain : ∀ j, mass ((lewisLoop s t p (levBits Δ) spt y0 K J t' R j).eval G.out)
      (fun o => ¬ Inv j o) ≤ j * F := by
    intro j
    induction j with
    | zero =>
        simp only [lewisLoop, RTree.eval_pure, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero]
        rw [mass_eq_tsum]
        refine ENNReal.tsum_eq_zero.mpr fun o => ?_
        by_cases ho : o = some y0
        · subst ho
          have : Inv 0 (some y0) := ⟨y0, rfl, by
            simp only [pow_zero, one_mul, E]; linarith⟩
          simp [this]
        · simp [PMF.pure_apply, ho]
    | succ j ih =>
        simp only [lewisLoop, RTree.eval_cast, RTree.eval_bind]
        refine (mass_bind_le_add _ _ (fun o => ¬ Inv j o) _ (ε := F) ih fun o ho => ?_).trans
          (le_of_eq (by push_cast; ring))
        push Not at ho
        obtain ⟨y, rfl, hy⟩ := ho
        simp only [lewisStepProg, RTree.eval_bind]
        refine (mass_bind_le_add _ _
          (fun o => ¬ ∃ out, o = some out ∧
            Sparsify.Good G (lewisW (1 - 2 / p) spt y) K t' (levDelta Δ R) R out) _
          (ε := 0) ?_ ?_).trans (by rw [add_zero])
        · refine (Sparsify.sparsify_fail_le hCs0 hCs (fun e => by unfold lewisW; positivity)
            hK ht' hδ0 hδ1 R).trans ?_
          refine add_le_add_right (mul_le_mul_left ?_ _) _
          exact_mod_cast Finset.card_le_univ _
        · intro o ho
          push Not at ho
          obtain ⟨out, rfl, hg⟩ := ho
          have := hstep j y ⟨y, rfl, hy⟩ out hg
          simp [RTree.eval_pure, this]
  refine (le_of_eq_of_le ?_ (hmain JL))
  rfl

end

end ImplicitLP
end CutQueryComplexity
