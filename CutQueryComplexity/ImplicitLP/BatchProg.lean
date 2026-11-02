import CutQueryComplexity.ImplicitLP.BatchPub
import CutQueryComplexity.ImplicitLP.LewisStage

set_option autoImplicit false

/-! # One public batch program (D7 → D8, step 3)

`batchProg` composes, on public LP points `κ, m, c, x, X`:
1. D4 + the public Newton step (`newtonProgPub`) on the copy-constant targets
   `D = 1/(e^X S(x)²)`, `q = tc + e^X φ'(x)` (`normDPt`, `normQPt`), giving `d`;
2. the public point `x' = x + d` (`addPt`);
3. the Lewis stage at `x'` (`lewisLoop` restarted at `zeroPt` with `J_L = lewisJL`);
4. the observation `z = log(e^y + c₀)` (`obsPt`);
5. the public support program at `q = ∇Φ(X − z)`, `w = e^X` (`batchSupProg`), giving `v`;
6. `X' = X − (1 + ξ)v` (`chasePt`).
It returns `some (x', X')`, or `none` if a Lewis D4 call aborts.

* `batchProg_cost`: every execution uses at most
  `Q_Newton + J_L·q_{D4,lev} + Q_support` queries.
* `batchProg_fail`: under the batch invariants at `(x, X)`, the output fails `BatchGood`
  (feasibility, the potential bound, `eq:capmargin`) with probability at most
  `ζ_Newton + J_L·ζ_lev`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

open DirectedMincut (LPPoint)
open scoped ENNReal

variable {n : ℕ}

/-! ## Public points of the batch -/

/-- `S(x) = κ/cos(κ(x − m))` as a public point. -/
def barSPt (κp mp xp : LPPoint (Fin n)) : LPPoint (Fin n) :=
  lpMap3 (fun k mm xx => k / Real.cos (k * (xx - mm))) κp mp xp

/-- `φ'(x) = κ tan(κ(x − m))` as a public point. -/
def barDphiPt (κp mp xp : LPPoint (Fin n)) : LPPoint (Fin n) :=
  lpMap3 (fun k mm xx => k * Real.tan (k * (xx - mm))) κp mp xp

/-- The Newton weights `D = 1/(e^X S²)` as a public point. -/
def normDPt (κp mp xp Xp : LPPoint (Fin n)) : LPPoint (Fin n) :=
  map2Pt (fun X S => 1 / (Real.exp X * S ^ 2)) Xp (barSPt κp mp xp)

/-- The Newton target `q = tc + e^X φ'` as a public point. -/
def normQPt (t : ℝ) (κp mp cp xp Xp : LPPoint (Fin n)) : LPPoint (Fin n) :=
  lpMap3 (fun c X d => t * c + Real.exp X * d) cp Xp (barDphiPt κp mp xp)

/-- The sum of two public points. -/
def addPt (p₁ p₂ : LPPoint (Fin n)) : LPPoint (Fin n) := map2Pt (· + ·) p₁ p₂

/-- The observation `z = log(e^y + c₀)` as a public point. -/
def obsPt (c₀ : ℝ) (y : LPPoint (Fin n)) : LPPoint (Fin n) :=
  mapPt (fun u => Real.log (Real.exp u + c₀)) y

/-- The chase update `X − (1 + ξ)v` as a public point. -/
def chasePt (ξ : ℝ) (Xp vp : LPPoint (Fin n)) : LPPoint (Fin n) :=
  map2Pt (fun a b => a - (1 + ξ) * b) Xp vp

section

variable (G : DiGraph (Fin n))

theorem lpVec_eq_lpD (P : LPPoint (Fin n)) :
    lpVec G P = lpD G (pairOf P.z) P.q P.yp P.ym := by
  funext i
  simp only [lpVec, lpD]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j))
  · simp only [lpVal, lpWeight]; rw [pairOf_mk_lt _ p.2]
  all_goals rfl

theorem lpVec_barSPt (κp mp xp : LPPoint (Fin n)) :
    lpVec G (barSPt κp mp xp) = barS (lpVec G κp) (lpVec G mp) (lpVec G xp) := by
  funext i; rw [barSPt, lpVec_lpMap3]; rfl

theorem lpVec_barDphiPt (κp mp xp : LPPoint (Fin n)) :
    lpVec G (barDphiPt κp mp xp) = barDphi (lpVec G κp) (lpVec G mp) (lpVec G xp) := by
  funext i; rw [barDphiPt, lpVec_lpMap3]; rfl

theorem lpVec_normDPt (κp mp xp Xp : LPPoint (Fin n)) :
    lpVec G (normDPt κp mp xp Xp) =
      normD (fun i => Real.exp (lpVec G Xp i)) (barS (lpVec G κp) (lpVec G mp) (lpVec G xp)) := by
  funext i; rw [normDPt, lpVec_map2Pt, lpVec_barSPt]; rfl

theorem lpVec_normQPt (t : ℝ) (κp mp cp xp Xp : LPPoint (Fin n)) :
    lpVec G (normQPt t κp mp cp xp Xp) =
      normQ t (lpVec G cp) (fun i => Real.exp (lpVec G Xp i))
        (barDphi (lpVec G κp) (lpVec G mp) (lpVec G xp)) := by
  funext i; rw [normQPt, lpVec_lpMap3, lpVec_barDphiPt]; rfl

theorem lpVec_addPt (p₁ p₂ : LPPoint (Fin n)) :
    lpVec G (addPt p₁ p₂) = lpVec G p₁ + lpVec G p₂ := by
  funext i; rw [addPt, lpVec_map2Pt]; rfl

theorem lpVec_obsPt (c₀ : ℝ) (y : LPPoint (Fin n)) :
    lpVec G (obsPt c₀ y) = fun i => Real.log (Real.exp (lpVec G y i) + c₀) := by
  funext i; rw [obsPt, lpVec_mapPt]

theorem lpVec_chasePt (ξ : ℝ) (Xp vp : LPPoint (Fin n)) :
    lpVec G (chasePt ξ Xp vp) = lpVec G Xp - (1 + ξ) • lpVec G vp := by
  funext i; rw [chasePt, lpVec_map2Pt]; simp [smul_eq_mul]

end

/-! ## The exact Newton direction in `newtonStep_public`'s form -/

theorem newtonPot_gram {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} (hA : (Aᵀ * A).det ≠ 0)
    {w S q : Fin M → ℝ} (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) :
    gram A (normD w S) *ᵥ newtonPot A w S q = Aᵀ *ᵥ fun i => normD w S i * q i := by
  have hd : ∀ i, 0 < 1 / (w i * S i ^ 2) := fun i => by
    have := hw i; have := hS i; positivity
  have hG := gram_det_ne hA hd
  have e1 : (fun i => normD w S i * q i) = fun i => q i / (w i * S i ^ 2) := by
    funext i; simp only [normD]; ring
  rw [e1]
  show gram A (fun i => 1 / (w i * S i ^ 2)) *ᵥ ((gram A (fun i => 1 / (w i * S i ^ 2)))⁻¹ *ᵥ
    (Aᵀ *ᵥ fun i => q i / (w i * S i ^ 2))) = _
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), one_mulVec]

theorem newtonDir_eq_normD {M r : ℕ} (A : Matrix (Fin M) (Fin r) ℝ) (w S q : Fin M → ℝ) :
    (fun i => -normD w S i * (q i - (A *ᵥ newtonPot A w S q) i)) = newtonDir A w S q := by
  funext i; simp only [normD, newtonDir]; ring

/-! ## The program -/

/-- The public support envelopes of a batch (`batch_support_public`'s `envSup`). -/
def batchSup (Mbar L₀ c₀ Δ T₀ : ℝ) : SupPub :=
  envSup Mbar (2 * (1 / (2 * L₀) / 8 / (12 * Δ)) * (12 * Mbar * T₀ / (1 / (2 * L₀) / 8)))
    (4 / 5 * c₀) (48 * (2 * L₀)) ((1 - 3 * (1 / (2 * L₀)) / 4) * Δ) (1 / (2 * L₀) / 8 / 1000)

/-- The public support program of a batch (`batch_support_public`'s `prog`). -/
def batchSupProg (Mbar L₀ c₀ Δ T₀ : ℝ) (Xp zp : LPPoint (Fin n)) :=
  supportPubProg (48 * (2 * L₀)) ((1 - 3 * (1 / (2 * L₀)) / 4) * Δ)
    (batchSup Mbar L₀ c₀ Δ T₀).ρ
    (clipQPt (2 * (1 / (2 * L₀) / 8 / (12 * Δ)) * (12 * Mbar * T₀ / (1 / (2 * L₀) / 8)))
      (gradPt (1 / (2 * L₀) / 8 / (12 * Δ)) Xp zp))
    (clipWPt (4 / 5 * c₀) (wPt Xp)) (batchSup Mbar L₀ c₀ Δ T₀).Mbar
    (batchSup Mbar L₀ c₀ Δ T₀).Ap (batchSup Mbar L₀ c₀ Δ T₀).h (batchSup Mbar L₀ c₀ Δ T₀).p
    (batchSup Mbar L₀ c₀ Δ T₀).B (batchSup Mbar L₀ c₀ Δ T₀).m (batchSup Mbar L₀ c₀ Δ T₀).N
    (batchSup Mbar L₀ c₀ Δ T₀).kτ (batchSup Mbar L₀ c₀ Δ T₀).kl (batchSup Mbar L₀ c₀ Δ T₀).kc
    (batchSup Mbar L₀ c₀ Δ T₀).po

/-- The public Lewis cap of a batch. -/
def batchJL (E : NewtonPub) (Δ : ℝ) : ℕ := lewisJL Δ (lewisE0 E.Mbar E.U E.sst)

/-- **One public batch program.** Newton (D4 + public step) → `x' = x + d` → Lewis stage at
`x'` → observation `z` → public support → `X' = X − (1 + ξ)v`. Output `some (x', X')`, or
`none` if a Lewis D4 call aborts. Every input is a public LP point or a public scalar. -/
def batchProg (E : NewtonPub) (s t₀ : Fin E.n) (κp mp cp xp Xp : LPPoint (Fin E.n))
    (t L₀ c₀ Δ T₀ : ℝ) (K J t' R : ℕ) :=
  (newtonProgPub E s t₀ (pairOf (normDPt κp mp xp Xp).z) (normDPt κp mp xp Xp).q
      (normDPt κp mp xp Xp).yp (normDPt κp mp xp Xp).ym (normQPt t κp mp cp xp Xp)
      K J t' R).bind fun d =>
    (lewisLoop s t₀ (1 - 1 / L₀) (levBits Δ) (invSlackPt κp mp (addPt xp d)) zeroPt K J t' R
        (batchJL E Δ)).bind fun o =>
      match o with
      | none => RTree.pure (PMF.pure none)
      | some y => RTree.ofDeterministic ((batchSupProg E.Mbar L₀ c₀ Δ T₀ Xp (obsPt c₀ y)).map
          fun out => some (addPt xp d, chasePt (1 / (2 * L₀) / 8) Xp out.2))

variable {E : NewtonPub} (G : DiGraph (Fin E.n))

/-- **Budget on every execution:**
`Q_Newton + J_L · q_{D4,lev} + Q_support` with `Q_Newton = q_D4 + 6n(B_rhs + k·B_mv + B_rep)`,
`q_{D4,lev} = q_D4 = R · levelBudget + 3n`, `Q_support = (2N + 2)(m + 3)·6Bn`. -/
theorem batchProg_cost (s t₀ : Fin E.n) (κp mp cp xp Xp : LPPoint (Fin E.n))
    (t L₀ c₀ Δ T₀ : ℝ) (K J t' R : ℕ) {o : Option (LPPoint (Fin E.n) × LPPoint (Fin E.n)) × ℕ}
    (ho : o ∈ (RTree.run G.out (batchProg E s t₀ κp mp cp xp Xp t L₀ c₀ Δ T₀ K J t' R)).support) :
    o.2 ≤ ((R * Sparsify.levelBudget (n := E.n) K J t' + 3 * E.n) +
        6 * E.n * (E.Brhs + E.k * E.Bmv + E.Brep)) +
      batchJL E Δ * (R * Sparsify.levelBudget (n := E.n) K J t' + 3 * E.n) +
      (2 * (batchSup E.Mbar L₀ c₀ Δ T₀).N + 2) *
        (((batchSup E.Mbar L₀ c₀ Δ T₀).m + 3) * (6 * (batchSup E.Mbar L₀ c₀ Δ T₀).B * E.n)) :=
  (RTree.cost_le _ _ ho).trans (le_of_eq (by ring))

/-- **The batch invariant at the output**: `some (x', X')` with `x'` strictly feasible, the
potential bound `Φ(X' − log g(x')) ≤ B₀`, and `eq:capmargin` `δ_t(x', e^{X'}) ≤ (1 − 1/(2k))Δ`.
The new state is public by construction (a pair of LP points). -/
def BatchGood (s t₀ : Fin E.n) (bc : Fin E.n → ℝ) (κ m c : Fin (lpM G) → ℝ) (t L₀ c₀ Δ T₀ : ℝ)
    (o : Option (LPPoint (Fin E.n) × LPPoint (Fin E.n))) : Prop :=
  ∃ xn Xn, o = some (xn, Xn) ∧ lpVec G xn ∈ Feasible (lpA G s t₀) bc κ m ∧
    pot ((1 / (2 * L₀) / 8) / (12 * Δ)) (lpVec G Xn - fun i =>
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (lpA G s t₀) (lpVec G xn) i)) ≤
        12 * lpM G * T₀ / (1 / (2 * L₀) / 8) ∧
    cent (48 * (2 * L₀)) (lpA G s t₀) (barS κ m (lpVec G xn)) (barDphi κ m (lpVec G xn)) c t
      (fun i => exp (lpVec G Xn i)) ≤ (1 - 1 / (2 * L₀) / 2) * Δ

/-- The per-call D4 failure bound at accuracy `δ`, with the residual count bounded by the
number of pairs (public). -/
def d4Fail (n : ℕ) (Csym : ℝ) (K J t' R : ℕ) (δ : ℝ) : ℝ≥0∞ :=
  R * (t' * (2⁻¹ : ℝ≥0∞) ^ J + ENNReal.ofReal (2 * n *
      Real.exp (-(δ ^ 2) / (8 * (Csym * (2 * K + 1 : ℕ) / t'))))) +
    (Fintype.card (Sym2 (Fin n)) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ R

open Probability in
set_option maxHeartbeats 6400000 in
/-- **One public batch preserves the full invariant.** Suppose the batch invariants hold at the
public state `(x, X) = (lpVec xp, lpVec Xp)` (with `κ, m, c` public): `x` strictly feasible,
`δ_t(x, e^X) ≤ Δ`, `Φ(X − log g(x)) ≤ B₀`, the D7 parameter regime (`k = 2L₀`, `C_N = 48k`,
`Δ ≤ (2¹⁶k²)⁻¹`, `K ≤ (2²⁰k)⁻¹`, `η ≤ Δ/(2¹⁶k)`, `N_w ≤ T₀‖·‖_∞`), the public envelope
`M ≤ M̄`, `c₀ = 1/(2M̄)`, and the path-following regime of `newtonStep_public`. Then the
output of `batchProg` fails `BatchGood` with probability at most `ζ_Newton + J_L·ζ_lev`, where
`ζ_Newton = d4Fail … (solveDelta R)` and `ζ_lev = d4Fail … (levDelta Δ R)`. -/
theorem batchProg_fail (s t₀ : Fin E.n) (hst : s ≠ t₀) {bc : Fin E.n → ℝ}
    {κp mp cp xp Xp : LPPoint (Fin E.n)} {κ m c x X : Fin (lpM G) → ℝ}
    (hκp : lpVec G κp = κ) (hmp : lpVec G mp = m) (hcp : lpVec G cp = c)
    (hxp : lpVec G xp = x) (hXp : lpVec G Xp = X)
    {t L₀ c₀ Δ K T₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * E.Mbar) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) (hc₀lo : 1 / (2 * E.Mbar) ≤ c₀) (hc₀hi : c₀ ≤ 1 / (2 * E.Mbar))
    (hU1 : 1 ≤ E.U) (hU : ∀ i, π / κ i ≤ E.U) {x₀ : Fin (lpM G) → ℝ}
    (hx : x ∈ Feasible (lpA G s t₀) bc κ m) (hx₀ : x₀ ∈ Feasible (lpA G s t₀) bc κ m)
    (hs0 : ∀ i, 1 / E.U ≤ slk κ m x₀ i)
    (hMbar : (lpM G : ℝ) ≤ E.Mbar) (hr : (1 : ℝ) ≤ E.n) (hε : 0 < E.ε) (hε1 : E.ε ≤ 1)
    (ht : |t| ≤ 16 * E.n / E.ε) (hc : ‖c‖ ≤ 4 * E.U)
    (hEC : E.C = 48 * (2 * L₀)) (hη0 : 0 < E.η) (hη : E.η ≤ 1 / (2 * L₀) * Δ / 2 ^ 16)
    (hΔ0 : 0 < Δ) (hΔ : Δ ≤ (1 / (2 * L₀)) ^ 2 / 2 ^ 16)
    (hK0 : 0 ≤ K) (hK : K ≤ 1 / (2 * L₀) / 2 ^ 20) (hT₀ : 1 ≤ T₀)
    (hT : ∀ v, mixed (48 * (2 * L₀)) (fun i => exp (X i)) v ≤ T₀ * ‖v‖)
    (hKμ : Real.log (12 * E.Mbar * T₀ / (1 / (2 * L₀) / 8)) /
      ((1 / (2 * L₀) / 8) / (12 * Δ)) ≤ K)
    (hpot : pot ((1 / (2 * L₀) / 8) / (12 * Δ))
      (X - fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ (lpA G s t₀) x i)) ≤
        12 * lpM G * T₀ / (1 / (2 * L₀) / 8))
    (hδ : cent (48 * (2 * L₀)) (lpA G s t₀) (barS κ m x) (barDphi κ m x) c t
      (fun i => exp (X i)) ≤ Δ)
    {Kd J t' R : ℕ} {Csym : ℝ} (hCsym0 : 0 ≤ Csym) (hCsym : ∀ e, (Spanner.symS G e : ℝ) ≤ Csym)
    (hKd : E.n ≤ 2 ^ Kd) (ht' : 0 < t') :
    mass ((batchProg E s t₀ κp mp cp xp Xp t L₀ c₀ Δ T₀ Kd J t' R).eval G.out)
        (fun o => ¬ BatchGood G s t₀ bc κ m c t L₀ c₀ Δ T₀ o) ≤
      d4Fail E.n Csym Kd J t' R (solveDelta R) +
        batchJL E Δ * d4Fail E.n Csym Kd J t' R (levDelta Δ R) := by
  -- constants
  set A := lpA G s t₀ with hAdef
  set a : ℝ := 1 / (2 * L₀) with ha_def
  set ξ : ℝ := a / 8 with hξ_def
  set μ : ℝ := ξ / (12 * Δ) with hμ_def
  set g := gfun κ m (1 - 1 / L₀) c₀ A with hg_def
  set w : Fin (lpM G) → ℝ := fun i => exp (X i) with hw_def
  have hL0 : 0 < L₀ := by linarith
  have ha0 : 0 < a := by positivity
  have ha4 : a ≤ 1 / 4 := by
    simp only [a]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hξ0 : 0 < ξ := by positivity
  have hμ0 : 0 < μ := by positivity
  have hΔs : Δ ≤ 1 / 2 ^ 20 := by nlinarith
  have hηs : E.η ≤ Δ := by nlinarith
  have hKs : K ≤ 1 / 2 ^ 22 := by nlinarith
  have hwpos : ∀ i, 0 < w i := fun i => exp_pos _
  have hA : (Aᵀ * A).det ≠ 0 := det_ne_zero_of_idRows (lpA_idRows G s t₀)
  have hrow : ∀ i, A i ≠ 0 := lpA_row_ne_zero G hst
  have hn0 : 0 < E.n := Fin.pos s
  have hMnat : 1 ≤ lpM G := Fin.pos (lpIota G ⟨0, hn0⟩)
  have hM1 : (1 : ℝ) ≤ lpM G := by exact_mod_cast hMnat
  have hMb1 : 1 ≤ E.Mbar := hM1.trans hMbar
  -- hidden-row parameters from the public envelope `M ≤ M̄`
  have hLMh : Real.logb 2 (2 * lpM G) ≤ L₀ - 1 :=
    (Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)).trans hLM
  have hcM : c₀ ≤ 1 / (2 * lpM G) :=
    hc₀hi.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hc₀pos : 0 < c₀ := lt_of_lt_of_le (by positivity) hc₀lo
  have hKμh : Real.log (12 * lpM G * T₀ / ξ) / μ ≤ K := by
    refine le_trans (div_le_div_of_nonneg_right (Real.log_le_log (by positivity) ?_) hμ0.le) hKμ
    gcongr
  -- the weight comparison and the windows at `x`
  have hXg : ∀ i, |X i - Real.log (g x i)| ≤ K := fun i => by
    have := pot_coord_bound hμ0 hpot i
    simp only [Pi.sub_apply] at this
    exact this.trans hKμh
  have hwin : ∀ i, |Real.log (w i) - Real.log (g x i)| ≤ 1 / 20 := fun i => by
    simp only [w, Real.log_exp]; exact (hXg i).trans (by linarith)
  have hwin5 : ∀ i, |Real.log (w i) - Real.log (g x i)| ≤ 1 / 5 := fun i =>
    (hwin i).trans (by norm_num)
  have hδc : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000 :=
    hδ.trans (by linarith)
  obtain ⟨hwlo, -, hwsum⟩ := weight_invariants hA hrow hL hc₀lo hcM hMbar hr hwpos hwin5
  -- the exact Newton direction and the copy-constant targets
  have hS0 := barS_pos hκ hx.2
  set q : Fin (lpM G) → ℝ := fun i => t * c i + exp (X i) * barDphi κ m x i with hq_def
  set h := newtonDir A w (barS κ m x) q with hh_def
  have hqN : normQ t c w (barDphi κ m x) = q := rfl
  have hDcopy : normD w (barS κ m x) =
      lpD G (pairOf (normDPt κp mp xp Xp).z) (normDPt κp mp xp Xp).q
        (normDPt κp mp xp Xp).yp (normDPt κp mp xp Xp).ym := by
    rw [← lpVec_eq_lpD, lpVec_normDPt, hκp, hmp, hxp, hXp]
  have hqcopy : normQ t c w (barDphi κ m x) = lpVec G (normQPt t κp mp cp xp Xp) := by
    rw [lpVec_normQPt, hκp, hmp, hcp, hxp, hXp]
  have hp := newtonPot_gram (q := normQ t c w (barDphi κ m x)) hA hwpos hS0
  have hC0 : 0 ≤ E.C := by rw [hEC]; positivity
  have hNew := newtonProgPub_numeric G s t₀ hst hL hLMh hκ hc₀lo hcM hU1 hU hx hx₀ hMbar hr hε
    hε1 hwpos ht hc hwin hδc hs0 hC0 hη0 hDcopy hqcopy hp (J := J) R hCsym0 hCsym hKd ht'
  have hcard : ((Sparsify.resid G (Sparsify.P0 (E.wf (pairOf (normDPt κp mp xp Xp).z)))).card :
      ℝ≥0∞) ≤ (Fintype.card (Sym2 (Fin E.n)) : ℝ≥0∞) := by
    exact_mod_cast Finset.card_le_univ _
  have hNew' := hNew.trans (add_le_add le_rfl (mul_le_mul' hcard le_rfl))
  rw [newtonDir_eq_normD] at hNew'
  -- the composition
  unfold batchProg
  rw [RTree.eval_bind]
  refine (mass_bind_le_add _ _ _ _ (ε := batchJL E Δ * d4Fail E.n Csym Kd J t' R (levDelta Δ R))
    hNew' ?_).trans le_rfl
  intro d hd
  rw [not_not] at hd
  obtain ⟨hAd, hed⟩ := hd
  -- the Newton error `e = d − h`
  set e : Fin (lpM G) → ℝ := lpVec G d - h with he_def
  have hAe : Aᵀ *ᵥ e = 0 := by
    rw [he_def, mulVec_sub, hAd, (newtonDir_spec hA hwpos hS0).1, sub_zero]
  have he : mixed (48 * (2 * L₀)) w (fun i => barS κ m x i * e i) ≤ E.η := by
    rw [← hEC]; exact hed
  -- the primal half
  obtain ⟨hx'F, hcent', hmove⟩ :=
    batch_primal hA hrow hL hLMh hκ hc₀pos.le hcM hx hΔ0 hΔ hK0 hK hη0.le hη hXg hδ hAe he
  set x' : Fin (lpM G) → ℝ := x + lpVec G d with hx'_def
  have hx'eq : x + (h + e) = x' := by
    rw [he_def, hx'_def]; abel
  have hxp' : lpVec G (addPt xp d) = x' := by rw [lpVec_addPt, hxp]
  rw [hx'eq] at hx'F hcent' hmove
  -- the windows at `x'`
  have hC : (0 : ℝ) < 48 * (2 * L₀) := by positivity
  have hu : ∀ i, |Real.log (g x' i) - Real.log (g x i)| ≤ Δ := fun i => by
    have h1 : |Real.log (g x' i) - Real.log (g x i)| ≤
        mixed (48 * (2 * L₀)) w (fun i => Real.log (g x' i) - Real.log (g x i)) := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (fun i => Real.log (g x' i) - Real.log (g x i)) i).trans
        (norm_le_mixed hC.le _)
    refine h1.trans (hmove.trans ?_)
    nlinarith
  have hwin' : ∀ i, |Real.log (w i) - Real.log (g x' i)| ≤ 1 / 20 := fun i => by
    simp only [w, Real.log_exp]
    have h1 := hXg i
    have h2 := hu i
    calc |X i - Real.log (g x' i)| ≤
          |X i - Real.log (g x i)| + |Real.log (g x' i) - Real.log (g x i)| := by
          have : X i - Real.log (g x' i) =
              (X i - Real.log (g x i)) - (Real.log (g x' i) - Real.log (g x i)) := by ring
          rw [this]; exact abs_sub _ _
      _ ≤ 1 / 20 := by linarith
  have hδ' : cent (48 * (2 * L₀)) A (barS κ m x') (barDphi κ m x') c t w ≤ 1 / 1000 :=
    hcent'.trans (by nlinarith)
  -- the slack floor at `x'`
  have hs' : ∀ i, E.sst ≤ slk κ m x' i := fun i =>
    slack_floor_note hA hrow hL hLMh hκ hc₀pos.le hcM hU1 hU hx'F hx₀ hMbar hr hε hε1 hwlo
      hwsum ht hc hwin' hδ' hs0 i
  have hU0 : 0 < E.U := by linarith
  have hsst0 : 0 < E.sst := by unfold NewtonPub.sst; positivity
  -- the Lewis stage at `x'`
  have hspt : lpVec G (invSlackPt κp mp (addPt xp d)) = fun i => exp (sfun κ m x' i) :=
    lpVec_invSlackPt G hκ hx'F.2 hκp hmp hxp'
  obtain ⟨hp0, hp2⟩ := lewisExp_bounds hL
  obtain ⟨-, hLew⟩ := lewisStage G hst hκ hx'F.2 hU1 hU hsst0 hs' hMbar hspt hp0 hp2
    hc₀pos.le hΔ0 (by linarith) J R hCsym0 hCsym hKd ht'
  rw [RTree.eval_bind]
  refine (mass_bind_le_add _ _ _ _ (ε := 0) hLew ?_).trans (le_of_eq (add_zero _))
  intro o ho
  rw [not_not] at ho
  obtain ⟨y, rfl, -, hy⟩ := ho
  -- the support step and `prop_batch`
  set st : PathState E.n := ⟨xp, Xp, obsPt c₀ y⟩
  set z : Fin (lpM G) → ℝ := fun i => Real.log (Real.exp (lpVec G y i) + c₀) with hz_def
  have hzst : lpVec G st.z = z := lpVec_obsPt G c₀ y
  have hz : ∀ i, |z i - Real.log (gfun κ m (1 - 1 / L₀) c₀ A
      (x + (newtonDir A (fun i => exp (X i)) (barS κ m x)
        (fun i => t * c i + exp (X i) * barDphi κ m x i) + e)) i)| ≤ Δ := fun i => by
    have : x + (newtonDir A (fun i => exp (X i)) (barS κ m x)
        (fun i => t * c i + exp (X i) * barDphi κ m x i) + e) = x' := hx'eq
    rw [this]
    exact (hy i).trans (by linarith)
  have hb := batch_support_public G st hXp hzst hA hrow hL hLMh hκ hc₀pos hcM hMnat hx hΔ0 hΔ
    hK0 hK hη0.le hη hT₀ hT hKμh hpot hδ hAe he hz hMbar
  obtain ⟨-, -, hF, hP, hCent⟩ := hb
  set out := (batchSupProg E.Mbar L₀ c₀ Δ T₀ Xp (obsPt c₀ y)).eval G.out with hout
  have hgood : BatchGood G s t₀ bc κ m c t L₀ c₀ Δ T₀
      (some (addPt xp d, chasePt (1 / (2 * L₀) / 8) Xp out.2)) := by
    refine ⟨_, _, rfl, ?_⟩
    rw [hxp', lpVec_chasePt, hXp, ← hx'eq]
    exact ⟨hF, hP, hCent⟩
  simp only [RTree.eval_ofDeterministic, DTree.eval_map, mass_pure]
  split_ifs with hbad
  · exact le_rfl
  · exact absurd hgood hbad


/-- **The path-parameter move after a batch** (`batch_tchange`): on a `BatchGood` output, a move
`|t'/t − 1| ≤ α` with `αT₁ ≤ Δ/(16k)` and `αΔ ≤ Δ/(16k)` restores `δ_{t'}(x', e^{X'}) ≤ Δ`, where
`N_{e^{X'}} ≤ T₁‖·‖_∞`. Feasibility and the potential bound do not depend on `t`. -/
theorem batchGood_tchange (s t₀ : Fin E.n) {bc : Fin E.n → ℝ} {κ m c : Fin (lpM G) → ℝ}
    {t L₀ c₀ Δ T₀ : ℝ} (hκ : ∀ i, 0 < κ i) (hL : 2 ≤ L₀) {xn Xn : LPPoint (Fin E.n)}
    (hgood : BatchGood G s t₀ bc κ m c t L₀ c₀ Δ T₀ (some (xn, Xn))) {T₁ α t' : ℝ}
    (hT10 : 0 ≤ T₁)
    (hT1 : ∀ v, mixed (48 * (2 * L₀)) (fun i => exp (lpVec G Xn i)) v ≤ T₁ * ‖v‖)
    (ht : 0 < t) (hα : |t' / t - 1| ≤ α) (hαT : α * T₁ ≤ 1 / (2 * L₀) * Δ / 16)
    (hΔ0 : 0 < Δ) (hαΔ : α * Δ ≤ 1 / (2 * L₀) * Δ / 16) :
    cent (48 * (2 * L₀)) (lpA G s t₀) (barS κ m (lpVec G xn)) (barDphi κ m (lpVec G xn)) c t'
      (fun i => exp (lpVec G Xn i)) ≤ Δ := by
  obtain ⟨xn', Xn', heq, hF, -, hcap⟩ := hgood
  cases heq
  have hL0 : 0 < L₀ := by linarith
  exact batch_tchange (by positivity) hκ hF.2 (fun i => exp_pos _) hT10 hT1 ht hα
    (by positivity) hαT hcap hΔ0 hαΔ

end

end ImplicitLP
end CutQueryComplexity
