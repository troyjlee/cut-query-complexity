import CutQueryComplexity.ImplicitLP.GenericQuery.Newton
import CutQueryComplexity.ImplicitLP.GenericQuery.Stage
import CutQueryComplexity.ImplicitLP.GenericQuery.BatchSupport

/-! # Executed general Newton–Lewis–support batch

Every transition is an actual query program on public point formulas. The
numerical, spectral, restart and support theorems discharge its component
hypotheses; the analytic batch theorem then proves the new invariant.
-/

set_option autoImplicit false
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Real Set
open scoped ENNReal
noncomputable section
variable {n me : ℕ}

def batchSupProg (Mbar L₀ c₀ Δ T₀ : ℝ) (Xp zp : Point n me) :=
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
def batchJL (E : NewtonPub) (a0 Δ : ℝ) : ℕ := lewisJL Δ (restartLog a0 E.Mbar E.U E.sst)

/-- **One public batch program.** Newton (D4 + public step) → `x' = x + d` → Lewis stage at
`x'` → observation `z` → public support → `X' = X − (1 + ξ)v`. Output `some (x', X')`, or
`none` if a Lewis D4 call aborts. Every input is a public LP point or a public scalar. -/
def batchProg (E : NewtonPub) (ER : ExplicitRows E.n me) (a0 : ℝ) (κp mp cp xp Xp : Point E.n me)
    (t L₀ c₀ Δ T₀ : ℝ) (K J t' R : ℕ) :=
  (newtonProgPub E ER (pairOf (normDPt κp mp xp Xp).pair)
      (normDPt κp mp xp Xp).explicit (normQPt t κp mp cp xp Xp)
      K J t' R).bind fun d =>
    (lewisLoop ER (1 - 1 / L₀) (levBits Δ) (invSlackPt κp mp (addPt xp d)) zeroPt K J t' R
        (batchJL E a0 Δ)).bind fun o =>
      match o with
      | none => RTree.pure (PMF.pure none)
      | some y => RTree.ofDeterministic ((batchSupProg E.Mbar L₀ c₀ Δ T₀ Xp (obsPt c₀ y)).map
          fun out => some (addPt xp d, chasePt (1 / (2 * L₀) / 8) Xp out.2))

variable {E : NewtonPub} (G : DiGraph (Fin E.n))

/-- **Budget on every execution:**
`Q_Newton + J_L · q_{D4,lev} + Q_support` with `Q_Newton = q_D4 + 6n(B_rhs + k·B_mv + B_rep)`,
`q_{D4,lev} = q_D4 = R · levelBudget + 3n`, `Q_support = (2N + 2)(m + 3)·6Bn`. -/
theorem batchProg_cost (ER : ExplicitRows E.n me) (a0 : ℝ) (κp mp cp xp Xp : Point E.n me)
    (t L₀ c₀ Δ T₀ : ℝ) (K J t' R : ℕ) (read : Finset (Fin E.n) → ℕ)
    {o : Option (Point E.n me × Point E.n me) × ℕ}
    (ho : o ∈ (RTree.run read (batchProg E ER a0 κp mp cp xp Xp t L₀ c₀ Δ T₀ K J t' R)).support) :
    o.2 ≤ ((R * Sparsify.levelBudget (n := E.n) K J t' + 3 * E.n) +
        6 * E.n * (E.Brhs + E.k * E.Bmv + E.Brep)) +
      batchJL E a0 Δ * (R * Sparsify.levelBudget (n := E.n) K J t' + 3 * E.n) +
      (2 * (batchSup E.Mbar L₀ c₀ Δ T₀).N + 2) *
        (((batchSup E.Mbar L₀ c₀ Δ T₀).m + 3) * (6 * (batchSup E.Mbar L₀ c₀ Δ T₀).B * E.n)) :=
  (RTree.cost_le _ _ ho).trans (le_of_eq (by ring))

/-- **The batch invariant at the output**: `some (x', X')` with `x'` strictly feasible, the
potential bound `Φ(X' − log g(x')) ≤ B₀`, and `eq:capmargin` `δ_t(x', e^{X'}) ≤ (1 − 1/(2k))Δ`.
The new state is public by construction (a pair of LP points). -/
def BatchGood (ER : ExplicitRows E.n me) (bc : Fin E.n → ℝ) (κ m c : Fin (rowCount G me) → ℝ) (t L₀ c₀ Δ T₀ : ℝ)
    (o : Option (Point E.n me × Point E.n me)) : Prop :=
  ∃ xn Xn, o = some (xn, Xn) ∧ vec G xn ∈ Feasible (matrix G ER) bc κ m ∧
    pot ((1 / (2 * L₀) / 8) / (12 * Δ)) (vec G Xn - fun i =>
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (matrix G ER) (vec G xn) i)) ≤
        12 * rowCount G me * T₀ / (1 / (2 * L₀) / 8) ∧
    cent (48 * (2 * L₀)) (matrix G ER) (barS κ m (vec G xn)) (barDphi κ m (vec G xn)) c t
      (fun i => exp (vec G Xn i)) ≤ (1 - 1 / (2 * L₀) / 2) * Δ

open Probability in
set_option maxHeartbeats 6400000 in
/-- **One public batch preserves the full invariant.** Suppose the batch invariants hold at the
public state `(x, X) = (vec xp, vec Xp)` (with `κ, m, c` public): `x` strictly feasible,
`δ_t(x, e^X) ≤ Δ`, `Φ(X − log g(x)) ≤ B₀`, the D7 parameter regime (`k = 2L₀`, `C_N = 48k`,
`Δ ≤ (2¹⁶k²)⁻¹`, `K ≤ (2²⁰k)⁻¹`, `η ≤ Δ/(2¹⁶k)`, `N_w ≤ T₀‖·‖_∞`), the public envelope
`M ≤ M̄`, `c₀ = 1/(2M̄)`, and the path-following regime of `newtonStep_public`. Then the
output of `batchProg` fails `BatchGood` with probability at most `ζ_Newton + J_L·ζ_lev`, where
`ζ_Newton = d4Fail … (solveDelta R)` and `ζ_lev = d4Fail … (levDelta Δ R)`. -/
theorem batchProg_fail (ER : ExplicitRows E.n me) {a0 : ℝ}
    (ha0 : 0 < a0) (ha1 : a0 ≤ 1)
    (hrows : ∀ j, a0 ^ 2 ≤ ∑ v, ER.matrix j v ^ 2 ∧ ∑ v, ER.matrix j v ^ 2 ≤ 2) {bc : Fin E.n → ℝ}
    {κp mp cp xp Xp : Point E.n me} {κ m c x X : Fin (rowCount G me) → ℝ}
    (hκp : vec G κp = κ) (hmp : vec G mp = m) (hcp : vec G cp = c)
    (hxp : vec G xp = x) (hXp : vec G Xp = X)
    {t L₀ c₀ Δ K T₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * E.Mbar) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) (hc₀lo : 1 / (2 * E.Mbar) ≤ c₀) (hc₀hi : c₀ ≤ 1 / (2 * E.Mbar))
    (hU1 : 1 ≤ E.U) (hU : ∀ i, π / κ i ≤ E.U) {x₀ : Fin (rowCount G me) → ℝ}
    (hx : x ∈ Feasible (matrix G ER) bc κ m) (hx₀ : x₀ ∈ Feasible (matrix G ER) bc κ m)
    (hs0 : ∀ i, 1 / E.U ≤ slk κ m x₀ i)
    (hMbar : (rowCount G me : ℝ) ≤ E.Mbar) (hr : (1 : ℝ) ≤ E.n) (hε : 0 < E.ε) (hε1 : E.ε ≤ 1)
    (ht : |t| ≤ 16 * E.n / E.ε) (hc : ‖c‖ ≤ 4 * E.U)
    (hEC : E.C = 48 * (2 * L₀)) (hη0 : 0 < E.η) (hη : E.η ≤ 1 / (2 * L₀) * Δ / 2 ^ 16)
    (hΔ0 : 0 < Δ) (hΔ : Δ ≤ (1 / (2 * L₀)) ^ 2 / 2 ^ 16)
    (hK0 : 0 ≤ K) (hK : K ≤ 1 / (2 * L₀) / 2 ^ 20) (hT₀ : 1 ≤ T₀)
    (hT : ∀ v, mixed (48 * (2 * L₀)) (fun i => exp (X i)) v ≤ T₀ * ‖v‖)
    (hKμ : Real.log (12 * E.Mbar * T₀ / (1 / (2 * L₀) / 8)) /
      ((1 / (2 * L₀) / 8) / (12 * Δ)) ≤ K)
    (hpot : pot ((1 / (2 * L₀) / 8) / (12 * Δ))
      (X - fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ (matrix G ER) x i)) ≤
        12 * rowCount G me * T₀ / (1 / (2 * L₀) / 8))
    (hδ : cent (48 * (2 * L₀)) (matrix G ER) (barS κ m x) (barDphi κ m x) c t
      (fun i => exp (X i)) ≤ Δ)
    {Kd J t' R : ℕ} {Csym : ℝ} (hCsym0 : 0 ≤ Csym) (hCsym : ∀ e, (Spanner.symS G e : ℝ) ≤ Csym)
    (hKd : E.n ≤ 2 ^ Kd) (ht' : 0 < t') :
    mass ((batchProg E ER a0 κp mp cp xp Xp t L₀ c₀ Δ T₀ Kd J t' R).eval G.out)
        (fun o => ¬ BatchGood G ER bc κ m c t L₀ c₀ Δ T₀ o) ≤
      d4Fail E.n Csym Kd J t' R (solveDelta R) +
        batchJL E a0 Δ * d4Fail E.n Csym Kd J t' R (levDelta Δ R) := by
  -- constants
  set A := matrix G ER with hAdef
  set a : ℝ := 1 / (2 * L₀) with ha_def
  set ξ : ℝ := a / 8 with hξ_def
  set μ : ℝ := ξ / (12 * Δ) with hμ_def
  set g := gfun κ m (1 - 1 / L₀) c₀ A with hg_def
  set w : Fin (rowCount G me) → ℝ := fun i => exp (X i) with hw_def
  have hL0 : 0 < L₀ := by linarith
  have ha_pos : 0 < a := by positivity
  have ha4 : a ≤ 1 / 4 := by
    simp only [a]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hξ0 : 0 < ξ := by positivity
  have hμ0 : 0 < μ := by positivity
  have hΔs : Δ ≤ 1 / 2 ^ 20 := by nlinarith
  have hηs : E.η ≤ Δ := by nlinarith
  have hKs : K ≤ 1 / 2 ^ 22 := by nlinarith
  have hwpos : ∀ i, 0 < w i := fun i => exp_pos _
  have hA : (Aᵀ * A).det ≠ 0 := det_ne_zero_of_idRows (matrix_idRows G ER)
  have hrow : ∀ i, A i ≠ 0 := matrix_row_ne_zero G ER ha0 ha1 hrows
  have hn0 : 0 < E.n := by exact_mod_cast (show (0 : ℝ) < E.n by linarith)
  have hMnat : 1 ≤ rowCount G me := Fin.pos (iota G ER ⟨0, hn0⟩)
  have hM1 : (1 : ℝ) ≤ rowCount G me := by exact_mod_cast hMnat
  have hMb1 : 1 ≤ E.Mbar := hM1.trans hMbar
  -- hidden-row parameters from the public envelope `M ≤ M̄`
  have hLMh : Real.logb 2 (2 * rowCount G me) ≤ L₀ - 1 :=
    (Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)).trans hLM
  have hcM : c₀ ≤ 1 / (2 * rowCount G me) :=
    hc₀hi.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hc₀pos : 0 < c₀ := lt_of_lt_of_le (by positivity) hc₀lo
  have hKμh : Real.log (12 * rowCount G me * T₀ / ξ) / μ ≤ K := by
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
  set q : Fin (rowCount G me) → ℝ := fun i => t * c i + exp (X i) * barDphi κ m x i with hq_def
  set h := newtonDir A w (barS κ m x) q with hh_def
  have hqN : normQ t c w (barDphi κ m x) = q := rfl
  have hDcopy : normD w (barS κ m x) =
      vec G (weights (pairOf (normDPt κp mp xp Xp).pair)
        (normDPt κp mp xp Xp).explicit) := by
    rw [← vec_eq_weights, vec_normDPt, hκp, hmp, hxp, hXp]
  have hqcopy : normQ t c w (barDphi κ m x) = vec G (normQPt t κp mp cp xp Xp) := by
    rw [vec_normQPt, hκp, hmp, hcp, hxp, hXp]
  have hp := newtonPot_gram (q := normQ t c w (barDphi κ m x)) hA hwpos hS0
  have hC0 : 0 ≤ E.C := by rw [hEC]; positivity
  have hNew := newtonProgPub_numeric G ER hrow (fun i => (matrix_row_bounds G ER ha0.le ha1 hrows i).2) hL hLMh hκ hc₀lo hcM hU1 hU hx hx₀ hMbar hr hε
    hε1 hwpos ht hc hwin hδc hs0 hC0 hη0 hDcopy hqcopy hp (J := J) R hCsym0 hCsym hKd ht'
  have hcard : ((Sparsify.resid G (Sparsify.P0 (E.wf (pairOf (normDPt κp mp xp Xp).pair)))).card :
      ℝ≥0∞) ≤ (Fintype.card (Sym2 (Fin E.n)) : ℝ≥0∞) := by
    exact_mod_cast Finset.card_le_univ _
  have hNew' := hNew.trans (add_le_add le_rfl (mul_le_mul' hcard le_rfl))
  rw [newtonDir_eq_normD] at hNew'
  -- the composition
  unfold batchProg
  rw [RTree.eval_bind]
  refine (mass_bind_le_add _ _ _ _ (ε := batchJL E a0 Δ * d4Fail E.n Csym Kd J t' R (levDelta Δ R))
    hNew' ?_).trans le_rfl
  intro d hd
  rw [not_not] at hd
  obtain ⟨hAd, hed⟩ := hd
  -- the Newton error `e = d − h`
  set e : Fin (rowCount G me) → ℝ := vec G d - h with he_def
  have hAe : Aᵀ *ᵥ e = 0 := by
    rw [he_def, mulVec_sub, hAd, (newtonDir_spec hA hwpos hS0).1, sub_zero]
  have he : mixed (48 * (2 * L₀)) w (fun i => barS κ m x i * e i) ≤ E.η := by
    rw [← hEC]; exact hed
  -- the primal half
  obtain ⟨hx'F, hcent', hmove⟩ :=
    batch_primal hA hrow hL hLMh hκ hc₀pos.le hcM hx hΔ0 hΔ hK0 hK hη0.le hη hXg hδ hAe he
  set x' : Fin (rowCount G me) → ℝ := x + vec G d with hx'_def
  have hx'eq : x + (h + e) = x' := by
    rw [he_def, hx'_def]; abel
  have hxp' : vec G (addPt xp d) = x' := by rw [vec_addPt, hxp]
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
  have hspt : vec G (invSlackPt κp mp (addPt xp d)) = fun i => exp (sfun κ m x' i) :=
    vec_invSlackPt G hκ hx'F.2 hκp hmp hxp'
  obtain ⟨hp0, hp2⟩ := lewisExp_bounds hL
  obtain ⟨-, hLew⟩ := lewisStage G ER hn0 ha0 ha1 hrows hκ hx'F.2 hU1 hU hsst0 hs' hMbar hspt hp0 hp2
    hc₀pos.le hΔ0 (by linarith) J R hCsym0 hCsym hKd ht'
  rw [RTree.eval_bind]
  refine (mass_bind_le_add _ _ _ _ (ε := 0) hLew ?_).trans (le_of_eq (add_zero _))
  intro o ho
  rw [not_not] at ho
  obtain ⟨y, rfl, -, hy⟩ := ho
  -- the support step and `prop_batch`
  set st : PathState E.n me := ⟨xp, Xp, obsPt c₀ y⟩
  set z : Fin (rowCount G me) → ℝ := fun i => Real.log (Real.exp (vec G y i) + c₀) with hz_def
  have hzst : vec G st.z = z := vec_obsPt G c₀ y
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
  have hgood : BatchGood G ER bc κ m c t L₀ c₀ Δ T₀
      (some (addPt xp d, chasePt (1 / (2 * L₀) / 8) Xp out.2)) := by
    refine ⟨_, _, rfl, ?_⟩
    rw [hxp', vec_chasePt, hXp, ← hx'eq]
    exact ⟨hF, hP, hCent⟩
  simp only [RTree.eval_ofDeterministic, DTree.eval_map, mass_pure]
  split_ifs with hbad
  · exact le_rfl
  · exact absurd hgood hbad


/-- **The path-parameter move after a batch** (`batch_tchange`): on a `BatchGood` output, a move
`|t'/t − 1| ≤ α` with `αT₁ ≤ Δ/(16k)` and `αΔ ≤ Δ/(16k)` restores `δ_{t'}(x', e^{X'}) ≤ Δ`, where
`N_{e^{X'}} ≤ T₁‖·‖_∞`. Feasibility and the potential bound do not depend on `t`. -/
theorem batchGood_tchange (ER : ExplicitRows E.n me) {bc : Fin E.n → ℝ} {κ m c : Fin (rowCount G me) → ℝ}
    {t L₀ c₀ Δ T₀ : ℝ} (hκ : ∀ i, 0 < κ i) (hL : 2 ≤ L₀) {xn Xn : Point E.n me}
    (hgood : BatchGood G ER bc κ m c t L₀ c₀ Δ T₀ (some (xn, Xn))) {T₁ α t' : ℝ}
    (hT10 : 0 ≤ T₁)
    (hT1 : ∀ v, mixed (48 * (2 * L₀)) (fun i => exp (vec G Xn i)) v ≤ T₁ * ‖v‖)
    (ht : 0 < t) (hα : |t' / t - 1| ≤ α) (hαT : α * T₁ ≤ 1 / (2 * L₀) * Δ / 16)
    (hΔ0 : 0 < Δ) (hαΔ : α * Δ ≤ 1 / (2 * L₀) * Δ / 16) :
    cent (48 * (2 * L₀)) (matrix G ER) (barS κ m (vec G xn)) (barDphi κ m (vec G xn)) c t'
      (fun i => exp (vec G Xn i)) ≤ Δ := by
  obtain ⟨xn', Xn', heq, hF, -, hcap⟩ := hgood
  cases heq
  have hL0 : 0 < L₀ := by linarith
  exact batch_tchange (by positivity) hκ hF.2 (fun i => exp_pos _) hT10 hT1 ht hα
    (by positivity) hαT hcap hΔ0 hαΔ

#print axioms batchProg_cost
#print axioms batchProg_fail
#print axioms batchGood_tchange

end
end CutQueryComplexity.ImplicitLP.GenericQuery
