import CutQueryComplexity.ImplicitLP.PublicParams
import CutQueryComplexity.ImplicitLP.BatchFull

set_option autoImplicit false

/-! # One public batch: state, support envelopes, and the support step (D7 → D8, step 1)

* **Public state.** Coordinatewise maps of public `LPPoint`s (`mapPt`, `map2Pt`) commute with
  `lpVec` and with `pairOf`, so every hidden-row quantity built from public points is a pair
  formula (copy-constant by construction). `PathState` holds the public points of a path batch.
* **Envelopes.** For `|qᵢ| ≤ Q`, `wᵢ ≥ w_min > 0`, `M ≤ M̄`: `Ā = C_*Q/(C√w_min)`,
  `A₊ = √M̄ Ā`, `S₊ = M̄Q`, `L₊ = max(A₊, C_*S₊)` (`envSup`, `support_envelopes`).
  Clipping the public formulas (`clipQPt`, `clipWPt`) gives `hAbar` on every pair, including
  nonedges, without changing actual-row values (`lpVec_clipQPt`, `lpVec_clipWPt`).
* **Gradient bound with approximate observation** (`potGrad_obs_bound`, `batch_support_inputs`):
  `‖∇Φ(X − z)‖_∞ ≤ 2μB₀`, since `z` is within `2Δ` of `log g(x)`; and `e^{X} ≥ (4/5)c₀`.
* **The support step of a batch** (`supportPub_env`, `support_batch_form`,
  `batch_support_public`): the public support oracle at the envelopes, with `σ = ξ/1000`, gives
  exactly the `hv`, `hal`, `hopt` that `prop_batch` consumes, so `prop_batch` holds for the
  output point.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

open DirectedMincut (LPPoint)

variable {n : ℕ}

/-! ## Public state: coordinatewise maps of public points -/

/-- Apply a scalar map to every coordinate of a public point. -/
def mapPt (f : ℝ → ℝ) (pt : LPPoint (Fin n)) : LPPoint (Fin n) :=
  ⟨fun u v => f (pt.z u v), f pt.q, fun j => f (pt.yp j), fun j => f (pt.ym j)⟩

/-- Apply a binary scalar map coordinatewise to two public points. -/
def map2Pt (f : ℝ → ℝ → ℝ) (p₁ p₂ : LPPoint (Fin n)) : LPPoint (Fin n) :=
  ⟨fun u v => f (p₁.z u v) (p₂.z u v), f p₁.q p₂.q, fun j => f (p₁.yp j) (p₂.yp j),
    fun j => f (p₁.ym j) (p₂.ym j)⟩

theorem pairOf_map (f : ℝ → ℝ) (z : Fin n → Fin n → ℝ) (e : Sym2 (Fin n)) :
    pairOf (fun u v => f (z u v)) e = f (pairOf z e) := by
  induction e using Sym2.ind with
  | _ u v => simp only [pairOf, Sym2.lift_mk]; split_ifs <;> rfl

theorem pairOf_map2 (f : ℝ → ℝ → ℝ) (z₁ z₂ : Fin n → Fin n → ℝ) (e : Sym2 (Fin n)) :
    pairOf (fun u v => f (z₁ u v) (z₂ u v)) e = f (pairOf z₁ e) (pairOf z₂ e) := by
  induction e using Sym2.ind with
  | _ u v => simp only [pairOf, Sym2.lift_mk]; split_ifs <;> rfl

theorem pairOf_mapPt (f : ℝ → ℝ) (pt : LPPoint (Fin n)) (e : Sym2 (Fin n)) :
    pairOf (mapPt f pt).z e = f (pairOf pt.z e) := pairOf_map f pt.z e

theorem pairOf_map2Pt (f : ℝ → ℝ → ℝ) (p₁ p₂ : LPPoint (Fin n)) (e : Sym2 (Fin n)) :
    pairOf (map2Pt f p₁ p₂).z e = f (pairOf p₁.z e) (pairOf p₂.z e) := pairOf_map2 f p₁.z p₂.z e

variable (G : DiGraph (Fin n))

theorem lpVec_mapPt (f : ℝ → ℝ) (pt : LPPoint (Fin n)) (i : Fin (lpM G)) :
    lpVec G (mapPt f pt) i = f (lpVec G pt i) := by
  simp only [lpVec]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j)) <;> rfl

theorem lpVec_map2Pt (f : ℝ → ℝ → ℝ) (p₁ p₂ : LPPoint (Fin n)) (i : Fin (lpM G)) :
    lpVec G (map2Pt f p₁ p₂) i = f (lpVec G p₁ i) (lpVec G p₂ i) := by
  simp only [lpVec]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j)) <;> rfl

/-- The public state of a path batch: the primal point `x`, the log-weights `X` (weights
`w = e^X`), and the observation `z` of `log g(x')`. All hidden rows are pair formulas. -/
structure PathState (n : ℕ) where
  x : LPPoint (Fin n)
  X : LPPoint (Fin n)
  z : LPPoint (Fin n)

/-- The weights `w = e^X` as a public point. -/
def wPt (X : LPPoint (Fin n)) : LPPoint (Fin n) := mapPt Real.exp X

/-- The support objective `q = ∇Φ(X − z)` as a public point. -/
def gradPt (μ : ℝ) (X z : LPPoint (Fin n)) : LPPoint (Fin n) :=
  map2Pt (fun a b => 2 * μ * Real.sinh (μ * (a - b))) X z

theorem lpVec_wPt (X : LPPoint (Fin n)) : lpVec G (wPt X) = fun i => Real.exp (lpVec G X i) :=
  funext fun i => lpVec_mapPt G _ _ i

theorem lpVec_gradPt (μ : ℝ) (X z : LPPoint (Fin n)) :
    lpVec G (gradPt μ X z) = potGrad μ (lpVec G X - lpVec G z) :=
  funext fun i => by simp only [gradPt, lpVec_map2Pt, potGrad, Pi.sub_apply]

/-! ## Clipping the public formulas -/

/-- `q` clipped to `[−Q, Q]` in every public coordinate. -/
def clipQPt (Q : ℝ) (qp : LPPoint (Fin n)) : LPPoint (Fin n) := mapPt (clipTo (-Q) Q) qp

/-- `w` raised to at least `w_min` in every public coordinate. -/
def clipWPt (wmin : ℝ) (wp : LPPoint (Fin n)) : LPPoint (Fin n) := mapPt (max wmin) wp

theorem abs_clipTo_le {Q : ℝ} (hQ : 0 ≤ Q) (y : ℝ) : |clipTo (-Q) Q y| ≤ Q :=
  abs_le.mpr ⟨le_clipTo _ _ _, clipTo_le (by linarith) _⟩

/-- **Clipping leaves actual rows unchanged** when they obey the envelope. -/
theorem lpVec_clipQPt {Q : ℝ} (qp : LPPoint (Fin n)) (h : ∀ i, |lpVec G qp i| ≤ Q) :
    lpVec G (clipQPt Q qp) = lpVec G qp :=
  funext fun i => by
    rw [clipQPt, lpVec_mapPt]
    exact clipTo_of_mem (abs_le.mp (h i)).1 (abs_le.mp (h i)).2

theorem lpVec_clipWPt {wmin : ℝ} (wp : LPPoint (Fin n)) (h : ∀ i, wmin ≤ lpVec G wp i) :
    lpVec G (clipWPt wmin wp) = lpVec G wp :=
  funext fun i => by rw [clipWPt, lpVec_mapPt]; exact max_eq_right (h i)

/-! ## Support envelopes -/

/-- The scalar envelope `|C_* qᵢ/(C√wᵢ)| ≤ C_*Q/(C√w_min)`. -/
theorem abs_coef_le {C Cs Q wmin qi wi : ℝ} (hC : 0 < C) (hCs : 0 < Cs) (hwmin : 0 < wmin)
    (hq : |qi| ≤ Q) (hw : wmin ≤ wi) :
    |Cs * qi / (C * Real.sqrt wi)| ≤ Cs * Q / (C * Real.sqrt wmin) := by
  have hs0 : 0 < Real.sqrt wmin := Real.sqrt_pos.mpr hwmin
  have hs : Real.sqrt wmin ≤ Real.sqrt wi := Real.sqrt_le_sqrt hw
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hq
  rw [abs_div, abs_mul, abs_of_pos hCs, abs_of_pos (mul_pos hC (Real.sqrt_pos.mpr (hwmin.trans_le hw)))]
  have h1 : Cs * |qi| ≤ Cs * Q := mul_le_mul_of_nonneg_left hq hCs.le
  calc Cs * |qi| / (C * Real.sqrt wi) ≤ Cs * Q / (C * Real.sqrt wi) := by gcongr
    _ ≤ Cs * Q / (C * Real.sqrt wmin) := by gcongr

/-- `‖a‖₂ ≤ √M̄ · Ā` from a coordinate bound and `M ≤ M̄`. -/
theorem euc_le_of_abs {M : ℕ} {a : Fin M → ℝ} {Ab Mbar : ℝ} (hAb : ∀ i, |a i| ≤ Ab)
    (hAb0 : 0 ≤ Ab) (hM : (M : ℝ) ≤ Mbar) : euc a ≤ Real.sqrt Mbar * Ab := by
  have hsq : ∑ i, a i ^ 2 ≤ Mbar * Ab ^ 2 := by
    calc ∑ i, a i ^ 2 ≤ ∑ _i : Fin M, Ab ^ 2 := sum_le_sum fun i _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hAb i) 2
      _ = M * Ab ^ 2 := by simp
      _ ≤ Mbar * Ab ^ 2 := mul_le_mul_of_nonneg_right hM (by positivity)
  have h0 : 0 ≤ euc a := euc_nonneg a
  have h1 : euc a ^ 2 ≤ (Real.sqrt Mbar * Ab) ^ 2 := by
    rw [euc_sq, mul_pow, Real.sq_sqrt ((Nat.cast_nonneg M).trans hM)]; exact hsq
  exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).mp h1

/-- The public envelopes of one support call: `Ā = C_*Q/(C√w_min)`, `A₊ = √M̄ Ā`, `S₊ = M̄Q`,
`L₊ = max(A₊, C_*S₊)`. -/
def envSup (Mbar Q wmin C Cs σ : ℝ) : SupPub where
  Mbar := Mbar
  Ap := Real.sqrt Mbar * (Cs * Q / (C * Real.sqrt wmin))
  Lb := max (Real.sqrt Mbar * (Cs * Q / (C * Real.sqrt wmin))) (Cs * (Mbar * Q))
  Sq := Mbar * Q
  Abar := Cs * Q / (C * Real.sqrt wmin)
  σ := σ

/-- **The support envelopes.** From `|qᵢ| ≤ Q`, `wᵢ ≥ w_min > 0` on the actual rows, `M ≤ M̄`,
and `|q| ≤ Q`, `w ≥ w_min` on every public pair, the hypotheses `hAp`, `hL`, `hSq`, `hAbar`,
`hMbar` of `supportPub_public` hold at `envSup`. -/
theorem support_envelopes (qp wp : LPPoint (Fin n)) {C Cs Q wmin Mbar σ : ℝ} (hC : 0 < C)
    (hCs : 0 < Cs) (hwmin : 0 < wmin) (hQ : 0 ≤ Q)
    (hq : ∀ i, |lpVec G qp i| ≤ Q) (hw : ∀ i, wmin ≤ lpVec G wp i)
    (hqe : ∀ e, |pairOf qp.z e| ≤ Q) (hwe : ∀ e, wmin ≤ pairOf wp.z e)
    (hMbar : (lpM G : ℝ) ≤ Mbar) :
    let S := envSup Mbar Q wmin C Cs σ
    euc (fun i => Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))) ≤ S.Ap ∧
    max (euc (fun i => Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))))
      (∑ i, |Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))| *
        (C * Real.sqrt (lpVec G wp i))) ≤ S.Lb ∧
    ∑ i, |lpVec G qp i| ≤ S.Sq ∧
    (∀ e, |Cs * pairOf qp.z e / (C * Real.sqrt (pairOf wp.z e))| ≤ S.Abar) ∧
    (lpM G : ℝ) ≤ S.Mbar := by
  intro S
  have hAb0 : 0 ≤ Cs * Q / (C * Real.sqrt wmin) := by positivity
  have hcoef := fun i => abs_coef_le hC hCs hwmin (hq i) (hw i)
  have hA : euc (fun i => Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))) ≤ S.Ap :=
    euc_le_of_abs hcoef hAb0 hMbar
  have hM0 : (0 : ℝ) ≤ lpM G := Nat.cast_nonneg _
  have hSq : ∑ i, |lpVec G qp i| ≤ S.Sq := by
    calc ∑ i, |lpVec G qp i| ≤ ∑ _i : Fin (lpM G), Q := sum_le_sum fun i _ => hq i
      _ = (lpM G : ℝ) * Q := by simp
      _ ≤ Mbar * Q := mul_le_mul_of_nonneg_right hMbar hQ
  have hκ : ∀ i, |Cs * lpVec G qp i / (C * Real.sqrt (lpVec G wp i))| *
      (C * Real.sqrt (lpVec G wp i)) = Cs * |lpVec G qp i| := fun i => by
    have hpos : 0 < C * Real.sqrt (lpVec G wp i) :=
      mul_pos hC (Real.sqrt_pos.mpr (hwmin.trans_le (hw i)))
    rw [abs_div, abs_mul, abs_of_pos hCs, abs_of_pos hpos, div_mul_cancel₀ _ hpos.ne']
  refine ⟨hA, max_le (hA.trans (le_max_left _ _)) ?_, hSq, fun e => ?_, hMbar⟩
  · simp_rw [hκ]
    rw [← mul_sum]
    exact (mul_le_mul_of_nonneg_left hSq hCs.le).trans (le_max_right _ _)
  · exact abs_coef_le hC hCs hwmin (hqe e) (hwe e)

/-- **The public support step at the envelopes.** Run the public support oracle on the clipped
points `q° = clip_{[−Q,Q]} q`, `w° = max(w_min, w)`. If the actual rows obey `|qᵢ| ≤ Q` and
`wᵢ ≥ w_min`, then on the actual rows the data are the original `q`, `w` and the output point `v`
is dyadic, in the ball `{N_w ≤ C_*}`, sign-aligned with `q`, `σ`-optimal; budget
`(2N + 2)(m + 3)·6Bn` with the public parameters of `envSup`. -/
theorem supportPub_env (qp wp : LPPoint (Fin n)) {C Cs Q wmin Mbar σ : ℝ} (hC : 0 < C)
    (hCs : 0 < Cs) (hwmin : 0 < wmin) (hQ : 0 ≤ Q) (hσ : 0 < σ)
    (hq : ∀ i, |lpVec G qp i| ≤ Q) (hw : ∀ i, wmin ≤ lpVec G wp i)
    (hMbar : (lpM G : ℝ) ≤ Mbar) :
    let S := envSup Mbar Q wmin C Cs σ
    let q := lpVec G qp
    let w := lpVec G wp
    let prog := supportPubProg C Cs S.ρ (clipQPt Q qp) (clipWPt wmin wp) S.Mbar S.Ap S.h S.p
      S.B S.m S.N S.kτ S.kl S.kc S.po
    let v := lpVec G (prog.eval G.out).2
    (∀ i, ∃ m : ℤ, v i = m / 2 ^ S.po) ∧ mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ q i * v i) ∧
      (∀ v₀, mixed C w v₀ ≤ Cs → q ⬝ᵥ v₀ ≤ q ⬝ᵥ v + σ) ∧
      prog.cost G.out ≤ (2 * S.N + 2) * ((S.m + 3) * (6 * S.B * n)) := by
  intro S q w prog v
  have eq := lpVec_clipQPt G qp hq
  have ew := lpVec_clipWPt G wp hw
  have hq' : ∀ i, |lpVec G (clipQPt Q qp) i| ≤ Q := by rw [eq]; exact hq
  have hw' : ∀ i, wmin ≤ lpVec G (clipWPt wmin wp) i := by rw [ew]; exact hw
  have hqe : ∀ e, |pairOf (clipQPt Q qp).z e| ≤ Q := fun e => by
    rw [clipQPt, pairOf_mapPt]; exact abs_clipTo_le hQ _
  have hwe : ∀ e, wmin ≤ pairOf (clipWPt wmin wp).z e := fun e => by
    rw [clipWPt, pairOf_mapPt]; exact le_max_left _ _
  obtain ⟨hA, hL, hSq, hAb, hMb⟩ := support_envelopes (σ := σ) G (clipQPt Q qp) (clipWPt wmin wp)
    hC hCs hwmin hQ hq' hw' hqe hwe hMbar
  have hwpos : ∀ i, 0 < lpVec G (clipWPt wmin wp) i := fun i => hwmin.trans_le (hw' i)
  have h := supportPub_public G S (clipQPt Q qp) (clipWPt wmin wp) hC hCs hwpos hσ hA hL hSq hAb
    hMb
  simp only [eq, ew] at h
  exact h

end

end ImplicitLP
end CutQueryComplexity
/-! # The support step in the form `prop_batch` consumes -/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

/-- **From the support guarantee to `prop_batch`'s hypotheses.** With `q = ∇Φ(X − z)`, the
ball, sign alignment `qᵢvᵢ ≥ 0` and `σ`-optimality against the ball give `hv`, `hal`
(`vᵢ(Xᵢ − zᵢ) ≥ 0`, since `sinh` has the sign of its argument) and `hopt`. -/
theorem support_batch_form {M : ℕ} {C Cs μ σ : ℝ} (hCs : 0 ≤ Cs) (hμ : 0 < μ)
    {X z w v : Fin M → ℝ}
    (hball : mixed C w v ≤ Cs) (hal : ∀ i, 0 ≤ potGrad μ (X - z) i * v i)
    (hopt : ∀ v₀, mixed C w v₀ ≤ Cs → potGrad μ (X - z) ⬝ᵥ v₀ ≤ potGrad μ (X - z) ⬝ᵥ v + σ) :
    mixed C w v ≤ Cs ∧ (∀ i, 0 ≤ v i * (X i - z i)) ∧
      supp {u | mixed C w u ≤ Cs} (potGrad μ (X - z)) - σ ≤ potGrad μ (X - z) ⬝ᵥ v := by
  refine ⟨hball, fun i => ?_, ?_⟩
  · have h := hal i
    simp only [potGrad, Pi.sub_apply] at h
    rcases lt_trichotomy (X i - z i) 0 with hd | hd | hd
    · have hs : sinh (μ * (X i - z i)) < 0 := sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hμ hd)
      have hg : 2 * μ * sinh (μ * (X i - z i)) < 0 := mul_neg_of_pos_of_neg (by positivity) hs
      have hv : v i ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      nlinarith
    · rw [hd, mul_zero]
    · have hs : 0 < sinh (μ * (X i - z i)) := sinh_pos_iff.mpr (mul_pos hμ hd)
      have hg : 0 < 2 * μ * sinh (μ * (X i - z i)) := by positivity
      have hv : 0 ≤ v i := by
        by_contra hc; push Not at hc; nlinarith
      positivity
  · have h0 : (0 : Fin M → ℝ) ∈ {u | mixed C w u ≤ Cs} := by
      show mixed C w 0 ≤ Cs
      simp [mixed, wnorm, hCs]
    have hle : supp {u | mixed C w u ≤ Cs} (potGrad μ (X - z)) ≤
        potGrad μ (X - z) ⬝ᵥ v + σ :=
      csSup_le (Set.Nonempty.image _ ⟨0, h0⟩) (by
        rintro _ ⟨v₀, hv₀, rfl⟩; exact hopt v₀ hv₀)
    linarith

/-- `e^{1/4} ≤ 21/16`. -/
theorem exp_quarter_le : exp (1 / 4 : ℝ) ≤ 21 / 16 := by
  have := abs_exp_sub_one_sub_id_le (x := (1 / 4 : ℝ)) (by norm_num)
  rw [abs_le] at this; norm_num at this ⊢; linarith

/-- **The potential gradient at an approximate observation.** If `Φ(X − y) ≤ B₀` and the
observation `z` is within `d` of `y` with `μd ≤ 1/4`, then `‖∇Φ(X − z)‖_∞ ≤ 2μB₀`. -/
theorem potGrad_obs_bound {M : ℕ} {μ B₀ d : ℝ} (hμ : 0 < μ) {X y z : Fin M → ℝ}
    (hpot : pot μ (X - y) ≤ B₀) (hd : μ * d ≤ 1 / 4) (hz : ∀ i, |z i - y i| ≤ d) (i : Fin M) :
    |potGrad μ (X - z) i| ≤ 2 * μ * B₀ := by
  set b := X i - y i
  have hterm : 2 * cosh (μ * b) ≤ B₀ := by
    have := single_le_sum (f := fun j => 2 * cosh (μ * (X - y) j)) (fun j _ => by
      have := cosh_pos (μ * (X - y) j); positivity) (mem_univ i)
    exact this.trans hpot
  have hc1 : 1 ≤ cosh (μ * b) := one_le_cosh _
  have hB2 : 2 ≤ B₀ := by linarith
  have hsc : |sinh (μ * b)| ≤ cosh (μ * b) := by
    have := (cosh_add_abs_sinh (μ * b)).2
    linarith [exp_pos (-|μ * b|)]
  have hgb : |2 * μ * sinh (μ * b)| ≤ μ * B₀ := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * μ)]
    nlinarith
  have hab : |(X i - z i) - b| ≤ d := by
    have : (X i - z i) - b = -(z i - y i) := by simp only [b]; ring
    rw [this, abs_neg]; exact hz i
  have h := grad_upper hμ hd hab
  have he : exp (μ * d) ≤ 21 / 16 := (exp_le_exp.mpr hd).trans exp_quarter_le
  have h2 : exp (μ * d) * |2 * μ * sinh (μ * b)| ≤ 21 / 16 * (μ * B₀) :=
    mul_le_mul he hgb (abs_nonneg _) (by norm_num)
  show |2 * μ * sinh (μ * (X - z) i)| ≤ 2 * μ * B₀
  simp only [Pi.sub_apply]
  nlinarith

variable {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c : Fin M → ℝ} {t : ℝ}

/-- **The public support inputs of a batch.** Under the batch invariants (the hypotheses of
`prop_batch` that precede the support step), the support objective `q = ∇Φ(X − z)` at the
observation `z` of `log g(x')` obeys `‖q‖_∞ ≤ 2μB₀` with `B₀ = 12MT₀/ξ` (the observed argument
is within `2Δ` of `X − log g(x)`: `Δ` from the observation and `C_* ≤ Δ` from the target move),
and the weights obey `e^{Xᵢ} ≥ (4/5)c₀`. -/
theorem batch_support_inputs (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) {x : Fin M → ℝ} (hx : x ∈ Feasible A b κ m)
    {X : Fin M → ℝ} {Δ K η T₀ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ (1 / (2 * L₀)) ^ 2 / 2 ^ 16)
    (hK0 : 0 ≤ K) (hK : K ≤ 1 / (2 * L₀) / 2 ^ 20) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / (2 * L₀) * Δ / 2 ^ 16)
    (hKμ : Real.log (12 * M * T₀ / (1 / (2 * L₀) / 8)) /
      ((1 / (2 * L₀) / 8) / (12 * Δ)) ≤ K)
    (hpot : pot ((1 / (2 * L₀) / 8) / (12 * Δ))
      (X - fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)) ≤
        12 * M * T₀ / (1 / (2 * L₀) / 8))
    (hδ : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t (fun i => exp (X i)) ≤ Δ)
    {e : Fin M → ℝ} (hAe : Aᵀ *ᵥ e = 0)
    (he : mixed (48 * (2 * L₀)) (fun i => exp (X i)) (fun i => barS κ m x i * e i) ≤ η)
    {z : Fin M → ℝ}
    (hz : ∀ i, |z i - Real.log (gfun κ m (1 - 1 / L₀) c₀ A
      (x + (newtonDir A (fun i => exp (X i)) (barS κ m x)
        (fun i => t * c i + exp (X i) * barDphi κ m x i) + e)) i)| ≤ Δ) :
    (∀ i, |potGrad ((1 / (2 * L₀) / 8) / (12 * Δ)) (X - z) i| ≤
        2 * ((1 / (2 * L₀) / 8) / (12 * Δ)) * (12 * M * T₀ / (1 / (2 * L₀) / 8))) ∧
      ∀ i, 4 / 5 * c₀ ≤ exp (X i) := by
  set a : ℝ := 1 / (2 * L₀)
  set ξ : ℝ := a / 8
  set μ : ℝ := ξ / (12 * Δ)
  set C : ℝ := 48 * (2 * L₀)
  set g := gfun κ m (1 - 1 / L₀) c₀ A
  have ha0 : 0 < a := by positivity
  have ha4 : a ≤ 1 / 4 := by
    simp only [a]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hμ0 : 0 < μ := by positivity
  have hC : 0 < C := by positivity
  have hXg : ∀ i, |X i - Real.log (g x i)| ≤ K := fun i => by
    have := pot_coord_bound hμ0 hpot i
    simp only [Pi.sub_apply] at this
    exact this.trans hKμ
  obtain ⟨-, -, hmove⟩ :=
    batch_primal hA hrow hL hLM hκ hc₀ hcM hx hΔ0 hΔ hK0 hK hη0 hη hXg hδ hAe he
  refine ⟨fun i => ?_, fun i => ?_⟩
  · -- the observation is within `2Δ` of `log g(x)`
    set x' := x + (newtonDir A (fun i => exp (X i)) (barS κ m x)
        (fun i => t * c i + exp (X i) * barDphi κ m x i) + e)
    have hu : ∀ j, |Real.log (g x' j) - Real.log (g x j)| ≤ Δ := fun j => by
      have h1 : |Real.log (g x' j) - Real.log (g x j)| ≤
          mixed C (fun i => exp (X i)) (fun i => Real.log (g x' i) - Real.log (g x i)) := by
        rw [← Real.norm_eq_abs]
        exact (norm_le_pi_norm (fun i => Real.log (g x' i) - Real.log (g x i)) j).trans
          (norm_le_mixed hC.le _)
      refine h1.trans (hmove.trans ?_)
      nlinarith
    have hz2 : ∀ j, |z j - Real.log (g x j)| ≤ 2 * Δ := fun j => by
      have h1 := hz j
      calc |z j - Real.log (g x j)| ≤
            |z j - Real.log (g x' j)| + |Real.log (g x' j) - Real.log (g x j)| := by
            have : z j - Real.log (g x j) =
                (z j - Real.log (g x' j)) + (Real.log (g x' j) - Real.log (g x j)) := by ring
            rw [this]; exact abs_add_le _ _
        _ ≤ 2 * Δ := by linarith [hu j]
    have hd : μ * (2 * Δ) ≤ 1 / 4 := by
      have : μ * (2 * Δ) = ξ / 6 := by simp only [μ]; field_simp; ring
      rw [this]; simp only [ξ]; linarith
    exact potGrad_obs_bound hμ0 hpot hd hz2 i
  · -- the weight floor
    have hK1 : K ≤ 1 / 5 := by
      have : a / 2 ^ 20 ≤ 1 / 5 := by nlinarith
      linarith
    have hg : 0 < g x i := add_pos_of_pos_of_nonneg (exp_pos _) hc₀
    have hgc : c₀ ≤ g x i := le_add_of_nonneg_left (exp_pos _).le
    have h1 := (abs_le.mp (hXg i)).1
    have h2 : exp (-K) * g x i ≤ exp (X i) := by
      calc exp (-K) * g x i = exp (-K) * exp (Real.log (g x i)) := by rw [exp_log hg]
        _ = exp (-K + Real.log (g x i)) := by rw [exp_add]
        _ ≤ exp (X i) := exp_le_exp.mpr (by linarith)
    have h3 : 4 / 5 ≤ exp (-K) :=
      exp_fifth_bounds.2.trans (exp_le_exp.mpr (by linarith))
    nlinarith [exp_pos (-K)]

end

end ImplicitLP
end CutQueryComplexity
/-! # One public batch -/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

open DirectedMincut (LPPoint)

/-- **One public batch: the support step preserves the full invariant.** The state is public
(`st : PathState n`; the support step reads the copy vectors `X`, `z`). Under the batch invariants of
`prop_batch` (all hypotheses except the support step's `hv`, `hal`, `hopt`), with public
`c₀ > 0` and `M ≤ M̄`, run the public support oracle on `q = ∇Φ(X − z)` and `w = e^X`
(as public points, clipped to `Q = 2μ·12M̄T₀/ξ` and `w_min = (4/5)c₀`) with the envelopes of
`envSup` and `σ = ξ/1000`. Its output point `v` is dyadic, the budget is
`(2N + 2)(m + 3)·6Bn` on every execution, and the three conclusions of `prop_batch` hold for
`x' = x + (h + e)`, `X' = X − (1 + ξ)v`. -/
theorem batch_support_public {n r : ℕ} (G : DiGraph (Fin n))
    {A : Matrix (Fin (lpM G)) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c : Fin (lpM G) → ℝ} {t : ℝ}
    (st : PathState n) {x X z : Fin (lpM G) → ℝ}
    (hXst : lpVec G st.X = X) (hzst : lpVec G st.z = z)
    (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * lpM G) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hcM : c₀ ≤ 1 / (2 * lpM G)) (hM : 1 ≤ lpM G) (hx : x ∈ Feasible A b κ m)
    {Δ K η T₀ Mbar : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ (1 / (2 * L₀)) ^ 2 / 2 ^ 16)
    (hK0 : 0 ≤ K) (hK : K ≤ 1 / (2 * L₀) / 2 ^ 20) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / (2 * L₀) * Δ / 2 ^ 16) (hT₀ : 1 ≤ T₀)
    (hT : ∀ v, mixed (48 * (2 * L₀)) (fun i => exp (X i)) v ≤ T₀ * ‖v‖)
    (hKμ : Real.log (12 * lpM G * T₀ / (1 / (2 * L₀) / 8)) /
      ((1 / (2 * L₀) / 8) / (12 * Δ)) ≤ K)
    (hpot : pot ((1 / (2 * L₀) / 8) / (12 * Δ))
      (X - fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)) ≤
        12 * lpM G * T₀ / (1 / (2 * L₀) / 8))
    (hδ : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t (fun i => exp (X i)) ≤ Δ)
    {e : Fin (lpM G) → ℝ} (hAe : Aᵀ *ᵥ e = 0)
    (he : mixed (48 * (2 * L₀)) (fun i => exp (X i)) (fun i => barS κ m x i * e i) ≤ η)
    (hz : ∀ i, |z i - Real.log (gfun κ m (1 - 1 / L₀) c₀ A
      (x + (newtonDir A (fun i => exp (X i)) (barS κ m x)
        (fun i => t * c i + exp (X i) * barDphi κ m x i) + e)) i)| ≤ Δ)
    (hMbar : (lpM G : ℝ) ≤ Mbar) :
    let ξ : ℝ := 1 / (2 * L₀) / 8
    let μ : ℝ := ξ / (12 * Δ)
    let C : ℝ := 48 * (2 * L₀)
    let Cs : ℝ := (1 - 3 * (1 / (2 * L₀)) / 4) * Δ
    let σ : ℝ := ξ / 1000
    let Q : ℝ := 2 * μ * (12 * Mbar * T₀ / ξ)
    let wmin : ℝ := 4 / 5 * c₀
    let S := envSup Mbar Q wmin C Cs σ
    let prog := supportPubProg C Cs S.ρ (clipQPt Q (gradPt μ st.X st.z))
      (clipWPt wmin (wPt st.X)) S.Mbar S.Ap S.h S.p S.B S.m S.N S.kτ S.kl S.kc S.po
    let v := lpVec G (prog.eval G.out).2
    let w : Fin (lpM G) → ℝ := fun i => exp (X i)
    let x' := x + (newtonDir A w (barS κ m x) (fun i => t * c i + w i * barDphi κ m x i) + e)
    let X' := X - (1 + ξ) • v
    (∀ i, ∃ k : ℤ, v i = k / 2 ^ S.po) ∧
      prog.cost G.out ≤ (2 * S.N + 2) * ((S.m + 3) * (6 * S.B * n)) ∧
      x' ∈ Feasible A b κ m ∧
      pot μ (X' - fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A x' i)) ≤
        12 * lpM G * T₀ / ξ ∧
      cent C A (barS κ m x') (barDphi κ m x') c t (fun i => exp (X' i)) ≤
        (1 - 1 / (2 * L₀) / 2) * Δ := by
  intro ξ μ C Cs σ Q wmin S prog v w x' X'
  have hL0 : 0 < L₀ := by linarith
  have ha0 : 0 < 1 / (2 * L₀) := by positivity
  have ha4 : 1 / (2 * L₀) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hξ0 : 0 < ξ := by positivity
  have hμ0 : 0 < μ := by positivity
  have hC : 0 < C := by positivity
  have hCs : 0 < Cs := by
    have : 0 < 1 - 3 * (1 / (2 * L₀)) / 4 := by linarith
    positivity
  have hσ0 : 0 < σ := by positivity
  have hwmin : 0 < wmin := by positivity
  have hM0 : (0 : ℝ) ≤ lpM G := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := by
    have : 0 ≤ Mbar := hM0.trans hMbar
    have : 0 ≤ T₀ := by linarith
    positivity
  obtain ⟨hqb, hwb⟩ := batch_support_inputs hA hrow hL hLM hκ hc₀.le hcM hx hΔ0 hΔ hK0 hK hη0
    hη hKμ hpot hδ hAe he hz
  have hq : ∀ i, |lpVec G (gradPt μ st.X st.z) i| ≤ Q := fun i => by
    rw [lpVec_gradPt, hXst, hzst]
    refine (hqb i).trans ?_
    have : 12 * (lpM G : ℝ) * T₀ / ξ ≤ 12 * Mbar * T₀ / ξ := by
      gcongr
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hw : ∀ i, wmin ≤ lpVec G (wPt st.X) i := fun i => by
    rw [lpVec_wPt, hXst]; exact hwb i
  obtain ⟨hdy, hball, hal, hopt, hcost⟩ :=
    supportPub_env G (gradPt μ st.X st.z) (wPt st.X) hC hCs hwmin hQ hσ0 hq hw hMbar
  rw [lpVec_gradPt, hXst, hzst] at hal hopt
  rw [lpVec_wPt, hXst] at hball hopt
  obtain ⟨hv, hal', hopt'⟩ := support_batch_form (C := C) hCs.le hμ0 hball hal hopt
  refine ⟨hdy, hcost, ?_⟩
  exact prop_batch hA hrow hL hLM hκ hc₀.le hcM hM hx hΔ0 hΔ hK0 hK hη0 hη hT₀ hT hKμ hpot hδ
    hAe he hz hv hal' hσ0.le le_rfl hopt'

end

end ImplicitLP
end CutQueryComplexity
