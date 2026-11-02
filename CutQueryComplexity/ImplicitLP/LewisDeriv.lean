import CutQueryComplexity.ImplicitLP.Lewis
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # The log–log Jacobian of Lewis weights (Lee–Sidford Lemma 24)

Lee–Sidford Lemma 24 differentiates the Lewis weights without proving that they are
differentiable (audit gap G3). Here differentiability comes from the implicit function theorem.

Let `B` have full column rank and no zero rows, `0 < p < 2`, and let `y(s) = log w_p(diag(eˢ) B)`
(`lewisLog`). The equation `y = T_s(y)`, where `T` is the Lewis map of `diag(eˢ) B`, is smooth in
`(s, y)` (`contDiffAt_lewisMap`). Its `y`-derivative `D` satisfies `‖D‖ ≤ 1 − p/2 < 1` because
`T_s` is a contraction, so `I − D` is invertible, and the implicit function theorem applies. The
local implicit function agrees with the global fixed point near `s = 0` because the fixed point
depends continuously on `s` (`dist_fixedPoint_le`). Hence `y` is differentiable at `0`.

Differentiating the Lewis identity `yᵢ = log σᵢ(diag(e^{s + (1/2−1/p)y}) B)` along `s = τh` with
the leverage-score derivative (P1) gives `(Σ + cΛ) ẏ = 2Λh` with `c = 2/p − 1`, so
`ẏ = 2(Σ + cΛ)⁻¹Λh = K h` (`hasDerivAt_lewisLog`). P0 then gives the consistency bound
`‖Kh‖_∞ + C‖Kh‖_w ≤ p(1 + 1/C)(‖h‖_∞ + C‖h‖_w)` (`lewisLog_consistency`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Filter Topology

noncomputable section

variable {M r : ℕ} {B : Matrix (Fin M) (Fin r) ℝ} {p : ℝ}

section Scale

theorem diag_gram (B : Matrix (Fin M) (Fin r) ℝ) (s : Fin M → ℝ) :
    (diagonal s * B)ᵀ * (diagonal s * B) = gram B (fun j => s j ^ 2) := by
  have hd : diagonal s * diagonal s = diagonal (fun j => s j ^ 2) := by
    rw [diagonal_mul_diagonal]; congr 1; funext j; ring
  simp only [gram, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal s) (diagonal s) B, hd]

theorem gram_diag (B : Matrix (Fin M) (Fin r) ℝ) (e d : Fin M → ℝ) :
    gram (diagonal e * B) d = gram B (fun j => e j ^ 2 * d j) := by
  have hd : diagonal e * (diagonal d * diagonal e) = diagonal (fun j => e j ^ 2 * d j) := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; congr 1; funext j; ring
  simp only [gram, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal d) (diagonal e) B,
    ← Matrix.mul_assoc (diagonal e) (diagonal d * diagonal e) B, hd]

theorem diag_row (B : Matrix (Fin M) (Fin r) ℝ) (e : Fin M → ℝ) (i : Fin M) :
    (diagonal e * B) i = e i • B i := by
  funext a; simp [diagonal_mul]

theorem qform_diag (B : Matrix (Fin M) (Fin r) ℝ) (e d : Fin M → ℝ) (i : Fin M) :
    qform (diagonal e * B) d i = e i ^ 2 * qform B (fun j => e j ^ 2 * d j) i := by
  simp only [qform, gram_diag, diag_row, mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  ring

theorem diag_det (hB : (Bᵀ * B).det ≠ 0) {e : Fin M → ℝ} (he : ∀ j, e j ≠ 0) :
    ((diagonal e * B)ᵀ * (diagonal e * B)).det ≠ 0 := by
  rw [diag_gram]
  exact gram_det_ne hB fun j => lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (he j)).symm

theorem diag_rows (hrow : ∀ i, B i ≠ 0) {e : Fin M → ℝ} (he : ∀ j, e j ≠ 0) (i : Fin M) :
    (diagonal e * B) i ≠ 0 := by
  rw [diag_row]; exact smul_ne_zero (he i) (hrow i)

/-- `diag(eᵘ) diag(eᵛ) B = diag(e^{u+v}) B`. -/
theorem diag_exp_mul (u v : Fin M → ℝ) :
    diagonal (fun j => exp (u j)) * (diagonal (fun j => exp (v j)) * B) =
      diagonal (fun j => exp (u j + v j)) * B := by
  rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
  congr 2; funext j; rw [exp_add]

end Scale

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem contDiffAt_qform (hB : (Bᵀ * B).det ≠ 0) {d : E → Fin M → ℝ} {x : E}
    (hd : ∀ j, ContDiffAt ℝ k (fun z => d z j) x) (hpos : ∀ j, 0 < d x j) (i : Fin M) :
    ContDiffAt ℝ k (fun z => qform B (d z) i) x := by
  have hG : ∀ a b, ContDiffAt ℝ k (fun z => gram B (d z) a b) x := by
    intro a b
    have : ∀ z, gram B (d z) a b = ∑ j, B j a * d z j * B j b := fun z => by
      simp only [gram]; rw [mul_apply]; simp only [mul_diagonal, transpose_apply]
    simp_rw [this]
    exact ContDiffAt.sum fun j _ => (contDiffAt_const.mul (hd j)).mul contDiffAt_const
  have hinv := contDiffAt_inv_entry hG (gram_det_ne hB hpos)
  simp only [qform, dotProduct, mulVec]
  exact ContDiffAt.sum fun a _ =>
    contDiffAt_const.mul (ContDiffAt.sum fun b _ => (hinv a b).mul contDiffAt_const)

/-- `lev(diag(eᵘ) B)ᵢ` is smooth in `u`. -/
theorem contDiffAt_levExp (hB : (Bᵀ * B).det ≠ 0) {u : E → Fin M → ℝ} {x : E}
    (hu : ∀ j, ContDiffAt ℝ k (fun z => u z j) x) (i : Fin M) :
    ContDiffAt ℝ k (fun z => lev (diagonal (fun j => exp (u z j)) * B) i) x := by
  simp_rw [lev_diag]
  exact ((hu i).exp.pow 2).mul
    (contDiffAt_qform hB (fun j => (hu j).exp.pow 2) (fun j => by positivity) i)

/-- The Lewis map of `diag(eˢ) B` at `y`, written through `B`. -/
theorem lewisMap_diag (s y : Fin M → ℝ) (i : Fin M) :
    lewisMap p (diagonal (fun j => exp (s j)) * B) y i = p / 2 * Real.log (exp (s i) ^ 2 *
      qform B (fun j => exp (s j) ^ 2 * exp ((1 - 2 / p) * y j)) i) := by
  simp only [lewisMap, qform_diag]

/-- **The scaled Lewis map is smooth** in `(s, y)`. -/
theorem contDiffAt_lewisMap (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) {s y : E → Fin M → ℝ} {x : E}
    (hs : ∀ j, ContDiffAt ℝ k (fun z => s z j) x) (hy : ∀ j, ContDiffAt ℝ k (fun z => y z j) x)
    (i : Fin M) :
    ContDiffAt ℝ k (fun z => lewisMap p (diagonal (fun j => exp (s z j)) * B) (y z) i) x := by
  simp_rw [lewisMap_diag]
  have hd : ∀ j, ContDiffAt ℝ k (fun z => exp (s z j) ^ 2 * exp ((1 - 2 / p) * y z j)) x :=
    fun j => ((hs j).exp.pow 2).mul ((contDiffAt_const.mul (hy j)).exp)
  have hq := contDiffAt_qform hB hd (fun j => by positivity) i
  refine contDiffAt_const.mul ((((hs i).exp.pow 2).mul hq).log ?_)
  exact (mul_pos (by positivity) (qform_pos hB hrow (fun j => by positivity) i)).ne'

/-- The scaled Lewis map is smooth jointly in `(s, y)`. -/
theorem contDiffAt_lewisMap_prod (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0)
    (z : (Fin M → ℝ) × (Fin M → ℝ)) (i : Fin M) :
    ContDiffAt ℝ 1 (fun z : (Fin M → ℝ) × (Fin M → ℝ) =>
        lewisMap p (diagonal (fun j => exp (z.1 j)) * B) z.2 i) z :=
  contDiffAt_lewisMap (p := p) (k := 1) hB hrow (s := fun z : (Fin M → ℝ) × (Fin M → ℝ) => z.1)
    (y := fun z : (Fin M → ℝ) × (Fin M → ℝ) => z.2)
    (fun j => ((contDiff_apply ℝ ℝ j).comp contDiff_fst).contDiffAt)
    (fun j => ((contDiff_apply ℝ ℝ j).comp contDiff_snd).contDiffAt) i

end Smooth

section Fixed

open Classical in
/-- **Logarithms of the `ℓ_p` Lewis weights**: the unique fixed point of the Lewis map. -/
def lewisLog (p : ℝ) (B : Matrix (Fin M) (Fin r) ℝ) : Fin M → ℝ :=
  if h : (Bᵀ * B).det ≠ 0 ∧ (∀ i, B i ≠ 0) ∧ 0 < p ∧ p < 2 then
    ContractingWith.fixedPoint (lewisMap p B) (lewisMap_contracting h.1 h.2.1 h.2.2.1 h.2.2.2)
  else 0

variable (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2)
include hB hrow hp0 hp2

theorem lewisLog_fixed : lewisMap p B (lewisLog p B) = lewisLog p B := by
  simp only [lewisLog, ne_eq, hB, not_false_eq_true, hrow, implies_true, hp0, hp2, and_self,
    ↓reduceDIte]
  exact ContractingWith.fixedPoint_isFixedPt _

theorem lewisLog_isLewis : IsLewis p B (fun i => exp (lewisLog p B i)) :=
  (isLewis_iff_fixed hB hrow hp0 _).mpr (lewisLog_fixed hB hrow hp0 hp2)

theorem dist_lewisLog_le (y : Fin M → ℝ) :
    dist y (lewisLog p B) ≤ dist y (lewisMap p B y) / (p / 2) := by
  simp only [lewisLog, ne_eq, hB, not_false_eq_true, hrow, implies_true, hp0, hp2, and_self,
    ↓reduceDIte]
  have := ContractingWith.dist_fixedPoint_le (lewisMap_contracting hB hrow hp0 hp2) y
  rwa [Real.coe_toNNReal _ (by linarith), sub_sub_cancel] at this

/-- **The Lewis identity in exponential form:** `σᵢ(diag(e^{(1/2−1/p) y}) B) = e^{yᵢ}`. -/
theorem lev_lewisLog (i : Fin M) :
    lev (diagonal (fun j => exp ((1 / 2 - 1 / p) * lewisLog p B j)) * B) i =
      exp (lewisLog p B i) := by
  have h := (lewisLog_isLewis hB hrow hp0 hp2).2 i
  have he : (fun j => exp (lewisLog p B j) ^ (1 / 2 - 1 / p)) =
      fun j => exp ((1 / 2 - 1 / p) * lewisLog p B j) := by
    funext j; rw [← Real.exp_mul, mul_comm]
  rwa [he] at h

end Fixed

section Jacobian

variable (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2)
include hB hrow hp0 hp2

/-- **Lewis weights are differentiable** in the row log-scaling (audit gap G3). -/
theorem hasFDerivAt_lewisLog_scale : ∃ L : (Fin M → ℝ) →L[ℝ] (Fin M → ℝ),
    HasFDerivAt (fun s : Fin M → ℝ => lewisLog p (diagonal (fun j => exp (s j)) * B)) L 0 := by
  set ys : (Fin M → ℝ) → Fin M → ℝ := fun s => lewisLog p (diagonal (fun j => exp (s j)) * B)
  have hBs : ∀ s : Fin M → ℝ, ((diagonal (fun j => exp (s j)) * B)ᵀ *
      (diagonal (fun j => exp (s j)) * B)).det ≠ 0 := fun s => diag_det hB fun j => exp_ne_zero _
  have hrs : ∀ s : Fin M → ℝ, ∀ i, (diagonal (fun j => exp (s j)) * B) i ≠ 0 :=
    fun s => diag_rows hrow fun j => exp_ne_zero _
  set y0 := ys 0
  set f : (Fin M → ℝ) × (Fin M → ℝ) → Fin M → ℝ :=
    fun z => z.2 - lewisMap p (diagonal (fun j => exp (z.1 j)) * B) z.2 with hfdef
  set u : (Fin M → ℝ) × (Fin M → ℝ) := (0, y0)
  have hsnd : ∀ (z : (Fin M → ℝ) × (Fin M → ℝ)) (j : Fin M),
      ContDiffAt ℝ 1 (fun z : (Fin M → ℝ) × (Fin M → ℝ) => z.2 j) z := fun z j =>
    ((contDiff_apply ℝ ℝ j).comp contDiff_snd).contDiffAt
  have hT := contDiffAt_lewisMap_prod (p := p) hB hrow
  have cdf : ContDiffAt ℝ 1 f u := by
    rw [contDiffAt_pi]
    intro i
    simp only [hfdef, Pi.sub_apply]
    exact (hsnd u i).sub (hT u i)
  -- the `y`-derivative is invertible: `T₀` is a `(1 − p/2)`-contraction
  set D := fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (Fin M → ℝ) (Fin M → ℝ)
  have hfd : HasFDerivAt f (fderiv ℝ f u) u := (cdf.differentiableAt one_ne_zero).hasFDerivAt
  have hg : HasFDerivAt (fun y => f (0, y)) D y0 :=
    hfd.comp y0 (hasFDerivAt_prodMk_right (0 : Fin M → ℝ) y0)
  set T0 := lewisMap p (diagonal (fun j => exp ((0 : Fin M → ℝ) j)) * B)
  have hT0eq : T0 = fun y => y - f (0, y) := by
    funext y; simp only [hfdef, sub_sub_cancel]; rfl
  have hT0 : HasFDerivAt T0 (ContinuousLinearMap.id ℝ (Fin M → ℝ) - D) y0 := by
    rw [hT0eq]; exact (hasFDerivAt_id y0).sub hg
  have hK := lewisMap_contracting (hBs 0) (hrs 0) hp0 hp2
  have hnorm := hT0.le_of_lipschitz hK.2
  rw [Real.coe_toNNReal _ (by linarith)] at hnorm
  have hinj : Function.Injective D := by
    intro v w hvw
    have h0 : D (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h1 : (ContinuousLinearMap.id ℝ (Fin M → ℝ) - D) (v - w) = v - w := by
      simp [h0]
    have h2 := (ContinuousLinearMap.id ℝ (Fin M → ℝ) - D).le_opNorm (v - w)
    rw [h1] at h2
    have h3 : ‖v - w‖ ≤ (1 - p / 2) * ‖v - w‖ :=
      h2.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    have h4 : ‖v - w‖ = 0 := by
      have := norm_nonneg (v - w); nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h4)
  have if₂ : D.IsInvertible :=
    ⟨(LinearEquiv.ofInjectiveEndo D.toLinearMap hinj).toContinuousLinearEquiv, by
      ext v; rfl⟩
  -- the implicit function agrees with the global fixed point near `0`
  have hψ := cdf.hasStrictFDerivAt_implicitFunction one_ne_zero if₂
  have hev := cdf.eventually_apply_eq_iff_implicitFunction one_ne_zero if₂
  have hfix : ∀ s, f (s, ys s) = 0 := fun s => by
    simp only [hfdef, ys]; rw [lewisLog_fixed (hBs s) (hrs s) hp0 hp2, sub_self]
  have hcont : Tendsto ys (𝓝 0) (𝓝 y0) := by
    have hTc : ContinuousAt (fun s : Fin M → ℝ =>
        lewisMap p (diagonal (fun j => exp (s j)) * B) y0) 0 := by
      rw [continuousAt_pi]
      intro i
      exact (contDiffAt_lewisMap (k := 1) hB hrow (s := fun s => s) (y := fun _ => y0)
        (fun j => (contDiff_apply ℝ ℝ j).contDiffAt) (fun j => contDiffAt_const) i).continuousAt
    have hT0y : lewisMap p (diagonal (fun j => exp ((0 : Fin M → ℝ) j)) * B) y0 = y0 :=
      lewisLog_fixed (hBs 0) (hrs 0) hp0 hp2
    have hlim : Tendsto (fun s : Fin M → ℝ =>
        dist y0 (lewisMap p (diagonal (fun j => exp (s j)) * B) y0) / (p / 2))
        (𝓝 0) (𝓝 0) := by
      have h1 := (tendsto_const_nhds (x := y0)).dist hTc.tendsto
      have h2 := h1.div_const (p / 2)
      have hT0y' : lewisMap p B y0 = y0 := by simpa using hT0y
      simpa [hT0y'] using h2
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun s => dist_nonneg) (fun s => ?_) hlim
    rw [dist_comm]
    exact dist_lewisLog_le (hBs s) (hrs s) hp0 hp2 y0
  have hpair : Tendsto (fun s => (s, ys s)) (𝓝 0) (𝓝 u) := tendsto_id.prodMk_nhds hcont
  have heq : ys =ᶠ[𝓝 0] cdf.implicitFunction one_ne_zero if₂ := by
    filter_upwards [hpair.eventually hev] with s hs
    have : f (s, ys s) = f u := by rw [hfix s, hfix 0]
    exact (hs.mp this).symm
  exact ⟨_, hψ.hasFDerivAt.congr_of_eventuallyEq heq⟩


/-- **The log–log Jacobian of Lewis weights** (Lee–Sidford Lemma 24):
`d/dτ log w_p(diag(e^{τh}) B)|_{τ=0} = 2(Σ + cΛ)⁻¹Λh`, with `c = 2/p − 1`, `P` the projection of
`W^{1/2−1/p} B`, `σ = diag P = w`, and `Λ = Σ − P ⊙ P`. -/
theorem hasDerivAt_lewisLog (h : Fin M → ℝ) (i : Fin M) :
    let P := proj (diagonal (fun j => exp ((1 / 2 - 1 / p) * lewisLog p B j)) * B)
    let σ : Fin M → ℝ := fun j => P j j
    let Λ : Matrix (Fin M) (Fin M) ℝ := diagonal σ - P ⊙ P
    let K : Matrix (Fin M) (Fin M) ℝ := (2 : ℝ) • ((diagonal σ + (2 / p - 1) • Λ)⁻¹ * Λ)
    HasDerivAt (fun τ => lewisLog p (diagonal (fun j => exp (τ * h j)) * B) i) ((K *ᵥ h) i) 0 := by
  intro P σ Λ K
  set c : ℝ := 1 / 2 - 1 / p with hc
  set ys : (Fin M → ℝ) → Fin M → ℝ := fun s => lewisLog p (diagonal (fun j => exp (s j)) * B)
    with hys
  have hBs : ∀ s : Fin M → ℝ, ((diagonal (fun j => exp (s j)) * B)ᵀ *
      (diagonal (fun j => exp (s j)) * B)).det ≠ 0 := fun s => diag_det hB fun j => exp_ne_zero _
  have hrs : ∀ s : Fin M → ℝ, ∀ i, (diagonal (fun j => exp (s j)) * B) i ≠ 0 :=
    fun s => diag_rows hrow fun j => exp_ne_zero _
  obtain ⟨L, hL⟩ := hasFDerivAt_lewisLog_scale hB hrow hp0 hp2
  have hys0 : ys 0 = lewisLog p B := by simp [hys]
  -- along the line `s = τh`
  have hline : HasDerivAt (fun τ : ℝ => τ • h) h 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
  have hL0 : HasFDerivAt ys L ((0 : ℝ) • h) := by rwa [zero_smul]
  have hgi : ∀ j, HasDerivAt (fun τ : ℝ => ys (τ • h) j) (L h j) 0 := by
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hL0 hline
    exact hasDerivAt_pi.mp this
  -- the Lewis identity along the line, in every coordinate
  set U : ℝ → Fin M → ℝ := fun τ k => (τ • h) k + c * ys (τ • h) k with hU
  set Φ : Fin M → (Fin M → ℝ) → ℝ := fun i' u => lev (diagonal (fun k => exp (u k)) * B) i'
    with hΦdef
  have hid : ∀ τ i', ys (τ • h) i' = Real.log (Φ i' (U τ)) := fun τ i' => by
    have := lev_lewisLog (hBs (τ • h)) (hrs (τ • h)) hp0 hp2 i'
    rw [diag_exp_mul] at this
    have hm : (diagonal fun k => exp ((τ • h) k + c * ys (τ • h) k)) =
        diagonal fun j => exp ((1 / 2 - 1 / p) *
          lewisLog p (diagonal (fun j => exp ((τ • h) j)) * B) j + (τ • h) j) := by
      congr 1; funext k; congr 1; simp only [hc, hys]; rw [add_comm]
    simp only [hΦdef, hU]
    rw [hm, this, Real.log_exp]
  have hUd : HasDerivAt U (h + c • L h) 0 := by
    refine hasDerivAt_pi.mpr fun k => ?_
    exact (hasDerivAt_pi.mp hline k).add ((hgi k).const_mul c)
  have hU0 : U 0 = fun k => (1 / 2 - 1 / p) * lewisLog p B k := by
    funext k; simp only [hU, zero_smul, Pi.zero_apply, zero_add, hc]; rw [hys0]
  -- the Fréchet derivative of `Φ` at `U 0`, in every direction (P1)
  set u0 := U 0
  set B' := diagonal (fun k => exp (u0 k)) * B with hB'
  have hB'P : proj B' = P := by simp only [hB', hU0, P]
  have hΦ : ∀ i', HasFDerivAt (Φ i') (fderiv ℝ (Φ i') u0) u0 := fun i' =>
    ((contDiffAt_levExp (k := 1) hB (u := fun u => u)
      (fun j => (contDiff_apply ℝ ℝ j).contDiffAt) i').differentiableAt one_ne_zero).hasFDerivAt
  have hdir : ∀ i' v, fderiv ℝ (Φ i') u0 v = 2 * (Λ *ᵥ v) i' := by
    intro i' v
    have hl : HasDerivAt (fun τ : ℝ => u0 + τ • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u0
    have hΦ' : HasFDerivAt (Φ i') (fderiv ℝ (Φ i') u0) (u0 + (0 : ℝ) • v) := by
      rw [zero_smul, add_zero]; exact hΦ i'
    have h1 : HasDerivAt (fun τ : ℝ => Φ i' (u0 + τ • v)) (fderiv ℝ (Φ i') u0 v) 0 := by
      have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hΦ' hl
      exact this
    have h2 := hasDerivAt_lev B' (diag_det hB fun j => exp_ne_zero _) v i'
    have heq : (fun τ : ℝ => Φ i' (u0 + τ • v)) =
        fun τ => lev (diagonal (fun j => exp (τ * v j)) * B') i' := by
      funext τ
      show lev (diagonal (fun k => exp ((u0 + τ • v) k)) * B) i' =
        lev (diagonal (fun j => exp (τ * v j)) * (diagonal (fun k => exp (u0 k)) * B)) i'
      rw [diag_exp_mul]
      congr 3; funext k; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf
    rw [heq] at h1
    rw [h1.unique h2, hB'P]
  have hσ : ∀ j, σ j = exp (lewisLog p B j) := fun j => lev_lewisLog hB hrow hp0 hp2 j
  have hΦU0 : ∀ i', Φ i' u0 = σ i' := fun i' => by simp only [hΦdef, u0, hU0]; rfl
  have hσpos : ∀ j, 0 < σ j := fun j => by rw [hσ]; exact exp_pos _
  -- differentiate the identity: `σ ẏ = 2Λ(h + cẏ)`
  have hall : ∀ i', σ i' * L h i' = 2 * (Λ *ᵥ h) i' + 2 * c * (Λ *ᵥ L h) i' := by
    intro i'
    have hΦU : HasDerivAt (fun τ => Φ i' (U τ)) (fderiv ℝ (Φ i') u0 (h + c • L h)) 0 := by
      have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (hΦ i') hUd
      exact this
    have hne : Φ i' (U 0) ≠ 0 := by rw [hΦU0]; exact (hσpos i').ne'
    have hlog := hΦU.log hne
    have heqf : (fun τ : ℝ => ys (τ • h) i') = fun τ => Real.log (Φ i' (U τ)) :=
      funext fun τ => hid τ i'
    have huniq := (hgi i').unique (heqf ▸ hlog)
    rw [hdir, hΦU0, mulVec_add, mulVec_smul] at huniq
    rw [huniq]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [(hσpos i').ne']
  -- solve the linear system with P0's invertibility
  have hPs : Pᵀ = P := proj_symm _
  have hPi : P * P = P := proj_idem (diag_det hB fun j => exp_ne_zero _)
  have hc0 : 0 ≤ 2 / p - 1 := by rw [sub_nonneg, le_div_iff₀ hp0]; linarith
  have hunit := (proj_jacobian_bound hPs hPi hσpos hc0).1
  set Bm := diagonal σ + (2 / p - 1) • Λ
  have hBm : Bm *ᵥ L h = (2 : ℝ) • (Λ *ᵥ h) := by
    funext i'
    simp only [Bm, add_mulVec, smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mulVec_diagonal]
    have := hall i'
    rw [hc] at this
    have e : 2 * (1 / 2 - 1 / p) = -(2 / p - 1) := by ring
    rw [e] at this
    linarith
  have hKh : K *ᵥ h = L h := by
    show ((2 : ℝ) • (Bm⁻¹ * Λ)) *ᵥ h = L h
    rw [smul_mulVec, ← mulVec_mulVec, ← mulVec_smul, ← hBm, mulVec_mulVec,
      nonsing_inv_mul _ hunit, one_mulVec]
  rw [hKh]
  exact hgi i

/-- **Consistency of Lewis weights** (P0 at the Lewis Jacobian): for every `C > 0`,
`‖ẏ‖_∞ + C‖ẏ‖_w ≤ p(1 + 1/C)(‖h‖_∞ + C‖h‖_w)`, where `ẏ = K h` is the derivative of the
log Lewis weights in the direction `h` (`hasDerivAt_lewisLog`) and `w = σ`. -/
theorem lewisLog_consistency (h : Fin M → ℝ) {C : ℝ} (hC : 0 < C) :
    let P := proj (diagonal (fun j => exp ((1 / 2 - 1 / p) * lewisLog p B j)) * B)
    let σ : Fin M → ℝ := fun j => P j j
    let Λ : Matrix (Fin M) (Fin M) ℝ := diagonal σ - P ⊙ P
    let K : Matrix (Fin M) (Fin M) ℝ := (2 : ℝ) • ((diagonal σ + (2 / p - 1) • Λ)⁻¹ * Λ)
    (∀ j, σ j = exp (lewisLog p B j)) ∧
      ‖K *ᵥ h‖ + C * wnorm σ (K *ᵥ h) ≤ p * (1 + 1 / C) * (‖h‖ + C * wnorm σ h) := by
  intro P σ Λ K
  have hσ : ∀ j, σ j = exp (lewisLog p B j) := fun j => lev_lewisLog hB hrow hp0 hp2 j
  refine ⟨hσ, ?_⟩
  have hPs : Pᵀ = P := proj_symm _
  have hPi : P * P = P := proj_idem (diag_det hB fun j => exp_ne_zero _)
  have hσpos : ∀ j, 0 < σ j := fun j => by rw [hσ]; exact exp_pos _
  have hc0 : 0 ≤ 2 / p - 1 := by rw [sub_nonneg, le_div_iff₀ hp0]; linarith
  have := proj_jacobian_mixed hPs hPi hσpos hc0 hC h
  rwa [beta_of_p hp0] at this

end Jacobian

end

end ImplicitLP
end CutQueryComplexity
