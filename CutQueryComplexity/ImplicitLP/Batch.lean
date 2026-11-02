import CutQueryComplexity.ImplicitLP.CenterClose
import CutQueryComplexity.ImplicitLP.Chase

/-! # One robust path batch (`prop:batch`, D7)

The audited draft's batch has three operations: an exactly feasible primal step `d = h + e` with
`N_w(Se) ≤ η`, a dyadic observation `z` of `log g(x')`, and the chase update
`w' = exp(X − (1+ξ)v)` with `v` in the ball `{N_w ≤ C_*}`. The parameters are `k = 2L₀`,
`C_N = 48k`, `ξ = 1/(8k)`, `C_* = (1 − 3/(4k))Δ`, `Δ ≤ (2¹⁶k²)⁻¹`, `K ≤ (2²⁰k)⁻¹`, and
`η ≤ Δ/(2¹⁶k)`.

* `batch_primal`: `x'` is strictly feasible, `δ_t(x', w) ≤ 8Δ² + 4η`, and the target moves by
  `N_w(log g(x') − log g(x)) ≤ (1 − 7/(8k))Δ < C_*`, so the move lies in the chasing ball. This
  uses `eq:projection`, `eq:newton`, `eq:gmove`, and two comparisons `N_g ≤ e^{K/2} N_w`.
* `batch_weights`: `δ_t(x', w') ≤ (1 − 1/(2k))Δ` (`eq:capmargin`), by `eq:wmove`.
* `pot_coord_bound`: `Φ(a) ≤ B₀` gives `‖a‖_∞ ≤ log B₀/μ`. With the audited draft's `μ⁻¹ log B₀ ≤ K`, the
  potential invariant gives the weight comparison `‖X − log g(x)‖_∞ ≤ K`.
* `mixedBall_chaseSet`: the ball `{N_w ≤ C_*}` is a chasing set when `N_w ≤ T₀‖·‖_∞`.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

variable {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c : Fin M → ℝ} {t : ℝ}

/-- `Φ(a) ≤ B₀` gives `|aᵢ| ≤ log B₀ / μ`. -/
theorem pot_coord_bound {μ B₀ : ℝ} (hμ : 0 < μ) {a : Fin M → ℝ} (h : pot μ a ≤ B₀) (i : Fin M) :
    |a i| ≤ Real.log B₀ / μ := by
  have hterm : 2 * cosh (μ * a i) ≤ B₀ := by
    have := single_le_sum (f := fun j => 2 * cosh (μ * a j)) (fun j _ => by
      have := cosh_pos (μ * a j); positivity) (mem_univ i)
    exact this.trans h
  have hexp : exp (μ * |a i|) ≤ B₀ := by
    have h1 := (cosh_add_abs_sinh (μ * a i)).1
    have h2 : |sinh (μ * a i)| ≤ cosh (μ * a i) := by
      have := (cosh_add_abs_sinh (μ * a i)).2
      linarith [exp_pos (-|μ * a i|)]
    rw [abs_mul, abs_of_pos hμ] at h1
    linarith
  rw [le_div_iff₀ hμ, mul_comm]
  rw [← exp_le_exp, exp_log (lt_of_lt_of_le (exp_pos _) hexp)]
  exact hexp

/-- **The mixed-norm ball is a chasing set** when `N_w ≤ T₀‖·‖_∞`. -/
theorem mixedBall_chaseSet {C Cs T₀ : ℝ} {w : Fin M → ℝ} (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i)
    (hT : ∀ v, mixed C w v ≤ T₀ * ‖v‖) (hT0 : 0 < T₀) (hCs : 0 ≤ Cs) :
    ChaseSet {v | mixed C w v ≤ Cs} Cs T₀ where
  solid v hv v' hv' := (mixed_mono hC hw hv').trans hv
  inner v hv := by
    refine (hT v).trans ?_
    have : ‖v‖ ≤ Cs / T₀ := by
      exact (pi_norm_le_iff_of_nonneg (div_nonneg hCs hT0.le)).mpr fun i => by rw [Real.norm_eq_abs]; exact hv i
    calc T₀ * ‖v‖ ≤ T₀ * (Cs / T₀) := mul_le_mul_of_nonneg_left this hT0.le
      _ = Cs := by field_simp
  outer v hv i := by
    rw [← Real.norm_eq_abs]
    exact ((norm_le_pi_norm v i).trans (norm_le_mixed hC v)).trans hv

/-- Arithmetic of the target move: with `a = 1/k ≤ 1/4`, `Δ ≤ a²/2¹⁶`, `η ≤ aΔ/2¹⁶`, `E ≤ 1 + a/2²⁰`,
and `v ≤ E(1 + a/16)Δ + Eη`, we get `E(1 − a + 4v)v ≤ (1 − 7a/8)Δ`. -/
theorem batch_target_arith {a Δ η E v : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 4) (hΔ0 : 0 < Δ)
    (hΔ : Δ ≤ a ^ 2 / 2 ^ 16) (hη0 : 0 ≤ η) (hη : η ≤ a * Δ / 2 ^ 16)
    (hE : E ≤ 1 + a / 2 ^ 20) (hv0 : 0 ≤ v) (hv : v ≤ E * ((1 + a / 16) * Δ + η)) :
    E * ((1 - a + 4 * v) * v) ≤ (1 - 7 * a / 8) * Δ := by
  -- `v ≤ (1 + a/15)Δ`
  have hv' : v ≤ (1 + a / 15) * Δ := by
    have h1 : (1 + a / 16) * Δ + η ≤ (1 + a / 16 + a / 2 ^ 16) * Δ := by nlinarith
    have h2 : E * ((1 + a / 16) * Δ + η) ≤ (1 + a / 2 ^ 20) * ((1 + a / 16 + a / 2 ^ 16) * Δ) :=
      mul_le_mul hE h1 (by positivity) (by positivity)
    nlinarith [mul_pos ha0 hΔ0, mul_pos (mul_pos ha0 ha0) hΔ0]
  have h4v : 4 * v ≤ a / 10000 := by nlinarith
  have hfac : 1 - a + 4 * v ≤ 1 - a + a / 10000 := by linarith
  have hfac0 : 0 ≤ 1 - a + 4 * v := by nlinarith
  calc E * ((1 - a + 4 * v) * v) ≤ (1 + a / 2 ^ 20) * ((1 - a + a / 10000) * ((1 + a / 15) * Δ)) :=
        mul_le_mul hE (mul_le_mul hfac hv' hv0 (by nlinarith)) (by positivity) (by positivity)
    _ ≤ (1 - 7 * a / 8) * Δ := by
        have : (1 + a / 2 ^ 20) * ((1 - a + a / 10000) * (1 + a / 15)) ≤ 1 - 7 * a / 8 := by
          nlinarith [mul_pos ha0 ha0, mul_pos (mul_pos ha0 ha0) ha0]
        nlinarith

/-- Arithmetic of the capped centrality: `(1 + 4Δ)(8Δ² + 4η + (1 − 5a/8)Δ) ≤ (1 − a/2)Δ`. -/
theorem batch_cap_arith {a Δ η : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 4) (hΔ0 : 0 < Δ)
    (hΔ : Δ ≤ a ^ 2 / 2 ^ 16) (hη0 : 0 ≤ η) (hη : η ≤ a * Δ / 2 ^ 16) :
    (1 + 4 * Δ) * (8 * Δ ^ 2 + 4 * η + (1 - 5 * a / 8) * Δ) ≤ (1 - a / 2) * Δ := by
  have h1 : 8 * Δ ^ 2 + 4 * η ≤ a / 4096 * Δ := by nlinarith
  have h2 : 4 * Δ ≤ a / 16384 := by nlinarith
  have h3 : 8 * Δ ^ 2 + 4 * η + (1 - 5 * a / 8) * Δ ≤ (1 - 5 * a / 8 + a / 4096) * Δ := by linarith
  have h4 : 0 ≤ 8 * Δ ^ 2 + 4 * η + (1 - 5 * a / 8) * Δ := by nlinarith
  calc (1 + 4 * Δ) * (8 * Δ ^ 2 + 4 * η + (1 - 5 * a / 8) * Δ)
      ≤ (1 + a / 16384) * ((1 - 5 * a / 8 + a / 4096) * Δ) :=
        mul_le_mul (by linarith) h3 h4 (by positivity)
    _ ≤ (1 - a / 2) * Δ := by
        have : (1 + a / 16384) * (1 - 5 * a / 8 + a / 4096) ≤ 1 - a / 2 := by nlinarith
        nlinarith

/-- `e^{K/2} ≤ 1 + K` for `0 ≤ K ≤ 1`. -/
theorem exp_half_le {K : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) : exp (K / 2) ≤ 1 + K := by
  have := abs_exp_sub_one_sub_id_le (x := K / 2) (by rw [abs_of_nonneg (by positivity)]; linarith)
  rw [abs_le] at this; nlinarith

/-- **The primal half of `prop:batch`.** -/
theorem batch_primal (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) {x : Fin M → ℝ} (hx : x ∈ Feasible A b κ m) {X : Fin M → ℝ}
    {Δ K η : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ (1 / (2 * L₀)) ^ 2 / 2 ^ 16) (hK0 : 0 ≤ K)
    (hK : K ≤ 1 / (2 * L₀) / 2 ^ 20) (hη0 : 0 ≤ η) (hη : η ≤ 1 / (2 * L₀) * Δ / 2 ^ 16)
    (hXg : ∀ i, |X i - Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)| ≤ K)
    (hδ : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t (fun i => exp (X i)) ≤ Δ)
    {e : Fin M → ℝ} (hAe : Aᵀ *ᵥ e = 0)
    (he : mixed (48 * (2 * L₀)) (fun i => exp (X i)) (fun i => barS κ m x i * e i) ≤ η) :
    let w : Fin M → ℝ := fun i => exp (X i)
    let h := newtonDir A w (barS κ m x) (fun i => t * c i + w i * barDphi κ m x i)
    x + (h + e) ∈ Feasible A b κ m ∧
      cent (48 * (2 * L₀)) A (barS κ m (x + (h + e))) (barDphi κ m (x + (h + e))) c t w ≤
        8 * Δ ^ 2 + 4 * η ∧
      mixed (48 * (2 * L₀)) w (fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A (x + (h + e)) i) -
        Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)) ≤ (1 - 7 * (1 / (2 * L₀)) / 8) * Δ := by
  intro w h
  set C : ℝ := 48 * (2 * L₀)
  set a : ℝ := 1 / (2 * L₀)
  set g := gfun κ m (1 - 1 / L₀) c₀ A x
  have hC : 0 < C := by positivity
  have ha0 : 0 < a := by positivity
  have ha4 : a ≤ 1 / 4 := by simp only [a]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hS : ∀ i, 0 < barS κ m x i := barS_pos hκ hx.2
  have hw : ∀ i, 0 < w i := fun i => exp_pos _
  have hg : ∀ i, 0 < g i := fun i => add_pos_of_pos_of_nonneg (exp_pos _) hc₀
  have hK1 : K ≤ 1 / 5 := by
    have : a / 2 ^ 20 ≤ 1 / 5 := by nlinarith
    linarith
  -- weight comparisons `w ≤ e^K g` and `g ≤ e^K w`
  have hwg : ∀ i, w i ≤ exp K * g i ∧ g i ≤ exp K * w i := fun i => by
    have h1 := abs_le.mp (hXg i)
    constructor
    · rw [← exp_log (hg i), ← exp_add]; simp only [w]; rw [exp_le_exp]; linarith
    · rw [← exp_log (hg i)]; simp only [w]; rw [← exp_add, exp_le_exp]; linarith
  obtain ⟨he1, he2⟩ := exp_fifth_bounds
  have hKe : exp K ≤ exp (1 / 5) := exp_le_exp.mpr hK1
  have hlo : ∀ i, 4 / 5 * g i ≤ w i := fun i => by
    have h1 := (hwg i).2
    have h2 : g i ≤ 5 / 4 * w i := h1.trans (mul_le_mul_of_nonneg_right (hKe.trans he1) (hw i).le)
    linarith
  have hhi : ∀ i, w i ≤ 5 / 4 * g i := fun i =>
    (hwg i).1.trans (mul_le_mul_of_nonneg_right (hKe.trans he1) (hg i).le)
  -- `eq:projection` and `eq:newton`
  obtain ⟨hh1, hh2⟩ := newtonDir_spec hA (q := fun i => t * c i + w i * barDphi κ m x i) hw hS
  have hproj := eq_projection_note hA hrow hL hLM hκ hc₀ hcM hx.2 hlo hhi hh1 hh2
  have hγ : 1 + 1 / (16 * (2 * L₀)) = 1 + a / 16 := by simp only [a]; field_simp
  have hγ1 : 1 + a / 16 ≤ 17 / 16 := by linarith
  have hδ0 : 0 ≤ cent C A (barS κ m x) (barDphi κ m x) c t w := cent_nonneg hC.le t w
  have hSh : mixed C w (fun i => barS κ m x i * h i) ≤
      (1 + a / 16) * cent C A (barS κ m x) (barDphi κ m x) c t w := by
    rw [← hγ]; exact hproj.2
  have hsmall : (1 + a / 16) * cent C A (barS κ m x) (barDphi κ m x) c t w + η ≤ 1 / 10 := by
    have : Δ ≤ 1 / 2 ^ 20 := by nlinarith
    have : η ≤ 1 / 2 ^ 20 := by nlinarith
    nlinarith
  obtain ⟨hint, hfeas, hcent⟩ := eq_newton hκ hC hx.2 hw hh1 hh2 hAe (by positivity) hγ1 hδ0
    hSh he hsmall
  have hfeas' : x + (h + e) ∈ Feasible A b κ m :=
    ⟨by rw [mulVec_add, hx.1, hfeas, add_zero], hint⟩
  refine ⟨hfeas', hcent.trans (by nlinarith), ?_⟩
  -- the target move
  set d := h + e
  have hSd : mixed C w (fun i => barS κ m x i * d i) ≤ (1 + a / 16) * Δ + η := by
    have hsplit : (fun i => barS κ m x i * d i) =
        (fun i => barS κ m x i * h i) + fun i => barS κ m x i * e i := by
      funext i; simp only [d, Pi.add_apply]; ring
    rw [hsplit]
    refine (mixed_add_le hC.le (fun i => (hw i).le) _ _).trans (add_le_add ?_ he)
    exact hSh.trans (mul_le_mul_of_nonneg_left hδ (by positivity))
  set E := exp (K / 2)
  have hE1 : 1 ≤ E := one_le_exp (by positivity)
  have hE : E ≤ 1 + a / 2 ^ 20 := (exp_half_le hK0 (by linarith)).trans (by linarith)
  have hvg : mixed C g (fun i => barS κ m x i * d i) ≤ E * ((1 + a / 16) * Δ + η) :=
    (mixed_le_of_le_exp hC.le hK0 (fun i => (hwg i).2) _).trans
      (mul_le_mul_of_nonneg_left hSd (exp_pos _).le)
  have hdi : ∀ i, barS κ m x i * |d i| < 1 := fun i => by
    have h1 : |barS κ m x i * d i| ≤ mixed C w (fun i => barS κ m x i * d i) := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (fun i => barS κ m x i * d i) i).trans (norm_le_mixed hC.le _)
    rw [abs_mul, abs_of_pos (hS i)] at h1
    nlinarith
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, Interior κ m (x + τ • d) := fun τ hτ =>
    segment_interior hκ hx.2 hdi hτ
  have hv1 : mixed C g (fun i => barS κ m x i * d i) ≤ 1 / 10 := by
    refine hvg.trans ?_
    have : (1 + a / 16) * Δ + η ≤ 1 / 20 := by nlinarith
    nlinarith
  have hgm := eq_gmove_note hA hrow hL hκ hc₀ hseg hv1
  have hback := mixed_le_of_le_exp (g := g) hC.le hK0 (fun i => (hwg i).1)
    (fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A (x + d) i) - Real.log (g i))
  set vg := mixed C g (fun i => barS κ m x i * d i)
  have hvg0 : 0 ≤ vg := mixed_nonneg hC.le _
  have harith := batch_target_arith ha0 ha4 hΔ0 hΔ hη0 hη hE hvg0 hvg
  have hk : 1 - 1 / (2 * L₀) = 1 - a := rfl
  calc mixed C w (fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A (x + d) i) - Real.log (g i))
      ≤ E * mixed C g (fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A (x + d) i) - Real.log (g i)) :=
        hback
    _ ≤ E * ((1 - a + 4 * vg) * vg) := mul_le_mul_of_nonneg_left (by rw [← hk]; exact hgm)
        (exp_pos _).le
    _ ≤ (1 - 7 * a / 8) * Δ := harith

/-- **The weight half of `prop:batch`** (`eq:capmargin`): with `ξ = a/8`, `C_* = (1 − 3a/4)Δ`,
`v` in the chasing ball and `δ_t(x', w) ≤ 8Δ² + 4η`, the updated weights
`w' = exp(X − (1+ξ)v)` give `δ_t(x', w') ≤ (1 − a/2)Δ`. -/
theorem batch_weights {C : ℝ} (hC : 0 < C) {A : Matrix (Fin M) (Fin r) ℝ} (hκ : ∀ i, 0 < κ i)
    {x' X v : Fin M → ℝ} (hx' : Interior κ m x') {a Δ η : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 4)
    (hΔ0 : 0 < Δ) (hΔ : Δ ≤ a ^ 2 / 2 ^ 16) (hη0 : 0 ≤ η) (hη : η ≤ a * Δ / 2 ^ 16)
    (hcent : cent C A (barS κ m x') (barDphi κ m x') c t (fun i => exp (X i)) ≤
      8 * Δ ^ 2 + 4 * η)
    (hv : mixed C (fun i => exp (X i)) v ≤ (1 - 3 * a / 4) * Δ) :
    cent C A (barS κ m x') (barDphi κ m x') c t (fun i => exp (X i - (1 + a / 8) * v i)) ≤
      (1 - a / 2) * Δ := by
  set w : Fin M → ℝ := fun i => exp (X i)
  set w' : Fin M → ℝ := fun i => exp (X i - (1 + a / 8) * v i)
  have hlogd : (fun i => Real.log (w' i) - Real.log (w i)) = (-(1 + a / 8)) • v := by
    funext i; simp only [w, w', Real.log_exp, Pi.smul_apply, smul_eq_mul]; ring
  have haw : mixed C w (fun i => Real.log (w' i) - Real.log (w i)) ≤ (1 - 5 * a / 8) * Δ := by
    rw [hlogd, mixed_smul, abs_neg, abs_of_pos (by linarith)]
    calc (1 + a / 8) * mixed C w v ≤ (1 + a / 8) * ((1 - 3 * a / 4) * Δ) :=
          mul_le_mul_of_nonneg_left hv (by linarith)
      _ ≤ (1 - 5 * a / 8) * Δ := by nlinarith
  have hΔ1 : Δ ≤ 1 / 2 ^ 20 := by nlinarith
  have haw1 : mixed C w (fun i => Real.log (w' i) - Real.log (w i)) ≤ 1 / 10 := by
    refine haw.trans ?_; nlinarith
  have hS := barS_pos hκ hx'
  have hdφ : ∀ i, |barDphi κ m x' i| ≤ barS κ m x' i := fun i => (eq_barrier hκ hx' i).1
  have hwm := eq_wmove (A := A) (c := c) hC hS hdφ t (fun i => exp_pos (X i))
    (fun i => exp_pos _) haw1
  set aw := mixed C w (fun i => Real.log (w' i) - Real.log (w i))
  have haw0 : 0 ≤ aw := mixed_nonneg hC.le _
  have hc0 : 0 ≤ cent C A (barS κ m x') (barDphi κ m x') c t w := cent_nonneg hC.le t w
  calc cent C A (barS κ m x') (barDphi κ m x') c t w'
      ≤ (1 + 4 * aw) * (cent C A (barS κ m x') (barDphi κ m x') c t w + aw) := hwm
    _ ≤ (1 + 4 * Δ) * (8 * Δ ^ 2 + 4 * η + (1 - 5 * a / 8) * Δ) := by
        apply mul_le_mul (by nlinarith) (add_le_add hcent haw) (by positivity) (by positivity)
    _ ≤ (1 - a / 2) * Δ := batch_cap_arith ha0 ha hΔ0 hΔ hη0 hη

end

end ImplicitLP
end CutQueryComplexity
