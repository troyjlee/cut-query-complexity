import CutQueryComplexity.ImplicitLP.Batch

/-! # The full batch invariant (`prop:batch` assembled, D7)

`prop_batch`: one support update `v` serves both the chase and the weight bound. Suppose the
invariants hold at `(x, X)`: `x` is strictly feasible, `δ_t(x, e^X) ≤ Δ`, and the potential
satisfies `Φ(X − log g(x)) ≤ B₀`, which with `μ⁻¹ log B₀ ≤ K` gives `‖X − log g(x)‖_∞ ≤ K`. Then:
* the primal step `x' = x + h + e` is strictly feasible (`batch_primal`);
* for an observation `z` within `Δ` of `log g(x')` and a sign-aligned, `σ`-optimal `v` in the
  ball `{N_w ≤ C_*}`, the potential invariant `Φ(X' − log g(x')) ≤ B₀` holds for
  `X' = X − (1+ξ)v` (`chase_invariant`, with the target move bounded by `batch_primal`);
* `δ_t(x', e^{X'}) ≤ (1 − 1/(2k))Δ` (`batch_weights`).

`batch_tchange`: a path-parameter move with `|t'/t − 1| ≤ α` and `αT₀ ≤ Δ/(16k)` then restores
`δ_{t'}(x', e^{X'}) ≤ Δ`, because `N_w(φ'/S) ≤ T₀`. The potential invariant and feasibility do
not depend on `t`, so the full batch invariant holds at `(x', X', t')`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Set

noncomputable section

variable {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c : Fin M → ℝ} {t : ℝ}

/-- **`prop:batch`**: the same support update preserves strict feasibility, the potential
invariant, and `eq:capmargin`. -/
theorem prop_batch (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) (hM : 1 ≤ M) {x : Fin M → ℝ} (hx : x ∈ Feasible A b κ m)
    {X : Fin M → ℝ} {Δ K η T₀ σ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ (1 / (2 * L₀)) ^ 2 / 2 ^ 16)
    (hK0 : 0 ≤ K) (hK : K ≤ 1 / (2 * L₀) / 2 ^ 20) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / (2 * L₀) * Δ / 2 ^ 16) (hT₀ : 1 ≤ T₀)
    (hT : ∀ v, mixed (48 * (2 * L₀)) (fun i => exp (X i)) v ≤ T₀ * ‖v‖)
    (hKμ : Real.log (12 * M * T₀ / (1 / (2 * L₀) / 8)) /
      ((1 / (2 * L₀) / 8) / (12 * Δ)) ≤ K)
    (hpot : pot ((1 / (2 * L₀) / 8) / (12 * Δ))
      (X - fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)) ≤
        12 * M * T₀ / (1 / (2 * L₀) / 8))
    (hδ : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t (fun i => exp (X i)) ≤ Δ)
    {e : Fin M → ℝ} (hAe : Aᵀ *ᵥ e = 0)
    (he : mixed (48 * (2 * L₀)) (fun i => exp (X i)) (fun i => barS κ m x i * e i) ≤ η)
    {z v : Fin M → ℝ}
    (hz : ∀ i, |z i - Real.log (gfun κ m (1 - 1 / L₀) c₀ A
      (x + (newtonDir A (fun i => exp (X i)) (barS κ m x)
        (fun i => t * c i + exp (X i) * barDphi κ m x i) + e)) i)| ≤ Δ)
    (hv : mixed (48 * (2 * L₀)) (fun i => exp (X i)) v ≤ (1 - 3 * (1 / (2 * L₀)) / 4) * Δ)
    (hal : ∀ i, 0 ≤ v i * (X i - z i)) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / (2 * L₀) / 8 / 1000)
    (hopt : supp {u | mixed (48 * (2 * L₀)) (fun i => exp (X i)) u ≤
        (1 - 3 * (1 / (2 * L₀)) / 4) * Δ}
        (potGrad ((1 / (2 * L₀) / 8) / (12 * Δ)) (X - z)) - σ ≤
      potGrad ((1 / (2 * L₀) / 8) / (12 * Δ)) (X - z) ⬝ᵥ v) :
    let w : Fin M → ℝ := fun i => exp (X i)
    let x' := x + (newtonDir A w (barS κ m x) (fun i => t * c i + w i * barDphi κ m x i) + e)
    let X' := X - (1 + 1 / (2 * L₀) / 8) • v
    x' ∈ Feasible A b κ m ∧
      pot ((1 / (2 * L₀) / 8) / (12 * Δ)) (X' - fun i => Real.log (gfun κ m (1 - 1 / L₀) c₀ A x' i))
        ≤ 12 * M * T₀ / (1 / (2 * L₀) / 8) ∧
      cent (48 * (2 * L₀)) A (barS κ m x') (barDphi κ m x') c t (fun i => exp (X' i)) ≤
        (1 - 1 / (2 * L₀) / 2) * Δ := by
  intro w x' X'
  set a : ℝ := 1 / (2 * L₀)
  set ξ : ℝ := a / 8
  set μ : ℝ := ξ / (12 * Δ)
  set C : ℝ := 48 * (2 * L₀)
  set Cs : ℝ := (1 - 3 * a / 4) * Δ
  set g := gfun κ m (1 - 1 / L₀) c₀ A
  have ha0 : 0 < a := by positivity
  have ha4 : a ≤ 1 / 4 := by
    simp only [a]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hξ0 : 0 < ξ := by positivity
  have hξ8 : ξ ≤ 1 / 8 := by simp only [ξ]; linarith
  have hμ0 : 0 < μ := by positivity
  have hC : 0 < C := by positivity
  have hw0 : ∀ i, 0 ≤ w i := fun i => (exp_pos _).le
  -- the potential gives the weight comparison
  have hXg : ∀ i, |X i - Real.log (g x i)| ≤ K := fun i => by
    have := pot_coord_bound hμ0 hpot i
    simp only [Pi.sub_apply] at this
    exact this.trans hKμ
  -- the primal half
  obtain ⟨hx', hcent', hmove⟩ :=
    batch_primal hA hrow hL hLM hκ hc₀ hcM hx hΔ0 hΔ hK0 hK hη0 hη hXg hδ hAe he
  refine ⟨hx', ?_, ?_⟩
  · -- the chase
    set y : Fin M → ℝ := fun i => Real.log (g x i)
    set u : Fin M → ℝ := fun i => Real.log (g x' i) - Real.log (g x i)
    have hCs4 : Δ / 4 ≤ Cs := by simp only [Cs]; nlinarith
    have hCsΔ : Cs ≤ Δ := by simp only [Cs]; nlinarith
    have hU := mixedBall_chaseSet (Cs := Cs) hC.le hw0 hT (by linarith) (by linarith)
    have hu : u ∈ {u | mixed C w u ≤ Cs} := by
      show mixed C w u ≤ Cs
      refine hmove.trans ?_
      simp only [Cs]; nlinarith
    have hz' : ∀ i, |z i - (y i + u i)| ≤ Δ := fun i => by
      have : y i + u i = Real.log (g x' i) := by simp only [y, u]; ring
      rw [this]; exact hz i
    have hM' : (1 : ℕ) ≤ M := hM
    have hinv := chase_invariant hU hΔ0 hξ0 hξ8 rfl hCs4 hCsΔ hT₀ hM' hσ0 hσ hu hz' hv hal hopt
      (by simpa [y] using hpot)
    have e1 : X' - (fun i => Real.log (g x' i)) = X - (1 + ξ) • v - (y + u) := by
      funext i; simp only [X', y, u, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1]; exact hinv
  · -- the weight half
    have hX' : (fun i => exp (X' i)) = fun i => exp (X i - (1 + a / 8) * v i) := by
      funext i; simp only [X', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; rfl
    rw [hX']
    have hres := batch_weights hC hκ hx'.2 ha0 ha4 hΔ0 hΔ hη0 hη hcent' hv
    simpa [a] using hres

/-- **The path-parameter move restores `δ ≤ Δ`** (`eq:tchange` after a batch). -/
theorem batch_tchange {C T₀ : ℝ} (hC : 0 < C) (hκ : ∀ i, 0 < κ i) {x w : Fin M → ℝ}
    (hx : Interior κ m x) (hw : ∀ i, 0 < w i) (hT0 : 0 ≤ T₀) (hT : ∀ v, mixed C w v ≤ T₀ * ‖v‖)
    {a Δ α t' : ℝ} (ht : 0 < t) (hα : |t' / t - 1| ≤ α) (ha : 0 < a)
    (hαT : α * T₀ ≤ a * Δ / 16)
    (hcap : cent C A (barS κ m x) (barDphi κ m x) c t w ≤ (1 - a / 2) * Δ) (hΔ0 : 0 < Δ)
    (hαΔ : α * Δ ≤ a * Δ / 16) :
    cent C A (barS κ m x) (barDphi κ m x) c t' w ≤ Δ := by
  have hS := barS_pos hκ hx
  have hdφ : ∀ i, |barDphi κ m x i| ≤ barS κ m x i := fun i => (eq_barrier hκ hx i).1
  have h1 := eq_tchange (A := A) (dφ := barDphi κ m x) (c := c) hC hS hw ht hα
  have hq : ‖fun i => barDphi κ m x i / barS κ m x i‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hS i), div_le_one (hS i)]; exact hdφ i
  have hα0 : 0 ≤ α := (abs_nonneg _).trans hα
  have h2 : mixed C w (fun i => barDphi κ m x i / barS κ m x i) ≤ T₀ :=
    (hT _).trans (by nlinarith [norm_nonneg (fun i => barDphi κ m x i / barS κ m x i)])
  have hc0 := cent_nonneg (A := A) (S := barS κ m x) (dφ := barDphi κ m x) (c := c) hC.le t w
  calc cent C A (barS κ m x) (barDphi κ m x) c t' w
      ≤ (1 + α) * cent C A (barS κ m x) (barDphi κ m x) c t w +
          α * mixed C w (fun i => barDphi κ m x i / barS κ m x i) := h1
    _ ≤ (1 + α) * ((1 - a / 2) * Δ) + α * T₀ :=
        add_le_add (mul_le_mul_of_nonneg_left hcap (by linarith))
          (mul_le_mul_of_nonneg_left h2 hα0)
    _ ≤ Δ := by
        have h4 : 0 ≤ α * (a / 2 * Δ) := by positivity
        have h3 : α * ((1 - a / 2) * Δ) ≤ α * Δ + α * (a / 2 * Δ) := by
          have : α * ((1 - a / 2) * Δ) = α * Δ - α * (a / 2 * Δ) := by ring
          linarith
        nlinarith

end

end ImplicitLP
end CutQueryComplexity
