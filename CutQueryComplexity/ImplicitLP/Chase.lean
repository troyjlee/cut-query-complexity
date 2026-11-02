import CutQueryComplexity.ImplicitLP.Movement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Chasing with an approximate support point (`lem:chase`, D7)

The potential is `Φ(v) = Σᵢ (e^{μvᵢ} + e^{−μvᵢ}) = Σᵢ 2 cosh(μvᵢ)` (`pot`), with gradient
`∇Φ(v)ᵢ = 2μ sinh(μvᵢ)` (`potGrad`). Because `Φ` is separable, the one-dimensional mean value
theorem suffices.

The scalar core (`sinh_shift_upper`, `sinh_shift_lower`) gives, for `|e| ≤ d`:
* `|sinh(x+e)| ≤ |sinh x| e^{|e|} + sinh|e|`;
* if `vx ≥ 0`, then `v sinh(x+e) ≥ (|sinh x| e^{−|e|} − sinh|e|)|v|`.

With `2 sinh|e| ≤ 4|e|` for `|e| ≤ 1`, these become the audited draft's gradient comparisons with additive
error `μ` once `μd ≤ 1/4`.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Finset Real

noncomputable section

/-- `cosh y + |sinh y| = e^{|y|}` and `cosh y − |sinh y| = e^{−|y|}`. -/
theorem cosh_add_abs_sinh (y : ℝ) : cosh y + |sinh y| = exp |y| ∧ cosh y - |sinh y| = exp (-|y|) := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (sinh_nonneg_iff.mpr h), cosh_eq, sinh_eq]
    constructor <;> ring
  · rw [abs_of_nonpos h, abs_of_nonpos (sinh_nonpos_iff.mpr h), cosh_eq, sinh_eq, neg_neg]
    constructor <;> ring

theorem cosh_le_abs_sinh_add_one (x : ℝ) : cosh x ≤ |sinh x| + 1 := by
  have := (cosh_add_abs_sinh x).2
  have h1 : exp (-|x|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg x])
  linarith

/-- `|sinh(x+e)| ≤ |sinh x| e^{|e|} + sinh|e|`. -/
theorem sinh_shift_upper (x e : ℝ) : |sinh (x + e)| ≤ |sinh x| * exp |e| + sinh |e| := by
  rw [sinh_add]
  have hc := cosh_le_abs_sinh_add_one x
  have hce := (cosh_add_abs_sinh e).1
  have hse : |sinh e| = sinh |e| := by
    rcases le_total 0 e with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (sinh_nonneg_iff.mpr h)]
    · rw [abs_of_nonpos h, abs_of_nonpos (sinh_nonpos_iff.mpr h), sinh_neg]
  calc |sinh x * cosh e + cosh x * sinh e| ≤ |sinh x| * cosh e + cosh x * |sinh e| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (cosh_pos e), abs_of_pos (cosh_pos x)]
    _ ≤ |sinh x| * cosh e + (|sinh x| + 1) * |sinh e| :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = |sinh x| * (cosh e + |sinh e|) + |sinh e| := by ring
    _ = |sinh x| * exp |e| + sinh |e| := by rw [hce, hse]

/-- Sign-aligned lower bound: if `v x ≥ 0` then
`v sinh(x+e) ≥ (|sinh x| e^{−|e|} − sinh|e|)|v|`. -/
theorem sinh_shift_lower {x e v : ℝ} (hvx : 0 ≤ v * x) :
    (|sinh x| * exp (-|e|) - sinh |e|) * |v| ≤ v * sinh (x + e) := by
  rw [sinh_add]
  have hc := cosh_le_abs_sinh_add_one x
  have hce := (cosh_add_abs_sinh e).2
  have hse : |sinh e| = sinh |e| := by
    rcases le_total 0 e with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (sinh_nonneg_iff.mpr h)]
    · rw [abs_of_nonpos h, abs_of_nonpos (sinh_nonpos_iff.mpr h), sinh_neg]
  -- `v sinh x = |v| |sinh x|`
  have hvs : v * sinh x = |v| * |sinh x| := by
    rcases le_total 0 x with h | h
    · have hv : 0 ≤ v ∨ x = 0 := by
        rcases eq_or_lt_of_le h with h0 | h0
        · exact Or.inr h0.symm
        · exact Or.inl (nonneg_of_mul_nonneg_left hvx h0)
      rcases hv with hv | hv
      · rw [abs_of_nonneg hv, abs_of_nonneg (sinh_nonneg_iff.mpr h)]
      · simp [hv]
    · have hv : v ≤ 0 ∨ x = 0 := by
        rcases eq_or_lt_of_le h with h0 | h0
        · exact Or.inr h0
        · left; nlinarith
      rcases hv with hv | hv
      · rw [abs_of_nonpos hv, abs_of_nonpos (sinh_nonpos_iff.mpr h)]; ring
      · simp [hv]
  have hterm : -(cosh x * |sinh e| * |v|) ≤ v * (cosh x * sinh e) := by
    have : |v * (cosh x * sinh e)| = cosh x * |sinh e| * |v| := by
      rw [abs_mul, abs_mul, abs_of_pos (cosh_pos x)]; ring
    linarith [neg_abs_le (v * (cosh x * sinh e))]
  calc (|sinh x| * exp (-|e|) - sinh |e|) * |v|
      = |v| * |sinh x| * (cosh e - |sinh e|) - |sinh e| * |v| := by rw [hce, hse]; ring
    _ ≤ |v| * |sinh x| * cosh e - (cosh x * |sinh e| * |v|) := by
        have := mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg (sinh e)) (abs_nonneg v))
        nlinarith [abs_nonneg v, abs_nonneg (sinh x), abs_nonneg (sinh e)]
    _ ≤ v * (sinh x * cosh e + cosh x * sinh e) := by
        rw [mul_add, ← mul_assoc, hvs]; linarith
    _ = v * (sinh x * cosh e + cosh x * sinh e) := rfl

/-- `2 sinh y ≤ 4y` for `0 ≤ y ≤ 1`. -/
theorem two_sinh_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 2 * sinh y ≤ 4 * y := by
  rw [sinh_eq]
  have h1 := abs_exp_sub_one_sub_id_le (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
  rw [abs_le] at h1
  have h2 : 0 < exp (-y) := exp_pos _
  have h3 : 1 - y ≤ exp (-y) := by linarith [add_one_le_exp (-y)]
  nlinarith

section Potential

variable {M : ℕ} {μ : ℝ}

/-- The potential `Φ(v) = Σᵢ 2 cosh(μvᵢ)`. -/
def pot (μ : ℝ) (v : Fin M → ℝ) : ℝ := ∑ i, 2 * cosh (μ * v i)

/-- Its gradient `∇Φ(v)ᵢ = 2μ sinh(μvᵢ)`. -/
def potGrad (μ : ℝ) (v : Fin M → ℝ) : Fin M → ℝ := fun i => 2 * μ * sinh (μ * v i)

/-- **Gradient comparison, upper:** `|∇Φ(a)| ≤ e^{μd}|∇Φ(b)| + μ` for `|a − b| ≤ d`,
`μd ≤ 1/4`. -/
theorem grad_upper (hμ : 0 < μ) {d a b : ℝ} (hd : μ * d ≤ 1 / 4) (hab : |a - b| ≤ d) :
    |2 * μ * sinh (μ * a)| ≤ exp (μ * d) * |2 * μ * sinh (μ * b)| + μ := by
  have he : |μ * (a - b)| ≤ μ * d := by rw [abs_mul, abs_of_pos hμ]; exact mul_le_mul_of_nonneg_left hab hμ.le
  have h := sinh_shift_upper (μ * b) (μ * (a - b))
  rw [show μ * b + μ * (a - b) = μ * a by ring] at h
  have h2 := two_sinh_le (abs_nonneg (μ * (a - b))) (by linarith)
  have h3 : exp |μ * (a - b)| ≤ exp (μ * d) := exp_le_exp.mpr he
  rw [abs_mul (2 * μ) (sinh (μ * a)), abs_of_pos (by positivity : (0 : ℝ) < 2 * μ)]
  calc 2 * μ * |sinh (μ * a)| ≤ 2 * μ * (|sinh (μ * b)| * exp |μ * (a - b)| + sinh |μ * (a - b)|) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ exp (μ * d) * (2 * μ * |sinh (μ * b)|) + μ := by
        have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * μ * |sinh (μ * b)|)
        nlinarith
    _ = exp (μ * d) * |2 * μ * sinh (μ * b)| + μ := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * μ)]

/-- **Gradient comparison, sign-aligned lower:** if `vb ≥ 0` then
`(e^{−μd}|∇Φ(b)| − μ)|v| ≤ v ∇Φ(a)`. -/
theorem grad_lower (hμ : 0 < μ) {d a b v : ℝ} (hd : μ * d ≤ 1 / 4) (hab : |a - b| ≤ d)
    (hvb : 0 ≤ v * b) :
    (exp (-(μ * d)) * |2 * μ * sinh (μ * b)| - μ) * |v| ≤ v * (2 * μ * sinh (μ * a)) := by
  have he : |μ * (a - b)| ≤ μ * d := by rw [abs_mul, abs_of_pos hμ]; exact mul_le_mul_of_nonneg_left hab hμ.le
  have hvx : 0 ≤ v * (μ * b) := by nlinarith
  have h := sinh_shift_lower (e := μ * (a - b)) hvx
  rw [show μ * b + μ * (a - b) = μ * a by ring] at h
  have h2 := two_sinh_le (abs_nonneg (μ * (a - b))) (by linarith)
  have h3 : exp (-(μ * d)) ≤ exp (-|μ * (a - b)|) := exp_le_exp.mpr (by linarith)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * μ)]
  have hv := abs_nonneg v
  have hs := abs_nonneg (sinh (μ * b))
  calc (exp (-(μ * d)) * (2 * μ * |sinh (μ * b)|) - μ) * |v|
      ≤ 2 * μ * ((|sinh (μ * b)| * exp (-|μ * (a - b)|) - sinh |μ * (a - b)|) * |v|) := by
        have := mul_le_mul_of_nonneg_left h3 (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * μ * |sinh (μ * b)|) hv)
        nlinarith [mul_nonneg hμ.le hv]
    _ ≤ 2 * μ * (v * sinh (μ * a)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = v * (2 * μ * sinh (μ * a)) := by ring

/-- `μ(2 cosh(μb) − 2) ≤ |2μ sinh(μb)|`. -/
theorem pot_le_grad (hμ : 0 < μ) (b : ℝ) : μ * (2 * cosh (μ * b) - 2) ≤ |2 * μ * sinh (μ * b)| := by
  have h := cosh_le_abs_sinh_add_one (μ * b)
  rw [abs_mul (2 * μ), abs_of_pos (by positivity : (0 : ℝ) < 2 * μ)]
  nlinarith [mul_le_mul_of_nonneg_left h hμ.le]

/-- **Mean value theorem for one coordinate of `Φ`.** -/
theorem cosh_mvt (a a' : ℝ) :
    ∃ ζ, |ζ - a| ≤ |a' - a| ∧ 2 * cosh (μ * a') - 2 * cosh (μ * a) = 2 * μ * sinh (μ * ζ) * (a' - a) := by
  have hD : ∀ x, HasDerivAt (fun x => 2 * cosh (μ * x)) (2 * μ * sinh (μ * x)) x := fun x => by
    have := ((hasDerivAt_id x).const_mul μ).cosh.const_mul 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  rcases lt_trichotomy a a' with h | h | h
  · obtain ⟨ζ, hζ, he⟩ := exists_hasDerivAt_eq_slope (fun x => 2 * cosh (μ * x))
      (fun x => 2 * μ * sinh (μ * x)) h (fun x _ => (hD x).continuousAt.continuousWithinAt)
      (fun x _ => hD x)
    refine ⟨ζ, ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hζ.1]), abs_of_pos (by linarith)]; linarith [hζ.2]
    · rw [he]; field_simp [show a' - a ≠ 0 by linarith]
  · subst h; exact ⟨a, by simp, by simp⟩
  · obtain ⟨ζ, hζ, he⟩ := exists_hasDerivAt_eq_slope (fun x => 2 * cosh (μ * x))
      (fun x => 2 * μ * sinh (μ * x)) h (fun x _ => (hD x).continuousAt.continuousWithinAt)
      (fun x _ => hD x)
    refine ⟨ζ, ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hζ.2]), abs_of_neg (by linarith)]; linarith [hζ.1]
    · have : 2 * cosh (μ * a) - 2 * cosh (μ * a') = 2 * μ * sinh (μ * ζ) * (a - a') := by
        rw [he]; field_simp [show a - a' ≠ 0 by linarith]
      linarith

end Potential

section Support

variable {M : ℕ}

/-- The support function `h_U(q) = sup_{v ∈ U} ⟨q, v⟩`. -/
def supp (U : Set (Fin M → ℝ)) (q : Fin M → ℝ) : ℝ := sSup ((fun v => q ⬝ᵥ v) '' U)

/-- The geometry of the chasing set: solid (`|v'| ≤ |v|` coordinatewise and `v ∈ U` imply
`v' ∈ U`), containing the cube of radius `C/T₀`, and contained in the cube of radius `C`. -/
structure ChaseSet (U : Set (Fin M → ℝ)) (C T₀ : ℝ) : Prop where
  solid : ∀ v ∈ U, ∀ v' : Fin M → ℝ, (∀ i, |v' i| ≤ |v i|) → v' ∈ U
  inner : ∀ v : Fin M → ℝ, (∀ i, |v i| ≤ C / T₀) → v ∈ U
  outer : ∀ v ∈ U, ∀ i, |v i| ≤ C

variable {U : Set (Fin M → ℝ)} {C T₀ : ℝ}

theorem ChaseSet.bdd (hU : ChaseSet U C T₀) (q : Fin M → ℝ) :
    BddAbove ((fun v => q ⬝ᵥ v) '' U) := by
  refine ⟨∑ i, |q i| * C, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  refine (le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_))
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hU.outer v hv i) (abs_nonneg _)

theorem ChaseSet.le_supp (hU : ChaseSet U C T₀) (q : Fin M → ℝ) {v : Fin M → ℝ} (hv : v ∈ U) :
    q ⬝ᵥ v ≤ supp U q :=
  le_csSup (hU.bdd q) ⟨v, hv, rfl⟩

theorem ChaseSet.nonempty (hU : ChaseSet U C T₀) (hC : 0 ≤ C / T₀) : U.Nonempty :=
  ⟨0, hU.inner 0 fun i => by simpa using hC⟩

theorem ChaseSet.supp_le (hU : ChaseSet U C T₀) (hC : 0 ≤ C / T₀) (q : Fin M → ℝ) {B : ℝ}
    (h : ∀ v ∈ U, q ⬝ᵥ v ≤ B) : supp U q ≤ B :=
  csSup_le ((hU.nonempty hC).image _) (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)

/-- `Σᵢ |qᵢ||vᵢ| ≤ h_U(q)` for `v ∈ U` (solidity). -/
theorem ChaseSet.abs_le_supp (hU : ChaseSet U C T₀) (q : Fin M → ℝ) {v : Fin M → ℝ}
    (hv : v ∈ U) : ∑ i, |q i| * |v i| ≤ supp U q := by
  set v' : Fin M → ℝ := fun i => if 0 ≤ q i then |v i| else -|v i|
  have hv' : v' ∈ U := hU.solid v hv v' fun i => by simp only [v']; split_ifs <;> simp
  have : q ⬝ᵥ v' = ∑ i, |q i| * |v i| := by
    simp only [dotProduct, v']
    exact sum_congr rfl fun i _ => by
      split_ifs with h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
  rw [← this]; exact hU.le_supp q hv'

/-- `h_U(q) ≥ (C/T₀) Σᵢ |qᵢ|` (the contained cube). -/
theorem ChaseSet.cube_le_supp (hU : ChaseSet U C T₀) (hC : 0 ≤ C / T₀) (q : Fin M → ℝ) :
    C / T₀ * ∑ i, |q i| ≤ supp U q := by
  have hv : (fun _ : Fin M => C / T₀) ∈ U := hU.inner _ fun i => by rw [abs_of_nonneg hC]
  have := hU.abs_le_supp q hv
  simp only [abs_of_nonneg hC] at this
  rw [mul_sum]; refine le_trans (le_of_eq ?_) this
  exact sum_congr rfl fun i _ => by ring

/-- **Support comparison:** `h_U(∇Φ(a)) ≤ e^{μd} h_U(∇Φ(b)) + μ M C` for `‖a − b‖_∞ ≤ d`,
`μd ≤ 1/4`. -/
theorem ChaseSet.supp_compare (hU : ChaseSet U C T₀) (hC : 0 ≤ C / T₀) {μ d : ℝ} (hμ : 0 < μ)
    (hd : μ * d ≤ 1 / 4) {a b : Fin M → ℝ} (hab : ∀ i, |a i - b i| ≤ d) :
    supp U (potGrad μ a) ≤ exp (μ * d) * supp U (potGrad μ b) + μ * M * C := by
  refine hU.supp_le hC _ fun v hv => ?_
  have h1 : potGrad μ a ⬝ᵥ v ≤ ∑ i, (exp (μ * d) * |potGrad μ b i| + μ) * |v i| := by
    refine (le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (grad_upper hμ hd (hab i)) (abs_nonneg _)
  have h2 : ∑ i, (exp (μ * d) * |potGrad μ b i| + μ) * |v i| =
      exp (μ * d) * ∑ i, |potGrad μ b i| * |v i| + μ * ∑ i, |v i| := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  have h3 := hU.abs_le_supp (potGrad μ b) hv
  have h4 : ∑ i, |v i| ≤ M * C := by
    calc ∑ i, |v i| ≤ ∑ _i : Fin M, C := sum_le_sum fun i _ => hU.outer v hv i
      _ = M * C := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h2] at h1
  nlinarith [exp_pos (μ * d)]

end Support

section Chase

variable {M : ℕ} {U : Set (Fin M → ℝ)} {Cs T₀ : ℝ}

set_option maxHeartbeats 1600000 in
/-- **`lem:chase`**: chasing a moving target with an approximate, sign-aligned support point.
With `μΔ = ξ/12`, `0 < ξ ≤ 1/8`, `0 ≤ C_* ≤ Δ`, `T₀ ≥ 1`, a target move `u ∈ U`, an observation `z`
within `Δ` of the new target, and `v ∈ U` sign-aligned with `q = ∇Φ(X − z)` and `σ`-optimal, the
update `X' = X − (1+ξ)v` satisfies
`Φ(X' − y') ≤ (1 − λ)Φ(X − y) + ξMC_*/(3Δ) + 2σ` with `λ = ξ²C_*/(30ΔT₀)`. -/
theorem lem_chase (hU : ChaseSet U Cs T₀) {μ Δ ξ σ : ℝ} (hΔ : 0 < Δ) (hξ : 0 < ξ)
    (hξ8 : ξ ≤ 1 / 8) (hμ : μ = ξ / (12 * Δ)) (hCs0 : 0 ≤ Cs) (hCsΔ : Cs ≤ Δ) (hT₀ : 1 ≤ T₀)
    (hσ0 : 0 ≤ σ) {X y u z v : Fin M → ℝ} (hu : u ∈ U) (hz : ∀ i, |z i - (y i + u i)| ≤ Δ)
    (hv : v ∈ U) (hal : ∀ i, 0 ≤ v i * (X i - z i))
    (hopt : supp U (potGrad μ (X - z)) - σ ≤ potGrad μ (X - z) ⬝ᵥ v) :
    pot μ (X - (1 + ξ) • v - (y + u)) ≤
      (1 - ξ ^ 2 * Cs / (30 * Δ * T₀)) * pot μ (X - y) + ξ * M * Cs / (3 * Δ) + 2 * σ := by
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hμΔ : μ * Δ = ξ / 12 := by rw [hμ]; field_simp
  have hCT : 0 ≤ Cs / T₀ := div_nonneg hCs0 (by linarith)
  set H := supp U (potGrad μ (X - y))
  set q := potGrad μ (X - z)
  have hMC : ∀ w ∈ U, ∑ i, |w i| ≤ M * Cs := fun w hw => by
    calc ∑ i, |w i| ≤ ∑ _i : Fin M, Cs := sum_le_sum fun i _ => hU.outer w hw i
      _ = M * Cs := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the target move
  have hT : pot μ (X - (y + u)) - pot μ (X - y) ≤ exp (μ * Δ) * H + μ * (M * Cs) := by
    have hζ : ∀ i, ∃ ζ, |ζ - (X - y) i| ≤ |(X - (y + u)) i - (X - y) i| ∧
        2 * cosh (μ * (X - (y + u)) i) - 2 * cosh (μ * (X - y) i) =
          2 * μ * sinh (μ * ζ) * ((X - (y + u)) i - (X - y) i) := fun i => cosh_mvt _ _
    choose ζ hζd hζe using hζ
    have hdiff : pot μ (X - (y + u)) - pot μ (X - y) =
        ∑ i, 2 * μ * sinh (μ * ζ i) * ((X - (y + u)) i - (X - y) i) := by
      simp only [pot, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => hζe i
    rw [hdiff]
    have hstep : ∀ i, 2 * μ * sinh (μ * ζ i) * ((X - (y + u)) i - (X - y) i) ≤
        (exp (μ * Δ) * |potGrad μ (X - y) i| + μ) * |u i| := fun i => by
      have he : (X - (y + u)) i - (X - y) i = -u i := by simp only [Pi.sub_apply, Pi.add_apply]; ring
      have hd : |ζ i - (X - y) i| ≤ Δ := by
        have := hζd i; rw [he, abs_neg] at this; exact this.trans ((hU.outer u hu i).trans hCsΔ)
      have hg := grad_upper hμ0 (by linarith) hd
      rw [he]
      calc 2 * μ * sinh (μ * ζ i) * -u i ≤ |2 * μ * sinh (μ * ζ i)| * |u i| := by
            rw [← abs_neg (u i), ← abs_mul]; exact le_abs_self _
        _ ≤ (exp (μ * Δ) * |potGrad μ (X - y) i| + μ) * |u i| :=
            mul_le_mul_of_nonneg_right hg (abs_nonneg _)
    refine (sum_le_sum fun i _ => hstep i).trans ?_
    have e : ∑ i, (exp (μ * Δ) * |potGrad μ (X - y) i| + μ) * |u i| =
        exp (μ * Δ) * ∑ i, |potGrad μ (X - y) i| * |u i| + μ * ∑ i, |u i| := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [e]
    have := hU.abs_le_supp (potGrad μ (X - y)) hu
    have h2 := hMC u hu
    nlinarith [exp_pos (μ * Δ)]
  -- the player move
  set p := X - (y + u)
  have hpz : ∀ i, |p i - (X - z) i| ≤ Δ := fun i => by
    have : p i - (X - z) i = z i - (y i + u i) := by simp only [p, Pi.sub_apply, Pi.add_apply]; ring
    rw [this]; exact hz i
  have hP : pot μ (X - (1 + ξ) • v - (y + u)) - pot μ p ≤
      -((1 + ξ) * (exp (-(3 * μ * Δ)) * (q ⬝ᵥ v) - μ * (M * Cs))) := by
    have hζ : ∀ i, ∃ ζ, |ζ - p i| ≤ |(X - (1 + ξ) • v - (y + u)) i - p i| ∧
        2 * cosh (μ * (X - (1 + ξ) • v - (y + u)) i) - 2 * cosh (μ * p i) =
          2 * μ * sinh (μ * ζ) * ((X - (1 + ξ) • v - (y + u)) i - p i) := fun i => cosh_mvt _ _
    choose ζ hζd hζe using hζ
    have he : ∀ i, (X - (1 + ξ) • v - (y + u)) i - p i = -((1 + ξ) * v i) := fun i => by
      simp only [p, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hdiff : pot μ (X - (1 + ξ) • v - (y + u)) - pot μ p =
        -((1 + ξ) * ∑ i, v i * (2 * μ * sinh (μ * ζ i))) := by
      simp only [pot, ← sum_sub_distrib, mul_sum, ← sum_neg_distrib]
      exact sum_congr rfl fun i _ => by rw [hζe i, he i]; ring
    rw [hdiff]
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have hstep : ∀ i, (exp (-(μ * (3 * Δ))) * |q i| - μ) * |v i| ≤ v i * (2 * μ * sinh (μ * ζ i)) :=
      fun i => by
        have hd : |ζ i - (X - z) i| ≤ 3 * Δ := by
          have h1 := hζd i
          rw [he i, abs_neg, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + ξ)] at h1
          have h2 := hU.outer v hv i
          have h3 := hpz i
          calc |ζ i - (X - z) i| ≤ |ζ i - p i| + |p i - (X - z) i| := abs_sub_le _ _ _
            _ ≤ (1 + ξ) * |v i| + Δ := add_le_add h1 h3
            _ ≤ (1 + 1) * Δ + Δ := by nlinarith [abs_nonneg (v i)]
            _ = 3 * Δ := by ring
        exact grad_lower hμ0 (by nlinarith) hd (by simpa [Pi.sub_apply] using hal i)
    have hsum := sum_le_sum fun i (_ : i ∈ Finset.univ) => hstep i
    have e : ∑ i, (exp (-(μ * (3 * Δ))) * |q i| - μ) * |v i| =
        exp (-(μ * (3 * Δ))) * ∑ i, |q i| * |v i| - μ * ∑ i, |v i| := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [e] at hsum
    have hqv : q ⬝ᵥ v ≤ ∑ i, |q i| * |v i| := by
      refine (le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans (le_of_eq ?_))
      exact sum_congr rfl fun i _ => abs_mul _ _
    have h2 := hMC v hv
    have h3 : exp (-(3 * μ * Δ)) = exp (-(μ * (3 * Δ))) := by ring_nf
    rw [h3]
    nlinarith [exp_pos (-(μ * (3 * Δ)))]
  -- the observed support value
  have hcmp := hU.supp_compare hCT (d := 2 * Δ) hμ0 (by nlinarith) (a := X - y) (b := X - z)
    fun i => by
      have : (X - y) i - (X - z) i = (z i - (y i + u i)) + u i := by
        simp only [Pi.sub_apply]; ring
      rw [this]
      exact (abs_add_le _ _).trans (by linarith [hz i, (hU.outer u hu i).trans hCsΔ])
  -- `h_U(q) ≥ e^{−2μΔ}(H − μMC_*)`
  have hsupq : exp (-(2 * μ * Δ)) * (H - μ * M * Cs) ≤ supp U q := by
    have h1 : H - μ * M * Cs ≤ exp (μ * (2 * Δ)) * supp U q := by linarith [hcmp]
    have h2 := mul_le_mul_of_nonneg_left h1 (exp_pos (-(2 * μ * Δ))).le
    have h3 : exp (-(2 * μ * Δ)) * (exp (μ * (2 * Δ)) * supp U q) = supp U q := by
      rw [← mul_assoc, ← exp_add, show -(2 * μ * Δ) + μ * (2 * Δ) = 0 by ring, exp_zero, one_mul]
    linarith
  -- numeric close
  set x := μ * Δ with hxdef
  have hx : x = ξ / 12 := hμΔ
  have hH0 : 0 ≤ H := le_trans (mul_nonneg hCT (sum_nonneg fun i _ => abs_nonneg _))
    (hU.cube_le_supp hCT _)
  have hHpot : Cs / T₀ * (μ * (pot μ (X - y) - 2 * M)) ≤ H := by
    refine le_trans ?_ (hU.cube_le_supp hCT _)
    apply mul_le_mul_of_nonneg_left _ hCT
    have : μ * (pot μ (X - y) - 2 * M) = ∑ i, μ * (2 * cosh (μ * (X - y) i) - 2) := by
      simp only [pot, mul_sub, sum_sub_distrib, mul_sum, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    rw [this]
    exact sum_le_sum fun i _ => pot_le_grad hμ0 _
  set E1 := exp x
  set E3 := exp (-(3 * μ * Δ))
  set E5 := exp (-(5 * x))
  have hE35 : E3 * exp (-(2 * μ * Δ)) = E5 := by
    simp only [E3, E5, hxdef, ← exp_add]; ring_nf
  have hE1 : E1 ≤ 1 + x + x ^ 2 := by
    have := abs_exp_sub_one_sub_id_le (x := x) (by rw [hx, abs_of_pos (by positivity)]; linarith)
    rw [abs_le] at this; linarith
  have hE5lo : 1 - 5 * x ≤ E5 := by linarith [add_one_le_exp (-(5 * x))]
  have hE5 : E5 ≤ 1 := exp_le_one_iff.mpr (by rw [hx]; linarith)
  have hE3 : E3 ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hE3pos : 0 < E3 := exp_pos _
  -- A and B
  have hA := add_le_add hT hP
  have hB : exp (-(2 * μ * Δ)) * (H - μ * M * Cs) - σ ≤ q ⬝ᵥ v := by
    have h1 : supp U q - σ ≤ q ⬝ᵥ v := hopt
    linarith only [hsupq, h1]
  have hC : E5 * (H - μ * M * Cs) - E3 * σ ≤ E3 * (q ⬝ᵥ v) := by
    have := mul_le_mul_of_nonneg_left hB hE3pos.le
    rw [mul_sub, ← mul_assoc, hE35] at this; linarith
  -- the coefficient of `H`
  have hcoef : E1 - (1 + ξ) * E5 ≤ -(2 * ξ / 5) := by
    have : (1 + ξ) * (1 - 5 * x) ≤ (1 + ξ) * E5 := mul_le_mul_of_nonneg_left hE5lo (by linarith)
    rw [hx] at hE1 this
    nlinarith
  have hMC0 : 0 ≤ μ * (M * Cs) := by positivity
  have hF : pot μ (X - (1 + ξ) • v - (y + u)) - pot μ (X - y) ≤
      -(2 * ξ / 5) * H + (3 + 2 * ξ) * (μ * (M * Cs)) + 2 * σ := by
    have h1 : (E1 - (1 + ξ) * E5) * H ≤ -(2 * ξ / 5) * H := mul_le_mul_of_nonneg_right hcoef hH0
    have h2 : (1 + ξ) * E5 * (μ * (M * Cs)) ≤ (1 + ξ) * (μ * (M * Cs)) :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by linarith) hE5) hMC0
    have h3 : (1 + ξ) * (E3 * σ) ≤ 2 * σ := by
      have h4 : E3 * σ ≤ σ := mul_le_of_le_one_left hσ0 hE3
      have h5 : (1 + ξ) * (E3 * σ) ≤ (1 + ξ) * σ := mul_le_mul_of_nonneg_left h4 (by linarith)
      nlinarith
    have hmul : (1 + ξ) * (E5 * (H - μ * M * Cs) - E3 * σ) ≤ (1 + ξ) * (E3 * (q ⬝ᵥ v)) :=
      mul_le_mul_of_nonneg_left hC (by linarith)
    have : pot μ (X - (1 + ξ) • v - (y + u)) - pot μ (X - y) ≤
        E1 * H + μ * (M * Cs) - (1 + ξ) * (E3 * (q ⬝ᵥ v) - μ * (M * Cs)) := by linarith
    nlinarith
  -- `H ≥ (C_*/T₀) μ (Φ − 2M)` and the final constants
  have hT0 : 0 < T₀ := by linarith
  have hlam : 2 * ξ / 5 * (Cs / T₀ * μ) = ξ ^ 2 * Cs / (30 * Δ * T₀) := by
    rw [hμ]; field_simp; ring
  have hadd : 2 * M * (ξ ^ 2 * Cs / (30 * Δ * T₀)) + (3 + 2 * ξ) * (μ * (M * Cs)) ≤
      ξ * M * Cs / (3 * Δ) := by
    rw [hμ]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hk : ξ * M * Cs / Δ ≥ 0 := by positivity
    have e1 : 2 * M * (ξ ^ 2 * Cs / (30 * Δ * T₀)) = ξ / (15 * T₀) * (ξ * M * Cs / Δ) := by
      field_simp; ring
    have e2 : (3 + 2 * ξ) * (ξ / (12 * Δ) * (M * Cs)) = (3 + 2 * ξ) / 12 * (ξ * M * Cs / Δ) := by
      field_simp
    have e3 : ξ * M * Cs / (3 * Δ) = 1 / 3 * (ξ * M * Cs / Δ) := by field_simp
    rw [e1, e2, e3]
    have h1 : ξ / (15 * T₀) ≤ 1 / 120 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : (3 + 2 * ξ) / 12 ≤ 13 / 48 := by linarith
    nlinarith
  have hfinal : -(2 * ξ / 5) * H ≤
      -(ξ ^ 2 * Cs / (30 * Δ * T₀)) * pot μ (X - y) + 2 * M * (ξ ^ 2 * Cs / (30 * Δ * T₀)) := by
    have := mul_le_mul_of_nonneg_left hHpot (by positivity : (0 : ℝ) ≤ 2 * ξ / 5)
    rw [← hlam]
    nlinarith
  nlinarith

/-- **The potential invariant is preserved** (`lem:chase`, last clause): with
`B₀ = 12MT₀/ξ`, `C_* ≥ Δ/4`, `M ≥ 1` and `σ ≤ ξ/1000`, `Φ(X − y) ≤ B₀` implies `Φ(X' − y') ≤ B₀`. -/
theorem chase_invariant (hU : ChaseSet U Cs T₀) {μ Δ ξ σ : ℝ} (hΔ : 0 < Δ) (hξ : 0 < ξ)
    (hξ8 : ξ ≤ 1 / 8) (hμ : μ = ξ / (12 * Δ)) (hCs4 : Δ / 4 ≤ Cs) (hCsΔ : Cs ≤ Δ)
    (hT₀ : 1 ≤ T₀) (hM : 1 ≤ M) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ξ / 1000) {X y u z v : Fin M → ℝ}
    (hu : u ∈ U) (hz : ∀ i, |z i - (y i + u i)| ≤ Δ) (hv : v ∈ U)
    (hal : ∀ i, 0 ≤ v i * (X i - z i))
    (hopt : supp U (potGrad μ (X - z)) - σ ≤ potGrad μ (X - z) ⬝ᵥ v)
    (hB : pot μ (X - y) ≤ 12 * M * T₀ / ξ) :
    pot μ (X - (1 + ξ) • v - (y + u)) ≤ 12 * M * T₀ / ξ := by
  have hCs0 : 0 ≤ Cs := by linarith
  have h := lem_chase hU hΔ hξ hξ8 hμ hCs0 hCsΔ hT₀ hσ0 hu hz hv hal hopt
  set lam := ξ ^ 2 * Cs / (30 * Δ * T₀)
  have hT0 : 0 < T₀ := by linarith
  have hlam1 : lam ≤ 1 := by
    simp only [lam]
    rw [div_le_one (by positivity)]
    have e1 := mul_le_mul_of_nonneg_left hCsΔ (sq_nonneg ξ)
    have e2 : ξ ^ 2 ≤ 1 := by nlinarith
    have e3 : ξ ^ 2 * Δ ≤ Δ := by nlinarith
    have e4 : Δ ≤ 30 * Δ * T₀ := by nlinarith
    linarith
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlamB : lam * (12 * M * T₀ / ξ) = 2 * ξ * M * Cs / (5 * Δ) := by
    simp only [lam]; field_simp; ring
  have hσ' : 2 * σ ≤ ξ * M * Cs / (15 * Δ) := by
    rw [le_div_iff₀ (by positivity)]
    have hMC : 1 * (Δ / 4) ≤ M * Cs := mul_le_mul hM' hCs4 (by positivity) (by positivity)
    have e1 := mul_le_mul_of_nonneg_left hMC hξ.le
    have e2 := mul_le_mul_of_nonneg_right hσ (by positivity : (0 : ℝ) ≤ 30 * Δ)
    nlinarith
  have h1 : (1 - lam) * pot μ (X - y) ≤ (1 - lam) * (12 * M * T₀ / ξ) :=
    mul_le_mul_of_nonneg_left hB (by linarith)
  have h2 : ξ * M * Cs / (3 * Δ) + ξ * M * Cs / (15 * Δ) = 2 * ξ * M * Cs / (5 * Δ) := by
    field_simp; ring
  nlinarith

end Chase

end

end ImplicitLP
end CutQueryComplexity
