import CutQueryComplexity.ImplicitLP.Movement
import Mathlib.Topology.MetricSpace.Bounded

/-! # The support problem: normalization and the value function (`lem:support`, D7)

The support problem `max{⟨q, v⟩ : N_w(v) ≤ C_*}` is rescaled with
`z = (C_N/C_*) W^{1/2} v`, `κᵢ = C_N √wᵢ`, and `aᵢ = C_* qᵢ/(C_N √wᵢ)` to
`max aᵀz` subject to `‖z‖₂ + ‖κ⁻¹z‖_∞ ≤ 1` (`support_normalize`). Here `‖·‖₂` is `euc = wnorm 1`;
the plain norm on `Fin M → ℝ` is the sup norm.

Splitting the constraint at `τ = ‖κ⁻¹z‖_∞` (`split_iff`) gives the parametrized sets
`F(τ) = {‖z‖₂ ≤ 1 − τ, |zᵢ| ≤ τκᵢ}`. With the regularized objective
`f_ρ(z) = aᵀz − ρ‖z‖₂²`, the value function `G_ρ(τ) = max_{F(τ)} f_ρ` satisfies:
* attainment (`exists_max`), since `F(τ)` is compact and nonempty;
* concavity (`G_concave`), by interpolating maximizers;
* `0 ≤ G(τ) ≤ min{‖a‖₂(1 − τ), τ Σ|aᵢ|κᵢ}` (`G_le_euc`, `G_le_box`);
* the Lipschitz bound `G(τ) ≤ G(τ') + L|τ − τ'|` with `L = max{‖a‖₂, Σ|aᵢ|κᵢ}` (`G_lipschitz`),
  by scaling, since `f_ρ(cz) ≥ c f_ρ(z)` for `c ∈ [0,1]`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Finset Real Set

noncomputable section

variable {M : ℕ}

/-- The Euclidean norm `‖z‖₂`. -/
def euc (z : Fin M → ℝ) : ℝ := wnorm (fun _ => 1) z

theorem euc_nonneg (z : Fin M → ℝ) : 0 ≤ euc z := wnorm_nonneg _ _

theorem euc_sq (z : Fin M → ℝ) : euc z ^ 2 = ∑ i, z i ^ 2 := by
  rw [euc, wnorm_sq (fun _ => zero_le_one)]; simp

theorem euc_smul (c : ℝ) (z : Fin M → ℝ) : euc (c • z) = |c| * euc z := wnorm_smul c z

theorem euc_add_le (x y : Fin M → ℝ) : euc (x + y) ≤ euc x + euc y :=
  wnorm_add_le (fun _ => zero_le_one) x y

/-- Cauchy–Schwarz: `aᵀz ≤ ‖a‖₂‖z‖₂`. -/
theorem dot_le_euc (a z : Fin M → ℝ) : a ⬝ᵥ z ≤ euc a * euc z := by
  have h := sum_mul_sq_le_sq_mul_sq univ a z
  rw [← euc_sq, ← euc_sq, ← mul_pow] at h
  exact (abs_le_of_sq_le_sq' h (mul_nonneg (euc_nonneg a) (euc_nonneg z))).2

theorem continuous_euc : Continuous (euc (M := M)) := continuous_wnorm

/-- The regularized objective `f_ρ(z) = aᵀz − ρ‖z‖₂²`. -/
def fobj (a : Fin M → ℝ) (ρ : ℝ) (z : Fin M → ℝ) : ℝ := a ⬝ᵥ z - ρ * euc z ^ 2

/-- The parametrized feasible set `F(τ) = {‖z‖₂ ≤ 1 − τ, |zᵢ| ≤ τκᵢ}`. -/
def Fset (κ : Fin M → ℝ) (τ : ℝ) : Set (Fin M → ℝ) := {z | euc z ≤ 1 - τ ∧ ∀ i, |z i| ≤ τ * κ i}

section Normalize

variable {C Cs : ℝ} {w q : Fin M → ℝ}

/-- **Normalization of the support problem.** With `z = (C/C_*) W^{1/2} v`, `κᵢ = C√wᵢ` and
`aᵢ = C_* qᵢ/(C√wᵢ)`, the condition `N_w(v) ≤ C_*` is `‖z‖₂ + ‖κ⁻¹z‖_∞ ≤ 1`, and `⟨q, v⟩ = aᵀz`. -/
theorem support_normalize (hC : 0 < C) (hCs : 0 < Cs) (hw : ∀ i, 0 < w i) (v : Fin M → ℝ) :
    let z : Fin M → ℝ := fun i => C / Cs * Real.sqrt (w i) * v i
    let κ : Fin M → ℝ := fun i => C * Real.sqrt (w i)
    let a : Fin M → ℝ := fun i => Cs * q i / (C * Real.sqrt (w i))
    (mixed C w v ≤ Cs ↔ euc z + ‖fun i => z i / κ i‖ ≤ 1) ∧ q ⬝ᵥ v = a ⬝ᵥ z := by
  intro z κ a
  have hsq : ∀ i, 0 < Real.sqrt (w i) := fun i => Real.sqrt_pos.mpr (hw i)
  have hzκ : (fun i => z i / κ i) = (1 / Cs) • v := by
    funext i; simp only [z, κ, Pi.smul_apply, smul_eq_mul]
    field_simp [(hsq i).ne', hC.ne', hCs.ne']
  have heuc : euc z = C / Cs * wnorm w v := by
    unfold euc wnorm
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ C / Cs), ← Real.sqrt_mul (sq_nonneg _), mul_sum]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    simp only [z, mul_pow, Real.sq_sqrt (hw i).le]; ring
  refine ⟨?_, ?_⟩
  · rw [hzκ, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), heuc]
    unfold mixed
    constructor
    · intro h
      calc C / Cs * wnorm w v + 1 / Cs * ‖v‖ = (‖v‖ + C * wnorm w v) / Cs := by
            field_simp; ring
        _ ≤ Cs / Cs := div_le_div_of_nonneg_right h hCs.le
        _ = 1 := div_self hCs.ne'
    · intro h
      have : (‖v‖ + C * wnorm w v) / Cs ≤ 1 := by
        calc (‖v‖ + C * wnorm w v) / Cs = C / Cs * wnorm w v + 1 / Cs * ‖v‖ := by
              field_simp; ring
          _ ≤ 1 := h
      rwa [div_le_one hCs] at this
  · simp only [dotProduct, a, z]
    exact sum_congr rfl fun i _ => by field_simp [(hsq i).ne', hC.ne', hCs.ne']

end Normalize

variable {κ a : Fin M → ℝ} {ρ : ℝ}

/-- **Splitting the constraint:** `‖z‖₂ + ‖κ⁻¹z‖_∞ ≤ 1` iff `z ∈ F(τ)` for some `τ ∈ [0,1]`. -/
theorem split_iff (hκ : ∀ i, 0 < κ i) (z : Fin M → ℝ) :
    euc z + ‖fun i => z i / κ i‖ ≤ 1 ↔ ∃ τ ∈ Icc (0 : ℝ) 1, z ∈ Fset κ τ := by
  constructor
  · intro h
    refine ⟨‖fun i => z i / κ i‖, ⟨norm_nonneg _, by linarith [euc_nonneg z]⟩, by linarith, fun i => ?_⟩
    have := norm_le_pi_norm (fun i => z i / κ i) i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hκ i), div_le_iff₀ (hκ i)] at this
    exact this
  · rintro ⟨τ, hτ, h1, h2⟩
    have : ‖fun i => z i / κ i‖ ≤ τ :=
      (pi_norm_le_iff_of_nonneg hτ.1).mpr fun i => by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (hκ i), div_le_iff₀ (hκ i)]; exact h2 i
    linarith

theorem zero_mem_Fset (hκ : ∀ i, 0 < κ i) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    (0 : Fin M → ℝ) ∈ Fset κ τ :=
  ⟨by simp [euc, wnorm]; linarith [hτ.2], fun i => by
    simp only [Pi.zero_apply, abs_zero]; exact mul_nonneg hτ.1 (hκ i).le⟩

theorem abs_le_euc (z : Fin M → ℝ) (i : Fin M) : |z i| ≤ euc z := by
  have h1 : z i ^ 2 ≤ euc z ^ 2 := by
    rw [euc_sq]; exact single_le_sum (f := fun j => z j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
  exact abs_le.mpr (abs_le_of_sq_le_sq' h1 (euc_nonneg z))

theorem isCompact_Fset (κ : Fin M → ℝ) (τ : ℝ) : IsCompact (Fset κ τ) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have hEq : Fset κ τ = {z | euc z ≤ 1 - τ} ∩ ⋂ i, {z : Fin M → ℝ | |z i| ≤ τ * κ i} := by
      ext z; simp only [Fset, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [hEq]
    exact IsClosed.inter (isClosed_le continuous_euc continuous_const)
      (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|1 - τ|, fun z hz => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact (abs_le_euc z i).trans (hz.1.trans (le_abs_self _))

theorem continuous_fobj (a : Fin M → ℝ) (ρ : ℝ) : Continuous (fobj a ρ) := by
  unfold fobj
  exact (continuous_const.dotProduct continuous_id).sub (continuous_const.mul (continuous_euc.pow 2))

/-- The value function `G_ρ(τ) = max_{F(τ)} f_ρ`. -/
def Gval (a κ : Fin M → ℝ) (ρ τ : ℝ) : ℝ := sSup (fobj a ρ '' Fset κ τ)

theorem le_Gval (a κ : Fin M → ℝ) (ρ τ : ℝ) {z : Fin M → ℝ} (hz : z ∈ Fset κ τ) :
    fobj a ρ z ≤ Gval a κ ρ τ :=
  le_csSup ((isCompact_Fset κ τ).bddAbove_image (continuous_fobj a ρ).continuousOn) ⟨z, hz, rfl⟩

/-- **Attainment:** the value function is achieved by some `z ∈ F(τ)`. -/
theorem Gval_attained (hκ : ∀ i, 0 < κ i) (a : Fin M → ℝ) (ρ : ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : ∃ z ∈ Fset κ τ, Gval a κ ρ τ = fobj a ρ z := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_Fset κ τ).exists_isMaxOn ⟨0, zero_mem_Fset hκ hτ⟩
    (continuous_fobj a ρ).continuousOn
  refine ⟨z, hz, le_antisymm ?_ (le_Gval a κ ρ τ hz)⟩
  exact csSup_le ⟨_, ⟨0, zero_mem_Fset hκ hτ, rfl⟩⟩ (by rintro _ ⟨y, hy, rfl⟩; exact hmax hy)

theorem Gval_nonneg (hκ : ∀ i, 0 < κ i) (a : Fin M → ℝ) (ρ : ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : 0 ≤ Gval a κ ρ τ := by
  have := le_Gval a κ ρ τ (zero_mem_Fset hκ hτ)
  simpa [fobj, euc, wnorm] using this

theorem fobj_le_dot (hρ : 0 ≤ ρ) (z : Fin M → ℝ) : fobj a ρ z ≤ a ⬝ᵥ z := by
  unfold fobj; nlinarith [sq_nonneg (euc z)]

/-- `G(τ) ≤ ‖a‖₂(1 − τ)`. -/
theorem Gval_le_euc (hκ : ∀ i, 0 < κ i) (hρ : 0 ≤ ρ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    Gval a κ ρ τ ≤ euc a * (1 - τ) := by
  obtain ⟨z, hz, he⟩ := Gval_attained hκ a ρ hτ
  rw [he]
  exact (fobj_le_dot hρ z).trans ((dot_le_euc a z).trans
    (mul_le_mul_of_nonneg_left hz.1 (euc_nonneg a)))

/-- `G(τ) ≤ τ Σ|aᵢ|κᵢ`. -/
theorem Gval_le_box (hκ : ∀ i, 0 < κ i) (hρ : 0 ≤ ρ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    Gval a κ ρ τ ≤ τ * ∑ i, |a i| * κ i := by
  obtain ⟨z, hz, he⟩ := Gval_attained hκ a ρ hτ
  rw [he]
  refine (fobj_le_dot hρ z).trans ((le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans ?_))
  rw [mul_sum]
  exact sum_le_sum fun i _ => by
    rw [abs_mul]
    calc |a i| * |z i| ≤ |a i| * (τ * κ i) := mul_le_mul_of_nonneg_left (hz.2 i) (abs_nonneg _)
      _ = τ * (|a i| * κ i) := by ring

/-- `f_ρ(cz) ≥ c f_ρ(z)` for `c ∈ [0,1]`, `ρ ≥ 0`. -/
theorem fobj_smul_ge (hρ : 0 ≤ ρ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (z : Fin M → ℝ) :
    c * fobj a ρ z ≤ fobj a ρ (c • z) := by
  unfold fobj
  rw [euc_smul, abs_of_nonneg hc0, dotProduct_smul, smul_eq_mul]
  have : 0 ≤ ρ * euc z ^ 2 * (c - c ^ 2) := mul_nonneg (mul_nonneg hρ (sq_nonneg _)) (by nlinarith)
  nlinarith

/-- **The Lipschitz bound:** `G(τ) ≤ G(τ') + L|τ − τ'|` with `L = max{‖a‖₂, Σ|aᵢ|κᵢ}`. -/
theorem Gval_lipschitz (hκ : ∀ i, 0 < κ i) (hρ : 0 ≤ ρ) {τ τ' : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hτ' : τ' ∈ Icc (0 : ℝ) 1) :
    Gval a κ ρ τ ≤ Gval a κ ρ τ' + max (euc a) (∑ i, |a i| * κ i) * |τ - τ'| := by
  obtain ⟨z, hz, he⟩ := Gval_attained hκ a ρ hτ
  have hG0 := Gval_nonneg hκ a ρ hτ
  rcases lt_trichotomy τ τ' with h | h | h
  · -- shrink the Euclidean radius
    set c := (1 - τ') / (1 - τ)
    have h1τ : 0 < 1 - τ := by linarith [hτ'.2]
    have hc0 : 0 ≤ c := div_nonneg (by linarith [hτ'.2]) h1τ.le
    have hc1 : c ≤ 1 := by rw [div_le_one h1τ]; linarith
    have hcz : c • z ∈ Fset κ τ' := by
      refine ⟨?_, fun i => ?_⟩
      · rw [euc_smul, abs_of_nonneg hc0]
        calc c * euc z ≤ c * (1 - τ) := mul_le_mul_of_nonneg_left hz.1 hc0
          _ = 1 - τ' := by simp only [c]; field_simp
      · rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc0]
        calc c * |z i| ≤ 1 * (τ * κ i) := mul_le_mul hc1 (hz.2 i) (abs_nonneg _) zero_le_one
          _ ≤ τ' * κ i := by rw [one_mul]; exact mul_le_mul_of_nonneg_right h.le (hκ i).le
    have hG' := (fobj_smul_ge hρ hc0 hc1 z).trans (le_Gval a κ ρ τ' hcz)
    rw [← he] at hG'
    have hbd := Gval_le_euc (a := a) hκ hρ hτ
    have hgap : (1 - c) * Gval a κ ρ τ ≤ euc a * (τ' - τ) := by
      have e : (1 - c) * (euc a * (1 - τ)) = euc a * (τ' - τ) := by simp only [c]; field_simp; ring
      rw [← e]; exact mul_le_mul_of_nonneg_left hbd (by linarith)
    have hL : euc a * (τ' - τ) ≤ max (euc a) (∑ i, |a i| * κ i) * |τ - τ'| := by
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    nlinarith
  · subst h; simp
  · -- shrink the box
    set c := τ' / τ
    have hτ0 : 0 < τ := lt_of_le_of_lt hτ'.1 h
    have hc0 : 0 ≤ c := div_nonneg hτ'.1 hτ0.le
    have hc1 : c ≤ 1 := by rw [div_le_one hτ0]; exact h.le
    have hcz : c • z ∈ Fset κ τ' := by
      refine ⟨?_, fun i => ?_⟩
      · rw [euc_smul, abs_of_nonneg hc0]
        calc c * euc z ≤ 1 * euc z := mul_le_mul_of_nonneg_right hc1 (euc_nonneg z)
          _ ≤ 1 - τ := by rw [one_mul]; exact hz.1
          _ ≤ 1 - τ' := by linarith
      · rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc0]
        calc c * |z i| ≤ c * (τ * κ i) := mul_le_mul_of_nonneg_left (hz.2 i) hc0
          _ = τ' * κ i := by simp only [c]; field_simp
    have hG' := (fobj_smul_ge hρ hc0 hc1 z).trans (le_Gval a κ ρ τ' hcz)
    rw [← he] at hG'
    have hbd := Gval_le_box (a := a) hκ hρ hτ
    have hgap : (1 - c) * Gval a κ ρ τ ≤ (τ - τ') * ∑ i, |a i| * κ i := by
      have e : (1 - c) * (τ * ∑ i, |a i| * κ i) = (τ - τ') * ∑ i, |a i| * κ i := by
        simp only [c]; field_simp
      rw [← e]; exact mul_le_mul_of_nonneg_left hbd (by linarith)
    have hL : (τ - τ') * ∑ i, |a i| * κ i ≤ max (euc a) (∑ i, |a i| * κ i) * |τ - τ'| := by
      rw [abs_of_pos (by linarith), mul_comm]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    nlinarith

/-- **Concavity of the value function.** -/
theorem Gval_concave (hκ : ∀ i, 0 < κ i) (hρ : 0 ≤ ρ) {τ₁ τ₂ θ : ℝ} (h₁ : τ₁ ∈ Icc (0 : ℝ) 1)
    (h₂ : τ₂ ∈ Icc (0 : ℝ) 1) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    θ * Gval a κ ρ τ₁ + (1 - θ) * Gval a κ ρ τ₂ ≤ Gval a κ ρ (θ * τ₁ + (1 - θ) * τ₂) := by
  obtain ⟨z₁, hz₁, he₁⟩ := Gval_attained hκ a ρ h₁
  obtain ⟨z₂, hz₂, he₂⟩ := Gval_attained hκ a ρ h₂
  have hθ1 : 0 ≤ 1 - θ := by linarith [hθ.2]
  set z := θ • z₁ + (1 - θ) • z₂
  have hz : z ∈ Fset κ (θ * τ₁ + (1 - θ) * τ₂) := by
    refine ⟨?_, fun i => ?_⟩
    · refine (euc_add_le _ _).trans ?_
      rw [euc_smul, euc_smul, abs_of_nonneg hθ.1, abs_of_nonneg hθ1]
      have e1 := mul_le_mul_of_nonneg_left hz₁.1 hθ.1
      have e2 := mul_le_mul_of_nonneg_left hz₂.1 hθ1
      linarith
    · simp only [z, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hθ.1, abs_of_nonneg hθ1]
      have e1 := mul_le_mul_of_nonneg_left (hz₁.2 i) hθ.1
      have e2 := mul_le_mul_of_nonneg_left (hz₂.2 i) hθ1
      linarith
  refine le_trans ?_ (le_Gval a κ ρ _ hz)
  rw [he₁, he₂]
  unfold fobj
  have hlin : a ⬝ᵥ z = θ * (a ⬝ᵥ z₁) + (1 - θ) * (a ⬝ᵥ z₂) := by
    simp only [z, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have heuc : euc z ≤ θ * euc z₁ + (1 - θ) * euc z₂ := by
    refine (euc_add_le _ _).trans (le_of_eq ?_)
    rw [euc_smul, euc_smul, abs_of_nonneg hθ.1, abs_of_nonneg hθ1]
  have hsq : euc z ^ 2 ≤ θ * euc z₁ ^ 2 + (1 - θ) * euc z₂ ^ 2 := by
    have h0 := euc_nonneg z
    have h1 : euc z ^ 2 ≤ (θ * euc z₁ + (1 - θ) * euc z₂) ^ 2 := pow_le_pow_left₀ h0 heuc 2
    nlinarith [sq_nonneg (euc z₁ - euc z₂), mul_nonneg hθ.1 hθ1]
  rw [hlin]
  nlinarith [mul_le_mul_of_nonneg_left hsq hρ]

section Duality

/-- The clipped one-dimensional maximizer `sign(a) min(B, |a|/(2μ))`. -/
def clip (a B μ : ℝ) : ℝ := if 0 ≤ a then min B (a / (2 * μ)) else -min B (-a / (2 * μ))

theorem clip_mul (a B μ : ℝ) : a * clip a B μ = |a| * min B (|a| / (2 * μ)) := by
  unfold clip
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]; ring

theorem clip_abs {a B μ : ℝ} (hB : 0 ≤ B) (hμ : 0 < μ) :
    |clip a B μ| = min B (|a| / (2 * μ)) := by
  unfold clip
  split_ifs with h
  · rw [abs_of_nonneg h, abs_of_nonneg (le_min hB (by positivity))]
  · rw [abs_of_neg (lt_of_not_ge h), abs_neg, abs_of_nonneg (le_min hB (by
      have : 0 < -a := by linarith [lt_of_not_ge h]
      positivity))]

theorem clip_sign (a B μ : ℝ) (hB : 0 ≤ B) (hμ : 0 < μ) : 0 ≤ a * clip a B μ := by
  rw [clip_mul]
  exact mul_nonneg (abs_nonneg a) (le_min hB (by positivity))

/-- **The one-dimensional clipped quadratic maximum:** for `|y| ≤ B`,
`ay − μy² ≤ aŷ − μŷ²` with `ŷ = clip a B μ`. -/
theorem clip_quad_max {a B μ y : ℝ} (hB : 0 ≤ B) (hμ : 0 < μ) (hy : |y| ≤ B) :
    a * y - μ * y ^ 2 ≤ a * clip a B μ - μ * clip a B μ ^ 2 := by
  have hsq : clip a B μ ^ 2 = min B (|a| / (2 * μ)) ^ 2 := by rw [← sq_abs, clip_abs hB hμ]
  rw [clip_mul, hsq]
  set t := |y|
  have hay : a * y ≤ |a| * t := by
    rw [← abs_mul]; exact le_abs_self _
  have hy2 : y ^ 2 = t ^ 2 := (sq_abs y).symm
  rw [hy2]
  have ht0 : 0 ≤ t := abs_nonneg y
  rcases le_total (|a| / (2 * μ)) B with h | h
  · rw [min_eq_right h]
    have e : |a| * (|a| / (2 * μ)) - μ * (|a| / (2 * μ)) ^ 2 - (|a| * t - μ * t ^ 2) =
        μ * (t - |a| / (2 * μ)) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hμ.le (sq_nonneg (t - |a| / (2 * μ)))]
  · rw [min_eq_left h]
    have h2 : μ * (B + t) ≤ |a| := by
      have : 2 * μ * B ≤ |a| := by rw [le_div_iff₀ (by positivity)] at h; linarith
      nlinarith
    have : |a| * t - μ * t ^ 2 ≤ |a| * B - μ * B ^ 2 := by
      have e : |a| * B - μ * B ^ 2 - (|a| * t - μ * t ^ 2) = (B - t) * (|a| - μ * (B + t)) := by ring
      nlinarith [mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr h2)]
    linarith

variable {κ a : Fin M → ℝ} {ρ : ℝ}

/-- The primal candidate `z(λ)ᵢ = sign(aᵢ) min(τκᵢ, |aᵢ|/(2(ρ+λ)))`. -/
def zlam (a κ : Fin M → ℝ) (ρ τ lm : ℝ) : Fin M → ℝ := fun i => clip (a i) (τ * κ i) (ρ + lm)

/-- The dual value `D(λ) = f_ρ(z(λ)) + λ(r² − ‖z(λ)‖₂²)` with `r = 1 − τ`. -/
def Dval (a κ : Fin M → ℝ) (ρ τ lm : ℝ) : ℝ :=
  fobj a ρ (zlam a κ ρ τ lm) + lm * ((1 - τ) ^ 2 - euc (zlam a κ ρ τ lm) ^ 2)

theorem zlam_box (hκ : ∀ i, 0 < κ i) {τ lm : ℝ} (hτ : 0 ≤ τ) (hpos : 0 < ρ + lm) (i : Fin M) :
    |zlam a κ ρ τ lm i| ≤ τ * κ i := by
  rw [zlam, clip_abs (mul_nonneg hτ (hκ i).le) hpos]; exact min_le_left _ _

theorem zlam_sign (hκ : ∀ i, 0 < κ i) {τ lm : ℝ} (hτ : 0 ≤ τ) (hpos : 0 < ρ + lm) (i : Fin M) :
    0 ≤ a i * zlam a κ ρ τ lm i :=
  clip_sign _ _ _ (mul_nonneg hτ (hκ i).le) hpos

/-- **Weak duality:** `f_ρ(z) ≤ D(λ)` for every `z ∈ F(τ)` and `λ ≥ 0`, hence `G_ρ(τ) ≤ D(λ)`. -/
theorem fobj_le_Dval (hκ : ∀ i, 0 < κ i) (hρ : 0 < ρ) {τ lm : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hlm : 0 ≤ lm) {z : Fin M → ℝ} (hz : z ∈ Fset κ τ) : fobj a ρ z ≤ Dval a κ ρ τ lm := by
  have hpos : 0 < ρ + lm := by linarith
  -- `f_ρ(z) ≤ f_ρ(z) + λ(r² − ‖z‖²)`
  have hr : euc z ^ 2 ≤ (1 - τ) ^ 2 := pow_le_pow_left₀ (euc_nonneg z) hz.1 2
  have h1 : fobj a ρ z ≤ ∑ i, (a i * z i - (ρ + lm) * z i ^ 2) + lm * (1 - τ) ^ 2 := by
    unfold fobj
    rw [euc_sq] at hr ⊢
    have : ∑ i, (a i * z i - (ρ + lm) * z i ^ 2) = a ⬝ᵥ z - (ρ + lm) * ∑ i, z i ^ 2 := by
      simp only [dotProduct, mul_sum, ← sum_sub_distrib]
    rw [this]; nlinarith
  -- coordinatewise clipped maximum
  have h2 : ∑ i, (a i * z i - (ρ + lm) * z i ^ 2) ≤
      ∑ i, (a i * zlam a κ ρ τ lm i - (ρ + lm) * zlam a κ ρ τ lm i ^ 2) :=
    sum_le_sum fun i _ => clip_quad_max (mul_nonneg hτ.1 (hκ i).le) hpos (hz.2 i)
  have h3 : ∑ i, (a i * zlam a κ ρ τ lm i - (ρ + lm) * zlam a κ ρ τ lm i ^ 2) +
      lm * (1 - τ) ^ 2 = Dval a κ ρ τ lm := by
    have hs : ∑ i, (a i * zlam a κ ρ τ lm i - (ρ + lm) * zlam a κ ρ τ lm i ^ 2) =
        ∑ i, a i * zlam a κ ρ τ lm i - ρ * ∑ i, zlam a κ ρ τ lm i ^ 2 -
          lm * ∑ i, zlam a κ ρ τ lm i ^ 2 := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    unfold Dval fobj
    rw [euc_sq, hs]
    simp only [dotProduct]
    ring
  linarith

theorem Gval_le_Dval (hκ : ∀ i, 0 < κ i) (hρ : 0 < ρ) {τ lm : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hlm : 0 ≤ lm) : Gval a κ ρ τ ≤ Dval a κ ρ τ lm := by
  obtain ⟨z, hz, he⟩ := Gval_attained hκ a ρ hτ
  rw [he]; exact fobj_le_Dval hκ hρ hτ hlm hz

/-- **The `λ = 0` case:** if `z(0)` satisfies the Euclidean constraint, it is optimal. -/
theorem Gval_eq_zero_case (hκ : ∀ i, 0 < κ i) (hρ : 0 < ρ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (h0 : euc (zlam a κ ρ τ 0) ≤ 1 - τ) :
    zlam a κ ρ τ 0 ∈ Fset κ τ ∧ Gval a κ ρ τ = fobj a ρ (zlam a κ ρ τ 0) := by
  have hmem : zlam a κ ρ τ 0 ∈ Fset κ τ :=
    ⟨h0, fun i => zlam_box hκ hτ.1 (by linarith) i⟩
  refine ⟨hmem, le_antisymm ?_ (le_Gval a κ ρ τ hmem)⟩
  have := Gval_le_Dval (a := a) hκ hρ hτ le_rfl
  simpa [Dval] using this

/-- `|z(λ)ᵢ|` is nonincreasing in `λ`, so `‖z(λ)‖₂` is too. -/
theorem zlam_abs_antitone (hκ : ∀ i, 0 < κ i) {τ l₁ l₂ : ℝ} (hτ : 0 ≤ τ) (hpos : 0 < ρ + l₁)
    (h12 : l₁ ≤ l₂) (i : Fin M) : |zlam a κ ρ τ l₂ i| ≤ |zlam a κ ρ τ l₁ i| := by
  have hB := mul_nonneg hτ (hκ i).le
  rw [zlam, zlam, clip_abs hB (by linarith), clip_abs hB hpos]
  exact min_le_min le_rfl (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by linarith))

theorem euc_zlam_antitone (hκ : ∀ i, 0 < κ i) {τ l₁ l₂ : ℝ} (hτ : 0 ≤ τ) (hpos : 0 < ρ + l₁)
    (h12 : l₁ ≤ l₂) : euc (zlam a κ ρ τ l₂) ≤ euc (zlam a κ ρ τ l₁) := by
  unfold euc wnorm
  apply Real.sqrt_le_sqrt
  refine sum_le_sum fun i _ => ?_
  simp only [one_mul]
  rw [← sq_abs, ← sq_abs (zlam a κ ρ τ l₁ i)]
  exact pow_le_pow_left₀ (abs_nonneg _) (zlam_abs_antitone hκ hτ hpos h12 i) 2

/-- At `λ ≥ Λ` the candidate is short: `‖z(λ)‖₂ ≤ ‖a‖₂/(2(ρ+λ))`. -/
theorem euc_zlam_le (hκ : ∀ i, 0 < κ i) {τ lm : ℝ} (hτ : 0 ≤ τ) (hpos : 0 < ρ + lm) :
    euc (zlam a κ ρ τ lm) ≤ euc a / (2 * (ρ + lm)) := by
  have hc : 0 < 1 / (2 * (ρ + lm)) := one_div_pos.mpr (by linarith)
  have h : euc (zlam a κ ρ τ lm) ≤ euc ((1 / (2 * (ρ + lm))) • a) := by
    unfold euc wnorm
    apply Real.sqrt_le_sqrt
    refine sum_le_sum fun i _ => ?_
    simp only [one_mul, Pi.smul_apply, smul_eq_mul]
    rw [← sq_abs, ← sq_abs (1 / (2 * (ρ + lm)) * a i)]
    apply pow_le_pow_left₀ (abs_nonneg _)
    rw [zlam, clip_abs (mul_nonneg hτ (hκ i).le) hpos, abs_mul, abs_of_pos hc]
    exact (min_le_right _ _).trans (le_of_eq (by ring))
  rw [euc_smul, abs_of_pos hc] at h
  calc euc (zlam a κ ρ τ lm) ≤ 1 / (2 * (ρ + lm)) * euc a := h
    _ = euc a / (2 * (ρ + lm)) := by ring

end Duality

section Evaluator

variable {κ a : Fin M → ℝ} {ρ : ℝ}

/-- `|min(B, x) − min(B, y)| ≤ |x − y|`. -/
theorem abs_min_sub_min (B x y : ℝ) : |min B x - min B y| ≤ |x - y| := by
  rcases le_total B x with h1 | h1 <;> rcases le_total B y with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2]; simp
  · rw [min_eq_left h1, min_eq_right h2, abs_le]; constructor <;>
      [linarith [le_abs_self (x - y)]; linarith [le_abs_self (x - y)]]
  · rw [min_eq_right h1, min_eq_left h2, abs_le]; constructor <;>
      [linarith [neg_abs_le (x - y)]; linarith [neg_abs_le (x - y)]]
  · rw [min_eq_right h1, min_eq_right h2]

/-- **`λ ↦ z(λ)` is Lipschitz:** `‖z(λ₁) − z(λ₂)‖₂ ≤ ‖a‖₂/(2ρ²) |λ₁ − λ₂|` for `λᵢ ≥ 0`. -/
theorem euc_zlam_sub (hρ : 0 < ρ) {τ l₁ l₂ : ℝ} (h1 : 0 ≤ l₁)
    (h2 : 0 ≤ l₂) :
    euc (zlam a κ ρ τ l₁ - zlam a κ ρ τ l₂) ≤ euc a / (2 * ρ ^ 2) * |l₁ - l₂| := by
  have hc : ∀ i, |zlam a κ ρ τ l₁ i - zlam a κ ρ τ l₂ i| ≤ |a i| / (2 * ρ ^ 2) * |l₁ - l₂| := by
    intro i
    have hpos1 : 0 < ρ + l₁ := by linarith
    have hpos2 : 0 < ρ + l₂ := by linarith
    -- both have the sign of `aᵢ`; compare magnitudes
    have hden : 0 < 2 * ((ρ + l₁) * (ρ + l₂)) := mul_pos two_pos (mul_pos hpos1 hpos2)
    have hmag : |min (τ * κ i) (|a i| / (2 * (ρ + l₁))) - min (τ * κ i) (|a i| / (2 * (ρ + l₂)))| ≤
        |a i| / (2 * ρ ^ 2) * |l₁ - l₂| := by
      refine (abs_min_sub_min _ _ _).trans ?_
      have e : |a i| / (2 * (ρ + l₁)) - |a i| / (2 * (ρ + l₂)) =
          |a i| * (l₂ - l₁) / (2 * ((ρ + l₁) * (ρ + l₂))) := by field_simp; ring
      rw [e, abs_div, abs_mul, abs_abs, abs_of_pos hden, abs_sub_comm, div_le_iff₀ hden]
      have hq : |a i| * |l₁ - l₂| = |a i| / (2 * ρ ^ 2) * |l₁ - l₂| * (2 * ρ ^ 2) := by
        field_simp
      rw [hq]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    unfold zlam clip
    split_ifs with h
    · rw [abs_of_nonneg h] at hmag ⊢; exact hmag
    · have : |a i| = -a i := abs_of_neg (lt_of_not_ge h)
      rw [this] at hmag ⊢
      rw [show -min (τ * κ i) (-a i / (2 * (ρ + l₁))) - -min (τ * κ i) (-a i / (2 * (ρ + l₂))) =
        -(min (τ * κ i) (-a i / (2 * (ρ + l₁))) - min (τ * κ i) (-a i / (2 * (ρ + l₂)))) by ring,
        abs_neg]
      exact hmag
  have hcoef : euc ((|l₁ - l₂| / (2 * ρ ^ 2)) • a) = euc a / (2 * ρ ^ 2) * |l₁ - l₂| := by
    rw [euc_smul, abs_of_nonneg (by positivity)]; ring
  rw [← hcoef]
  unfold euc wnorm
  apply Real.sqrt_le_sqrt
  refine sum_le_sum fun i _ => ?_
  simp only [one_mul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [← sq_abs, ← sq_abs (|l₁ - l₂| / (2 * ρ ^ 2) * a i)]
  apply pow_le_pow_left₀ (abs_nonneg _)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |l₁ - l₂| / (2 * ρ ^ 2))]
  calc |zlam a κ ρ τ l₁ i - zlam a κ ρ τ l₂ i| ≤ |a i| / (2 * ρ ^ 2) * |l₁ - l₂| := hc i
    _ = |l₁ - l₂| / (2 * ρ ^ 2) * |a i| := by ring

/-- The bisection on `λ` for a fixed `τ`, starting from `[0, Λ]`. -/
def bisect (a κ : Fin M → ℝ) (ρ τ Λ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, Λ)
  | n + 1 =>
      let p := bisect a κ ρ τ Λ n
      if euc (zlam a κ ρ τ ((p.1 + p.2) / 2)) ≤ 1 - τ then (p.1, (p.1 + p.2) / 2)
      else ((p.1 + p.2) / 2, p.2)

theorem bisect_inv {τ Λ : ℝ} (hΛ : 0 ≤ Λ)
    (h0 : 1 - τ < euc (zlam a κ ρ τ 0)) (hΛr : euc (zlam a κ ρ τ Λ) ≤ 1 - τ) (n : ℕ) :
    0 ≤ (bisect a κ ρ τ Λ n).1 ∧ (bisect a κ ρ τ Λ n).1 ≤ (bisect a κ ρ τ Λ n).2 ∧
      (bisect a κ ρ τ Λ n).2 ≤ Λ ∧
      (bisect a κ ρ τ Λ n).2 - (bisect a κ ρ τ Λ n).1 = Λ / 2 ^ n ∧
      euc (zlam a κ ρ τ (bisect a κ ρ τ Λ n).2) ≤ 1 - τ ∧
      1 - τ < euc (zlam a κ ρ τ (bisect a κ ρ τ Λ n).1) := by
  induction n with
  | zero => simp [bisect, hΛ, h0, hΛr]
  | succ n ih =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
      simp only [bisect]
      split_ifs with hm
      · refine ⟨h1, by linarith, by linarith, ?_, hm, h6⟩
        rw [pow_succ, ← div_div, ← h4]; ring
      · refine ⟨by linarith, by linarith, h3, ?_, h5, lt_of_not_ge hm⟩
        rw [pow_succ, ← div_div, ← h4]; ring

/-- **The certified fixed-`τ` evaluator** (exact evaluations). The output `ẑ` is feasible and
sign-aligned, and `ℓ = f_ρ(ẑ) ≤ G_ρ(τ) ≤ u` with `u − ℓ ≤ Λ²‖a‖₂/(ρ² 2ⁿ)`. If `z(0)` is
feasible, the evaluator returns it with `ℓ = u`. -/
theorem evaluator (hκ : ∀ i, 0 < κ i) (hρ : 0 < ρ) {τ Λ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hΛ : 0 ≤ Λ) (hΛr : euc (zlam a κ ρ τ Λ) ≤ 1 - τ) (n : ℕ) :
    ∃ zh : Fin M → ℝ, ∃ ℓ u : ℝ, zh ∈ Fset κ τ ∧ (∀ i, 0 ≤ a i * zh i) ∧ ℓ = fobj a ρ zh ∧
      ℓ ≤ Gval a κ ρ τ ∧ Gval a κ ρ τ ≤ u ∧ u - ℓ ≤ Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ n) := by
  by_cases h0 : euc (zlam a κ ρ τ 0) ≤ 1 - τ
  · obtain ⟨hmem, heq⟩ := Gval_eq_zero_case (a := a) hκ hρ hτ h0
    refine ⟨zlam a κ ρ τ 0, fobj a ρ (zlam a κ ρ τ 0), fobj a ρ (zlam a κ ρ τ 0), hmem,
      fun i => zlam_sign hκ hτ.1 (by linarith) i, rfl, heq.ge, heq.le, ?_⟩
    rw [sub_self]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (euc_nonneg a)) (by positivity)
  push Not at h0
  obtain ⟨hl0, hlh, hhΛ, hwidth, hfeas, hinf⟩ := bisect_inv (a := a) (κ := κ) (ρ := ρ) hΛ h0 hΛr n
  set lo := (bisect a κ ρ τ Λ n).1
  set hi := (bisect a κ ρ τ Λ n).2
  have hhi0 : 0 ≤ hi := by linarith
  have hmem : zlam a κ ρ τ hi ∈ Fset κ τ := ⟨hfeas, fun i => zlam_box hκ hτ.1 (by linarith) i⟩
  refine ⟨zlam a κ ρ τ hi, fobj a ρ (zlam a κ ρ τ hi), Dval a κ ρ τ hi, hmem,
    fun i => zlam_sign hκ hτ.1 (by linarith) i, rfl, le_Gval a κ ρ τ hmem,
    Gval_le_Dval hκ hρ hτ hhi0, ?_⟩
  -- the duality gap `hi (r² − ‖z(hi)‖²)`
  set r := 1 - τ
  set e := euc (zlam a κ ρ τ hi)
  have he0 : 0 ≤ e := euc_nonneg _
  have hgap : Dval a κ ρ τ hi - fobj a ρ (zlam a κ ρ τ hi) = hi * ((r - e) * (r + e)) := by
    unfold Dval; ring
  have hre : r - e ≤ euc a / (2 * ρ ^ 2) * (hi - lo) := by
    have h1 : euc (zlam a κ ρ τ lo) - e ≤ euc (zlam a κ ρ τ lo - zlam a κ ρ τ hi) := by
      have := euc_add_le (zlam a κ ρ τ lo - zlam a κ ρ τ hi) (zlam a κ ρ τ hi)
      rw [sub_add_cancel] at this; linarith
    have h2 := euc_zlam_sub (a := a) (κ := κ) (τ := τ) hρ hl0 hhi0
    rw [abs_of_nonpos (by linarith), neg_sub] at h2
    linarith
  have hr1 : r + e ≤ 2 := by simp only [r]; linarith [hτ.1, hfeas]
  have hre0 : 0 ≤ r - e := by simp only [r, e]; linarith
  rw [hgap]
  rw [hwidth] at hre
  have hea := euc_nonneg a
  calc hi * ((r - e) * (r + e)) ≤ Λ * ((euc a / (2 * ρ ^ 2) * (Λ / 2 ^ n)) * 2) := by
        apply mul_le_mul hhΛ _ (mul_nonneg hre0 (by linarith)) hΛ
        exact mul_le_mul hre hr1 (by linarith)
          (mul_nonneg (div_nonneg hea (by positivity)) (div_nonneg hΛ (by positivity)))
    _ = Λ ^ 2 * euc a / (ρ ^ 2 * 2 ^ n) := by field_simp

end Evaluator

section Rescale

variable {κ a : Fin M → ℝ} {ρ : ℝ}

/-- **Conservative rescaling** for inexact norm evaluations. If `z` satisfies the box
constraints of `F(τ)`, is sign-aligned with `a`, and `‖z‖₂ ≤ ñ ≤ r + δ` for a certified upper
value `ñ`, then `c z` with `c = min{1, r/ñ}` lies in `F(τ)`, is sign-aligned, and
`f_ρ(cz) ≥ f_ρ(z) − δ‖a‖₂`. -/
theorem rescale_feasible (hρ : 0 ≤ ρ) {τ ntil δ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    {z : Fin M → ℝ} (hbox : ∀ i, |z i| ≤ τ * κ i) (hsign : ∀ i, 0 ≤ a i * z i)
    (hn : euc z ≤ ntil) (hnr : ntil ≤ (1 - τ) + δ) (hδ : 0 ≤ δ) :
    let c : ℝ := if ntil ≤ 1 - τ then 1 else (1 - τ) / ntil
    c • z ∈ Fset κ τ ∧ (∀ i, 0 ≤ a i * (c • z) i) ∧ fobj a ρ z - δ * euc a ≤ fobj a ρ (c • z) := by
  intro c
  have hr : 0 ≤ 1 - τ := by linarith [hτ.2]
  have hc : 0 ≤ c ∧ c ≤ 1 ∧ c * ntil ≤ 1 - τ ∧ (1 - c) * ntil ≤ δ := by
    simp only [c]
    split_ifs with h
    · exact ⟨zero_le_one, le_rfl, by linarith, by simp; exact hδ⟩
    · push Not at h
      have hn0 : 0 < ntil := lt_of_le_of_lt hr h
      refine ⟨div_nonneg hr hn0.le, (div_le_one hn0).mpr h.le, by field_simp; exact le_rfl, ?_⟩
      have : (1 - (1 - τ) / ntil) * ntil = ntil - (1 - τ) := by field_simp
      rw [this]; linarith
  obtain ⟨hc0, hc1, hcn, hloss⟩ := hc
  have hmem : c • z ∈ Fset κ τ := by
    refine ⟨?_, fun i => ?_⟩
    · rw [euc_smul, abs_of_nonneg hc0]
      exact (mul_le_mul_of_nonneg_left hn hc0).trans hcn
    · rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc0]
      exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans (hbox i)
  refine ⟨hmem, fun i => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm]; exact mul_nonneg hc0 (hsign i)
  · have h1 := fobj_smul_ge (a := a) hρ hc0 hc1 z
    have h2 : fobj a ρ z ≤ euc a * euc z := (fobj_le_dot hρ z).trans (dot_le_euc a z)
    have h3 : (1 - c) * fobj a ρ z ≤ δ * euc a := by
      rcases le_total 0 (fobj a ρ z) with hf | hf
      · calc (1 - c) * fobj a ρ z ≤ (1 - c) * (euc a * ntil) :=
              mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hn (euc_nonneg a)))
                (by linarith)
          _ = euc a * ((1 - c) * ntil) := by ring
          _ ≤ euc a * δ := mul_le_mul_of_nonneg_left hloss (euc_nonneg a)
          _ = δ * euc a := by ring
      · have : (1 - c) * fobj a ρ z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hf
        exact this.trans (mul_nonneg hδ (euc_nonneg a))
    nlinarith

end Rescale

end

end ImplicitLP
end CutQueryComplexity
