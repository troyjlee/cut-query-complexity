import CutQueryComplexity.ImplicitLP.GMove
import Mathlib.Topology.MetricSpace.Bounded

/-! # Frozen-weight centers exist and are unique (Lee–Sidford audit, gap G8)

For fixed `t`, positive weights `w`, and the barrier `φᵢ = −log cos θᵢ`, the weighted center is
`x̄ = argmin_{Aᵀy = b, y interior} tcᵀy + Σᵢ wᵢ φᵢ(yᵢ)` (`centerObj`). Lee–Sidford (Lemma 41) and
the audited draft (`lem:center`) use `x̄` without proving that it exists.

* **Existence** (`center_exists`): suppose a strictly feasible point `x₀` exists. A sublevel set
  `{F ≤ F(x₀)}` keeps every `cos θᵢ ≥ ηᵢ > 0`, because the other barrier terms are
  nonnegative and the linear term is bounded on the box. That set is compact, so `F` attains
  its minimum.
* **Uniqueness** (`center_unique`): `−log cos` is strictly midpoint convex on `(−π/2, π/2)`,
  since `cos a cos b = (cos(a−b) + cos(a+b))/2 < cos²((a+b)/2)` for `a ≠ b`.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Metric

noncomputable section

variable {M r : ℕ}

/-- The weighted barrier objective `tcᵀy + Σᵢ wᵢ(−log cos θᵢ(y))`. -/
def centerObj (κ m c w : Fin M → ℝ) (t : ℝ) (y : Fin M → ℝ) : ℝ :=
  t * (c ⬝ᵥ y) + ∑ i, w i * -Real.log (cos (theta κ m y i))

/-- The strictly feasible region `{y : Aᵀy = b, y interior}`. -/
def Feasible (A : Matrix (Fin M) (Fin r) ℝ) (b : Fin r → ℝ) (κ m : Fin M → ℝ) :
    Set (Fin M → ℝ) :=
  {y | Aᵀ *ᵥ y = b ∧ Interior κ m y}

/-- Strict midpoint convexity of `−log cos`: `cos a cos b < cos²((a+b)/2)` for `a ≠ b` in
`(−π/2, π/2)`. -/
theorem cos_mul_cos_lt {a b : ℝ} (ha : |a| < π / 2) (hb : |b| < π / 2) (hab : a ≠ b) :
    cos a * cos b < cos ((a + b) / 2) ^ 2 := by
  have h1 : cos a * cos b = (cos (a - b) + cos (a + b)) / 2 := by
    rw [cos_sub, cos_add]; ring
  have h2 : cos ((a + b) / 2) ^ 2 = (1 + cos (a + b)) / 2 := by
    rw [cos_sq]; ring_nf
  rw [h1, h2]
  have hlt : cos (a - b) < 1 := by
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hb1 : -(2 * π) < a - b := by linarith [neg_abs_le a, le_abs_self b, pi_pos]
    have hb2 : a - b < 2 * π := by linarith [le_abs_self a, neg_abs_le b, pi_pos]
    exact lt_of_le_of_ne (cos_le_one _) fun h =>
      hne ((cos_eq_one_iff_of_lt_of_lt hb1 hb2).mp h)
  linarith

theorem cos_mul_cos_le {a b : ℝ} : cos a * cos b ≤ cos ((a + b) / 2) ^ 2 := by
  have h1 : cos a * cos b = (cos (a - b) + cos (a + b)) / 2 := by
    rw [cos_sub, cos_add]; ring
  have h2 : cos ((a + b) / 2) ^ 2 = (1 + cos (a + b)) / 2 := by
    rw [cos_sq]; ring_nf
  rw [h1, h2]; linarith [cos_le_one (a - b)]

variable {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c w : Fin M → ℝ} {t : ℝ}

theorem theta_midpoint (y₁ y₂ : Fin M → ℝ) (i : Fin M) :
    theta κ m ((1 / 2 : ℝ) • (y₁ + y₂)) i = (theta κ m y₁ i + theta κ m y₂ i) / 2 := by
  simp only [theta, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

/-- **Uniqueness of the frozen-weight center.** -/
theorem center_unique (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i) {y₁ y₂ : Fin M → ℝ}
    (h₁ : y₁ ∈ Feasible A b κ m) (h₂ : y₂ ∈ Feasible A b κ m)
    (hmin₁ : ∀ y ∈ Feasible A b κ m, centerObj κ m c w t y₁ ≤ centerObj κ m c w t y)
    (hmin₂ : ∀ y ∈ Feasible A b κ m, centerObj κ m c w t y₂ ≤ centerObj κ m c w t y) :
    y₁ = y₂ := by
  by_contra hne
  set z := (1 / 2 : ℝ) • (y₁ + y₂)
  have hzθ := theta_midpoint (κ := κ) (m := m) y₁ y₂
  have hz : z ∈ Feasible A b κ m := by
    refine ⟨?_, fun i => ?_⟩
    · simp only [z, mulVec_smul, mulVec_add, h₁.1, h₂.1]
      funext j; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    · rw [hzθ]
      have := h₁.2 i; have := h₂.2 i
      rw [abs_div, abs_two, div_lt_iff₀ two_pos]
      linarith [abs_add_le (theta κ m y₁ i) (theta κ m y₂ i)]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hθne : theta κ m y₁ i ≠ theta κ m y₂ i := fun h => hi (by
    simp only [theta] at h
    have := mul_left_cancel₀ (hκ i).ne' h
    linarith)
  -- per-coordinate midpoint bounds
  have hc₁ := fun j => cos_theta_pos h₁.2 j
  have hc₂ := fun j => cos_theta_pos h₂.2 j
  have hcz := fun j => cos_theta_pos hz.2 j
  have hterm : ∀ j, 2 * -Real.log (cos (theta κ m z j)) ≤
      -Real.log (cos (theta κ m y₁ j)) + -Real.log (cos (theta κ m y₂ j)) := fun j => by
    have := cos_mul_cos_le (a := theta κ m y₁ j) (b := theta κ m y₂ j)
    rw [← hzθ] at this
    have hl := Real.log_le_log (mul_pos (hc₁ j) (hc₂ j)) this
    rw [Real.log_mul (hc₁ j).ne' (hc₂ j).ne', Real.log_pow] at hl
    push_cast at hl; linarith
  have hstrict : 2 * -Real.log (cos (theta κ m z i)) <
      -Real.log (cos (theta κ m y₁ i)) + -Real.log (cos (theta κ m y₂ i)) := by
    have := cos_mul_cos_lt (h₁.2 i) (h₂.2 i) hθne
    rw [← hzθ] at this
    have hl := Real.log_lt_log (mul_pos (hc₁ i) (hc₂ i)) this
    rw [Real.log_mul (hc₁ i).ne' (hc₂ i).ne', Real.log_pow] at hl
    push_cast at hl; linarith
  have hsum : 2 * ∑ j, w j * -Real.log (cos (theta κ m z j)) <
      ∑ j, w j * -Real.log (cos (theta κ m y₁ j)) + ∑ j, w j * -Real.log (cos (theta κ m y₂ j)) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_lt_sum
    · intro j _
      have := mul_le_mul_of_nonneg_left (hterm j) (hw j).le
      linarith
    · exact ⟨i, mem_univ i, by have := mul_lt_mul_of_pos_left hstrict (hw i); linarith⟩
  have hlin : 2 * (t * (c ⬝ᵥ z)) = t * (c ⬝ᵥ y₁) + t * (c ⬝ᵥ y₂) := by
    simp only [z, dotProduct_smul, dotProduct_add, smul_eq_mul]; ring
  have h1 := hmin₁ z hz
  have h2 := hmin₂ z hz
  unfold centerObj at h1 h2
  linarith

/-- **Existence of the frozen-weight center** given a strictly feasible point. -/
theorem center_exists (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i) {x₀ : Fin M → ℝ}
    (hx₀ : x₀ ∈ Feasible A b κ m) :
    ∃ y ∈ Feasible A b κ m, ∀ y' ∈ Feasible A b κ m,
      centerObj κ m c w t y ≤ centerObj κ m c w t y' := by
  set F := centerObj κ m c w t
  set B₀ := F x₀
  -- the linear term is bounded on the box
  set T : ℝ := |t| * ∑ i, |c i| * (|m i| + π / (2 * κ i))
  have hbox : ∀ y, Interior κ m y → ∀ i, |y i| ≤ |m i| + π / (2 * κ i) := fun y hy i => by
    have h := hy i
    simp only [theta, abs_mul, abs_of_pos (hκ i)] at h
    have : |y i - m i| ≤ π / (2 * κ i) := by
      rw [le_div_iff₀ (by have := hκ i; positivity)]; nlinarith [hκ i]
    have := abs_sub_abs_le_abs_sub (y i) (m i)
    linarith
  have hlin : ∀ y, Interior κ m y → -T ≤ t * (c ⬝ᵥ y) := fun y hy => by
    have : |t * (c ⬝ᵥ y)| ≤ T := by
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbox y hy i) (abs_nonneg _)
    linarith [neg_abs_le (t * (c ⬝ᵥ y))]
  have hterm0 : ∀ y, Interior κ m y → ∀ j, 0 ≤ w j * -Real.log (cos (theta κ m y j)) :=
    fun y hy j => mul_nonneg (hw j).le (neg_nonneg.mpr (Real.log_nonpos
      (cos_theta_pos hy j).le (cos_le_one _)))
  -- sublevel sets keep `cos θᵢ ≥ ηᵢ`
  set η : Fin M → ℝ := fun i => exp (-((B₀ + T) / w i))
  have hη : ∀ y ∈ Feasible A b κ m, F y ≤ B₀ → ∀ i, η i ≤ cos (theta κ m y i) := by
    intro y hy hFy i
    have hc := cos_theta_pos hy.2 i
    have hsingle : w i * -Real.log (cos (theta κ m y i)) ≤
        ∑ j, w j * -Real.log (cos (theta κ m y j)) :=
      single_le_sum (f := fun j => w j * -Real.log (cos (theta κ m y j)))
        (fun j _ => hterm0 y hy.2 j) (mem_univ i)
    have := hlin y hy.2
    have hle : -Real.log (cos (theta κ m y i)) ≤ (B₀ + T) / w i := by
      rw [le_div_iff₀ (hw i)]
      simp only [F, centerObj] at hFy
      linarith
    rw [← exp_log hc]
    exact exp_le_exp.mpr (by linarith)
  -- the compact sublevel region
  set K : Set (Fin M → ℝ) :=
    {y | Aᵀ *ᵥ y = b ∧ ∀ i, |theta κ m y i| ≤ π / 2 ∧ η i ≤ cos (theta κ m y i)}
  have hKint : ∀ y ∈ K, Interior κ m y := fun y hy i => by
    obtain ⟨h1, h2⟩ := hy.2 i
    rcases eq_or_lt_of_le h1 with he | hlt
    · exfalso
      have : cos (theta κ m y i) = 0 := by
        rcases abs_eq (by positivity : (0 : ℝ) ≤ π / 2) |>.mp he with h | h
        · rw [h, cos_pi_div_two]
        · rw [h, cos_neg, cos_pi_div_two]
      have := exp_pos (-((B₀ + T) / w i))
      linarith
    · exact hlt
  have hthc : ∀ i, Continuous fun y : Fin M → ℝ => theta κ m y i := fun i => by
    unfold theta; fun_prop
  have hKeq : K = {y | Aᵀ *ᵥ y = b} ∩ ⋂ i, ({y | |theta κ m y i| ≤ π / 2} ∩
      {y | η i ≤ cos (theta κ m y i)}) := by
    ext y; simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  have hKclosed : IsClosed K := by
    rw [hKeq]
    refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_const) ?_
    exact isClosed_iInter fun i => (isClosed_le (continuous_abs.comp (hthc i))
      continuous_const).inter (isClosed_le continuous_const (continuous_cos.comp (hthc i)))
  have hKbdd : Bornology.IsBounded K := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨∑ i, (|m i| + π / (2 * κ i)), fun y hy => ?_⟩
    refine (pi_norm_le_iff_of_nonneg (sum_nonneg fun i _ => by
      have := hκ i; positivity)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact (hbox y (hKint y hy) i).trans (single_le_sum (f := fun i => |m i| + π / (2 * κ i))
      (fun i _ => by have := hκ i; positivity) (mem_univ i))
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  have hx₀K : x₀ ∈ K := ⟨hx₀.1, fun i => ⟨(hx₀.2 i).le, hη x₀ hx₀ le_rfl i⟩⟩
  have hFcont : ContinuousOn F K := by
    refine (continuousOn_const.mul (by fun_prop)).add (continuousOn_finsetSum _ fun i _ => ?_)
    refine continuousOn_const.mul (ContinuousOn.neg ?_)
    refine ContinuousOn.log (continuous_cos.comp (hthc i)).continuousOn fun y hy => ?_
    exact (cos_theta_pos (hKint y hy) i).ne'
  obtain ⟨y, hyK, hymin⟩ := hKcpt.exists_isMinOn ⟨x₀, hx₀K⟩ hFcont
  refine ⟨y, ⟨hyK.1, hKint y hyK⟩, fun y' hy' => ?_⟩
  by_cases hle : F y' ≤ B₀
  · exact hymin ⟨hy'.1, fun i => ⟨(hy'.2 i).le, hη y' hy' hle i⟩⟩
  · exact (hymin hx₀K).trans (le_of_lt (lt_of_not_ge hle))

end

end ImplicitLP
end CutQueryComplexity
