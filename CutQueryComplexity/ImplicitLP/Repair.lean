import CutQueryComplexity.ImplicitLP.Movement

/-! # Exact feasibility repair through the explicit `+I_r` rows (`lem:numeric`, D7)

The LP contains explicit rows `+e_j`, `j ∈ [r]`, at public positions `ι j` (`IdRows`). The
selector `R_*` (`selector`) puts a `1` at `(ι j, j)`, so `AᵀR_* = I_r` (`selector_spec`). For an
approximate direction `h̃`, the repaired direction `d = h̃ − R_* Aᵀh̃` satisfies `Aᵀd = 0`
exactly (`repair_feasible`). When `Aᵀh = 0`,
`d − h = (h̃ − h) − R_* Aᵀ(h̃ − h)`, hence `‖d − h‖_∞ ≤ (1 + √2 M)‖h̃ − h‖_∞` if every entry of `A`
is at most `√2` in absolute value (`repair_error`). Finally
`N_w(S(d − h)) ≤ (1 + C√(Σw)) · max S · (1 + √2 M) ‖h̃ − h‖_∞` (`repair_mixed`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset

noncomputable section

variable {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ}

/-- `A` contains the explicit rows `e_j` at the injective positions `ι j`. -/
def IdRows (A : Matrix (Fin M) (Fin r) ℝ) (ι : Fin r → Fin M) : Prop :=
  Function.Injective ι ∧ ∀ j, A (ι j) = Pi.single j 1

/-- The selector `R_*` of the explicit identity rows. -/
def selector (ι : Fin r → Fin M) : Matrix (Fin M) (Fin r) ℝ :=
  fun i j => if i = ι j then 1 else 0

theorem selector_spec {ι : Fin r → Fin M} (hι : IdRows A ι) : Aᵀ * selector ι = 1 := by
  ext j k
  simp only [mul_apply, transpose_apply, selector, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' univ (ι k)]
  simp only [mem_univ, ↓reduceIte, hι.2 k]
  by_cases h : j = k
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

theorem selector_mulVec_norm {ι : Fin r → Fin M} (hι : IdRows A ι) (v : Fin r → ℝ) :
    ‖selector ι *ᵥ v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun i => ?_
  have : (selector ι *ᵥ v) i = ∑ j, if i = ι j then v j else 0 := by
    simp only [mulVec, dotProduct, selector, ite_mul, one_mul, zero_mul]
  rw [this]
  by_cases h : ∃ j, i = ι j
  · obtain ⟨j, rfl⟩ := h
    rw [Finset.sum_eq_single j (fun k _ hk => ite_eq_right_iff.mpr fun h => absurd (hι.1 h).symm hk)
      (fun h => absurd (mem_univ j) h)]
    simp only [↓reduceIte]
    exact norm_le_pi_norm v j
  · push Not at h
    rw [Finset.sum_eq_zero fun j _ => ite_eq_right_iff.mpr fun hj => absurd hj (h j), norm_zero]
    exact norm_nonneg v

/-- `‖Aᵀu‖_∞ ≤ √2 M ‖u‖_∞` when every entry of `A` is at most `√2`. -/
theorem transpose_mulVec_norm (hA : ∀ i j, |A i j| ≤ Real.sqrt 2) (u : Fin M → ℝ) :
    ‖Aᵀ *ᵥ u‖ ≤ Real.sqrt 2 * M * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  simp only [mulVec, dotProduct, transpose_apply, Real.norm_eq_abs]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |A i j * u i| ≤ ∑ _i : Fin M, Real.sqrt 2 * ‖u‖ := sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hA i j) (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u i)
          (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * M * ‖u‖ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

variable {ι : Fin r → Fin M}

/-- The repaired direction `d = h̃ − R_* Aᵀ h̃`. -/
def repairDir (A : Matrix (Fin M) (Fin r) ℝ) (ι : Fin r → Fin M) (h' : Fin M → ℝ) :
    Fin M → ℝ :=
  h' - selector ι *ᵥ (Aᵀ *ᵥ h')

/-- **Exact feasibility of the repaired direction.** -/
theorem repair_feasible (hι : IdRows A ι) (h' : Fin M → ℝ) : Aᵀ *ᵥ repairDir A ι h' = 0 := by
  rw [repairDir, mulVec_sub, mulVec_mulVec, selector_spec hι, one_mulVec, sub_self]

/-- **Repair error:** if `Aᵀh = 0` then `‖d − h‖_∞ ≤ (1 + √2 M)‖h̃ − h‖_∞`. -/
theorem repair_error (hι : IdRows A ι) (hA : ∀ i j, |A i j| ≤ Real.sqrt 2) {h h' : Fin M → ℝ}
    (hh : Aᵀ *ᵥ h = 0) : ‖repairDir A ι h' - h‖ ≤ (1 + Real.sqrt 2 * M) * ‖h' - h‖ := by
  have e : repairDir A ι h' - h = (h' - h) - selector ι *ᵥ (Aᵀ *ᵥ (h' - h)) := by
    rw [repairDir, mulVec_sub Aᵀ, hh, sub_zero]; abel
  rw [e]
  calc ‖(h' - h) - selector ι *ᵥ (Aᵀ *ᵥ (h' - h))‖
      ≤ ‖h' - h‖ + ‖selector ι *ᵥ (Aᵀ *ᵥ (h' - h))‖ := norm_sub_le _ _
    _ ≤ ‖h' - h‖ + Real.sqrt 2 * M * ‖h' - h‖ :=
        add_le_add le_rfl ((selector_mulVec_norm hι _).trans (transpose_mulVec_norm hA _))
    _ = (1 + Real.sqrt 2 * M) * ‖h' - h‖ := by ring

/-- **Repair error in the mixed norm:** with `0 < Sᵢ ≤ S̄` and `Σ w ≤ W̄`,
`N_w(S(d − h)) ≤ (1 + C√W̄) S̄ (1 + √2 M) ‖h̃ − h‖_∞`. -/
theorem repair_mixed (hι : IdRows A ι) (hA : ∀ i j, |A i j| ≤ Real.sqrt 2) {h h' : Fin M → ℝ}
    (hh : Aᵀ *ᵥ h = 0) {C Sbar Wbar : ℝ} {S w : Fin M → ℝ} (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i)
    (hS0 : ∀ i, 0 ≤ S i) (hSbar : 0 ≤ Sbar) (hS : ∀ i, S i ≤ Sbar) (hW : ∑ i, w i ≤ Wbar) :
    mixed C w (fun i => S i * (repairDir A ι h' - h) i) ≤
      (1 + C * Real.sqrt Wbar) * Sbar * ((1 + Real.sqrt 2 * M) * ‖h' - h‖) := by
  set v := repairDir A ι h' - h
  have hv := repair_error hι hA hh (h' := h')
  have hSv : ∀ i, |S i * v i| ≤ Sbar * ‖v‖ := fun i => by
    rw [abs_mul, abs_of_nonneg (hS0 i)]
    exact mul_le_mul (hS i) (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i)
      (abs_nonneg _) ((hS0 i).trans (hS i))
  have hinf : ‖fun i => S i * v i‖ ≤ Sbar * ‖v‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by rw [Real.norm_eq_abs]; exact hSv i
  have hw2 : wnorm w (fun i => S i * v i) ≤ Real.sqrt Wbar * (Sbar * ‖v‖) := by
    unfold wnorm
    rw [← Real.sqrt_sq (by positivity : 0 ≤ Sbar * ‖v‖), ← Real.sqrt_mul (by
      exact (sum_nonneg fun i _ => hw i).trans hW)]
    apply Real.sqrt_le_sqrt
    have hsq : ∀ i, (S i * v i) ^ 2 ≤ (Sbar * ‖v‖) ^ 2 := fun i => by
      rw [← sq_abs (S i * v i)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hSv i) 2
    calc ∑ i, w i * (S i * v i) ^ 2 ≤ ∑ i, w i * (Sbar * ‖v‖) ^ 2 := sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hsq i) (hw i)
      _ = (∑ i, w i) * (Sbar * ‖v‖) ^ 2 := by rw [sum_mul]
      _ ≤ Wbar * (Sbar * ‖v‖) ^ 2 := mul_le_mul_of_nonneg_right hW (sq_nonneg _)
  unfold mixed
  calc ‖fun i => S i * v i‖ + C * wnorm w (fun i => S i * v i)
      ≤ Sbar * ‖v‖ + C * (Real.sqrt Wbar * (Sbar * ‖v‖)) :=
        add_le_add hinf (mul_le_mul_of_nonneg_left hw2 hC)
    _ = (1 + C * Real.sqrt Wbar) * Sbar * ‖v‖ := by ring
    _ ≤ (1 + C * Real.sqrt Wbar) * Sbar * ((1 + Real.sqrt 2 * M) * ‖h' - h‖) :=
        mul_le_mul_of_nonneg_left hv (by positivity)

end

end ImplicitLP
end CutQueryComplexity
