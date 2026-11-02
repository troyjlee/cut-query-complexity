import CutQueryComplexity.ImplicitLP.GenericQuery.Scalars

/-! # Original finite boxes and the analytic barrier

These lemmas translate the original input assumptions into the barrier's
coordinates. The supplied point gives strict feasibility and a slack floor;
no assertion about future iterates is included in the input interface.
-/

set_option autoImplicit false
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Real
noncomputable section
variable {n me : ℕ}

def kappaPt (D : Data n me) : Point n me := fun i => π / (D.upper i - D.lower i)
def midpointPt (D : Data n me) : Point n me := fun i => (D.lower i + D.upper i) / 2

def ClosedFeasible (G : DiGraph (Fin n)) (D : Data n me)
    (x : Fin (rowCount G me) → ℝ) : Prop :=
  (matrix G D.rows)ᵀ *ᵥ x = D.rhs ∧ ∀ i, vec G D.lower i ≤ x i ∧ x i ≤ vec G D.upper i

theorem scalar_box_walls {l u : ℝ} (h : l < u) :
    (l + u) / 2 - π / (2 * (π / (u - l))) = l ∧
      (l + u) / 2 + π / (2 * (π / (u - l))) = u := by
  have hd : u - l ≠ 0 := (sub_pos.mpr h).ne'
  constructor <;> field_simp [hd, Real.pi_ne_zero] <;> ring

theorem scalar_box_closed {l u x : ℝ} (h : l < u) :
    |π / (u - l) * (x - (l + u) / 2)| ≤ π / 2 ↔ l ≤ x ∧ x ≤ u := by
  have hk : 0 < π / (u - l) := div_pos pi_pos (sub_pos.mpr h)
  have he : π / (u - l) * ((u - l) / 2) = π / 2 := by
    field_simp [(sub_pos.mpr h).ne']
  rw [abs_mul, abs_of_pos hk, ← he, mul_le_mul_iff_right₀ hk, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem scalar_box_interior {l u x : ℝ} (h : l < u) :
    |π / (u - l) * (x - (l + u) / 2)| < π / 2 ↔ l < x ∧ x < u := by
  have hk : 0 < π / (u - l) := div_pos pi_pos (sub_pos.mpr h)
  have he : π / (u - l) * ((u - l) / 2) = π / 2 := by
    field_simp [(sub_pos.mpr h).ne']
  rw [abs_mul, abs_of_pos hk, ← he, mul_lt_mul_iff_right₀ hk, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

variable {G : DiGraph (Fin n)} {D : Data n me} {P : Envelope}

theorem kappa_pos (H : PublicHyp D P) (i : Fin (rowCount G me)) :
    0 < vec G (kappaPt D) i :=
  div_pos pi_pos (sub_pos.mpr (H.width_pos _ (rowIndex_used _)))

theorem barrier_width (H : PublicHyp D P) (i : Fin (rowCount G me)) :
    π / vec G (kappaPt D) i ≤ P.U := by
  let j := rowIndex ((rowEquiv G me).symm i)
  have hw : D.upper j - D.lower j ≠ 0 := (sub_pos.mpr (H.width_pos j (rowIndex_used _))).ne'
  have he : π / (π / (D.upper j - D.lower j)) = D.upper j - D.lower j := by
    field_simp [Real.pi_ne_zero, hw]
  change π / (π / (D.upper j - D.lower j)) ≤ P.U
  rw [he]
  exact H.width_le j (rowIndex_used _)

theorem box_closed_iff (H : PublicHyp D P) (x : Fin (rowCount G me) → ℝ) :
    (∀ i, |theta (vec G (kappaPt D)) (vec G (midpointPt D)) x i| ≤ π / 2) ↔
      ∀ i, vec G D.lower i ≤ x i ∧ x i ≤ vec G D.upper i := by
  apply forall_congr'
  intro i
  exact scalar_box_closed (H.width_pos _ (rowIndex_used _))

theorem original_slack (H : PublicHyp D P) (x : Fin (rowCount G me) → ℝ)
    (i : Fin (rowCount G me)) :
    slk (vec G (kappaPt D)) (vec G (midpointPt D)) x i =
      min (x i - vec G D.lower i) (vec G D.upper i - x i) := by
  have hw := scalar_box_walls (H.width_pos _ (rowIndex_used ((rowEquiv G me).symm i)))
  have hs := slack_eq (xi := x i) (mi := vec G (midpointPt D) i) (kappa_pos H i)
  change min (x i - ((D.lower _ + D.upper _) / 2 - π / (2 * (π / (D.upper _ - D.lower _)))))
    (((D.lower _ + D.upper _) / 2 + π / (2 * (π / (D.upper _ - D.lower _)))) - x i) = _ at hs
  rw [hw.1, hw.2] at hs
  exact hs.symm

theorem initial_feasible (H : PublicHyp D P) (HG : HonestInput G D P) :
    vec G D.initial ∈ Feasible (matrix G D.rows) D.rhs
      (vec G (kappaPt D)) (vec G (midpointPt D)) := by
  refine ⟨HG.initial_feasible, fun i => ?_⟩
  have hU : 0 < P.U := by linarith [H.U_ge]
  apply (scalar_box_interior (H.width_pos _ (rowIndex_used _))).mpr
  constructor
  · exact sub_pos.mp ((one_div_pos.mpr hU).trans_le (HG.initial_lower i))
  · have := HG.initial_upper i
    exact sub_pos.mp ((one_div_pos.mpr hU).trans_le this)

theorem initial_slack (H : PublicHyp D P) (HG : HonestInput G D P)
    (i : Fin (rowCount G me)) :
    1 / P.U ≤ slk (vec G (kappaPt D)) (vec G (midpointPt D)) (vec G D.initial) i := by
  rw [original_slack H]
  exact le_min (HG.initial_lower i) (HG.initial_upper i)

theorem cost_norm_le (H : PublicHyp D P) : ‖vec G D.cost‖ ≤ P.U := by
  apply (pi_norm_le_iff_of_nonneg (by linarith [H.U_ge])).mpr
  intro i
  simpa only [Real.norm_eq_abs, vec] using
    (H.coordinate_bound _ (rowIndex_used ((rowEquiv G me).symm i))).2.2.1

#print axioms box_closed_iff
#print axioms original_slack
#print axioms initial_feasible
#print axioms initial_slack
#print axioms cost_norm_le

end
end CutQueryComplexity.ImplicitLP.GenericQuery
