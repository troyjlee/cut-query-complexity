import CutQueryComplexity.ImplicitLP.PathFollowing.Initialization
import CutQueryComplexity.ImplicitLP.PathFollowing.Budget
import CutQueryComplexity.DirectedMincut.GlobalReduction
import CutQueryComplexity.Sparsify.Params

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! # Initialization followed by an actual path run

The initial invariant is proved by the rounded Lewis program. The artificial cost is
constructed from its output and carried with the final public state. This closes the
first path phase without assuming an initial or full-run invariant. A numerical frozen
centering loop derives its own endpoint centrality and objective bounds. `pathSolver` composes
both paths and the cost switch. The concrete terminal box and extraction are composed in
`terminalSolver`; public scalar calibration and the global asymptotic bound remain separate.
-/

namespace CutQueryComplexity.ImplicitLP.PathFollowing

open Matrix Finset Real
open DirectedMincut (LPPoint)
open Probability
open scoped ENNReal
noncomputable section

/-- The exact centrality loss when changing the public objective vector. -/
theorem cent_cost_change {M r : ℕ} {C : ℝ} {A : Matrix (Fin M) (Fin r) ℝ}
    {S dφ c c' w : Fin M → ℝ} (hC : 0 < C) (hA : (Aᵀ * A).det ≠ 0)
    (hS : ∀ i, 0 < S i) (hw : ∀ i, 0 < w i) (t : ℝ) :
    cent C A S dφ c' t w ≤ cent C A S dφ c t w +
      |t| * mixed C w (fun i => (c' i - c i) / (w i * S i)) := by
  obtain ⟨ν, hν⟩ := cent_attained (c := c) (dφ := dφ) hC hA hS t hw
  refine (ciInf_le (cent_bdd (A := A) (S := S) (dφ := dφ) (c := c') hC.le t w) ν).trans ?_
  have hsplit : (fun i => (t * c' i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i)) =
      (fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i)) +
        t • (fun i => (c' i - c i) / (w i * S i)) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit]
  refine (mixed_add_le hC.le (fun i => (hw i).le) _ _).trans ?_
  rw [mixed_smul, ← hν]

/-- A repaired inexact frozen-weight step contracts centrality and controls the moving
Lewis window. Its error is a direction error, as certified by the numerical primitive;
no centrality or window assertion about the output is assumed. -/
theorem center_step_inexact {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ}
    {b : Fin r → ℝ} {κ m c w y : Fin M → ℝ} {t L c₀ η D : ℝ}
    (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) (hL : 2 ≤ L)
    (hLM : Real.logb 2 (2 * M) ≤ L - 1) (hκ : ∀ i, 0 < κ i)
    (hc₀ : 0 ≤ c₀) (hcM : c₀ ≤ 1 / (2 * M))
    (hy : y ∈ Feasible A b κ m) (hw : ∀ i, 0 < w i)
    (hwin : ∀ i, |Real.log (w i) - Real.log (gfun κ m (1 - 1 / L) c₀ A y i)| ≤ 1 / 5)
    (hδ : cent (48 * (2 * L)) A (barS κ m y) (barDphi κ m y) c t w ≤ D)
    (hD : D ≤ 1 / 1000)
    {e : Fin M → ℝ} (hAe : Aᵀ *ᵥ e = 0)
    (he : mixed (48 * (2 * L)) w (fun i => barS κ m y i * e i) ≤ η)
    (hη : η ≤ D / 64) :
    let h := newtonDir A w (barS κ m y) (fun i => t * c i + w i * barDphi κ m y i)
    y + (h + e) ∈ Feasible A b κ m ∧
      cent (48 * (2 * L)) A (barS κ m (y + (h + e)))
        (barDphi κ m (y + (h + e))) c t w ≤ 8 * D ^ 2 + 4 * η ∧
      (∀ i, |Real.log (gfun κ m (1 - 1 / L) c₀ A (y + (h + e)) i) -
        Real.log (gfun κ m (1 - 1 / L) c₀ A y i)| ≤ 2 * D) ∧
      ∀ i, barS κ m y i * |(h + e) i| ≤ 2 * D := by
  intro h
  let δ := D
  set C : ℝ := 48 * (2 * L)
  set g := gfun κ m (1 - 1 / L) c₀ A y
  have hC : 0 < C := by positivity
  have hS : ∀ i, 0 < barS κ m y i := barS_pos hκ hy.2
  have hg : ∀ i, 0 < g i := fun i => add_pos_of_pos_of_nonneg (exp_pos _) hc₀
  obtain ⟨he1, he2⟩ := exp_fifth_bounds
  have hwg : ∀ i, w i ≤ exp (1 / 5) * g i ∧ g i ≤ exp (1 / 5) * w i := fun i => by
    have h1 := abs_le.mp (hwin i)
    constructor
    · rw [← exp_log (hw i), ← exp_log (hg i), ← exp_add, exp_le_exp]; linarith
    · rw [← exp_log (hw i), ← exp_log (hg i), ← exp_add, exp_le_exp]; linarith
  have hlo : ∀ i, 4 / 5 * g i ≤ w i := fun i => by
    have := (hwg i).2
    have h' : g i * exp (-(1 / 5)) ≤ w i := by
      rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]; linarith
    nlinarith [hg i]
  have hhi : ∀ i, w i ≤ 5 / 4 * g i := fun i => by nlinarith [(hwg i).1, hg i]
  obtain ⟨hh1, hh2⟩ := newtonDir_spec hA (q := fun i => t * c i + w i * barDphi κ m y i) hw hS
  have hproj := eq_projection_note hA hrow hL hLM hκ hc₀ hcM hy.2 hlo hhi hh1 hh2
  have hγ : 1 + 1 / (16 * (2 * L)) ≤ 17 / 16 := by
    have : 1 / (16 * (2 * L)) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hδ0 : 0 ≤ δ := (cent_nonneg hC.le t w).trans hδ
  have hη0 : 0 ≤ η := (mixed_nonneg hC.le _).trans he
  have hSh : mixed C w (fun i => barS κ m y i * h i) ≤
      (1 + 1 / (16 * (2 * L))) * δ :=
    hproj.2.trans (mul_le_mul_of_nonneg_left hδ (by positivity))
  have hnew := eq_newton hκ hC hy.2 hw hh1 hh2 hAe (by positivity) hγ hδ0 hSh he
    (by nlinarith [mul_le_mul_of_nonneg_right hγ hδ0])
  obtain ⟨hint, hfeas, hcent⟩ := hnew
  have hd : mixed C w (fun i => barS κ m y i * (h + e) i) ≤ (17 / 16) * δ + η := by
    have hsplit : (fun i => barS κ m y i * (h + e) i) =
        (fun i => barS κ m y i * h i) + (fun i => barS κ m y i * e i) := by
      ext i
      simp only [Pi.add_apply]
      ring
    rw [hsplit]
    exact (mixed_add_le hC.le (fun i => (hw i).le) _ _).trans
      (add_le_add (hSh.trans (mul_le_mul_of_nonneg_right hγ hδ0)) he)
  have hdcoord : ∀ i, barS κ m y i * |(h + e) i| ≤ 2 * δ := fun i => by
    have h1 : |barS κ m y i * (h + e) i| ≤
        mixed C w (fun i => barS κ m y i * (h + e) i) := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (fun j => barS κ m y j * (h + e) j) i).trans (norm_le_mixed hC.le _)
    rw [abs_mul, abs_of_pos (hS i)] at h1
    linarith
  refine ⟨⟨by rw [mulVec_add, hy.1, hfeas, add_zero], hint⟩, hcent, ?_, hdcoord⟩
  intro i
  have hseg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Interior κ m (y + τ • (h + e)) := fun τ hτ =>
    segment_interior hκ hy.2 (fun i => by linarith [hdcoord i]) hτ
  have hv : mixed C g (fun i => barS κ m y i * (h + e) i) ≤
      exp (1 / 5 / 2) * ((17 / 16) * δ + η) :=
    (mixed_le_of_le_exp hC.le (by norm_num) (fun i => (hwg i).2) _).trans
      (mul_le_mul_of_nonneg_left hd (exp_pos _).le)
  have he10 : exp (1 / 5 / 2 : ℝ) ≤ 5 / 4 := (exp_le_exp.mpr (by norm_num)).trans he1
  have hv' : mixed C g (fun i => barS κ m y i * (h + e) i) ≤
      (5 / 4) * ((17 / 16) * δ + η) :=
    hv.trans (mul_le_mul_of_nonneg_right he10 (by positivity))
  have hv1 : mixed C g (fun i => barS κ m y i * (h + e) i) ≤ 1 / 10 := by nlinarith
  have hgm := eq_gmove_note hA hrow hL hκ hc₀ hseg hv1
  set v := mixed C g (fun i => barS κ m y i * (h + e) i)
  have hv0 : 0 ≤ v := mixed_nonneg hC.le _
  have hvδ : v ≤ (3 / 2) * δ := by nlinarith
  have hvsmall : v ≤ 1 / 500 := by linarith
  have hbound : (1 - 1 / (2 * L) + 4 * v) * v ≤ 2 * δ := by
    have ha : 0 ≤ 1 / (2 * L) := by positivity
    nlinarith [mul_nonneg ha hv0, mul_nonneg hv0 (sub_nonneg.mpr hvsmall)]
  have hcoord : |Real.log (gfun κ m (1 - 1 / L) c₀ A (y + (h + e)) i) - Real.log (g i)| ≤
      mixed C g (fun i => Real.log (gfun κ m (1 - 1 / L) c₀ A (y + (h + e)) i) - Real.log (g i)) := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (fun j =>
      Real.log (gfun κ m (1 - 1 / L) c₀ A (y + (h + e)) j) - Real.log (g j)) i).trans
      (norm_le_mixed hC.le _)
  exact hcoord.trans (hgm.trans hbound)

/-- A frozen center has objective gap at most `sum w / t`, even against a feasible
comparator on the closed boundary of the box. The midpoint supplies a legal interior
direction for the already proved stationarity theorem. -/
theorem center_gap_closed {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ}
    {b : Fin r → ℝ} {κ m c w xbar v : Fin M → ℝ} {t : ℝ}
    (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 ≤ w i) (ht : 0 < t)
    (hxbar : xbar ∈ Feasible A b κ m)
    (hmin : ∀ y ∈ Feasible A b κ m, centerObj κ m c w t xbar ≤ centerObj κ m c w t y)
    (hv : Aᵀ *ᵥ v = b) (hbox : ∀ i, |theta κ m v i| ≤ π / 2) :
    c ⬝ᵥ xbar - c ⬝ᵥ v ≤ (∑ i, w i) / t := by
  let z := (1 / 2 : ℝ) • (v + xbar)
  have hz : z ∈ Feasible A b κ m := by
    constructor
    · simp only [z, mulVec_smul, mulVec_add, hv, hxbar.1]
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    · intro i
      rw [theta_midpoint]
      calc |(theta κ m v i + theta κ m xbar i) / 2| ≤
            (|theta κ m v i| + |theta κ m xbar i|) / 2 := by
              rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
              exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
        _ < π / 2 := by linarith [hbox i, hxbar.2 i]
  have hstat := center_stationary hxbar hz hmin
  have hzsub : z - xbar = (1 / 2 : ℝ) • (v - xbar) := by
    ext i
    simp only [z, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hsum : (∑ j, w j * barDphi κ m xbar j * ((1 / 2 : ℝ) * (v - xbar) j)) =
      (1 / 2 : ℝ) * ∑ j, w j * barDphi κ m xbar j * (v - xbar) j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hstat' : t * (c ⬝ᵥ (v - xbar)) +
      ∑ j, w j * barDphi κ m xbar j * (v - xbar) j = 0 := by
    change t * (c ⬝ᵥ (z - xbar)) +
      ∑ j, w j * barDphi κ m xbar j * (z - xbar) j = 0 at hstat
    rw [hzsub] at hstat
    simp only [dotProduct_smul, Pi.smul_apply, smul_eq_mul] at hstat
    rw [hsum] at hstat
    linarith
  have hle : ∑ j, w j * barDphi κ m xbar j * (v - xbar) j ≤ ∑ j, w j := by
    apply sum_le_sum
    intro i _
    have hi := (barrier_bounds (hκ i) (hxbar.2 i)).2.2.2.2.2 (theta κ m v i) (hbox i)
    have he : (theta κ m v i - theta κ m xbar i) / κ i = v i - xbar i := by
      unfold theta
      field_simp [(hκ i).ne']
      ring
    rw [he] at hi
    change κ i * tan (theta κ m xbar i) * (v i - xbar i) ≤ 1 at hi
    have := mul_le_mul_of_nonneg_left hi (hw i)
    simpa only [mul_one, Pi.sub_apply, barDphi, mul_assoc] using this
  rw [dotProduct_sub] at hstat'
  rw [le_div_iff₀ ht]
  nlinarith

/-- The objective perturbation is controlled in the same infinity norm used by `lem_center`. -/
theorem objective_distance {M : ℕ} (c x y : Fin M → ℝ) :
    |c ⬝ᵥ x - c ⬝ᵥ y| ≤ (∑ i, |c i|) * ‖x - y‖ := by
  rw [← dotProduct_sub]
  calc |c ⬝ᵥ (x - y)| ≤ ∑ i, |c i * (x - y) i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * ‖x - y‖ := by
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
    _ = (∑ i, |c i|) * ‖x - y‖ := (sum_mul ..).symm

/-- Analytic endpoint against every closed feasible comparator. Small final centrality is
an explicit remaining input; this theorem does not assume an optimizer or an LP solver. -/
theorem objective_gap_from_centrality {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ}
    {b : Fin r → ℝ} {κ m c w x v : Fin M → ℝ} {t L c₀ U : ℝ}
    (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) (hL : 2 ≤ L)
    (hLM : Real.logb 2 (2 * M) ≤ L - 1) (hκ : ∀ i, 0 < κ i)
    (hc₀ : 0 ≤ c₀) (hcM : c₀ ≤ 1 / (2 * M)) (hU : 0 ≤ U)
    (hwidth : ∀ i, π / κ i ≤ U) (hx : x ∈ Feasible A b κ m)
    (hw : ∀ i, 0 < w i) (ht : 0 < t)
    (hwin : ∀ i, |Real.log (w i) - Real.log (gfun κ m (1 - 1 / L) c₀ A x i)| ≤ 1 / 20)
    (hδ : cent (48 * (2 * L)) A (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hv : Aᵀ *ᵥ v = b) (hbox : ∀ i, |theta κ m v i| ≤ π / 2) :
    c ⬝ᵥ x - c ⬝ᵥ v ≤ (∑ i, w i) / t +
      (∑ i, |c i|) * (4 * U * cent (48 * (2 * L)) A (barS κ m x) (barDphi κ m x) c t w) := by
  obtain ⟨xbar, hxbar, hmin⟩ := center_exists (c := c) (t := t) hκ hw hx
  have hcenter := center_gap_closed hκ (fun i => (hw i).le) ht hxbar hmin hv hbox
  have hclose := (lem_center hA hrow hL hLM hκ hc₀ hcM hU hwidth hx hw hwin hδ hxbar hmin).2
  have herror := (objective_distance c x xbar).trans
    (mul_le_mul_of_nonneg_left hclose (sum_nonneg fun i _ => abs_nonneg (c i)))
  linarith [le_abs_self (c ⬝ᵥ x - c ⬝ᵥ xbar)]

/-- The actual terminal LP box, represented without hidden multiplicities. -/
def terminalRadius (n : ℕ) : LPPoint (Fin n) :=
  ⟨fun _ _ => 1, n + 1, fun _ => 2 * n, fun _ => 2 * n⟩

def terminalMid (n : ℕ) : LPPoint (Fin n) :=
  ⟨fun _ _ => 0, n - 1, fun _ => 2 * n, fun _ => 2 * n⟩

def terminalKappa (n : ℕ) : LPPoint (Fin n) :=
  mapPt (fun r => π / (2 * r)) (terminalRadius n)

def terminalCost (n : ℕ) : LPPoint (Fin n) :=
  ⟨fun _ _ => 0, -1 / 2, fun _ => 1, fun _ => 1⟩

theorem angle_radius_le {r m x : ℝ} (hr : 0 < r) :
    |π / (2 * r) * (x - m)| ≤ π / 2 ↔ m - r ≤ x ∧ x ≤ m + r := by
  have hk : 0 < π / (2 * r) := div_pos pi_pos (by positivity)
  have he : π / (2 * r) * r = π / 2 := by
    rw [div_mul_eq_mul_div₀, mul_div_mul_right _ _ hr.ne']
  rw [abs_mul, abs_of_pos hk, ← he, mul_le_mul_iff_right₀ hk, abs_le]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

theorem slack_radius {r m x : ℝ} (hr : 0 < r) :
    (π / 2 - |π / (2 * r) * (x - m)|) / (π / (2 * r)) = r - |x - m| := by
  have hk : 0 < π / (2 * r) := div_pos pi_pos (by positivity)
  have he : π / (2 * r) * r = π / 2 := by
    rw [div_mul_eq_mul_div₀, mul_div_mul_right _ _ hr.ne']
  rw [abs_mul, abs_of_pos hk, div_eq_iff hk.ne', ← he]
  ring

variable {n : ℕ}

theorem terminalKappa_pos (G : DiGraph (Fin n)) (hn : (1 : ℝ) ≤ n) :
    ∀ i, 0 < lpVec G (terminalKappa n) i := by
  have hn0 : (0 : ℝ) < n := by linarith
  intro i
  obtain ⟨row, rfl⟩ := (lpEquiv G).surjective i
  simp only [terminalKappa, lpVec, Equiv.symm_apply_apply]
  rcases row with ⟨p, k⟩ | (_ | (j | j)) <;>
    simp only [lpVal, mapPt, terminalRadius] <;> positivity

/-- A closed feasible terminal point is a legal comparator for the barrier endpoint. -/
theorem terminal_closed (G : DiGraph (Fin n)) (s t : Fin n)
    (hn : (1 : ℝ) ≤ n) {x : LPPoint (Fin n)} (hx : DirectedMincut.Feasible G s t x) :
    (lpA G s t)ᵀ *ᵥ lpVec G x = DirectedMincut.bvec G ∧
      ∀ i, |theta (lpVec G (terminalKappa n)) (lpVec G (terminalMid n)) (lpVec G x) i| ≤ π / 2 := by
  have hn0 : (0 : ℝ) < n := by linarith
  constructor
  · rw [lpA_transpose_lpVec]
    funext v
    exact hx.2.2.2.2.2 v
  · intro i
    obtain ⟨row, rfl⟩ := (lpEquiv G).surjective i
    simp only [theta, terminalKappa, lpVec, Equiv.symm_apply_apply]
    rcases row with ⟨p, k⟩ | (_ | (j | j)) <;>
      simp only [lpVal, mapPt, terminalRadius, terminalMid]
    · exact (angle_radius_le (by norm_num)).mpr (by simpa using hx.1 _ _ p.2)
    · apply (angle_radius_le (by positivity)).mpr
      have hq := hx.2.2.1
      simp only [Fintype.card_fin] at hq
      constructor <;> linarith [hx.2.1]
    · apply (angle_radius_le (by positivity)).mpr
      have hp := hx.2.2.2.1 j
      simp only [Fintype.card_fin] at hp
      constructor <;> linarith [hp.1, hp.2]
    · apply (angle_radius_le (by positivity)).mpr
      have hm := hx.2.2.2.2.1 j
      simp only [Fintype.card_fin] at hm
      constructor <;> linarith [hm.1, hm.2]

/-- The degree-query strict start has slack at least one in the concrete box. -/
theorem strictStart_slack (G : DiGraph (Fin n)) (hG : G.Simple) (hn : (1 : ℝ) ≤ n) :
    ∀ i, 1 ≤ slk (lpVec G (terminalKappa n)) (lpVec G (terminalMid n))
      (lpVec G (strictStartPoint (DirectedMincut.bvec G))) i := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hb : ∀ v, |DirectedMincut.bvec G v| ≤ n - 1 := by
    intro v
    have ho := DirectedMincut.outdeg_le hG v
    have hi := DirectedMincut.indeg_le hG v
    simp only [Fintype.card_fin] at ho hi
    rw [DirectedMincut.bvec, abs_le]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (G.outdeg v),
      Nat.cast_nonneg (α := ℝ) (G.indeg v)]
  intro i
  obtain ⟨row, rfl⟩ := (lpEquiv G).surjective i
  simp only [slk, theta, terminalKappa, lpVec, Equiv.symm_apply_apply]
  rcases row with ⟨p, k⟩ | (_ | (j | j)) <;>
    simp only [lpVal, mapPt, terminalRadius, terminalMid, strictStartPoint]
  · rw [slack_radius (r := 1) (by norm_num)]
    norm_num
  · rw [slack_radius (r := (n : ℝ) + 1) (by positivity), zero_sub, abs_neg,
      abs_of_nonneg (by linarith)]
    linarith
  · rw [slack_radius (r := 2 * (n : ℝ)) (by positivity), add_sub_cancel_left, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hb j]
  · rw [slack_radius (r := 2 * (n : ℝ)) (by positivity), sub_sub_cancel_left, abs_neg, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hb j]

theorem strictStart_barrier_feasible (G : DiGraph (Fin n)) (s t : Fin n)
    (hG : G.Simple) (hn : (1 : ℝ) ≤ n) :
    lpVec G (strictStartPoint (DirectedMincut.bvec G)) ∈
      Feasible (lpA G s t) (DirectedMincut.bvec G)
        (lpVec G (terminalKappa n)) (lpVec G (terminalMid n)) := by
  have hf := (strictStartProg_feasible G s t hG).1
  rw [strictStartProg_eval] at hf
  refine ⟨(terminal_closed G s t hn hf).1, fun i => ?_⟩
  have hs := strictStart_slack G hG hn i
  have hk := terminalKappa_pos G hn i
  rw [slk, le_div_iff₀ hk] at hs
  linarith

/-- Hidden copies have zero objective coefficient; explicit rows give exactly `R-q/2`. -/
theorem terminal_obj (G : DiGraph (Fin n)) (x : LPPoint (Fin n)) :
    lpVec G (terminalCost n) ⬝ᵥ lpVec G x = DirectedMincut.obj x := by
  simp only [dotProduct, lpVec]
  rw [← (lpEquiv G).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [lpVal, terminalCost, DirectedMincut.obj, DirectedMincut.Rsum, sum_add_distrib]
  ring

theorem terminal_cost_sum (G : DiGraph (Fin n)) :
    (∑ i, |lpVec G (terminalCost n) i|) = 2 * n + 1 / 2 := by
  simp only [lpVec]
  rw [← (lpEquiv G).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [lpVal, terminalCost]
  ring

/-- Every concrete terminal box has width at most `4n`. -/
theorem terminal_width_le (G : DiGraph (Fin n)) (hn : (1 : ℝ) ≤ n) :
    ∀ i, π / lpVec G (terminalKappa n) i ≤ 4 * n := by
  intro i
  obtain ⟨row, rfl⟩ := (lpEquiv G).surjective i
  simp only [terminalKappa, lpVec, Equiv.symm_apply_apply]
  rcases row with ⟨p, k⟩ | (_ | (j | j)) <;>
    simp only [lpVal, mapPt, terminalRadius, div_div_cancel₀ pi_ne_zero] <;> linarith

theorem terminal_cost_norm (G : DiGraph (Fin n)) : ‖lpVec G (terminalCost n)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
  obtain ⟨row, rfl⟩ := (lpEquiv G).surjective i
  simp only [lpVec, Equiv.symm_apply_apply, Real.norm_eq_abs]
  rcases row with ⟨p, k⟩ | (_ | (j | j)) <;> norm_num [lpVal, terminalCost]

/-- A public polynomial bound on the actual hidden-plus-explicit row count. -/
theorem terminal_rows_le (G : DiGraph (Fin n)) (hG : G.Simple) :
    lpM G ≤ 2 * n ^ 2 + 2 * n + 1 := by
  have hp : Fintype.card (CPair n) ≤ n ^ 2 := by
    have h := Fintype.card_subtype_le (fun p : Fin n × Fin n => p.1 < p.2)
    simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h
  have hs : (∑ p : CPair n, G.sym p.1.1 p.1.2) ≤ 2 * Fintype.card (CPair n) := by
    calc (∑ p : CPair n, G.sym p.1.1 p.1.2) ≤ ∑ _p : CPair n, 2 := by
          apply sum_le_sum
          intro p _
          unfold DiGraph.sym
          have := hG p.1.1 p.1.2
          have := hG p.1.2 p.1.1
          omega
      _ = _ := by simp [mul_comm]
  simp only [lpM, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
    Fintype.card_unit]
  omega

theorem terminal_sym_le (G : DiGraph (Fin n)) (hG : G.Simple) :
    ∀ e, (Spanner.symS G e : ℝ) ≤ 2 := by
  intro e
  induction e using Sym2.ind with
  | h u v =>
      have h : G.sym u v ≤ 2 := by
        unfold DiGraph.sym
        have := hG u v
        have := hG v u
        omega
      exact_mod_cast h

/-- The analytic feasible endpoint produces a feasible terminal point after public clipping. -/
theorem terminal_clip_feasible (G : DiGraph (Fin n)) (s t : Fin n)
    (hn : (1 : ℝ) ≤ n) {x : LPPoint (Fin n)}
    (hx : lpVec G x ∈ Feasible (lpA G s t) (DirectedMincut.bvec G)
      (lpVec G (terminalKappa n)) (lpVec G (terminalMid n))) :
    DirectedMincut.Feasible G s t (clipPairPoint x) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hbox : ∀ row : LPRow G,
      |π / (2 * lpVal G (terminalRadius n) row) *
        (lpVal G x row - lpVal G (terminalMid n) row)| ≤ π / 2 := by
    intro row
    have h := (hx.2 ((lpEquiv G) row)).le
    rw [theta, terminalKappa, lpVec_mapPt] at h
    simpa only [lpVec, Equiv.symm_apply_apply] using h
  apply clipPairPoint_feasible G s t x hx.1
  · intro i e hi
    obtain ⟨row, rfl⟩ := (lpEquiv G).surjective i
    rcases row with ⟨p, k⟩ | (_ | (j | j))
    · have h := (angle_radius_le (r := 1) (by norm_num)).mp (hbox (.inl ⟨p, k⟩))
      simpa only [lpVec, Equiv.symm_apply_apply, lpVal, terminalRadius, terminalMid,
        zero_sub, zero_add] using h
    all_goals simp [lpHidF, lpHid] at hi
  · have h := (angle_radius_le (r := (n : ℝ) + 1) (by positivity)).mp (hbox (.inr (.inl ())))
    simp only [lpVal, terminalMid] at h
    constructor <;> linarith [h.1, h.2]
  · intro v
    have h := (angle_radius_le (r := 2 * (n : ℝ)) (by positivity)).mp (hbox (.inr (.inr (.inl v))))
    simp only [lpVal, terminalMid] at h
    constructor <;> linarith [h.1, h.2]
  · intro v
    have h := (angle_radius_le (r := 2 * (n : ℝ)) (by positivity)).mp (hbox (.inr (.inr (.inr v))))
    simp only [lpVal, terminalMid] at h
    constructor <;> linarith [h.1, h.2]

variable {E : NewtonPub} {G : DiGraph (Fin E.n)} {P : Params E} {bc : Fin E.n → ℝ}

/-- A public choice that satisfies both the batch cap and the potential-to-window cap.
The positive-part logarithm keeps this definition positive for every public envelope. -/
def calibratedDelta (L M T : ℝ) : ℝ :=
  min ((1 / (2 * L)) ^ 2 / 2 ^ 16)
    ((1 / (2 * L) / 2 ^ 20) * (1 / (2 * L)) /
      (96 * (max (Real.log (12 * M * T / (1 / (2 * L) / 8))) 0 + 1)))

theorem calibratedDelta_spec {L M T : ℝ} (hL : 2 ≤ L) :
    0 < calibratedDelta L M T ∧
      calibratedDelta L M T ≤ (1 / (2 * L)) ^ 2 / 2 ^ 16 ∧
      Real.log (12 * M * T / (1 / (2 * L) / 8)) /
        ((1 / (2 * L) / 8) / (12 * calibratedDelta L M T)) ≤ 1 / (2 * L) / 2 ^ 20 := by
  let a := 1 / (2 * L)
  let B := 12 * M * T / (a / 8)
  let W := max (Real.log B) 0 + 1
  let D := calibratedDelta L M T
  have ha : 0 < a := by dsimp [a]; positivity
  have hW : 0 < W := by dsimp [W]; have := le_max_right (Real.log B) 0; linarith
  have hD : 0 < D := by
    change 0 < min (a ^ 2 / 2 ^ 16) ((a / 2 ^ 20) * a / (96 * W))
    exact lt_min (by positivity) (by positivity)
  refine ⟨hD, min_le_left _ _, ?_⟩
  have hcap : D ≤ (a / 2 ^ 20) * a / (96 * W) := min_le_right _ _
  have hlog : Real.log B ≤ W := by dsimp [W]; linarith [le_max_left (Real.log B) 0]
  change Real.log B / ((a / 8) / (12 * D)) ≤ a / 2 ^ 20
  have he : Real.log B / ((a / 8) / (12 * D)) = 96 * D * Real.log B / a := by
    field_simp [ha.ne', hD.ne']
    ring
  rw [he]
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) ha.le).trans ?_
  rw [div_le_iff₀ ha]
  have h := (le_div_iff₀ (by positivity : 0 < 96 * W)).mp hcap
  nlinarith

/-- The final accuracy requirement determines a positive direction tolerance without
depending on any run output or on a later precision choice. -/
def calibratedTolerance (L Δ : ℝ) (N : ℕ) : ℝ :=
  min (1 / (2 * L) * Δ / 2 ^ 16) ((1 / 2 : ℝ) ^ N * Δ / 64)

theorem calibratedTolerance_spec {L Δ : ℝ} (hL : 2 ≤ L) (hΔ : 0 < Δ) (N : ℕ) :
    0 < calibratedTolerance L Δ N ∧
      calibratedTolerance L Δ N ≤ 1 / (2 * L) * Δ / 2 ^ 16 ∧
      calibratedTolerance L Δ N ≤ (1 / 2 : ℝ) ^ N * Δ / 64 := by
  exact ⟨lt_min (by positivity) (by positivity), min_le_left _ _, min_le_right _ _⟩

/-- All remaining terminal licensing conditions are public scalar conditions. There is
no graph-dependent reference, geometric premise, state invariant, or solver premise. -/
structure PublicLicense (P : Params E) : Prop where
  vertices : 2 ≤ E.n
  distinct : P.s ≠ P.terminal
  kappa : P.κ = terminalKappa E.n
  midpoint : P.m = terminalMid E.n
  cost : P.c = terminalCost E.n
  L_ge : 2 ≤ P.L
  logM_le : Real.logb 2 (2 * E.Mbar) ≤ P.L - 1
  width : 4 * (E.n : ℝ) ≤ E.U
  rows : 2 * (E.n : ℝ) ^ 2 + 2 * E.n + 1 ≤ E.Mbar
  ε_pos : 0 < E.ε
  ε_le : E.ε ≤ 1
  C_eq : E.C = P.C
  η_pos : 0 < E.η
  η_le : E.η ≤ 1 / (2 * P.L) * P.Δ / 2 ^ 16
  Δ_pos : 0 < P.Δ
  Δ_le : P.Δ ≤ (1 / (2 * P.L)) ^ 2 / 2 ^ 16
  K_nonneg : 0 ≤ P.K
  K_le : P.K ≤ 1 / (2 * P.L) / 2 ^ 20
  window_le : Real.log (12 * E.Mbar * P.T / (1 / (2 * P.L) / 8)) / P.μ ≤ P.K
  vertices_le : E.n ≤ 2 ^ P.Kd
  samples_pos : 0 < P.samples

/-- Construct the entire graph-dependent geometric regime from a public license and
simplicity of the input graph. The reference is the proved strict-start point. -/
def PublicLicense.regime (Q : PublicLicense P) (G : DiGraph (Fin E.n)) (hG : G.Simple) :
    Regime G P (DirectedMincut.bvec G) := by
  have hn : (1 : ℝ) ≤ E.n := by exact_mod_cast (by have := Q.vertices; omega : 1 ≤ E.n)
  have hU : 1 ≤ E.U := by linarith [Q.width]
  refine {
    distinct := Q.distinct
    L_ge := Q.L_ge
    logM_le := Q.logM_le
    κ_pos := ?_
    U_ge := hU
    width_le := ?_
    reference := lpVec G (strictStartPoint (DirectedMincut.bvec G))
    reference_feasible := ?_
    reference_slack := ?_
    M_le := ?_
    ε_pos := Q.ε_pos
    ε_le := Q.ε_le
    cost_le := ?_
    C_eq := Q.C_eq
    η_pos := Q.η_pos
    η_le := Q.η_le
    Δ_pos := Q.Δ_pos
    Δ_le := Q.Δ_le
    K_nonneg := Q.K_nonneg
    K_le := Q.K_le
    window_le := Q.window_le
    Csym := 2
    Csym_nonneg := by norm_num
    sym_le := terminal_sym_le G hG
    vertices_le := Q.vertices_le
    samples_pos := Q.samples_pos }
  · rw [Q.kappa]
    exact terminalKappa_pos G hn
  · rw [Q.kappa]
    exact fun i => (terminal_width_le G hn i).trans Q.width
  · rw [Q.kappa, Q.midpoint]
    exact strictStart_barrier_feasible G P.s P.terminal hG hn
  · rw [Q.kappa, Q.midpoint]
    have hu : 1 / E.U ≤ (1 : ℝ) := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hU
    exact fun i => hu.trans (strictStart_slack G hG hn i)
  · have hm : (lpM G : ℝ) ≤ 2 * (E.n : ℝ) ^ 2 + 2 * E.n + 1 := by
      exact_mod_cast terminal_rows_le G hG
    exact hm.trans Q.rows
  · rw [Q.cost]
    exact (terminal_cost_norm G).trans (by linarith)

/-- The artificial cost has the public norm bound needed by the numerical primitives. -/
theorem artificialCost_bound (H : Regime G P bc) {x X : LPPoint (Fin E.n)}
    (hx : lpVec G x ∈ Feasible (lpA G P.s P.terminal) bc (lpVec G P.κ) (lpVec G P.m))
    (hs : ∀ i, 1 / E.U ≤ slk (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i)
    (hp : pot P.μ (lpVec G X - fun i => Real.log
      (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
        (lpA G P.s P.terminal) (lpVec G x) i)) ≤
      12 * lpM G * P.T / (1 / (2 * P.L) / 8)) :
    ‖lpVec G (artificialCost P.κ P.m x X)‖ ≤ 4 * E.U := by
  have hw := (weight_bounds_of_potential H (st := (x, X)) hp).2.1
  have hU : 0 < E.U := by linarith [H.U_ge]
  rw [lpVec_artificialCost]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (exp_pos _)]
  have hd := (eq_barrier H.κ_pos hx.2 i).2.1
  have hds : |barDphi (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i| ≤ E.U := by
    have hb := mul_le_mul_of_nonneg_left (hs i)
      (abs_nonneg (barDphi (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i))
    change _ ≤ |barDphi (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i| *
      ((π / 2 - |theta (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i|) / lpVec G P.κ i) at hb
    have hdiv : |barDphi (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i| / E.U ≤ 1 := by
      simpa only [mul_one_div] using hb.trans hd
    exact (div_le_one hU).mp hdiv
  exact mul_le_mul (hw i) hds (abs_nonneg _) (by norm_num)

def Regime.withCost (H : Regime G P bc) (cp : LPPoint (Fin E.n))
    (hc : ‖lpVec G cp‖ ≤ 4 * E.U) : Regime G {P with c := cp} bc where
  distinct := H.distinct
  L_ge := H.L_ge
  logM_le := H.logM_le
  κ_pos := H.κ_pos
  U_ge := H.U_ge
  width_le := H.width_le
  reference := H.reference
  reference_feasible := H.reference_feasible
  reference_slack := H.reference_slack
  M_le := H.M_le
  ε_pos := H.ε_pos
  ε_le := H.ε_le
  cost_le := hc
  C_eq := H.C_eq
  η_pos := H.η_pos
  η_le := H.η_le
  Δ_pos := H.Δ_pos
  Δ_le := H.Δ_le
  K_nonneg := H.K_nonneg
  K_le := H.K_le
  window_le := H.window_le
  Csym := H.Csym
  Csym_nonneg := H.Csym_nonneg
  sym_le := H.sym_le
  vertices_le := H.vertices_le
  samples_pos := H.samples_pos

/-- A sufficiently small public parameter lets a successful batch switch to any
licensed public objective, using the batch's proved centrality margin. -/
theorem batchGood_changeCost (H : Regime G P bc) {t : ℝ} {st : State E.n}
    (cp : LPPoint (Fin E.n)) (hcp : ‖lpVec G cp‖ ≤ 4 * E.U)
    (htsmall : |t| * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤ 1 / (2 * P.L) * P.Δ / 2)
    (hg : BatchGood G P.s P.terminal bc (lpVec G P.κ) (lpVec G P.m) (lpVec G P.c)
      t P.L P.c₀ P.Δ P.T (some st)) : Invariant G {P with c := cp} bc t st := by
  obtain ⟨xn, Xn, he, hF, hP, hc⟩ := hg
  have he' : (xn, Xn) = st := Option.some.inj he.symm
  cases he'
  refine ⟨hF, hP, ?_⟩
  have hMb : 0 < E.Mbar := H.rows_pos.trans_le H.M_le
  have hU : 0 < E.U := by linarith [H.U_ge]
  have hweights := (weight_bounds_of_potential H (st := (xn, Xn)) hP).1
  have hS := barS_pos H.κ_pos hF.2
  let q := fun i => (lpVec G cp i - lpVec G P.c i) /
    (exp (lpVec G Xn i) * barS (lpVec G P.κ) (lpVec G P.m) (lpVec G xn) i)
  have hq : ‖q‖ ≤ 32 * E.Mbar * E.U ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have hcp' : |lpVec G cp i| ≤ 4 * E.U := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ i).trans hcp
    have hc' : |lpVec G P.c i| ≤ 4 * E.U := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ i).trans H.cost_le
    have hnum : |lpVec G cp i - lpVec G P.c i| ≤ 8 * E.U :=
      (abs_sub _ _).trans (by linarith)
    have hden : 1 / (4 * E.Mbar * E.U) ≤ exp (lpVec G Xn i) *
        barS (lpVec G P.κ) (lpVec G P.m) (lpVec G xn) i := by
      calc 1 / (4 * E.Mbar * E.U) = (1 / (4 * E.Mbar)) * (1 / E.U) := by ring
        _ ≤ _ := mul_le_mul (hweights i) (barrier_env H.κ_pos hF.2 H.U_ge H.width_le i).1
          (by positivity) (exp_pos _).le
    change |q i| ≤ _
    dsimp [q]
    rw [abs_div, abs_of_pos (mul_pos (exp_pos _) (hS i)),
      div_le_iff₀ (mul_pos (exp_pos _) (hS i))]
    refine hnum.trans ?_
    have hh := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 32 * E.Mbar * E.U ^ 2)
    have heq : (32 * E.Mbar * E.U ^ 2) * (1 / (4 * E.Mbar * E.U)) = 8 * E.U := by
      field_simp [hMb.ne', hU.ne']
      ring
    rwa [heq] at hh
  have hmix : mixed P.C (fun i => exp (lpVec G Xn i)) q ≤ P.T * (32 * E.Mbar * E.U ^ 2) :=
    (mixedEnvelope_of_potential H (st := (xn, Xn)) hP q).trans
      (mul_le_mul_of_nonneg_left hq (by linarith [H.T_ge]))
  have hchange := cent_cost_change (c := lpVec G P.c) (c' := lpVec G cp)
    (dφ := barDphi (lpVec G P.κ) (lpVec G P.m) (lpVec G xn)) H.C_pos
    (det_ne_zero_of_idRows (lpA_idRows G P.s P.terminal)) hS
    (fun i => exp_pos (lpVec G Xn i)) t
  have hnew := hchange.trans (add_le_add hc (mul_le_mul_of_nonneg_left hmix (abs_nonneg t)))
  exact hnew.trans (by nlinarith)

/-- Execute one actual batch and then reinterpret its public state at the new objective. -/
theorem batch_switch_failure (H : Regime G P bc) {t : ℝ} {st : State E.n}
    (cp : LPPoint (Fin E.n)) (hcp : ‖lpVec G cp‖ ≤ 4 * E.U)
    (ht : |t| ≤ 16 * E.n / E.ε)
    (htsmall : |t| * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤ 1 / (2 * P.L) * P.Δ / 2)
    (hs : Invariant G P bc t st) :
    mass ((batch P t st).eval G.out) (fun out => ¬Good G {P with c := cp} bc t out) ≤
      H.batchFailure := by
  rw [batch, RTree.eval_cast]
  refine (mass_mono _ (fun out hbad hg => ?_)).trans (batchProg_fail_public H ht hs)
  have hg' := hg
  obtain ⟨xn, Xn, he, _⟩ := hg
  apply hbad
  refine ⟨(xn, Xn), he, ?_⟩
  rw [he] at hg'
  exact batchGood_changeCost H cp hcp htsmall hg'

def Params.newtonBudget (P : Params E) : ℕ :=
  (P.rounds * Sparsify.levelBudget (n := E.n) P.Kd P.J P.samples + 3 * E.n) +
    6 * E.n * (E.Brhs + E.k * E.Bmv + E.Brep)

/-- One numerical Newton query program with frozen public log weights. -/
def frozenStep (P : Params E) (t : ℝ) (X x : LPPoint (Fin E.n)) :
    RTree (Finset (Fin E.n)) ℕ (LPPoint (Fin E.n)) P.newtonBudget :=
  ((newtonProgPub E P.s P.terminal (pairOf (normDPt P.κ P.m x X).z)
    (normDPt P.κ P.m x X).q (normDPt P.κ P.m x X).yp (normDPt P.κ P.m x X).ym
    (normQPt t P.κ P.m P.c x X) P.Kd P.J P.samples P.rounds).map (addPt x)).cast
      (by unfold Params.newtonBudget; ring)

/-- The final centering loop is a real sequence of the certified numerical programs. -/
def frozenRun (P : Params E) (t : ℝ) (X : LPPoint (Fin E.n)) : (N : ℕ) →
    LPPoint (Fin E.n) → RTree (Finset (Fin E.n)) ℕ (LPPoint (Fin E.n)) (N * P.newtonBudget)
  | 0, x => RTree.pure (PMF.pure x)
  | N + 1, x => ((frozenStep P t X x).bind (frozenRun P t X N)).cast (by ring)

structure FrozenInvariant (G : DiGraph (Fin E.n)) (P : Params E) (bc : Fin E.n → ℝ)
    (t : ℝ) (X : LPPoint (Fin E.n)) (D W : ℝ) (x : LPPoint (Fin E.n)) : Prop where
  feasible : lpVec G x ∈ Feasible (lpA G P.s P.terminal) bc (lpVec G P.κ) (lpVec G P.m)
  centrality : cent P.C (lpA G P.s P.terminal) (barS (lpVec G P.κ) (lpVec G P.m) (lpVec G x))
    (barDphi (lpVec G P.κ) (lpVec G P.m) (lpVec G x)) (lpVec G P.c) t
    (fun i => exp (lpVec G X i)) ≤ D
  window : ∀ i, |lpVec G X i - Real.log
    (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
      (lpA G P.s P.terminal) (lpVec G x) i)| ≤ W

theorem frozenStep_failure (H : Regime G P bc) {t D W : ℝ} {X x : LPPoint (Fin E.n)}
    (ht : |t| ≤ 16 * E.n / E.ε) (hD : D ≤ 1 / 1000) (hW : W ≤ 1 / 20)
    (hη : E.η ≤ D / 64) (hx : FrozenInvariant G P bc t X D W x) :
    mass ((frozenStep P t X x).eval G.out)
      (fun y => ¬FrozenInvariant G P bc t X (D / 2) (W + 2 * D) y) ≤
      d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) := by
  have hA := det_ne_zero_of_idRows (lpA_idRows G P.s P.terminal)
  have hLM : Real.logb 2 (2 * lpM G) ≤ P.L - 1 :=
    (Real.logb_le_logb_of_le (by norm_num) (by have := H.rows_pos; positivity)
      (by linarith [H.M_le])).trans H.logM_le
  have hc₀ : 0 ≤ P.c₀ := by
    have hMb := H.rows_pos.trans_le H.M_le
    unfold Params.c₀
    positivity
  have hw : ∀ i, 0 < exp (lpVec G X i) := fun i => exp_pos _
  have hS := barS_pos H.κ_pos hx.feasible.2
  have hwin : ∀ i, |Real.log (exp (lpVec G X i)) - Real.log
      (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
        (lpA G P.s P.terminal) (lpVec G x) i)| ≤ 1 / 20 := by
    intro i
    rw [Real.log_exp]
    exact (hx.window i).trans hW
  have hDcopy : normD (fun i => exp (lpVec G X i))
      (barS (lpVec G P.κ) (lpVec G P.m) (lpVec G x)) =
      lpD G (pairOf (normDPt P.κ P.m x X).z) (normDPt P.κ P.m x X).q
        (normDPt P.κ P.m x X).yp (normDPt P.κ P.m x X).ym := by
    rw [← lpVec_eq_lpD, lpVec_normDPt]
  have hqcopy : normQ t (lpVec G P.c) (fun i => exp (lpVec G X i))
      (barDphi (lpVec G P.κ) (lpVec G P.m) (lpVec G x)) =
      lpVec G (normQPt t P.κ P.m P.c x X) := (lpVec_normQPt G t P.κ P.m P.c x X).symm
  have hp := newtonPot_gram (q := normQ t (lpVec G P.c) (fun i => exp (lpVec G X i))
    (barDphi (lpVec G P.κ) (lpVec G P.m) (lpVec G x))) hA hw hS
  have hnum := newtonProgPub_numeric G P.s P.terminal H.distinct H.L_ge hLM H.κ_pos
    (le_refl _) H.c₀_le H.U_ge H.width_le hx.feasible H.reference_feasible H.M_le
    H.rank_ge H.ε_pos H.ε_le hw ht H.cost_le hwin (hx.centrality.trans hD)
    H.reference_slack (by rw [H.C_eq]; exact H.C_pos.le) H.η_pos hDcopy hqcopy hp
    (J := P.J) P.rounds H.Csym_nonneg H.sym_le H.vertices_le H.samples_pos
  have hcard : ((Sparsify.resid G (Sparsify.P0
      (E.wf (pairOf (normDPt P.κ P.m x X).z)))).card : ℝ≥0∞) ≤
      (Fintype.card (Sym2 (Fin E.n)) : ℝ≥0∞) := by exact_mod_cast Finset.card_le_univ _
  have hnum' := hnum.trans (add_le_add le_rfl (mul_le_mul' hcard le_rfl))
  rw [newtonDir_eq_normD] at hnum'
  rw [frozenStep, RTree.eval_cast, RTree.eval_map, mass_map]
  refine (mass_mono _ (fun d hbad hgood => ?_)).trans hnum'
  obtain ⟨hAd, hed⟩ := hgood
  let h := newtonDir (lpA G P.s P.terminal) (fun i => exp (lpVec G X i))
    (barS (lpVec G P.κ) (lpVec G P.m) (lpVec G x))
    (normQ t (lpVec G P.c) (fun i => exp (lpVec G X i))
      (barDphi (lpVec G P.κ) (lpVec G P.m) (lpVec G x)))
  let e := lpVec G d - h
  have hAe : (lpA G P.s P.terminal)ᵀ *ᵥ e = 0 := by
    rw [show e = lpVec G d - h from rfl, mulVec_sub, hAd, (newtonDir_spec hA hw hS).1, sub_zero]
  have he : mixed P.C (fun i => exp (lpVec G X i))
      (fun i => barS (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i * e i) ≤ E.η := by
    rw [← H.C_eq]
    exact hed
  obtain ⟨hy, hc, hm, _⟩ := center_step_inexact hA (lpA_row_ne_zero G H.distinct)
    H.L_ge hLM H.κ_pos hc₀ H.c₀_le hx.feasible hw
    (fun i => (hwin i).trans (by norm_num)) hx.centrality hD hAe he hη
  have heq : lpVec G x + (h + e) = lpVec G (addPt x d) := by rw [lpVec_addPt]; dsimp [e]; abel
  change lpVec G x + (h + e) ∈ _ at hy
  change cent P.C _ (barS _ _ (lpVec G x + (h + e)))
    (barDphi _ _ (lpVec G x + (h + e))) _ t _ ≤ _ at hc
  change ∀ i, |Real.log (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
    (lpA G P.s P.terminal) (lpVec G x + (h + e)) i) -
    Real.log (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
      (lpA G P.s P.terminal) (lpVec G x) i)| ≤ 2 * D at hm
  rw [heq] at hy hc hm
  apply hbad
  refine ⟨hy, hc.trans ?_, fun i => ?_⟩
  · have hD0 : 0 ≤ D := (cent_nonneg H.C_pos.le t _).trans hx.centrality
    nlinarith [mul_le_mul_of_nonneg_left hD hD0]
  · have ht := abs_sub_le (lpVec G X i)
      (Real.log (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
        (lpA G P.s P.terminal) (lpVec G x) i))
      (Real.log (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
        (lpA G P.s P.terminal) (lpVec G (addPt x d)) i))
    rw [abs_sub_comm (Real.log (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
      (lpA G P.s P.terminal) (lpVec G x) i))] at ht
    exact ht.trans (add_le_add (hx.window i) (hm i))

/-- The full frozen loop halves a public centrality cap at each step. The moving
log-weight window is proved by summing the geometric movement bounds. -/
theorem frozenRun_failure (H : Regime G P bc) {t D W : ℝ} {X x : LPPoint (Fin E.n)}
    (ht : |t| ≤ 16 * E.n / E.ε) (hD : D ≤ 1 / 1000) (hW : W + 4 * D ≤ 1 / 20)
    (N : ℕ) (hη : E.η ≤ (1 / 2 : ℝ) ^ N * D / 64)
    (hx : FrozenInvariant G P bc t X D W x) :
    mass ((frozenRun P t X N x).eval G.out)
      (fun y => ¬FrozenInvariant G P bc t X ((1 / 2 : ℝ) ^ N * D) (W + 4 * D) y) ≤
      N * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) := by
  have hD0 : 0 ≤ D := (cent_nonneg H.C_pos.le t _).trans hx.centrality
  induction N generalizing D W x with
  | zero =>
      have hx' : FrozenInvariant G P bc t X D (W + 4 * D) x :=
        ⟨hx.feasible, hx.centrality, fun i => (hx.window i).trans (by linarith)⟩
      simp [frozenRun, hx']
  | succ N ih =>
      have hηstep : E.η ≤ D / 64 := hη.trans (div_le_div_of_nonneg_right
        (mul_le_of_le_one_left hD0 (pow_le_one₀ (by norm_num) (by norm_num))) (by norm_num))
      have hηtail : E.η ≤ (1 / 2 : ℝ) ^ N * (D / 2) / 64 := by
        calc E.η ≤ (1 / 2 : ℝ) ^ (N + 1) * D / 64 := hη
          _ = (1 / 2 : ℝ) ^ N * (D / 2) / 64 := by rw [pow_succ]; ring
      rw [frozenRun, RTree.eval_cast, RTree.eval_bind]
      refine (mass_bind_le_add _ _ _ _
        (ε := (N : ℝ≥0∞) * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds))
        (frozenStep_failure H ht hD (by linarith) hηstep hx) ?_).trans (le_of_eq ?_)
      · intro y hy
        have hi := ih (D := D / 2) (W := W + 2 * D) (x := y) (by linarith) (by linarith)
          hηtail (not_not.mp hy) (by positivity)
        have hcap : (1 / 2 : ℝ) ^ N * (D / 2) = (1 / 2 : ℝ) ^ (N + 1) * D := by
          rw [pow_succ]
          ring
        have hwindow : (W + 2 * D) + 4 * (D / 2) = W + 4 * D := by ring
        simpa only [hcap, hwindow] using hi
      · push_cast
        ring

theorem frozenRun_cost (G : DiGraph (Fin E.n)) (P : Params E) (t : ℝ)
    (X x : LPPoint (Fin E.n)) (N : ℕ) {out : LPPoint (Fin E.n) × ℕ}
    (ho : out ∈ (RTree.run G.out (frozenRun P t X N x)).support) :
    out.2 ≤ N * P.newtonBudget := RTree.cost_le _ _ ho

theorem Regime.final_constants (H : Regime G P bc) :
    P.Δ ≤ 1 / 1000 ∧ P.K + 4 * P.Δ ≤ 1 / 20 := by
  have ha0 : 0 ≤ 1 / (2 * P.L) := by have := H.L_ge; positivity
  have ha : 1 / (2 * P.L) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [H.L_ge])
  have hd : P.Δ ≤ 1 / 2 ^ 20 := by
    nlinarith [H.Δ_le, mul_le_mul ha ha ha0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hk : P.K ≤ 1 / 2 ^ 22 := by nlinarith [H.K_le]
  constructor <;> linarith

/-- The batch invariant starts final centering; no final-run invariant is a premise. -/
theorem frozenRun_failure_from_invariant (H : Regime G P bc) {t : ℝ} {st : State E.n}
    (ht : |t| ≤ 16 * E.n / E.ε) (N : ℕ)
    (hη : E.η ≤ (1 / 2 : ℝ) ^ N * P.Δ / 64) (hs : Invariant G P bc t st) :
    mass ((frozenRun P t st.2 N st.1).eval G.out)
      (fun y => ¬FrozenInvariant G P bc t st.2 ((1 / 2 : ℝ) ^ N * P.Δ)
        (P.K + 4 * P.Δ) y) ≤
      N * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) :=
  frozenRun_failure H ht H.final_constants.1 H.final_constants.2 N hη
    ⟨hs.feasible, hs.centrality, logWindow_of_potential H (st := st) hs.potential⟩

/-- A numerical finite-run objective endpoint against every closed feasible comparator.
The final centrality bound is produced by `frozenRun`, not postulated. -/
theorem frozenRun_endpoint (H : Regime G P bc) {t : ℝ} {st : State E.n}
    (ht0 : 0 < t) (ht : |t| ≤ 16 * E.n / E.ε) (N : ℕ)
    (hη : E.η ≤ (1 / 2 : ℝ) ^ N * P.Δ / 64) (hs : Invariant G P bc t st)
    {v : Fin (lpM G) → ℝ} (hv : (lpA G P.s P.terminal)ᵀ *ᵥ v = bc)
    (hbox : ∀ i, |theta (lpVec G P.κ) (lpVec G P.m) v i| ≤ π / 2) :
    mass ((frozenRun P t st.2 N st.1).eval G.out)
      (fun y => ¬(lpVec G y ∈ Feasible (lpA G P.s P.terminal) bc (lpVec G P.κ) (lpVec G P.m) ∧
        lpVec G P.c ⬝ᵥ lpVec G y - lpVec G P.c ⬝ᵥ v ≤ 4 * E.n / t +
          (∑ i, |lpVec G P.c i|) * (4 * E.U * ((1 / 2 : ℝ) ^ N * P.Δ)))) ≤
      N * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) := by
  refine (mass_mono _ (fun y hbad hgood => ?_)).trans
    (frozenRun_failure_from_invariant H ht N hη hs)
  have hcap : (1 / 2 : ℝ) ^ N * P.Δ ≤ P.Δ :=
    mul_le_of_le_one_left H.Δ_pos.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hLM : Real.logb 2 (2 * lpM G) ≤ P.L - 1 :=
    (Real.logb_le_logb_of_le (by norm_num) (by have := H.rows_pos; positivity)
      (by linarith [H.M_le])).trans H.logM_le
  have hc₀ : 0 ≤ P.c₀ := by
    have hMb := H.rows_pos.trans_le H.M_le
    unfold Params.c₀
    positivity
  have hgap := objective_gap_from_centrality
    (det_ne_zero_of_idRows (lpA_idRows G P.s P.terminal)) (lpA_row_ne_zero G H.distinct)
    H.L_ge hLM H.κ_pos hc₀ H.c₀_le (by linarith [H.U_ge]) H.width_le hgood.feasible
    (fun i => exp_pos (lpVec G st.2 i)) ht0
    (fun i => by rw [Real.log_exp]; exact (hgood.window i).trans H.final_constants.2)
    (hgood.centrality.trans (hcap.trans H.final_constants.1)) hv hbox
  apply hbad
  refine ⟨hgood.feasible, hgap.trans (add_le_add ?_ ?_)⟩
  · exact div_le_div_of_nonneg_right
      (weight_bounds_of_potential H (st := st) hs.potential).2.2 ht0.le
  · exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hgood.centrality (by linarith [H.U_ge]))
      (sum_nonneg fun i _ => abs_nonneg (lpVec G P.c i))

def Params.initialBudget (P : Params E) : ℕ :=
  batchJL E P.Δ * ((P.rounds * Sparsify.levelBudget (n := E.n) P.Kd P.J P.samples + 3 * E.n) + 0)

/-- Compute initial weights, define the artificial cost, and run `N` public batches. -/
def initializedRun (P : Params E) (x : LPPoint (Fin E.n)) (τ : ℕ → ℝ) (N : ℕ) :
    RTree (Finset (Fin E.n)) ℕ (Option (State E.n × LPPoint (Fin E.n)))
      (P.initialBudget + N * P.batchBudget) :=
  ((initialWeights P x).cast (r := P.initialBudget) rfl).bind fun out => match out with
    | none => RTree.pure (PMF.pure none)
    | some X => ((run {P with c := artificialCost P.κ P.m x X} τ N 0 (x, X)).map
        (fun out => out.map (fun st => (st, artificialCost P.κ P.m x X)))).cast (by rfl)

/-- A complete first-phase execution: initialization plus adaptive composition.
The only point hypotheses concern feasibility and initial slack, not centrality. -/
theorem initializedRun_failure (H : Regime G P bc) (x : LPPoint (Fin E.n))
    (hx : lpVec G x ∈ Feasible (lpA G P.s P.terminal) bc (lpVec G P.κ) (lpVec G P.m))
    (hs : ∀ i, E.sst ≤ slk (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i)
    (hsU : ∀ i, 1 / E.U ≤ slk (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i)
    {τ : ℕ → ℝ} (hτ : Schedule P τ) (hτ0 : τ 0 = 1) (N : ℕ) :
    mass ((initializedRun P x τ N).eval G.out)
      (fun out => ¬∃ st cp, out = some (st, cp) ∧ ‖lpVec G cp‖ ≤ 4 * E.U ∧
        Invariant G {P with c := cp} bc (τ N) st) ≤
      batchJL E P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) +
        N * H.batchFailure := by
  erw [initializedRun, RTree.eval_bind, RTree.eval_cast]
  refine mass_bind_le_add _ _ _ _ (initialWeights_failure H x hx hs) ?_
  intro out hout
  obtain ⟨X, rfl, hX, _⟩ := not_not.mp hout
  let cp := artificialCost P.κ P.m x X
  have hc : ‖lpVec G cp‖ ≤ 4 * E.U := artificialCost_bound H (x := x) (X := X) hx hsU hX.potential
  let H' := H.withCost cp hc
  have hinit : Invariant G {P with c := cp} bc (τ 0) (x, X) := by rw [hτ0]; exact hX
  have hτ' : Schedule {P with c := cp} τ :=
    ⟨hτ.positive, hτ.bounded, hτ.move_T, hτ.move_Δ⟩
  have hrun := run_failure H' hτ' N 0 hinit
  simp only [Nat.zero_add] at hrun
  erw [RTree.eval_cast, RTree.eval_map, mass_map]
  refine (mass_mono _ (fun o hbad hgood => ?_)).trans hrun
  obtain ⟨st, rfl, hst⟩ := hgood
  exact hbad ⟨st, cp, rfl, hc, hst⟩

/-- An unconditional query cap for the initialized execution. -/
theorem initializedRun_cost (G : DiGraph (Fin E.n)) (P : Params E) (x : LPPoint (Fin E.n))
    (τ : ℕ → ℝ) (N : ℕ) {out : Option (State E.n × LPPoint (Fin E.n)) × ℕ}
    (ho : out ∈ (RTree.run G.out (initializedRun P x τ N)).support) :
    out.2 ≤ P.initialBudget + N * P.batchBudget := RTree.cost_le _ _ ho

/-- Initialization, the artificial path, one margin-producing switch batch, the true-cost
path, and final numerical centering, all as one public query program. -/
def pathSolver (P : Params E) (x : LPPoint (Fin E.n)) (τ : ℕ → ℝ) (Ndown : ℕ)
    (σ : ℕ → ℝ) (Nup Nfinal : ℕ) :
    RTree (Finset (Fin E.n)) ℕ (Option (LPPoint (Fin E.n)))
      ((P.initialBudget + Ndown * P.batchBudget) +
        (P.batchBudget + (Nup * P.batchBudget + Nfinal * P.newtonBudget))) :=
  (initializedRun P x τ Ndown).bind fun out => match out with
    | none => RTree.pure (PMF.pure none)
    | some (st, cp) => ((batch {P with c := cp} (τ Ndown) st).cast
        (show {P with c := cp}.batchBudget = P.batchBudget from rfl)).bind fun out => match out with
      | none => RTree.pure (PMF.pure none)
      | some st' => (run P σ Nup 0 st').bind fun out => match out with
        | none => RTree.pure (PMF.pure none)
        | some stf => (frozenRun P (σ Nup) stf.2 Nfinal stf.1).map some

def Endpoint (G : DiGraph (Fin E.n)) (P : Params E) (bc : Fin E.n → ℝ)
    (t : ℝ) (N : ℕ) (v : Fin (lpM G) → ℝ) (y : LPPoint (Fin E.n)) : Prop :=
  lpVec G y ∈ Feasible (lpA G P.s P.terminal) bc (lpVec G P.κ) (lpVec G P.m) ∧
    lpVec G P.c ⬝ᵥ lpVec G y - lpVec G P.c ⬝ᵥ v ≤ 4 * E.n / t +
      (∑ i, |lpVec G P.c i|) * (4 * E.U * ((1 / 2 : ℝ) ^ N * P.Δ))

/-- End-to-end execution of the licensed implicit LP routine. Only the initial point's
feasibility and slack are inputs: initialization, both paths, cost switching, and final
centering establish all later invariants. Concrete terminal-LP instantiation is separate. -/
theorem pathSolver_failure (H : Regime G P bc) (x : LPPoint (Fin E.n))
    (hx : lpVec G x ∈ Feasible (lpA G P.s P.terminal) bc (lpVec G P.κ) (lpVec G P.m))
    (hs : ∀ i, E.sst ≤ slk (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i)
    (hsU : ∀ i, 1 / E.U ≤ slk (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i)
    {τ σ : ℕ → ℝ} (hτ : Schedule P τ) (hτ0 : τ 0 = 1) (hσ : Schedule P σ)
    (Ndown Nup Nfinal : ℕ) (hjoin : σ 0 = τ Ndown)
    (hswitch : |τ Ndown| * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤
      1 / (2 * P.L) * P.Δ / 2)
    (hη : E.η ≤ (1 / 2 : ℝ) ^ Nfinal * P.Δ / 64)
    {v : Fin (lpM G) → ℝ} (hv : (lpA G P.s P.terminal)ᵀ *ᵥ v = bc)
    (hbox : ∀ i, |theta (lpVec G P.κ) (lpVec G P.m) v i| ≤ π / 2) :
    mass ((pathSolver P x τ Ndown σ Nup Nfinal).eval G.out)
      (fun out => ¬∃ y, out = some y ∧ Endpoint G P bc (σ Nup) Nfinal v y) ≤
      batchJL E P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) +
        (Ndown + 1 + Nup : ℕ) * H.batchFailure +
        Nfinal * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) := by
  erw [pathSolver, RTree.eval_bind]
  refine (mass_bind_le_add _ _ _ _
    (ε := H.batchFailure + ((Nup : ℝ≥0∞) * H.batchFailure +
      Nfinal * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds)))
    (initializedRun_failure H x hx hs hsU hτ hτ0 Ndown) ?_).trans (le_of_eq ?_)
  · intro out hout
    obtain ⟨st, cp, rfl, hcp, hst⟩ := not_not.mp hout
    let H' := H.withCost cp hcp
    erw [RTree.eval_bind, RTree.eval_cast]
    refine mass_bind_le_add _ _ _ _
      (ε := (Nup : ℝ≥0∞) * H.batchFailure +
        Nfinal * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds))
      (batch_switch_failure H' P.c H.cost_le (hτ.bounded Ndown) hswitch hst) ?_
    intro out hout
    obtain ⟨st', rfl, hst'⟩ := not_not.mp hout
    have hinit : Invariant G P bc (σ 0) st' := by rw [hjoin]; exact hst'
    have hrun := run_failure H hσ Nup 0 hinit
    simp only [Nat.zero_add] at hrun
    rw [RTree.eval_bind]
    refine mass_bind_le_add _ _ _ _
      (ε := (Nfinal : ℝ≥0∞) * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds))
      hrun ?_
    intro out hout
    obtain ⟨stf, rfl, hstf⟩ := not_not.mp hout
    rw [RTree.eval_map, mass_map]
    refine (mass_mono _ (fun y hbad hgood => hbad ⟨y, rfl, hgood⟩)).trans
      (frozenRun_endpoint H (hσ.positive Nup) (hσ.bounded Nup) Nfinal hη hstf hv hbox)
  · push_cast
    ring

theorem pathSolver_cost (G : DiGraph (Fin E.n)) (P : Params E) (x : LPPoint (Fin E.n))
    (τ σ : ℕ → ℝ) (Ndown Nup Nfinal : ℕ) {out : Option (LPPoint (Fin E.n)) × ℕ}
    (ho : out ∈ (RTree.run G.out (pathSolver P x τ Ndown σ Nup Nfinal)).support) :
    out.2 ≤ (P.initialBudget + Ndown * P.batchBudget) +
      (P.batchBudget + (Nup * P.batchBudget + Nfinal * P.newtonBudget)) := RTree.cost_le _ _ ho

def Params.solverBudget (P : Params E) (Ndown Nup Nfinal : ℕ) : ℕ :=
  (P.initialBudget + Ndown * P.batchBudget) +
    (P.batchBudget + (Nup * P.batchBudget + Nfinal * P.newtonBudget))

def Regime.solverFailure (H : Regime G P bc) (Ndown Nup Nfinal : ℕ) : ℝ≥0∞ :=
  batchJL E P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) +
    (Ndown + 1 + Nup : ℕ) * H.batchFailure +
    Nfinal * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds)

def solverSpectralCap (P : Params E) (Ndown Nup Nfinal : ℕ) : ℕ :=
  batchJL E P.Δ + (Ndown + 1 + Nup) * (1 + batchJL E P.Δ) + Nfinal

theorem solverFailure_of_per_call (H : Regime G P bc) (Ndown Nup Nfinal : ℕ) {δ : ℝ≥0∞}
    (hsolve : d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) ≤ δ)
    (hlev : d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) ≤ δ) :
    H.solverFailure Ndown Nup Nfinal ≤ solverSpectralCap P Ndown Nup Nfinal * δ := by
  unfold Regime.solverFailure Regime.batchFailure
  calc _ ≤ batchJL E P.Δ * δ + (Ndown + 1 + Nup : ℕ) *
        (δ + batchJL E P.Δ * δ) + Nfinal * δ :=
      add_le_add (add_le_add (mul_le_mul' le_rfl hlev)
        (mul_le_mul' le_rfl (add_le_add hsolve (mul_le_mul' le_rfl hlev))))
        (mul_le_mul' le_rfl hsolve)
    _ = solverSpectralCap P Ndown Nup Nfinal * δ := by
      unfold solverSpectralCap
      push_cast
      ring

/-- A spectral call licensed at a smaller positive error also bounds either numerical
interface's failure expression. This is an inequality of explicit public scalars. -/
theorem d4Fail_antitone_accuracy (n K J samples R : ℕ) {Cs δ δ' : ℝ}
    (hCs : 0 ≤ Cs) (hδ : 0 ≤ δ) (hle : δ ≤ δ') :
    d4Fail n Cs K J samples R δ' ≤ d4Fail n Cs K J samples R δ := by
  unfold d4Fail
  refine add_le_add (mul_le_mul' le_rfl (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))) le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg (pow_le_pow_left₀ hδ hle 2)) (by positivity)

/-- The existing explicit spectral parameters also certify the public failure bound
used in the adaptive run, including its public residual-pair cap. -/
theorem d4Fail_public_parameters {n : ℕ} {Cs ε ζ : ℝ} (hn : 2 ≤ n)
    (hCs : 1 ≤ Cs) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hζ : 0 < ζ) (hζ2 : ζ ≤ 1 / 2) :
    d4Fail n Cs (Sparsify.pK n) (Sparsify.pJ n Cs ε ζ) (Sparsify.pt n Cs ε ζ)
      (Sparsify.pR n ζ) (Sparsify.pδ n ε ζ) ≤ ENNReal.ofReal ζ := by
  obtain ⟨_, _, _, _, _, hJ, hγ, hres⟩ := Sparsify.params_ok hn hCs hε hε2 hζ hζ2
  have hround : (Sparsify.pR n ζ : ℝ≥0∞) * ENNReal.ofReal (2 * n *
      exp (-(Sparsify.pδ n ε ζ ^ 2) /
        (8 * (Cs * (2 * Sparsify.pK n + 1 : ℕ) / Sparsify.pt n Cs ε ζ)))) ≤
      ENNReal.ofReal (ζ / 4) := by
    calc _ = ENNReal.ofReal ((Sparsify.pR n ζ : ℝ) * (2 * n *
          exp (-(Sparsify.pδ n ε ζ ^ 2) /
            (8 * (Cs * (2 * Sparsify.pK n + 1 : ℕ) / Sparsify.pt n Cs ε ζ))))) := by
            rw [ENNReal.ofReal_mul (by positivity)]
            simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal hγ
  have hcard : Fintype.card (Sym2 (Fin n)) ≤ n ^ 2 := by
    rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel]
    apply Nat.div_le_of_le_mul
    nlinarith
  have hlast : (Fintype.card (Sym2 (Fin n)) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ Sparsify.pR n ζ ≤
      ENNReal.ofReal (ζ / 4) := by
    calc _ ≤ (n : ℝ≥0∞) ^ 2 * (4⁻¹ : ℝ≥0∞) ^ Sparsify.pR n ζ :=
          mul_le_mul' (by exact_mod_cast hcard) le_rfl
      _ = ENNReal.ofReal ((n : ℝ) ^ 2 * (4⁻¹ : ℝ) ^ Sparsify.pR n ζ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
        simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal hres
  unfold d4Fail
  rw [mul_add]
  refine (add_le_add (add_le_add hJ hround) hlast).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem spectral_accuracy_compatible {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    {R : ℕ} (hR : 1 ≤ R) :
    (Δ / 4096) / (3 * R) ≤ levDelta Δ R ∧
      (Δ / 4096) / (3 * R) ≤ solveDelta R := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  constructor
  · unfold levDelta levEps
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hΔ.le (sub_nonneg.mpr hR')]
  · unfold solveDelta
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hΔ1) (show (0 : ℝ) ≤ R by positivity)]

/-- One shared, explicitly chosen spectral parameter set covers both numerical
interfaces. Neither failure inequality is an assumed probabilistic guarantee. -/
theorem d4Fail_numerical_parameters {n : ℕ} {Cs Δ ζ : ℝ} (hn : 2 ≤ n)
    (hCs : 1 ≤ Cs) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hζ : 0 < ζ) (hζ2 : ζ ≤ 1 / 2) :
    d4Fail n Cs (Sparsify.pK n) (Sparsify.pJ n Cs (Δ / 4096) ζ)
        (Sparsify.pt n Cs (Δ / 4096) ζ) (Sparsify.pR n ζ)
        (solveDelta (Sparsify.pR n ζ)) ≤ ENNReal.ofReal ζ ∧
      d4Fail n Cs (Sparsify.pK n) (Sparsify.pJ n Cs (Δ / 4096) ζ)
        (Sparsify.pt n Cs (Δ / 4096) ζ) (Sparsify.pR n ζ)
        (levDelta Δ (Sparsify.pR n ζ)) ≤ ENNReal.ofReal ζ := by
  have hb := d4Fail_public_parameters hn hCs (ε := Δ / 4096) (by positivity)
    (by linarith) hζ hζ2
  have hcompat := spectral_accuracy_compatible hΔ hΔ1 (Sparsify.pR_pos hn hζ hζ2)
  have hδ : 0 ≤ Sparsify.pδ n (Δ / 4096) ζ := by unfold Sparsify.pδ; positivity
  constructor
  · exact (d4Fail_antitone_accuracy n _ _ _ _ (Cs := Cs) (by linarith) hδ hcompat.2).trans hb
  · exact (d4Fail_antitone_accuracy n _ _ _ _ (Cs := Cs) (by linarith) hδ hcompat.1).trans hb

/-- The full LP query program includes the degree queries that construct its start. -/
def terminalLP (P : Params E) (τ σ : ℕ → ℝ) (Ndown Nup Nfinal : ℕ) :
    RTree (Finset (Fin E.n)) ℕ (Option (LPPoint (Fin E.n)))
      (2 * E.n + P.solverBudget Ndown Nup Nfinal) :=
  (RTree.ofDeterministic (strictStartProg E.n)).bind fun x =>
    ((pathSolver P x τ Ndown σ Nup Nfinal).map (fun out => out.map clipPairPoint)).cast (by rfl)

/-- The constructed routine solves the terminal LP under static public numerical bounds.
Its initial point, invariant sequence, comparator, and extraction feasibility are proved. -/
theorem terminalLP_failure (H : Regime G P (DirectedMincut.bvec G)) (hG : G.Simple)
    (hκ : P.κ = terminalKappa E.n) (hm : P.m = terminalMid E.n)
    (hc : P.c = terminalCost E.n) (hsst : E.sst ≤ 1)
    {τ σ : ℕ → ℝ} (hτ : Schedule P τ) (hτ0 : τ 0 = 1) (hσ : Schedule P σ)
    (Ndown Nup Nfinal : ℕ) (hjoin : σ 0 = τ Ndown)
    (hswitch : |τ Ndown| * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤
      1 / (2 * P.L) * P.Δ / 2)
    (hη : E.η ≤ (1 / 2 : ℝ) ^ Nfinal * P.Δ / 64) {ε : ℝ}
    (haccuracy : 4 * E.n / σ Nup + (2 * E.n + 1 / 2) *
      (4 * E.U * ((1 / 2 : ℝ) ^ Nfinal * P.Δ)) ≤ ε) :
    mass ((terminalLP P τ σ Ndown Nup Nfinal).eval G.out)
      (fun out => ¬∃ y, out = some y ∧ DirectedMincut.LPGood P.s P.terminal ε G y) ≤
      H.solverFailure Ndown Nup Nfinal := by
  let x := strictStartPoint (DirectedMincut.bvec G)
  have hx : lpVec G x ∈ Feasible (lpA G P.s P.terminal) (DirectedMincut.bvec G)
      (lpVec G P.κ) (lpVec G P.m) := by
    simpa only [hκ, hm] using strictStart_barrier_feasible G P.s P.terminal hG H.rank_ge
  have hslack : ∀ i, 1 ≤ slk (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i := by
    simpa only [hκ, hm] using strictStart_slack G hG H.rank_ge
  have hU : 1 / E.U ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) H.U_ge
  obtain ⟨v, hv, hval⟩ := DirectedMincut.exists_feasible_obj_eq hG H.distinct
  have hclosed := terminal_closed G P.s P.terminal H.rank_ge hv
  have hbox : ∀ i, |theta (lpVec G P.κ) (lpVec G P.m) (lpVec G v) i| ≤ π / 2 := by
    simpa only [hκ, hm] using hclosed.2
  have hpath := pathSolver_failure H x hx (fun i => hsst.trans (hslack i))
    (fun i => hU.trans (hslack i)) hτ hτ0 hσ Ndown Nup Nfinal hjoin hswitch hη hclosed.1 hbox
  erw [terminalLP, RTree.eval_bind, RTree.eval_ofDeterministic, PMF.pure_bind,
    strictStartProg_eval, RTree.eval_cast, RTree.eval_map, mass_map]
  refine (mass_mono _ (fun out hbad hgood => ?_)).trans hpath
  obtain ⟨y, rfl, hy⟩ := hgood
  apply hbad
  refine ⟨clipPairPoint y, rfl, terminal_clip_feasible G P.s P.terminal H.rank_ge ?_, ?_⟩
  · simpa only [hκ, hm] using hy.1
  · have hgap := hy.2
    rw [hc, terminal_obj, terminal_obj, terminal_cost_sum] at hgap
    rw [clipPairPoint_obj]
    linarith

/-- The actual terminal-cut routine. Extraction also handles the zero-point abort fallback,
so every execution returns a terminal shore with its queried value. -/
def terminalSolver (P : Params E) (τ σ : ℕ → ℝ) (Ndown Nup Nfinal k : ℕ) (θ : ℝ) :
    RTree (Finset (Fin E.n)) ℕ (Finset (Fin E.n) × ℕ)
      ((2 * E.n + P.solverBudget Ndown Nup Nfinal) + (2 * E.n * (3 + 3 * k) + 1)) :=
  (terminalLP P τ σ Ndown Nup Nfinal).bind fun out =>
    (RTree.ofDeterministic (DirectedMincut.extract P.s P.terminal k θ (out.getD zeroPt))).cast
      (by simp)

theorem terminalSolver_valid (G : DiGraph (Fin E.n)) (P : Params E)
    (hst : P.s ≠ P.terminal) (τ σ : ℕ → ℝ) (Ndown Nup Nfinal k : ℕ)
    (hk : E.n ≤ 2 ^ k) (θ : ℝ) {out : Finset (Fin E.n) × ℕ}
    (ho : out ∈ ((terminalSolver P τ σ Ndown Nup Nfinal k θ).eval G.out).support) :
    P.s ∈ out.1 ∧ P.terminal ∉ out.1 ∧ out.2 = G.out out.1 := by
  simp only [terminalSolver, RTree.eval_bind, PMF.mem_support_bind_iff] at ho
  obtain ⟨p, _, ho⟩ := ho
  simp only [RTree.eval_cast, RTree.eval_ofDeterministic, PMF.support_pure, Set.mem_singleton_iff] at ho
  subst ho
  exact DirectedMincut.extract_valid G hst (by simpa only [Fintype.card_fin] using hk) θ _

theorem terminalSolver_failure (H : Regime G P (DirectedMincut.bvec G)) (hG : G.Simple)
    (hκ : P.κ = terminalKappa E.n) (hm : P.m = terminalMid E.n)
    (hc : P.c = terminalCost E.n) (hsst : E.sst ≤ 1)
    {τ σ : ℕ → ℝ} (hτ : Schedule P τ) (hτ0 : τ 0 = 1) (hσ : Schedule P σ)
    (Ndown Nup Nfinal : ℕ) (hjoin : σ 0 = τ Ndown)
    (hswitch : |τ Ndown| * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤
      1 / (2 * P.L) * P.Δ / 2)
    (hη : E.η ≤ (1 / 2 : ℝ) ^ Nfinal * P.Δ / 64) {ε θ : ℝ}
    (haccuracy : 4 * E.n / σ Nup + (2 * E.n + 1 / 2) *
      (4 * E.U * ((1 / 2 : ℝ) ^ Nfinal * P.Δ)) ≤ ε)
    (k : ℕ) (hk : E.n ≤ 2 ^ k) (hθ : 0 < θ) (hsmall : 8 * (E.n : ℝ) ^ 2 * θ ≤ 1)
    (hε : ε ≤ θ / 16) :
    mass ((terminalSolver P τ σ Ndown Nup Nfinal k θ).eval G.out)
      (fun out => ¬DirectedMincut.STGood P.s P.terminal G out) ≤
      H.solverFailure Ndown Nup Nfinal := by
  rw [terminalSolver, RTree.eval_bind]
  refine (mass_bind_le_add _ _ _ _ (ε := 0)
    (terminalLP_failure H hG hκ hm hc hsst hτ hτ0 hσ Ndown Nup Nfinal
      hjoin hswitch hη haccuracy) ?_).trans (le_of_eq (add_zero _))
  intro out hout
  obtain ⟨y, rfl, hy⟩ := not_not.mp hout
  have he := DirectedMincut.extract_correct hG H.distinct
    (by simpa only [Fintype.card_fin] using hk) hθ
    (by simpa only [Fintype.card_fin] using hsmall) hε hy
  simp only [RTree.eval_cast, RTree.eval_ofDeterministic, mass_pure]
  simp [he]

theorem terminalSolver_cost (G : DiGraph (Fin E.n)) (P : Params E)
    (τ σ : ℕ → ℝ) (Ndown Nup Nfinal k : ℕ) (θ : ℝ) {out : (Finset (Fin E.n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run G.out (terminalSolver P τ σ Ndown Nup Nfinal k θ)).support) :
    out.2 ≤ (2 * E.n + P.solverBudget Ndown Nup Nfinal) + (2 * E.n * (3 + 3 * k) + 1) :=
  RTree.cost_le _ _ ho

/-- The terminal solver with all three iteration counts and both paths fixed by public formulas. -/
def publicTerminalSolver (P : Params E) (k : ℕ) (θ : ℝ) :=
  terminalSolver P (initialPhase P) (truePhase P) P.downSteps P.upSteps P.finalSteps k θ

theorem Regime.sst_le_one (H : Regime G P bc) : E.sst ≤ 1 := by
  have hrows1 : 1 ≤ lpM G := Nat.succ_le_of_lt (by exact_mod_cast H.rows_pos)
  have hM1 : 1 ≤ E.Mbar := le_trans (by exact_mod_cast hrows1) H.M_le
  have hden : 1 ≤ 2 ^ 12 * (E.n : ℝ) * E.Mbar ^ 2 * E.U ^ 3 :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) H.rank_ge) (one_le_pow₀ hM1))
      (one_le_pow₀ H.U_ge)
  unfold NewtonPub.sst
  rw [div_le_one (by linarith)]
  exact H.ε_le.trans hden

/-- A finite query endpoint with constructed schedules and objective accuracy. Only
static numerical licensing and extraction-scale inequalities remain as inputs. -/
theorem publicTerminalSolver_failure (H : Regime G P (DirectedMincut.bvec G)) (hG : G.Simple)
    (hκ : P.κ = terminalKappa E.n) (hm : P.m = terminalMid E.n)
    (hc : P.c = terminalCost E.n)
    (hη : E.η ≤ (1 / 2 : ℝ) ^ P.finalSteps * P.Δ / 64)
    (k : ℕ) (hk : E.n ≤ 2 ^ k) {θ : ℝ} (hθ : 0 < θ)
    (hsmall : 8 * (E.n : ℝ) ^ 2 * θ ≤ 1) (hε : E.ε ≤ θ / 16) :
    mass ((publicTerminalSolver P k θ).eval G.out)
      (fun out => ¬DirectedMincut.STGood P.s P.terminal G out) ≤
      H.solverFailure P.downSteps P.upSteps P.finalSteps :=
  terminalSolver_failure H hG hκ hm hc H.sst_le_one (initialPhase_licensed H) (initialPhase_starts P)
    (truePhase_licensed H).1 P.downSteps P.upSteps P.finalSteps (truePhase_joins P)
    (initialPhase_switch H) hη (public_final_accuracy H) k hk hθ hsmall hε

theorem publicTerminalSolver_cost (G : DiGraph (Fin E.n)) (P : Params E)
    (k : ℕ) (θ : ℝ) {out : (Finset (Fin E.n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run G.out (publicTerminalSolver P k θ)).support) :
    out.2 ≤ (2 * E.n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
      (2 * E.n * (3 + 3 * k) + 1) := RTree.cost_le _ _ ho

/-- Changing terminals uses the proved degree start as a new reference point. Thus a
single set of public numerical parameters licenses every distinct terminal pair. -/
def Regime.withTerminals (H : Regime G P (DirectedMincut.bvec G)) (hG : G.Simple)
    (hκ : P.κ = terminalKappa E.n) (hm : P.m = terminalMid E.n)
    (s t : Fin E.n) (hst : s ≠ t) :
    Regime G {P with s := s, terminal := t} (DirectedMincut.bvec G) where
  distinct := hst
  L_ge := H.L_ge
  logM_le := H.logM_le
  κ_pos := H.κ_pos
  U_ge := H.U_ge
  width_le := H.width_le
  reference := lpVec G (strictStartPoint (DirectedMincut.bvec G))
  reference_feasible := by
    simpa only [hκ, hm] using strictStart_barrier_feasible G s t hG H.rank_ge
  reference_slack := by
    have hu : 1 / E.U ≤ (1 : ℝ) := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) H.U_ge
    intro i
    have hs := hu.trans (strictStart_slack G hG H.rank_ge i)
    simpa only [hκ, hm] using hs
  M_le := H.M_le
  ε_pos := H.ε_pos
  ε_le := H.ε_le
  cost_le := H.cost_le
  C_eq := H.C_eq
  η_pos := H.η_pos
  η_le := H.η_le
  Δ_pos := H.Δ_pos
  Δ_le := H.Δ_le
  K_nonneg := H.K_nonneg
  K_le := H.K_le
  window_le := H.window_le
  Csym := H.Csym
  Csym_nonneg := H.Csym_nonneg
  sym_le := H.sym_le
  vertices_le := H.vertices_le
  samples_pos := H.samples_pos

def publicTerminalFamily (P : Params E) (k : ℕ) (θ : ℝ) (s t : Fin E.n) :
    RTree (Finset (Fin E.n)) ℕ (Finset (Fin E.n) × ℕ)
      ((2 * E.n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
        (2 * E.n * (3 + 3 * k) + 1)) :=
  publicTerminalSolver {P with s := s, terminal := t} k θ

theorem publicTerminalFamily_spec (H : Regime G P (DirectedMincut.bvec G)) (hG : G.Simple)
    (hκ : P.κ = terminalKappa E.n) (hm : P.m = terminalMid E.n)
    (hc : P.c = terminalCost E.n) (hη : E.η ≤ (1 / 2 : ℝ) ^ P.finalSteps * P.Δ / 64)
    (k : ℕ) (hk : E.n ≤ 2 ^ k) {θ ζ : ℝ} (hθ : 0 < θ)
    (hsmall : 8 * (E.n : ℝ) ^ 2 * θ ≤ 1) (hε : E.ε ≤ θ / 16)
    (hfail : H.solverFailure P.downSteps P.upSteps P.finalSteps ≤ ENNReal.ofReal ζ) :
    DirectedMincut.TermSpec G (publicTerminalFamily P k θ) ζ := by
  constructor
  · intro s t hst out ho
    exact terminalSolver_valid G {P with s := s, terminal := t} hst _ _ _ _ _ k hk θ ho
  · intro s t hst
    let H' := H.withTerminals hG hκ hm s t hst
    have hf := publicTerminalSolver_failure H' hG hκ hm hc hη k hk hθ hsmall hε
    refine (mass_mono _ (fun out hbad hgood => hbad hgood.2.2.1)).trans (hf.trans hfail)

/-- The existing global reduction instantiated with the actual constructed terminal family. -/
def publicGlobalSolver (P : Params E) (k h K : ℕ) (θ : ℝ) :=
  letI : Nonempty (Fin E.n) := ⟨P.s⟩
  DirectedMincut.global k h K P.s (publicTerminalFamily P k θ)

theorem publicGlobalSolver_success (H : Regime G P (DirectedMincut.bvec G)) (hG : G.Simple)
    (hκ : P.κ = terminalKappa E.n) (hm : P.m = terminalMid E.n)
    (hc : P.c = terminalCost E.n) (hη : E.η ≤ (1 / 2 : ℝ) ^ P.finalSteps * P.Δ / 64)
    (hn : 2 ≤ E.n) (k : ℕ) (hk : E.n ≤ 2 ^ k) {θ ζ : ℝ} (hθ : 0 < θ)
    (hsmall : 8 * (E.n : ℝ) ^ 2 * θ ≤ 1) (hε : E.ε ≤ θ / 16)
    (hfail : H.solverFailure P.downSteps P.upSteps P.finalSteps ≤ ENNReal.ofReal ζ)
    (hζ : 0 ≤ ζ) (h K : ℕ) (hh : h ≤ E.n) :
    1 - ((1 - (h : ℝ) / E.n) ^ K + ζ) ≤
      (publicGlobalSolver P k h K θ).successProb G.out (DirectedMincut.Opt G) := by
  let : Nonempty (Fin E.n) := ⟨P.s⟩
  have hspec := publicTerminalFamily_spec H hG hκ hm hc hη k hk hθ hsmall hε hfail
  have hs := DirectedMincut.global_solves (X := Unit) (fun _ => G) (fun _ => hG)
    (by simpa only [Fintype.card_fin] using hn) (by simpa only [Fintype.card_fin] using hk)
    h K (by simpa only [Fintype.card_fin] using hh) P.s (fun _ => hspec) hζ ()
  simpa only [publicGlobalSolver, Fintype.card_fin] using hs

theorem publicGlobalSolver_cost (G : DiGraph (Fin E.n)) (P : Params E)
    (k h K : ℕ) (θ : ℝ) {out : (Finset (Fin E.n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run G.out (publicGlobalSolver P k h K θ)).support) :
    out.2 ≤ 2 * E.n +
      (DirectedMincut.learnFuel (V := Fin E.n) h * (3 + 3 * k) +
        (DirectedMincut.learnFuel (V := Fin E.n) h * (3 + 3 * k) + 1)) +
      2 * K * ((2 * E.n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
        (2 * E.n * (3 + 3 * k) + 1)) := by
  simpa only [Fintype.card_fin] using RTree.cost_le _ _ ho

end
end CutQueryComplexity.ImplicitLP.PathFollowing

#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.artificialCost_bound
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.initializedRun_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.initializedRun_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.center_gap_closed
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.objective_gap_from_centrality
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.cent_cost_change
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.center_step_inexact
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.frozenStep_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.frozenRun_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.frozenRun_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.frozenRun_failure_from_invariant
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.frozenRun_endpoint
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.batchGood_changeCost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.batch_switch_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.pathSolver_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.pathSolver_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.strictStart_slack
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.strictStart_barrier_feasible
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.terminal_clip_feasible
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.terminal_width_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.terminal_rows_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.PublicLicense.regime
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedDelta_spec
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTolerance_spec
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.terminalLP_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.terminalSolver_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.terminalSolver_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.terminalSolver_valid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.solverFailure_of_per_call
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.d4Fail_antitone_accuracy
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.d4Fail_public_parameters
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.d4Fail_numerical_parameters
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicTerminalSolver_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicTerminalSolver_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicTerminalFamily_spec
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicGlobalSolver_success
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicGlobalSolver_cost
