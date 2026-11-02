import CutQueryComplexity.ImplicitLP.LewisDeriv

/-! # The inexact Lewis iteration (`lem:lewis`, `eq:lewisfloor`, D7)

* `lewisMap_eq_lev`: the audited draft's implementable update
  `log T(v)ᵢ = (p/2) log σᵢ(V^{1/2−1/p} B) + (1 − p/2) log vᵢ` is the Lewis map in log coordinates.
* `inexact_iter`: if every iterate satisfies `‖y_{j+1} − T(y_j)‖_∞ ≤ ζ`, then
  `‖y_j − y*‖_∞ ≤ (1 − p/2)^j ‖y₀ − y*‖_∞ + ζ/(p/2)`.
* `lewis_floor` (`eq:lewisfloor`): every Lewis weight is at least `min_k σ_k(B)`. If `j` minimizes
  `w`, then `BᵀW^aB ⪯ w_j^a BᵀB` for `a = 1 − 2/p < 0`, and the Lewis identity gives
  `w_j ≥ σ_j(B)`.
* `restart_error`: if `q ≤ wᵢ ≤ 1`, then restarting from `v = 1` gives `‖0 − y*‖_∞ ≤ log(1/q)`.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ} {B : Matrix (Fin M) (Fin r) ℝ} {p : ℝ}

/-- **The Lewis map through leverage scores.** -/
theorem lewisMap_eq_lev (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p)
    (y : Fin M → ℝ) (i : Fin M) :
    lewisMap p B y i = p / 2 * Real.log (lev (diagonal (fun j => exp ((1 / 2 - 1 / p) * y j)) * B) i)
      + (1 - p / 2) * y i := by
  rw [lev_diag]
  have e : ∀ k, exp ((1 / 2 - 1 / p) * y k) ^ 2 = exp ((1 - 2 / p) * y k) := fun k => by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  simp only [e]
  have hq := qform_pos hB hrow (fun j => exp_pos ((1 - 2 / p) * y j)) i
  rw [Real.log_mul (exp_pos _).ne' hq.ne', Real.log_exp, lewisMap]
  field_simp
  ring

/-- **The inexact iteration:** `E_j ≤ (1 − p/2)^j E₀ + ζ/(p/2)`. -/
theorem inexact_iter (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2)
    {ζ : ℝ} (hζ : 0 ≤ ζ) {y : ℕ → Fin M → ℝ} (hy : ∀ j, dist (y (j + 1)) (lewisMap p B (y j)) ≤ ζ)
    {ystar : Fin M → ℝ} (hfix : lewisMap p B ystar = ystar) (j : ℕ) :
    dist (y j) ystar ≤ (1 - p / 2) ^ j * dist (y 0) ystar + ζ / (p / 2) := by
  have hq0 : 0 ≤ 1 - p / 2 := by linarith
  have hp' : 0 < p / 2 := by positivity
  induction j with
  | zero => simp; positivity
  | succ j ih =>
      have hT := lewisMap_dist_le hB hrow hp0 hp2 (y j) ystar
      rw [hfix] at hT
      calc dist (y (j + 1)) ystar ≤ dist (y (j + 1)) (lewisMap p B (y j)) +
            dist (lewisMap p B (y j)) ystar := dist_triangle _ _ _
        _ ≤ ζ + (1 - p / 2) * dist (y j) ystar := add_le_add (hy j) hT
        _ ≤ ζ + (1 - p / 2) * ((1 - p / 2) ^ j * dist (y 0) ystar + ζ / (p / 2)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hq0)
        _ = (1 - p / 2) ^ (j + 1) * dist (y 0) ystar + ζ / (p / 2) := by
            field_simp; ring

/-- **The Lewis floor** (`eq:lewisfloor`): `wᵢ ≥ min_k σ_k(B)` for every `i`. -/
theorem lewis_floor (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p) (hp1 : p < 2)
    {q : ℝ} (hq : ∀ k, q ≤ lev B k) (i : Fin M) : q ≤ exp (lewisLog p B i) := by
  set y := lewisLog p B
  -- a minimizing coordinate
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image univ y ⟨i, mem_univ i⟩
  suffices h : lev B j ≤ exp (y j) by
    exact (hq j).trans (h.trans (exp_le_exp.mpr (hj i (mem_univ i))))
  set a : ℝ := 1 - 2 / p
  have ha : a < 0 := by simp only [a]; rw [sub_neg, lt_div_iff₀ hp0]; linarith
  -- Lewis identity: `qform(e^{a y})_j = e^{(2/p) y_j}`
  have hLew : qform B (fun k => exp (a * y k)) j = exp ((1 - a) * y j) := by
    have h := lev_lewisLog hB hrow hp0 hp1 j
    rw [lev_diag] at h
    have e : ∀ k, exp ((1 / 2 - 1 / p) * lewisLog p B k) ^ 2 = exp (a * y k) := fun k => by
      rw [← exp_nat_mul]; congr 1; simp only [a, y]; push_cast; ring
    simp only [e] at h
    have hne : exp (a * y j) ≠ 0 := exp_ne_zero _
    rw [show (1 - a) * y j = y j - a * y j by ring, exp_sub]
    field_simp
    linarith
  -- `BᵀW^aB ⪯ w_j^a BᵀB`, so `σ_j(B) = qform(1)_j ≤ w_j^a · qform(e^{ay})_j = w_j`
  have hcmp : qform B (fun _ => (1 : ℝ)) j ≤ exp (a * y j) * qform B (fun k => exp (a * y k)) j :=
    qform_le hB (d := fun k => exp (a * y k)) (d' := fun _ => 1) (fun k => exp_pos _)
      (fun _ => one_pos) (exp_pos (a * y j)) (fun k => by
        rw [mul_one, exp_le_exp]
        exact mul_le_mul_of_nonpos_left (hj k (mem_univ k)) ha.le) j
  have hlev : lev B j = qform B (fun _ => (1 : ℝ)) j := by
    have := lev_diag (B := B) (fun _ => (1 : ℝ)) j
    simpa using this
  rw [hlev]
  refine hcmp.trans (le_of_eq ?_)
  rw [hLew, ← exp_add]; congr 1; ring

/-- **Restart from `v = 1`:** if `q ≤ e^{y*ᵢ} ≤ 1` with `0 < q ≤ 1`, then
`‖0 − y*‖_∞ ≤ log(1/q)`. -/
theorem restart_error {ystar : Fin M → ℝ} {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hlo : ∀ i, q ≤ exp (ystar i)) (hhi : ∀ i, exp (ystar i) ≤ 1) :
    dist (0 : Fin M → ℝ) ystar ≤ Real.log (1 / q) := by
  have h0 : 0 ≤ Real.log (1 / q) := Real.log_nonneg (by rw [le_div_iff₀ hq]; linarith)
  refine (dist_pi_le_iff h0).mpr fun i => ?_
  have hy0 : ystar i ≤ 0 := by have := hhi i; rwa [exp_le_one_iff] at this
  have hlq : Real.log q ≤ ystar i := by
    rw [← exp_le_exp, exp_log hq]; exact hlo i
  rw [Pi.zero_apply, Real.dist_eq, zero_sub, abs_neg, abs_of_nonpos hy0, one_div, Real.log_inv]
  linarith

end

end ImplicitLP
end CutQueryComplexity
