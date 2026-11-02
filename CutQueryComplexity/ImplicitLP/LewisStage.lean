import CutQueryComplexity.ImplicitLP.PublicParams
import CutQueryComplexity.ImplicitLP.LewisFloor
import CutQueryComplexity.ImplicitLP.Size
import CutQueryComplexity.ImplicitLP.NumericLP

set_option autoImplicit false

/-! # The public Lewis stage: restart and cap (D7 → D8, step 2)

At a strictly interior state `x` with the slack floor `s_* ≤ slk(x)` and box widths `≤ U`:

* `lpMap3`, `lpVec_lpMap3`: a coordinatewise formula of copy-constant points is copy-constant,
  so the inverse-slack point `s = e^{s(x)} = 1/S(x)` (`invSlackPt`) is a public LP point when
  `κ, m, x` are (`lpVec_invSlackPt`).
* `lewis_restart_lp`: restarting the Lewis iteration from `v = 1` (`zeroPt`, `log v = 0`) has
  `‖0 − y*‖_∞ ≤ E₀ := log(1/q̄)` with the public floor `q̄ = s_*²/(8M̄U²) ≤ q_*`
  (`lewis_floor_qstar` with `a₀ = 1`, the weights `≤ 1` by `eq_gsize`), for the Lewis fixed
  point `y* = log w_p(diag(e^{s(x)}) A)` — the one inside `g(x)`.
* `lewis_cap`: `J_L = 3 · iters(Δ/(32(E₀+1)))` gives `(3/4)^{J_L} E₀ ≤ Δ/32`
  (`(3/4)³ ≤ 1/2` and `half_pow_iters_le`).
* `lewisStage`: the loop with this `J_L` from `zeroPt` costs `≤ J_L · q_D4` on every execution
  and, outside `J_L · F`, outputs `y` with `‖y − y*‖_∞ ≤ Δ/16`; the observation
  `z = log(e^y + c₀)` satisfies `|z − log g(x)| ≤ Δ/16`, the form of `prop_batch`'s `hz`.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Spectral

noncomputable section

open DirectedMincut (LPPoint)
open scoped ENNReal

variable {n : ℕ}

/-! ## Public points -/

/-- A coordinatewise formula of three LP points. -/
def lpMap3 (f : ℝ → ℝ → ℝ → ℝ) (a b c : LPPoint (Fin n)) : LPPoint (Fin n) :=
  ⟨fun u v => f (a.z u v) (b.z u v) (c.z u v), f a.q b.q c.q,
    fun j => f (a.yp j) (b.yp j) (c.yp j), fun j => f (a.ym j) (b.ym j) (c.ym j)⟩

/-- The restart point `log v = 0`. -/
def zeroPt : LPPoint (Fin n) := ⟨fun _ _ => 0, 0, fun _ => 0, fun _ => 0⟩

/-- The inverse-slack point `e^{s(x)} = cos(κ(x − m))/κ` of copy-constant `κ, m, x`. -/
def invSlackPt (κp mp xp : LPPoint (Fin n)) : LPPoint (Fin n) :=
  lpMap3 (fun k mm xx => Real.cos (k * (xx - mm)) / k) κp mp xp

variable (G : DiGraph (Fin n))

theorem lpVec_lpMap3 (f : ℝ → ℝ → ℝ → ℝ) (a b c : LPPoint (Fin n)) (i : Fin (lpM G)) :
    lpVec G (lpMap3 f a b c) i = f (lpVec G a i) (lpVec G b i) (lpVec G c i) := by
  simp only [lpVec]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j)) <;> rfl

theorem lpVec_zeroPt : lpVec G (zeroPt : LPPoint (Fin n)) = 0 := by
  funext i
  simp only [lpVec, Pi.zero_apply]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j)) <;> rfl

/-- **The inverse-slack point is public:** `lpVec (invSlackPt κ m x) = e^{s(x)}`. -/
theorem lpVec_invSlackPt {κ m x : Fin (lpM G) → ℝ} (hκ : ∀ i, 0 < κ i)
    (hx : Interior κ m x) {κp mp xp : LPPoint (Fin n)} (hκp : lpVec G κp = κ)
    (hmp : lpVec G mp = m) (hxp : lpVec G xp = x) :
    lpVec G (invSlackPt κp mp xp) = fun i => exp (sfun κ m x i) := by
  funext i
  rw [invSlackPt, lpVec_lpMap3, hκp, hmp, hxp, sfun,
    exp_log (div_pos (cos_theta_pos hx i) (hκ i))]
  rfl

/-- Every LP row has squared norm at least `1` (`a₀ = 1`). -/
theorem lpA_row_sq_ge {s t : Fin n} (hst : s ≠ t) (i : Fin (lpM G)) :
    1 ≤ ∑ j, lpA G s t i j ^ 2 := by
  suffices h : ∃ j, lpA G s t i j ^ 2 = 1 by
    obtain ⟨j, hj⟩ := h
    rw [← hj]
    exact single_le_sum (f := fun j => lpA G s t i j ^ 2) (fun _ _ => sq_nonneg _) (mem_univ j)
  simp only [lpA]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j))
  · exact ⟨p.1.1, by simp [lpRowVec, incVec_apply, p.2.ne]⟩
  · exact ⟨s, by simp [lpRowVec, DirectedMincut.chi, hst]⟩
  · exact ⟨j, by simp [lpRowVec]⟩
  · exact ⟨j, by simp [lpRowVec]⟩

/-! ## The public floor, the restart error, and the cap -/

/-- The public Lewis floor `q̄ = s_*²/(8M̄U²)`. -/
def lewisQ (Mbar U sst : ℝ) : ℝ := sst ^ 2 / (8 * Mbar * U ^ 2)

/-- The public restart error `E₀ = log(1/q̄)`. -/
def lewisE0 (Mbar U sst : ℝ) : ℝ := Real.log (1 / lewisQ Mbar U sst)

/-- The public Lewis iteration count `J_L = 3 · iters(Δ/(32(E₀+1)))`. -/
def lewisJL (Δ E₀ : ℝ) : ℕ := 3 * iters (Δ / (32 * (E₀ + 1)))

/-- **The cap:** `(3/4)^{J_L} E₀ ≤ Δ/32`. -/
theorem lewis_cap {Δ E₀ : ℝ} (hΔ : 0 < Δ) (hE₀ : 0 ≤ E₀) :
    (3 / 4 : ℝ) ^ lewisJL Δ E₀ * E₀ ≤ Δ / 32 := by
  set β : ℝ := Δ / (32 * (E₀ + 1)) with hβ
  have hβ0 : 0 < β := by positivity
  have h1 : (3 / 4 : ℝ) ^ lewisJL Δ E₀ ≤ β := by
    rw [lewisJL, pow_mul]
    refine (pow_le_pow_left₀ (by norm_num) (by norm_num : ((3 : ℝ) / 4) ^ 3 ≤ 1 / 2) _).trans ?_
    exact half_pow_iters_le hβ0
  have h2 : β * E₀ = Δ / 32 * (E₀ / (E₀ + 1)) := by
    rw [hβ]; field_simp
  have h3 : E₀ / (E₀ + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  calc (3 / 4 : ℝ) ^ lewisJL Δ E₀ * E₀ ≤ β * E₀ := mul_le_mul_of_nonneg_right h1 hE₀
    _ = Δ / 32 * (E₀ / (E₀ + 1)) := h2
    _ ≤ Δ / 32 := mul_le_of_le_one_right (by positivity) h3

/-- **Final error after the cap:** `(3/4)^{J_L}‖y₀ − y*‖ + Δ/32 ≤ Δ/16` when `‖y₀ − y*‖ ≤ E₀`. -/
theorem lewis_cap_final {Δ E₀ d : ℝ} (hΔ : 0 < Δ) (hd0 : 0 ≤ d) (hd : d ≤ E₀) :
    (3 / 4 : ℝ) ^ lewisJL Δ E₀ * d + Δ / 32 ≤ Δ / 16 := by
  have h := lewis_cap hΔ (hd0.trans hd)
  have : (3 / 4 : ℝ) ^ lewisJL Δ E₀ * d ≤ (3 / 4) ^ lewisJL Δ E₀ * E₀ :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  linarith

/-- `u ↦ log(e^u + c₀)` is `1`-Lipschitz for `c₀ ≥ 0`. -/
theorem abs_log_exp_add_sub_le {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (a b : ℝ) :
    |Real.log (exp a + c₀) - Real.log (exp b + c₀)| ≤ |a - b| := by
  have key : ∀ a b : ℝ, b ≤ a →
      0 ≤ Real.log (exp a + c₀) - Real.log (exp b + c₀) ∧
        Real.log (exp a + c₀) - Real.log (exp b + c₀) ≤ a - b := by
    intro a b hab
    have hb0 : 0 < exp b + c₀ := by positivity
    have ha0 : 0 < exp a + c₀ := by positivity
    have hle : exp b + c₀ ≤ exp a + c₀ := by linarith [exp_le_exp.mpr hab]
    refine ⟨sub_nonneg.mpr (Real.log_le_log hb0 hle), ?_⟩
    have h1 : 1 ≤ exp (a - b) := one_le_exp (by linarith)
    have h2 : exp a + c₀ ≤ exp (a - b) * (exp b + c₀) := by
      rw [mul_add, ← exp_add, show a - b + b = a by ring]; nlinarith
    have h3 := Real.log_le_log ha0 h2
    rw [Real.log_mul (exp_pos _).ne' hb0.ne', Real.log_exp] at h3
    linarith
  rcases le_total b a with h | h
  · obtain ⟨h1, h2⟩ := key a b h
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]; exact h2
  · obtain ⟨h1, h2⟩ := key b a h
    rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg (by linarith)]; exact h2

variable {κ m x : Fin (lpM G) → ℝ}

/-- **The restart bound at an interior state with the slack floor.** For
`B = diag(e^{s(x)}) A` (rows nonzero, `BᵀB` invertible) the Lewis fixed point
`y* = lewisLog p B` satisfies `‖0 − y*‖_∞ ≤ E₀ = log(1/q̄)`, and `0 ≤ E₀`. -/
theorem lewis_restart_lp {s t : Fin n} (hst : s ≠ t) (hκ : ∀ i, 0 < κ i)
    (hx : Interior κ m x) {U : ℝ} (hU1 : 1 ≤ U) (hU : ∀ i, π / κ i ≤ U)
    {sst Mbar : ℝ} (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hMbar : (lpM G : ℝ) ≤ Mbar)
    {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    let B := diagonal (fun j => exp (sfun κ m x j)) * lpA G s t
    (Bᵀ * B).det ≠ 0 ∧ (∀ i, B i ≠ 0) ∧ lewisMap p B (lewisLog p B) = lewisLog p B ∧
      (∀ i, lewisQ Mbar U sst ≤ exp (lewisLog p B i) ∧ exp (lewisLog p B i) ≤ 1) ∧
      0 ≤ lewisE0 Mbar U sst ∧ dist (0 : Fin (lpM G) → ℝ) (lewisLog p B) ≤ lewisE0 Mbar U sst := by
  intro B
  set A := lpA G s t
  have hA : (Aᵀ * A).det ≠ 0 := det_ne_zero_of_idRows (lpA_idRows G s t)
  have hS0 := barS_pos hκ hx
  have hdiag : (fun j => exp (sfun κ m x j)) = fun j => (barS κ m x j)⁻¹ := by
    funext j; rw [exp_sfun hκ hx j, one_div]
  have hBeq : B = diagonal (fun j => (barS κ m x j)⁻¹) * A := by simp only [B, A, hdiag]
  have hB : (Bᵀ * B).det ≠ 0 := diag_det hA fun j => (exp_pos _).ne'
  have hrowB : ∀ i, B i ≠ 0 := fun i h0 => by
    apply lpA_row_ne_zero G hst i
    funext j
    have := congrFun h0 j
    simp only [B, diagonal_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (exp_pos _).ne'
  have hfix := lewisLog_fixed hB hrowB hp0 hp2
  -- the floor `q_* ≤ w` and `w ≤ 1`
  have hn : 0 < n := Fin.pos s
  have hM : 0 < lpM G := Fin.pos (lpIota G ⟨0, hn⟩)
  have hM1 : (1 : ℝ) ≤ lpM G := by exact_mod_cast hM
  have hU0 : 0 < U := by linarith
  have hslk0 : ∀ i, 0 < slk κ m x i := fun i => lt_of_lt_of_le hsst (hs i)
  have hS := fun i => barrier_env hκ hx hU1 hU i
  have hrowlo : ∀ i, (1 : ℝ) ^ 2 ≤ euc (A i) ^ 2 := fun i => by
    rw [one_pow, euc_sq]; exact lpA_row_sq_ge G hst i
  have hrowhi : ∀ i, euc (A i) ^ 2 ≤ 2 := fun i => by
    rw [euc_sq]; exact lpA_row_sq_le G s t i
  have hShi : ∀ i, barS κ m x i ≤ 2 / slk κ m x i := fun i => by
    rw [le_div_iff₀ (hslk0 i)]; exact (hS i).2.1
  have hfloor : ∀ i, 1 ^ 2 * sst ^ 2 / (8 * lpM G * U ^ 2) ≤ exp (lewisLog p B i) := fun i => by
    rw [hBeq] at hB hrowB ⊢
    exact lewis_floor_qstar hB hrowB hp0 hp2 hM one_pos hU0 hsst hrowlo hrowhi
      (fun i => (hS i).1) hShi hs i
  have hMb0 : 0 < Mbar := by linarith
  have hq0 : 0 < lewisQ Mbar U sst := by unfold lewisQ; positivity
  have hqle : ∀ i, lewisQ Mbar U sst ≤ exp (lewisLog p B i) := fun i => by
    refine le_trans ?_ (hfloor i)
    unfold lewisQ
    rw [one_pow, one_mul]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
  have hhi : ∀ i, exp (lewisLog p B i) ≤ 1 := fun i => by
    have := ((eq_gsize hB hrowB hp0 hp2 0).2 i).2
    linarith
  have hq1 : lewisQ Mbar U sst ≤ 1 := (hqle (lpIota G ⟨0, hn⟩)).trans (hhi _)
  have hE0 : 0 ≤ lewisE0 Mbar U sst :=
    Real.log_nonneg (by rw [le_div_iff₀ hq0]; linarith)
  exact ⟨hB, hrowB, hfix, fun i => ⟨hqle i, hhi i⟩, hE0,
    restart_error hq0 hq1 hqle hhi⟩

open Probability in
set_option maxHeartbeats 3200000 in
/-- **The public Lewis stage.** At an interior state `x` with box widths `≤ U`, slack floor
`s_* ≤ slk(x)` and `M ≤ M̄`, with the public inverse-slack point `spt` (`lpVec spt = e^{s(x)}`,
e.g. `invSlackPt`), `1/2 ≤ p < 2` and `0 < Δ ≤ 256`, the Lewis loop restarted at `zeroPt`
with `J_L = lewisJL Δ (lewisE0 M̄ U s_*)` iterations
* costs at most `J_L · q_D4,lev` on every execution, and
* outside probability `J_L · F` outputs `y` with `‖y − y*‖_∞ ≤ Δ/16` for the Lewis fixed point
  `y*` inside `g(x)`, so the observation `z = log(e^y + c₀)` has
  `|z − log g(x)| ≤ Δ/16` (the shape of `prop_batch`'s `hz`, with `Δ/16 ≤ Δ`). -/
theorem lewisStage {s t : Fin n} (hst : s ≠ t) (hκ : ∀ i, 0 < κ i)
    (hx : Interior κ m x) {U : ℝ} (hU1 : 1 ≤ U) (hU : ∀ i, π / κ i ≤ U)
    {sst Mbar : ℝ} (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hMbar : (lpM G : ℝ) ≤ Mbar)
    {spt : LPPoint (Fin n)} (hspt : lpVec G spt = fun i => exp (sfun κ m x i))
    {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp2 : p < 2) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 256)
    {K : ℕ} (J : ℕ) {t' : ℕ} (R : ℕ) {Cs : ℝ} (hCs0 : 0 ≤ Cs)
    (hCs : ∀ e, (Spanner.symS G e : ℝ) ≤ Cs) (hK : n ≤ 2 ^ K) (ht' : 0 < t') :
    let JL := lewisJL Δ (lewisE0 Mbar U sst)
    let prog := lewisLoop s t p (levBits Δ) spt zeroPt K J t' R JL
    let ystar := lewisLog p (diagonal (fun j => exp (sfun κ m x j)) * lpA G s t)
    (∀ o ∈ (RTree.run G.out prog).support,
      o.2 ≤ JL * (R * Sparsify.levelBudget (n := n) K J t' + 3 * n)) ∧
    mass (prog.eval G.out)
        (fun o => ¬ ∃ y, o = some y ∧ dist (lpVec G y) ystar ≤ Δ / 16 ∧
          ∀ i, |Real.log (exp (lpVec G y i) + c₀) -
            Real.log (gfun κ m p c₀ (lpA G s t) x i)| ≤ Δ / 16) ≤
      JL * (R * (t' * (2⁻¹ : ℝ≥0∞) ^ J + ENNReal.ofReal (2 * n *
          Real.exp (-(levDelta Δ R ^ 2) / (8 * (Cs * (2 * K + 1 : ℕ) / t'))))) +
        (Fintype.card (Sym2 (Fin n)) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ R) := by
  intro JL prog ystar
  obtain ⟨-, -, hfix, -, -, hrest⟩ :=
    lewis_restart_lp G hst hκ hx hU1 hU hsst hs hMbar (p := p) (by linarith) hp2
  refine ⟨fun o ho => lewisLoop_cost G s t p (levBits Δ) spt zeroPt K J t' R JL ho, ?_⟩
  have hspos : ∀ i, 0 < lpVec G spt i := fun i => by rw [hspt]; exact exp_pos _
  have hfix' : lewisMap p (diagonal (lpVec G spt) * lpA G s t) ystar = ystar := by
    rw [hspt]; exact hfix
  have h := lewisLoop_fail_le G s t hst hspos hp0 hp2 hΔ0 hΔ zeroPt J R hCs0 hCs hK ht' hfix' JL
  refine le_trans (mass_mono _ fun o ho => ?_) h
  intro hgood
  apply ho
  obtain ⟨y, rfl, hy⟩ := hgood
  rw [lpVec_zeroPt] at hy
  have hd : dist (lpVec G y) ystar ≤ Δ / 16 :=
    hy.trans (lewis_cap_final hΔ0 dist_nonneg hrest)
  refine ⟨y, rfl, hd, fun i => ?_⟩
  have hi : |lpVec G y i - ystar i| ≤ Δ / 16 := by
    rw [← Real.dist_eq]; exact (dist_le_pi_dist _ _ i).trans hd
  exact (abs_log_exp_add_sub_le hc₀ _ _).trans hi

/-- **The path-following exponent.** `p = 1 − 1/L₀` with `L₀ ≥ 2` satisfies `1/2 ≤ p < 2`, so
`lewisStage` applies with `gfun κ m (1 − 1/L₀) c₀`, the regularized weights of `prop_batch`;
its window `Δ/16` is within `prop_batch`'s `hz` tolerance `Δ`. -/
theorem lewisExp_bounds {L₀ : ℝ} (hL : 2 ≤ L₀) : 1 / 2 ≤ 1 - 1 / L₀ ∧ 1 - 1 / L₀ < 2 := by
  have h0 : 0 < L₀ := by linarith
  have h1 : 1 / L₀ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hL
  have h2 : 0 < 1 / L₀ := by positivity
  constructor <;> linarith

end

end ImplicitLP
end CutQueryComplexity
