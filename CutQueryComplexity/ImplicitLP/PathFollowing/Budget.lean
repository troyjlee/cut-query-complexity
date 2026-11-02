import CutQueryComplexity.ImplicitLP.PathFollowing.Run

set_option autoImplicit false

/-! # Fixed path schedules and spectral-call accounting

Increasing and decreasing geometric paths are stopped at a public cap. The theorem on
the spectral-call cap is obtained from the failure theorem for the real composed run.
-/

namespace CutQueryComplexity.ImplicitLP.PathFollowing

open Probability
open scoped ENNReal
noncomputable section

variable {E : NewtonPub}

def upSchedule (start α : ℝ) (cap j : ℕ) : ℝ := start * (1 + α) ^ min j cap
def downSchedule (start α : ℝ) (cap j : ℕ) : ℝ := start / (1 + α) ^ min j cap

/-- A deterministic logarithmic phase cap computed entirely from public scalars. -/
def phaseSteps (ratio α : ℝ) : ℕ := ⌈Real.log ratio / Real.log (1 + α)⌉₊

theorem phaseSteps_reaches {ratio α : ℝ} (hr : 0 < ratio) (hα : 0 < α) :
    ratio ≤ (1 + α) ^ phaseSteps ratio α := by
  have hb : 0 < 1 + α := by linarith
  have hl : 0 < Real.log (1 + α) := Real.log_pos (by linarith)
  apply (Real.log_le_log_iff hr (pow_pos hb _)).mp
  rw [Real.log_pow]
  exact (div_le_iff₀ hl).mp (Nat.le_ceil (Real.log ratio / Real.log (1 + α)))

theorem phaseSteps_bound {ratio α : ℝ} (hr : 1 ≤ ratio) (hα : 0 < α) :
    (phaseSteps ratio α : ℝ) ≤ Real.log ratio / Real.log (1 + α) + 1 := by
  have hl : 0 < Real.log (1 + α) := Real.log_pos (by linarith)
  exact (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hr) hl.le)).le

theorem phaseSteps_overshoot {ratio α : ℝ} (hr : 1 ≤ ratio) (hα : 0 < α) :
    (1 + α) ^ phaseSteps ratio α ≤ ratio * (1 + α) := by
  have hr0 : 0 < ratio := by linarith
  have hb : 0 < 1 + α := by linarith
  have hl : 0 < Real.log (1 + α) := Real.log_pos (by linarith)
  apply (Real.log_le_log_iff (pow_pos hb _) (mul_pos hr0 hb)).mp
  rw [Real.log_pow, Real.log_mul hr0.ne' hb.ne']
  have h := mul_le_mul_of_nonneg_right (phaseSteps_bound hr hα) hl.le
  rwa [add_mul, div_mul_cancel₀ _ hl.ne', one_mul] at h

theorem phaseSteps_bound_step {ratio α : ℝ} (hr : 1 ≤ ratio) (hα : 0 < α) (hα1 : α ≤ 1) :
    (phaseSteps ratio α : ℝ) ≤ (2 / α) * Real.log ratio + 1 := by
  have hlog : α / 2 ≤ Real.log (1 + α) := by
    refine le_trans ?_ (Real.le_log_one_add_of_nonneg hα.le)
    rw [le_div_iff₀ (by linarith : 0 < α + 2)]
    nlinarith [mul_le_mul_of_nonneg_left hα1 hα.le]
  refine (phaseSteps_bound hr hα).trans (add_le_add ?_ le_rfl)
  calc Real.log ratio / Real.log (1 + α) ≤ Real.log ratio / (α / 2) :=
        div_le_div_of_nonneg_left (Real.log_nonneg hr) (by positivity) hlog
    _ = (2 / α) * Real.log ratio := by field_simp [hα.ne']

theorem downSchedule_reaches {start target α : ℝ} (hs : 0 < start) (ht : 0 < target)
    (hα : 0 < α) :
    downSchedule start α (phaseSteps (start / target) α) (phaseSteps (start / target) α) ≤ target := by
  have hb : 0 < 1 + α := by linarith
  simp only [downSchedule, min_self]
  rw [div_le_iff₀ (pow_pos hb _)]
  have h := (div_le_iff₀ ht).mp (phaseSteps_reaches (div_pos hs ht) hα)
  simpa only [mul_comm] using h

theorem upSchedule_move {start α : ℝ} (hs : 0 < start) (hα : 0 ≤ α) (cap j : ℕ) :
    |upSchedule start α cap (j + 1) / upSchedule start α cap j - 1| ≤ α := by
  have hb : 0 < 1 + α := by linarith
  by_cases hj : j < cap
  · rw [upSchedule, upSchedule, min_eq_left (by omega), min_eq_left (by omega), pow_succ]
    have he : start * ((1 + α) ^ j * (1 + α)) / (start * (1 + α) ^ j) - 1 = α := by
      field_simp [hs.ne', hb.ne']; ring
    rw [he, abs_of_nonneg hα]
  · rw [upSchedule, upSchedule, min_eq_right (by omega), min_eq_right (by omega)]
    rw [div_self (mul_pos hs (pow_pos hb _)).ne', sub_self, abs_zero]
    exact hα

theorem downSchedule_move {start α : ℝ} (hs : 0 < start) (hα : 0 ≤ α) (cap j : ℕ) :
    |downSchedule start α cap (j + 1) / downSchedule start α cap j - 1| ≤ α := by
  have hb : 0 < 1 + α := by linarith
  by_cases hj : j < cap
  · rw [downSchedule, downSchedule, min_eq_left (by omega), min_eq_left (by omega), pow_succ]
    have he : start / ((1 + α) ^ j * (1 + α)) / (start / (1 + α) ^ j) - 1 = -α / (1 + α) := by
      field_simp [hs.ne', hb.ne']; ring
    rw [he, abs_div, abs_neg, abs_of_nonneg hα, abs_of_pos hb]
    exact div_le_self hα (by linarith)
  · rw [downSchedule, downSchedule, min_eq_right (by omega), min_eq_right (by omega)]
    rw [div_self (div_pos hs (pow_pos hb _)).ne', sub_self, abs_zero]
    exact hα

variable {G : DiGraph (Fin E.n)} {P : Params E} {bc : Fin E.n → ℝ}

/-- A public step size that satisfies both centrality-margin inequalities. -/
def Params.stepSize (P : Params E) : ℝ :=
  min ((1 / (2 * P.L) * P.Δ) / (16 * P.T)) ((1 / (2 * P.L)) / 16)

theorem stepSize_spec (H : Regime G P bc) :
    0 < P.stepSize ∧ P.stepSize * P.T ≤ 1 / (2 * P.L) * P.Δ / 16 ∧
      P.stepSize * P.Δ ≤ 1 / (2 * P.L) * P.Δ / 16 := by
  have hL : 0 < P.L := by linarith [H.L_ge]
  have hT : 0 < P.T := by linarith [H.T_ge]
  have hΔ := H.Δ_pos
  refine ⟨lt_min (by positivity) (by positivity), ?_, ?_⟩
  · have h := min_le_left ((1 / (2 * P.L) * P.Δ) / (16 * P.T)) ((1 / (2 * P.L)) / 16)
    change P.stepSize ≤ _ at h
    rw [le_div_iff₀ (by positivity : 0 < 16 * P.T)] at h
    linarith
  · have h := mul_le_mul_of_nonneg_right
      (min_le_right ((1 / (2 * P.L) * P.Δ) / (16 * P.T)) ((1 / (2 * P.L)) / 16)) hΔ.le
    change P.stepSize * P.Δ ≤ _ at h
    convert h using 1; ring

theorem upSchedule_licensed (H : Regime G P bc) {start α : ℝ} (hs : 0 < start)
    (hα : 0 ≤ α) (cap : ℕ) (hend : start * (1 + α) ^ cap ≤ 16 * E.n / E.ε)
    (hαT : α * P.T ≤ 1 / (2 * P.L) * P.Δ / 16)
    (hαΔ : α * P.Δ ≤ 1 / (2 * P.L) * P.Δ / 16) : Schedule P (upSchedule start α cap) := by
  have hb : 0 < 1 + α := by linarith
  refine ⟨fun j => mul_pos hs (pow_pos hb _), ?_, ?_, ?_⟩
  · intro j
    rw [upSchedule, abs_of_pos (mul_pos hs (pow_pos hb _))]
    refine (mul_le_mul_of_nonneg_left ?_ hs.le).trans hend
    exact pow_le_pow_right₀ (by linarith) (min_le_right j cap)
  · intro j
    exact (mul_le_mul_of_nonneg_right (upSchedule_move hs hα cap j) (by linarith [H.T_ge])).trans hαT
  · intro j
    exact (mul_le_mul_of_nonneg_right (upSchedule_move hs hα cap j) H.Δ_pos.le).trans hαΔ

theorem downSchedule_licensed (H : Regime G P bc) {start α : ℝ} (hs : 0 < start)
    (hα : 0 ≤ α) (cap : ℕ) (hstart : start ≤ 16 * E.n / E.ε)
    (hαT : α * P.T ≤ 1 / (2 * P.L) * P.Δ / 16)
    (hαΔ : α * P.Δ ≤ 1 / (2 * P.L) * P.Δ / 16) : Schedule P (downSchedule start α cap) := by
  have hb : 0 < 1 + α := by linarith
  refine ⟨fun j => div_pos hs (pow_pos hb _), ?_, ?_, ?_⟩
  · intro j
    rw [downSchedule, abs_of_pos (div_pos hs (pow_pos hb _))]
    exact (div_le_self hs.le (one_le_pow₀ (by linarith))).trans hstart
  · intro j
    exact (mul_le_mul_of_nonneg_right (downSchedule_move hs hα cap j) (by linarith [H.T_ge])).trans hαT
  · intro j
    exact (mul_le_mul_of_nonneg_right (downSchedule_move hs hα cap j) H.Δ_pos.le).trans hαΔ

theorem upSchedule_endpoint (start α : ℝ) (cap : ℕ) :
    upSchedule start α cap cap = start * (1 + α) ^ cap := by simp [upSchedule]

theorem downSchedule_endpoint (start α : ℝ) (cap : ℕ) :
    downSchedule start α cap cap = start / (1 + α) ^ cap := by simp [downSchedule]

theorem upSchedule_public (H : Regime G P bc) {start : ℝ} (hs : 0 < start) (cap : ℕ)
    (hend : start * (1 + P.stepSize) ^ cap ≤ 16 * E.n / E.ε) :
    Schedule P (upSchedule start P.stepSize cap) :=
  upSchedule_licensed H hs (stepSize_spec H).1.le cap hend
    (stepSize_spec H).2.1 (stepSize_spec H).2.2

theorem downSchedule_public (H : Regime G P bc) {start : ℝ} (hs : 0 < start) (cap : ℕ)
    (hstart : start ≤ 16 * E.n / E.ε) : Schedule P (downSchedule start P.stepSize cap) :=
  downSchedule_licensed H hs (stepSize_spec H).1.le cap hstart
    (stepSize_spec H).2.1 (stepSize_spec H).2.2

theorem stepSize_le_one (H : Regime G P bc) : P.stepSize ≤ 1 := by
  have ha : 1 / (2 * P.L) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [H.L_ge])
  exact (min_le_right _ _).trans (by linarith)

theorem stepSize_eq (H : Regime G P bc) :
    P.stepSize = (1 / (2 * P.L) * P.Δ) / (16 * P.T) := by
  have ha : 1 / (2 * P.L) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [H.L_ge])
  have ha0 : 0 ≤ 1 / (2 * P.L) := by have := H.L_ge; positivity
  have hd : P.Δ ≤ P.T := by
    nlinarith [H.Δ_le, H.T_ge, mul_le_mul ha ha ha0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  apply min_eq_left
  rw [div_le_div_iff₀ (by linarith [H.T_ge]) (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left hd ha0]

/-- The public phase length has the explicit `L T / Δ` factor used in query accounting. -/
theorem phaseSteps_public_bound (H : Regime G P bc) {ratio : ℝ} (hr : 1 ≤ ratio) :
    (phaseSteps ratio P.stepSize : ℝ) ≤
      (64 * P.L * P.T / P.Δ) * Real.log ratio + 1 := by
  have h := phaseSteps_bound_step hr (stepSize_spec H).1 (stepSize_le_one H)
  have he : 2 / P.stepSize = 64 * P.L * P.T / P.Δ := by
    rw [stepSize_eq H]
    have hL : 0 < P.L := by linarith [H.L_ge]
    have hT : 0 < P.T := by linarith [H.T_ge]
    field_simp [hL.ne', hT.ne', H.Δ_pos.ne']; ring
  simpa only [he] using h

/-- A public cost-switch parameter with the required margin. -/
def Params.switchTarget (P : Params E) : ℝ :=
  min 1 ((1 / (2 * P.L) * P.Δ / 2) / (P.T * (32 * E.Mbar * E.U ^ 2)))

def Params.downSteps (P : Params E) : ℕ := phaseSteps (1 / P.switchTarget) P.stepSize
def initialPhase (P : Params E) : ℕ → ℝ := downSchedule 1 P.stepSize P.downSteps
def Params.upSteps (P : Params E) : ℕ :=
  phaseSteps ((8 * E.n / E.ε) / initialPhase P P.downSteps) P.stepSize
def truePhase (P : Params E) : ℕ → ℝ :=
  upSchedule (initialPhase P P.downSteps) P.stepSize P.upSteps

theorem switchTarget_spec (H : Regime G P bc) :
    0 < P.switchTarget ∧ P.switchTarget ≤ 1 ∧
      P.switchTarget * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤ 1 / (2 * P.L) * P.Δ / 2 := by
  have hL : 0 < P.L := by linarith [H.L_ge]
  have hT : 0 < P.T := by linarith [H.T_ge]
  have hM : 0 < E.Mbar := H.rows_pos.trans_le H.M_le
  have hU : 0 < E.U := by linarith [H.U_ge]
  have hΔ := H.Δ_pos
  exact ⟨lt_min (by norm_num) (by positivity), min_le_left _ _,
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)⟩

theorem initialPhase_licensed (H : Regime G P bc) : Schedule P (initialPhase P) := by
  apply downSchedule_public H (by norm_num)
  rw [le_div_iff₀ H.ε_pos]
  nlinarith [H.rank_ge, H.ε_le]

theorem initialPhase_starts (P : Params E) : initialPhase P 0 = 1 := by
  simp [initialPhase, downSchedule]

theorem initialPhase_switch (H : Regime G P bc) :
    |initialPhase P P.downSteps| * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤
      1 / (2 * P.L) * P.Δ / 2 := by
  have ht := (initialPhase_licensed H).positive P.downSteps
  have hend : initialPhase P P.downSteps ≤ P.switchTarget :=
    downSchedule_reaches (by norm_num) (switchTarget_spec H).1 (stepSize_spec H).1
  have hM : 0 < E.Mbar := H.rows_pos.trans_le H.M_le
  rw [abs_of_pos ht]
  exact (mul_le_mul_of_nonneg_right hend
    (by have := H.T_ge; positivity)).trans (switchTarget_spec H).2.2

theorem truePhase_joins (P : Params E) : truePhase P 0 = initialPhase P P.downSteps := by
  simp [truePhase, upSchedule]

/-- The constructed true-cost schedule stays below the public numerical cap and reaches
the objective-gap target. Both step counts are logarithmic public ceilings. -/
theorem truePhase_licensed (H : Regime G P bc) :
    Schedule P (truePhase P) ∧ 8 * E.n / E.ε ≤ truePhase P P.upSteps := by
  have hs := (initialPhase_licensed H).positive P.downSteps
  have hn : (0 : ℝ) < E.n := by linarith [H.rank_ge]
  have htarget : 0 < 8 * E.n / E.ε := by have := H.ε_pos; positivity
  have hs1 : initialPhase P P.downSteps ≤ 1 :=
    (downSchedule_reaches (by norm_num) (switchTarget_spec H).1 (stepSize_spec H).1).trans
      (switchTarget_spec H).2.1
  have hst : initialPhase P P.downSteps ≤ 8 * E.n / E.ε := by
    refine hs1.trans ?_
    rw [le_div_iff₀ H.ε_pos]
    nlinarith [H.rank_ge, H.ε_le]
  have hratio : 1 ≤ (8 * E.n / E.ε) / initialPhase P P.downSteps :=
    (one_le_div hs).mpr hst
  have hu := phaseSteps_overshoot hratio (stepSize_spec H).1
  have he : initialPhase P P.downSteps *
      ((8 * E.n / E.ε) / initialPhase P P.downSteps * (1 + P.stepSize)) =
      (8 * E.n / E.ε) * (1 + P.stepSize) := by field_simp [hs.ne', H.ε_pos.ne']
  constructor
  · apply upSchedule_public H hs
    calc initialPhase P P.downSteps * (1 + P.stepSize) ^ P.upSteps ≤
          initialPhase P P.downSteps *
            ((8 * E.n / E.ε) / initialPhase P P.downSteps * (1 + P.stepSize)) :=
          mul_le_mul_of_nonneg_left hu hs.le
      _ = (8 * E.n / E.ε) * (1 + P.stepSize) := he
      _ ≤ (8 * E.n / E.ε) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [stepSize_le_one H]) htarget.le
      _ = 16 * E.n / E.ε := by ring
  · have h := mul_le_mul_of_nonneg_left
      (phaseSteps_reaches (div_pos htarget hs) (stepSize_spec H).1) hs.le
    have he' : initialPhase P P.downSteps * ((8 * E.n / E.ε) / initialPhase P P.downSteps) =
        8 * E.n / E.ε := by field_simp [hs.ne', H.ε_pos.ne']
    rw [he'] at h
    simpa only [truePhase, upSchedule, min_self, Params.upSteps] using h

def Params.finalGoal (_P : Params E) : ℝ := E.ε / (8 * E.U * (2 * E.n + 1 / 2))
def Params.finalSteps (P : Params E) : ℕ := phaseSteps (P.Δ / P.finalGoal) 1

theorem finalSteps_reaches (H : Regime G P bc) :
    (1 / 2 : ℝ) ^ P.finalSteps * P.Δ ≤ P.finalGoal := by
  have hU : 0 < E.U := by linarith [H.U_ge]
  have hgoal : 0 < P.finalGoal := by unfold Params.finalGoal; have := H.ε_pos; positivity
  have h := phaseSteps_reaches (div_pos H.Δ_pos hgoal) (by norm_num : (0 : ℝ) < 1)
  have h' : P.Δ / (2 : ℝ) ^ P.finalSteps ≤ P.finalGoal := by
    rw [div_le_iff₀ (by positivity)]
    have h'' := (div_le_iff₀ hgoal).mp h
    norm_num only at h''
    simpa only [mul_comm, Params.finalSteps] using h''
  simpa only [div_pow, one_pow, one_div_mul_eq_div] using h'

/-- The two public phase caps and final centering count imply the full LP accuracy bound. -/
theorem public_final_accuracy (H : Regime G P bc) :
    4 * E.n / truePhase P P.upSteps + (2 * E.n + 1 / 2) *
      (4 * E.U * ((1 / 2 : ℝ) ^ P.finalSteps * P.Δ)) ≤ E.ε := by
  have hn : (0 : ℝ) < E.n := by linarith [H.rank_ge]
  have hU : 0 < E.U := by linarith [H.U_ge]
  have hrpos : 0 < 2 * (E.n : ℝ) + 1 / 2 := by positivity
  have ht := (truePhase_licensed H).1.positive P.upSteps
  have hfirst : 4 * E.n / truePhase P P.upSteps ≤ E.ε / 2 := by
    rw [div_le_iff₀ ht]
    have h := mul_le_mul_of_nonneg_left (truePhase_licensed H).2 H.ε_pos.le
    have he : E.ε * (8 * E.n / E.ε) = 8 * E.n := by field_simp [H.ε_pos.ne']
    rw [he] at h
    linarith
  have hsecond : (2 * E.n + 1 / 2) * (4 * E.U * ((1 / 2 : ℝ) ^ P.finalSteps * P.Δ)) ≤
      E.ε / 2 := by
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (finalSteps_reaches H) (by positivity : 0 ≤ 4 * E.U))
      (by positivity : (0 : ℝ) ≤ 2 * E.n + 1 / 2)
    convert h using 1
    unfold Params.finalGoal
    field_simp [hU.ne', hrpos.ne']; ring
  linarith

/-- One Newton D4 call and `J_L` Lewis D4 calls per batch. -/
def spectralCallCap (P : Params E) (N : ℕ) : ℕ := N * (1 + batchJL E P.Δ)

/-- Assigning a common per-call conditional failure bound yields the deterministic global
spectral cap, for the actual public run. -/
theorem run_failure_of_per_call (H : Regime G P bc) {τ : ℕ → ℝ} (hτ : Schedule P τ)
    (N j : ℕ) {st : State E.n} (hs : Invariant G P bc (τ j) st) {δ : ℝ≥0∞}
    (hsolve : d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) ≤ δ)
    (hlev : d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) ≤ δ) :
    mass ((run P τ N j st).eval G.out) (fun out => ¬Good G P bc (τ (j + N)) out) ≤
      spectralCallCap P N * δ := by
  refine (run_failure H hτ N j hs).trans ?_
  calc (N : ℝ≥0∞) * H.batchFailure ≤ N * (δ + batchJL E P.Δ * δ) :=
        mul_le_mul' le_rfl (add_le_add hsolve (mul_le_mul' le_rfl hlev))
    _ = spectralCallCap P N * δ := by unfold spectralCallCap; push_cast; ring

end
end CutQueryComplexity.ImplicitLP.PathFollowing

#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.upSchedule_licensed
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.downSchedule_licensed
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.run_failure_of_per_call
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.stepSize_spec
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.downSchedule_public
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.upSchedule_public
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.phaseSteps_bound
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.downSchedule_reaches
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.initialPhase_licensed
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.initialPhase_switch
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.truePhase_licensed
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.public_final_accuracy
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.phaseSteps_public_bound
