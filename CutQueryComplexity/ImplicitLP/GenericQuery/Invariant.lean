import CutQueryComplexity.ImplicitLP.GenericQuery.Batch
import CutQueryComplexity.ImplicitLP.MixedEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! # Public states and the closed batch invariant

The state is two public LP points. Copy equality therefore holds on every execution,
including unsuccessful spectral executions. The analytic invariant has only feasibility,
potential, and centrality; its log window and mixed-norm envelope are consequences.
The regularizer is the repaired `1 / (2 Mbar)` throughout.
-/

namespace CutQueryComplexity.ImplicitLP.GenericQuery

open Matrix Finset Real
open scoped ENNReal
noncomputable section

abbrev State (n me : ℕ) := Point n me × Point n me

/-- All choices here are public and independent of hidden multiplicities. -/
structure Params (E : NewtonPub) (me : ℕ) where
  rows : ExplicitRows E.n me
  a0 : ℝ
  κ : Point E.n me
  m : Point E.n me
  c : Point E.n me
  L : ℝ
  Δ : ℝ
  K : ℝ
  Kd : ℕ
  J : ℕ
  samples : ℕ
  rounds : ℕ

variable {me : ℕ} {E : NewtonPub}

def Params.C (P : Params E me) : ℝ := 48 * (2 * P.L)
def Params.T (P : Params E me) : ℝ := 1 + P.C * Real.sqrt (4 * E.n)
def Params.μ (P : Params E me) : ℝ := (1 / (2 * P.L) / 8) / (12 * P.Δ)
def Params.c₀ (_P : Params E me) : ℝ := 1 / (2 * E.Mbar)

/-- Static geometric and numerical hypotheses, with no state invariant or solver assumption. -/
structure Regime (G : DiGraph (Fin E.n)) (P : Params E me) (bc : Fin E.n → ℝ) where
  rank_pos : 0 < E.n
  a0_pos : 0 < P.a0
  a0_le : P.a0 ≤ 1
  row_norms : ∀ j, P.a0 ^ 2 ≤ ∑ v, P.rows.matrix j v ^ 2 ∧
    ∑ v, P.rows.matrix j v ^ 2 ≤ 2
  L_ge : 2 ≤ P.L
  logM_le : Real.logb 2 (2 * E.Mbar) ≤ P.L - 1
  κ_pos : ∀ i, 0 < vec G P.κ i
  U_ge : 1 ≤ E.U
  width_le : ∀ i, π / vec G P.κ i ≤ E.U
  reference : Fin (rowCount G me) → ℝ
  reference_feasible : reference ∈ Feasible (matrix G P.rows) bc
    (vec G P.κ) (vec G P.m)
  reference_slack : ∀ i, 1 / E.U ≤ slk (vec G P.κ) (vec G P.m) reference i
  M_le : (rowCount G me : ℝ) ≤ E.Mbar
  ε_pos : 0 < E.ε
  ε_le : E.ε ≤ 1
  cost_le : ‖vec G P.c‖ ≤ 4 * E.U
  C_eq : E.C = P.C
  η_pos : 0 < E.η
  η_le : E.η ≤ 1 / (2 * P.L) * P.Δ / 2 ^ 16
  Δ_pos : 0 < P.Δ
  Δ_le : P.Δ ≤ (1 / (2 * P.L)) ^ 2 / 2 ^ 16
  K_nonneg : 0 ≤ P.K
  K_le : P.K ≤ 1 / (2 * P.L) / 2 ^ 20
  window_le : Real.log (12 * E.Mbar * P.T / (1 / (2 * P.L) / 8)) / P.μ ≤ P.K
  Csym : ℝ
  Csym_nonneg : 0 ≤ Csym
  sym_le : ∀ e, (Spanner.symS G e : ℝ) ≤ Csym
  vertices_le : E.n ≤ 2 ^ P.Kd
  samples_pos : 0 < P.samples

/-- The three maintained analytic facts. Copy equality is provided by `State` itself. -/
structure Invariant (G : DiGraph (Fin E.n)) (P : Params E me) (bc : Fin E.n → ℝ)
    (t : ℝ) (st : State E.n me) : Prop where
  feasible : vec G st.1 ∈ Feasible (matrix G P.rows) bc (vec G P.κ) (vec G P.m)
  potential : pot P.μ (vec G st.2 - fun i => Real.log
    (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
      (matrix G P.rows) (vec G st.1) i)) ≤ 12 * rowCount G me * P.T / (1 / (2 * P.L) / 8)
  centrality : cent P.C (matrix G P.rows) (barS (vec G P.κ) (vec G P.m) (vec G st.1))
    (barDphi (vec G P.κ) (vec G P.m) (vec G st.1)) (vec G P.c) t
    (fun i => exp (vec G st.2 i)) ≤ P.Δ

/-- Representation alone preserves copy equality on all branches. -/
theorem public_copy_eq {n : ℕ} (G : DiGraph (Fin n)) (p : Point n me)
    {i j : Fin (rowCount G me)} {e : Sym2 (Fin n)}
    (hi : hidden G me i = some e) (hj : hidden G me j = some e) :
    vec G p i = vec G p j := copy_eq G p hi hj

theorem frozen_copy_eq {n : ℕ} (G : DiGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (de : Fin me → ℝ) {i j : Fin (rowCount G me)} {e : Sym2 (Fin n)}
    (hi : hidden G me i = some e) (hj : hidden G me j = some e) :
    vec G (weights w de) i = vec G (weights w de) j := copy_eq G _ hi hj

variable {G : DiGraph (Fin E.n)} {P : Params E me} {bc : Fin E.n → ℝ}

theorem Regime.rank_ge (H : Regime G P bc) : (1 : ℝ) ≤ E.n := by
  exact_mod_cast H.rank_pos

theorem Regime.rows_pos (H : Regime G P bc) : (0 : ℝ) < rowCount G me := by
  exact_mod_cast Fin.pos (iota G P.rows ⟨0, H.rank_pos⟩)

theorem Regime.row_ne (H : Regime G P bc) : ∀ i, matrix G P.rows i ≠ 0 :=
  matrix_row_ne_zero G P.rows H.a0_pos H.a0_le H.row_norms

theorem Regime.row_sq_le (H : Regime G P bc) : ∀ i, ∑ j, matrix G P.rows i j ^ 2 ≤ 2 :=
  fun i => (matrix_row_bounds G P.rows H.a0_pos.le H.a0_le H.row_norms i).2

theorem Regime.C_pos (H : Regime G P bc) : 0 < P.C := by
  unfold Params.C
  have := H.L_ge
  positivity

theorem Regime.T_ge (H : Regime G P bc) : 1 ≤ P.T := by
  unfold Params.T
  have := mul_nonneg H.C_pos.le (Real.sqrt_nonneg (4 * E.n))
  linarith

theorem Regime.μ_pos (H : Regime G P bc) : 0 < P.μ := by
  unfold Params.μ
  have := H.L_ge
  have := H.Δ_pos
  positivity

theorem Regime.c₀_le (H : Regime G P bc) : P.c₀ ≤ 1 / (2 * rowCount G me) := by
  exact one_div_le_one_div_of_le (by have := H.rows_pos; positivity) (by nlinarith [H.M_le])

theorem Regime.K_small (H : Regime G P bc) : P.K ≤ 1 / 20 := by
  have ha : 1 / (2 * P.L) ≤ (1 / 4 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [H.L_ge]
  exact H.K_le.trans ((div_le_div_of_nonneg_right ha (by positivity : (0 : ℝ) ≤ 2 ^ 20)).trans
    (by norm_num))

/-- The potential supplies the log window at the next state; no extra invariant is assumed. -/
theorem logWindow_of_potential (H : Regime G P bc) {st : State E.n me}
    (hp : pot P.μ (vec G st.2 - fun i => Real.log
      (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G st.1) i)) ≤
      12 * rowCount G me * P.T / (1 / (2 * P.L) / 8)) (i : Fin (rowCount G me)) :
    |vec G st.2 i - Real.log (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
      (matrix G P.rows) (vec G st.1) i)| ≤ P.K := by
  have hB : Real.log (12 * rowCount G me * P.T / (1 / (2 * P.L) / 8)) / P.μ ≤ P.K := by
    refine le_trans (div_le_div_of_nonneg_right (Real.log_le_log ?_ ?_) H.μ_pos.le) H.window_le
    · have := H.rows_pos; have := H.T_ge; have := H.L_ge; positivity
    · have := H.M_le; have := H.T_ge; have := H.L_ge; gcongr
  exact (pot_coord_bound H.μ_pos hp i).trans hB

theorem weight_bounds_of_potential (H : Regime G P bc) {st : State E.n me}
    (hp : pot P.μ (vec G st.2 - fun i => Real.log
      (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G st.1) i)) ≤
      12 * rowCount G me * P.T / (1 / (2 * P.L) / 8)) :
    (∀ i, 1 / (4 * E.Mbar) ≤ exp (vec G st.2 i)) ∧
    (∀ i, exp (vec G st.2 i) ≤ 4) ∧ ∑ i, exp (vec G st.2 i) ≤ 4 * E.n := by
  apply weight_invariants (det_ne_zero_of_idRows (matrix_idRows G P.rows))
    (H.row_ne) H.L_ge (le_refl _) H.c₀_le H.M_le H.rank_ge
    (fun i => exp_pos _)
  intro i
  rw [Real.log_exp]
  exact (logWindow_of_potential H (st := st) hp i).trans (H.K_small.trans (by norm_num))

theorem mixedEnvelope_of_potential (H : Regime G P bc) {st : State E.n me}
    (hp : pot P.μ (vec G st.2 - fun i => Real.log
      (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G st.1) i)) ≤
      12 * rowCount G me * P.T / (1 / (2 * P.L) / 8)) (v : Fin (rowCount G me) → ℝ) :
    mixed P.C (fun i => exp (vec G st.2 i)) v ≤ P.T * ‖v‖ :=
  mixed_le_public H.C_pos.le (fun _i => (exp_pos _).le)
    (weight_bounds_of_potential H (st := st) hp).2.2 v

/-- One public batch, with the mixed-norm premise discharged from the input potential. -/
theorem batchProg_fail_public (H : Regime G P bc) {t : ℝ} {st : State E.n me}
    (ht : |t| ≤ 16 * E.n / E.ε) (hs : Invariant G P bc t st) :
    Probability.mass ((batchProg E P.rows P.a0 P.κ P.m P.c st.1 st.2 t P.L P.c₀ P.Δ P.T
      P.Kd P.J P.samples P.rounds).eval G.out)
      (fun o => ¬ BatchGood G P.rows bc (vec G P.κ) (vec G P.m) (vec G P.c)
        t P.L P.c₀ P.Δ P.T o) ≤
      d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) +
        batchJL E P.a0 P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) := by
  exact batchProg_fail G P.rows H.a0_pos H.a0_le H.row_norms rfl rfl rfl rfl rfl H.L_ge H.logM_le
    H.κ_pos (le_refl _) (le_refl _) H.U_ge H.width_le hs.feasible H.reference_feasible
    H.reference_slack H.M_le H.rank_ge H.ε_pos H.ε_le ht H.cost_le H.C_eq H.η_pos H.η_le
    H.Δ_pos H.Δ_le H.K_nonneg H.K_le H.T_ge (mixedEnvelope_of_potential H (st := st) hs.potential)
    H.window_le hs.potential hs.centrality H.Csym_nonneg H.sym_le H.vertices_le H.samples_pos

/-- After a successful batch, a licensed parameter move restores the complete invariant. -/
theorem batchGood_invariant (H : Regime G P bc) {t t' α : ℝ} {st : State E.n me}
    (hg : BatchGood G P.rows bc (vec G P.κ) (vec G P.m) (vec G P.c)
      t P.L P.c₀ P.Δ P.T (some st))
    (ht : 0 < t) (hα : |t' / t - 1| ≤ α)
    (hαT : α * P.T ≤ 1 / (2 * P.L) * P.Δ / 16)
    (hαΔ : α * P.Δ ≤ 1 / (2 * P.L) * P.Δ / 16) : Invariant G P bc t' st := by
  have hg' := hg
  obtain ⟨xn, Xn, heq, hF, hP, _⟩ := hg
  have he : (xn, Xn) = st := Option.some.inj heq.symm
  cases he
  refine ⟨hF, hP, ?_⟩
  exact batchGood_tchange G P.rows H.κ_pos H.L_ge hg' (by linarith [H.T_ge])
    (mixedEnvelope_of_potential H (st := (xn, Xn)) hP) ht hα hαT H.Δ_pos hαΔ

end
end CutQueryComplexity.ImplicitLP.GenericQuery

#print axioms CutQueryComplexity.ImplicitLP.GenericQuery.public_copy_eq
#print axioms CutQueryComplexity.ImplicitLP.GenericQuery.frozen_copy_eq
#print axioms CutQueryComplexity.ImplicitLP.GenericQuery.logWindow_of_potential
#print axioms CutQueryComplexity.ImplicitLP.GenericQuery.weight_bounds_of_potential
#print axioms CutQueryComplexity.ImplicitLP.GenericQuery.mixedEnvelope_of_potential
#print axioms CutQueryComplexity.ImplicitLP.GenericQuery.batchProg_fail_public
#print axioms CutQueryComplexity.ImplicitLP.GenericQuery.batchGood_invariant
