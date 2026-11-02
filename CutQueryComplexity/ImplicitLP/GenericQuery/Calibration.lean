import CutQueryComplexity.ImplicitLP.GenericQuery.Solver
import CutQueryComplexity.ImplicitLP.GenericQuery.Box

/-! # General input data determine the actual finite solver

The public geometry is chosen first, then the finite path and centering counts,
then direction precision and spectral failure allocation. Every internal
geometric condition is derived from original input data. The last remaining
asymptotic obligation is to simplify the literal query-tree budget.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Real Probability
open PathFollowing (calibratedDelta calibratedDelta_spec calibratedTolerance
  calibratedTolerance_spec d4Fail_numerical_parameters)
open scoped ENNReal
noncomputable section
variable {n me : ℕ}

def publicLogExponent (P : Envelope) : ℕ :=
  ⌈logb 2 (max 2 (logb 2 (2 * P.Mbar) + 1))⌉₊
def publicLogSize (P : Envelope) : ℝ := 2 ^ publicLogExponent P
def publicMixed (P : Envelope) : ℝ := 48 * (2 * publicLogSize P)
def publicEnvelope (n : ℕ) (P : Envelope) : ℝ := 1 + publicMixed P * sqrt (4 * n)
def publicDelta (n : ℕ) (P : Envelope) : ℝ :=
  calibratedDelta (publicLogSize P) P.Mbar (publicEnvelope n P)
def publicFinalCount (n : ℕ) (P : Envelope) : ℕ :=
  phaseSteps (publicDelta n P / (P.ε / (8 * P.Mbar * P.U ^ 2))) 1

def publicEnvironment (n : ℕ) (P : Envelope) : NewtonPub where
  n := n
  Mbar := P.Mbar
  U := P.U
  ε := P.ε
  C := publicMixed P
  η := calibratedTolerance (publicLogSize P) (publicDelta n P) (publicFinalCount n P)

def publicSkeleton (D : Data n me) (P : Envelope) : Params (publicEnvironment n P) me where
  rows := D.rows
  a0 := P.a0
  κ := kappaPt D
  m := midpointPt D
  c := D.cost
  L := publicLogSize P
  Δ := publicDelta n P
  K := 1 / (2 * publicLogSize P) / 2 ^ 20
  Kd := 0
  J := 0
  samples := 1
  rounds := 0

def publicCallCount (D : Data n me) (P : Envelope) : ℕ :=
  let Q := publicSkeleton D P
  solverSpectralCap Q Q.downSteps Q.upSteps Q.finalSteps
def publicCallFailure (D : Data n me) (P : Envelope) : ℝ :=
  P.ζ / (4 * ((publicCallCount D P : ℝ) + 1))

def calibratedParams (D : Data n me) (P : Envelope) : Params (publicEnvironment n P) me :=
  { publicSkeleton D P with
    Kd := Sparsify.pK n
    J := Sparsify.pJ n P.C (publicDelta n P / 4096) (publicCallFailure D P)
    samples := Sparsify.pt n P.C (publicDelta n P / 4096) (publicCallFailure D P)
    rounds := Sparsify.pR n (publicCallFailure D P) }

theorem publicLogSize_spec (P : Envelope) :
    2 ≤ publicLogSize P ∧ logb 2 (2 * P.Mbar) ≤ publicLogSize P - 1 := by
  have hmax : max 2 (logb 2 (2 * P.Mbar) + 1) ≤ publicLogSize P :=
    Sparsify.le_two_pow_ceil_logb (by norm_num : (1 : ℝ) < 2)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _))
  refine ⟨(le_max_left _ _).trans hmax, ?_⟩
  have := (le_max_right (2 : ℝ) (logb 2 (2 * P.Mbar) + 1)).trans hmax
  linarith

theorem publicDelta_spec (n : ℕ) (P : Envelope) :
    0 < publicDelta n P ∧ publicDelta n P ≤ (1 / (2 * publicLogSize P)) ^ 2 / 2 ^ 16 ∧
      publicDelta n P ≤ 1 := by
  have hL := (publicLogSize_spec P).1
  have hD := calibratedDelta_spec (M := P.Mbar) (T := publicEnvelope n P) hL
  have ha : 1 / (2 * publicLogSize P) ≤ (1 / 4 : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have ha0 : 0 ≤ 1 / (2 * publicLogSize P) := by positivity
  refine ⟨hD.1, hD.2.1, ?_⟩
  have hcap : publicDelta n P ≤ (1 / (2 * publicLogSize P)) ^ 2 / 2 ^ 16 := hD.2.1
  have hsq := mul_le_mul ha ha ha0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  nlinarith

theorem publicCallFailure_spec {D : Data n me} {P : Envelope} (H : PublicHyp D P) :
    0 < publicCallFailure D P ∧ publicCallFailure D P ≤ 1 / 2 ∧
      (publicCallCount D P : ℝ) * publicCallFailure D P ≤ P.ζ := by
  have hc : (0 : ℝ) ≤ publicCallCount D P := by positivity
  have hd : 0 < 4 * ((publicCallCount D P : ℝ) + 1) := by positivity
  refine ⟨div_pos H.ζ_pos hd, ?_, ?_⟩
  · change P.ζ / (4 * ((publicCallCount D P : ℝ) + 1)) ≤ 1 / 2
    rw [div_le_iff₀ hd]
    linarith [H.ζ_le]
  · change (publicCallCount D P : ℝ) * (P.ζ / (4 * ((publicCallCount D P : ℝ) + 1))) ≤ P.ζ
    rw [← mul_div_assoc, div_le_iff₀ hd]
    calc
      (publicCallCount D P : ℝ) * P.ζ ≤
          (4 * ((publicCallCount D P : ℝ) + 1)) * P.ζ :=
        mul_le_mul_of_nonneg_right (by linarith) H.ζ_pos.le
      _ = P.ζ * (4 * ((publicCallCount D P : ℝ) + 1)) := mul_comm _ _

/-- Construct all geometric hypotheses from the original data and honest graph. -/
def calibratedRegime {D : Data n me} {P : Envelope} (H : PublicHyp D P)
    {G : DiGraph (Fin n)} (HG : HonestInput G D P) :
    Regime G (calibratedParams D P) D.rhs := by
  have hL := publicLogSize_spec P
  have hD := calibratedDelta_spec (M := P.Mbar) (T := publicEnvelope n P) hL.1
  have hη := calibratedTolerance_spec hL.1 hD.1 (publicFinalCount n P)
  have hcall := publicCallFailure_spec H
  have hs := Sparsify.params_ok H.rank_ge H.C_ge
    (ε := publicDelta n P / 4096) (by have := (publicDelta_spec n P).1; positivity)
    (by linarith [(publicDelta_spec n P).2.2]) hcall.1 hcall.2.1
  refine {
    rank_pos := by change 0 < n; have := H.rank_ge; omega
    a0_pos := H.a0_pos
    a0_le := H.a0_le
    row_norms := H.row_norms
    L_ge := hL.1
    logM_le := hL.2
    κ_pos := kappa_pos H
    U_ge := by change 1 ≤ P.U; linarith [H.U_ge]
    width_le := barrier_width H
    reference := vec G D.initial
    reference_feasible := initial_feasible H HG
    reference_slack := initial_slack H HG
    M_le := original_row_count H HG
    ε_pos := H.ε_pos
    ε_le := H.ε_le
    cost_le := (cost_norm_le H).trans (by change P.U ≤ 4 * P.U; linarith [H.U_ge])
    C_eq := rfl
    η_pos := hη.1
    η_le := hη.2.1
    Δ_pos := hD.1
    Δ_le := hD.2.1
    K_nonneg := ?_
    K_le := le_rfl
    window_le := hD.2.2
    Csym := P.C
    Csym_nonneg := by linarith [H.C_ge]
    sym_le := ?_
    vertices_le := hs.1
    samples_pos := hs.2.1 }
  · change 0 ≤ 1 / (2 * publicLogSize P) / 2 ^ 20
    have := hL.1
    positivity
  · intro e
    induction e using Sym2.ind with
    | h u v =>
      change (G.sym u v : ℝ) ≤ P.C
      exact HG.multiplicity u v

theorem calibrated_finalTolerance (D : Data n me) (P : Envelope) :
    (publicEnvironment n P).η ≤ (1 / 2 : ℝ) ^ (calibratedParams D P).finalSteps *
      (calibratedParams D P).Δ / 64 :=
  (calibratedTolerance_spec (publicLogSize_spec P).1 (publicDelta_spec n P).1
    (publicFinalCount n P)).2.2

theorem calibrated_failure {D : Data n me} {P : Envelope} (H : PublicHyp D P)
    {G : DiGraph (Fin n)} (HG : HonestInput G D P) :
    let Q := calibratedParams D P
    (calibratedRegime H HG).solverFailure Q.downSteps Q.upSteps Q.finalSteps ≤ ENNReal.ofReal P.ζ := by
  intro Q
  let HR := calibratedRegime H HG
  have hcall := publicCallFailure_spec H
  have hs := d4Fail_numerical_parameters H.rank_ge H.C_ge
    (publicDelta_spec n P).1 (publicDelta_spec n P).2.2 hcall.1 hcall.2.1
  have hsolve : d4Fail (publicEnvironment n P).n HR.Csym Q.Kd Q.J Q.samples Q.rounds
      (solveDelta Q.rounds) ≤ ENNReal.ofReal (publicCallFailure D P) := hs.1
  have hlev : d4Fail (publicEnvironment n P).n HR.Csym Q.Kd Q.J Q.samples Q.rounds
      (levDelta Q.Δ Q.rounds) ≤ ENNReal.ofReal (publicCallFailure D P) := hs.2
  refine (solverFailure_of_per_call HR Q.downSteps Q.upSteps Q.finalSteps hsolve hlev).trans ?_
  change (publicCallCount D P : ℝ≥0∞) * ENNReal.ofReal (publicCallFailure D P) ≤ ENNReal.ofReal P.ζ
  calc _ = ENNReal.ofReal ((publicCallCount D P : ℝ) * publicCallFailure D P) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hcall.2.2

/-- Public finite budget, fixed before an oracle is supplied. -/
def queryCap (D : Data n me) (P : Envelope) : ℕ :=
  let Q := calibratedParams D P
  Q.solverBudget Q.downSteps Q.upSteps Q.finalSteps

def solve (D : Data n me) (P : Envelope) :
    RTree (Finset (Fin n)) ℕ (Option (Point n me)) (queryCap D P) :=
  let Q := calibratedParams D P
  pathSolver Q D.initial (initialPhase Q) Q.downSteps (truePhase Q) Q.upSteps Q.finalSteps

def Solved (G : DiGraph (Fin n)) (D : Data n me) (ε : ℝ) (out : Option (Point n me)) : Prop :=
  ∃ y, out = some y ∧ ClosedFeasible G D (vec G y) ∧
    ∀ v, ClosedFeasible G D v → vec G D.cost ⬝ᵥ vec G y ≤ vec G D.cost ⬝ᵥ v + ε

/-- The initial barrier floor follows from the original reciprocal-slack promise. -/
theorem initial_numerical_floor {D : Data n me} {P : Envelope} (H : PublicHyp D P)
    {G : DiGraph (Fin n)} (HG : HonestInput G D P) :
    ∀ i, (publicEnvironment n P).sst ≤
      slk (vec G (kappaPt D)) (vec G (midpointPt D)) (vec G D.initial) i := by
  have HR := calibratedRegime H HG
  have hn : (1 : ℝ) ≤ n := HR.rank_ge
  have hm : (1 : ℝ) ≤ P.Mbar := by
    have hm' : (1 : ℝ) ≤ rowCount G me := by
      exact_mod_cast Fin.pos (iota G D.rows ⟨0, by have := H.rank_ge; omega⟩)
    exact hm'.trans (original_row_count H HG)
  have hu : 1 ≤ P.U := by linarith [H.U_ge]
  have hu0 : 0 < P.U := by linarith
  have hd : 1 ≤ (2 : ℝ) ^ 12 * n * P.Mbar ^ 2 * P.U ^ 2 := by
    calc (1 : ℝ) = 1 * 1 * 1 ^ 2 * 1 ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ 12 * n * P.Mbar ^ 2 * P.U ^ 2 := by gcongr <;> norm_num
  have he : (publicEnvironment n P).sst =
      (P.ε / (2 ^ 12 * n * P.Mbar ^ 2 * P.U ^ 2)) / P.U := by
    unfold NewtonPub.sst publicEnvironment
    ring
  intro i
  refine le_trans ?_ (initial_slack H HG i)
  rw [he]
  exact div_le_div_of_nonneg_right ((div_le_self H.ε_pos.le hd).trans H.ε_le) hu0.le

/-- One success event gives exact feasibility and epsilon error against every comparator. -/
theorem solve_failure {D : Data n me} {P : Envelope} (H : PublicHyp D P)
    {G : DiGraph (Fin n)} (HG : HonestInput G D P) :
    mass ((solve D P).eval G.out) (fun out => ¬Solved G D P.ε out) ≤ ENNReal.ofReal P.ζ := by
  let Q := calibratedParams D P
  let HR := calibratedRegime H HG
  have hf := pathSolver_failure HR D.initial (initial_feasible H HG)
    (initial_numerical_floor H HG) (initial_slack H HG)
    (initialPhase_licensed HR) (initialPhase_starts Q) (truePhase_licensed HR).1
    Q.downSteps Q.upSteps Q.finalSteps (truePhase_joins Q) (initialPhase_switch HR)
    (calibrated_finalTolerance D P)
  refine (mass_mono _ (fun out hbad hgood => ?_)).trans (hf.trans (calibrated_failure H HG))
  obtain ⟨y, rfl, hy, hgap⟩ := hgood
  apply hbad
  refine ⟨y, rfl, ⟨hy.1, (box_closed_iff H _).mp (fun i => (hy.2 i).le)⟩, ?_⟩
  intro v hv
  have hb := hgap v hv.1 ((box_closed_iff H v).mpr hv.2)
  have hcost := objective_l1 H HG
  have hfactor : 0 ≤ 4 * P.U * ((1 / 2 : ℝ) ^ Q.finalSteps * Q.Δ) := by
    have := H.U_ge
    have := HR.Δ_pos
    positivity
  have htotal := public_final_accuracy HR
  have hcompare := mul_le_mul_of_nonneg_right hcost hfactor
  change vec G D.cost ⬝ᵥ vec G y - vec G D.cost ⬝ᵥ v ≤
    4 * n / truePhase Q Q.upSteps +
      (∑ i, |vec G D.cost i|) * (4 * P.U * ((1 / 2 : ℝ) ^ Q.finalSteps * Q.Δ)) at hb
  change 4 * n / truePhase Q Q.upSteps + (P.Mbar * P.U) *
    (4 * P.U * ((1 / 2 : ℝ) ^ Q.finalSteps * Q.Δ)) ≤ P.ε at htotal
  linarith

theorem solve_success {D : Data n me} {P : Envelope} (H : PublicHyp D P)
    {G : DiGraph (Fin n)} (HG : HonestInput G D P) :
    1 - P.ζ ≤ (solve D P).successProb G.out (Solved G D P.ε) := by
  erw [RTree.successProb_eq]
  exact success_of_failure_le _ _ H.ζ_pos.le (solve_failure H HG)

/-- This literal cap holds for arbitrary replies and every abort branch. -/
theorem solve_cost (D : Data n me) (P : Envelope) (read : Finset (Fin n) → ℕ)
    {out : Option (Point n me) × ℕ} (ho : out ∈ (RTree.run read (solve D P)).support) :
    out.2 ≤ queryCap D P := RTree.cost_le _ _ ho

#print axioms calibratedRegime
#print axioms calibrated_failure
#print axioms initial_numerical_floor
#print axioms solve_failure
#print axioms solve_success
#print axioms solve_cost

end
end CutQueryComplexity.ImplicitLP.GenericQuery
