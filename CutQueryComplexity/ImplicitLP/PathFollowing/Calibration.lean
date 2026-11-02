import CutQueryComplexity.ImplicitLP.PathFollowing.Main

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! # Concrete public parameters for the finite terminal solver

Geometry, final centering count, direction tolerance, and spectral failure allocation
are chosen in that order. None of these choices depends on a hidden graph or a run
output. The query cap is the literal finite cap of the composed program; simplifying
it to the advertised asymptotic bound is a separate obligation.
-/

namespace CutQueryComplexity.ImplicitLP.PathFollowing

open Real Probability
open scoped ENNReal
noncomputable section

def publicRows (n : ℕ) : ℝ := 2 * (n : ℝ) ^ 2 + 2 * n + 1
def publicWidth (n : ℕ) : ℝ := 4 * n
def publicLogExponent (n : ℕ) : ℕ := ⌈Real.logb 2 (max 2 (Real.logb 2 (2 * publicRows n) + 1))⌉₊
/-- Taking a power of two also makes the public chase multiplier dyadic. -/
def publicLogSize (n : ℕ) : ℝ := 2 ^ publicLogExponent n
def publicMixed (n : ℕ) : ℝ := 48 * (2 * publicLogSize n)
def publicEnvelope (n : ℕ) : ℝ := 1 + publicMixed n * Real.sqrt (4 * n)
def publicDelta (n : ℕ) : ℝ := calibratedDelta (publicLogSize n) (publicRows n) (publicEnvelope n)
def publicExtractionScale (n : ℕ) : ℝ := 1 / (8 * (n : ℝ) ^ 2)
def publicAccuracy (n : ℕ) : ℝ := publicExtractionScale n / 16
def publicFinalCount (n : ℕ) : ℕ :=
  phaseSteps (publicDelta n / (publicAccuracy n / (8 * publicWidth n * (2 * n + 1 / 2)))) 1

/-- The direction precision is chosen after the final count, which does not use it. -/
def publicEnvironment (n : ℕ) : NewtonPub where
  n := n
  Mbar := publicRows n
  U := publicWidth n
  ε := publicAccuracy n
  C := publicMixed n
  η := calibratedTolerance (publicLogSize n) (publicDelta n) (publicFinalCount n)

/-- This skeleton is used only to calculate counts; its spectral fields are then replaced. -/
def publicSkeleton (n : ℕ) (s t : Fin n) : Params (publicEnvironment n) where
  s := s
  terminal := t
  κ := terminalKappa n
  m := terminalMid n
  c := terminalCost n
  L := publicLogSize n
  Δ := publicDelta n
  K := 1 / (2 * publicLogSize n) / 2 ^ 20
  Kd := 0
  J := 0
  samples := 1
  rounds := 0

def publicCallCount (n : ℕ) (s t : Fin n) : ℕ :=
  let P := publicSkeleton n s t
  solverSpectralCap P P.downSteps P.upSteps P.finalSteps

def publicCallFailure (n : ℕ) (s t : Fin n) (ζ : ℝ) : ℝ :=
  ζ / (4 * ((publicCallCount n s t : ℝ) + 1))

/-- One public spectral parameter set is used by every Newton and Lewis call. -/
def calibratedParams (n : ℕ) (s t : Fin n) (ζ : ℝ) : Params (publicEnvironment n) :=
  { publicSkeleton n s t with
    Kd := Sparsify.pK n
    J := Sparsify.pJ n 2 (publicDelta n / 4096) (publicCallFailure n s t ζ)
    samples := Sparsify.pt n 2 (publicDelta n / 4096) (publicCallFailure n s t ζ)
    rounds := Sparsify.pR n (publicCallFailure n s t ζ) }

theorem publicLogSize_spec (n : ℕ) :
    2 ≤ publicLogSize n ∧ Real.logb 2 (2 * publicRows n) ≤ publicLogSize n - 1 := by
  have hmax : max 2 (Real.logb 2 (2 * publicRows n) + 1) ≤ publicLogSize n :=
    Sparsify.le_two_pow_ceil_logb (by norm_num : (1 : ℝ) < 2)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _))
  refine ⟨(le_max_left _ _).trans hmax, ?_⟩
  have := (le_max_right (2 : ℝ) (Real.logb 2 (2 * publicRows n) + 1)).trans hmax
  linarith

/-- The scale used by the existing weight-chasing update has one fixed dyadic denominator. -/
theorem publicChaseMultiplier_grid (n : ℕ) :
    ∃ k : ℤ, 1 + 1 / (2 * publicLogSize n) / 8 =
      k / (2 : ℝ) ^ (publicLogExponent n + 4) := by
  refine ⟨(2 : ℤ) ^ (publicLogExponent n + 4) + 1, ?_⟩
  push_cast
  simp only [publicLogSize, pow_add]
  norm_num
  field_simp
  ring

/-- Subtracting a certified dyadic support direction keeps the fixed sum grid. -/
theorem dyadic_chase_preserves {p q : ℕ} {x v a : ℝ}
    (hx : ∃ k : ℤ, x = k / (2 : ℝ) ^ (p + q))
    (hv : ∃ k : ℤ, v = k / (2 : ℝ) ^ p)
    (ha : ∃ k : ℤ, a = k / (2 : ℝ) ^ q) :
    ∃ k : ℤ, x - a * v = k / (2 : ℝ) ^ (p + q) := by
  obtain ⟨kx, rfl⟩ := hx
  obtain ⟨kv, rfl⟩ := hv
  obtain ⟨ka, rfl⟩ := ha
  refine ⟨kx - ka * kv, ?_⟩
  push_cast
  simp only [pow_add]
  field_simp

theorem calibratedChase_grid {n : ℕ} (G : DiGraph (Fin n)) (X v : DirectedMincut.LPPoint (Fin n))
    (p : ℕ)
    (hX : ∀ i, ∃ k : ℤ, lpVec G X i = k / (2 : ℝ) ^ (p + (publicLogExponent n + 4)))
    (hv : ∀ i, ∃ k : ℤ, lpVec G v i = k / (2 : ℝ) ^ p) :
    ∀ i, ∃ k : ℤ,
      lpVec G (chasePt (1 / (2 * publicLogSize n) / 8) X v) i =
        k / (2 : ℝ) ^ (p + (publicLogExponent n + 4)) := by
  intro i
  rw [lpVec_chasePt]
  exact dyadic_chase_preserves (hX i) (hv i) (publicChaseMultiplier_grid n)

/-- Certified support rounding puts every actual-row coordinate on its public grid,
including when the preceding numerical inputs are outside the successful envelope. -/
theorem roundedSupportPoint_grid {n : ℕ} (G : DiGraph (Fin n))
    (C Cs ρ : ℝ) (p : ℕ) (scalars : ℝ × ℝ × ℝ)
    (q w : DirectedMincut.LPPoint (Fin n)) (i : Fin (lpM G)) :
    ∃ k : ℤ, lpVec G (roundPt C Cs ρ p scalars q w) i = k / (2 : ℝ) ^ p := by
  rw [lpVec_roundPt]
  exact (truncDyadic_props p _).2.2.2

theorem batchSupport_grid {E : NewtonPub} (G : DiGraph (Fin E.n)) (P : Params E)
    (X z : DirectedMincut.LPPoint (Fin E.n)) (i : Fin (lpM G)) :
    ∃ k : ℤ, lpVec G ((batchSupProg E.Mbar P.L P.c₀ P.Δ P.T X z).eval G.out).2 i =
      k / (2 : ℝ) ^ (batchSup E.Mbar P.L P.c₀ P.Δ P.T).po := by
  rw [batchSupProg, supportPubProg, DTree.eval_map]
  exact roundedSupportPoint_grid G _ _ _ _ _ _ _ i

theorem publicDelta_spec (n : ℕ) :
    0 < publicDelta n ∧ publicDelta n ≤ (1 / (2 * publicLogSize n)) ^ 2 / 2 ^ 16 ∧
      publicDelta n ≤ 1 := by
  have hL := (publicLogSize_spec n).1
  have hD := calibratedDelta_spec (M := publicRows n) (T := publicEnvelope n) hL
  have ha : 1 / (2 * publicLogSize n) ≤ (1 / 4 : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have ha0 : 0 ≤ 1 / (2 * publicLogSize n) := by positivity
  refine ⟨hD.1, hD.2.1, ?_⟩
  have hcap : publicDelta n ≤ (1 / (2 * publicLogSize n)) ^ 2 / 2 ^ 16 := hD.2.1
  have hsq := mul_le_mul ha ha ha0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  nlinarith

theorem publicExtractionScale_spec {n : ℕ} (hn : 2 ≤ n) :
    0 < publicExtractionScale n ∧ publicExtractionScale n ≤ 1 ∧
      8 * (n : ℝ) ^ 2 * publicExtractionScale n ≤ 1 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < 8 * (n : ℝ) ^ 2 := by positivity
  refine ⟨by unfold publicExtractionScale; positivity, ?_, ?_⟩
  · rw [publicExtractionScale, div_le_one hd]
    nlinarith
  · unfold publicExtractionScale
    rw [mul_one_div_cancel hd.ne']

theorem publicCallFailure_spec {n : ℕ} (s t : Fin n) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    0 < publicCallFailure n s t ζ ∧ publicCallFailure n s t ζ ≤ 1 / 2 ∧
      (publicCallCount n s t : ℝ) * publicCallFailure n s t ζ ≤ ζ := by
  have hcount : (0 : ℝ) ≤ publicCallCount n s t := by positivity
  have hden : 0 < 4 * ((publicCallCount n s t : ℝ) + 1) := by positivity
  refine ⟨div_pos hζ hden, ?_, ?_⟩
  · change ζ / (4 * ((publicCallCount n s t : ℝ) + 1)) ≤ 1 / 2
    rw [div_le_iff₀ hden]
    linarith
  · change (publicCallCount n s t : ℝ) * (ζ / (4 * ((publicCallCount n s t : ℝ) + 1))) ≤ ζ
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith [mul_nonneg hcount hζ.le]

/-- Every static license field follows from the chosen public numbers. -/
theorem calibratedParams_license {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) : PublicLicense (calibratedParams n s t ζ) := by
  have hL := publicLogSize_spec n
  have hD := calibratedDelta_spec (M := publicRows n) (T := publicEnvelope n) hL.1
  have hη := calibratedTolerance_spec hL.1 hD.1 (publicFinalCount n)
  have hθ := publicExtractionScale_spec hn
  have hcall := publicCallFailure_spec s t hζ hζ1
  have hspec := Sparsify.params_ok hn (C := 2) (by norm_num)
    (ε := publicDelta n / 4096) (by have := (publicDelta_spec n).1; positivity)
    (by linarith [(publicDelta_spec n).2.2]) hcall.1 hcall.2.1
  refine {
    vertices := hn
    distinct := hst
    kappa := rfl
    midpoint := rfl
    cost := rfl
    L_ge := hL.1
    logM_le := hL.2
    width := le_rfl
    rows := le_rfl
    ε_pos := ?_
    ε_le := ?_
    C_eq := rfl
    η_pos := hη.1
    η_le := hη.2.1
    Δ_pos := hD.1
    Δ_le := hD.2.1
    K_nonneg := ?_
    K_le := le_rfl
    window_le := hD.2.2
    vertices_le := hspec.1
    samples_pos := hspec.2.1 }
  · change 0 < publicExtractionScale n / 16
    exact div_pos hθ.1 (by norm_num)
  · change publicExtractionScale n / 16 ≤ 1
    linarith [hθ.2.1]
  · change 0 ≤ 1 / (2 * publicLogSize n) / 2 ^ 20
    have := hL.1
    positivity

theorem calibratedParams_finalTolerance (n : ℕ) (s t : Fin n) (ζ : ℝ) :
    (publicEnvironment n).η ≤ (1 / 2 : ℝ) ^ (calibratedParams n s t ζ).finalSteps *
      (calibratedParams n s t ζ).Δ / 64 :=
  (calibratedTolerance_spec (publicLogSize_spec n).1 (publicDelta_spec n).1 (publicFinalCount n)).2.2

/-- The complete adaptive spectral failure sum is discharged by the explicit allocation. -/
theorem calibratedParams_failure {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (G : DiGraph (Fin n)) (hG : G.Simple) :
    let P := calibratedParams n s t ζ
    let H := (calibratedParams_license hn s t hst hζ hζ1).regime G hG
    H.solverFailure P.downSteps P.upSteps P.finalSteps ≤ ENNReal.ofReal ζ := by
  intro P H
  have hcall := publicCallFailure_spec s t hζ hζ1
  have hspec := d4Fail_numerical_parameters hn (Cs := 2) (by norm_num)
    (publicDelta_spec n).1 (publicDelta_spec n).2.2 hcall.1 hcall.2.1
  have hsolve : d4Fail (publicEnvironment n).n H.Csym P.Kd P.J P.samples P.rounds
      (solveDelta P.rounds) ≤ ENNReal.ofReal (publicCallFailure n s t ζ) := hspec.1
  have hlev : d4Fail (publicEnvironment n).n H.Csym P.Kd P.J P.samples P.rounds
      (levDelta P.Δ P.rounds) ≤ ENNReal.ofReal (publicCallFailure n s t ζ) := hspec.2
  refine (solverFailure_of_per_call H P.downSteps P.upSteps P.finalSteps hsolve hlev).trans ?_
  change (publicCallCount n s t : ℝ≥0∞) * ENNReal.ofReal (publicCallFailure n s t ζ) ≤
    ENNReal.ofReal ζ
  calc _ = ENNReal.ofReal ((publicCallCount n s t : ℝ) * publicCallFailure n s t ζ) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hcall.2.2

/-- A public finite query solver with no licensing argument in its interface. -/
def calibratedTerminalSolver (n : ℕ) (s t : Fin n) (ζ : ℝ) :=
  publicTerminalSolver (calibratedParams n s t ζ) (Sparsify.pK n) (publicExtractionScale n)

theorem calibratedTerminalSolver_failure {n : ℕ} (hn : 2 ≤ n)
    (s t : Fin n) (hst : s ≠ t) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (G : DiGraph (Fin n)) (hG : G.Simple) :
    mass ((calibratedTerminalSolver n s t ζ).eval G.out)
      (fun out => ¬DirectedMincut.STGood s t G out) ≤ ENNReal.ofReal ζ := by
  let P := calibratedParams n s t ζ
  let Q : PublicLicense P := calibratedParams_license hn s t hst hζ hζ1
  let H := Q.regime G hG
  have hθ := publicExtractionScale_spec hn
  exact (publicTerminalSolver_failure H hG rfl rfl rfl
    (calibratedParams_finalTolerance n s t ζ) (Sparsify.pK n) Q.vertices_le
    hθ.1 hθ.2.2 (le_refl _)).trans (calibratedParams_failure hn s t hst hζ hζ1 G hG)

theorem calibratedTerminalSolver_success {n : ℕ} (hn : 2 ≤ n)
    (s t : Fin n) (hst : s ≠ t) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (G : DiGraph (Fin n)) (hG : G.Simple) :
    1 - ζ ≤ (calibratedTerminalSolver n s t ζ).successProb G.out (DirectedMincut.STGood s t G) := by
  erw [RTree.successProb_eq]
  exact success_of_failure_le _ _ hζ.le (calibratedTerminalSolver_failure hn s t hst hζ hζ1 G hG)

theorem calibratedTerminalSolver_cost (n : ℕ) (s t : Fin n) (ζ : ℝ) (G : DiGraph (Fin n))
    {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run G.out (calibratedTerminalSolver n s t ζ)).support) :
    let P := calibratedParams n s t ζ
    out.2 ≤ (2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
      (2 * n * (3 + 3 * Sparsify.pK n) + 1) := RTree.cost_le _ _ ho

/-- Canonical terminals are used only to license a family containing every terminal pair. -/
def calibratedGlobalParams (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) : Params (publicEnvironment n) :=
  calibratedParams n ⟨0, by omega⟩ ⟨1, by omega⟩ ζ

def calibratedGlobalSolver (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) (h K : ℕ) :=
  publicGlobalSolver (calibratedGlobalParams n hn ζ) (Sparsify.pK n) h K (publicExtractionScale n)

/-- The actual global reduction instantiated with the fully calibrated terminal program. -/
theorem calibratedGlobalSolver_success {n : ℕ} (hn : 2 ≤ n) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (G : DiGraph (Fin n)) (hG : G.Simple)
    (h K : ℕ) (hh : h ≤ n) :
    1 - ((1 - (h : ℝ) / n) ^ K + ζ) ≤
      (calibratedGlobalSolver n hn ζ h K).successProb G.out (DirectedMincut.Opt G) := by
  let s : Fin n := ⟨0, by omega⟩
  let t : Fin n := ⟨1, by omega⟩
  have hst : s ≠ t := by intro he; have := congrArg Fin.val he; simp [s, t] at this
  let Q := calibratedParams_license hn s t hst hζ hζ1
  let H := Q.regime G hG
  have hθ := publicExtractionScale_spec hn
  exact publicGlobalSolver_success H hG rfl rfl rfl (calibratedParams_finalTolerance n s t ζ)
    hn (Sparsify.pK n) Q.vertices_le hθ.1 hθ.2.2 (le_refl _)
    (calibratedParams_failure hn s t hst hζ hζ1 G hG) hζ.le h K hh

theorem calibratedGlobalSolver_cost (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) (h K : ℕ)
    (G : DiGraph (Fin n)) {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run G.out (calibratedGlobalSolver n hn ζ h K)).support) :
    let P := calibratedGlobalParams n hn ζ
    out.2 ≤ 2 * n +
      (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) +
        (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) + 1)) +
      2 * K * ((2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
        (2 * n * (3 + 3 * Sparsify.pK n) + 1)) := by
  exact publicGlobalSolver_cost G (calibratedGlobalParams n hn ζ)
    (Sparsify.pK n) h K (publicExtractionScale n) ho

/-- Enough public roots to give the global reduction failure at most `ζ/2`. -/
def publicRootCount (n h : ℕ) (ζ : ℝ) : ℕ := ⌈(n : ℝ) / h * Real.log (2 / ζ)⌉₊

theorem publicRootCount_spec {n h : ℕ} (hn : 0 < n) (hh : 0 < h) (hhn : h ≤ n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (1 - (h : ℝ) / n) ^ publicRootCount n h ζ ≤ ζ / 2 ∧
      (publicRootCount n h ζ : ℝ) ≤ (n : ℝ) / h * Real.log (2 / ζ) + 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hx : (h : ℝ) / n ≤ 1 := by rw [div_le_one hn']; exact_mod_cast hhn
  have hx0 : 0 < (h : ℝ) / n := div_pos hh' hn'
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - (h : ℝ) / n)
    (Real.one_sub_le_exp_neg ((h : ℝ) / n)) (publicRootCount n h ζ)
  rw [← Real.exp_nat_mul] at hp
  have hceil : (n : ℝ) / h * Real.log (2 / ζ) ≤ publicRootCount n h ζ := Nat.le_ceil _
  have he : ((n : ℝ) / h * Real.log (2 / ζ)) * ((h : ℝ) / n) = Real.log (2 / ζ) := by
    field_simp [hn'.ne', hh'.ne']
  have hlog : Real.log (2 / ζ) ≤ (publicRootCount n h ζ : ℝ) * ((h : ℝ) / n) := by
    rw [← he]
    exact mul_le_mul_of_nonneg_right hceil hx0.le
  constructor
  · refine hp.trans ?_
    calc Real.exp ((publicRootCount n h ζ : ℝ) * -((h : ℝ) / n)) ≤
          Real.exp (-Real.log (2 / ζ)) := Real.exp_le_exp.mpr (by linarith)
      _ = ζ / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 / ζ)]
        simp only [inv_div]
  · have hlog0 : 0 ≤ Real.log (2 / ζ) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hζ]
      linarith
    exact (Nat.ceil_lt_add_one (mul_nonneg (div_nonneg hn'.le hh'.le) hlog0)).le

/-- A fully specified global query program, apart from the public shore-size tradeoff `h`. -/
def calibratedGlobalMinCut (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) (h : ℕ) :=
  calibratedGlobalSolver n hn (ζ / 2) h (publicRootCount n h ζ)

theorem calibratedGlobalMinCut_success {n : ℕ} (hn : 2 ≤ n) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (G : DiGraph (Fin n)) (hG : G.Simple)
    (h : ℕ) (hh : 0 < h) (hhn : h ≤ n) :
    1 - ζ ≤ (calibratedGlobalMinCut n hn ζ h).successProb G.out (DirectedMincut.Opt G) := by
  have hmiss := (publicRootCount_spec (by omega : 0 < n) hh hhn hζ hζ1).1
  have hsucc := calibratedGlobalSolver_success hn (ζ := ζ / 2) (by positivity) (by linarith)
    G hG h (publicRootCount n h ζ) hhn
  exact (show 1 - ζ ≤ 1 - ((1 - (h : ℝ) / n) ^ publicRootCount n h ζ + ζ / 2) by linarith).trans hsucc

theorem calibratedGlobalMinCut_cost (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) (h : ℕ)
    (G : DiGraph (Fin n)) {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run G.out (calibratedGlobalMinCut n hn ζ h)).support) :
    let P := calibratedGlobalParams n hn (ζ / 2)
    out.2 ≤ 2 * n +
      (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) +
        (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) + 1)) +
      2 * publicRootCount n h ζ * ((2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
        (2 * n * (3 + 3 * Sparsify.pK n) + 1)) :=
  calibratedGlobalSolver_cost n hn (ζ / 2) h (publicRootCount n h ζ) G ho

/-- The terminal cap holds for every answer oracle, independently of graph promises. -/
theorem calibratedTerminalSolver_cost_all_oracles (n : ℕ) (s t : Fin n) (ζ : ℝ)
    (read : Finset (Fin n) → ℕ) {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run read (calibratedTerminalSolver n s t ζ)).support) :
    let P := calibratedParams n s t ζ
    out.2 ≤ (2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
      (2 * n * (3 + 3 * Sparsify.pK n) + 1) := RTree.cost_le _ _ ho

/-- The fully calibrated global cap also holds for every answer oracle. -/
theorem calibratedGlobalMinCut_cost_all_oracles (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) (h : ℕ)
    (read : Finset (Fin n) → ℕ) {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run read (calibratedGlobalMinCut n hn ζ h)).support) :
    let P := calibratedGlobalParams n hn (ζ / 2)
    out.2 ≤ 2 * n +
      (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) +
        (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) + 1)) +
      2 * publicRootCount n h ζ * ((2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
        (2 * n * (3 + 3 * Sparsify.pK n) + 1)) := by
  intro P
  have hc : out.2 ≤ 2 * Fintype.card (Fin n) +
      (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) +
        (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) + 1)) +
      2 * publicRootCount n h ζ * ((2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
        (2 * n * (3 + 3 * Sparsify.pK n) + 1)) := RTree.cost_le _ _ ho
  simpa only [Fintype.card_fin] using hc

end
end CutQueryComplexity.ImplicitLP.PathFollowing

#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicDelta_spec
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicChaseMultiplier_grid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedChase_grid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.batchSupport_grid
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicExtractionScale_spec
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicCallFailure_spec
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedParams_license
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedParams_finalTolerance
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedParams_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_success
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalSolver_success
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalSolver_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.publicRootCount_spec
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalMinCut_success
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalMinCut_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_cost_all_oracles
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalMinCut_cost_all_oracles
