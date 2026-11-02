import CutQueryComplexity.StarContraction2022.Randomized.HighDegree
import CutQueryComplexity.StarContraction2022.Certificates.Parallel
import CutQueryComplexity.StarContraction2022.Certificates.SmallQuotient
import CutQueryComplexity.Primitive.Learn
import Mathlib.Data.Fintype.Lattice

/-! # One actual uniform linear-query attempt

Every constructor uses public dimensions and the observed transcript. Small
original inputs are learned exactly; large inputs use the actual capped
certificate or contraction programs. All candidate values are original-cut
queries. In particular an internal failed solver cannot create an underestimate.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Randomized

noncomputable section
open scoped Classical ENNReal
open CutQueryComplexity.Probability CutQueryComplexity.StarContraction2022.Contraction

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]

/-- These are the coefficients of the actual implementations, not parameters
supplied by a caller as cost or success assumptions. -/
def attemptCoefficient : ℕ :=
  Schedule.attemptCoefficient Recovery.bucketConstant Certificates.parallelZeroErrorConstant

private def tailCoefficientFor (a u h p d w : ℕ) : ℕ :=
  3 * a + 9 + 5000 * u + 2 * h * u +
    100 * (p * d + 1) + 100 * (160001 * p + 1) + 12 + w

private theorem coefficient_model (CB CP u : ℕ)
    (hu : Schedule.recoveryCoefficient CB = u) :
    Schedule.attemptCoefficient CB CP = 1 +
      tailCoefficientFor Schedule.sizeCutoff u Schedule.insideCoefficient CP
        Schedule.degreeCutoff Schedule.weightedCoefficient := by
  subst u
  unfold Schedule.attemptCoefficient tailCoefficientFor
  omega

def tailCoefficient : ℕ :=
  tailCoefficientFor Schedule.sizeCutoff Recovery.recoveryHardCoefficient
    Schedule.insideCoefficient Certificates.parallelZeroErrorConstant
    Schedule.degreeCutoff Schedule.weightedCoefficient

private theorem tail_alias : tailCoefficient =
  tailCoefficientFor Schedule.sizeCutoff Recovery.recoveryHardCoefficient
    Schedule.insideCoefficient Certificates.parallelZeroErrorConstant
    Schedule.degreeCutoff Schedule.weightedCoefficient := rfl

private theorem attempt_instantiate :
    Schedule.attemptCoefficient Recovery.bucketConstant Certificates.parallelZeroErrorConstant =
      1 + tailCoefficientFor Schedule.sizeCutoff Recovery.recoveryHardCoefficient
        Schedule.insideCoefficient Certificates.parallelZeroErrorConstant
        Schedule.degreeCutoff Schedule.weightedCoefficient :=
  coefficient_model Recovery.bucketConstant Certificates.parallelZeroErrorConstant
    Recovery.recoveryHardCoefficient Contraction.Joint.recoveryHardCoefficient_schedule.symm

private theorem attempt_alias : attemptCoefficient =
    Schedule.attemptCoefficient Recovery.bucketConstant Certificates.parallelZeroErrorConstant := rfl

theorem attemptCoefficient_eq : attemptCoefficient = 1 + tailCoefficient :=
  attempt_alias.trans (attempt_instantiate.trans
    (congrArg (fun t : ℕ => 1 + t) tail_alias.symm))


private theorem coefficient_bounds (a u h p d w : ℕ) :
    let c := tailCoefficientFor a u h p d w
    (100 * (p * d + 1) + 1 ≤ c) ∧
    (3 + 5000 * u + w + 1 ≤ c) ∧
    (6 + 2 * h * u + 5000 * u + (100 * (160001 * p + 1) + 12) + 1 ≤ c) ∧
    (3 * a ≤ c) := by
  dsimp only [tailCoefficientFor]
  omega

private theorem high_budget_factor (n u w : ℕ) :
    3 * n + u * 5000 * n + (w * n + 1) =
      (3 + 5000 * u + w) * n + 1 := by ring

private theorem middle_budget_factor (n u h p : ℕ) :
    3 * n + (3 * n + 2 * u * h * n + u * 5000 * n) +
      ((100 * (160001 * p + 1) + 12) * n + 1) =
        (6 + 2 * h * u + 5000 * u + (100 * (160001 * p + 1) + 12)) * n + 1 := by ring

def smallDegreeBudget (n : ℕ) : ℕ :=
  100 * (Certificates.parallelZeroErrorConstant * Schedule.degreeCutoff + 1) * n + 1

def middleSolveBudget (n : ℕ) : ℕ :=
  (100 * (160001 * Certificates.parallelZeroErrorConstant + 1) + 12) * n + 1

def middleBudget (n : ℕ) : ℕ := Uniform.middleBudget n + middleSolveBudget n

def reconstructionBudget (n : ℕ) : ℕ := n + n.choose 2 + 1

/-- Total public adaptation to a common branch index. The index comparison
uses no oracle and rejection costs no queries. -/
def fit {b : ℕ} (limit : ℕ) (T : RTree (Finset V) ℝ (Option (CutResult V)) b) :
    RTree (Finset V) ℝ (Option (CutResult V)) limit :=
  if h : b ≤ limit then T.weaken h else RTree.pure (PMF.pure none)

theorem fit_eval {b : ℕ} (limit : ℕ)
    (T : RTree (Finset V) ℝ (Option (CutResult V)) b) (h : b ≤ limit)
    (read : Finset V → ℝ) : (fit limit T).eval read = T.eval read := by
  simp only [fit, dif_pos h, RTree.eval_weaken]

theorem fit_sound {b : ℕ} (limit : ℕ)
    (T : RTree (Finset V) ℝ (Option (CutResult V)) b) (G : WeightedGraph V)
    (hs : ∀ out, some out ∈ (T.eval G.cut).support → out.Sound G)
    {out : CutResult V} (hout : some out ∈ ((fit limit T).eval G.cut).support) :
    out.Sound G := by
  unfold fit at hout
  split_ifs at hout with hb
  · exact hs out (by simpa only [RTree.eval_weaken] using hout)
  · simp at hout

theorem branch_budgets (n : ℕ) (hn : 1 ≤ n) :
    smallDegreeBudget n ≤ tailCoefficient * n ∧
    highBudget n ≤ tailCoefficient * n ∧
    middleBudget n ≤ tailCoefficient * n := by
  obtain ⟨hs, hh, hm, _⟩ := coefficient_bounds Schedule.sizeCutoff
    Recovery.recoveryHardCoefficient Schedule.insideCoefficient
    Certificates.parallelZeroErrorConstant Schedule.degreeCutoff Schedule.weightedCoefficient
  refine ⟨?_, ?_, ?_⟩
  · calc
      smallDegreeBudget n ≤
          100 * (Certificates.parallelZeroErrorConstant * Schedule.degreeCutoff + 1) * n + n :=
        Nat.add_le_add_left hn _
      _ = (100 * (Certificates.parallelZeroErrorConstant * Schedule.degreeCutoff + 1) + 1) * n := by
        simp only [Nat.add_mul, one_mul]
      _ ≤ tailCoefficient * n := Nat.mul_le_mul_right n hs
  · calc
      highBudget n =
          (3 + 5000 * Recovery.recoveryHardCoefficient + Schedule.weightedCoefficient) * n + 1 := by
        exact high_budget_factor n Recovery.recoveryHardCoefficient Schedule.weightedCoefficient
      _ ≤ (3 + 5000 * Recovery.recoveryHardCoefficient + Schedule.weightedCoefficient) * n + n :=
        Nat.add_le_add_left hn _
      _ = (3 + 5000 * Recovery.recoveryHardCoefficient + Schedule.weightedCoefficient + 1) * n := by
        simp only [Nat.add_mul, one_mul]
      _ ≤ tailCoefficient * n := Nat.mul_le_mul_right n hh
  · calc
      middleBudget n =
          (6 + 2 * Schedule.insideCoefficient * Recovery.recoveryHardCoefficient +
            5000 * Recovery.recoveryHardCoefficient +
            (100 * (160001 * Certificates.parallelZeroErrorConstant + 1) + 12)) * n + 1 := by
        exact middle_budget_factor n Recovery.recoveryHardCoefficient Schedule.insideCoefficient
          Certificates.parallelZeroErrorConstant
      _ ≤ (6 + 2 * Schedule.insideCoefficient * Recovery.recoveryHardCoefficient +
            5000 * Recovery.recoveryHardCoefficient +
            (100 * (160001 * Certificates.parallelZeroErrorConstant + 1) + 12)) * n + n :=
        Nat.add_le_add_left hn _
      _ = (6 + 2 * Schedule.insideCoefficient * Recovery.recoveryHardCoefficient +
            5000 * Recovery.recoveryHardCoefficient +
            (100 * (160001 * Certificates.parallelZeroErrorConstant + 1) + 12) + 1) * n := by
        simp only [Nat.add_mul, one_mul]
      _ ≤ tailCoefficient * n := Nat.mul_le_mul_right n hm

theorem reconstructionBudget_le (n : ℕ) (hn : 1 ≤ n) (hsmall : n < Schedule.sizeCutoff) :
    reconstructionBudget n ≤ tailCoefficient * n := by
  have hc : n.choose 2 ≤ n * n := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hnSquare : n ≤ n * n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hn
  have hcoef : 3 * Schedule.sizeCutoff ≤ tailCoefficient :=
    (coefficient_bounds Schedule.sizeCutoff Recovery.recoveryHardCoefficient
      Schedule.insideCoefficient Certificates.parallelZeroErrorConstant Schedule.degreeCutoff
      Schedule.weightedCoefficient).2.2.2
  calc
    reconstructionBudget n ≤ n * n + n * n + n * n :=
      Nat.add_le_add (Nat.add_le_add hnSquare hc) (hn.trans hnSquare)
    _ = 3 * n ^ 2 := by ring
    _ ≤ 3 * Schedule.sizeCutoff * n := Schedule.small_input_envelope n hsmall
    _ ≤ tailCoefficient * n := Nat.mul_le_mul_right n hcoef

attribute [local irreducible] attemptCoefficient tailCoefficient tailCoefficientFor

/-! The actual finite parallel program, followed by one original-value query. -/

def parallelPostprocess (π : PublicQuotient V Q) (hq : 2 ≤ Fintype.card Q)
    (H : Option (WeightedGraph Q)) : DTree (Finset V) ℝ (Option (CutResult V)) 1 :=
  match H with
  | none => DTree.pure none
  | some H => verifyShore (π.lift (explicitMinimum hq H))

def parallelShore (π : PublicQuotient V Q) (r : ℕ) (hq : 2 ≤ Fintype.card Q) :
    RTree (Finset V) ℝ (Option (CutResult V))
      (Certificates.parallelZeroErrorClock V Q r + 1) :=
  (Certificates.parallelZeroErrorFuel π r (Certificates.parallelZeroErrorClock V Q r)).bind
    (fun H => RTree.ofDeterministic (parallelPostprocess π hq H))

theorem parallelPostprocess_sound (π : PublicQuotient V Q) (hq : 2 ≤ Fintype.card Q)
    (H : Option (WeightedGraph Q)) (G : WeightedGraph V) {out : CutResult V}
    (hout : (parallelPostprocess π hq H).eval G.cut = some out) : out.Sound G := by
  cases H with
  | none => simp [parallelPostprocess] at hout
  | some H => exact verifyShore_sound G _ hout

theorem parallelShore_sound (π : PublicQuotient V Q) (r : ℕ) (hq : 2 ≤ Fintype.card Q)
    (G : WeightedGraph V) {out : CutResult V}
    (hout : some out ∈ ((parallelShore π r hq).eval G.cut).support) : out.Sound G := by
  rw [parallelShore, RTree.eval_bind, PMF.mem_support_bind_iff] at hout
  obtain ⟨H, _, hH⟩ := hout
  rw [RTree.eval_ofDeterministic, PMF.mem_support_pure_iff] at hH
  exact parallelPostprocess_sound π hq H G hH.symm

theorem parallelPostprocess_correct (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q) (G : WeightedGraph V) (H : WeightedGraph Q)
    (hH : IsThresholdCertificate r (π.graph G) H)
    (he : mincutValue (π.graph G) = mincutValue G) (hr : mincutValue G < r) :
    FoundMinimum G ((parallelPostprocess π hq (some H)).eval G.cut) := by
  have hmin : IsMinCut G (π.lift (explicitMinimum hq H)) :=
    π.lift_minimum_of_value_eq he
      (threshold_minimum hH (by rwa [he]) (explicitMinimum_spec hq H))
  refine ⟨⟨π.lift (explicitMinimum hq H), G.cut (π.lift (explicitMinimum hq H))⟩,
    ?_, ⟨hmin.1, rfl⟩, hmin, cut_eq_mincut_of_isMinCut hmin⟩
  simp [parallelPostprocess, verifyShore_eval, hmin.1]

theorem parallelShore_success (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q) (G : SimpleInput V)
    (hp : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ))
    (he : mincutValue (π.graph G.toWeighted) = mincutValue G.toWeighted)
    (hr : mincutValue G.toWeighted < r) :
    ENNReal.ofReal (99 / 100) ≤
      mass ((parallelShore π r hq).eval G.toWeighted.cut) (FoundMinimum G.toWeighted) := by
  have hs : ENNReal.ofReal (99 / 100) ≤
      mass ((Certificates.parallelZeroErrorFuel π r
        (Certificates.parallelZeroErrorClock V Q r)).eval G.toWeighted.cut)
        (fun H => H ≠ none) := by
    apply ninetyNine_of_failure
    simpa only [not_not] using Certificates.parallelZeroErrorFuel_one_percent π r G hq hp
  rw [parallelShore, RTree.eval_bind]
  calc
    ENNReal.ofReal (99 / 100) = ENNReal.ofReal (99 / 100) * 1 := by simp
    _ ≤ mass ((Certificates.parallelZeroErrorFuel π r
        (Certificates.parallelZeroErrorClock V Q r)).eval G.toWeighted.cut)
        (fun H => H ≠ none) * 1 := mul_le_mul_of_nonneg_right hs (by positivity)
    _ ≤ _ := by
      apply mass_bind_ge_countable
      intro H hH hne
      cases H with
      | none => exact (hne rfl).elim
      | some H =>
          have hc := Certificates.parallelZeroErrorFuel_success π r _ G hH
          have ho := parallelPostprocess_correct π r hq G.toWeighted H hc he hr
          simp only [RTree.eval_ofDeterministic, mass_pure, if_pos ho]
          exact le_rfl

theorem parallelClock_eq (r : ℕ) :
    Certificates.parallelZeroErrorClock V Q r =
      Schedule.parallelClock Certificates.parallelZeroErrorConstant
        (Fintype.card V) r (Fintype.card Q) := rfl

def smallDegreeProgram (d : ℕ) (hn : 2 ≤ Fintype.card V) :
    RTree (Finset V) ℝ (Option (CutResult V)) (smallDegreeBudget (Fintype.card V)) :=
  fit _ (parallelShore (PublicQuotient.identity (V := V)) d hn)

theorem smallDegreeProgram_sound (d : ℕ) (hn : 2 ≤ Fintype.card V)
    (G : WeightedGraph V) {out : CutResult V}
    (hout : some out ∈ ((smallDegreeProgram (V := V) d hn).eval G.cut).support) :
    out.Sound G :=
  fit_sound _ _ G (fun _ => parallelShore_sound _ d hn G) hout

theorem smallDegreeProgram_success (d : ℕ) (hn : 2 ≤ Fintype.card V)
    (hlarge : Schedule.sizeCutoff ≤ Fintype.card V) (hd : d < Schedule.degreeCutoff)
    (G : SimpleInput V) (hr : mincutValue G.toWeighted < d) :
    ENNReal.ofReal (99 / 100) ≤
      mass ((smallDegreeProgram (V := V) d hn).eval G.toWeighted.cut)
        (FoundMinimum G.toWeighted) := by
  have hb := Schedule.small_degree_parallelClock_le Certificates.parallelZeroErrorConstant
    (Fintype.card V) d hlarge hd
  have he := Schedule.parallelEligible_identity (Fintype.card V) hlarge
  rw [smallDegreeProgram, fit_eval _ _ (by
    rw [parallelClock_eq]; exact Nat.add_le_add_right hb 1)]
  apply parallelShore_success _ d hn G (by simpa only [Real.logb] using he.2.2) _ hr
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G.toWeighted hn
  exact (PublicQuotient.identity (V := V)).mincut_eq hS (by
    intro u v huv
    change u = v at huv
    simp only [huv])

/-! Middle quotients are solved at their public cube-logarithm branch. -/

def middleSolve (π : PublicQuotient V Q) (d : ℕ) :
    RTree (Finset V) ℝ (Option (CutResult V)) (middleSolveBudget (Fintype.card V)) :=
  if hn : Schedule.sizeCutoff ≤ Fintype.card V then
    if hg : Schedule.MiddleGuard (Fintype.card V) d (Fintype.card Q) then
      if (Fintype.card Q : ℝ) ≤ (Real.log (Fintype.card V)) ^ 3 then
        fit _ (RTree.ofDeterministic (Certificates.smallQuotientShore π d))
      else fit _ (parallelShore π d hg.2.1)
    else RTree.pure (PMF.pure none)
  else RTree.pure (PMF.pure none)

theorem middleSolve_sound (π : PublicQuotient V Q) (d : ℕ) (G : WeightedGraph V)
    {out : CutResult V} (hout : some out ∈ ((middleSolve π d).eval G.cut).support) :
    out.Sound G := by
  unfold middleSolve at hout
  split_ifs at hout with hn hg hc
  · apply fit_sound _ _ G _ hout
    intro out ho
    rw [RTree.eval_ofDeterministic, PMF.mem_support_pure_iff] at ho
    exact Certificates.smallQuotientShore_sound π d G ho.symm
  · exact fit_sound _ _ G (fun _ => parallelShore_sound π d hg.2.1 G) hout
  · simp at hout
  · simp at hout

theorem middleSolve_success (π : PublicQuotient V Q) (d : ℕ)
    (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (hg : Schedule.MiddleGuard (Fintype.card V) d (Fintype.card Q)) (G : SimpleInput V)
    (he : mincutValue (π.graph G.toWeighted) = mincutValue G.toWeighted)
    (hr : mincutValue G.toWeighted < d) :
    ENNReal.ofReal (99 / 100) ≤
      mass ((middleSolve π d).eval G.toWeighted.cut) (FoundMinimum G.toWeighted) := by
  rw [middleSolve, dif_pos hn, dif_pos hg]
  by_cases hc : (Fintype.card Q : ℝ) ≤ (Real.log (Fintype.card V)) ^ 3
  · have hfit : 12 * Fintype.card V + 1 ≤ middleSolveBudget (Fintype.card V) := by
      unfold middleSolveBudget
      exact Nat.add_le_add_right (Nat.mul_le_mul_right (Fintype.card V) (by omega)) 1
    rw [if_pos hc, fit_eval _ _ hfit]
    obtain ⟨S, hS, hs⟩ := π.exists_respecting_minimum_of_value_eq hg.2.1 he
    obtain ⟨out, ho, hsound, hmin, hv⟩ := Certificates.smallQuotientShore_correct π d
      hn hg hc G.toWeighted G.integral_toWeighted hS hs hr
    rw [RTree.eval_ofDeterministic, ho]
    have hgood : FoundMinimum G.toWeighted (some out) := ⟨out, rfl, hsound, hmin, hv⟩
    simp only [mass_pure, if_pos hgood]
    norm_num
  · rw [if_neg hc]
    have hlarge : (Real.log (Fintype.card V)) ^ 3 ≤ (Fintype.card Q : ℝ) :=
      (lt_of_not_ge hc).le
    have hb := Schedule.middle_parallelClock_le Certificates.parallelZeroErrorConstant
      (Fintype.card V) d (Fintype.card Q) hn hg hlarge
    have hfit : Certificates.parallelZeroErrorClock V Q d + 1 ≤
        middleSolveBudget (Fintype.card V) := by
      rw [parallelClock_eq]
      unfold middleSolveBudget
      exact Nat.add_le_add_right
        (hb.trans (Nat.mul_le_mul_right (Fintype.card V) (by omega))) 1
    rw [fit_eval _ _ hfit]
    have hp := Schedule.parallelEligible_of_cube (Fintype.card V) (Fintype.card Q)
      hn hg.2.1 hg.2.2.1 hlarge
    exact parallelShore_success π d hg.2.1 G (by simpa only [Real.logb] using hp.2.2) he hr

variable [LinearOrder V]

def middleContinuation (d : ℕ) (out : Option (Joint.MiddleTranscript V)) :
    RTree (Finset V) ℝ (Option (CutResult V)) (middleSolveBudget (Fintype.card V)) :=
  match out with
  | none => RTree.pure (PMF.pure none)
  | some T => middleSolve T.quotient d

def middleProgram (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    RTree (Finset V) ℝ (Option (CutResult V)) (middleBudget (Fintype.card V)) :=
  (Uniform.middleProgram d hd).bind (middleContinuation d)

theorem middleContinuation_sound (d : ℕ) (T : Option (Joint.MiddleTranscript V))
    (G : WeightedGraph V) {out : CutResult V}
    (hout : some out ∈ ((middleContinuation d T).eval G.cut).support) : out.Sound G := by
  cases T with
  | none => simp [middleContinuation] at hout
  | some T => exact middleSolve_sound T.quotient d G hout

theorem middleProgram_sound (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (G : WeightedGraph V) {out : CutResult V}
    (hout : some out ∈ ((middleProgram (V := V) d hd).eval G.cut).support) :
    out.Sound G := by
  change some out ∈ (((Uniform.middleProgram (V := V) d hd).bind
    (middleContinuation d)).eval G.cut).support at hout
  rw [RTree.eval_bind, PMF.mem_support_bind_iff] at hout
  obtain ⟨T, _, hT⟩ := hout
  exact middleContinuation_sound d T G hT

theorem middleProgram_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (hdegree : Schedule.DegreeGuard (Fintype.card V) d)
    (hbranch : (d : ℝ) ≤ (Real.log (Fintype.card V)) ^ 10)
    (hS : IsMinCut G.toWeighted S) (hdeg : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v)
    (hcut : G.toWeighted.cut S < d) :
    ENNReal.ofReal Schedule.pStar ≤
      mass ((middleProgram (V := V) d hd).eval G.toWeighted.cut)
        (FoundMinimum G.toWeighted) := by
  rw [Joint.pStar_eq_middleContraction_times_certificate,
    ENNReal.ofReal_mul (by positivity)]
  apply (mul_le_mul_of_nonneg_right (Uniform.middleProgram_success G S d hd hS hdeg hcut)
    (by positivity)).trans
  change _ ≤ mass (((Uniform.middleProgram (V := V) d hd).bind
    (middleContinuation d)).eval G.toWeighted.cut) (FoundMinimum G.toWeighted)
  rw [RTree.eval_bind]
  apply mass_bind_ge_countable
  intro T hT hgood
  obtain ⟨T, rfl, _, he⟩ := hgood
  exact middleSolve_success T.quotient d hn
    (Uniform.middleProgram_guard d hd G.toWeighted.cut T hT hdegree hbranch) G he
    (by rwa [← cut_eq_mincut_of_isMinCut hS])

/-! Exact bounded-size reconstruction and the public branch selector. -/

def reconstructionProgram (hn : 2 ≤ Fintype.card V) :
    DTree (Finset V) ℝ (Option (CutResult V)) (reconstructionBudget (Fintype.card V)) :=
  (reconstruct (V := V)).bind fun H => verifyShore (explicitMinimum hn H)

theorem reconstructionProgram_sound (hn : 2 ≤ Fintype.card V) (G : WeightedGraph V)
    {out : CutResult V} (hout : (reconstructionProgram hn).eval G.cut = some out) :
    out.Sound G := by
  change ((reconstruct (V := V)).bind fun H => verifyShore (explicitMinimum hn H)).eval
    G.cut = some out at hout
  rw [DTree.eval_bind] at hout
  exact verifyShore_sound G _ hout

theorem reconstructionProgram_correct (hn : 2 ≤ Fintype.card V) (G : WeightedGraph V) :
    FoundMinimum G ((reconstructionProgram hn).eval G.cut) := by
  have he : (reconstruct (V := V)).eval G.cut = G :=
    congrArg Prod.fst (reconstruct_run G)
  change FoundMinimum G (((reconstruct (V := V)).bind fun H =>
    verifyShore (explicitMinimum hn H)).eval G.cut)
  rw [DTree.eval_bind, he]
  have hs := explicitMinimum_spec hn G
  refine ⟨⟨explicitMinimum hn G, G.cut (explicitMinimum hn G)⟩,
    ?_, ⟨hs.1, rfl⟩, hs, cut_eq_mincut_of_isMinCut hs⟩
  simp [verifyShore_eval, hs.1]

def candidateProgram (hn : 2 ≤ Fintype.card V) (d : ℕ) :
    RTree (Finset V) ℝ (Option (CutResult V)) (tailCoefficient * Fintype.card V) :=
  if Fintype.card V < Schedule.sizeCutoff then
    fit _ (RTree.ofDeterministic (reconstructionProgram hn))
  else if d = 0 then RTree.pure (PMF.pure none)
  else if hd : d < Schedule.degreeCutoff then
    fit _ (smallDegreeProgram d hn)
  else if (Real.log (Fintype.card V)) ^ 10 < (d : ℝ) then
    fit _ (highProgram d (Nat.le_of_not_gt hd))
  else fit _ (middleProgram d (Nat.le_of_not_gt hd))

theorem candidateProgram_sound (hn : 2 ≤ Fintype.card V) (d : ℕ)
    (G : WeightedGraph V) {out : CutResult V}
    (hout : some out ∈ ((candidateProgram hn d).eval G.cut).support) : out.Sound G := by
  unfold candidateProgram at hout
  split_ifs at hout with hsmall hz hd hhigh
  · apply fit_sound _ _ G _ hout
    intro out ho
    rw [RTree.eval_ofDeterministic, PMF.mem_support_pure_iff] at ho
    exact reconstructionProgram_sound hn G ho.symm
  · simp at hout
  · exact fit_sound _ _ G (fun _ => smallDegreeProgram_sound d hn G) hout
  · exact fit_sound _ _ G (fun _ => highProgram_sound d _ G) hout
  · exact fit_sound _ _ G (fun _ => middleProgram_sound d _ G) hout

theorem pStar_le_ninetyNine : Schedule.pStar ≤ (99 / 100 : ℝ) := by
  have hp : (3 / 10 : ℝ) ^ 115 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact pStar_le_high_times_certificate.trans (by nlinarith)

theorem candidateProgram_success (hn : 2 ≤ Fintype.card V) (d : ℕ)
    (G : SimpleInput V) (hdn : d < Fintype.card V)
    (hdeg : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v)
    (hr : mincutValue G.toWeighted < d) :
    ENNReal.ofReal Schedule.pStar ≤
      mass ((candidateProgram hn d).eval G.toWeighted.cut) (FoundMinimum G.toWeighted) := by
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G.toWeighted hn
  have hcut : G.toWeighted.cut S < d := by rwa [cut_eq_mincut_of_isMinCut hS]
  have hd0 : d ≠ 0 := by
    intro hz
    have h0 := mincutValue_nonneg G.toWeighted
    simp only [hz, Nat.cast_zero] at hr
    linarith
  have hguard : Schedule.DegreeGuard (Fintype.card V) d := ⟨by omega, hdn⟩
  obtain ⟨hbsmall, hbhigh, hbmiddle⟩ := branch_budgets (Fintype.card V) (by omega)
  unfold candidateProgram
  by_cases hsmall : Fintype.card V < Schedule.sizeCutoff
  · rw [if_pos hsmall, fit_eval _ _ (reconstructionBudget_le _ (by omega) hsmall),
      RTree.eval_ofDeterministic]
    have hgood := reconstructionProgram_correct hn G.toWeighted
    simp only [mass_pure, if_pos hgood]
    exact (ENNReal.ofReal_le_ofReal Schedule.pStar_le_one).trans_eq (by simp)
  · rw [if_neg hsmall, if_neg hd0]
    have hlarge := Nat.le_of_not_gt hsmall
    by_cases hd : d < Schedule.degreeCutoff
    · rw [dif_pos hd, fit_eval _ _ hbsmall]
      exact (ENNReal.ofReal_le_ofReal pStar_le_ninetyNine).trans
        (smallDegreeProgram_success d hn hlarge hd G hr)
    · rw [dif_neg hd]
      by_cases hhigh : (Real.log (Fintype.card V)) ^ 10 < (d : ℝ)
      · rw [if_pos hhigh, fit_eval _ _ hbhigh]
        exact highProgram_success G S d (Nat.le_of_not_gt hd) hlarge hguard hhigh hS hdeg hcut
      · rw [if_neg hhigh, fit_eval _ _ hbmiddle]
        exact middleProgram_success G S d (Nat.le_of_not_gt hd) hlarge hguard
          (le_of_not_gt hhigh) hS hdeg hcut

/-! Singleton measurements are actual original queries. The total decoder
validates every count before any logarithm of a measured degree is used. -/

private theorem exists_minimumVertex (hn : 2 ≤ Fintype.card V) (answers : V → ℝ) :
    ∃ v, ∀ u, answers v ≤ answers u := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact Finite.exists_min answers

def minimumVertex (hn : 2 ≤ Fintype.card V) (answers : V → ℝ) : V :=
  Classical.choose (exists_minimumVertex hn answers)

theorem minimumVertex_le (hn : 2 ≤ Fintype.card V) (answers : V → ℝ) (v : V) :
    answers (minimumVertex hn answers) ≤ answers v :=
  Classical.choose_spec (exists_minimumVertex hn answers) v

def ValidDegreeTable (answers : V → ℝ) : Prop :=
  ∀ v, ∃ k, validateCount (Fintype.card V - 1) (answers v) = some k

def decodeDegrees (hn : 2 ≤ Fintype.card V) (answers : V → ℝ) : Option (V × ℕ) :=
  if ValidDegreeTable answers then
    let v := minimumVertex hn answers
    match validateCount (Fintype.card V - 1) (answers v) with
    | none => none
    | some d => some (v, d.val)
  else none

theorem decodeDegrees_spec (hn : 2 ≤ Fintype.card V) (answers : V → ℝ)
    {v : V} {d : ℕ} (ho : decodeDegrees hn answers = some (v, d)) :
    ValidDegreeTable answers ∧ d < Fintype.card V ∧ answers v = d ∧
      ∀ u, answers v ≤ answers u := by
  unfold decodeDegrees at ho
  split_ifs at ho with ht
  · cases he : validateCount (Fintype.card V - 1) (answers (minimumVertex hn answers)) with
    | none => simp [he] at ho
    | some k =>
        simp only [he] at ho
        have hp := Option.some.inj ho
        have hv : minimumVertex hn answers = v := congrArg Prod.fst hp
        have hd : (k : ℕ) = d := congrArg Prod.snd hp
        have hk := validateCount_spec he
        refine ⟨ht, ?_, ?_, ?_⟩
        · have hb := hk.2
          omega
        · calc
            answers v = answers (minimumVertex hn answers) := congrArg answers hv.symm
            _ = (k : ℕ) := hk.1.symm
            _ = d := by exact_mod_cast hd
        · intro u
          rw [← hv]
          exact minimumVertex_le hn answers u
theorem decodeDegrees_correct (hn : 2 ≤ Fintype.card V) (G : SimpleInput V) :
    ∃ v d, decodeDegrees hn (fun u => G.toWeighted.cut {u}) = some (v, d) ∧
      d < Fintype.card V ∧ G.toWeighted.cut {v} = d ∧
      (∀ u, (d : ℝ) ≤ G.toWeighted.degree u) := by
  have hv : ValidDegreeTable (fun u => G.toWeighted.cut {u}) := by
    intro u
    exact ⟨_, validate_singleton G u⟩
  let v := minimumVertex hn (fun u => G.toWeighted.cut {u})
  refine ⟨v, G.cut {v}, ?_, ?_, ?_, ?_⟩
  · simp only [decodeDegrees, if_pos hv]
    rw [validate_singleton]
  · have hc := singleton_count_le G v
    omega
  · exact CapacityGraph.toWeighted_cut G {v}
  · intro u
    have hm := minimumVertex_le hn (fun u => G.toWeighted.cut {u}) u
    calc
      (G.cut {v} : ℝ) = G.toWeighted.cut {v} := (CapacityGraph.toWeighted_cut G {v}).symm
      _ ≤ G.toWeighted.cut {u} := hm
      _ = G.toWeighted.degree u := G.toWeighted.cut_singleton u

def degreeProgram : DTree (Finset V) ℝ (V → ℝ) (Fintype.card V) :=
  DTree.queryAll (fun v => {v}) (fun _ => 0)

@[simp] theorem degreeProgram_eval (read : Finset V → ℝ) :
    (degreeProgram (V := V)).eval read = fun v => read {v} := by
  simp [degreeProgram, DTree.eval]

def attemptTail (hn : 2 ≤ Fintype.card V) (answers : V → ℝ) :
    RTree (Finset V) ℝ (CutResult V) (tailCoefficient * Fintype.card V) :=
  match decodeDegrees hn answers with
  | none => RTree.pure (PMF.pure ⟨∅, 0⟩)
  | some (v, d) => (candidateProgram hn d).map (retain ⟨{v}, (d : ℝ)⟩)

def attempt (hn : 2 ≤ Fintype.card V) :
    RTree (Finset V) ℝ (CutResult V) (attemptCoefficient * Fintype.card V) :=
  ((RTree.ofDeterministic degreeProgram).bind (attemptTail hn)).cast (by
    rw [attemptCoefficient_eq]
    ring)

theorem attempt_eval (hn : 2 ≤ Fintype.card V) (read : Finset V → ℝ) :
    (attempt hn).eval read = (attemptTail hn (fun v => read {v})).eval read := by
  simp only [attempt, RTree.eval_cast, RTree.eval_bind, RTree.eval_ofDeterministic,
    degreeProgram_eval, PMF.pure_bind]

theorem retain_optimal_right {G : WeightedGraph V} {old out : CutResult V}
    (hold : old.Sound G) (hout : CutResult.Optimal G out) :
    CutResult.Optimal G (retain old (some out)) := by
  have hs := retain_sound hold (fun x hx => by
    cases Option.some.inj hx
    exact hout.1)
  apply CutResult.optimal_of_sound_value hs
  have hle : (retain old (some out)).value ≤ out.value := by
    simp only [retain]
    split_ifs with h
    · exact le_rfl
    · exact le_of_not_gt h
  exact le_antisymm (hle.trans_eq hout.2.2) hs.mincut_le

theorem attempt_sound (hn : 2 ≤ Fintype.card V) (G : SimpleInput V)
    {out : CutResult V} (hout : out ∈ ((attempt hn).eval G.toWeighted.cut).support) :
    out.Sound G.toWeighted := by
  obtain ⟨v, d, he, _, hv, _⟩ := decodeDegrees_correct hn G
  rw [attempt_eval, attemptTail, he, RTree.eval_map] at hout
  obtain ⟨candidate, hc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  apply retain_sound
  · exact ⟨properShore_singleton v hn, hv.symm⟩
  · intro fresh hf
    rw [hf] at hc
    exact candidateProgram_sound hn d G.toWeighted hc

/-- One complete attempt succeeds with the fixed public probability pStar.
The equality lambda=d case uses only the measured singleton, so strict
threshold extraction is never invoked at equality. -/
theorem attempt_success (hn : 2 ≤ Fintype.card V) (G : SimpleInput V) :
    ENNReal.ofReal Schedule.pStar ≤
      mass ((attempt hn).eval G.toWeighted.cut) (CutResult.Optimal G.toWeighted) := by
  obtain ⟨v, d, he, hdn, hv, hdeg⟩ := decodeDegrees_correct hn G
  have hold : (⟨{v}, (d : ℝ)⟩ : CutResult V).Sound G.toWeighted :=
    ⟨properShore_singleton v hn, hv.symm⟩
  rw [attempt_eval, attemptTail, he, RTree.eval_map, mass_map]
  by_cases hm : (d : ℝ) = mincutValue G.toWeighted
  · have hall : mass ((candidateProgram hn d).eval G.toWeighted.cut)
        (fun candidate => CutResult.Optimal G.toWeighted (retain ⟨{v}, (d : ℝ)⟩ candidate)) = 1 := by
      apply mass_eq_one_of_support
      intro candidate hc
      have hnew : ∀ fresh, candidate = some fresh → fresh.Sound G.toWeighted := by
        intro fresh hf
        rw [hf] at hc
        exact candidateProgram_sound hn d G.toWeighted hc
      exact CutResult.optimal_of_sound_value (retain_sound hold hnew)
        (retain_preserves_minimum hold hnew hm)
    rw [hall]
    exact (ENNReal.ofReal_le_ofReal Schedule.pStar_le_one).trans_eq (by simp)
  · have hr : mincutValue G.toWeighted < d := by
      have hl := hold.mincut_le
      change mincutValue G.toWeighted ≤ (d : ℝ) at hl
      exact lt_of_le_of_ne hl (Ne.symm hm)
    apply (candidateProgram_success hn d G hdn hdeg hr).trans
    apply mass_mono
    rintro candidate ⟨fresh, rfl, hf⟩
    exact retain_optimal_right hold hf

theorem attempt_every_oracle (hn : 2 ≤ Fintype.card V) (read : Finset V → ℝ)
    {out : CutResult V × ℕ} (hout : out ∈ (RTree.run read (attempt hn)).support) :
    out.2 ≤ attemptCoefficient * Fintype.card V := RTree.cost_le _ _ hout

#print axioms attemptCoefficient_eq
#print axioms branch_budgets
#print axioms reconstructionBudget_le
#print axioms parallelShore_sound
#print axioms parallelShore_success
#print axioms smallDegreeProgram_success
#print axioms middleSolve_success
#print axioms middleProgram_success
#print axioms reconstructionProgram_correct
#print axioms candidateProgram_sound
#print axioms candidateProgram_success
#print axioms decodeDegrees_spec
#print axioms decodeDegrees_correct
#print axioms attempt_sound
#print axioms attempt_success
#print axioms attempt_every_oracle

end
end CutQueryComplexity.StarContraction2022.Randomized

