import CutQueryComplexity.StarContraction2022.Contraction.Joint.Attachments
import CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.Outside
import CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.Centers

/-! Part of the actual contraction proof: outside-row recovery and high-degree transcripts. -/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.Joint

open Finset LearnSubgraph
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

private theorem recovery_mass_bind_ge {T U : Type*} (p : PMF T) (next : T → PMF U)
    (Good : T → Prop) (Success : U → Prop) (c : ℝ≥0∞)
    (h : ∀ t ∈ p.support, Good t → c ≤ mass (next t) Success) :
    mass p Good * c ≤ mass (p.bind next) Success := by
  rw [mass_eq_tsum, mass_bind, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases ht : Good t
  · simp only [ht, ite_true]
    by_cases hs : t ∈ p.support
    · exact mul_le_mul le_rfl (h t hs ht) (by positivity) (by positivity)
    · have hz : p t = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
      simp [hz]
  · simp [ht]

/-! Actual outside recovery followed by fresh replacement draws. -/

/-- A missing recovery is represented by empty public lists. It is charged
as a failed outcome in the probability proof, never declared successful. -/
def learnedOutsideRows (R B : Finset V)
    (out : Option (Recovery.BucketState (outsideSources R B) R)) :
    outsideSources R B → Finset R :=
  out.elim (fun _ => ∅) fun st u => (st.learned u).getD ∅

/-- This predicate is proof-only; the public program receives neither G nor S. -/
def OutsideRecovered (G : SimpleInput V) (S R B : Finset V)
    (out : Option (Recovery.BucketState (outsideSources R B) R)) : Prop :=
  ∃ st, out = some st ∧
    (∀ u, ∃ N, st.learned u = some N ∧ 5000 ≤ N.card ∧
      ∀ v ∈ N, (G.w u.val v.val : ℕ) = 1) ∧
    (∀ u, recoveredRatio u (outsideCrossing G S R B u) (some st) ≤ 7 / 10) ∧
    (∑ u, recoveredRatio u (outsideCrossing G S R B u) (some st)) ≤ 80

/-- The true-neighbor conclusion of capped recovery identifies its row
ratio with the ratio used by the actual attachment sampler. -/
theorem outsideRecovered_properties (G : SimpleInput V) (S R B : Finset V)
    (out : Option (Recovery.BucketState (outsideSources R B) R))
    (hout : OutsideRecovered G S R B out) :
    (∀ u, (learnedOutsideRows R B out u).Nonempty) ∧
    (∀ u, CenterAttachment.outsideRatio (outsideSources R B) R S
      (learnedOutsideRows R B out) u ≤ 7 / 10) ∧
    (∑ u, CenterAttachment.outsideRatio (outsideSources R B) R S
      (learnedOutsideRows R B out) u) ≤ 80 := by
  rcases hout with ⟨st, rfl, hrows, hmax, hsum⟩
  have hsub : ∀ u, learnedOutsideRows R B (some st) u ⊆ outsideNeighbors G R B u := by
    intro u
    obtain ⟨N, hN, _, htrue⟩ := hrows u
    simp only [learnedOutsideRows, Option.elim_some, hN, Option.getD_some]
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    dsimp only [Recovery.graphMatrix, Function.Embedding.subtype_apply]
    exact @decide_eq_true _ _ (htrue v hv)
  have he (u : outsideSources R B) :
      CenterAttachment.outsideRatio (outsideSources R B) R S
        (learnedOutsideRows R B (some st)) u =
      recoveredRatio u (outsideCrossing G S R B u) (some st) := by
    rw [recoveredRatio_some]
    exact CenterAttachment.outsideRatio_true_subrow (outsideSources R B) R S
      (learnedOutsideRows R B (some st)) (outsideNeighbors G R B) hsub u
  refine ⟨?_, ?_, ?_⟩
  · intro u
    obtain ⟨N, hN, hcard, _⟩ := hrows u
    simpa only [learnedOutsideRows, Option.elim_some, hN, Option.getD_some] using
      (card_pos.mp (show 0 < N.card by omega))
  · intro u
    rw [he]
    exact hmax u
  · simp_rw [he]
    exact hsum

/-- One actual outside recovery call, followed by fresh draws from its full
returned row table. The complete bucket state remains in the output. -/
def learnedOutsideDrawsProgram (R B : Finset V) :
    RTree (Finset V) ℝ
      (Option (Recovery.BucketState (outsideSources R B) R) × (V → Option R))
      (Recovery.recoveryHardCoefficient * 5000 * Fintype.card V) :=
  outsideAttachmentAfter (outsideRecoveryProgram R B) R B (learnedOutsideRows R B)

theorem learnedOutsideDrawsProgram_success (G : SimpleInput V) (S R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) (hS : IsMinCut G.toWeighted S) :
    let B := SparseCenters.badRows (SparseCenters.inputRows G) d R
    (1 / 2 : ℝ≥0∞) * ENNReal.ofReal ((3 / 10 : ℝ) ^ 115) ≤
      mass ((learnedOutsideDrawsProgram R B).eval G.toWeighted.cut) (fun out =>
        OutsideRecovered G S R B out.1 ∧
        IsMinCut ((outsideQuotient R out.2).graph G.toWeighted)
          (S.image (outsideQuotient R out.2).map) ∧
        mincutValue ((outsideQuotient R out.2).graph G.toWeighted) = mincutValue G.toWeighted ∧
        2 ≤ Fintype.card (R ⊕ CenterAttachment.unattached R out.2) ∧
        (Fintype.card (R ⊕ CenterAttachment.unattached R out.2) : ℝ) * d ≤
          300001 * Fintype.card V * Real.log d) := by
  intro B
  have hrec : (1 / 2 : ℝ≥0∞) ≤
      mass ((outsideRecoveryProgram R B).eval G.toWeighted.cut) (OutsideRecovered G S R B) :=
    outsideRecoveryProgram_center_success G S R d hd hgood
  apply (mul_le_mul hrec le_rfl (by positivity) (by positivity)).trans
  exact outsideAttachmentAfter_success (outsideRecoveryProgram R B) R B S d
    (learnedOutsideRows R B) G.toWeighted hS hd hgood.1 hgood.2.1
    (OutsideRecovered G S R B) (fun out _ ho => outsideRecovered_properties G S R B out ho)

/-- All retained information is public: sampled sets, measured counts, the
complete learned state, and the subsequent replacement draws. -/
structure HighTranscript (V : Type) [Fintype V] [DecidableEq V] where
  centers : Finset V
  bad : Finset V
  measured : V → ℝ
  recovery : Option (Recovery.BucketState (outsideSources centers bad) centers)
  attachment : V → Option centers

def HighTranscript.quotient (out : HighTranscript V) :
    PublicQuotient V (out.centers ⊕ CenterAttachment.unattached out.centers out.attachment) :=
  outsideQuotient out.centers out.attachment

/-- Continue the actual center query stage. The public bad set is used to
choose row indices, and all-answer costs are fixed before receiving answers. -/
def highAfterCenters (out : Option (Finset V × Finset V × (V → ℝ))) :
    RTree (Finset V) ℝ (Option (HighTranscript V))
      (Recovery.recoveryHardCoefficient * 5000 * Fintype.card V) :=
  match out with
  | none => RTree.pure (PMF.pure none)
  | some (R, B, answers) =>
      (learnedOutsideDrawsProgram R B).map fun learned =>
        some ⟨R, B, answers, learned.1, learned.2⟩

/-- Actual public high-degree contraction, through original-cut queries.
The hidden graph and its optimum shore are absent from every program input. -/
def highContractionProgram (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    RTree (Finset V) ℝ (Option (HighTranscript V))
      (3 * Fintype.card V + Recovery.recoveryHardCoefficient * 5000 * Fintype.card V) :=
  (SparseCenters.centersProgram d hd).bind highAfterCenters

theorem highContractionProgram_every_oracle (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) {out : Option (HighTranscript V) × ℕ}
    (hout : out ∈ (RTree.run read (highContractionProgram (V := V) d hd)).support) :
    out.2 ≤ 3 * Fintype.card V + Recovery.recoveryHardCoefficient * 5000 * Fintype.card V :=
  RTree.cost_le _ _ hout

def HighSuccess (G : WeightedGraph V) (S : Finset V) (d : ℕ)
    (out : Option (HighTranscript V)) : Prop :=
  ∃ T, out = some T ∧
    IsMinCut (T.quotient.graph G) (S.image T.quotient.map) ∧
    mincutValue (T.quotient.graph G) = mincutValue G ∧
    2 ≤ Fintype.card (T.centers ⊕ CenterAttachment.unattached T.centers T.attachment) ∧
    (Fintype.card (T.centers ⊕ CenterAttachment.unattached T.centers T.attachment) : ℝ) * d ≤
      300001 * Fintype.card V * Real.log d

theorem highAfterCenters_success (G : SimpleInput V) (S R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) (hS : IsMinCut G.toWeighted S)
    (answers : V → ℝ) :
    (1 / 2 : ℝ≥0∞) * ENNReal.ofReal ((3 / 10 : ℝ) ^ 115) ≤
      mass ((highAfterCenters (some (R, SparseCenters.badRows
        (SparseCenters.inputRows G) d R, answers))).eval G.toWeighted.cut)
        (HighSuccess G.toWeighted S d) := by
  simp only [highAfterCenters, RTree.eval_map, mass_map]
  apply (learnedOutsideDrawsProgram_success G S R d hd hgood hS).trans
  apply mass_mono
  intro learned hlearned
  exact ⟨⟨R, SparseCenters.badRows (SparseCenters.inputRows G) d R,
    answers, learned.1, learned.2⟩, rfl, hlearned.2⟩

/-- The actual center, capped-recovery and replacement-draw laws give the
literal high-degree success constant. There is no successful-row oracle or
induced-minimum hypothesis in this statement. -/
theorem highContractionProgram_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hS : IsMinCut G.toWeighted S)
    (hdegree : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v) (hcut : G.toWeighted.cut S < d) :
    ENNReal.ofReal ((1 / 3 : ℝ) * (3 / 10 : ℝ) ^ 115) ≤
      mass ((highContractionProgram (V := V) d hd).eval G.toWeighted.cut)
        (HighSuccess G.toWeighted S d) := by
  let Good := fun out : Option (Finset V × Finset V × (V → ℝ)) =>
    ∃ R, SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R ∧
      out = some (R, SparseCenters.badRows (SparseCenters.inputRows G) d R,
        fun v => ((SparseCenters.inputRows G v ∩ R).card : ℝ))
  have hcenter : ENNReal.ofReal (2 / 3 : ℝ) ≤
      mass ((SparseCenters.centersProgram (V := V) d hd).eval G.toWeighted.cut) Good := by
    have hr := SparseCenters.centersProgram_minimum_success G S d hd hS hdegree hcut
    have he := ENNReal.ofReal_le_ofReal hr
    simpa only [ENNReal.ofReal_toReal (mass_ne_top _ _)] using he
  have hfactor : ENNReal.ofReal ((1 / 3 : ℝ) * (3 / 10 : ℝ) ^ 115) =
      ENNReal.ofReal (2 / 3 : ℝ) *
        ((1 / 2 : ℝ≥0∞) * ENNReal.ofReal ((3 / 10 : ℝ) ^ 115)) := by
    rw [show (1 / 3 : ℝ) * (3 / 10 : ℝ) ^ 115 =
      (2 / 3 : ℝ) * ((1 / 2 : ℝ) * (3 / 10 : ℝ) ^ 115) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 / 3),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hfactor, highContractionProgram, RTree.eval_bind]
  apply (mul_le_mul hcenter le_rfl (by positivity) (by positivity)).trans
  apply recovery_mass_bind_ge _ _ Good _ _
  intro out _ hout
  rcases hout with ⟨R, hgood, rfl⟩
  exact highAfterCenters_success G S R d hd hgood hS _

/-! The middle-degree branch learns both inside and outside rows. -/

/-- This postprocessing test uses only the public quotient dimensions. -/
def HighSizeGuard (d : ℕ) (T : HighTranscript V) : Prop :=
  2 ≤ Fintype.card (T.centers ⊕ CenterAttachment.unattached T.centers T.attachment) ∧
    (Fintype.card (T.centers ⊕ CenterAttachment.unattached T.centers T.attachment) : ℝ) * d ≤
      300001 * Fintype.card V * Real.log d

def checkHighOutput (d : ℕ) (out : Option (HighTranscript V)) : Option (HighTranscript V) :=
  match out with
  | none => none
  | some T => if HighSizeGuard d T then some T else none

theorem checkHighOutput_guard (d : ℕ) (out : Option (HighTranscript V)) (T : HighTranscript V)
    (he : checkHighOutput d out = some T) : HighSizeGuard d T := by
  cases out with
  | none => simp [checkHighOutput] at he
  | some X =>
      by_cases hx : HighSizeGuard d X
      · have hXT : X = T := by simpa only [checkHighOutput, if_pos hx, Option.some.injEq] using he
        exact hXT ▸ hx
      · simp [checkHighOutput, hx] at he

theorem checkHighOutput_of_success (G : WeightedGraph V) (S : Finset V) (d : ℕ)
    (out : Option (HighTranscript V)) (ho : HighSuccess G S d out) :
    checkHighOutput d out = out := by
  rcases ho with ⟨T, rfl, _, _, hcard, hsize⟩
  exact if_pos (show HighSizeGuard d T from ⟨hcard, hsize⟩)

def checkedHighContractionProgram (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    RTree (Finset V) ℝ (Option (HighTranscript V))
      (3 * Fintype.card V + Recovery.recoveryHardCoefficient * 5000 * Fintype.card V) :=
  (highContractionProgram d hd).map (checkHighOutput d)

/-- Every retained result satisfies the public guard for every oracle. -/
theorem checkedHighContractionProgram_guard (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) (T : HighTranscript V)
    (hT : some T ∈ ((checkedHighContractionProgram (V := V) d hd).eval read).support) :
    HighSizeGuard d T := by
  rw [checkedHighContractionProgram, RTree.eval_map] at hT
  obtain ⟨out, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hT
  exact checkHighOutput_guard d out T he

theorem checkedHighContractionProgram_every_oracle (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) {out : Option (HighTranscript V) × ℕ}
    (hout : out ∈ (RTree.run read (checkedHighContractionProgram (V := V) d hd)).support) :
    out.2 ≤ 3 * Fintype.card V + Recovery.recoveryHardCoefficient * 5000 * Fintype.card V :=
  RTree.cost_le _ _ hout

/-- The retained public quotient supplies the complete schedule guard once
the caller's public degree and branch tests have succeeded. -/
theorem checkedHighContractionProgram_scheduleGuard (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) (T : HighTranscript V)
    (hT : some T ∈ ((checkedHighContractionProgram (V := V) d hd).eval read).support)
    (hdegree : Schedule.DegreeGuard (Fintype.card V) d)
    (hbranch : (Real.log (Fintype.card V)) ^ 10 < (d : ℝ)) :
    Schedule.HighGuard (Fintype.card V) d
      (Fintype.card (T.centers ⊕ CenterAttachment.unattached T.centers T.attachment)) := by
  have hguard := checkedHighContractionProgram_guard d hd read T hT
  exact ⟨hdegree, hguard.1, T.quotient.card_le, hbranch, hguard.2⟩

theorem checkedHighContractionProgram_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hS : IsMinCut G.toWeighted S)
    (hdegree : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v) (hcut : G.toWeighted.cut S < d) :
    ENNReal.ofReal ((1 / 3 : ℝ) * (3 / 10 : ℝ) ^ 115) ≤
      mass ((checkedHighContractionProgram (V := V) d hd).eval G.toWeighted.cut)
        (HighSuccess G.toWeighted S d) := by
  rw [checkedHighContractionProgram, RTree.eval_map, mass_map]
  apply (highContractionProgram_success G S d hd hS hdegree hcut).trans
  apply mass_mono
  intro out ho
  rwa [checkHighOutput_of_success G.toWeighted S d out ho]

section MiddleRecovery

variable [LinearOrder V]

def learnedCenterRows (R : Finset V) (out : Option (LearnedTranscript R)) : R → Finset R :=
  out.elim (fun _ => ∅) LearnedTranscript.rows

def CenterRecovered (G : SimpleInput V) (S R B : Finset V) (d : ℕ)
    (out : Option (LearnedTranscript R)) : Prop :=
  LearnedResult (Function.Embedding.subtype (· ∈ R)) G (S.subtype (· ∈ R))
    (Schedule.height d) (B ∩ R).card (4 / 5) 800 out

theorem centerRecovered_properties (G : SimpleInput V) (S R B : Finset V) (d : ℕ)
    (out : Option (LearnedTranscript R)) (hout : CenterRecovered G S R B d out) :
    GoodRows (4 / 5) 800 (learnedCenterRows R out) (CenterAttachment.trace R S) ∧
    (∀ u, learnedCenterRows R out u ≠ ∅ → Schedule.height d ≤ (learnedCenterRows R out u).card) ∧
    (((zeroSources (learnedCenterRows R out)).card : ℝ) ≤
      (B ∩ R).card + (R.card : ℝ) / Schedule.height d) ∧
    (∀ u, u ∉ learnedCenterRows R out u) := by
  rcases hout with ⟨T, rfl, hgood, htrue, hdegree, hzero⟩
  have htrace : CenterAttachment.trace R S = S.subtype (· ∈ R) := by
    ext u
    simp [CenterAttachment.trace]
  refine ⟨?_, hdegree, ?_, ?_⟩
  · simpa only [learnedCenterRows, Option.elim_some, htrace] using hgood
  · simpa only [learnedCenterRows, Option.elim_some, Fintype.card_coe] using hzero
  · intro u hu
    exact originalRowsOn_loopless (Function.Embedding.subtype (· ∈ R)) G u (htrue u hu)

abbrev RecoveryTranscript (R B : Finset V) :=
  Option (LearnedTranscript R) × Option (Recovery.BucketState (outsideSources R B) R)

/-- Both capped routines run on their own fresh random tapes after the
public center statistics. Their full states are retained; rows within either
state remain arbitrarily correlated. -/
def recoverRowsProgram (R B : Finset V) (d : ℕ) (answers : V → ℝ) :
    RTree (Finset V) ℝ (RecoveryTranscript R B)
      (learnSubgraphBudget R (Schedule.height d) +
        Recovery.recoveryHardCoefficient * 5000 * Fintype.card V) :=
  (centerLearnProgram R d answers).bind fun inside =>
    (outsideRecoveryProgram R B).map fun outside => (inside, outside)

theorem recoverRowsProgram_eval (R B : Finset V) (d : ℕ) (answers : V → ℝ)
    (read : Finset V → ℝ) :
    (recoverRowsProgram R B d answers).eval read =
      ((centerLearnProgram R d answers).eval read).bind fun inside =>
        ((outsideRecoveryProgram R B).eval read).map fun outside => (inside, outside) := by
  simp only [recoverRowsProgram, RTree.eval_bind, RTree.eval_map]

def RecoveredRows (G : SimpleInput V) (S R B : Finset V) (d : ℕ)
    (out : RecoveryTranscript R B) : Prop :=
  CenterRecovered G S R B d out.1 ∧ OutsideRecovered G S R B out.2

/-- The one-quarter bound comes from the two actual sequential calls. No
marginal events of overlapping rows are multiplied. -/
theorem recoverRowsProgram_success (G : SimpleInput V) (S R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) :
    let B := SparseCenters.badRows (SparseCenters.inputRows G) d R
    (1 / 2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ≤
      mass ((recoverRowsProgram R B d ((centerStatistics R).eval G.toWeighted.cut)).eval
        G.toWeighted.cut) (RecoveredRows G S R B d) := by
  intro B
  have hcenter : (1 / 2 : ℝ≥0∞) ≤
      mass ((centerLearnProgram R d ((centerStatistics R).eval G.toWeighted.cut)).eval
        G.toWeighted.cut) (CenterRecovered G S R B d) := by
    have hpred : CenterRecovered G S R B d =
        LearnedResult (Function.Embedding.subtype (· ∈ R)) G (S.subtype (· ∈ R))
          (Schedule.height d) (B ∩ R).card (4 / 5) 800 := by
      funext out
      rfl
    rw [hpred]
    have hh := ENNReal.ofReal_le_ofReal (centerLearnProgram_success_half G S R d hd hgood)
    simpa only [B, ENNReal.ofReal_toReal (mass_ne_top _ _),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hh
  have hout : (1 / 2 : ℝ≥0∞) ≤
      mass ((outsideRecoveryProgram R B).eval G.toWeighted.cut) (OutsideRecovered G S R B) :=
    outsideRecoveryProgram_center_success G S R d hd hgood
  rw [recoverRowsProgram_eval]
  apply (mul_le_mul hcenter le_rfl (by positivity) (by positivity)).trans
  apply recovery_mass_bind_ge _ _ (CenterRecovered G S R B d) _ _
  intro inside _ hinside
  rw [mass_map]
  apply hout.trans
  apply mass_mono
  exact fun outside ho => ⟨hinside, ho⟩

def learnedComponentDrawsProgram (R B : Finset V) (d : ℕ) (answers : V → ℝ) :
    RTree (Finset V) ℝ (RecoveryTranscript R B × (TwoOut.Tape R × (V → Option R)))
      (learnSubgraphBudget R (Schedule.height d) +
        Recovery.recoveryHardCoefficient * 5000 * Fintype.card V) :=
  componentAttachmentAfter (recoverRowsProgram R B d answers) R B
    (fun out => learnedCenterRows R out.1) (fun out => learnedOutsideRows R B out.2)

theorem learnedComponentDrawsProgram_success (G : SimpleInput V) (S R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) (hS : IsMinCut G.toWeighted S) :
    let B := SparseCenters.badRows (SparseCenters.inputRows G) d R
    ((1 / 2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞)) *
        ((ENNReal.ofReal ((1 / 5 : ℝ) ^ 2000) * ENNReal.ofReal (199 / 200 : ℝ)) *
          ENNReal.ofReal ((3 / 10 : ℝ) ^ 115)) ≤
      mass ((learnedComponentDrawsProgram R B d
        ((centerStatistics R).eval G.toWeighted.cut)).eval G.toWeighted.cut) (fun out =>
        RecoveredRows G S R B d out.1 ∧
        IsMinCut ((composedQuotient R out.2.1 out.2.2).graph G.toWeighted)
          (S.image (composedQuotient R out.2.1 out.2.2).map) ∧
        mincutValue ((composedQuotient R out.2.1 out.2.2).graph G.toWeighted) =
          mincutValue G.toWeighted ∧
        2 ≤ Fintype.card
          ((TwoOut.selectedGraph out.2.1).ConnectedComponent ⊕ CenterAttachment.unattached R out.2.2) ∧
        Fintype.card
          ((TwoOut.selectedGraph out.2.1).ConnectedComponent ⊕ CenterAttachment.unattached R out.2.2) * d ≤
            80000 * Fintype.card V) := by
  intro B
  apply (mul_le_mul (recoverRowsProgram_success G S R d hd hgood) le_rfl
    (by positivity) (by positivity)).trans
  apply componentAttachmentAfter_success
    (recoverRowsProgram R B d ((centerStatistics R).eval G.toWeighted.cut)) R B S d
    (fun out => learnedCenterRows R out.1) (fun out => learnedOutsideRows R B out.2)
    G.toWeighted hS hd hgood.1 hgood.2.1 (RecoveredRows G S R B d)
  intro out _ ho
  rcases centerRecovered_properties G S R B d out.1 ho.1 with ⟨hc, hdegree, hzero, hloop⟩
  exact ⟨hc, hdegree, hzero, hloop, outsideRecovered_properties G S R B out.2 ho.2⟩

def middleContinuationBudget (n : ℕ) : ℕ :=
  3 * n + 2 * Recovery.recoveryHardCoefficient * Schedule.insideCoefficient * n +
    Recovery.recoveryHardCoefficient * 5000 * n

theorem middleRowsBudget_le (R : Finset V) (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (hc : Schedule.CenterGuard (Fintype.card V) d R.card) :
    learnSubgraphBudget R (Schedule.height d) +
        Recovery.recoveryHardCoefficient * 5000 * Fintype.card V ≤
      middleContinuationBudget (Fintype.card V) := by
  have hcard := Nat.mul_le_mul_left 3 hc.1
  have hheight := Nat.mul_le_mul_left (2 * Recovery.recoveryHardCoefficient)
    (Schedule.height_centers_le (Fintype.card V) d R.card hd hc)
  unfold learnSubgraphBudget middleContinuationBudget
  rw [Fintype.card_coe]
  nlinarith

structure MiddleTranscript (V : Type) [Fintype V] [DecidableEq V] where
  centers : Finset V
  bad : Finset V
  measured : V → ℝ
  recovery : RecoveryTranscript centers bad
  tape : TwoOut.Tape centers
  attachment : V → Option centers

def MiddleTranscript.quotient (out : MiddleTranscript V) :
    PublicQuotient V ((TwoOut.selectedGraph out.tape).ConnectedComponent ⊕
      CenterAttachment.unattached out.centers out.attachment) :=
  composedQuotient out.centers out.tape out.attachment

/-- The repeated guard is public and proves a fixed linear all-answer cap.
It is already satisfied on every good output of the actual center stage. -/
def middleAfterCenters (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (out : Option (Finset V × Finset V × (V → ℝ))) :
    RTree (Finset V) ℝ (Option (MiddleTranscript V)) (middleContinuationBudget (Fintype.card V)) :=
  match out with
  | none => RTree.pure (PMF.pure none)
  | some (R, B, answers) =>
      if hc : Schedule.CenterGuard (Fintype.card V) d R.card then
        ((learnedComponentDrawsProgram R B d answers).map fun learned =>
          some ⟨R, B, answers, learned.1, learned.2.1, learned.2.2⟩).weaken
            (middleRowsBudget_le R d hd hc)
      else RTree.pure (PMF.pure none)

def middleContractionProgram (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    RTree (Finset V) ℝ (Option (MiddleTranscript V))
      (3 * Fintype.card V + middleContinuationBudget (Fintype.card V)) :=
  (SparseCenters.centersProgram d hd).bind (middleAfterCenters d hd)

theorem middleContractionProgram_every_oracle (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) {out : Option (MiddleTranscript V) × ℕ}
    (hout : out ∈ (RTree.run read (middleContractionProgram (V := V) d hd)).support) :
    out.2 ≤ 3 * Fintype.card V + middleContinuationBudget (Fintype.card V) :=
  RTree.cost_le _ _ hout

def MiddleSuccess (G : WeightedGraph V) (S : Finset V) (d : ℕ)
    (out : Option (MiddleTranscript V)) : Prop :=
  ∃ T, out = some T ∧
    IsMinCut (T.quotient.graph G) (S.image T.quotient.map) ∧
    mincutValue (T.quotient.graph G) = mincutValue G ∧
    2 ≤ Fintype.card ((TwoOut.selectedGraph T.tape).ConnectedComponent ⊕
      CenterAttachment.unattached T.centers T.attachment) ∧
    Fintype.card ((TwoOut.selectedGraph T.tape).ConnectedComponent ⊕
      CenterAttachment.unattached T.centers T.attachment) * d ≤ 80000 * Fintype.card V

theorem middleAfterCenters_success (G : SimpleInput V) (S R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) (hS : IsMinCut G.toWeighted S) :
    ((1 / 2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞)) *
        ((ENNReal.ofReal ((1 / 5 : ℝ) ^ 2000) * ENNReal.ofReal (199 / 200 : ℝ)) *
          ENNReal.ofReal ((3 / 10 : ℝ) ^ 115)) ≤
      mass ((middleAfterCenters d hd (some (R, SparseCenters.badRows
        (SparseCenters.inputRows G) d R, (centerStatistics R).eval G.toWeighted.cut))).eval
          G.toWeighted.cut) (MiddleSuccess G.toWeighted S d) := by
  simp only [middleAfterCenters, dif_pos hgood.1, RTree.eval_weaken, RTree.eval_map, mass_map]
  apply (learnedComponentDrawsProgram_success G S R d hd hgood hS).trans
  apply mass_mono
  intro learned hlearned
  exact ⟨⟨R, SparseCenters.badRows (SparseCenters.inputRows G) d R,
    (centerStatistics R).eval G.toWeighted.cut, learned.1, learned.2.1, learned.2.2⟩,
    rfl, hlearned.2⟩

/-- Actual middle-degree contraction. Original minimum preservation and
the size event are proved together under the complete realized transcript. -/
theorem middleContractionProgram_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hS : IsMinCut G.toWeighted S)
    (hdegree : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v) (hcut : G.toWeighted.cut S < d) :
    ENNReal.ofReal ((1 / 6 : ℝ) * (1 / 5 : ℝ) ^ 2000 * (199 / 200) * (3 / 10 : ℝ) ^ 115) ≤
      mass ((middleContractionProgram (V := V) d hd).eval G.toWeighted.cut)
        (MiddleSuccess G.toWeighted S d) := by
  let Good := fun out : Option (Finset V × Finset V × (V → ℝ)) =>
    ∃ R, SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R ∧
      out = some (R, SparseCenters.badRows (SparseCenters.inputRows G) d R,
        fun v => ((SparseCenters.inputRows G v ∩ R).card : ℝ))
  have hcenter : ENNReal.ofReal (2 / 3 : ℝ) ≤
      mass ((SparseCenters.centersProgram (V := V) d hd).eval G.toWeighted.cut) Good := by
    have hr := SparseCenters.centersProgram_minimum_success G S d hd hS hdegree hcut
    have he := ENNReal.ofReal_le_ofReal hr
    simpa only [ENNReal.ofReal_toReal (mass_ne_top _ _)] using he
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hfactor : ENNReal.ofReal
      ((1 / 6 : ℝ) * (1 / 5 : ℝ) ^ 2000 * (199 / 200) * (3 / 10 : ℝ) ^ 115) =
      ENNReal.ofReal (2 / 3 : ℝ) *
        (((1 / 2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞)) *
          ((ENNReal.ofReal ((1 / 5 : ℝ) ^ 2000) * ENNReal.ofReal (199 / 200 : ℝ)) *
            ENNReal.ofReal ((3 / 10 : ℝ) ^ 115))) := by
    rw [show (1 / 6 : ℝ) * (1 / 5 : ℝ) ^ 2000 * (199 / 200) * (3 / 10 : ℝ) ^ 115 =
      (2 / 3 : ℝ) * (((1 / 2 : ℝ) * (1 / 2)) *
        (((1 / 5 : ℝ) ^ 2000 * (199 / 200)) * (3 / 10 : ℝ) ^ 115)) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 / 3),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (1 / 2) * (1 / 2)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 / 5 : ℝ) ^ 2000 * (199 / 200)),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 / 5 : ℝ) ^ 2000)]
    simp only [hhalf]
  rw [hfactor, middleContractionProgram, RTree.eval_bind]
  apply (mul_le_mul hcenter le_rfl (by positivity) (by positivity)).trans
  apply recovery_mass_bind_ge _ _ Good _ _
  intro out _ hout
  rcases hout with ⟨R, hgood, rfl⟩
  simpa only [SparseCenters.centerStatistics_input_eval] using
    middleAfterCenters_success G S R d hd hgood hS

def MiddleSizeGuard (d : ℕ) (T : MiddleTranscript V) : Prop :=
  2 ≤ Fintype.card ((TwoOut.selectedGraph T.tape).ConnectedComponent ⊕
    CenterAttachment.unattached T.centers T.attachment) ∧
    Fintype.card ((TwoOut.selectedGraph T.tape).ConnectedComponent ⊕
      CenterAttachment.unattached T.centers T.attachment) * d ≤ 80000 * Fintype.card V

def checkMiddleOutput (d : ℕ) (out : Option (MiddleTranscript V)) : Option (MiddleTranscript V) :=
  match out with
  | none => none
  | some T => if MiddleSizeGuard d T then some T else none

theorem checkMiddleOutput_guard (d : ℕ) (out : Option (MiddleTranscript V)) (T : MiddleTranscript V)
    (he : checkMiddleOutput d out = some T) : MiddleSizeGuard d T := by
  cases out with
  | none => simp [checkMiddleOutput] at he
  | some X =>
      by_cases hx : MiddleSizeGuard d X
      · have hXT : X = T := by simpa only [checkMiddleOutput, if_pos hx, Option.some.injEq] using he
        exact hXT ▸ hx
      · simp [checkMiddleOutput, hx] at he

theorem checkMiddleOutput_of_success (G : WeightedGraph V) (S : Finset V) (d : ℕ)
    (out : Option (MiddleTranscript V)) (ho : MiddleSuccess G S d out) :
    checkMiddleOutput d out = out := by
  rcases ho with ⟨T, rfl, _, _, hcard, hsize⟩
  exact if_pos (show MiddleSizeGuard d T from ⟨hcard, hsize⟩)

def checkedMiddleContractionProgram (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    RTree (Finset V) ℝ (Option (MiddleTranscript V))
      (3 * Fintype.card V + middleContinuationBudget (Fintype.card V)) :=
  (middleContractionProgram d hd).map (checkMiddleOutput d)

theorem checkedMiddleContractionProgram_guard (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) (T : MiddleTranscript V)
    (hT : some T ∈ ((checkedMiddleContractionProgram (V := V) d hd).eval read).support) :
    MiddleSizeGuard d T := by
  rw [checkedMiddleContractionProgram, RTree.eval_map] at hT
  obtain ⟨out, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hT
  exact checkMiddleOutput_guard d out T he

theorem checkedMiddleContractionProgram_every_oracle (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) {out : Option (MiddleTranscript V) × ℕ}
    (hout : out ∈ (RTree.run read (checkedMiddleContractionProgram (V := V) d hd)).support) :
    out.2 ≤ 3 * Fintype.card V + middleContinuationBudget (Fintype.card V) :=
  RTree.cost_le _ _ hout

/-- The middle branch's full public guard includes the quotient-cardinality
bound obtained from its constructed surjection. -/
theorem checkedMiddleContractionProgram_scheduleGuard (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) (T : MiddleTranscript V)
    (hT : some T ∈ ((checkedMiddleContractionProgram (V := V) d hd).eval read).support)
    (hdegree : Schedule.DegreeGuard (Fintype.card V) d)
    (hbranch : (d : ℝ) ≤ (Real.log (Fintype.card V)) ^ 10) :
    Schedule.MiddleGuard (Fintype.card V) d
      (Fintype.card ((TwoOut.selectedGraph T.tape).ConnectedComponent ⊕
        CenterAttachment.unattached T.centers T.attachment)) := by
  have hguard := checkedMiddleContractionProgram_guard d hd read T hT
  exact ⟨hdegree, hguard.1, T.quotient.card_le, hguard.2, hbranch⟩

theorem checkedMiddleContractionProgram_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hS : IsMinCut G.toWeighted S)
    (hdegree : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v) (hcut : G.toWeighted.cut S < d) :
    ENNReal.ofReal ((1 / 6 : ℝ) * (1 / 5 : ℝ) ^ 2000 * (199 / 200) * (3 / 10 : ℝ) ^ 115) ≤
      mass ((checkedMiddleContractionProgram (V := V) d hd).eval G.toWeighted.cut)
        (MiddleSuccess G.toWeighted S d) := by
  rw [checkedMiddleContractionProgram, RTree.eval_map, mass_map]
  apply (middleContractionProgram_success G S d hd hS hdegree hcut).trans
  apply mass_mono
  intro out ho
  rwa [checkMiddleOutput_of_success G.toWeighted S d out ho]

end MiddleRecovery

/-- The schedule's numeric parameter is instantiated by the actual proved
bucket program, whose constant is fixed in Recovery.LearnBucket. -/
theorem recoveryHardCoefficient_schedule :
    Recovery.recoveryHardCoefficient = Schedule.recoveryCoefficient Recovery.bucketConstant := rfl

theorem highContraction_budget_le_attempt (n CP : ℕ) :
    3 * n + Recovery.recoveryHardCoefficient * 5000 * n ≤
      Schedule.attemptCoefficient Recovery.bucketConstant CP * n := by
  have hc : 3 + Recovery.recoveryHardCoefficient * 5000 ≤
      Schedule.attemptCoefficient Recovery.bucketConstant CP := by
    rw [recoveryHardCoefficient_schedule]
    unfold Schedule.attemptCoefficient
    nlinarith
  calc
    _ = (3 + Recovery.recoveryHardCoefficient * 5000) * n := by ring
    _ ≤ _ := Nat.mul_le_mul_right n hc

theorem middleContraction_budget_le_attempt (n CP : ℕ) :
    3 * n + middleContinuationBudget n ≤
      Schedule.attemptCoefficient Recovery.bucketConstant CP * n := by
  have hc : 6 + 2 * Recovery.recoveryHardCoefficient * Schedule.insideCoefficient +
      Recovery.recoveryHardCoefficient * 5000 ≤
        Schedule.attemptCoefficient Recovery.bucketConstant CP := by
    rw [recoveryHardCoefficient_schedule]
    unfold Schedule.attemptCoefficient
    nlinarith
  calc
    _ = (6 + 2 * Recovery.recoveryHardCoefficient * Schedule.insideCoefficient +
        Recovery.recoveryHardCoefficient * 5000) * n := by
      unfold middleContinuationBudget
      ring
    _ ≤ _ := Nat.mul_le_mul_right n hc

/-- Exact accounting of the remaining certificate-success factor. This is
only arithmetic; no certificate program or success guarantee is assumed. -/
theorem pStar_eq_middleContraction_times_certificate :
    Schedule.pStar =
      ((1 / 6 : ℝ) * (1 / 5 : ℝ) ^ 2000 * (199 / 200) * (3 / 10 : ℝ) ^ 115) *
        (99 / 100) := by
  unfold Schedule.pStar
  ring

theorem pStar_le_highContraction :
    Schedule.pStar ≤ (1 / 3 : ℝ) * (3 / 10 : ℝ) ^ 115 := by
  have h5 : (1 / 5 : ℝ) ^ 2000 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h30 : 0 ≤ (3 / 10 : ℝ) ^ 115 := by positivity
  unfold Schedule.pStar
  calc
    (1 / 6 : ℝ) * (3 / 10) ^ 115 * (1 / 5) ^ 2000 * (199 / 200) * (99 / 100) ≤
        (1 / 6 : ℝ) * (3 / 10) ^ 115 * 1 * (199 / 200) * (99 / 100) := by
      gcongr
    _ ≤ _ := by nlinarith


#print axioms outsideRecovered_properties
#print axioms learnedOutsideDrawsProgram_success
#print axioms highContractionProgram_every_oracle
#print axioms highAfterCenters_success
#print axioms highContractionProgram_success
#print axioms centerRecovered_properties
#print axioms recoverRowsProgram_eval
#print axioms recoverRowsProgram_success
#print axioms learnedComponentDrawsProgram_success
#print axioms middleRowsBudget_le
#print axioms middleContractionProgram_every_oracle
#print axioms middleAfterCenters_success
#print axioms middleContractionProgram_success
#print axioms checkedHighContractionProgram_guard
#print axioms checkedHighContractionProgram_every_oracle
#print axioms checkedHighContractionProgram_success
#print axioms checkedMiddleContractionProgram_guard
#print axioms checkedMiddleContractionProgram_every_oracle
#print axioms checkedMiddleContractionProgram_success
#print axioms checkedHighContractionProgram_scheduleGuard
#print axioms checkedMiddleContractionProgram_scheduleGuard
#print axioms recoveryHardCoefficient_schedule
#print axioms highContraction_budget_le_attempt
#print axioms middleContraction_budget_le_attempt
#print axioms pStar_eq_middleContraction_times_certificate
#print axioms pStar_le_highContraction

end
end CutQueryComplexity.StarContraction2022.Contraction.Joint
