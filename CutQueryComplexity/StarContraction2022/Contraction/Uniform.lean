import CutQueryComplexity.StarContraction2022.Contraction.Joint.Recovery
import CutQueryComplexity.StarContraction2022.Common.Threshold

/-! # Actual public contractions for the uniform linear-query algorithm

The constructors below retain the full producer transcripts. Only the theorems
mention the hidden graph or a minimum shore. Equality of minimum values yields
an actual lifted minimum respecting the public quotient; it is not an extra
assumption about a chosen original minimum.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022

noncomputable section
open scoped Classical ENNReal
open CutQueryComplexity.Probability

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]

namespace PublicQuotient

theorem lift_minimum_of_value_eq (π : PublicQuotient V Q) {G : WeightedGraph V}
    (he : mincutValue (π.graph G) = mincutValue G) {T : Finset Q}
    (hT : IsMinCut (π.graph G) T) : IsMinCut G (π.lift T) := by
  refine ⟨π.proper_lift hT.1, fun U hU => ?_⟩
  calc
    G.cut (π.lift T) = (π.graph G).cut T := (π.cut_graph G T).symm
    _ = mincutValue (π.graph G) := cut_eq_mincut_of_isMinCut hT
    _ = mincutValue G := he
    _ ≤ G.cut U := mincutValue_le G hU

/-- This selector occurs only in a proof. The query program receives neither
the hidden graph nor the resulting shore. -/
theorem exists_respecting_minimum_of_value_eq (π : PublicQuotient V Q)
    (hq : 2 ≤ Fintype.card Q) {G : WeightedGraph V}
    (he : mincutValue (π.graph G) = mincutValue G) :
    ∃ S, IsMinCut G S ∧ RespectsBlocks π.map S := by
  refine ⟨π.lift (explicitMinimum hq (π.graph G)), ?_, π.respects_lift _⟩
  exact π.lift_minimum_of_value_eq he (explicitMinimum_spec hq (π.graph G))

end PublicQuotient

namespace CutResult

def Optimal (G : WeightedGraph V) (out : CutResult V) : Prop :=
  out.Sound G ∧ IsMinCut G out.shore ∧ out.value = mincutValue G

theorem optimal_of_sound_value {G : WeightedGraph V} {out : CutResult V}
    (hs : out.Sound G) (hv : out.value = mincutValue G) : Optimal G out := by
  refine ⟨hs, ⟨hs.1, fun S hS => ?_⟩, hv⟩
  rw [← hs.2, hv]
  exact mincutValue_le G hS

end CutResult

def FoundMinimum (G : WeightedGraph V) (o : Option (CutResult V)) : Prop :=
  ∃ out, o = some out ∧ CutResult.Optimal G out

namespace Contraction.Uniform

abbrev highBudget (n : ℕ) : ℕ :=
  3 * n + Recovery.recoveryHardCoefficient * 5000 * n

abbrev middleBudget (n : ℕ) : ℕ := 3 * n + Joint.middleContinuationBudget n

/-- Both aliases are the actual capped producer, with no supplied solver. -/
def highProgram (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    RTree (Finset V) ℝ (Option (Joint.HighTranscript V)) (highBudget (Fintype.card V)) :=
  Joint.checkedHighContractionProgram d hd

def HighPreserves (G : WeightedGraph V) (out : Option (Joint.HighTranscript V)) : Prop :=
  ∃ T, out = some T ∧
    2 ≤ Fintype.card (T.centers ⊕ Joint.CenterAttachment.unattached T.centers T.attachment) ∧
    mincutValue (T.quotient.graph G) = mincutValue G

theorem highProgram_guard (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) (T : Joint.HighTranscript V)
    (hT : some T ∈ ((highProgram (V := V) d hd).eval read).support)
    (hdegree : Schedule.DegreeGuard (Fintype.card V) d)
    (hbranch : (Real.log (Fintype.card V)) ^ 10 < (d : ℝ)) :
    Schedule.HighGuard (Fintype.card V) d
      (Fintype.card (T.centers ⊕ Joint.CenterAttachment.unattached T.centers T.attachment)) :=
  Joint.checkedHighContractionProgram_scheduleGuard d hd read T hT hdegree hbranch

theorem highProgram_every_oracle (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) {out : Option (Joint.HighTranscript V) × ℕ}
    (hout : out ∈ (RTree.run read (highProgram (V := V) d hd)).support) :
    out.2 ≤ highBudget (Fintype.card V) := RTree.cost_le _ _ hout

theorem highProgram_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hS : IsMinCut G.toWeighted S)
    (hdegree : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v) (hcut : G.toWeighted.cut S < d) :
    ENNReal.ofReal ((1 / 3 : ℝ) * (3 / 10 : ℝ) ^ 115) ≤
      mass ((highProgram (V := V) d hd).eval G.toWeighted.cut)
        (HighPreserves G.toWeighted) := by
  apply (Joint.checkedHighContractionProgram_success G S d hd hS hdegree hcut).trans
  apply mass_mono
  rintro out ⟨T, rfl, _, he, hq, _⟩
  exact ⟨T, rfl, hq, he⟩

variable [LinearOrder V]

def middleProgram (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    RTree (Finset V) ℝ (Option (Joint.MiddleTranscript V)) (middleBudget (Fintype.card V)) :=
  Joint.checkedMiddleContractionProgram d hd

def MiddlePreserves (G : WeightedGraph V) (out : Option (Joint.MiddleTranscript V)) : Prop :=
  ∃ T, out = some T ∧
    2 ≤ Fintype.card ((TwoOut.selectedGraph T.tape).ConnectedComponent ⊕
      Joint.CenterAttachment.unattached T.centers T.attachment) ∧
    mincutValue (T.quotient.graph G) = mincutValue G

theorem middleProgram_guard (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) (T : Joint.MiddleTranscript V)
    (hT : some T ∈ ((middleProgram (V := V) d hd).eval read).support)
    (hdegree : Schedule.DegreeGuard (Fintype.card V) d)
    (hbranch : (d : ℝ) ≤ (Real.log (Fintype.card V)) ^ 10) :
    Schedule.MiddleGuard (Fintype.card V) d
      (Fintype.card ((TwoOut.selectedGraph T.tape).ConnectedComponent ⊕
        Joint.CenterAttachment.unattached T.centers T.attachment)) :=
  Joint.checkedMiddleContractionProgram_scheduleGuard d hd read T hT hdegree hbranch

theorem middleProgram_every_oracle (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) {out : Option (Joint.MiddleTranscript V) × ℕ}
    (hout : out ∈ (RTree.run read (middleProgram (V := V) d hd)).support) :
    out.2 ≤ middleBudget (Fintype.card V) := RTree.cost_le _ _ hout

theorem middleProgram_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hS : IsMinCut G.toWeighted S)
    (hdegree : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v) (hcut : G.toWeighted.cut S < d) :
    ENNReal.ofReal ((1 / 6 : ℝ) * (1 / 5 : ℝ) ^ 2000 * (199 / 200) *
      (3 / 10 : ℝ) ^ 115) ≤
      mass ((middleProgram (V := V) d hd).eval G.toWeighted.cut)
        (MiddlePreserves G.toWeighted) := by
  apply (Joint.checkedMiddleContractionProgram_success G S d hd hS hdegree hcut).trans
  apply mass_mono
  rintro out ⟨T, rfl, _, he, hq, _⟩
  exact ⟨T, rfl, hq, he⟩

end Contraction.Uniform

#print axioms PublicQuotient.lift_minimum_of_value_eq
#print axioms PublicQuotient.exists_respecting_minimum_of_value_eq
#print axioms CutResult.optimal_of_sound_value
#print axioms Contraction.Uniform.highProgram_guard
#print axioms Contraction.Uniform.highProgram_every_oracle
#print axioms Contraction.Uniform.highProgram_success
#print axioms Contraction.Uniform.middleProgram_guard
#print axioms Contraction.Uniform.middleProgram_every_oracle
#print axioms Contraction.Uniform.middleProgram_success

end
end CutQueryComplexity.StarContraction2022
