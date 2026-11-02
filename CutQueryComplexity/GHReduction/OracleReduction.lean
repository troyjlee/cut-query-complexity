import CutQueryComplexity.GHReduction.FrontierReduction
import CutQueryComplexity.Sparsification.WeightedParams

/-! # One public oracle program from sparsification to a witnessed cut tree

This composition executes the existing weighted sparsifier at accuracy one
percent, then feeds its actual output to the adaptive frontier reduction.
Only the supplied canonical weighted s-t family is an algorithmic premise.
All query caps and finite repetition counts are explicit public parameters.
The failure theorem has three terms: initial approximation, executed inner
calls, and unfinished frontier depth. Parameter arithmetic is separate.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability OuterPivot

variable {V : Type} [Fintype V] [DecidableEq V]

def reductionSparsifierBudget (V : Type) [Fintype V] (confidence : ℝ) : ℕ :=
  capQ V (paramρ V confidence) (paramc V confidence (1 / 100))

def reductionSparsifier (V : Type) [Fintype V] (confidence : ℝ) :
    RTree (Finset V) ℝ (Option (WeightedGraph V)) (reductionSparsifierBudget V confidence) :=
  sparsify (paramρ V confidence) (paramc V confidence (1 / 100)) (paramR V confidence)
    ⌈2 * paramc V confidence (1 / 100) * (Fintype.card V : ℝ) ^ 2⌉₊
    (reductionSparsifierBudget V confidence)

def reductionBudget (V : Type) [Fintype V] (M : ℕ) (Q : ℕ → ℕ) (confidence : ℝ)
    (samples trials guideLevels scale exponent levels fuel : ℕ) : ℕ :=
  reductionSparsifierBudget V confidence +
    fuel * frontierRoundBudget M Q (Fintype.card V) samples trials guideLevels scale exponent levels

/-- Chosen before quantifying over the hidden graph. Both `none` and malformed
intermediate outputs have explicit bounded failure branches. -/
def oracleReduction {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (confidence : ℝ) (samples trials guideLevels scale exponent levels fuel : ℕ) (r : V) :
    RTree (Finset V) ℝ (Option (CutTree V))
      (reductionBudget V M Q confidence samples trials guideLevels scale exponent levels fuel) :=
  (reductionSparsifier V confidence).bind (fun output =>
    match output with
    | none => RTree.pure (PMF.pure none)
    | some K => frontierReduction family (Fintype.card V) samples trials guideLevels scale exponent
        levels fuel K le_rfl r)

theorem oracleReduction_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (confidence : ℝ) (samples trials guideLevels scale exponent levels fuel : ℕ) (r : V)
    (read : Finset V → ℝ) {out : Option (CutTree V) × ℕ}
    (hout : out ∈ (RTree.run read (oracleReduction family confidence samples trials guideLevels
      scale exponent levels fuel r)).support) :
    out.2 ≤ reductionBudget V M Q confidence samples trials guideLevels scale exponent levels fuel :=
  RTree.cost_le _ read hout

theorem reductionSparsifier_failure (G : WeightedGraph V) (hn : 1 ≤ Fintype.card V)
    {confidence : ℝ} (hc : 0 ≤ confidence) :
    mass ((reductionSparsifier V confidence).eval G.cut)
      (fun output => ¬∃ K, output = some K ∧
        (∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧ K.cut S ≤ (101 / 100 : ℝ) * G.cut S)) ≤
      ENNReal.ofReal (baseB V ^ (-confidence)) := by
  have he : (inferInstance : DecidableEq V) = Classical.decEq V := Subsingleton.elim _ _
  cases he
  unfold reductionSparsifier reductionSparsifierBudget
  apply le_trans (mass_mono _ ?_)
    (sparsify_whp G hn hc (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num : (1 / 100 : ℝ) ≤ 1))
  intro output hbad hgood
  obtain ⟨K, hK, happrox, _⟩ := hgood
  apply hbad
  refine ⟨K, hK, ?_⟩
  simpa only [show (1 : ℝ) - 1 / 100 = 99 / 100 by norm_num,
    show (1 : ℝ) + 1 / 100 = 101 / 100 by norm_num] using happrox.2

theorem oracleReduction_failure_le {M scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular (Fintype.card V) Q)
    (hnscale : Fintype.card V ≤ scale) (confidence : ℝ) (hc : 0 ≤ confidence)
    (samples trials guideLevels exponent levels fuel : ℕ)
    (hguideLevels : thresholdLevels (Fintype.card V) ≤ guideLevels)
    (hpivotLevels : thresholdLevels (Fintype.card V) ≤ levels)
    (r : V) (G : WeightedGraph V) (hG : InputPromise M G) :
    mass ((oracleReduction family confidence samples trials guideLevels scale exponent levels fuel r).eval G.cut)
      (fun output => ¬TreeOutputSuccess G output) ≤
      ENNReal.ofReal (baseB V ^ (-confidence)) +
        ((fuel : ℝ≥0∞) * ((Fintype.card V : ℝ≥0∞) *
          singleSourceError M (Fintype.card V) samples trials scale exponent) +
          (Fintype.card V : ℝ≥0∞) * (contractionRate levels ^ fuel * (Fintype.card V : ℝ≥0∞))) := by
  haveI : Nonempty V := ⟨r⟩
  unfold oracleReduction reductionBudget
  rw [RTree.eval_bind]
  apply mass_bind_le_add _ _
    (fun output => ¬∃ K, output = some K ∧
      (∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧ K.cut S ≤ (101 / 100 : ℝ) * G.cut S)) _
    (reductionSparsifier_failure G Fintype.card_pos hc)
  intro output hgood
  obtain ⟨K, rfl, happrox⟩ := not_not.mp hgood
  exact frontierReduction_failure_le family hQ Fintype.card_pos hnscale samples trials guideLevels
    exponent levels fuel hguideLevels hpivotLevels G K hG le_rfl r happrox

theorem oracleReduction_depthFuel_failure {M scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular (Fintype.card V) Q)
    (hnscale : Fintype.card V ≤ scale) (confidence : ℝ) (hc : 0 ≤ confidence)
    (samples trials guideLevels exponent levels : ℕ)
    (hguideLevels : thresholdLevels (Fintype.card V) ≤ guideLevels)
    (hpivotLevels : thresholdLevels (Fintype.card V) ≤ levels)
    (r : V) (G : WeightedGraph V) (hG : InputPromise M G) {failure : ℝ} (hf : 0 < failure) :
    mass ((oracleReduction family confidence samples trials guideLevels scale exponent levels
      (depthFuel levels (Fintype.card V * Fintype.card V) failure) r).eval G.cut)
      (fun output => ¬TreeOutputSuccess G output) ≤
      ENNReal.ofReal (baseB V ^ (-confidence)) +
        ((depthFuel levels (Fintype.card V * Fintype.card V) failure : ℝ≥0∞) *
          ((Fintype.card V : ℝ≥0∞) * singleSourceError M (Fintype.card V) samples trials scale exponent) +
          ENNReal.ofReal failure) := by
  haveI : Nonempty V := ⟨r⟩
  unfold oracleReduction reductionBudget
  rw [RTree.eval_bind]
  apply mass_bind_le_add _ _
    (fun output => ¬∃ K, output = some K ∧
      (∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧ K.cut S ≤ (101 / 100 : ℝ) * G.cut S)) _
    (reductionSparsifier_failure G Fintype.card_pos hc)
  intro output hgood
  obtain ⟨K, rfl, happrox⟩ := not_not.mp hgood
  exact frontierReduction_depthFuel_failure family hQ Fintype.card_pos hnscale samples trials guideLevels
    exponent levels hguideLevels hpivotLevels G K hG le_rfl r happrox hf

end
end CutQueryComplexity.GHReduction
