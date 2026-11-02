import CutQueryComplexity.StarContraction2022.Contraction.Uniform
import CutQueryComplexity.StarContraction2022.Adapters.Weighted

/-! # The high-degree branch composed from actual programs

The second randomized routine is chosen from the complete returned transcript.
The probability argument is pointwise after fixing that transcript and does not
assert independence of recovered rows or condition on a global cap event.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Randomized

noncomputable section
open scoped Classical ENNReal
open CutQueryComplexity.Probability CutQueryComplexity.StarContraction2022.Contraction

/-- The output includes a real-valued verified cut, so the probability
composition is proved for arbitrary discrete PMFs, without a finite-output
instance. It still fixes the complete first transcript before the second bound. -/
theorem mass_bind_ge_countable {α β : Type*} (p : PMF α) (next : α → PMF β)
    (Good : α → Prop) (Success : β → Prop) (c : ℝ≥0∞)
    (h : ∀ a ∈ p.support, Good a → c ≤ mass (next a) Success) :
    mass p Good * c ≤ mass (p.bind next) Success := by
  rw [mass_eq_tsum, mass_bind, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : Good a
  · simp only [ha, ite_true]
    by_cases hs : a ∈ p.support
    · exact mul_le_mul le_rfl (h a hs ha) (by positivity) (by positivity)
    · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
      simp [hz]
  · simp [ha]

variable {V : Type} [Fintype V] [DecidableEq V]

theorem ninetyNine_of_failure {α : Type} (p : PMF α) (P : α → Prop)
    (h : mass p (fun x => ¬ P x) ≤ ENNReal.ofReal (1 / 100)) :
    ENNReal.ofReal (99 / 100) ≤ mass p P := by
  have hs := success_of_failure_le p P (by norm_num : (0 : ℝ) ≤ 1 / 100) h
  have hr : (99 / 100 : ℝ) ≤ (mass p P).toReal := by linarith
  simpa only [ENNReal.ofReal_toReal (mass_ne_top p P)] using ENNReal.ofReal_le_ofReal hr

def highContinuation (d : ℕ) (out : Option (Joint.HighTranscript V)) :
    RTree (Finset V) ℝ (Option (CutResult V))
      (Schedule.weightedCoefficient * Fintype.card V + 1) :=
  match out with
  | none => RTree.pure (PMF.pure none)
  | some T => WeightedAdapter.guardedProgram T.quotient d

def highBudget (n : ℕ) : ℕ :=
  Uniform.highBudget n + (Schedule.weightedCoefficient * n + 1)

def highProgram (d : ℕ) (hd : Schedule.degreeCutoff ≤ d) :
    RTree (Finset V) ℝ (Option (CutResult V)) (highBudget (Fintype.card V)) :=
  (Uniform.highProgram d hd).bind (highContinuation d)

theorem highProgram_every_oracle (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (read : Finset V → ℝ) {out : Option (CutResult V) × ℕ}
    (hout : out ∈ (RTree.run read (highProgram (V := V) d hd)).support) :
    out.2 ≤ highBudget (Fintype.card V) := RTree.cost_le _ _ hout

theorem highContinuation_sound (d : ℕ) (T : Option (Joint.HighTranscript V))
    (G : WeightedGraph V) {out : CutResult V}
    (hout : some out ∈ ((highContinuation d T).eval G.cut).support) : out.Sound G := by
  cases T with
  | none => simp [highContinuation] at hout
  | some T => exact WeightedAdapter.guardedProgram_sound T.quotient d G hout

theorem highProgram_sound (d : ℕ) (hd : Schedule.degreeCutoff ≤ d)
    (G : WeightedGraph V) {out : CutResult V}
    (hout : some out ∈ ((highProgram (V := V) d hd).eval G.cut).support) :
    out.Sound G := by
  change some out ∈ (((Uniform.highProgram (V := V) d hd).bind
    (highContinuation d)).eval G.cut).support at hout
  rw [RTree.eval_bind, PMF.mem_support_bind_iff] at hout
  obtain ⟨T, _, hT⟩ := hout
  exact highContinuation_sound d T G hT

theorem highContinuation_success (G : SimpleInput V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (hdegree : Schedule.DegreeGuard (Fintype.card V) d)
    (hbranch : (Real.log (Fintype.card V)) ^ 10 < (d : ℝ))
    (T : Option (Joint.HighTranscript V))
    (hT : T ∈ ((Uniform.highProgram (V := V) d hd).eval G.toWeighted.cut).support)
    (hgood : Uniform.HighPreserves G.toWeighted T) :
    ENNReal.ofReal (99 / 100) ≤
      mass ((highContinuation d T).eval G.toWeighted.cut) (FoundMinimum G.toWeighted) := by
  obtain ⟨T, rfl, hq, he⟩ := hgood
  have hg := Uniform.highProgram_guard d hd G.toWeighted.cut T hT hdegree hbranch
  obtain ⟨S, hS, hs⟩ := T.quotient.exists_respecting_minimum_of_value_eq hq he
  apply ninetyNine_of_failure
  exact WeightedAdapter.guardedProgram_failure T.quotient d hn hg G.toWeighted hS hs

theorem pStar_le_high_times_certificate :
    Schedule.pStar ≤ ((1 / 3 : ℝ) * (3 / 10 : ℝ) ^ 115) * (99 / 100) := by
  have h5 : (1 / 5 : ℝ) ^ 2000 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h30 : 0 ≤ (3 / 10 : ℝ) ^ 115 := by positivity
  unfold Schedule.pStar
  calc
    (1 / 6 : ℝ) * (3 / 10) ^ 115 * (1 / 5) ^ 2000 * (199 / 200) * (99 / 100) ≤
        (1 / 6 : ℝ) * (3 / 10) ^ 115 * 1 * (199 / 200) * (99 / 100) := by gcongr
    _ ≤ _ := by nlinarith

/-- The complete high branch loses only the actual weighted solver's one
percent failure, after the actual contraction transcript is fixed. -/
theorem highProgram_success (G : SimpleInput V) (S : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d) (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (hdegree : Schedule.DegreeGuard (Fintype.card V) d)
    (hbranch : (Real.log (Fintype.card V)) ^ 10 < (d : ℝ))
    (hS : IsMinCut G.toWeighted S) (hdeg : ∀ v, (d : ℝ) ≤ G.toWeighted.degree v)
    (hcut : G.toWeighted.cut S < d) :
    ENNReal.ofReal Schedule.pStar ≤
      mass ((highProgram (V := V) d hd).eval G.toWeighted.cut) (FoundMinimum G.toWeighted) := by
  apply (ENNReal.ofReal_le_ofReal pStar_le_high_times_certificate).trans
  rw [ENNReal.ofReal_mul (by positivity)]
  apply (mul_le_mul_of_nonneg_right (Uniform.highProgram_success G S d hd hS hdeg hcut)
    (by positivity)).trans
  change _ ≤ mass (((Uniform.highProgram (V := V) d hd).bind
    (highContinuation d)).eval G.toWeighted.cut) (FoundMinimum G.toWeighted)
  rw [RTree.eval_bind]
  apply mass_bind_ge_countable
  intro T hT hgood
  exact highContinuation_success G d hd hn hdegree hbranch T hT hgood

#print axioms mass_bind_ge_countable
#print axioms ninetyNine_of_failure
#print axioms highProgram_every_oracle
#print axioms highProgram_sound
#print axioms highContinuation_success
#print axioms pStar_le_high_times_certificate
#print axioms highProgram_success

end
end CutQueryComplexity.StarContraction2022.Randomized
