import CutQueryComplexity.GHReduction.FrontierConditionalProgress
import CutQueryComplexity.GHReduction.FrontierAssemblyProgram

/-! # Termination of the actual finite adaptive frontier execution

Each fixed original vertex has an excess potential, killed when any executed
round fails. Conditional one-step progress applies at the actual next state.
The induction follows the implemented binds and charges failed rounds through
the existing failure theorem. A finite union over original vertices then
bounds the probability of a nonsingleton final block. Empty split rounds still
consume fuel, and no query-budget loss is introduced by this depth argument.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators ENNReal
open WeightedGraph Probability OuterPivot

variable {V : Type} [Fintype V] [DecidableEq V]

def frontierTracePotential (G : WeightedGraph V) {levels : ℕ}
    (trace : FrontierTrace V levels) (v : V) : ℕ :=
  if trace.Good G then frontierVertexExcess trace.endState v else 0

theorem frontierTrace_good_cons (G : WeightedGraph V) {levels : ℕ}
    (record : FrontierRoundRecord V levels) (tail : FrontierTrace V levels) :
    (⟨tail.endState, record :: tail.records⟩ : FrontierTrace V levels).Good G ↔
      record.Good G ∧ tail.Good G := by
  simp [FrontierTrace.Good]

theorem frontierTracePotential_cons (G : WeightedGraph V) {levels : ℕ}
    (record : FrontierRoundRecord V levels) (tail : FrontierTrace V levels) (v : V) :
    frontierTracePotential G ⟨tail.endState, record :: tail.records⟩ v =
      if record.Good G then frontierTracePotential G tail v else 0 := by
  unfold frontierTracePotential
  rw [frontierTrace_good_cons]
  by_cases hr : record.Good G <;> by_cases ht : tail.Good G <;> simp [hr, ht]

theorem frontierExecution_expected_potential {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (fuel : ℕ) (state : PublicFrontierState V) (v : V) :
    expect ((frontierExecution family n samples trials guideLevels scale exponent levels
      K hvn fuel state).eval G.cut) (fun trace => (frontierTracePotential G trace v : ℝ≥0∞)) ≤
      contractionRate levels ^ fuel * (frontierVertexExcess state v : ℝ≥0∞) := by
  induction fuel generalizing state with
  | zero => simp [frontierExecution, frontierTracePotential, FrontierTrace.Good]
  | succ fuel ih =>
      simp only [frontierExecution, RTree.eval_cast, RTree.eval_bind, expect_bind,
        RTree.eval_map, expect_map]
      calc
        _ ≤ expect ((frontierStateStep family n samples trials guideLevels scale exponent levels
            K hvn state).eval G.cut)
            (fun record => contractionRate levels ^ fuel * (frontierRoundPotential G record v : ℝ≥0∞)) := by
          apply expect_mono_on_support
          intro record _
          by_cases hr : record.Good G
          · simpa only [frontierTracePotential_cons, if_pos hr, frontierRoundPotential,
              if_pos hr] using ih record.after
          · simp only [frontierTracePotential_cons, if_neg hr, frontierRoundPotential,
              if_neg hr, Nat.cast_zero, expect_const, mul_zero, le_refl]
        _ = contractionRate levels ^ fuel *
            expect ((frontierStateStep family n samples trials guideLevels scale exponent levels
              K hvn state).eval G.cut) (fun record => (frontierRoundPotential G record v : ℝ≥0∞)) :=
          expect_const_mul _ _ _
        _ ≤ contractionRate levels ^ fuel *
            (contractionRate levels * (frontierVertexExcess state v : ℝ≥0∞)) :=
          mul_le_mul' le_rfl (frontierStateStep_expected_potential family hQ samples trials guideLevels
            scale exponent levels hlevels G K hG hvn state v)
        _ = _ := by rw [pow_succ, mul_assoc]

theorem frontierExecution_vertex_tail {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (fuel : ℕ) (state : PublicFrontierState V) (v : V) :
    mass ((frontierExecution family n samples trials guideLevels scale exponent levels
      K hvn fuel state).eval G.cut)
      (fun trace => trace.Good G ∧ 0 < frontierVertexExcess trace.endState v) ≤
      contractionRate levels ^ fuel * (n : ℝ≥0∞) := by
  have hmarkov := mul_mass_le_expect
    ((frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel state).eval G.cut)
    (fun trace => trace.Good G ∧ 0 < frontierVertexExcess trace.endState v)
    (fun trace => (frontierTracePotential G trace v : ℝ≥0∞)) 1 (by
      intro trace _ htrace
      rw [frontierTracePotential, if_pos htrace.1]
      exact_mod_cast Nat.succ_le_of_lt htrace.2)
  rw [one_mul] at hmarkov
  apply (hmarkov.trans (frontierExecution_expected_potential family hQ samples trials guideLevels
    scale exponent levels hlevels G K hG hvn fuel state v)).trans
  apply mul_le_mul' le_rfl
  exact_mod_cast (Nat.sub_le (fiber state.block (state.block v)).card 1).trans
    ((Finset.card_le_univ _).trans hvn)

theorem exists_vertex_excess_of_not_discrete (state : PublicFrontierState V)
    (hbad : ¬state.Discrete) : ∃ v, 0 < frontierVertexExcess state v := by
  change ¬∀ b, (fiber state.block b).card = 1 at hbad
  obtain ⟨b, hb⟩ := not_forall.mp hbad
  obtain ⟨v, hv⟩ := state.onto b
  have hpos : 0 < (fiber state.block b).card :=
    Finset.card_pos.mpr (frontier_fiber_nonempty state.block state.onto b)
  refine ⟨v, ?_⟩
  simp only [frontierVertexExcess, excess, hv]
  omega

theorem frontierExecution_good_depth_tail {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (fuel : ℕ) (state : PublicFrontierState V) :
    mass ((frontierExecution family n samples trials guideLevels scale exponent levels
      K hvn fuel state).eval G.cut) (fun trace => trace.Good G ∧ ¬trace.endState.Discrete) ≤
      (n : ℝ≥0∞) * (contractionRate levels ^ fuel * (n : ℝ≥0∞)) := by
  let P := (frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel state).eval G.cut
  calc
    _ ≤ mass P (fun trace => ∃ v ∈ (Finset.univ : Finset V),
        trace.Good G ∧ 0 < frontierVertexExcess trace.endState v) := by
      apply mass_mono
      intro trace htrace
      obtain ⟨v, hv⟩ := exists_vertex_excess_of_not_discrete trace.endState htrace.2
      exact ⟨v, Finset.mem_univ v, htrace.1, hv⟩
    _ ≤ ∑ v : V, mass P (fun trace => trace.Good G ∧ 0 < frontierVertexExcess trace.endState v) :=
      mass_exists_finset_le P Finset.univ _
    _ ≤ ∑ _v : V, contractionRate levels ^ fuel * (n : ℝ≥0∞) :=
      Finset.sum_le_sum (fun v _ => frontierExecution_vertex_tail family hQ samples trials guideLevels
        scale exponent levels hlevels G K hG hvn fuel state v)
    _ = (Fintype.card V : ℝ≥0∞) * (contractionRate levels ^ fuel * (n : ℝ≥0∞)) := by simp
    _ ≤ _ := mul_le_mul' (Nat.cast_le.mpr hvn) le_rfl

theorem frontierExecution_termination_failure {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 0 < n) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent levels : ℕ)
    (hguideLevels : thresholdLevels n ≤ guideLevels) (hpivotLevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧ K.cut S ≤ (101 / 100 : ℝ) * G.cut S)
    (fuel : ℕ) (state : PublicFrontierState V) :
    mass ((frontierExecution family n samples trials guideLevels scale exponent levels
      K hvn fuel state).eval G.cut) (fun trace => ¬(trace.Good G ∧ trace.endState.Discrete)) ≤
      (fuel : ℝ≥0∞) * ((n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent) +
        (n : ℝ≥0∞) * (contractionRate levels ^ fuel * (n : ℝ≥0∞)) := by
  let P := (frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel state).eval G.cut
  calc
    _ ≤ mass P (fun trace => ¬trace.Good G ∨ (trace.Good G ∧ ¬trace.endState.Discrete)) := by
      apply mass_mono
      intro trace hbad
      by_cases hg : trace.Good G
      · exact Or.inr ⟨hg, fun hd => hbad ⟨hg, hd⟩⟩
      · exact Or.inl hg
    _ ≤ mass P (fun trace => ¬trace.Good G) + mass P (fun trace => trace.Good G ∧ ¬trace.endState.Discrete) :=
      mass_or_le P _ _
    _ ≤ _ := add_le_add
      (frontierExecution_failure_le family hQ hn hnscale samples trials guideLevels exponent levels
        hguideLevels G K hG hvn happrox fuel state)
      (frontierExecution_good_depth_tail family hQ samples trials guideLevels scale exponent levels
        hpivotLevels G K hG hvn fuel state)

theorem frontierExecution_depthFuel {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (state : PublicFrontierState V) {failure : ℝ} (hf : 0 < failure) :
    mass ((frontierExecution family n samples trials guideLevels scale exponent levels
      K hvn (depthFuel levels (n * n) failure) state).eval G.cut)
      (fun trace => trace.Good G ∧ ¬trace.endState.Discrete) ≤ ENNReal.ofReal failure := by
  apply (frontierExecution_good_depth_tail family hQ samples trials guideLevels scale exponent levels
    hlevels G K hG hvn _ state).trans
  calc
    _ = contractionRate levels ^ depthFuel levels (n * n) failure * ((n * n : ℕ) : ℝ≥0∞) := by
      rw [Nat.cast_mul]
      ac_rfl
    _ ≤ ENNReal.ofReal (Real.exp (-(depthFuel levels (n * n) failure : ℝ) /
          (removalDenominator levels : ℝ))) * ((n * n : ℕ) : ℝ≥0∞) :=
      mul_le_mul' (contractionRate_pow_le_exp levels _) le_rfl
    _ ≤ _ := by
      rw [show ((n * n : ℕ) : ℝ≥0∞) = ENNReal.ofReal (n * n : ℕ) by simp,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (depthFuel_error_le levels (n * n) hf)

end
end CutQueryComplexity.GHReduction
