import CutQueryComplexity.StarContraction2022.Quantum.Global.Program
import CutQueryComplexity.StarContraction2022.Quantum.Global.Success
import CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds

/-! # The public quantum global-mincut endpoint

The same accepted native circuit has a fixed, fully charged query schedule,
arbitrary-answer normalization, truthful original candidates and minimum-cut
success at least two thirds. The exact bound uses `logWidth n` to the fifth
power. Its conventional natural-log comparison is derived below; neither is
the earlier paper's log-power-ten accounting. No constructor is changed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Global
noncomputable section
open QuantumQueryComplexity ProductPrograms
open scoped Classical Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

/-- Exact match to the accepted numerical sum, with every verification retained. -/
theorem native_schedule_matches {n : ℕ} (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    (globalRoutine n t K ht eta).len = CostBounds.combinedQueries n t K eta := by
  simp only [globalRoutine_len, globalQueries, ite_eq_left hn, jointQueries,
    lowQueries, highQueries, CostBounds.combinedQueries]

/-- Tiny inputs retain the original zero-query branch. -/
theorem native_schedule_all (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    (globalRoutine n t K ht eta).len =
      if 2 ≤ n then CostBounds.combinedQueries n t K eta else 0 := rfl

/-- One explicit positive coefficient, fixed before the input size and graph. -/
def logFiveCoefficient : ℝ := CostBounds.coefficient 12 publicHighTrials (1 / 3)

theorem logFiveCoefficient_eq : logFiveCoefficient =
    819205 * 12 + 70860 * (1 + Real.log 3) ^ 2 + 600000000000 * (publicHighTrials : ℝ) := by
  norm_num [logFiveCoefficient, CostBounds.coefficient]

theorem logFiveCoefficient_pos : 0 < logFiveCoefficient :=
  CostBounds.coefficient_pos (by norm_num) _ _

theorem globalRoutine_logFive_cost (n : ℕ) :
    ((globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).len : ℝ) ≤
      logFiveCoefficient * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 := by
  by_cases hn : 2 ≤ n
  · rw [native_schedule_matches hn]
    exact CostBounds.combinedQueries_le hn (by norm_num) publicHighTrials (by norm_num) (by norm_num)
  · rw [native_schedule_all, ite_eq_right hn, Nat.cast_zero]
    have hc := logFiveCoefficient_pos.le
    positivity

/-- Every honest candidate reports the exact original value, including failed
minimum-search histories; no size or success premise is needed for truthfulness. -/
theorem public_candidate_truthful (n : ℕ) (G : CapacityGraph (Fin n) 1)
    (S : Finset (Fin n)) (a : CutAnswer n 1)
    (h : 0 < (globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).prob (capacityRead G)
      (globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).len (some (S, a))) :
    ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S :=
  globalAlg_sound _ _ _ _ _ G (some (S, a)) h

/-- Literal minimum-shore/value event in the actual final Born state. -/
theorem public_minimum_shore_value (n : ℕ) (G : CapacityGraph (Fin n) 1) (hn : 2 ≤ n) :
    2 / 3 ≤ goodProb (globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).readout
      (fun c => ∃ S a, c = some (S, a) ∧ IsMinCut G.toWeighted S ∧
        decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
      ((globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).run (capacityRead G) *ᵥ
        (globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).init) := by
  apply (globalRoutine_public_success n G hn).trans_eq
  rw [goodProb_eq_sum_ite, goodProb_eq_sum_ite]
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg
    (fun d : Decidable (Forest.LowMinimumCandidate G
      ((globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).readout b)) =>
      @ite ℝ (Forest.LowMinimumCandidate G
        ((globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).readout b)) d
        (Complex.normSq (((globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).run
          (capacityRead G) *ᵥ (globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).init) b)) 0)
    (Subsingleton.elim _ _)

theorem public_tiny_input {n : ℕ} (hn : n < 2) :
    (globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).len = 0 ∧
      ∀ read : AnswerTable n,
        (globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).prob read
          (globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).len none = 1 := by
  have hlen := (global_small hn 12 publicHighTrials (by norm_num) (1 / 3) (fun _ => 0)).1
  refine ⟨hlen, fun read => ?_⟩
  rw [hlen]
  exact (global_small hn 12 publicHighTrials (by norm_num) (1 / 3) read).2

/-- Production export of the accepted same-circuit log-power-five endpoint.
The positive constant precedes every n; the named circuit precedes every graph.
No cost, probability, row-independence or producer-success premise is supplied. -/
theorem public_log_five_endpoint :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      let T := globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)
      let R := globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)
      R.len = (if 2 ≤ n then CostBounds.combinedQueries n 12 publicHighTrials (1 / 3) else 0) ∧
      (R.len : ℝ) ≤ C * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 ∧
      T.step = R.step ∧
      (∀ read : AnswerTable n, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ (G : CapacityGraph (Fin n) 1) (S : Finset (Fin n)) (a : CutAnswer n 1),
        0 < T.prob (capacityRead G) R.len (some (S, a)) →
          ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S) ∧
      (∀ G : CapacityGraph (Fin n) 1, 2 ≤ n →
        2 / 3 ≤ goodProb T.readout
          (fun c => ∃ S a, c = some (S, a) ∧ IsMinCut G.toWeighted S ∧
            decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
          (R.run (capacityRead G) *ᵥ T.init)) ∧
      (n < 2 → R.len = 0 ∧ ∀ read : AnswerTable n, T.prob read R.len none = 1) := by
  refine ⟨logFiveCoefficient, logFiveCoefficient_pos, fun n => ?_⟩
  dsimp only
  exact ⟨native_schedule_all _ _ _ _ _, globalRoutine_logFive_cost n, rfl,
    fun read => ⟨globalRoutine_state _ _ _ _ _ read, globalRoutine_normalized _ _ _ _ _ read⟩,
    public_candidate_truthful n, public_minimum_shore_value n, public_tiny_input⟩

/-- The upper binary logarithm is controlled by the square of 2n; all ceilings
are handled by the accepted discrete power bound. -/
theorem pow_logWidth_le_square {n : ℕ} (hn : 2 ≤ n) :
    2 ^ logWidth n ≤ (2 * n) ^ 2 := by
  calc
    _ = 2 * 2 ^ Nat.clog 2 (n + 2) := by simp [logWidth, Nat.pow_add]
    _ ≤ 2 * (2 * (n + 2)) :=
      Nat.mul_le_mul_left 2 (Forest.pow_clog_le_twice (n + 2) (by omega))
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_right n hn]

/-- Explicit conversion to the conventional natural logarithm, for n>=2. -/
theorem logWidth_le_four_log {n : ℕ} (hn : 2 ≤ n) :
    (logWidth n : ℝ) ≤ 4 * Real.log (2 * (n : ℝ)) := by
  have hp : (2 : ℝ) ^ logWidth n ≤ (2 * (n : ℝ)) ^ 2 := by
    exact_mod_cast pow_logWidth_le_square hn
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ logWidth n) hp
  rw [Real.log_pow, Real.log_pow] at hl
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hhalf := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (logWidth n) : (0 : ℝ) ≤ logWidth n)
  norm_num only [Nat.cast_ofNat] at hl
  linarith

/-- The natural-log coefficient remains fixed before n and the hidden graph. -/
def naturalLogCoefficient : ℝ := 1024 * logFiveCoefficient

theorem naturalLogCoefficient_pos : 0 < naturalLogCoefficient := by
  unfold naturalLogCoefficient
  exact mul_pos (by norm_num) logFiveCoefficient_pos

theorem globalRoutine_naturalLog_cost {n : ℕ} (hn : 2 ≤ n) :
    ((globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).len : ℝ) ≤
      naturalLogCoefficient * Real.sqrt (n : ℝ) * (Real.log (2 * (n : ℝ))) ^ 5 := by
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (logWidth n) : (0 : ℝ) ≤ logWidth n)
    (logWidth_le_four_log hn) 5
  calc
    _ ≤ logFiveCoefficient * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 := globalRoutine_logFive_cost n
    _ ≤ logFiveCoefficient * Real.sqrt (n : ℝ) * (4 * Real.log (2 * (n : ℝ))) ^ 5 :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg logFiveCoefficient_pos.le (Real.sqrt_nonneg _))
    _ = _ := by unfold naturalLogCoefficient; ring

/-- The natural-log corollary concerns the identical physical algorithm and
retains exact schedule, truthfulness, arbitrary-answer normalization and tiny inputs. -/
theorem public_natural_log_five_endpoint :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      let T := globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)
      let R := globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)
      R.len = (if 2 ≤ n then CostBounds.combinedQueries n 12 publicHighTrials (1 / 3) else 0) ∧
      (2 ≤ n → (R.len : ℝ) ≤ C * Real.sqrt (n : ℝ) * (Real.log (2 * (n : ℝ))) ^ 5) ∧
      T.step = R.step ∧
      (∀ read : AnswerTable n, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ (G : CapacityGraph (Fin n) 1) (S : Finset (Fin n)) (a : CutAnswer n 1),
        0 < T.prob (capacityRead G) R.len (some (S, a)) →
          ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S) ∧
      (∀ G : CapacityGraph (Fin n) 1, 2 ≤ n →
        2 / 3 ≤ goodProb T.readout
          (fun c => ∃ S a, c = some (S, a) ∧ IsMinCut G.toWeighted S ∧
            decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
          (R.run (capacityRead G) *ᵥ T.init)) ∧
      (n < 2 → R.len = 0 ∧ ∀ read : AnswerTable n, T.prob read R.len none = 1) := by
  refine ⟨naturalLogCoefficient, naturalLogCoefficient_pos, fun n => ?_⟩
  dsimp only
  exact ⟨native_schedule_all _ _ _ _ _, globalRoutine_naturalLog_cost, rfl,
    fun read => ⟨globalRoutine_state _ _ _ _ _ read, globalRoutine_normalized _ _ _ _ _ read⟩,
    public_candidate_truthful n, public_minimum_shore_value n, public_tiny_input⟩

/-- Literal existential public QAlg/routine family. Both envelopes apply to
the same witness, and the entire public family is chosen before hidden inputs. -/
theorem exists_public_endpoint :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
        (T : CutQAlg n 1 (Candidate n) Work)
        (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) Work),
      R.len = (if 2 ≤ n then CostBounds.combinedQueries n 12 publicHighTrials (1 / 3) else 0) ∧
      (R.len : ℝ) ≤ C * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 ∧
      (2 ≤ n → (R.len : ℝ) ≤ (1024 * C) * Real.sqrt (n : ℝ) * (Real.log (2 * (n : ℝ))) ^ 5) ∧
      T.step = R.step ∧
      (∀ read : AnswerTable n, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ (G : CapacityGraph (Fin n) 1) (S : Finset (Fin n)) (a : CutAnswer n 1),
        0 < T.prob (capacityRead G) R.len (some (S, a)) →
          ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S) ∧
      (∀ G : CapacityGraph (Fin n) 1, 2 ≤ n →
        2 / 3 ≤ goodProb T.readout
          (fun c => ∃ S a, c = some (S, a) ∧ IsMinCut G.toWeighted S ∧
            decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
          (R.run (capacityRead G) *ᵥ T.init)) ∧
      (n < 2 → R.len = 0 ∧ ∀ read : AnswerTable n, T.prob read R.len none = 1) := by
  refine ⟨logFiveCoefficient, logFiveCoefficient_pos, fun n =>
    ⟨globalWork n 12 publicHighTrials (by norm_num) (1 / 3), inferInstance, inferInstance,
      globalAlg n 12 publicHighTrials (by norm_num) (1 / 3),
      globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3), ?_⟩⟩
  exact ⟨native_schedule_all _ _ _ _ _, globalRoutine_logFive_cost n,
    globalRoutine_naturalLog_cost, rfl,
    fun read => ⟨globalRoutine_state _ _ _ _ _ read, globalRoutine_normalized _ _ _ _ _ read⟩,
    public_candidate_truthful n, public_minimum_shore_value n, public_tiny_input⟩

#print axioms native_schedule_matches
#print axioms native_schedule_all
#print axioms logFiveCoefficient_eq
#print axioms logFiveCoefficient_pos
#print axioms globalRoutine_logFive_cost
#print axioms public_candidate_truthful
#print axioms public_minimum_shore_value
#print axioms public_tiny_input
#print axioms public_log_five_endpoint
#print axioms pow_logWidth_le_square
#print axioms logWidth_le_four_log
#print axioms naturalLogCoefficient_pos
#print axioms globalRoutine_naturalLog_cost
#print axioms public_natural_log_five_endpoint
#print axioms exists_public_endpoint

end
end CutQueryComplexity.StarContraction2022.Quantum.Global
