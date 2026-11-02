import CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactHistory
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.ScaledTail

/-!
# Exact-flow cost linear in the actual part size

Both thresholds are used only in the proof. The program still runs to exact
completion. The capacity and size conditions are public numeric conditions;
phase counts, route work and query costs are consequences of the execution.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate DirectedCertificate DirectedUnitST.Repair
open scoped Classical
noncomputable section

theorem phase_threshold_arithmetic (q R t C : ℝ) (hq : 0 ≤ q)
    (hR : 1 ≤ R) (ht : 1 ≤ t) (hC : C ≤ R) (hqt : q ≤ t ^ 3) :
    8 * C * q ^ 2 / (8 * R * t ^ 2) ^ 2 ≤ t ^ 2 := by
  have hqsq : q ^ 2 ≤ t ^ 6 := by
    have h := mul_self_le_mul_self hq hqt
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ 8 * q ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hqsq (by positivity : 0 ≤ 8 * R)
  have h3 : 8 * R ≤ 64 * R ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ t ^ 6)
  apply (div_le_iff₀ (by positivity : 0 < (8 * R * t ^ 2) ^ 2)).mpr
  nlinarith

theorem length_threshold_arithmetic (q R t C : ℝ) (hq : 0 ≤ q)
    (hR : 1 ≤ R) (ht : 1 ≤ t) (hC : C ≤ R) (hqt : q ≤ t ^ 3) :
    8 * C * q ^ 2 / (4 * R * t) ≤ 2 * q * t ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ 8 * q ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hqt (by positivity : 0 ≤ 8 * R * q)
  apply (div_le_iff₀ (by positivity : 0 < 4 * R * t)).mpr
  nlinarith

theorem eventUnitWork_eq (events : List PhaseEvent) :
    (eventUnitWork events : ℝ) = eventLength events + eventValue events := by
  induction events with
  | nil => simp [eventUnitWork, eventLength, eventValue]
  | cons e rest ih =>
      simp only [eventUnitWork, eventLength, eventValue, List.map_cons, List.sum_cons,
        Nat.cast_add, Nat.cast_mul, Nat.cast_one] at ih ⊢
      nlinarith

variable {V : Type} [Fintype V] [DecidableEq V]

theorem scaledNetwork_internal_bound (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C : ℕ) (a z : V → ℕ) :
    ∀ u v, u ≠ source → u ≠ sink → v ≠ source → v ≠ sink →
      (directed (twoStar (scaledInternal G C) a z)).c u v +
        (directed (twoStar (scaledInternal G C) a z)).c v u ≤ 2 * (C : ℝ) := by
  intro u v hus hut hvs hvt
  cases u with
  | inr i => fin_cases i <;> simp [source, sink] at hus hut
  | inl x =>
      cases v with
      | inr i => fin_cases i <;> simp [source, sink] at hvs hvt
      | inl y => exact scaled_internal_pair_bound hG C a z x y

/-- The recorded positive phases and their work satisfy the two analytic
threshold bounds in original capacity units. -/
theorem scaledExactProg_phase_work (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C R t : ℕ) (hC : 1 ≤ C) (hCR : C ≤ R) (ht : 1 ≤ t)
    (hq : Fintype.card V ≤ t ^ 3) (a z : V → ℕ)
    (ha : (∑ v, a v) ≤ Fintype.card V * t) :
    let result := (scaledExactProg C a z).eval G.cut
    result.events.length ≤ 9 * R * t ^ 2 ∧
      eventUnitWork result.events ≤ 7 * R * Fintype.card V * t ^ 2 := by
  let result := (scaledExactProg C a z).eval G.cut
  obtain ⟨history, hpositive, hcost⟩ := scaledExactProg_history G hG C a z
  change PhaseHistory _ source sink (fun _ _ => 0) result.events result.flow at history
  have hcap := scaledNetwork_internal_bound G hG C a z
  have hR : 1 ≤ R := hC.trans hCR
  have hCR' : (C : ℝ) ≤ R := by exact_mod_cast hCR
  have hC' : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hq' : (Fintype.card V : ℝ) ≤ (t : ℝ) ^ 3 := by exact_mod_cast hq
  have hvalue : eventValue result.events ≤ Fintype.card V * t :=
    (history.value_le_source_capacity (scaledInternal G C) a z).trans ha
  have hRt2 : 1 ≤ R * t ^ 2 := Nat.succ_le_of_lt
    (Nat.mul_pos (by omega) (pow_pos (by omega) 2))
  have hRt : 1 ≤ R * t := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hphases := history.scaled_phase_count C hC' hcap hpositive
    (8 * R * t ^ 2) (by nlinarith only [hRt2])
  have hlength := history.scaled_length_bound C hC' hcap (4 * R * t)
    (Fintype.card V * t) (by nlinarith only [hRt]) hvalue
  simp only [internalVertices_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hphases hlength
  have hphaseTail := phase_threshold_arithmetic (Fintype.card V) R t C
    (Nat.cast_nonneg _) hR' ht' hCR' hq'
  have hworkTail := length_threshold_arithmetic (Fintype.card V) R t C
    (Nat.cast_nonneg _) hR' ht' hCR' hq'
  have hRtimes : (t : ℝ) ^ 2 ≤ (R : ℝ) * t ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hR' (sq_nonneg (t : ℝ))]
  have hqRtimes : (Fintype.card V : ℝ) * t ^ 2 ≤
      (R : ℝ) * Fintype.card V * t ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hRtimes (Nat.cast_nonneg (Fintype.card V) :
      (0 : ℝ) ≤ Fintype.card V)
    nlinarith only [h]
  have hvalueR : (eventValue result.events : ℝ) ≤ (Fintype.card V : ℝ) * t := by
    exact_mod_cast hvalue
  have htSquare : (Fintype.card V : ℝ) * t ≤ (Fintype.card V : ℝ) * t ^ 2 := by
    have hs : (t : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith only [ht']
    exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
  constructor
  · have h : (result.events.length : ℝ) ≤ 9 * (R : ℝ) * t ^ 2 := by
      linarith only [hphases, hphaseTail, hRtimes]
    exact_mod_cast h
  · have hw := eventUnitWork_eq result.events
    have h : (eventUnitWork result.events : ℝ) ≤
        7 * (R : ℝ) * Fintype.card V * t ^ 2 := by
      nlinarith only [hlength, hworkTail, hw, hvalueR, htSquare, hqRtimes]
    exact_mod_cast h

def exactSharpBudget (V : Type) [Fintype V] (R t : ℕ) : ℕ :=
  128 * Fintype.card V * R * t ^ 2 * neighborBudget V

/-- Literal executed-query bound, retaining the current part cardinality.
No solver, cost, phase-count or flow-value bound is supplied as a premise. -/
theorem scaledExactProg_cost_sharp (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C R t : ℕ) (hC : 1 ≤ C) (hCR : C ≤ R) (ht : 1 ≤ t)
    (hqpos : 1 ≤ Fintype.card V) (hq : Fintype.card V ≤ t ^ 3) (a z : V → ℕ)
    (ha : (∑ v, a v) ≤ Fintype.card V * t) :
    (scaledExactProg C a z).cost G.cut ≤ exactSharpBudget V R t := by
  let result := (scaledExactProg C a z).eval G.cut
  obtain ⟨hphases, hwork⟩ := scaledExactProg_phase_work G hG C R t hC hCR ht hq a z ha
  have hcost := (scaledExactProg_history G hG C a z).2.2
  change result.events.length ≤ 9 * R * t ^ 2 at hphases
  change eventUnitWork result.events ≤ 7 * R * Fintype.card V * t ^ 2 at hwork
  change (scaledExactProg C a z).cost G.cut ≤ historyBudget V result.events at hcost
  let q := Fintype.card V
  let workScale := R * t ^ 2
  have hworkScale : 1 ≤ workScale := Nat.succ_le_of_lt
    (Nat.mul_pos (by omega) (pow_pos (by omega) 2))
  have hq3 : q + 2 ≤ 3 * q := by dsimp [q]; omega
  have hp : result.events.length ≤ 9 * workScale := by
    simpa only [workScale, Nat.mul_assoc] using hphases
  have hp1 : result.events.length + 1 ≤ 10 * workScale := by omega
  have hw : eventUnitWork result.events ≤ 7 * q * workScale := by
    simpa only [q, workScale, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hwork
  have h1 := Nat.mul_le_mul hp1 (Nat.mul_le_mul_left 2 hq3)
  have h2 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hq3) hp
  have hcoeff : (result.events.length + 1) * (2 * (q + 2)) +
      (2 * (q + 2) * result.events.length + eventUnitWork result.events) ≤ 128 * q * workScale := by
    nlinarith only [h1, h2, hw]
  have hmul := Nat.mul_le_mul_right (neighborBudget V) hcoeff
  apply hcost.trans
  simpa only [historyBudget, bfsBudget, network_card, exactSharpBudget, q, workScale,
    Nat.add_mul, Nat.mul_assoc] using hmul

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactProg_phase_work
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactProg_cost_sharp
