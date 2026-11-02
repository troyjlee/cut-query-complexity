import CutQueryComplexity.DeterministicAPMCExpansion.Flow.CutCertificate
import CutQueryComplexity.DirectedUnitST.Repair.Cost

/-!
# Augmentation tails for finite, possibly early-stopped phase histories

The history is proof-only evidence about explicit current/final flows and
recorded events. It contains no solver or query-cost premise. An operational
blocking loop must produce this history before using the cost conclusion.
In particular no constructor requires the final flow to be maximum.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset DirectedCertificate Certificate
open DirectedUnitST.Repair
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

structure PhaseEvent where
  distance : ℕ
  amount : ℕ

def eventValue (events : List PhaseEvent) : ℕ := (events.map PhaseEvent.amount).sum

def eventLength (events : List PhaseEvent) : ℝ :=
  (events.map fun e => (e.distance : ℝ) * e.amount).sum

def eventTail (events : List PhaseEvent) (k : ℕ) : ℝ :=
  (events.map fun e => if k < e.distance then (e.amount : ℝ) else 0).sum

theorem event_sum_eq {A : Type} [AddCommMonoid A] (events : List PhaseEvent)
    (f : PhaseEvent → A) :
    (events.map f).sum = ∑ i : Fin events.length, f (events.get i) := by
  have he : List.ofFn (fun i : Fin events.length => f (events.get i)) = events.map f := by
    change List.ofFn (f ∘ events.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← he, List.sum_ofFn]

theorem eventTail_eq_value (events : List PhaseEvent) (k : ℕ)
    (h : ∀ e ∈ events, k < e.distance) : eventTail events k = eventValue events := by
  induction events with
  | nil => simp [eventTail, eventValue]
  | cons e rest ih =>
      have he := h e (by simp)
      have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [eventTail, eventValue, List.map_cons, List.sum_cons, he, ↓reduceIte,
        Nat.cast_add]
      exact congrArg (fun r : ℝ => (e.amount : ℝ) + r) ht

theorem eventTail_le_value (events : List PhaseEvent) (k : ℕ) :
    eventTail events k ≤ eventValue events := by
  induction events with
  | nil => simp [eventTail, eventValue]
  | cons e rest ih =>
      simp only [eventTail, eventValue, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
      split_ifs
      · linarith
      · linarith [Nat.cast_nonneg (α := ℝ) e.amount]

/-- Recorded phases are tied to actual feasible flows in the same original
network. The level condition applies to the full current residual graph. -/
inductive PhaseHistory (H : WeightedDiGraph (NetworkVertex V)) (s t : NetworkVertex V) :
    (NetworkVertex V → NetworkVertex V → ℝ) → List PhaseEvent →
      (NetworkVertex V → NetworkVertex V → ℝ) → Prop
  | nil (current : NetworkVertex V → NetworkVertex V → ℝ)
      (feasible : H.STFlow s t current) : PhaseHistory H s t current [] current
  | step {current next final : NetworkVertex V → NetworkVertex V → ℝ}
      {level : NetworkVertex V → ℕ} {amount : ℕ} {events : List PhaseEvent}
      (current_flow : H.STFlow s t current)
      (source : level s = 0)
      (rise : ∀ u v, 0 < (residual H current current_flow.1).c u v →
        level v ≤ level u + 1)
      (increment : netOut next s = netOut current s + amount)
      (tail : PhaseHistory H s t next events final)
      (later : ∀ e ∈ events, level t < e.distance) :
      PhaseHistory H s t current (⟨level t, amount⟩ :: events) final

theorem PhaseHistory.start_flow {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final) :
    H.STFlow s t current := by
  cases history with
  | nil _ feasible => exact feasible
  | step current_flow _ _ _ _ _ => exact current_flow

theorem PhaseHistory.final_flow {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final) :
    H.STFlow s t final := by
  induction history with
  | nil _ feasible => exact feasible
  | step _ _ _ _ _ _ ih => exact ih

theorem PhaseHistory.value_difference {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final) :
    netOut final s - netOut current s = eventValue events := by
  induction history with
  | nil _ _ => simp [eventValue]
  | step _ _ _ increment _ _ ih =>
      simp only [eventValue, List.map_cons, List.sum_cons, Nat.cast_add]
      change netOut _ _ - netOut _ _ = (_ : ℝ) + (eventValue _ : ℝ)
      linarith

theorem PhaseHistory.increasing {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final) :
    events.Pairwise (fun e f => e.distance < f.distance) := by
  induction history with
  | nil _ _ => simp
  | step _ _ _ _ _ later ih => exact List.pairwise_cons.mpr ⟨later, ih⟩

/-- Apply the residual middle-cut bound to the recorded final flow, not an
optimal flow. This proves tails for every valid early-stopped prefix. -/
theorem PhaseHistory.tail_bound {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t → H.c u v + H.c v u ≤ 2)
    (k : ℕ) (hk : 3 ≤ k) :
    eventTail events k ≤ 8 * ((internalVertices s t).card : ℝ) ^ 2 /
      ((k : ℝ) + 1) ^ 2 := by
  induction history with
  | nil _ _ => simp only [eventTail, List.map_nil, List.sum_nil]; positivity
  | @step current next final level amount events hcurrent hs hrise hincr tail later ih =>
      by_cases hdist : k < level t
      · have hfull := PhaseHistory.step hcurrent hs hrise hincr tail later
        have hall : ∀ e ∈ (⟨level t, amount⟩ :: events), k < e.distance := by
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hdist
          · exact hdist.trans (later e he)
        rw [eventTail_eq_value _ _ hall]
        have hdef := residual_middle_layer_deficit H s t final current
          tail.final_flow hcurrent level (level t) hrise hs rfl (by omega) hcap
        rw [hfull.value_difference] at hdef
        have hlevel : (k : ℝ) + 1 ≤ level t := by
          exact_mod_cast (show k + 1 ≤ level t by omega)
        have hden : ((k : ℝ) + 1) ^ 2 ≤ (level t : ℝ) ^ 2 := by
          have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (k : ℝ) + 1) hlevel
          nlinarith
        have hquot := mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2) hden)
          (by positivity : 0 ≤ 8 * ((internalVertices s t).card : ℝ) ^ 2)
        exact hdef.trans (by simpa only [mul_one_div] using hquot)
      · simp only [eventTail, List.map_cons, List.sum_cons, hdist, ↓reduceIte, zero_add]
        exact ih

/-- The public total capacity of the known source star bounds every feasible
flow, without a `source capacity ≤ q²` restriction. -/
theorem netOut_le_source_capacity (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f) :
    netOut f source ≤ ((∑ v, a v : ℕ) : ℝ) := by
  have h := sum_le_sum (s := (univ : Finset (NetworkVertex V))) fun v _ => hf.2 source v
  change netOut f source ≤ ∑ v, (twoStar G a z).w source v at h
  simpa only [Fintype.sum_sum_type, twoStar_source, twoStar, embedded, knownStars,
    source, terminalCapacity, ↓reduceIte, add_zero, sum_const_zero, zero_add, Nat.cast_sum] using h

theorem PhaseHistory.value_le_source_capacity (G : WeightedGraph V) (a z : V → ℕ)
    {final : NetworkVertex V → NetworkVertex V → ℝ} {events : List PhaseEvent}
    (history : PhaseHistory (directed (twoStar G a z)) source sink (fun _ _ => 0)
      events final) : eventValue events ≤ ∑ v, a v := by
  have hvalue := history.value_difference
  simp only [netOut, sum_const_zero, sub_zero] at hvalue
  have hcap := netOut_le_source_capacity G a z final history.final_flow.1
  change netOut final source = (eventValue events : ℝ) at hvalue
  rw [hvalue] at hcap
  exact_mod_cast hcap

/-- Finite layer-cake summation of a proved history. The distance ceiling is
public loop fuel; it does not assert an external query cost. -/
theorem PhaseHistory.length_bound {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t → H.c u v + H.c v u ≤ 2)
    (M K F : ℕ) (hM : ∀ e ∈ events, e.distance ≤ M) (hK : 4 ≤ K)
    (hvalue : eventValue events ≤ F) :
    eventLength events ≤ (K : ℝ) * F +
      8 * ((internalVertices s t).card : ℝ) ^ 2 / K := by
  let distance := fun i : Fin events.length => (events.get i).distance
  let amount := fun i : Fin events.length => ((events.get i).amount : ℝ)
  have htail (k : ℕ) : tailMass distance amount k = eventTail events k := by
    unfold tailMass eventTail
    rw [event_sum_eq]
  have hhead : ∀ k, tailMass distance amount k ≤ (F : ℝ) := by
    intro k
    rw [htail]
    exact (eventTail_le_value events k).trans (by exact_mod_cast hvalue)
  have hlong : ∀ k, K ≤ k → tailMass distance amount k ≤
      8 * ((internalVertices s t).card : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro k hk
    rw [htail]
    exact history.tail_bound hcap k (by omega)
  have h := phase_length_split distance amount M K
    (fun i => hM _ (List.get_mem events i)) (by omega) F
    (8 * ((internalVertices s t).card : ℝ) ^ 2) (by positivity) hhead hlong
  simpa only [eventLength, event_sum_eq, distance, amount] using h

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.tail_bound
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.value_le_source_capacity
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.length_bound
