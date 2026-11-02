import CutQueryComplexity.DeterministicAPMCExpansion.Flow.Tail
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.ScaledGeometry
import Mathlib.Data.List.Pairwise

/-!
# Scaled tails and the actual integral phase count

Capacity normalization is confined to the geometric lemma. Recorded amounts
stay in their original natural-number units. Thus every executed positive
phase contributes at least one unit to its tail, even when the internal
capacity is greater than one. Terminal capacities are unrestricted.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset DirectedCertificate Certificate DirectedUnitST.Repair
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem PhaseHistory.scaled_tail_bound {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final)
    (C : ℝ) (hC : 0 < C)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t → H.c u v + H.c v u ≤ 2 * C)
    (k : ℕ) (hk : 3 ≤ k) :
    eventTail events k ≤ 8 * C * ((internalVertices s t).card : ℝ) ^ 2 /
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
        have hdef := scaled_residual_middle_layer_deficit H C hC s t final current
          tail.final_flow hcurrent level (level t) hrise hs rfl (by omega) hcap
        rw [hfull.value_difference] at hdef
        have hlevel : (k : ℝ) + 1 ≤ level t := by exact_mod_cast Nat.succ_le_of_lt hdist
        have hden : ((k : ℝ) + 1) ^ 2 ≤ (level t : ℝ) ^ 2 := by
          have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (k : ℝ) + 1) hlevel
          nlinarith
        have hquot := mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2) hden)
          (by positivity : 0 ≤ 8 * C * ((internalVertices s t).card : ℝ) ^ 2)
        exact hdef.trans (by simpa only [mul_one_div] using hquot)
      · simp only [eventTail, List.map_cons, List.sum_cons, hdist, ↓reduceIte, zero_add]
        exact ih

theorem PhaseHistory.distance_injective {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final) :
    Function.Injective (fun i : Fin events.length => (events.get i).distance) := by
  intro i j he
  change (events.get i).distance = (events.get j).distance at he
  rcases lt_trichotomy i j with hij | hij | hji
  · have h := history.increasing.rel_get_of_lt hij
    exact False.elim ((Nat.ne_of_lt h) he)
  · exact hij
  · have h := history.increasing.rel_get_of_lt hji
    exact False.elim ((Nat.ne_of_lt h) he.symm)

/-- The distance shift permits even a zero-distance event in this general
history lemma. The actual distinct terminals have positive distances. -/
theorem PhaseHistory.scaled_phase_count {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final)
    (C : ℝ) (hC : 0 < C)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t → H.c u v + H.c v u ≤ 2 * C)
    (ha : ∀ e ∈ events, 0 < e.amount) (K : ℕ) (hK : 4 ≤ K) :
    (events.length : ℝ) ≤ K +
      8 * C * ((internalVertices s t).card : ℝ) ^ 2 / (K : ℝ) ^ 2 := by
  let distance := fun i : Fin events.length => (events.get i).distance + 1
  let amount := fun i : Fin events.length => ((events.get i).amount : ℝ)
  have hdinj : Function.Injective distance := by
    intro i j he
    apply history.distance_injective
    exact Nat.add_right_cancel he
  have hapos : ∀ i, 1 ≤ amount i := by
    intro i
    change (1 : ℝ) ≤ (events.get i).amount
    exact_mod_cast Nat.succ_le_of_lt (ha _ (List.get_mem events i))
  have hcount := phase_count_le_head_add_tail distance amount
    (fun _ => Nat.succ_pos _) hdinj hapos K
  have htail : tailMass distance amount K = eventTail events (K - 1) := by
    unfold tailMass eventTail
    rw [event_sum_eq]
    apply sum_congr rfl
    intro i _
    have he : K < (events.get i).distance + 1 ↔ K - 1 < (events.get i).distance := by omega
    simp only [distance, amount, he]
  rw [htail, Fintype.card_fin] at hcount
  have hb := history.scaled_tail_bound C hC hcap (K - 1) (by omega)
  have he : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
    exact_mod_cast (show K - 1 + 1 = K by omega)
  rw [he] at hb
  linarith

/-- Finite layer cake needs no supplied distance ceiling: take the maximum
of the explicitly recorded finite distance table. -/
theorem PhaseHistory.scaled_length_bound {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {current final : NetworkVertex V → NetworkVertex V → ℝ}
    {events : List PhaseEvent} (history : PhaseHistory H s t current events final)
    (C : ℝ) (hC : 0 < C)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t → H.c u v + H.c v u ≤ 2 * C)
    (K F : ℕ) (hK : 4 ≤ K) (hvalue : eventValue events ≤ F) :
    eventLength events ≤ (K : ℝ) * F +
      8 * C * ((internalVertices s t).card : ℝ) ^ 2 / K := by
  let distance := fun i : Fin events.length => (events.get i).distance
  let amount := fun i : Fin events.length => ((events.get i).amount : ℝ)
  let M := (univ : Finset (Fin events.length)).sup distance
  have hM : ∀ i, distance i ≤ M := fun i => le_sup (f := distance) (mem_univ i)
  have htail (k : ℕ) : tailMass distance amount k = eventTail events k := by
    unfold tailMass eventTail
    rw [event_sum_eq]
  have hhead : ∀ k, tailMass distance amount k ≤ (F : ℝ) := by
    intro k
    rw [htail]
    exact (eventTail_le_value events k).trans (by exact_mod_cast hvalue)
  have hlong : ∀ k, K ≤ k → tailMass distance amount k ≤
      8 * C * ((internalVertices s t).card : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro k hk
    rw [htail]
    exact history.scaled_tail_bound C hC hcap k (by omega)
  have h := phase_length_split distance amount M K hM (by omega) F
    (8 * C * ((internalVertices s t).card : ℝ) ^ 2) (by positivity) hhead hlong
  simpa only [eventLength, event_sum_eq, distance, amount] using h

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.scaled_tail_bound
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.scaled_phase_count
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.scaled_length_bound
