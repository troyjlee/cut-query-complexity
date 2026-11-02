import CutQueryComplexity.DirectedUnitST.Blocking.Run
import CutQueryComplexity.DirectedUnitST.Repair.HeavyTerminal
import CutQueryComplexity.DirectedUnitST.Repair.Cost
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Actual phase histories and repair query accounting

The history below is proof-only evidence for the events produced by the
operational run. Each constructor contains a checked phase output and full
residual BFS facts; it is not an oracle or an assumed query-cost premise.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Blocking

open Finset DirectedCertificate Certificate Prog
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def eventValue (events : List PhaseEvent) : ℕ := (events.map PhaseEvent.amount).sum
def eventLength (events : List PhaseEvent) : ℝ :=
  (events.map fun e => (e.distance : ℝ) * e.amount).sum
def eventTail (events : List PhaseEvent) (k : ℕ) : ℝ :=
  (events.map fun e => if k < e.distance then (e.amount : ℝ) else 0).sum

omit [Fintype V] [DecidableEq V] in
theorem event_sum_eq {A : Type*} [AddCommMonoid A] (events : List PhaseEvent)
    (f : PhaseEvent → A) :
    (events.map f).sum = ∑ i : Fin events.length, f (events.get i) := by
  have he : List.ofFn (fun i : Fin events.length => f (events.get i)) = events.map f := by
    change List.ofFn (f ∘ events.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← he, List.sum_ofFn]

omit [Fintype V] [DecidableEq V] in
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

omit [Fintype V] [DecidableEq V] in
theorem eventTail_le_value (events : List PhaseEvent) (k : ℕ) :
    eventTail events k ≤ eventValue events := by
  induction events with
  | nil => simp [eventTail, eventValue]
  | cons e rest ih =>
      simp only [eventTail, eventValue, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
      split_ifs
      · linarith
      · linarith [Nat.cast_nonneg (α := ℝ) e.amount]

inductive PhaseHistory (G : WeightedDiGraph V) (s t : Node V) :
    WeightedDiGraph (Node V) → List PhaseEvent → Prop
  | nil (H : WeightedDiGraph (Node V)) : PhaseHistory G s t H []
  | step {H : WeightedDiGraph (Node V)} {level : Node V → ℕ}
      {phase : PhaseResult V} {rest : List PhaseEvent}
      (source : level s = 0)
      (rise : ∀ u v, 0 < H.c u v → level v ≤ level u + 1)
      (correct : PhaseCorrect G H level s t phase)
      (reachable : PathAt H s t (level t))
      (tail : PhaseHistory G s t (Repair.residual H _ correct.feasible) rest)
      (later : ∀ e ∈ rest, level t < e.distance) :
      PhaseHistory G s t H (⟨level t, phase.value⟩ :: rest)

/-- The remaining values in a real history form a feasible remaining flow;
the witness is composed from the actual signed phase updates. -/
theorem PhaseHistory.flow {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {s t : Node V} {events : List PhaseEvent} (history : PhaseHistory G s t H events) :
    ∃ f : Node V → Node V → ℝ, H.Feasible f ∧ ∀ x,
      netOut f x = (if x = s then (eventValue events : ℝ) else 0) -
        (if x = t then (eventValue events : ℝ) else 0) := by
  induction history with
  | nil H =>
      refine ⟨fun _ _ => 0, ⟨fun _ _ => by simp, H.nonneg⟩, ?_⟩
      intro x
      simp [eventValue, netOut]
  | @step H level phase rest source rise correct reachable tail later ih =>
      obtain ⟨f, hf, hdiv⟩ := ih
      refine ⟨fun u v => usageDelta phase.usage u v + f u v,
        feasible_add_flow H _ f correct.feasible hf, ?_⟩
      intro x
      simp only [netOut, sum_add_distrib]
      change netOut (usageDelta phase.usage) x + netOut f x = _
      rw [correct.divergence, hdiv]
      simp only [eventValue, List.map_cons, List.sum_cons, Nat.cast_add]
      split_ifs <;> ring

theorem PhaseHistory.positive_amount {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {s t : Node V} {events : List PhaseEvent} (history : PhaseHistory G s t H events) :
    ∀ e ∈ events, 0 < e.amount := by
  induction history with
  | nil H => simp
  | @step H level phase rest source rise correct reachable tail later ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact correct.value_pos source rise reachable
      · exact ih e he

theorem PhaseHistory.increasing {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {s t : Node V} {events : List PhaseEvent} (history : PhaseHistory G s t H events) :
    events.Pairwise (fun e f => e.distance < f.distance) := by
  induction history with
  | nil H => simp
  | step source rise correct reachable tail later ih =>
      exact List.pairwise_cons.mpr ⟨later, ih⟩

/-- Heavy terminal arcs are excluded by the full BFS-level condition; only
internal opposite pairs enter the inverse-square remaining-value bound. -/
theorem PhaseHistory.tail_bound {G : WeightedDiGraph V} {H : WeightedDiGraph (Node V)}
    {s t : Node V} {events : List PhaseEvent} (history : PhaseHistory G s t H events)
    (hst : s ≠ t)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t → H.c u v + H.c v u ≤ 2)
    (k : ℕ) (hk : 3 ≤ k) :
    eventTail events k ≤ 8 * ((Repair.internalVertices s t).card : ℝ) ^ 2 /
      ((k : ℝ) + 1) ^ 2 := by
  induction history with
  | nil H => simp only [eventTail, List.map_nil, List.sum_nil]; positivity
  | @step H level phase rest source rise correct reachable tail later ih =>
      by_cases hdist : k < level t
      · have hhist := PhaseHistory.step source rise correct reachable tail later
        have hall : ∀ e ∈ (⟨level t, phase.value⟩ :: rest), k < e.distance := by
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hdist
          · exact hdist.trans (later e he)
        rw [eventTail_eq_value _ _ hall]
        obtain ⟨f, hf, hdiv⟩ := hhist.flow
        have hfST : H.STFlow s t f := by
          refine ⟨hf, ?_⟩
          intro x hxs hxt
          simp [hdiv, hxs, hxt]
        have hdef := Repair.middle_layer_deficit H level rise s t (level t) source rfl
          (by omega) hcap f hfST
        have hsrc : netOut f s = (eventValue (⟨level t, phase.value⟩ :: rest) : ℝ) := by
          simp [hdiv, hst]
        rw [hsrc] at hdef
        have hlevel : (k : ℝ) + 1 ≤ level t := by exact_mod_cast (show k + 1 ≤ level t by omega)
        have hden : ((k : ℝ) + 1) ^ 2 ≤ (level t : ℝ) ^ 2 := by
          have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (k : ℝ) + 1) hlevel
          nlinarith
        have hquot := mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2) hden)
          (by positivity : 0 ≤ 8 * ((Repair.internalVertices s t).card : ℝ) ^ 2)
        exact hdef.trans (by simpa only [mul_one_div] using hquot)
      · simp only [eventTail, List.map_cons, List.sum_cons, hdist, ↓reduceIte, zero_add]
        apply ih
        intro u v hus hut hvs hvt
        rw [Repair.residual_pair_sum]
        exact hcap u v hus hut hvs hvt

/-- The public event amounts add up to the public returned value for every
answer history, including early exits caused by inconsistent answers. -/
theorem solveRun_value_events (read : Finset V → ℝ) (s t : Node V)
    (fuel : ℕ) (st : NetworkState V) :
    let result := (solveRun s t fuel st).eval read
    result.value = eventValue result.phases := by
  induction fuel generalizing st with
  | zero =>
      rw [solveRun, Prog.eval_bind]
      split_ifs <;> rfl
  | succ fuel ih =>
      rw [solveRun, Prog.eval_bind]
      split_ifs
      · rfl
      · rw [Prog.eval_bind, Prog.eval_map]
        simp only [prependPhase, eventValue, List.map_cons, List.sum_cons]
        exact congrArg (fun r =>
          ((phaseProg ((bfsProg st s).eval read).network
            (bfsLevel ((bfsProg st s).eval read)) s t).eval read).value + r) (ih _)

/-- Every recorded event is an actual completed blocking phase. The lower
distance bound is propagated using the actual previous phase endpoint. -/
theorem solveRun_history (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (s t : Node V) (hst : s ≠ t) (fuel : ℕ) (st : NetworkState V)
    (hr : st.Realizes G H) (hint : IntegralCap H) (lower : ℕ)
    (hlower : ∀ d, PathAt H s t d → lower ≤ d) :
    let result := (solveRun s t fuel st).eval G.out
    PhaseHistory G s t H result.phases ∧
      ∀ e ∈ result.phases, lower ≤ e.distance ∧ e.distance < Fintype.card (Node V) := by
  induction fuel generalizing H st lower with
  | zero =>
      rw [solveRun, Prog.eval_bind]
      split_ifs <;> exact ⟨PhaseHistory.nil H, by simp [solveEmpty]⟩
  | succ fuel ih =>
      rw [solveRun, Prog.eval_bind]
      obtain ⟨hreal, hsource, hrise, hsourceMem, hout, hpath⟩ := bfsProg_facts G H st hr s
      split_ifs with ht
      · exact ⟨PhaseHistory.nil H, by simp [solveEmpty]⟩
      · rw [Prog.eval_bind, Prog.eval_map]
        let bfs := (bfsProg st s).eval G.out
        let phase := (phaseProg bfs.network (bfsLevel bfs) s t).eval G.out
        have hp : PhaseCorrect G H (bfsLevel bfs) s t phase :=
          phaseProg_complete G H bfs.network hreal hint (bfsLevel bfs) s t hst
        have hint' := integralCap_residual hint phase.usage hp.feasible
        have hlow := hlower _ (hpath t ht).1
        change lower ≤ bfsLevel bfs t at hlow
        have hrec := ih (Repair.residual H _ hp.feasible) phase.network hp.realizes hint'
          (bfsLevel bfs t + 1)
          (fun d path => Nat.succ_le_of_lt (hp.distance_strict hsource hrise path))
        refine ⟨PhaseHistory.step hsource hrise hp (hpath t ht).1 hrec.1 ?_, ?_⟩
        · intro e he
          have hl := (hrec.2 e he).1
          exact Nat.lt_of_succ_le hl
        · intro e he
          change e ∈ ⟨bfsLevel bfs t, phase.value⟩ ::
            ((solveRun s t fuel phase.network).eval G.out).phases at he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨hlow, (hpath t ht).2⟩
          · obtain ⟨hl, hu⟩ := hrec.2 e he
            exact ⟨by omega, hu⟩

theorem solveProg_history (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (s t : Node V) (hst : s ≠ t) :
    let result := (solveProg st s t).eval G.out
    PhaseHistory G s t H result.phases ∧
      ∀ e ∈ result.phases, e.distance < Fintype.card (Node V) := by
  have h := solveRun_history G H s t hst (Fintype.card (Node V)) st hr hint 0
    (fun _ _ => Nat.zero_le _)
  exact ⟨h.1, fun e he => (h.2 e he).2⟩

/-- Cost of the actual run in terms of its actual recorded phases. BFS and
failed-discovery overheads contribute 4N per phase plus the last BFS's 2N. -/
theorem solveRun_cost_events (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (s t : Node V) (hst : s ≠ t) (fuel : ℕ) (st : NetworkState V)
    (hr : st.Realizes G H) (hint : IntegralCap H) :
    let result := (solveRun s t fuel st).eval G.out
    ((solveRun s t fuel st).cost G.out : ℝ) ≤
      (2 * (Fintype.card (Node V) : ℝ) +
        4 * (Fintype.card (Node V) : ℝ) * result.phases.length +
        eventLength result.phases) * edgeQueryBound V := by
  induction fuel generalizing H st with
  | zero =>
      rw [solveRun, Prog.cost_bind, Prog.eval_bind]
      have hb : ((bfsProg st s).cost G.out : ℝ) ≤
          (2 * (Fintype.card (Node V) : ℝ)) * edgeQueryBound V := by
        exact_mod_cast bfsProg_cost G.out st s
      split_ifs <;> simpa [solveEmpty, eventLength] using hb
  | succ fuel ih =>
      rw [solveRun, Prog.cost_bind, Prog.eval_bind]
      obtain ⟨hreal, hsource, hrise, hsourceMem, hout, hpath⟩ := bfsProg_facts G H st hr s
      have hb : ((bfsProg st s).cost G.out : ℝ) ≤
          (2 * (Fintype.card (Node V) : ℝ)) * edgeQueryBound V := by
        exact_mod_cast bfsProg_cost G.out st s
      split_ifs with ht
      · simpa [solveEmpty, eventLength] using hb
      · rw [Prog.cost_bind, Prog.cost_map, Prog.eval_bind, Prog.eval_map]
        let bfs := (bfsProg st s).eval G.out
        let phase := (phaseProg bfs.network (bfsLevel bfs) s t).eval G.out
        have hp : PhaseCorrect G H (bfsLevel bfs) s t phase :=
          phaseProg_complete G H bfs.network hreal hint (bfsLevel bfs) s t hst
        have hpcost := phaseProg_cost_distance_value G H bfs.network hreal hint
          (bfsLevel bfs) s t hst
        have hint' := integralCap_residual hint phase.usage hp.feasible
        have hrec := ih (Repair.residual H _ hp.feasible) phase.network hp.realizes hint'
        have hsourceR : (bfsLevel bfs s : ℝ) = 0 := by exact_mod_cast hsource
        rw [hsourceR, sub_zero] at hpcost
        have htotal := add_le_add hb (add_le_add hpcost hrec)
        simp only [Nat.cast_add] at htotal ⊢
        convert htotal using 1
        simp only [prependPhase, List.length_cons, eventLength,
          List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
        ring

theorem solveProg_cost_events (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (s t : Node V) (hst : s ≠ t) :
    let result := (solveProg st s t).eval G.out
    ((solveProg st s t).cost G.out : ℝ) ≤
      (2 * (Fintype.card (Node V) : ℝ) +
        4 * (Fintype.card (Node V) : ℝ) * result.phases.length +
        eventLength result.phases) * edgeQueryBound V :=
  solveRun_cost_events G H s t hst _ st hr hint

theorem PhaseHistory.positive_distance {G : WeightedDiGraph V}
    {H : WeightedDiGraph (Node V)} {s t : Node V} {events : List PhaseEvent}
    (history : PhaseHistory G s t H events) (hst : s ≠ t) :
    ∀ e ∈ events, 0 < e.distance := by
  induction history with
  | nil H => simp
  | @step H level phase rest source rise correct reachable tail later ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · change 0 < level t
        by_contra hn
        have hz : level t = 0 := by omega
        rw [hz] at reachable
        cases reachable
        exact hst rfl
      · exact ih e he

theorem PhaseHistory.numeric_bounds {G : WeightedDiGraph V}
    {H : WeightedDiGraph (Node V)} {s t : Node V} {events : List PhaseEvent}
    (history : PhaseHistory G s t H events) (hst : s ≠ t)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t → H.c u v + H.c v u ≤ 2)
    (hM : ∀ e ∈ events, e.distance ≤ Fintype.card (Node V)) (R : ℝ)
    (hn : 1 ≤ ((Repair.internalVertices s t).card : ℝ)) (hR : 1 ≤ R)
    (hRn : R ≤ ((Repair.internalVertices s t).card : ℝ) ^ 2)
    (hvalue : (eventValue events : ℝ) ≤ R) :
    eventLength events ≤ 7 * ((Repair.internalVertices s t).card : ℝ) * Real.sqrt R ∧
      (events.length : ℝ) ≤ min R (6 * ((Repair.internalVertices s t).card : ℝ) ^ (2 / 3 : ℝ)) := by
  let distance : Fin events.length → ℕ := fun i => (events.get i).distance
  let amount : Fin events.length → ℝ := fun i => (events.get i).amount
  have hsum : (∑ i, amount i) = (eventValue events : ℝ) := by
    have hv : eventValue events = ∑ i : Fin events.length, (events.get i).amount :=
      event_sum_eq events PhaseEvent.amount
    dsimp only [amount]
    exact_mod_cast hv.symm
  have htailEq (k : ℕ) : Repair.tailMass distance amount k = eventTail events k := by
    exact (event_sum_eq events (fun e => if k < e.distance then (e.amount : ℝ) else 0)).symm
  have hhead (k : ℕ) : Repair.tailMass distance amount k ≤ R := by
    rw [htailEq]
    exact (eventTail_le_value events k).trans hvalue
  have htail (k : ℕ) (hk : 3 ≤ k) : Repair.tailMass distance amount k ≤
      8 * ((Repair.internalVertices s t).card : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    rw [htailEq]
    exact history.tail_bound hst hcap k hk
  have ha (i : Fin events.length) : 1 ≤ amount i := by
    have hi := history.positive_amount (events.get i) (List.get_mem events i)
    have hi' : 1 ≤ (events.get i).amount := hi
    dsimp only [amount]
    exact_mod_cast hi'
  have hd (i : Fin events.length) : 0 < distance i :=
    history.positive_distance hst (events.get i) (List.get_mem events i)
  have hmono : StrictMono distance := by
    intro i j hij
    exact List.pairwise_iff_get.mp history.increasing i j hij
  have hlen := Repair.phase_length_sqrt distance amount (Fintype.card (Node V))
    (fun i => hM _ (List.get_mem events i)) ((Repair.internalVertices s t).card : ℝ)
    R hn hR hRn hhead htail
  have hcount := Repair.phase_count_two_thirds distance amount hd hmono.injective ha
    ((Repair.internalVertices s t).card : ℝ) hn htail
  have hcountValue : (events.length : ℝ) ≤ ∑ i, amount i := by
    calc
      _ = ∑ _ : Fin events.length, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum fun i _ => ha i
  rw [hsum] at hcountValue
  refine ⟨?_, le_min (hcountValue.trans hvalue) ?_⟩
  · rw [eventLength, event_sum_eq]
    exact hlen
  · simpa only [Fintype.card_fin] using hcount

/-- Sharp query bound for the actual terminal solve, using only the internal
pair cap and a public upper bound R on its feasible value. -/
theorem solveProg_cost_sharp (G : WeightedDiGraph V) (H : WeightedDiGraph (Node V))
    (st : NetworkState V) (hr : st.Realizes G H) (hint : IntegralCap H)
    (s t : Node V) (hst : s ≠ t)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t → H.c u v + H.c v u ≤ 2)
    (R : ℝ) (hn : 1 ≤ ((Repair.internalVertices s t).card : ℝ)) (hR : 1 ≤ R)
    (hRn : R ≤ ((Repair.internalVertices s t).card : ℝ) ^ 2)
    (hsource : H.out {s} ≤ R) :
    ((solveProg st s t).cost G.out : ℝ) ≤
      (2 * (Fintype.card (Node V) : ℝ) +
        4 * (Fintype.card (Node V) : ℝ) *
          min R (6 * ((Repair.internalVertices s t).card : ℝ) ^ (2 / 3 : ℝ)) +
        7 * ((Repair.internalVertices s t).card : ℝ) * Real.sqrt R) * edgeQueryBound V := by
  let result := (solveProg st s t).eval G.out
  have hc := solveProg_complete G H st hr hint s t hst
  have hh := solveProg_history G H st hr hint s t hst
  have hv : (eventValue result.phases : ℝ) ≤ R := by
    have hvalue := solveRun_value_events G.out s t (Fintype.card (Node V)) st
    change result.value = eventValue result.phases at hvalue
    rw [← hvalue, hc.value_eq_cut]
    exact (hc.min_cut {s} (by simp) (by simpa using Ne.symm hst)).trans hsource
  obtain ⟨hlen, hcount⟩ := hh.1.numeric_bounds hst hcap
    (fun e he => (hh.2 e he).le) R hn hR hRn hv
  have hcost := solveProg_cost_events G H st hr hint s t hst
  apply hcost.trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  have hscale := mul_le_mul_of_nonneg_left hcount
    (by positivity : 0 ≤ 4 * (Fintype.card (Node V) : ℝ))
  linarith

end
end CutQueryComplexity.DirectedUnitST.Blocking

#print axioms CutQueryComplexity.DirectedUnitST.Blocking.PhaseHistory.flow
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.PhaseHistory.tail_bound
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.solveProg_history
#print axioms CutQueryComplexity.DirectedUnitST.Blocking.solveProg_cost_sharp
