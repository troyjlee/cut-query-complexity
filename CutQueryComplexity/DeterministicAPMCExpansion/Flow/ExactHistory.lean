import CutQueryComplexity.DeterministicAPMCExpansion.Flow.Exact

/-!
# Phase history produced by the actual exact-flow execution

Every recorded amount is positive in the original integral capacity units.
Distances strictly increase because a completed phase blocks its old level
graph while preserving the old level-rise inequalities. The history is proved
for every finite executed prefix; no maximum-flow or cost premise constructs it.
The cost statement includes the final failed BFS whenever it is executed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate DirectedCertificate Prog DirectedUnitST.Repair
open DirectedUnitST.Blocking (IntegralCap)
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def eventUnitWork (events : List PhaseEvent) : ℕ :=
  (events.map fun e => (e.distance + 1) * e.amount).sum

def historyBudget (V : Type) [Fintype V] (events : List PhaseEvent) : ℕ :=
  (events.length + 1) * bfsBudget V +
    (2 * Fintype.card (NetworkVertex V) * events.length + eventUnitWork events) * neighborBudget V

theorem exactRun_eval_unseen (read : Finset V → ℝ) (a z : V → ℕ) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hunseen : sink ∈ ((bfsProg a z f source).eval read).unseen) :
    (exactRun a z (fuel + 1) f).eval read =
      exactEmpty f ((bfsProg a z f source).eval read).unseenᶜ true := by
  simp only [exactRun, Prog.eval_bind, hunseen, ↓reduceIte, Prog.eval_pure]

theorem exactRun_cost_unseen (read : Finset V → ℝ) (a z : V → ℕ) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hunseen : sink ∈ ((bfsProg a z f source).eval read).unseen) :
    (exactRun a z (fuel + 1) f).cost read = (bfsProg a z f source).cost read := by
  simp only [exactRun, Prog.cost_bind, hunseen, ↓reduceIte, Prog.cost_pure, Nat.add_zero]

theorem exactRun_eval_phase (read : Finset V → ℝ) (a z : V → ℕ) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hunseen : sink ∉ ((bfsProg a z f source).eval read).unseen)
    (hfinished : ((unitPhaseProg a z
      (bfsLevel ((bfsProg a z f source).eval read)) f).eval read).finished = true) :
    (exactRun a z (fuel + 1) f).eval read =
      exactPrepend (bfsLevel ((bfsProg a z f source).eval read) sink)
        ((unitPhaseProg a z (bfsLevel ((bfsProg a z f source).eval read)) f).eval read).amount
        ((exactRun a z fuel
          ((unitPhaseProg a z (bfsLevel ((bfsProg a z f source).eval read)) f).eval read).flow).eval read) := by
  simp only [exactRun, Prog.eval_bind, hunseen, ↓reduceIte, hfinished, Prog.eval_map]

theorem exactRun_cost_phase (read : Finset V → ℝ) (a z : V → ℕ) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hunseen : sink ∉ ((bfsProg a z f source).eval read).unseen)
    (hfinished : ((unitPhaseProg a z
      (bfsLevel ((bfsProg a z f source).eval read)) f).eval read).finished = true) :
    (exactRun a z (fuel + 1) f).cost read = (bfsProg a z f source).cost read +
      ((unitPhaseProg a z (bfsLevel ((bfsProg a z f source).eval read)) f).cost read +
        (exactRun a z fuel
          ((unitPhaseProg a z (bfsLevel ((bfsProg a z f source).eval read)) f).eval read).flow).cost read) := by
  simp only [exactRun, Prog.cost_bind, hunseen, ↓reduceIte, hfinished, Prog.cost_map]

/-- A nonempty recorded history begins with the BFS actually executed at
this state. This is an operational identity, valid on arbitrary replies. -/
theorem exactRun_first (read : Finset V → ℝ) (a z : V → ℕ) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (e : PhaseEvent) (rest : List PhaseEvent)
    (hevents : ((exactRun a z fuel f).eval read).events = e :: rest) :
    sink ∉ ((bfsProg a z f source).eval read).unseen ∧
      e.distance = bfsLevel ((bfsProg a z f source).eval read) sink := by
  cases fuel with
  | zero => simp [exactRun, exactEmpty] at hevents
  | succ fuel =>
      by_cases hunseen : sink ∈ ((bfsProg a z f source).eval read).unseen
      · rw [exactRun_eval_unseen read a z fuel f hunseen] at hevents
        simp [exactEmpty] at hevents
      · let phase := (unitPhaseProg a z (bfsLevel ((bfsProg a z f source).eval read)) f).eval read
        cases hfinished : phase.finished with
        | false =>
            simp only [exactRun, Prog.eval_bind, hunseen, ↓reduceIte] at hevents
            change ((if phase.finished then
              (exactRun a z fuel phase.flow).map
                (exactPrepend (bfsLevel ((bfsProg a z f source).eval read) sink) phase.amount)
              else Prog.pure (exactEmpty phase.flow {source} false)).eval read).events = e :: rest at hevents
            simp only [hfinished, Bool.false_eq_true, ↓reduceIte, Prog.eval_pure, exactEmpty] at hevents
            contradiction
        | true =>
            rw [exactRun_eval_phase read a z fuel f hunseen hfinished] at hevents
            change _ :: _ = e :: rest at hevents
            have he := (List.cons.inj hevents).1
            exact ⟨hunseen, (congrArg PhaseEvent.distance he).symm⟩

/-- Actual algorithmic evidence, including strict distance order, unscaled
positive integer augmentations, and the DFS/BFS execution cost. -/
theorem exactRun_history (G : WeightedGraph V) (a z : V → ℕ) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).STFlow source sink f)
    (hint : IntegralCap (residualNetwork G a z f hf.1))
    (hstart : 0 ≤ netOut f source) :
    let result := (exactRun a z fuel f).eval G.cut
    PhaseHistory (directed (twoStar G a z)) source sink f result.events result.flow ∧
      (∀ e ∈ result.events, 0 < e.amount) ∧
      (exactRun a z fuel f).cost G.cut ≤ historyBudget V result.events := by
  induction fuel generalizing f with
  | zero =>
      refine ⟨PhaseHistory.nil f hf, ?_, ?_⟩
      · simp [exactRun, exactEmpty]
      · simp [exactRun, exactEmpty, historyBudget, eventUnitWork]
  | succ fuel ih =>
      let data := (bfsProg a z f source).eval G.cut
      obtain ⟨hsource, hrise, hpath⟩ := bfsProg_level_rise G a z f hf.1 source
      change bfsLevel data source = 0 at hsource
      change ∀ u v, 0 < (residualNetwork G a z f hf.1).c u v →
        bfsLevel data v ≤ bfsLevel data u + 1 at hrise
      change ∀ v, v ∉ data.unseen →
        PathAt (residualNetwork G a z f hf.1) source v (bfsLevel data v) at hpath
      by_cases hunseen : sink ∈ data.unseen
      · rw [exactRun_eval_unseen G.cut a z fuel f hunseen]
        refine ⟨PhaseHistory.nil f hf, ?_, ?_⟩
        · simp [exactEmpty]
        · rw [exactRun_cost_unseen G.cut a z fuel f hunseen]
          simpa only [exactEmpty, historyBudget, eventUnitWork, bfsBudget, List.length_nil,
            List.map_nil, List.sum_nil, Nat.zero_add, Nat.one_mul, Nat.mul_zero,
            Nat.add_zero, Nat.zero_mul] using bfsProg_cost G.cut a z f source
      · let phase := (unitPhaseProg a z (bfsLevel data) f).eval G.cut
        have hp := unitPhaseProg_facts G a z (bfsLevel data) f hf hint
        change UnitPhaseFacts _ _ _ _ _ _ phase at hp
        have hfinished : phase.finished = true :=
          unitPhaseProg_finishes G a z (bfsLevel data) f hf hint hstart
        have hpositive : 0 < phase.amount :=
          unitPhaseProg_amount_pos G a z (bfsLevel data) f hf hint hstart
            ((hpath sink hunseen).tight (bfsLevel data) hsource hrise rfl)
        have hnextStart : 0 ≤ netOut phase.flow source := by
          have hnonneg : (0 : ℝ) ≤ phase.amount := Nat.cast_nonneg _
          linarith [hp.value]
        let result := (exactRun a z fuel phase.flow).eval G.cut
        have hi := ih phase.flow hp.feasible hp.integral hnextStart
        change PhaseHistory _ _ _ _ result.events result.flow ∧
          (∀ e ∈ result.events, 0 < e.amount) ∧ _ at hi
        have hlater : ∀ e ∈ result.events, bfsLevel data sink < e.distance := by
          cases hevents : result.events with
          | nil => simp only [List.not_mem_nil, false_implies, implies_true]
          | cons first rest =>
              have hfirst := exactRun_first G.cut a z fuel phase.flow first rest hevents
              let nextData := (bfsProg a z phase.flow source).eval G.cut
              obtain ⟨_, _, hnextPath⟩ := bfsProg_level_rise G a z phase.flow hp.feasible.1 source
              have path := hnextPath sink hfirst.1
              have hrise' : ∀ u v, 0 < (residualNetwork G a z phase.flow hp.feasible.1).c u v →
                  bfsLevel data v ≤ bfsLevel data u + 1 := hp.rise hrise
              have hle := path.level_le (bfsLevel data) hsource hrise'
              have hne : bfsLevel data sink ≠ bfsLevel nextData sink := by
                intro heq
                exact hp.blocks hfinished _ (path.tight (bfsLevel data) hsource hrise' heq)
              have hlt : bfsLevel data sink < first.distance := by
                have hfirstDistance : first.distance = bfsLevel nextData sink := hfirst.2
                rw [hfirstDistance]
                change bfsLevel data sink ≤ bfsLevel nextData sink at hle
                omega
              have horder := hi.1.increasing
              rw [hevents] at horder
              intro e he
              rcases List.mem_cons.mp he with rfl | he
              · exact hlt
              · exact hlt.trans ((List.pairwise_cons.mp horder).1 e he)
        rw [exactRun_eval_phase G.cut a z fuel f hunseen hfinished]
        refine ⟨PhaseHistory.step hf hsource hrise hp.value hi.1 hlater, ?_, ?_⟩
        · intro e he
          change e ∈ ⟨bfsLevel data sink, phase.amount⟩ :: result.events at he
          rcases List.mem_cons.mp he with rfl | he
          · exact hpositive
          · exact hi.2.1 e he
        · rw [exactRun_cost_phase G.cut a z fuel f hunseen hfinished]
          have hb := bfsProg_cost G.cut a z f source
          change (bfsProg a z f source).cost G.cut ≤ bfsBudget V at hb
          have hphase := unitPhaseProg_cost_sharp G a z (bfsLevel data) hsource f hf hint
          have htail := hi.2.2
          change (bfsProg a z f source).cost G.cut +
            ((unitPhaseProg a z (bfsLevel data) f).cost G.cut +
              (exactRun a z fuel phase.flow).cost G.cut) ≤
            historyBudget V (⟨bfsLevel data sink, phase.amount⟩ :: result.events)
          simp only [historyBudget, eventUnitWork, List.length_cons, List.map_cons,
            List.sum_cons] at htail ⊢
          change (unitPhaseProg a z (bfsLevel data) f).cost G.cut ≤
            (2 * Fintype.card (NetworkVertex V) + (bfsLevel data sink + 1) * phase.amount) *
              neighborBudget V at hphase
          nlinarith

theorem exactProg_history (G : WeightedGraph V) (hG : IntegralWeights G) (a z : V → ℕ) :
    let result := (exactProg a z).eval G.cut
    PhaseHistory (directed (twoStar G a z)) source sink (fun _ _ => 0)
      result.events result.flow ∧ (∀ e ∈ result.events, 0 < e.amount) ∧
      (exactProg a z).cost G.cut ≤ historyBudget V result.events := by
  apply exactRun_history G a z (exactFuel a) (fun _ _ => 0) (zero_stFlow G a z)
  · intro u v
    obtain ⟨k, hk⟩ := twoStar_integral hG a z u v
    exact ⟨k, by simpa only [residual_c, sub_zero] using hk⟩
  · simp [netOut]

theorem scaledExactProg_history (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (C : ℕ) (a z : V → ℕ) :
    let result := (scaledExactProg C a z).eval G.cut
    PhaseHistory (directed (twoStar (scaledInternal G C) a z)) source sink (fun _ _ => 0)
      result.events result.flow ∧ (∀ e ∈ result.events, 0 < e.amount) ∧
      (scaledExactProg C a z).cost G.cut ≤ historyBudget V result.events := by
  rw [scaledExactProg, scaleAnswers_eval, scaleAnswers_cost, ← scaledInternal_cut G C]
  exact exactProg_history _ (scaledInternal_integral hG C) a z

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactRun_first
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactRun_history
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactProg_history
