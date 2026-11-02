import CutQueryComplexity.DeterministicAPMCExpansion.Flow.DFS
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.Tail
import CutQueryComplexity.DirectedUnitST.Blocking.Run

/-!
# An actual unit-augmentation blocking phase

The program repeatedly executes the residual DFS, sends one unit on each
complete path, and retains the discovered dead vertices. Every successful
path is integral in the original capacity units. Public fuel guarantees
termination on arbitrary transcripts; on integral feasible inputs, source
capacity proves that the fuel cannot expire before the phase blocks.

No graph or feasibility certificate is an input to the program. Proof-side
network parameters below certify its executions against the cut oracle.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate DirectedCertificate Prog
open DirectedUnitST.Repair
open DirectedUnitST.Blocking (Frame StackPath LevelPath DeadClosed IntegralCap
  stackArcs pathUse pathDelta pathDelta_forward pathDelta_off_le pathUse_forward
  integralCap_residual deadClosed_residual feasible_add_flow residual_add_flow)
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def unitUpdate (f : NetworkVertex V → NetworkVertex V → ℝ)
    (stack : List (Frame V)) : NetworkVertex V → NetworkVertex V → ℝ :=
  fun u v => f u v + pathDelta stack 1 u v

/-- Positive integral residual capacity supports a whole unit of flow. -/
theorem unit_path_feasible {H : WeightedDiGraph (NetworkVertex V)}
    {level : NetworkVertex V → ℕ} {s : NetworkVertex V} {stack : List (Frame V)}
    (hint : IntegralCap H) (hp : StackPath H level s stack) :
    H.Feasible (pathDelta stack 1) := by
  refine ⟨phaseDelta_isFlow _, ?_⟩
  intro u v
  by_cases he : (u, v) ∈ stackArcs stack
  · rw [pathDelta_forward hp 1 he]
    obtain ⟨k, hk⟩ := hint u v
    have hpos := (hp.arc he).1
    rw [hk] at hpos ⊢
    have hkpos : 0 < k := by exact_mod_cast hpos
    exact_mod_cast (show 1 ≤ k by omega)
  · exact (pathDelta_off_le stack 1 he).trans (H.nonneg u v)

theorem unitUpdate_feasible {H : WeightedDiGraph (NetworkVertex V)}
    {f : NetworkVertex V → NetworkVertex V → ℝ} (hf : H.Feasible f)
    {level : NetworkVertex V → ℕ} {s : NetworkVertex V} {stack : List (Frame V)}
    (hint : IntegralCap (residual H f hf))
    (hp : StackPath (residual H f hf) level s stack) :
    H.Feasible (unitUpdate f stack) :=
  feasible_add_flow H f _ hf (unit_path_feasible hint hp)

theorem unitUpdate_divergence {H : WeightedDiGraph (NetworkVertex V)}
    {level : NetworkVertex V → ℕ} {s : NetworkVertex V} {stack : List (Frame V)}
    (hp : StackPath H level s stack) (f : NetworkVertex V → NetworkVertex V → ℝ)
    {head : Frame V} {tail : List (Frame V)} (hstack : stack = head :: tail)
    (v : NetworkVertex V) :
    netOut (unitUpdate f stack) v = netOut f v +
      (if v = s then (1 : ℝ) else 0) - (if v = head.vertex then (1 : ℝ) else 0) := by
  simp only [unitUpdate, netOut, sum_add_distrib]
  change netOut f v + netOut (pathDelta stack 1) v = _
  rw [hp.pathDelta_netOut 1 head tail hstack]
  push_cast
  dsimp only [netOut]
  ring

theorem unitUpdate_stFlow {H : WeightedDiGraph (NetworkVertex V)}
    {s t : NetworkVertex V} {f : NetworkVertex V → NetworkVertex V → ℝ}
    (hf : H.STFlow s t f) {level : NetworkVertex V → ℕ} {stack : List (Frame V)}
    (hint : IntegralCap (residual H f hf.1))
    (hp : StackPath (residual H f hf.1) level s stack)
    {head : Frame V} {tail : List (Frame V)} (hstack : stack = head :: tail)
    (ht : head.vertex = t) : H.STFlow s t (unitUpdate f stack) := by
  refine ⟨unitUpdate_feasible hf.1 hint hp, ?_⟩
  intro v hvs hvt
  rw [unitUpdate_divergence hp f hstack v, ht, hf.2 v hvs hvt]
  simp only [hvs, hvt, ↓reduceIte, add_zero, sub_zero]

theorem unitUpdate_integral {H : WeightedDiGraph (NetworkVertex V)}
    {f : NetworkVertex V → NetworkVertex V → ℝ} (hf : H.Feasible f)
    {level : NetworkVertex V → ℕ} {s : NetworkVertex V} {stack : List (Frame V)}
    (hint : IntegralCap (residual H f hf))
    (hp : StackPath (residual H f hf) level s stack) :
    IntegralCap (residual H (unitUpdate f stack) (unitUpdate_feasible hf hint hp)) := by
  have h := integralCap_residual hint (pathUse stack 1) (unit_path_feasible hint hp)
  change IntegralCap (residual (residual H f hf) (pathDelta stack 1)
    (unit_path_feasible hint hp)) at h
  rw [residual_add_flow H f (pathDelta stack 1) hf (unit_path_feasible hint hp)] at h
  exact h

theorem unitUpdate_deadClosed {H : WeightedDiGraph (NetworkVertex V)}
    {f : NetworkVertex V → NetworkVertex V → ℝ} (hf : H.Feasible f)
    {level : NetworkVertex V → ℕ} {s t : NetworkVertex V} {stack : List (Frame V)}
    (hint : IntegralCap (residual H f hf))
    (hp : StackPath (residual H f hf) level s stack) {dead : Finset (NetworkVertex V)}
    (hd : DeadClosed (residual H f hf) level t dead) :
    DeadClosed (residual H (unitUpdate f stack) (unitUpdate_feasible hf hint hp)) level t dead := by
  have h := deadClosed_residual hd (pathUse stack 1) (pathUse_forward hp 1)
    (unit_path_feasible hint hp)
  change DeadClosed (residual (residual H f hf) (pathDelta stack 1)
    (unit_path_feasible hint hp)) level t dead at h
  rw [residual_add_flow H f (pathDelta stack 1) hf (unit_path_feasible hint hp)] at h
  exact h

theorem unitUpdate_rise {H : WeightedDiGraph (NetworkVertex V)}
    {f : NetworkVertex V → NetworkVertex V → ℝ} (hf : H.Feasible f)
    {level : NetworkVertex V → ℕ} {s : NetworkVertex V} {stack : List (Frame V)}
    (hint : IntegralCap (residual H f hf))
    (hp : StackPath (residual H f hf) level s stack)
    (hrise : ∀ u v, 0 < H.c u v - f u v → level v ≤ level u + 1) :
    ∀ u v, 0 < H.c u v - unitUpdate f stack u v → level v ≤ level u + 1 := by
  have hriseR : ∀ u v, 0 < (residual H f hf).c u v →
      (level v : ℝ) ≤ level u + 1 := by
    intro u v hpos
    exact_mod_cast hrise u v hpos
  have hforward : ∀ u v, 0 < pathDelta stack 1 u v →
      (level v : ℝ) = level u + 1 := by
    intro u v hpos
    apply phaseDelta_pos_forward (fun u v => (pathUse stack 1 u v : ℝ))
      (fun v => (level v : ℝ)) (fun _ _ => Nat.cast_nonneg _) _ hpos
    intro x y huse
    have huseNat : pathUse stack 1 x y ≠ 0 := by exact_mod_cast huse
    exact_mod_cast pathUse_forward hp 1 x y huseNat
  intro u v hpos
  have hp' : 0 < (residual (residual H f hf) (pathDelta stack 1)
      (unit_path_feasible hint hp)).c u v := by
    simp only [residual_c, unitUpdate] at hpos ⊢
    linarith
  exact_mod_cast residual_level_rise (residual H f hf) (fun v => (level v : ℝ))
    hriseR (pathDelta stack 1) (unit_path_feasible hint hp) hforward u v hp'

structure UnitPhaseResult (V : Type) where
  flow : NetworkVertex V → NetworkVertex V → ℝ
  dead : Finset (NetworkVertex V)
  amount : ℕ
  finished : Bool

def unitPhaseEmpty (f : NetworkVertex V → NetworkVertex V → ℝ)
    (dead : Finset (NetworkVertex V)) (finished : Bool) : UnitPhaseResult V :=
  ⟨f, dead, 0, finished⟩

def unitPhaseMore (result : UnitPhaseResult V) : UnitPhaseResult V :=
  { result with amount := result.amount + 1 }

def unitPhaseRun (a z : V → ℕ) (level : NetworkVertex V → ℕ)
    (s t : NetworkVertex V) : ℕ → (NetworkVertex V → NetworkVertex V → ℝ) →
      Finset (NetworkVertex V) → Prog (Finset V) ℝ (UnitPhaseResult V)
  | 0, f, dead => .pure (unitPhaseEmpty f dead false)
  | fuel + 1, f, dead => (dfsProg a z f level dead s t).bind fun data =>
      match data.stack with
      | [] => .pure (unitPhaseEmpty f data.dead true)
      | head :: _ =>
          if head.vertex = t then
            (unitPhaseRun a z level s t fuel (unitUpdate f data.stack) data.dead).map unitPhaseMore
          else .pure (unitPhaseEmpty f data.dead false)

theorem unitPhaseRun_cost (read : Finset V → ℝ) (a z : V → ℕ)
    (level : NetworkVertex V → ℕ) (s t : NetworkVertex V) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (dead : Finset (NetworkVertex V)) :
    (unitPhaseRun a z level s t fuel f dead).cost read ≤ fuel * bfsBudget V := by
  induction fuel generalizing f dead with
  | zero => simp [unitPhaseRun]
  | succ fuel ih =>
      simp only [unitPhaseRun, Prog.cost_bind]
      have hdfs := dfsProg_cost read a z f level dead s t
      change (dfsProg a z f level dead s t).cost read ≤ bfsBudget V at hdfs
      cases hs : ((dfsProg a z f level dead s t).eval read).stack with
      | nil =>
          simp only [Prog.cost_pure, Nat.add_zero]
          rw [Nat.succ_mul]
          omega
      | cons head tail =>
          dsimp only
          split_ifs
          · simp only [Prog.cost_map]
            have hi := ih (unitUpdate f (head :: tail))
              ((dfsProg a z f level dead s t).eval read).dead
            rw [Nat.succ_mul]
            omega
          · simp only [Prog.cost_pure, Nat.add_zero]
            rw [Nat.succ_mul]
            omega

/-- Inductive semantic facts about the actual finite phase execution.
`unfinished` will rule out exhaustion using only the source capacity. -/
structure UnitPhaseFacts (H : WeightedDiGraph (NetworkVertex V))
    (level : NetworkVertex V → ℕ) (s t : NetworkVertex V)
    (initial : NetworkVertex V → NetworkVertex V → ℝ) (fuel : ℕ)
    (result : UnitPhaseResult V) : Prop where
  feasible : H.STFlow s t result.flow
  integral : IntegralCap (residual H result.flow feasible.1)
  closed : DeadClosed (residual H result.flow feasible.1) level t result.dead
  value : netOut result.flow s = netOut initial s + result.amount
  zero : result.amount = 0 → result.flow = initial
  blocks : result.finished = true →
    ∀ d, ¬ LevelPath (residual H result.flow feasible.1) level s t d
  unfinished : result.finished = false → result.amount = fuel
  rise : (∀ u v, 0 < H.c u v - initial u v → level v ≤ level u + 1) →
    ∀ u v, 0 < H.c u v - result.flow u v → level v ≤ level u + 1

theorem unitPhaseRun_facts (G : WeightedGraph V) (a z : V → ℕ)
    (level : NetworkVertex V → ℕ) (s t : NetworkVertex V) (hst : s ≠ t) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (dead : Finset (NetworkVertex V))
    (hf : (directed (twoStar G a z)).STFlow s t f)
    (hint : IntegralCap (residualNetwork G a z f hf.1))
    (hd : DeadClosed (residualNetwork G a z f hf.1) level t dead) :
    UnitPhaseFacts (directed (twoStar G a z)) level s t f fuel
      ((unitPhaseRun a z level s t fuel f dead).eval G.cut) := by
  induction fuel generalizing f dead with
  | zero =>
      refine ⟨hf, hint, hd, ?_, ?_, ?_, ?_, ?_⟩
      · simp [unitPhaseRun, unitPhaseEmpty]
      · intro _; rfl
      · simp [unitPhaseRun, unitPhaseEmpty]
      · intro _; rfl
      · exact fun hrise => hrise
  | succ fuel ih =>
      let data := (dfsProg a z f level dead s t).eval G.cut
      have hdfs := dfsProg_complete G a z f hf.1 level dead s t hd
      change DFSInvariant (residualNetwork G a z f hf.1) level s t data ∧
        DFSFinished t data at hdfs
      simp only [unitPhaseRun, Prog.eval_bind]
      change UnitPhaseFacts _ _ _ _ _ _
        ((match data.stack with
          | [] => Prog.pure (unitPhaseEmpty f data.dead true)
          | head :: _ => if head.vertex = t then
              (unitPhaseRun a z level s t fuel (unitUpdate f data.stack) data.dead).map unitPhaseMore
            else Prog.pure (unitPhaseEmpty f data.dead false)).eval G.cut)
      cases hstack : data.stack with
      | nil =>
          simp only [Prog.eval_pure]
          refine ⟨hf, hint, hdfs.1.closed, ?_, ?_, ?_, ?_, ?_⟩
          · simp [unitPhaseEmpty]
          · intro _; rfl
          · intro _
            exact dfsProg_exhausted_blocks G a z f hf.1 level dead s t hd hstack
          · simp [unitPhaseEmpty]
          · exact fun hrise => hrise
      | cons head tail =>
          have ht : head.vertex = t := by
            rcases hdfs.2 with he | ⟨head', tail', he, ht⟩
            · rw [hstack] at he; contradiction
            · rw [hstack] at he
              cases he
              exact ht
          have hpath : StackPath (residualNetwork G a z f hf.1) level s data.stack := by
            rcases hdfs.1.path with he | hp
            · rw [hstack] at he; contradiction
            · exact hp
          have hf' := unitUpdate_stFlow hf hint hpath hstack ht
          have hint' := unitUpdate_integral hf.1 hint hpath
          have hd' := unitUpdate_deadClosed hf.1 hint hpath hdfs.1.closed
          have hi := ih (unitUpdate f data.stack) data.dead hf' hint' hd'
          simp only [ht, ↓reduceIte, Prog.eval_map, unitPhaseMore]
          rw [← hstack]
          refine ⟨hi.feasible, hi.integral, hi.closed, ?_, ?_, hi.blocks, ?_, ?_⟩
          · have hv := unitUpdate_divergence hpath f hstack s
            rw [ht] at hv
            simp only [hst, ↓reduceIte, sub_zero] at hv
            change netOut _ s = netOut f s + ((_: ℕ) + 1 : ℕ)
            rw [Nat.cast_add, Nat.cast_one]
            linarith [hi.value]
          · intro hz
            change _ + 1 = 0 at hz
            omega
          · intro hu
            have ha := hi.unfinished hu
            change _ + 1 = fuel + 1
            omega
          · intro hrise
            exact hi.rise (unitUpdate_rise hf.1 hint hpath hrise)

/-- One extra DFS beyond the source-capacity fuel is enough to witness
blocking. The algorithm does not assume that the source star is saturable. -/
def unitPhaseProg (a z : V → ℕ) (level : NetworkVertex V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) :
    Prog (Finset V) ℝ (UnitPhaseResult V) :=
  unitPhaseRun a z level source sink ((∑ v, a v) + 1) f ∅

theorem unitPhaseProg_facts (G : WeightedGraph V) (a z : V → ℕ)
    (level : NetworkVertex V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).STFlow source sink f)
    (hint : IntegralCap (residualNetwork G a z f hf.1)) :
    UnitPhaseFacts (directed (twoStar G a z)) level source sink f ((∑ v, a v) + 1)
      ((unitPhaseProg a z level f).eval G.cut) := by
  apply unitPhaseRun_facts G a z level source sink source_ne_sink _ _ _ hf hint
  exact ⟨notMem_empty _, fun _ h => False.elim (notMem_empty _ h)⟩

theorem unitPhaseProg_finishes (G : WeightedGraph V) (a z : V → ℕ)
    (level : NetworkVertex V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).STFlow source sink f)
    (hint : IntegralCap (residualNetwork G a z f hf.1)) (hstart : 0 ≤ netOut f source) :
    ((unitPhaseProg a z level f).eval G.cut).finished = true := by
  let result := (unitPhaseProg a z level f).eval G.cut
  have facts := unitPhaseProg_facts G a z level f hf hint
  change UnitPhaseFacts _ _ _ _ _ _ result at facts
  change result.finished = true
  cases hfinished : result.finished with
  | true => rfl
  | false =>
      have hamount := facts.unfinished hfinished
      have hcap := netOut_le_source_capacity G a z result.flow facts.feasible.1
      have hvalue := facts.value
      rw [hamount, Nat.cast_add, Nat.cast_one] at hvalue
      linarith

/-- Positive amount is derived from the actual blocking execution and a
reachable frozen-level target. It is measured before capacity normalization. -/
theorem unitPhaseProg_amount_pos (G : WeightedGraph V) (a z : V → ℕ)
    (level : NetworkVertex V → ℕ) (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).STFlow source sink f)
    (hint : IntegralCap (residualNetwork G a z f hf.1)) (hstart : 0 ≤ netOut f source)
    {d : ℕ} (path : LevelPath (residualNetwork G a z f hf.1) level source sink d) :
    0 < ((unitPhaseProg a z level f).eval G.cut).amount := by
  let result := (unitPhaseProg a z level f).eval G.cut
  have facts := unitPhaseProg_facts G a z level f hf hint
  change UnitPhaseFacts _ _ _ _ _ _ result at facts
  have finished := unitPhaseProg_finishes G a z level f hf hint hstart
  change 0 < result.amount
  by_contra hn
  have hzero : result.amount = 0 := by omega
  have hflow := facts.zero hzero
  have he : residual (directed (twoStar G a z)) result.flow facts.feasible.1 =
      residualNetwork G a z f hf.1 := by
    apply DirectedUnitST.Blocking.network_eq_of_capacity
    intro u v
    simp only [residual_c, hflow]
  have hb := facts.blocks finished d
  rw [he] at hb
  exact hb path

/-- Drop the initial stack credit but retain dead-vertex credit across calls. -/
theorem unit_dfs_charged (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).Feasible f)
    (level : NetworkVertex V → ℕ) (dead : Finset (NetworkVertex V))
    (s t : NetworkVertex V) (hd : DeadClosed (residualNetwork G a z f hf) level t dead) :
    (dfsProg a z f level dead s t).cost G.cut + 2 * dead.card * neighborBudget V ≤
      ((dfsProg a z f level dead s t).eval G.cut).charge * neighborBudget V := by
  have h := dfsRun_cost_charged G a z f hf level s t
    (2 * Fintype.card (NetworkVertex V)) (initialDFS dead s)
    (initialDFS_invariant _ level dead s t hd)
  change (dfsProg a z f level dead s t).cost G.cut +
    (initialDFS dead s).charge * neighborBudget V ≤
      ((dfsProg a z f level dead s t).eval G.cut).charge * neighborBudget V at h
  have hc : 2 * dead.card ≤ (initialDFS dead s).charge := by
    simp only [DFSData.charge, initialDFS]
    omega
  have hm := Nat.mul_le_mul_right (neighborBudget V) hc
  omega

/-- Amortization over the executed phase, including every unsuccessful row
search. A dead vertex is charged once; every sent unit pays its path length. -/
theorem unitPhaseRun_cost_charged (G : WeightedGraph V) (a z : V → ℕ)
    (level : NetworkVertex V → ℕ) (s t : NetworkVertex V) (hst : s ≠ t)
    (hs : level s = 0) (fuel : ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (dead : Finset (NetworkVertex V))
    (hf : (directed (twoStar G a z)).STFlow s t f)
    (hint : IntegralCap (residualNetwork G a z f hf.1))
    (hd : DeadClosed (residualNetwork G a z f hf.1) level t dead) :
    let program := unitPhaseRun a z level s t fuel f dead
    let result := program.eval G.cut
    program.cost G.cut + 2 * dead.card * neighborBudget V ≤
      (2 * result.dead.card + (level t + 1) * result.amount) * neighborBudget V := by
  induction fuel generalizing f dead with
  | zero => simp [unitPhaseRun, unitPhaseEmpty]
  | succ fuel ih =>
      let data := (dfsProg a z f level dead s t).eval G.cut
      have hdfs := dfsProg_complete G a z f hf.1 level dead s t hd
      change DFSInvariant (residualNetwork G a z f hf.1) level s t data ∧
        DFSFinished t data at hdfs
      have hcost := unit_dfs_charged G a z f hf.1 level dead s t hd
      change (dfsProg a z f level dead s t).cost G.cut +
        2 * dead.card * neighborBudget V ≤ data.charge * neighborBudget V at hcost
      simp only [unitPhaseRun, Prog.cost_bind, Prog.eval_bind]
      cases hstack : data.stack with
      | nil =>
          simp only [show (dfsProg a z f level dead s t).eval G.cut = data from rfl,
            hstack, Prog.cost_pure, Prog.eval_pure, unitPhaseEmpty, Nat.add_zero,
            Nat.mul_zero]
          simpa only [DFSData.charge, hstack, List.length_nil, Nat.add_zero] using hcost
      | cons head tail =>
          have ht : head.vertex = t := by
            rcases hdfs.2 with he | ⟨head', tail', he, ht⟩
            · rw [hstack] at he; contradiction
            · rw [hstack] at he
              cases he
              exact ht
          have hp : StackPath (residualNetwork G a z f hf.1) level s data.stack := by
            rcases hdfs.1.path with he | hp
            · rw [hstack] at he; contradiction
            · exact hp
          have hlength : data.stack.length = level t + 1 := by
            have h := stackPath_length hp head tail hstack
            rw [hs, ht, Nat.zero_add] at h
            exact h.symm
          have hf' := unitUpdate_stFlow hf hint hp hstack ht
          have hint' := unitUpdate_integral hf.1 hint hp
          have hd' := unitUpdate_deadClosed hf.1 hint hp hdfs.1.closed
          have hi := ih (unitUpdate f data.stack) data.dead hf' hint' hd'
          simp only [show (dfsProg a z f level dead s t).eval G.cut = data from rfl,
            hstack, ht, ↓reduceIte, Prog.cost_map, Prog.eval_map, unitPhaseMore]
          simp only [DFSData.charge, hlength] at hcost
          dsimp only at hi
          rw [← hstack]
          nlinarith

theorem unitPhaseProg_cost_sharp (G : WeightedGraph V) (a z : V → ℕ)
    (level : NetworkVertex V → ℕ) (hs : level source = 0)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (hf : (directed (twoStar G a z)).STFlow source sink f)
    (hint : IntegralCap (residualNetwork G a z f hf.1)) :
    (unitPhaseProg a z level f).cost G.cut ≤
      (2 * Fintype.card (NetworkVertex V) +
        (level sink + 1) * ((unitPhaseProg a z level f).eval G.cut).amount) * neighborBudget V := by
  have hd : DeadClosed (residualNetwork G a z f hf.1) level sink ∅ :=
    ⟨notMem_empty _, fun _ h => False.elim (notMem_empty _ h)⟩
  have h := unitPhaseRun_cost_charged G a z level source sink source_ne_sink hs
    ((∑ v, a v) + 1) f ∅ hf hint hd
  change (unitPhaseProg a z level f).cost G.cut + 2 * (∅ : Finset (NetworkVertex V)).card *
    neighborBudget V ≤
      (2 * ((unitPhaseProg a z level f).eval G.cut).dead.card +
        (level sink + 1) * ((unitPhaseProg a z level f).eval G.cut).amount) *
        neighborBudget V at h
  simp only [card_empty, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at h
  have hc := card_le_univ ((unitPhaseProg a z level f).eval G.cut).dead
  exact h.trans (Nat.mul_le_mul_right (neighborBudget V)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) _))

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.unit_path_feasible
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitUpdate_stFlow
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitUpdate_integral
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitPhaseRun_facts
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitPhaseProg_finishes
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitPhaseProg_amount_pos
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitPhaseProg_cost_sharp
