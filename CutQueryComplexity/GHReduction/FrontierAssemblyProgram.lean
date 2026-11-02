import CutQueryComplexity.GHReduction.FrontierExecution
import CutQueryComplexity.GHReduction.DisjointStarAssembly

/-! # Public backward assembly of an executed frontier trace

The program starts with one-terminal trees at the final blocks and traverses
the actual round records backwards. Each old block assembles its residual
tree and the trees at its actual child labels using the recorded shores and
queried values. Public guards reject incomplete leaves, incoherent states,
failed joins or incomplete final terminal coverage. No hidden graph enters
this postprocessing, and it makes no further oracle queries.

This module defines the full postprocessing and proves its concrete lookup
and leaf interfaces. Proving success on good, terminating traces additionally
requires the recursive attachment invariant; that theorem is not assumed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def collectBlockTrees (results : B → Option (PackedSteinerTree V)) :
    Option (B → PackedSteinerTree V) :=
  if h : ∀ b, ∃ T, results b = some T then some (fun b => Classical.choose (h b)) else none

theorem collectBlockTrees_spec (results : B → Option (PackedSteinerTree V))
    {out : B → PackedSteinerTree V} (hout : collectBlockTrees results = some out) :
    ∀ b, results b = some (out b) := by
  unfold collectBlockTrees at hout
  split at hout
  next h =>
    have he : (fun b => Classical.choose (h b)) = out := Option.some.inj hout
    intro b
    rw [← he]
    exact Classical.choose_spec (h b)
  next h => contradiction

theorem collectBlockTrees_exists (results : B → Option (PackedSteinerTree V))
    (h : ∀ b, ∃ T, results b = some T) :
    ∃ out, collectBlockTrees results = some out ∧ ∀ b, results b = some (out b) := by
  refine ⟨fun b => Classical.choose (h b), ?_, fun b => Classical.choose_spec (h b)⟩
  simp only [collectBlockTrees, dif_pos h]

def FrontierForest (state : PublicFrontierState V) := Fin state.size → PackedSteinerTree V

def PublicFrontierState.Discrete (state : PublicFrontierState V) : Prop :=
  ∀ b, (fiber state.block b).card = 1

def leafFrontierForest (state : PublicFrontierState V) : FrontierForest state :=
  fun b => singletonSteinerOutput (blockRepresentative state.block state.onto b)

theorem discrete_fiber_singleton (state : PublicFrontierState V) (h : state.Discrete)
    (b : Fin state.size) : fiber state.block b = {blockRepresentative state.block state.onto b} := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (h b)
  have hrep : blockRepresentative state.block state.onto b ∈ fiber state.block b :=
    (mem_fiber _ _ _).mpr (blockRepresentative_mem _ _ _)
  have he : blockRepresentative state.block state.onto b = v := by simpa only [hv, Finset.mem_singleton] using hrep
  simpa only [he] using hv

theorem singletonSteinerOutput_represents (r x : V) : Represents (singletonSteinerOutput r) x ↔ x = r := by
  constructor
  · rintro ⟨u, hu⟩
    exact hu.symm
  · rintro rfl
    exact ⟨(0 : Fin 1), rfl⟩

theorem leafFrontierForest_correct (G : WeightedGraph V) (state : PublicFrontierState V)
    (b : Fin state.size) : IsSteinerCutTree G (leafFrontierForest state b).value :=
  singletonSteinerOutput_correct G _

theorem leafFrontierForest_coverage (state : PublicFrontierState V) (h : state.Discrete)
    (b : Fin state.size) (x : V) : Represents (leafFrontierForest state b) x ↔ x ∈ fiber state.block b := by
  rw [discrete_fiber_singleton state h b, Finset.mem_singleton]
  exact singletonSteinerOutput_represents _ _

theorem leafFrontierForest_attach (state : PublicFrontierState V) (b : Fin state.size) (x y : V) :
    (leafFrontierForest state b).value.attach x = (leafFrontierForest state b).value.attach y := rfl

/-- The finite relabeling used by `advanceFrontierState`, not an independently
chosen correspondence with a scalar size ledger. -/
def frontierRoundLabel {levels : ℕ} (record : FrontierRoundRecord V levels)
    (c : RoundBlock (fun b => (record.split b).children)) : Fin record.after.size :=
  Fintype.equivFin _ c

def frontierRoundChild {levels : ℕ} (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) (b : Fin record.before.size) (i : V) : PackedSteinerTree V :=
  if hi : i ∈ (record.split b).children then
    forest (frontierRoundLabel record ⟨b, some ⟨i, hi⟩⟩)
  else forest (frontierRoundLabel record ⟨b, none⟩)

theorem frontierRoundChild_of_mem {levels : ℕ} (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) (b : Fin record.before.size) (i : V)
    (hi : i ∈ (record.split b).children) :
    frontierRoundChild record forest b i = forest (frontierRoundLabel record ⟨b, some ⟨i, hi⟩⟩) := by
  rw [frontierRoundChild, dif_pos hi]

def assembleFrontierBlock {levels : ℕ} (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) (b : Fin record.before.size) : Option (PackedSteinerTree V) :=
  assembleDisjointStar (forest (frontierRoundLabel record ⟨b, none⟩)) (record.split b).source
    (frontierRoundChild record forest b) (record.split b).shore (record.split b).value
    (record.split b).children.toList

def assembleFrontierRound {levels : ℕ} (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) : Option (FrontierForest record.before) :=
  collectBlockTrees (assembleFrontierBlock record forest)

theorem assembleFrontierRound_spec {levels : ℕ} (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) {out : FrontierForest record.before}
    (hout : assembleFrontierRound record forest = some out) :
    ∀ b, assembleFrontierBlock record forest b = some (out b) := collectBlockTrees_spec _ hout

/-- Public data only. All correctness and attachment facts are proved
externally about this value, never supplied as fields of an oracle solver. -/
structure FrontierForestState (V : Type) where
  state : PublicFrontierState V
  trees : FrontierForest state

def restoreFrontierRecord {levels : ℕ} (record : FrontierRoundRecord V levels)
    (forest : FrontierForestState V) : Option (FrontierForestState V) :=
  if h : forest.state = record.after then
    (assembleFrontierRound record (h ▸ forest.trees)).map (fun trees => ⟨record.before, trees⟩)
  else none

theorem restoreFrontierRecord_before {levels : ℕ} (record : FrontierRoundRecord V levels)
    (forest : FrontierForestState V) {out : FrontierForestState V}
    (hout : restoreFrontierRecord record forest = some out) : out.state = record.before := by
  unfold restoreFrontierRecord at hout
  split at hout
  next h =>
    cases hround : assembleFrontierRound record (h ▸ forest.trees) with
    | none => simp only [hround, Option.map_none, reduceCtorEq] at hout
    | some trees =>
        have he : (⟨record.before, trees⟩ : FrontierForestState V) = out := by
          simpa only [hround, Option.map_some, Option.some.injEq] using hout
        exact (congrArg FrontierForestState.state he).symm
  next h => contradiction

def restoreFrontierRecords {levels : ℕ} : List (FrontierRoundRecord V levels) →
    FrontierForestState V → Option (FrontierForestState V)
  | [], forest => some forest
  | record :: rest, forest =>
      (restoreFrontierRecords rest forest).bind (restoreFrontierRecord record)

def assembleFrontierTrace {levels : ℕ} (trace : FrontierTrace V levels) : Option (CutTree V) :=
  if trace.endState.Discrete then
    (restoreFrontierRecords trace.records ⟨trace.endState, leafFrontierForest trace.endState⟩).bind
      (fun forest =>
        let tree := forest.trees forest.state.tree.root
        if h : Function.Surjective tree.value.terminal then some (completeSteinerTree tree.value h)
        else none)
  else none

def assembleFrontierTraceProgram {levels : ℕ} (trace : FrontierTrace V levels) :
    Prog (Finset V) ℝ (Option (CutTree V)) := Prog.pure (assembleFrontierTrace trace)

@[simp] theorem assembleFrontierTraceProgram_eval {levels : ℕ} (trace : FrontierTrace V levels)
    (read : Finset V → ℝ) : Prog.eval read (assembleFrontierTraceProgram trace) = assembleFrontierTrace trace := rfl

@[simp] theorem assembleFrontierTraceProgram_cost {levels : ℕ} (trace : FrontierTrace V levels)
    (read : Finset V → ℝ) : Prog.cost read (assembleFrontierTraceProgram trace) = 0 := rfl

end
end CutQueryComplexity.GHReduction
