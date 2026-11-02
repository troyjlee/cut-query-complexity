import CutQueryComplexity.GHReduction.TreeJoin
import CutQueryComplexity.GHReduction.SteinerEndpoint
import CutQueryComplexity.Model.Prog
import Mathlib.Data.Fintype.EquivFin

/-! # A public finite fold assembling recursive terminal trees

Finite label types are packed into `Fin` so differently sized recursive
outputs can be stored in one list. Every join checks public terminal placement
and attachment consistency. A malformed list returns `none`. A successful fold
is correct when its supplied recursive outputs, separating shores, and queried
values are correct; bridge endpoint minimality follows from the existing
two-tree theorem rather than being a field of the input.

This is an actual zero-query assembly program. Producing the list from the
outer recursion and proving that its public guards succeed remain separate
obligations.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V U W : Type} [Fintype V] [DecidableEq V]
  [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

/-- Change only the public tree-label representation. -/
def relabelSteinerTree (T : SteinerCutTree V U) (e : U ≃ W) : SteinerCutTree V W where
  tree := {
    topology := relabelRootedTree T.tree.topology e
    weight := fun w => T.tree.weight (e.symm w)
    nonneg := fun w => T.tree.nonneg (e.symm w) }
  terminal := T.terminal ∘ e.symm
  attach := e ∘ T.attach
  attach_terminal w := by simp only [Function.comp_apply, T.attach_terminal, Equiv.apply_symm_apply]

@[simp] theorem relabelSteinerTree_terminal (T : SteinerCutTree V U) (e : U ≃ W) (u : U) :
    (relabelSteinerTree T e).terminal (e u) = T.terminal u := by
  simp only [relabelSteinerTree, Function.comp_apply, Equiv.symm_apply_apply]

theorem relabelSteinerTree_shore (T : SteinerCutTree V U) (e : U ≃ W) (u : U) :
    pull (relabelSteinerTree T e).attach ((relabelSteinerTree T e).tree.topology.D (e u)) =
      pull T.attach (T.tree.topology.D u) := by
  change pull (e ∘ T.attach) ((relabelRootedTree T.tree.topology e).D (e u)) = _
  rw [relabelRootedTree_subtree]
  ext v
  simp only [mem_pull, Function.comp_apply, Equiv.symm_apply_apply]

theorem relabelSteinerTree_correct (G : WeightedGraph V) (T : SteinerCutTree V U)
    (e : U ≃ W) (hT : IsSteinerCutTree G T) : IsSteinerCutTree G (relabelSteinerTree T e) := by
  intro w hw
  obtain ⟨u, rfl⟩ := e.surjective w
  have hu : u ≠ T.tree.topology.root := by
    intro he
    apply hw
    simpa only [relabelSteinerTree, relabelRootedTree] using congrArg e he
  obtain ⟨hmin, hweight⟩ := hT u hu
  have hparent : (relabelSteinerTree T e).terminal
      ((relabelSteinerTree T e).tree.topology.parent (e u)) =
        T.terminal (T.tree.topology.parent u) := by
    simp only [relabelSteinerTree, relabelRootedTree, Function.comp_apply,
      Equiv.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · rw [relabelSteinerTree_terminal T e u, hparent, relabelSteinerTree_shore T e u]
    exact hmin
  · change T.tree.weight (e.symm (e u)) = _
    rw [Equiv.symm_apply_apply, relabelSteinerTree_shore]
    exact hweight

/-- Public finite output data, with no hidden-graph correctness field. -/
structure PackedSteinerTree (V : Type) where
  size : ℕ
  value : SteinerCutTree V (Fin size)

def packSteinerTree (T : SteinerCutTree V U) : PackedSteinerTree V :=
  ⟨Fintype.card U, relabelSteinerTree T (Fintype.equivFin U)⟩

theorem packSteinerTree_correct (G : WeightedGraph V) (T : SteinerCutTree V U)
    (hT : IsSteinerCutTree G T) : IsSteinerCutTree G (packSteinerTree T).value :=
  relabelSteinerTree_correct G T (Fintype.equivFin U) hT

/-- A one-terminal recursive base case, including a singleton component. -/
def singletonSteinerOutput (r : V) : PackedSteinerTree V where
  size := 1
  value := {
    tree := {
      topology := {
        root := 0
        parent := fun _ => 0
        depth := fun _ => 0
        parent_root := rfl
        depth_root := rfl
        depth_parent := by
          intro v hv
          exact (hv (Subsingleton.elim _ _)).elim }
      weight := fun _ => 0
      nonneg := fun _ => le_rfl }
    terminal := fun _ => r
    attach := fun _ => 0
    attach_terminal := fun _ => Subsingleton.elim _ _ }

theorem singletonSteinerOutput_correct (G : WeightedGraph V) (r : V) :
    IsSteinerCutTree G (singletonSteinerOutput r).value := by
  intro u hu
  exact (hu (Subsingleton.elim (α := Fin 1) _ _)).elim

/-- Every condition is a finite predicate on the supplied public trees and
shore. It does not inspect the hidden graph or assert a cut optimum. -/
def SteinerJoinGuard (L R : PackedSteinerTree V) (S : Finset V) (s t : V) : Prop :=
  (∃ u, L.value.terminal u = s) ∧
  (∃ v, R.value.terminal v = t) ∧
  (∀ u, L.value.terminal u ∈ S) ∧
  (∀ v, R.value.terminal v ∉ S) ∧
  (∀ x, x ∉ S → L.value.attach x = L.value.attach t) ∧
  (∀ x ∈ S, R.value.attach x = R.value.attach s)

def checkedSteinerJoin (L R : PackedSteinerTree V) (S : Finset V) (s t : V) (value : ℝ) :
    Option (PackedSteinerTree V) :=
  if h : SteinerJoinGuard L R S s t then
    some (packSteinerTree (joinSteinerTrees S L.value R.value
      (L.value.attach t) (R.value.attach s) value h.2.2.1 h.2.2.2.1))
  else none

theorem checkedSteinerJoin_correct (G : WeightedGraph V) (L R : PackedSteinerTree V)
    (hL : IsSteinerCutTree G L.value) (hR : IsSteinerCutTree G R.value)
    (S : Finset V) (s t : V) (value : ℝ) (hS : IsSTMinCut G s t S)
    (hvalue : value = G.cut S) (out : PackedSteinerTree V)
    (hout : checkedSteinerJoin L R S s t value = some out) :
    IsSteinerCutTree G out.value := by
  by_cases h : SteinerJoinGuard L R S s t
  · obtain ⟨u, hu⟩ := h.1
    obtain ⟨v, hv⟩ := h.2.1
    have hjoined := joinSteinerTrees_correct G S L.value R.value hL hR u v
      (by simpa only [hu, hv] using hS) h.2.2.1 h.2.2.2.1
      (by simpa only [hv] using h.2.2.2.2.1)
      (by simpa only [hu] using h.2.2.2.2.2) value hvalue
    have hcorrect : IsSteinerCutTree G
        (packSteinerTree (joinSteinerTrees S L.value R.value
          (L.value.attach t) (R.value.attach s) value h.2.2.1 h.2.2.2.1)).value := by
      apply packSteinerTree_correct G
      simpa only [hu, hv] using hjoined
    have hout' : packSteinerTree (joinSteinerTrees S L.value R.value
        (L.value.attach t) (R.value.attach s) value h.2.2.1 h.2.2.2.1) = out := by
      simpa only [checkedSteinerJoin, h, dite_true, Option.some.injEq] using hout
    exact hout' ▸ hcorrect
  · simp [checkedSteinerJoin, h] at hout

/-- One public instruction appending a recursive output tree. The separating
shore is oriented toward the accumulated tree, away from the new child. -/
structure SteinerAssemblyStep (V : Type) where
  child : PackedSteinerTree V
  shore : Finset V
  leftTerminal : V
  rightTerminal : V
  value : ℝ

def SteinerAssemblyStep.Correct (G : WeightedGraph V) (step : SteinerAssemblyStep V) : Prop :=
  IsSteinerCutTree G step.child.value ∧
  IsSTMinCut G step.leftTerminal step.rightTerminal step.shore ∧
  step.value = G.cut step.shore

def assembleSteinerSteps : PackedSteinerTree V → List (SteinerAssemblyStep V) →
    Option (PackedSteinerTree V)
  | base, [] => some base
  | base, step :: rest =>
      (checkedSteinerJoin base step.child step.shore step.leftTerminal step.rightTerminal
        step.value).bind (fun next => assembleSteinerSteps next rest)

theorem assembleSteinerSteps_correct (G : WeightedGraph V) (base : PackedSteinerTree V)
    (hbase : IsSteinerCutTree G base.value) (steps : List (SteinerAssemblyStep V))
    (hsteps : ∀ step ∈ steps, step.Correct G) (out : PackedSteinerTree V)
    (hout : assembleSteinerSteps base steps = some out) : IsSteinerCutTree G out.value := by
  induction steps generalizing base with
  | nil =>
      have he : base = out := by simpa only [assembleSteinerSteps, Option.some.injEq] using hout
      exact he ▸ hbase
  | cons step rest ih =>
      have hstep := hsteps step (by simp)
      have hrest : ∀ next ∈ rest, next.Correct G := fun next hn => hsteps next (by simp [hn])
      cases hj : checkedSteinerJoin base step.child step.shore step.leftTerminal step.rightTerminal
          step.value with
      | none => simp only [assembleSteinerSteps, hj, Option.bind_none, reduceCtorEq] at hout
      | some next =>
          have hnext := checkedSteinerJoin_correct G base step.child hbase hstep.1
            step.shore step.leftTerminal step.rightTerminal step.value hstep.2.1 hstep.2.2 next hj
          apply ih next hnext hrest
          simpa only [assembleSteinerSteps, hj, Option.bind_some] using hout

/-- A public coverage guard removes the terminal representation only when
every original vertex is present. -/
def finishSteinerAssembly (base : PackedSteinerTree V) (steps : List (SteinerAssemblyStep V)) :
    Option (CutTree V) :=
  (assembleSteinerSteps base steps).bind (fun out =>
    if h : Function.Surjective out.value.terminal then some (completeSteinerTree out.value h)
    else none)

theorem finishSteinerAssembly_correct (G : WeightedGraph V) (base : PackedSteinerTree V)
    (hbase : IsSteinerCutTree G base.value) (steps : List (SteinerAssemblyStep V))
    (hsteps : ∀ step ∈ steps, step.Correct G) (out : CutTree V)
    (hout : finishSteinerAssembly base steps = some out) : IsGomoryHuTree G out := by
  cases hfold : assembleSteinerSteps base steps with
  | none => simp only [finishSteinerAssembly, hfold, Option.bind_none, reduceCtorEq] at hout
  | some packed =>
      have hcorrect := assembleSteinerSteps_correct G base hbase steps hsteps packed hfold
      by_cases hcover : Function.Surjective packed.value.terminal
      · have he : completeSteinerTree packed.value hcover = out := by
          simpa only [finishSteinerAssembly, hfold, Option.bind_some, hcover, dite_true,
            Option.some.injEq] using hout
        exact he ▸ completeSteinerTree_correct G packed.value hcover hcorrect
      · simp only [finishSteinerAssembly, hfold, Option.bind_some, hcover, dite_false,
          reduceCtorEq] at hout

/-- Public postprocessing is an actual query program with zero calls for
every oracle, including malformed answer histories. -/
def assembleSteinerProgram (base : PackedSteinerTree V) (steps : List (SteinerAssemblyStep V)) :
    Prog (Finset V) ℝ (Option (PackedSteinerTree V)) :=
  Prog.pure (assembleSteinerSteps base steps)

@[simp] theorem assembleSteinerProgram_eval (base : PackedSteinerTree V)
    (steps : List (SteinerAssemblyStep V)) (read : Finset V → ℝ) :
    Prog.eval read (assembleSteinerProgram base steps) = assembleSteinerSteps base steps := rfl

@[simp] theorem assembleSteinerProgram_cost (base : PackedSteinerTree V)
    (steps : List (SteinerAssemblyStep V)) (read : Finset V → ℝ) :
    Prog.cost read (assembleSteinerProgram base steps) = 0 := rfl

def finishSteinerProgram (base : PackedSteinerTree V) (steps : List (SteinerAssemblyStep V)) :
    Prog (Finset V) ℝ (Option (CutTree V)) := Prog.pure (finishSteinerAssembly base steps)

@[simp] theorem finishSteinerProgram_eval (base : PackedSteinerTree V)
    (steps : List (SteinerAssemblyStep V)) (read : Finset V → ℝ) :
    Prog.eval read (finishSteinerProgram base steps) = finishSteinerAssembly base steps := rfl

@[simp] theorem finishSteinerProgram_cost (base : PackedSteinerTree V)
    (steps : List (SteinerAssemblyStep V)) (read : Finset V → ℝ) :
    Prog.cost read (finishSteinerProgram base steps) = 0 := rfl

end
end CutQueryComplexity.GHReduction
