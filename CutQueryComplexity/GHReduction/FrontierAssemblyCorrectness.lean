import CutQueryComplexity.GHReduction.RoundForestAssembly
import CutQueryComplexity.GHReduction.FrontierWitnessInduction

/-! # Full backward assembly on a good terminating execution trace

Singleton leaves satisfy the recursive forest invariant. Each reverse round
proves its own join guards, preserves full minimum-cut shores and terminal
coverage, and preserves attachment compatibility with the preceding frontier.
The induction follows the concrete record list. At the initial one-block
state the assembled tree represents every original vertex, so the public
coverage guard succeeds and yields a genuine cut-equivalent tree.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A proved recursive invariant, external to every algorithm data type. -/
def FrontierForestSound (G : WeightedGraph V) (state : PublicFrontierState V)
    (forest : FrontierForest state) : Prop :=
  (∀ b, IsSteinerCutTree G (forest b).value) ∧
  (∀ b x, Represents (forest b) x ↔ state.block x = b) ∧
  ForestCompatible state.block state.tree forest

theorem leafFrontierForest_sound (G : WeightedGraph V) (state : PublicFrontierState V)
    (hdiscrete : state.Discrete) : FrontierForestSound G state (leafFrontierForest state) := by
  refine ⟨leafFrontierForest_correct G state, ?_, leafFrontierForest_compatible state⟩
  intro b x
  exact (leafFrontierForest_coverage state hdiscrete b x).trans (mem_fiber state.block b x)

theorem assembleFrontierRound_success (G : WeightedGraph V) {levels : ℕ}
    (record : FrontierRoundRecord V levels) (hbefore : record.before.Witnessed G)
    (hgood : record.Good G) (forest : FrontierForest record.after)
    (hforest : FrontierForestSound G record.after forest) :
    ∃ out, assembleFrontierRound record forest = some out ∧ FrontierForestSound G record.before out := by
  let I := fun b => (record.split b).children
  let S := fun b => (record.split b).shore
  let a := roundSplitAttachment record.before.block record.before.onto I S
  let p := roundBlockMap record.before.block I S
  let T := roundBlockTree record.before.tree I a
  let e := Fintype.equivFin (RoundBlock I)
  let raw := fun z : RoundBlock I => forest (frontierRoundLabel record z)
  have hrawCorrect : ∀ z, IsSteinerCutTree G (raw z).value :=
    fun z => hforest.1 (frontierRoundLabel record z)
  have hrawCover : ∀ z x, Represents (raw z) x ↔ p x = z := by
    intro z x
    rw [hforest.2.1]
    change e (p x) = e z ↔ p x = z
    exact e.apply_eq_iff_eq
  have hrawCompatible : ForestCompatible p T raw :=
    ForestCompatible.unrelabel p T e forest hforest.2.2
  have hpull : ∀ b i, ∃ A : Finset (FrontierVertex record.before.block record.before.tree b),
      (record.split b).shore i = pull (frontierMap record.before.block record.before.tree b) A := by
    intro b i
    exact checkedFrontierSplit_shore_pull record.before.block record.before.onto record.before.tree b _ i
  have hs : ∀ b, ∃ out, assembleFrontierBlock record forest b = some out ∧
      IsSteinerCutTree G out.value ∧ (∀ x, Represents out x ↔ record.before.block x = b) ∧
      ∀ u, u ≠ record.before.tree.root → ∀ x y,
        ¬(b ∈ record.before.tree.D u ↔ record.before.block x ∈ record.before.tree.D u) →
        ¬(b ∈ record.before.tree.D u ↔ record.before.block y ∈ record.before.tree.D u) →
          out.value.attach x = out.value.attach y := by
    intro b
    exact roundForestAssemble_success G record.before.block record.before.onto record.before.tree
      record.split record.split_valid hpull (record.split_minCuts G hbefore hgood)
      raw hrawCorrect hrawCover hrawCompatible b
  obtain ⟨out, hout, hentries⟩ := collectBlockTrees_exists (assembleFrontierBlock record forest)
    (fun b => by obtain ⟨tree, htree, _⟩ := hs b; exact ⟨tree, htree⟩)
  have hproperties (b : Fin record.before.size) :
      IsSteinerCutTree G (out b).value ∧ (∀ x, Represents (out b) x ↔ record.before.block x = b) ∧
      ∀ u, u ≠ record.before.tree.root → ∀ x y,
        ¬(b ∈ record.before.tree.D u ↔ record.before.block x ∈ record.before.tree.D u) →
        ¬(b ∈ record.before.tree.D u ↔ record.before.block y ∈ record.before.tree.D u) →
          (out b).value.attach x = (out b).value.attach y := by
    obtain ⟨tree, htree, hproperties⟩ := hs b
    have he : tree = out b := Option.some.inj (htree.symm.trans (hentries b))
    exact he ▸ hproperties
  exact ⟨out, hout, fun b => (hproperties b).1,
    fun b => (hproperties b).2.1, fun b => (hproperties b).2.2⟩

theorem restoreFrontierRecords_success (G : WeightedGraph V) {levels : ℕ}
    (records : List (FrontierRoundRecord V levels)) :
    ∀ start final (forest : FrontierForest final),
      FrontierTrace.Follows start records final → start.Witnessed G →
      (∀ record ∈ records, record.Good G) → FrontierForestSound G final forest →
      ∃ out : FrontierForest start,
        restoreFrontierRecords records ⟨final, forest⟩ = some ⟨start, out⟩ ∧
          FrontierForestSound G start out := by
  induction records with
  | nil =>
      intro start final forest hfollows _ _ hforest
      change final = start at hfollows
      subst final
      exact ⟨forest, rfl, hforest⟩
  | cons record rest ih =>
      intro start final forest hfollows hstart hgood hforest
      obtain ⟨hbefore, hrest⟩ := hfollows
      subst start
      have hrecord := hgood record (by simp)
      obtain ⟨middle, hmiddle, hmiddleSound⟩ := ih record.after final forest hrest
        (record.after_witnessed G hstart hrecord)
        (fun next hnext => hgood next (List.mem_cons_of_mem _ hnext)) hforest
      obtain ⟨out, hout, houtSound⟩ := assembleFrontierRound_success G record hstart hrecord middle hmiddleSound
      have hrestore : restoreFrontierRecord record ⟨record.after, middle⟩ = some ⟨record.before, out⟩ := by
        simp [restoreFrontierRecord, hout]
      refine ⟨out, ?_, houtSound⟩
      rw [restoreFrontierRecords, hmiddle, Option.bind_some, hrestore]

theorem assembleFrontierTrace_success (G : WeightedGraph V) (r : V) {levels : ℕ}
    (trace : FrontierTrace V levels)
    (hfollows : FrontierTrace.Follows (initialFrontierState r) trace.records trace.endState)
    (hgood : trace.Good G) (hdiscrete : trace.endState.Discrete) :
    ∃ tree, assembleFrontierTrace trace = some tree ∧ IsGomoryHuTree G tree := by
  obtain ⟨forest, hforest, hsound⟩ := restoreFrontierRecords_success G trace.records
    (initialFrontierState r) trace.endState (leafFrontierForest trace.endState) hfollows
    (initialFrontierState_witnessed G r) hgood (leafFrontierForest_sound G trace.endState hdiscrete)
  let packed := forest (initialFrontierState r).tree.root
  have hcover : Function.Surjective packed.value.terminal := by
    intro x
    exact (hsound.2.1 (initialFrontierState r).tree.root x).mpr (by change (0 : Fin 1) = 0; rfl)
  refine ⟨completeSteinerTree packed.value hcover, ?_, completeSteinerTree_correct G packed.value hcover
    (hsound.1 (initialFrontierState r).tree.root)⟩
  simp only [assembleFrontierTrace, ite_eq_left hdiscrete, hforest, Option.bind_some]
  change (if h : Function.Surjective packed.value.terminal then
    some (completeSteinerTree packed.value h) else none) = _
  rw [dif_pos hcover]

end
end CutQueryComplexity.GHReduction
