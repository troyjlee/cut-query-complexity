import CutQueryComplexity.GHReduction.FrontierRoundGeometry
import CutQueryComplexity.GHReduction.FrontierSplitCorrectness
import CutQueryComplexity.GHReduction.FrontierExecution

/-! # Cut-witness induction along the actual adaptive execution

The initial one-block state has no edge obligation. On a successful round,
the existing edge witnesses protect every auxiliary proxy fiber. Returned
minimum shores therefore lift to the original graph. The concrete public
update preserves the old witnesses and adds these lifted witnesses, including
after its finite relabeling. Induction follows the actual execution records.

This proposition is proved about states; it is not a field supplied to the
query algorithm and is not a replacement for the final GH assembly theorem.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def PublicFrontierState.Witnessed (G : WeightedGraph V) (state : PublicFrontierState V) : Prop :=
  ∀ e, e ≠ state.tree.root → ∃ s t, IsSTMinCut G s t (pull state.block (state.tree.D e))

theorem initialFrontierState_witnessed (G : WeightedGraph V) (r : V) :
    (initialFrontierState r).Witnessed G := by
  unfold PublicFrontierState.Witnessed initialFrontierState
  intro e he
  exact (he (Subsingleton.elim _ _)).elim

theorem frontierBranch_minCut_witness (G : WeightedGraph V) (p : V → B) (T : RootedTree B)
    (hold : ∀ e, e ≠ T.root → ∃ s t, IsSTMinCut G s t (pull p (T.D e)))
    (b : B) (e : frontierProxies T b) :
    ∃ s t, IsSTMinCut G s t (pull p (frontierBranch T b e)) := by
  have he : e.val ≠ T.root := ((mem_frontierProxies T b e.val).mp e.property).1
  obtain ⟨s, t, hcut⟩ := hold e.val he
  by_cases heb : e.val = b
  · refine ⟨t, s, ?_⟩
    simpa only [frontierBranch, heb, ite_true, pull_compl] using stMinCut_compl G hcut
  · exact ⟨s, t, by simpa only [frontierBranch, heb, ite_false] using hcut⟩

theorem packFrontierState_witnessed (G : WeightedGraph V)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (hT : ∀ e, e ≠ T.root → ∃ s t, IsSTMinCut G s t (pull p (T.D e))) :
    (packFrontierState p hp T).Witnessed G := by
  let e := Fintype.equivFin B
  intro v hv
  have hv0 : e.symm v ≠ T.root := by
    intro he
    apply hv
    change v ≠ e T.root at hv
    exact (e.apply_symm_apply v).symm.trans (congrArg e he)
  have hshore : pull (e ∘ p) ((relabelRootedTree T e).D v) = pull p (T.D (e.symm v)) := by
    conv_lhs => rw [← e.apply_symm_apply v, relabelRootedTree_subtree]
    ext x
    simp only [mem_pull, Function.comp_apply, Equiv.symm_apply_apply]
  change ∃ s t, IsSTMinCut G s t (pull (e ∘ p) ((relabelRootedTree T e).D v))
  rw [hshore]
  exact hT (e.symm v) hv0

theorem checkedFrontierSplit_none_children (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) (levels : ℕ) :
    (checkedFrontierSplit p hp T b (levels := levels) none).children = ∅ := by
  unfold checkedFrontierSplit normalizeBlockSplit
  split <;> rfl

theorem checkedFrontierSplit_good_minCuts (G : WeightedGraph V) (p : V → B)
    (hp : Function.Surjective p) (T : RootedTree B)
    (hold : ∀ e, e ≠ T.root → ∃ s t, IsSTMinCut G s t (pull p (T.D e)))
    (b : B) {levels : ℕ} (out : Option (SourcePivotOutput (FrontierVertex p T b) levels))
    (hgood : FrontierPivotGood G p T b out) :
    ∀ v ∈ (checkedFrontierSplit p hp T b out).children,
      IsSTMinCut G v (checkedFrontierSplit p hp T b out).source
        ((checkedFrontierSplit p hp T b out).shore v) ∧
      (checkedFrontierSplit p hp T b out).value v = G.cut ((checkedFrontierSplit p hp T b out).shore v) := by
  by_cases hactive : 2 ≤ (fiber p b).card
  · simp only [FrontierPivotGood, hactive, ite_true] at hgood
    cases out with
    | none => exact hgood.elim
    | some out =>
        have hbranch : ∀ e : frontierProxies T b,
            ∃ s t, IsSTMinCut G s t (pull p (frontierBranch T b e)) :=
          frontierBranch_minCut_witness G p T hold b
        choose r c hcut using hbranch
        exact checkedFrontierSplit_minCuts G p hp T b r c hcut out hgood
  · have hout : out = none := by simpa only [FrontierPivotGood, hactive, ite_false] using hgood
    subst out
    rw [checkedFrontierSplit_none_children]
    intro v hv
    simp at hv

theorem advanceFrontierState_witnessed (G : WeightedGraph V) (state : PublicFrontierState V)
    (splits : Fin state.size → PublicBlockSplit V)
    (hvalid : ∀ b, ValidBlockSplit (fiber state.block b) (splits b))
    (hstate : state.Witnessed G)
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex state.block state.tree b),
      (splits b).shore i = pull (frontierMap state.block state.tree b) A)
    (hnew : ∀ b i, i ∈ (splits b).children → ∃ s t, IsSTMinCut G s t ((splits b).shore i)) :
    (advanceFrontierState state splits hvalid).Witnessed G := by
  apply packFrontierState_witnessed
  · apply roundBlockMap_surjective state.block
      (fun b => (splits b).children) (fun b => (splits b).shore)
      (fun b i hi j hj hij => (hvalid b).disjoint hi hj hij) (fun b => (splits b).source)
    · intro b
      exact (mem_fiber _ _ _).mp (hvalid b).source_mem
    · intro b i hi
      exact (hvalid b).excludes i hi
    · intro b i
      exact ⟨i.val, (mem_fiber _ _ _).mp (Finset.mem_erase.mp ((hvalid b).indices i.property)).2,
        (hvalid b).contains i.val i.property⟩
  · intro v hv
    exact roundBlockTree_minCut_witness G state.block state.onto state.tree
      (fun b => (splits b).children) (fun b => (splits b).shore)
      (fun b i hi j hj hij => (hvalid b).disjoint hi hj hij) hpull hstate hnew hv

theorem FrontierRoundRecord.split_minCuts (G : WeightedGraph V) {levels : ℕ}
    (record : FrontierRoundRecord V levels) (hbefore : record.before.Witnessed G)
    (hgood : record.Good G) (b : Fin record.before.size) :
    ∀ v ∈ (record.split b).children,
      IsSTMinCut G v (record.split b).source ((record.split b).shore v) ∧
      (record.split b).value v = G.cut ((record.split b).shore v) := by
  cases hresult : record.result with
  | none => simp only [FrontierRoundRecord.Good, hresult, Option.elim_none] at hgood
  | some table =>
      have hg : FrontierPivotGood G record.before.block record.before.tree b (table b) := by
        exact (show ∀ c, FrontierPivotGood G record.before.block record.before.tree c (table c) from
          by simpa only [FrontierRoundRecord.Good, hresult, Option.elim_some] using hgood) b
      simpa only [FrontierRoundRecord.split, hresult, Option.elim_some] using
        checkedFrontierSplit_good_minCuts G record.before.block record.before.onto
          record.before.tree hbefore b (table b) hg

theorem FrontierRoundRecord.after_witnessed (G : WeightedGraph V) {levels : ℕ}
    (record : FrontierRoundRecord V levels) (hbefore : record.before.Witnessed G)
    (hgood : record.Good G) : record.after.Witnessed G := by
  apply advanceFrontierState_witnessed G record.before record.split record.split_valid hbefore
  · intro b i
    exact checkedFrontierSplit_shore_pull record.before.block record.before.onto
      record.before.tree b _ i
  · intro b i hi
    exact ⟨i, (record.split b).source, (record.split_minCuts G hbefore hgood b i hi).1⟩

theorem frontierTrace_witnessed (G : WeightedGraph V) {levels : ℕ}
    (records : List (FrontierRoundRecord V levels)) :
    ∀ start final, FrontierTrace.Follows start records final → start.Witnessed G →
      (∀ record ∈ records, record.Good G) → final.Witnessed G := by
  induction records with
  | nil =>
      intro start final hfollows hstart _
      change final = start at hfollows
      subst final
      exact hstart
  | cons record rest ih =>
      intro start final hfollows hstart hgood
      obtain ⟨hbefore, hrest⟩ := hfollows
      have hrecord : record.before.Witnessed G := hbefore.symm ▸ hstart
      apply ih record.after final hrest (record.after_witnessed G hrecord (hgood record (by simp)))
      intro next hnext
      exact hgood next (List.mem_cons_of_mem _ hnext)

end
end CutQueryComplexity.GHReduction
