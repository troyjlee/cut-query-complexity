import CutQueryComplexity.GHReduction.TrackedPivotProgress
import CutQueryComplexity.GHReduction.FrontierWitnessInduction

/-! # A tracked original vertex follows its actual auxiliary child

The selected cells on original vertices and on their auxiliary terminal labels
have the same membership tests. This identifies the actual refined fiber,
including finite relabeling, with the sampled auxiliary child. Its cardinality
is therefore the one used by the tracked-pivot progress theorem.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph OuterPivot

variable {V B ι : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq ι]

theorem refinementCell_eq_iff_memberships (I : Finset ι) (S : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) (v w : V) :
    refinementCell I S v = refinementCell I S w ↔ ∀ i ∈ I, v ∈ S i ↔ w ∈ S i := by
  constructor
  · intro he i hi
    rw [← refinementCell_eq_some I S hdisj v ⟨i, hi⟩,
      ← refinementCell_eq_some I S hdisj w ⟨i, hi⟩, he]
  · exact refinementCell_congr_membership I S hdisj v w

theorem roundBlockMap_fiber_at (p : V → B) (I : B → Finset ι) (S : B → ι → Finset V)
    (v x : V) : x ∈ fiber (roundBlockMap p I S) (roundBlockMap p I S v) ↔
      p x = p v ∧ refinementCell (I (p v)) (S (p v)) x =
        refinementCell (I (p v)) (S (p v)) v := by
  rw [mem_fiber]
  constructor
  · intro he
    have hx : p x = p v := congrArg (roundBlockParent I) he
    rw [roundBlockMap_of_fiber p I S x (p v) hx] at he
    change (⟨p v, refinementCell (I (p v)) (S (p v)) x⟩ : RoundBlock I) =
      ⟨p v, refinementCell (I (p v)) (S (p v)) v⟩ at he
    exact ⟨hx, eq_of_heq (Sigma.mk.inj_iff.mp he).2⟩
  · rintro ⟨hx, hc⟩
    rw [roundBlockMap_of_fiber p I S x (p v) hx]
    exact congrArg (fun c => (⟨p v, c⟩ : RoundBlock I)) hc

theorem packFrontierState_fiber_at (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (v : V) :
    fiber (packFrontierState p hp T).block ((packFrontierState p hp T).block v) = fiber p (p v) := by
  unfold packFrontierState
  ext x
  simp only [mem_fiber, Function.comp_apply, Equiv.apply_eq_iff_eq]

theorem advanceFrontierState_fiber_at (state : PublicFrontierState V)
    (splits : Fin state.size → PublicBlockSplit V)
    (hvalid : ∀ b, ValidBlockSplit (fiber state.block b) (splits b)) (v : V) :
    fiber (advanceFrontierState state splits hvalid).block
      ((advanceFrontierState state splits hvalid).block v) =
    fiber (roundBlockMap state.block (fun b => (splits b).children) (fun b => (splits b).shore))
      (roundBlockMap state.block (fun b => (splits b).children) (fun b => (splits b).shore) v) := by
  unfold advanceFrontierState packFrontierState
  ext x
  simp only [mem_fiber, Function.comp_apply, Equiv.apply_eq_iff_eq]

theorem advanceFrontierState_fiber_subset (state : PublicFrontierState V)
    (splits : Fin state.size → PublicBlockSplit V)
    (hvalid : ∀ b, ValidBlockSplit (fiber state.block b) (splits b)) (v : V) :
    fiber (advanceFrontierState state splits hvalid).block
      ((advanceFrontierState state splits hvalid).block v) ⊆ fiber state.block (state.block v) := by
  rw [advanceFrontierState_fiber_at]
  exact roundBlockMap_fiber_subset _ _ _ _

theorem checkedFrontierSplit_cell_iff (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) {levels : ℕ}
    (out : SourcePivotOutput (FrontierVertex p T b) levels)
    (hpivot : out.pivot ∈ frontierTerminals p T b)
    (hform : WellFormed (frontierTerminals p T b) out.pivot out.values out.step.batch)
    (v x : V) (hv : v ∈ fiber p b) (hx : x ∈ fiber p b) :
    refinementCell (checkedFrontierSplit p hp T b (some out)).children
      (checkedFrontierSplit p hp T b (some out)).shore x =
      refinementCell (checkedFrontierSplit p hp T b (some out)).children
        (checkedFrontierSplit p hp T b (some out)).shore v ↔
    refinementCell out.step.batch.accepted out.step.batch.shore (frontierMap p T b x) =
      refinementCell out.step.batch.accepted out.step.batch.shore (frontierMap p T b v) := by
  let split := checkedFrontierSplit p hp T b (some out)
  have hvalid := checkedFrontierSplit_valid p hp T b (some out)
  have hdisj : ∀ i ∈ split.children, ∀ j ∈ split.children,
      i ≠ j → Disjoint (split.shore i) (split.shore j) :=
    fun i hi j hj hij => hvalid.disjoint hi hj hij
  have hauxdisj : ∀ i ∈ out.step.batch.accepted, ∀ j ∈ out.step.batch.accepted,
      i ≠ j → Disjoint (out.step.batch.shore i) (out.step.batch.shore j) :=
    fun i hi j hj hij => hform.disjoint hi hj hij
  change refinementCell split.children split.shore x = refinementCell split.children split.shore v ↔ _
  rw [refinementCell_eq_iff_memberships _ _ hdisj,
    refinementCell_eq_iff_memberships _ _ hauxdisj]
  have hsplit : split = liftFrontierSplit p T b (blockRepresentative p hp b) (some out) :=
    checkedFrontierSplit_of_wellFormed p hp T b out hpivot hform
  constructor
  · intro h i hi
    have hiU := (Finset.mem_erase.mp (hform.indices hi)).2
    obtain ⟨u, hu⟩ := (mem_frontierTerminals p T b i).mp hiU
    have hmap : frontierMap p T b u.val = i :=
      ((frontierMap_eq_inl p T b u.val u).mpr rfl).trans hu
    have huacc : u.val ∈ split.children := by
      rw [hsplit]
      exact Finset.mem_filter.mpr ⟨u.property, hmap.symm ▸ hi⟩
    have hm := h u.val huacc
    simpa only [hsplit, liftFrontierSplit, mem_pull, hmap] using hm
  · intro h i hi
    have hiacc : frontierMap p T b i ∈ out.step.batch.accepted := by
      rw [hsplit] at hi
      exact (Finset.mem_filter.mp hi).2
    simpa only [hsplit, liftFrontierSplit, mem_pull] using h _ hiacc

theorem roundBlockMap_tracked_fiber (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (splits : B → PublicBlockSplit V) (b : B) {levels : ℕ}
    (out : SourcePivotOutput (FrontierVertex p T b) levels)
    (hpivot : out.pivot ∈ frontierTerminals p T b)
    (hform : WellFormed (frontierTerminals p T b) out.pivot out.values out.step.batch)
    (hsplit : splits b = checkedFrontierSplit p hp T b (some out)) (v : V) (hv : p v = b) :
    fiber (roundBlockMap p (fun c => (splits c).children) (fun c => (splits c).shore))
      (roundBlockMap p (fun c => (splits c).children) (fun c => (splits c).shore) v) =
      pull (frontierMap p T b)
        (trackedPivotChild (frontierTerminals p T b) out.step (frontierMap p T b v)) ∩ fiber p b := by
  ext x
  rw [roundBlockMap_fiber_at, hv, Finset.mem_inter, mem_pull, mem_fiber,
    mem_trackedPivotChild _ _ _ out.step hform]
  by_cases hx : p x = b
  · have hxU := frontierMap_mem_terminals p T b ((mem_fiber _ _ _).mpr hx)
    have hvU : v ∈ fiber p b := (mem_fiber _ _ _).mpr hv
    simp only [hx, true_and, and_true, hxU]
    rw [hsplit]
    exact checkedFrontierSplit_cell_iff p hp T b out hpivot hform v x hvU
      ((mem_fiber _ _ _).mpr hx)
  · simp only [hx, false_and, and_false]

theorem advanceFrontierState_tracked_card (state : PublicFrontierState V)
    (splits : Fin state.size → PublicBlockSplit V)
    (hvalid : ∀ b, ValidBlockSplit (fiber state.block b) (splits b))
    (b : Fin state.size) {levels : ℕ}
    (out : SourcePivotOutput (FrontierVertex state.block state.tree b) levels)
    (hpivot : out.pivot ∈ frontierTerminals state.block state.tree b)
    (hform : WellFormed (frontierTerminals state.block state.tree b) out.pivot out.values out.step.batch)
    (hsplit : splits b = checkedFrontierSplit state.block state.onto state.tree b (some out))
    (v : V) (hv : state.block v = b) :
    (fiber (advanceFrontierState state splits hvalid).block
      ((advanceFrontierState state splits hvalid).block v)).card =
      (trackedPivotChild (frontierTerminals state.block state.tree b) out.step
        (frontierMap state.block state.tree b v)).card := by
  rw [advanceFrontierState_fiber_at,
    roundBlockMap_tracked_fiber state.block state.onto state.tree splits b out hpivot hform hsplit v hv,
    frontier_terminal_trace_card, Finset.inter_eq_left.mpr (trackedPivotChild_subset _ _ _)]

end
end CutQueryComplexity.GHReduction
