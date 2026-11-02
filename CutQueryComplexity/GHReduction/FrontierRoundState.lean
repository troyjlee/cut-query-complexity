import CutQueryComplexity.GHReduction.FrontierPivotRound
import CutQueryComplexity.GHReduction.RoundRefinement
import CutQueryComplexity.GHReduction.SteinerEndpoint
import Mathlib.Data.Fintype.EquivFin

/-! # Public states and total updates for executed frontier rounds

The state stores a finite partition and its actual tree, with a proved
surjectivity fact about public data. It contains no hidden cut-correctness or
complexity assertion. Returned auxiliary shores are lifted through the actual
frontier map, and finite public guards ensure every next label has a vertex.
Malformed data produce an empty split, keeping the same block.

The update supplies the next actual contraction maps for the next query round.
Preservation of minimum-cut witnesses and final tree assembly remain separate.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

structure PublicBlockSplit (V : Type) where
  source : V
  children : Finset V
  shore : V → Finset V
  value : V → ℝ

/-- Every field is a decidable finite property of the public output, with no
reference to the hidden graph or to a minimum-cut value. -/
structure ValidBlockSplit (U : Finset V) (S : PublicBlockSplit V) : Prop where
  source_mem : S.source ∈ U
  indices : S.children ⊆ U.erase S.source
  contains : ∀ v ∈ S.children, v ∈ S.shore v
  excludes : ∀ v ∈ S.children, S.source ∉ S.shore v
  small : ∀ v ∈ S.children, 2 * (S.shore v ∩ U).card ≤ U.card
  disjoint : (S.children : Set V).PairwiseDisjoint S.shore

def emptyBlockSplit (r : V) : PublicBlockSplit V := ⟨r, ∅, fun _ => ∅, fun _ => 0⟩

theorem emptyBlockSplit_valid (U : Finset V) (r : U) : ValidBlockSplit U (emptyBlockSplit r.val) := by
  refine ⟨r.property, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [emptyBlockSplit, Set.PairwiseDisjoint, Set.Pairwise]

def normalizeBlockSplit (U : Finset V) (r : U) (S : PublicBlockSplit V) : PublicBlockSplit V :=
  if ValidBlockSplit U S then S else emptyBlockSplit r.val

theorem normalizeBlockSplit_valid (U : Finset V) (r : U) (S : PublicBlockSplit V) :
    ValidBlockSplit U (normalizeBlockSplit U r S) := by
  by_cases h : ValidBlockSplit U S
  · simpa only [normalizeBlockSplit, h, ite_true] using h
  · simpa only [normalizeBlockSplit, h, ite_false] using emptyBlockSplit_valid U r

theorem normalizeBlockSplit_of_valid (U : Finset V) (r : U) (S : PublicBlockSplit V)
    (h : ValidBlockSplit U S) : normalizeBlockSplit U r S = S := by
  simp only [normalizeBlockSplit, h, ite_true]

def blockRepresentative (p : V → B) (hp : Function.Surjective p) (b : B) : V :=
  Classical.choose (hp b)

@[simp] theorem blockRepresentative_mem (p : V → B) (hp : Function.Surjective p) (b : B) :
    p (blockRepresentative p hp b) = b := Classical.choose_spec (hp b)

/-- Lift the actual auxiliary output using its public contraction map.
The fallback representative matters only if the reported pivot is a proxy. -/
def liftFrontierSplit (p : V → B) (T : RootedTree B) (b : B) (r : V) {levels : ℕ}
    (out : Option (SourcePivotOutput (FrontierVertex p T b) levels)) : PublicBlockSplit V :=
  match out with
  | none => emptyBlockSplit r
  | some result => {
      source := match result.pivot with | Sum.inl u => u.val | Sum.inr _ => r
      children := (fiber p b).filter (fun v => frontierMap p T b v ∈ result.step.batch.accepted)
      shore := fun v => pull (frontierMap p T b) (result.step.batch.shore (frontierMap p T b v))
      value := fun v => result.step.batch.value (frontierMap p T b v) }

def checkedFrontierSplit (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (b : B)
    {levels : ℕ} (out : Option (SourcePivotOutput (FrontierVertex p T b) levels)) : PublicBlockSplit V :=
  normalizeBlockSplit (fiber p b)
    ⟨blockRepresentative p hp b, (mem_fiber _ _ _).mpr (blockRepresentative_mem p hp b)⟩
    (liftFrontierSplit p T b (blockRepresentative p hp b) out)

theorem checkedFrontierSplit_valid (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (b : B) {levels : ℕ} (out : Option (SourcePivotOutput (FrontierVertex p T b) levels)) :
    ValidBlockSplit (fiber p b) (checkedFrontierSplit p hp T b out) :=
  normalizeBlockSplit_valid _ _ _

/-- Public representation data and its mechanically proved nonempty-fiber
property. There is no semantic graph or desired algorithm theorem here. -/
structure PublicFrontierState (V : Type) where
  size : ℕ
  block : V → Fin size
  tree : RootedTree (Fin size)
  onto : Function.Surjective block

def packFrontierState (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) :
    PublicFrontierState V where
  size := Fintype.card B
  block := Fintype.equivFin B ∘ p
  tree := relabelRootedTree T (Fintype.equivFin B)
  onto := (Fintype.equivFin B).surjective.comp hp

def initialFrontierState (r : V) : PublicFrontierState V where
  size := 1
  block := fun _ => 0
  tree := {
    root := 0
    parent := fun _ => 0
    depth := fun _ => 0
    parent_root := rfl
    depth_root := rfl
    depth_parent := by intro v hv; exact (hv (Subsingleton.elim _ _)).elim }
  onto := fun b => ⟨r, Subsingleton.elim _ _⟩

theorem PublicFrontierState.size_le (S : PublicFrontierState V) : S.size ≤ Fintype.card V := by
  simpa using Fintype.card_le_of_surjective S.block S.onto

theorem PublicFrontierState.frontier_sizes (S : PublicFrontierState V) :
    (∑ b, Fintype.card (FrontierVertex S.block S.tree b)) =
      Fintype.card V + 2 * (S.size - 1) ∧
    (∑ b, Fintype.card (FrontierVertex S.block S.tree b)) ≤ 3 * Fintype.card V ∧
    ∀ b, Fintype.card (FrontierVertex S.block S.tree b) ≤ Fintype.card V := by
  refine ⟨?_, frontier_vertex_sum_le S.block S.onto S.tree,
    fun b => frontierVertex_card_le S.block S.onto S.tree b⟩
  simpa using frontier_vertex_sum S.block S.tree

/-- Refine all old blocks simultaneously, then merely relabel the finite
result. This operation uses returned shores and public representatives only. -/
def advanceFrontierState (state : PublicFrontierState V) (splits : Fin state.size → PublicBlockSplit V)
    (hvalid : ∀ b, ValidBlockSplit (fiber state.block b) (splits b)) : PublicFrontierState V := by
  let I := fun b => (splits b).children
  let shores := fun b => (splits b).shore
  let attachment := fun b c => refinementCell (I b) (shores b)
    (blockRepresentative state.block state.onto c)
  have hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (shores b i) (shores b j) := by
    intro b i hi j hj hij
    exact (hvalid b).disjoint hi hj hij
  have hmap : Function.Surjective (roundBlockMap state.block I shores) := by
    apply roundBlockMap_surjective state.block I shores hdisj (fun b => (splits b).source)
    · intro b
      exact (mem_fiber _ _ _).mp (hvalid b).source_mem
    · intro b i hi
      exact (hvalid b).excludes i hi
    · intro b i
      exact ⟨i.val, (mem_fiber _ _ _).mp (Finset.mem_erase.mp ((hvalid b).indices i.property)).2,
        (hvalid b).contains i.val i.property⟩
  exact packFrontierState (roundBlockMap state.block I shores) hmap
    (roundBlockTree state.tree I attachment)

structure FrontierRoundRecord (V : Type) [Fintype V] [DecidableEq V] (levels : ℕ) where
  before : PublicFrontierState V
  result : Option ((b : Fin before.size) → Option
    (SourcePivotOutput (FrontierVertex before.block before.tree b) levels))

def FrontierRoundRecord.split {levels : ℕ} (record : FrontierRoundRecord V levels)
    (b : Fin record.before.size) : PublicBlockSplit V :=
  checkedFrontierSplit record.before.block record.before.onto record.before.tree b
    (record.result.elim none (fun table => table b))

theorem FrontierRoundRecord.split_valid {levels : ℕ} (record : FrontierRoundRecord V levels)
    (b : Fin record.before.size) :
    ValidBlockSplit (fiber record.before.block b) (record.split b) :=
  checkedFrontierSplit_valid _ _ _ _ _

def FrontierRoundRecord.after {levels : ℕ} (record : FrontierRoundRecord V levels) : PublicFrontierState V :=
  advanceFrontierState record.before record.split record.split_valid

/-- This holds even on malformed outputs: the finite public guards supplied
the actual proof that the next round's partition has no empty labels. -/
theorem FrontierRoundRecord.after_frontier_sizes {levels : ℕ} (record : FrontierRoundRecord V levels) :
    (∑ b, Fintype.card (FrontierVertex record.after.block record.after.tree b)) ≤ 3 * Fintype.card V ∧
    ∀ b, Fintype.card (FrontierVertex record.after.block record.after.tree b) ≤ Fintype.card V :=
  ⟨record.after.frontier_sizes.2.1, record.after.frontier_sizes.2.2⟩

end
end CutQueryComplexity.GHReduction
