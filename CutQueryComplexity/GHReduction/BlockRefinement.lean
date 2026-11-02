import CutQueryComplexity.Graph.Operations
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! # Public refinement of one partial-tree block

Accepted pairwise-disjoint shores split one block into child blocks and a
residual block. Other blocks keep their original vertices. The new label type
and its map are functions of public data; neither takes the hidden graph.

The surjectivity theorem uses an actual surviving pivot and an actual vertex
in every accepted child. Consequently the block count bounds the number of
nonempty fibers of this very map. Updating the tree topology, preserving cut
witnesses, and connecting a recursive execution to its frontier remain
separate obligations.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B ι : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq ι]

/-- Old blocks other than `b`, together with a residual block and one label
for each accepted child. -/
abbrev RefinedBlock (b : B) (I : Finset ι) :=
  (Finset.univ.erase b : Finset B) ⊕ Option I

instance refinedBlockFintype (b : B) (I : Finset ι) : Fintype (RefinedBlock b I) :=
  inferInstanceAs (Fintype (_ ⊕ _))

instance refinedBlockDecidableEq (b : B) (I : Finset ι) : DecidableEq (RefinedBlock b I) :=
  inferInstanceAs (DecidableEq (_ ⊕ _))

/-- A public choice of an accepted shore containing the vertex, if one exists.
Disjointness is a correctness condition, not an input used by the map. -/
def refinementCell (I : Finset ι) (S : ι → Finset V) (v : V) : Option I :=
  if h : ∃ i : I, v ∈ S i.val then some (Classical.choose h) else none

theorem refinementCell_eq_none (I : Finset ι) (S : ι → Finset V) (v : V) :
    refinementCell I S v = none ↔ ∀ i ∈ I, v ∉ S i := by
  constructor
  · intro hnone i hi hvi
    have hex : ∃ j : I, v ∈ S j.val := ⟨⟨i, hi⟩, hvi⟩
    simp [refinementCell, hex] at hnone
  · intro hn
    have hnot : ¬ ∃ i : I, v ∈ S i.val := by
      rintro ⟨i, hi⟩
      exact hn i.val i.property hi
    simp [refinementCell, hnot]

theorem refinementCell_eq_some (I : Finset ι) (S : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (v : V) (i : I) : refinementCell I S v = some i ↔ v ∈ S i.val := by
  constructor
  · intro he
    have hex : ∃ j : I, v ∈ S j.val := by
      by_contra hnot
      simp [refinementCell, hnot] at he
    have hchoose : Classical.choose hex = i := by
      simpa [refinementCell, hex] using he
    simpa only [hchoose] using Classical.choose_spec hex
  · intro hi
    have hex : ∃ j : I, v ∈ S j.val := ⟨i, hi⟩
    have hchoose : Classical.choose hex = i := by
      apply Subtype.ext
      by_contra hne
      exact Finset.disjoint_left.mp
        (hdisj _ (Classical.choose hex).property _ i.property hne)
        (Classical.choose_spec hex) hi
    simp [refinementCell, hex, hchoose]

/-- The block map after a public split. Vertices outside the selected block
ignore the accepted shores and stay in their old blocks. -/
def refinedBlockMap (p : V → B) (b : B) (I : Finset ι) (S : ι → Finset V)
    (v : V) : RefinedBlock b I :=
  if hv : p v = b then Sum.inr (refinementCell I S v)
  else Sum.inl ⟨p v, Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩⟩

theorem refinedBlockMap_eq_old (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V) (v : V) (c : (Finset.univ.erase b : Finset B)) :
    refinedBlockMap p b I S v = Sum.inl c ↔ p v = c.val := by
  have hc : c.val ≠ b := (Finset.mem_erase.mp c.property).1
  by_cases hv : p v = b
  · simp [refinedBlockMap, hv, Ne.symm hc]
  · rw [refinedBlockMap, dite_eq_right hv]
    constructor
    · intro h
      exact congrArg Subtype.val (Sum.inl.inj h)
    · intro h
      exact congrArg (fun z : (Finset.univ.erase b : Finset B) =>
        (Sum.inl z : RefinedBlock b I)) (Subtype.ext h)

theorem refinedBlockMap_eq_residual (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V) (v : V) :
    refinedBlockMap p b I S v = Sum.inr none ↔
      p v = b ∧ ∀ i ∈ I, v ∉ S i := by
  by_cases hv : p v = b
  · rw [refinedBlockMap, dite_eq_left hv]
    constructor
    · intro h
      exact ⟨hv, (refinementCell_eq_none I S v).mp (Sum.inr.inj h)⟩
    · rintro ⟨_, hn⟩
      exact congrArg (fun z : Option I => (Sum.inr z : RefinedBlock b I))
        ((refinementCell_eq_none I S v).mpr hn)
  · simp [refinedBlockMap, hv]

theorem refinedBlockMap_eq_child (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (v : V) (i : I) :
    refinedBlockMap p b I S v = Sum.inr (some i) ↔ p v = b ∧ v ∈ S i.val := by
  by_cases hv : p v = b
  · rw [refinedBlockMap, dite_eq_left hv]
    constructor
    · intro h
      exact ⟨hv, (refinementCell_eq_some I S hdisj v i).mp (Sum.inr.inj h)⟩
    · rintro ⟨_, hi⟩
      exact congrArg (fun z : Option I => (Sum.inr z : RefinedBlock b I))
        ((refinementCell_eq_some I S hdisj v i).mpr hi)
  · simp [refinedBlockMap, hv]

theorem refinedBlockMap_old_fiber (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V) (c : (Finset.univ.erase b : Finset B)) :
    fiber (refinedBlockMap p b I S) (Sum.inl c) = fiber p c.val := by
  ext v
  simp only [fiber, pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  exact refinedBlockMap_eq_old p b I S v c

theorem refinedBlockMap_residual_fiber (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V) :
    fiber (refinedBlockMap p b I S) (Sum.inr none) = fiber p b \ I.biUnion S := by
  ext v
  simp only [fiber, pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.mem_sdiff,
    Finset.mem_biUnion, not_exists, not_and]
  exact refinedBlockMap_eq_residual p b I S v

theorem refinedBlockMap_child_fiber (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) (i : I) :
    fiber (refinedBlockMap p b I S) (Sum.inr (some i)) = fiber p b ∩ S i.val := by
  ext v
  simp only [fiber, pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.mem_inter]
  exact refinedBlockMap_eq_child p b I S hdisj v i

/-- Forget the split, recovering the original block labels. -/
def refinedBlockParent (b : B) (I : Finset ι) : RefinedBlock b I → B
  | Sum.inl c => c.val
  | Sum.inr _ => b

theorem refinedBlockParent_map (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V) (v : V) :
    refinedBlockParent b I (refinedBlockMap p b I S v) = p v := by
  by_cases hv : p v = b <;> simp [refinedBlockMap, refinedBlockParent, hv]

/-- Refinement never merges vertices from different old blocks. -/
theorem refinedBlockMap_fiber_subset (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V) (c : RefinedBlock b I) :
    fiber (refinedBlockMap p b I S) c ⊆ fiber p (refinedBlockParent b I c) := by
  intro v hv
  have he := (mem_fiber (refinedBlockMap p b I S) c v).mp hv
  apply (mem_fiber p (refinedBlockParent b I c) v).mpr
  calc
    p v = refinedBlockParent b I (refinedBlockMap p b I S v) :=
      (refinedBlockParent_map p b I S v).symm
    _ = refinedBlockParent b I c := congrArg (refinedBlockParent b I) he

/-- Taking all new labels over one old block recovers exactly that old fiber. -/
theorem refinedBlockMap_pull_parent_fiber (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V) (c : B) :
    pull (refinedBlockMap p b I S) (fiber (refinedBlockParent b I) c) = fiber p c := by
  ext v
  simp only [mem_pull, mem_fiber, refinedBlockParent_map]

/-- Each new label has a real vertex: old blocks use the original
surjectivity, children use their witnesses, and the residual uses the pivot. -/
theorem refinedBlockMap_surjective (p : V → B) (b : B) (I : Finset ι)
    (S : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (hp : Function.Surjective p) (r : V) (hr : p r = b)
    (hrS : ∀ i ∈ I, r ∉ S i)
    (hchild : ∀ i : I, ∃ v : V, p v = b ∧ v ∈ S i.val) :
    Function.Surjective (refinedBlockMap p b I S) := by
  intro c
  cases c with
  | inl c =>
      obtain ⟨v, hv⟩ := hp c.val
      exact ⟨v, (refinedBlockMap_eq_old p b I S v c).mpr hv⟩
  | inr c =>
      cases c with
      | none =>
          exact ⟨r, (refinedBlockMap_eq_residual p b I S r).mpr ⟨hr, hrS⟩⟩
      | some i =>
          obtain ⟨v, hvb, hvi⟩ := hchild i
          exact ⟨v, (refinedBlockMap_eq_child p b I S hdisj v i).mpr ⟨hvb, hvi⟩⟩

/-- Accepted terminals themselves can witness the child blocks. -/
theorem refinedBlockMap_surjective_of_terminals (p : V → B) (b : B) (I : Finset V)
    (S : V → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (hp : Function.Surjective p) (r : V) (hr : p r = b)
    (hrS : ∀ i ∈ I, r ∉ S i)
    (hI : ∀ i ∈ I, p i = b) (hself : ∀ i ∈ I, i ∈ S i) :
    Function.Surjective (refinedBlockMap p b I S) :=
  refinedBlockMap_surjective p b I S hdisj hp r hr hrS
    (fun i => ⟨i.val, hI i.val i.property, hself i.val i.property⟩)

theorem refinedBlock_card (b : B) (I : Finset ι) :
    Fintype.card (RefinedBlock b I) = Fintype.card B + I.card := by
  have hpos : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨b⟩
  have hc : Fintype.card (RefinedBlock b I) = Fintype.card B - 1 + (I.card + 1) := by
    let e : RefinedBlock b I ≃
        ((Finset.univ.erase b : Finset B) ⊕ Option I) := Equiv.refl _
    calc
      Fintype.card (RefinedBlock b I) =
          Fintype.card ((Finset.univ.erase b : Finset B) ⊕ Option I) := Fintype.card_congr e
      _ = _ := by
        simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_coe,
          Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
  omega

theorem refinedBlock_card_le (p : V → B) (b : B) (I : Finset ι) (S : ι → Finset V)
    (hsurj : Function.Surjective (refinedBlockMap p b I S)) :
    Fintype.card (RefinedBlock b I) ≤ Fintype.card V :=
  Fintype.card_le_of_surjective (refinedBlockMap p b I S) hsurj

/-- The cardinality bound concerns the actual refined map, rather than an
independent scalar recurrence. -/
theorem refinedBlock_growth_le (p : V → B) (b : B) (I : Finset ι) (S : ι → Finset V)
    (hsurj : Function.Surjective (refinedBlockMap p b I S)) :
    Fintype.card B + I.card ≤ Fintype.card V := by
  rw [← refinedBlock_card b I]
  exact refinedBlock_card_le p b I S hsurj

/-- The actual residual fiber and covered part partition the selected old
block. This equality needs no disjointness or graph-correctness assumption. -/
theorem refinedBlockMap_residual_partition_card (p : V → B) (b : B)
    (I : Finset ι) (S : ι → Finset V) :
    (fiber (refinedBlockMap p b I S) (Sum.inr none)).card +
      (fiber p b ∩ I.biUnion S).card = (fiber p b).card := by
  rw [refinedBlockMap_residual_fiber]
  exact Finset.card_sdiff_add_card_inter (fiber p b) (I.biUnion S)

/-- With disjoint accepted shores, the covered mass is the sum of the exact
child fibers described by `refinedBlockMap_child_fiber`. No vertex is lost. -/
theorem refinedBlockMap_partition_card (p : V → B) (b : B)
    (I : Finset ι) (S : ι → Finset V)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) :
    (fiber (refinedBlockMap p b I S) (Sum.inr none)).card +
      (∑ i ∈ I, (fiber p b ∩ S i).card) = (fiber p b).card := by
  have hparts : (I : Set ι).PairwiseDisjoint (fun i => fiber p b ∩ S i) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    exact Finset.disjoint_left.mp (hdisj i hi j hj hij)
      (Finset.mem_inter.mp hvi).2 (Finset.mem_inter.mp hvj).2
  have hunion : I.biUnion (fun i => fiber p b ∩ S i) = fiber p b ∩ I.biUnion S := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hvi).1,
        Finset.mem_biUnion.mpr ⟨i, hi, (Finset.mem_inter.mp hvi).2⟩⟩
    · intro hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hv).2
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hvi⟩⟩
  rw [← Finset.card_biUnion hparts, hunion]
  exact refinedBlockMap_residual_partition_card p b I S

#print axioms refinementCell_eq_none
#print axioms refinementCell_eq_some
#print axioms refinedBlockMap_eq_old
#print axioms refinedBlockMap_eq_residual
#print axioms refinedBlockMap_eq_child
#print axioms refinedBlockMap_old_fiber
#print axioms refinedBlockMap_residual_fiber
#print axioms refinedBlockMap_child_fiber
#print axioms refinedBlockParent_map
#print axioms refinedBlockMap_fiber_subset
#print axioms refinedBlockMap_pull_parent_fiber
#print axioms refinedBlockMap_surjective
#print axioms refinedBlockMap_surjective_of_terminals
#print axioms refinedBlock_card
#print axioms refinedBlock_card_le
#print axioms refinedBlock_growth_le
#print axioms refinedBlockMap_residual_partition_card
#print axioms refinedBlockMap_partition_card

end
end CutQueryComplexity.GHReduction
