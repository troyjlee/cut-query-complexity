import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Public enumeration of labelled trees

The raw tree subtype is definitionally the `LabelledTree` type used by the
tree-pattern certificate. This module is independent of that certificate's
costs, weighted graph, divergence, and verification program.

The Prüfer construction below works on a finite set of active labels. Removed
labels remain isolated in the ambient graph, avoiding any relabelling during
leaf deletion.
-/

set_option autoImplicit false

namespace CutQueryComplexity.Certificate.TreePattern

open Finset SimpleGraph
open scoped Classical
noncomputable section

/-- All labelled trees, determined before any weighted input or divergence. -/
def labelledTrees (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  univ.filter SimpleGraph.IsTree

@[simp] theorem mem_labelledTrees {n : ℕ} (T : SimpleGraph (Fin n)) :
    T ∈ labelledTrees n ↔ T.IsTree := by simp [labelledTrees]

theorem labelledTree_card_zero :
    Fintype.card {T : SimpleGraph (Fin 0) // T.IsTree} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun T => ?_⟩
  obtain ⟨v⟩ := T.property.connected.nonempty
  exact Fin.elim0 v

theorem labelledTree_card_one :
    Fintype.card {T : SimpleGraph (Fin 1) // T.IsTree} = 1 := by
  letI : Unique {T : SimpleGraph (Fin 1) // T.IsTree} :=
    ⟨⟨⊥, SimpleGraph.IsTree.of_subsingleton⟩,
      fun T => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Fintype.card_unique

abbrev PruferCode (n : ℕ) := Fin (n - 2) → Fin n

namespace Prufer

variable {α : Type} [Fintype α] [LinearOrder α]

/-- A tree on the active labels, with every other ambient label isolated. -/
structure TreeOn (S : Finset α) (G : SimpleGraph α) : Prop where
  nonempty : S.Nonempty
  supported : ∀ {u v}, G.Adj u v → u ∈ S ∧ v ∈ S
  acyclic : G.IsAcyclic
  reachable : ∀ u ∈ S, ∀ v ∈ S, G.Reachable u v

def eraseVertex (G : SimpleGraph α) (v : α) : SimpleGraph α where
  Adj x y := x ≠ v ∧ y ≠ v ∧ G.Adj x y
  symm := ⟨by intro x y h; exact ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨by intro x h; exact G.irrefl h.2.2⟩

@[simp] theorem eraseVertex_adj (G : SimpleGraph α) (v x y : α) :
    (eraseVertex G v).Adj x y ↔ x ≠ v ∧ y ≠ v ∧ G.Adj x y := Iff.rfl

theorem eraseVertex_le (G : SimpleGraph α) (v : α) : eraseVertex G v ≤ G :=
  fun _ _ h => h.2.2

theorem walk_support_mem {S : Finset α} {G : SimpleGraph α}
    (hsupp : ∀ {u v}, G.Adj u v → u ∈ S ∧ v ∈ S)
    {u v : α} (hu : u ∈ S) (p : G.Walk u v) : ∀ x ∈ p.support, x ∈ S := by
  induction p with
  | nil => simpa using hu
  | @cons u w v h p ih =>
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · exact ih (hsupp h).2 x hx

theorem TreeOn.induce_isTree {S : Finset α} {G : SimpleGraph α} (h : TreeOn S G) :
    (G.induce (S : Set α)).IsTree := by
  letI : Nonempty (S : Set α) := ⟨⟨h.nonempty.choose, h.nonempty.choose_spec⟩⟩
  refine ⟨⟨?_⟩, h.acyclic.induce _⟩
  intro u v
  let p := (h.reachable u.val u.property v.val v.property).some
  exact (p.induce (S : Set α) (walk_support_mem h.supported u.property p)).reachable

theorem TreeOn.univ_iff (G : SimpleGraph α) : TreeOn univ G ↔ G.IsTree := by
  constructor
  · intro h
    letI : Nonempty α := ⟨h.nonempty.choose⟩
    exact ⟨⟨fun u v => h.reachable u (mem_univ _) v (mem_univ _)⟩, h.acyclic⟩
  · intro h
    obtain ⟨v⟩ := h.connected.nonempty
    exact ⟨⟨v, mem_univ _⟩, fun _ => ⟨mem_univ _, mem_univ _⟩,
      h.isAcyclic, fun u _ v _ => h.connected u v⟩

theorem TreeOn.exists_leaf {S : Finset α} {G : SimpleGraph α}
    (h : TreeOn S G) (hS : 2 ≤ S.card) : ∃ v ∈ S, G.degree v = 1 := by
  have hcard : 1 < Fintype.card (S : Set α) := by
    simpa using (show 1 < S.card by omega)
  letI : Nontrivial (S : Set α) := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨v, hv⟩ := h.induce_isTree.exists_vert_degree_one_of_nontrivial
  obtain ⟨a, ha, hunique⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
  refine ⟨v.val, v.property, degree_eq_one_iff_existsUnique_adj.mpr ?_⟩
  refine ⟨a.val, ha, ?_⟩
  intro x hx
  have hxS := (h.supported hx).2
  exact congrArg Subtype.val (hunique ⟨x, hxS⟩ hx)

theorem TreeOn.erase_leaf {S : Finset α} {G : SimpleGraph α}
    (h : TreeOn S G) {v : α} (hv : v ∈ S) (hdeg : G.degree v = 1) :
    TreeOn (S.erase v) (eraseVertex G v) := by
  obtain ⟨a, ha, hunique⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  have haS := (h.supported ha).2
  let vs : (S : Set α) := ⟨v, hv⟩
  have hdegS : (G.induce (S : Set α)).degree vs = 1 := by
    apply degree_eq_one_iff_existsUnique_adj.mpr
    refine ⟨⟨a, haS⟩, ha, ?_⟩
    intro x hx
    exact Subtype.ext (hunique x.val hx)
  have hc := h.induce_isTree.connected.induce_compl_singleton_of_degree_eq_one hdegS
  let f : ((G.induce (S : Set α)).induce ({vs}ᶜ)) →g eraseVertex G v :=
    { toFun := fun x => x.val.val
      map_rel' := by
        intro x y hxy
        refine ⟨?_, ?_, hxy⟩
        · intro he
          exact x.property (Subtype.ext he)
        · intro he
          exact y.property (Subtype.ext he) }
  refine ⟨⟨a, mem_erase.mpr ⟨ha.ne', haS⟩⟩, ?_,
    h.acyclic.anti (eraseVertex_le G v), ?_⟩
  · intro x y hxy
    exact ⟨mem_erase.mpr ⟨hxy.1, (h.supported hxy.2.2).1⟩,
      mem_erase.mpr ⟨hxy.2.1, (h.supported hxy.2.2).2⟩⟩
  · intro x hx y hy
    let xs : (S : Set α) := ⟨x, mem_of_mem_erase hx⟩
    let ys : (S : Set α) := ⟨y, mem_of_mem_erase hy⟩
    have hxv : xs ∈ ({vs}ᶜ : Set (S : Set α)) := by
      intro he
      exact (mem_erase.mp hx).1 (congrArg Subtype.val he)
    have hyv : ys ∈ ({vs}ᶜ : Set (S : Set α)) := by
      intro he
      exact (mem_erase.mp hy).1 (congrArg Subtype.val he)
    exact (hc ⟨xs, hxv⟩ ⟨ys, hyv⟩).map f

theorem TreeOn.attach_leaf {S : Finset α} {G : SimpleGraph α}
    (h : TreeOn S G) {v a : α} (hv : v ∉ S) (ha : a ∈ S) :
    TreeOn (insert v S) (G ⊔ edge v a) := by
  have hva : v ≠ a := fun he => hv (he.symm ▸ ha)
  have hnreach : ¬G.Reachable v a := by
    intro hr
    obtain ⟨x, hx⟩ := hr.nonempty_neighborSet_left hva
    exact hv (h.supported hx).1
  refine ⟨⟨v, mem_insert_self _ _⟩, ?_,
    h.acyclic.sup_edge_of_not_reachable hnreach, ?_⟩
  · intro x y hxy
    rcases hxy with hxy | hxy
    · exact ⟨mem_insert_of_mem (h.supported hxy).1,
        mem_insert_of_mem (h.supported hxy).2⟩
    · rw [edge_adj] at hxy
      rcases hxy.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ha]
  · have hreach (x : α) (hx : x ∈ insert v S) : (G ⊔ edge v a).Reachable x a := by
      rcases mem_insert.mp hx with hxv | hx
      · subst x
        exact (show (G ⊔ edge v a).Adj v a from
          Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hva⟩)).reachable
      · exact (h.reachable x hx a ha).mono le_sup_left
    intro x hx y hy
    exact (hreach x hx).trans (hreach y hy).symm

theorem eraseVertex_attach {S : Finset α} {G : SimpleGraph α}
    (hsupp : ∀ {x y}, G.Adj x y → x ∈ S ∧ y ∈ S)
    {v a : α} (hv : v ∉ S) : eraseVertex (G ⊔ edge v a) v = G := by
  ext x y
  simp only [eraseVertex_adj, sup_adj, edge_adj]
  constructor
  · rintro ⟨hx, hy, h | h⟩
    · exact h
    · rcases h.1 with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> contradiction
  · intro h
    refine ⟨?_, ?_, Or.inl h⟩
    · intro he; exact hv (he ▸ (hsupp h).1)
    · intro he; exact hv (he ▸ (hsupp h).2)

theorem reconstruct_leaf {G : SimpleGraph α} {v a : α}
    (ha : G.Adj v a) (hunique : ∀ x, G.Adj v x → x = a) :
    eraseVertex G v ⊔ edge v a = G := by
  ext x y
  simp only [sup_adj, eraseVertex_adj, edge_adj]
  constructor
  · rintro (⟨_, _, h⟩ | ⟨h, _⟩)
    · exact h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ha
      · exact ha.symm
  · intro h
    by_cases hx : x = v
    · subst x
      exact Or.inr ⟨Or.inl ⟨rfl, hunique y h⟩, h.ne⟩
    by_cases hy : y = v
    · subst y
      exact Or.inr ⟨Or.inr ⟨hunique x h.symm, rfl⟩, h.ne⟩
    exact Or.inl ⟨hx, hy, h⟩

end Prufer
end
end CutQueryComplexity.Certificate.TreePattern

#print axioms CutQueryComplexity.Certificate.TreePattern.labelledTree_card_zero
#print axioms CutQueryComplexity.Certificate.TreePattern.labelledTree_card_one
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.TreeOn.exists_leaf
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.TreeOn.erase_leaf
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.TreeOn.attach_leaf
#print axioms CutQueryComplexity.Certificate.TreePattern.Prufer.reconstruct_leaf
