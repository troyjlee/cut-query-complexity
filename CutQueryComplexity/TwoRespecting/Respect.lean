import CutQueryComplexity.TwoRespecting.Main

/-! # Shores crossing at most two tree edges

For a rooted tree `T` and a shore `S`, `crossedEdges T S` is the set of tree edges
(non-root vertices `v`, standing for the edge to `parent v`) whose endpoints lie on
different sides of `S`. Membership in `S` flips exactly along crossed edges, so a
vertex lies in `S` iff the root does, up to the parity of crossed edges above it.
Consequently a proper shore crossing at most two tree edges, or its complement, is
one of the shores searched by `twoRespecting` (`isTwoRespShore_of_card_le_two`).
-/

namespace CutQueryComplexity
namespace TwoRespecting

open RootedTree

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (T : RootedTree V)

/-- Tree edges crossed by the shore `S`. -/
noncomputable def RootedTree.crossedEdges (S : Finset V) : Finset V :=
  Finset.univ.filter fun v => v ≠ T.root ∧ ¬ (v ∈ S ↔ T.parent v ∈ S)

variable {T}

omit [LinearOrder V] in
theorem mem_crossedEdges {S : Finset V} {v : V} :
    v ∈ T.crossedEdges S ↔ v ≠ T.root ∧ ¬ (v ∈ S ↔ T.parent v ∈ S) := by
  simp [RootedTree.crossedEdges]

omit [LinearOrder V] in
/-- Membership flips exactly along crossed edges. -/
theorem mem_iff_parity (S : Finset V) : ∀ (n : ℕ) (x : V), T.depth x ≤ n →
    (x ∈ S ↔ (T.root ∈ S ↔ Even ((T.crossedEdges S).filter fun d => T.IsAnc d x).card))
  | 0, x, hx => by
      have hxr := eq_root_of_depth_eq_zero (Nat.le_zero.mp hx)
      subst hxr
      have : (T.crossedEdges S).filter (fun d => T.IsAnc d T.root) = ∅ := by
        ext d
        simp only [Finset.mem_filter, mem_crossedEdges, Finset.notMem_empty, iff_false, not_and]
        intro hd hanc
        exact hd.1 hanc.eq_root_of_isAnc_root
      simp [this]
  | n + 1, x, hx => by
      by_cases hxr : x = T.root
      · subst hxr; exact mem_iff_parity S 0 T.root (by rw [T.depth_root])
      have hdp : T.depth (T.parent x) ≤ n := by have := T.depth_parent x hxr; omega
      have ih := mem_iff_parity S n (T.parent x) hdp
      have hsplit : (T.crossedEdges S).filter (fun d => T.IsAnc d x) =
          ((T.crossedEdges S).filter fun d => T.IsAnc d (T.parent x)) ∪
            (if x ∈ T.crossedEdges S then {x} else ∅) := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_union]
        rw [isAnc_iff_eq_or_isAnc_parent]
        split_ifs with hx'
        · simp only [Finset.mem_singleton]
          constructor
          · rintro ⟨hd, rfl | ⟨-, h⟩⟩
            · exact Or.inr rfl
            · exact Or.inl ⟨hd, h⟩
          · rintro (⟨hd, h⟩ | rfl)
            · exact ⟨hd, Or.inr ⟨hxr, h⟩⟩
            · exact ⟨hx', Or.inl rfl⟩
        · simp only [Finset.notMem_empty, or_false]
          constructor
          · rintro ⟨hd, rfl | ⟨-, h⟩⟩
            · exact absurd hd hx'
            · exact ⟨hd, h⟩
          · rintro ⟨hd, h⟩
            exact ⟨hd, Or.inr ⟨hxr, h⟩⟩
      have hdisj : Disjoint ((T.crossedEdges S).filter fun d => T.IsAnc d (T.parent x))
          (if x ∈ T.crossedEdges S then {x} else ∅) := by
        split_ifs
        · rw [Finset.disjoint_singleton_right, Finset.mem_filter]
          rintro ⟨-, h⟩
          have := h.depth_le
          have := T.depth_parent x hxr
          omega
        · exact Finset.disjoint_empty_right _
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
      by_cases hx' : x ∈ T.crossedEdges S
      · rw [ite_eq_left hx', Finset.card_singleton, Nat.even_add_one]
        rw [mem_crossedEdges] at hx'
        have := hx'.2
        rw [ih] at this
        tauto
      · rw [ite_eq_right hx', Finset.card_empty, Nat.add_zero]
        rw [mem_crossedEdges] at hx'
        push Not at hx'
        rw [hx' hxr, ih]

omit [LinearOrder V] in
/-- A proper shore crossing at most two tree edges, or its complement, is a searched
two-respecting shore. -/
theorem isTwoRespShore_of_card_le_two {S : Finset V} (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (hc : (T.crossedEdges S).card ≤ 2) :
    T.IsTwoRespShore S ∨ T.IsTwoRespShore Sᶜ := by
  have hpar := fun x => mem_iff_parity (T := T) S (T.depth x) x le_rfl
  have hmemD : ∀ d ∈ T.crossedEdges S, d ≠ T.root := fun d hd => (mem_crossedEdges.mp hd).1
  -- `S` is determined by the root's side and the crossed edges
  have key : ∀ (P : V → Prop) [DecidablePred P], (∀ x, (x ∈ S ↔ (T.root ∈ S ↔ ¬ P x))) →
      (T.root ∉ S → S = Finset.univ.filter P) ∧ (T.root ∈ S → Sᶜ = Finset.univ.filter P) := by
    intro P _ hP
    refine ⟨fun hr => ?_, fun hr => ?_⟩
    · ext x; rw [hP x]; simp [hr]
    · ext x; rw [Finset.mem_compl, hP x]; simp [hr]
  rcases Nat.lt_or_ge (T.crossedEdges S).card 1 with h0 | h1
  · -- no crossed edge: `S` would be empty or everything
    have hempty : T.crossedEdges S = ∅ := Finset.card_eq_zero.mp (by omega)
    exfalso
    have hall : ∀ x, x ∈ S ↔ T.root ∈ S := fun x => by rw [hpar x, hempty]; simp
    by_cases hr : T.root ∈ S
    · exact hS' (Finset.eq_univ_of_forall fun x => (hall x).mpr hr)
    · obtain ⟨x, hx⟩ := hS
      exact hr ((hall x).mp hx)
  rcases Nat.lt_or_ge (T.crossedEdges S).card 2 with h1' | h2
  · obtain ⟨e, he⟩ := Finset.card_eq_one.mp (show (T.crossedEdges S).card = 1 by omega)
    have hP : ∀ x, (x ∈ S ↔ (T.root ∈ S ↔ ¬ T.IsAnc e x)) := by
      intro x
      rw [hpar x, he]
      by_cases hex : T.IsAnc e x
      · simp [Finset.filter_singleton, hex]
      · simp [Finset.filter_singleton, hex]
    have heS : e ≠ T.root := hmemD e (by rw [he]; exact Finset.mem_singleton_self e)
    obtain ⟨k1, k2⟩ := key (T.IsAnc e) hP
    have hsub : Finset.univ.filter (T.IsAnc e) = T.subtree e := by ext x; simp
    by_cases hr : T.root ∈ S
    · exact Or.inr (Or.inl ⟨e, heS, (k2 hr).trans hsub⟩)
    · exact Or.inl (Or.inl ⟨e, heS, (k1 hr).trans hsub⟩)
  · obtain ⟨e, f, hef, he⟩ := Finset.card_eq_two.mp (show (T.crossedEdges S).card = 2 by omega)
    have heS : e ≠ T.root := hmemD e (by rw [he]; simp)
    have hfS : f ≠ T.root := hmemD f (by rw [he]; simp)
    have hP : ∀ x, (x ∈ S ↔ (T.root ∈ S ↔ ¬ (¬ (T.IsAnc e x ↔ T.IsAnc f x)))) := by
      intro x
      rw [hpar x, he]
      by_cases hex : T.IsAnc e x <;> by_cases hfx : T.IsAnc f x <;>
        simp [Finset.filter_insert, Finset.filter_singleton, hex, hfx, hef]
    obtain ⟨k1, k2⟩ := key (fun x => ¬ (T.IsAnc e x ↔ T.IsAnc f x)) hP
    have hsub : Finset.univ.filter (fun x => ¬ (T.IsAnc e x ↔ T.IsAnc f x)) = T.pairShore e f := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, RootedTree.pairShore,
        Finset.mem_symmDiff, mem_subtree]
      tauto
    by_cases hr : T.root ∈ S
    · exact Or.inr (Or.inr ⟨e, f, heS, hfS, hef, (k2 hr).trans hsub⟩)
    · exact Or.inl (Or.inr ⟨e, f, heS, hfS, hef, (k1 hr).trans hsub⟩)

end TwoRespecting
end CutQueryComplexity
