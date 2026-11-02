import CutQueryComplexity.GHReduction.SteinerAssemblyFold

/-! # Public coverage and attachment laws for checked tree joins

These interfaces expose the actual checked join's terminal set and attachment
map. They are independent of minimum-cut correctness and remain valid for
zero bridge weights. Recursive assembly uses them to prove later public guards
rather than assuming that every join succeeds.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V U W : Type} [Fintype V] [DecidableEq V]
  [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

def Represents (T : PackedSteinerTree V) (x : V) : Prop := ∃ u, T.value.terminal u = x

theorem packSteinerTree_represents (T : SteinerCutTree V U) (x : V) :
    Represents (packSteinerTree T) x ↔ ∃ u, T.terminal u = x := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨(Fintype.equivFin U).symm w, hw⟩
  · rintro ⟨u, hu⟩
    refine ⟨Fintype.equivFin U u, ?_⟩
    simpa only [packSteinerTree, relabelSteinerTree, Function.comp_apply,
      Equiv.symm_apply_apply] using hu

theorem packSteinerTree_attach_eq (T : SteinerCutTree V U) {x y : V}
    (h : T.attach x = T.attach y) :
    (packSteinerTree T).value.attach x = (packSteinerTree T).value.attach y :=
  congrArg (Fintype.equivFin U) h

theorem checkedSteinerJoin_exists (L R : PackedSteinerTree V) (S : Finset V)
    (s t : V) (value : ℝ) (h : SteinerJoinGuard L R S s t) :
    ∃ out, checkedSteinerJoin L R S s t value = some out := by
  simp only [checkedSteinerJoin, h, dite_true]
  exact ⟨_, rfl⟩

theorem checkedSteinerJoin_represents (L R : PackedSteinerTree V) (S : Finset V)
    (s t : V) (value : ℝ) {out : PackedSteinerTree V}
    (hout : checkedSteinerJoin L R S s t value = some out) (x : V) :
    Represents out x ↔ Represents L x ∨ Represents R x := by
  by_cases h : SteinerJoinGuard L R S s t
  · have he : packSteinerTree (joinSteinerTrees S L.value R.value
        (L.value.attach t) (R.value.attach s) value h.2.2.1 h.2.2.2.1) = out := by
      simpa only [checkedSteinerJoin, h, dite_true, Option.some.injEq] using hout
    rw [← he, packSteinerTree_represents]
    change (∃ u : Fin L.size ⊕ Fin R.size, Sum.elim L.value.terminal R.value.terminal u = x) ↔ _
    constructor
    · rintro ⟨u, hu⟩
      cases u with
      | inl u => exact Or.inl ⟨u, hu⟩
      | inr u => exact Or.inr ⟨u, hu⟩
    · rintro (⟨u, hu⟩ | ⟨u, hu⟩)
      · exact ⟨Sum.inl u, hu⟩
      · exact ⟨Sum.inr u, hu⟩
  · simp [checkedSteinerJoin, h] at hout

theorem checkedSteinerJoin_attach_left (L R : PackedSteinerTree V) (S : Finset V)
    (s t : V) (value : ℝ) {out : PackedSteinerTree V}
    (hout : checkedSteinerJoin L R S s t value = some out)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (heq : L.value.attach x = L.value.attach y) :
    out.value.attach x = out.value.attach y := by
  by_cases h : SteinerJoinGuard L R S s t
  · have he : packSteinerTree (joinSteinerTrees S L.value R.value
        (L.value.attach t) (R.value.attach s) value h.2.2.1 h.2.2.2.1) = out := by
      simpa only [checkedSteinerJoin, h, dite_true, Option.some.injEq] using hout
    rw [← he]
    apply packSteinerTree_attach_eq
    change joinedAttach S L.value R.value x = joinedAttach S L.value R.value y
    simp only [joinedAttach, hx, hy, ite_true, heq]
  · simp [checkedSteinerJoin, h] at hout

theorem checkedSteinerJoin_attach_right (L R : PackedSteinerTree V) (S : Finset V)
    (s t : V) (value : ℝ) {out : PackedSteinerTree V}
    (hout : checkedSteinerJoin L R S s t value = some out)
    {x y : V} (hx : x ∉ S) (hy : y ∉ S) (heq : R.value.attach x = R.value.attach y) :
    out.value.attach x = out.value.attach y := by
  by_cases h : SteinerJoinGuard L R S s t
  · have he : packSteinerTree (joinSteinerTrees S L.value R.value
        (L.value.attach t) (R.value.attach s) value h.2.2.1 h.2.2.2.1) = out := by
      simpa only [checkedSteinerJoin, h, dite_true, Option.some.injEq] using hout
    rw [← he]
    apply packSteinerTree_attach_eq
    change joinedAttach S L.value R.value x = joinedAttach S L.value R.value y
    simp only [joinedAttach, hx, hy, ite_false, heq]
  · simp [checkedSteinerJoin, h] at hout

end
end CutQueryComplexity.GHReduction
