import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite separating measurements and exhaustive decoding

All candidate vectors and all candidate subset-measurement families are finite
public sets. We select the first family of minimum cardinality and decode by
examining its finite consistent set. Singleton tests prove existence without
an assumed recovery oracle. This file supplies no logarithmic query bound;
that bound must be proved for these same families in the sparse decoder module.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Recovery

open Finset
open scoped Classical
noncomputable section

variable {C : Type} [Fintype C] [DecidableEq C]

/-- A Boolean measurement is a subset of the named coordinates. -/
abbrev TestFamily (C : Type) := Finset (Finset C)

def measure (S : Finset C) (x : C → ℕ) : ℕ := ∑ c ∈ S, x c

def signature (F : TestFamily C) (x : C → ℕ) : F → ℕ :=
  fun S => measure S.1 x

/-- Separation is an ordinary injectivity statement for actual subset sums. -/
def Separates (F : TestFamily C) (A : Finset (C → ℕ)) : Prop :=
  Set.InjOn (signature F) (A : Set (C → ℕ))

/-- Explicit enumeration of all vectors with entries in `[0,d]`. -/
def box (C : Type) [Fintype C] [DecidableEq C] (d : ℕ) : Finset (C → ℕ) :=
  univ.image fun x : C → Fin (d + 1) => fun c => (x c : ℕ)

theorem mem_box {d : ℕ} {x : C → ℕ} :
    x ∈ box C d ↔ ∀ c, x c ≤ d := by
  constructor
  · intro hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hx
    exact fun c => Nat.le_of_lt_succ (y c).isLt
  · intro hx
    exact mem_image.mpr ⟨(fun c => ⟨x c, Nat.lt_succ_of_le (hx c)⟩), mem_univ _, rfl⟩

/-- Explicit Boolean sparse vectors; this handles zero dimensions and zero sparsity. -/
def sparse (C : Type) [Fintype C] [DecidableEq C] (ell : ℕ) : Finset (C → ℕ) :=
  (box C 1).filter fun x => measure univ x ≤ ell

theorem mem_sparse {ell : ℕ} {x : C → ℕ} :
    x ∈ sparse C ell ↔ (∀ c, x c ≤ 1) ∧ measure univ x ≤ ell := by
  simp only [sparse, mem_filter, mem_box]

/-- A public baseline family, used only to prove totality of the finite search. -/
def singletonFamily (C : Type) [Fintype C] [DecidableEq C] : TestFamily C :=
  univ.image fun c : C => ({c} : Finset C)

theorem singletonFamily_separates (A : Finset (C → ℕ)) :
    Separates (singletonFamily C) A := by
  intro x _ y _ h
  funext c
  have hc : ({c} : Finset C) ∈ singletonFamily C := mem_image_of_mem _ (mem_univ c)
  have he := congrFun h ⟨{c}, hc⟩
  simpa only [signature, measure, sum_singleton] using he

def separatingFamilies (A : Finset (C → ℕ)) : Finset (TestFamily C) :=
  univ.filter fun F => Separates F A

theorem mem_separatingFamilies {A : Finset (C → ℕ)} {F : TestFamily C} :
    F ∈ separatingFamilies A ↔ Separates F A := by
  simp only [separatingFamilies, mem_filter, mem_univ, true_and]

theorem separatingFamilies_nonempty (A : Finset (C → ℕ)) :
    (separatingFamilies A).Nonempty :=
  ⟨singletonFamily C, mem_separatingFamilies.mpr (singletonFamily_separates A)⟩

/-- Enumerate all cardinality minimizers; no matrix/oracle enters this search. -/
def minimumCandidates (A : Finset (C → ℕ)) : Finset (TestFamily C) :=
  (separatingFamilies A).filter fun F =>
    ∀ E ∈ separatingFamilies A, F.card ≤ E.card

theorem minimumCandidates_nonempty (A : Finset (C → ℕ)) :
    (minimumCandidates A).Nonempty := by
  obtain ⟨F, hF, hmin⟩ := exists_min_image (separatingFamilies A)
    Finset.card (separatingFamilies_nonempty A)
  exact ⟨F, mem_filter.mpr ⟨hF, hmin⟩⟩

/-- First minimum-size family in an explicitly finite exhaustive enumeration. -/
def minimumFamily (A : Finset (C → ℕ)) : TestFamily C :=
  (minimumCandidates A).toList.head (minimumCandidates_nonempty A).toList_ne_nil

theorem minimumFamily_mem (A : Finset (C → ℕ)) :
    minimumFamily A ∈ minimumCandidates A := by
  exact mem_toList.mp (List.head_mem (minimumCandidates_nonempty A).toList_ne_nil)

theorem minimumFamily_separates (A : Finset (C → ℕ)) :
    Separates (minimumFamily A) A :=
  mem_separatingFamilies.mp (mem_filter.mp (minimumFamily_mem A)).1

/-- Later existence bounds transfer to the same public minimum-family selector. -/
theorem minimumFamily_card_le {A : Finset (C → ℕ)} {F : TestFamily C}
    (hF : Separates F A) : (minimumFamily A).card ≤ F.card :=
  (mem_filter.mp (minimumFamily_mem A)).2 F (mem_separatingFamilies.mpr hF)

/-- Only a finiteness baseline; it is not the efficient recovery bound. -/
theorem minimumFamily_card_le_dimension (A : Finset (C → ℕ)) :
    (minimumFamily A).card ≤ Fintype.card C := by
  apply (minimumFamily_card_le (singletonFamily_separates A)).trans
  exact (card_image_le).trans_eq (card_univ : (univ : Finset C).card = Fintype.card C)

def consistent (A : Finset (C → ℕ)) (F : TestFamily C) (answers : F → ℕ) :
    Finset (C → ℕ) := A.filter fun x => signature F x = answers

/-- Reject an inconsistent finite transcript; otherwise inspect its first candidate. -/
def decode (A : Finset (C → ℕ)) (F : TestFamily C) (answers : F → ℕ) :
    Option (C → ℕ) := (consistent A F answers).toList.head?

theorem decode_sound {A : Finset (C → ℕ)} {F : TestFamily C} {answers : F → ℕ}
    {x : C → ℕ} (hx : decode A F answers = some x) :
    x ∈ A ∧ signature F x = answers := by
  have hmem : x ∈ consistent A F answers := mem_toList.mp (List.mem_of_head? hx)
  exact mem_filter.mp hmem

theorem decode_correct {A : Finset (C → ℕ)} {F : TestFamily C}
    (hF : Separates F A) {x : C → ℕ} (hx : x ∈ A) :
    decode A F (signature F x) = some x := by
  have hc : consistent A F (signature F x) = {x} := by
    ext y
    simp only [consistent, mem_filter, mem_singleton]
    constructor
    · rintro ⟨hy, he⟩
      exact hF hy hx he
    · intro he
      subst y
      exact ⟨hx, rfl⟩
  simp only [decode, hc, toList_singleton, List.head?_cons]

theorem minimumFamily_decode {A : Finset (C → ℕ)} {x : C → ℕ} (hx : x ∈ A) :
    decode A (minimumFamily A) (signature (minimumFamily A) x) = some x :=
  decode_correct (minimumFamily_separates A) hx

theorem box_decode {d : ℕ} {x : C → ℕ} (hx : ∀ c, x c ≤ d) :
    decode (box C d) (minimumFamily (box C d))
      (signature (minimumFamily (box C d)) x) = some x :=
  minimumFamily_decode (mem_box.mpr hx)

theorem sparse_decode {ell : ℕ} {x : C → ℕ}
    (hx : ∀ c, x c ≤ 1) (hs : measure univ x ≤ ell) :
    decode (sparse C ell) (minimumFamily (sparse C ell))
      (signature (minimumFamily (sparse C ell)) x) = some x :=
  minimumFamily_decode (mem_sparse.mpr ⟨hx, hs⟩)

end
end CutQueryComplexity.StarContraction2022.Recovery

#print axioms CutQueryComplexity.StarContraction2022.Recovery.mem_box
#print axioms CutQueryComplexity.StarContraction2022.Recovery.singletonFamily_separates
#print axioms CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_separates
#print axioms CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_card_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.decode_sound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_decode
#print axioms CutQueryComplexity.StarContraction2022.Recovery.sparse_decode
