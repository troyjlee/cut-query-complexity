import CutQueryComplexity.AllPairsAudit.MinimalShore
import CutQueryComplexity.Graph.Integral
import Mathlib.Tactic

/-!
# Fixed canonical extensions of public core traces

The paper uses shores containing `t` and excluding `s`. A trace is the set of
core vertices labeled one. The representative minimizes the explicit graph
`K` on a finite set and is a fixed function of `C`, `K`, `s`, `t`, and the trace.
Neither the hidden graph nor subsequently learned core edges is an argument.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A core trace respects terminal labels even when either terminal was peeled. -/
def AdmissibleTrace (C : Finset V) (s t : V) (x : Finset V) : Prop :=
  x ⊆ C ∧ s ∉ x ∧ (t ∈ C → t ∈ x)

/-- All feasible extensions of one trace; this finite domain uses public data. -/
def extensionCandidates (C : Finset V) (s t : V) (x : Finset V) : Finset (Finset V) :=
  univ.filter fun S => t ∈ S ∧ s ∉ S ∧ S ∩ C = x

@[simp] theorem mem_extensionCandidates (C : Finset V) (s t : V) (x S : Finset V) :
    S ∈ extensionCandidates C s t x ↔ t ∈ S ∧ s ∉ S ∧ S ∩ C = x := by
  simp [extensionCandidates]

omit [Fintype V] in
theorem admissibleTrace_of_shore (C : Finset V) {s t : V} {S : Finset V}
    (ht : t ∈ S) (hs : s ∉ S) : AdmissibleTrace C s t (S ∩ C) := by
  exact ⟨inter_subset_right, fun h => hs (mem_inter.mp h).1,
    fun h => mem_inter.mpr ⟨ht, h⟩⟩

theorem extensionCandidates_nonempty (C : Finset V) {s t : V} (hst : s ≠ t)
    {x : Finset V} (hx : AdmissibleTrace C s t x) :
    (extensionCandidates C s t x).Nonempty := by
  refine ⟨insert t x, (mem_extensionCandidates _ _ _ _ _).mpr ⟨by simp, ?_, ?_⟩⟩
  · simp [hst, hx.2.1]
  · ext v
    constructor
    · intro hv
      obtain ⟨hv, hvC⟩ := mem_inter.mp hv
      rcases mem_insert.mp hv with rfl | hv
      · exact hx.2.2 hvC
      · exact hv
    · intro hv
      exact mem_inter.mpr ⟨mem_insert_of_mem hv, hx.1 hv⟩

/-- Fixed finite minimization of the public outside graph. Invalid traces
return the empty set; every admissible trace is proved feasible below. -/
def canonicalExtension (C : Finset V) (K : WeightedGraph V) (s t : V)
    (x : Finset V) : Finset V :=
  if h : (extensionCandidates C s t x).Nonempty then
    Classical.choose (Finset.exists_min_image (extensionCandidates C s t x) K.cut h)
  else ∅

theorem canonicalExtension_spec (C : Finset V) (K : WeightedGraph V)
    {s t : V} (hst : s ≠ t) {x : Finset V} (hx : AdmissibleTrace C s t x) :
    t ∈ canonicalExtension C K s t x ∧ s ∉ canonicalExtension C K s t x ∧
      canonicalExtension C K s t x ∩ C = x := by
  have h := extensionCandidates_nonempty C hst hx
  rw [canonicalExtension, dite_eq_left h]
  exact (mem_extensionCandidates _ _ _ _ _).mp
    (Classical.choose_spec (Finset.exists_min_image (extensionCandidates C s t x) K.cut h)).1

theorem canonicalExtension_min (C : Finset V) (K : WeightedGraph V)
    {s t : V} (hst : s ≠ t) {x : Finset V} (hx : AdmissibleTrace C s t x)
    {S : Finset V} (ht : t ∈ S) (hs : s ∉ S) (htrace : S ∩ C = x) :
    K.cut (canonicalExtension C K s t x) ≤ K.cut S := by
  have h := extensionCandidates_nonempty C hst hx
  rw [canonicalExtension, dite_eq_left h]
  exact (Classical.choose_spec
    (Finset.exists_min_image (extensionCandidates C s t x) K.cut h)).2 S
      ((mem_extensionCandidates _ _ _ _ _).mpr ⟨ht, hs, htrace⟩)

theorem canonicalExtension_trace (C : Finset V) (K : WeightedGraph V)
    {s t : V} (hst : s ≠ t) {x : Finset V} (hx : AdmissibleTrace C s t x) :
    canonicalExtension C K s t x ∩ C = x :=
  (canonicalExtension_spec C K hst hx).2.2

/-- Distinct admissible labels cannot collapse to the same representative. -/
theorem canonicalExtension_injective (C : Finset V) (K : WeightedGraph V)
    {s t : V} (hst : s ≠ t) {x y : Finset V}
    (hx : AdmissibleTrace C s t x) (hy : AdmissibleTrace C s t y)
    (he : canonicalExtension C K s t x = canonicalExtension C K s t y) : x = y := by
  rw [← canonicalExtension_trace C K hst hx, he, canonicalExtension_trace C K hst hy]

def canonicalFamily (C : Finset V) (K : WeightedGraph V) (s t : V) : Finset (Finset V) :=
  (univ.filter (AdmissibleTrace C s t)).image (canonicalExtension C K s t)

theorem canonicalExtension_mem_family (C : Finset V) (K : WeightedGraph V)
    {s t : V} {x : Finset V} (hx : AdmissibleTrace C s t x) :
    canonicalExtension C K s t x ∈ canonicalFamily C K s t := by
  exact mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ x, hx⟩, rfl⟩

theorem canonicalFamily_terminal (C : Finset V) (K : WeightedGraph V)
    {s t : V} (hst : s ≠ t) {S : Finset V} (hS : S ∈ canonicalFamily C K s t) :
    t ∈ S ∧ s ∉ S := by
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hS
  have h := canonicalExtension_spec C K hst (mem_filter.mp hx).2
  exact ⟨h.1, h.2.1⟩

/-- A graph supported in the core depends only on the shore's core trace. -/
theorem cut_eq_of_core_trace (C : Finset V) (L : WeightedGraph V)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0)
    {S T : Finset V} (htrace : S ∩ C = T ∩ C) : L.cut S = L.cut T := by
  have hind : L.induce C = L := by
    ext u v
    by_cases hu : u ∈ C
    · by_cases hv : v ∈ C
      · simp [WeightedGraph.induce, hu, hv]
      · simp [WeightedGraph.induce, hu, hv, hL u v (Or.inr hv)]
    · simp [WeightedGraph.induce, hu, hL u v (Or.inl hu)]
  have he (U : Finset V) : L.cut U = L.localCut C U := by
    rw [localCut_eq_cut_induce, hind]
  calc
    L.cut S = L.localCut C (S ∩ C) := (he S).trans (L.localCut_inter C S).symm
    _ = L.localCut C (T ∩ C) := by rw [htrace]
    _ = L.cut T := (L.localCut_inter C T).trans (he T).symm

/-- The learned core contribution is exactly the cut of the public trace;
the outside contribution is the same fixed K-minimizing representative. -/
theorem canonicalExtension_cut_add (C : Finset V) (K L : WeightedGraph V)
    {s t : V} (hst : s ≠ t) {x : Finset V} (hx : AdmissibleTrace C s t x)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) :
    (K.add L).cut (canonicalExtension C K s t x) =
      K.cut (canonicalExtension C K s t x) + L.cut x := by
  rw [cut_add]
  have htrace : canonicalExtension C K s t x ∩ C = x ∩ C := by
    rw [canonicalExtension_trace C K hst hx, inter_eq_left.mpr hx.1]
  rw [cut_eq_of_core_trace C L hL htrace]

/-- Canonicalizing a terminal shore never increases any extension by core edges. -/
theorem canonicalExtension_cut_le (C : Finset V) (K L : WeightedGraph V)
    {s t : V} (hst : s ≠ t)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0)
    {S : Finset V} (ht : t ∈ S) (hs : s ∉ S) :
    (K.add L).cut (canonicalExtension C K s t (S ∩ C)) ≤ (K.add L).cut S := by
  have hx := admissibleTrace_of_shore C ht hs
  have hk := canonicalExtension_min C K hst hx ht hs rfl
  have hl := cut_eq_of_core_trace C L hL (canonicalExtension_trace C K hst hx)
  rw [cut_add, cut_add, hl]
  linarith only [hk]

/-- The fixed family contains a true terminal optimum for every supported
core extension. No minimum-degree, seed graph, or counting theorem is assumed. -/
theorem canonicalFamily_contains_optimum (C : Finset V) (K L : WeightedGraph V)
    {s t : V} (hst : s ≠ t)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) :
    ∃ S ∈ canonicalFamily C K s t, IsSTMinCut (K.add L) t s S := by
  obtain ⟨T, hT⟩ := AllPairsAudit.exists_st_minimum (K.add L) (Ne.symm hst)
  have hx := admissibleTrace_of_shore C hT.1 hT.2.1
  have hf := canonicalExtension_spec C K hst hx
  refine ⟨canonicalExtension C K s t (T ∩ C),
    canonicalExtension_mem_family C K hx, hf.1, hf.2.1, ?_⟩
  intro U ht hs
  exact (canonicalExtension_cut_le C K L hst hL hT.1 hT.2.1).trans (hT.2.2 U ht hs)

/-- Complementing restores the repository's source-oriented output convention
and preserves the exact cut value. -/
theorem canonicalFamily_contains_output_optimum (C : Finset V) (K L : WeightedGraph V)
    {s t : V} (hst : s ≠ t)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) :
    ∃ S ∈ canonicalFamily C K s t, IsSTMinCut (K.add L) s t Sᶜ ∧
      (K.add L).cut Sᶜ = (K.add L).cut S := by
  obtain ⟨S, hS, hmin⟩ := canonicalFamily_contains_optimum C K L hst hL
  exact ⟨S, hS, AllPairsAudit.st_compl _ hmin, (K.add L).cut_compl S⟩

end
end CutQueryComplexity.CanonicalST

#print axioms CutQueryComplexity.CanonicalST.canonicalExtension_spec
#print axioms CutQueryComplexity.CanonicalST.canonicalExtension_min
#print axioms CutQueryComplexity.CanonicalST.canonicalExtension_injective
#print axioms CutQueryComplexity.CanonicalST.cut_eq_of_core_trace
#print axioms CutQueryComplexity.CanonicalST.canonicalExtension_cut_add
#print axioms CutQueryComplexity.CanonicalST.canonicalExtension_cut_le
#print axioms CutQueryComplexity.CanonicalST.canonicalFamily_contains_optimum
#print axioms CutQueryComplexity.CanonicalST.canonicalFamily_contains_output_optimum
