import CutQueryComplexity.GHReduction.CanonicalCuts
import CutQueryComplexity.Certificate.Isolating

/-! # Binary separators and disjoint isolating cells

Disjointness and the aggregate cell size hold for every collection of returned
bit shores, including malformed oracle histories. Containment of the canonical
isolating shore additionally uses optimality of the bit separators.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph
open Certificate (termIdx bitClass mem_bitClass)

variable {V : Type} [Fintype V] [DecidableEq V]

theorem bitClass_union (R : Finset V) (j : ℕ) :
    bitClass R j true ∪ bitClass R j false = R := by
  ext v
  cases h : (termIdx R v).testBit j <;> simp [mem_bitClass, h]

theorem bitClass_sdiff (R : Finset V) (j : ℕ) :
    R \ bitClass R j true = bitClass R j false := by
  ext v
  cases h : (termIdx R v).testBit j <;> simp [mem_bitClass, h]

def bitSide (R : Finset V) (cuts : Fin (Nat.clog 2 R.card) → Finset V)
    (v : V) (j : Fin (Nat.clog 2 R.card)) : Finset V :=
  if (termIdx R v).testBit j.val = true then cuts j else (cuts j)ᶜ

def isolatingCell (R : Finset V) (cuts : Fin (Nat.clog 2 R.card) → Finset V)
    (v : V) : Finset V :=
  Finset.univ.filter (fun x => ∀ j, x ∈ bitSide R cuts v j)

@[simp] theorem mem_isolatingCell (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V) (v x : V) :
    x ∈ isolatingCell R cuts v ↔ ∀ j, x ∈ bitSide R cuts v j := by
  simp [isolatingCell]

theorem isolatingCells_disjoint (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V) :
    (R : Set V).PairwiseDisjoint (isolatingCell R cuts) := by
  intro v hv w hw hvw
  obtain ⟨j, hj, hne⟩ := Certificate.exists_bit_ne hv hw hvw
  have hd : Disjoint (bitSide R cuts v ⟨j, hj⟩) (bitSide R cuts w ⟨j, hj⟩) := by
    cases h1 : (termIdx R v).testBit j <;> cases h2 : (termIdx R w).testBit j <;>
      simp_all [bitSide, disjoint_compl_left, disjoint_compl_right]
  apply Finset.disjoint_left.mpr
  intro x hxv hxw
  exact Finset.disjoint_left.mp hd ((mem_isolatingCell _ _ _ _).mp hxv ⟨j, hj⟩)
    ((mem_isolatingCell _ _ _ _).mp hxw ⟨j, hj⟩)

theorem isolatingCells_size (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V) :
    (∑ v ∈ R, (isolatingCell R cuts v).card) ≤ Fintype.card V := by
  rw [← Finset.card_biUnion (isolatingCells_disjoint R cuts)]
  exact Finset.card_le_univ _

theorem bitSide_min (G : WeightedGraph V) (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V)
    (hcuts : ∀ j, IsMinTraceCut G R (bitClass R j.val true) (cuts j))
    (v : V) (j : Fin (Nat.clog 2 R.card)) :
    IsMinTraceCut G R (bitClass R j.val ((termIdx R v).testBit j.val))
      (bitSide R cuts v j) := by
  cases h : (termIdx R v).testBit j.val
  · simpa only [bitSide, h, Bool.false_eq_true, ite_false, bitClass_sdiff] using
      minTrace_compl G (hcuts j)
  · simpa only [bitSide, h, ite_true] using hcuts j

theorem terminal_mem_cell (G : WeightedGraph V) (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V)
    (hcuts : ∀ j, IsMinTraceCut G R (bitClass R j.val true) (cuts j))
    {v : V} (hv : v ∈ R) : v ∈ isolatingCell R cuts v := by
  apply (mem_isolatingCell _ _ _ _).mpr
  intro j
  have hm : v ∈ bitSide R cuts v j ∩ R := by
    rw [(bitSide_min G R cuts hcuts v j).1]
    exact mem_bitClass.mpr ⟨hv, rfl⟩
  exact (Finset.mem_inter.mp hm).1

theorem isolatingCell_trace (G : WeightedGraph V) (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V)
    (hcuts : ∀ j, IsMinTraceCut G R (bitClass R j.val true) (cuts j))
    {v : V} (hv : v ∈ R) : isolatingCell R cuts v ∩ R = {v} := by
  ext w
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hwP, hwR⟩
    by_contra hwv
    have hdisj := isolatingCells_disjoint R cuts hv hwR (Ne.symm hwv)
    exact Finset.disjoint_left.mp hdisj hwP (terminal_mem_cell G R cuts hcuts hwR)
  · rintro rfl
    exact ⟨terminal_mem_cell G R cuts hcuts hv, hv⟩

theorem canonical_iso_subset_cell (G : WeightedGraph V) (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V)
    (hcuts : ∀ j, IsMinTraceCut G R (bitClass R j.val true) (cuts j))
    {v : V} (hv : v ∈ R) {C : Finset V} (hC : IsCanonicalTraceCut G R {v} C) :
    C ⊆ isolatingCell R cuts v := by
  intro x hx
  apply (mem_isolatingCell _ _ _ _).mpr
  intro j
  have hsub : ({v} : Finset V) ⊆ bitClass R j.val ((termIdx R v).testBit j.val) :=
    Finset.singleton_subset_iff.mpr (mem_bitClass.mpr ⟨hv, rfl⟩)
  exact canonical_trace_subset G hsub hC (bitSide_min G R cuts hcuts v j) hx

theorem isolatingCell_proper (G : WeightedGraph V) (R : Finset V)
    (cuts : Fin (Nat.clog 2 R.card) → Finset V)
    (hcuts : ∀ j, IsMinTraceCut G R (bitClass R j.val true) (cuts j))
    (hR : 2 ≤ R.card) {v : V} (hv : v ∈ R) :
    isolatingCell R cuts v ≠ Finset.univ := by
  intro he
  have h := isolatingCell_trace G R cuts hcuts hv
  rw [he, Finset.univ_inter] at h
  have hc := congrArg Finset.card h
  simp only [Finset.card_singleton] at hc
  omega

end
end CutQueryComplexity.GHReduction
