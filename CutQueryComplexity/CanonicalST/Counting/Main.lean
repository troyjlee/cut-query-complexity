import CutQueryComplexity.CanonicalST.Counting.Global
import CutQueryComplexity.CanonicalST.Extension

/-!
# Explicit small-cut counts and fixed canonical representatives

The public counting graph J is supported only on C and has minimum degree D
only at core vertices. The ambient parameter n is kept separate from |C|.
The canonical family depends only on C,K,s,t; the theorem applies to every
later learned core L containing J, without changing any representative.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Counting

noncomputable section
open Finset WeightedGraph AllPairsAudit
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

@[simp] theorem coreLabelings_empty (J : WeightedGraph V) (b : ℕ) :
    coreLabelings J ∅ b = {∅} := by
  simp [coreLabelings, Nat.cast_nonneg]

/-- The empty core has one labeling, independently of the ambient size. -/
theorem empty_core_count (J : WeightedGraph V) (b : ℕ) :
    (coreLabelings J ∅ b).card = 1 := by simp

/-- The constructed partition and joint-budget encoding discharge the count. -/
theorem coreLabelings_card_le (J : WeightedGraph V) (C : Finset V)
    (hJ : Unweighted J)
    (hsupp : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0)
    {D n b : ℕ} (hD : 2 ≤ D) (hCn : C.card ≤ n) (hbn : b ≤ n)
    (hdeg : ∀ v ∈ C, (D : ℝ) ≤ J.degree v) :
    (coreLabelings J C b).card ≤ (2 * n) ^ countExponent C.card b D := by
  by_cases hC : C = ∅
  · subst C
    rw [empty_core_count]
    by_cases hn : n = 0
    · have hb : b = 0 := by omega
      simp [hn, hb, countExponent]
    · simpa only [one_pow, card_empty] using
        (pow_le_pow_left' (by omega : (1 : ℕ) ≤ 2 * n) (countExponent 0 b D))
  · have hne := nonempty_iff_ne_empty.mpr hC
    have hn : 1 ≤ n := hne.card_pos.trans_le hCn
    obtain ⟨P, hconn, hparts, _, _⟩ := exists_corePartition J C hne hJ hsupp hD hdeg
    exact partitionLabelings_card_le J hJ P (by omega) hn hCn hbn hconn hparts

/-- **Paper 02, small-cut count**, with an explicit natural exponent. Both a
labeling and its complement are counted. No connectivity promise is imposed. -/
theorem smallCutLabelings_card_le (J : WeightedGraph V) (C : Finset V)
    (hJ : Unweighted J)
    (hsupp : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0)
    {D n b : ℕ} (hD : 2 ≤ D) (hCn : C.card ≤ n) (hbn : b ≤ n)
    (hdeg : ∀ v ∈ C, (D : ℝ) ≤ J.degree v) :
    (C.powerset.filter (fun x => J.cut x ≤ (b : ℝ))).card ≤
      (2 * n) ^ ⌈32 * ((C.card : ℝ) + (b : ℝ)) / (D : ℝ)⌉₊ := by
  exact coreLabelings_card_le J C hJ hsupp hD hCn hbn hdeg

/-- The public, fixed extension rule makes restriction injective on its family. -/
theorem canonicalTrace_injective (C : Finset V) (K : WeightedGraph V)
    {s t : V} (hst : s ≠ t) :
    Set.InjOn (fun S : Finset V => S ∩ C) (canonicalFamily C K s t) := by
  intro S hS T hT he
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hS
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hT
  change canonicalExtension C K s t x ∩ C = canonicalExtension C K s t y ∩ C at he
  rw [canonicalExtension_trace C K hst (mem_filter.mp hx).2,
    canonicalExtension_trace C K hst (mem_filter.mp hy).2] at he
  rw [he]

/-- Every canonical shore's trace costs at most its learned cut. The later L
appears here in correctness, never in the choice of canonical representative. -/
theorem canonicalTrace_cut_le (C : Finset V) (K J L : WeightedGraph V)
    {s t : V} (hst : s ≠ t)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) (hJL : J.IsSubgraph L)
    {S : Finset V} (hS : S ∈ canonicalFamily C K s t) :
    J.cut (S ∩ C) ≤ (K.add L).cut S := by
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hS
  have hx' := (mem_filter.mp hx).2
  rw [canonicalExtension_trace C K hst hx', canonicalExtension_cut_add C K L hst hx' hL]
  exact (hJL.cut_le x).trans (le_add_of_nonneg_left (K.cut_nonneg _))

/-- **Paper 02, canonical-family count.** Quantification over the future public
learned core is outside the fixed family construction. -/
theorem canonicalFamily_card_le (C : Finset V) (K J : WeightedGraph V)
    {s t : V} (hst : s ≠ t) (hJ : Unweighted J)
    (hsupp : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0)
    {D n b : ℕ} (hD : 2 ≤ D) (hCn : C.card ≤ n) (hbn : b ≤ n)
    (hdeg : ∀ v ∈ C, (D : ℝ) ≤ J.degree v) :
    ∀ L : WeightedGraph V,
      (∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) → J.IsSubgraph L →
      ((canonicalFamily C K s t).filter (fun S => (K.add L).cut S ≤ (b : ℝ))).card ≤
        (2 * n) ^ ⌈32 * ((C.card : ℝ) + (b : ℝ)) / (D : ℝ)⌉₊ := by
  intro L hL hJL
  apply le_trans ?_ (coreLabelings_card_le J C hJ hsupp hD hCn hbn hdeg)
  apply card_le_card_of_injOn (fun S : Finset V => S ∩ C)
  · intro S hS
    obtain ⟨hS, hc⟩ := mem_filter.mp hS
    exact (mem_coreLabelings J C (S ∩ C) b).mpr
      ⟨inter_subset_right, (canonicalTrace_cut_le C K J L hst hL hJL hS).trans hc⟩
  · intro S hS T hT he
    exact canonicalTrace_injective C K hst (mem_filter.mp hS).1 (mem_filter.mp hT).1 he

/-- Ambient-vertex specialization of the same bound, retaining |C| explicitly. -/
theorem canonicalFamily_ambient_card_le (C : Finset V) (K J : WeightedGraph V)
    {s t : V} (hst : s ≠ t) (hJ : Unweighted J)
    (hsupp : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0)
    {D b : ℕ} (hD : 2 ≤ D) (hbn : b ≤ Fintype.card V)
    (hdeg : ∀ v ∈ C, (D : ℝ) ≤ J.degree v) :
    ∀ L : WeightedGraph V,
      (∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) → J.IsSubgraph L →
      ((canonicalFamily C K s t).filter (fun S => (K.add L).cut S ≤ (b : ℝ))).card ≤
        (2 * Fintype.card V) ^ ⌈32 * ((C.card : ℝ) + (b : ℝ)) / (D : ℝ)⌉₊ :=
  canonicalFamily_card_le C K J hst hJ hsupp hD (card_le_univ C) hbn hdeg

/-- When both the core and budget fit in n, the exponent is at most ceil(64n/D). -/
theorem countExponent_le_ambient {N b n D : ℕ} (hN : N ≤ n) (hb : b ≤ n) :
    countExponent N b D ≤ ⌈64 * (n : ℝ) / (D : ℝ)⌉₊ := by
  unfold countExponent
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg D)
  have hNr : (N : ℝ) ≤ n := by exact_mod_cast hN
  have hbr : (b : ℝ) ≤ n := by exact_mod_cast hb
  linarith

/-- The source's purely ambient canonical bound, with explicit constant 64. -/
theorem canonicalFamily_ambientPower_card_le (C : Finset V) (K J : WeightedGraph V)
    {s t : V} (hst : s ≠ t) (hJ : Unweighted J)
    (hsupp : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0)
    {D b : ℕ} (hD : 2 ≤ D) (hbn : b ≤ Fintype.card V)
    (hdeg : ∀ v ∈ C, (D : ℝ) ≤ J.degree v) :
    ∀ L : WeightedGraph V,
      (∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) → J.IsSubgraph L →
      ((canonicalFamily C K s t).filter (fun S => (K.add L).cut S ≤ (b : ℝ))).card ≤
        (2 * Fintype.card V) ^ ⌈64 * (Fintype.card V : ℝ) / (D : ℝ)⌉₊ := by
  intro L hL hJL
  apply (canonicalFamily_ambient_card_le C K J hst hJ hsupp hD hbn hdeg L hL hJL).trans
  have hn : 1 ≤ Fintype.card V := by simpa using (card_le_univ ({s} : Finset V))
  exact pow_le_pow_right' (by omega : 1 ≤ 2 * Fintype.card V)
    (countExponent_le_ambient (card_le_univ C) hbn)

end
end CutQueryComplexity.CanonicalST.Counting

#print axioms CutQueryComplexity.CanonicalST.Counting.empty_core_count
#print axioms CutQueryComplexity.CanonicalST.Counting.smallCutLabelings_card_le
#print axioms CutQueryComplexity.CanonicalST.Counting.canonicalTrace_injective
#print axioms CutQueryComplexity.CanonicalST.Counting.canonicalTrace_cut_le
#print axioms CutQueryComplexity.CanonicalST.Counting.canonicalFamily_card_le
#print axioms CutQueryComplexity.CanonicalST.Counting.canonicalFamily_ambient_card_le
#print axioms CutQueryComplexity.CanonicalST.Counting.countExponent_le_ambient
#print axioms CutQueryComplexity.CanonicalST.Counting.canonicalFamily_ambientPower_card_le
