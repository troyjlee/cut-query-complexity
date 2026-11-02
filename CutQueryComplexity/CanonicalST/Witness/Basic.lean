import CutQueryComplexity.CanonicalST.Extension
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Public finite padded witnesses

A possible crossing pair is oriented from the shore to its complement, so
each unordered crossing pair occurs exactly once. Padding may contain nonedges.
The potential averages over pairs `(shore, padding)`, retaining the binomial
multiplicity of each shore. Every definition uses only explicitly learned data.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Witness

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def possiblePairs (S : Finset V) : Finset (V × V) := S ×ˢ Sᶜ

@[simp] theorem mem_possiblePairs (S : Finset V) (u v : V) :
    (u, v) ∈ possiblePairs S ↔ u ∈ S ∧ v ∉ S := by
  simp [possiblePairs]

theorem possiblePairs_card (S : Finset V) :
    (possiblePairs S).card = S.card * Sᶜ.card := by simp [possiblePairs]

theorem possiblePairs_card_ge {S : Finset V} {s t : V}
    (ht : t ∈ S) (hs : s ∉ S) :
    Fintype.card V - 1 ≤ (possiblePairs S).card := by
  have ha : 1 ≤ S.card := card_pos.mpr ⟨t, ht⟩
  have hb : 1 ≤ Sᶜ.card := card_pos.mpr ⟨s, mem_compl.mpr hs⟩
  have hab := card_add_card_compl S
  have hn : 1 ≤ Fintype.card V := by omega
  have hp := Nat.mul_le_mul_left (S.card - 1) hb
  rw [possiblePairs_card]
  nlinarith [Nat.sub_add_cancel ha, Nat.sub_add_cancel hn]

def knownPairs (H : WeightedGraph V) (S : Finset V) : Finset (V × V) :=
  (possiblePairs S).filter fun e => 0 < H.w e.1 e.2

@[simp] theorem mem_knownPairs (H : WeightedGraph V) (S : Finset V) (u v : V) :
    (u, v) ∈ knownPairs H S ↔ u ∈ S ∧ v ∉ S ∧ 0 < H.w u v := by
  simp [knownPairs, and_assoc]

theorem knownPairs_subset (H : WeightedGraph V) (S : Finset V) :
    knownPairs H S ⊆ possiblePairs S := filter_subset _ _

theorem knownPairs_card_eq_cut {H : WeightedGraph V}
    (hH : AllPairsAudit.Unweighted H) (S : Finset V) :
    ((knownPairs H S).card : ℝ) = H.cut S := by
  calc
    ((knownPairs H S).card : ℝ) =
        ∑ e ∈ possiblePairs S, if 0 < H.w e.1 e.2 then (1 : ℝ) else 0 := by
          simp only [knownPairs, card_filter, Nat.cast_sum, Nat.cast_ite,
            Nat.cast_one, Nat.cast_zero]
    _ = ∑ e ∈ possiblePairs S, H.w e.1 e.2 := by
          apply sum_congr rfl
          intro e _
          rcases hH e.1 e.2 with h | h <;> simp [h]
    _ = H.cut S := by simp [possiblePairs, WeightedGraph.cut, sum_product]

def paddingFamily (H : WeightedGraph V) (S : Finset V) (b : ℕ) :
    Finset (Finset (V × V)) :=
  ((possiblePairs S).powersetCard b).filter fun Y => knownPairs H S ⊆ Y

@[simp] theorem mem_paddingFamily (H : WeightedGraph V) (S : Finset V)
    (b : ℕ) (Y : Finset (V × V)) :
    Y ∈ paddingFamily H S b ↔
      Y ⊆ possiblePairs S ∧ Y.card = b ∧ knownPairs H S ⊆ Y := by
  simp [paddingFamily, and_assoc]

/-- The exact conditional multiplicity, including padding by nonedges. -/
theorem paddingFamily_card (H : WeightedGraph V) (S : Finset V) {b : ℕ}
    (hb : (knownPairs H S).card ≤ b) :
    (paddingFamily H S b).card =
      ((possiblePairs S).card - (knownPairs H S).card).choose
        (b - (knownPairs H S).card) :=
  card_filter_powersetCard_subset _ _ _ (knownPairs_subset H S) hb

theorem paddingFamily_nonempty_iff (H : WeightedGraph V) (S : Finset V) {b : ℕ}
    (hb : b ≤ (possiblePairs S).card) :
    (paddingFamily H S b).Nonempty ↔ (knownPairs H S).card ≤ b := by
  constructor
  · rintro ⟨Y, hY⟩
    obtain ⟨_, hcard, hsub⟩ := (mem_paddingFamily _ _ _ _).mp hY
    exact hcard ▸ card_le_card hsub
  · intro hk
    have hsize : b - (knownPairs H S).card ≤
        (possiblePairs S \ knownPairs H S).card := by
      rw [card_sdiff_of_subset (knownPairs_subset H S)]
      omega
    obtain ⟨Z, hZ, hZcard⟩ := exists_subset_card_eq hsize
    rw [paddingFamily, filter_powersetCard_subset _ _ _ (knownPairs_subset H S) hk]
    exact ⟨Z ∪ knownPairs H S, mem_image.mpr
      ⟨Z, mem_powersetCard.mpr ⟨hZ, hZcard⟩, rfl⟩⟩

def paddedWitnesses (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) :
    Finset (Finset V × Finset (V × V)) :=
  A.biUnion fun S => (paddingFamily H S b).image fun Y => (S, Y)

@[simp] theorem mem_paddedWitnesses (A : Finset (Finset V)) (H : WeightedGraph V)
    (b : ℕ) (S : Finset V) (Y : Finset (V × V)) :
    (S, Y) ∈ paddedWitnesses A H b ↔ S ∈ A ∧ Y ∈ paddingFamily H S b := by
  simp [paddedWitnesses]

theorem paddedWitnesses_nonempty_iff (A : Finset (Finset V)) (H : WeightedGraph V)
    {b : ℕ} (hb : ∀ S ∈ A, b ≤ (possiblePairs S).card) :
    (paddedWitnesses A H b).Nonempty ↔ ∃ S ∈ A, (knownPairs H S).card ≤ b := by
  constructor
  · rintro ⟨⟨S, Y⟩, hw⟩
    obtain ⟨hS, hY⟩ := (mem_paddedWitnesses _ _ _ _ _).mp hw
    exact ⟨S, hS, (paddingFamily_nonempty_iff H S (hb S hS)).mp ⟨Y, hY⟩⟩
  · rintro ⟨S, hS, hk⟩
    obtain ⟨Y, hY⟩ := (paddingFamily_nonempty_iff H S (hb S hS)).mpr hk
    exact ⟨(S, Y), (mem_paddedWitnesses _ _ _ _ _).mpr ⟨hS, hY⟩⟩

theorem paddedWitnesses_cut_le (A : Finset (Finset V)) {H : WeightedGraph V}
    (hH : AllPairsAudit.Unweighted H) {b : ℕ}
    {w : Finset V × Finset (V × V)} (hw : w ∈ paddedWitnesses A H b) :
    H.cut w.1 ≤ b := by
  obtain ⟨_, hY⟩ := (mem_paddedWitnesses _ _ _ _ _).mp hw
  obtain ⟨_, hcard, hsub⟩ := (mem_paddingFamily _ _ _ _).mp hY
  rw [← knownPairs_card_eq_cut hH]
  exact_mod_cast (hcard ▸ card_le_card hsub)

/-- The representative family is fixed by C, K, and the terminals. Learned
core edges L affect only membership and multiplicity of padded witnesses. -/
def canonicalWitnesses (C : Finset V) (K : WeightedGraph V) (s t : V)
    (L : WeightedGraph V) (b : ℕ) : Finset (Finset V × Finset (V × V)) :=
  paddedWitnesses (canonicalFamily C K s t) (K.add L) b

theorem canonicalWitnesses_nonempty_iff (C : Finset V) (K L : WeightedGraph V)
    {s t : V} (hst : s ≠ t) (hH : AllPairsAudit.Unweighted (K.add L))
    {b : ℕ} (hb : b ≤ Fintype.card V - 1)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) :
    (canonicalWitnesses C K s t L b).Nonempty ↔
      ∃ S : Finset V, t ∈ S ∧ s ∉ S ∧ (K.add L).cut S ≤ b := by
  rw [canonicalWitnesses, paddedWitnesses_nonempty_iff _ _ (fun S hS =>
    hb.trans (possiblePairs_card_ge
      (canonicalFamily_terminal C K hst hS).1
      (canonicalFamily_terminal C K hst hS).2))]
  constructor
  · rintro ⟨S, hS, hc⟩
    obtain ⟨ht, hs⟩ := canonicalFamily_terminal C K hst hS
    refine ⟨S, ht, hs, ?_⟩
    rw [← knownPairs_card_eq_cut hH]
    exact_mod_cast hc
  · rintro ⟨S, ht, hs, hc⟩
    let T := canonicalExtension C K s t (S ∩ C)
    have hT : T ∈ canonicalFamily C K s t :=
      canonicalExtension_mem_family C K (admissibleTrace_of_shore C ht hs)
    refine ⟨T, hT, ?_⟩
    have hcut : (K.add L).cut T ≤ b :=
      (canonicalExtension_cut_le C K L hst hL ht hs).trans hc
    rw [← knownPairs_card_eq_cut hH] at hcut
    exact_mod_cast hcut

/-- Emptiness is an actual minimum-cut threshold test; no oracle or promised
minimum cut is stored in the public witness data. -/
theorem canonicalWitnesses_empty_iff (C : Finset V) (K L : WeightedGraph V)
    {s t : V} (hst : s ≠ t) (hH : AllPairsAudit.Unweighted (K.add L))
    {b : ℕ} (hb : b ≤ Fintype.card V - 1)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) :
    canonicalWitnesses C K s t L b = ∅ ↔
      ∀ S : Finset V, t ∈ S → s ∉ S → (b + 1 : ℕ) ≤ (K.add L).cut S := by
  rw [← not_nonempty_iff_eq_empty, canonicalWitnesses_nonempty_iff C K L hst hH hb hL]
  push_neg
  constructor
  · intro h S ht hs
    have hc := h S ht hs
    rw [← knownPairs_card_eq_cut hH] at hc ⊢
    have hn : b < (knownPairs (K.add L) S).card := by exact_mod_cast hc
    exact_mod_cast (Nat.succ_le_of_lt hn)
  · intro h S ht hs
    have hc := h S ht hs
    have hbR : (b : ℝ) < (b + 1 : ℕ) := by push_cast; linarith
    exact hbR.trans_le hc

def potential (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) (v : V) : ℚ :=
  (((paddedWitnesses A H b).filter fun w => v ∈ w.1).card : ℚ) /
    (paddedWitnesses A H b).card

theorem potential_nonneg (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) (v : V) :
    0 ≤ potential A H b v := by unfold potential; positivity

theorem potential_le_one (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) (v : V) :
    potential A H b v ≤ 1 := by
  by_cases hz : (paddedWitnesses A H b).card = 0
  · simp [potential, hz]
  · have hp : (0 : ℚ) < (paddedWitnesses A H b).card := by
      exact_mod_cast (Nat.pos_of_ne_zero hz)
    rw [potential, div_le_one hp]
    exact_mod_cast (card_filter_le (paddedWitnesses A H b) fun w => v ∈ w.1)

theorem potential_source (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) (s : V)
    (hs : ∀ S ∈ A, s ∉ S) : potential A H b s = 0 := by
  have he : (paddedWitnesses A H b).filter (fun w => s ∈ w.1) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro w hw
    exact hs w.1 ((mem_paddedWitnesses _ _ _ _ _).mp hw).1
  simp [potential, he]

theorem potential_sink (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) (t : V)
    (ht : ∀ S ∈ A, t ∈ S) (hne : (paddedWitnesses A H b).Nonempty) :
    potential A H b t = 1 := by
  have he : (paddedWitnesses A H b).filter (fun w => t ∈ w.1) =
      paddedWitnesses A H b := by
    apply filter_eq_self.mpr
    intro w hw
    exact ht w.1 ((mem_paddedWitnesses _ _ _ _ _).mp hw).1
  have hc : ((paddedWitnesses A H b).card : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (card_pos.mpr hne))
  simp [potential, he, hc]

theorem canonical_potential_terminals (C : Finset V) (K L : WeightedGraph V)
    {s t : V} (hst : s ≠ t) {b : ℕ}
    (hne : (canonicalWitnesses C K s t L b).Nonempty) :
    potential (canonicalFamily C K s t) (K.add L) b s = 0 ∧
      potential (canonicalFamily C K s t) (K.add L) b t = 1 := by
  exact ⟨potential_source _ _ _ _ (fun S hS => (canonicalFamily_terminal C K hst hS).2),
    potential_sink _ _ _ _ (fun S hS => (canonicalFamily_terminal C K hst hS).1) hne⟩

end
end CutQueryComplexity.CanonicalST.Witness

#print axioms CutQueryComplexity.CanonicalST.Witness.possiblePairs_card_ge
#print axioms CutQueryComplexity.CanonicalST.Witness.knownPairs_card_eq_cut
#print axioms CutQueryComplexity.CanonicalST.Witness.paddingFamily_card
#print axioms CutQueryComplexity.CanonicalST.Witness.paddingFamily_nonempty_iff
#print axioms CutQueryComplexity.CanonicalST.Witness.canonicalWitnesses_nonempty_iff
#print axioms CutQueryComplexity.CanonicalST.Witness.canonicalWitnesses_empty_iff
#print axioms CutQueryComplexity.CanonicalST.Witness.potential_le_one
#print axioms CutQueryComplexity.CanonicalST.Witness.canonical_potential_terminals
