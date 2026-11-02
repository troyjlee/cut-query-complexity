import CutQueryComplexity.CanonicalST.Witness.Basic
import CutQueryComplexity.CanonicalST.Counting.Main
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Log

/-!
# Exact witness multiplicities and the padding contribution to the count

These are finite counting statements about the explicit learned graph. The
canonical shore estimate is supplied by the separate Counting package; this
module proves the additional padding factor and does not assume a witness
count or a phase-progress estimate.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Witness

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem paddingFamily_empty_of_lt (H : WeightedGraph V) (S : Finset V) {b : ℕ}
    (hb : b < (knownPairs H S).card) : paddingFamily H S b = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro Y hY
  obtain ⟨_, hc, hs⟩ := (mem_paddingFamily _ _ _ _).mp hY
  have hle : (knownPairs H S).card ≤ b := hc ▸ card_le_card hs
  omega

def multiplicity (H : WeightedGraph V) (S : Finset V) (b : ℕ) : ℕ :=
  if (knownPairs H S).card ≤ b then
    ((possiblePairs S).card - (knownPairs H S).card).choose (b - (knownPairs H S).card)
  else 0

theorem paddingFamily_card_eq_multiplicity (H : WeightedGraph V) (S : Finset V) (b : ℕ) :
    (paddingFamily H S b).card = multiplicity H S b := by
  by_cases hb : (knownPairs H S).card ≤ b
  · simpa only [multiplicity, hb, ↓reduceIte] using paddingFamily_card H S hb
  · simp [multiplicity, hb, paddingFamily_empty_of_lt H S (b := b) (by omega)]

theorem paddedWitnesses_card (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) :
    (paddedWitnesses A H b).card = ∑ S ∈ A, (paddingFamily H S b).card := by
  unfold paddedWitnesses
  rw [card_biUnion]
  · apply sum_congr rfl
    intro S _
    exact card_image_of_injective _ (fun Y Z h => (Prod.mk.inj h).2)
  · intro S _ T _ hST
    apply disjoint_left.mpr
    intro w hwS hwT
    obtain ⟨Y, _, heS⟩ := mem_image.mp hwS
    obtain ⟨Z, _, heT⟩ := mem_image.mp hwT
    exact hST (congrArg Prod.fst (heS.trans heT.symm))

theorem paddedWitnesses_card_eq_sum (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) :
    (paddedWitnesses A H b).card = ∑ S ∈ A, multiplicity H S b := by
  simp only [paddedWitnesses_card, paddingFamily_card_eq_multiplicity]

theorem paddedWitnesses_filter_vertex (A : Finset (Finset V)) (H : WeightedGraph V)
    (b : ℕ) (v : V) :
    (paddedWitnesses A H b).filter (fun w => v ∈ w.1) =
      paddedWitnesses (A.filter fun S => v ∈ S) H b := by
  ext ⟨S, Y⟩
  simp only [mem_filter, mem_paddedWitnesses]
  tauto

/-- Exact rational marginals weight each shore by its actual number of
possible padding sets. There is no uniform-shore replacement. -/
theorem potential_eq_weighted_sum (A : Finset (Finset V)) (H : WeightedGraph V)
    (b : ℕ) (v : V) :
    potential A H b v =
      ((∑ S ∈ A, if v ∈ S then multiplicity H S b else 0 : ℕ) : ℚ) /
        ((∑ S ∈ A, multiplicity H S b : ℕ) : ℚ) := by
  rw [potential, paddedWitnesses_filter_vertex, paddedWitnesses_card_eq_sum,
    paddedWitnesses_card_eq_sum, sum_filter]

def lowShores (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) : Finset (Finset V) :=
  A.filter fun S => (knownPairs H S).card ≤ b

theorem paddedWitnesses_restrict_low (A : Finset (Finset V)) (H : WeightedGraph V) (b : ℕ) :
    paddedWitnesses A H b = paddedWitnesses (lowShores A H b) H b := by
  ext ⟨S, Y⟩
  simp only [mem_paddedWitnesses, lowShores, mem_filter]
  constructor
  · rintro ⟨hS, hY⟩
    obtain ⟨_, hc, hs⟩ := (mem_paddingFamily _ _ _ _).mp hY
    exact ⟨⟨hS, hc ▸ card_le_card hs⟩, hY⟩
  · exact fun h => ⟨h.1.1, h.2⟩

theorem lowShores_eq_filter_cut (A : Finset (Finset V)) {H : WeightedGraph V}
    (hH : AllPairsAudit.Unweighted H) (b : ℕ) :
    lowShores A H b = A.filter fun S => H.cut S ≤ b := by
  ext S
  simp only [lowShores, mem_filter]
  rw [← knownPairs_card_eq_cut hH]
  norm_cast

theorem possiblePairs_card_le (S : Finset V) {n : ℕ} (hn : Fintype.card V ≤ n) :
    (possiblePairs S).card ≤ n * n := by
  rw [possiblePairs_card]
  exact Nat.mul_le_mul ((card_le_univ _).trans hn) ((card_le_univ _).trans hn)

theorem paddingFamily_card_le_pow (H : WeightedGraph V) (S : Finset V)
    {b k n : ℕ} (hn : Fintype.card V ≤ n) (hnpos : 1 ≤ n)
    (hk : b - (knownPairs H S).card ≤ k) :
    (paddingFamily H S b).card ≤ n ^ (2 * k) := by
  by_cases hb : (knownPairs H S).card ≤ b
  · rw [paddingFamily_card H S hb]
    calc
      ((possiblePairs S).card - (knownPairs H S).card).choose
          (b - (knownPairs H S).card) ≤
          ((possiblePairs S).card - (knownPairs H S).card) ^ (b - (knownPairs H S).card) :=
            Nat.choose_le_pow _ _
      _ ≤ (n * n) ^ (b - (knownPairs H S).card) :=
          Nat.pow_le_pow_left ((Nat.sub_le _ _).trans (possiblePairs_card_le S hn)) _
      _ ≤ (n * n) ^ k := Nat.pow_le_pow_right (by nlinarith) hk
      _ = n ^ (2 * k) := by rw [← sq, pow_mul]
  · simp [paddingFamily_empty_of_lt H S (b := b) (by omega)]

/-- The entire padding contribution is at most n^(2k), per eligible shore. -/
theorem paddedWitnesses_card_le (A : Finset (Finset V)) (H : WeightedGraph V)
    {b k n : ℕ} (hn : Fintype.card V ≤ n) (hnpos : 1 ≤ n)
    (hk : ∀ S ∈ lowShores A H b, b - (knownPairs H S).card ≤ k) :
    (paddedWitnesses A H b).card ≤ (lowShores A H b).card * n ^ (2 * k) := by
  rw [paddedWitnesses_restrict_low, paddedWitnesses_card]
  calc
    ∑ S ∈ lowShores A H b, (paddingFamily H S b).card ≤
        ∑ _S ∈ lowShores A H b, n ^ (2 * k) :=
      sum_le_sum fun S hS => paddingFamily_card_le_pow H S hn hnpos (hk S hS)
    _ = _ := by simp

/-- The strict padding deficit follows from the phase's integer parameters. -/
theorem phase_padding_deficit {f k h : ℕ} (hk : 1 ≤ k) (hkf : k ≤ f)
    (hh : f - k ≤ h) : (f - k / 2 - 1) - h < k := by omega

theorem phase_paddedWitnesses_card_le (A : Finset (Finset V)) (H : WeightedGraph V)
    {f k n : ℕ} (hn : Fintype.card V ≤ n) (hnpos : 1 ≤ n)
    (hk : 1 ≤ k) (hkf : k ≤ f)
    (hcut : ∀ S ∈ A, f - k ≤ (knownPairs H S).card) :
    (paddedWitnesses A H (f - k / 2 - 1)).card ≤
      (lowShores A H (f - k / 2 - 1)).card * n ^ (2 * k) := by
  apply paddedWitnesses_card_le A H hn hnpos
  intro S hS
  exact (phase_padding_deficit hk hkf (hcut S (mem_filter.mp hS).1)).le

/-- Public exponent after combining genuine canonical counting and padding. -/
def phaseCountExponent (n D k : ℕ) : ℕ := ⌈64 * (n : ℝ) / (D : ℝ)⌉₊ + 2 * k

def phaseCountBits (n D k : ℕ) : ℕ := phaseCountExponent n D k * Nat.clog 2 (2 * n)

/-- The actual canonical padded family has the claimed ambient bound. The
canonical count is proved by Counting.Main; only the phase's ordinary lower
cut invariant is an input. -/
theorem phase_canonicalWitnesses_card_le (C : Finset V) (K J L : WeightedGraph V)
    {s t : V} (hst : s ≠ t) (hJ : AllPairsAudit.Unweighted J)
    (hJsupp : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) (hJL : J.IsSubgraph L)
    (hH : AllPairsAudit.Unweighted (K.add L))
    {D f k : ℕ} (hD : 2 ≤ D) (hk : 1 ≤ k) (hkf : k ≤ f)
    (hfn : f ≤ Fintype.card V - 1)
    (hdeg : ∀ v ∈ C, (D : ℝ) ≤ J.degree v)
    (hcut : ∀ S : Finset V, t ∈ S → s ∉ S → (f - k : ℕ) ≤ (K.add L).cut S) :
    (canonicalWitnesses C K s t L (f - k / 2 - 1)).card ≤
      (2 * Fintype.card V) ^ phaseCountExponent (Fintype.card V) D k := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hb : f - k / 2 - 1 ≤ Fintype.card V := by omega
  have hshore := Counting.canonicalFamily_ambientPower_card_le C K J hst hJ hJsupp
    hD hb hdeg L hL hJL
  have hknown : ∀ S ∈ canonicalFamily C K s t,
      f - k ≤ (knownPairs (K.add L) S).card := by
    intro S hS
    obtain ⟨ht, hs⟩ := canonicalFamily_terminal C K hst hS
    have h := hcut S ht hs
    rw [← knownPairs_card_eq_cut hH] at h
    exact_mod_cast h
  have hpad := phase_paddedWitnesses_card_le (canonicalFamily C K s t) (K.add L)
    (le_refl (Fintype.card V)) hn hk hkf hknown
  rw [lowShores_eq_filter_cut _ hH] at hpad
  change (paddedWitnesses (canonicalFamily C K s t) (K.add L) _).card ≤ _
  calc
    _ ≤ ((canonicalFamily C K s t).filter
        (fun S => (K.add L).cut S ≤ (f - k / 2 - 1 : ℕ))).card *
          (Fintype.card V) ^ (2 * k) := hpad
    _ ≤ (2 * Fintype.card V) ^ ⌈64 * (Fintype.card V : ℝ) / (D : ℝ)⌉₊ *
          (2 * Fintype.card V) ^ (2 * k) :=
      Nat.mul_le_mul hshore (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [phaseCountExponent, pow_add]

/-- A finite binary bit bound for fixed, publicly chosen phase fuel. -/
theorem phase_canonicalWitnesses_card_le_two_pow (C : Finset V) (K J L : WeightedGraph V)
    {s t : V} (hst : s ≠ t) (hJ : AllPairsAudit.Unweighted J)
    (hJsupp : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0)
    (hL : ∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) (hJL : J.IsSubgraph L)
    (hH : AllPairsAudit.Unweighted (K.add L))
    {D f k : ℕ} (hD : 2 ≤ D) (hk : 1 ≤ k) (hkf : k ≤ f)
    (hfn : f ≤ Fintype.card V - 1)
    (hdeg : ∀ v ∈ C, (D : ℝ) ≤ J.degree v)
    (hcut : ∀ S : Finset V, t ∈ S → s ∉ S → (f - k : ℕ) ≤ (K.add L).cut S) :
    (canonicalWitnesses C K s t L (f - k / 2 - 1)).card ≤
      2 ^ phaseCountBits (Fintype.card V) D k := by
  apply (phase_canonicalWitnesses_card_le C K J L hst hJ hJsupp hL hJL hH
    hD hk hkf hfn hdeg hcut).trans
  calc
    (2 * Fintype.card V) ^ phaseCountExponent (Fintype.card V) D k ≤
        (2 ^ Nat.clog 2 (2 * Fintype.card V)) ^ phaseCountExponent (Fintype.card V) D k :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = _ := by rw [← pow_mul]; simp only [phaseCountBits, Nat.mul_comm]

end
end CutQueryComplexity.CanonicalST.Witness

#print axioms CutQueryComplexity.CanonicalST.Witness.paddingFamily_card_eq_multiplicity
#print axioms CutQueryComplexity.CanonicalST.Witness.paddedWitnesses_card_eq_sum
#print axioms CutQueryComplexity.CanonicalST.Witness.potential_eq_weighted_sum
#print axioms CutQueryComplexity.CanonicalST.Witness.paddingFamily_card_le_pow
#print axioms CutQueryComplexity.CanonicalST.Witness.phase_paddedWitnesses_card_le

#print axioms CutQueryComplexity.CanonicalST.Witness.phase_canonicalWitnesses_card_le
#print axioms CutQueryComplexity.CanonicalST.Witness.phase_canonicalWitnesses_card_le_two_pow
