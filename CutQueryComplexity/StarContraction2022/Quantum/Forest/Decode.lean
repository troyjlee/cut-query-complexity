import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! # Public count-one and bit-mask decoding

The decoder takes only finite answer data and a public eligible set. A count
other than one, a non-binary mask count, an out-of-range code, a loop, or an
ineligible endpoint is rejected. On honest counts it returns exactly the
unique element of the sampled row. No hidden graph is a constructor input.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest

noncomputable section
open Finset
open scoped Classical

variable {n width : ℕ}

def bitCode (width : ℕ) (v : Fin n) : Fin width → Bool :=
  fun j => v.val.testBit j.val

def bitMask (n width : ℕ) (j : Fin width) : Finset (Fin n) :=
  univ.filter fun v => bitCode width v j = true

@[simp] theorem mem_bitMask (j : Fin width) (v : Fin n) :
    v ∈ bitMask n width j ↔ bitCode width v j = true := by
  simp [bitMask]

/-- The width bound is public, including the empty-vertex case. -/
theorem bitCode_injective (hwidth : n ≤ 2 ^ width) :
    Function.Injective (bitCode (n := n) width) := by
  intro u v h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < width
  · exact congrFun h ⟨j, hj⟩
  · have hp : n ≤ 2 ^ j := hwidth.trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (not_lt.mp hj))
    rw [Nat.testBit_eq_false_of_lt (u.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (v.isLt.trans_le hp)]

/-- Exhaustive finite decoding is free computation in the query model. The
search ranges over public vertex labels, never over an unknown graph. -/
def decodeBits (n width : ℕ) (bits : Fin width → Bool) : Option (Fin n) :=
  if h : ∃ v : Fin n, bitCode width v = bits then some h.choose else none

theorem decodeBits_spec {bits : Fin width → Bool} {v : Fin n}
    (h : decodeBits n width bits = some v) : bitCode width v = bits := by
  unfold decodeBits at h
  split_ifs at h with hex
  · have he : hex.choose = v := Option.some.inj h
    exact he ▸ hex.choose_spec

@[simp] theorem decodeBits_code (hwidth : n ≤ 2 ^ width) (v : Fin n) :
    decodeBits n width (bitCode width v) = some v := by
  have hex : ∃ w : Fin n, bitCode width w = bitCode width v := ⟨v, rfl⟩
  unfold decodeBits
  rw [dif_pos hex]
  exact congrArg some (bitCode_injective hwidth hex.choose_spec)

theorem decodeBits_none_iff (bits : Fin width → Bool) :
    decodeBits n width bits = none ↔ ¬∃ v : Fin n, bitCode width v = bits := by
  unfold decodeBits
  split_ifs <;> simp_all

/-- Honest mask counts of one explicit row. All masks restrict the same row. -/
def maskCounts (N : Finset (Fin n)) : Fin width → ℕ :=
  fun j => (N ∩ bitMask n width j).card

@[simp] theorem maskCounts_singleton (v : Fin n) (j : Fin width) :
    maskCounts (width := width) {v} j = if bitCode width v j then 1 else 0 := by
  cases hb : bitCode width v j <;>
    simp [maskCounts, bitMask, hb, inter_filter, filter_singleton]

theorem singletonCounts_binary (v : Fin n) :
    ∀ j : Fin width, maskCounts {v} j ≤ 1 := by
  intro j
  rw [maskCounts_singleton]
  cases bitCode width v j <;> decide

theorem singletonCounts_code (v : Fin n) :
    (fun j : Fin width => decide (maskCounts {v} j = 1)) = bitCode width v := by
  funext j
  rw [maskCounts_singleton]
  cases bitCode width v j <;> decide

/-- Every check is on public data or observed integer answers. -/
def decodeRow (blue : Finset (Fin n)) (u : Fin n) (total : ℕ)
    (counts : Fin width → ℕ) : Option (Fin n) :=
  if total = 1 ∧ (∀ j, counts j ≤ 1) then
    match decodeBits n width (fun j => decide (counts j = 1)) with
    | none => none
    | some v => if v ∈ blue ∧ u ≠ v then some v else none
  else none

theorem decodeRow_spec (blue : Finset (Fin n)) (u v : Fin n) (total : ℕ)
    (counts : Fin width → ℕ) :
    decodeRow blue u total counts = some v ↔
      total = 1 ∧ (∀ j, counts j ≤ 1) ∧
        decodeBits n width (fun j => decide (counts j = 1)) = some v ∧
        v ∈ blue ∧ u ≠ v := by
  by_cases hg : total = 1 ∧ ∀ j, counts j ≤ 1
  · cases hd : decodeBits n width (fun j => decide (counts j = 1)) with
    | none => simp [decodeRow, hg, hd]
    | some w =>
        by_cases hw : w ∈ blue ∧ u ≠ w
        · simp only [decodeRow, if_pos hg, hd, if_pos hw, Option.some.injEq]
          constructor
          · intro he
            subst v
            exact ⟨hg.1, hg.2, rfl, hw.1, hw.2⟩
          · intro h
            exact h.2.2.1
        · simp only [decodeRow, if_pos hg, hd, if_neg hw, reduceCtorEq, false_iff,
            Option.some.injEq]
          rintro ⟨_, _, he, hv, huv⟩
          subst v
          exact hw ⟨hv, huv⟩
  · simp only [decodeRow, if_neg hg, reduceCtorEq, false_iff]
    intro h
    exact hg ⟨h.1, h.2.1⟩

/-- Malformed replies cannot bypass public endpoint checks. -/
theorem decodeRow_guard {blue : Finset (Fin n)} {u v : Fin n} {total : ℕ}
    {counts : Fin width → ℕ} (h : decodeRow blue u total counts = some v) :
    total = 1 ∧ v ∈ blue ∧ u ≠ v := by
  have hs := (decodeRow_spec blue u v total counts).mp h
  exact ⟨hs.1, hs.2.2.2.1, hs.2.2.2.2⟩

theorem decodeRow_singleton (hwidth : n ≤ 2 ^ width) (blue : Finset (Fin n))
    (u v : Fin n) (hv : v ∈ blue) (huv : u ≠ v) :
    decodeRow blue u 1 (maskCounts (width := width) {v}) = some v := by
  apply (decodeRow_spec blue u v 1 _).mpr
  refine ⟨rfl, singletonCounts_binary v, ?_, hv, huv⟩
  rw [singletonCounts_code, decodeBits_code hwidth]

/-- Exact count-one recovery, in both directions. The blue set is public;
the row N occurs only in this semantic theorem. -/
theorem decodeRow_honest (hwidth : n ≤ 2 ^ width) (blue N : Finset (Fin n))
    (u v : Fin n) (hN : N ⊆ blue) (hu : u ∉ blue) :
    decodeRow blue u N.card (maskCounts (width := width) N) = some v ↔ N = {v} := by
  constructor
  · intro h
    have hcard := (decodeRow_guard h).1
    obtain ⟨w, hw⟩ := card_eq_one.mp hcard
    have hwb : w ∈ blue := hN (by simp [hw])
    have huw : u ≠ w := by
      intro he
      subst u
      exact hu hwb
    have he := decodeRow_singleton hwidth blue u w hwb huw
    rw [hw, card_singleton] at h
    rw [he] at h
    have hwv := Option.some.inj h
    exact hw.trans (congrArg singleton hwv)
  · intro he
    have hv : v ∈ blue := hN (by simp [he])
    rw [he, card_singleton]
    apply decodeRow_singleton hwidth blue u v hv
    intro h
    subst u
    exact hu hv

@[simp] theorem decodeRow_empty (blue : Finset (Fin n)) (u : Fin n) :
    decodeRow blue u 0 (maskCounts (n := n) (width := width) ∅) = none := by
  simp [decodeRow]

/-- The proposed common logarithmic width is sufficient; this file does not
define or take ownership of the shared schedule. -/
theorem logarithmic_width (n : ℕ) : n ≤ 2 ^ (1 + Nat.clog 2 (n + 2)) := by
  exact (show n ≤ n + 2 by omega).trans
    ((Nat.le_pow_clog (by decide) (n + 2)).trans
      (Nat.pow_le_pow_right (by decide) (by omega)))

#print axioms bitCode_injective
#print axioms decodeBits_spec
#print axioms decodeBits_code
#print axioms decodeBits_none_iff
#print axioms singletonCounts_code
#print axioms decodeRow_spec
#print axioms decodeRow_guard
#print axioms decodeRow_singleton
#print axioms decodeRow_honest
#print axioms decodeRow_empty
#print axioms logarithmic_width

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest
