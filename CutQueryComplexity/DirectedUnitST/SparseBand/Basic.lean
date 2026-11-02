import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! # Public finite data for uniform sparse bands

All data here depend on `n,k` and public potentials, never on graph capacities.
The finite checker uses the expanded integer band; its soundness and existence
are proved in the subsequent modules.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST

namespace SparseBand

/-- Each unordered pair has the public orientation from its smaller endpoint. -/
abbrev Pair (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

abbrev Offset (k : ℕ) := Fin (2 * k + 1)
abbrev OffsetTable (n k : ℕ) := Pair n → Offset k
abbrev GridPoint (n k : ℕ) := Fin n → Fin (8 * n * k + 1)

def offsetInt {k : ℕ} (a : Offset k) : ℤ := (a.val : ℤ) - k

def offsetRat {n k : ℕ} (c : OffsetTable n k) (e : Pair n) : ℚ :=
  (offsetInt (c e) : ℚ) / k

def bandBudget (n k : ℕ) : ℕ :=
  (6 * (n.choose 2) + k - 1) / k + 2 * n * Nat.clog 2 (8 * n * k + 1) + 1

def GridActive {n k : ℕ} (c : OffsetTable n k) (g : GridPoint n k)
    (e : Pair n) : Prop :=
  |(g e.val.1 : ℤ) - (g e.val.2 : ℤ) - 4 * offsetInt (c e)| ≤ 8

instance {n k : ℕ} (c : OffsetTable n k) (g : GridPoint n k) (e : Pair n) :
    Decidable (GridActive c g e) := inferInstanceAs (Decidable (_ ≤ (8 : ℤ)))

def gridActivePairs {n k : ℕ} (c : OffsetTable n k) (g : GridPoint n k) :
    Finset (Pair n) := Finset.univ.filter (GridActive c g)

def GridAccept {n k : ℕ} (c : OffsetTable n k) : Prop :=
  ∀ g : GridPoint n k, (gridActivePairs c g).card ≤ bandBudget n k

instance {n k : ℕ} (c : OffsetTable n k) : Decidable (GridAccept c) :=
  inferInstanceAs (Decidable (∀ g : GridPoint n k,
    (gridActivePairs c g).card ≤ bandBudget n k))

def Active {n k : ℕ} (c : OffsetTable n k) (r : Fin n → ℝ)
    (e : Pair n) : Prop :=
  |r e.val.1 - r e.val.2 - (offsetRat c e : ℝ)| < 1 / (k : ℝ)

noncomputable def activePairs {n k : ℕ} (c : OffsetTable n k) (r : Fin n → ℝ) :
    Finset (Pair n) := by
  classical
  exact Finset.univ.filter (Active c r)

def BandGood {n k : ℕ} (c : OffsetTable n k) : Prop :=
  ∀ r : Fin n → ℝ, (activePairs c r).card ≤ bandBudget n k

@[simp] theorem card_pair (n : ℕ) : Fintype.card (Pair n) = n.choose 2 := by
  simpa [Pair, Fintype.card_subtype] using
    (Fintype.card_product_filter_lt (α := Fin n))

theorem offsetInt_bounds {k : ℕ} (a : Offset k) :
    -(k : ℤ) ≤ offsetInt a ∧ offsetInt a ≤ k := by
  have h := a.isLt
  dsimp [offsetInt]
  omega

@[simp] theorem offsetRat_cast {n k : ℕ} (c : OffsetTable n k) (e : Pair n) :
    (offsetRat c e : ℝ) = (offsetInt (c e) : ℝ) / k := by
  simp [offsetRat]

theorem offsetRat_abs_le_one {n k : ℕ} (hk : 0 < k) (c : OffsetTable n k)
    (e : Pair n) : |(offsetRat c e : ℝ)| ≤ 1 := by
  rw [offsetRat_cast, abs_div, abs_of_pos (show (0 : ℝ) < k from Nat.cast_pos.mpr hk), div_le_one
    (Nat.cast_pos.mpr hk), abs_le]
  exact_mod_cast offsetInt_bounds (c e)

theorem active_abs_sub_lt_two {n k : ℕ} (hk : 0 < k) (c : OffsetTable n k)
    (r : Fin n → ℝ) (e : Pair n) (he : Active c r e) :
    |r e.val.1 - r e.val.2| < 2 := by
  have h₁ : 1 / (k : ℝ) ≤ 1 := by
    apply (div_le_one (Nat.cast_pos.mpr hk)).mpr
    exact_mod_cast hk
  have h₂ := offsetRat_abs_le_one hk c e
  have h₃ := abs_add_le (r e.val.1 - r e.val.2 - (offsetRat c e : ℝ))
    (offsetRat c e : ℝ)
  dsimp [Active] at he
  rw [sub_add_cancel] at h₃
  linarith

theorem gridAccept_of_card_le {n k : ℕ} (c : OffsetTable n k)
    (h : n.choose 2 ≤ bandBudget n k) : GridAccept c := by
  intro g
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using h)

theorem bandGood_of_card_le {n k : ℕ} (c : OffsetTable n k)
    (h : n.choose 2 ≤ bandBudget n k) : BandGood c := by
  intro r
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using h)

end SparseBand
end CutQueryComplexity.DirectedUnitST
