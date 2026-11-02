import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Exact rational potential bins

The final bin includes potential one, even when `2 / δ` is integral.
No floating-point operation or hidden graph is used by these definitions.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.LongEdge

def binIndex (δ x : ℚ) : ℕ := ⌊x / (δ / 2)⌋₊

def binCount (δ : ℚ) : ℕ := ⌊1 / (δ / 2)⌋₊ + 1

theorem binCount_pos (δ : ℚ) : 0 < binCount δ := by
  unfold binCount
  omega

/-- In particular, the endpoint one is in the last bin, not discarded. -/
theorem binIndex_one_add (δ : ℚ) : binIndex δ 1 + 1 = binCount δ := rfl

theorem bin_lower {δ x : ℚ} (hδ : 0 < δ) (hx : 0 ≤ x) :
    (binIndex δ x : ℚ) * (δ / 2) ≤ x := by
  have hη : 0 < δ / 2 := by positivity
  exact (le_div_iff₀ hη).mp (Nat.floor_le (div_nonneg hx hη.le))

theorem bin_upper {δ x : ℚ} (hδ : 0 < δ) :
    x < ((binIndex δ x : ℚ) + 1) * (δ / 2) := by
  have hη : 0 < δ / 2 := by positivity
  exact (div_lt_iff₀ hη).mp (Nat.lt_floor_add_one (x / (δ / 2)))

theorem binIndex_lt_count {δ x : ℚ} (hδ : 0 < δ) (hx : x ≤ 1) :
    binIndex δ x < binCount δ := by
  have hη : 0 < δ / 2 := by positivity
  have h := Nat.floor_le_floor ((div_le_div_iff_of_pos_right hη).mpr hx)
  change ⌊x / (δ / 2)⌋₊ < ⌊1 / (δ / 2)⌋₊ + 1
  omega

/-- Length at least δ forces two or more bin steps. -/
theorem bin_forward {δ x y : ℚ} (hδ : 0 < δ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hlength : δ ≤ |x - y|) :
    binIndex δ x + 2 ≤ binIndex δ y ∨ binIndex δ y + 2 ≤ binIndex δ x := by
  by_contra h
  have hxy : binIndex δ x ≤ binIndex δ y + 1 := by omega
  have hyx : binIndex δ y ≤ binIndex δ x + 1 := by omega
  have hxyR : (binIndex δ x : ℚ) ≤ (binIndex δ y : ℚ) + 1 := by exact_mod_cast hxy
  have hyxR : (binIndex δ y : ℚ) ≤ (binIndex δ x : ℚ) + 1 := by exact_mod_cast hyx
  have hη : 0 ≤ δ / 2 := by positivity
  have hmxy := mul_le_mul_of_nonneg_right hxyR hη
  have hmyx := mul_le_mul_of_nonneg_right hyxR hη
  have hxl := bin_lower hδ hx
  have hyl := bin_lower hδ hy
  have hxu := bin_upper (x := x) hδ
  have hyu := bin_upper (x := y) hδ
  have habs : |x - y| < δ := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  exact (not_lt_of_ge hlength) habs

private theorem bin_gap_length {δ x y : ℚ} (hδ : 0 < δ) (hy : 0 ≤ y)
    (hgap : binIndex δ x + 2 ≤ binIndex δ y) : δ / 2 ≤ y - x := by
  have hgapR : (binIndex δ x : ℚ) + 2 ≤ (binIndex δ y : ℚ) := by exact_mod_cast hgap
  have hm := mul_le_mul_of_nonneg_right hgapR (show 0 ≤ δ / 2 by positivity)
  have hxu := bin_upper (x := x) hδ
  have hyl := bin_lower hδ hy
  nlinarith

/-- Two bin steps force actual length at least δ/2, including the last bin. -/
theorem bin_backward {δ x y : ℚ} (hδ : 0 < δ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hgap : binIndex δ x + 2 ≤ binIndex δ y ∨ binIndex δ y + 2 ≤ binIndex δ x) :
    δ / 2 ≤ |x - y| := by
  rcases hgap with hgap | hgap
  · rw [abs_sub_comm]
    exact (bin_gap_length hδ hy hgap).trans (le_abs_self _)
  · exact (bin_gap_length hδ hx hgap).trans (le_abs_self _)

/-- A public natural precision scale for expressing the logarithmic cap. -/
def reciprocalScale (δ : ℚ) : ℕ := ⌈1 / δ⌉₊

theorem reciprocalScale_pos {δ : ℚ} (hδ : 0 < δ) : 0 < reciprocalScale δ := by
  have h := (one_div_pos.mpr hδ).trans_le (Nat.le_ceil (1 / δ))
  exact_mod_cast h

theorem binCount_le_four_scale {δ : ℚ} (hδ : 0 < δ) :
    binCount δ ≤ 4 * reciprocalScale δ := by
  have he : (1 : ℚ) / (δ / 2) = 2 * (1 / δ) := by field_simp [hδ.ne']
  have hfloor := Nat.floor_le (show (0 : ℚ) ≤ 1 / (δ / 2) by positivity)
  have hceil := Nat.le_ceil (1 / δ)
  have hpos : (1 : ℚ) ≤ reciprocalScale δ := by
    exact_mod_cast (Nat.succ_le_of_lt (reciprocalScale_pos hδ))
  have hR : (binCount δ : ℚ) ≤ 4 * (reciprocalScale δ : ℚ) := by
    unfold binCount reciprocalScale at *
    push_cast
    rw [he] at hfloor ⊢
    nlinarith
  exact_mod_cast hR

theorem binCount_clog_le {δ : ℚ} (hδ : 0 < δ) :
    Nat.clog 2 (binCount δ) ≤ Nat.clog 2 (reciprocalScale δ) + 2 := by
  apply Nat.clog_le_of_le_pow
  calc
    binCount δ ≤ 4 * reciprocalScale δ := binCount_le_four_scale hδ
    _ ≤ 4 * 2 ^ Nat.clog 2 (reciprocalScale δ) :=
      Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
    _ = 2 ^ (Nat.clog 2 (reciprocalScale δ) + 2) := by rw [pow_add]; ring

end CutQueryComplexity.CanonicalST.LongEdge

#print axioms CutQueryComplexity.CanonicalST.LongEdge.binIndex_lt_count
#print axioms CutQueryComplexity.CanonicalST.LongEdge.binIndex_one_add
#print axioms CutQueryComplexity.CanonicalST.LongEdge.bin_forward
#print axioms CutQueryComplexity.CanonicalST.LongEdge.bin_backward
#print axioms CutQueryComplexity.CanonicalST.LongEdge.binCount_clog_le
