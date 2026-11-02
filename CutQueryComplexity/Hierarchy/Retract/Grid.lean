import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max

/-! # Grid-counting bounds (B3)

The rounding map of `Retract/Rounding` uses two uniform grids of `m` shifts `j / m`, one for
the scale and one for the band offset. Its error analysis needs only the following real bounds.

* `card_floor_ne_le`: the floors `⌊a + j/m⌋` and `⌊a' + j/m⌋` differ for at most
  `m |a' − a| + 1` of the `m` shifts;
* `logb_two_sub_le`: for `0 < r₁ ≤ r₂ ≤ r₁ + δ`, `log₂ r₂ − log₂ r₁ ≤ 2δ / r₁`;
* `exists_le_of_forall_pos`: on a finite set, a bound up to every `ε > 0` is attained. This is
  how the grid error `E / m` and the zero-length perturbation are removed.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace Retract

open Finset

/-- The floors of two shifted reals differ for at most `m (a' − a) + 1` of the shifts `j / m`:
`j ↦ m ⌊a' + j/m⌋ − j` injects the bad shifts into the integers of `(m a, m a']`. -/
theorem card_floor_ne_le {m : ℕ} (hm : 0 < m) {a a' : ℝ} (h : a ≤ a') :
    (((range m).filter fun j : ℕ => ⌊a + j / m⌋ ≠ ⌊a' + j / m⌋).card : ℝ) ≤ m * (a' - a) + 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set S := (range m).filter fun j : ℕ => ⌊a + j / m⌋ ≠ ⌊a' + j / m⌋
  let g : ℕ → ℤ := fun j => m * ⌊a' + j / m⌋ - j
  have hmaps : ∀ j ∈ S, g j ∈ Ioc ⌊m * a⌋ ⌊m * a'⌋ := by
    intro j hj
    obtain ⟨-, hne⟩ := mem_filter.mp hj
    have hle : ⌊a + j / m⌋ ≤ ⌊a' + j / m⌋ := Int.floor_mono (by linarith)
    have hlt : ⌊a + j / m⌋ < ⌊a' + j / m⌋ := lt_of_le_of_ne hle hne
    have h1 : a + j / m < ⌊a' + j / m⌋ := by
      have := Int.lt_floor_add_one (a + j / m)
      have h2 : ((⌊a + j / m⌋ + 1 : ℤ) : ℝ) ≤ ⌊a' + j / m⌋ := by exact_mod_cast hlt
      push_cast at h2; linarith
    have h3 : (⌊a' + j / m⌋ : ℝ) ≤ a' + j / m := Int.floor_le _
    have hjm : (m : ℝ) * (j / m) = j := by field_simp
    rw [mem_Ioc]
    constructor
    · rw [Int.floor_lt]
      simp only [g]; push_cast
      have := mul_lt_mul_of_pos_left h1 hm'
      rw [mul_add, hjm] at this; linarith
    · rw [Int.le_floor]
      simp only [g]; push_cast
      have := mul_le_mul_of_nonneg_left h3 hm'.le
      rw [mul_add, hjm] at this; linarith
  have hinj : Set.InjOn g S := by
    intro j hj j' hj' he
    have hjm : j < m := mem_range.mp (mem_filter.mp hj).1
    have hjm' : j' < m := mem_range.mp (mem_filter.mp hj').1
    simp only [g] at he
    set n := ⌊a' + j / m⌋
    set n' := ⌊a' + j' / m⌋
    have hk : (j' : ℤ) - j = m * (n' - n) := by linarith
    have : n' - n = 0 := by
      rcases lt_trichotomy (n' - n) 0 with hl | hl | hl
      · have : (m : ℤ) * (n' - n) ≤ -m := by nlinarith
        omega
      · exact hl
      · have : (m : ℤ) ≤ m * (n' - n) := by nlinarith
        omega
    rw [this, mul_zero] at hk
    omega
  have hcard : S.card ≤ (Ioc ⌊m * a⌋ ⌊m * a'⌋).card := card_le_card_of_injOn g hmaps hinj
  rw [Int.card_Ioc] at hcard
  have hcR : (S.card : ℝ) ≤ ((⌊m * a'⌋ - ⌊m * a⌋).toNat : ℝ) := by exact_mod_cast hcard
  have hfl : ⌊m * a⌋ ≤ ⌊m * a'⌋ := Int.floor_mono (mul_le_mul_of_nonneg_left h hm'.le)
  have htn : (((⌊m * a'⌋ - ⌊m * a⌋).toNat : ℤ) : ℝ) = ((⌊m * a'⌋ - ⌊m * a⌋ : ℤ) : ℝ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  have e1 : ((⌊m * a'⌋ - ⌊m * a⌋).toNat : ℝ) =
      (((⌊m * a'⌋ - ⌊m * a⌋).toNat : ℤ) : ℝ) := by norm_cast
  rw [e1, htn] at hcR
  push_cast at hcR
  have := Int.floor_le ((m : ℝ) * a')
  have := Int.lt_floor_add_one ((m : ℝ) * a)
  nlinarith

/-- The unordered form of `card_floor_ne_le`. -/
theorem card_floor_ne_le_abs {m : ℕ} (hm : 0 < m) (a a' : ℝ) :
    (((range m).filter fun j : ℕ => ⌊a + j / m⌋ ≠ ⌊a' + j / m⌋).card : ℝ) ≤ m * |a' - a| + 1 := by
  rcases le_total a a' with h | h
  · rw [abs_of_nonneg (by linarith)]; exact card_floor_ne_le hm h
  · rw [abs_of_nonpos (by linarith)]
    have := card_floor_ne_le hm h
    simp_rw [ne_comm (a := ⌊a + _⌋)]
    linarith

/-- `log₂` is `2 / r₁`-Lipschitz on `[r₁, ∞)`. -/
theorem logb_two_sub_le {r₁ r₂ δ : ℝ} (h0 : 0 < r₁) (h : r₁ ≤ r₂) (h2 : r₂ ≤ r₁ + δ) :
    Real.logb 2 r₂ - Real.logb 2 r₁ ≤ 2 * δ / r₁ := by
  have hr₂ : 0 < r₂ := lt_of_lt_of_le h0 h
  have hδ : 0 ≤ δ / r₁ := div_nonneg (by linarith) h0.le
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) two_pos; norm_num at this ⊢; linarith
  rw [← Real.logb_div hr₂.ne' h0.ne', Real.logb]
  have hlog : Real.log (r₂ / r₁) ≤ δ / r₁ := by
    have := Real.log_le_sub_one_of_pos (div_pos hr₂ h0)
    have : r₂ / r₁ - 1 ≤ δ / r₁ := by
      rw [div_sub_one h0.ne']; exact div_le_div_of_nonneg_right (by linarith) h0.le
    linarith
  rw [div_le_iff₀ (by linarith), mul_div_assoc]
  nlinarith

/-- On a finite set, a bound that holds up to every positive error holds exactly. -/
theorem exists_le_of_forall_pos {ι : Type*} (s : Finset ι) (g : ι → ℝ) (B : ℝ)
    (h : ∀ ε > 0, ∃ i ∈ s, g i ≤ B + ε) : ∃ i ∈ s, g i ≤ B := by
  obtain ⟨i₁, hi₁, -⟩ := h 1 one_pos
  obtain ⟨i₀, hi₀, hmin⟩ := s.exists_min_image g ⟨i₁, hi₁⟩
  by_contra hne
  push Not at hne
  have hgap : 0 < (g i₀ - B) / 2 := by have := hne i₀ hi₀; linarith
  obtain ⟨i, hi, hle⟩ := h _ hgap
  have := hmin i hi
  have := hne i₀ hi₀
  linarith

end Retract
end Hierarchy
end CutQueryComplexity
