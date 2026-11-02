import CutQueryComplexity.Sparsification.LocalCutCounting
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Counting the labelings of one internally connected block

The existing local contraction count treats proper shores. We add the two
constant labelings explicitly; this also handles singleton blocks. The
integer exponent keeps the later product count in natural arithmetic.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Counting

noncomputable section
open Finset WeightedGraph
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- All binary labelings of a block, including its two constants. -/
def localLabelings (J : WeightedGraph V) (U : Finset V) (a : ℕ) :
    Finset (Finset V) :=
  U.powerset.filter (fun S => J.localCut U S ≤ (a : ℝ))

omit [Fintype V] in
@[simp] theorem mem_localLabelings (J : WeightedGraph V) (U S : Finset V) (a : ℕ) :
    S ∈ localLabelings J U a ↔ S ⊆ U ∧ J.localCut U S ≤ (a : ℝ) := by
  simp [localLabelings]

/-- A positive integral rounding of the local budget ratio. -/
def localScale (τ : ℝ) (a : ℕ) : ℕ := ⌈(a : ℝ) / τ⌉₊ + 1

/-- Natural exponent used for one block in the product encoding. -/
def localExponent (τ : ℝ) (a : ℕ) : ℕ := 2 * localScale τ a + 1

theorem localScale_pos (τ : ℝ) (a : ℕ) : 1 ≤ localScale τ a := by
  simp [localScale]

theorem budget_le_localScale {τ : ℝ} (hτ : 0 < τ) (a : ℕ) :
    (a : ℝ) ≤ localScale τ a * τ := by
  apply (div_le_iff₀ hτ).mp
  calc
    (a : ℝ) / τ ≤ (⌈(a : ℝ) / τ⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (localScale τ a : ℝ) := by simp [localScale]

theorem localExponent_le {τ : ℝ} (hτ : 0 < τ) (a : ℕ) :
    (localExponent τ a : ℝ) ≤ 5 + 2 * (a : ℝ) / τ := by
  have hc := Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg a) hτ.le)
  dsimp [localExponent, localScale]
  push_cast
  rw [mul_div_assoc]
  linarith

/-- The proper local count plus two constants, with the ambient base explicit. -/
theorem localLabelings_card_le (J : WeightedGraph V) (U : Finset V)
    {τ : ℝ} (hτ : 0 < τ)
    (hmin : ∀ S, LocalShore U S → τ ≤ J.localCut U S)
    (hU : U.Nonempty) {n : ℕ} (hUn : U.card ≤ n) (a : ℕ) :
    (localLabelings J U a).card ≤ (2 * n) ^ localExponent τ a := by
  let k := localScale τ a
  have hk : 1 ≤ k := localScale_pos τ a
  have hn : 1 ≤ n := (card_pos.mpr hU).trans_le hUn
  have hcover : localLabelings J U a ⊆
      J.localNearMinShores U τ k ∪ ({∅, U} : Finset (Finset V)) := by
    intro S hS
    obtain ⟨hSU, hcut⟩ := (mem_localLabelings J U S a).mp hS
    by_cases hzero : S = ∅
    · simp [hzero]
    by_cases hfull : S = U
    · simp [hfull]
    have hlocal : LocalShore U S :=
      ⟨hSU, nonempty_iff_ne_empty.mpr hzero,
        sdiff_nonempty.mpr (by intro hUS; exact hfull (Subset.antisymm hSU hUS))⟩
    apply mem_union_left
    exact mem_filter.mpr ⟨(mem_localShores U S).mpr hlocal,
      hcut.trans (budget_le_localScale hτ a)⟩
  have hproper : (J.localNearMinShores U τ k).card ≤ (2 * n) ^ (2 * k) :=
    (J.localNearMinShores_card_le_pow U hτ hmin (card_pos.mpr hU) k hk).trans
      (pow_le_pow_left' (Nat.mul_le_mul_left 2 hUn) _)
  have hbase : 2 ≤ 2 * n := by omega
  have hpow : 2 ≤ (2 * n) ^ (2 * k) :=
    hbase.trans (le_self_pow (by omega) (by omega))
  calc
    (localLabelings J U a).card ≤
        (J.localNearMinShores U τ k ∪ ({∅, U} : Finset (Finset V))).card :=
      card_le_card hcover
    _ ≤ (J.localNearMinShores U τ k).card + ({∅, U} : Finset (Finset V)).card :=
      card_union_le _ _
    _ ≤ (2 * n) ^ (2 * k) + 2 :=
      Nat.add_le_add hproper (by simpa using (card_insert_le (∅ : Finset V) ({U} : Finset (Finset V))))
    _ ≤ (2 * n) ^ (2 * k) + (2 * n) ^ (2 * k) := Nat.add_le_add_left hpow _
    _ = (2 * n) ^ (2 * k) * 2 := by omega
    _ ≤ (2 * n) ^ (2 * k) * (2 * n) := Nat.mul_le_mul_left _ hbase
    _ = (2 * n) ^ localExponent τ a := by
      change (2 * n) ^ (2 * k) * (2 * n) = (2 * n) ^ (2 * k + 1)
      exact (pow_succ (2 * n) (2 * k)).symm

end
end CutQueryComplexity.CanonicalST.Counting

#print axioms CutQueryComplexity.CanonicalST.Counting.budget_le_localScale
#print axioms CutQueryComplexity.CanonicalST.Counting.localExponent_le
#print axioms CutQueryComplexity.CanonicalST.Counting.localLabelings_card_le
