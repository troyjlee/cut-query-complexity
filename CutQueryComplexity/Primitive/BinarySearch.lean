import CutQueryComplexity.Primitive.Reductions
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Sort

/-! # Balanced positive-weight search from subset sums -/

namespace CutQueryComplexity

noncomputable section
open scoped Classical

namespace Split

variable {V : Type} [DecidableEq V]

/-- A public prefix containing at most `m` candidates. -/
def left (m : ℕ) (U : Finset V) : Finset V := (U.toList.take m).toFinset

theorem left_subset (m : ℕ) (U : Finset V) : left m U ⊆ U := by
  intro v hv
  exact Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hv))

theorem card_left (m : ℕ) (U : Finset V) : (left m U).card = min m U.card := by
  rw [left, List.toFinset_card_of_nodup (show (U.toList.take m).Nodup from U.nodup_toList.take)]
  simp

theorem card_left_le (m : ℕ) (U : Finset V) : (left m U).card ≤ m := by
  rw [card_left]; exact min_le_left _ _

theorem card_right_le {m : ℕ} {U : Finset V} (h : U.card ≤ 2 * m) :
    (U \ left m U).card ≤ m := by
  rw [Finset.card_sdiff_of_subset (left_subset m U), card_left]
  omega

theorem sum_split (w : V → ℝ) (m : ℕ) (U : Finset V) :
    (∑ v ∈ left m U, w v) + (∑ v ∈ U \ left m U, w v) = ∑ v ∈ U, w v := by
  have hd : Disjoint (left m U) (U \ left m U) :=
    Finset.disjoint_left.mpr (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₂).2 h₁)
  rw [← Finset.sum_union hd,
    Finset.union_sdiff_of_subset (left_subset m U)]

end Split

variable {V : Type} [DecidableEq V]

/-- One scalar answer for the sum of all candidate weights in a shore. -/
def subsetSum (w : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, w v

/-- Search a set of at most `2^k` candidates whose total weight is known to be positive. -/
def searchPositive : (k : ℕ) → Finset V → DTree (Finset V) ℝ (Option V) k
  | 0, U => U.toList.head?
  | k + 1, U => DTree.query (Split.left (2 ^ k) U) fun a =>
      if 0 < a then searchPositive k (Split.left (2 ^ k) U)
      else searchPositive k (U \ Split.left (2 ^ k) U)

theorem searchPositive_correct (w : V → ℝ) (k : ℕ) (U : Finset V)
    (hcard : U.card ≤ 2 ^ k) (hpos : 0 < subsetSum w U) :
    ∃ v, (searchPositive k U).eval (subsetSum w) = some v ∧ v ∈ U ∧ 0 < w v := by
  induction k generalizing U with
  | zero =>
      have hne : U.Nonempty := by
        by_contra h
        have : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        simp [this, subsetSum] at hpos
      obtain ⟨v, hv⟩ := hne
      have hU : U = {v} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hv, fun u hu => (Finset.card_le_one.mp (by simpa using hcard)) u hu v hv⟩
      subst U
      refine ⟨v, ?_, by simp, ?_⟩
      · simp [searchPositive, DTree.eval, DTree.run]
      · simpa [subsetSum] using hpos
  | succ k ih =>
      have hr : (U \ Split.left (2 ^ k) U).card ≤ 2 ^ k :=
        Split.card_right_le (by simpa [pow_succ, Nat.mul_comm] using hcard)
      by_cases hl : 0 < subsetSum w (Split.left (2 ^ k) U)
      · obtain ⟨v, he, hv, hp⟩ := ih _ (Split.card_left_le _ _) hl
        refine ⟨v, ?_, Split.left_subset _ _ hv, hp⟩
        simpa [searchPositive, hl] using he
      · have hright : 0 < subsetSum w (U \ Split.left (2 ^ k) U) := by
          have hs := Split.sum_split w (2 ^ k) U
          dsimp [subsetSum] at hl hpos ⊢
          linarith
        obtain ⟨v, he, hv, hp⟩ := ih _ hr hright
        refine ⟨v, ?_, Finset.sdiff_subset hv, hp⟩
        simpa [searchPositive, hl] using he

/-- Detect absence, or return a positive-weight candidate, in at most `k+1` queries. -/
def findPositive (k : ℕ) (U : Finset V) : DTree (Finset V) ℝ (Option V) (k + 1) :=
  DTree.query U fun a => if 0 < a then searchPositive k U else DTree.pure none

/-- Exact result contract, including all-zero inputs. -/
def PositiveResult (w : V → ℝ) (U : Finset V) : Option V → Prop
  | none => ∀ v ∈ U, w v = 0
  | some v => v ∈ U ∧ 0 < w v

theorem findPositive_correct (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (k : ℕ) (U : Finset V)
    (hcard : U.card ≤ 2 ^ k) :
    PositiveResult w U ((findPositive k U).eval (subsetSum w)) := by
  by_cases hp : 0 < subsetSum w U
  · obtain ⟨v, hv, hm, hw⟩ := searchPositive_correct w k U hcard hp
    simpa [findPositive, hp, hv, PositiveResult] using And.intro hm hw
  · have hzero : subsetSum w U = 0 := le_antisymm (le_of_not_gt hp)
        (Finset.sum_nonneg (fun v _ => hw v))
    simp only [findPositive, DTree.eval_query, ite_eq_right hp, DTree.eval_pure, PositiveResult]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hw v)).mp hzero

variable [Fintype V]

/-- Public binary-search depth, valid for empty and singleton vertex sets too. -/
def searchDepth (V : Type) [Fintype V] : ℕ := Nat.clog 2 (Fintype.card V)

theorem card_le_pow_searchDepth (U : Finset V) : U.card ≤ 2 ^ searchDepth V :=
  (Finset.card_le_univ U).trans (Nat.le_pow_clog (by decide) _)

end
end CutQueryComplexity
