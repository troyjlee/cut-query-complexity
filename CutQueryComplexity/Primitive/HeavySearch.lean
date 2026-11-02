import CutQueryComplexity.Primitive.BinarySearch

/-! # Finding an element at least as heavy as the average

Each split retains a half whose average is at least a fixed target. A root
subset-sum query supplies that target. The routine is deterministic and uses
one query per level, without inspecting individual unqueried weights.
-/

namespace CutQueryComplexity
noncomputable section
open scoped Classical
variable {V : Type} [DecidableEq V]

/-- Search with a known lower bound on the current average. -/
def searchAverage : (k : ℕ) → Finset V → ℝ → DTree (Finset V) ℝ (Option V) k
  | 0, U, _ => U.toList.head?
  | k + 1, U, target => DTree.query (Split.left (2 ^ k) U) fun a =>
      if target * (Split.left (2 ^ k) U).card ≤ a then
        searchAverage k (Split.left (2 ^ k) U) target
      else searchAverage k (U \ Split.left (2 ^ k) U) target

theorem searchAverage_correct (w : V → ℝ) (k : ℕ) (U : Finset V) (target : ℝ)
    (hcard : U.card ≤ 2 ^ k) (hne : U.Nonempty)
    (hav : target * U.card ≤ subsetSum w U) :
    ∃ v, (searchAverage k U target).eval (subsetSum w) = some v ∧ v ∈ U ∧ target ≤ w v := by
  induction k generalizing U with
  | zero =>
      obtain ⟨v, hv⟩ := hne
      have hU : U = {v} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hv, fun u hu => (Finset.card_le_one.mp (by simpa using hcard)) u hu v hv⟩
      subst U
      refine ⟨v, ?_, by simp, ?_⟩
      · simp [searchAverage, DTree.eval, DTree.run]
      · simpa [subsetSum] using hav
  | succ k ih =>
      have hleft : (Split.left (2 ^ k) U).Nonempty := by
        apply Finset.card_pos.mp
        rw [Split.card_left]
        exact lt_min (pow_pos (by decide) _) hne.card_pos
      have hright : (U \ Split.left (2 ^ k) U).card ≤ 2 ^ k :=
        Split.card_right_le (by simpa [pow_succ, Nat.mul_comm] using hcard)
      by_cases hl : target * (Split.left (2 ^ k) U).card ≤ subsetSum w (Split.left (2 ^ k) U)
      · obtain ⟨v, he, hv, hw⟩ := ih _ (Split.card_left_le _ _) hleft hl
        exact ⟨v, by simpa [searchAverage, hl] using he, Split.left_subset _ _ hv, hw⟩
      · have hc : ((Split.left (2 ^ k) U).card : ℝ) +
            (U \ Split.left (2 ^ k) U).card = U.card := by
          have hcNat : (Split.left (2 ^ k) U).card +
              (U \ Split.left (2 ^ k) U).card = U.card := by
            have := Finset.card_sdiff_add_card_eq_card (Split.left_subset (2 ^ k) U)
            omega
          exact_mod_cast hcNat
        have hc' : target * (Split.left (2 ^ k) U).card +
            target * (U \ Split.left (2 ^ k) U).card = target * U.card := by
          rw [← mul_add, hc]
        have hs := Split.sum_split w (2 ^ k) U
        have hr : target * (U \ Split.left (2 ^ k) U).card <
            subsetSum w (U \ Split.left (2 ^ k) U) := by
          unfold subsetSum at *
          linarith
        have hrne : (U \ Split.left (2 ^ k) U).Nonempty := by
          by_contra h
          have he := Finset.not_nonempty_iff_eq_empty.mp h
          simp [he, subsetSum] at hr
        obtain ⟨v, he, hv, hw⟩ := ih _ hright hrne hr.le
        exact ⟨v, by simpa [searchAverage, hl] using he, Finset.sdiff_subset hv, hw⟩

/-- Query the total and search for an element at least as heavy as its average. -/
def findHeavySubset (k : ℕ) (U : Finset V) : DTree (Finset V) ℝ (Option V) (k + 1) :=
  DTree.query U fun total =>
    if 0 < total then searchAverage k U (total / U.card) else DTree.pure none

def HeavySubsetResult (w : V → ℝ) (U : Finset V) : Option V → Prop
  | none => ∀ v ∈ U, w v = 0
  | some v => v ∈ U ∧ 0 < w v ∧ subsetSum w U ≤ (U.card : ℝ) * w v

theorem findHeavySubset_positive (w : V → ℝ) (k : ℕ) (U : Finset V)
    (hcard : U.card ≤ 2 ^ k) (hp : 0 < subsetSum w U) :
    ∃ v, (findHeavySubset k U).eval (subsetSum w) = some v ∧
      v ∈ U ∧ 0 < w v ∧ subsetSum w U ≤ (U.card : ℝ) * w v := by
  have hne : U.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h, subsetSum] at hp
  have hc : 0 < (U.card : ℝ) := by exact_mod_cast hne.card_pos
  obtain ⟨v, he, hv, hw⟩ := searchAverage_correct w k U (subsetSum w U / U.card) hcard hne
    (by rw [div_mul_cancel₀ _ (ne_of_gt hc)])
  refine ⟨v, by simpa [findHeavySubset, hp] using he, hv, (div_pos hp hc).trans_le hw, ?_⟩
  simpa [mul_comm] using (div_le_iff₀ hc).mp hw

theorem findHeavySubset_zero (w : V → ℝ) (k : ℕ) (U : Finset V)
    (hz : subsetSum w U = 0) : (findHeavySubset k U).eval (subsetSum w) = none := by
  simp [findHeavySubset, hz]

theorem findHeavySubset_correct (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (k : ℕ) (U : Finset V)
    (hcard : U.card ≤ 2 ^ k) :
    HeavySubsetResult w U ((findHeavySubset k U).eval (subsetSum w)) := by
  by_cases hp : 0 < subsetSum w U
  · obtain ⟨v, he, hv, hvp, hav⟩ := findHeavySubset_positive w k U hcard hp
    rw [he]
    exact ⟨hv, hvp, hav⟩
  · have hz : subsetSum w U = 0 := le_antisymm (le_of_not_gt hp)
        (Finset.sum_nonneg (fun v _ => hw v))
    rw [findHeavySubset_zero w k U hz]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hw v)).mp hz

end
end CutQueryComplexity
