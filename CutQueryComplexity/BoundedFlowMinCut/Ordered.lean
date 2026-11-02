import CutQueryComplexity.BoundedFlowMinCut.Incidence

/-! # Ordered search along a list

Given a list `L` and an oracle for the masses `Σ_{x ∈ A} w x` of a nonnegative
weight `w`, find the first position of `L` whose weight is positive, with one
mass query per halving of the candidate range. Applied to the reversed list it
finds the last such position.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical

variable {V : Type} [DecidableEq V]

/-- The vertex set of the first `m` entries. -/
def prefixSet (L : List V) (m : ℕ) : Finset V := (L.take m).toFinset

/-- Binary search between `lo` (prefix mass zero) and `hi` (prefix mass positive). -/
def searchFirst (L : List V) : (fuel : ℕ) → ℕ → ℕ → DTree (Finset V) ℝ ℕ fuel
  | 0, _, hi => DTree.pure (hi - 1)
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then DTree.pure (hi - 1) else
        DTree.query (prefixSet L ((lo + hi) / 2)) fun a =>
          if 0 < a then searchFirst L fuel lo ((lo + hi) / 2)
          else searchFirst L fuel ((lo + hi) / 2) hi

theorem prefixSet_mono (L : List V) {m m' : ℕ} (h : m ≤ m') : prefixSet L m ⊆ prefixSet L m' := by
  intro x hx
  simp only [prefixSet, List.mem_toFinset] at hx ⊢
  exact (List.take_prefix_take_left h).subset hx

/-- Search invariant: `[0, lo)` has no positive entry, and `[0, hi)` has one. -/
theorem searchFirst_correct (w : V → ℝ) (hw : ∀ x, 0 ≤ w x) (L : List V) :
    ∀ (fuel lo hi : ℕ), lo < hi → hi ≤ L.length → hi - lo ≤ 2 ^ fuel →
      (∀ m < lo, ∀ h : m < L.length, w L[m] = 0) → (∃ m < hi, ∃ h : m < L.length, 0 < w L[m]) →
      let i := (searchFirst L fuel lo hi).eval (fun A => ∑ x ∈ A, w x)
      ∃ h : i < L.length, 0 < w L[i] ∧ ∀ m < i, ∀ h' : m < L.length, w L[m] = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hlt hhi hgap hzero hpos
      have hhl : hi = lo + 1 := by simp at hgap; omega
      subst hhl
      obtain ⟨m, hm, hml, hwm⟩ := hpos
      have hmlo : m = lo := by
        by_contra hne
        exact (lt_irrefl _) (hzero m (by omega) hml ▸ hwm)
      subst hmlo
      exact ⟨hml, hwm, hzero⟩
  | succ fuel ih =>
      intro lo hi hlt hhi hgap hzero hpos
      by_cases hstop : hi ≤ lo + 1
      · have hhl : hi = lo + 1 := by omega
        subst hhl
        obtain ⟨m, hm, hml, hwm⟩ := hpos
        have hmlo : m = lo := by
          by_contra hne
          exact (lt_irrefl _) (hzero m (by omega) hml ▸ hwm)
        subst hmlo
        rw [searchFirst, ite_eq_left hstop, DTree.eval_pure]
        exact ⟨by omega, by simpa using hwm, by simpa using hzero⟩
      · set mid := (lo + hi) / 2
        have hmid1 : lo < mid := by omega
        have hmid2 : mid < hi := by omega
        have hmass : (∑ x ∈ prefixSet L mid, w x) = 0 ↔
            ∀ m < mid, ∀ h : m < L.length, w L[m] = 0 := by
          rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hw x)]
          constructor
          · intro h m hm hml
            apply h
            simp only [prefixSet, List.mem_toFinset]
            exact List.mem_iff_getElem.mpr ⟨m, by simp; omega, by simp⟩
          · intro h x hx
            simp only [prefixSet, List.mem_toFinset] at hx
            obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hx
            simp only [List.length_take] at hm
            simpa using h m (by omega) (by omega)
        rw [searchFirst, ite_eq_right hstop, DTree.eval_query]
        by_cases hp : 0 < ∑ x ∈ prefixSet L mid, w x
        · rw [ite_eq_left hp]
          apply ih lo mid hmid1 (by omega) (by rw [pow_succ] at hgap; omega) hzero
          by_contra hno
          push Not at hno
          have : (∑ x ∈ prefixSet L mid, w x) = 0 := hmass.mpr (fun m hm hml =>
            le_antisymm (hno m hm hml) (hw _))
          linarith
        · rw [ite_eq_right hp]
          have hz : (∑ x ∈ prefixSet L mid, w x) = 0 :=
            le_antisymm (not_lt.mp hp) (Finset.sum_nonneg (fun x _ => hw x))
          apply ih mid hi hmid2 hhi (by rw [pow_succ] at hgap; omega) (hmass.mp hz) hpos

end
end CutQueryComplexity.BoundedFlowMinCut
