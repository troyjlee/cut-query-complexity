import CutQueryComplexity.GHReduction.CanonicalCuts
import CutQueryComplexity.Probability.Expectation
import Mathlib.Probability.Distributions.Uniform

/-! # Uniform public pivots and small canonical target shores

`canonicalShore` is used only in the analysis. The pivot distribution is uniform
on the public terminal set and has no graph parameter. Opposite minimum shores
are disjoint by inclusion minimality; hence at least one orientation of every
unordered terminal pair is balanced. Ties may contribute both orientations.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.OuterPivot
noncomputable section
open scoped Classical BigOperators ENNReal
open WeightedGraph Probability

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A proof-only canonical witness, empty on the unused diagonal. -/
def canonicalShore (G : WeightedGraph V) (v s : V) : Finset V :=
  if h : v ≠ s then Classical.choose (exists_canonicalSTCut G h) else ∅

theorem canonicalShore_correct (G : WeightedGraph V) {v s : V} (hvs : v ≠ s) :
    IsCanonicalSTCut G v s (canonicalShore G v s) := by
  rw [canonicalShore, dite_eq_left hvs]
  exact Classical.choose_spec (exists_canonicalSTCut G hvs)

@[simp] theorem canonicalShore_self (G : WeightedGraph V) (s : V) :
    canonicalShore G s s = ∅ := by simp [canonicalShore]

theorem canonical_opposite_disjoint (G : WeightedGraph V) {v s : V}
    {S T : Finset V} (hS : IsCanonicalSTCut G v s S)
    (hT : IsCanonicalSTCut G s v T) : Disjoint S T := by
  have hsub := hS.2 Tᶜ (stMinCut_compl G hT.1)
  exact Finset.disjoint_left.mpr (fun x hxS hxT =>
    (Finset.mem_compl.mp (hsub hxS)) hxT)

theorem canonicalShore_opposite_disjoint (G : WeightedGraph V) (v s : V) :
    Disjoint (canonicalShore G v s) (canonicalShore G s v) := by
  by_cases hvs : v = s
  · subst v
    simp
  · exact canonical_opposite_disjoint G (canonicalShore_correct G hvs)
      (canonicalShore_correct G (Ne.symm hvs))

theorem canonicalShore_opposite_card (G : WeightedGraph V) (U : Finset V) (v s : V) :
    (canonicalShore G v s ∩ U).card + (canonicalShore G s v ∩ U).card ≤ U.card := by
  have hd := (canonicalShore_opposite_disjoint G v s).mono
    (Finset.inter_subset_left (s₁ := canonicalShore G v s) (s₂ := U))
    (Finset.inter_subset_left (s₁ := canonicalShore G s v) (s₂ := U))
  rw [← Finset.card_union_of_disjoint hd]
  exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_right
    Finset.inter_subset_right)

def balancedTargets (G : WeightedGraph V) (U : Finset V) (s : V) : Finset V :=
  (U.erase s).filter (fun v => 2 * (canonicalShore G v s ∩ U).card ≤ U.card)

@[simp] theorem mem_balancedTargets (G : WeightedGraph V) (U : Finset V) (s v : V) :
    v ∈ balancedTargets G U s ↔
      v ≠ s ∧ v ∈ U ∧ 2 * (canonicalShore G v s ∩ U).card ≤ U.card := by
  simp [balancedTargets, and_assoc]

theorem balancedTargets_subset (G : WeightedGraph V) (U : Finset V) (s : V) :
    balancedTargets G U s ⊆ U.erase s := Finset.filter_subset _ _

@[simp] theorem balancedTargets_empty (G : WeightedGraph V) (s : V) :
    balancedTargets G ∅ s = ∅ := by simp [balancedTargets]

@[simp] theorem balancedTargets_singleton (G : WeightedGraph V) (s : V) :
    balancedTargets G {s} s = ∅ := by simp [balancedTargets]

theorem balanced_pair (G : WeightedGraph V) {U : Finset V} {s v : V}
    (hs : s ∈ U) (hv : v ∈ U) (hvs : v ≠ s) :
    v ∈ balancedTargets G U s ∨ s ∈ balancedTargets G U v := by
  have hc := canonicalShore_opposite_card G U v s
  by_cases hsmall : 2 * (canonicalShore G v s ∩ U).card ≤ U.card
  · exact Or.inl ((mem_balancedTargets G U s v).mpr ⟨hvs, hv, hsmall⟩)
  · exact Or.inr ((mem_balancedTargets G U v s).mpr ⟨Ne.symm hvs, hs, by omega⟩)

omit [Fintype V] in
private theorem indicator_sum (U A : Finset V) (hAU : A ⊆ U) :
    (∑ v ∈ U, if v ∈ A then 1 else 0 : ℕ) = A.card := by
  have hfilter : U.filter (fun v => v ∈ A) = A := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hAU h, h⟩⟩
  rw [← Finset.sum_filter, hfilter]
  simp

/-- Ordered-pair counting is valid also for zero or one terminal. -/
theorem balancedTargets_double_count (G : WeightedGraph V) (U : Finset V) :
    U.card * (U.card - 1) ≤ 2 * ∑ s ∈ U, (balancedTargets G U s).card := by
  have hpoint (s : V) (hs : s ∈ U) (v : V) (hv : v ∈ U) :
      (if v ≠ s then 1 else 0 : ℕ) ≤
        (if v ∈ balancedTargets G U s then 1 else 0) +
          (if s ∈ balancedTargets G U v then 1 else 0) := by
    by_cases hvs : v = s
    · simp [hvs]
    · rcases balanced_pair G hs hv hvs with h | h <;> simp [hvs, h]
  have hrow (s : V) (hs : s ∈ U) :
      (∑ v ∈ U, if v ≠ s then 1 else 0 : ℕ) = U.card - 1 := by
    have hfilter : U.filter (fun v => v ≠ s) = U.erase s := by
      ext v
      simp [and_comm]
    rw [← Finset.sum_filter, hfilter]
    simp [Finset.card_erase_of_mem hs]
  have hmember (s : V) :
      (∑ v ∈ U, if v ∈ balancedTargets G U s then 1 else 0 : ℕ) =
        (balancedTargets G U s).card :=
    indicator_sum U _ ((balancedTargets_subset G U s).trans (Finset.erase_subset _ _))
  have hleft : (∑ s ∈ U, ∑ v ∈ U, if v ≠ s then 1 else 0 : ℕ) =
      U.card * (U.card - 1) := by
    rw [Finset.sum_congr rfl hrow]
    simp
  have hright : (∑ s ∈ U, ∑ v ∈ U,
      ((if v ∈ balancedTargets G U s then 1 else 0) +
        (if s ∈ balancedTargets G U v then 1 else 0) : ℕ)) =
      2 * ∑ s ∈ U, (balancedTargets G U s).card := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun s _ => hmember s)]
    rw [Finset.sum_comm (s := U) (t := U)]
    rw [Finset.sum_congr rfl (fun s _ => hmember s)]
    omega
  have h := Finset.sum_le_sum (fun s hs => Finset.sum_le_sum (fun v hv => hpoint s hs v hv))
  simpa only [hleft, hright] using h

omit [Fintype V] [DecidableEq V] in
/-- Uniform averaging, retaining ENNReal's actual expectation. -/
theorem expect_uniform_finset (U : Finset V) (hU : U.Nonempty) (f : V → ℝ≥0∞) :
    expect (PMF.uniformOfFinset U hU) f = (U.card : ℝ≥0∞)⁻¹ * ∑ s ∈ U, f s := by
  rw [expect, tsum_eq_sum (s := U) (fun s hs => by
    rw [PMF.uniformOfFinset_apply_of_notMem hU hs, zero_mul])]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun s hs => by
    rw [PMF.uniformOfFinset_apply_of_mem hU hs])

/-- A uniform public pivot leaves at least half the other terminals eligible,
in expectation. The graph appears only in this analysis, not in the PMF. -/
theorem pivot_balance (G : WeightedGraph V) (U : Finset V) (hU : U.Nonempty) :
    ((U.card - 1 : ℕ) : ℝ≥0∞) ≤ 2 *
      expect (PMF.uniformOfFinset U hU) (fun s => ((balancedTargets G U s).card : ℝ≥0∞)) := by
  have hc : (U.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr hU))
  have hcast : (U.card : ℝ≥0∞) * ((U.card - 1 : ℕ) : ℝ≥0∞) ≤
      2 * ∑ s ∈ U, ((balancedTargets G U s).card : ℝ≥0∞) := by
    exact_mod_cast balancedTargets_double_count G U
  have hmul := mul_le_mul_right hcast (U.card : ℝ≥0∞)⁻¹
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc (by simp), one_mul] at hmul
  rw [expect_uniform_finset]
  calc
    _ ≤ (U.card : ℝ≥0∞)⁻¹ * (2 * ∑ s ∈ U, ((balancedTargets G U s).card : ℝ≥0∞)) := hmul
    _ = _ := by ac_rfl

#print axioms canonical_opposite_disjoint
#print axioms canonicalShore_opposite_card
#print axioms balanced_pair
#print axioms balancedTargets_double_count
#print axioms pivot_balance

end
end CutQueryComplexity.GHReduction.OuterPivot
