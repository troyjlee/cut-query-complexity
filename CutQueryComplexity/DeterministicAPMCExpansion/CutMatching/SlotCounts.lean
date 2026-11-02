import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.CloneAssignment
import Mathlib.Data.Fintype.BigOperators

/-! # The literal source and sink capacities of a clone bisection -/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {b : ℕ}

def slotFiberEquiv (S : Finset (Clone V b)) (v : V) :
    {c : S // c.val.1 = v} ≃ {i : Fin b // (v, i) ∈ S} where
  toFun := by
    rintro ⟨⟨⟨u, i⟩, hc⟩, hu⟩
    change u = v at hu
    subst u
    exact ⟨i, hc⟩
  invFun i := ⟨⟨(v, i.val), i.property⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨u, i⟩, hc⟩, hu⟩
    dsimp at hu
    subst u
    rfl
  right_inv := by rintro ⟨i, hi⟩; rfl

theorem slotCount_sum (S : Finset (Clone V b)) (v : V) :
    slotCount S v = ∑ i : Fin b, if (v, i) ∈ S then 1 else 0 := by
  rw [slotCount, Fintype.card_congr (slotFiberEquiv S v), Fintype.card_subtype,
    card_filter]

theorem slotCount_add_compl (S : Finset (Clone V b)) (v : V) :
    slotCount S v + slotCount Sᶜ v = b := by
  simp only [slotCount_sum, mem_compl]
  rw [← sum_add_distrib]
  calc
    _ = ∑ _i : Fin b, 1 := by
      apply sum_congr rfl
      intro i _
      by_cases h : (v, i) ∈ S <;> simp [h]
    _ = b := by simp

theorem slotCount_le (S : Finset (Clone V b)) (v : V) : slotCount S v ≤ b := by
  have h := slotCount_add_compl S v
  omega

theorem sum_slotCount (S : Finset (Clone V b)) : (∑ v, slotCount S v) = S.card := by
  change (∑ v, Fintype.card {c : S // c.val.1 = v}) = S.card
  rw [← Fintype.card_sigma,
    Fintype.card_congr (Equiv.sigmaFiberEquiv (fun c : S => c.val.1)), Fintype.card_coe]

theorem slotCount_shore_le (S : Finset (Clone V b)) (P : Finset V) :
    (∑ v ∈ P, slotCount S v) ≤ b * P.card := by
  calc
    _ ≤ ∑ _v ∈ P, b := sum_le_sum fun v _ => slotCount_le S v
    _ = b * P.card := by simp [Nat.mul_comm]

theorem slotCount_shore_le_real (S : Finset (Clone V b)) (P : Finset V) :
    (∑ v ∈ P, (slotCount S v : ℝ)) ≤ (b : ℝ) * P.card := by
  exact_mod_cast slotCount_shore_le S P

theorem bisection_star_totals (cut : Bisection (Clone V b)) :
    (∑ v, slotCount cut.shore v) = cut.shore.card ∧
      (∑ v, slotCount cut.shoreᶜ v) = cut.shore.card := by
  rw [sum_slotCount, sum_slotCount, cut.balanced]
  exact ⟨rfl, rfl⟩

theorem bisection_clone_card (cut : Bisection (Clone V b)) :
    2 * cut.shore.card = Fintype.card V * b := by
  have h := card_add_card_compl cut.shore
  rw [← cut.balanced] at h
  simpa only [Clone, Fintype.card_prod, Fintype.card_fin, two_mul] using h

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.slotCount_add_compl
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.sum_slotCount
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.bisection_star_totals
