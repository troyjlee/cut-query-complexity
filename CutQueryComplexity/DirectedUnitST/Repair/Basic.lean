import CutQueryComplexity.DirectedCertificate.Flow
import Mathlib.Algebra.BigOperators.Field

/-! # Capacity and flow algebra for directed unit repair

All capacity restrictions below concern **opposite internal pair totals**.  They
do not restrict the capacities of auxiliary terminal stars.  Signed flow is
the existing antisymmetric `Certificate.IsFlow`; nonnegative phase usage is a
different object, introduced in `Dinic`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Repair

open Finset Certificate DirectedCertificate

variable {V : Type*} [Fintype V]

/-- The capacity invariant for internal pairs, including learned split pairs. -/
def PairBounded (G : WeightedDiGraph V) : Prop :=
  ∀ u v, G.c u v + G.c v u ≤ 2

/-- The sum of absolute coordinates. -/
def l1 (x : V → ℝ) : ℝ := ∑ v, |x v|

/-- Total positive supply. -/
def supply (x : V → ℝ) : ℝ := ∑ v, max (x v) 0

theorem l1_nonneg (x : V → ℝ) : 0 ≤ l1 x :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem supply_nonneg (x : V → ℝ) : 0 ≤ supply x :=
  sum_nonneg fun _ _ => le_max_right _ _

theorem two_supply (x : V → ℝ) : 2 * supply x = l1 x + ∑ v, x v := by
  have hx (v : V) : 2 * max (x v) 0 = |x v| + x v := by
    by_cases h : 0 ≤ x v
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right (le_of_not_ge h), abs_of_nonpos (le_of_not_ge h)]; ring
  simp only [supply, l1, mul_sum, hx, sum_add_distrib]

theorem two_supply_of_sum_zero {x : V → ℝ} (hx : ∑ v, x v = 0) :
    2 * supply x = l1 x := by rw [two_supply, hx, add_zero]

theorem sum_subset_le_l1 (x : V → ℝ) (S : Finset V) : ∑ v ∈ S, x v ≤ l1 x := by
  calc
    _ ≤ ∑ v ∈ S, |x v| := sum_le_sum fun v _ => le_abs_self _
    _ ≤ ∑ v, |x v| := sum_le_univ_sum_of_nonneg fun v => abs_nonneg _

omit [Fintype V] in
theorem PairBounded.arc_le_two {G : WeightedDiGraph V} (hG : PairBounded G)
    (u v : V) : G.c u v ≤ 2 := by
  linarith [hG u v, G.nonneg v u]

/-- Residual capacity after a feasible signed flow. -/
def residual (G : WeightedDiGraph V) (f : V → V → ℝ) (hf : G.Feasible f) :
    WeightedDiGraph V where
  c u v := G.c u v - f u v
  nonneg u v := sub_nonneg.mpr (hf.2 u v)
  diag v := by rw [G.diag, hf.1.self]; ring

omit [Fintype V] in
@[simp] theorem residual_c (G : WeightedDiGraph V) (f : V → V → ℝ)
    (hf : G.Feasible f) (u v : V) :
    (residual G f hf).c u v = G.c u v - f u v := rfl

omit [Fintype V] in
/-- A reverse residual arc never changes the total capacity of its pair. -/
theorem residual_pair_sum (G : WeightedDiGraph V) (f : V → V → ℝ)
    (hf : G.Feasible f) (u v : V) :
    (residual G f hf).c u v + (residual G f hf).c v u = G.c u v + G.c v u := by
  simp only [residual_c, hf.1 u v]
  ring

omit [Fintype V] in
theorem PairBounded.residual {G : WeightedDiGraph V} (hG : PairBounded G)
    (f : V → V → ℝ) (hf : G.Feasible f) : PairBounded (residual G f hf) := by
  intro u v
  rw [residual_pair_sum]
  exact hG u v

/-- Divergence of the capacity representation. -/
def capacityDiv (G : WeightedDiGraph V) (v : V) : ℝ := ∑ w, (G.c v w - G.c w v)

theorem residual_capacityDiv (G : WeightedDiGraph V) (f : V → V → ℝ)
    (hf : G.Feasible f) (v : V) :
    capacityDiv (residual G f hf) v = capacityDiv G v - 2 * netOut f v := by
  simp only [capacityDiv, residual_c, hf.1 v, netOut, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro w _
  ring

omit [Fintype V] in
/-- A target feasible flow minus the current flow is feasible in the full
residual network.  This supplies the remaining-deficit witness. -/
theorem residual_difference_feasible (G : WeightedDiGraph V)
    (f g : V → V → ℝ) (hf : G.Feasible f) (hg : G.Feasible g) :
    (residual G f hf).Feasible (fun u v => g u v - f u v) := by
  refine ⟨?_, ?_⟩
  · intro u v
    dsimp
    rw [hf.1 u v, hg.1 u v]
    ring
  · intro u v
    change g u v - f u v ≤ G.c u v - f u v
    exact sub_le_sub_right (hg.2 u v) _

theorem residual_difference_divergence (f g : V → V → ℝ) (v : V) :
    netOut (fun u w => g u w - f u w) v = netOut g v - netOut f v := by
  simp only [netOut, sum_sub_distrib]

omit [Fintype V] in
/-- Comparing two representations with the same pair totals gives a feasible
repair flow.  This is an existence witness, not an oracle used by a program. -/
theorem comparison_feasible (G H : WeightedDiGraph V)
    (htot : ∀ u v, G.c u v + G.c v u = H.c u v + H.c v u) :
    G.Feasible (fun u v => G.c u v - H.c u v) := by
  refine ⟨?_, ?_⟩
  · intro u v
    dsimp
    linarith [htot u v]
  · intro u v
    dsimp
    linarith [H.nonneg u v]

theorem comparison_divergence (G H : WeightedDiGraph V)
    (htot : ∀ u v, G.c u v + G.c v u = H.c u v + H.c v u) (v : V) :
    netOut (fun u w => G.c u w - H.c u w) v =
      (capacityDiv G v - capacityDiv H v) / 2 := by
  rw [capacityDiv, capacityDiv, ← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro w _
  linarith [htot v w]

end CutQueryComplexity.DirectedUnitST.Repair

#print axioms CutQueryComplexity.DirectedUnitST.Repair.two_supply_of_sum_zero
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residual_pair_sum
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residual_capacityDiv
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residual_difference_feasible
#print axioms CutQueryComplexity.DirectedUnitST.Repair.comparison_feasible
#print axioms CutQueryComplexity.DirectedUnitST.Repair.comparison_divergence
