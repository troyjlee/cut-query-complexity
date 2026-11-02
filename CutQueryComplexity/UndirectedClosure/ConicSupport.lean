import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Basic.Real.Basic

/-! # Finite nonnegative representations with independent support

A nonnegative finite linear combination can be represented on a subset of
linearly independent columns.  The proof removes one coefficient at a time
along a dependence, using the smallest nonnegative ratio.  It does not assume
a linear-programming oracle or compactness of the feasible coefficient set.
-/

set_option autoImplicit false

namespace CutQueryComplexity.UndirectedClosure

open Finset

variable {E M : Type*} [DecidableEq E] [AddCommGroup M] [Module ℝ M]

omit [DecidableEq E] in
/-- A finite dependence can be oriented to have a positive coefficient. -/
theorem exists_positive_dependence (v : E → M) {s : Finset E}
    (h : ¬ LinearIndepOn ℝ v (s : Set E)) :
    ∃ d : E → ℝ, (∑ e ∈ s, d e • v e) = 0 ∧ ∃ e ∈ s, 0 < d e := by
  obtain ⟨d, hd, e, he, hde⟩ := not_linearIndepOn_finset_iff.mp h
  rcases lt_or_gt_of_ne hde with hn | hp
  · refine ⟨fun i => -d i, ?_, e, he, neg_pos.mpr hn⟩
    simp only [neg_smul, sum_neg_distrib, hd, neg_zero]
  · exact ⟨d, hd, e, he, hp⟩

/-- Removing one coefficient of a dependent nonnegative representation
preserves both its value and nonnegativity. -/
theorem nonneg_representation_erase (v : E → M) {s : Finset E}
    (h : ¬ LinearIndepOn ℝ v (s : Set E)) (x : E → ℝ)
    (hx : ∀ e ∈ s, 0 ≤ x e) :
    ∃ e ∈ s, ∃ y : E → ℝ,
      (∀ i ∈ s.erase e, 0 ≤ y i) ∧
      (∑ i ∈ s.erase e, y i • v i) = ∑ i ∈ s, x i • v i := by
  classical
  obtain ⟨d, hd, e, he, hde⟩ := exists_positive_dependence v h
  let p := s.filter (fun i => 0 < d i)
  obtain ⟨i₀, hi₀, hmin⟩ := p.exists_min_image (fun i => x i / d i)
    ⟨e, mem_filter.mpr ⟨he, hde⟩⟩
  have his : i₀ ∈ s := (mem_filter.mp hi₀).1
  have hdi : 0 < d i₀ := (mem_filter.mp hi₀).2
  let y : E → ℝ := fun i => x i - x i₀ / d i₀ * d i
  have hyzero : y i₀ = 0 := by simp [y, ne_of_gt hdi]
  refine ⟨i₀, his, y, ?_, ?_⟩
  · intro i hi
    have his' : i ∈ s := mem_of_mem_erase hi
    change 0 ≤ x i - x i₀ / d i₀ * d i
    apply sub_nonneg.mpr
    by_cases hpos : 0 < d i
    · exact (le_div_iff₀ hpos).mp (hmin i (mem_filter.mpr ⟨his', hpos⟩))
    · exact (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (hx i₀ his) (le_of_lt hdi)) (le_of_not_gt hpos)).trans (hx i his')
  · calc
      (∑ i ∈ s.erase i₀, y i • v i) = ∑ i ∈ s, y i • v i :=
        sum_erase _ (by rw [hyzero, zero_smul])
      _ = ∑ i ∈ s, x i • v i := by
        simp only [y, sub_smul, mul_smul, sum_sub_distrib, ← smul_sum,
          hd, smul_zero, sub_zero]

/-- Conic support reduction, with the surviving columns independent.  The
indices remain a subset of the original finite index set. -/
theorem exists_nonneg_independent_representation (v : E → M) (s : Finset E)
    (x : E → ℝ) (hx : ∀ e ∈ s, 0 ≤ x e) :
    ∃ t : Finset E, ∃ y : E → ℝ,
      t ⊆ s ∧ LinearIndepOn ℝ v (t : Set E) ∧
      (∀ e ∈ t, 0 ≤ y e) ∧
      (∑ e ∈ t, y e • v e) = ∑ e ∈ s, x e • v e := by
  classical
  induction s using Finset.strongInductionOn generalizing x with
  | _ s ih =>
    by_cases h : LinearIndepOn ℝ v (s : Set E)
    · exact ⟨s, x, Subset.refl _, h, hx, rfl⟩
    · obtain ⟨e, he, y, hy, hsum⟩ := nonneg_representation_erase v h x hx
      obtain ⟨t, z, hts, ht, hz, htz⟩ := ih (s.erase e) (erase_ssubset he) y hy
      exact ⟨t, z, hts.trans (erase_subset _ _), ht, hz, htz.trans hsum⟩

/-- A nonnegative finite combination needs at most the ambient dimension
many columns, without changing its value. -/
theorem exists_nonneg_sparse_representation [Module.Finite ℝ M]
    (v : E → M) (s : Finset E) (x : E → ℝ) (hx : ∀ e ∈ s, 0 ≤ x e) :
    ∃ t : Finset E, ∃ y : E → ℝ,
      t ⊆ s ∧ t.card ≤ Module.finrank ℝ M ∧
      (∀ e ∈ t, 0 ≤ y e) ∧
      (∑ e ∈ t, y e • v e) = ∑ e ∈ s, x e • v e := by
  obtain ⟨t, y, hts, ht, hy, hsum⟩ :=
    exists_nonneg_independent_representation v s x hx
  refine ⟨t, y, hts, ?_, hy, hsum⟩
  have hlin : LinearIndependent ℝ (fun e : t => v e) := ht
  simpa only [Fintype.card_coe] using hlin.fintype_card_le_finrank

/-- The finite row form: any feasible nonnegative system with `card I`
equations has a representation using at most `card I` columns. -/
theorem exists_nonneg_sparse_rows {I : Type*} [Fintype E] [Fintype I]
    (A : E → I → ℝ) (a : I → ℝ)
    (hfeas : ∃ x : E → ℝ, (∀ e, 0 ≤ x e) ∧
      ∀ i, (∑ e, x e * A e i) = a i) :
    ∃ t : Finset E, ∃ y : E → ℝ,
      t.card ≤ Fintype.card I ∧ (∀ e, 0 ≤ y e) ∧
      ∀ i, (∑ e ∈ t, y e * A e i) = a i := by
  classical
  obtain ⟨x, hx, ha⟩ := hfeas
  obtain ⟨t, z, _, ht, hz, hsum⟩ := exists_nonneg_sparse_representation
    A univ x (fun e _ => hx e)
  refine ⟨t, fun e => if e ∈ t then z e else 0, ?_, ?_, ?_⟩
  · simpa only [Module.finrank_fintype_fun_eq_card] using ht
  · intro e
    change 0 ≤ if e ∈ t then z e else 0
    split_ifs with he
    · exact hz e he
    · exact le_rfl
  · intro i
    have heq : (∑ e ∈ t, z e * A e i) = ∑ e, x e * A e i := by
      simpa only [sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hsum i
    calc
      (∑ e ∈ t, (if e ∈ t then z e else 0) * A e i) =
          ∑ e ∈ t, z e * A e i := by
        apply sum_congr rfl
        intro e he
        rw [ite_eq_left he]
      _ = a i := heq.trans (ha i)

#print axioms exists_positive_dependence
#print axioms nonneg_representation_erase
#print axioms exists_nonneg_independent_representation
#print axioms exists_nonneg_sparse_representation
#print axioms exists_nonneg_sparse_rows

end CutQueryComplexity.UndirectedClosure
