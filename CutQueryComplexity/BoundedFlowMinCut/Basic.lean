import CutQueryComplexity.Problem.Basic
import CutQueryComplexity.AllPairsAudit.CutAlgebra
import CutQueryComplexity.GHReduction.Programs
import CutQueryComplexity.Primitive.Learn
import CutQueryComplexity.Primitive.BinarySearch
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Deterministic unweighted minimum cut: parameters and degrees

The algorithm of Kenneth-Mordoch (*Deterministic Global Minimum Cut Using
Õ(n^{3/2}) Cut Queries*, arXiv 2610.23461) with the degree cutoff
`cutoff n = (⌊√n⌋ + 1) · L(n)`, where `L(n) = ⌈log₂(2n+2)⌉ + 1`. Below the cutoff
a threshold certificate is recovered; above it, a dominating set and bounded
max-flows are used.

This file fixes the parameters and the degree contracts of unit graphs
(`AllPairsAudit.Unweighted`: every weight is 0 or 1). Degrees are read from
singleton cuts and decoded with `⌊·⌋₊`, which is exact on unit graphs and a
public default on any other answer.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph GHReduction

/-! ### Parameters -/

/-- The logarithmic factor `L(n) = ⌈log₂(2n+2)⌉ + 1`, as `AllPairs.budgetLog`. -/
def logFactor (n : ℕ) : ℕ := Nat.clog 2 (2 * n + 2) + 1

/-- `t(n) = ⌊√n⌋ + 1`. -/
def cutoffRoot (n : ℕ) : ℕ := Nat.sqrt n + 1

/-- The degree cutoff `t(n) · L(n)`. -/
def cutoff (n : ℕ) : ℕ := cutoffRoot n * logFactor n

theorem one_le_logFactor (n : ℕ) : 1 ≤ logFactor n := by
  unfold logFactor
  omega

theorem clog_add_one_le_logFactor (n : ℕ) : Nat.clog 2 n + 1 ≤ logFactor n :=
  Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1

theorem one_le_cutoffRoot (n : ℕ) : 1 ≤ cutoffRoot n := by
  unfold cutoffRoot
  omega

theorem le_cutoffRoot_sq (n : ℕ) : n ≤ cutoffRoot n * cutoffRoot n := by
  unfold cutoffRoot
  exact (Nat.lt_succ_sqrt n).le

theorem cutoffRoot_le_cutoff (n : ℕ) : cutoffRoot n ≤ cutoff n :=
  Nat.le_mul_of_pos_right _ (one_le_logFactor n)

/-- **High-branch balance.** Above the cutoff, a set obeying the dominating-set size
bound `(δ+1)|R| ≤ n L(n)` has at most `t(n)` elements. -/
theorem high_branch_balances {n δ r : ℕ} (hδ : cutoff n < δ)
    (hsize : (δ + 1) * r ≤ n * logFactor n) : r ≤ cutoffRoot n := by
  rcases Nat.eq_zero_or_pos r with hr | hp
  · subst hr
    exact Nat.zero_le _
  have hx : cutoffRoot n * r * logFactor n < n * logFactor n := by
    calc
      cutoffRoot n * r * logFactor n = cutoff n * r := by unfold cutoff; ring
      _ < (δ + 1) * r := Nat.mul_lt_mul_of_pos_right (by omega) hp
      _ ≤ n * logFactor n := hsize
  have hx' : cutoffRoot n * r < n := Nat.lt_of_mul_lt_mul_right hx
  have hn := le_cutoffRoot_sq n
  by_contra hr'
  have hmul := Nat.mul_le_mul_left (cutoffRoot n) (Nat.le_of_lt (Nat.lt_of_not_ge hr'))
  omega

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem searchDepth_add_one_le_logFactor :
    searchDepth V + 1 ≤ logFactor (Fintype.card V) :=
  clog_add_one_le_logFactor _

/-! ### Unit graphs and their degrees -/

/-- The neighbours of `v`: vertices joined to it by positive weight. -/
def nbrs (G : WeightedGraph V) (v : V) : Finset V := Finset.univ.filter (fun u => 0 < G.w v u)

omit [DecidableEq V] in
@[simp] theorem mem_nbrs (G : WeightedGraph V) (v u : V) : u ∈ nbrs G v ↔ 0 < G.w v u := by
  simp [nbrs]

omit [DecidableEq V] in
theorem not_mem_nbrs_self (G : WeightedGraph V) (v : V) : v ∉ nbrs G v := by
  simp [G.diag]

omit [DecidableEq V] in
theorem mem_nbrs_comm (G : WeightedGraph V) (u v : V) : u ∈ nbrs G v ↔ v ∈ nbrs G u := by
  simp [G.symm u v]

/-- The natural degree: the number of neighbours. -/
def natDegree (G : WeightedGraph V) (v : V) : ℕ := (nbrs G v).card

omit [Fintype V] [DecidableEq V] in
/-- On a unit graph, every weight is the indicator of adjacency. -/
theorem unit_w {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) (u v : V) :
    G.w u v = if 0 < G.w u v then 1 else 0 := by
  rcases hG u v with h | h <;> simp [h]

theorem unit_sum_eq_card {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) (v : V)
    (T : Finset V) : ∑ u ∈ T, G.w v u = ((nbrs G v ∩ T).card : ℝ) := by
  rw [Finset.sum_congr rfl (fun u _ => unit_w hG v u), Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext u
  simp [and_comm]

theorem degree_eq_natDegree {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) (v : V) :
    G.degree v = natDegree G v := by
  change ∑ u ∈ Finset.univ, G.w v u = _
  rw [unit_sum_eq_card hG, Finset.inter_univ]
  rfl

theorem cut_singleton_eq_natDegree {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    (v : V) : G.cut {v} = natDegree G v := by
  rw [G.cut_singleton, degree_eq_natDegree hG]

theorem natDegree_le (G : WeightedGraph V) (v : V) : natDegree G v ≤ Fintype.card V - 1 := by
  have h : nbrs G v ⊆ Finset.univ.erase v := fun u hu =>
    Finset.mem_erase.mpr ⟨fun he => not_mem_nbrs_self G v (he ▸ hu), Finset.mem_univ u⟩
  exact (Finset.card_le_card h).trans (by simp)

/-! ### Reading the degrees -/

/-- Decode a singleton answer to a degree of a simple graph on `n` vertices: a
natural number at most `n - 1` is accepted, and anything else becomes the public
default `0`. -/
def decodeDegree (n : ℕ) (a : ℝ) : ℕ :=
  if (⌊a⌋₊ : ℝ) = a ∧ ⌊a⌋₊ ≤ n - 1 then ⌊a⌋₊ else 0

/-- Every decoded degree is in range, whatever the answer. -/
theorem decodeDegree_le (n : ℕ) (a : ℝ) : decodeDegree n a ≤ n - 1 := by
  unfold decodeDegree
  split_ifs with h
  · exact h.2
  · exact Nat.zero_le _

@[simp] theorem decodeDegree_natCast {n k : ℕ} (hk : k ≤ n - 1) : decodeDegree n k = k := by
  simp [decodeDegree, hk]

/-- Query every singleton cut and decode the degrees. -/
def degreeProg : Prog (Finset V) ℝ (V → ℕ) :=
  (liftDTree (DTree.queryAll (fun v => ({v} : Finset V)) (fun _ => 0))).map
    (fun a v => decodeDegree (Fintype.card V) (a v))

theorem degreeProg_eval {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) :
    Prog.eval G.cut degreeProg = natDegree G := by
  funext v
  simp [degreeProg, DTree.eval, cut_singleton_eq_natDegree hG, natDegree_le G v]

theorem degreeProg_le (read : Finset V → ℝ) (v : V) :
    Prog.eval read (degreeProg (V := V)) v ≤ Fintype.card V - 1 := by
  simp only [degreeProg, Prog.eval_map]
  exact decodeDegree_le _ _

theorem degreeProg_cost (read : Finset V → ℝ) :
    Prog.cost read (degreeProg (V := V)) = Fintype.card V := by
  simp [degreeProg, DTree.cost]

/-- A vertex of least degree. -/
def minVertex (deg : V → ℕ) (h : (Finset.univ : Finset V).Nonempty) : V :=
  Classical.choose (Finset.exists_min_image Finset.univ deg h)

omit [DecidableEq V] in
theorem minVertex_le (deg : V → ℕ) (h : (Finset.univ : Finset V).Nonempty) (v : V) :
    deg (minVertex deg h) ≤ deg v :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ deg h)).2 v (Finset.mem_univ v)

/-- A singleton is a proper shore, so the minimum cut is at most every degree. -/
theorem mincutValue_le_natDegree {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    (hn : 2 ≤ Fintype.card V) (v : V) : mincutValue G ≤ natDegree G v := by
  rw [← cut_singleton_eq_natDegree hG]
  exact mincutValue_le G (properShore_singleton v hn)

end
end CutQueryComplexity.BoundedFlowMinCut
