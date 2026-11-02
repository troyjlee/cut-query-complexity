import CutQueryComplexity.Certificate.Flow
import CutQueryComplexity.TwoRespecting.Tree
import Mathlib.Tactic

set_option autoImplicit false

/-! # The fundamental-shore model for a specified Gomory–Hu tree

Tree edges are indexed by nonroot vertices, even when their weights vanish.
The certificate is one finite query family chosen before every unrestricted
nonnegative real-weighted competitor. Complete pair learning is provided as
an actual quadratic certificate primitive, not a weighted-star oracle.
-/

namespace CutQueryComplexity.Certificate.GomoryHu

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def edges (T : TwoRespecting.RootedTree V) : Finset V := univ.erase T.root

@[simp] theorem mem_edges (T : TwoRespecting.RootedTree V) (v : V) :
    v ∈ edges T ↔ v ≠ T.root := by simp [edges]

theorem card_edges (T : TwoRespecting.RootedTree V) :
    (edges T).card = Fintype.card V - 1 := by simp [edges]

def degree (T : TwoRespecting.RootedTree V) (u : V) : ℕ :=
  ((edges T).filter fun v => v = u ∨ T.parent v = u).card

def positiveWeights (T : TwoRespecting.RootedTree V) (tau : V → ℝ) : Finset ℝ :=
  ((edges T).filter fun v => 0 < tau v).image tau

def fundamentalQueries (T : TwoRespecting.RootedTree V) : Finset (Finset V) :=
  (edges T).image T.subtree

theorem fundamentalQueries_card (T : TwoRespecting.RootedTree V) :
    (fundamentalQueries T).card ≤ Fintype.card V - 1 :=
  (card_image_le).trans_eq (card_edges T)

theorem fundamental_mem (T : TwoRespecting.RootedTree V) {v : V}
    (hv : v ≠ T.root) : T.subtree v ∈ fundamentalQueries T :=
  mem_image_of_mem _ ((mem_edges T v).mpr hv)

theorem parent_not_mem_subtree (T : TwoRespecting.RootedTree V) {v : V}
    (hv : v ≠ T.root) : T.parent v ∉ T.subtree v := by
  intro h
  have hd := (TwoRespecting.RootedTree.mem_subtree.mp h).depth_le
  have hp := T.depth_parent v hv
  omega

theorem subtree_separates (T : TwoRespecting.RootedTree V) {v : V}
    (hv : v ≠ T.root) :
    v ∈ T.subtree v ∧ T.parent v ∉ T.subtree v :=
  ⟨TwoRespecting.RootedTree.self_mem_subtree (T := T) v, parent_not_mem_subtree T hv⟩

/-- The structural degree sum counts every nonroot parent edge twice. -/
theorem sum_degree (T : TwoRespecting.RootedTree V) :
    (∑ u : V, degree T u) = 2 * (Fintype.card V - 1) := by
  have hcount (v : V) (hv : v ∈ edges T) :
      (∑ u : V, if v = u ∨ T.parent v = u then (1 : ℕ) else 0) = 2 := by
    have hne : v ≠ T.parent v :=
      (TwoRespecting.RootedTree.parent_ne_self (T := T) ((mem_edges T v).mp hv)).symm
    calc
      _ = ∑ u ∈ ({v, T.parent v} : Finset V), (1 : ℕ) := by
        rw [← sum_filter]
        congr 1
        ext u
        simp [eq_comm]
      _ = 2 := by simp [hne]
  calc
    (∑ u : V, degree T u) =
        ∑ u : V, ∑ v ∈ edges T, if v = u ∨ T.parent v = u then (1 : ℕ) else 0 := by
      simp [degree, ← sum_filter]
    _ = ∑ v ∈ edges T, ∑ u : V,
        if v = u ∨ T.parent v = u then (1 : ℕ) else 0 := sum_comm
    _ = ∑ _v ∈ edges T, (2 : ℕ) := sum_congr rfl hcount
    _ = 2 * (Fintype.card V - 1) := by simp [card_edges, Nat.mul_comm]

/-- The supplied fundamental shores, including their values and endpoint optimality. -/
def FundamentalCorrect (G : WeightedGraph V) (T : TwoRespecting.RootedTree V)
    (tau : V → ℝ) : Prop :=
  ∀ v, v ≠ T.root → G.cut (T.subtree v) = tau v ∧
    IsSTMinCut G v (T.parent v) (T.subtree v)

/-- A simultaneous certificate; the competitor can add arbitrary original nonedges. -/
def TreeCertificate (G : WeightedGraph V) (T : TwoRespecting.RootedTree V)
    (tau : V → ℝ) (Q : Finset (Finset V)) : Prop :=
  fundamentalQueries T ⊆ Q ∧
  ∀ H : WeightedGraph V, Certificate.Consistent G H Q → FundamentalCorrect H T tau

theorem FundamentalCorrect.nonneg {G : WeightedGraph V}
    {T : TwoRespecting.RootedTree V} {tau : V → ℝ}
    (hT : FundamentalCorrect G T tau) {v : V} (hv : v ≠ T.root) : 0 ≤ tau v := by
  rw [← (hT v hv).1]
  exact G.cut_nonneg _

theorem FundamentalCorrect.lower {G : WeightedGraph V}
    {T : TwoRespecting.RootedTree V} {tau : V → ℝ}
    (hT : FundamentalCorrect G T tau) {v : V} (hv : v ≠ T.root)
    {S : Finset V} (hs : v ∈ S) (ht : T.parent v ∉ S) : tau v ≤ G.cut S := by
  rw [← (hT v hv).1]
  exact (hT v hv).2.2.2 S hs ht

theorem TreeCertificate.mono {G : WeightedGraph V}
    {T : TwoRespecting.RootedTree V} {tau : V → ℝ} {Q Q' : Finset (Finset V)}
    (h : TreeCertificate G T tau Q) (hQ : Q ⊆ Q') : TreeCertificate G T tau Q' :=
  ⟨h.1.trans hQ, fun H hH => h.2 H (hH.mono hQ)⟩

/-- If all supplied weights vanish, fundamental queries alone certify the tree. -/
theorem zero_tree_certificate {G : WeightedGraph V}
    {T : TwoRespecting.RootedTree V} {tau : V → ℝ}
    (hT : FundamentalCorrect G T tau) (hz : ∀ v, v ≠ T.root → tau v = 0) :
    TreeCertificate G T tau (fundamentalQueries T) := by
  refine ⟨subset_refl _, fun H hH v hv => ?_⟩
  have hc : H.cut (T.subtree v) = tau v :=
    (hH _ (fundamental_mem T hv)).trans (hT v hv).1
  refine ⟨hc, (subtree_separates T hv).1, (subtree_separates T hv).2, fun S _ _ => ?_⟩
  rw [hc, hz v hv]
  exact H.cut_nonneg S

/-- Pair queries include singleton queries by allowing the two indices to coincide. -/
def allPairQueries (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  (univ : Finset (V × V)).image fun p => ({p.1, p.2} : Finset V)

theorem allPairQueries_card : (allPairQueries V).card ≤ (Fintype.card V) ^ 2 := by
  exact (card_image_le).trans_eq (by simp [Fintype.card_prod, pow_two])

theorem pair_mem_allPairQueries (u v : V) : {u, v} ∈ allPairQueries V :=
  mem_image_of_mem _ (mem_univ (u, v))

theorem singleton_mem_allPairQueries (v : V) : {v} ∈ allPairQueries V := by
  simpa using pair_mem_allPairQueries v v

/-- Complete pair learning determines even zero pairs against all competitors. -/
theorem eq_of_consistent_allPairQueries {G H : WeightedGraph V}
    (h : Certificate.Consistent G H (allPairQueries V)) : H = G := by
  ext u v
  by_cases huv : u = v
  · subst v; simp [H.diag, G.diag]
  · exact h.w_eq huv (singleton_mem_allPairQueries u) (singleton_mem_allPairQueries v)
      (pair_mem_allPairQueries u v)

/-- A substantive quadratic baseline, useful for the completely learned star graphs. -/
theorem exists_quadratic_certificate (G : WeightedGraph V)
    (T : TwoRespecting.RootedTree V) (tau : V → ℝ) (hT : FundamentalCorrect G T tau) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ (Fintype.card V) ^ 2 + (Fintype.card V - 1) ∧ TreeCertificate G T tau Q := by
  refine ⟨allPairQueries V ∪ fundamentalQueries T,
    (card_union_le _ _).trans (Nat.add_le_add allPairQueries_card (fundamentalQueries_card T)),
    subset_union_right, fun H hH => ?_⟩
  have he := eq_of_consistent_allPairQueries (hH.mono subset_union_left)
  subst H
  exact hT

end
end CutQueryComplexity.Certificate.GomoryHu

#print axioms CutQueryComplexity.Certificate.GomoryHu.sum_degree
#print axioms CutQueryComplexity.Certificate.GomoryHu.zero_tree_certificate
#print axioms CutQueryComplexity.Certificate.GomoryHu.eq_of_consistent_allPairQueries
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_quadratic_certificate
