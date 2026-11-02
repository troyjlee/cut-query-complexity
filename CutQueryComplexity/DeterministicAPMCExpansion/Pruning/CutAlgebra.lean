import CutQueryComplexity.Graph.InducedCut
import CutQueryComplexity.AllPairsAudit.CutAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# The structural fake-edge pruning inequalities

This module proves consequences of a minimum source shore in the explicit
two-star network. It does not select that shore or assume a query algorithm.
The eventual exact-flow program must produce the minimum-shore certificate.
Comparisons with the source-only shore and with an enlarged source shore
give the size, boundary and induced-expansion conclusions directly.

The vertex type here is the current part, not the ambient padded graph.
`D` represents the explicit fake multigraph; its degree/count identities
will be proved from that public multigraph before this lemma is consumed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open Finset WeightedGraph AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Mathematical value of the source shore `{s} union P`. Original edges
have capacity R, source capacities are a, and sink capacities are b/2.
This definition is used in specifications, not to inspect an unknown graph. -/
def starObjective (J : WeightedGraph V) (a : V → ℝ) (b R : ℝ) (P : Finset V) : ℝ :=
  (∑ v, a v) - (∑ v ∈ P, a v) + (b / 2) * P.card + R * J.cut P

def IsPruningMinimizer (J : WeightedGraph V) (a : V → ℝ) (b R : ℝ)
    (P : Finset V) : Prop :=
  ∀ S : Finset V, starObjective J a b R P ≤ starObjective J a b R S

/-- Exact augmented expansion, retaining the actual fake cut term. -/
def FakeCertificate (J D : WeightedGraph V) (b R : ℝ) : Prop :=
  ∀ T : Finset V,
    b * min (T.card : ℝ) (Tᶜ.card : ℝ) ≤ R * J.cut T + D.cut T

theorem subset_compl_disjoint {P T : Finset V} (hT : T ⊆ Pᶜ) : Disjoint P T := by
  apply disjoint_left.mpr
  intro v hvP hvT
  exact (mem_compl.mp (hT hvT)) hvP

theorem cut_eq_local_add_cross (J : WeightedGraph V) {P T : Finset V}
    (hT : T ⊆ Pᶜ) :
    J.cut T = J.localCut Pᶜ T + J.cross T P := by
  have hsplit : Tᶜ = P ∪ (Pᶜ \ T) := by
    ext v
    have ht : v ∈ T → v ∉ P := fun hv => mem_compl.mp (hT hv)
    simp only [mem_compl, mem_union, mem_sdiff]
    tauto
  have hd : Disjoint P (Pᶜ \ T) := by
    apply disjoint_left.mpr
    intro v hvP hv
    exact (mem_compl.mp (mem_sdiff.mp hv).1) hvP
  rw [← J.cross_compl T, hsplit, J.cross_union_right T P (Pᶜ \ T) hd,
    J.localCut_of_subset hT]
  exact add_comm _ _

theorem cut_union_eq (J : WeightedGraph V) {P T : Finset V} (hT : T ⊆ Pᶜ) :
    J.cut (P ∪ T) = J.cut P + J.localCut Pᶜ T - J.cross T P := by
  have h := J.cross_eq_three_cuts (subset_compl_disjoint hT)
  rw [J.cross_comm P T, cut_eq_local_add_cross J hT] at h
  linarith

theorem starObjective_union (J : WeightedGraph V) (a : V → ℝ) (b R : ℝ)
    {P T : Finset V} (hT : T ⊆ Pᶜ) :
    starObjective J a b R (P ∪ T) = starObjective J a b R P - (∑ v ∈ T, a v) +
      (b / 2) * T.card + R * J.localCut Pᶜ T - R * J.cross T P := by
  have hd := subset_compl_disjoint hT
  simp only [starObjective, sum_union hd, card_union_of_disjoint hd, Nat.cast_add,
    cut_union_eq J hT]
  ring

/-- Comparing the minimum source shore to the source-only shore. -/
theorem prune_source_comparison (J : WeightedGraph V) (a : V → ℝ) (b R : ℝ)
    {P : Finset V} (hmin : IsPruningMinimizer J a b R P) :
    (b / 2) * P.card + R * J.cut P ≤ ∑ v ∈ P, a v := by
  have h := hmin ∅
  simp only [starObjective, sum_empty, sub_zero, card_empty, Nat.cast_zero,
    mul_zero, J.cut_empty, add_zero] at h
  linarith

/-- The conservation inequality also follows directly from minimum-cut
optimality by comparing P with P union T. -/
theorem prune_flow_drain (J : WeightedGraph V) (a : V → ℝ) (b R : ℝ)
    {P T : Finset V} (hmin : IsPruningMinimizer J a b R P) (hT : T ⊆ Pᶜ) :
    (∑ v ∈ T, a v) + R * J.cross T P ≤
      (b / 2) * T.card + R * J.localCut Pᶜ T := by
  have h := hmin (P ∪ T)
  rw [starObjective_union J a b R hT] at h
  linarith

theorem fake_cut_le_degree_sum (D : WeightedGraph V) (T : Finset V) :
    D.cut T ≤ ∑ v ∈ T, D.degree v := by
  change (∑ v ∈ T, incident D v Tᶜ) ≤ ∑ v ∈ T, D.degree v
  exact sum_le_sum fun v _ => incident_le_degree D v Tᶜ

theorem degree_sum_le_total (D : WeightedGraph V) (P : Finset V) :
    (∑ v ∈ P, D.degree v) ≤ ∑ v, D.degree v :=
  sum_le_sum_of_subset_of_nonneg (subset_univ P) (fun v _ _ => degree_nonneg D v)

theorem prune_size_boundary (J D : WeightedGraph V) (b R M : ℝ) (hR : 0 ≤ R)
    (hM : (∑ v, D.degree v) = 2 * M) {P : Finset V}
    (hmin : IsPruningMinimizer J D.degree b R P) :
    (b / 2) * P.card + R * J.cut P ≤ ∑ v ∈ P, D.degree v ∧
    (∑ v ∈ P, D.degree v) ≤ 2 * M ∧ b * P.card ≤ 4 * M := by
  have hs := prune_source_comparison J D.degree b R hmin
  have htotal : (∑ v ∈ P, D.degree v) ≤ 2 * M := by
    simpa only [hM] using degree_sum_le_total D P
  have hcut := mul_nonneg hR (J.cut_nonneg P)
  exact ⟨hs, htotal, by linarith⟩

theorem prune_boundary_strict (J D : WeightedGraph V) (b R : ℝ)
    (hb : 0 < b) (hR : 0 < R) (hdegree : ∀ v, D.degree v ≤ R * b)
    {P : Finset V} (hmin : IsPruningMinimizer J D.degree b R P)
    (hP : P.Nonempty) : J.cut P < b * P.card := by
  have hs := prune_source_comparison J D.degree b R hmin
  have hsum : (∑ v ∈ P, D.degree v) ≤ (P.card : ℝ) * (R * b) := by
    calc
      _ ≤ ∑ _v ∈ P, R * b := sum_le_sum fun v _ => hdegree v
      _ = _ := by simp [nsmul_eq_mul]
  have hp : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hpos : 0 < (b / 2) * P.card := mul_pos (by positivity) hp
  have hscaled : R * J.cut P < R * (b * P.card) := by nlinarith
  exact lt_of_mul_lt_mul_left hscaled hR.le

theorem prune_boundary_le (J D : WeightedGraph V) (b R : ℝ)
    (hb : 0 < b) (hR : 0 < R) (hdegree : ∀ v, D.degree v ≤ R * b)
    {P : Finset V} (hmin : IsPruningMinimizer J D.degree b R P) :
    J.cut P ≤ b * P.card := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simp
  · exact (prune_boundary_strict J D b R hb hR hdegree hmin hP).le

theorem prune_large_remainder (J D : WeightedGraph V) (b R M : ℝ)
    (hb : 0 < b) (hR : 0 ≤ R) (hM : (∑ v, D.degree v) = 2 * M)
    (hbudget : 32 * M ≤ (Fintype.card V : ℝ) * b) {P : Finset V}
    (hmin : IsPruningMinimizer J D.degree b R P) : 8 * P.card ≤ Fintype.card V := by
  have hsize := (prune_size_boundary J D b R M hR hM hmin).2.2
  have hscaled : b * (8 * (P.card : ℝ)) ≤ b * Fintype.card V := by nlinarith
  have h := le_of_mul_le_mul_left hscaled hb
  exact_mod_cast h

theorem prune_small_shore_expansion (J D : WeightedGraph V) (b R : ℝ)
    (hcertificate : FakeCertificate J D b R) {P T : Finset V}
    (hmin : IsPruningMinimizer J D.degree b R P) (hT : T ⊆ Pᶜ)
    (hsmall : T.card ≤ (Pᶜ \ T).card) :
    b * T.card ≤ 4 * R * J.localCut Pᶜ T := by
  have hsub : Pᶜ \ T ⊆ Tᶜ := by
    intro v hv
    exact mem_compl.mpr (mem_sdiff.mp hv).2
  have hc : T.card ≤ Tᶜ.card := hsmall.trans (card_le_card hsub)
  have hcR : (T.card : ℝ) ≤ Tᶜ.card := by exact_mod_cast hc
  have hexpand := hcertificate T
  rw [min_eq_left hcR, cut_eq_local_add_cross J hT] at hexpand
  have hfake := fake_cut_le_degree_sum D T
  have hdrain := prune_flow_drain J D.degree b R hmin hT
  nlinarith

theorem localCut_sdiff (J : WeightedGraph V) {U T : Finset V} (hT : T ⊆ U) :
    J.localCut U (U \ T) = J.localCut U T := by
  have hback : U \ (U \ T) = T := by
    ext v
    have ht : v ∈ T → v ∈ U := fun h => hT h
    simp only [mem_sdiff]
    tauto
  rw [J.localCut_of_subset sdiff_subset, J.localCut_of_subset hT, hback]
  exact J.cross_comm _ _

/-- Expansion is in the induced retained graph, not in the ambient graph
with the retained vertices merely designated as terminals. -/
theorem prune_induced_expansion (J D : WeightedGraph V) (b R : ℝ)
    (hcertificate : FakeCertificate J D b R) {P : Finset V}
    (hmin : IsPruningMinimizer J D.degree b R P) :
    ∀ T : Finset V, T ⊆ Pᶜ →
      b * min (T.card : ℝ) ((Pᶜ \ T).card : ℝ) ≤ 4 * R * J.localCut Pᶜ T := by
  intro T hT
  by_cases hsmall : T.card ≤ (Pᶜ \ T).card
  · have hsmallR : (T.card : ℝ) ≤ (Pᶜ \ T).card := by exact_mod_cast hsmall
    rw [min_eq_left hsmallR]
    exact prune_small_shore_expansion J D b R hcertificate hmin hT hsmall
  · have hback : Pᶜ \ (Pᶜ \ T) = T := by
      ext v
      have ht : v ∈ T → v ∉ P := fun h => mem_compl.mp (hT h)
      simp only [mem_sdiff, mem_compl]
      tauto
    have hs : (Pᶜ \ T).card ≤ (Pᶜ \ (Pᶜ \ T)).card := by rw [hback]; omega
    have he := prune_small_shore_expansion J D b R hcertificate hmin sdiff_subset hs
    rw [localCut_sdiff J hT] at he
    have hsmallNat : (Pᶜ \ T).card ≤ T.card := by omega
    have hsmallR : ((Pᶜ \ T).card : ℝ) ≤ T.card := by exact_mod_cast hsmallNat
    simpa only [min_eq_right hsmallR] using he

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_flow_drain
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_size_boundary
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_boundary_strict
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_large_remainder
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_induced_expansion
