import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Leakage
import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.CutAlgebra

/-!
# Offline pruning of the explicit matching graph

This is a finite public computation, after four balanced subgames. The graph
argument is the already revealed matching multigraph. It is never the hidden
input graph. Each step removes a nonempty small shore whose induced cut has
expansion below one-half. A cardinality fuel makes the search total.

The proved invariant keeps fewer than one-quarter of the vertices removed.
A final matching sends each removed vertex into the retained set. Together
with half-expansion there, this gives full expansion one-quarter.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Unit expansion on shores between one-quarter and one-half of the vertices. -/
def QuarterDense (H : WeightedGraph V) : Prop :=
  ∀ S : Finset V, Fintype.card V ≤ 4 * S.card →
    2 * S.card ≤ Fintype.card V → (S.card : ℝ) ≤ H.cut S

structure SparseHalf (H : WeightedGraph V) (removed S : Finset V) : Prop where
  subset : S ⊆ removedᶜ
  nonempty : S.Nonempty
  half : 2 * S.card ≤ removedᶜ.card
  sparse : 2 * H.localCut removedᶜ S < (S.card : ℝ)

def chooseSmall (H : WeightedGraph V) (removed : Finset V) :
    Option {S : Finset V // SparseHalf H removed S} :=
  if h : ∃ S, SparseHalf H removed S then
    some ⟨Classical.choose h, Classical.choose_spec h⟩
  else none

theorem chooseSmall_none_iff (H : WeightedGraph V) (removed : Finset V) :
    chooseSmall H removed = none ↔ ∀ S, ¬ SparseHalf H removed S := by
  unfold chooseSmall
  split_ifs with h
  · simp only [Option.some_ne_none, false_iff]
    exact not_forall.mpr ⟨Classical.choose h, not_not.mpr (Classical.choose_spec h)⟩
  · simp only [true_iff]
    exact fun S hs => h ⟨S, hs⟩

def peelRun (H : WeightedGraph V) : ℕ → Finset V → Finset V
  | 0, removed => removed
  | fuel + 1, removed =>
      match chooseSmall H removed with
      | none => removed
      | some chosen => peelRun H fuel (removed ∪ chosen.val)

def peeled (H : WeightedGraph V) : Finset V := peelRun H (Fintype.card V) ∅

theorem peel_step_card {P S : Finset V} (hS : S ⊆ Pᶜ) :
    (P ∪ S)ᶜ.card + S.card = Pᶜ.card := by
  have hu := card_union_of_disjoint (Pruning.subset_compl_disjoint hS)
  have hp := card_le_univ P
  have hps := card_le_univ (P ∪ S)
  simp only [card_compl] at *
  omega

structure PeelInvariant (H : WeightedGraph V) (removed : Finset V) : Prop where
  boundary : 2 * H.cut removed ≤ (removed.card : ℝ)
  small : 4 * removed.card < Fintype.card V

theorem peel_step_invariant (H : WeightedGraph V) (hdense : QuarterDense H)
    {P S : Finset V} (hP : PeelInvariant H P) (hS : SparseHalf H P S) :
    PeelInvariant H (P ∪ S) := by
  have hdis := Pruning.subset_compl_disjoint hS.subset
  have hcard := card_union_of_disjoint hdis
  have hcardR : ((P ∪ S).card : ℝ) = (P.card : ℝ) + S.card := by
    exact_mod_cast hcard
  have hcross := H.cross_nonneg S P
  have hboundary : 2 * H.cut (P ∪ S) ≤ ((P ∪ S).card : ℝ) := by
    rw [Pruning.cut_union_eq H hS.subset]
    have hp := hP.boundary
    have hs := hS.sparse
    linarith
  refine ⟨hboundary, ?_⟩
  by_contra hsmall
  have hquarter : Fintype.card V ≤ 4 * (P ∪ S).card := by omega
  have hhalfS := hS.half
  have hp := hP.small
  have hpbound := card_le_univ P
  have hrbound := card_le_univ (P ∪ S)
  have hn : 0 < Fintype.card V := by omega
  have hpositive : (0 : ℝ) < (P ∪ S).card := by
    exact_mod_cast (show 0 < (P ∪ S).card by omega)
  by_cases hhalf : 2 * (P ∪ S).card ≤ Fintype.card V
  · have hd := hdense (P ∪ S) hquarter hhalf
    linarith
  · have hquarter' : Fintype.card V ≤ 4 * (P ∪ S)ᶜ.card := by
      simp only [card_compl] at *
      omega
    have hhalf' : 2 * (P ∪ S)ᶜ.card ≤ Fintype.card V := by
      simp only [card_compl]
      omega
    have hd := hdense (P ∪ S)ᶜ hquarter' hhalf'
    rw [H.cut_compl] at hd
    have hcomp : ((P ∪ S)ᶜ.card : ℝ) + (P ∪ S).card = Fintype.card V := by
      exact_mod_cast (show (P ∪ S)ᶜ.card + (P ∪ S).card = Fintype.card V by
        simp only [card_compl]; omega)
    have hnew : 2 * (P ∪ S).card ≤ Fintype.card V + P.card := by
      simp only [card_compl] at hhalfS
      omega
    have hnewR : 2 * ((P ∪ S).card : ℝ) ≤ (Fintype.card V : ℝ) + P.card := by
      exact_mod_cast hnew
    have hpR : 4 * (P.card : ℝ) < Fintype.card V := by exact_mod_cast hp
    have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    linarith

theorem peelRun_invariant (H : WeightedGraph V) (hdense : QuarterDense H)
    (fuel : ℕ) (P : Finset V) (hP : PeelInvariant H P) :
    PeelInvariant H (peelRun H fuel P) := by
  induction fuel generalizing P with
  | zero => exact hP
  | succ fuel ih =>
      rw [peelRun]
      cases hc : chooseSmall H P with
      | none => exact hP
      | some chosen => exact ih _ (peel_step_invariant H hdense hP chosen.property)

theorem peelRun_stable (H : WeightedGraph V) (fuel : ℕ) (P : Finset V)
    (hroom : Pᶜ.card ≤ fuel) : ∀ S, ¬ SparseHalf H (peelRun H fuel P) S := by
  induction fuel generalizing P with
  | zero =>
      intro S hs
      change SparseHalf H P S at hs
      have hle := card_le_card hs.subset
      have hpos := hs.nonempty.card_pos
      omega
  | succ fuel ih =>
      rw [peelRun]
      cases hc : chooseSmall H P with
      | none => exact (chooseSmall_none_iff H P).mp hc
      | some chosen =>
          apply ih
          have hstep := peel_step_card chosen.property.subset
          have hpos := chosen.property.nonempty.card_pos
          omega

theorem peeled_invariant (H : WeightedGraph V) (hdense : QuarterDense H)
    (hN : 0 < Fintype.card V) : PeelInvariant H (peeled H) := by
  apply peelRun_invariant H hdense
  exact ⟨by simp, by simpa using hN⟩

theorem peeled_stable (H : WeightedGraph V) : ∀ S, ¬ SparseHalf H (peeled H) S :=
  peelRun_stable H (Fintype.card V) ∅ (by simp)

theorem stable_small_expansion (H : WeightedGraph V) {P S : Finset V}
    (hstable : ∀ T, ¬ SparseHalf H P T) (hS : S ⊆ Pᶜ)
    (hsmall : S.card ≤ (Pᶜ \ S).card) :
    (S.card : ℝ) ≤ 2 * H.localCut Pᶜ S := by
  rcases S.eq_empty_or_nonempty with rfl | hnonempty
  · simp [WeightedGraph.localCut]
  · have hhalf : 2 * S.card ≤ Pᶜ.card := by
      have hcard := card_sdiff_add_card_eq_card hS
      omega
    by_contra hcut
    exact hstable S ⟨hS, hnonempty, hhalf, lt_of_not_ge hcut⟩

theorem stable_expansion (H : WeightedGraph V) {P S : Finset V}
    (hstable : ∀ T, ¬ SparseHalf H P T) (hS : S ⊆ Pᶜ) :
    min (S.card : ℝ) ((Pᶜ \ S).card : ℝ) ≤ 2 * H.localCut Pᶜ S := by
  by_cases hsmall : S.card ≤ (Pᶜ \ S).card
  · have hsmallR : (S.card : ℝ) ≤ (Pᶜ \ S).card := by exact_mod_cast hsmall
    rw [min_eq_left hsmallR]
    exact stable_small_expansion H hstable hS hsmall
  · have hback : Pᶜ \ (Pᶜ \ S) = S := by
      ext v
      have hsub : v ∈ S → v ∉ P := fun h => mem_compl.mp (hS h)
      simp only [mem_sdiff, mem_compl]
      tauto
    have hrev : (Pᶜ \ S).card ≤ (Pᶜ \ (Pᶜ \ S)).card := by rw [hback]; omega
    have h := stable_small_expansion H hstable sdiff_subset hrev
    rw [Pruning.localCut_sdiff H hS] at h
    have hsmallR : ((Pᶜ \ S).card : ℝ) ≤ S.card := by
      exact_mod_cast (show (Pᶜ \ S).card ≤ S.card by omega)
    simpa only [min_eq_right hsmallR] using h

/-- An internal endpoint in `P` either contributes a crossing matching edge
or is paired with a vertex of the shore's retained part. -/
theorem Matching.cut_ge_removed_shore (M : Matching V) (P T : Finset V)
    (hout : ∀ v ∈ P, M.mate v ∉ P) :
    (T.card : ℝ) - 2 * (T ∩ Pᶜ).card ≤ M.graph.cut T := by
  let A := T ∩ Pᶜ
  let B := A.image M.mate
  let C := T.filter (fun v => M.mate v ∉ T)
  have hcover : T ⊆ (A ∪ B) ∪ C := by
    intro v hv
    by_cases hvP : v ∈ P
    · by_cases hmT : M.mate v ∈ T
      · apply mem_union_left
        apply mem_union_right
        apply mem_image.mpr
        exact ⟨M.mate v, mem_inter.mpr ⟨hmT, mem_compl.mpr (hout v hvP)⟩,
          M.involutive v⟩
      · exact mem_union_right _ (mem_filter.mpr ⟨hv, hmT⟩)
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hv, mem_compl.mpr hvP⟩))
  have hB : B.card = A.card := card_image_of_injective A M.mate.injective
  have hcard : T.card ≤ 2 * A.card + C.card := by
    have h1 := card_le_card hcover
    have h2 := card_union_le (A ∪ B) C
    have h3 := card_union_le A B
    omega
  have hC : (C.card : ℝ) = M.graph.cut T := by
    rw [Matching.cut_eq_indicator]
    calc
      _ = ∑ _v ∈ C, (1 : ℝ) := by simp
      _ = _ := by simp only [C, sum_filter, ite_not]
  have hcardR : (T.card : ℝ) ≤ 2 * (A.card : ℝ) + C.card := by exact_mod_cast hcard
  change (T.card : ℝ) - 2 * A.card ≤ M.graph.cut T
  linarith

theorem pruned_final_matching_small (H : WeightedGraph V) (hdense : QuarterDense H)
    (hN : 0 < Fintype.card V) (M : Matching V)
    (hout : ∀ v ∈ peeled H, M.mate v ∉ peeled H) (T : Finset V)
    (hhalf : 2 * T.card ≤ Fintype.card V) :
    (T.card : ℝ) ≤ 4 * (M.graph.cut T + H.cut T) := by
  let P := peeled H
  let S := T ∩ Pᶜ
  have hp := peeled_invariant H hdense hN
  have hS : S ⊆ Pᶜ := inter_subset_right
  have hlocal := stable_expansion H (peeled_stable H) hS
  have hmono : H.localCut Pᶜ S ≤ H.cut T := by
    change H.localCut Pᶜ (T ∩ Pᶜ) ≤ H.cut T
    rw [H.localCut_inter]
    simpa only [H.localCut_univ] using H.localCut_mono (subset_univ Pᶜ) T
  have hparts : ((Pᶜ \ S).card : ℝ) =
      (Fintype.card V : ℝ) - P.card - S.card := by
    have h1 := card_sdiff_add_card_eq_card hS
    have h2 : Pᶜ.card + P.card = Fintype.card V := by
      have := card_le_univ P
      simp only [card_compl]
      omega
    have h1R : ((Pᶜ \ S).card : ℝ) + S.card = Pᶜ.card := by exact_mod_cast h1
    have h2R : (Pᶜ.card : ℝ) + P.card = Fintype.card V := by exact_mod_cast h2
    linarith
  change min (S.card : ℝ) ((Pᶜ \ S).card : ℝ) ≤ 2 * H.localCut Pᶜ S at hlocal
  rw [hparts] at hlocal
  have hcut : min (S.card : ℝ) ((Fintype.card V : ℝ) - P.card - S.card) ≤
      2 * H.cut T := by linarith
  have hmatch := M.cut_ge_removed_shore P T hout
  have hhalfR : 2 * (T.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hhalf
  have hpR : 4 * (P.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hp.small.le
  have hx : (S.card : ℝ) ≤ T.card := by
    exact_mod_cast card_le_card (show S ⊆ T from inter_subset_left)
  have h := pruning_finish_quarter (Fintype.card V) P.card T.card S.card
    (H.cut T) (M.graph.cut T) hhalfR hpR hx (H.cut_nonneg T) (M.graph.cut_nonneg T)
    hcut hmatch
  linarith

/-- The quarter constant is explicit; this is one full game, before the
four-fold normalization used by the final public cut-player. -/
theorem pruned_final_matching_quarter (H : WeightedGraph V) (hdense : QuarterDense H)
    (hN : 0 < Fintype.card V) (M : Matching V)
    (hout : ∀ v ∈ peeled H, M.mate v ∉ peeled H) (T : Finset V) :
    min (T.card : ℝ) (Tᶜ.card : ℝ) ≤ 4 * (M.graph.cut T + H.cut T) := by
  by_cases hhalf : 2 * T.card ≤ Fintype.card V
  · have hc : (T.card : ℝ) ≤ Tᶜ.card := by
      have hbound := card_le_univ T
      exact_mod_cast (show T.card ≤ Tᶜ.card by simp only [card_compl]; omega)
    rw [min_eq_left hc]
    exact pruned_final_matching_small H hdense hN M hout T hhalf
  · have hbound := card_le_univ T
    have hhalf' : 2 * Tᶜ.card ≤ Fintype.card V := by simp only [card_compl]; omega
    have hc : (Tᶜ.card : ℝ) ≤ T.card := by
      exact_mod_cast (show Tᶜ.card ≤ T.card by simp only [card_compl]; omega)
    rw [min_eq_right hc]
    simpa only [M.graph.cut_compl, H.cut_compl] using
      pruned_final_matching_small H hdense hN M hout Tᶜ hhalf'

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.peel_step_invariant
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.peeled_stable
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pruned_final_matching_quarter
