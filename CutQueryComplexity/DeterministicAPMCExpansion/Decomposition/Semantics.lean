import CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.Program

/-!
# Semantic invariants produced by honest recursive executions

The structural guards use only public finite sets. Exact-flow and matching
correctness prove that honest inputs pass those guards. The leaf property
is stated in the existing additive-expansion interface, with parameters
`b = 2t`, `Rcert = 8R`, and `betaCert = t²`; its shaving scale is `32Rt²`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

open Finset WeightedGraph Pruning CutMatching
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem small_leaf_additive (G : WeightedGraph V) (R t : ℕ) (hR : 1 ≤ R)
    (ht : 1 ≤ t) (W : Finset V) (hsmall : W.card ≤ 64 * R) (hcube : W.card ≤ t ^ 3) :
    AdditiveExpands G W (2 * t) (8 * R) (t ^ 2) := by
  have hsize : W.card ≤ 16 * R * t ^ 2 := by
    by_cases ht1 : t = 1
    · subst t
      norm_num at hcube ⊢
      omega
    · have ht2 : 2 ≤ t := by omega
      have hs : 4 ≤ t ^ 2 := by nlinarith
      have hm := Nat.mul_le_mul_left (16 * R) hs
      nlinarith
  intro S hS
  have hs : (S.card : ℝ) ≤ 16 * (R : ℝ) * (t : ℝ) ^ 2 := by
    exact_mod_cast (card_le_card hS).trans hsize
  have hm := (min_le_left (S.card : ℝ) ((W \ S).card : ℝ)).trans hs
  have hn := mul_nonneg (show (0 : ℝ) ≤ 8 * R by positivity) (G.localCut_nonneg W S)
  have he := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 2 * t by positivity)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  nlinarith

theorem liftShore_sdiff (W : Finset V) (S T : Finset (PartVertex W)) :
    liftShore W (S \ T) = liftShore W S \ liftShore W T := map_sdiff _ _

theorem partGraph_localCut (G : WeightedGraph V) (W : Finset V)
    (U S : Finset (PartVertex W)) :
    (partGraph G W).localCut U S = G.localCut (liftShore W U) (liftShore W S) := by
  simp only [localCut, partGraph_cross, liftShore, map_inter, map_sdiff]

theorem pruned_leaf_additive (G : WeightedGraph V) (R t : ℕ) (W : Finset V)
    (P : Finset (PartVertex W))
    (hexpand : ∀ S : Finset (PartVertex W), S ⊆ Pᶜ →
      (2 * (t : ℝ)) * min (S.card : ℝ) ((Pᶜ \ S).card : ℝ) ≤
        4 * (R : ℝ) * (partGraph G W).localCut Pᶜ S) :
    AdditiveExpands G (W \ liftShore W P) (2 * t) (8 * R) (t ^ 2) := by
  intro T hT
  let S := restrictShore W T
  have hTW : T ⊆ W := hT.trans sdiff_subset
  have heS : liftShore W S = T := by
    simpa only [S, liftShore_restrictShore] using inter_eq_right.mpr hTW
  have hs : S ⊆ Pᶜ := by
    intro v hv
    apply mem_compl.mpr
    intro hp
    have hvT : v.val ∈ T := (mem_restrictShore W T v).mp hv
    have hvP := (mem_liftShore W P v).mpr hp
    exact (mem_sdiff.mp (hT hvT)).2 hvP
  have hcard : S.card = T.card := by rw [← liftShore_card W S, heS]
  have hdiff : (Pᶜ \ S).card = ((W \ liftShore W P) \ T).card := by
    rw [← liftShore_card W (Pᶜ \ S), liftShore_sdiff, liftShore_compl, heS]
  have he := hexpand S hs
  rw [hcard, hdiff, partGraph_localCut, liftShore_compl, heS] at he
  have hn := G.localCut_nonneg (W \ liftShore W P) T
  have hnR := mul_nonneg (show (0 : ℝ) ≤ 4 * R by positivity) hn
  have herr : (0 : ℝ) ≤ 2 * (8 * (R : ℝ)) * (t : ℝ) ^ 2 * (2 * t) := by positivity
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  nlinarith

theorem splitGuard_of_correct (G : WeightedGraph V) (R t : ℕ) (hR : 1 ≤ R)
    (W : Finset V) (hactive : 64 * R < W.card) (P : Finset (PartVertex W))
    (h : SplitCorrect (partGraph G W) (2 * t) (localTolerance (Fintype.card (PartVertex W)) R) P) :
    SplitGuard R W (liftShore W P) := by
  have hl : localTolerance W.card R < (liftShore W P).card := by
    simpa only [partVertex_card, liftShore_card] using (show localTolerance
      (Fintype.card (PartVertex W)) R < P.card by exact_mod_cast h.1)
  have hr : localTolerance W.card R < (W \ liftShore W P).card := by
    rw [← liftShore_compl, liftShore_card]
    simpa only [partVertex_card] using (show localTolerance
      (Fintype.card (PartVertex W)) R < Pᶜ.card by exact_mod_cast h.2.1)
  have hsum : (liftShore W P).card + (W \ liftShore W P).card = W.card := by
    have hc := card_sdiff_add_card_eq_card (liftShore_subset W P)
    omega
  have hshrink := split_child_shrink hR hactive hsum hl hr
  exact ⟨by omega, by omega, hshrink⟩

theorem pruneGuard_of_correct (W : Finset V) (hW : 0 < W.card)
    (P : Finset (PartVertex W)) (h : 8 * P.card ≤ Fintype.card (PartVertex W)) :
    PruneGuard W (liftShore W P) := by
  have hs : 8 * (liftShore W P).card ≤ W.card := by
    simpa only [liftShore_card, partVertex_card] using h
  exact ⟨hs, by omega⟩

theorem split_cross_of_correct (G : WeightedGraph V) (R t : ℕ)
    (W : Finset V) (P : Finset (PartVertex W))
    (h : SplitCorrect (partGraph G W) (2 * t) (localTolerance (Fintype.card (PartVertex W)) R) P) :
    G.cross (liftShore W P) (W \ liftShore W P) ≤
      (2 * (t : ℝ)) * min ((liftShore W P).card : ℝ) ((W \ liftShore W P).card : ℝ) := by
  have hc := h.2.2.le
  rw [partGraph_cut] at hc
  simpa only [← liftShore_compl, liftShore_card, Nat.cast_mul, Nat.cast_ofNat] using hc

theorem prune_cross_of_correct (G : WeightedGraph V) (t : ℕ)
    (W : Finset V) (P : Finset (PartVertex W))
    (hsize : 8 * P.card ≤ Fintype.card (PartVertex W))
    (hcut : (partGraph G W).cut P ≤ (2 * (t : ℝ)) * P.card) :
    G.cross (liftShore W P) (W \ liftShore W P) ≤
      (2 * (t : ℝ)) * min ((liftShore W P).card : ℝ) ((W \ liftShore W P).card : ℝ) := by
  have hsum := card_sdiff_add_card_eq_card (liftShore_subset W P)
  have hs : 8 * (liftShore W P).card ≤ W.card := by
    simpa only [liftShore_card, partVertex_card] using hsize
  have hm : ((liftShore W P).card : ℝ) ≤ ((W \ liftShore W P).card : ℝ) := by
    exact_mod_cast (show (liftShore W P).card ≤ (W \ liftShore W P).card by omega)
  rw [min_eq_left hm, liftShore_card]
  simpa only [partGraph_cut] using hcut

def SplitTree.ExpandingLeaves (G : WeightedGraph V) (R t : ℕ) : SplitTree V → Prop
  | .leaf W => AdditiveExpands G W (2 * t) (8 * R) (t ^ 2)
  | .branch left right => left.ExpandingLeaves G R t ∧ right.ExpandingLeaves G R t

def State.Correct (G : WeightedGraph V) {R : ℕ} (t : ℕ) {W : Finset V}
    (result : State R W) : Prop :=
  result.complete = true ∧ result.tree.SparseSplits G (2 * t) ∧
    result.tree.ExpandingLeaves G R t

theorem State.finish_correct (G : WeightedGraph V) (R t : ℕ) (W : Finset V)
    (h : AdditiveExpands G W (2 * t) (8 * R) (t ^ 2)) :
    (State.finish R W).Correct G t := ⟨rfl, trivial, h⟩

theorem State.join_correct (G : WeightedGraph V) {R : ℕ} (t : ℕ)
    (W L U : Finset V) (hW : 0 < W.card) (hd : Disjoint L U) (hu : L ∪ U = W)
    (left : State R L) (right : State R U)
    (hl : ShrinkStep (64 * R) W.card left.work.vertices.card)
    (hr : ShrinkStep (64 * R) W.card right.work.vertices.card)
    (hcross : G.cross L U ≤ (2 * (t : ℝ)) * min (L.card : ℝ) (U.card : ℝ))
    (hleft : left.Correct G t) (hright : right.Correct G t) :
    (State.join W L U hW hd hu left right hl hr).Correct G t := by
  refine ⟨?_, ?_, hleft.2.2, hright.2.2⟩
  · change left.complete && right.complete = true
    rw [hleft.1, hright.1]
    rfl
  · change Disjoint left.tree.vertices right.tree.vertices ∧
      G.cross left.tree.vertices right.tree.vertices ≤
        ((2 * t : ℕ) : ℝ) * min (left.tree.vertices.card : ℝ) (right.tree.vertices.card : ℝ) ∧
      left.tree.SparseSplits G (2 * t) ∧ right.tree.SparseSplits G (2 * t)
    rw [left.covers, right.covers]
    exact ⟨hd, by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcross,
      hleft.2.1, hright.2.1⟩

theorem run_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (N R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hN : N ≤ t ^ 3)
    (hrounds : ∀ q ≤ N, normalizedRounds (q * (2 * t)) ≤ R)
    (fuel : ℕ) (W : Finset V) (hW : W.card ≤ N) (hfuel : W.card ≤ fuel) :
    ((run R t hR fuel W).eval G.cut).Correct G t := by
  induction fuel generalizing W with
  | zero =>
      have hs : W.card ≤ 64 * R := by omega
      simpa only [run, decide_eq_true hs, Prog.eval_pure] using
        State.finish_correct G R t W (small_leaf_additive G R t hR ht W hs (hW.trans hN))
  | succ fuel ih =>
      by_cases hs : W.card ≤ 64 * R
      · simpa only [run, dif_pos hs, Prog.eval_pure] using
          State.finish_correct G R t W (small_leaf_additive G R t hR ht W hs (hW.trans hN))
      · have hpos : 0 < W.card := by omega
        have hn := partNode_correct G hG R t hR ht W hpos (hW.trans hN) (hrounds W.card hW)
        simp only [run, dif_neg hs, Prog.eval_bind]
        cases he : (partNode R t W).eval G.cut with
        | invalid =>
            have hf : False := by simpa only [he, NodeCorrect] using hn
            exact hf.elim
        | split P =>
            have hc : SplitCorrect (partGraph G W) (2 * t)
                (localTolerance (Fintype.card (PartVertex W)) R) P := by
              simpa only [he, NodeCorrect] using hn
            have hg := splitGuard_of_correct G R t hR W (by omega) P hc
            have hl := ih (liftShore W P) ((card_le_card (liftShore_subset W P)).trans hW)
              (by have hp := hg.1; omega)
            have hr := ih (W \ liftShore W P) ((card_le_card sdiff_subset).trans hW)
              (by have hp := hg.2.1; omega)
            simp only [dif_pos hg, Prog.eval_bind, Prog.eval_map]
            exact State.join_correct G t W _ _ hpos disjoint_sdiff_self_right
              (union_sdiff_of_subset (liftShore_subset W P)) _ _ _ _
              (split_cross_of_correct G R t W P hc) hl hr
        | pruned P =>
            have hc : NodeCorrect (partGraph G W) R t (.pruned P) := by
              simpa only [he] using hn
            have hg := pruneGuard_of_correct W hpos P hc.1
            have hl := ih (liftShore W P) ((card_le_card (liftShore_subset W P)).trans hW)
              (by have hp := hg.2; omega)
            have hr := State.finish_correct G R t (W \ liftShore W P)
              (pruned_leaf_additive G R t W P hc.2.2)
            simp only [dif_pos hg, Prog.eval_map]
            exact State.join_correct G t W _ _ hpos disjoint_sdiff_self_right
              (union_sdiff_of_subset (liftShore_subset W P)) _ _ _ _
              (prune_cross_of_correct G t W P hc.1 hc.2.1) hl hr

theorem decomposition_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hN : Fintype.card V ≤ t ^ 3)
    (hrounds : ∀ q ≤ Fintype.card V, normalizedRounds (q * (2 * t)) ≤ R) :
    ((decomposition (V := V) R t hR).eval G.cut).Correct G t := by
  rw [decomposition, program_eval]
  exact run_correct G hG (Fintype.card V) R t hR ht hN hrounds
    (Fintype.card V) univ (by simp) (by simp)

end
end CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.small_leaf_additive
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.pruned_leaf_additive
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.run_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.decomposition_correct
