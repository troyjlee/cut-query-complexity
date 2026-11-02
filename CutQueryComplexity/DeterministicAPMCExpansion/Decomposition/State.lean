import CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.LocalNode

/-!
# Public structural state of the recursive producer

These invariants concern only explicit finite sets and the recorded work
tree. They hold for every answer transcript, including an aborted one.
Semantic claims about input cuts are proved separately on honest inputs.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

open Finset Pruning
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {R : ℕ}

theorem shrinkStep_mono_child {a parent small large : ℕ}
    (h : ShrinkStep a parent large) (hsize : small ≤ large) :
    ShrinkStep a parent small := by
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left a hsize) parent).trans h

theorem shrinkStep_zero (R q : ℕ) (hR : 1 ≤ R) : ShrinkStep (64 * R) q 0 := by
  have h := Nat.mul_le_mul_right q (show 1 ≤ 64 * R by omega)
  simpa only [ShrinkStep, Nat.mul_zero, Nat.zero_add, Nat.one_mul] using h

structure State (R : ℕ) (W : Finset V) where
  tree : SplitTree V
  work : WorkTree V
  complete : Bool
  covers : tree.vertices = W
  disjoint : tree.DisjointSplits
  work_subset : work.vertices ⊆ W
  work_covered : work.Covered
  work_shrinks : work.Shrinks (64 * R)
  work_positive : work.Positive

namespace State

def finish (R : ℕ) (W : Finset V) (complete : Bool := true) : State R W where
  tree := .leaf W
  work := .done
  complete := complete
  covers := rfl
  disjoint := trivial
  work_subset := empty_subset _
  work_covered := trivial
  work_shrinks := trivial
  work_positive := trivial

/-- A query was made at this node, so even an invalid output has one active
work node. It cannot disappear from cost accounting. -/
def abortActive (R : ℕ) (hR : 1 ≤ R) (W : Finset V) (hW : 0 < W.card) : State R W where
  tree := .leaf W
  work := .call W .done .done
  complete := false
  covers := rfl
  disjoint := trivial
  work_subset := le_rfl
  work_covered := ⟨disjoint_empty_left _, by simp [WorkTree.vertices], trivial, trivial⟩
  work_shrinks := ⟨shrinkStep_zero R W.card hR, shrinkStep_zero R W.card hR, trivial, trivial⟩
  work_positive := ⟨hW, trivial, trivial⟩

def join (W L U : Finset V) (hW : 0 < W.card) (hd : Disjoint L U)
    (hu : L ∪ U = W) (left : State R L) (right : State R U)
    (hl : ShrinkStep (64 * R) W.card left.work.vertices.card)
    (hr : ShrinkStep (64 * R) W.card right.work.vertices.card) : State R W where
  tree := .branch left.tree right.tree
  work := .call W left.work right.work
  complete := left.complete && right.complete
  covers := by simpa only [SplitTree.vertices, left.covers, right.covers] using hu
  disjoint := ⟨by simpa only [left.covers, right.covers] using hd, left.disjoint, right.disjoint⟩
  work_subset := le_rfl
  work_covered := ⟨hd.mono left.work_subset right.work_subset,
    by simpa only [← hu] using union_subset_union left.work_subset right.work_subset,
    left.work_covered, right.work_covered⟩
  work_shrinks := ⟨hl, hr, left.work_shrinks, right.work_shrinks⟩
  work_positive := ⟨hW, left.work_positive, right.work_positive⟩

def split (W L : Finset V) (hW : 0 < W.card) (hL : L ⊆ W)
    (left : State R L) (right : State R (W \ L))
    (hl : ShrinkStep (64 * R) W.card L.card)
    (hr : ShrinkStep (64 * R) W.card (W \ L).card) : State R W :=
  join W L (W \ L) hW disjoint_sdiff_self_right (union_sdiff_of_subset hL) left right
    (shrinkStep_mono_child hl (card_le_card left.work_subset))
    (shrinkStep_mono_child hr (card_le_card right.work_subset))

def prune (hR : 1 ≤ R) (W P : Finset V) (hW : 0 < W.card) (hP : P ⊆ W)
    (child : State R P) (hsize : 8 * P.card ≤ W.card) : State R W :=
  join W P (W \ P) hW disjoint_sdiff_self_right (union_sdiff_of_subset hP)
    child (finish R (W \ P))
    (shrinkStep_mono_child (pruned_child_shrink hR hsize) (card_le_card child.work_subset))
    (shrinkStep_zero R W.card hR)

theorem mass_le (R N : ℕ) (hR : 1 ≤ R) {W : Finset V} (result : State R W)
    (hW : W.card ≤ N) :
    result.work.mass ≤ (64 * R) * Nat.clog 2 (N + 1) * N :=
  result.work.mass_le_clog (64 * R) N (by omega) result.work_covered
    result.work_shrinks result.work_positive ((card_le_card result.work_subset).trans hW)

end State
end
end CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State.mass_le
