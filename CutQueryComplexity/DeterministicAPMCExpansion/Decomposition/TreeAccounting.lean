import CutQueryComplexity.DeterministicAPMCExpansion.Basic
import CutQueryComplexity.AllPairs.Partition

/-!
# Accounting for the public binary decomposition tree

Both children are charged, including games that end with a split. The bound
uses the total number of leaves, not an assumed logarithmic recursion depth.
The future query producer must establish `SparseSplits` from its measured cut
outputs; none of these tree predicates is a query-program input.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

inductive SplitTree (V : Type) where
  | leaf : Finset V → SplitTree V
  | branch : SplitTree V → SplitTree V → SplitTree V

namespace SplitTree

def vertices : SplitTree V → Finset V
  | .leaf W => W
  | .branch left right => left.vertices ∪ right.vertices

def leaves : SplitTree V → ℕ
  | .leaf _ => 1
  | .branch left right => left.leaves + right.leaves

def nodes : SplitTree V → ℕ
  | .leaf _ => 1
  | .branch left right => left.nodes + right.nodes + 1

def DisjointSplits : SplitTree V → Prop
  | .leaf _ => True
  | .branch left right =>
      Disjoint left.vertices right.vertices ∧ left.DisjointSplits ∧ right.DisjointSplits

def LargeLeaves (β : ℕ) : SplitTree V → Prop
  | .leaf W => β < W.card
  | .branch left right => left.LargeLeaves β ∧ right.LargeLeaves β

def SparseSplits (G : WeightedGraph V) (b : ℕ) : SplitTree V → Prop
  | .leaf _ => True
  | .branch left right =>
      Disjoint left.vertices right.vertices ∧
      G.cross left.vertices right.vertices ≤
        (b : ℝ) * min (left.vertices.card : ℝ) (right.vertices.card : ℝ) ∧
      left.SparseSplits G b ∧ right.SparseSplits G b

def leafBoundary (G : WeightedGraph V) : SplitTree V → ℝ
  | .leaf W => G.cut W
  | .branch left right => left.leafBoundary G + right.leafBoundary G

theorem nodes_add_one (tree : SplitTree V) : tree.nodes + 1 = 2 * tree.leaves := by
  induction tree with
  | leaf W => rfl
  | branch left right hl hr => simp only [nodes, leaves]; omega

theorem leaves_pos (tree : SplitTree V) : 0 < tree.leaves := by
  induction tree with
  | leaf W => exact Nat.zero_lt_one
  | branch left right hl hr => simp only [leaves]; omega

theorem largeLeaves_mass (tree : SplitTree V) (β : ℕ)
    (hd : tree.DisjointSplits) (hl : tree.LargeLeaves β) :
    tree.leaves * (β + 1) ≤ tree.vertices.card := by
  induction tree with
  | leaf W =>
      simpa only [leaves, vertices, one_mul] using (Nat.succ_le_of_lt hl)
  | branch left right ihl ihr =>
      obtain ⟨hdisj, hdl, hdr⟩ := hd
      have hleft := ihl hdl hl.1
      have hright := ihr hdr hl.2
      simp only [vertices, card_union_of_disjoint hdisj, leaves, Nat.add_mul]
      exact Nat.add_le_add hleft hright

/-- A denominator-free bound on every game node, successful or split-ending. -/
theorem node_mass_bound (tree : SplitTree V) (β : ℕ)
    (hd : tree.DisjointSplits) (hl : tree.LargeLeaves β) :
    (tree.nodes + 1) * (β + 1) ≤ 2 * tree.vertices.card := by
  rw [nodes_add_one]
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left 2 (tree.largeLeaves_mass β hd hl)

theorem sparseSplits_disjoint (tree : SplitTree V) (G : WeightedGraph V) (b : ℕ)
    (h : tree.SparseSplits G b) : tree.DisjointSplits := by
  induction tree with
  | leaf W => trivial
  | branch left right ihl ihr => exact ⟨h.1, ihl h.2.2.1, ihr h.2.2.2⟩

/-- The ceiling-log potential charges sparse splits even on a deep tree. -/
theorem leafBoundary_le (tree : SplitTree V) (G : WeightedGraph V) (b : ℕ)
    (h : tree.SparseSplits G b) :
    tree.leafBoundary G ≤ G.cut tree.vertices +
      2 * (b : ℝ) * tree.vertices.card * Nat.clog 2 tree.vertices.card := by
  induction tree with
  | leaf W =>
      change G.cut W ≤ G.cut W + 2 * (b : ℝ) * W.card * Nat.clog 2 W.card
      exact le_add_of_nonneg_right (by positivity)
  | branch left right ihl ihr =>
      obtain ⟨hdisj, hcross, hleft, hright⟩ := h
      have hl := ihl hleft
      have hr := ihr hright
      have hc := G.cross_eq_three_cuts hdisj
      have hp := AllPairs.clog_potential_split left.vertices.card right.vertices.card
      have hpR :
          (left.vertices.card : ℝ) * Nat.clog 2 left.vertices.card +
          (right.vertices.card : ℝ) * Nat.clog 2 right.vertices.card +
          min (left.vertices.card : ℝ) (right.vertices.card : ℝ) ≤
          ((left.vertices.card : ℝ) + right.vertices.card) *
            Nat.clog 2 (left.vertices.card + right.vertices.card) := by
        exact_mod_cast hp
      have hscaled := mul_le_mul_of_nonneg_left hpR (show 0 ≤ 2 * (b : ℝ) by positivity)
      change left.leafBoundary G + right.leafBoundary G ≤
        G.cut (left.vertices ∪ right.vertices) +
          2 * (b : ℝ) * (left.vertices ∪ right.vertices).card *
            Nat.clog 2 (left.vertices ∪ right.vertices).card
      rw [card_union_of_disjoint hdisj, Nat.cast_add]
      linarith

theorem root_boundary_le (tree : SplitTree V) (G : WeightedGraph V) (b : ℕ)
    (h : tree.SparseSplits G b) (hroot : tree.vertices = univ) :
    tree.leafBoundary G ≤ 2 * (b : ℝ) * Fintype.card V * Nat.clog 2 (Fintype.card V) := by
  simpa only [hroot, G.cut_univ, card_univ, zero_add] using tree.leafBoundary_le G b h

end SplitTree
end
end CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.node_mass_bound
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.leafBoundary_le
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.root_boundary_le
