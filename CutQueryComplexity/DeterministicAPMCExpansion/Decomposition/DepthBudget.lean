import CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.TreeAccounting
import Mathlib.Data.Nat.Log

/-!
# Integer shrink and mass bounds for the active recursion

Finished output blocks need no further work. The active work tree therefore
records only nodes where a game or pruning flow runs. Its child root sets are
disjoint subsets of the current part; finished blocks are omitted.

The integer shrink inequality avoids logarithms of rational factors. Every
`a` steps halves the part size, so `a * clog 2 (N+1)` steps force size zero.
These are analysis lemmas; the decomposition producer must establish their
structural invariants from its actual split and pruning outputs.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

open Finset
open scoped Classical
noncomputable section

/-- Equivalent to `child ≤ (1 - 1/a) * parent` when `a > 0`, without division. -/
def ShrinkStep (a parent child : ℕ) : Prop := a * child + parent ≤ a * parent

theorem shrinkStep_le {a parent child : ℕ} (ha : 0 < a)
    (h : ShrinkStep a parent child) : child ≤ parent := by
  have hm : a * child ≤ a * parent := (Nat.le_add_right _ _).trans h
  exact le_of_mul_le_mul_left hm ha

theorem shrinkStep_of_discard {a parent child β : ℕ}
    (hsize : child + β ≤ parent) (htolerance : parent ≤ a * β) :
    ShrinkStep a parent child := by
  have h := Nat.mul_le_mul_left a hsize
  dsimp [ShrinkStep]
  nlinarith

theorem shrinkStep_of_half {a parent child : ℕ} (ha : 2 ≤ a)
    (hhalf : 2 * child ≤ parent) : ShrinkStep a parent child := by
  have h1 := Nat.mul_le_mul_left a hhalf
  have h2 := Nat.mul_le_mul_right parent ha
  dsimp [ShrinkStep]
  nlinarith only [h1, h2]

def ShrinkingSequence (a : ℕ) (size : ℕ → ℕ) : Prop :=
  ∀ k, ShrinkStep a (size k) (size (k + 1))

theorem ShrinkingSequence.shift {a : ℕ} {size : ℕ → ℕ}
    (h : ShrinkingSequence a size) (offset : ℕ) :
    ShrinkingSequence a (fun k => size (offset + k)) := by
  intro k
  simpa only [Nat.add_assoc] using h (offset + k)

theorem ShrinkingSequence.antitone {a : ℕ} {size : ℕ → ℕ} (ha : 0 < a)
    (h : ShrinkingSequence a size) : Antitone size := by
  apply antitone_nat_of_succ_le
  intro k
  exact shrinkStep_le ha (h k)

theorem ShrinkingSequence.linear_drop {a : ℕ} {size : ℕ → ℕ} (ha : 0 < a)
    (h : ShrinkingSequence a size) (k : ℕ) :
    (a + k) * size k ≤ a * size 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := h k
      have hmono := shrinkStep_le ha hstep
      have hmul := Nat.mul_le_mul_left k hmono
      dsimp [ShrinkStep] at hstep
      nlinarith

theorem ShrinkingSequence.half_block {a : ℕ} {size : ℕ → ℕ} (ha : 0 < a)
    (h : ShrinkingSequence a size) : 2 * size a ≤ size 0 := by
  have hh := h.linear_drop ha a
  have hm : a * (2 * size a) ≤ a * size 0 := by nlinarith
  exact le_of_mul_le_mul_left hm ha

theorem ShrinkingSequence.pow_drop {a : ℕ} {size : ℕ → ℕ} (ha : 0 < a)
    (h : ShrinkingSequence a size) (k : ℕ) :
    2 ^ k * size (a * k) ≤ size 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hh := (h.shift (a * k)).half_block ha
      have hm := Nat.mul_le_mul_left (2 ^ k) hh
      simp only [Nat.add_zero] at hm
      calc
        2 ^ (k + 1) * size (a * (k + 1)) =
            2 ^ k * (2 * size (a * k + a)) := by rw [pow_succ, Nat.mul_succ]; ring
        _ ≤ 2 ^ k * size (a * k) := hm
        _ ≤ size 0 := ih

theorem ShrinkingSequence.zero_after_clog {a : ℕ} {size : ℕ → ℕ} (ha : 0 < a)
    (h : ShrinkingSequence a size) (N : ℕ) (hN : size 0 ≤ N) :
    size (a * Nat.clog 2 (N + 1)) = 0 := by
  have hp := h.pow_drop ha (Nat.clog 2 (N + 1))
  have hclog := Nat.le_pow_clog (by decide : 1 < 2) (N + 1)
  by_contra hz
  have hpos : 1 ≤ size (a * Nat.clog 2 (N + 1)) := by omega
  have hmul := Nat.mul_le_mul_left (2 ^ Nat.clog 2 (N + 1)) hpos
  simp only [Nat.mul_one] at hmul
  omega

variable {V : Type} [Fintype V] [DecidableEq V]

inductive WorkTree (V : Type) where
  | done : WorkTree V
  | call : Finset V → WorkTree V → WorkTree V → WorkTree V

namespace WorkTree

def vertices : WorkTree V → Finset V
  | .done => ∅
  | .call W _ _ => W

def depth : WorkTree V → ℕ
  | .done => 0
  | .call _ left right => 1 + max left.depth right.depth

def mass : WorkTree V → ℕ
  | .done => 0
  | .call W left right => W.card + left.mass + right.mass

def Covered : WorkTree V → Prop
  | .done => True
  | .call W left right =>
      Disjoint left.vertices right.vertices ∧ left.vertices ∪ right.vertices ⊆ W ∧
        left.Covered ∧ right.Covered

def Shrinks (a : ℕ) : WorkTree V → Prop
  | .done => True
  | .call W left right =>
      ShrinkStep a W.card left.vertices.card ∧ ShrinkStep a W.card right.vertices.card ∧
        left.Shrinks a ∧ right.Shrinks a

def Positive : WorkTree V → Prop
  | .done => True
  | .call W left right => 0 < W.card ∧ left.Positive ∧ right.Positive

def levelMass : WorkTree V → ℕ → ℕ
  | .done, _ => 0
  | .call W _ _, 0 => W.card
  | .call _ left right, k + 1 => left.levelMass k + right.levelMass k

theorem child_mass_le {W : Finset V} {left right : WorkTree V}
    (h : (WorkTree.call W left right).Covered) :
    left.vertices.card + right.vertices.card ≤ W.card := by
  rw [← card_union_of_disjoint h.1]
  exact card_le_card h.2.1

theorem levelMass_le (tree : WorkTree V) (h : tree.Covered) (k : ℕ) :
    tree.levelMass k ≤ tree.vertices.card := by
  induction tree generalizing k with
  | done => simp [levelMass, vertices]
  | call W left right ihl ihr =>
      cases k with
      | zero => exact le_rfl
      | succ k =>
          exact (Nat.add_le_add (ihl h.2.2.1 k) (ihr h.2.2.2 k)).trans (child_mass_le h)

theorem mass_le_depth (tree : WorkTree V) (h : tree.Covered) :
    tree.mass ≤ tree.depth * tree.vertices.card := by
  induction tree with
  | done => simp [mass, depth, vertices]
  | call W left right ihl ihr =>
      have hl := ihl h.2.2.1
      have hr := ihr h.2.2.2
      have hl' := Nat.mul_le_mul_right left.vertices.card (le_max_left left.depth right.depth)
      have hr' := Nat.mul_le_mul_right right.vertices.card (le_max_right left.depth right.depth)
      have hm := Nat.mul_le_mul_left (max left.depth right.depth) (child_mass_le h)
      change W.card + left.mass + right.mass ≤ (1 + max left.depth right.depth) * W.card
      nlinarith

/-- Follow a deepest active child. The sequence is zero after active work
ends, so it is defined at every natural depth. -/
def spineSize : WorkTree V → ℕ → ℕ
  | .done, _ => 0
  | .call W _ _, 0 => W.card
  | .call _ left right, k + 1 =>
      if left.depth ≤ right.depth then right.spineSize k else left.spineSize k

@[simp] theorem spineSize_zero (tree : WorkTree V) : tree.spineSize 0 = tree.vertices.card := by
  cases tree <;> rfl

theorem spineSize_positive (tree : WorkTree V) (h : tree.Positive) (k : ℕ) :
    0 < tree.spineSize k ↔ k < tree.depth := by
  induction tree generalizing k with
  | done => simp [spineSize, depth]
  | call W left right ihl ihr =>
      cases k with
      | zero =>
          change 0 < W.card ↔ 0 < 1 + max left.depth right.depth
          exact ⟨fun _ => by omega, fun _ => h.1⟩
      | succ k =>
          by_cases hd : left.depth ≤ right.depth
          · simpa only [spineSize, if_pos hd, depth, max_eq_right hd,
              Nat.add_comm 1 right.depth, Nat.add_lt_add_iff_right] using ihr h.2.2 k
          · have hd' : right.depth ≤ left.depth := le_of_lt (lt_of_not_ge hd)
            simpa only [spineSize, if_neg hd, depth, max_eq_left hd',
              Nat.add_comm 1 left.depth, Nat.add_lt_add_iff_right] using ihl h.2.1 k

theorem spineSize_shrinks (tree : WorkTree V) (a : ℕ) (h : tree.Shrinks a) :
    ShrinkingSequence a tree.spineSize := by
  intro k
  induction tree generalizing k with
  | done => simp [spineSize, ShrinkStep]
  | call W left right ihl ihr =>
      cases k with
      | zero =>
          by_cases hd : left.depth ≤ right.depth
          · simpa only [spineSize, if_pos hd, spineSize_zero] using h.2.1
          · simpa only [spineSize, if_neg hd, spineSize_zero] using h.1
      | succ k =>
          by_cases hd : left.depth ≤ right.depth
          · simpa only [spineSize, if_pos hd] using ihr h.2.2.2 k
          · simpa only [spineSize, if_neg hd] using ihl h.2.2.1 k

theorem depth_le_clog (tree : WorkTree V) (a N : ℕ) (ha : 0 < a)
    (hs : tree.Shrinks a) (hp : tree.Positive) (hN : tree.vertices.card ≤ N) :
    tree.depth ≤ a * Nat.clog 2 (N + 1) := by
  have hz := (tree.spineSize_shrinks a hs).zero_after_clog ha N
    (by simpa only [spineSize_zero] using hN)
  have hpos := tree.spineSize_positive hp (a * Nat.clog 2 (N + 1))
  rw [hz] at hpos
  omega

/-- Sum of all active part sizes, including nodes whose game returns a split. -/
theorem mass_le_clog (tree : WorkTree V) (a N : ℕ) (ha : 0 < a)
    (hc : tree.Covered) (hs : tree.Shrinks a) (hp : tree.Positive)
    (hN : tree.vertices.card ≤ N) :
    tree.mass ≤ a * Nat.clog 2 (N + 1) * N :=
  (tree.mass_le_depth hc).trans
    (Nat.mul_le_mul (tree.depth_le_clog a N ha hs hp hN) hN)

end WorkTree
end
end CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.ShrinkingSequence.zero_after_clog
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.levelMass_le
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.mass_le_depth
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.depth_le_clog
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.mass_le_clog
