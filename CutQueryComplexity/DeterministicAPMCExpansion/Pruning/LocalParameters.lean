import CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.DepthBudget

/-!
# Integer tolerance for an active part

The tolerance depends only on the current public part size and the fixed
round bound. Its two inequalities simultaneously pay for the fake edges
and force progress in both children of a failed matching game.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning

open Finset Decomposition

def localTolerance (q R : ℕ) : ℕ := q / (32 * R)

theorem localTolerance_budget (q R : ℕ) : 32 * R * localTolerance q R ≤ q := by
  simpa only [localTolerance, Nat.mul_comm] using Nat.div_mul_le_self q (32 * R)

theorem localTolerance_pos {q R : ℕ} (hR : 1 ≤ R) (hq : 64 * R < q) :
    1 ≤ localTolerance q R := by
  have hd : 0 < 32 * R := by omega
  apply (Nat.le_div_iff_mul_le hd).mpr
  omega

theorem localTolerance_shrink {q R : ℕ} (hR : 1 ≤ R) (hq : 64 * R < q) :
    q ≤ 64 * R * localTolerance q R := by
  have hd : 0 < 32 * R := by omega
  have hpos := localTolerance_pos hR hq
  have hmod := Nat.mod_lt q hd
  have hdivision := Nat.mod_add_div q (32 * R)
  have hsmall : 32 * R ≤ 32 * R * localTolerance q R := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (32 * R) hpos
  dsimp only [localTolerance] at hsmall ⊢
  nlinarith

theorem split_child_shrink {q R left right : ℕ} (hR : 1 ≤ R)
    (hq : 64 * R < q) (hsum : left + right = q)
    (hleft : localTolerance q R < left) (hright : localTolerance q R < right) :
    ShrinkStep (64 * R) q left ∧ ShrinkStep (64 * R) q right := by
  have ht := localTolerance_shrink hR hq
  constructor
  · exact shrinkStep_of_discard (by omega) ht
  · exact shrinkStep_of_discard (by omega) ht

theorem pruned_child_shrink {q R child : ℕ} (hR : 1 ≤ R)
    (hchild : 8 * child ≤ q) : ShrinkStep (64 * R) q child :=
  shrinkStep_of_half (by omega) (by omega)

end CutQueryComplexity.DeterministicAPMCExpansion.Pruning

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.localTolerance_budget
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.localTolerance_shrink
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.split_child_shrink
