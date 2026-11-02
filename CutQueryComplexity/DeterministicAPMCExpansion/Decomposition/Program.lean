import CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State

/-!
# Actual capped recursive decomposition

Small parts finish without queries. Failed matching games recurse on both
sides. Successful games prune once, finish the large remainder, and recurse
only on the removed part. Public cardinality guards reject malformed output.
Each active node, including an aborted one, is recorded in the work tree.

The cost theorem below holds for every real-valued oracle. In particular,
neither a graph promise nor an assumed cost bound is used to obtain the
hard cap. Correctness and exhaustion of the public recursion fuel on honest
inputs are separate semantic obligations.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

open Finset Pruning
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def SplitGuard (R : ℕ) (W L : Finset V) : Prop :=
  L.card < W.card ∧ (W \ L).card < W.card ∧
    ShrinkStep (64 * R) W.card L.card ∧ ShrinkStep (64 * R) W.card (W \ L).card

def PruneGuard (W P : Finset V) : Prop :=
  8 * P.card ≤ W.card ∧ P.card < W.card

def run (R t : ℕ) (hR : 1 ≤ R) : (fuel : ℕ) → (W : Finset V) →
    Prog (Finset V) ℝ (State R W)
  | 0, W => .pure (State.finish R W (decide (W.card ≤ 64 * R)))
  | fuel + 1, W =>
      if hsmall : W.card ≤ 64 * R then .pure (State.finish R W)
      else
        (partNode R t W).bind fun answer =>
          match answer with
          | .invalid => .pure (State.abortActive R hR W (by omega))
          | .split P =>
              let L := liftShore W P
              if hguard : SplitGuard R W L then
                (run R t hR fuel L).bind fun left =>
                  (run R t hR fuel (W \ L)).map fun right =>
                    State.split W L (by omega) (liftShore_subset W P) left right
                      hguard.2.2.1 hguard.2.2.2
              else .pure (State.abortActive R hR W (by omega))
          | .pruned P =>
              let L := liftShore W P
              if hguard : PruneGuard W L then
                (run R t hR fuel L).map fun child =>
                  State.prune hR W L (by omega) (liftShore_subset W P) child hguard.1
              else .pure (State.abortActive R hR W (by omega))

/-- Cost follows the literal recursive execution, rather than a hypothetical
tree with externally supplied costs. -/
theorem run_cost_work (N R t : ℕ) (hR : 1 ≤ R) (fuel : ℕ) (W : Finset V)
    (hW : W.card ≤ N) (read : Finset V → ℝ) :
    (run R t hR fuel W).cost read ≤
      nodeUnitBudget N R t * ((run R t hR fuel W).eval read).work.mass := by
  induction fuel generalizing W with
  | zero => simp [run, State.finish, WorkTree.mass]
  | succ fuel ih =>
      by_cases hsmall : W.card ≤ 64 * R
      · simp only [run, dif_pos hsmall, Prog.cost_pure, Prog.eval_pure,
          State.finish, WorkTree.mass, Nat.mul_zero, le_refl]
      · have hn := partNode_linear_cost N R t W hW read
        simp only [run, dif_neg hsmall, Prog.cost_bind, Prog.eval_bind]
        cases he : (partNode R t W).eval read with
        | invalid =>
            simpa only [Prog.cost_pure, Nat.add_zero, Prog.eval_pure,
              State.abortActive, WorkTree.mass, Nat.add_zero] using hn
        | split P =>
            let L := liftShore W P
            by_cases hg : SplitGuard R W (liftShore W P)
            · have hl := ih L ((card_le_card (liftShore_subset W P)).trans hW)
              have hr := ih (W \ L) ((card_le_card sdiff_subset).trans hW)
              simp only [dif_pos hg, Prog.cost_bind, Prog.eval_bind, Prog.cost_map, Prog.eval_map]
              change (partNode R t W).cost read +
                ((run R t hR fuel L).cost read + (run R t hR fuel (W \ L)).cost read) ≤
                  nodeUnitBudget N R t * (W.card +
                    ((run R t hR fuel L).eval read).work.mass +
                    ((run R t hR fuel (W \ L)).eval read).work.mass)
              nlinarith
            · simpa only [dif_neg hg, Prog.cost_pure, Nat.add_zero, Prog.eval_pure,
                State.abortActive, WorkTree.mass, Nat.add_zero] using hn
        | pruned P =>
            let L := liftShore W P
            by_cases hg : PruneGuard W (liftShore W P)
            · have hl := ih L ((card_le_card (liftShore_subset W P)).trans hW)
              simp only [dif_pos hg, Prog.cost_map, Prog.eval_map]
              change (partNode R t W).cost read + (run R t hR fuel L).cost read ≤
                nodeUnitBudget N R t * (W.card + ((run R t hR fuel L).eval read).work.mass + 0)
              nlinarith
            · simpa only [dif_neg hg, Prog.cost_pure, Nat.add_zero, Prog.eval_pure,
                State.abortActive, WorkTree.mass, Nat.add_zero] using hn

def queryBudget (N R t : ℕ) : ℕ :=
  nodeUnitBudget N R t * ((64 * R) * Nat.clog 2 (N + 1) * N)

theorem run_cost (N R t : ℕ) (hR : 1 ≤ R) (fuel : ℕ) (W : Finset V)
    (hW : W.card ≤ N) (read : Finset V → ℝ) :
    (run R t hR fuel W).cost read ≤ queryBudget N R t :=
  (run_cost_work N R t hR fuel W hW read).trans
    (Nat.mul_le_mul_left _ (((run R t hR fuel W).eval read).mass_le R N hR hW))

def program (R t : ℕ) (hR : 1 ≤ R) (fuel : ℕ) (W : Finset V) :
    DTree (Finset V) ℝ (State R W) (queryBudget (Fintype.card V) R t) :=
  ((run R t hR fuel W).toDTree (queryBudget (Fintype.card V) R t)).map
    (fun result => result.getD (State.finish R W false))

theorem program_eval (R t : ℕ) (hR : 1 ≤ R) (fuel : ℕ) (W : Finset V)
    (read : Finset V → ℝ) :
    (program R t hR fuel W).eval read = (run R t hR fuel W).eval read := by
  rw [program, DTree.eval_map,
    Prog.toDTree_eval read _ _ (run_cost (Fintype.card V) R t hR fuel W (card_le_univ W) read)]
  rfl

def decomposition (R t : ℕ) (hR : 1 ≤ R) :
    DTree (Finset V) ℝ (State R (univ : Finset V)) (queryBudget (Fintype.card V) R t) :=
  program R t hR (Fintype.card V) univ

end
end CutQueryComplexity.DeterministicAPMCExpansion.Decomposition

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.run_cost_work
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.run_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.program_eval
