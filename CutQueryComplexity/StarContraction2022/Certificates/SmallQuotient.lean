import CutQueryComplexity.StarContraction2022.Common.Threshold
import CutQueryComplexity.StarContraction2022.Common.Constants

/-! # The guarded deterministic small-quotient branch

This uses the actual sequential forest program only in the public small-size
branch. It does not stand in for the efficient parallel algorithm. The existing
`sequentialShore` includes its single original-value query already.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]

private theorem det_eval_weaken {I A O : Type} {b c : ℕ} (h : b ≤ c)
    (T : DTree I A O b) (read : I → A) : (T.weaken h).eval read = T.eval read := by
  simp only [DTree.eval, DTree.run_weaken]

/-- Both tests concern public sizes, before the hidden graph is supplied. -/
def smallQuotientShore (π : PublicQuotient V Q) (r : ℕ) :
    DTree (Finset V) ℝ (Option (CutResult V)) (12 * Fintype.card V + 1) :=
  if hq : 2 ≤ Fintype.card Q then
    if hb : r * forestBudget Q ≤ 12 * Fintype.card V then
      (sequentialShore π r hq).weaken (Nat.add_le_add_right hb 1)
    else DTree.pure none
  else DTree.pure none

theorem smallQuotientShore_cost (π : PublicQuotient V Q) (r : ℕ)
    (read : Finset V → ℝ) :
    (smallQuotientShore π r).cost read ≤ 12 * Fintype.card V + 1 := DTree.cost_le _ _

theorem smallQuotientShore_sound (π : PublicQuotient V Q) (r : ℕ)
    (G : WeightedGraph V) {out : CutResult V}
    (ho : (smallQuotientShore π r).eval G.cut = some out) : out.Sound G := by
  unfold smallQuotientShore at ho
  split at ho
  next hq =>
    split at ho
    next hb =>
      rw [det_eval_weaken] at ho
      exact sequentialShore_sound π r hq G ho
    next hb => simp at ho
  next hq => simp at ho

/-- The numerical small-quotient guards discharge the real program index. -/
theorem smallQuotient_budget (π : PublicQuotient V Q) (r : ℕ)
    (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (hmid : Schedule.MiddleGuard (Fintype.card V) r (Fintype.card Q))
    (hsmall : (Fintype.card Q : ℝ) ≤ (Real.log (Fintype.card V)) ^ 3) :
    r * forestBudget Q ≤ 12 * Fintype.card V := by
  rw [sequentialCertificate_budget]
  have h := Schedule.middle_small_envelope (Fintype.card V) r (Fintype.card Q) hn hmid hsmall
  exact_mod_cast h

/-- A surviving strict minimum is returned with its actual original value.
No certificate, cost, or solver hypothesis is supplied to this program theorem. -/
theorem smallQuotientShore_correct (π : PublicQuotient V Q) (r : ℕ)
    (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (hmid : Schedule.MiddleGuard (Fintype.card V) r (Fintype.card Q))
    (hsmall : (Fintype.card Q : ℝ) ≤ (Real.log (Fintype.card V)) ^ 3)
    (G : WeightedGraph V) (hG : G.IsIntegral) {S : Finset V}
    (hS : IsMinCut G S) (hs : RespectsBlocks π.map S) (hr : mincutValue G < r) :
    ∃ out, (smallQuotientShore π r).eval G.cut = some out ∧ out.Sound G ∧
      IsMinCut G out.shore ∧ out.value = mincutValue G := by
  have hq : 2 ≤ Fintype.card Q := hmid.2.1
  have hb := smallQuotient_budget π r hn hmid hsmall
  rw [smallQuotientShore, dif_pos hq, dif_pos hb, det_eval_weaken]
  exact sequentialShore_correct π r hq G hG hS hs hr

#print axioms smallQuotientShore_cost
#print axioms smallQuotientShore_sound
#print axioms smallQuotient_budget
#print axioms smallQuotientShore_correct

end
end CutQueryComplexity.StarContraction2022.Certificates
