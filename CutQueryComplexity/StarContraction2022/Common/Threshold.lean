import CutQueryComplexity.StarContraction2022.Common.Quotient
import CutQueryComplexity.Primitive.Certificate

/-! # Strict threshold extraction and the implemented sequential fallback

The threshold semantics truncate both sides. A certificate minimum at exactly
the threshold need not name a minimum original shore; the extraction below uses
the strict inequality and the endpoint keeps its singleton in the equality case.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022

noncomputable section
open scoped Classical

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]

/-- The output direction of strict threshold preservation. -/
theorem threshold_cut_eq_of_lt {r : ℕ} {G H : WeightedGraph V}
    (h : IsThresholdCertificate r G H) {S : Finset V} (hS : H.cut S < r) :
    G.cut S = H.cut S := by
  have he := h.2.2.2 S
  by_cases hg : G.cut S < r
  · rw [min_eq_right hS.le, min_eq_right hg.le] at he
    exact he.symm
  · have hr : (r : ℝ) ≤ G.cut S := le_of_not_gt hg
    rw [min_eq_right hS.le, min_eq_left hr] at he
    linarith

/-- Every minimizing certificate shore is correct below the threshold. -/
theorem threshold_minimum {r : ℕ} {G H : WeightedGraph V}
    (h : IsThresholdCertificate r G H) (hr : mincutValue G < r)
    {S : Finset V} (hS : IsMinCut H S) : IsMinCut G S := by
  have hv : H.cut S = mincutValue G :=
    (cut_eq_mincut_of_isMinCut hS).trans (h.mincut_eq hr.le)
  have hlt : H.cut S < r := by rwa [hv]
  have he := threshold_cut_eq_of_lt h hlt
  refine ⟨hS.1, fun T hT => ?_⟩
  rw [he, hv]
  exact mincutValue_le G hT

theorem threshold_lift_minimum (π : PublicQuotient V Q) {r : ℕ}
    {G : WeightedGraph V} {H : WeightedGraph Q}
    (h : IsThresholdCertificate r (π.graph G) H)
    {S : Finset V} (hS : IsMinCut G S) (hs : RespectsBlocks π.map S)
    (hr : mincutValue G < r) {T : Finset Q} (hT : IsMinCut H T) :
    IsMinCut G (π.lift T) := by
  apply π.lift_minimum hS hs
  apply threshold_minimum h _ hT
  rwa [π.mincut_eq hS hs]

/-- Minimization uses a fully explicit graph returned by preceding queries. -/
def explicitMinimum (hq : 2 ≤ Fintype.card Q) (H : WeightedGraph Q) : Finset Q :=
  Classical.choose (exists_isMinCut_of_two_le_card H hq)

theorem explicitMinimum_spec (hq : 2 ≤ Fintype.card Q) (H : WeightedGraph Q) :
    IsMinCut H (explicitMinimum hq H) :=
  Classical.choose_spec (exists_isMinCut_of_two_le_card H hq)

/-- The existing sequential residual-forest program, compiled to original cuts. -/
def sequentialCertificate (π : PublicQuotient V Q) (r : ℕ) :
    DTree (Finset V) ℝ (WeightedGraph Q) (r * forestBudget Q) :=
  π.compileDet (thresholdCertificate r)

theorem sequentialCertificate_correct (π : PublicQuotient V Q) (r : ℕ)
    (G : WeightedGraph V) (hG : G.IsIntegral) :
    IsThresholdCertificate r (π.graph G) ((sequentialCertificate π r).eval G.cut) := by
  rw [sequentialCertificate, π.compileDet_eval]
  exact thresholdCertificate_correct r (π.graph G) (π.integral_graph G hG)

theorem sequentialCertificate_budget (r : ℕ) :
    r * forestBudget Q = 12 * r * Fintype.card Q * (Nat.clog 2 (Fintype.card Q) + 1) := by
  unfold forestBudget searchDepth
  ring

theorem sequentialCertificate_cost (π : PublicQuotient V Q) (r : ℕ)
    (read : Finset V → ℝ) :
    (sequentialCertificate π r).cost read ≤
      12 * r * Fintype.card Q * (Nat.clog 2 (Fintype.card Q) + 1) := by
  rw [← sequentialCertificate_budget]
  exact DTree.cost_le _ _

/-- Small-quotient fallback, including exactly one original-value query. -/
def sequentialShore (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q) :
    DTree (Finset V) ℝ (Option (CutResult V)) (r * forestBudget Q + 1) :=
  (sequentialCertificate π r).bind fun H =>
    verifyShore (π.lift (explicitMinimum hq H))

theorem sequentialShore_cost (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q) (read : Finset V → ℝ) :
    (sequentialShore π r hq).cost read ≤
      12 * r * Fintype.card Q * (Nat.clog 2 (Fintype.card Q) + 1) + 1 := by
  rw [← sequentialCertificate_budget]
  exact DTree.cost_le _ _

/-- Verification remains sound even when a preceding attempt did not preserve a minimum. -/
theorem sequentialShore_sound (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q) (G : WeightedGraph V) {out : CutResult V}
    (h : (sequentialShore π r hq).eval G.cut = some out) : out.Sound G := by
  rw [sequentialShore, DTree.eval_bind] at h
  exact verifyShore_sound G _ h

theorem sequentialShore_correct (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q) (G : WeightedGraph V) (hG : G.IsIntegral)
    {S : Finset V} (hS : IsMinCut G S) (hs : RespectsBlocks π.map S)
    (hr : mincutValue G < r) :
    ∃ out, (sequentialShore π r hq).eval G.cut = some out ∧ out.Sound G ∧
      IsMinCut G out.shore ∧ out.value = mincutValue G := by
  let H := (sequentialCertificate π r).eval G.cut
  let T := explicitMinimum hq H
  have hH : IsThresholdCertificate r (π.graph G) H :=
    sequentialCertificate_correct π r G hG
  have hT : IsMinCut H T := explicitMinimum_spec hq H
  have hlift : IsMinCut G (π.lift T) := threshold_lift_minimum π hH hS hs hr hT
  refine ⟨⟨π.lift T, G.cut (π.lift T)⟩, ?_, ⟨hlift.1, rfl⟩, hlift,
    cut_eq_mincut_of_isMinCut hlift⟩
  rw [sequentialShore, DTree.eval_bind]
  change (verifyShore (π.lift T)).eval G.cut = _
  rw [verifyShore_eval, if_pos hlift.1]

#print axioms threshold_cut_eq_of_lt
#print axioms threshold_minimum
#print axioms threshold_lift_minimum
#print axioms sequentialCertificate_correct
#print axioms sequentialCertificate_cost
#print axioms sequentialShore_correct
#print axioms sequentialShore_cost
#print axioms sequentialShore_sound

end
end CutQueryComplexity.StarContraction2022
