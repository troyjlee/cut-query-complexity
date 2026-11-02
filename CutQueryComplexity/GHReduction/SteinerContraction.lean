import CutQueryComplexity.GHReduction.SteinerTree
import CutQueryComplexity.Certificate.GomoryHu.Contraction

/-! # Lifting recursive terminal trees and certifying their attachment edge

Protected quotient fibers lift every endpoint witness of a recursive tree.
The attachment map then proves the new bridge minimum: a cut cheaper than
the separating shore cannot distinguish a pivot terminal from the terminal
to which the opposite proxy attaches. The argument includes ties and zeros.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V W U U' : Type}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype U] [DecidableEq U] [Fintype U'] [DecidableEq U']

def SteinerCutTree.lift (T : SteinerCutTree W U) (pi : V → W) (r : W → V)
    (hr : ∀ w, pi (r w) = w) : SteinerCutTree V U where
  tree := T.tree
  terminal := r ∘ T.terminal
  attach := T.attach ∘ pi
  attach_terminal u := by simp only [Function.comp_apply, hr, T.attach_terminal]

theorem SteinerCutTree.lift_correct (G : WeightedGraph V) (T : SteinerCutTree W U)
    (pi : V → W) (r : W → V) (hr : ∀ w, pi (r w) = w)
    (hroot : ∀ w, Certificate.GomoryHu.RootProtected G (fiber pi w) (r w))
    (hT : IsSteinerCutTree (G.contract pi) T) :
    IsSteinerCutTree G (T.lift pi r hr) := by
  intro u hu
  obtain ⟨hmin, hweight⟩ := hT u hu
  have hpull : pull (T.attach ∘ pi) (T.tree.topology.D u) =
      pull pi (pull T.attach (T.tree.topology.D u)) := by ext v; simp
  refine ⟨?_, ?_⟩
  · change IsSTMinCut G (r (T.terminal u)) (r (T.terminal (T.tree.topology.parent u)))
      (pull (T.attach ∘ pi) (T.tree.topology.D u))
    rw [hpull]
    exact Certificate.GomoryHu.lift_minCut pi r hr hroot hmin
  · change T.tree.weight u = G.cut (pull (T.attach ∘ pi) (T.tree.topology.D u))
    rw [hpull, ← cut_contract]
    exact hweight

/-- A cheap cut cannot separate a terminal from the attachment of a vertex
on the opposite side of one of its minimum shores. -/
theorem steiner_attachment_cut_lower (G : WeightedGraph V) (T : SteinerCutTree V U)
    (hT : IsSteinerCutTree G T) (u : U) (p : V) (S : Finset V)
    (hS : IsSTMinCut G (T.terminal u) p S) (A : Finset V)
    (hsep : ¬(T.terminal u ∈ A ↔ T.terminal (T.attach p) ∈ A)) : G.cut S ≤ G.cut A := by
  have hne : u ≠ T.attach p := by
    intro he
    exact hsep (by rw [he])
  obtain ⟨e, he, _, hmin, _⟩ := steinerTree_allPairs G T hT hne
  have hp : p ∉ steinerPathShore T u e := by
    have ht := (pathShore_separates T.tree.topology he).2
    simpa only [steinerPathShore, mem_pull] using ht
  have hlower := hS.2.2 (steinerPathShore T u e) hmin.1 hp
  by_cases hu : T.terminal u ∈ A
  · have ha : T.terminal (T.attach p) ∉ A := by
      intro ha
      exact hsep ⟨fun _ => ha, fun _ => hu⟩
    exact hlower.trans (hmin.2.2 A hu ha)
  · have ha : T.terminal (T.attach p) ∈ A := by
      by_contra ha
      exact hsep ⟨fun h => (hu h).elim, fun h => (ha h).elim⟩
    exact hlower.trans (by simpa only [cut_compl] using
      (hmin.2.2 Aᶜ (by simpa using hu) (by simpa using ha)))

theorem steiner_attachment_agrees_of_cheaper (G : WeightedGraph V)
    (T : SteinerCutTree V U) (hT : IsSteinerCutTree G T)
    (u : U) (p : V) (S : Finset V) (hS : IsSTMinCut G (T.terminal u) p S)
    (A : Finset V) (hcheap : G.cut A < G.cut S) :
    T.terminal u ∈ A ↔ T.terminal (T.attach p) ∈ A := by
  by_contra hsep
  exact (not_lt_of_ge (steiner_attachment_cut_lower G T hT u p S hS A hsep)) hcheap

/-- The bridge joins the images of the opposite contraction proxies. Its
endpoint minimum follows from the two recursive tree certificates and the
original separating cut; it is not assumed as an assembly invariant. -/
theorem steiner_bridge_minCut (G : WeightedGraph V)
    (L : SteinerCutTree V U) (R : SteinerCutTree V U')
    (hL : IsSteinerCutTree G L) (hR : IsSteinerCutTree G R)
    (u : U) (v : U') (S : Finset V)
    (hS : IsSTMinCut G (L.terminal u) (R.terminal v) S)
    (hleft : L.terminal (L.attach (R.terminal v)) ∈ S)
    (hright : R.terminal (R.attach (L.terminal u)) ∉ S) :
    IsSTMinCut G (L.terminal (L.attach (R.terminal v)))
      (R.terminal (R.attach (L.terminal u))) S := by
  refine ⟨hleft, hright, fun A hLA hRA => ?_⟩
  by_contra hle
  have hcheap : G.cut A < G.cut S := lt_of_not_ge hle
  have hl := steiner_attachment_agrees_of_cheaper G L hL u (R.terminal v) S hS A hcheap
  have hr := steiner_attachment_agrees_of_cheaper G R hR v (L.terminal u) Sᶜ
    (stMinCut_compl G hS) A (by simpa only [cut_compl] using hcheap)
  have hbound := hS.2.2 A (hl.mpr hLA) (fun hvA => hRA (hr.mp hvA))
  exact (not_lt_of_ge hbound) hcheap

end
end CutQueryComplexity.GHReduction
