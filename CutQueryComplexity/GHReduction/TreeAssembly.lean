import CutQueryComplexity.GHReduction.SteinerTree
import CutQueryComplexity.MinCut.SpanTree

/-! # Public tree assembly from edge cuts

The input is an explicit connected edge family with one shore per edge. Each
shore crosses exactly its own edge. A public BFS orients this family, and the
shore witnesses then identify its fundamental cuts, up to complement. Hidden
minimum cuts are used only in the correctness theorem, never to choose the
tree, its root, its parent edges, or its weights.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

def EdgeShoreSystem (F : Finset (U × U)) (shore : U × U → Finset U) : Prop :=
  ∀ e ∈ F, e.1 ∈ shore e ∧ e.2 ∉ shore e ∧
    ∀ d ∈ F, ¬(d.1 ∈ shore e ↔ d.2 ∈ shore e) → d = e

theorem tree_parent_not_mem_subtree (T : RootedTree U) {v : U} (hv : v ≠ T.root) :
    T.parent v ∉ T.D v := by
  intro hp
  have hd := ((T.mem_D _ _).mp hp).depth_le
  have hs := T.depth_parent v hv
  omega

/-- Select the available orientation of a public parent edge. -/
def selectedParentEdge (T : RootedTree U) (F : Finset (U × U)) (v : U) : U × U :=
  if (v, T.parent v) ∈ F then (v, T.parent v) else (T.parent v, v)

theorem selectedParentEdge_endpoints (T : RootedTree U) (F : Finset (U × U)) (v : U) :
    selectedParentEdge T F v = (v, T.parent v) ∨
      selectedParentEdge T F v = (T.parent v, v) := by
  unfold selectedParentEdge
  split <;> simp

theorem selectedParentEdge_mem (T : RootedTree U) (F : Finset (U × U)) {v : U}
    (hv : SpanTree.Adj F (T.parent v) v) : selectedParentEdge T F v ∈ F := by
  unfold selectedParentEdge
  split
  · assumption
  · exact hv.resolve_right (by assumption)

theorem selectedParentEdge_identifies (T : RootedTree U) (F : Finset (U × U))
    {v w : U} (hv : v ≠ T.root) (hw : w ≠ T.root)
    (he : selectedParentEdge T F w = selectedParentEdge T F v) : w = v := by
  have hdv := T.depth_parent v hv
  have hdw := T.depth_parent w hw
  rcases selectedParentEdge_endpoints T F v with hev | hev <;>
    rcases selectedParentEdge_endpoints T F w with hew | hew
  · rw [hev, hew] at he
    exact (Prod.mk.inj he).1
  · rw [hev, hew] at he
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
    rw [h₁] at hdw
    rw [h₂] at hdw
    omega
  · rw [hev, hew] at he
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
    rw [h₂] at hdw
    rw [h₁] at hdw
    omega
  · rw [hev, hew] at he
    exact (Prod.mk.inj he).2

theorem edgeShore_crossSet_singleton (T : RootedTree U) (F : Finset (U × U))
    (hTF : ∀ v, v ≠ T.root → SpanTree.Adj F (T.parent v) v)
    (shore : U × U → Finset U) (hshore : EdgeShoreSystem F shore)
    {v : U} (hv : v ≠ T.root) :
    T.crossSet (shore (selectedParentEdge T F v)) = {v} := by
  let e := selectedParentEdge T F v
  have he : e ∈ F := selectedParentEdge_mem T F (hTF v hv)
  obtain ⟨he₁, he₂, honly⟩ := hshore e he
  ext w
  simp only [RootedTree.crossSet, Finset.mem_filter, Finset.mem_univ, true_and,
    RootedTree.Crosses, Finset.mem_singleton]
  constructor
  · rintro ⟨hw, hcross⟩
    have hselected : ¬((selectedParentEdge T F w).1 ∈ shore e ↔
        (selectedParentEdge T F w).2 ∈ shore e) := by
      rcases selectedParentEdge_endpoints T F w with hwedge | hwedge
      · simpa only [hwedge] using hcross
      · simpa only [hwedge, iff_comm] using hcross
    exact selectedParentEdge_identifies T F hv hw
      (honly _ (selectedParentEdge_mem T F (hTF w hw)) hselected)
  · intro hw
    subst w
    refine ⟨hv, ?_⟩
    change ¬(v ∈ shore e ↔ T.parent v ∈ shore e)
    rcases selectedParentEdge_endpoints T F v with hedge | hedge
    · change e = (v, T.parent v) at hedge
      rw [hedge] at he₁ he₂ ⊢
      exact fun h => he₂ (h.mp he₁)
    · change e = (T.parent v, v) at hedge
      rw [hedge] at he₁ he₂ ⊢
      exact fun h => he₂ (h.mpr he₁)

theorem edgeShore_fundamental (T : RootedTree U) (F : Finset (U × U))
    (hTF : ∀ v, v ≠ T.root → SpanTree.Adj F (T.parent v) v)
    (shore : U × U → Finset U) (hshore : EdgeShoreSystem F shore)
    {v : U} (hv : v ≠ T.root) :
    T.D v = shore (selectedParentEdge T F v) ∨
      T.D v = (shore (selectedParentEdge T F v))ᶜ := by
  have hc := edgeShore_crossSet_singleton T F hTF shore hshore hv
  by_cases hr : T.root ∈ shore (selectedParentEdge T F v)
  · right
    have hcomp : T.crossSet ((shore (selectedParentEdge T F v))ᶜ) =
        T.crossSet (shore (selectedParentEdge T F v)) := by
      ext w
      simp only [RootedTree.crossSet, RootedTree.Crosses, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_compl]
      tauto
    exact (T.eq_D_of_crossSet_one (S := (shore (selectedParentEdge T F v))ᶜ)
      (by simpa using hr) (hcomp.trans hc)).symm
  · exact Or.inl (T.eq_D_of_crossSet_one hr hc).symm

/-- Public capacities are clipped at zero on arbitrary malformed read histories. -/
def assembleCutTree (F : Finset (U × U)) (hF : SpanTree.Spans F) (root : U)
    (weight : U × U → ℝ) : CutTree U where
  topology := SpanTree.bfsTree F root hF
  weight v := if v = root then 0 else
    max 0 (weight (selectedParentEdge (SpanTree.bfsTree F root hF) F v))
  nonneg v := by split <;> simp only [le_refl, le_max_iff, true_or]

def assembleSteinerTree (F : Finset (U × U)) (hF : SpanTree.Spans F) (root : U)
    (weight : U × U → ℝ) (terminal : U → V) (attach : V → U)
    (hfix : ∀ u, attach (terminal u) = u) : SteinerCutTree V U where
  tree := assembleCutTree F hF root weight
  terminal := terminal
  attach := attach
  attach_terminal := hfix

theorem stMinCut_reorient {G : WeightedGraph V} {a b s t : V} {S R : Finset V}
    (hS : IsSTMinCut G a b S) (hp : (s = a ∧ t = b) ∨ (s = b ∧ t = a))
    (hR : R = S ∨ R = Sᶜ) (hs : s ∈ R) (ht : t ∉ R) : IsSTMinCut G s t R := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hR with rfl | rfl
    · exact hS
    · exact ((Finset.mem_compl.mp hs) hS.1).elim
  · rcases hR with rfl | rfl
    · exact (hS.2.1 hs).elim
    · exact stMinCut_compl G hS

/-- This theorem turns checked edge witnesses into the full fundamental-shore
contract. Its hypotheses are local cut facts about supplied data, not an
assumed query algorithm or a cut-equivalent-tree existence theorem. -/
theorem assembleSteinerTree_correct (G : WeightedGraph V)
    (F : Finset (U × U)) (hF : SpanTree.Spans F) (root : U)
    (weight : U × U → ℝ) (terminal : U → V) (attach : V → U)
    (hfix : ∀ u, attach (terminal u) = u)
    (shore : U × U → Finset U) (hshore : EdgeShoreSystem F shore)
    (hmin : ∀ e ∈ F, IsSTMinCut G (terminal e.1) (terminal e.2) (pull attach (shore e)))
    (hweight : ∀ e ∈ F, weight e = G.cut (pull attach (shore e))) :
    IsSteinerCutTree G (assembleSteinerTree F hF root weight terminal attach hfix) := by
  let T := SpanTree.bfsTree F root hF
  have hTF : ∀ v, v ≠ T.root → SpanTree.Adj F (T.parent v) v :=
    fun _ hv => SpanTree.bfsTree_adj hF hv
  intro v hv
  change v ≠ T.root at hv
  let e := selectedParentEdge T F v
  have he : e ∈ F := selectedParentEdge_mem T F (hTF v hv)
  have hshape := edgeShore_fundamental T F hTF shore hshore hv
  have hshape' : pull attach (T.D v) = pull attach (shore e) ∨
      pull attach (T.D v) = (pull attach (shore e))ᶜ := by
    rcases hshape with h | h
    · exact Or.inl (congrArg (pull attach) h)
    · right
      rw [h]
      ext x
      simp [e]
  have hcut : G.cut (pull attach (T.D v)) = G.cut (pull attach (shore e)) := by
    rcases hshape' with h | h
    · rw [h]
    · rw [h, cut_compl]
  refine ⟨?_, ?_⟩
  · change IsSTMinCut G (terminal v) (terminal (T.parent v)) (pull attach (T.D v))
    apply stMinCut_reorient (hmin e he) ?_ hshape'
      (by simpa only [mem_pull, hfix] using T.self_mem_D v)
      (by simpa only [mem_pull, hfix] using tree_parent_not_mem_subtree T hv)
    rcases selectedParentEdge_endpoints T F v with h | h
    · exact Or.inl ⟨by rw [show e = (v, T.parent v) from h],
        by rw [show e = (v, T.parent v) from h]⟩
    · exact Or.inr ⟨by rw [show e = (T.parent v, v) from h],
        by rw [show e = (T.parent v, v) from h]⟩
  · change (if v = root then 0 else max 0 (weight e)) = G.cut (pull attach (T.D v))
    have hvroot : v ≠ root := hv
    rw [if_neg hvroot, hweight e he, max_eq_right (G.cut_nonneg _), hcut]

end
end CutQueryComplexity.GHReduction
