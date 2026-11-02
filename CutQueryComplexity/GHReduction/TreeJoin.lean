import CutQueryComplexity.GHReduction.TreeAssembly
import CutQueryComplexity.GHReduction.SteinerContraction

/-! # Joining two terminal trees across one accepted shore

The public edge family is the disjoint union of both trees and one attachment
edge. Old edge shores extend to the entire opposite tree exactly when they
contain the attachment vertex. This preserves the original lifted shores.
The construction is finite, performs no queries, and keeps zero-weight edges.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V U W : Type} [Fintype V] [DecidableEq V]
  [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

theorem subtree_parent_cross_iff (T : RootedTree U) (x y : U) (hy : y ≠ T.root) :
    ¬(y ∈ T.D x ↔ T.parent y ∈ T.D x) ↔ y = x := by
  by_cases hyx : y = x
  · subst x
    simp only [T.self_mem_D, tree_parent_not_mem_subtree T hy, true_iff,
      not_false_eq_true]
  · have hxy : x ≠ y := Ne.symm hyx
    have hm : y ∈ T.D x ↔ T.parent y ∈ T.D x := by
      simp only [RootedTree.mem_D, T.isAnc_iff_of_ne_root hy, hxy, false_or]
    simp only [hm, not_true_eq_false, hyx]

theorem rooted_parent_membership_constant (T : RootedTree U) (P : U → Prop)
    (hP : ∀ x, x ≠ T.root → (P x ↔ P (T.parent x))) (x y : U) : P x ↔ P y := by
  let S : Finset U := Finset.univ.filter P
  have hcross : T.crossSet S = ∅ := by
    ext z
    simp only [RootedTree.crossSet, RootedTree.Crosses, S, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro hz
    exact not_not_intro (hP z hz)
  have hroot (z : U) : P z ↔ P T.root := by
    have h := T.mem_iff_parity S z
    have hzero : Even (0 : ℕ) := ⟨0, rfl⟩
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and,
      RootedTree.crossAbove, hcross, Finset.filter_empty, Finset.card_empty,
      hzero, iff_true] using h
  exact (hroot x).trans (hroot y).symm

def joinedEdges (L : RootedTree U) (R : RootedTree W) (a : U) (b : W) :
    Finset ((U ⊕ W) × (U ⊕ W)) :=
  Finset.univ.filter (fun e => match e.1, e.2 with
    | Sum.inl x, Sum.inl y => x ≠ L.root ∧ y = L.parent x
    | Sum.inr x, Sum.inr y => x ≠ R.root ∧ y = R.parent x
    | Sum.inl x, Sum.inr y => x = a ∧ y = b
    | Sum.inr _, Sum.inl _ => False)

@[simp] theorem mem_joinedEdges_ll (L : RootedTree U) (R : RootedTree W) (a : U) (b : W)
    (x y : U) : (Sum.inl x, Sum.inl y) ∈ joinedEdges L R a b ↔
      x ≠ L.root ∧ y = L.parent x := by simp [joinedEdges]

@[simp] theorem mem_joinedEdges_rr (L : RootedTree U) (R : RootedTree W) (a : U) (b : W)
    (x y : W) : (Sum.inr x, Sum.inr y) ∈ joinedEdges L R a b ↔
      x ≠ R.root ∧ y = R.parent x := by simp [joinedEdges]

@[simp] theorem mem_joinedEdges_lr (L : RootedTree U) (R : RootedTree W) (a : U) (b : W)
    (x : U) (y : W) : (Sum.inl x, Sum.inr y) ∈ joinedEdges L R a b ↔ x = a ∧ y = b := by
  simp [joinedEdges]

@[simp] theorem not_mem_joinedEdges_rl (L : RootedTree U) (R : RootedTree W) (a : U) (b : W)
    (x : W) (y : U) : (Sum.inr x, Sum.inl y) ∉ joinedEdges L R a b := by simp [joinedEdges]

theorem joinedEdges_spans (L : RootedTree U) (R : RootedTree W) (a : U) (b : W) :
    SpanTree.Spans (joinedEdges L R a b) := by
  intro S hS
  by_contra hnone
  have hclosed : ∀ e ∈ joinedEdges L R a b, (e.1 ∈ S ↔ e.2 ∈ S) := by
    intro e he
    have hn : ¬(e.1 ∈ S ↔ e.2 ∉ S) := fun h => hnone ⟨e, he, h⟩
    tauto
  have hl (x y : U) : Sum.inl x ∈ S ↔ Sum.inl y ∈ S :=
    rooted_parent_membership_constant L (fun z => Sum.inl z ∈ S)
      (fun z hz => hclosed (Sum.inl z, Sum.inl (L.parent z)) (by simp [hz])) x y
  have hr (x y : W) : Sum.inr x ∈ S ↔ Sum.inr y ∈ S :=
    rooted_parent_membership_constant R (fun z => Sum.inr z ∈ S)
      (fun z hz => hclosed (Sum.inr z, Sum.inr (R.parent z)) (by simp [hz])) x y
  have hb : Sum.inl a ∈ S ↔ Sum.inr b ∈ S :=
    hclosed (Sum.inl a, Sum.inr b) (by simp)
  have hall (z : U ⊕ W) : z ∈ S ↔ Sum.inl a ∈ S := by
    cases z with
    | inl x => exact hl x a
    | inr x => exact (hr x b).trans hb.symm
  obtain ⟨z, hz⟩ := hS.1
  apply hS.2
  ext y
  simp only [Finset.mem_univ, iff_true]
  exact (hall y).mpr ((hall z).mp hz)

def leftExtension (a : U) (X : Finset U) : Finset (U ⊕ W) :=
  Finset.univ.filter (fun z => match z with | Sum.inl x => x ∈ X | Sum.inr _ => a ∈ X)

def rightExtension (b : W) (X : Finset W) : Finset (U ⊕ W) :=
  Finset.univ.filter (fun z => match z with | Sum.inl _ => b ∈ X | Sum.inr x => x ∈ X)

def leftHalf : Finset (U ⊕ W) := Finset.univ.filter (fun z => z.isLeft)

@[simp] theorem mem_leftExtension_inl (a x : U) (X : Finset U) :
    Sum.inl x ∈ (leftExtension a X : Finset (U ⊕ W)) ↔ x ∈ X := by simp [leftExtension]

@[simp] theorem mem_leftExtension_inr (a : U) (x : W) (X : Finset U) :
    Sum.inr x ∈ leftExtension a X ↔ a ∈ X := by simp [leftExtension]

@[simp] theorem mem_rightExtension_inl (b : W) (x : U) (X : Finset W) :
    Sum.inl x ∈ rightExtension b X ↔ b ∈ X := by simp [rightExtension]

@[simp] theorem mem_rightExtension_inr (b x : W) (X : Finset W) :
    Sum.inr x ∈ (rightExtension b X : Finset (U ⊕ W)) ↔ x ∈ X := by simp [rightExtension]

@[simp] theorem mem_leftHalf_inl (x : U) : Sum.inl x ∈ (leftHalf : Finset (U ⊕ W)) := by
  simp [leftHalf]

@[simp] theorem not_mem_leftHalf_inr (x : W) : Sum.inr x ∉ (leftHalf : Finset (U ⊕ W)) := by
  simp [leftHalf]

def joinedShore (L : RootedTree U) (R : RootedTree W) (a : U) (b : W)
    (e : (U ⊕ W) × (U ⊕ W)) : Finset (U ⊕ W) :=
  match e.1, e.2 with
  | Sum.inl x, Sum.inl _ => leftExtension a (L.D x)
  | Sum.inr x, Sum.inr _ => rightExtension b (R.D x)
  | Sum.inl _, Sum.inr _ => leftHalf
  | Sum.inr _, Sum.inl _ => ∅

theorem joinedShore_system (L : RootedTree U) (R : RootedTree W) (a : U) (b : W) :
    EdgeShoreSystem (joinedEdges L R a b) (joinedShore L R a b) := by
  intro e he
  rcases e with ⟨x, y⟩
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      obtain ⟨hx, rfl⟩ := (mem_joinedEdges_ll L R a b x y).mp he
      refine ⟨by simpa [joinedShore] using L.self_mem_D x,
        by simpa [joinedShore] using tree_parent_not_mem_subtree L hx, ?_⟩
      rintro ⟨z, w⟩ hd hc
      cases z <;> cases w
      case inl.inl z w =>
        obtain ⟨hz, rfl⟩ := (mem_joinedEdges_ll L R a b z w).mp hd
        have hzx : z = x := (subtree_parent_cross_iff L x z hz).mp
          (by simpa [joinedShore] using hc)
        simp [hzx]
      case inl.inr z w =>
        obtain ⟨rfl, rfl⟩ := (mem_joinedEdges_lr L R a b z w).mp hd
        simp [joinedShore] at hc
      case inr.inl z w => exact (not_mem_joinedEdges_rl L R a b z w hd).elim
      case inr.inr z w => simp [joinedShore] at hc
    | inr y =>
      obtain ⟨hxa, hyb⟩ := (mem_joinedEdges_lr L R a b x y).mp he
      subst x
      subst y
      refine ⟨by simp [joinedShore], by simp [joinedShore], ?_⟩
      rintro ⟨z, w⟩ hd hc
      cases z <;> cases w
      case inl.inl z w => simp [joinedShore] at hc
      case inl.inr z w =>
        obtain ⟨rfl, rfl⟩ := (mem_joinedEdges_lr L R a b z w).mp hd
        rfl
      case inr.inl z w => exact (not_mem_joinedEdges_rl L R a b z w hd).elim
      case inr.inr z w => simp [joinedShore] at hc
  | inr x =>
    cases y with
    | inl y => exact (not_mem_joinedEdges_rl L R a b x y he).elim
    | inr y =>
      obtain ⟨hx, rfl⟩ := (mem_joinedEdges_rr L R a b x y).mp he
      refine ⟨by simpa [joinedShore] using R.self_mem_D x,
        by simpa [joinedShore] using tree_parent_not_mem_subtree R hx, ?_⟩
      rintro ⟨z, w⟩ hd hc
      cases z <;> cases w
      case inl.inl z w => simp [joinedShore] at hc
      case inl.inr z w =>
        obtain ⟨rfl, rfl⟩ := (mem_joinedEdges_lr L R a b z w).mp hd
        simp [joinedShore] at hc
      case inr.inl z w => exact (not_mem_joinedEdges_rl L R a b z w hd).elim
      case inr.inr z w =>
        obtain ⟨hz, rfl⟩ := (mem_joinedEdges_rr L R a b z w).mp hd
        have hzx : z = x := (subtree_parent_cross_iff R x z hz).mp
          (by simpa [joinedShore] using hc)
        simp [hzx]

def joinedAttach (S : Finset V) (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (x : V) : U ⊕ W := if x ∈ S then Sum.inl (L.attach x) else Sum.inr (R.attach x)

def joinedTerminal (L : SteinerCutTree V U) (R : SteinerCutTree V W) : U ⊕ W → V :=
  Sum.elim L.terminal R.terminal

theorem joinedAttach_terminal (S : Finset V) (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (hL : ∀ u, L.terminal u ∈ S) (hR : ∀ w, R.terminal w ∉ S) (z : U ⊕ W) :
    joinedAttach S L R (joinedTerminal L R z) = z := by
  cases z <;> simp [joinedAttach, joinedTerminal, hL, hR, L.attach_terminal, R.attach_terminal]

theorem pull_joinedAttach_left (S : Finset V) (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (a : U) (hL : ∀ x, x ∉ S → L.attach x = a) (X : Finset U) :
    pull (joinedAttach S L R) (leftExtension a X) = pull L.attach X := by
  ext x
  by_cases hx : x ∈ S
  · simp [joinedAttach, hx]
  · simp [joinedAttach, hx, hL x hx]

theorem pull_joinedAttach_right (S : Finset V) (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (b : W) (hR : ∀ x ∈ S, R.attach x = b) (X : Finset W) :
    pull (joinedAttach S L R) (rightExtension b X) = pull R.attach X := by
  ext x
  by_cases hx : x ∈ S
  · simp [joinedAttach, hx, hR x hx]
  · simp [joinedAttach, hx]

theorem pull_joinedAttach_half (S : Finset V) (L : SteinerCutTree V U) (R : SteinerCutTree V W) :
    pull (joinedAttach S L R) leftHalf = S := by
  ext x
  by_cases hx : x ∈ S <;> simp [joinedAttach, hx]

def joinedWeight (L : CutTree U) (R : CutTree W) (bridge : ℝ)
    (e : (U ⊕ W) × (U ⊕ W)) : ℝ := match e.1, e.2 with
  | Sum.inl x, Sum.inl _ => L.weight x
  | Sum.inr x, Sum.inr _ => R.weight x
  | Sum.inl _, Sum.inr _ => bridge
  | Sum.inr _, Sum.inl _ => 0

/-- A zero-query construction from public recursive outputs and a queried
bridge value. The membership guards are finite public predicates. -/
def joinSteinerTrees (S : Finset V) (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (a : U) (b : W) (bridge : ℝ)
    (hL : ∀ u, L.terminal u ∈ S) (hR : ∀ w, R.terminal w ∉ S) : SteinerCutTree V (U ⊕ W) :=
  assembleSteinerTree (joinedEdges L.tree.topology R.tree.topology a b)
    (joinedEdges_spans L.tree.topology R.tree.topology a b) (Sum.inl L.tree.topology.root)
    (joinedWeight L.tree R.tree bridge) (joinedTerminal L R) (joinedAttach S L R)
    (joinedAttach_terminal S L R hL hR)

theorem joinSteinerTrees_correct (G : WeightedGraph V) (S : Finset V)
    (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (hL : IsSteinerCutTree G L) (hR : IsSteinerCutTree G R)
    (u : U) (v : W) (hS : IsSTMinCut G (L.terminal u) (R.terminal v) S)
    (hLterm : ∀ x, L.terminal x ∈ S) (hRterm : ∀ x, R.terminal x ∉ S)
    (hLout : ∀ x, x ∉ S → L.attach x = L.attach (R.terminal v))
    (hRin : ∀ x ∈ S, R.attach x = R.attach (L.terminal u))
    (bridge : ℝ) (hbridge : bridge = G.cut S) :
    IsSteinerCutTree G
      (joinSteinerTrees S L R (L.attach (R.terminal v)) (R.attach (L.terminal u))
        bridge hLterm hRterm) := by
  let a := L.attach (R.terminal v)
  let b := R.attach (L.terminal u)
  have hbmin := steiner_bridge_minCut G L R hL hR u v S hS (hLterm a) (hRterm b)
  apply assembleSteinerTree_correct G _ _ _ _ _ _ _
    (joinedShore L.tree.topology R.tree.topology a b)
    (joinedShore_system L.tree.topology R.tree.topology a b)
  · rintro ⟨x, y⟩ he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        obtain ⟨hx, rfl⟩ := (mem_joinedEdges_ll _ _ a b x y).mp he
        simpa only [joinedTerminal, Sum.elim_inl, joinedShore,
          pull_joinedAttach_left S L R a hLout] using (hL x hx).1
      | inr y =>
        obtain ⟨rfl, rfl⟩ := (mem_joinedEdges_lr _ _ a b x y).mp he
        simpa only [joinedTerminal, Sum.elim_inl, Sum.elim_inr, joinedShore,
          pull_joinedAttach_half] using hbmin
    | inr x =>
      cases y with
      | inl y => exact (not_mem_joinedEdges_rl _ _ a b x y he).elim
      | inr y =>
        obtain ⟨hx, rfl⟩ := (mem_joinedEdges_rr _ _ a b x y).mp he
        simpa only [joinedTerminal, Sum.elim_inr, joinedShore,
          pull_joinedAttach_right S L R b hRin] using (hR x hx).1
  · rintro ⟨x, y⟩ he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        obtain ⟨hx, rfl⟩ := (mem_joinedEdges_ll _ _ a b x y).mp he
        simpa only [joinedWeight, joinedShore, pull_joinedAttach_left S L R a hLout]
          using (hL x hx).2
      | inr y =>
        obtain ⟨rfl, rfl⟩ := (mem_joinedEdges_lr _ _ a b x y).mp he
        simpa only [joinedWeight, joinedShore, pull_joinedAttach_half] using hbridge
    | inr x =>
      cases y with
      | inl y => exact (not_mem_joinedEdges_rl _ _ a b x y he).elim
      | inr y =>
        obtain ⟨hx, rfl⟩ := (mem_joinedEdges_rr _ _ a b x y).mp he
        simpa only [joinedWeight, joinedShore, pull_joinedAttach_right S L R b hRin]
          using (hR x hx).2

end
end CutQueryComplexity.GHReduction
