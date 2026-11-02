import CutQueryComplexity.Hierarchy.Children

/-! # The hierarchy of a laminar family containing all singletons

A finite family `F` of nonempty vertex sets that is laminar (any two members are nested or
disjoint) and contains the whole vertex set and every singleton defines a hierarchy
`laminarHier F hF` on the node type `{A // A ∈ F}`: the root is `univ`, the parent of a node
is its smallest strict superset in `F`, and its depth is the number of strict supersets. This
generalizes `Hierarchy/Existence/Tree.lean`, whose declarations are specialized to the bandwidth
construction.

* `laminarTree_isAnc_iff`: ancestry is reverse inclusion, so `cluster X = X` (`laminarHier_cluster_eq`);
* `leafChildless`: the singleton nodes are childless, and `isLeaf_of_children_eq_empty`: every
  childless node is a singleton;
* `two_le_card_children`: every non-singleton node has at least two children;
* `card_node_le`: there are at most `2n − 1` nodes.
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset TwoRespecting

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A laminar family of nonempty sets containing the whole set and all singletons. -/
structure IsLaminarCover (F : Finset (Finset V)) : Prop where
  nonempty : ∀ A ∈ F, A.Nonempty
  laminar : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  univ_mem : univ ∈ F
  singleton_mem : ∀ v, ({v} : Finset V) ∈ F

section Tree

variable (F : Finset (Finset V)) (hF : IsLaminarCover F)

/-- The nodes: the members of `F`. -/
abbrev LNode := {A : Finset V // A ∈ F}

/-- The root `univ`. -/
def rootL : LNode F := ⟨univ, hF.univ_mem⟩

/-- Strict supersets in the family. -/
def strictSupL (X : LNode F) : Finset (LNode F) := univ.filter fun Y => X.1 ⊂ Y.1

open Classical in
/-- A smallest strict superset (the node itself for the root). -/
noncomputable def parentL (X : LNode F) : LNode F :=
  if h : (strictSupL F X).Nonempty then
    Classical.choose (exists_min_image _ (fun Y : LNode F => Y.1.card) h)
  else X

/-- The number of strict supersets. -/
def depthL (X : LNode F) : ℕ := (strictSupL F X).card

variable {F}
include hF

theorem strictSupL_root : strictSupL F (rootL F hF) = ∅ := by
  ext Y
  simp only [strictSupL, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro h
  exact (Finset.ssubset_iff_subset_ne.mp h).2 (subset_antisymm h.1 (subset_univ _))

theorem root_mem_strictSupL {X : LNode F} (hX : X ≠ rootL F hF) :
    rootL F hF ∈ strictSupL F X := by
  refine mem_filter.mpr ⟨mem_univ _, ssubset_of_subset_of_ne (subset_univ _) fun he => hX ?_⟩
  exact Subtype.ext he

omit [DecidableEq V] in
theorem lnode_laminar (X Y : LNode F) : X.1 ⊆ Y.1 ∨ Y.1 ⊆ X.1 ∨ Disjoint X.1 Y.1 :=
  hF.laminar X.1 X.2 Y.1 Y.2

/-- The parent is the smallest strict superset. -/
theorem parentL_spec {X : LNode F} (hX : X ≠ rootL F hF) :
    parentL F X ∈ strictSupL F X ∧ ∀ Y ∈ strictSupL F X, (parentL F X).1 ⊆ Y.1 := by
  classical
  have hne : (strictSupL F X).Nonempty := ⟨_, root_mem_strictSupL hF hX⟩
  have hs := Classical.choose_spec (exists_min_image _ (fun Y : LNode F => Y.1.card) hne)
  simp only [parentL, dite_eq_left hne]
  refine ⟨hs.1, fun Y hY => ?_⟩
  set P := Classical.choose (exists_min_image _ (fun Y : LNode F => Y.1.card) hne)
  have hXP := (mem_filter.mp hs.1).2
  have hXY := (mem_filter.mp hY).2
  rcases lnode_laminar hF P Y with h | h | h
  · exact h
  · by_cases he : Y.1 = P.1
    · rw [he]
    · have := card_lt_card (ssubset_of_subset_of_ne h he)
      have := hs.2 Y hY
      omega
  · obtain ⟨v, hv⟩ := hF.nonempty X.1 X.2
    exact absurd (disjoint_left.mp h (hXP.1 hv) (hXY.1 hv)) (by simp)

theorem parentL_root : parentL F (rootL F hF) = rootL F hF := by
  classical
  have : ¬ (strictSupL F (rootL F hF)).Nonempty := by
    rw [strictSupL_root]; exact not_nonempty_empty
  simp only [parentL, dite_eq_right this]

theorem strictSupL_eq {X : LNode F} (hX : X ≠ rootL F hF) :
    strictSupL F X = insert (parentL F X) (strictSupL F (parentL F X)) := by
  obtain ⟨hP, hmin⟩ := parentL_spec hF hX
  have hXP := (mem_filter.mp hP).2
  ext Y
  simp only [mem_insert, strictSupL, mem_filter, mem_univ, true_and]
  constructor
  · intro hXY
    have hPY := hmin Y (mem_filter.mpr ⟨mem_univ _, hXY⟩)
    by_cases he : parentL F X = Y
    · exact Or.inl he.symm
    · exact Or.inr (ssubset_of_subset_of_ne hPY fun h => he (Subtype.ext h))
  · rintro (rfl | h)
    · exact hXP
    · exact hXP.trans h

omit [Fintype V] hF in
theorem notMem_strictSupL_self (X : LNode F) : X ∉ strictSupL F X := by
  simp [strictSupL]

theorem depthL_parent {X : LNode F} (hX : X ≠ rootL F hF) :
    depthL F (parentL F X) + 1 = depthL F X := by
  unfold depthL
  rw [strictSupL_eq hF hX, card_insert_of_notMem (notMem_strictSupL_self (parentL F X))]

variable (F) in
/-- The rooted tree of the family. -/
noncomputable def laminarTree : RootedTree (LNode F) where
  root := rootL F hF
  parent := parentL F
  depth := depthL F
  parent_root := parentL_root hF
  depth_root := by unfold depthL; rw [strictSupL_root]; rfl
  depth_parent := fun _ hv => depthL_parent hF hv

theorem parentL_supset (X : LNode F) : X.1 ⊆ (parentL F X).1 := by
  by_cases hX : X = rootL F hF
  · rw [hX, parentL_root]
  · exact (mem_filter.mp (parentL_spec hF hX).1).2.1

/-- Ancestry is reverse inclusion. -/
theorem laminarTree_isAnc_iff (X Y : LNode F) : (laminarTree F hF).IsAnc X Y ↔ Y.1 ⊆ X.1 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    clear hk
    induction k generalizing Y with
    | zero => exact le_rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply]
        exact (parentL_supset hF Y).trans (ih _)
  · intro h
    have key : ∀ d (Y : LNode F), depthL F Y = d → Y.1 ⊆ X.1 →
        (laminarTree F hF).IsAnc X Y := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro Y hd hYX
        by_cases hXY : X = Y
        · rw [hXY]
        by_cases hYr : Y = rootL F hF
        · exfalso; apply hXY
          apply Subtype.ext
          rw [hYr] at hYX ⊢
          exact subset_antisymm (subset_univ _) hYX
        have hss : Y.1 ⊂ X.1 := ssubset_of_subset_of_ne hYX fun he => hXY (Subtype.ext he.symm)
        have hPX := (parentL_spec hF hYr).2 X (mem_filter.mpr ⟨mem_univ _, hss⟩)
        have hdp := depthL_parent hF hYr
        have := ih _ (by omega) (parentL F Y) rfl hPX
        exact RootedTree.isAnc_trans this (RootedTree.isAnc_parent (T := laminarTree F hF) Y)
    exact key _ Y rfl h

variable (F) in
/-- The hierarchy of the family; its leaves are the singletons. -/
noncomputable def laminarHier : Hier V (LNode F) where
  T := laminarTree F hF
  leaf v := ⟨{v}, hF.singleton_mem v⟩
  leaf_inj v w h := by
    have := congrArg Subtype.val h
    simpa using this

theorem laminarHier_root : (laminarHier F hF).T.root = rootL F hF := rfl

theorem laminarHier_leaf (v : V) : ((laminarHier F hF).leaf v).1 = {v} := rfl

theorem laminarHier_cluster_eq (X : LNode F) : (laminarHier F hF).cluster X = X.1 := by
  ext v
  rw [Hier.mem_cluster]
  show (laminarTree F hF).IsAnc X _ ↔ _
  rw [laminarTree_isAnc_iff]
  exact singleton_subset_iff

/-- Children are strict subsets. -/
theorem ssubset_of_mem_children {X C : LNode F} (hC : C ∈ (laminarHier F hF).children X) :
    C.1 ⊂ X.1 := by
  obtain ⟨hCr, hpar⟩ := Hier.mem_children.mp hC
  have := (mem_filter.mp (parentL_spec hF hCr).1).2
  show C.1 ⊂ X.1
  rw [← hpar]
  exact this

/-- A singleton node has no children. -/
theorem leafChildless : (laminarHier F hF).LeafChildless := by
  intro v
  ext C
  simp only [Finset.notMem_empty, iff_false]
  intro hC
  have hss := ssubset_of_mem_children hF hC
  rw [laminarHier_leaf] at hss
  obtain ⟨u, hu⟩ := hF.nonempty C.1 C.2
  have := card_lt_card hss
  rw [card_singleton] at this
  have := card_pos.mpr ⟨u, hu⟩
  omega

/-- Every vertex of a node lies in a child, unless the node is that vertex's singleton. -/
theorem exists_child_mem {X : LNode F} {v : V} (hv : v ∈ X.1)
    (hne : X ≠ (laminarHier F hF).leaf v) :
    ∃ C ∈ (laminarHier F hF).children X, v ∈ C.1 := by
  have hanc : (laminarHier F hF).T.IsAnc X ((laminarHier F hF).leaf v) := by
    show (laminarTree F hF).IsAnc X _
    rw [laminarTree_isAnc_iff, laminarHier_leaf]
    exact singleton_subset_iff.mpr hv
  obtain ⟨C, hC, hCv⟩ := Hier.exists_child hanc hne
  refine ⟨C, hC, ?_⟩
  have : (laminarTree F hF).IsAnc C ((laminarHier F hF).leaf v) := hCv
  rw [laminarTree_isAnc_iff, laminarHier_leaf] at this
  exact singleton_subset_iff.mp this

/-- A childless node is a singleton node. -/
theorem isLeaf_of_children_eq_empty {X : LNode F}
    (h : (laminarHier F hF).children X = ∅) : (laminarHier F hF).IsLeaf X := by
  obtain ⟨v, hv⟩ := hF.nonempty X.1 X.2
  refine ⟨v, ?_⟩
  by_contra hne
  obtain ⟨C, hC, -⟩ := exists_child_mem hF hv (Ne.symm hne)
  rw [h] at hC
  exact Finset.notMem_empty C hC

/-- A node that is not a singleton node has at least two children. -/
theorem two_le_card_children {X : LNode F} (hX : ¬ (laminarHier F hF).IsLeaf X) :
    2 ≤ ((laminarHier F hF).children X).card := by
  obtain ⟨u, hu⟩ := hF.nonempty X.1 X.2
  obtain ⟨C₁, hC₁, huC₁⟩ := exists_child_mem hF hu fun h => hX ⟨u, h.symm⟩
  have hss := ssubset_of_mem_children hF hC₁
  obtain ⟨w, hwX, hwC₁⟩ := Finset.exists_of_ssubset hss
  obtain ⟨C₂, hC₂, hwC₂⟩ := exists_child_mem hF hwX fun h => hX ⟨w, h.symm⟩
  have hne : C₁ ≠ C₂ := fun h => hwC₁ (h ▸ hwC₂)
  exact Finset.one_lt_card.mpr ⟨C₁, hC₁, C₂, hC₂, hne⟩

/-- Every vertex is the cluster of its leaf. -/
theorem cluster_leaf (v : V) : (laminarHier F hF).cluster ((laminarHier F hF).leaf v) = {v} := by
  rw [laminarHier_cluster_eq, laminarHier_leaf]

/-- At most `2n − 1` nodes. -/
theorem card_node_le [Nonempty V] : Fintype.card (LNode F) ≤ 2 * Fintype.card V - 1 := by
  set H := laminarHier F hF
  set L : Finset (LNode F) := univ.image H.leaf
  have hL : L.card = Fintype.card V := by
    rw [card_image_of_injective _ H.leaf_inj, card_univ]
  have hedges : H.edges.card = Fintype.card (LNode F) - 1 := by
    rw [Hier.edges, card_erase_of_mem (mem_univ _), card_univ]
  have hsum : ∑ x ∈ H.edges, (1 : ℕ) = ∑ u, (H.children u).card := by
    rw [Hier.sum_edges_eq_sum_children]
    exact sum_congr rfl fun u _ => by rw [card_eq_sum_ones]
  have hlow : ∑ u ∈ univ \ L, 2 ≤ ∑ u, (H.children u).card := by
    refine le_trans (sum_le_sum fun u hu => ?_) (sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun _ _ _ => Nat.zero_le _)
    have hu' : ¬ H.IsLeaf u := by
      rintro ⟨v, rfl⟩
      exact (mem_sdiff.mp hu).2 (mem_image_of_mem _ (mem_univ v))
    exact two_le_card_children hF hu'
  rw [sum_const, smul_eq_mul, card_univ_sdiff, hL] at hlow
  rw [sum_const, smul_eq_mul, mul_one, hedges] at hsum
  have h1 : 1 ≤ Fintype.card (LNode F) := Fintype.card_pos_iff.mpr ⟨rootL F hF⟩
  have hLle : Fintype.card V ≤ Fintype.card (LNode F) := by
    rw [← hL]; exact card_le_univ L
  omega

/-- Children are exactly the maximal members strictly below a node. -/
theorem mem_children_iff_maximal {X C : LNode F} :
    C ∈ (laminarHier F hF).children X ↔ C.1 ⊂ X.1 ∧ ∀ Z ∈ F, C.1 ⊂ Z → X.1 ⊆ Z := by
  rw [Hier.mem_children]
  show C ≠ rootL F hF ∧ parentL F C = X ↔ _
  constructor
  · rintro ⟨hCr, hpar⟩
    obtain ⟨hP, hmin⟩ := parentL_spec hF hCr
    rw [hpar] at hP hmin
    exact ⟨(mem_filter.mp hP).2, fun Z hZ hCZ => hmin ⟨Z, hZ⟩ (mem_filter.mpr ⟨mem_univ _, hCZ⟩)⟩
  · rintro ⟨hCX, hmax⟩
    have hCr : C ≠ rootL F hF := by
      rintro rfl
      exact (Finset.ssubset_iff_subset_ne.mp hCX).2 (subset_antisymm (subset_univ _) hCX.1).symm
    obtain ⟨hP, hmin⟩ := parentL_spec hF hCr
    refine ⟨hCr, Subtype.ext (subset_antisymm (hmin X (mem_filter.mpr ⟨mem_univ _, hCX⟩))
      (hmax _ (parentL F C).2 (mem_filter.mp hP).2))⟩

omit [Fintype V] hF in
/-- The depth of a node is the number of its strict supersets in the family. -/
theorem depthL_eq_card_filter (X : LNode F) :
    depthL F X = (F.filter fun T => X.1 ⊂ T).card := by
  unfold depthL strictSupL
  refine card_bij (fun Y _ => Y.1) ?_ ?_ ?_
  · intro Y hY
    exact mem_filter.mpr ⟨Y.2, (mem_filter.mp hY).2⟩
  · intro Y _ Y' _ h
    exact Subtype.ext h
  · intro T hT
    exact ⟨⟨T, (mem_filter.mp hT).1⟩, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hT).2⟩, rfl⟩

/-- A node is a leaf node exactly when it is a singleton. -/
theorem isLeaf_iff (X : LNode F) : (laminarHier F hF).IsLeaf X ↔ ∃ v, X.1 = {v} := by
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩
  · rintro ⟨v, hv⟩; exact ⟨v, Subtype.ext hv.symm⟩

end Tree

end Hierarchy
end CutQueryComplexity
