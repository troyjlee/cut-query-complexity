import CutQueryComplexity.Hierarchy.Existence.Clusters

/-! # The hierarchy of the cluster family (hierarchy plan, Milestone 5, part 2)

For nonempty `V`, the nodes are the clusters of `univ`. The parent of a cluster is a smallest
strict superset in the family (unique by laminarity), and its depth is the number of strict
supersets. `clusterHier` is the resulting hierarchy; its leaves are the singletons.

* `isAnc_iff`: ancestry is inclusion, so `cluster x = x` (`cluster_eq`);
* `mem_children_iff`: the children of a cluster are exactly its chosen parts;
* `rep_le_clusterHier`: by Milestone 1, `R(S) ≤ 26 λ (D + 1) c_J(S)` whenever all depths are
  at most `D`.
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset TwoRespecting

variable {V : Type} [Fintype V] [DecidableEq V]

section Tree

variable (J : WeightedGraph V) {lam : ℝ} (hlam1 : 1 ≤ lam)
  (hlamB : 4 * beta (Fintype.card V) ≤ lam)

include hlam1 in
/-- The whole vertex set has bandwidth `λ ≥ 1`. -/
theorem bandwidth_univ : Bandwidth J (univ : Finset V) lam := by
  intro U _ _
  rw [← compl_eq_univ_sdiff, cross_compl]
  have := J.cut_nonneg U
  nlinarith

/-- The nodes: the clusters of `univ`. -/
abbrev Node := {X : Finset V // X ∈ clusters J hlam1 hlamB (univ : Finset V)}

variable [Nonempty V]

include hlam1 in
theorem good_univ : Good J (lam := lam) (univ : Finset V) :=
  ⟨univ_nonempty, bandwidth_univ J hlam1⟩

theorem node_good (X : Node J hlam1 hlamB) : Good J (lam := lam) X.1 :=
  (clusters_good J hlam1 hlamB _ (good_univ J hlam1) X.1 X.2).2

/-- The root `univ`. -/
noncomputable def rootN : Node J hlam1 hlamB := ⟨univ, self_mem_clusters J hlam1 hlamB _⟩

/-- Strict supersets in the family. -/
noncomputable def strictSup (X : Node J hlam1 hlamB) : Finset (Node J hlam1 hlamB) :=
  univ.filter fun Y => X.1 ⊂ Y.1

open Classical in
/-- A smallest strict superset (the root for the root). -/
noncomputable def parentN (X : Node J hlam1 hlamB) : Node J hlam1 hlamB :=
  if h : (strictSup J hlam1 hlamB X).Nonempty then
    Classical.choose (exists_min_image _ (fun Y : Node J hlam1 hlamB => Y.1.card) h)
  else X

/-- The number of strict supersets. -/
noncomputable def depthN (X : Node J hlam1 hlamB) : ℕ := (strictSup J hlam1 hlamB X).card

omit [Nonempty V] in
theorem strictSup_root : strictSup J hlam1 hlamB (rootN J hlam1 hlamB) = ∅ := by
  ext Y
  simp only [strictSup, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro h
  exact (Finset.ssubset_iff_subset_ne.mp h).2 (subset_antisymm h.1 (subset_univ _))

omit [Nonempty V] in
theorem root_mem_strictSup {X : Node J hlam1 hlamB} (hX : X ≠ rootN J hlam1 hlamB) :
    rootN J hlam1 hlamB ∈ strictSup J hlam1 hlamB X := by
  refine mem_filter.mpr ⟨mem_univ _, ssubset_of_subset_of_ne (subset_univ _) fun he => hX ?_⟩
  exact Subtype.ext he

theorem laminar_nodes (X Y : Node J hlam1 hlamB) : X.1 ⊆ Y.1 ∨ Y.1 ⊆ X.1 ∨ Disjoint X.1 Y.1 :=
  clusters_laminar J hlam1 hlamB _ (good_univ J hlam1) X.1 X.2 Y.1 Y.2

/-- The parent is the smallest strict superset. -/
theorem parentN_spec {X : Node J hlam1 hlamB} (hX : X ≠ rootN J hlam1 hlamB) :
    parentN J hlam1 hlamB X ∈ strictSup J hlam1 hlamB X ∧
      ∀ Y ∈ strictSup J hlam1 hlamB X, (parentN J hlam1 hlamB X).1 ⊆ Y.1 := by
  classical
  have hne : (strictSup J hlam1 hlamB X).Nonempty := ⟨_, root_mem_strictSup J hlam1 hlamB hX⟩
  have hs := Classical.choose_spec
    (exists_min_image _ (fun Y : Node J hlam1 hlamB => Y.1.card) hne)
  simp only [parentN, dite_eq_left hne]
  refine ⟨hs.1, fun Y hY => ?_⟩
  set P := Classical.choose (exists_min_image _ (fun Y : Node J hlam1 hlamB => Y.1.card) hne)
  have hXP := (mem_filter.mp hs.1).2
  have hXY := (mem_filter.mp hY).2
  rcases laminar_nodes J hlam1 hlamB P Y with h | h | h
  · exact h
  · by_cases he : Y.1 = P.1
    · rw [he]
    · have := card_lt_card (ssubset_of_subset_of_ne h he)
      have := hs.2 Y hY
      omega
  · obtain ⟨v, hv⟩ := (node_good J hlam1 hlamB X).1
    exact absurd (disjoint_left.mp h (hXP.1 hv) (hXY.1 hv)) (by simp)

omit [Nonempty V] in
theorem parentN_root : parentN J hlam1 hlamB (rootN J hlam1 hlamB) = rootN J hlam1 hlamB := by
  classical
  have : ¬ (strictSup J hlam1 hlamB (rootN J hlam1 hlamB)).Nonempty := by
    rw [strictSup_root]; exact not_nonempty_empty
  simp only [parentN, dite_eq_right this]

theorem strictSup_eq {X : Node J hlam1 hlamB} (hX : X ≠ rootN J hlam1 hlamB) :
    strictSup J hlam1 hlamB X =
      insert (parentN J hlam1 hlamB X) (strictSup J hlam1 hlamB (parentN J hlam1 hlamB X)) := by
  obtain ⟨hP, hmin⟩ := parentN_spec J hlam1 hlamB hX
  have hXP := (mem_filter.mp hP).2
  ext Y
  simp only [mem_insert, strictSup, mem_filter, mem_univ, true_and]
  constructor
  · intro hXY
    have hPY := hmin Y (mem_filter.mpr ⟨mem_univ _, hXY⟩)
    by_cases he : parentN J hlam1 hlamB X = Y
    · exact Or.inl he.symm
    · exact Or.inr (ssubset_of_subset_of_ne hPY fun h => he (Subtype.ext h))
  · rintro (rfl | h)
    · exact hXP
    · exact hXP.trans h

omit [Nonempty V] in
theorem not_mem_strictSup_self (X : Node J hlam1 hlamB) : X ∉ strictSup J hlam1 hlamB X := by
  simp [strictSup]

theorem depthN_parent {X : Node J hlam1 hlamB} (hX : X ≠ rootN J hlam1 hlamB) :
    depthN J hlam1 hlamB (parentN J hlam1 hlamB X) + 1 = depthN J hlam1 hlamB X := by
  unfold depthN
  rw [strictSup_eq J hlam1 hlamB hX, card_insert_of_notMem (not_mem_strictSup_self J hlam1 hlamB _)]

/-- The rooted tree of the cluster family. -/
noncomputable def clusterTree : RootedTree (Node J hlam1 hlamB) where
  root := rootN J hlam1 hlamB
  parent := parentN J hlam1 hlamB
  depth := depthN J hlam1 hlamB
  parent_root := parentN_root J hlam1 hlamB
  depth_root := by unfold depthN; rw [strictSup_root]; rfl
  depth_parent := fun _ hv => depthN_parent J hlam1 hlamB hv

theorem parentN_supset (X : Node J hlam1 hlamB) : X.1 ⊆ (parentN J hlam1 hlamB X).1 := by
  by_cases hX : X = rootN J hlam1 hlamB
  · rw [hX, parentN_root]
  · exact (mem_filter.mp (parentN_spec J hlam1 hlamB hX).1).2.1

/-- Ancestry is inclusion. -/
theorem isAnc_iff (X Y : Node J hlam1 hlamB) :
    (clusterTree J hlam1 hlamB).IsAnc X Y ↔ Y.1 ⊆ X.1 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    clear hk
    induction k generalizing Y with
    | zero => exact le_rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply]
        exact (parentN_supset J hlam1 hlamB Y).trans (ih _)
  · intro h
    -- strong induction on the depth of `Y`
    have key : ∀ d (Y : Node J hlam1 hlamB), depthN J hlam1 hlamB Y = d → Y.1 ⊆ X.1 →
        (clusterTree J hlam1 hlamB).IsAnc X Y := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro Y hd hYX
        by_cases hXY : X = Y
        · rw [hXY]
        by_cases hYr : Y = rootN J hlam1 hlamB
        · exfalso; apply hXY
          apply Subtype.ext
          rw [hYr] at hYX ⊢
          exact subset_antisymm (subset_univ _) hYX
        have hss : Y.1 ⊂ X.1 := ssubset_of_subset_of_ne hYX fun he => hXY (Subtype.ext he.symm)
        have hPX := (parentN_spec J hlam1 hlamB hYr).2 X (mem_filter.mpr ⟨mem_univ _, hss⟩)
        have hdp := depthN_parent J hlam1 hlamB hYr
        have := ih _ (by omega) (parentN J hlam1 hlamB Y) rfl hPX
        exact RootedTree.isAnc_trans this (RootedTree.isAnc_parent (T := clusterTree J hlam1 hlamB) Y)
    exact key _ Y rfl h

/-- The hierarchy of the cluster family; its leaves are the singletons. -/
noncomputable def clusterHier : Hier V (Node J hlam1 hlamB) where
  T := clusterTree J hlam1 hlamB
  leaf v := ⟨{v}, singleton_mem_clusters J hlam1 hlamB _ (good_univ J hlam1) v (mem_univ v)⟩
  leaf_inj v w h := by
    have := congrArg Subtype.val h
    simpa using this

theorem cluster_eq (X : Node J hlam1 hlamB) : (clusterHier J hlam1 hlamB).cluster X = X.1 := by
  ext v
  rw [Hier.mem_cluster]
  show (clusterTree J hlam1 hlamB).IsAnc X _ ↔ _
  rw [isAnc_iff]
  exact singleton_subset_iff

/-- The children of a cluster are exactly its chosen parts. -/
theorem mem_children_iff (X C : Node J hlam1 hlamB) :
    C ∈ (clusterHier J hlam1 hlamB).children X ↔ C.1 ∈ bpart J hlam1 hlamB X.1 := by
  have hgU := good_univ J hlam1
  rw [Hier.mem_children]
  show C ≠ rootN J hlam1 hlamB ∧ parentN J hlam1 hlamB C = X ↔ _
  constructor
  · rintro ⟨hCr, hpar⟩
    obtain ⟨hP, hmin⟩ := parentN_spec J hlam1 hlamB hCr
    rw [hpar] at hP hmin
    have hCX := (mem_filter.mp hP).2
    have hCin := mem_clusters_of_subset J hlam1 hlamB _ hgU C.1 C.2 X.1 X.2 hCX.1
    rcases (mem_clusters J hlam1 hlamB).mp hCin with he | ⟨D, hD, hCD⟩
    · exact absurd he (Finset.ssubset_iff_subset_ne.mp hCX).2
    have hDsub := subset_of_mem_bpart J hlam1 hlamB hD
    have hgD := good_of_mem_bpart J hlam1 hlamB hD
    have hCDsub := (clusters_good J hlam1 hlamB D hgD C.1 hCD).1
    have hDmem : D ∈ clusters J hlam1 hlamB (univ : Finset V) :=
      clusters_subset_of_mem J hlam1 hlamB _ X.1 X.2 ((mem_clusters J hlam1 hlamB).mpr
        (Or.inr ⟨D, hD, self_mem_clusters J hlam1 hlamB D⟩))
    by_cases hCDe : C.1 = D
    · rw [hCDe]; exact hD
    · exfalso
      have hlt : C.1 ⊂ D := ssubset_of_subset_of_ne hCDsub hCDe
      have hXD : X.1 ⊆ D := hmin ⟨D, hDmem⟩ (mem_filter.mpr ⟨mem_univ _, hlt⟩)
      have hcard := bpart_card_lt J hlam1 hlamB hD
      have := card_le_card hXD
      omega
  · intro hC
    have hlt := bpart_card_lt J hlam1 hlamB hC
    have hCX : C.1 ⊂ X.1 := ssubset_of_subset_of_ne (subset_of_mem_bpart J hlam1 hlamB hC)
      fun he => by rw [he] at hlt; omega
    have hCr : C ≠ rootN J hlam1 hlamB := fun he => by
      have hCu : C.1 = univ := by rw [he]; rfl
      have := card_le_univ X.1
      rw [hCu, card_univ] at hlt
      omega
    refine ⟨hCr, ?_⟩
    obtain ⟨hP, hmin⟩ := parentN_spec J hlam1 hlamB hCr
    have hPX := hmin X (mem_filter.mpr ⟨mem_univ _, hCX⟩)
    by_contra hne
    set P := parentN J hlam1 hlamB C
    have hCP := (mem_filter.mp hP).2
    have hPne : P.1 ≠ X.1 := fun h => hne (Subtype.ext h)
    have hPin := mem_clusters_of_subset J hlam1 hlamB _ hgU P.1 P.2 X.1 X.2 hPX
    rcases (mem_clusters J hlam1 hlamB).mp hPin with he | ⟨D, hD, hPD⟩
    · exact hPne he
    have hgD := good_of_mem_bpart J hlam1 hlamB hD
    have hPDsub := (clusters_good J hlam1 hlamB D hgD P.1 hPD).1
    -- `C ⊆ P ⊆ D` with `C`, `D` parts of `X`, so `C = D ⊇ P ⊋ C`
    have hCD : C.1 = D := by
      by_contra hCD
      obtain ⟨v, hv⟩ := (node_good J hlam1 hlamB C).1
      exact disjoint_left.mp (disjoint_of_mem_bpart J hlam1 hlamB (node_good J hlam1 hlamB X)
        hC hD hCD) hv (hPDsub (hCP.1 hv))
    rw [← hCD] at hPDsub
    exact (Finset.ssubset_iff_subset_ne.mp hCP).2 (subset_antisymm hCP.1 hPDsub)

omit [Nonempty V] in
theorem bpart_small {P C : Finset V} (hC : C ∈ bpart J hlam1 hlamB P) :
    6 * C.card ≤ 5 * P.card := by
  classical
  by_cases h : 2 ≤ P.card ∧ Bandwidth J P lam
  · exact (bpart_spec J hlam1 hlamB h.1 h.2).2.2.1 C hC
  · rw [bpart_eq_empty J hlam1 hlamB h] at hC; exact absurd hC (Finset.notMem_empty C)

/-- Sizes shrink by `5/6` per level: `6^d |X| ≤ 5^d n`. -/
theorem pow_card_le (X : Node J hlam1 hlamB) :
    6 ^ depthN J hlam1 hlamB X * X.1.card ≤ 5 ^ depthN J hlam1 hlamB X * Fintype.card V := by
  have key : ∀ d (X : Node J hlam1 hlamB), depthN J hlam1 hlamB X = d →
      6 ^ d * X.1.card ≤ 5 ^ d * Fintype.card V := by
    intro d
    induction d with
    | zero =>
        intro X hX
        simp only [pow_zero, one_mul]
        exact card_le_univ _
    | succ d ih =>
        intro X hX
        have hXr : X ≠ rootN J hlam1 hlamB := by
          rintro rfl; unfold depthN at hX; rw [strictSup_root] at hX; simp at hX
        have hdp := depthN_parent J hlam1 hlamB hXr
        have hih := ih (parentN J hlam1 hlamB X) (by omega)
        have hchild : X ∈ (clusterHier J hlam1 hlamB).children (parentN J hlam1 hlamB X) :=
          Hier.mem_children.mpr ⟨hXr, rfl⟩
        have hsm := bpart_small J hlam1 hlamB ((mem_children_iff J hlam1 hlamB _ X).mp hchild)
        calc 6 ^ (d + 1) * X.1.card = 6 ^ d * (6 * X.1.card) := by ring
          _ ≤ 6 ^ d * (5 * (parentN J hlam1 hlamB X).1.card) := by gcongr
          _ = 5 * (6 ^ d * (parentN J hlam1 hlamB X).1.card) := by ring
          _ ≤ 5 * (5 ^ d * Fintype.card V) := by gcongr
          _ = 5 ^ (d + 1) * Fintype.card V := by ring
  exact key _ X rfl

/-- **Milestone 5, the bound on the cluster hierarchy.** -/
theorem rep_le_clusterHier {D : ℕ} (hD : ∀ X, depthN J hlam1 hlamB X ≤ D) (S : Finset V) :
    (clusterHier J hlam1 hlamB).rep ((clusterHier J hlam1 hlamB).canon J) S ≤
      26 * lam * (D + 1) * J.cut S := by
  have hlam0 : 0 ≤ lam := by linarith
  have h := Hier.rep_le_of_local (clusterHier J hlam1 hlamB) J S (lam := lam) (δ := 25 * lam)
    (D := D) hlam0 (by positivity) ?_ ?_ ?_ ?_ hD
  · calc _ ≤ (lam + 25 * lam) * (D + 1) * J.cut S := h
      _ = 26 * lam * (D + 1) * J.cut S := by ring
  · -- leaf nodes are childless
    intro v
    ext C
    simp only [Finset.notMem_empty, iff_false]
    intro hC
    have hmem := (mem_children_iff J hlam1 hlamB _ C).mp hC
    have hlt : C.1.card < ({v} : Finset V).card := bpart_card_lt J hlam1 hlamB hmem
    rw [card_singleton] at hlt
    have := (node_good J hlam1 hlamB C).1.card_pos
    omega
  · intro v; rw [cluster_eq]; rfl
  · intro X; rw [cluster_eq]; exact (node_good J hlam1 hlamB X).2
  · intro X hX U hU hUc
    rw [cluster_eq] at hU hUc ⊢
    have h2 : 2 ≤ X.1.card := by
      by_contra hlt
      push Not at hlt
      have h1 : X.1.card = 1 := by have := (node_good J hlam1 hlamB X).1.card_pos; omega
      obtain ⟨v, hv⟩ := card_eq_one.mp h1
      apply hX
      exact ⟨v, Subtype.ext hv.symm⟩
    have hcw := (bpart_spec J hlam1 hlamB h2 (node_good J hlam1 hlamB X).2).2.2.2 U hU hUc
    -- the children sum is the parts sum
    have himg : ((clusterHier J hlam1 hlamB).children X).image Subtype.val =
        bpart J hlam1 hlamB X.1 := by
      ext C
      simp only [mem_image]
      constructor
      · rintro ⟨c, hc, rfl⟩; exact (mem_children_iff J hlam1 hlamB X c).mp hc
      · intro hC
        have hCmem : C ∈ clusters J hlam1 hlamB (univ : Finset V) :=
          clusters_subset_of_mem J hlam1 hlamB _ X.1 X.2 ((mem_clusters J hlam1 hlamB).mpr
            (Or.inr ⟨C, hC, self_mem_clusters J hlam1 hlamB C⟩))
        exact ⟨⟨C, hCmem⟩, (mem_children_iff J hlam1 hlamB X ⟨C, hCmem⟩).mpr hC, rfl⟩
    have hsum : ∑ c ∈ (clusterHier J hlam1 hlamB).children X,
        J.cross (U ∩ (clusterHier J hlam1 hlamB).cluster c)
          ((clusterHier J hlam1 hlamB).cluster c)ᶜ =
        ∑ C ∈ bpart J hlam1 hlamB X.1, J.cross (U ∩ C) Cᶜ := by
      rw [← himg, sum_image fun a _ b _ h => Subtype.ext h]
      exact sum_congr rfl fun c _ => by rw [cluster_eq]
    rw [hsum]
    exact hcw

end Tree

end Hierarchy
end CutQueryComplexity
