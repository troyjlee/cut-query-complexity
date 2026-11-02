import CutQueryComplexity.TwoRespecting.Tree
import CutQueryComplexity.Graph.ArborescencePacking
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # A finite rooted-tree centroid

Choose a deepest vertex whose subtree has at least half the vertices. The
component toward the original root, and every child subtree, each have at
most half the vertices. This is the balancing lemma needed at each recursive
node of the connected-tree certificate.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset TwoRespecting.RootedTree

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The first time the parent walk exits at the root. -/
noncomputable def inArbHeight {r : V} (T : InArb r) (v : V) : ℕ :=
  Nat.find ((mem_inArbs.mp T.property).acyclic v)

theorem inArbHeight_pos {r : V} (T : InArb r) (v : V) : 0 < inArbHeight T v := by
  apply (Nat.find_pos _).2
  simp

theorem inArbHeight_root {r : V} (T : InArb r) : inArbHeight T r = 1 := by
  apply (Nat.find_eq_iff _).2
  constructor
  · simp [parentStep, (mem_inArbs.mp T.property).root]
  · intro m hm
    have hm0 : m = 0 := by omega
    subst m
    simp

theorem inArbHeight_parent {r : V} (T : InArb r) {u v : V}
    (hp : T.val u = some v) : inArbHeight T u = inArbHeight T v + 1 := by
  have hstep : parentStep T.val (some u) = some v := by simp [parentStep, hp]
  have hupper : inArbHeight T u ≤ inArbHeight T v + 1 := by
    apply Nat.find_min'
    rw [Function.iterate_succ_apply, hstep]
    exact Nat.find_spec ((mem_inArbs.mp T.property).acyclic v)
  have hu := inArbHeight_pos T u
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : inArbHeight T u ≠ 0)
  have hs := Nat.find_spec ((mem_inArbs.mp T.property).acyclic u)
  change (parentStep T.val)^[inArbHeight T u] (some u) = none at hs
  rw [hm, Function.iterate_succ_apply, hstep] at hs
  have hlower : inArbHeight T v ≤ m := Nat.find_min' _ hs
  omega

/-- Convert an actual arborescence parent map to the rooted-tree API. The
depth is derived from its proved termination, not supplied as a new premise. -/
noncomputable def inArbTree {r : V} (T : InArb r) : TwoRespecting.RootedTree V where
  root := r
  parent v := (T.val v).getD r
  depth v := inArbHeight T v - 1
  parent_root := by simp [(mem_inArbs.mp T.property).root]
  depth_root := by rw [inArbHeight_root]
  depth_parent v hv := by
    cases hp : T.val v with
    | none => exact ((mem_inArbs.mp T.property).nonroot v hv hp).elim
    | some u =>
      have hh := inArbHeight_parent T hp
      have hu := inArbHeight_pos T u
      simp only [Option.getD_some]
      omega

theorem inArbTree_parent {r : V} (T : InArb r) {u v : V}
    (hp : T.val u = some v) : (inArbTree T).parent u = v := by
  simp [inArbTree, hp]

/-- The two kinds of components after deleting a rooted-tree centroid obey
the half-size bound. The rootward component is the complement of its subtree. -/
theorem exists_subtree_centroid (T : TwoRespecting.RootedTree V) :
    ∃ c : V, 2 * (T.subtree c)ᶜ.card ≤ Fintype.card V ∧
      ∀ v : V, v ≠ T.root → T.parent v = c →
        2 * (T.subtree v).card ≤ Fintype.card V := by
  classical
  let heavy : Finset V := univ.filter fun v => Fintype.card V ≤ 2 * (T.subtree v).card
  have hroot : T.root ∈ heavy := by
    simp only [heavy, mem_filter, mem_univ, true_and, subtree_root, card_univ]
    omega
  obtain ⟨c, hc, hmax⟩ := heavy.exists_max_image T.depth ⟨T.root, hroot⟩
  have hheavy : Fintype.card V ≤ 2 * (T.subtree c).card := (mem_filter.mp hc).2
  refine ⟨c, ?_, fun v hv hp => ?_⟩
  · rw [card_compl]
    have hcard := card_le_univ (T.subtree c)
    omega
  · by_contra hlarge
    have hmem : v ∈ heavy := mem_filter.mpr ⟨mem_univ v, by omega⟩
    have hdepth := hmax v hmem
    have hpdepth := T.depth_parent v hv
    rw [hp] at hpdepth
    omega

/-- Balance an arbitrary finite vertex mass supported on `W`. The chosen
ambient vertex may lie outside `W`; in that case it partitions the mass for
free. This avoids rebuilding or rerooting a tree on each recursive component. -/
theorem exists_restricted_subtree_centroid (T : TwoRespecting.RootedTree V)
    (W : Finset V) (hW : W.Nonempty) :
    ∃ c : V, 2 * (W \ T.subtree c).card ≤ W.card ∧
      ∀ v : V, v ≠ T.root → T.parent v = c →
        2 * (W ∩ T.subtree v).card ≤ W.card := by
  classical
  let heavy : Finset V := univ.filter fun v => W.card < 2 * (W ∩ T.subtree v).card
  have hroot : T.root ∈ heavy := by
    have hpos := hW.card_pos
    simp only [heavy, mem_filter, mem_univ, true_and, subtree_root, inter_univ]
    omega

  obtain ⟨c, hc, hmax⟩ := heavy.exists_max_image T.depth ⟨T.root, hroot⟩
  have hheavy : W.card < 2 * (W ∩ T.subtree c).card := (mem_filter.mp hc).2
  refine ⟨c, ?_, fun v hv hp => ?_⟩
  · have hsplit : (W \ T.subtree c).card + (W ∩ T.subtree c).card = W.card := by
      rw [card_sdiff, inter_comm (T.subtree c) W]
      have hle := card_le_card (show W ∩ T.subtree c ⊆ W from inter_subset_left)
      omega
    omega
  · by_contra hlarge
    have hmem : v ∈ heavy := mem_filter.mpr ⟨mem_univ v, by omega⟩
    have hdepth := hmax v hmem
    have hpdepth := T.depth_parent v hv
    rw [hp] at hpdepth
    omega


omit [Fintype V] [DecidableEq V] in
/-- A strict descendant belongs to the subtree of a child of the ancestor. -/
theorem exists_child_ancestor (T : TwoRespecting.RootedTree V) {c x : V}
    (hx : T.IsAnc c x) (hxc : x ≠ c) :
    ∃ v : V, v ≠ T.root ∧ T.parent v = c ∧ T.IsAnc v x := by
  classical
  induction hd : T.depth x generalizing x with
  | zero =>
    have hxr := eq_root_of_depth_eq_zero hd
    have hcr := (hxr ▸ hx).eq_root_of_isAnc_root
    exact (hxc (hxr.trans hcr.symm)).elim
  | succ d ih =>
    have hxr : x ≠ T.root := by
      intro h
      rw [h, T.depth_root] at hd
      omega
    by_cases hp : T.parent x = c
    · exact ⟨x, hxr, hp, isAnc_refl x⟩
    · have hdp : T.depth (T.parent x) = d := by
        have h := T.depth_parent x hxr
        omega
      obtain ⟨v, hvr, hvc, hvx⟩ := ih
        (hx.isAnc_parent_of_ne (Ne.symm hxc)) hp hdp
      exact ⟨v, hvr, hvc, isAnc_trans hvx (isAnc_parent x)⟩

/-- Distinct children have disjoint subtrees. -/
theorem disjoint_child_subtrees (T : TwoRespecting.RootedTree V) {c u v : V}
    (hu : u ≠ T.root) (hv : v ≠ T.root) (hpu : T.parent u = c)
    (hpv : T.parent v = c) (hne : u ≠ v) :
    Disjoint (T.subtree u) (T.subtree v) := by
  have hd : T.depth u = T.depth v := by
    have hu' := T.depth_parent u hu
    have hv' := T.depth_parent v hv
    rw [hpu] at hu'
    rw [hpv] at hv'
    omega
  apply disjoint_subtree
  · intro h
    apply hne
    rw [h.eq_iterate, hd, Nat.sub_self, Function.iterate_zero_apply]
  · intro h
    apply hne
    symm
    rw [h.eq_iterate, hd, Nat.sub_self, Function.iterate_zero_apply]

/-- The actual pieces after deleting an ambient pivot, restricted to `W`. -/
noncomputable def separatorParts (T : TwoRespecting.RootedTree V) (W : Finset V) (c : V) :
    Finset (Finset V) :=
  insert (W \ T.subtree c)
    ((univ.filter fun v => v ≠ T.root ∧ T.parent v = c).image fun v => W ∩ T.subtree v)

theorem separatorParts_cases (T : TwoRespecting.RootedTree V) (W : Finset V) (c : V)
    {P : Finset V} (hP : P ∈ separatorParts T W c) :
    P = W \ T.subtree c ∨ ∃ v, v ≠ T.root ∧ T.parent v = c ∧ P = W ∩ T.subtree v := by
  rcases mem_insert.mp hP with h | h
  · exact Or.inl h
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp h
    exact Or.inr ⟨v, (mem_filter.mp hv).2.1, (mem_filter.mp hv).2.2, rfl⟩

theorem separatorParts_subset (T : TwoRespecting.RootedTree V) (W : Finset V) (c : V)
    {P : Finset V} (hP : P ∈ separatorParts T W c) : P ⊆ W := by
  rcases separatorParts_cases T W c hP with rfl | ⟨v, -, -, rfl⟩
  · exact sdiff_subset
  · exact inter_subset_left

theorem separatorParts_cover (T : TwoRespecting.RootedTree V) (W : Finset V) (c : V)
    {x : V} (hx : x ∈ W) (hxc : x ≠ c) :
    ∃ P ∈ separatorParts T W c, x ∈ P := by
  by_cases hcx : T.IsAnc c x
  · obtain ⟨v, hvr, hvc, hvx⟩ := exists_child_ancestor T hcx hxc
    refine ⟨W ∩ T.subtree v, mem_insert_of_mem (mem_image.mpr
      ⟨v, mem_filter.mpr ⟨mem_univ v, hvr, hvc⟩, rfl⟩), ?_⟩
    exact mem_inter.mpr ⟨hx, mem_subtree.mpr hvx⟩
  · exact ⟨W \ T.subtree c, mem_insert_self _ _, mem_sdiff.mpr ⟨hx, by simpa using hcx⟩⟩

theorem separatorParts_disjoint (T : TwoRespecting.RootedTree V) (W : Finset V) (c : V) :
    (separatorParts T W c : Set (Finset V)).PairwiseDisjoint id := by
  intro P hP Q hQ hne
  rcases separatorParts_cases T W c hP with rfl | ⟨u, hur, huc, rfl⟩ <;>
    rcases separatorParts_cases T W c hQ with rfl | ⟨v, hvr, hvc, rfl⟩
  · exact (hne rfl).elim
  · apply disjoint_left.mpr
    intro x hx hy
    apply (mem_sdiff.mp hx).2
    exact subtree_subset (hvc ▸ isAnc_parent v) (mem_inter.mp hy).2
  · apply disjoint_left.mpr
    intro x hx hy
    apply (mem_sdiff.mp hy).2
    exact subtree_subset (huc ▸ isAnc_parent u) (mem_inter.mp hx).2
  · have huv : u ≠ v := fun h => hne (h ▸ rfl)
    exact (disjoint_child_subtrees T hur hvr huc hvc huv).mono inter_subset_right inter_subset_right

theorem separatorParts_volume (T : TwoRespecting.RootedTree V) (W : Finset V) (c : V) :
    ∑ P ∈ separatorParts T W c, P.card ≤ W.card := by
  have hc := card_biUnion (separatorParts_disjoint T W c)
  simp only [id_eq] at hc
  rw [← hc]
  apply card_le_card
  intro x hx
  obtain ⟨P, hP, hxP⟩ := mem_biUnion.mp hx
  exact separatorParts_subset T W c hP hxP

/-- Connectivity in the parent tree, expressed by internal paths to a common
vertex. One-respected arborescence shores provide exactly these witnesses. -/
def ParentConnected (T : TwoRespecting.RootedTree V) (S : Finset V) : Prop :=
  ∃ x ∈ S, ∀ v ∈ S,
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ T.parent a = b) v x

/-- Membership of a separator part is unchanged along an edge avoiding the
pivot. This applies whether or not the pivot itself belongs to `W`. -/
theorem separatorParts_parent_iff (T : TwoRespecting.RootedTree V) (W : Finset V) (c : V)
    {P : Finset V} (hP : P ∈ separatorParts T W c) {u v : V}
    (hu : u ∈ W) (hv : v ∈ W) (huc : u ≠ c) (hvc : v ≠ c)
    (hp : T.parent u = v) : u ∈ P ↔ v ∈ P := by
  have hanc : T.IsAnc c u ↔ T.IsAnc c v := by
    constructor
    · intro h
      exact hp ▸ h.isAnc_parent_of_ne (Ne.symm huc)
    · intro h
      exact isAnc_trans h (hp ▸ isAnc_parent u)
  rcases separatorParts_cases T W c hP with rfl | ⟨w, -, hwc, rfl⟩
  · simpa only [mem_sdiff, hu, hv, true_and, mem_subtree] using not_congr hanc
  · have hw : T.IsAnc w u ↔ T.IsAnc w v := by
      constructor
      · intro h
        have hwu : w ≠ u := by
          intro heq
          have := heq ▸ hwc
          exact hvc (hp.symm.trans this)
        exact hp ▸ h.isAnc_parent_of_ne hwu
      · intro h
        exact isAnc_trans h (hp ▸ isAnc_parent u)
    simpa only [mem_inter, hu, hv, true_and, mem_subtree] using hw

/-- A connected shore avoiding the pivot lies wholly in one actual part.
In particular, an outside pivot requires no local flow certificate. -/
theorem exists_separatorPart_of_connected (T : TwoRespecting.RootedTree V)
    (W : Finset V) (c : V) {S : Finset V} (hSW : S ⊆ W)
    (hS : ParentConnected T S) (hcS : c ∉ S) :
    ∃ P ∈ separatorParts T W c, S ⊆ P := by
  obtain ⟨x, hx, hpaths⟩ := hS
  obtain ⟨P, hP, hxP⟩ := separatorParts_cover T W c (hSW hx) (fun h => hcS (h ▸ hx))
  refine ⟨P, hP, fun v hv => ?_⟩
  have hpath_iff : ∀ {a b : V},
      Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ T.parent a = b) a b →
      (a ∈ P ↔ b ∈ P) := by
    intro a b hab
    induction hab with
    | refl => rfl
    | @tail y z hpath hstep ih =>
      exact ih.trans (separatorParts_parent_iff T W c hP (hSW hstep.1)
        (hSW hstep.2.1) (fun h => hcS (h ▸ hstep.1))
        (fun h => hcS (h ▸ hstep.2.1)) hstep.2.2)
  exact (hpath_iff (hpaths v hv)).mpr hxP

/-- Construct the separator nodes by cardinality-halving recursion. A pivot
outside its current component produces no node and no query cost. Every node
that is kept has its pivot inside its component. -/
theorem exists_centroid_nodes (T : TwoRespecting.RootedTree V) :
    ∀ d : ℕ, ∀ W : Finset V, W.card < 2 ^ d →
      ∃ nodes : Finset (Finset V × V),
        (∀ p ∈ nodes, p.1 ⊆ W ∧ p.2 ∈ p.1) ∧
        (∑ p ∈ nodes, p.1.card) ≤ W.card * d ∧
        ∀ S : Finset V, S ⊆ W → ParentConnected T S →
          ∃ p ∈ nodes, S ⊆ p.1 ∧ p.2 ∈ S := by
  classical
  intro d
  induction d with
  | zero =>
    intro W hW
    have hw : W = ∅ := card_eq_zero.mp (by simpa using hW)
    subst W
    refine ⟨∅, by simp, by simp, ?_⟩
    rintro S hS ⟨x, hx, -⟩
    exact (notMem_empty x (hS hx)).elim
  | succ d ih =>
    intro W hsize
    by_cases hW : W.Nonempty
    · obtain ⟨c, hroot, hchild⟩ := exists_restricted_subtree_centroid T W hW
      let parts := separatorParts T W c
      have hsmall : ∀ P ∈ parts, P.card < 2 ^ d := by
        intro P hP
        have hhalf : 2 * P.card ≤ W.card := by
          rcases separatorParts_cases T W c hP with rfl | ⟨v, hvr, hvc, rfl⟩
          · exact hroot
          · exact hchild v hvr hvc
        rw [pow_succ] at hsize
        omega
      have hex : ∀ P : Finset V, ∃ N : Finset (Finset V × V),
          (∀ p ∈ N, p.1 ⊆ P ∧ p.2 ∈ p.1) ∧
          (∑ p ∈ N, p.1.card) ≤ P.card * d ∧
          (P ∈ parts → ∀ S : Finset V, S ⊆ P → ParentConnected T S →
            ∃ p ∈ N, S ⊆ p.1 ∧ p.2 ∈ S) := by
        intro P
        by_cases hP : P ∈ parts
        · obtain ⟨N, hn, hv, hc⟩ := ih P (hsmall P hP)
          exact ⟨N, hn, hv, fun _ => hc⟩
        · exact ⟨∅, by simp, by simp, fun h => (hP h).elim⟩
      choose N hvalid hvolume hcover using hex
      let R := parts.biUnion N
      have hRvalid : ∀ p ∈ R, p.1 ⊆ W ∧ p.2 ∈ p.1 := by
        intro p hp
        obtain ⟨P, hP, hp⟩ := mem_biUnion.mp hp
        exact ⟨(hvalid P p hp).1.trans (separatorParts_subset T W c hP),
          (hvalid P p hp).2⟩
      have hNdisj : (parts : Set (Finset V)).PairwiseDisjoint N := by
        intro P hP Q hQ hne
        apply disjoint_left.mpr
        intro p hp hq
        exact disjoint_left.mp (separatorParts_disjoint T W c hP hQ hne)
          ((hvalid P p hp).1 (hvalid P p hp).2)
          ((hvalid Q p hq).1 (hvalid Q p hq).2)
      have hRvolume : (∑ p ∈ R, p.1.card) ≤ W.card * d := by
        calc (∑ p ∈ R, p.1.card) = ∑ P ∈ parts, ∑ p ∈ N P, p.1.card := sum_biUnion hNdisj
          _ ≤ ∑ P ∈ parts, P.card * d := sum_le_sum fun P _ => hvolume P
          _ = (∑ P ∈ parts, P.card) * d := (sum_mul ..).symm
          _ ≤ W.card * d := Nat.mul_le_mul_right d (separatorParts_volume T W c)
      let nodes := if c ∈ W then insert (W, c) R else R
      have hRnodes : R ⊆ nodes := by
        by_cases hc : c ∈ W <;> simp [nodes, hc]
      refine ⟨nodes, ?_, ?_, ?_⟩
      · intro p hp
        by_cases hc : c ∈ W
        · rw [show nodes = insert (W, c) R from ite_eq_left hc] at hp
          rcases mem_insert.mp hp with rfl | hp
          · exact ⟨subset_refl W, hc⟩
          · exact hRvalid p hp
        · rw [show nodes = R from ite_eq_right hc] at hp
          exact hRvalid p hp
      · have hnodes : (∑ p ∈ nodes, p.1.card) ≤ W.card + ∑ p ∈ R, p.1.card := by
          by_cases hc : c ∈ W
          · rw [show nodes = insert (W, c) R from ite_eq_left hc]
            by_cases hm : (W, c) ∈ R
            · rw [insert_eq_of_mem hm]
              omega
            · rw [sum_insert hm]
          · rw [show nodes = R from ite_eq_right hc]
            omega
        calc (∑ p ∈ nodes, p.1.card) ≤ W.card + ∑ p ∈ R, p.1.card := hnodes
          _ ≤ W.card + W.card * d := Nat.add_le_add le_rfl hRvolume
          _ = W.card * (d + 1) := by ring
      · intro S hSW hS
        by_cases hcS : c ∈ S
        · have hcW := hSW hcS
          refine ⟨(W, c), ?_, hSW, hcS⟩
          simp [nodes, hcW]
        · obtain ⟨P, hP, hSP⟩ := exists_separatorPart_of_connected T W c hSW hS hcS
          obtain ⟨p, hp, hSp, hpS⟩ := hcover P hP S hSP hS
          exact ⟨p, hRnodes (mem_biUnion.mpr ⟨P, hP, hp⟩), hSp, hpS⟩
    · have hw := not_nonempty_iff_eq_empty.mp hW
      subst W
      refine ⟨∅, by simp, by simp, ?_⟩
      rintro S hS ⟨x, hx, -⟩
      exact (notMem_empty x (hS hx)).elim

/-- A fully constructed centroid decomposition with total component volume
at most `|W| ceil(log₂(|W|+1))`, covering every parent-connected shore in `W`. -/
theorem exists_centroid_decomposition (T : TwoRespecting.RootedTree V) (W : Finset V) :
    ∃ nodes : Finset (Finset V × V),
      (∀ p ∈ nodes, p.1 ⊆ W ∧ p.2 ∈ p.1) ∧
      (∑ p ∈ nodes, p.1.card) ≤ W.card * Nat.clog 2 (W.card + 1) ∧
      ∀ S : Finset V, S ⊆ W → ParentConnected T S →
        ∃ p ∈ nodes, S ⊆ p.1 ∧ p.2 ∈ S := by
  apply exists_centroid_nodes T
  have h := Nat.le_pow_clog (by decide : 1 < 2) (W.card + 1)
  omega

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_subtree_centroid

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_restricted_subtree_centroid

#print axioms CutQueryComplexity.DirectedCertificate.Completion.inArbTree

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_centroid_decomposition
