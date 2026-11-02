import CutQueryComplexity.Certificate.GomoryHu.Contraction
import CutQueryComplexity.MinCut.RootedTree
import CutQueryComplexity.DirectedCertificate.Completion.Centroid

set_option autoImplicit false

/-! # Tree paths and the boundary volume needed by structural certificates

The conversion to the existing parity API is explicit. Fundamental correctness
implies all-pairs minimum shores selected using only the supplied tree and its
weights. Boundary volume counts original tree edges, including zero edges.
-/

namespace CutQueryComplexity.Certificate.GomoryHu

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def legacyTree (T : TwoRespecting.RootedTree V) : CutQueryComplexity.RootedTree V :=
  ⟨T.root, T.parent, T.depth, T.parent_root, T.depth_root, T.depth_parent⟩

def pathEdges (T : TwoRespecting.RootedTree V) (s t : V) : Finset V :=
  (edges T).filter fun v => ¬ (s ∈ T.subtree v ↔ t ∈ T.subtree v)

@[simp] theorem mem_pathEdges (T : TwoRespecting.RootedTree V) (s t v : V) :
    v ∈ pathEdges T s t ↔ v ≠ T.root ∧ ¬ (s ∈ T.subtree v ↔ t ∈ T.subtree v) := by
  simp [pathEdges]

/-- Every separating shore crosses an edge on the actual tree path. -/
theorem exists_path_crossing (T : TwoRespecting.RootedTree V) {s t : V}
    {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    ∃ v ∈ pathEdges T s t, ¬ (v ∈ S ↔ T.parent v ∈ S) := by
  by_contra hn
  have hNo : ∀ v ∈ pathEdges T s t, v ∈ S ↔ T.parent v ∈ S := by
    intro v hv
    by_contra h
    exact hn ⟨v, hv, h⟩
  have he : (legacyTree T).crossAbove S s = (legacyTree T).crossAbove S t := by
    ext v
    simp only [CutQueryComplexity.RootedTree.crossAbove, mem_filter]
    by_cases hv : v ∈ (legacyTree T).crossSet S
    · simp only [hv, true_and]
      change T.IsAnc v s ↔ T.IsAnc v t
      by_contra hanc
      have hcross : v ≠ T.root ∧ ¬ (v ∈ S ↔ T.parent v ∈ S) := by
        have hlegacy : (legacyTree T).Crosses S v := (Finset.mem_filter.mp hv).2
        exact hlegacy
      apply hcross.2 (hNo v _)
      apply (mem_pathEdges T s t v).mpr
      exact ⟨hcross.1, by simpa only [TwoRespecting.RootedTree.mem_subtree] using hanc⟩
    · simp [hv]
  have hspar := (legacyTree T).mem_iff_parity S s
  have htpar := (legacyTree T).mem_iff_parity S t
  rw [he] at hspar
  exact ht (htpar.mpr (hspar.mp hs))

theorem pathEdges_nonempty (T : TwoRespecting.RootedTree V) {s t : V} (hst : s ≠ t) :
    (pathEdges T s t).Nonempty := by
  obtain ⟨v, hv, _⟩ := exists_path_crossing T (S := {s}) (mem_singleton_self s)
    (by simpa using hst.symm)
  exact ⟨v, hv⟩

def pathShore (T : TwoRespecting.RootedTree V) (s v : V) : Finset V :=
  if s ∈ T.subtree v then T.subtree v else (T.subtree v)ᶜ

theorem pathShore_separates (T : TwoRespecting.RootedTree V) {s t v : V}
    (hv : v ∈ pathEdges T s t) : s ∈ pathShore T s v ∧ t ∉ pathShore T s v := by
  have h := (mem_pathEdges T s t v).mp hv
  by_cases hs : s ∈ T.subtree v
  · have ht : t ∉ T.subtree v := fun ht => h.2 ⟨fun _ => ht, fun _ => hs⟩
    simp [pathShore, hs, ht]
  · have ht : t ∈ T.subtree v := by
      by_contra ht
      exact h.2 ⟨fun h => (hs h).elim, fun h => (ht h).elim⟩
    simp [pathShore, hs, ht]

theorem FundamentalCorrect.crossing_lower {G : WeightedGraph V}
    {T : TwoRespecting.RootedTree V} {tau : V → ℝ} (hT : FundamentalCorrect G T tau)
    {v : V} (hv : v ≠ T.root) {S : Finset V}
    (hcross : ¬ (v ∈ S ↔ T.parent v ∈ S)) : tau v ≤ G.cut S := by
  by_cases hs : v ∈ S
  · have ht : T.parent v ∉ S := fun ht => hcross ⟨fun _ => ht, fun _ => hs⟩
    exact hT.lower hv hs ht
  · have ht : T.parent v ∈ S := by
      by_contra ht
      exact hcross ⟨fun h => (hs h).elim, fun h => (ht h).elim⟩
    simpa only [cut_compl] using hT.lower hv (mem_compl.mpr hs)
      (fun h => mem_compl.mp h ht)

/-- The minimum path edge and its oriented shore are selected before the graph. -/
theorem exists_public_pair_shore (T : TwoRespecting.RootedTree V) (tau : V → ℝ)
    {s t : V} (hst : s ≠ t) :
    ∃ v ∈ pathEdges T s t, (∀ w ∈ pathEdges T s t, tau v ≤ tau w) ∧
      ∀ G : WeightedGraph V, FundamentalCorrect G T tau →
        IsSTMinCut G s t (pathShore T s v) ∧ G.cut (pathShore T s v) = tau v := by
  obtain ⟨v, hv, hmin⟩ := exists_min_image (pathEdges T s t) tau (pathEdges_nonempty T hst)
  refine ⟨v, hv, hmin, fun G hT => ?_⟩
  have hvroot := ((mem_pathEdges T s t v).mp hv).1
  have hval : G.cut (pathShore T s v) = tau v := by
    unfold pathShore
    split_ifs <;> simp [(hT v hvroot).1]
  refine ⟨⟨(pathShore_separates T hv).1, (pathShore_separates T hv).2, ?_⟩, hval⟩
  intro S hs ht
  obtain ⟨w, hw, hcross⟩ := exists_path_crossing T hs ht
  rw [hval]
  exact (hmin w hw).trans
    (hT.crossing_lower ((mem_pathEdges T s t w).mp hw).1 hcross)

/-- One whole-tree certificate also fixes one public shore/value for each pair. -/
theorem TreeCertificate.pair_shore {G : WeightedGraph V}
    {T : TwoRespecting.RootedTree V} {tau : V → ℝ} {Q : Finset (Finset V)}
    (h : TreeCertificate G T tau Q) {s t : V} (hst : s ≠ t) :
    ∃ S : Finset V, ∃ a : ℝ, ∀ H : WeightedGraph V, Consistent G H Q →
      IsSTMinCut H s t S ∧ H.cut S = a := by
  obtain ⟨v, _, _, hv⟩ := exists_public_pair_shore T tau hst
  exact ⟨pathShore T s v, tau v, fun H hH => hv H (h.2 H hH)⟩

def boundary (T : TwoRespecting.RootedTree V) (U : Finset V) : Finset V :=
  (edges T).filter fun v => ¬ (v ∈ U ↔ T.parent v ∈ U)

def frontierVolume (T : TwoRespecting.RootedTree V) (U : Finset V) : ℕ :=
  U.card + (boundary T U).card

/-- Counting incidences inside a shore upper-bounds its tree boundary size. -/
theorem boundary_card_le_degree_sum (T : TwoRespecting.RootedTree V) (U : Finset V) :
    (boundary T U).card ≤ ∑ u ∈ U, degree T u := by
  have hd (u : V) : degree T u =
      ∑ v ∈ edges T, if v = u ∨ T.parent v = u then (1 : ℕ) else 0 := by
    simp [degree, ← sum_filter]
  have he (v : V) (hv : v ∈ edges T) :
      (∑ u ∈ U, if v = u ∨ T.parent v = u then (1 : ℕ) else 0) =
        (if v ∈ U then 1 else 0) + (if T.parent v ∈ U then 1 else 0) := by
    have hne : v ≠ T.parent v :=
      (TwoRespecting.RootedTree.parent_ne_self (T := T) ((mem_edges T v).mp hv)).symm
    calc
      _ = ∑ u ∈ U, ((if v = u then (1 : ℕ) else 0) +
          (if T.parent v = u then 1 else 0)) := by
        apply sum_congr rfl
        intro u _
        by_cases h₁ : v = u <;> by_cases h₂ : T.parent v = u <;> simp_all
      _ = _ := by rw [sum_add_distrib]; simp [eq_comm]
  have hsum : (∑ u ∈ U, degree T u) =
      ∑ v ∈ edges T, ((if v ∈ U then (1 : ℕ) else 0) +
        (if T.parent v ∈ U then 1 else 0)) := by
    simp_rw [hd]
    rw [sum_comm]
    exact sum_congr rfl he
  rw [hsum]
  have hb : (boundary T U).card =
      ∑ v ∈ edges T, if ¬ (v ∈ U ↔ T.parent v ∈ U) then (1 : ℕ) else 0 := by
    rw [boundary, card_eq_sum_ones, sum_filter]
  rw [hb]
  apply sum_le_sum
  intro v _
  by_cases h₁ : v ∈ U <;> by_cases h₂ : T.parent v ∈ U <;> simp [h₁, h₂]

/-- The `3n−2` ledger holds for every genuinely disjoint family of active sets. -/
theorem disjoint_frontier_volume (T : TwoRespecting.RootedTree V)
    (parts : Finset (Finset V)) (hd : (parts : Set (Finset V)).PairwiseDisjoint id) :
    (∑ U ∈ parts, frontierVolume T U) ≤ 3 * Fintype.card V - 2 := by
  have hcard : (∑ U ∈ parts, U.card) ≤ Fintype.card V := by
    calc
      (∑ U ∈ parts, U.card) = (parts.biUnion id).card := (card_biUnion hd).symm
      _ ≤ Fintype.card V := card_le_univ _
  have hdegree : (∑ U ∈ parts, ∑ u ∈ U, degree T u) ≤
      ∑ u : V, degree T u := by
    calc
      (∑ U ∈ parts, ∑ u ∈ U, degree T u) =
          ∑ u ∈ parts.biUnion id, degree T u := (sum_biUnion (f := degree T) hd).symm
      _ ≤ ∑ u : V, degree T u := sum_le_sum_of_subset (subset_univ _)
  have hb : (∑ U ∈ parts, (boundary T U).card) ≤
      ∑ U ∈ parts, ∑ u ∈ U, degree T u :=
    sum_le_sum fun U _ => boundary_card_le_degree_sum T U
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨T.root⟩
  simp only [frontierVolume, sum_add_distrib]
  rw [sum_degree] at hdegree
  omega

/-- In a connected active tree component a balanced pivot actually lies inside it. -/
theorem exists_connected_centroid (T : TwoRespecting.RootedTree V) (U : Finset V)
    (hU : DirectedCertificate.Completion.ParentConnected T U) :
    ∃ c ∈ U, ∀ P ∈ DirectedCertificate.Completion.separatorParts T U c,
      2 * P.card ≤ U.card := by
  have hne : U.Nonempty := by obtain ⟨x, hx, _⟩ := hU; exact ⟨x, hx⟩
  obtain ⟨c, hroot, hchild⟩ :=
    DirectedCertificate.Completion.exists_restricted_subtree_centroid T U hne
  have hhalf : ∀ P ∈ DirectedCertificate.Completion.separatorParts T U c,
      2 * P.card ≤ U.card := by
    intro P hP
    rcases DirectedCertificate.Completion.separatorParts_cases T U c hP with
      rfl | ⟨v, hv, hvc, rfl⟩
    · exact hroot
    · exact hchild v hv hvc
  have hc : c ∈ U := by
    by_contra hc
    obtain ⟨P, hP, hUP⟩ := DirectedCertificate.Completion.exists_separatorPart_of_connected
      T U c (subset_refl U) hU hc
    have h₁ := hhalf P hP
    have h₂ := card_le_card hUP
    have h₃ := hne.card_pos
    omega
  exact ⟨c, hc, hhalf⟩

/-- A set contains both endpoints of every edge on a path between its vertices.
This is a purely combinatorial predicate, independent of graph capacities. -/
def PathClosed (T : TwoRespecting.RootedTree V) (U : Finset V) : Prop :=
  ∀ s ∈ U, ∀ t ∈ U, ∀ e ∈ pathEdges T s t, e ∈ U ∧ T.parent e ∈ U

theorem pathClosed_univ (T : TwoRespecting.RootedTree V) : PathClosed T univ :=
  fun _ _ _ _ _ _ => ⟨mem_univ _, mem_univ _⟩

theorem PathClosed.inter {T : TwoRespecting.RootedTree V} {U W : Finset V}
    (hU : PathClosed T U) (hW : PathClosed T W) : PathClosed T (U ∩ W) := by
  intro s hs t ht e he
  have h₁ := hU s (mem_inter.mp hs).1 t (mem_inter.mp ht).1 e he
  have h₂ := hW s (mem_inter.mp hs).2 t (mem_inter.mp ht).2 e he
  exact ⟨mem_inter.mpr ⟨h₁.1, h₂.1⟩, mem_inter.mpr ⟨h₁.2, h₂.2⟩⟩

theorem pathEdges_symm (T : TwoRespecting.RootedTree V) (s t : V) :
    pathEdges T s t = pathEdges T t s := by
  ext e
  simp only [mem_pathEdges]
  tauto

theorem subtree_pathClosed (T : TwoRespecting.RootedTree V) (v : V) :
    PathClosed T (T.subtree v) := by
  have haux : ∀ s ∈ T.subtree v, ∀ t ∈ T.subtree v, ∀ e,
      s ∈ T.subtree e → t ∉ T.subtree e → e ∈ T.subtree v ∧ T.parent e ∈ T.subtree v := by
    intro s hs t ht e hes het
    have hve : T.IsAnc v e := by
      rcases TwoRespecting.RootedTree.isAnc_total_of_common
        (TwoRespecting.RootedTree.mem_subtree.mp hs)
        (TwoRespecting.RootedTree.mem_subtree.mp hes) with h | h
      · exact h
      · exact (het (TwoRespecting.RootedTree.mem_subtree.mpr
          (TwoRespecting.RootedTree.isAnc_trans h
            (TwoRespecting.RootedTree.mem_subtree.mp ht)))).elim
    have hne : v ≠ e := by intro h; subst e; exact het ht
    exact ⟨TwoRespecting.RootedTree.mem_subtree.mpr hve,
      TwoRespecting.RootedTree.mem_subtree.mpr (hve.isAnc_parent_of_ne hne)⟩
  intro s hs t ht e he
  have hx := ((mem_pathEdges T s t e).mp he).2
  by_cases hse : s ∈ T.subtree e
  · exact haux s hs t ht e hse (fun hte => hx ⟨fun _ => hte, fun _ => hse⟩)
  · have hte : t ∈ T.subtree e := by tauto
    exact haux t ht s hs e hte hse

theorem compl_subtree_pathClosed (T : TwoRespecting.RootedTree V) (v : V) :
    PathClosed T (T.subtree v)ᶜ := by
  intro s hs t ht e he
  have hx := ((mem_pathEdges T s t e).mp he).2
  have hex : ∃ x, x ∈ (T.subtree v)ᶜ ∧ x ∈ T.subtree e := by
    by_cases hse : s ∈ T.subtree e
    · exact ⟨s, hs, hse⟩
    · exact ⟨t, ht, by tauto⟩
  obtain ⟨x, hxv, hxe⟩ := hex
  have hev : e ∉ T.subtree v := by
    intro h
    exact mem_compl.mp hxv (TwoRespecting.RootedTree.subtree_subset
      (TwoRespecting.RootedTree.mem_subtree.mp h) hxe)
  have hpv : T.parent e ∉ T.subtree v := by
    intro h
    apply hev
    exact TwoRespecting.RootedTree.mem_subtree.mpr
      (TwoRespecting.RootedTree.isAnc_trans (TwoRespecting.RootedTree.mem_subtree.mp h)
        (TwoRespecting.RootedTree.isAnc_parent e))
  exact ⟨mem_compl.mpr hev, mem_compl.mpr hpv⟩

/-- Only the edge above `v` crosses its fundamental shore. -/
theorem crosses_subtree_iff (T : TwoRespecting.RootedTree V) {v e : V}
    (hv : v ≠ T.root) :
    (¬ (e ∈ T.subtree v ↔ T.parent e ∈ T.subtree v)) ↔ e = v := by
  constructor
  · intro h
    by_contra he
    apply h
    constructor
    · intro hm
      exact TwoRespecting.RootedTree.mem_subtree.mpr
        ((TwoRespecting.RootedTree.mem_subtree.mp hm).isAnc_parent_of_ne (Ne.symm he))
    · intro hm
      exact TwoRespecting.RootedTree.mem_subtree.mpr
        (TwoRespecting.RootedTree.isAnc_trans (TwoRespecting.RootedTree.mem_subtree.mp hm)
          (TwoRespecting.RootedTree.isAnc_parent e))
  · intro heq
    subst e
    intro h
    exact parent_not_mem_subtree T hv
      (h.mp (TwoRespecting.RootedTree.self_mem_subtree (T := T) v))

theorem PathClosed.separatorParts {T : TwoRespecting.RootedTree V} {U : Finset V}
    (hU : PathClosed T U) (c : V) {P : Finset V}
    (hP : P ∈ DirectedCertificate.Completion.separatorParts T U c) : PathClosed T P := by
  rcases DirectedCertificate.Completion.separatorParts_cases T U c hP with
    rfl | ⟨v, _, _, rfl⟩
  · have he : U \ T.subtree c = U ∩ (T.subtree c)ᶜ := by ext x; simp
    rw [he]
    exact hU.inter (compl_subtree_pathClosed T c)
  · exact hU.inter (subtree_pathClosed T v)

theorem PathClosed.subset_separatorPart {T : TwoRespecting.RootedTree V}
    {U W : Finset V} (hU : PathClosed T U) (hne : U.Nonempty)
    (hUW : U ⊆ W) {c : V} (hc : c ∉ U) :
    ∃ P ∈ DirectedCertificate.Completion.separatorParts T W c, U ⊆ P := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨P, hP, hxP⟩ := DirectedCertificate.Completion.separatorParts_cover
    T W c (hUW hx) (fun h => hc (h ▸ hx))
  refine ⟨P, hP, fun y hy => ?_⟩
  rcases DirectedCertificate.Completion.separatorParts_cases T W c hP with
    rfl | ⟨v, hv, hvc, rfl⟩
  · have hxc : x ∉ T.subtree c := (mem_sdiff.mp hxP).2
    have hyc : y ∉ T.subtree c := by
      intro hyc
      have hcr : c ≠ T.root := by
        intro h
        apply hxc
        rw [h, TwoRespecting.RootedTree.subtree_root]
        exact mem_univ x
      have he : c ∈ pathEdges T x y := (mem_pathEdges T x y c).mpr
        ⟨hcr, fun h => hxc (h.mpr hyc)⟩
      exact hc (hU x hx y hy c he).1
    exact mem_sdiff.mpr ⟨hUW hy, hyc⟩
  · have hxv := (mem_inter.mp hxP).2
    have hyv : y ∈ T.subtree v := by
      by_contra hyv
      have he : v ∈ pathEdges T x y := (mem_pathEdges T x y v).mpr
        ⟨hv, fun h => hyv (h.mp hxv)⟩
      exact hc (hvc ▸ (hU x hx y hy v he).2)
    exact mem_inter.mpr ⟨hUW hy, hyv⟩

theorem exists_pathClosed_centroid (T : TwoRespecting.RootedTree V) (U : Finset V)
    (hne : U.Nonempty) (hU : PathClosed T U) :
    ∃ c ∈ U, ∀ P ∈ DirectedCertificate.Completion.separatorParts T U c,
      2 * P.card ≤ U.card := by
  obtain ⟨c, hroot, hchild⟩ :=
    DirectedCertificate.Completion.exists_restricted_subtree_centroid T U hne
  have hhalf : ∀ P ∈ DirectedCertificate.Completion.separatorParts T U c,
      2 * P.card ≤ U.card := by
    intro P hP
    rcases DirectedCertificate.Completion.separatorParts_cases T U c hP with
      rfl | ⟨v, hv, hvc, rfl⟩
    · exact hroot
    · exact hchild v hv hvc
  have hc : c ∈ U := by
    by_contra hc
    obtain ⟨P, hP, hUP⟩ := hU.subset_separatorPart hne (subset_refl U) hc
    have h₁ := hhalf P hP
    have h₂ := card_le_card hUP
    have h₃ := hne.card_pos
    omega
  exact ⟨c, hc, hhalf⟩

/-- The actual outside component on a boundary edge of a path-closed set. -/
def outerShore (T : TwoRespecting.RootedTree V) (U : Finset V) (e : V) : Finset V :=
  if e ∈ U then (T.subtree e)ᶜ else T.subtree e

def outerRoot (T : TwoRespecting.RootedTree V) (U : Finset V) (e : V) : V :=
  if e ∈ U then T.parent e else e

def innerRoot (T : TwoRespecting.RootedTree V) (U : Finset V) (e : V) : V :=
  if e ∈ U then e else T.parent e

theorem boundary_endpoints (T : TwoRespecting.RootedTree V) {U : Finset V} {e : V}
    (he : e ∈ boundary T U) :
    e ≠ T.root ∧ innerRoot T U e ∈ U ∧ outerRoot T U e ∉ U := by
  have h := mem_filter.mp he
  have her := (mem_edges T e).mp h.1
  by_cases heU : e ∈ U
  · simp only [innerRoot, outerRoot, if_pos heU]
    exact ⟨her, heU, fun hp => h.2 ⟨fun _ => hp, fun _ => heU⟩⟩
  · simp only [innerRoot, outerRoot, if_neg heU]
    exact ⟨her, by tauto, heU⟩

theorem outerShore_endpoints (T : TwoRespecting.RootedTree V) {U : Finset V} {e : V}
    (he : e ∈ boundary T U) :
    outerRoot T U e ∈ outerShore T U e ∧ innerRoot T U e ∉ outerShore T U e := by
  have h := subtree_separates T (boundary_endpoints T he).1
  by_cases heU : e ∈ U <;> simp [outerShore, outerRoot, innerRoot, heU, h.1, h.2]

theorem outerShore_pathClosed (T : TwoRespecting.RootedTree V) (U : Finset V) (e : V) :
    PathClosed T (outerShore T U e) := by
  unfold outerShore
  split_ifs
  · exact compl_subtree_pathClosed T e
  · exact subtree_pathClosed T e

theorem crosses_outerShore_iff (T : TwoRespecting.RootedTree V) {U : Finset V} {e f : V}
    (he : e ∈ boundary T U) :
    (¬ (f ∈ outerShore T U e ↔ T.parent f ∈ outerShore T U e)) ↔ f = e := by
  have h := crosses_subtree_iff T (e := f) (boundary_endpoints T he).1
  by_cases heU : e ∈ U
  · simp only [outerShore, heU, ite_true, mem_compl]
    tauto
  · simpa only [outerShore, heU, ite_false] using h

theorem PathClosed.disjoint_outerShore {T : TwoRespecting.RootedTree V} {U : Finset V}
    (hU : PathClosed T U) {e : V} (he : e ∈ boundary T U) :
    Disjoint U (outerShore T U e) := by
  apply disjoint_left.mpr
  intro x hx hxK
  have hends := boundary_endpoints T he
  have hcut := outerShore_endpoints T he
  have hex : e ∈ pathEdges T (innerRoot T U e) x := by
    apply (mem_pathEdges T _ _ e).mpr
    refine ⟨hends.1, ?_⟩
    by_cases heU : e ∈ U <;> simp_all [outerShore, innerRoot]
  have hp := hU _ hends.2.1 x hx e hex
  apply hends.2.2
  by_cases heU : e ∈ U
  · simpa only [outerRoot, heU, ite_true] using hp.2
  · simpa only [outerRoot, heU, ite_false] using hp.1

/-- Distinct boundary edges determine disjoint actual outside components. -/
theorem PathClosed.outerShore_disjoint {T : TwoRespecting.RootedTree V} {U : Finset V}
    (hU : PathClosed T U) {e f : V} (he : e ∈ boundary T U) (hf : f ∈ boundary T U)
    (hef : e ≠ f) : Disjoint (outerShore T U e) (outerShore T U f) := by
  apply disjoint_left.mpr
  intro x hxE hxF
  have hE := boundary_endpoints T he
  have hF := boundary_endpoints T hf
  have hFout := (outerShore_endpoints T hf).1
  have hFinner : innerRoot T U f ∉ outerShore T U e :=
    fun h => disjoint_left.mp (hU.disjoint_outerShore he) hF.2.1 h
  have hEinner : innerRoot T U e ∉ outerShore T U f :=
    fun h => disjoint_left.mp (hU.disjoint_outerShore hf) hE.2.1 h
  have hroot : outerRoot T U f ∈ outerShore T U e := by
    by_contra hroot
    have hep : e ∈ pathEdges T x (outerRoot T U f) := by
      apply (mem_pathEdges T _ _ e).mpr
      refine ⟨hE.1, ?_⟩
      by_cases heU : e ∈ U <;> simp_all [outerShore]
    have hpath := outerShore_pathClosed T U f x hxF _ hFout e hep
    apply hEinner
    by_cases heU : e ∈ U
    · simpa [innerRoot, heU] using hpath.1
    · simpa [innerRoot, heU] using hpath.2
  have hcross : ¬ (f ∈ outerShore T U e ↔ T.parent f ∈ outerShore T U e) := by
    by_cases hfU : f ∈ U <;> simp_all [innerRoot, outerRoot]
  exact hef ((crosses_outerShore_iff T he).mp hcross).symm

/-- Every outside vertex belongs to an actual boundary component. -/
theorem PathClosed.outerShore_cover {T : TwoRespecting.RootedTree V} {U : Finset V}
    (hU : PathClosed T U) (hne : U.Nonempty) {x : V} (hx : x ∉ U) :
    ∃ e ∈ boundary T U, x ∈ outerShore T U e := by
  obtain ⟨s, hs⟩ := hne
  obtain ⟨e, hep, hecross⟩ := exists_path_crossing T hs hx
  have he : e ∈ boundary T U := mem_filter.mpr
    ⟨(mem_edges T e).mpr ((mem_pathEdges T s x e).mp hep).1, hecross⟩
  have hsK : s ∉ outerShore T U e :=
    fun h => disjoint_left.mp (hU.disjoint_outerShore he) hs h
  have hsep := ((mem_pathEdges T s x e).mp hep).2
  refine ⟨e, he, ?_⟩
  by_cases heU : e ∈ U <;> simp_all [outerShore]

/-- Quotient vertices are the active vertices and one actual outside component
for every boundary tree edge. No ambient isolated padding is counted. -/
abbrev FrontierVertex (T : TwoRespecting.RootedTree V) (U : Finset V) :=
  {v : V // v ∈ U} ⊕ {e : V // e ∈ boundary T U}

def frontierBlock (T : TwoRespecting.RootedTree V) (U : Finset V) :
    FrontierVertex T U → Finset V
  | .inl v => {v.val}
  | .inr e => outerShore T U e.val

def frontierRoot (T : TwoRespecting.RootedTree V) (U : Finset V) :
    FrontierVertex T U → V
  | .inl v => v.val
  | .inr e => outerRoot T U e.val

def frontierPartition (T : TwoRespecting.RootedTree V) (U : Finset V)
    (hU : PathClosed T U) (hne : U.Nonempty) : BlockPartition V (FrontierVertex T U) where
  block := frontierBlock T U
  root := frontierRoot T U
  root_mem b := by
    cases b with
    | inl v => exact mem_singleton_self _
    | inr e => exact (outerShore_endpoints T e.property).1
  disjoint b c hbc := by
    cases b with
    | inl v =>
      cases c with
      | inl w =>
        apply disjoint_singleton.mpr
        intro he
        exact hbc (congrArg Sum.inl (Subtype.ext he))
      | inr e =>
        exact disjoint_singleton_left.mpr fun h =>
          disjoint_left.mp (hU.disjoint_outerShore e.property) v.property h
    | inr e =>
      cases c with
      | inl w =>
        exact disjoint_singleton_right.mpr fun h =>
          disjoint_left.mp (hU.disjoint_outerShore e.property) w.property h
      | inr f =>
        apply hU.outerShore_disjoint e.property f.property
        intro he
        exact hbc (congrArg Sum.inr (Subtype.ext he))
  cover x := by
    by_cases hx : x ∈ U
    · exact ⟨.inl ⟨x, hx⟩, mem_singleton_self _⟩
    · obtain ⟨e, he, hxE⟩ := hU.outerShore_cover hne hx
      exact ⟨.inr ⟨e, he⟩, hxE⟩

theorem card_frontierVertex (T : TwoRespecting.RootedTree V) (U : Finset V) :
    Fintype.card (FrontierVertex T U) = frontierVolume T U := by
  simp [FrontierVertex, frontierVolume]

/-- Previously certified boundary mincuts supply all protection hypotheses of
the actual active-component quotient, also for an unrestricted competitor. -/
theorem frontier_protected (G : WeightedGraph V) (T : TwoRespecting.RootedTree V)
    (U : Finset V)
    (hmin : ∀ e ∈ boundary T U, IsSTMinCut G e (T.parent e) (T.subtree e)) :
    ∀ b : FrontierVertex T U, RootProtected G (frontierBlock T U b) (frontierRoot T U b) := by
  intro b
  cases b with
  | inl v => exact rootProtected_singleton G v.val
  | inr e =>
    change RootProtected G (outerShore T U e.val) (outerRoot T U e.val)
    have hm := hmin e.val e.property
    by_cases heU : e.val ∈ U
    · simp only [outerShore, outerRoot, heU, ite_true]
      refine ⟨mem_compl.mpr hm.2.1, fun A hA hp => ?_⟩
      have heA : e.val ∉ A := fun h => mem_compl.mp (hA h) hm.1
      have hc := hm.2.2 Aᶜ (mem_compl.mpr heA) (fun h => mem_compl.mp h hp)
      simpa only [cut_compl] using hc
    · simpa only [outerShore, outerRoot, heU, ite_false] using RootProtected.of_minCut hm

/-- Lifting from a frontier quotient uses only the already proved boundary
mincuts. The terminals are original active vertices. -/
theorem lift_frontier_minCut {G : WeightedGraph V} (T : TwoRespecting.RootedTree V)
    (U : Finset V) (hU : PathClosed T U) (hne : U.Nonempty)
    (hmin : ∀ e ∈ boundary T U, IsSTMinCut G e (T.parent e) (T.subtree e))
    {s t : {v : V // v ∈ U}} {S : Finset (FrontierVertex T U)}
    (hS : IsSTMinCut (G.contract (frontierPartition T U hU hne).projection)
      (.inl s) (.inl t) S) :
    IsSTMinCut G s.val t.val (pull (frontierPartition T U hU hne).projection S) :=
  (frontierPartition T U hU hne).lift_minCut (frontier_protected G T U hmin) hS


end
end CutQueryComplexity.Certificate.GomoryHu

#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_path_crossing
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_public_pair_shore
#print axioms CutQueryComplexity.Certificate.GomoryHu.TreeCertificate.pair_shore
#print axioms CutQueryComplexity.Certificate.GomoryHu.disjoint_frontier_volume
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_connected_centroid
#print axioms CutQueryComplexity.Certificate.GomoryHu.exists_pathClosed_centroid
#print axioms CutQueryComplexity.Certificate.GomoryHu.frontierPartition
#print axioms CutQueryComplexity.Certificate.GomoryHu.card_frontierVertex
#print axioms CutQueryComplexity.Certificate.GomoryHu.frontier_protected
#print axioms CutQueryComplexity.Certificate.GomoryHu.lift_frontier_minCut
