import CutQueryComplexity.Hierarchy.Laminar
import CutQueryComplexity.Hierarchy.TerminalCuts
import CutQueryComplexity.Hierarchy.Completion
import CutQueryComplexity.Hierarchy.Existence

/-! # Canonical normalization of a hierarchy's topology

Given a hierarchy `H` with arbitrary terminal locations (terminals may sit at internal nodes or
at the root, and clusters may be empty or repeated), `clusterFamily H` is the finite family of
its nonempty clusters together with every singleton and the whole vertex set. It is laminar,
so `Hierarchy/Laminar.lean` turns it into a hierarchy; `normalTopology P` transports that
hierarchy to a `Fin m` node type. The new topology depends only on the supplied one.

`Pkg.Normal` records the structural guarantees: at most `2n − 1` nodes, childless terminal
nodes, every childless node a terminal node, at least two children at every internal node, and
every vertex at its singleton cluster.

The central result is `normalTopology_rep_le`: if the capacities `cap` of `P` dominate every
cut of `G` (`c_G(S) ≤ R_P(S)`), then with canonical capacities the normalized hierarchy
satisfies `c_G(S) ≤ R_new(S) ≤ R_P(S)` for every shore `S`. The proof uses only cut domination:
every nonempty proper cluster of `P` is a fundamental cluster of the new tree, so its new cost
is at most its cut, hence at most its old capacity (`rep_cluster_le`), and
`rep_le_rep_of_clusters` transfers this through the parity presentation of shores.
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset TwoRespecting

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The cluster family -/

section Family

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The nonempty clusters of `H`, every singleton, and the whole vertex set. -/
def clusterFamily (H : Hier V N) : Finset (Finset V) :=
  ((univ.image H.cluster).filter fun A => A.Nonempty) ∪
    univ.image (fun v => ({v} : Finset V)) ∪ {univ}

theorem mem_clusterFamily {H : Hier V N} {A : Finset V} :
    A ∈ clusterFamily H ↔
      (∃ x, H.cluster x = A ∧ A.Nonempty) ∨ (∃ v, A = {v}) ∨ A = univ := by
  simp only [clusterFamily, mem_union, mem_filter, mem_image, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ((⟨⟨x, hx⟩, hA⟩ | ⟨v, hv⟩) | h)
    · exact Or.inl ⟨x, hx, hA⟩
    · exact Or.inr (Or.inl ⟨v, hv.symm⟩)
    · exact Or.inr (Or.inr h)
  · rintro (⟨x, hx, hA⟩ | ⟨v, hv⟩ | h)
    · exact Or.inl (Or.inl ⟨⟨x, hx⟩, hA⟩)
    · exact Or.inl (Or.inr ⟨v, hv.symm⟩)
    · exact Or.inr h

theorem cluster_mem_clusterFamily {H : Hier V N} {x : N} (h : (H.cluster x).Nonempty) :
    H.cluster x ∈ clusterFamily H :=
  mem_clusterFamily.mpr (Or.inl ⟨x, rfl, h⟩)

/-- The family is laminar, consists of nonempty sets, and contains `univ` and all singletons. -/
theorem clusterFamily_isLaminarCover [Nonempty V] (H : Hier V N) :
    IsLaminarCover (clusterFamily H) := by
  refine ⟨?_, ?_, mem_clusterFamily.mpr (Or.inr (Or.inr rfl)),
    fun v => mem_clusterFamily.mpr (Or.inr (Or.inl ⟨v, rfl⟩))⟩
  · intro A hA
    rcases mem_clusterFamily.mp hA with ⟨x, -, h⟩ | ⟨v, rfl⟩ | rfl
    · exact h
    · exact singleton_nonempty v
    · exact univ_nonempty
  · intro A hA B hB
    -- singletons and `univ` compare with everything
    have hsing : ∀ (v : V) (C : Finset V), ({v} : Finset V) ⊆ C ∨ Disjoint {v} C := by
      intro v C
      by_cases hv : v ∈ C
      · exact Or.inl (singleton_subset_iff.mpr hv)
      · exact Or.inr (disjoint_singleton_left.mpr hv)
    rcases mem_clusterFamily.mp hA with ⟨x, rfl, -⟩ | ⟨v, rfl⟩ | rfl
    · rcases mem_clusterFamily.mp hB with ⟨y, rfl, -⟩ | ⟨w, rfl⟩ | rfl
      · exact H.cluster_laminar x y
      · rcases hsing w (H.cluster x) with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h.symm)
      · exact Or.inl (subset_univ _)
    · rcases hsing v B with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (subset_univ _))

end Family

/-! ## The normalized topology -/

/-- Structural guarantees of a normalized topology. -/
structure Pkg.Normal (P : Pkg V) : Prop where
  size : P.m ≤ 2 * Fintype.card V - 1
  leaves : P.H.LeafChildless
  childless_isLeaf : ∀ x, P.H.children x = ∅ → P.H.IsLeaf x
  branching : ∀ x, ¬ P.H.IsLeaf x → 2 ≤ (P.H.children x).card
  singleton : ∀ v, P.H.cluster (P.H.leaf v) = {v}

section Normal

variable [Nonempty V] {N : Type} [Fintype N] [DecidableEq N]

/-- The hierarchy of the cluster family. -/
noncomputable def normalHier (H : Hier V N) : Hier V (LNode (clusterFamily H)) :=
  laminarHier _ (clusterFamily_isLaminarCover H)

/-- The normalized topology of a supplied hierarchy, on a `Fin m` node type. -/
noncomputable def normalTopology (P : Pkg V) : Pkg V :=
  ⟨Fintype.card (LNode (clusterFamily P.H)), (normalHier P.H).transfer (Fintype.equivFin _)⟩

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype N] [DecidableEq N] in
theorem Hier.isLeaf_transfer {M : Type} [Fintype M] [DecidableEq M] (H : Hier V N) (e : N ≃ M)
    (x : N) : (H.transfer e).IsLeaf (e x) ↔ H.IsLeaf x := by
  unfold Hier.IsLeaf
  constructor
  · rintro ⟨v, hv⟩; exact ⟨v, e.injective hv⟩
  · rintro ⟨v, hv⟩; exact ⟨v, by rw [← hv]; rfl⟩

/-- The normalized topology has the structural guarantees. -/
theorem normalTopology_normal (P : Pkg V) : (normalTopology P).Normal := by
  set hF := clusterFamily_isLaminarCover P.H
  set e := Fintype.equivFin (LNode (clusterFamily P.H))
  refine ⟨card_node_le hF, Hier.leafChildless_transfer (leafChildless hF) e, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    change ((normalHier P.H).transfer e).children (e x) = ∅ at hy
    rw [Hier.children_transfer, map_eq_empty] at hy
    exact (Hier.isLeaf_transfer _ e x).mpr (isLeaf_of_children_eq_empty hF hy)
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    change ¬ ((normalHier P.H).transfer e).IsLeaf (e x) at hy
    change 2 ≤ (((normalHier P.H).transfer e).children (e x)).card
    rw [Hier.children_transfer, card_map]
    exact two_le_card_children hF fun h => hy ((Hier.isLeaf_transfer _ e x).mpr h)
  · intro v
    show ((normalHier P.H).transfer e).cluster (e ((normalHier P.H).leaf v)) = {v}
    rw [Hier.cluster_transfer]
    exact cluster_leaf hF v

/-- Every nonempty cluster of the input is a cluster of the normalized topology. -/
theorem normalTopology_cluster_of_nonempty (P : Pkg V) {x : Fin P.m}
    (h : (P.H.cluster x).Nonempty) :
    ∃ y, (normalTopology P).H.cluster y = P.H.cluster x := by
  set e := Fintype.equivFin (LNode (clusterFamily P.H))
  refine ⟨e ⟨P.H.cluster x, cluster_mem_clusterFamily h⟩, ?_⟩
  show ((normalHier P.H).transfer e).cluster (e _) = _
  rw [Hier.cluster_transfer]
  exact laminarHier_cluster_eq _ _

/-- **Normalization keeps every representation cost between the cut and the old cost.**
Only cut domination by the input capacities is assumed. -/
theorem normalTopology_rep_le (P : Pkg V) (cap : Fin P.m → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    (G : WeightedGraph V) (hdom : ∀ S, G.cut S ≤ P.H.rep cap S) (S : Finset V) :
    G.cut S ≤ (normalTopology P).H.rep ((normalTopology P).H.canon G) S ∧
      (normalTopology P).H.rep ((normalTopology P).H.canon G) S ≤ P.H.rep cap S := by
  set Q := (normalTopology P).H
  refine ⟨Q.cut_le_rep G S, ?_⟩
  refine Hier.rep_le_rep_of_clusters Q (fun y _ => G.cut_nonneg _) (fun x hx => ?_) S
  have hxr : x ≠ P.H.T.root := (Hier.mem_edges P.H).mp hx
  rcases (P.H.cluster x).eq_empty_or_nonempty with he | hne
  · rw [he]
    exact (Hier.rep_empty_le _).trans (hcap x)
  obtain ⟨y, hy⟩ := normalTopology_cluster_of_nonempty P hne
  by_cases hyr : y = Q.T.root
  · rw [hyr, Hier.cluster_root] at hy
    rw [← hy]
    exact (Hier.rep_univ_le _).trans (hcap x)
  · rw [← hy]
    refine (Hier.rep_cluster_le _ hyr).trans ?_
    show G.cut (Q.cluster y) ≤ cap x
    rw [hy]
    exact (hdom _).trans (Hier.rep_cluster_le cap hxr)

end Normal

end Hierarchy
end CutQueryComplexity
