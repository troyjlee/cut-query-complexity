import CutQueryComplexity.Hierarchy.Basic

/-! # Children in a hierarchy

Children of a node, the unique child on the way to a proper descendant, induction from
the leaves up, and subadditivity of canonical capacities: away from leaf nodes, a
cluster is the disjoint union of its children's clusters, so its cut is at most the sum
of theirs.
-/

namespace CutQueryComplexity
namespace Hierarchy

open TwoRespecting WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N] (H : Hier V N)

/-- The children of a node: the tree edges hanging from it. -/
def children (x : N) : Finset N := {c ∈ H.edges | H.T.parent c = x}

/-- A node is a leaf node when some vertex is placed there. -/
def IsLeaf (x : N) : Prop := ∃ v, H.leaf v = x

instance : DecidablePred H.IsLeaf := fun x => inferInstanceAs (Decidable (∃ v, H.leaf v = x))

/-- Leaf nodes have no children. -/
def LeafChildless : Prop := ∀ v, H.children (H.leaf v) = ∅

/-- Capacities are subadditive over children away from leaf nodes (on the tree edges). -/
def Subadd (cap : N → ℝ) : Prop :=
  ∀ x ∈ H.edges, ¬ H.IsLeaf x → cap x ≤ ∑ c ∈ H.children x, cap c

variable {H}

omit [Fintype V] [DecidableEq V] in
theorem mem_children {x c : N} : c ∈ H.children x ↔ c ≠ H.T.root ∧ H.T.parent c = x := by
  simp [children]

omit [Fintype V] [DecidableEq V] in
theorem sum_edges_eq_sum_children {M : Type} [AddCommMonoid M] (f : N → M) :
    ∑ x ∈ H.edges, f x = ∑ u, ∑ c ∈ H.children u, f c :=
  (Finset.sum_fiberwise H.edges H.T.parent f).symm

omit [Fintype V] [DecidableEq V] in
theorem depth_child {x c : N} (hc : c ∈ H.children x) : H.T.depth c = H.T.depth x + 1 := by
  obtain ⟨hne, hp⟩ := mem_children.mp hc
  rw [← H.T.depth_parent c hne, hp]

omit [Fintype N] [DecidableEq N] in
theorem _root_.CutQueryComplexity.TwoRespecting.RootedTree.eq_of_isAnc_of_depth_eq
    {T : RootedTree N} {u v : N} (h : T.IsAnc u v) (hd : T.depth u = T.depth v) :
    u = v := by
  rw [h.eq_iterate, hd, Nat.sub_self, Function.iterate_zero_apply]

omit [Fintype V] [DecidableEq V] in
theorem isAnc_of_mem_children {x c y : N} (hc : c ∈ H.children x) (h : H.T.IsAnc c y) :
    H.T.IsAnc x y := by
  have := (mem_children.mp hc).2
  exact RootedTree.isAnc_trans (this ▸ RootedTree.isAnc_parent c) h

omit [Fintype V] [DecidableEq V] in
theorem ne_of_mem_children {x c y : N} (hc : c ∈ H.children x) (h : H.T.IsAnc c y) : x ≠ y := by
  rintro rfl
  have := h.depth_le
  rw [depth_child hc] at this
  omega

omit [Fintype V] [DecidableEq V] in
theorem exists_child {x y : N} (h : H.T.IsAnc x y) (hne : x ≠ y) :
    ∃ c ∈ H.children x, H.T.IsAnc c y := by
  have hlt : H.T.depth x < H.T.depth y := by
    rcases lt_or_eq_of_le h.depth_le with hl | he
    · exact hl
    · exact absurd (RootedTree.eq_of_isAnc_of_depth_eq h he) hne
  set k := H.T.depth y - H.T.depth x - 1
  refine ⟨H.T.parent^[k] y, ?_, ⟨k, rfl⟩⟩
  have hdc : H.T.depth (H.T.parent^[k] y) = H.T.depth x + 1 := by
    rw [RootedTree.depth_iterate y k (by omega)]; omega
  refine mem_children.mpr ⟨fun hr => ?_, ?_⟩
  · rw [hr, H.T.depth_root] at hdc; omega
  · rw [← Function.iterate_succ_apply' H.T.parent k y]
    have : k.succ = H.T.depth y - H.T.depth x := by omega
    rw [this]; exact h.eq_iterate.symm

omit [Fintype V] [DecidableEq V] in
theorem child_unique {x c c' y : N} (hc : c ∈ H.children x) (hc' : c' ∈ H.children x)
    (h : H.T.IsAnc c y) (h' : H.T.IsAnc c' y) : c = c' := by
  have hd : H.T.depth c = H.T.depth c' := by rw [depth_child hc, depth_child hc']
  rcases RootedTree.isAnc_total_of_common h h' with h1 | h1
  · exact RootedTree.eq_of_isAnc_of_depth_eq h1 hd
  · exact (RootedTree.eq_of_isAnc_of_depth_eq h1 hd.symm).symm

omit [Fintype V] [DecidableEq V] in
/-- Induction from the leaves up. -/
theorem induction_up {P : N → Prop} (h : ∀ x, (∀ c ∈ H.children x, P c) → P x) (x : N) : P x := by
  set D := Finset.univ.sup H.T.depth
  have key : ∀ k, ∀ x, D ≤ H.T.depth x + k → P x := by
    intro k
    induction k with
    | zero =>
        intro x hx
        refine h x fun c hc => absurd (Finset.le_sup (f := H.T.depth) (Finset.mem_univ c)) ?_
        rw [depth_child hc]; omega
    | succ k ih =>
        intro x hx
        exact h x fun c hc => ih c (by have := depth_child hc; omega)
  exact key D x (by omega)

omit [Fintype V] [DecidableEq V] in
/-- A node has at most `depth y` proper ancestors. -/
theorem card_strictAnc_le (y : N) :
    (Finset.univ.filter fun u => H.T.IsAnc u y ∧ u ≠ y).card ≤ H.T.depth y := by
  refine le_trans (Finset.card_le_card ?_) ((Finset.card_image_le (s := Finset.range (H.T.depth y))
    (f := fun k => H.T.parent^[k + 1] y)).trans (Finset.card_range _).le)
  intro u hu
  obtain ⟨hanc, hne⟩ := (Finset.mem_filter.mp hu).2
  have hlt : H.T.depth u < H.T.depth y := by
    rcases lt_or_eq_of_le hanc.depth_le with hl | he
    · exact hl
    · exact absurd (RootedTree.eq_of_isAnc_of_depth_eq hanc he) hne
  refine Finset.mem_image.mpr ⟨H.T.depth y - H.T.depth u - 1, Finset.mem_range.mpr (by omega), ?_⟩
  show H.T.parent^[_ + 1] y = u
  rw [show H.T.depth y - H.T.depth u - 1 + 1 = H.T.depth y - H.T.depth u by omega]
  exact hanc.eq_iterate.symm

/-- Away from leaf nodes, cluster indicators split over the children. -/
theorem ind_cluster_eq_sum {x : N} (hx : ¬ H.IsLeaf x) (v : V) :
    (if v ∈ H.cluster x then (1 : ℝ) else 0) =
      ∑ c ∈ H.children x, (if v ∈ H.cluster c then (1 : ℝ) else 0) := by
  simp only [mem_cluster]
  by_cases h : H.T.IsAnc x (H.leaf v)
  · rw [ite_eq_left h]
    have hne : x ≠ H.leaf v := fun he => hx ⟨v, he.symm⟩
    obtain ⟨c0, hc0, h0⟩ := exists_child (H := H) h hne
    rw [Finset.sum_eq_single c0 (fun c hc hcne => by
      rw [ite_eq_right fun h' => hcne (child_unique hc hc0 h' h0)]) (fun h' => absurd hc0 h'),
      ite_eq_left h0]
  · rw [ite_eq_right h]
    exact (Finset.sum_eq_zero fun c hc => ite_eq_right fun h' => h (isAnc_of_mem_children hc h')).symm

/-- Canonical capacities are subadditive. -/
theorem canon_subadd (G : WeightedGraph V) : H.Subadd (H.canon G) := by
  intro x _ hx
  have := cut_le_of_decomp G (H.cluster x) (H.children x) H.cluster (fun _ => 1) 0
    (fun v => by rw [ind_cluster_eq_sum hx v, zero_add]; simp)
  simpa [canon] using this

omit [Fintype V] [DecidableEq V] in
theorem subadd_congr {cap cap' : N → ℝ} (h : ∀ x ∈ H.edges, cap x = cap' x)
    (hs : H.Subadd cap) : H.Subadd cap' := by
  intro x hx hl
  rw [← h x hx]
  refine (hs x hx hl).trans (le_of_eq (Finset.sum_congr rfl fun c hc => h c ?_))
  exact (Finset.mem_filter.mp hc).1

end Hier
end Hierarchy
end CutQueryComplexity
