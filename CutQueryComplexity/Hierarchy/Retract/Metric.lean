import CutQueryComplexity.Hierarchy.GuardDuality

/-! # The tree metric of a hierarchy (B3, metric identities)

For edge lengths `ℓ` (on the tree edges, i.e. the non-root nodes), two nodes are separated by
the edge above `e` exactly when one of them lies below `e` (in `downSet e`). The node distance is the total length
of the separating edges (`nodeDist`), and the weighted height of a node is the length of its
root path (`rootDist`).

* `terminalDist_eq_nodeDist`: on terminals, the node distance is `terminalDist`;
* `nodeDist_triangle`, `nodeDist_comm`, `nodeDist_self`;
* `nodeDist_of_isAnc`: for an ancestor `y` of `x`, `d(x, y) = h(x) − h(y)` (`h = rootDist`);
* `nodeDist_parent`, `rootDist_parent`: the edge above `x` has length `ℓ x`;
* `nodeDist_pos`: with positive lengths, distinct nodes are at positive distance;
* `rdist` (distance to the nearest terminal), `rdist_lipschitz`, `rdist_pos`.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace Hier

open Finset TwoRespecting

variable {V : Type} [Fintype V] [DecidableEq V] {N : Type} [Fintype N] [DecidableEq N]

open Classical in
/-- The nodes below `e`. -/
noncomputable def downSet (H : Hier V N) (e : N) : Finset N := univ.filter fun y => H.T.IsAnc e y

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_downSet (H : Hier V N) {e y : N} : y ∈ H.downSet e ↔ H.T.IsAnc e y := by
  simp [downSet]

/-- The distance between nodes: the total length of the separating tree edges. -/
noncomputable def nodeDist (H : Hier V N) (ℓ : N → ℝ) (x y : N) : ℝ :=
  ∑ e ∈ H.edges, if (x ∈ H.downSet e) = (y ∈ H.downSet e) then 0 else ℓ e

/-- The weighted height: the length of the root path. -/
noncomputable def rootDist (H : Hier V N) (ℓ : N → ℝ) (x : N) : ℝ :=
  ∑ e ∈ H.edges, if x ∈ H.downSet e then ℓ e else 0

variable (H : Hier V N) (ℓ : N → ℝ)

theorem terminalDist_eq_nodeDist (u v : V) :
    H.terminalDist ℓ u v = H.nodeDist ℓ (H.leaf u) (H.leaf v) := by
  unfold terminalDist nodeDist
  refine sum_congr rfl fun e _ => ?_
  simp only [mem_cluster, mem_downSet]

omit [Fintype V] [DecidableEq V] in
theorem nodeDist_comm (x y : N) : H.nodeDist ℓ x y = H.nodeDist ℓ y x := by
  unfold nodeDist
  refine sum_congr rfl fun e _ => ?_
  by_cases hx : x ∈ H.downSet e <;> by_cases hy : y ∈ H.downSet e <;> simp [hx, hy]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem nodeDist_self (x : N) : H.nodeDist ℓ x x = 0 := by simp [nodeDist]

variable {ℓ}

omit [Fintype V] [DecidableEq V] in
theorem nodeDist_nonneg (hℓ : ∀ e, 0 ≤ ℓ e) (x y : N) : 0 ≤ H.nodeDist ℓ x y :=
  sum_nonneg fun e _ => by split_ifs; exacts [le_rfl, hℓ e]

omit [Fintype V] [DecidableEq V] in
theorem nodeDist_triangle (hℓ : ∀ e, 0 ≤ ℓ e) (x y z : N) :
    H.nodeDist ℓ x z ≤ H.nodeDist ℓ x y + H.nodeDist ℓ y z := by
  unfold nodeDist
  rw [← sum_add_distrib]
  refine sum_le_sum fun e _ => ?_
  have := hℓ e
  by_cases hx : x ∈ H.downSet e <;> by_cases hy : y ∈ H.downSet e <;> by_cases hz : z ∈ H.downSet e <;>
    simp [hx, hy, hz] <;> linarith

omit [Fintype V] [DecidableEq V] in
/-- The distance to an ancestor is the difference of heights. -/
theorem nodeDist_of_isAnc {x y : N} (h : H.T.IsAnc y x) :
    H.nodeDist ℓ x y = H.rootDist ℓ x - H.rootDist ℓ y := by
  unfold nodeDist rootDist
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  by_cases hx : x ∈ H.downSet e <;> by_cases hy : y ∈ H.downSet e <;> simp only [hx, hy] <;>
    simp
  -- `y` below `e` forces `x` below `e`
  exact (hx ((H.mem_downSet).mpr (RootedTree.isAnc_trans ((H.mem_downSet).mp hy) h))).elim

omit [Fintype V] [DecidableEq V] in
theorem rootDist_mono (hℓ : ∀ e, 0 ≤ ℓ e) {x y : N} (h : H.T.IsAnc y x) :
    H.rootDist ℓ y ≤ H.rootDist ℓ x := by
  have := H.nodeDist_nonneg hℓ x y
  rw [H.nodeDist_of_isAnc h] at this
  linarith

omit [Fintype V] [DecidableEq V] in
/-- The edge above `x` separates exactly `x` from its parent. -/
theorem nodeDist_parent {x : N} (hx : x ≠ H.T.root) :
    H.nodeDist ℓ x (H.T.parent x) = ℓ x := by
  unfold nodeDist
  rw [sum_eq_single x]
  · have h1 : x ∈ H.downSet x := (H.mem_downSet).mpr (RootedTree.isAnc_refl x)
    have h2 : H.T.parent x ∉ H.downSet x := fun h => by
      have h' := (H.mem_downSet).mp h
      have := RootedTree.isAnc_antisymm h' (RootedTree.isAnc_parent x)
      have hd := H.T.depth_parent x hx
      rw [← this] at hd; omega
    simp [h1, h2]
  · intro e _ hne
    by_cases hx' : x ∈ H.downSet e
    · have hp : H.T.parent x ∈ H.downSet e :=
        (H.mem_downSet).mpr (((H.mem_downSet).mp hx').isAnc_parent_of_ne hne)
      simp [hx', hp]
    · have hp : H.T.parent x ∉ H.downSet e := fun hp => hx'
        ((H.mem_downSet).mpr (RootedTree.isAnc_trans ((H.mem_downSet).mp hp)
          (RootedTree.isAnc_parent x)))
      simp [hx', hp]
  · intro h; exact absurd ((mem_edges H).mpr hx) h

omit [Fintype V] [DecidableEq V] in
theorem rootDist_parent {x : N} (hx : x ≠ H.T.root) :
    H.rootDist ℓ x = H.rootDist ℓ (H.T.parent x) + ℓ x := by
  have h1 := H.nodeDist_of_isAnc (ℓ := ℓ) (RootedTree.isAnc_parent x)
  rw [H.nodeDist_parent hx] at h1
  linarith

omit [Fintype V] [DecidableEq V] in
/-- With positive lengths, distinct nodes are at positive distance. -/
theorem nodeDist_pos (hℓ : ∀ e, 0 < ℓ e) {x y : N} (hxy : x ≠ y) : 0 < H.nodeDist ℓ x y := by
  have hℓ0 : ∀ e, 0 ≤ ℓ e := fun e => (hℓ e).le
  -- some edge separates `x` and `y`
  obtain ⟨e, he, hsep⟩ : ∃ e ∈ H.edges, ¬ ((x ∈ H.downSet e) = (y ∈ H.downSet e)) := by
    by_cases hxy' : H.T.IsAnc x y
    · refine ⟨y, (mem_edges H).mpr fun hr => ?_, ?_⟩
      · exact hxy (RootedTree.isAnc_antisymm hxy' (hr ▸ RootedTree.isAnc_root x))
      · intro h
        have hy : y ∈ H.downSet y := (H.mem_downSet).mpr (RootedTree.isAnc_refl y)
        rw [← h] at hy
        exact hxy (RootedTree.isAnc_antisymm hxy' ((H.mem_downSet).mp hy))
    · refine ⟨x, (mem_edges H).mpr fun hr => hxy' (hr ▸ RootedTree.isAnc_root y), ?_⟩
      intro h
      have hx : x ∈ H.downSet x := (H.mem_downSet).mpr (RootedTree.isAnc_refl x)
      rw [h] at hx
      exact hxy' ((H.mem_downSet).mp hx)
  unfold nodeDist
  calc (0 : ℝ) < ℓ e := hℓ e
    _ = if (x ∈ H.downSet e) = (y ∈ H.downSet e) then 0 else ℓ e := by rw [ite_eq_right hsep]
    _ ≤ ∑ e ∈ H.edges, if (x ∈ H.downSet e) = (y ∈ H.downSet e) then 0 else ℓ e :=
        single_le_sum (f := fun e => if (x ∈ H.downSet e) = (y ∈ H.downSet e) then 0 else ℓ e)
          (fun e _ => by split_ifs; exacts [le_rfl, hℓ0 e]) he

/-! ## Distance to the nearest terminal -/

variable [Nonempty V]

omit [DecidableEq V] in
variable (ℓ) in
/-- The distance from a node to the nearest terminal. -/
noncomputable def rdist (x : N) : ℝ :=
  univ.inf' univ_nonempty fun v : V => H.nodeDist ℓ x (H.leaf v)

omit [DecidableEq V] in
theorem rdist_le (x : N) (v : V) : H.rdist ℓ x ≤ H.nodeDist ℓ x (H.leaf v) :=
  inf'_le _ (mem_univ v)

omit [DecidableEq V] in
theorem exists_rdist_eq (x : N) : ∃ v, H.rdist ℓ x = H.nodeDist ℓ x (H.leaf v) := by
  obtain ⟨v, -, hv⟩ := exists_mem_eq_inf' univ_nonempty fun v : V => H.nodeDist ℓ x (H.leaf v)
  exact ⟨v, hv⟩

omit [DecidableEq V] in
theorem rdist_nonneg (hℓ : ∀ e, 0 ≤ ℓ e) (x : N) : 0 ≤ H.rdist ℓ x := by
  obtain ⟨v, hv⟩ := H.exists_rdist_eq (ℓ := ℓ) x
  rw [hv]; exact H.nodeDist_nonneg hℓ _ _

omit [DecidableEq V] in
theorem rdist_leaf (hℓ : ∀ e, 0 ≤ ℓ e) (v : V) : H.rdist ℓ (H.leaf v) = 0 :=
  le_antisymm ((H.rdist_le _ v).trans (by simp)) (H.rdist_nonneg hℓ _)

omit [DecidableEq V] in
/-- The distance to the nearest terminal is 1-Lipschitz. -/
theorem rdist_lipschitz (hℓ : ∀ e, 0 ≤ ℓ e) (x y : N) :
    H.rdist ℓ x ≤ H.rdist ℓ y + H.nodeDist ℓ x y := by
  obtain ⟨v, hv⟩ := H.exists_rdist_eq (ℓ := ℓ) y
  calc H.rdist ℓ x ≤ H.nodeDist ℓ x (H.leaf v) := H.rdist_le x v
    _ ≤ H.nodeDist ℓ x y + H.nodeDist ℓ y (H.leaf v) := H.nodeDist_triangle hℓ _ _ _
    _ = H.rdist ℓ y + H.nodeDist ℓ x y := by rw [hv]; ring

omit [DecidableEq V] in
/-- With positive lengths, a node that is not a leaf node has positive distance to the
terminals. -/
theorem rdist_pos (hℓ : ∀ e, 0 < ℓ e) {x : N} (hx : ¬ H.IsLeaf x) : 0 < H.rdist ℓ x := by
  obtain ⟨v, hv⟩ := H.exists_rdist_eq (ℓ := ℓ) x
  rw [hv]
  exact H.nodeDist_pos hℓ fun h => hx ⟨v, h.symm⟩

end Hier
end Hierarchy
end CutQueryComplexity
