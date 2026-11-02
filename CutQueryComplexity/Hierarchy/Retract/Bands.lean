import CutQueryComplexity.Hierarchy.Retract.Metric
import CutQueryComplexity.Hierarchy.Retract.Grid

/-! # Scales, bands, and the rounding map (B3)

Fix a scale shift `s` and a band offset `t`. A node `x` with `r(x) > 0` (distance to the
nearest terminal) gets the scale

  `Δ(x) = 2 ^ (⌊log₂ r(x) + s⌋ − s)`,  so `Δ(x) ≤ r(x) < 2 Δ(x)` (`scaleOf_le`, `lt_two_scaleOf`).

At scale `Δ`, bands are slabs of weighted height of width `Δ / 2`, offset by `t`. The top of
`x` (`top`) is the highest ancestor reached by climbing while the band stays the same;
`top x = top (parent x)` exactly when the band does not change across the edge above `x`
(`top_eq_top_parent`). Climbing stays in one band, so `d(x, top x) < Δ / 2` (`dist_top_lt`).

The rounding map sends a terminal node to its terminal and any other node `x` to a nearest
terminal of `top x` at scale `Δ(x)`. It fixes terminals (`round_leaf`), moves every node by at
most `2 r(x)` (`dist_round_le`), and agrees across a tree edge whose endpoints have the same
scale index and the same band (`round_eq_round_parent`).
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace Hier

open Finset TwoRespecting

/-! ## Tops of band blocks -/

section Top

variable {V N : Type} [DecidableEq N] (H : Hier V N)

/-- Climb from `x` while the band `b` does not change. -/
noncomputable def top (b : N → ℤ) (x : N) : N :=
  if _h : x ≠ H.T.root ∧ b (H.T.parent x) = b x then top b (H.T.parent x) else x
termination_by H.T.depth x
decreasing_by
  have := H.T.depth_parent x _h.1
  omega

theorem top_eq_top_parent (b : N → ℤ) {x : N} (hx : x ≠ H.T.root)
    (hb : b (H.T.parent x) = b x) : H.top b x = H.top b (H.T.parent x) := by
  rw [top, dite_eq_left ⟨hx, hb⟩]

theorem top_spec (b : N → ℤ) (x : N) : H.T.IsAnc (H.top b x) x ∧ b (H.top b x) = b x := by
  rw [top]
  split_ifs with h
  · obtain ⟨h1, h2⟩ := top_spec b (H.T.parent x)
    exact ⟨RootedTree.isAnc_trans h1 (RootedTree.isAnc_parent x), h2.trans h.2⟩
  · exact ⟨RootedTree.isAnc_refl x, rfl⟩
termination_by H.T.depth x
decreasing_by
  have := H.T.depth_parent x h.1
  omega

end Top

variable {V : Type} [Fintype V] [DecidableEq V] {N : Type} [Fintype N] [DecidableEq N]
variable (H : Hier V N)

/-! ## Bands and scales -/

variable (ℓ : N → ℝ)

omit [Fintype V] [DecidableEq V] in
/-- The band of `x` at scale `Δ` with offset `t`: slabs of weighted height of width `Δ / 2`. -/
noncomputable def band (Δ t : ℝ) (x : N) : ℤ := ⌊H.rootDist ℓ x / (Δ / 2) + t⌋

omit [Fintype V] [DecidableEq V] in
/-- Climbing to the top of a band block moves less than the band width. -/
theorem dist_top_lt (hℓ : ∀ e, 0 ≤ ℓ e) {Δ : ℝ} (hΔ : 0 < Δ) (t : ℝ) (x : N) :
    H.nodeDist ℓ x (H.top (H.band ℓ Δ t) x) < Δ / 2 := by
  obtain ⟨hanc, hb⟩ := H.top_spec (H.band ℓ Δ t) x
  rw [H.nodeDist_of_isAnc hanc]
  have hw : 0 < Δ / 2 := by linarith
  have := Int.abs_sub_lt_one_of_floor_eq_floor hb
  have hmono := H.rootDist_mono hℓ hanc
  rw [abs_lt] at this
  have h2 : H.rootDist ℓ x / (Δ / 2) - H.rootDist ℓ (H.top (H.band ℓ Δ t) x) / (Δ / 2) < 1 := by
    linarith
  rw [← sub_div, div_lt_one hw] at h2
  exact h2

variable [Nonempty V]

omit [DecidableEq V] in
/-- The scale index `⌊log₂ r(x) + s⌋`. -/
noncomputable def scaleIdx (s : ℝ) (x : N) : ℤ := ⌊Real.logb 2 (H.rdist ℓ x) + s⌋

omit [DecidableEq V] in
/-- The scale `Δ(x) = 2 ^ (⌊log₂ r(x) + s⌋ − s)`. -/
noncomputable def scaleOf (s : ℝ) (x : N) : ℝ := (2 : ℝ) ^ ((H.scaleIdx ℓ s x : ℝ) - s)

omit [DecidableEq V] in
theorem scaleOf_pos (s : ℝ) (x : N) : 0 < H.scaleOf ℓ s x := Real.rpow_pos_of_pos two_pos _

omit [DecidableEq V] in
theorem scaleOf_le {s : ℝ} {x : N} (hr : 0 < H.rdist ℓ x) : H.scaleOf ℓ s x ≤ H.rdist ℓ x := by
  unfold scaleOf
  conv_rhs => rw [← Real.rpow_logb two_pos (by norm_num) hr]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have := Int.floor_le (Real.logb 2 (H.rdist ℓ x) + s)
  unfold scaleIdx; linarith

omit [DecidableEq V] in
theorem lt_two_scaleOf {s : ℝ} {x : N} (hr : 0 < H.rdist ℓ x) :
    H.rdist ℓ x < 2 * H.scaleOf ℓ s x := by
  unfold scaleOf
  have h2 : (2 : ℝ) * 2 ^ ((H.scaleIdx ℓ s x : ℝ) - s) = 2 ^ ((H.scaleIdx ℓ s x : ℝ) - s + 1) := by
    rw [Real.rpow_add two_pos, Real.rpow_one, mul_comm]
  rw [h2]
  conv_lhs => rw [← Real.rpow_logb two_pos (by norm_num) hr]
  refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
  have := Int.lt_floor_add_one (Real.logb 2 (H.rdist ℓ x) + s)
  unfold scaleIdx; linarith

/-! ## The rounding map -/

omit [DecidableEq V] in
/-- A chosen nearest terminal. -/
noncomputable def nearest (x : N) : V := Classical.choose (H.exists_rdist_eq (ℓ := ℓ) x)

omit [DecidableEq V] in
theorem dist_nearest (x : N) : H.nodeDist ℓ x (H.leaf (H.nearest ℓ x)) = H.rdist ℓ x :=
  (Classical.choose_spec (H.exists_rdist_eq (ℓ := ℓ) x)).symm

omit [DecidableEq V] in
/-- The rounding map with scale shift `s` and band offset `t`. -/
noncomputable def round (s t : ℝ) (x : N) : V :=
  if h : H.IsLeaf x then Classical.choose h
  else H.nearest ℓ (H.top (H.band ℓ (H.scaleOf ℓ s x) t) x)

omit [DecidableEq V] in
theorem round_leaf (s t : ℝ) (v : V) : H.round ℓ s t (H.leaf v) = v := by
  have h : H.IsLeaf (H.leaf v) := ⟨v, rfl⟩
  rw [round, dite_eq_left h]
  exact H.leaf_inj (Classical.choose_spec h)

omit [DecidableEq V] in
theorem round_of_not_leaf (s t : ℝ) {x : N} (hx : ¬ H.IsLeaf x) :
    H.round ℓ s t x = H.nearest ℓ (H.top (H.band ℓ (H.scaleOf ℓ s x) t) x) := by
  rw [round, dite_eq_right hx]

omit [DecidableEq V] in
/-- The rounding map moves a node by at most twice its distance to the terminals. -/
theorem dist_round_le (hℓ : ∀ e, 0 < ℓ e) (s t : ℝ) (x : N) :
    H.nodeDist ℓ x (H.leaf (H.round ℓ s t x)) ≤ 2 * H.rdist ℓ x := by
  have hℓ0 : ∀ e, 0 ≤ ℓ e := fun e => (hℓ e).le
  by_cases hx : H.IsLeaf x
  · obtain ⟨v, rfl⟩ := hx
    rw [H.round_leaf, H.nodeDist_self]
    have := H.rdist_nonneg hℓ0 (H.leaf v); linarith
  · rw [H.round_of_not_leaf ℓ s t hx]
    have hr := H.rdist_pos hℓ hx
    set Δ := H.scaleOf ℓ s x
    set u := H.top (H.band ℓ Δ t) x
    have h1 := H.dist_top_lt ℓ hℓ0 (H.scaleOf_pos ℓ s x) t x
    have h2 := H.rdist_lipschitz hℓ0 u x
    have h3 := H.nodeDist_triangle hℓ0 x u (H.leaf (H.nearest ℓ u))
    have h4 := H.scaleOf_le ℓ (s := s) hr
    rw [H.dist_nearest] at h3
    rw [H.nodeDist_comm ℓ u x] at h2
    linarith

omit [DecidableEq V] in
/-- Across a tree edge whose endpoints are not terminal nodes and share the scale index and the
band, the rounding map agrees. -/
theorem round_eq_round_parent (s t : ℝ) {x : N} (hx : x ≠ H.T.root) (hxl : ¬ H.IsLeaf x)
    (hpl : ¬ H.IsLeaf (H.T.parent x))
    (hk : H.scaleIdx ℓ s x = H.scaleIdx ℓ s (H.T.parent x))
    (hb : H.band ℓ (H.scaleOf ℓ s x) t (H.T.parent x) = H.band ℓ (H.scaleOf ℓ s x) t x) :
    H.round ℓ s t x = H.round ℓ s t (H.T.parent x) := by
  have hΔ : H.scaleOf ℓ s (H.T.parent x) = H.scaleOf ℓ s x := by unfold scaleOf; rw [hk]
  rw [H.round_of_not_leaf ℓ s t hxl, H.round_of_not_leaf ℓ s t hpl, hΔ,
    H.top_eq_top_parent _ hx hb]

end Hier
end Hierarchy
end CutQueryComplexity
