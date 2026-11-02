import CutQueryComplexity.Hierarchy.Retract.Bands

/-! # Finite rounding and the approximate aggregate inequality (B3)

Positive lengths `ℓ`. For a mesh `m ≥ 1`, the grid point `(i, j) ∈ [m] × [m]` gives the
rounding map with scale shift `i / m` and band offset `j / m` (`gridRound`). For a tree edge
`y → p` of length `δ = ℓ y`, with `r₁ = min (r y) (r p)`:

* always `d(f y, f p) ≤ 4 r₁ + 3 δ` (`edge_dist_le`, from the displacement bound `2 r`);
* if `δ < r₁`, both endpoints are non-terminal and `f y = f p` unless the scale indices or the
  bands differ (`edge_dist_eq_zero`); by `Retract.card_floor_ne_le_abs` the scale indices differ for at
  most `2 m δ / r₁ + 1` values of `i`, and for each other `i` the bands differ for at most
  `4 m δ / r₁ + 1` values of `j`.

Summing over the grid (`sum_grid_edge_le`),

  `Σ_{i,j} d(f_{ij} y, f_{ij} p) ≤ 42 m² δ + 14 m r(y)`,

and averaging (`exists_gridRound_le`) gives a terminal-fixing map with

  `Σ_y cap_y d(f y, f (parent y)) ≤ 42 Σ_y cap_y ℓ_y + E / m`,  `E = 14 Σ_y cap_y r(y)`,

where `E` does not depend on `m`.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace Hier

open Finset TwoRespecting

variable {V : Type} [Fintype V] [DecidableEq V] {N : Type} [Fintype N] [DecidableEq N]
variable (H : Hier V N) (ℓ : N → ℝ) [Nonempty V]

omit [DecidableEq V] in
/-- The rounding map at grid point `(i, j)` of mesh `m`. -/
noncomputable def gridRound (m i j : ℕ) : N → V := H.round ℓ ((i : ℝ) / m) ((j : ℝ) / m)

omit [DecidableEq V] in
theorem gridRound_fixing (m i j : ℕ) : H.Fixing (H.gridRound ℓ m i j) := fun v =>
  H.round_leaf ℓ _ _ v

variable {ℓ}

omit [DecidableEq V] in
theorem rdist_parent_le (hℓ : ∀ e, 0 ≤ ℓ e) {y : N} (hy : y ≠ H.T.root) :
    H.rdist ℓ (H.T.parent y) ≤ H.rdist ℓ y + ℓ y ∧ H.rdist ℓ y ≤ H.rdist ℓ (H.T.parent y) + ℓ y := by
  have h1 := H.rdist_lipschitz hℓ (H.T.parent y) y
  have h2 := H.rdist_lipschitz hℓ y (H.T.parent y)
  rw [H.nodeDist_comm, H.nodeDist_parent hy] at h1
  rw [H.nodeDist_parent hy] at h2
  exact ⟨h1, h2⟩

omit [DecidableEq V] in
/-- Any rounding stretches a tree edge to at most `4 r₁ + 3 δ`. -/
theorem edge_dist_le (hℓ : ∀ e, 0 < ℓ e) (s t : ℝ) {y : N} (hy : y ≠ H.T.root) :
    H.nodeDist ℓ (H.leaf (H.round ℓ s t y)) (H.leaf (H.round ℓ s t (H.T.parent y))) ≤
      4 * min (H.rdist ℓ y) (H.rdist ℓ (H.T.parent y)) + 3 * ℓ y := by
  have hℓ0 : ∀ e, 0 ≤ ℓ e := fun e => (hℓ e).le
  have h1 := H.dist_round_le ℓ hℓ s t y
  have h2 := H.dist_round_le ℓ hℓ s t (H.T.parent y)
  rw [H.nodeDist_comm] at h1
  have t1 := H.nodeDist_triangle hℓ0 (H.leaf (H.round ℓ s t y)) y
    (H.leaf (H.round ℓ s t (H.T.parent y)))
  have t2 := H.nodeDist_triangle hℓ0 y (H.T.parent y) (H.leaf (H.round ℓ s t (H.T.parent y)))
  rw [H.nodeDist_parent hy] at t2
  obtain ⟨l1, l2⟩ := H.rdist_parent_le hℓ0 hy
  rcases le_total (H.rdist ℓ y) (H.rdist ℓ (H.T.parent y)) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

omit [DecidableEq V] in
theorem edge_dist_eq_zero (s t : ℝ) {y : N} (hy : y ≠ H.T.root) (hyl : ¬ H.IsLeaf y)
    (hpl : ¬ H.IsLeaf (H.T.parent y))
    (hk : H.scaleIdx ℓ s y = H.scaleIdx ℓ s (H.T.parent y))
    (hb : H.band ℓ (H.scaleOf ℓ s y) t (H.T.parent y) = H.band ℓ (H.scaleOf ℓ s y) t y) :
    H.nodeDist ℓ (H.leaf (H.round ℓ s t y)) (H.leaf (H.round ℓ s t (H.T.parent y))) = 0 := by
  rw [H.round_eq_round_parent ℓ s t hy hyl hpl hk hb, nodeDist_self]

omit [DecidableEq V] in
theorem not_leaf_of_rdist_pos (hℓ : ∀ e, 0 ≤ ℓ e) {x : N} (hr : 0 < H.rdist ℓ x) :
    ¬ H.IsLeaf x := by
  rintro ⟨v, rfl⟩
  rw [H.rdist_leaf hℓ] at hr
  exact lt_irrefl _ hr

omit [DecidableEq V] in
/-- The grid sum for one tree edge. -/
theorem sum_grid_edge_le (hℓ : ∀ e, 0 < ℓ e) {m : ℕ} (hm : 0 < m) {y : N} (hy : y ≠ H.T.root) :
    ∑ i ∈ range m, ∑ j ∈ range m,
        H.nodeDist ℓ (H.leaf (H.gridRound ℓ m i j y)) (H.leaf (H.gridRound ℓ m i j (H.T.parent y)))
      ≤ 42 * (m : ℝ) ^ 2 * ℓ y + 14 * m * H.rdist ℓ y := by
  have hℓ0 : ∀ e, 0 ≤ ℓ e := fun e => (hℓ e).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set p := H.T.parent y
  set δ := ℓ y
  set r₁ := min (H.rdist ℓ y) (H.rdist ℓ p)
  have hδ : 0 < δ := hℓ y
  have hry := H.rdist_nonneg hℓ0 y
  have hr₁y : r₁ ≤ H.rdist ℓ y := min_le_left _ _
  have hr₁p : r₁ ≤ H.rdist ℓ p := min_le_right _ _
  have hr₁0 : 0 ≤ r₁ := le_min hry (H.rdist_nonneg hℓ0 p)
  have hle : ∀ i j, H.nodeDist ℓ (H.leaf (H.gridRound ℓ m i j y))
      (H.leaf (H.gridRound ℓ m i j p)) ≤ 4 * r₁ + 3 * δ := fun i j =>
    H.edge_dist_le hℓ _ _ hy
  rcases le_or_gt r₁ δ with hcase | hcase
  · -- long edge: every rounding stretches it by at most `7`
    calc _ ≤ ∑ i ∈ range m, ∑ j ∈ range m, 7 * δ :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => (hle i j).trans (by linarith)
      _ = 7 * (m : ℝ) ^ 2 * δ := by simp [sum_const, card_range]; ring
      _ ≤ _ := by nlinarith
  · -- short edge: both endpoints are non-terminal, and the rounding rarely separates them
    have hr₁ : 0 < r₁ := lt_trans hδ hcase
    have hyl := H.not_leaf_of_rdist_pos hℓ0 (lt_of_lt_of_le hr₁ hr₁y)
    have hpl := H.not_leaf_of_rdist_pos hℓ0 (lt_of_lt_of_le hr₁ hr₁p)
    obtain ⟨l1, l2⟩ : H.rdist ℓ p ≤ H.rdist ℓ y + δ ∧ H.rdist ℓ y ≤ H.rdist ℓ p + δ :=
      H.rdist_parent_le hℓ0 hy
    have hlt : ∀ i j, H.nodeDist ℓ (H.leaf (H.gridRound ℓ m i j y))
        (H.leaf (H.gridRound ℓ m i j p)) ≤ 7 * r₁ := fun i j => (hle i j).trans (by linarith)
    -- scale indices
    set bad : ℕ → Prop := fun i =>
      H.scaleIdx ℓ ((i : ℝ) / m) y ≠ H.scaleIdx ℓ ((i : ℝ) / m) p
    have hbad : (((range m).filter bad).card : ℝ) ≤ m * (2 * δ / r₁) + 1 := by
      have hc := Retract.card_floor_ne_le_abs hm (Real.logb 2 (H.rdist ℓ y)) (Real.logb 2 (H.rdist ℓ p))
      have habs : |Real.logb 2 (H.rdist ℓ p) - Real.logb 2 (H.rdist ℓ y)| ≤ 2 * δ / r₁ := by
        rcases le_total (H.rdist ℓ y) (H.rdist ℓ p) with h | h
        · have hm1 : r₁ = H.rdist ℓ y := min_eq_left h
          have := Retract.logb_two_sub_le (δ := δ) (hm1 ▸ hr₁) h (by linarith)
          have hmono : Real.logb 2 (H.rdist ℓ y) ≤ Real.logb 2 (H.rdist ℓ p) :=
            Real.logb_le_logb_of_le (by norm_num) (hm1 ▸ hr₁) h
          rw [abs_of_nonneg (by linarith), hm1]; exact this
        · have hm1 : r₁ = H.rdist ℓ p := min_eq_right h
          have := Retract.logb_two_sub_le (δ := δ) (hm1 ▸ hr₁) h (by linarith)
          have hmono : Real.logb 2 (H.rdist ℓ p) ≤ Real.logb 2 (H.rdist ℓ y) :=
            Real.logb_le_logb_of_le (by norm_num) (hm1 ▸ hr₁) h
          rw [abs_of_nonpos (by linarith), hm1]; linarith
      have : (((range m).filter bad).card : ℝ) ≤ m * |Real.logb 2 (H.rdist ℓ p) -
          Real.logb 2 (H.rdist ℓ y)| + 1 := hc
      nlinarith
    -- per scale shift
    have hrow : ∀ i ∈ range m, ∑ j ∈ range m, H.nodeDist ℓ (H.leaf (H.gridRound ℓ m i j y))
        (H.leaf (H.gridRound ℓ m i j p)) ≤
          7 * r₁ * ((if bad i then (m : ℝ) else 0) + (m * (4 * δ / r₁) + 1)) := by
      intro i _
      have hY : 0 ≤ (m : ℝ) * (4 * δ / r₁) + 1 := by positivity
      by_cases hi : bad i
      · simp only [hi, ite_true]
        calc _ ≤ ∑ j ∈ range m, 7 * r₁ := sum_le_sum fun j _ => hlt i j
          _ = 7 * r₁ * m := by simp [sum_const, card_range]; ring
          _ ≤ _ := by nlinarith
      · simp only [hi, ite_false, zero_add]
        have hk : H.scaleIdx ℓ ((i : ℝ) / m) y = H.scaleIdx ℓ ((i : ℝ) / m) p := not_not.mp hi
        set Δ := H.scaleOf ℓ ((i : ℝ) / m) y
        have hΔ : 0 < Δ := H.scaleOf_pos ℓ _ y
        have h2Δ : H.rdist ℓ y < 2 * Δ := H.lt_two_scaleOf ℓ (lt_of_lt_of_le hr₁ hr₁y)
        have hterm : ∀ j ∈ range m, H.nodeDist ℓ (H.leaf (H.gridRound ℓ m i j y))
            (H.leaf (H.gridRound ℓ m i j p)) ≤
              if H.band ℓ Δ ((j : ℝ) / m) p ≠ H.band ℓ Δ ((j : ℝ) / m) y then 7 * r₁ else 0 := by
          intro j _
          split_ifs with hb
          · exact hlt i j
          · exact (H.edge_dist_eq_zero _ _ hy hyl hpl hk (not_not.mp hb)).le
        have hcount := Retract.card_floor_ne_le_abs hm (H.rootDist ℓ p / (Δ / 2)) (H.rootDist ℓ y / (Δ / 2))
        have hh : H.rootDist ℓ y = H.rootDist ℓ p + δ := H.rootDist_parent hy
        have hdiff : |H.rootDist ℓ y / (Δ / 2) - H.rootDist ℓ p / (Δ / 2)| ≤ 4 * δ / r₁ := by
          rw [← sub_div, hh, add_sub_cancel_left, abs_of_nonneg (by positivity),
            div_le_div_iff₀ (by positivity) hr₁]
          nlinarith
        have hcard : (((range m).filter fun j : ℕ =>
            H.band ℓ Δ ((j : ℝ) / m) p ≠ H.band ℓ Δ ((j : ℝ) / m) y).card : ℝ) ≤
              m * (4 * δ / r₁) + 1 := by
          have : (((range m).filter fun j : ℕ =>
              H.band ℓ Δ ((j : ℝ) / m) p ≠ H.band ℓ Δ ((j : ℝ) / m) y).card : ℝ) ≤
                m * |H.rootDist ℓ y / (Δ / 2) - H.rootDist ℓ p / (Δ / 2)| + 1 := hcount
          nlinarith
        calc _ ≤ ∑ j ∈ range m, (if H.band ℓ Δ ((j : ℝ) / m) p ≠ H.band ℓ Δ ((j : ℝ) / m) y
                then 7 * r₁ else 0) := sum_le_sum hterm
          _ = 7 * r₁ * (((range m).filter fun j : ℕ =>
                H.band ℓ Δ ((j : ℝ) / m) p ≠ H.band ℓ Δ ((j : ℝ) / m) y).card : ℝ) := by
              rw [← sum_filter, sum_const, nsmul_eq_mul]; ring
          _ ≤ _ := by nlinarith
    calc _ ≤ ∑ i ∈ range m, 7 * r₁ * ((if bad i then (m : ℝ) else 0) + (m * (4 * δ / r₁) + 1)) :=
          sum_le_sum hrow
      _ = 7 * r₁ * (m * (((range m).filter bad).card : ℝ) + m * (m * (4 * δ / r₁) + 1)) := by
          rw [← mul_sum, sum_add_distrib, ← sum_filter, sum_const, sum_const, card_range,
            nsmul_eq_mul, nsmul_eq_mul]; ring
      _ ≤ 7 * r₁ * (m * (m * (2 * δ / r₁) + 1) + m * (m * (4 * δ / r₁) + 1)) := by
          have := mul_le_mul_of_nonneg_left hbad hmR.le
          nlinarith
      _ = 42 * (m : ℝ) ^ 2 * δ + 14 * m * r₁ := by field_simp; ring
      _ ≤ _ := by nlinarith

/-- **Approximate aggregate inequality.** For positive lengths and every mesh `m ≥ 1`, some grid
rounding fixes the terminals and costs at most `42 Σ cap ℓ + E / m`, with
`E = 14 Σ cap r` independent of `m`. -/
theorem exists_gridRound_le (hℓ : ∀ e, 0 < ℓ e) (cap : N → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    {m : ℕ} (hm : 0 < m) :
    ∃ f : N → V, H.Fixing f ∧
      ∑ y ∈ H.edges, cap y * H.terminalDist ℓ (f y) (f (H.T.parent y)) ≤
        42 * ∑ y ∈ H.edges, cap y * ℓ y + (14 * ∑ y ∈ H.edges, cap y * H.rdist ℓ y) / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set B := 42 * ∑ y ∈ H.edges, cap y * ℓ y + (14 * ∑ y ∈ H.edges, cap y * H.rdist ℓ y) / m
  set cost : ℕ → ℕ → ℝ := fun i j => ∑ y ∈ H.edges, cap y *
    H.terminalDist ℓ (H.gridRound ℓ m i j y) (H.gridRound ℓ m i j (H.T.parent y))
  suffices ∃ i ∈ range m, ∃ j ∈ range m, cost i j ≤ B by
    obtain ⟨i, -, j, -, h⟩ := this
    exact ⟨_, H.gridRound_fixing ℓ m i j, h⟩
  by_contra hne
  push Not at hne
  have hne' : (range m).Nonempty := nonempty_range_iff.mpr hm.ne'
  have hlt : ∑ i ∈ range m, ∑ j ∈ range m, B < ∑ i ∈ range m, ∑ j ∈ range m, cost i j :=
    sum_lt_sum_of_nonempty hne' fun i hi => sum_lt_sum_of_nonempty hne' fun j hj => hne i hi j hj
  have hswap : ∑ i ∈ range m, ∑ j ∈ range m, cost i j = ∑ y ∈ H.edges, cap y *
      ∑ i ∈ range m, ∑ j ∈ range m, H.nodeDist ℓ (H.leaf (H.gridRound ℓ m i j y))
        (H.leaf (H.gridRound ℓ m i j (H.T.parent y))) := by
    simp only [cost, terminalDist_eq_nodeDist, mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => Finset.sum_comm
  have hle : ∑ i ∈ range m, ∑ j ∈ range m, cost i j ≤
      ∑ y ∈ H.edges, cap y * (42 * (m : ℝ) ^ 2 * ℓ y + 14 * m * H.rdist ℓ y) := by
    rw [hswap]
    exact sum_le_sum fun y hy => mul_le_mul_of_nonneg_left
      (H.sum_grid_edge_le hℓ hm ((H.mem_edges).mp hy)) (hcap y)
  have hB : ∑ i ∈ range m, ∑ j ∈ range m, B =
      ∑ y ∈ H.edges, cap y * (42 * (m : ℝ) ^ 2 * ℓ y + 14 * m * H.rdist ℓ y) := by
    have e : ∀ y, cap y * (42 * (m : ℝ) ^ 2 * ℓ y + 14 * m * H.rdist ℓ y) =
        42 * (m : ℝ) ^ 2 * (cap y * ℓ y) + 14 * m * (cap y * H.rdist ℓ y) := fun y => by ring
    simp only [sum_const, card_range, nsmul_eq_mul, B, e, sum_add_distrib, ← mul_sum]
    field_simp
  linarith

end Hier
end Hierarchy
end CutQueryComplexity
