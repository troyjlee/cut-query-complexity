import CutQueryComplexity.FractionalForest.Deletion
import CutQueryComplexity.Graph.ArborescencePacking
import CutQueryComplexity.DirectedCertificate.Flow

/-! # A small common source set (W4; `cor:small-source-set`)

Take in- and out-arborescence packings of value `λ` in `H` with a common root `r`. Normalize
their underlying forests by `λ` (`normForest`, a fractional spanning tree) and delete from
both. Put `R = Z_in ∪ Z_out ∪ {r}`. Then `F_H(S), F_H(V ∖ S) ≥ (λ/k)|S|` for every
`S ⊆ V ∖ R`, and `|R| ≤ 4(⌈n/k⌉ − 1) + 1` (`small_source_set`). W1 then gives the two separate
shared flows, each carrying `λ/k` per outside vertex in its own direction
(`small_source_set_flows`). Nothing is claimed about their sum.
-/

/-! ## F. A small common source set (`cor:small-source-set`) -/

namespace CutQueryComplexity.DirectedCertificate

open Finset FractionalForest Certificate

variable {V : Type*} [Fintype V] [DecidableEq V] {r : V}

omit [Fintype V] in
theorem row_ind_none {p : V → Option V} {u : V} (h : p u = none) (X : Finset V) :
    ∑ v ∈ X, (if p u = some v then (1 : ℝ) else 0) = 0 := by
  simp [h]

omit [Fintype V] in
theorem row_ind_some {p : V → Option V} {u w : V} (h : p u = some w) (X : Finset V) :
    ∑ v ∈ X, (if p u = some v then (1 : ℝ) else 0) = if w ∈ X then 1 else 0 := by
  simp [h]

omit [Fintype V] in
theorem row_ind_le_one (p : V → Option V) (u : V) (X : Finset V) :
    ∑ v ∈ X, (if p u = some v then (1 : ℝ) else 0) ≤ 1 := by
  rcases Option.eq_none_or_eq_some (p u) with h | ⟨w, h⟩
  · rw [row_ind_none h]; norm_num
  · rw [row_ind_some h]; split_ifs <;> norm_num

omit [Fintype V] in
theorem row_ind_nonneg (p : V → Option V) (u : V) (X : Finset V) :
    0 ≤ ∑ v ∈ X, (if p u = some v then (1 : ℝ) else 0) :=
  sum_nonneg fun v _ => by split_ifs <;> norm_num

theorem load_nonneg {a : InArb r → ℝ} (ha : ∀ T, 0 ≤ a T) (u v : V) : 0 ≤ load a u v :=
  sum_nonneg fun T _ => mul_nonneg (ha T) (by split_ifs <;> norm_num)

theorem load_diag (a : InArb r → ℝ) (v : V) : load a v v = 0 := by
  unfold load
  refine sum_eq_zero fun T _ => ?_
  simp [(mem_inArbs.1 T.2).irrefl v]

/-- Sums of loads over a block are coefficient-weighted sums of arc counts. -/
theorem sum_load_eq (a : InArb r → ℝ) (S X : Finset V) :
    ∑ u ∈ S, ∑ v ∈ X, load a u v =
      ∑ T : InArb r, a T * ∑ u ∈ S, ∑ v ∈ X, (if T.1 u = some v then (1 : ℝ) else 0) := by
  simp only [load, mul_sum]
  exact (sum_congr rfl fun u _ => sum_comm).trans sum_comm

/-- Row sums: a nonroot vertex has load `∑ a` leaving it in total. -/
theorem sum_load_row {a : InArb r → ℝ} {u : V} (hu : u ≠ r) :
    ∑ v, load a u v = ∑ T, a T := by
  have := sum_load_eq a {u} univ
  simp only [sum_singleton] at this
  rw [this]
  refine sum_congr rfl fun T _ => ?_
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 ((mem_inArbs.1 T.2).nonroot u hu)
  rw [row_ind_some hw]; simp

theorem sum_load_row_root (a : InArb r → ℝ) : ∑ v, load a r v = 0 := by
  have := sum_load_eq a {r} univ
  simp only [sum_singleton] at this
  rw [this]
  refine sum_eq_zero fun T _ => ?_
  rw [row_ind_none (mem_inArbs.1 T.2).root, mul_zero]

/-- Each in-arborescence has at most `|S| - 1` arcs inside a nonempty `S`. -/
theorem inner_arcs_le (T : InArb r) {S : Finset V} (hS : S.Nonempty) :
    ∑ u ∈ S, ∑ v ∈ S, (if T.1 u = some v then (1 : ℝ) else 0) ≤ S.card - 1 := by
  have hT := mem_inArbs.1 T.2
  obtain ⟨u0, hu0, hrow⟩ : ∃ u0 ∈ S,
      ∑ v ∈ S, (if T.1 u0 = some v then (1 : ℝ) else 0) = 0 := by
    by_cases hr : r ∈ S
    · exact ⟨r, hr, row_ind_none hT.root S⟩
    · obtain ⟨u, hu, w, hw, huw⟩ := hT.exists_leaving hS hr
      exact ⟨u, hu, by rw [row_ind_some huw]; simp [hw]⟩
  rw [← add_sum_erase S _ hu0, hrow, zero_add]
  have hc : ((S.erase u0).card : ℝ) = S.card - 1 := by
    rw [card_erase_of_mem hu0, Nat.cast_sub (card_pos.2 hS)]; simp
  rw [← hc]
  calc ∑ u ∈ S.erase u0, ∑ v ∈ S, (if T.1 u = some v then (1 : ℝ) else 0)
      ≤ ∑ u ∈ S.erase u0, (1 : ℝ) := sum_le_sum fun u _ => row_ind_le_one _ _ _
    _ = _ := by simp

theorem inner_load_le {a : InArb r → ℝ} (ha : ∀ T, 0 ≤ a T) {S : Finset V} (hS : S.Nonempty) :
    ∑ u ∈ S, ∑ v ∈ S, load a u v ≤ (∑ T, a T) * (S.card - 1) := by
  rw [sum_load_eq, sum_mul]
  exact sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (inner_arcs_le T hS) (ha T)

/-- For `r ∉ S`: the load leaving `S` is `(∑ a)|S|` minus the load inside `S`. -/
theorem leaving_load_eq (a : InArb r → ℝ) {S : Finset V} (hr : r ∉ S) :
    ∑ u ∈ S, ∑ v ∈ Sᶜ, load a u v = (∑ T, a T) * S.card - ∑ u ∈ S, ∑ v ∈ S, load a u v := by
  have h : ∀ u ∈ S, ∑ v ∈ S, load a u v + ∑ v ∈ Sᶜ, load a u v = ∑ T, a T := fun u hu => by
    rw [sum_add_sum_compl]; exact sum_load_row (fun h => hr (h ▸ hu))
  have := sum_congr rfl h
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at this
  linarith

/-- The underlying symmetrized forest of a packing, normalized by its value `λ`. -/
noncomputable def normForest (a : InArb r → ℝ) (ha : ∀ T, 0 ≤ a T) (lam : ℝ) (hlam : 0 ≤ lam) :
    WeightedGraph V where
  w u v := (load a u v + load a v u) / lam
  symm u v := by rw [add_comm]
  nonneg u v := div_nonneg (add_nonneg (load_nonneg ha u v) (load_nonneg ha v u)) hlam
  diag v := by rw [load_diag, add_zero, zero_div]

theorem mass_normForest (a : InArb r → ℝ) (ha : ∀ T, 0 ≤ a T) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : Finset V) :
    mass (normForest a ha lam hlam) S = (∑ u ∈ S, ∑ v ∈ S, load a u v) / lam := by
  simp only [mass, normForest, ← sum_div, sum_add_distrib]
  rw [sum_comm (f := fun u v => load a v u)]
  ring

/-- The normalized forest of a packing of value `λ > 0` is a fractional forest. -/
theorem normForest_isFractionalForest {a : InArb r → ℝ} (ha : ∀ T, 0 ≤ a T) {lam : ℝ}
    (hlam : 0 < lam) (hsum : ∑ T, a T = lam) :
    IsFractionalForest (normForest a ha lam hlam.le) := by
  intro S hS
  rw [mass_normForest, div_le_iff₀ hlam]
  have := inner_load_le ha hS
  rw [hsum] at this
  linarith

/-- ... and in fact a fractional spanning tree: total mass `n - 1`. -/
theorem mass_normForest_univ {a : InArb r → ℝ} (ha : ∀ T, 0 ≤ a T) {lam : ℝ}
    (hlam : 0 < lam) (hsum : ∑ T, a T = lam) :
    mass (normForest a ha lam hlam.le) univ = (Fintype.card V : ℝ) - 1 := by
  rw [mass_normForest, div_eq_iff hlam.ne']
  rw [← add_sum_erase univ _ (mem_univ r), sum_load_row_root, zero_add]
  rw [sum_congr rfl fun u hu => sum_load_row (a := a) (ne_of_mem_erase hu), sum_const,
    card_erase_of_mem (mem_univ r), nsmul_eq_mul, hsum, card_univ,
    Nat.cast_sub (Fintype.card_pos_iff.2 ⟨r⟩)]
  push_cast; ring

/-- Load leaving `S ∌ r` is at least `λ/k |S|` when the normalized forest meets the target. -/
theorem leaving_load_ge {a : InArb r → ℝ} (ha : ∀ T, 0 ≤ a T) {lam : ℝ} (hlam : 0 < lam)
    (hsum : ∑ T, a T = lam) {k : ℕ} {S : Finset V} (hr : r ∉ S)
    (hS : mass (normForest a ha lam hlam.le) S ≤ (1 - 1 / (k : ℝ)) * S.card) :
    lam / k * S.card ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, load a u v := by
  rw [leaving_load_eq a hr, hsum]
  rw [mass_normForest, div_le_iff₀ hlam] at hS
  have : lam / k * S.card = lam * S.card - (1 - 1 / (k : ℝ)) * S.card * lam := by ring
  linarith

/-- **Small common source set** (`cor:small-source-set`), conditional on unit progress for
every fractional forest and every `k ≥ 3`. Given in- and out-packings of value `λ > 0` with
common root `r` under `H`, there is `R ∋ r` with `|R| ≤ 4(⌈n/k⌉ - 1) + 1` such that every
`S` avoiding `R` has `λ/k |S| ≤ F_H(S)` and `λ/k |S| ≤ F_H(V ∖ S)`. -/
theorem small_source_set (H : WeightedDiGraph V) (r : V) {lam : ℝ} (hlam : 0 < lam)
    (a b : InArb r → ℝ) (ha : ∀ T, 0 ≤ a T) (hasum : ∑ T, a T = lam)
    (haload : ∀ u v, load a u v ≤ H.c u v)
    (hb : ∀ T, 0 ≤ b T) (hbsum : ∑ T, b T = lam) (hbload : ∀ u v, outLoad b u v ≤ H.c u v)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V)
    (hprog : ∀ x : WeightedGraph V, IsFractionalForest x → ∀ k : ℕ, 3 ≤ k → ∀ W : Finset V,
      (∃ S ⊆ W, (1 - 1 / (k : ℝ)) * S.card < mass x S) → ∃ v ∈ W, 1 ≤ gain x (2 / k) W v) :
    ∃ R : Finset V, r ∈ R ∧ R.card ≤ 4 * (ceilA (Fintype.card V) k - 1) + 1 ∧
      ∀ S : Finset V, Disjoint S R → lam / k * S.card ≤ H.out S ∧ lam / k * S.card ≤ H.out Sᶜ := by
  have hxa := normForest_isFractionalForest ha hlam hasum
  have hxb := normForest_isFractionalForest hb hlam hbsum
  obtain ⟨Za, hZa, hTa⟩ := forest_deletion_uniform hxa hk hkn (hprog _ hxa)
  obtain ⟨Zb, hZb, hTb⟩ := forest_deletion_uniform hxb hk hkn (hprog _ hxb)
  refine ⟨Za ∪ Zb ∪ {r}, mem_union_right _ (mem_singleton_self r), ?_, ?_⟩
  · calc (Za ∪ Zb ∪ {r}).card ≤ (Za ∪ Zb).card + ({r} : Finset V).card := card_union_le _ _
      _ ≤ Za.card + Zb.card + 1 := by rw [card_singleton]; exact Nat.add_le_add_right (card_union_le _ _) 1
      _ ≤ _ := by omega
  · intro S hS
    rw [disjoint_union_right, disjoint_union_right, disjoint_singleton_right] at hS
    obtain ⟨⟨hSa, hSb⟩, hr⟩ := hS
    constructor
    · calc lam / k * S.card ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, load a u v :=
            leaving_load_ge ha hlam hasum hr (hTa S (subset_compl_iff_disjoint_right.2 hSa))
        _ ≤ H.out S := sum_le_sum fun u _ => sum_le_sum fun v _ => haload u v
    · calc lam / k * S.card ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, load b u v :=
            leaving_load_ge hb hlam hbsum hr (hTb S (subset_compl_iff_disjoint_right.2 hSb))
        _ = ∑ u ∈ Sᶜ, ∑ v ∈ S, outLoad b u v := by rw [sum_comm]; rfl
        _ ≤ H.out Sᶜ := by
            unfold WeightedDiGraph.out; rw [compl_compl]
            exact sum_le_sum fun u _ => sum_le_sum fun v _ => hbload u v

/-- **Shared flows from the small source set.** Two separate feasible flows: one sends `λ/k`
out of every vertex outside `R` into `R`, the other sends `λ/k` from `R` into every vertex
outside `R`. No claim is made that their sum is feasible. -/
theorem small_source_set_flows (H : WeightedDiGraph V) (r : V) {lam : ℝ} (hlam : 0 < lam)
    (a b : InArb r → ℝ) (ha : ∀ T, 0 ≤ a T) (hasum : ∑ T, a T = lam)
    (haload : ∀ u v, load a u v ≤ H.c u v)
    (hb : ∀ T, 0 ≤ b T) (hbsum : ∑ T, b T = lam) (hbload : ∀ u v, outLoad b u v ≤ H.c u v)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V)
    (hprog : ∀ x : WeightedGraph V, IsFractionalForest x → ∀ k : ℕ, 3 ≤ k → ∀ W : Finset V,
      (∃ S ⊆ W, (1 - 1 / (k : ℝ)) * S.card < mass x S) → ∃ v ∈ W, 1 ≤ gain x (2 / k) W v) :
    ∃ R : Finset V, r ∈ R ∧ R.card ≤ 4 * (ceilA (Fintype.card V) k - 1) + 1 ∧
      (∃ f : V → V → ℝ, H.Feasible f ∧ (∀ v, v ∉ R → netOut f v = lam / k) ∧
        ∀ v ∈ R, netOut f v ≤ 0) ∧
      (∃ g : V → V → ℝ, H.Feasible g ∧ (∀ v, v ∉ R → netOut g v = -(lam / k)) ∧
        ∀ v ∈ R, 0 ≤ netOut g v) := by
  obtain ⟨R, hr, hcard, hcut⟩ :=
    small_source_set H r hlam a b ha hasum haload hb hbsum hbload hk hkn hprog
  have hβ : 0 ≤ lam / k := div_nonneg hlam.le (Nat.cast_nonneg k)
  exact ⟨R, hr, hcard, (H.uniform_supply_iff _ hβ R).1 fun S hS => (hcut S hS).1,
    (H.uniform_demand_iff _ hβ R).1 fun S hS => (hcut S hS).2⟩

end CutQueryComplexity.DirectedCertificate
