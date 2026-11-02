import CutQueryComplexity.DirectedUnitST.Repair.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra

/-! # Small cuts from disjoint middle rectangles

The rectangle lemma bounds only arcs crossing the chosen cut.  Other arcs,
in particular auxiliary source and sink stars, can have arbitrary capacity.
The averaging lemma is shared by BFS middle layers and potential bands.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Repair

open Finset Certificate DirectedCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If every positive crossing arc lies in `A × B`, the cut is exactly that
rectangle.  No condition is imposed on arcs that do not cross the cut. -/
theorem out_eq_rectangle (G : WeightedDiGraph V) (S A B : Finset V)
    (hA : A ⊆ S) (hB : B ⊆ Sᶜ)
    (hcross : ∀ u ∈ S, ∀ v ∈ Sᶜ, 0 < G.c u v → u ∈ A ∧ v ∈ B) :
    G.out S = ∑ u ∈ A, ∑ v ∈ B, G.c u v := by
  unfold WeightedDiGraph.out
  calc
    _ = ∑ u ∈ A, ∑ v ∈ Sᶜ, G.c u v := by
      symm
      apply sum_subset hA
      intro u hu huA
      apply sum_eq_zero
      intro v hv
      exact le_antisymm (le_of_not_gt fun hp => huA (hcross u hu v hv hp).1)
        (G.nonneg u v)
    _ = _ := by
      apply sum_congr rfl
      intro u hu
      symm
      apply sum_subset hB
      intro v hv hvB
      exact le_antisymm (le_of_not_gt fun hp => hvB (hcross u (hA hu) v hv hp).2)
        (G.nonneg u v)

theorem out_le_two_mul_card (G : WeightedDiGraph V) (S A B : Finset V)
    (hA : A ⊆ S) (hB : B ⊆ Sᶜ)
    (hcross : ∀ u ∈ S, ∀ v ∈ Sᶜ, 0 < G.c u v → u ∈ A ∧ v ∈ B)
    (hcap : ∀ u ∈ A, ∀ v ∈ B, G.c u v ≤ 2) :
    G.out S ≤ 2 * (A.card : ℝ) * B.card := by
  rw [out_eq_rectangle G S A B hA hB hcross]
  calc
    _ ≤ ∑ u ∈ A, ∑ v ∈ B, (2 : ℝ) :=
      sum_le_sum fun u hu => sum_le_sum fun v hv => hcap u hu v hv
    _ = _ := by simp; ring

omit [DecidableEq V] in
/-- Any feasible internal transshipment already has total supply at most
`n²/2`.  Thus the repair precondition `R ≤ n²` follows without inspecting the
hidden original directions or assuming a path decomposition. -/
theorem feasible_supply_le_half_sq (G : WeightedDiGraph V) (hG : PairBounded G)
    (f : V → V → ℝ) (hf : G.Feasible f) :
    supply (netOut f) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  classical
  let S := univ.filter fun v => 0 < netOut f v
  have hsup : supply (netOut f) = ∑ v ∈ S, netOut f v := by
    simp only [supply, S, sum_filter]
    apply sum_congr rfl
    intro v _
    by_cases h : 0 < netOut f v
    · simp only [h, ↓reduceIte, max_eq_left h.le]
    · simp only [h, ↓reduceIte, max_eq_right (le_of_not_gt h)]
  have hflow := WeightedDiGraph.sum_netOut_le_out hf S
  have hcut := out_le_two_mul_card G S S Sᶜ (Subset.refl _) (Subset.refl _)
    (fun _ hu _ hv _ => ⟨hu, hv⟩) (fun u _ v _ => hG.arc_le_two u v)
  have hcard : (S.card : ℝ) + Sᶜ.card = Fintype.card V := by
    exact_mod_cast card_add_card_compl S
  rw [hsup]
  nlinarith [sq_nonneg ((S.card : ℝ) - Sᶜ.card)]

omit [Fintype V] in
/-- A disjoint family of vertex sets contains a member no larger than its
average.  The scaled formulation avoids any rounding or division premise. -/
theorem exists_small_disjoint_member_in {I : Type*} [DecidableEq I]
    (region : Finset V)
    (indices : Finset I) (hne : indices.Nonempty) (C : I → Finset V)
    (hsub : ∀ i ∈ indices, C i ⊆ region)
    (hdisj : (indices : Set I).PairwiseDisjoint C) :
    ∃ i ∈ indices, indices.card * (C i).card ≤ region.card := by
  have htotal : ∑ i ∈ indices, (C i).card ≤ region.card := by
    rw [← card_biUnion hdisj]
    exact card_le_card (biUnion_subset.mpr hsub)
  by_contra! h
  obtain ⟨i, hi⟩ := hne
  have hsum : ∑ _ ∈ indices, region.card <
      ∑ j ∈ indices, indices.card * (C j).card :=
    sum_lt_sum (fun j hj => (h j hj).le) ⟨i, hi, h i hi⟩
  simp only [sum_const, nsmul_eq_mul, ← mul_sum] at hsum
  exact (not_lt_of_ge (Nat.mul_le_mul_left indices.card htotal)) hsum

/-- Unrestricted-vertex version of the disjoint-set averaging lemma. -/
theorem exists_small_disjoint_member {I : Type*} [DecidableEq I]
    (indices : Finset I) (hne : indices.Nonempty) (C : I → Finset V)
    (hdisj : (indices : Set I).PairwiseDisjoint C) :
    ∃ i ∈ indices, indices.card * (C i).card ≤ Fintype.card V := by
  simpa only [card_univ] using exists_small_disjoint_member_in (univ : Finset V)
    indices hne C (fun _ _ => subset_univ _) hdisj

/-- Disjoint middle rectangles give a small cut.  The conclusion is
`cut ≤ n²/(2m²)` in a denominator-free form. -/
theorem exists_small_rectangle_cut_in {I : Type*} [DecidableEq I]
    (G : WeightedDiGraph V) (region : Finset V) (indices : Finset I) (hne : indices.Nonempty)
    (S A B : I → Finset V)
    (hsub : ∀ i ∈ indices, A i ∪ B i ⊆ region)
    (hAB : ∀ i ∈ indices, Disjoint (A i) (B i))
    (hdisj : (indices : Set I).PairwiseDisjoint (fun i => A i ∪ B i))
    (hcut : ∀ i ∈ indices, G.out (S i) ≤ 2 * ((A i).card : ℝ) * (B i).card) :
    ∃ i ∈ indices,
      2 * (indices.card : ℝ) ^ 2 * G.out (S i) ≤ (region.card : ℝ) ^ 2 := by
  obtain ⟨i, hi, hsize⟩ := exists_small_disjoint_member_in region indices hne
    (fun i => A i ∪ B i) hsub hdisj
  rw [card_union_of_disjoint (hAB i hi)] at hsize
  have hsizeR : (indices.card : ℝ) * ((A i).card + (B i).card) ≤ region.card := by
    exact_mod_cast hsize
  have hsquare := mul_self_le_mul_self (by positivity) hsizeR
  have hbalance := sq_nonneg (((A i).card : ℝ) - (B i).card)
  have hproduct : 4 * ((A i).card : ℝ) * (B i).card ≤
      (((A i).card : ℝ) + (B i).card) ^ 2 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hproduct
    (sq_nonneg (indices.card : ℝ))
  have hscaledCut := mul_le_mul_of_nonneg_left (hcut i hi)
    (show 0 ≤ 2 * (indices.card : ℝ) ^ 2 by positivity)
  refine ⟨i, hi, ?_⟩
  nlinarith

/-- Unrestricted-vertex version of the small-rectangle cut lemma. -/
theorem exists_small_rectangle_cut {I : Type*} [DecidableEq I]
    (G : WeightedDiGraph V) (indices : Finset I) (hne : indices.Nonempty)
    (S A B : I → Finset V)
    (hAB : ∀ i ∈ indices, Disjoint (A i) (B i))
    (hdisj : (indices : Set I).PairwiseDisjoint (fun i => A i ∪ B i))
    (hcut : ∀ i ∈ indices, G.out (S i) ≤ 2 * ((A i).card : ℝ) * (B i).card) :
    ∃ i ∈ indices,
      2 * (indices.card : ℝ) ^ 2 * G.out (S i) ≤ (Fintype.card V : ℝ) ^ 2 := by
  simpa only [card_univ] using exists_small_rectangle_cut_in G (univ : Finset V)
    indices hne S A B (fun _ _ => subset_univ _) hAB hdisj hcut

omit [Fintype V] [DecidableEq V] in
/-- A positive arc crossing a BFS prefix must join the last level to the
next one.  The edge premise applies to **every** positive capacity arc. -/
theorem crossing_levels {G : WeightedDiGraph V} (level : V → ℕ)
    (hlevel : ∀ u v, 0 < G.c u v → level v ≤ level u + 1)
    {u v : V} {i : ℕ} (hu : level u ≤ i) (hv : i < level v)
    (hpos : 0 < G.c u v) : level u = i ∧ level v = i + 1 := by
  have := hlevel u v hpos
  omega

omit [Fintype V] [DecidableEq V] in
/-- Heavy source/sink arcs are excluded from every middle prefix.  This
requires no bound at all on an arc incident to `s` or `t`. -/
theorem middle_crossing_internal {G : WeightedDiGraph V} (level : V → ℕ)
    (hlevel : ∀ u v, 0 < G.c u v → level v ≤ level u + 1)
    {s t u v : V} {i d : ℕ} (hs : level s = 0) (ht : level t = d)
    (hi : 1 ≤ i) (hid : i + 2 ≤ d) (hu : level u ≤ i) (hv : i < level v)
    (hpos : 0 < G.c u v) : u ≠ s ∧ u ≠ t ∧ v ≠ s ∧ v ≠ t := by
  obtain ⟨hul, hvl⟩ := crossing_levels level hlevel hu hv hpos
  constructor
  · intro h; subst u; omega
  constructor
  · intro h; subst u; omega
  constructor
  · intro h; subst v; omega
  · intro h; subst v; omega

/-- A level set, including no assumptions about the way levels were found. -/
def layer (level : V → ℕ) (i : ℕ) : Finset V := univ.filter fun v => level v = i

def levelPrefix (level : V → ℕ) (i : ℕ) : Finset V := univ.filter fun v => level v ≤ i

def internalVertices (s t : V) : Finset V := univ.filter fun v => v ≠ s ∧ v ≠ t

theorem middle_cut_bound (G : WeightedDiGraph V) (level : V → ℕ)
    (hlevel : ∀ u v, 0 < G.c u v → level v ≤ level u + 1)
    (s t : V) (d i : ℕ) (hs : level s = 0) (ht : level t = d)
    (hi : 1 ≤ i) (hid : i + 2 ≤ d)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t →
      G.c u v + G.c v u ≤ 2) :
    G.out (levelPrefix level i) ≤
      2 * ((layer level i).card : ℝ) * (layer level (i + 1)).card := by
  apply out_le_two_mul_card
  · intro v hv
    simp only [layer, levelPrefix, mem_filter, mem_univ, true_and] at hv ⊢
    omega
  · intro v hv
    simp only [layer, mem_filter, mem_univ, true_and] at hv
    simp only [mem_compl, levelPrefix, mem_filter, mem_univ, true_and, not_le]
    omega
  · intro u hu v hv hpos
    simp only [levelPrefix, mem_filter, mem_univ, true_and] at hu
    simp only [mem_compl, levelPrefix, mem_filter, mem_univ, true_and, not_le] at hv
    simpa only [layer, mem_filter, mem_univ, true_and] using
      crossing_levels level hlevel hu hv hpos
  · intro u hu v hv
    simp only [layer, mem_filter, mem_univ, true_and] at hu hv
    have hus : u ≠ s := by intro h; subst u; omega
    have hut : u ≠ t := by intro h; subst u; omega
    have hvs : v ≠ s := by intro h; subst v; omega
    have hvt : v ≠ t := by intro h; subst v; omega
    linarith [hcap u v hus hut hvs hvt, G.nonneg v u]

/-- The accepted middle-layer deficit bound.  Heavy terminal arcs have no
capacity bound; only pairs between the original vertices are bounded by two.
`hlevel` constrains every positive arc in the full residual network. -/
theorem middle_layer_deficit (G : WeightedDiGraph V) (level : V → ℕ)
    (hlevel : ∀ u v, 0 < G.c u v → level v ≤ level u + 1)
    (s t : V) (d : ℕ) (hs : level s = 0) (ht : level t = d) (hd : 4 ≤ d)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t →
      G.c u v + G.c v u ≤ 2)
    (f : V → V → ℝ) (hf : G.STFlow s t f) :
    netOut f s ≤ 8 * ((internalVertices s t).card : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
  let m := (d - 1) / 2
  have hm : 0 < m := by dsimp [m]; omega
  have hmid : ∀ j ∈ range m, 2 * j + 1 + 2 ≤ d := by
    intro j hj
    simp only [mem_range] at hj
    dsimp [m] at hj
    omega
  let S := fun j => levelPrefix level (2 * j + 1)
  let A := fun j => layer level (2 * j + 1)
  let B := fun j => layer level (2 * j + 2)
  have hsub : ∀ j ∈ range m, A j ∪ B j ⊆ internalVertices s t := by
    intro j hj v hv
    simp only [A, B, layer, mem_union, mem_filter, mem_univ, true_and] at hv
    have hjd := hmid j hj
    simp only [internalVertices, mem_filter, mem_univ, true_and]
    constructor
    · intro h; subst v; omega
    · intro h; subst v; omega
  have hAB : ∀ j ∈ range m, Disjoint (A j) (B j) := by
    intro j _
    apply disjoint_left.mpr
    intro v hv hw
    simp only [A, B, layer, mem_filter, mem_univ, true_and] at hv hw
    omega
  have hdisj : (range m : Set ℕ).PairwiseDisjoint (fun j => A j ∪ B j) := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro v hv hw
    simp only [A, B, layer, mem_union, mem_filter, mem_univ, true_and] at hv hw
    omega
  have hcuts : ∀ j ∈ range m, G.out (S j) ≤ 2 * ((A j).card : ℝ) * (B j).card := by
    intro j hj
    exact middle_cut_bound G level hlevel s t d (2 * j + 1) hs ht (by omega)
      (hmid j hj) hcap
  obtain ⟨j, hj, hsmall⟩ := exists_small_rectangle_cut_in G (internalVertices s t)
    (range m) ⟨0, mem_range.mpr hm⟩ S A B hsub hAB hdisj hcuts
  simp only [card_range] at hsmall
  have hstS : s ∈ S j := by simp [S, levelPrefix, hs]
  have httS : t ∉ S j := by
    have := hmid j hj
    simp only [S, levelPrefix, mem_filter, mem_univ, true_and, ht, not_le]
    omega
  have hflow := WeightedDiGraph.netOut_le_out hf hstS httS
  have hdm : (d : ℝ) ≤ 4 * (m : ℝ) := by
    exact_mod_cast (show d ≤ 4 * m by dsimp [m]; omega)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hsq : (d : ℝ) ^ 2 ≤ 16 * (m : ℝ) ^ 2 := by
    have h := mul_self_le_mul_self hdR.le hdm
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq (G.out_nonneg (S j))
  have hflowMul := mul_le_mul_of_nonneg_left hflow (sq_nonneg (d : ℝ))
  apply (le_div_iff₀ (sq_pos_of_pos hdR)).mpr
  nlinarith

/-- The remaining deficit after an arbitrary feasible current s–t flow is
bounded by a middle cut of its full residual network. Opposite internal
pair totals are inherited from the original network; terminal capacities
remain unrestricted. -/
theorem residual_middle_layer_deficit (G : WeightedDiGraph V) (s t : V)
    (target current : V → V → ℝ) (htarget : G.STFlow s t target)
    (hcurrent : G.STFlow s t current) (level : V → ℕ) (d : ℕ)
    (hlevel : ∀ u v, 0 < (residual G current hcurrent.1).c u v →
      level v ≤ level u + 1)
    (hs : level s = 0) (ht : level t = d) (hd : 4 ≤ d)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t →
      G.c u v + G.c v u ≤ 2) :
    netOut target s - netOut current s ≤
      8 * ((internalVertices s t).card : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
  have hdiff : (residual G current hcurrent.1).STFlow s t
      (fun u v => target u v - current u v) := by
    refine ⟨residual_difference_feasible G current target hcurrent.1 htarget.1, ?_⟩
    intro v hvs hvt
    rw [residual_difference_divergence, htarget.2 v hvs hvt, hcurrent.2 v hvs hvt]
    ring
  have hcap' : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t →
      (residual G current hcurrent.1).c u v +
        (residual G current hcurrent.1).c v u ≤ 2 := by
    intro u v hus hut hvs hvt
    rw [residual_pair_sum]
    exact hcap u v hus hut hvs hvt
  have h := middle_layer_deficit (residual G current hcurrent.1) level hlevel
    s t d hs ht hd hcap' (fun u v => target u v - current u v) hdiff
  simpa only [residual_difference_divergence] using h

end CutQueryComplexity.DirectedUnitST.Repair

#print axioms CutQueryComplexity.DirectedUnitST.Repair.out_eq_rectangle
#print axioms CutQueryComplexity.DirectedUnitST.Repair.feasible_supply_le_half_sq
#print axioms CutQueryComplexity.DirectedUnitST.Repair.exists_small_rectangle_cut_in
#print axioms CutQueryComplexity.DirectedUnitST.Repair.middle_crossing_internal
#print axioms CutQueryComplexity.DirectedUnitST.Repair.middle_layer_deficit
#print axioms CutQueryComplexity.DirectedUnitST.Repair.residual_middle_layer_deficit
