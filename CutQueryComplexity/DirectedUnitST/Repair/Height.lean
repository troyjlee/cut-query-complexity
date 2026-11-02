import CutQueryComplexity.DirectedUnitST.Repair.HeavyTerminal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-! # A potential-height bound from cuts of the full capacity network

This is a direct derivation of the height bound in paper 4, rather than a
formalization of its path-decomposition proof.  For cuts at heights `4j+2`,
every crossing arc lies between the two halves of `[4j,4j+4)`.  These bands
are disjoint, so one cut has capacity at most `n²/(2m²)`.  Flow conservation
then bounds the positive potential mass.  The rise hypothesis concerns
**all** positive capacity arcs, never just paths used by a chosen flow.

No integrality, max-flow algorithm, decomposition, query access, or preproved
height-tail estimate is assumed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Repair

open Finset Certificate DirectedCertificate
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def below (r : V → ℝ) (a : ℝ) : Finset V := univ.filter fun v => r v < a

def lowerBand (r : V → ℝ) (j : ℕ) : Finset V :=
  univ.filter fun v => 4 * (j : ℝ) ≤ r v ∧ r v < 4 * (j : ℝ) + 2

def upperBand (r : V → ℝ) (j : ℕ) : Finset V :=
  univ.filter fun v => 4 * (j : ℝ) + 2 ≤ r v ∧ r v < 4 * (j : ℝ) + 4

omit [DecidableEq V] in
theorem bands_disjoint (r : V → ℝ) (j : ℕ) :
    Disjoint (lowerBand r j) (upperBand r j) := by
  apply disjoint_left.mpr
  intro v hv hw
  simp only [lowerBand, upperBand, mem_filter, mem_univ, true_and] at hv hw
  linarith

theorem band_unions_pairwise (r : V → ℝ) (m : ℕ) :
    (range m : Set ℕ).PairwiseDisjoint (fun j => lowerBand r j ∪ upperBand r j) := by
  intro i _ j _ hij
  apply disjoint_left.mpr
  intro v hv hw
  have bounds (k : ℕ) (hk : v ∈ lowerBand r k ∪ upperBand r k) :
      4 * (k : ℝ) ≤ r v ∧ r v < 4 * (k : ℝ) + 4 := by
    simp only [mem_union, lowerBand, upperBand, mem_filter, mem_univ, true_and] at hk
    rcases hk with hk | hk <;> constructor <;> linarith
  have hi := bounds i hv
  have hj := bounds j hw
  rcases lt_or_gt_of_ne hij with h | h
  · have hR : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    linarith
  · have hR : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    linarith

/-- The full-capacity cut at a band midpoint is supported on the adjacent
halves of that band. -/
theorem band_cut_bound (G : WeightedDiGraph V) (hG : PairBounded G)
    (r : V → ℝ) (hrise : ∀ u v, 0 < G.c u v → r v - r u ≤ 2) (j : ℕ) :
    G.out (below r (4 * (j : ℝ) + 2)) ≤
      2 * ((lowerBand r j).card : ℝ) * (upperBand r j).card := by
  apply out_le_two_mul_card
  · intro v hv
    simpa only [below, mem_filter, mem_univ, true_and] using
      (show 4 * (j : ℝ) ≤ r v ∧ r v < 4 * (j : ℝ) + 2 from by
        simpa only [lowerBand, mem_filter, mem_univ, true_and] using hv).2
  · intro v hv
    simp only [upperBand, mem_filter, mem_univ, true_and] at hv
    simp only [mem_compl, below, mem_filter, mem_univ, true_and, not_lt]
    exact hv.1
  · intro u hu v hv hpos
    simp only [below, mem_filter, mem_univ, true_and] at hu
    simp only [mem_compl, below, mem_filter, mem_univ, true_and, not_lt] at hv
    have hr := hrise u v hpos
    simp only [lowerBand, upperBand, mem_filter, mem_univ, true_and]
    constructor <;> constructor <;> linarith
  · intro u _ v _
    exact hG.arc_le_two u v

/-- Among `m` disjoint potential bands is a cut of capacity at most
`n²/(2m²)`, expressed without division. -/
theorem exists_small_band_cut (G : WeightedDiGraph V) (hG : PairBounded G)
    (r : V → ℝ) (hrise : ∀ u v, 0 < G.c u v → r v - r u ≤ 2)
    (m : ℕ) (hm : 0 < m) :
    ∃ j < m, 2 * (m : ℝ) ^ 2 * G.out (below r (4 * (j : ℝ) + 2)) ≤
      (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨j, hj, hcut⟩ := exists_small_rectangle_cut G (range m)
    ⟨0, mem_range.mpr hm⟩ (fun j => below r (4 * (j : ℝ) + 2))
    (lowerBand r) (upperBand r) (fun j _ => bands_disjoint r j)
    (band_unions_pairwise r m) (fun j _ => band_cut_bound G hG r hrise j)
  exact ⟨j, mem_range.mp hj, by simpa only [card_range] using hcut⟩

/-- Conservation bounds the potential mass above a cut by its full capacity. -/
theorem upper_potential_mass_le_cut (G : WeightedDiGraph V) (f : V → V → ℝ)
    (hf : G.Feasible f) (r e : V → ℝ)
    (hdiv : ∀ v, netOut f v = (-r v + e v) / 2)
    (a : ℝ) :
    ∑ v ∈ (below r a)ᶜ, r v ≤ l1 e + 2 * G.out (below r a) := by
  let S := below r a
  have hzero := WeightedDiGraph.sum_univ_netOut hf.1
  have hsplit := sum_add_sum_compl S (netOut f)
  have hcut := WeightedDiGraph.sum_netOut_le_out hf S
  have hpotential : ∑ v ∈ Sᶜ, r v =
      ∑ v ∈ Sᶜ, e v - 2 * ∑ v ∈ Sᶜ, netOut f v := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro v _
    rw [hdiv]
    ring
  have hE := sum_subset_le_l1 e Sᶜ
  linarith

/-- Flow conservation converts an arbitrary nonnegative potential threshold
into a bound on the positive potential mass. -/
theorem supply_potential_le_cut (G : WeightedDiGraph V) (f : V → V → ℝ)
    (hf : G.Feasible f) (r e : V → ℝ)
    (hdiv : ∀ v, netOut f v = (-r v + e v) / 2)
    (a : ℝ) (ha : 0 ≤ a) :
    supply r ≤ (Fintype.card V : ℝ) * a + l1 e + 2 * G.out (below r a) := by
  let S := below r a
  have hhigh := upper_potential_mass_le_cut G f hf r e hdiv a
  have hlow : ∑ v ∈ S, max (r v) 0 ≤ (Fintype.card V : ℝ) * a := by
    calc
      _ ≤ ∑ _ ∈ S, a := by
        apply sum_le_sum
        intro v hv
        have hv' : r v < a := by simpa only [S, below, mem_filter, mem_univ, true_and] using hv
        exact max_le hv'.le ha
      _ = (S.card : ℝ) * a := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ S) ha
  have hhighMax : ∑ v ∈ Sᶜ, max (r v) 0 = ∑ v ∈ Sᶜ, r v := by
    apply sum_congr rfl
    intro v hv
    have hv' : a ≤ r v := by
      simpa only [S, mem_compl, below, mem_filter, mem_univ, true_and, not_lt] using hv
    exact max_eq_left (ha.trans hv')
  unfold supply
  rw [← sum_add_sum_compl S, hhighMax]
  linarith

/-- A reusable height-tail estimate derived from all capacity arcs. -/
theorem potential_height_tail (G : WeightedDiGraph V) (hG : PairBounded G)
    (f : V → V → ℝ) (hf : G.Feasible f) (r e : V → ℝ)
    (hrise : ∀ u v, 0 < G.c u v → r v - r u ≤ 2)
    (hdiv : ∀ v, netOut f v = (-r v + e v) / 2)
    (m : ℕ) (hm : 0 < m) :
    ∑ v ∈ (below r (4 * (m : ℝ)))ᶜ, r v ≤
      l1 e + (Fintype.card V : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
  obtain ⟨j, hj, hcut⟩ := exists_small_band_cut G hG r hrise m hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hjR : (j : ℝ) + 1 ≤ m := by exact_mod_cast (show j + 1 ≤ m by omega)
  have hsub : (below r (4 * (m : ℝ)))ᶜ ⊆ (below r (4 * (j : ℝ) + 2))ᶜ := by
    intro v hv
    simp only [mem_compl, below, mem_filter, mem_univ, true_and, not_lt] at hv ⊢
    linarith
  have hsum : ∑ v ∈ (below r (4 * (m : ℝ)))ᶜ, r v ≤
      ∑ v ∈ (below r (4 * (j : ℝ) + 2))ᶜ, r v := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro v hv _
    simp only [mem_compl, below, mem_filter, mem_univ, true_and, not_lt] at hv
    have hj0 : (0 : ℝ) ≤ j := by positivity
    linarith
  have hhigh := upper_potential_mass_le_cut G f hf r e hdiv (4 * (j : ℝ) + 2)
  have hcut' : 2 * G.out (below r (4 * (j : ℝ) + 2)) ≤
      (Fintype.card V : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hmR)).mpr
    nlinarith
  linarith

omit [DecidableEq V] in
/-- Integer-parameter height bound.  No tail bound is an input. -/
theorem potential_height_integer (G : WeightedDiGraph V) (hG : PairBounded G)
    (f : V → V → ℝ) (hf : G.Feasible f) (r e : V → ℝ)
    (hr : ∑ v, r v = 0)
    (hrise : ∀ u v, 0 < G.c u v → r v - r u ≤ 2)
    (hdiv : ∀ v, netOut f v = (-r v + e v) / 2)
    (m : ℕ) (hm : 0 < m) :
    supply (netOut f) ≤ 2 * (m : ℝ) * Fintype.card V +
      (Fintype.card V : ℝ) ^ 2 / (2 * (m : ℝ) ^ 2) + 3 * l1 e / 4 := by
  obtain ⟨j, hj, hcut⟩ := exists_small_band_cut G hG r hrise m hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hjR : (j : ℝ) + 1 ≤ m := by exact_mod_cast (show j + 1 ≤ m by omega)
  have hpot := supply_potential_le_cut G f hf r e hdiv (4 * (j : ℝ) + 2) (by positivity)
  have hcut' : G.out (below r (4 * (j : ℝ) + 2)) ≤
      (Fintype.card V : ℝ) ^ 2 / (2 * (m : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hnorm : 2 * l1 (netOut f) ≤ l1 r + l1 e := by
    unfold l1
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro v _
    rw [hdiv, abs_div]
    norm_num
    have habs := abs_add_le (-r v) (e v)
    rw [abs_neg] at habs
    linarith
  have hq := two_supply_of_sum_zero (WeightedDiGraph.sum_univ_netOut hf.1)
  have hp := two_supply_of_sum_zero hr
  have hthreshold : (Fintype.card V : ℝ) * (4 * (j : ℝ) + 2) ≤
      4 * (m : ℝ) * Fintype.card V := by
    have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
    nlinarith
  nlinarith

omit [DecidableEq V] in
/-- The all-arc potential-height theorem, with the stronger error coefficient
`3/4`.  The usual `5/4` bound follows immediately below. -/
theorem potential_height_strong (G : WeightedDiGraph V) (hG : PairBounded G)
    (f : V → V → ℝ) (hf : G.Feasible f) (r e : V → ℝ)
    (hn : 0 < Fintype.card V) (hr : ∑ v, r v = 0)
    (hrise : ∀ u v, 0 < G.c u v → r v - r u ≤ 2)
    (hdiv : ∀ v, netOut f v = (-r v + e v) / 2) :
    supply (netOut f) ≤ 4 * (Fintype.card V : ℝ) ^ (4 / 3 : ℝ) + 3 * l1 e / 4 := by
  let n : ℝ := Fintype.card V
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (show 1 ≤ Fintype.card V by omega)
  have hn0 : 0 < n := by positivity
  let a : ℝ := n ^ (1 / 3 : ℝ)
  have ha1 : 1 ≤ a := Real.one_le_rpow hn1 (by norm_num)
  have ha0 : 0 < a := by linarith
  let m : ℕ := ⌊a⌋₊
  have hm : 0 < m := Nat.floor_pos.mpr ha1
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hmle : (m : ℝ) ≤ a := Nat.floor_le ha0.le
  have hhalf : a ≤ 2 * (m : ℝ) := by
    have h := Nat.lt_floor_add_one a
    change a < (m : ℝ) + 1 at h
    linarith
  have hcube : a ^ 3 = n := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hpower : n * a = n ^ (4 / 3 : ℝ) := by
    calc
      n * a = n ^ (1 : ℝ) * n ^ (1 / 3 : ℝ) := by simp only [Real.rpow_one]; rfl
      _ = n ^ ((1 : ℝ) + 1 / 3) := (Real.rpow_add hn0 _ _).symm
      _ = _ := by norm_num
  have hsquare : a ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by
    have h := mul_self_le_mul_self ha0.le hhalf
    nlinarith
  have hterm : n ^ 2 / (2 * (m : ℝ) ^ 2) ≤ 2 * n * a := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hsquare
      (show 0 ≤ n * a by positivity)
    have hid : n ^ 2 = n * a * a ^ 2 := by rw [← hcube]; ring
    rw [hid]
    nlinarith
  have hfirst : 2 * (m : ℝ) * n ≤ 2 * n * a := by
    nlinarith [mul_le_mul_of_nonneg_left hmle hn0.le]
  have h := potential_height_integer G hG f hf r e hr hrise hdiv m hm
  change supply (netOut f) ≤ 2 * (m : ℝ) * n + n ^ 2 / (2 * (m : ℝ) ^ 2) +
    3 * l1 e / 4 at h
  change supply (netOut f) ≤ 4 * n ^ (4 / 3 : ℝ) + 3 * l1 e / 4
  rw [← hpower]
  linarith

omit [DecidableEq V] in
/-- Paper 4's advertised bound `R ≤ 4n^(4/3) + 5‖e‖₁/4`, proved before
repair from the full represented capacity graph. -/
theorem potential_height (G : WeightedDiGraph V) (hG : PairBounded G)
    (f : V → V → ℝ) (hf : G.Feasible f) (r e : V → ℝ)
    (hn : 0 < Fintype.card V) (hr : ∑ v, r v = 0)
    (hrise : ∀ u v, 0 < G.c u v → r v - r u ≤ 2)
    (hdiv : ∀ v, netOut f v = (-r v + e v) / 2) :
    supply (netOut f) ≤ 4 * (Fintype.card V : ℝ) ^ (4 / 3 : ℝ) + 5 * l1 e / 4 := by
  have h := potential_height_strong G hG f hf r e hn hr hrise hdiv
  linarith [l1_nonneg e]

omit [DecidableEq V] in
/-- Apply the height theorem directly to two capacity representations with
the same opposite-pair totals. The feasible discrepancy flow is constructed
by subtraction, so feasibility of the discrepancy is not an input. `H` may
be the unknown original graph; it is used only as a mathematical witness. -/
theorem representation_height (G H : WeightedDiGraph V) (hG : PairBounded G)
    (htot : ∀ u v, G.c u v + G.c v u = H.c u v + H.c v u)
    (r : V → ℝ) (hn : 0 < Fintype.card V) (hr : ∑ v, r v = 0)
    (hrise : ∀ u v, 0 < G.c u v → r v - r u ≤ 2) :
    supply (fun v => (capacityDiv G v - capacityDiv H v) / 2) ≤
      4 * (Fintype.card V : ℝ) ^ (4 / 3 : ℝ) +
        5 * l1 (fun v => capacityDiv G v - capacityDiv H v + r v) / 4 := by
  let f := fun u v => G.c u v - H.c u v
  let e := fun v => capacityDiv G v - capacityDiv H v + r v
  have hf : G.Feasible f := comparison_feasible G H htot
  have hdiv : ∀ v, netOut f v = (-r v + e v) / 2 := by
    intro v
    rw [show netOut f v = (capacityDiv G v - capacityDiv H v) / 2 from
      comparison_divergence G H htot v]
    dsimp [e]
    ring
  have h := potential_height G hG f hf r e hn hr hrise hdiv
  have hnet : netOut f = fun v => (capacityDiv G v - capacityDiv H v) / 2 := by
    funext v
    exact comparison_divergence G H htot v
  simpa only [hnet] using h

end
end CutQueryComplexity.DirectedUnitST.Repair

#print axioms CutQueryComplexity.DirectedUnitST.Repair.potential_height_tail
#print axioms CutQueryComplexity.DirectedUnitST.Repair.potential_height_integer
#print axioms CutQueryComplexity.DirectedUnitST.Repair.potential_height_strong
#print axioms CutQueryComplexity.DirectedUnitST.Repair.potential_height
#print axioms CutQueryComplexity.DirectedUnitST.Repair.representation_height
