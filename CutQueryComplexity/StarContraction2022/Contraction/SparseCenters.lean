import CutQueryComplexity.StarContraction2022.Probability.ConditionalRatio
import CutQueryComplexity.AllPairsAudit.CutAlgebra
import CutQueryComplexity.Primitive.Learn

/-!
# Public center sampling and original-cut ratio bounds

The sampler receives a public probability, and the statistics program receives
only the sampled public center set. The fixed minimum cut is used exclusively
in the analysis. Crossing fractions are zero at vertices of degree zero.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction

open Finset WeightedGraph AllPairsAudit
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- One independent center decision per named input vertex. -/
def sampleCenters (p : ℝ≥0∞) (hp : p ≤ 1) : PMF (Finset V) :=
  Probability.bernoulliSubset univ p hp

/-- The underlying independent bit has an actual normalized mass function,
including the deterministic p=0 and p=1 endpoints. -/
def centerBit (p : ℝ≥0∞) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b = true then p else 1 - p) (by
    rw [Fintype.sum_bool]
    change p + (1 - p) = 1
    exact add_tsub_cancel_of_le hp)

@[simp] theorem centerBit_apply (p : ℝ≥0∞) (hp : p ≤ 1) (b : Bool) :
    centerBit p hp b = if b = true then p else 1 - p := rfl

def centerBits (p : ℝ≥0∞) (hp : p ≤ 1) : PMF (V → Bool) :=
  Probability.product fun _ : V => centerBit p hp

theorem map_point_mass {A B : Type*} (p : PMF A) (f : A → B) (b : B) :
    (p.map f) b = mass p (fun a => f a = b) := by
  rw [PMF.map_apply, mass_eq_tsum]
  apply tsum_congr
  intro a
  simp only [eq_comm]

theorem selected_eq_iff (N S : Finset V) (hSN : S ⊆ N) (bits : V → Bool) :
    N.filter (fun v => bits v = true) = S ↔
      ∀ v, v ∈ N → (bits v = true ↔ v ∈ S) := by
  constructor
  · intro he v hv
    have hm : v ∈ N.filter (fun w => bits w = true) ↔ v ∈ S := by rw [he]
    simpa only [mem_filter, hv, true_and] using hm
  · intro h
    ext v
    by_cases hv : v ∈ N
    · simp only [mem_filter, hv, true_and, h v hv]
    · have hs : v ∉ S := fun hS => hv (hSN hS)
      simp [hv, hs]

/-- Restricting the actual independent bit tape to any fixed row produces
the actual Bernoulli subset law on that row. Other bits are integrated out. -/
theorem centerBits_subset_law (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1) :
    (centerBits (V := V) p hp).map (fun bits => N.filter (fun v => bits v = true)) =
      Probability.bernoulliSubset N p hp := by
  ext S : 1
  rw [map_point_mass, Probability.bernoulliSubset_apply]
  by_cases hSN : S ⊆ N
  · rw [if_pos hSN]
    have he : (fun bits : V → Bool => N.filter (fun v => bits v = true) = S) =
        (fun bits => ∀ v, v ∈ N → (bits v = true ↔ v ∈ S)) := by
      funext bits
      exact propext (selected_eq_iff N S hSN bits)
    rw [he, centerBits,
      Probability.mass_product (fun _ : V => centerBit p hp)
        (fun v b => v ∈ N → (b = true ↔ v ∈ S))]
    have hmass (v : V) :
        mass (centerBit p hp) (fun b => v ∈ N → (b = true ↔ v ∈ S)) =
          if v ∈ N then (if v ∈ S then p else 1 - p) else 1 := by
      by_cases hvN : v ∈ N
      · rw [if_pos hvN, mass_eq_tsum, tsum_fintype, Fintype.sum_bool]
        by_cases hvS : v ∈ S <;> simp [centerBit_apply, hvN, hvS]
      · simp [hvN]
    simp_rw [hmass]
    rw [Fintype.prod_ite_mem, Finset.prod_ite]
    have hyes : N.filter (fun v => v ∈ S) = S := by
      ext v
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun hv => ⟨hSN hv, hv⟩⟩
    have hno : N.filter (fun v => v ∉ S) = N \ S := by ext v; simp
    rw [hyes, hno]
    simp only [Finset.prod_const, card_sdiff_of_subset hSN]
  · rw [if_neg hSN]
    have he : (fun bits : V → Bool => N.filter (fun v => bits v = true) = S) =
        (fun _ => False) := by
      funext bits
      apply propext
      constructor
      · intro hh
        exact hSN (hh ▸ filter_subset _ _)
      · exact False.elim
    rw [he, mass_false]

/-- The same global center set is used for all rows. Its restriction to one
fixed neighbor list has the proved Bernoulli law, without claiming that
overlapping rows are independent. -/
theorem sampleCenters_restriction (N : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1) :
    (sampleCenters (V := V) p hp).map (fun R => N ∩ R) =
      Probability.bernoulliSubset N p hp := by
  rw [sampleCenters, ← centerBits_subset_law (univ : Finset V) p hp, PMF.map_comp]
  have he : (fun R : Finset V => N ∩ R) ∘
      (fun bits : V → Bool => univ.filter (fun v => bits v = true)) =
      (fun bits => N.filter (fun v => bits v = true)) := by
    funext bits
    ext v
    simp
  rw [he, centerBits_subset_law]

theorem sampleCenters_ratio_mean_le (N C : Finset V) (p : ℝ≥0∞) (hp : p ≤ 1)
    (hC : C ⊆ N) :
    expect (sampleCenters (V := V) p hp)
      (fun R => ENNReal.ofReal (Probability.crossingRatio C (N ∩ R))) ≤
      ENNReal.ofReal ((C.card : ℝ) / N.card) := by
  rw [← expect_map (sampleCenters (V := V) p hp) (fun R => N ∩ R)
    (fun T => ENNReal.ofReal (Probability.crossingRatio C T)), sampleCenters_restriction]
  exact Probability.bernoulliSubset_ratio_mean_le N C p hp hC

theorem sampleCenters_ratio_tenth_tail (N C : Finset V) (p : ℝ≥0∞)
    (hp0 : 0 < p) (hp : p ≤ 1) (hC : C ⊆ N) :
    mass (sampleCenters (V := V) p hp)
      (fun R => (C.card : ℝ) / N.card + 1 / 10 < Probability.crossingRatio C (N ∩ R)) ≤
      (200 * ENNReal.ofReal ((C.card : ℝ) / N.card)) / ((N.card : ℝ≥0∞) * p) := by
  rw [← mass_map (sampleCenters (V := V) p hp) (fun R => N ∩ R)
    (fun T => (C.card : ℝ) / N.card + 1 / 10 < Probability.crossingRatio C T),
    sampleCenters_restriction]
  exact Probability.bernoulliSubset_ratio_tenth_tail N C p hp0 hp hC

def crossingFraction (G : WeightedGraph V) (S : Finset V) (v : V) : ℝ :=
  crossing G S v / G.degree v

theorem crossingFraction_nonneg (G : WeightedGraph V) (S : Finset V) (v : V) :
    0 ≤ crossingFraction G S v :=
  div_nonneg (crossing_nonneg G S v) (degree_nonneg G v)

theorem sum_crossing (G : WeightedGraph V) (S : Finset V) :
    (∑ v, crossing G S v) = 2 * G.cut S := by
  have inside (T : Finset V) : (∑ v ∈ T, crossing G T v) = G.cut T := by
    unfold WeightedGraph.cut
    apply Finset.sum_congr rfl
    intro v hv
    simp only [crossing, hv, ite_true, incident]
  calc
    _ = (∑ v ∈ S, crossing G S v) + ∑ v ∈ Sᶜ, crossing G S v :=
      (sum_add_sum_compl S (fun v => crossing G S v)).symm
    _ = G.cut S + G.cut Sᶜ := by
      rw [inside S]
      congr 1
      simpa only [crossing_compl] using inside Sᶜ
    _ = 2 * G.cut S := by rw [G.cut_compl]; ring

theorem minimum_complement {G : WeightedGraph V} {S : Finset V}
    (hS : IsMinCut G S) : IsMinCut G Sᶜ := by
  refine ⟨⟨?_, (compl_ne_univ_iff_nonempty S).mpr hS.1.1⟩, ?_⟩
  · apply nonempty_iff_ne_empty.mpr
    intro he
    exact hS.1.2 ((compl_eq_empty_iff S).mp he)
  · intro T hT
    rw [G.cut_compl]
    exact hS.2 T hT

/-- When the optimum is below every singleton degree, neither side of an
optimal cut is a singleton. This discharges the vertex-moving precondition. -/
theorem minimum_nontrivial {G : WeightedGraph V} {S : Finset V} {d : ℝ}
    (hS : IsMinCut G S) (hd : ∀ v, d ≤ G.degree v) (hcut : G.cut S < d) :
    NontrivialShore S := by
  have aux (T : Finset V) (hT : ProperShore T) (hc : G.cut T < d) : 2 ≤ T.card := by
    have hpos : 0 < T.card := card_pos.mpr hT.1
    by_contra hn
    have he : T.card = 1 := by omega
    obtain ⟨v, rfl⟩ := card_eq_one.mp he
    rw [G.cut_singleton] at hc
    exact (not_lt_of_ge (hd v)) hc
  exact ⟨aux S hS.1 hcut,
    aux Sᶜ (minimum_complement hS).1 (by simpa only [G.cut_compl] using hcut)⟩

/-- Moving a vertex across a nontrivial minimum cut cannot improve it. -/
theorem minimum_half_crossing {G : WeightedGraph V} {S : Finset V}
    (hS : IsMinCut G S) (hsize : NontrivialShore S) (v : V) :
    2 * crossing G S v ≤ G.degree v := by
  have aux (T : Finset V) (hT : IsMinCut G T) (hc : 2 ≤ T.card) (hv : v ∈ T) :
      2 * crossing G T v ≤ G.degree v := by
    have hproper : ProperShore (T.erase v) := by
      refine ⟨card_pos.mp ?_, ?_⟩
      · rw [card_erase_of_mem hv]
        omega
      · intro he
        have hmem : v ∈ T.erase v := by rw [he]; exact mem_univ _
        exact notMem_erase v T hmem
    have hm := hT.2 (T.erase v) hproper
    rw [cut_erase G hv] at hm
    linarith
  by_cases hv : v ∈ S
  · exact aux S hS hsize.1 hv
  · simpa only [crossing_compl] using
      aux Sᶜ (minimum_complement hS) hsize.2 (mem_compl.mpr hv)

theorem sum_crossingFraction_le {G : WeightedGraph V} (S : Finset V)
    {d : ℝ} (hd0 : 0 < d) (hd : ∀ v, d ≤ G.degree v) :
    (∑ v, crossingFraction G S v) ≤ 2 * G.cut S / d := by
  calc
    _ ≤ ∑ v, crossing G S v / d := by
      apply Finset.sum_le_sum
      intro v _
      exact div_le_div_of_nonneg_left (crossing_nonneg G S v) hd0 (hd v)
    _ = (∑ v, crossing G S v) / d := (sum_div _ _ _).symm
    _ = _ := by rw [sum_crossing]

/-- The actual original minimum supplies (1/2,2)-goodness. No goodness oracle
is an input to sampling or to the query program. -/
theorem minimum_fractions {G : WeightedGraph V} {S : Finset V} {d : ℝ}
    (hS : IsMinCut G S) (hd0 : 0 < d) (hd : ∀ v, d ≤ G.degree v)
    (hcut : G.cut S < d) :
    (∀ v, crossingFraction G S v ≤ 1 / 2) ∧
      (∑ v, crossingFraction G S v) ≤ 2 := by
  refine ⟨?_, (sum_crossingFraction_le S hd0 hd).trans ?_⟩
  · intro v
    have hh := minimum_half_crossing hS (minimum_nontrivial hS hd hcut) v
    unfold crossingFraction
    apply (div_le_iff₀ (hd0.trans_le (hd v))).mpr
    linarith
  · apply (div_le_iff₀ hd0).mpr
    linarith

/-- All center-neighbor weights are measured with three public cut families.
The vertex is removed from the second shore, so the cross identity is valid
even for a vertex that is itself a center. -/
def centerStatistics (R : Finset V) :
    DTree (Finset V) ℝ (V → ℝ) (3 * Fintype.card V) :=
  ((DTree.queryAll (fun v : V => ({v} : Finset V)) (fun _ => (0 : ℝ))).bind fun a =>
    (DTree.queryAll (fun v => R.erase v) (fun _ => (0 : ℝ))).bind fun b =>
      (DTree.queryAll (fun v => ({v} : Finset V) ∪ R.erase v) (fun _ => (0 : ℝ))).map
        (fun c v => (a v + b v - c v) / 2)).cast (by omega)

theorem centerStatistics_eval (G : WeightedGraph V) (R : Finset V) :
    (centerStatistics R).eval G.cut = fun v => incident G v R := by
  simp only [centerStatistics, DTree.eval, DTree.run_cast, DTree.run_bind,
    DTree.run_map, DTree.queryAll_run]
  funext v
  have he := G.cross_eq_three_cuts
    (disjoint_singleton_left.mpr (notMem_erase v R))
  have hc : G.cross {v} (R.erase v) = incident G v R := by
    simpa only [WeightedGraph.cross, sum_singleton, incident] using incident_erase_self G v R
  exact he.symm.trans hc

theorem centerStatistics_cost (R : Finset V) (answer : Finset V → ℝ) :
    (centerStatistics R).cost answer ≤ 3 * Fintype.card V := DTree.cost_le _ _

/-- The measured bad set is split once into inside and outside portions.
This identity prevents paying its cardinality twice in the component bound. -/
theorem badSet_split (B R : Finset V) :
    (B \ R).card + (B ∩ R).card = B.card := card_sdiff_add_card_inter B R

#print axioms minimum_nontrivial
#print axioms centerBits_subset_law
#print axioms sampleCenters_restriction
#print axioms sampleCenters_ratio_mean_le
#print axioms sampleCenters_ratio_tenth_tail
#print axioms minimum_half_crossing
#print axioms minimum_fractions
#print axioms centerStatistics_eval
#print axioms centerStatistics_cost
#print axioms badSet_split

end
end CutQueryComplexity.StarContraction2022.Contraction
