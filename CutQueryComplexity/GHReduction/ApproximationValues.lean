import CutQueryComplexity.GHReduction.CanonicalCuts
import CutQueryComplexity.GHReduction.TerminalGuides
import CutQueryComplexity.Graph.ForestFacts

/-! # Approximate source values and exact zero-component information

One simultaneous cut-approximation event controls every pair minimum and every
zero cut. Its component partition can therefore be computed from the explicit
approximator even when later terminal sets are adaptive. Positive terminal
packing is invoked only within a nontrivial connected component.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

theorem stValue_approximation (F K : WeightedGraph V) {eps : ℝ}
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (happrox : ∀ S, (1 - eps) * F.cut S ≤ K.cut S ∧ K.cut S ≤ (1 + eps) * F.cut S)
    {s t : V} (hst : s ≠ t) :
    (1 - eps) * stValue F s t ≤ stValue K s t ∧
      stValue K s t ≤ (1 + eps) * stValue F s t := by
  obtain ⟨SF, hSF, hvF⟩ := exists_stMinCut F hst
  obtain ⟨SK, hSK, hvK⟩ := exists_stMinCut K hst
  constructor
  · calc
      _ ≤ (1 - eps) * F.cut SK :=
        mul_le_mul_of_nonneg_left (stValue_le F hSK.1 hSK.2.1) (sub_nonneg.mpr heps1)
      _ ≤ K.cut SK := (happrox SK).1
      _ = _ := hvK
  · calc
      _ ≤ K.cut SF := stValue_le K hSF.1 hSF.2.1
      _ ≤ (1 + eps) * F.cut SF := (happrox SF).2
      _ = _ := by rw [hvF]

theorem cut_zero_iff_of_approximation (F K : WeightedGraph V) {eps : ℝ} (heps1 : eps < 1)
    (happrox : ∀ S, (1 - eps) * F.cut S ≤ K.cut S ∧ K.cut S ≤ (1 + eps) * F.cut S)
    (S : Finset V) : F.cut S = 0 ↔ K.cut S = 0 := by
  constructor
  · intro hF
    exact le_antisymm (by simpa only [hF, mul_zero] using (happrox S).2) (K.cut_nonneg S)
  · intro hK
    have h := (happrox S).1
    rw [hK] at h
    have hp : 0 < 1 - eps := sub_pos.mpr heps1
    have hn := F.cut_nonneg S
    nlinarith

theorem cut_component_zero (G : WeightedGraph V) (r : V) : G.cut (forestBlock G.support r) = 0 := by
  unfold WeightedGraph.cut
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  by_contra hw
  have hru := (mem_forestBlock G.support r u).mp hu
  have huv : G.support.Reachable u v :=
    (_root_.SimpleGraph.Adj.reachable (G := G.support)) hw
  exact (Finset.mem_compl.mp hv) ((mem_forestBlock G.support r v).mpr (hru.trans huv))

/-- Equality of component relations follows from zero cuts, not from agreement
of individual edges of the sparsifier and the hidden graph. -/
theorem reachable_iff_of_approximation (F K : WeightedGraph V) {eps : ℝ} (heps1 : eps < 1)
    (happrox : ∀ S, (1 - eps) * F.cut S ≤ K.cut S ∧ K.cut S ≤ (1 + eps) * F.cut S)
    (u v : V) : F.support.Reachable u v ↔ K.support.Reachable u v := by
  constructor
  · intro huv
    have hz : F.cut (forestBlock K.support u) = 0 :=
      (cut_zero_iff_of_approximation F K heps1 happrox _).mpr (cut_component_zero K u)
    exact (mem_forestBlock K.support u v).mp
      (reachable_mem_of_cut_zero F _ hz (root_mem_forestBlock K.support u) huv)
  · intro huv
    have hz : K.cut (forestBlock F.support u) = 0 :=
      (cut_zero_iff_of_approximation F K heps1 happrox _).mp (cut_component_zero F u)
    exact (mem_forestBlock F.support u v).mp
      (reachable_mem_of_cut_zero K _ hz (root_mem_forestBlock F.support u) huv)

theorem stValue_pos_of_reachable (G : WeightedGraph V) {s t : V} (hst : s ≠ t)
    (hreach : G.support.Reachable s t) : 0 < stValue G s t := by
  obtain ⟨S, hS, hval⟩ := exists_stMinCut G hst
  have hz : G.cut S ≠ 0 := by
    intro hz
    exact hS.2.1 (reachable_mem_of_cut_zero G S hz hS.1 hreach)
  rw [← hval]
  exact lt_of_le_of_ne (G.cut_nonneg S) (Ne.symm hz)

theorem stValue_zero_of_not_reachable (G : WeightedGraph V) {s t : V}
    (hreach : ¬G.support.Reachable s t) : stValue G s t = 0 := by
  have hs : s ∈ forestBlock G.support s := root_mem_forestBlock G.support s
  have ht : t ∉ forestBlock G.support s := fun h => hreach ((mem_forestBlock _ _ _).mp h)
  exact le_antisymm ((stValue_le G hs ht).trans_eq (cut_component_zero G s)) (stValue_nonneg G s t)

theorem terminalMin_pos_of_connected (G : WeightedGraph V) (U : Finset V) (hU : 2 ≤ U.card)
    (hconn : ∀ a ∈ U, ∀ b ∈ U, G.support.Reachable a b) : 0 < terminalMin G U := by
  obtain ⟨S, hS, hval⟩ := exists_terminalMin G hU
  obtain ⟨a, ha⟩ := hS.1
  obtain ⟨haS, haU⟩ := Finset.mem_inter.mp ha
  have hex : ∃ b ∈ U, b ∉ S := by
    by_contra hnone
    apply hS.2
    intro b hb
    by_contra hbS
    exact hnone ⟨b, hb, hbS⟩
  obtain ⟨b, hbU, hbS⟩ := hex
  have hab : a ≠ b := fun he => hbS (he ▸ haS)
  have hp := stValue_pos_of_reachable G hab (hconn a haU b hbU)
  exact hp.trans_le ((stValue_le G haS hbS).trans_eq hval)

/-- Lower bounds on source-to-terminal values lower-bound every terminal cut. -/
theorem le_terminalMin_of_source (G : WeightedGraph V) (U : Finset V) (s : V)
    (hU : 2 ≤ U.card) (hs : s ∈ U) (lower : ℝ)
    (hlower : ∀ t ∈ U, t ≠ s → lower ≤ stValue G t s) : lower ≤ terminalMin G U := by
  apply le_terminalMin G hU
  intro S hS
  by_cases hsS : s ∈ S
  · have hex : ∃ t ∈ U, t ∉ S := by
      by_contra hnone
      apply hS.2
      intro t ht
      by_contra htS
      exact hnone ⟨t, ht, htS⟩
    obtain ⟨t, ht, htS⟩ := hex
    have hts : t ≠ s := fun he => htS (he.symm ▸ hsS)
    have h := stValue_le G (S := Sᶜ) (by simpa using htS) (by simpa using hsS)
    exact (hlower t ht hts).trans (by simpa only [cut_compl] using h)
  · obtain ⟨t, ht⟩ := hS.1
    obtain ⟨htS, htU⟩ := Finset.mem_inter.mp ht
    have hts : t ≠ s := fun he => hsS (he ▸ htS)
    exact (hlower t htU hts).trans (stValue_le G htS hsS)

end
end CutQueryComplexity.GHReduction
