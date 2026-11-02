import CutQueryComplexity.Sparsification.CutTailBound
import CutQueryComplexity.Sparsification.EstimateSound

/-! # Completeness of the estimation contraction

Let `C` be `κ`-strong in the reference graph, and let every counted draw have
weight at most `κ/ρ`. Restricting the sample to `C` gives a law whose mean is the
reference restricted to `C`; every pair inside `C` has strength at least `κ`
there, so each draw copy is `ρ`-smooth. The summed cut tails then preserve every
cut of the restriction within `1 ± 1/4`. In particular `C` remains
`3κ/4`-strong in the sample, so a `3κ/4` contraction keeps it in one block.

Draws landing outside `C` contribute zero after restriction; the admissibility
condition is needed only for edges inside `C`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem induce_addition (X Y : WeightedGraph V) (C : Finset V) :
    (X + Y).induce C = X.induce C + Y.induce C := by
  ext u v
  by_cases h : u ∈ C ∧ v ∈ C <;> simp [induce, h]

omit [Fintype V] in
@[simp] theorem induce_zero (C : Finset V) : (0 : WeightedGraph V).induce C = 0 := by
  ext u v
  simp [induce]

omit [Fintype V] in
theorem induce_edgeGraph (e : EdgeIndex V) (a : ℝ) (ha : 0 ≤ a) (C : Finset V) :
    (edgeGraph e a ha).induce C =
      if e.val.1 ∈ C ∧ e.val.2 ∈ C then edgeGraph e a ha else 0 := by
  rcases e with ⟨⟨x, y⟩, hne⟩
  ext u v
  simp only [induce, edgeGraph]
  split_ifs with h1 h2 h2 <;> simp_all [Prod.ext_iff] <;> aesop

/-- Inside a `κ`-strong set, every pair is at least `κ`-strong in the restriction. -/
theorem IsStrong.le_strength_induce {R : WeightedGraph V} {κ : ℝ} {C : Finset V}
    (h : R.IsStrong κ C) {u v : V} (hne : u ≠ v) (hu : u ∈ C) (hv : v ∈ C) :
    κ ≤ (R.induce C).strength u v := by
  have hn : 2 ≤ C.card := by
    have : ({u, v} : Finset V) ⊆ C := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    simpa [Finset.card_pair hne] using Finset.card_le_card this
  have hm := (R.isStrong_iff_le_inducedMincut hn κ).mp h
  rw [← R.inducedMincut_induce_self C] at hm
  exact hm.trans ((R.induce C).inducedMincut_le_strength hne hu hv)

namespace CountedBucket

/-- Restricted component cuts still have independent bounded-draw laws. -/
theorem sampleLaw_induce_boundedCutLaw (bs : List (CountedBucket V)) {κ c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ b ∈ bs, c * (b.mass / b.count) ≤ κ) {C : Finset V}
    (hC : (reference bs).IsStrong κ C) (U S : Finset V) :
    HasBoundedCutLaw
      (((reference bs).induce C).strengthPieceLaw ((sampleLaw bs).map (fun X => X.induce C))
        U c hc) S := by
  set G := (reference bs).induce C
  let f := fun X : WeightedGraph V => ((G.strengthPiece (X.induce C) U).scale c hc).cut S
  have hzero : f 0 = 0 := by simp [f, cut_scale]
  have hadd (X Y : WeightedGraph V) : f (X + Y) = f X + f Y := by
    simp only [f, induce_addition, strengthPiece_add, cut_scale, cut_addition, mul_add]
  obtain ⟨ds, hds⟩ := independentGraphSum_boundedLaw ((expanded bs).map drawLaw) f hzero hadd
    (by
      intro p hp X hX
      obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hp
      obtain ⟨e, _, rfl⟩ := (b.mem_support_drawLaw X).mp hX
      refine ⟨cut_nonneg _ _, ?_⟩
      simp only [f, induce_edgeGraph]
      split_ifs with hm
      · exact G.strengthPiece_edgeGraph_cut_le_one U S e _ _ c hc
          ((hb b (mem_of_mem_expanded hb')).trans
            (hC.le_strength_induce e.property hm.1 hm.2))
      · simp [cut_scale])
  refine ⟨ds, ?_⟩
  simpa only [strengthPieceLaw, PMF.map_comp, Function.comp_def, sampleLaw, f] using hds

/-- The restriction to a strong set is a `1 ± 1/4` sparsifier with explicit confidence. -/
theorem sampleLaw_induce_sparsifier (bs : List (CountedBucket V)) {κ ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2) (hb : ∀ b ∈ bs, ρ * (b.mass / b.count) ≤ κ) {C : Finset V}
    (hC : (reference bs).IsStrong κ C)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ / 4) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤
      (Probability.mass (sampleLaw bs)
        (fun X => IsCutSparsifier (1 / 4) ((reference bs).induce C) (X.induce C))).toReal := by
  set G := (reference bs).induce C
  have hmean : HasMean ((sampleLaw bs).map (fun X => X.induce C)) G :=
    (sampleLaw_mean bs).induce C
  have hexp' : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-((1 / 4 : ℝ) ^ 2 * ρ / 8)) ≤
      δ / 4 := by
    convert hexp using 4
    ring
  have h := hmean.sparsifier_success_of_cut_tail_bounds (ε := 1 / 4) (by norm_num)
    (by norm_num) hρ hδ
    (fun U _ S _ => sampleLaw_induce_boundedCutLaw bs hρ.le hb hC U S)
    (fun U hU => G.strengthPiece_cutTailSum_le_of_exp hU hρ hδ2 hexp')
  simpa only [mass_map, Function.comp_def] using h

/-- **Completeness.** A `κ`-strong set of the reference graph stays `3κ/4`-strong
in the counted sample with probability at least `1 − (|V|−1)δ`. -/
theorem sampleLaw_complete (bs : List (CountedBucket V)) {κ ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2) (hb : ∀ b ∈ bs, ρ * (b.mass / b.count) ≤ κ) {C : Finset V}
    (hC : (reference bs).IsStrong κ C)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ / 4) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤
      (Probability.mass (sampleLaw bs) (fun X => X.IsStrong (3 * κ / 4) C)).toReal := by
  apply (sampleLaw_induce_sparsifier bs hρ hδ hδ2 hb hC hexp).trans
  apply ENNReal.toReal_mono (mass_ne_top _ _)
  apply mass_mono
  intro X hX S hS hT
  have hk := hC S hS hT
  have hl := (hX.2 S).1
  rw [← localCut_eq_cut_induce, ← localCut_eq_cut_induce] at hl
  linarith

end CountedBucket
end
end CutQueryComplexity.WeightedGraph
