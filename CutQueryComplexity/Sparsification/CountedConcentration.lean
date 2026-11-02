import CutQueryComplexity.Sparsification.CountedSampling
import CutQueryComplexity.Sparsification.ComponentConcentration

/-! # Bounded-draw witnesses for the counted sampler

The count bound is imposed on each occurrence, before repeated edges are
aggregated. It constructs every normalized component cut's bounded-draw law.
Consequently only deterministic cut counting remains in the probability
bound for a fixed family of buckets.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V] [DecidableEq V]

theorem strengthPiece_add (G X Y : WeightedGraph V) (U : Finset V) :
    G.strengthPiece (X + Y) U = G.strengthPiece X U + G.strengthPiece Y U := by
  ext u v
  by_cases hm : u ∈ U ∧ v ∈ U <;> simp [strengthPiece, hm, add_div]

@[simp] theorem strengthPiece_zero (G : WeightedGraph V) (U : Finset V) :
    G.strengthPiece 0 U = 0 := by
  ext; simp [strengthPiece]

theorem strengthPiece_edgeGraph (G : WeightedGraph V) (U : Finset V)
    (e : EdgeIndex V) (a : ℝ) (ha : 0 ≤ a) :
    G.strengthPiece (edgeGraph e a ha) U =
      edgeGraph e (if e.val.1 ∈ U ∧ e.val.2 ∈ U then a / G.strength e.val.1 e.val.2 else 0)
        (by split <;> simp [div_nonneg ha (G.strength_nonneg _ _)]) := by
  rcases e with ⟨⟨u, v⟩, hne⟩
  ext x y
  by_cases hxy : (x, y) = (u, v)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
    simp [strengthPiece, edgeGraph, hne, Ne.symm hne]
  · by_cases hyx : (y, x) = (u, v)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyx
      simp [strengthPiece, edgeGraph, hne, Ne.symm hne, and_comm, G.strength_symm y x]
    · simp only [Prod.mk.injEq] at hxy hyx
      simp [strengthPiece, edgeGraph, hxy, hyx]

/-- A single normalized occurrence contributes at most one to any cut. -/
theorem strengthPiece_edgeGraph_cut_le_one (G : WeightedGraph V) (U S : Finset V)
    (e : EdgeIndex V) (a : ℝ) (ha : 0 ≤ a) (c : ℝ) (hc : 0 ≤ c)
    (hbound : c * a ≤ G.strength e.val.1 e.val.2) :
    ((G.strengthPiece (edgeGraph e a ha) U).scale c hc).cut S ≤ 1 := by
  rw [strengthPiece_edgeGraph, edgeGraph_scale]
  apply (cut_edgeGraph_le _ _ _ _).trans
  split_ifs with hm
  · rw [← mul_div_assoc]
    by_cases hz : G.strength e.val.1 e.val.2 = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne (G.strength_nonneg _ _) (Ne.symm hz))).mpr hbound
  · simp

namespace CountedBucket

/-- Smoothness of each draw copy, relative to the full reference graph. -/
def Admissible (b : CountedBucket V) (G : WeightedGraph V) (c : ℝ) : Prop :=
  ∀ e, 0 < b.weight e → c * (b.mass / b.count) ≤ G.strength e.val.1 e.val.2

/-- The usual sample-count condition supplies copywise smoothness. -/
theorem admissible_of_count (b : CountedBucket V) (G : WeightedGraph V) (c : ℝ)
    {β : ℝ} (hβ : 0 < β)
    (hstrength : ∀ e, 0 < b.weight e → β ≤ G.strength e.val.1 e.val.2)
    (hcount : c * b.mass / β ≤ b.count) : b.Admissible G c := by
  intro e he
  have hr : (0 : ℝ) < b.count := by exact_mod_cast b.count_pos
  have h := (div_le_iff₀ hβ).mp hcount
  apply le_trans _ (hstrength e he)
  rw [← mul_div_assoc, div_le_iff₀ hr]
  nlinarith

/-- All component shores get explicit independent bounded-draw representations. -/
theorem sampleLaw_boundedCutLaw (bs : List (CountedBucket V)) (G : WeightedGraph V)
    (c : ℝ) (hc : 0 ≤ c) (hb : ∀ b ∈ bs, b.Admissible G c) (U S : Finset V) :
    HasBoundedCutLaw (G.strengthPieceLaw (sampleLaw bs) U c hc) S := by
  let f := fun X : WeightedGraph V => ((G.strengthPiece X U).scale c hc).cut S
  have hzero : f 0 = 0 := by simp [f, cut_scale]
  have hadd (X Y : WeightedGraph V) : f (X + Y) = f X + f Y := by
    simp only [f, strengthPiece_add, cut_scale, cut_addition, mul_add]
  obtain ⟨ds, hds⟩ := independentGraphSum_boundedLaw ((expanded bs).map drawLaw) f hzero hadd
    (by
      intro p hp X hX
      obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hp
      obtain ⟨e, he, rfl⟩ := (b.mem_support_drawLaw X).mp hX
      exact ⟨cut_nonneg _ _, G.strengthPiece_edgeGraph_cut_le_one U S e _ _ c hc
        (hb b (mem_of_mem_expanded hb') e he)⟩)
  refine ⟨ds, ?_⟩
  simpa only [strengthPieceLaw, PMF.map_comp, Function.comp_def, sampleLaw, f] using hds

/-- The stochastic law and its mean are now concrete; only the cut sum is unbounded. -/
theorem sampleLaw_failure_le_cut_sum (bs : List (CountedBucket V))
    {ε c : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c)
    (hb : ∀ b ∈ bs, b.Admissible (reference bs) c) :
    Probability.mass (sampleLaw bs) (fun X => ¬IsCutSparsifier ε (reference bs) X) ≤
      ∑ U ∈ (reference bs).strongComponents,
        (((reference bs).strengthPiece (reference bs) U).scale c hc.le).cutTailSum U ε := by
  apply (sampleLaw_mean bs).sparsifier_failure_le_strength_cut_sum hε hε1 hc
  intro U _ S _
  exact sampleLaw_boundedCutLaw bs (reference bs) c hc.le hb U S

theorem sampleLaw_success_of_cut_tail_bounds (bs : List (CountedBucket V))
    {ε c δ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hb : ∀ b ∈ bs, b.Admissible (reference bs) c)
    (hcount : ∀ U ∈ (reference bs).strongComponents,
      (((reference bs).strengthPiece (reference bs) U).scale c hc.le).cutTailSum U ε ≤
        ENNReal.ofReal δ) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤
      (Probability.mass (sampleLaw bs) (IsCutSparsifier ε (reference bs))).toReal := by
  exact (sampleLaw_mean bs).sparsifier_success_of_cut_tail_bounds hε hε1 hc hδ
    (fun U _ S _ => sampleLaw_boundedCutLaw bs (reference bs) c hc.le hb U S) hcount

end CountedBucket
end
end CutQueryComplexity.WeightedGraph
