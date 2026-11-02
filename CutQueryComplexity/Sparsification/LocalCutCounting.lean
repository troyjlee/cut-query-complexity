import CutQueryComplexity.Sparsification.CutCounting
import CutQueryComplexity.Graph.VertexRestriction
import CutQueryComplexity.Sparsification.ComponentConcentration

/-! # Cut counts inside a component

Restriction to the vertex subtype makes the counting dimension `|U|`, even
when the public graph type contains arbitrarily many isolated outside vertices.
The final bound applies to exactly the shore family in `cutTailSum`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

def localNearMinShores (G : WeightedGraph V) (U : Finset V) (κ : ℝ) (k : ℕ) :
    Finset (Finset V) := (localShores U).filter (fun S => G.localCut U S ≤ k * κ)

theorem localNearMinShores_card_le (G : WeightedGraph V) (U : Finset V) {κ : ℝ}
    (hκ : 0 < κ) (hmin : ∀ S, LocalShore U S → κ ≤ G.localCut U S)
    (k : ℕ) (hk : 1 ≤ k) :
    (G.localNearMinShores U κ k).card ≤ contractionCountBound U.card (2 * k) := by
  have hlocal {S : Finset V} (hS : S ∈ G.localNearMinShores U κ k) : LocalShore U S :=
    (mem_localShores _ _).mp (Finset.mem_filter.mp hS).1
  have hinj : Set.InjOn (projectShore U) (G.localNearMinShores U κ k) := by
    intro S hS T hT he
    change projectShore U S = projectShore U T at he
    rw [← lift_projectShore (hlocal hS).1, ← lift_projectShore (hlocal hT).1, he]
  have hsub : (G.localNearMinShores U κ k).image (projectShore U) ⊆
      (G.onVertices U).nearMinShores κ k := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    refine Finset.mem_filter.mpr ⟨(mem_properShores _).mpr (hlocal hS).project, ?_⟩
    rw [G.onVertices_cut_project]
    exact (Finset.mem_filter.mp hS).2
  calc
    _ = ((G.localNearMinShores U κ k).image (projectShore U)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((G.onVertices U).nearMinShores κ k).card := Finset.card_le_card hsub
    _ ≤ contractionCountBound (Fintype.card U) (2 * k) :=
      (G.onVertices U).nearMinShores_card_le hκ
        (fun T hT => by rw [G.onVertices_cut_lift]; exact hmin _ (localShore_lift hT)) k hk
    _ = _ := by simp

theorem localNearMinShores_card_le_pow (G : WeightedGraph V) (U : Finset V) {κ : ℝ}
    (hκ : 0 < κ) (hmin : ∀ S, LocalShore U S → κ ≤ G.localCut U S)
    (hn : 1 ≤ U.card) (k : ℕ) (hk : 1 ≤ k) :
    (G.localNearMinShores U κ k).card ≤ (2 * U.card) ^ (2 * k) :=
  (G.localNearMinShores_card_le U hκ hmin k hk).trans (contractionCountBound_le_pow hn (2 * k))

/-- Count the low-weight terms of the exponential cut sum, including complementary shores. -/
theorem positiveLocalShores_bounded_card (G : WeightedGraph V) (U : Finset V)
    (hG : G.induce U = G) (hκ : 0 < G.inducedMincut U) (k : ℕ) (hk : 1 ≤ k) :
    ((G.positiveLocalShores U).filter (fun S => G.cut S ≤ k * G.inducedMincut U)).card ≤
      (2 * U.card) ^ (2 * k) := by
  have hn : 1 ≤ U.card := by
    by_contra hn
    have hz := G.inducedMincut_eq_zero_of_card_le_one (U := U) (by omega)
    linarith
  apply le_trans _ (G.localNearMinShores_card_le_pow U hκ
    (fun S hS => G.inducedMincut_le hS) hn k hk)
  apply Finset.card_le_card
  intro S hS
  obtain ⟨hS, hc⟩ := Finset.mem_filter.mp hS
  refine Finset.mem_filter.mpr ⟨(mem_localShores _ _).mpr
    ((mem_positiveLocalShores _ _ _).mp hS).1, ?_⟩
  simpa only [localCut_eq_cut_induce, hG] using hc

/-- Each normalized BK piece has a polynomial shore count at every integer cut threshold. -/
theorem strengthPiece_bounded_shores_card (G : WeightedGraph V) {U : Finset V}
    (hU : U ∈ G.strongComponents) {c : ℝ} (hc : 0 < c) (k : ℕ) (hk : 1 ≤ k) :
    ((((G.strengthPiece G U).scale c hc.le).positiveLocalShores U).filter
      (fun S => ((G.strengthPiece G U).scale c hc.le).cut S ≤ k * c)).card ≤
        (2 * U.card) ^ (2 * k) := by
  have hm := G.strengthPiece_reference_mincut hU c hc.le
  have hp : 0 < ((G.strengthPiece G U).scale c hc.le).inducedMincut U := by
    rw [hm]
    exact hc
  simpa only [hm] using ((G.strengthPiece G U).scale c hc.le).positiveLocalShores_bounded_card U
    (G.scaled_strengthPiece_induce G U c hc.le) hp k hk

end
end CutQueryComplexity.WeightedGraph
