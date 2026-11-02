import CutQueryComplexity.Graph.RandomMean
import CutQueryComplexity.Graph.InducedCut
import CutQueryComplexity.Probability.Chernoff

/-! # Concentration of cuts represented by bounded draws

Independence is specified by equality with a sum of bounded-draw laws for
each cut. Different cuts, edges, and components need not be independent.
The mean identity determines the sum's mean automatically. A finite union
bound uses only positive proper shores inside the graph's supporting vertex
set, so isolated outside vertices do not create duplicate events.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A per-cut distributional witness, with independence inside the sum law. -/
def HasBoundedCutLaw (p : PMF (WeightedGraph V)) (S : Finset V) : Prop :=
  ∃ ds : List BoundedDraw, p.map (fun X => X.cut S) = BoundedDraw.sumLaw ds

theorem HasMean.cut_zero {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) {X : WeightedGraph V} (hX : X ∈ p.support)
    {S : Finset V} (hz : G.cut S = 0) : X.cut S = 0 := by
  have he : expect p (fun Y => ENNReal.ofReal (Y.cut S)) = 0 := by
    rw [h.cut S, hz, ENNReal.ofReal_zero]
  have hx := (expect_eq_zero_iff p _).mp he X hX
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (X.cut_nonneg S)

theorem HasMean.boundedCut_mean {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (S : Finset V) (ds : List BoundedDraw)
    (hlaw : p.map (fun X => X.cut S) = BoundedDraw.sumLaw ds) :
    BoundedDraw.sumMean ds = G.cut S := by
  have he : ENNReal.ofReal (BoundedDraw.sumMean ds) = ENNReal.ofReal (G.cut S) := by
    rw [← BoundedDraw.expect_sumLaw_eq, ← hlaw, expect_map]
    exact h.cut S
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (BoundedDraw.sumMean_nonneg ds),
    ENNReal.toReal_ofReal (G.cut_nonneg S)] using hr

theorem HasMean.cut_concentration {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (S : Finset V) (hd : HasBoundedCutLaw p S)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mass p (fun X => ¬((1 - ε) * G.cut S ≤ X.cut S ∧ X.cut S ≤ (1 + ε) * G.cut S)) ≤
      2 * ENNReal.ofReal (Real.exp (-(ε ^ 2 * G.cut S / 4))) := by
  obtain ⟨ds, hlaw⟩ := hd
  have hm := h.boundedCut_mean S ds hlaw
  have hb := BoundedDraw.sum_two_sided ds hε hε1
  rw [hm, ← hlaw, mass_map] at hb
  exact hb

theorem induce_eq_self_of_support {G X : WeightedGraph V} {U : Finset V}
    (hG : G.induce U = G) (hX : X.support ≤ G.support) : X.induce U = X := by
  ext u v
  by_cases hm : u ∈ U ∧ v ∈ U
  · simp only [induce, ite_eq_left hm]
  · have hg : G.w u v = 0 := by
      have he := congrArg (fun H : WeightedGraph V => H.w u v) hG
      simpa only [induce, ite_eq_right hm] using he.symm
    have hx : X.w u v = 0 := by
      by_contra hn
      exact hX hn hg
    simp only [induce, ite_eq_right hm, hx]

theorem cut_eq_inter_of_induce_eq (G : WeightedGraph V) {U : Finset V}
    (hG : G.induce U = G) (S : Finset V) : G.cut S = G.cut (S ∩ U) := by
  calc
    _ = G.localCut U S := by rw [localCut_eq_cut_induce, hG]
    _ = G.localCut U (S ∩ U) := (G.localCut_inter U S).symm
    _ = _ := by rw [localCut_eq_cut_induce, hG]

theorem cut_zero_of_not_localShore (G : WeightedGraph V) {U S : Finset V}
    (hG : G.induce U = G) (hS : S ⊆ U) (hs : ¬LocalShore U S) : G.cut S = 0 := by
  have he : G.cut S = G.cross S (U \ S) := by
    rw [← G.localCut_of_subset hS, localCut_eq_cut_induce, hG]
  rw [he]
  by_cases hn : S.Nonempty
  · have hz : U \ S = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hs ⟨hS, hn, h⟩)
    simp [hz]
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hz]

/-- Positive proper shores, before applying a cut-counting estimate. -/
def positiveLocalShores (G : WeightedGraph V) (U : Finset V) : Finset (Finset V) :=
  (localShores U).filter (fun S => 0 < G.cut S)

@[simp] theorem mem_positiveLocalShores (G : WeightedGraph V) (U S : Finset V) :
    S ∈ G.positiveLocalShores U ↔ LocalShore U S ∧ 0 < G.cut S := by
  simp [positiveLocalShores]

def cutTailSum (G : WeightedGraph V) (U : Finset V) (ε : ℝ) : ℝ≥0∞ :=
  ∑ S ∈ G.positiveLocalShores U, 2 * ENNReal.ofReal (Real.exp (-(ε ^ 2 * G.cut S / 4)))

/-- The remaining all-cuts task is a deterministic bound on this finite exponential sum. -/
theorem HasMean.sparsifier_failure_le_local_cut_sum
    {p : PMF (WeightedGraph V)} {G : WeightedGraph V} (h : HasMean p G)
    (U : Finset V) (hG : G.induce U = G) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hd : ∀ S ∈ G.positiveLocalShores U, HasBoundedCutLaw p S) :
    mass p (fun X => ¬IsCutSparsifier ε G X) ≤ G.cutTailSum U ε := by
  unfold cutTailSum
  apply mass_failure_le_sum_bounds p (G.positiveLocalShores U)
    (fun S X => (1 - ε) * G.cut S ≤ X.cut S ∧ X.cut S ≤ (1 + ε) * G.cut S)
    (IsCutSparsifier ε G)
  · intro X hX hcuts
    refine ⟨h.support hX, fun S => ?_⟩
    have hx := induce_eq_self_of_support hG (h.support hX)
    rw [G.cut_eq_inter_of_induce_eq hG S, X.cut_eq_inter_of_induce_eq hx S]
    by_cases hp : 0 < G.cut (S ∩ U)
    · have hs : LocalShore U (S ∩ U) := by
        by_contra hn
        have hz := G.cut_zero_of_not_localShore hG Finset.inter_subset_right hn
        linarith
      exact hcuts _ ((G.mem_positiveLocalShores _ _).mpr ⟨hs, hp⟩)
    · have hz := le_antisymm (le_of_not_gt hp) (G.cut_nonneg (S ∩ U))
      have hzX := h.cut_zero hX hz
      simp [hz, hzX]
  · intro S hS
    exact h.cut_concentration S (hd S hS) hε hε1

end
end CutQueryComplexity.WeightedGraph
