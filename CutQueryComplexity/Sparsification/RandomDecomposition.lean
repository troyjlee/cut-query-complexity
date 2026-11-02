import CutQueryComplexity.Graph.RandomMean
import CutQueryComplexity.Sparsification.StrengthDecomposition
import CutQueryComplexity.Probability.FiniteEvents

/-! # Random BK pieces and simultaneous failure accounting

Each piece is a pushforward of the same random graph. Its expected graph is
the corresponding reference piece, so the deterministic decomposition gives
BK's expected-mincut and bounded-weight guarantees. A union bound over at
most `n-1` pieces transfers their failure bounds without an independence
assumption between pieces. The concentration estimates for individual pieces
remain separate hypotheses.
-/

namespace CutQueryComplexity
namespace WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V] [DecidableEq V]

theorem HasMean.strengthPiece {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (R : WeightedGraph V) (U : Finset V) :
    HasMean (p.map (fun X => R.strengthPiece X U)) (R.strengthPiece G U) := by
  intro u v
  rw [expect_map]
  by_cases hm : u ∈ U ∧ v ∈ U
  · change expect p (fun X => ENNReal.ofReal
        (if u ∈ U ∧ v ∈ U then X.w u v / R.strength u v else 0)) = _
    simp only [ite_eq_left hm]
    change expect p (fun X => ENNReal.ofReal (X.w u v / R.strength u v)) =
      ENNReal.ofReal (if u ∈ U ∧ v ∈ U then G.w u v / R.strength u v else 0)
    rw [ite_eq_left hm]
    by_cases hz : R.strength u v = 0
    · simp [hz]
    · have hp := lt_of_le_of_ne (R.strength_nonneg u v) (Ne.symm hz)
      simp only [ENNReal.ofReal_div_of_pos hp]
      simp only [div_eq_mul_inv, expect_mul_const]
      rw [h u v]
  · change expect p (fun X => ENNReal.ofReal
        (if u ∈ U ∧ v ∈ U then X.w u v / R.strength u v else 0)) =
      ENNReal.ofReal (if u ∈ U ∧ v ∈ U then G.w u v / R.strength u v else 0)
    simp only [ite_eq_right hm, ENNReal.ofReal_zero, expect_const]

def strengthPieceLaw (G : WeightedGraph V) (p : PMF (WeightedGraph V))
    (U : Finset V) (c : ℝ) (hc : 0 ≤ c) : PMF (WeightedGraph V) :=
  p.map (fun X => (G.strengthPiece X U).scale c hc)

theorem HasMean.strengthPieceLaw {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (U : Finset V) (c : ℝ) (hc : 0 ≤ c) :
    HasMean (G.strengthPieceLaw p U c hc) ((G.strengthPiece G U).scale c hc) := by
  simpa only [WeightedGraph.strengthPieceLaw, PMF.map_comp, Function.comp_def] using
    (h.strengthPiece G U).scale c hc

/-- Entrywise smoothness of each supported outcome, relative to its mean.
For counted sampling, the analogous bound must be proved on draw copies before aggregation. -/
structure IsSmooth (p : PMF (WeightedGraph V)) (G : WeightedGraph V) (c : ℝ) : Prop where
  mean : HasMean p G
  bound : ∀ X ∈ p.support, ∀ u v, c * X.w u v ≤ G.strength u v

theorem IsSmooth.piece_bounded {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    {c : ℝ} (h : IsSmooth p G c) (hc : 0 ≤ c) (U : Finset V)
    {Y : WeightedGraph V} (hY : Y ∈ (G.strengthPieceLaw p U c hc).support) (u v : V) :
    Y.w u v ≤ 1 := by
  obtain ⟨X, hX, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hY
  exact G.strengthPiece_scaled_weight_le_one X hc (h.bound X hX) U u v

/-- The random form of BK Lemma 5.3, before applying concentration to the pieces. -/
theorem IsSmooth.exists_decomposition {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    {c : ℝ} (h : IsSmooth p G c) (hc : 0 < c) :
    ∃ (I : Finset (Finset V)) (a : Finset V → ℝ)
      (F : WeightedGraph V → Finset V → WeightedGraph V),
      I.card ≤ Fintype.card V - 1 ∧
      (∀ U ∈ I, 0 < a U ∧ HasMean (p.map (fun X => F X U)) (F G U) ∧
        (F G U).inducedMincut U = c ∧
        ∀ X ∈ p.support, ∀ u v, (F X U).w u v ≤ 1) ∧
      (∀ X ∈ p.support, ∀ u v, X.w u v = ∑ U ∈ I, a U * (F X U).w u v) := by
  refine ⟨G.strongComponents, (fun U => G.componentCoefficient U / c),
    (fun X U => (G.strengthPiece X U).scale c hc.le),
    G.strongComponents_card_le, ?_, ?_⟩
  · intro U hU
    refine ⟨G.strengthDecomposition_scaled_coefficient_pos hU hc,
      h.mean.strengthPieceLaw U c hc.le, G.strengthPiece_reference_mincut hU c hc.le, ?_⟩
    intro X hX u v
    exact G.strengthPiece_scaled_weight_le_one X hc.le (h.bound X hX) U u v
  · intro X hX u v
    exact G.strengthDecomposition_scaled_weight X (h.mean.support hX) hc u v

/-- The pieces are dependent pushforwards; their failure probabilities still add. -/
theorem HasMean.sparsifier_failure_le_sum {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (ε : ℝ) {c : ℝ} (hc : 0 < c) :
    mass p (fun X => ¬IsCutSparsifier ε G X) ≤
      ∑ U ∈ G.strongComponents, mass (G.strengthPieceLaw p U c hc.le)
        (fun Y => ¬IsCutSparsifier ε ((G.strengthPiece G U).scale c hc.le) Y) := by
  simp only [WeightedGraph.strengthPieceLaw, mass_map]
  apply mass_failure_le_sum
  intro X hX hpieces
  exact G.isCutSparsifier_of_scaledStrengthPieces X ε (h.support hX) hc
    (fun U hU S => (hpieces U hU).2 S)

theorem HasMean.sparsifier_failure_le_sum_bounds
    {p : PMF (WeightedGraph V)} {G : WeightedGraph V} (h : HasMean p G)
    (ε : ℝ) {c : ℝ} (hc : 0 < c) (δ : Finset V → ℝ≥0∞)
    (hpiece : ∀ U ∈ G.strongComponents, mass (G.strengthPieceLaw p U c hc.le)
      (fun Y => ¬IsCutSparsifier ε ((G.strengthPiece G U).scale c hc.le) Y) ≤ δ U) :
    mass p (fun X => ¬IsCutSparsifier ε G X) ≤ ∑ U ∈ G.strongComponents, δ U :=
  (h.sparsifier_failure_le_sum ε hc).trans (Finset.sum_le_sum hpiece)

theorem HasMean.sparsifier_failure_le {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (ε : ℝ) {c : ℝ} (hc : 0 < c) (δ : ℝ≥0∞)
    (hpiece : ∀ U ∈ G.strongComponents, mass (G.strengthPieceLaw p U c hc.le)
      (fun Y => ¬IsCutSparsifier ε ((G.strengthPiece G U).scale c hc.le) Y) ≤ δ) :
    mass p (fun X => ¬IsCutSparsifier ε G X) ≤ (Fintype.card V - 1 : ℕ) * δ := by
  have hsum := h.sparsifier_failure_le_sum_bounds ε hc (fun _ => δ) hpiece
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  apply hsum.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast G.strongComponents_card_le

theorem HasMean.sparsifier_success {p : PMF (WeightedGraph V)} {G : WeightedGraph V}
    (h : HasMean p G) (ε : ℝ) {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpiece : ∀ U ∈ G.strongComponents, mass (G.strengthPieceLaw p U c hc.le)
      (fun Y => ¬IsCutSparsifier ε ((G.strengthPiece G U).scale c hc.le) Y) ≤ ENNReal.ofReal δ) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤ (mass p (IsCutSparsifier ε G)).toReal := by
  apply success_of_failure_le p _ (mul_nonneg (Nat.cast_nonneg _) hδ)
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using
    h.sparsifier_failure_le ε hc (ENNReal.ofReal δ) hpiece

end
end WeightedGraph

namespace RTree
noncomputable section
open scoped Classical
open Probability
variable {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}

/-- A fixed cut-query program inherits the component bounds without changing its query budget. -/
theorem sparsifier_solves_of_piece_bounds (T : RTree (Finset V) ℝ (WeightedGraph V) q)
    (ε : ℝ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hmean : ∀ G : WeightedGraph V, WeightedGraph.HasMean (T.eval G.cut) G)
    (hpiece : ∀ (G : WeightedGraph V) U, U ∈ G.strongComponents →
      mass (G.strengthPieceLaw (T.eval G.cut) U c hc.le)
        (fun Y => ¬IsCutSparsifier ε ((G.strengthPiece G U).scale c hc.le) Y) ≤
          ENNReal.ofReal δ) :
    T.SolvesWithError WeightedGraph.cut (IsCutSparsifier ε) ((Fintype.card V - 1 : ℕ) * δ) := by
  intro G
  rw [successProb_eq]
  exact (hmean G).sparsifier_success ε hc hδ (hpiece G)

end
end RTree
end CutQueryComplexity
