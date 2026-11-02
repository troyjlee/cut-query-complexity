import CutQueryComplexity.Sparsification.ComponentNormalization

/-! # The deterministic BK strength decomposition

Fix a reference graph `G` (later the expected graph). Every graph `X` supported
on `G` is reconstructed using the same positive component coefficients.
Scaling pieces by `c > 0` gives reference minimum induced cut `c` and, under
the pointwise smoothness bound, edge weights at most one. Component cut
approximation transfers to all original cuts without accumulating error.

These are algebraic statements for every outcome. No independence or
concentration theorem is assumed here.
-/

namespace CutQueryComplexity
namespace WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Restrict `X` to a component and normalize by the fixed reference strengths. -/
def strengthPiece (G X : WeightedGraph V) (U : Finset V) : WeightedGraph V where
  w u v := if u ∈ U ∧ v ∈ U then X.w u v / G.strength u v else 0
  symm u v := by simp only [and_comm, X.symm u v, G.strength_symm u v]
  nonneg u v := by split <;> simp [div_nonneg (X.nonneg u v) (G.strength_nonneg u v)]
  diag v := by simp [X.diag]

theorem strengthPiece_self (G : WeightedGraph V) (U : Finset V) :
    G.strengthPiece G U = G.strengthNormalized.induce U := by
  ext u v
  rfl

/-- Exact reconstruction with coefficients independent of `X`. -/
theorem strengthDecomposition_weight (G X : WeightedGraph V)
    (hsupport : X.support ≤ G.support) (u v : V) :
    X.w u v = ∑ U ∈ G.strongComponents,
      G.componentCoefficient U * (G.strengthPiece X U).w u v := by
  by_cases hx : X.w u v = 0
  · simp [strengthPiece, hx]
  · have hg : G.w u v ≠ 0 := hsupport hx
    have hp := G.strength_pos_of_weight_pos (lt_of_le_of_ne (G.nonneg u v) (Ne.symm hg))
    calc
      _ = G.strength u v * (X.w u v / G.strength u v) := by
        rw [mul_div_cancel₀ _ (ne_of_gt hp)]
      _ = (∑ U ∈ G.strongComponents,
          if u ∈ U ∧ v ∈ U then G.componentCoefficient U else 0) *
            (X.w u v / G.strength u v) := by rw [G.sum_componentCoefficients_pair hp]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro U _
        by_cases h : u ∈ U ∧ v ∈ U <;> simp [strengthPiece, h]

/-- Passing any finite edgewise linear identity to cuts. -/
theorem cut_eq_sum_of_weights {ι : Type*} (X : WeightedGraph V) (I : Finset ι)
    (a : ι → ℝ) (F : ι → WeightedGraph V)
    (h : ∀ u v, X.w u v = ∑ i ∈ I, a i * (F i).w u v) (S : Finset V) :
    X.cut S = ∑ i ∈ I, a i * (F i).cut S := by
  calc
    _ = ∑ u ∈ S, ∑ v ∈ Sᶜ, ∑ i ∈ I, a i * (F i).w u v := by simp only [cut, h]
    _ = ∑ u ∈ S, ∑ i ∈ I, ∑ v ∈ Sᶜ, a i * (F i).w u v :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ I, ∑ u ∈ S, ∑ v ∈ Sᶜ, a i * (F i).w u v := Finset.sum_comm
    _ = _ := by simp only [cut, Finset.mul_sum]

theorem strengthDecomposition_cut (G X : WeightedGraph V)
    (hsupport : X.support ≤ G.support) (S : Finset V) :
    X.cut S = ∑ U ∈ G.strongComponents,
      G.componentCoefficient U * (G.strengthPiece X U).cut S :=
  X.cut_eq_sum_of_weights _ _ _ (G.strengthDecomposition_weight X hsupport) S

/-- The scaled version of BK Lemma 5.3's reconstruction identity. -/
theorem strengthDecomposition_scaled_weight (G X : WeightedGraph V)
    (hsupport : X.support ≤ G.support) {c : ℝ} (hc : 0 < c) (u v : V) :
    X.w u v = ∑ U ∈ G.strongComponents,
      (G.componentCoefficient U / c) * ((G.strengthPiece X U).scale c hc.le).w u v := by
  rw [G.strengthDecomposition_weight X hsupport]
  apply Finset.sum_congr rfl
  intro U _
  change _ = (G.componentCoefficient U / c) * (c * (G.strengthPiece X U).w u v)
  rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hc)]

theorem strengthDecomposition_scaled_cut (G X : WeightedGraph V)
    (hsupport : X.support ≤ G.support) {c : ℝ} (hc : 0 < c) (S : Finset V) :
    X.cut S = ∑ U ∈ G.strongComponents,
      (G.componentCoefficient U / c) * ((G.strengthPiece X U).scale c hc.le).cut S :=
  X.cut_eq_sum_of_weights _ _ _ (G.strengthDecomposition_scaled_weight X hsupport hc) S

theorem strengthDecomposition_scaled_coefficient_pos (G : WeightedGraph V)
    {U : Finset V} (hU : U ∈ G.strongComponents) {c : ℝ} (hc : 0 < c) :
    0 < G.componentCoefficient U / c := div_pos (G.componentCoefficient_pos hU) hc

/-- Each reference piece has minimum induced cut exactly `c` on its own vertices. -/
theorem strengthPiece_reference_mincut (G : WeightedGraph V) {U : Finset V}
    (hU : U ∈ G.strongComponents) (c : ℝ) (hc : 0 ≤ c) :
    ((G.strengthPiece G U).scale c hc).inducedMincut U = c := by
  rw [inducedMincut_scale, G.strengthPiece_self, inducedMincut_induce_self,
    G.normalized_component_mincut_eq_one hU, mul_one]

/-- Pointwise `c`-smoothness makes every scaled piece edge at most one. -/
theorem strengthPiece_scaled_weight_le_one (G X : WeightedGraph V) {c : ℝ} (hc : 0 ≤ c)
    (hsmooth : ∀ u v, c * X.w u v ≤ G.strength u v) (U : Finset V) (u v : V) :
    ((G.strengthPiece X U).scale c hc).w u v ≤ 1 := by
  change c * (if u ∈ U ∧ v ∈ U then X.w u v / G.strength u v else 0) ≤ 1
  by_cases hmem : u ∈ U ∧ v ∈ U
  · rw [ite_eq_left hmem, ← mul_div_assoc]
    by_cases hz : G.strength u v = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne (G.strength_nonneg u v) (Ne.symm hz))).mpr
        (hsmooth u v)
  · simp [hmem]

/-- A single family and coefficients work for every supported graph `X`.
This is the deterministic content of BK's decomposition lemma. -/
theorem exists_strengthDecomposition (G : WeightedGraph V) {c : ℝ} (hc : 0 < c) :
    ∃ (I : Finset (Finset V)) (a : Finset V → ℝ)
      (F : WeightedGraph V → Finset V → WeightedGraph V),
      I.card ≤ Fintype.card V - 1 ∧
      (∀ U ∈ I, 0 < a U ∧ (F G U).inducedMincut U = c) ∧
      (∀ X, X.support ≤ G.support → ∀ u v,
        X.w u v = ∑ U ∈ I, a U * (F X U).w u v) ∧
      (∀ X, (∀ u v, c * X.w u v ≤ G.strength u v) →
        ∀ U ∈ I, ∀ u v, (F X U).w u v ≤ 1) := by
  refine ⟨G.strongComponents, (fun U => G.componentCoefficient U / c),
    (fun X U => (G.strengthPiece X U).scale c hc.le),
    G.strongComponents_card_le, ?_, ?_, ?_⟩
  · intro U hU
    exact ⟨G.strengthDecomposition_scaled_coefficient_pos hU hc,
      G.strengthPiece_reference_mincut hU c hc.le⟩
  · intro X hX u v
    exact G.strengthDecomposition_scaled_weight X hX hc u v
  · intro X hX U _ u v
    exact G.strengthPiece_scaled_weight_le_one X hc.le hX U u v

/-- Simultaneous component cut approximation implies the same original cut error. -/
theorem isCutSparsifier_of_strengthPieces (G X : WeightedGraph V) (ε : ℝ)
    (hsupport : X.support ≤ G.support)
    (hpieces : ∀ U ∈ G.strongComponents, ∀ S : Finset V,
      (1 - ε) * (G.strengthPiece G U).cut S ≤ (G.strengthPiece X U).cut S ∧
        (G.strengthPiece X U).cut S ≤ (1 + ε) * (G.strengthPiece G U).cut S) :
    IsCutSparsifier ε G X := by
  refine ⟨hsupport, fun S => ⟨?_, ?_⟩⟩
  · calc
      _ = ∑ U ∈ G.strongComponents,
          G.componentCoefficient U * ((1 - ε) * (G.strengthPiece G U).cut S) := by
        rw [G.strengthDecomposition_cut G le_rfl, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U _
        ring
      _ ≤ ∑ U ∈ G.strongComponents,
          G.componentCoefficient U * (G.strengthPiece X U).cut S := by
        apply Finset.sum_le_sum
        intro U hU
        exact mul_le_mul_of_nonneg_left (hpieces U hU S).1 (G.componentCoefficient_nonneg U)
      _ = _ := (G.strengthDecomposition_cut X hsupport S).symm
  · calc
      _ = ∑ U ∈ G.strongComponents,
          G.componentCoefficient U * (G.strengthPiece X U).cut S :=
        G.strengthDecomposition_cut X hsupport S
      _ ≤ ∑ U ∈ G.strongComponents,
          G.componentCoefficient U * ((1 + ε) * (G.strengthPiece G U).cut S) := by
        apply Finset.sum_le_sum
        intro U hU
        exact mul_le_mul_of_nonneg_left (hpieces U hU S).2 (G.componentCoefficient_nonneg U)
      _ = _ := by
        rw [G.strengthDecomposition_cut G le_rfl, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U _
        ring

theorem isCutSparsifier_of_scaledStrengthPieces (G X : WeightedGraph V) (ε : ℝ)
    (hsupport : X.support ≤ G.support) {c : ℝ} (hc : 0 < c)
    (hpieces : ∀ U ∈ G.strongComponents, ∀ S : Finset V,
      (1 - ε) * ((G.strengthPiece G U).scale c hc.le).cut S ≤
        ((G.strengthPiece X U).scale c hc.le).cut S ∧
      ((G.strengthPiece X U).scale c hc.le).cut S ≤
        (1 + ε) * ((G.strengthPiece G U).scale c hc.le).cut S) :
    IsCutSparsifier ε G X := by
  apply G.isCutSparsifier_of_strengthPieces X ε hsupport
  intro U hU S
  have h := hpieces U hU S
  simp only [cut_scale] at h
  constructor
  · apply le_of_mul_le_mul_left (a := c) ?_ hc
    convert h.1 using 1 <;> ring
  · apply le_of_mul_le_mul_left (a := c) ?_ hc
    convert h.2 using 1 <;> ring

end
end WeightedGraph
end CutQueryComplexity
