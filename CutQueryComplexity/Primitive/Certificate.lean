import CutQueryComplexity.Graph.Integral
import CutQueryComplexity.Primitive.Forest

/-! # Residual-forest threshold certificates

The output is an integral capacity subgraph with at most `r*(n-1)` edge
copies. Both cut values are truncated at the threshold; a tree may have
more than one edge crossing a shore.
-/
namespace CutQueryComplexity
noncomputable section
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A threshold certificate, including the original-edge capacity constraint. -/
def IsThresholdCertificate (r : ℕ) (G H : WeightedGraph V) : Prop :=
  H.IsSubgraph G ∧ H.IsIntegral ∧
  H.edgeMass ≤ (r * (Fintype.card V - 1) : ℕ) ∧
  ∀ S, min (r : ℝ) (H.cut S) = min (r : ℝ) (G.cut S)

theorem IsThresholdCertificate.cut_eq_of_le {r : ℕ} {G H : WeightedGraph V}
    (h : IsThresholdCertificate r G H) {S : Finset V} (hS : G.cut S ≤ r) :
    H.cut S = G.cut S := by
  apply le_antisymm (h.1.cut_le S)
  rw [← min_eq_right hS, ← h.2.2.2 S]
  exact min_le_right _ _

/-- If the input mincut is below the threshold, its value is preserved exactly. -/
theorem IsThresholdCertificate.mincut_eq {r : ℕ} {G H : WeightedGraph V}
    (h : IsThresholdCertificate r G H) (hr : mincutValue G ≤ r) :
    mincutValue H = mincutValue G := by
  by_cases hs : (properShores V).Nonempty
  · obtain ⟨S, hS, heS⟩ := exists_isMinCut G hs
    obtain ⟨T, hT, heT⟩ := exists_isMinCut H hs
    apply le_antisymm
    · calc
        mincutValue H ≤ H.cut S := mincutValue_le H hS.1
        _ = G.cut S := h.cut_eq_of_le (by rwa [heS])
        _ = mincutValue G := heS
    · calc
        mincutValue G ≤ min (r : ℝ) (G.cut T) := le_min hr (mincutValue_le G hT.1)
        _ = min (r : ℝ) (H.cut T) := (h.2.2.2 T).symm
        _ ≤ H.cut T := min_le_right _ _
        _ = mincutValue H := heT
  · simp [mincutValue, hs]

def forestBudget (V : Type) [Fintype V] : ℕ :=
  12 * Fintype.card V * (searchDepth V + 1)

/-- Repeatedly remove one unit spanning forest; each residual cut costs one original cut. -/
def thresholdCertificate : (r : ℕ) →
    DTree (Finset V) ℝ (WeightedGraph V) (r * forestBudget V)
  | 0 => DTree.pure 0
  | r + 1 =>
      (spanningForest.bind fun F =>
        ((thresholdCertificate r).substitute (deletionQuery (SimpleGraph.toWeighted F))).map
          (fun H => (SimpleGraph.toWeighted F).add H)).cast
            (by unfold forestBudget; simp only [Nat.mul_one, Nat.succ_mul]; omega)

/-- Strong induction invariant: the output cut dominates the truncated input cut. -/
theorem thresholdCertificate_invariant (r : ℕ) (G : WeightedGraph V) (hG : G.IsIntegral) :
    let H := (thresholdCertificate r).eval G.cut
    H.IsSubgraph G ∧ H.IsIntegral ∧
    H.edgeMass ≤ (r * (Fintype.card V - 1) : ℕ) ∧
    ∀ S, min (r : ℝ) (G.cut S) ≤ H.cut S := by
  induction r generalizing G with
  | zero =>
      simp only [thresholdCertificate, DTree.eval_pure]
      refine ⟨G.nonneg, WeightedGraph.integral_zero, ?_, ?_⟩
      · simp
      · intro S; simp [G.cut_nonneg]
  | succ r ih =>
      let F := spanningForest.eval G.cut
      let K := SimpleGraph.toWeighted F
      have hF : IsSpanningForest G F := spanningForest_correct G
      have hK : K.IsSubgraph G := hF.toWeighted_subgraph hG
      have hKi : K.IsIntegral := integral_toWeighted F
      have hres := hG.subtract hKi hK
      obtain ⟨hH, hHi, hsize, hcuts⟩ := ih (G.subtract K) hres
      simp only [thresholdCertificate, DTree.eval_cast, DTree.eval_bind, DTree.eval_map,
        DTree.eval_substitute]
      have hcall : (fun j => (deletionQuery (SimpleGraph.toWeighted (spanningForest.eval G.cut)) j).eval
          G.cut) = (G.subtract K).cut := funext (deletionQuery_eval G K hK)
      rw [hcall]
      change (K.add ((thresholdCertificate r).eval (G.subtract K).cut)).IsSubgraph G ∧ _
      let H := (thresholdCertificate r).eval (G.subtract K).cut
      have hsub : (K.add H).IsSubgraph G := by
        intro u v
        have hh := hH u v
        change H.w u v ≤ max 0 (G.w u v - K.w u v) at hh
        rw [max_eq_right (sub_nonneg.mpr (hK u v))] at hh
        simp only [WeightedGraph.add_w]
        linarith
      refine ⟨hsub, hKi.add hHi, ?_, ?_⟩
      · rw [WeightedGraph.edgeMass_add]
        have hfsize : K.edgeMass ≤ (Fintype.card V - 1 : ℕ) := by
          rw [edgeMass_toWeighted]
          exact_mod_cast forest_card_le F hF.2.1
        push_cast at hsize ⊢
        nlinarith
      · intro S
        rw [WeightedGraph.cut_add]
        have hc := hcuts S
        rw [G.cut_subtract K hK] at hc
        have hle := hK.cut_le S
        by_cases hz : G.cut S = 0
        · rw [hz, min_eq_right (by positivity)]
          exact add_nonneg (K.cut_nonneg S) (H.cut_nonneg S)
        · have hpos : 0 < G.cut S := lt_of_le_of_ne (G.cut_nonneg S) (Ne.symm hz)
          have hunit : 1 ≤ K.cut S := hF.one_le_cut hpos
          by_cases hr : G.cut S - K.cut S ≤ (r : ℝ)
          · rw [min_eq_right hr] at hc
            exact (min_le_right _ _).trans (by linarith)
          · rw [min_eq_left (le_of_not_ge hr)] at hc
            have := min_le_left (↑(r + 1) : ℝ) (G.cut S)
            push_cast at this ⊢
            linarith

/-- One input-independent algorithm produces a sparse threshold-preserving certificate. -/
theorem thresholdCertificate_correct (r : ℕ) (G : WeightedGraph V) (hG : G.IsIntegral) :
    IsThresholdCertificate r G ((thresholdCertificate r).eval G.cut) := by
  obtain ⟨hsub, hint, hsize, hcut⟩ := thresholdCertificate_invariant r G hG
  refine ⟨hsub, hint, hsize, fun S => le_antisymm (min_le_min_left _ (hsub.cut_le S)) ?_⟩
  exact le_min (min_le_left _ _) (hcut S)

/-- Bounded natural capacities satisfy the promise, with no dependence on their magnitude. -/
theorem thresholdCertificate_capacity {W : ℕ} (r : ℕ) (G : CapacityGraph V W) :
    IsThresholdCertificate r G.toWeighted
      ((thresholdCertificate r).eval G.toWeighted.cut) :=
  thresholdCertificate_correct r G.toWeighted G.integral_toWeighted

end
end CutQueryComplexity
