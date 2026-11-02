import CutQueryComplexity.Primitive.Certificate

/-! # Capacity semantics for completed parallel residual forests

The order here is the residual order, not the order in which queries were
performed. The parallel algorithm may grow all forests at once. Its completed
forests satisfy `ResidualForestChain`, which is enough for the corrected
two-sided truncated-cut contract. All sums retain edge multiplicities.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- Sum of the actual unit forest capacities; repeated pairs add capacity. -/
def forestSum : List (_root_.SimpleGraph Q) → WeightedGraph Q
  | [] => 0
  | F :: Fs => (SimpleGraph.toWeighted F).add (forestSum Fs)

@[simp] theorem forestSum_nil : forestSum ([] : List (_root_.SimpleGraph Q)) = 0 := rfl

@[simp] theorem forestSum_cons (F : _root_.SimpleGraph Q)
    (Fs : List (_root_.SimpleGraph Q)) :
    forestSum (F :: Fs) = (SimpleGraph.toWeighted F).add (forestSum Fs) := rfl

/-- Each forest spans the support remaining after the preceding forests. -/
def ResidualForestChain (G : WeightedGraph Q) : List (_root_.SimpleGraph Q) → Prop
  | [] => True
  | F :: Fs => IsSpanningForest G F ∧
      ResidualForestChain (G.subtract (SimpleGraph.toWeighted F)) Fs

theorem forestSum_integral (Fs : List (_root_.SimpleGraph Q)) :
    (forestSum Fs).IsIntegral := by
  induction Fs with
  | nil => exact WeightedGraph.integral_zero
  | cons F Fs ih => exact (integral_toWeighted F).add ih

theorem forestSum_edgeMass (Fs : List (_root_.SimpleGraph Q)) :
    (forestSum Fs).edgeMass =
      ((Fs.map fun F => F.edgeFinset.card).sum : ℝ) := by
  induction Fs with
  | nil => simp
  | cons F Fs ih =>
      simp only [forestSum_cons, WeightedGraph.edgeMass_add, edgeMass_toWeighted,
        List.map_cons, List.sum_cons, Nat.cast_add, ih]

theorem forestSum_edgeMass_le (Fs : List (_root_.SimpleGraph Q))
    (hFs : ∀ F ∈ Fs, F.IsAcyclic) :
    (forestSum Fs).edgeMass ≤ (Fs.length * (Fintype.card Q - 1) : ℕ) := by
  induction Fs with
  | nil => simp
  | cons F Fs ih =>
      have hF : F.IsAcyclic := hFs F (by simp)
      have ht : ∀ H ∈ Fs, H.IsAcyclic := fun H hH => hFs H (by simp [hH])
      have hb : (SimpleGraph.toWeighted F).edgeMass ≤ (Fintype.card Q - 1 : ℕ) := by
        rw [edgeMass_toWeighted]
        exact_mod_cast forest_card_le F hF
      have hi := ih ht
      rw [forestSum_cons, WeightedGraph.edgeMass_add, List.length_cons,
        Nat.succ_mul, Nat.cast_add]
      linarith

theorem ResidualForestChain.acyclic {G : WeightedGraph Q}
    {Fs : List (_root_.SimpleGraph Q)} (hFs : ResidualForestChain G Fs) :
    ∀ F ∈ Fs, F.IsAcyclic := by
  induction Fs generalizing G with
  | nil => simp
  | cons F Fs ih =>
      rcases hFs with ⟨hF, ht⟩
      intro H hH
      rcases List.mem_cons.mp hH with rfl | hH
      · exact hF.2.1
      · exact ih ht H hH

/-- Residual forest union dominates the input cut truncated at its length.
This is the mathematical invariant discharged by a completed parallel state. -/
theorem residualForestChain_invariant (G : WeightedGraph Q) (hG : G.IsIntegral)
    (Fs : List (_root_.SimpleGraph Q)) (hFs : ResidualForestChain G Fs) :
    (forestSum Fs).IsSubgraph G ∧
      ∀ S, min (Fs.length : ℝ) (G.cut S) ≤ (forestSum Fs).cut S := by
  induction Fs generalizing G with
  | nil =>
      refine ⟨G.nonneg, ?_⟩
      intro S
      simp [G.cut_nonneg]
  | cons F Fs ih =>
      rcases hFs with ⟨hF, ht⟩
      let K := SimpleGraph.toWeighted F
      have hK : K.IsSubgraph G := hF.toWeighted_subgraph hG
      have hres : (G.subtract K).IsIntegral :=
        hG.subtract (integral_toWeighted F) hK
      obtain ⟨hH, hc⟩ := ih (G.subtract K) hres ht
      refine ⟨?_, ?_⟩
      · intro u v
        have hw := hH u v
        change (forestSum Fs).w u v ≤ max 0 (G.w u v - K.w u v) at hw
        rw [max_eq_right (sub_nonneg.mpr (hK u v))] at hw
        change K.w u v + (forestSum Fs).w u v ≤ G.w u v
        linarith
      · intro S
        change min ((Fs.length + 1 : ℕ) : ℝ) (G.cut S) ≤
          (K.add (forestSum Fs)).cut S
        rw [WeightedGraph.cut_add]
        have hcuts := hc S
        rw [G.cut_subtract K hK] at hcuts
        by_cases hz : G.cut S = 0
        · rw [hz, min_eq_right (by positivity)]
          exact add_nonneg (K.cut_nonneg S) ((forestSum Fs).cut_nonneg S)
        · have hp : 0 < G.cut S :=
            lt_of_le_of_ne (G.cut_nonneg S) (Ne.symm hz)
          have hunit : 1 ≤ K.cut S := hF.one_le_cut hp
          by_cases hr : G.cut S - K.cut S ≤ (Fs.length : ℝ)
          · rw [min_eq_right hr] at hcuts
            exact (min_le_right _ _).trans (by linarith)
          · rw [min_eq_left (le_of_not_ge hr)] at hcuts
            have hmin := min_le_left (((Fs.length + 1 : ℕ) : ℝ)) (G.cut S)
            push_cast at hmin ⊢
            linarith

/-- A completed residual-forest sequence is a genuine threshold certificate.
The premise names the actual individual spanning forests, not a cut-preservation
or cost assumption. No simple-quotient assumption is made. -/
theorem residualForestChain_certificate (G : WeightedGraph Q) (hG : G.IsIntegral)
    (Fs : List (_root_.SimpleGraph Q)) (hFs : ResidualForestChain G Fs) :
    IsThresholdCertificate Fs.length G (forestSum Fs) := by
  obtain ⟨hsub, hcuts⟩ := residualForestChain_invariant G hG Fs hFs
  refine ⟨hsub, forestSum_integral Fs,
    forestSum_edgeMass_le Fs hFs.acyclic, ?_⟩
  intro S
  apply le_antisymm (min_le_min_left _ (hsub.cut_le S))
  exact le_min (min_le_left _ _) (hcuts S)

/-- An empty residual suffix requires no queries or positive-capacity promise. -/
theorem empty_certificate (G : WeightedGraph Q) :
    IsThresholdCertificate 0 G 0 := by
  refine ⟨G.nonneg, WeightedGraph.integral_zero, ?_, ?_⟩
  · simp
  · intro S
    simp [G.cut_nonneg]

#print axioms forestSum_integral
#print axioms forestSum_edgeMass
#print axioms forestSum_edgeMass_le
#print axioms ResidualForestChain.acyclic
#print axioms residualForestChain_invariant
#print axioms residualForestChain_certificate
#print axioms empty_certificate

end
end CutQueryComplexity.StarContraction2022.Certificates
