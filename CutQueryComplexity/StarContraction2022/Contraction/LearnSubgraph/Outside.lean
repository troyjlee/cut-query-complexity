import CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph
import CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.RecoveryMoments

/-!
# Outside

Recovery of the neighbors outside the sampled centers, with the every-oracle
cap of the outside-recovery program.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph

open Finset WeightedGraph
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

/-- Eligible outside vertices, computed from the public measured center and
bad sets. Centers remain all the possible target columns. -/
def outsideSources (R B : Finset V) : Finset V := univ \ (R ∪ B)

theorem outside_sources_disjoint (R B : Finset V) : Disjoint (outsideSources R B) R := by
  apply disjoint_left.mpr
  intro v hv hR
  exact (mem_sdiff.mp hv).2 (mem_union_left B hR)

theorem outside_source_target_card (R B : Finset V) :
    Fintype.card (outsideSources R B) + Fintype.card R ≤ Fintype.card V := by
  simpa only [Fintype.card_coe, card_union_of_disjoint (outside_sources_disjoint R B)] using
    card_le_univ (outsideSources R B ∪ R)

def outsideRecoveryProgram (R B : Finset V) :
    RTree (Finset V) ℝ (Option (Recovery.BucketState (outsideSources R B) R))
      (Recovery.recoveryHardCoefficient * 5000 * Fintype.card V) :=
  (Recovery.recoverTree (Function.Embedding.subtype (· ∈ outsideSources R B))
    (Function.Embedding.subtype (· ∈ R)) 5000).weaken
      (Nat.mul_le_mul_left _ (outside_source_target_card R B))

theorem outsideRecoveryProgram_eval (R B : Finset V) (read : Finset V → ℝ) :
    (outsideRecoveryProgram R B).eval read =
      (Recovery.recoverTree (Function.Embedding.subtype (· ∈ outsideSources R B))
        (Function.Embedding.subtype (· ∈ R)) 5000).eval read :=
  RTree.eval_weaken _ _ _

theorem outsideRecoveryProgram_every_oracle (R B : Finset V) (read : Finset V → ℝ)
    {out : Option (Recovery.BucketState (outsideSources R B) R) × ℕ}
    (hout : out ∈ (RTree.run read (outsideRecoveryProgram R B)).support) :
    out.2 ≤ Recovery.recoveryHardCoefficient * 5000 * Fintype.card V :=
  RTree.cost_le _ _ hout

/-- The true outside neighbor table is analysis-only. -/
def outsideNeighbors (G : SimpleInput V) (R B : Finset V) (u : outsideSources R B) : Finset R :=
  Recovery.rowNeighbors (Recovery.graphMatrix (Function.Embedding.subtype (· ∈ outsideSources R B))
    (Function.Embedding.subtype (· ∈ R)) G u)

theorem outsideNeighbors_map (G : SimpleInput V) (R B : Finset V) (u : outsideSources R B) :
    (outsideNeighbors G R B u).map (Function.Embedding.subtype (· ∈ R)) =
      SparseCenters.inputRows G u.val ∩ R := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
    have hg : (G.w u.val w.val : ℕ) = 1 := by
      have hrow : Recovery.graphMatrix
          (Function.Embedding.subtype (· ∈ outsideSources R B))
          (Function.Embedding.subtype (· ∈ R)) G u w = true :=
        (Finset.mem_filter.mp hw).2
      dsimp only [Recovery.graphMatrix, Function.Embedding.subtype_apply] at hrow
      exact @of_decide_eq_true _ _ hrow
    refine mem_inter.mpr ⟨?_,w.property⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change (0 : ℝ) < ((G.w u.val w.val : ℕ) : ℝ)
    rw [hg]
    norm_num
  · intro hv
    rcases mem_inter.mp hv with ⟨hn,hr⟩
    have hp : (0 : ℝ) < G.toWeighted.w u.val v := (mem_filter.mp hn).2
    change (0 : ℝ) < ((G.w u.val v : ℕ) : ℝ) at hp
    have hpN : 0 < (G.w u.val v : ℕ) := by exact_mod_cast hp
    have hb := (G.w u.val v).isLt
    have hg : (G.w u.val v : ℕ) = 1 := by omega
    apply mem_map.mpr
    refine ⟨⟨v,hr⟩,?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    dsimp only [Recovery.graphMatrix, Function.Embedding.subtype_apply]
    exact @decide_eq_true _ _ hg

theorem outside_fullDegrees (G : SimpleInput V) (R B : Finset V) (u : outsideSources R B) :
    Recovery.fullDegrees (Recovery.graphMatrix (Function.Embedding.subtype (· ∈ outsideSources R B))
      (Function.Embedding.subtype (· ∈ R)) G) u = (SparseCenters.inputRows G u.val ∩ R).card := by
  rw [Recovery.fullDegrees,Recovery.sampleCount_eq_restriction,univ_inter]
  simpa only [outsideNeighbors, card_map] using
    congrArg Finset.card (outsideNeighbors_map G R B u)

def outsideCrossing (G : SimpleInput V) (S R B : Finset V) (u : outsideSources R B) : Finset R :=
  (outsideNeighbors G R B u).filter fun v => v.val ∈ crossingSet S u.val

theorem outside_baseRatio (G : SimpleInput V) (S R B : Finset V) (u : outsideSources R B) :
    ((outsideCrossing G S R B u).card : ℝ) / (outsideNeighbors G R B u).card =
      rowFraction (fun v => SparseCenters.inputRows G v ∩ R) S u.val := by
  unfold rowFraction Probability.crossingRatio
  apply congrArg₂ (fun a b : ℕ => (a : ℝ) / (b : ℝ))
  · apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      have hv' : v ∈ outsideNeighbors G R B u ∧ v.val ∈ crossingSet S u.val := by
        simpa only [outsideCrossing, mem_filter] using hv
      have hn : v.val ∈ SparseCenters.inputRows G u.val ∩ R := by
        rw [← outsideNeighbors_map G R B u]
        exact mem_map.mpr ⟨v, hv'.1, rfl⟩
      simp only [mem_inter] at hn ⊢
      exact ⟨hv'.2, hn⟩
    · intro v _ w _ he
      exact Subtype.ext he
    · intro v hv
      have hv' : v ∈ crossingSet S u.val ∧
          v ∈ SparseCenters.inputRows G u.val ∧ v ∈ R := by
        simpa only [mem_inter] using hv
      have hn : v ∈ (outsideNeighbors G R B u).map
          (Function.Embedding.subtype (· ∈ R)) := by
        rw [outsideNeighbors_map G R B u]
        simpa only [mem_inter] using hv'.2
      obtain ⟨w, hw, he⟩ := mem_map.mp hn
      change w.val = v at he
      refine ⟨w, ?_, he⟩
      simp only [outsideCrossing, mem_filter]
      exact ⟨hw, he.symm ▸ hv'.1⟩
  · simpa only [card_map] using
      congrArg Finset.card (outsideNeighbors_map G R B u)

theorem outside_base_good (G : SimpleInput V) (S R B : Finset V) (d : ℕ)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) :
    (∀ u : outsideSources R B, ((outsideCrossing G S R B u).card : ℝ) /
      (outsideNeighbors G R B u).card ≤ 3 / 5) ∧
    (∑ u : outsideSources R B, ((outsideCrossing G S R B u).card : ℝ) /
      (outsideNeighbors G R B u).card) ≤ 8 := by
  have hg := center_goodRows G S R d hgood
  constructor
  · intro u
    rw [outside_baseRatio]
    exact hg.1 u.val
  · simp_rw [outside_baseRatio]
    rw [sum_coe_sort (outsideSources R B)
      (fun v => rowFraction (fun w => SparseCenters.inputRows G w ∩ R) S v)]
    apply le_trans _ hg.2
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun v _ _ => rowFraction_nonneg _ _ v)

theorem outside_degree_5000 (G : SimpleInput V) (R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d)
    (u : outsideSources R (SparseCenters.badRows (SparseCenters.inputRows G) d R)) :
    5000 ≤ Recovery.fullDegrees
      (Recovery.graphMatrix (Function.Embedding.subtype
        (· ∈ outsideSources R (SparseCenters.badRows (SparseCenters.inputRows G) d R)))
        (Function.Embedding.subtype (· ∈ R)) G) u := by
  rw [outside_fullDegrees]
  have hu : u.val ∉ SparseCenters.badRows (SparseCenters.inputRows G) d R :=
    fun hu => (mem_sdiff.mp u.property).2 (mem_union_right R hu)
  have hsmall : ¬ ((SparseCenters.inputRows G u.val ∩ R).card : ℝ) ≤ 50000 * Real.log d :=
    fun he => hu (mem_filter.mpr ⟨mem_univ _,he⟩)
  have ht := Schedule.log_degree_ge d hd
  have hc : (5000 : ℝ) ≤ (SparseCenters.inputRows G u.val ∩ R).card := by
    linarith [lt_of_not_ge hsmall]
  exact_mod_cast hc

/-- Concrete outside recovery after a fixed shared good-center transcript.
All degree and ratio premises of the generic capped call are discharged. -/
theorem outsideRecoveryProgram_center_success (G : SimpleInput V) (S R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) :
    let B := SparseCenters.badRows (SparseCenters.inputRows G) d R
    (1 / 2 : ℝ≥0∞) ≤ mass ((outsideRecoveryProgram R B).eval G.toWeighted.cut) (fun out =>
      ∃ st : Recovery.BucketState (outsideSources R B) R, out = some st ∧
        (∀ u, ∃ N, st.learned u = some N ∧ 5000 ≤ N.card ∧
          ∀ v ∈ N, (G.w u.val v.val : ℕ) = 1) ∧
        (∀ u, recoveredRatio u (outsideCrossing G S R B u) (some st) ≤ 7 / 10) ∧
        (∑ u, recoveredRatio u (outsideCrossing G S R B u) (some st)) ≤ 80) := by
  intro B
  rw [outsideRecoveryProgram_eval]
  apply recoverTree_outside_success_half _ _ _ G (outside_degree_5000 G R d hd)
    (outsideCrossing G S R B) (fun u => filter_subset _ _)
    (outside_base_good G S R B d hgood).1 (outside_base_good G S R B d hgood).2
  intro u v he
  have huv : u.val = v.val := by
    simpa only [Function.Embedding.subtype_apply] using he
  exact disjoint_left.mp (outside_sources_disjoint R B) u.property (huv.symm ▸ v.property)

/- Exact marginal identities for the actual two independent recovery calls.
They make no assertion that rows within either recovery are independent. -/

#print axioms outside_source_target_card
#print axioms outsideRecoveryProgram_eval
#print axioms outsideRecoveryProgram_every_oracle
#print axioms outsideNeighbors_map
#print axioms outside_fullDegrees
#print axioms outside_baseRatio
#print axioms outside_base_good
#print axioms outside_degree_5000
#print axioms outsideRecoveryProgram_center_success

end
end CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph
