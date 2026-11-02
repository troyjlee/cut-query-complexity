import CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.Recovery

/-!
# Centers

Learning the rows of the sampled centers, with the every-oracle cap and the
success probability of the center-learning program.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph

open Finset WeightedGraph
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

/-! The public center-learning adapter reuses the measured counts. Its
correctness discharges all row and deficiency premises from the actual shared
center event; the trace is arbitrary and is not assumed to be induced-minimum. -/

theorem originalRowsOn_centers (G : SimpleInput V) (R : Finset V) :
    originalRowsOn (Function.Embedding.subtype (· ∈ R)) G =
      onRows R (SparseCenters.inputRows G) := by
  funext u
  ext v
  simp only [mem_originalRowsOn, onRows, mem_subtype, SparseCenters.inputRows,
    AllPairs.rowSupport, mem_filter, mem_univ, true_and]
  change (G.w u.val v.val : ℕ) = 1 ↔ (0 : ℝ) < ((G.w u.val v.val : ℕ) : ℝ)
  have hb := (G.w u.val v.val).isLt
  constructor
  · intro he
    rw [he]
    norm_num
  · intro hp
    have hn : 0 < (G.w u.val v.val : ℕ) := by exact_mod_cast hp
    omega

def measuredCenterDegrees (R : Finset V) (answers : V → ℝ) : R → ℕ :=
  fun u => Nat.floor (answers u.val)

theorem measuredCenterDegrees_eval (G : SimpleInput V) (R : Finset V) :
    measuredCenterDegrees R ((centerStatistics R).eval G.toWeighted.cut) =
      fun u => (originalRowsOn (Function.Embedding.subtype (· ∈ R)) G u).card := by
  rw [originalRowsOn_centers]
  funext u
  simp only [measuredCenterDegrees, SparseCenters.centerStatistics_input_eval,
    Nat.floor_natCast, onRows_card]

def centerLearnProgram (R : Finset V) (d : ℕ) (answers : V → ℝ) :
    RTree (Finset V) ℝ (Option (LearnedTranscript R))
      (learnSubgraphBudget R (Schedule.height d)) :=
  learnSubgraphProgram (Function.Embedding.subtype (· ∈ R))
    (measuredCenterDegrees R answers) (Schedule.height d)

theorem centerLearnProgram_every_oracle (R : Finset V) (d : ℕ) (answers : V → ℝ)
    (read : Finset V → ℝ) {out : Option (LearnedTranscript R) × ℕ}
    (hout : out ∈ (RTree.run read (centerLearnProgram R d answers)).support) :
    out.2 ≤ 3 * R.card + 2 * Recovery.recoveryHardCoefficient * Schedule.height d * R.card := by
  simpa only [learnSubgraphBudget, Fintype.card_coe] using
    (RTree.cost_le (centerLearnProgram R d answers) read hout)

theorem centerLearnProgram_success_half (G : SimpleInput V) (S R : Finset V) (d : ℕ)
    (hd : Schedule.degreeCutoff ≤ d)
    (hgood : SparseCenters.GoodCenters (SparseCenters.inputRows G)
      (SparseCenters.inputCrossRows G S) d R) :
    (1 / 2 : ℝ) ≤
      (mass ((centerLearnProgram R d ((centerStatistics R).eval G.toWeighted.cut)).eval G.toWeighted.cut)
        (LearnedResult (Function.Embedding.subtype (· ∈ R)) G (S.subtype (· ∈ R))
          (Schedule.height d) (SparseCenters.badRows (SparseCenters.inputRows G) d R ∩ R).card
          (4 / 5) 800)).toReal := by
  have hh := Schedule.height_ge d hd
  have hlow : (lowSources (originalRowsOn (Function.Embedding.subtype (· ∈ R)) G)
      (Schedule.height d)).card ≤
      (SparseCenters.badRows (SparseCenters.inputRows G) d R ∩ R).card := by
    rw [originalRowsOn_centers]
    exact center_subtype_lowSources_card_le G R d hd
  have hg : GoodRows (3 / 5) 8
      (originalRowsOn (Function.Embedding.subtype (· ∈ R)) G) (S.subtype (· ∈ R)) := by
    rw [originalRowsOn_centers]
    exact center_subtype_goodRows G S R d hgood
  have hheight : 10000 * (8 : ℝ) ≤ Schedule.height d := by
    exact_mod_cast (show 10000 * 8 ≤ Schedule.height d by omega)
  have hs := learnSubgraphProgram_success_half (Function.Embedding.subtype (· ∈ R)) G
    (S.subtype (· ∈ R)) (measuredCenterDegrees R ((centerStatistics R).eval G.toWeighted.cut))
    (Schedule.height d) (SparseCenters.badRows (SparseCenters.inputRows G) d R ∩ R).card
    (by omega) (measuredCenterDegrees_eval G R) hlow (by norm_num : (0 : ℝ) ≤ 3 / 5)
    (by norm_num : (0 : ℝ) < 8) hg hheight
  norm_num [centerLearnProgram] at hs ⊢
  exact hs


#print axioms originalRowsOn_centers
#print axioms measuredCenterDegrees_eval
#print axioms centerLearnProgram_every_oracle
#print axioms centerLearnProgram_success_half

end
end CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph
