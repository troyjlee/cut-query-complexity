import CutQueryComplexity.AllPairs.Padding
import CutQueryComplexity.AllPairs.Representation
import CutQueryComplexity.Model.Reduction

/-! # Deterministic one-query padding and restriction of exact answers -/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion

open AllPairs AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

theorem padded_substitute_eval {O : Type} {q : ℕ}
    (T : DTree (Finset (Padded V)) ℝ O q) (G : WeightedGraph V) :
    (T.substitute paddedQuery).eval G.cut = T.eval (paddedGraph G).cut := by
  simp only [DTree.eval_substitute, paddedQuery_eval]

def restrictAnswers (out : Answers (Padded V)) : Answers V := fun s t =>
  ⟨originalShore (out (.inl s) (.inl t)).shore, (out (.inl s) (.inl t)).value⟩

theorem restrictAnswers_correct (G : WeightedGraph V) {out : Answers (Padded V)}
    (hout : allPairsGood (paddedGraph G) out) : allPairsGood G (restrictAnswers out) := by
  intro s t hst
  have hst' : (Sum.inl s : Padded V) ≠ Sum.inl t := by simpa using hst
  obtain ⟨hcut, hvalue⟩ := hout (.inl s) (.inl t) hst'
  obtain ⟨hminimum, hequal⟩ := padded_minimum_extract G hcut
  exact ⟨hminimum, hvalue.trans hequal⟩

/-- The whole padded program is chosen before the original graph. -/
def unpadProgram {q : ℕ} (T : DTree (Finset (Padded V)) ℝ (Answers (Padded V)) q) :
    DTree (Finset V) ℝ (Answers V) q :=
  ((T.substitute paddedQuery).map restrictAnswers).cast (Nat.mul_one q)

theorem unpadProgram_correct {q : ℕ}
    (T : DTree (Finset (Padded V)) ℝ (Answers (Padded V)) q)
    (G : WeightedGraph V)
    (hT : allPairsGood (paddedGraph G) (T.eval (paddedGraph G).cut)) :
    allPairsGood G ((unpadProgram T).eval G.cut) := by
  simp only [unpadProgram, DTree.eval_cast, DTree.eval_map, padded_substitute_eval]
  exact restrictAnswers_correct G hT

theorem unpadProgram_cost {q : ℕ}
    (T : DTree (Finset (Padded V)) ℝ (Answers (Padded V)) q) (oracle : Finset V → ℝ) :
    (unpadProgram T).cost oracle ≤ q := DTree.cost_le _ _

end
end CutQueryComplexity.DeterministicAPMCExpansion

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.unpadProgram_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.unpadProgram_cost
