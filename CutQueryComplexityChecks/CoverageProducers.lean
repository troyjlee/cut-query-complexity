import CutQueryComplexity.Reconstruction.DirectedData
import CutQueryComplexity.Certificate.UnitAllPairs
import CutQueryComplexityChecks.AxiomAudit

/-! Independent public-data and unit-competitor contracts for coverage producers. -/
namespace CutQueryComplexityChecks.CoverageProducers
open CutQueryComplexity
open CutQueryComplexity.DirectedCertificate
open scoped Classical
noncomputable section

theorem public_directed_answers (V : Type) [Fintype V] [DecidableEq V] :
    ∃ decode : Reconstruction.DirectedData V → AllPairs.Answers V,
      decode = Reconstruction.DirectedData.allPairsAnswers ∧
      ∀ (D : Reconstruction.DirectedData V) (G : WeightedDiGraph V),
        D.sym = G.sym → D.imbalance = G.imbalance →
        ∀ s t, s ≠ t →
          s ∈ (decode D s t).shore ∧ t ∉ (decode D s t).shore ∧
          (decode D s t).value = G.out (decode D s t).shore ∧
          ∀ S, s ∈ S → t ∉ S → G.out (decode D s t).shore ≤ G.out S := by
  refine ⟨Reconstruction.DirectedData.allPairsAnswers, rfl, ?_⟩
  intro D G hs hb s t hst
  exact D.allPairsAnswers_correct G hs hb s t hst

theorem known_unit_graph_certificate (V : Type) [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G) :
    ∃ Q : Finset (Finset V), Q.card ≤ 3 * Fintype.card V ∧
      ∃ out : AllPairs.Answers V,
        ∀ H : WeightedGraph V, AllPairsAudit.Unweighted H →
          (∀ S ∈ Q, H.cut S = G.cut S) →
            H = G ∧ AllPairs.allPairsGood H out := by
  refine ⟨Certificate.UnitAllPairs.queries G,
    Certificate.UnitAllPairs.queries_card G,
    Certificate.UnitAllPairs.answers G, ?_⟩
  intro H hH h
  have he : H = G := Certificate.UnitAllPairs.eq_of_consistent hG hH h
  exact ⟨he, he.symm ▸ Certificate.UnitAllPairs.answers_correct G⟩

end
end CutQueryComplexityChecks.CoverageProducers

#audit_cut_axioms [CutQueryComplexity.Reconstruction.DirectedData,
  CutQueryComplexity.Certificate.UnitAllPairs] pins [
  CutQueryComplexity.Reconstruction.DirectedData.cut_correct,
  CutQueryComplexity.Reconstruction.DirectedData.terminalAnswer_correct,
  CutQueryComplexity.Reconstruction.DirectedData.allPairsAnswers_correct,
  CutQueryComplexity.Reconstruction.DirectedData.globalAnswer_correct,
  CutQueryComplexity.Certificate.UnitAllPairs.queries_card,
  CutQueryComplexity.Certificate.UnitAllPairs.eq_of_consistent,
  CutQueryComplexity.Certificate.UnitAllPairs.exists_unit_allPairs_certificate,
  CutQueryComplexity.Certificate.UnitAllPairs.transcript_certificate]
#audit_cut_decl CutQueryComplexityChecks.CoverageProducers.public_directed_answers
#audit_cut_decl CutQueryComplexityChecks.CoverageProducers.known_unit_graph_certificate
