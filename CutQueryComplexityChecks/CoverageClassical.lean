import CutQueryComplexity.Coverage.Classical
import CutQueryComplexityChecks.AxiomAudit

namespace CutQueryComplexityChecks.CoverageClassical
open CutQueryComplexity CutQueryComplexity.DirectedCertificate
open CutQueryComplexity.Reconstruction
open CutQueryComplexity.Probability
open scoped Classical
noncomputable section

/-- A named program fixed before every real-weight directed graph returns all
original optimum shores and values, using exactly its fixed quadratic schedule. -/
theorem real_directed_public_all_pairs (n : ℕ) :
    ∃ P : DTree (Finset (Fin n)) ℝ (AllPairs.Answers (Fin n))
        (WeightedDirected.queryBudget (Fin n)),
      P = WeightedDirected.allPairsProgram ∧
      WeightedDirected.queryBudget (Fin n) = n ^ 2 + 2 * n ∧
      (∀ read, P.cost read ≤ 3 * n ^ 2) ∧
      ∀ G : WeightedDiGraph (Fin n), ∀ s t, s ≠ t →
        s ∈ (P.eval G.out s t).shore ∧ t ∉ (P.eval G.out s t).shore ∧
        (P.eval G.out s t).value = G.out (P.eval G.out s t).shore ∧
        ∀ S, s ∈ S → t ∉ S → G.out (P.eval G.out s t).shore ≤ G.out S := by
  obtain ⟨P, he, hc, hg⟩ := WeightedDirected.deterministic_allPairs (V := Fin n)
  refine ⟨P, he, ?_, ?_, hg⟩
  · simpa using WeightedDirected.queryBudget_eq (V := Fin n)
  · simpa using hc

/-- A named program fixed before every real-weight undirected graph returns all
original optimum shores and values from its public singleton-and-pair schedule. -/
theorem real_undirected_public_all_pairs (n : ℕ) :
    ∃ P : DTree (Finset (Fin n)) ℝ (AllPairs.Answers (Fin n))
        (WeightedUndirected.queryBudget (Fin n)),
      P = WeightedUndirected.allPairsProgram ∧
      WeightedUndirected.queryBudget (Fin n) = n + n.choose 2 ∧
      (∀ read, P.cost read ≤ n ^ 2) ∧
      ∀ G : WeightedGraph (Fin n), ∀ s t, s ≠ t →
        IsSTMinCut G s t (P.eval G.cut s t).shore ∧
        (P.eval G.cut s t).value = G.cut (P.eval G.cut s t).shore := by
  obtain ⟨P, he, hc, hg⟩ := WeightedUndirected.deterministic_allPairs (V := Fin n)
  refine ⟨P, he, by simp [WeightedUndirected.queryBudget], ?_, hg⟩
  simpa using hc

/-- Every real-weight undirected competitor agreeing on the same schedule is
the original graph, so it inherits all original optimum answers. -/
theorem real_undirected_certificate (n : ℕ) (G : WeightedGraph (Fin n)) :
    ∃ Q : Finset (Finset (Fin n)), Q.card ≤ n + n.choose 2 ∧
      ∃ out : AllPairs.Answers (Fin n), AllPairs.allPairsGood G out ∧
        ∀ H : WeightedGraph (Fin n), Certificate.Consistent G H Q →
          H = G ∧ AllPairs.allPairsGood H out := by
  refine ⟨WeightedUndirected.queries (Fin n), ?_, WeightedUndirected.allPairsAnswers G,
    WeightedUndirected.allPairsAnswers_correct G, fun H h => ?_⟩
  · simpa [WeightedUndirected.queryBudget] using WeightedUndirected.queries_card (V := Fin n)
  · have he := WeightedUndirected.eq_of_consistent h
    exact ⟨he, he ▸ WeightedUndirected.allPairsAnswers_correct G⟩

/-- Deterministic compressed reconstruction gives a point mass on the entire
correct directed-unit answer table, retaining the actual charged count. -/
theorem unit_directed_joint_execution (n : ℕ) (hn : 2 ≤ n) :
    (∀ read : Finset (Fin n) → ℝ,
      ((CompressedDirected.allPairsProgram (V := Fin n)).cost read : ℝ) ≤
        (4 + 32768 * Real.log 3) * (n : ℝ)^2 / Real.log (2 * (n : ℝ))) ∧
    ∀ G : WeightedDiGraph (Fin n), CompressedDirected.Unit G →
      RTree.run G.out (CompressedDirected.allPairsRandomized (V := Fin n)) =
        PMF.pure ((CompressedDirected.honestData G).allPairsAnswers,
          CompressedDirected.budget (Fin n)) ∧
      (∀ s t, s ≠ t →
        s ∈ ((CompressedDirected.honestData G).allPairsAnswers s t).shore ∧
        t ∉ ((CompressedDirected.honestData G).allPairsAnswers s t).shore ∧
        ((CompressedDirected.honestData G).allPairsAnswers s t).value =
          G.out ((CompressedDirected.honestData G).allPairsAnswers s t).shore ∧
        ∀ S, s ∈ S → t ∉ S →
          G.out ((CompressedDirected.honestData G).allPairsAnswers s t).shore ≤ G.out S) := by
  refine ⟨(CompressedDirected.allPairs_deterministic n (by omega)).1, ?_⟩
  intro G hG
  exact ⟨CompressedDirected.allPairsRandomized_run G hG,
    DirectedData.allPairsAnswers_correct _ G rfl rfl⟩

attribute [local irreducible] RTree WeightedMinCut.Endpoint.queryBudget

/-- The weighted randomized wrapper retains the original value query and a
stronger natural-log-squared bound; only nonnegative real capacities are assumed. -/
theorem weighted_global_public {V : Type} [Fintype V] (hn : 2 ≤ Fintype.card V) :
    ∃ P : RTree (Finset V) ℝ (Option (AllPairs.STAnswer V))
        (WeightedMinCut.Endpoint.queryBudget V),
      P = WeightedMinCut.Endpoint.program hn ∧
      (∀ read, ∀ r ∈ (RTree.run read P).support,
        (r.2 : ℝ) ≤ 1000000000 * Fintype.card V * Real.log (2 * (Fintype.card V : ℝ)) ^ 2) ∧
      ∀ G : WeightedGraph V,
        mass (P.eval G.cut) (fun o => ¬∃ a, o = some a ∧
          (a.shore.Nonempty ∧ a.shore ≠ Finset.univ) ∧
          (∀ S, S.Nonempty → S ≠ Finset.univ → G.cut a.shore ≤ G.cut S) ∧
          a.value = G.cut a.shore) ≤ ENNReal.ofReal (1 / 3 : ℝ) := by
  obtain ⟨P, he, hc, hg⟩ :=
    WeightedMinCut.Endpoint.weighted_global (V := V) hn
  refine ⟨P, he, ?_, ?_⟩
  · simpa using hc
  · intro G
    apply le_trans (mass_mono _ ?_) (hg G)
    intro o hbad hgood
    apply hbad
    obtain ⟨a, ha, hmin, hv⟩ := hgood
    exact ⟨a, ha, hmin.1, fun S hS hU => hmin.2 S ⟨hS, hU⟩, hv⟩

end
end CutQueryComplexityChecks.CoverageClassical

#audit_cut_axioms [CutQueryComplexity.Certificate.UnitAllPairs,
  CutQueryComplexity.Reconstruction.DirectedData,
  CutQueryComplexity.Reconstruction.CompressedDirected.Program,
  CutQueryComplexity.Reconstruction.CompressedDirected.Endpoint,
  CutQueryComplexity.Reconstruction.WeightedDirected.Program,
  CutQueryComplexity.Reconstruction.WeightedDirected.Endpoint,
  CutQueryComplexity.Reconstruction.WeightedUndirected,
  CutQueryComplexity.MinCut.WeightedEndpoint] pins [
  CutQueryComplexity.Certificate.UnitAllPairs.exists_unit_allPairs_certificate,
  CutQueryComplexity.Reconstruction.CompressedDirected.program_run,
  CutQueryComplexity.Reconstruction.CompressedDirected.budget_bound,
  CutQueryComplexity.Reconstruction.CompressedDirected.global_deterministic,
  CutQueryComplexity.Reconstruction.CompressedDirected.allPairs_deterministic,
  CutQueryComplexity.Reconstruction.CompressedDirected.allPairsRandomized_success,
  CutQueryComplexity.Reconstruction.WeightedDirected.deterministic_global,
  CutQueryComplexity.Reconstruction.WeightedDirected.deterministic_terminal,
  CutQueryComplexity.Reconstruction.WeightedDirected.deterministic_allPairs,
  CutQueryComplexity.Reconstruction.WeightedDirected.randomized_global,
  CutQueryComplexity.Reconstruction.WeightedDirected.randomized_terminal,
  CutQueryComplexity.Reconstruction.WeightedDirected.randomized_allPairs,
  CutQueryComplexity.Reconstruction.WeightedDirected.queries_cut_equivalent,
  CutQueryComplexity.Reconstruction.WeightedDirected.allPairs_certificate,
  CutQueryComplexity.Reconstruction.WeightedUndirected.queryBudget_le,
  CutQueryComplexity.Reconstruction.WeightedUndirected.deterministic_terminal,
  CutQueryComplexity.Reconstruction.WeightedUndirected.deterministic_allPairs,
  CutQueryComplexity.Reconstruction.WeightedUndirected.randomized_terminal,
  CutQueryComplexity.Reconstruction.WeightedUndirected.randomized_allPairs,
  CutQueryComplexity.Reconstruction.WeightedUndirected.eq_of_consistent,
  CutQueryComplexity.Reconstruction.WeightedUndirected.allPairs_certificate,
  CutQueryComplexity.WeightedMinCut.Endpoint.program_run,
  CutQueryComplexity.WeightedMinCut.Endpoint.queryBudget_logSquared,
  CutQueryComplexity.WeightedMinCut.Endpoint.weighted_global]
#audit_cut_decl CutQueryComplexityChecks.CoverageClassical.real_directed_public_all_pairs
#audit_cut_decl CutQueryComplexityChecks.CoverageClassical.real_undirected_public_all_pairs
#audit_cut_decl CutQueryComplexityChecks.CoverageClassical.real_undirected_certificate
#audit_cut_decl CutQueryComplexityChecks.CoverageClassical.unit_directed_joint_execution
#audit_cut_decl CutQueryComplexityChecks.CoverageClassical.weighted_global_public
