import CutQueryComplexity.GHReduction.GuideOneGeometry
import CutQueryComplexity.GHReduction.GuideRecurrence

/-! # Completeness of the actual one-respecting guide recursion

The proof follows the concrete child selected by the parent minimum cut. Its
quotient minimum retains a one-edge guide witness. The actual program's minimum
selection cannot lose that exact value, and its independent one-sided theorem
supplies the original shore certificate for the selected candidate.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

theorem guideOneProgram_child_le {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (fuel : ℕ) (G : WeightedGraph V) (T : GuideTree V N) (hlarge : ¬T.real.card ≤ 10)
    (P : T.parts) (S : Finset V)
    (hS : S = Prog.eval G.cut (centroidShoreProgram family T) P)
    (htrace : S ∩ T.realVertices = T.graphGroup P.val) (t : V) {D : CutCandidate (ShoreVertex S)}
    (hDvalid : CandidateValid (G.contract (shoreMap S)) (shoreMap S T.source) (shoreMap S t) D)
    (hD : Prog.eval (G.contract (shoreMap S)).cut
      (guideOneProgram family fuel (childGuide T P S htrace)) (shoreMap S t) = some D) :
    ∃ E, Prog.eval G.cut (guideOneProgram family (fuel + 1) T) t = some E ∧ E.value ≤ D.value := by
  subst S
  let S := Prog.eval G.cut (centroidShoreProgram family T) P
  have hread : G.cut ∘ pull (shoreMap S) = (G.contract (shoreMap S)).cut := by
    funext X
    exact (cut_contract G _ X).symm
  simp only [guideOneProgram, hlarge, ite_false, Prog.eval_bind, Prog.eval_map,
    finiteTable_eval]
  apply bestCandidates_le (A := ⟨pull (shoreMap S) D.shore, D.value⟩)
  apply List.mem_cons_of_mem
  apply List.mem_map.mpr
  refine ⟨P, by simp, ?_⟩
  simp only [htrace, dite_true, Prog.eval_map, queryMap_eval]
  change pullCandidate (shoreMap S) T.source t
    (Prog.eval (G.cut ∘ pull (shoreMap S))
      (guideOneProgram family fuel (childGuide T P S htrace)) (shoreMap S t)) = _
  rw [hread, hD]
  exact pullCandidate_of_valid G (shoreMap S) T.source t hDvalid

theorem guideOneProgram_complete {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (fuel : ℕ) :
    ∀ {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
      (G : WeightedGraph V), InputPromise M G → ∀ T : GuideTree V N,
      T.real.card ≤ 8 * 2 ^ fuel + 2 → ∀ t ∈ T.realVertices,
      (∃ C, IsSTMinCut G t T.source C ∧ T.RespectsCut C 1) →
      ∃ output, Prog.eval G.cut (guideOneProgram family fuel T) t = some output ∧
        CandidateExact G T.source t output := by
  induction fuel with
  | zero =>
    intro V N _ _ _ _ G hG T hdepth t ht hrespect
    have hsmall : T.real.card ≤ 10 := by simpa using hdepth
    obtain ⟨C, hC, _⟩ := hrespect
    have hst : T.source ≠ t := fun he => hC.2.1 (he.symm ▸ hC.1)
    simpa only [guideOneProgram, hsmall, ite_true, guideBaseProgram] using
      sourceBaseProgram_exact family G hG T.source T.realVertices ht hst
  | succ fuel ih =>
    intro V N _ _ _ _ G hG T hdepth t ht hrespect
    by_cases hsmall : T.real.card ≤ 10
    · obtain ⟨C, hC, _⟩ := hrespect
      have hst : T.source ≠ t := fun he => hC.2.1 (he.symm ▸ hC.1)
      simpa only [guideOneProgram, hsmall, ite_true, guideBaseProgram] using
        sourceBaseProgram_exact family G hG T.source T.realVertices ht hst
    · have hlarge : 2 < T.real.card := by omega
      obtain ⟨C, hC, hrespectC⟩ := hrespect
      obtain ⟨P, htrace, X, hX, hrespectX⟩ :=
        oneEdge_child family G hG T hlarge ht hC hrespectC
      let S := Prog.eval G.cut (centroidShoreProgram family T) P
      let child := childGuide T P S htrace
      have hchildCut : IsSTMinCut (G.contract (shoreMap S)) (shoreMap S t) child.source X := by
        rw [childGuide_source]
        exact minCut_contract_of_pull G (shoreMap S) hX rfl
      have hchildDepth : child.real.card ≤ 8 * 2 ^ fuel + 2 := by
        rw [childGuide_real_card]
        exact child_fuel_bound (T.part_half P.property) hdepth
      have htChild : shoreMap S t ∈ child.realVertices := childGuide_map_real T P S htrace ht
      obtain ⟨D, hD, hDexact⟩ := ih (G.contract (shoreMap S)) (shore_contraction_promise G hG S)
        child hchildDepth (shoreMap S t) htChild ⟨X, hchildCut, hrespectX⟩
      have hDexact' : CandidateExact (G.contract (shoreMap S))
          (shoreMap S T.source) (shoreMap S t) D := by
        simpa only [child, childGuide_source] using hDexact
      have hpullExact : CandidateExact G T.source t ⟨pull (shoreMap S) D.shore, D.value⟩ :=
        candidateExact_pull_of_representable G (shoreMap S) hX rfl hDexact'
      obtain ⟨E, hE, hle⟩ := guideOneProgram_child_le family fuel G T hsmall P S rfl htrace t
        (hDexact'.valid _) hD
      exact ⟨E, hE, valid_le_exact_is_exact G
        (guideOneProgram_valid family (fuel + 1) G T t E hE) hpullExact hle⟩

/-- A public logarithmic fuel choice works uniformly for every hidden graph.
This is a one-respecting endpoint, not the still-pending two-respecting solver
or the full all-pairs reduction. -/
theorem guideOneProgram_clog_complete {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) (G : WeightedGraph V) (hG : InputPromise M G)
    {t : V} (ht : t ∈ T.realVertices)
    (hrespect : ∃ C, IsSTMinCut G t T.source C ∧ T.RespectsCut C 1) :
    ∃ output, Prog.eval G.cut (guideOneProgram family (Nat.clog 2 (T.real.card + 1)) T) t = some output ∧
      CandidateExact G T.source t output :=
  guideOneProgram_complete family _ G hG T (initial_fuel_bound T.real.card) t ht hrespect

end
end CutQueryComplexity.GHReduction
