import CutQueryComplexity.GHReduction.GuideBase
import CutQueryComplexity.GHReduction.GuideSplit
import CutQueryComplexity.GHReduction.GuidePruning
import CutQueryComplexity.GHReduction.CandidateLifting

/-! # The finite same-parameter guide recursion

This is the actual `k = 1` recursive query program: a real-centroid pair call,
canonical group isolation, guarded complement contractions, recursive calls,
and minimum selection of lifted witnesses. Fuel is consumed on every internal
step. Its sharp fuel/cost theorem and respected-cut completeness are separate
obligations; this module does not assume either conclusion as a solver field.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def centroidPairProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) : Prog (Finset V) ℝ (Option (CutCandidate V)) :=
  if T.centroid ∈ T.real then pairCandidateProgram family T.source (T.label T.centroid)
    else Prog.pure none

theorem centroidPairProgram_value {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (T : GuideTree V N) {C : CutCandidate V}
    (h : Prog.eval G.cut (centroidPairProgram family T) = some C) : C.value = G.cut C.shore := by
  by_cases hc : T.centroid ∈ T.real
  · simp only [centroidPairProgram, hc, ite_true] at h
    exact (pairCandidateProgram_valid family G T.source (T.label T.centroid) h).2.2
  · simp [centroidPairProgram, hc] at h

theorem labels_mem_of_trace (T : GuideTree V N) (P : T.parts) (S : Finset V)
    (htrace : S ∩ T.realVertices = T.graphGroup P.val) :
    ∀ v ∈ P.val, T.label v ∈ S := by
  intro v hv
  have hmem : T.label v ∈ T.graphGroup P.val := Finset.mem_image.mpr ⟨v, hv, rfl⟩
  rw [← htrace] at hmem
  exact (Finset.mem_inter.mp hmem).1

def childGuide (T : GuideTree V N) (P : T.parts) (S : Finset V)
    (htrace : S ∩ T.realVertices = T.graphGroup P.val) : GuideTree (ShoreVertex S) (Option N) :=
  T.addProxy P.val (T.part_subset P.property) S (labels_mem_of_trace T P S htrace)

theorem childGuide_source (T : GuideTree V N) (P : T.parts) (S : Finset V)
    (htrace : S ∩ T.realVertices = T.graphGroup P.val) :
    (childGuide T P S htrace).source = shoreMap S T.source :=
  T.addProxy_source P.val (T.part_subset P.property) S (labels_mem_of_trace T P S htrace) htrace

theorem childGuide_real_card (T : GuideTree V N) (P : T.parts) (S : Finset V)
    (htrace : S ∩ T.realVertices = T.graphGroup P.val) :
    (childGuide T P S htrace).real.card = P.val.card + 1 :=
  T.addProxy_real_card P.val (T.part_subset P.property) S (labels_mem_of_trace T P S htrace)

def guideOneProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (fuel : ℕ) {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
    (T : GuideTree V N) : Prog (Finset V) ℝ (V → Option (CutCandidate V)) :=
  match fuel with
  | 0 => if T.real.card ≤ 10 then guideBaseProgram family T else Prog.pure (fun _ => none)
  | fuel + 1 => if T.real.card ≤ 10 then guideBaseProgram family T else
      (centroidPairProgram family T).bind (fun initial =>
        (centroidShoreProgram family T).bind (fun shores =>
          (finiteTable (fun P : T.parts =>
            let S := shores P
            if htrace : S ∩ T.realVertices = T.graphGroup P.val then
              let child := childGuide T P S htrace
              (queryMap (WeightedGraph.pull (shoreMap S)) (guideOneProgram family fuel child)).map
                (fun output t => pullCandidate (shoreMap S) T.source t (output (shoreMap S t)))
            else Prog.pure (fun _ => none))).map (fun children t =>
              bestCandidates (filterCandidate T.source t initial ::
                (Finset.univ.toList.map (fun P : T.parts => children P t))))))
termination_by fuel

/-- Every candidate output by the finite recursion is a witnessed upper bound,
even when a primitive's returned shore is malformed. Exactness of the supplied
primitive is not needed for this one-sided claim. -/
theorem guideOneProgram_valid {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (fuel : ℕ) :
    ∀ {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
      (G : WeightedGraph V) (T : GuideTree V N) (t : V) (C : CutCandidate V),
      Prog.eval G.cut (guideOneProgram family fuel T) t = some C → CandidateValid G T.source t C := by
  induction fuel with
  | zero =>
    intro V N _ _ _ _ G T t C h
    by_cases hsmall : T.real.card ≤ 10
    · simpa only [guideOneProgram, hsmall, ite_true, guideBaseProgram] using
        sourceBaseProgram_valid family G T.source T.realVertices t
          (by simpa only [guideOneProgram, hsmall, ite_true, guideBaseProgram] using h)
    · simp [guideOneProgram, hsmall] at h
  | succ fuel ih =>
    intro V N _ _ _ _ G T t C h
    by_cases hsmall : T.real.card ≤ 10
    · exact sourceBaseProgram_valid family G T.source T.realVertices t
        (by simpa only [guideOneProgram, hsmall, ite_true, guideBaseProgram] using h)
    · let initial := Prog.eval G.cut (centroidPairProgram family T)
      rw [guideOneProgram, if_neg hsmall] at h
      rw [Prog.eval_bind, Prog.eval_bind] at h
      -- Validity holds for arbitrary shores; keep their evaluator out of child types.
      generalize Prog.eval G.cut (centroidShoreProgram family T) = shores at h
      simp only [Prog.eval_map, finiteTable_eval] at h
      apply bestCandidates_valid G T.source t _ ?_ h
      intro a ha B hB
      rcases List.mem_cons.mp ha with ha | ha
      · rw [ha] at hB
        exact filterCandidate_valid G T.source t
          (fun A hA => centroidPairProgram_value family G T (C := A) hA) hB
      · obtain ⟨P, _, hP⟩ := List.mem_map.mp ha
        rw [← hP] at hB
        let S := shores P
        rw [show shores P = S from rfl] at hB
        by_cases htrace : S ∩ T.realVertices = T.graphGroup P.val
        · let child := childGuide T P S htrace
          have hread : G.cut ∘ WeightedGraph.pull (shoreMap S) = (G.contract (shoreMap S)).cut := by
            funext X
            exact (WeightedGraph.cut_contract G _ X).symm
          have hchild : ∀ D,
              Prog.eval (G.contract (shoreMap S)).cut (guideOneProgram family fuel child) (shoreMap S t) =
                some D → D.value = (G.contract (shoreMap S)).cut D.shore := by
            intro D hD
            exact (ih (G.contract (shoreMap S)) child (shoreMap S t) D hD).2.2
          apply pullCandidate_valid G (shoreMap S) T.source t hchild
          simpa only [htrace, dite_true, Prog.eval_map, queryMap_eval, hread] using hB
        · simp [htrace] at hB

end
end CutQueryComplexity.GHReduction
