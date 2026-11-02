import CutQueryComplexity.GHReduction.SampledGuides

/-! # Coverage and solver failure in the sampled-guide source routine

Hidden minimum shores are selected only inside the probability proof. The
program samples from the explicit graph and solves the resulting guides using
the terminal primitive. The two failure terms cover guide misses and actual
recursive solver failures, respectively.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal BigOperators
open Probability

variable {V : Type} [Fintype V] [DecidableEq V]

theorem guideSampleProgram_source_coverage (G K : WeightedGraph V) (U : Finset V) (s : U)
    (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S)
    (hsmall : ∀ t ∈ U, t ≠ s.val → ∀ S, IsSTMinCut G t s.val S →
      G.cut S ≤ (11 / 10 : ℝ) * terminalMin G U) (samples : ℕ) :
    mass ((guideSampleProgram K U hU hpos samples).eval G.cut)
      (fun L => ¬(L.length = samples ∧ GuideListCoverage G U s.val L)) ≤
      ((U.erase s.val).card : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ samples := by
  let shore : V → Finset V := fun t =>
    if hts : t ≠ s.val then Classical.choose (exists_stMinCut G hts) else ∅
  have hshore (t : V) (hts : t ≠ s.val) : IsSTMinCut G t s.val (shore t) := by
    rw [show shore t = Classical.choose (exists_stMinCut G hts) by
      unfold shore
      rw [dite_eq_left hts]]
    exact (Classical.choose_spec (exists_stMinCut G hts)).1
  have hsmall' (t : V) (ht : t ∈ U.erase s.val) :
      G.cut (shore t) ≤ (11 / 10 : ℝ) * terminalMin G U :=
    hsmall t (Finset.mem_erase.mp ht).2 (Finset.mem_erase.mp ht).1 _
      (hshore t (Finset.mem_erase.mp ht).1)
  have hcoverage := guideSampleProgram_coverage G K U hU hpos happrox
    (U.erase s.val) shore hsmall' samples G.cut
  apply le_trans (mass_mono_on_support _ ?_) hcoverage
  intro L hL hbad hall
  apply hbad
  refine ⟨guideSampleProgram_length K U hU hpos samples G.cut hL, ?_⟩
  intro t ht hts
  obtain ⟨T, hT, hcross⟩ := hall t (Finset.mem_erase.mpr ⟨hts, ht⟩)
  exact ⟨T, hT, shore t, hshore t hts, hcross⟩

theorem sampledGuideContinuation_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (samples trials levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : U)
    (hvn : Fintype.card V ≤ n) (L : List (RootedTree U))
    (hlen : L.length = samples) (hcoverage : GuideListCoverage G U s.val L) :
    mass ((sampledGuideContinuation family n samples trials levels scale exponent U s hvn L).eval G.cut)
      (fun output => ¬SourceValuesSuccess G U s.val output) ≤
      (samples : ℝ≥0∞) * guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) U.card := by
  let f := fun i : Fin samples => guideTwoTree family n trials levels scale exponent
    (Nat.clog 2 (n + 1)) (terminalGuide U s (guideListEntry L hlen i)) hvn
  let Good := fun i : Fin samples => GuideTwoSuccess G (terminalGuide U s (guideListEntry L hlen i))
  let δ := guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) U.card
  have heach (i : Fin samples) : mass ((f i).eval G.cut) (fun output => ¬Good i output) ≤ δ := by
    simpa only [f, Good, δ, terminalGuide_real_card] using
      guideTwoTree_clog_failure_le family hQ hnscale trials levels exponent hlevels G hG
        (terminalGuide U s (guideListEntry L hlen i)) hvn
  have htable := randomTable_failure_le (fun _ => none) f G.cut Good (fun _ => δ) heach
  rw [sampledGuideContinuation, dif_pos hlen, RTree.eval_cast, RTree.eval_map, mass_map]
  apply le_trans (mass_mono _ ?_)
    (by simpa only [δ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using htable)
  intro output hbad hgood
  exact hbad (mergeGuideValues_success G U s L hlen hcoverage output hgood)

theorem sampledGuideTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (samples trials levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : U)
    (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U) (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S)
    (hsmall : ∀ t ∈ U, t ≠ s.val → ∀ S, IsSTMinCut G t s.val S →
      G.cut S ≤ (11 / 10 : ℝ) * terminalMin G U) :
    mass ((sampledGuideTree family n samples trials levels scale exponent K U s hU hpos hvn).eval G.cut)
      (fun output => ¬SourceValuesSuccess G U s.val output) ≤
      ((U.erase s.val).card : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ samples +
      (samples : ℝ≥0∞) * guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) U.card := by
  rw [sampledGuideTree, RTree.eval_cast, RTree.eval_bind]
  apply mass_bind_le_add _ _ (fun L => ¬(L.length = samples ∧ GuideListCoverage G U s.val L)) _
    (guideSampleProgram_source_coverage G K U s hU hpos happrox hsmall samples)
  intro L hgood
  have h := not_not.mp hgood
  exact sampledGuideContinuation_failure_le family hQ hnscale samples trials levels exponent hlevels
    G hG U s hvn L h.1 h.2

end
end CutQueryComplexity.GHReduction
