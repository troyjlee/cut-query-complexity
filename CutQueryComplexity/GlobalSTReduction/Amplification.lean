import CutQueryComplexity.GlobalSTReduction.Specification

/-! # Amplifying a family that returns arbitrary minimum shores (Phase 5)

The existing amplification `STPrograms.amplify r` runs the program `r` times
with fresh randomness, queries the value of every returned shore, discards
shores that miss the source or contain the sink, and returns the intersection of
the remaining shores of least queried value (`selectShore`). Its cost is
`amplifiedCost r Q k = r (Q k + k)`, which preserves size regularity.

Here the runs need not return the canonical shore. If one run returns *some*
minimum shore, the least queried value is the minimum, so every kept shore is a
minimum shore; minimum s-t shores are closed under intersection
(`stMinCut_inter`), so the selection is a minimum shore
(`selectShore_stMinCut`). No canonical output, majority or agreement between
runs is needed. Hence `OptFailsAtMost δ` becomes `OptFailsAtMost (δ ^ r)`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability GHReduction GHReduction.Randomized

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The intersection of a nonempty list of minimum s-t shores is a minimum s-t shore. -/
theorem foldr_inter_stMinCut (G : WeightedGraph V) {s t : V} :
    ∀ {L : List (Finset V × ℝ)}, L ≠ [] → (∀ p ∈ L, IsSTMinCut G s t p.1) →
      IsSTMinCut G s t (L.foldr (fun p acc => p.1 ∩ acc) Finset.univ)
  | [], hne, _ => absurd rfl hne
  | [p], _, h => by simpa using h p List.mem_cons_self
  | p :: q :: L, _, h => by
      rw [List.foldr_cons]
      exact stMinCut_inter G (h p List.mem_cons_self)
        (foldr_inter_stMinCut G (List.cons_ne_nil q L) (fun x hx => h x (List.mem_cons_of_mem p hx)))

/-- If the reported values are the true cut values and one candidate is a minimum
s-t shore, the selection is a minimum s-t shore. -/
theorem selectShore_stMinCut (G : WeightedGraph V) {s t : V} {L : List (Finset V × ℝ)}
    (hval : ∀ p ∈ L, p.2 = G.cut p.1) {p : Finset V × ℝ} (hp : p ∈ L)
    (hmin : IsSTMinCut G s t p.1) : IsSTMinCut G s t (selectShore s t L) := by
  have hpC : p ∈ L.filter (fun p => s ∈ p.1 ∧ t ∉ p.1) := by
    simpa [List.mem_filter] using And.intro hp (And.intro hmin.1 hmin.2.1)
  have hpLeast : p ∈ (L.filter (fun p => s ∈ p.1 ∧ t ∉ p.1)).filter
      (fun p => ∀ p' ∈ L.filter (fun p => s ∈ p.1 ∧ t ∉ p.1), p.2 ≤ p'.2) := by
    refine List.mem_filter.mpr ⟨hpC, ?_⟩
    simp only [decide_eq_true_eq]
    intro p' hp'
    obtain ⟨hp'L, hp'st⟩ := List.mem_filter.mp hp'
    simp only [decide_eq_true_eq] at hp'st
    rw [hval p hp, hval p' hp'L]
    exact hmin.2.2 p'.1 hp'st.1 hp'st.2
  unfold selectShore
  dsimp only
  refine foldr_inter_stMinCut G (List.ne_nil_of_mem hpLeast) (fun p' hp' => ?_)
  obtain ⟨hp'C, hleast⟩ := List.mem_filter.mp hp'
  simp only [decide_eq_true_eq] at hleast
  obtain ⟨hp'L, hp'st⟩ := List.mem_filter.mp hp'C
  simp only [decide_eq_true_eq] at hp'st
  have hle : G.cut p'.1 ≤ G.cut p.1 := by
    rw [← hval p' hp'L, ← hval p hp]
    exact hleast p hpC
  exact ⟨hp'st.1, hp'st.2, fun A hsA htA => hle.trans (hmin.2.2 A hsA htA)⟩

/-- The amplified run misses a minimum shore only if every run did. -/
theorem amplifiedRun_optFailure (G : WeightedGraph V) {q : ℕ}
    (T : RTree (Finset V) ℝ (Finset V) q) (s t : V) (r : ℕ) {δ : ℝ≥0∞}
    (hT : mass (T.eval G.cut) (fun S => ¬IsSTMinCut G s t S) ≤ δ) :
    mass ((amplifiedRun T s t r).eval G.cut) (fun S => ¬IsSTMinCut G s t S) ≤ δ ^ r := by
  have hbad : mass ((valuedRun T).eval G.cut) (fun p => ¬IsSTMinCut G s t p.1) ≤ δ := by
    rw [valuedRun_eval, mass_map]
    exact hT
  rw [amplifiedRun, RTree.eval_map, mass_map]
  refine le_trans (mass_mono_on_support _ ?_) (randomRepeat_failure_le _ r G.cut _ hbad)
  intro L hL hfail p hp hmin
  have hval : ∀ p ∈ L, p.2 = G.cut p.1 := by
    intro p' hp'
    have h := randomRepeat_member _ r G.cut hL hp'
    rw [valuedRun_eval] at h
    obtain ⟨S, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    rfl
  exact hfail (selectShore_stMinCut G hval hp hmin)

/-- `r` repetitions turn per-instance failure `δ` into `δ ^ r`, for arbitrary
minimum shores. -/
theorem OptFailsAtMost.amplify {Q : ℕ → ℕ} {P : STPrograms Q} {δ : ℝ≥0∞}
    (hP : OptFailsAtMost P δ) (r : ℕ) : OptFailsAtMost (P.amplify r) (δ ^ r) := by
  intro k s t hst G
  simp only [STPrograms.amplify, RTree.eval_weaken]
  exact amplifiedRun_optFailure G _ s t r (hP k s t hst G)

/-- An amplified randomized real-weight family fails with probability at most `3⁻¹ ^ r`. -/
theorem RandomRealSTFamily.amplify_optFailsAtMost {Q : ℕ → ℕ}
    (family : RandomRealSTFamily Q) (r : ℕ) :
    OptFailsAtMost (STPrograms.amplify (Q := Q) family.program r) (3⁻¹ ^ r) := by
  simpa only [one_div] using OptFailsAtMost.amplify family.optFailsAtMost r

end
end CutQueryComplexity.GlobalSTReduction
