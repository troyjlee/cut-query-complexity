import CutQueryComplexity.GHReduction.ThresholdProgress

/-! # Bounded threshold rounds and adaptive repeated elimination

The reference size stays fixed at the original `n`; no local regularity at a
contracted graph size is assumed. Every seed executes a bounded decision tree.
Fresh rounds are composed by `RTree.bind`, so later samples are conditional on
the actual earlier transcript. This module supplies execution and exact laws;
the numerical repeated-elimination failure bound is proved separately.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V : Type} [Fintype V] [DecidableEq V]

def thresholdRoundBudget (Q : ℕ → ℕ) (n levels : ℕ) : ℕ :=
  (levels + 1) * (Nat.clog 2 n + 3) * (Q n + n)

theorem thresholdRoundProgram_cost {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (U : Finset V) (s : V)
    (W : ℝ) (z levels : ℕ) (seed : ThresholdSeed V levels) (read : Finset V → ℝ) :
    Prog.cost read (thresholdRoundProgram family U s W z levels seed) ≤
      thresholdRoundBudget Q n levels := by
  haveI : Nonempty V := ⟨s⟩
  have hn : 0 < n := lt_of_lt_of_le Fintype.card_pos hvn
  have h := thresholdRoundProgram_cost_scaled family hvn hQ U s W z levels seed read
  have hmul := Nat.mul_le_mul_left ((levels + 1) * (Nat.clog 2 n + 3) * (Q n + n)) hvn
  have hfinal : n * Prog.cost read (thresholdRoundProgram family U s W z levels seed) ≤
      n * thresholdRoundBudget Q n levels := by
    unfold thresholdRoundBudget
    nlinarith
  by_contra hnot
  have hstrict : thresholdRoundBudget Q n levels + 1 ≤
      Prog.cost read (thresholdRoundProgram family U s W z levels seed) := by omega
  have hscaled := Nat.mul_le_mul_left n hstrict
  nlinarith

def thresholdRoundTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) :
    RTree (Finset V) ℝ (Finset V) (thresholdRoundBudget Q n levels) :=
  RTree.mix ((thresholdSeedPMF V levels).map (fun seed => RTree.ofDeterministic
    ((Prog.toDTree (thresholdRoundProgram family U s W z levels seed)
      (thresholdRoundBudget Q n levels)).map (fun output => output.getD ∅))))

theorem thresholdRoundTree_eval {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (U : Finset V) (s : V)
    (W : ℝ) (z levels : ℕ) (read : Finset V → ℝ) :
    (thresholdRoundTree family n U s W z levels).eval read =
      (thresholdSeedPMF V levels).map (fun seed =>
        Prog.eval read (thresholdRoundProgram family U s W z levels seed)) := by
  simp only [thresholdRoundTree, RTree.eval_mix, PMF.bind_map, Function.comp_def]
  have he (seed : ThresholdSeed V levels) :
      (RTree.ofDeterministic ((Prog.toDTree (thresholdRoundProgram family U s W z levels seed)
        (thresholdRoundBudget Q n levels)).map (fun output => output.getD ∅))).eval read =
      PMF.pure (Prog.eval read (thresholdRoundProgram family U s W z levels seed)) := by
    simp only [RTree.eval, RTree.run_ofDeterministic, PMF.pure_map]
    apply congrArg PMF.pure
    change ((Prog.toDTree (thresholdRoundProgram family U s W z levels seed)
      (thresholdRoundBudget Q n levels)).map (fun output => output.getD ∅)).eval read = _
    rw [DTree.eval_map, Prog.toDTree_eval _ _ _
      (thresholdRoundProgram_cost family hvn hQ U s W z levels seed read)]
    rfl
  simp_rw [he]
  rfl

theorem thresholdRoundTree_sound {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (G : WeightedGraph V)
    (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) {D : Finset V}
    (hD : D ∈ ((thresholdRoundTree family n U s W z levels).eval G.cut).support) :
    ∀ x ∈ D, x ∈ U ∧ x ≠ s ∧ stValue G x s ≤ W := by
  rw [thresholdRoundTree_eval family hvn hQ] at hD
  obtain ⟨seed, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hD
  exact fun x hx => thresholdRoundProgram_sound family G U s W z levels seed hx

theorem thresholdRoundTree_expected_progress {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (D U : Finset V) (s : V)
    (W : ℝ) (z levels : ℕ) (C : V → Finset V)
    (hlevels : thresholdLevels U.card ≤ levels) (hDU : D ⊆ U) (hsU : s ∈ U)
    (hC : ∀ v ∈ D, IsCanonicalSTCut G v s (C v))
    (hvalue : ∀ v ∈ D, stValue G v s ≤ W)
    (hsize : ∀ v ∈ D, (C v ∩ U).card ≤ z) :
    (D.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) ≤ (levels + 1 : ℕ) *
      expect ((thresholdRoundTree family n U s W z levels).eval G.cut)
        (fun covered => (covered.card : ℝ≥0∞)) := by
  rw [thresholdRoundTree_eval family hvn hQ, expect_map]
  exact thresholdRoundProgram_expected_progress family G hG D U s W z levels C
    hlevels hDU hsU hC hvalue hsize

/-- Remaining terminals after fresh adaptive rounds. Each round has a fixed
public cap, including on histories that violate the hidden input promise. -/
def thresholdRemainingTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (s : V) (W : ℝ) (levels : ℕ) : (rounds : ℕ) → (U : Finset V) →
      RTree (Finset V) ℝ (Finset V) (rounds * thresholdRoundBudget Q n levels)
  | 0, U => RTree.pure (PMF.pure U)
  | rounds + 1, U =>
    ((thresholdRoundTree family n U s W n levels).bind (fun covered =>
      thresholdRemainingTree family n s W levels rounds (U \ covered))).cast (by ring)

/-- Operational PMF of the same finite program, retaining the dependence of
later terminal sets on earlier sampled shores. -/
def thresholdRemainingLaw {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (s : V) (W : ℝ) (z levels : ℕ) (read : Finset V → ℝ) : ℕ → Finset V → PMF (Finset V)
  | 0, U => PMF.pure U
  | rounds + 1, U => (thresholdSeedPMF V levels).bind (fun seed =>
      thresholdRemainingLaw family s W z levels read rounds
        (U \ Prog.eval read (thresholdRoundProgram family U s W z levels seed)))

theorem thresholdRemainingTree_eval {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (s : V) (W : ℝ) (levels rounds : ℕ) (U : Finset V) (read : Finset V → ℝ) :
    (thresholdRemainingTree family n s W levels rounds U).eval read =
      thresholdRemainingLaw family s W n levels read rounds U := by
  induction rounds generalizing U with
  | zero => simp [thresholdRemainingTree, thresholdRemainingLaw]
  | succ rounds ih =>
    simp only [thresholdRemainingTree, RTree.eval_cast, RTree.eval_bind,
      thresholdRoundTree_eval family hvn hQ, PMF.bind_map, Function.comp_def,
      ih, thresholdRemainingLaw]

theorem thresholdRemainingTree_invariant {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (s : V) (W : ℝ) (levels rounds : ℕ) (U : Finset V)
    {R : Finset V}
    (hR : R ∈ ((thresholdRemainingTree family n s W levels rounds U).eval G.cut).support) :
    R ⊆ U ∧ (s ∈ U → s ∈ R) ∧ ∀ x ∈ U \ R, x ≠ s ∧ stValue G x s ≤ W := by
  induction rounds generalizing U R with
  | zero =>
    have he : R = U := by simpa [thresholdRemainingTree] using hR
    subst R
    simp
  | succ rounds ih =>
    simp only [thresholdRemainingTree, RTree.eval_cast, RTree.eval_bind] at hR
    obtain ⟨covered, hc, hR⟩ := (PMF.mem_support_bind_iff _ _ _).mp hR
    have hs := thresholdRoundTree_sound family hvn hQ G U s W n levels hc
    obtain ⟨hsub, hsource, hremoved⟩ := ih _ hR
    refine ⟨hsub.trans Finset.sdiff_subset, ?_, ?_⟩
    · intro hsU
      exact hsource (Finset.mem_sdiff.mpr ⟨hsU, fun hsc => (hs s hsc).2.1 rfl⟩)
    · intro x hx
      obtain ⟨hxU, hxR⟩ := Finset.mem_sdiff.mp hx
      by_cases hxc : x ∈ covered
      · exact (hs x hxc).2
      · exact hremoved x (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxU, hxc⟩, hxR⟩)

end
end CutQueryComplexity.GHReduction
