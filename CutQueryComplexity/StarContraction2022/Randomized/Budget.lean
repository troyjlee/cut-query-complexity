import CutQueryComplexity.StarContraction2022.Randomized.Main
import CutQueryComplexity.MinCut.Weighted

/-! # Literal linear cap and finite amplification

The constant is fixed before n and before the hidden graph. Each iteration
starts a fresh complete attempt; retention alone uses earlier outputs. The
geometric failure theorem is applied to the actual state transformer, after
proving its invariant and success bound from the concrete one-attempt program.
No infinite solver, independent learned rows, or future-success conditioning
appears in this composition.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Randomized

noncomputable section
open scoped Classical ENNReal
open CutQueryComplexity.Probability

def linearConstant : ℕ := Schedule.repetitions * attemptCoefficient

attribute [local irreducible] attemptCoefficient tailCoefficient linearConstant

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

def StateSound (G : WeightedGraph V) (state : Option (CutResult V)) : Prop :=
  ∀ out, state = some out → out.Sound G

def retainState (state : Option (CutResult V)) (fresh : CutResult V) :
    Option (CutResult V) :=
  some (state.elim fresh (fun old => retain old (some fresh)))

theorem retainState_sound (G : WeightedGraph V) (state : Option (CutResult V))
    (fresh : CutResult V) (hs : StateSound G state) (hf : fresh.Sound G) :
    StateSound G (retainState state fresh) := by
  intro out ho
  cases state with
  | none =>
      have he : fresh = out := Option.some.inj ho
      exact he ▸ hf
  | some old =>
      have he : retain old (some fresh) = out := Option.some.inj ho
      rw [← he]
      exact retain_sound (hs old rfl) (fun r hr => by
        cases Option.some.inj hr
        exact hf)

theorem retainState_good_right (G : WeightedGraph V) (state : Option (CutResult V))
    (fresh : CutResult V) (hs : StateSound G state) (hf : CutResult.Optimal G fresh) :
    FoundMinimum G (retainState state fresh) := by
  cases state with
  | none => exact ⟨fresh, rfl, hf⟩
  | some old => exact ⟨retain old (some fresh), rfl, retain_optimal_right (hs old rfl) hf⟩

theorem retainState_good_left (G : WeightedGraph V) (state : Option (CutResult V))
    (fresh : CutResult V) (hs : FoundMinimum G state) (hf : fresh.Sound G) :
    FoundMinimum G (retainState state fresh) := by
  obtain ⟨old, rfl, hold⟩ := hs
  have hnew : ∀ out, some fresh = some out → out.Sound G := by
    intro out ho
    cases Option.some.inj ho
    exact hf
  refine ⟨retain old (some fresh), rfl, ?_⟩
  exact CutResult.optimal_of_sound_value (retain_sound hold.1 hnew)
    (retain_preserves_minimum hold.1 hnew hold.2.2)

def retainedStep (hn : 2 ≤ Fintype.card V) (state : Option (CutResult V)) :
    RTree (Finset V) ℝ (Option (CutResult V)) (attemptCoefficient * Fintype.card V) :=
  (attempt hn).map (retainState state)

theorem retainedStep_present (hn : 2 ≤ Fintype.card V) (state : Option (CutResult V))
    (read : Finset V → ℝ) {out : Option (CutResult V)}
    (hout : out ∈ ((retainedStep hn state).eval read).support) : out ≠ none := by
  rw [retainedStep, RTree.eval_map] at hout
  obtain ⟨fresh, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  simp only [retainState, ne_eq, reduceCtorEq, not_false_eq_true]

theorem retainedStep_sound (hn : 2 ≤ Fintype.card V) (G : SimpleInput V)
    (state : Option (CutResult V)) (hs : StateSound G.toWeighted state)
    {out : Option (CutResult V)}
    (hout : out ∈ ((retainedStep hn state).eval G.toWeighted.cut).support) :
    StateSound G.toWeighted out := by
  rw [retainedStep, RTree.eval_map] at hout
  obtain ⟨fresh, hf, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact retainState_sound G.toWeighted state fresh hs (attempt_sound hn G hf)

theorem retainedStep_keep (hn : 2 ≤ Fintype.card V) (G : SimpleInput V)
    (state : Option (CutResult V)) (hs : FoundMinimum G.toWeighted state)
    {out : Option (CutResult V)}
    (hout : out ∈ ((retainedStep hn state).eval G.toWeighted.cut).support) :
    FoundMinimum G.toWeighted out := by
  rw [retainedStep, RTree.eval_map] at hout
  obtain ⟨fresh, hf, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact retainState_good_left G.toWeighted state fresh hs (attempt_sound hn G hf)

theorem retainedStep_success (hn : 2 ≤ Fintype.card V) (G : SimpleInput V)
    (state : Option (CutResult V)) (hs : StateSound G.toWeighted state) :
    ENNReal.ofReal Schedule.pStar ≤
      mass ((retainedStep hn state).eval G.toWeighted.cut) (FoundMinimum G.toWeighted) := by
  rw [retainedStep, RTree.eval_map, mass_map]
  apply (attempt_success hn G).trans
  exact mass_mono _ (fun fresh hf => retainState_good_right G.toWeighted state fresh hs hf)

theorem retainedStep_failure (hn : 2 ≤ Fintype.card V) (G : SimpleInput V)
    (state : Option (CutResult V)) (hs : StateSound G.toWeighted state) :
    mass ((retainedStep hn state).eval G.toWeighted.cut)
      (fun out => ¬ FoundMinimum G.toWeighted out) ≤ ENNReal.ofReal (1 - Schedule.pStar) := by
  apply failure_le_of_success _ _ (sub_nonneg.mpr Schedule.pStar_le_one)
  have hr := ENNReal.toReal_mono (mass_ne_top _ _)
    (retainedStep_success hn G state hs)
  rw [ENNReal.toReal_ofReal Schedule.pStar_pos.le] at hr
  linarith

theorem iterate_sound (hn : 2 ≤ Fintype.card V) (G : SimpleInput V) (N : ℕ)
    (state : Option (CutResult V)) (hs : StateSound G.toWeighted state)
    {out : Option (CutResult V)}
    (hout : out ∈ ((RTree.iterate (retainedStep hn) N state).eval G.toWeighted.cut).support) :
    StateSound G.toWeighted out := by
  induction N generalizing state out with
  | zero =>
      rw [RTree.eval_iterate_zero, PMF.mem_support_pure_iff] at hout
      simpa only [hout] using hs
  | succ N ih =>
      rw [RTree.eval_iterate_succ, PMF.mem_support_bind_iff] at hout
      obtain ⟨mid, hm, ho⟩ := hout
      exact ih mid (retainedStep_sound hn G state hs hm) ho

/-- Presence holds for arbitrary replies, because every full attempt returns
public data and the first iteration initializes the retained state. -/
theorem iterate_present (hn : 2 ≤ Fintype.card V) (read : Finset V → ℝ) (N : ℕ)
    (state : Option (CutResult V)) (hp : N ≠ 0 ∨ state ≠ none)
    {out : Option (CutResult V)}
    (hout : out ∈ ((RTree.iterate (retainedStep hn) N state).eval read).support) : out ≠ none := by
  induction N generalizing state out with
  | zero =>
      rw [RTree.eval_iterate_zero, PMF.mem_support_pure_iff] at hout
      simpa only [hout] using (hp.resolve_left (by simp))
  | succ N ih =>
      rw [RTree.eval_iterate_succ, PMF.mem_support_bind_iff] at hout
      obtain ⟨mid, hm, ho⟩ := hout
      exact ih mid (Or.inr (retainedStep_present hn state read hm)) ho

theorem repetitions_pos : 0 < Schedule.repetitions := by
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hs := Schedule.repetitions_mul_pStar
  by_contra h
  have hz : Schedule.repetitions = 0 := by omega
  simp only [hz, Nat.cast_zero, zero_mul] at hs
  linarith

theorem repeated_failure (hn : 2 ≤ Fintype.card V) (G : SimpleInput V) :
    mass ((RTree.iterate (retainedStep hn) Schedule.repetitions none).eval G.toWeighted.cut)
      (fun state => ¬ (StateSound G.toWeighted state ∧ FoundMinimum G.toWeighted state)) ≤
        ENNReal.ofReal (1 / 3) := by
  have hnone : StateSound G.toWeighted (none : Option (CutResult V)) := by
    intro out ho
    cases ho
  have hbad : ¬ FoundMinimum G.toWeighted (none : Option (CutResult V)) := by
    rintro ⟨out, ho, _⟩
    cases ho
  have h := WeightedMinCut.iterate_fail_pow (retainedStep hn) G.toWeighted.cut
    (StateSound G.toWeighted) (FoundMinimum G.toWeighted) (ENNReal.ofReal (1 - Schedule.pStar))
    (fun state hs _ ho => retainedStep_sound hn G state hs ho)
    (fun state _ hs _ ho => retainedStep_keep hn G state hs ho)
    (fun state hs => retainedStep_failure hn G state hs)
    Schedule.repetitions none hnone
  rw [if_neg hbad] at h
  apply h.trans
  rw [← ENNReal.ofReal_pow (sub_nonneg.mpr Schedule.pStar_le_one)]
  exact ENNReal.ofReal_le_ofReal Schedule.repetition_failure_le

/-- One family is selected using n alone, before supplying any hidden graph.
The empty and singleton vertex sets use the explicit empty/zero convention. -/
def program (n : ℕ) :
    RTree (Finset (Fin n)) ℝ (CutResult (Fin n)) (linearConstant * n) :=
  if hn : 2 ≤ n then
    ((RTree.iterate (retainedStep (V := Fin n) (by simpa using hn))
      Schedule.repetitions none).map (fun state => state.getD ⟨∅, 0⟩)).cast (by
        simp only [linearConstant, Fintype.card_fin, Nat.mul_assoc])
  else RTree.pure (PMF.pure ⟨∅, 0⟩)

theorem program_every_oracle (n : ℕ) (read : Finset (Fin n) → ℝ)
    {out : CutResult (Fin n) × ℕ}
    (hout : out ∈ (RTree.run read (program n)).support) :
    out.2 ≤ linearConstant * n := RTree.cost_le _ _ hout

theorem program_small (n : ℕ) (hn : n < 2) (read : Finset (Fin n) → ℝ) :
    (program n).eval read = PMF.pure ⟨∅, 0⟩ := by
  simp only [program, dif_neg (Nat.not_le.mpr hn), RTree.eval_pure]

theorem program_sound (n : ℕ) (hn : 2 ≤ n) (G : SimpleInput (Fin n))
    {out : CutResult (Fin n)}
    (hout : out ∈ ((program n).eval G.toWeighted.cut).support) :
    ProperShore out.shore ∧ out.value = G.toWeighted.cut out.shore := by
  rw [program, dif_pos hn, RTree.eval_cast, RTree.eval_map] at hout
  obtain ⟨state, hs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  have hinit : StateSound G.toWeighted (none : Option (CutResult (Fin n))) := by
    intro out ho
    cases ho
  have hsound := iterate_sound (by simpa using hn) G Schedule.repetitions none hinit hs
  have hp := iterate_present (by simpa using hn) G.toWeighted.cut Schedule.repetitions none
    (Or.inl (Nat.ne_of_gt repetitions_pos)) hs
  cases state with
  | none => exact (hp rfl).elim
  | some result => exact hsound result rfl

theorem program_failure (n : ℕ) (hn : 2 ≤ n) (G : SimpleInput (Fin n)) :
    mass ((program n).eval G.toWeighted.cut) (fun out => ¬ CutResult.Optimal G.toWeighted out) ≤
      ENNReal.ofReal (1 / 3) := by
  rw [program, dif_pos hn, RTree.eval_cast, RTree.eval_map, mass_map]
  apply le_trans _ (repeated_failure (by simpa using hn) G)
  apply mass_mono
  intro state hbad hgood
  obtain ⟨out, he, ho⟩ := hgood.2
  rw [he] at hbad
  exact hbad ho

/-- Literal endpoint: exact original value, an actual proper minimum shore,
and probability at least two thirds. No graph-dependent program selector. -/
theorem program_success (n : ℕ) (hn : 2 ≤ n) (G : SimpleInput (Fin n)) :
    ENNReal.ofReal (2 / 3 : ℝ) ≤
      mass ((program n).eval G.toWeighted.cut) (fun out =>
        ProperShore out.shore ∧ out.value = G.toWeighted.cut out.shore ∧
        IsMinCut G.toWeighted out.shore ∧ out.value = mincutValue G.toWeighted) := by
  have h := success_of_failure_le ((program n).eval G.toWeighted.cut)
    (CutResult.Optimal G.toWeighted) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (program_failure n hn G)
  have hr : (2 / 3 : ℝ) ≤
      (mass ((program n).eval G.toWeighted.cut) (CutResult.Optimal G.toWeighted)).toReal := by
    linarith
  have he := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_toReal (mass_ne_top _ _)] at he
  apply he.trans
  apply mass_mono
  intro out ho
  exact ⟨ho.1.1, ho.1.2, ho.2.1, ho.2.2⟩

/-- The coefficient is one literal natural number, using the actual B and P
constants and the same fixed repetition count as the program. -/
theorem linearConstant_eq :
    linearConstant = Schedule.repetitions *
      Schedule.attemptCoefficient Recovery.bucketConstant Certificates.parallelZeroErrorConstant := by
  exact (show linearConstant = Schedule.repetitions * attemptCoefficient from by
    unfold linearConstant; rfl).trans
    (congrArg (fun c : ℕ => Schedule.repetitions * c)
      (show attemptCoefficient = Schedule.attemptCoefficient Recovery.bucketConstant
        Certificates.parallelZeroErrorConstant from by unfold attemptCoefficient; rfl))

theorem linearConstant_pos : 0 < linearConstant := by
  unfold linearConstant
  apply Nat.mul_pos repetitions_pos
  rw [attemptCoefficient_eq]
  omega

/-- The quantifier order makes the information boundary explicit: one constant
and one family of programs precede every hidden input graph and every oracle. -/
theorem exists_uniform_linear_program :
    ∃ C : ℕ, 0 < C ∧
      ∃ P : (n : ℕ) → RTree (Finset (Fin n)) ℝ (CutResult (Fin n)) (C * n),
        (∀ n read (out : CutResult (Fin n) × ℕ),
          out ∈ (RTree.run read (P n)).support → out.2 ≤ C * n) ∧
        (∀ n, 2 ≤ n → ∀ G : SimpleInput (Fin n), ∀ out,
          out ∈ ((P n).eval G.toWeighted.cut).support →
          ProperShore out.shore ∧ out.value = G.toWeighted.cut out.shore) ∧
        (∀ n, 2 ≤ n → ∀ G : SimpleInput (Fin n),
          ENNReal.ofReal (2 / 3 : ℝ) ≤
            mass ((P n).eval G.toWeighted.cut) (fun out =>
              ProperShore out.shore ∧ out.value = G.toWeighted.cut out.shore ∧
              IsMinCut G.toWeighted out.shore ∧ out.value = mincutValue G.toWeighted)) ∧
        (∀ n, n < 2 → ∀ read, (P n).eval read = PMF.pure ⟨∅, 0⟩) := by
  refine ⟨linearConstant, linearConstant_pos, program, ?_, ?_, ?_, ?_⟩
  · intro n read out ho
    exact program_every_oracle n read ho
  · intro n hn G out ho
    exact program_sound n hn G ho
  · exact program_success
  · exact program_small

#print axioms retainState_sound
#print axioms retainState_good_right
#print axioms retainState_good_left
#print axioms retainedStep_sound
#print axioms retainedStep_keep
#print axioms retainedStep_failure
#print axioms iterate_sound
#print axioms iterate_present
#print axioms repetitions_pos
#print axioms repeated_failure
#print axioms program_every_oracle
#print axioms program_small
#print axioms program_sound
#print axioms program_failure
#print axioms program_success
#print axioms linearConstant_eq
#print axioms linearConstant_pos
#print axioms exists_uniform_linear_program

end
end CutQueryComplexity.StarContraction2022.Randomized
