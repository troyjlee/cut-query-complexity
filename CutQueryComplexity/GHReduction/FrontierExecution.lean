import CutQueryComplexity.GHReduction.FrontierRoundState

/-! # Actual adaptive execution of finite frontier rounds

Each recorded round executes the current state's contraction programs, then
computes the next state from its own returned table. Fuel decreases even when
every split is empty. The output retains the public round records for later
tree assembly; it does not claim that their final topology is already a GH
tree. Failure is charged to this actual adaptive sequence and the hard cap
holds for every oracle answer function.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal
open Probability

variable {V : Type} [Fintype V] [DecidableEq V]

def FrontierRoundRecord.Good (G : WeightedGraph V) {levels : ℕ}
    (record : FrontierRoundRecord V levels) : Prop :=
  record.result.elim False (fun table =>
    ∀ b, FrontierPivotGood G record.before.block record.before.tree b (table b))

def frontierRoundBudget (M : ℕ) (Q : ℕ → ℕ)
    (n samples trials guideLevels scale exponent levels : ℕ) : ℕ :=
  3 * sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels

def frontierStateStep {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (state : PublicFrontierState V) :
    RTree (Finset V) ℝ (FrontierRoundRecord V levels)
      (frontierRoundBudget M Q n samples trials guideLevels scale exponent levels) :=
  (frontierPivotRoundCapped family n samples trials guideLevels scale exponent levels
    K state.block state.onto state.tree hvn).map (fun result => ⟨state, result⟩)

theorem frontierStateStep_before {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (state : PublicFrontierState V) (read : Finset V → ℝ)
    {record : FrontierRoundRecord V levels}
    (hrecord : record ∈ ((frontierStateStep family n samples trials guideLevels scale exponent levels
      K hvn state).eval read).support) : record.before = state := by
  unfold frontierStateStep frontierRoundBudget at hrecord
  rw [RTree.eval_map] at hrecord
  obtain ⟨result, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hrecord
  rfl

theorem frontierStateStep_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 0 < n) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent levels : ℕ) (hlevels : thresholdLevels n ≤ guideLevels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) (state : PublicFrontierState V) :
    mass ((frontierStateStep family n samples trials guideLevels scale exponent levels K hvn state).eval G.cut)
      (fun record => ¬record.Good G) ≤
      (n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent := by
  unfold frontierStateStep frontierRoundBudget
  rw [RTree.eval_map, mass_map]
  exact frontierPivotRoundCapped_failure_le family hQ hn hnscale samples trials guideLevels exponent levels
    hlevels G K hG state.block state.onto state.tree hvn happrox

structure FrontierTrace (V : Type) [Fintype V] [DecidableEq V] (levels : ℕ) where
  endState : PublicFrontierState V
  records : List (FrontierRoundRecord V levels)

def FrontierTrace.Good (G : WeightedGraph V) {levels : ℕ} (trace : FrontierTrace V levels) : Prop :=
  ∀ record ∈ trace.records, record.Good G

/-- Literal execution correspondence for a finite public record list. -/
def FrontierTrace.Follows {levels : ℕ} : PublicFrontierState V →
    List (FrontierRoundRecord V levels) → PublicFrontierState V → Prop
  | start, [], final => final = start
  | start, record :: rest, final => record.before = start ∧ FrontierTrace.Follows record.after rest final

def frontierExecution {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) : (fuel : ℕ) → PublicFrontierState V →
      RTree (Finset V) ℝ (FrontierTrace V levels)
        (fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels)
  | 0, state => RTree.pure (PMF.pure ⟨state, []⟩)
  | fuel + 1, state =>
      ((frontierStateStep family n samples trials guideLevels scale exponent levels K hvn state).bind
        (fun record => (frontierExecution family n samples trials guideLevels scale exponent levels
          K hvn fuel record.after).map (fun tail => ⟨tail.endState, record :: tail.records⟩))).cast
            (by rw [Nat.succ_mul]; omega)

/-- Every supported output lists exactly the rounds that generated its final
state. The graph may occur only in the external answer function `read`. -/
theorem frontierExecution_support {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (fuel : ℕ) (state : PublicFrontierState V) (read : Finset V → ℝ)
    {trace : FrontierTrace V levels}
    (htrace : trace ∈ ((frontierExecution family n samples trials guideLevels scale exponent levels
      K hvn fuel state).eval read).support) :
    trace.records.length = fuel ∧ FrontierTrace.Follows state trace.records trace.endState := by
  induction fuel generalizing state trace with
  | zero =>
      simp only [frontierExecution, RTree.eval_pure] at htrace
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp htrace
      exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      simp only [frontierExecution, RTree.eval_cast, RTree.eval_bind] at htrace
      obtain ⟨record, hrecord, htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp htrace
      rw [RTree.eval_map] at htail
      obtain ⟨tail, htailSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htail
      have hrest := ih record.after htailSupported
      refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ hrest.1, ?_⟩
      exact ⟨frontierStateStep_before family samples trials guideLevels scale exponent levels
        K hvn state read hrecord, hrest.2⟩

/-- The executable cap is unconditional, not an expected query bound. -/
theorem frontierExecution_cost {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (fuel : ℕ) (state : PublicFrontierState V) (read : Finset V → ℝ)
    {out : FrontierTrace V levels × ℕ}
    (hout : out ∈ (RTree.run read (frontierExecution family n samples trials guideLevels scale exponent levels
      K hvn fuel state)).support) :
    out.2 ≤ fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels :=
  RTree.cost_le _ read hout

/-- The same original approximation event covers every adaptively chosen
state. This induction charges fresh failures along the actual bind order;
it does not condition the next pivot on future successful outcomes. -/
theorem frontierExecution_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 0 < n) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent levels : ℕ) (hlevels : thresholdLevels n ≤ guideLevels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) (fuel : ℕ) (state : PublicFrontierState V) :
    mass ((frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel state).eval G.cut)
      (fun trace => ¬trace.Good G) ≤
      (fuel : ℝ≥0∞) * ((n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent) := by
  induction fuel generalizing state with
  | zero => simp [frontierExecution, FrontierTrace.Good]
  | succ fuel ih =>
      let δ := (n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent
      have hfirst := frontierStateStep_failure_le family hQ hn hnscale samples trials guideLevels exponent levels
        hlevels G K hG hvn happrox state
      simp only [frontierExecution, RTree.eval_cast, RTree.eval_bind]
      calc
        _ ≤ δ + (fuel : ℝ≥0∞) * δ := by
          apply mass_bind_le_add _ _ (fun record => ¬record.Good G) _ hfirst
          intro record hrecord
          have hg : record.Good G := not_not.mp hrecord
          rw [RTree.eval_map, mass_map]
          apply le_trans (mass_mono _ ?_) (ih record.after)
          intro tail hbad hgood
          apply hbad
          intro next hnext
          rcases List.mem_cons.mp hnext with he | hn
          · subst next
            exact hg
          · exact hgood next hn
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, δ]; ac_rfl

end
end CutQueryComplexity.GHReduction
