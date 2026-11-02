import CutQueryComplexity.ImplicitLP.PathFollowing.Invariant

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! # A finite execution of the public batch program

This is an actual adaptive query program: each next batch receives the previous public
state. Aborts propagate. Its proof uses the numerical batch theorem, not an assumed
transition theorem. A path schedule must satisfy only scalar bounds and relative changes.
-/

namespace CutQueryComplexity.ImplicitLP.PathFollowing

open DirectedMincut (LPPoint)
open Probability
open scoped ENNReal
noncomputable section

variable {E : NewtonPub}

def Params.batchBudget (P : Params E) : ℕ :=
  ((P.rounds * Sparsify.levelBudget (n := E.n) P.Kd P.J P.samples + 3 * E.n) +
    6 * E.n * (E.Brhs + E.k * E.Bmv + E.Brep)) +
  batchJL E P.Δ * (P.rounds * Sparsify.levelBudget (n := E.n) P.Kd P.J P.samples + 3 * E.n) +
  (2 * (batchSup E.Mbar P.L P.c₀ P.Δ P.T).N + 2) *
    (((batchSup E.Mbar P.L P.c₀ P.Δ P.T).m + 3) *
      (6 * (batchSup E.Mbar P.L P.c₀ P.Δ P.T).B * E.n))

/-- Reindex the existing batch at its stated public budget. -/
def batch (P : Params E) (t : ℝ) (st : State E.n) :
    RTree (Finset (Fin E.n)) ℕ (Option (State E.n)) P.batchBudget :=
  (batchProg E P.s P.terminal P.κ P.m P.c st.1 st.2 t P.L P.c₀ P.Δ P.T
    P.Kd P.J P.samples P.rounds).cast (by unfold Params.batchBudget; ring)

/-- `N` batches on an arbitrary fixed public schedule, starting at schedule index `j`. -/
def run (P : Params E) (τ : ℕ → ℝ) : (N j : ℕ) → State E.n →
    RTree (Finset (Fin E.n)) ℕ (Option (State E.n)) (N * P.batchBudget)
  | 0, _, st => RTree.pure (PMF.pure (some st))
  | N + 1, j, st => ((batch P (τ j) st).bind fun out => match out with
      | none => RTree.pure (PMF.pure none)
      | some st' => run P τ N (j + 1) st').cast (by ring)

/-- The scalar conditions needed for parameter changes. They contain no state or
probabilistic premise and permit both increasing and decreasing schedules. -/
structure Schedule (P : Params E) (τ : ℕ → ℝ) : Prop where
  positive : ∀ j, 0 < τ j
  bounded : ∀ j, |τ j| ≤ 16 * E.n / E.ε
  move_T : ∀ j, |τ (j + 1) / τ j - 1| * P.T ≤ 1 / (2 * P.L) * P.Δ / 16
  move_Δ : ∀ j, |τ (j + 1) / τ j - 1| * P.Δ ≤ 1 / (2 * P.L) * P.Δ / 16

def Good (G : DiGraph (Fin E.n)) (P : Params E) (bc : Fin E.n → ℝ)
    (t : ℝ) (out : Option (State E.n)) : Prop :=
  ∃ st, out = some st ∧ Invariant G P bc t st

def Regime.batchFailure {G : DiGraph (Fin E.n)} {P : Params E} {bc : Fin E.n → ℝ}
    (H : Regime G P bc) : ℝ≥0∞ :=
  d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) +
    batchJL E P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds)

variable {G : DiGraph (Fin E.n)} {P : Params E} {bc : Fin E.n → ℝ}

theorem batch_failure (H : Regime G P bc) {τ : ℕ → ℝ} (hτ : Schedule P τ)
    (j : ℕ) {st : State E.n} (hs : Invariant G P bc (τ j) st) :
    mass ((batch P (τ j) st).eval G.out) (fun out => ¬Good G P bc (τ (j + 1)) out) ≤
      H.batchFailure := by
  rw [batch, RTree.eval_cast]
  refine (mass_mono _ (fun out hbad hg => ?_)).trans
    (batchProg_fail_public H (hτ.bounded j) hs)
  have hg' := hg
  obtain ⟨xn, Xn, he, _⟩ := hg
  apply hbad
  refine ⟨(xn, Xn), he, ?_⟩
  rw [he] at hg'
  exact batchGood_invariant H hg' (hτ.positive j) le_rfl (hτ.move_T j) (hτ.move_Δ j)

/-- The adaptive union bound for the actual run. No independence between batches is used. -/
theorem run_failure (H : Regime G P bc) {τ : ℕ → ℝ} (hτ : Schedule P τ)
    (N j : ℕ) {st : State E.n} (hs : Invariant G P bc (τ j) st) :
    mass ((run P τ N j st).eval G.out) (fun out => ¬Good G P bc (τ (j + N)) out) ≤
      N * H.batchFailure := by
  induction N generalizing j st with
  | zero =>
      simp [run, Good]
      exact ⟨st.1, st.2, rfl, hs⟩
  | succ N ih =>
      rw [run, RTree.eval_cast, RTree.eval_bind]
      refine (mass_bind_le_add _ _ (fun out => ¬Good G P bc (τ (j + 1)) out) _
        (ε := (N : ℝ≥0∞) * H.batchFailure)
        (batch_failure H hτ j hs) ?_).trans (le_of_eq ?_)
      · intro out hout
        obtain ⟨st', rfl, hs'⟩ := not_not.mp hout
        simpa only [Nat.add_assoc, Nat.add_comm 1 N] using ih (j + 1) hs'
      · push_cast
        ring

/-- The cap applies to every execution, including all failure branches. -/
theorem run_cost (G : DiGraph (Fin E.n)) (P : Params E) (τ : ℕ → ℝ) (N j : ℕ)
    (st : State E.n) {out : Option (State E.n) × ℕ}
    (ho : out ∈ (RTree.run G.out (run P τ N j st)).support) : out.2 ≤ N * P.batchBudget :=
  RTree.cost_le _ _ ho

/-- All outputs of the real run have equal duplicate primal and log-weight coordinates.
This statement has no success-event hypothesis. -/
theorem run_copy_eq (G : DiGraph (Fin E.n)) (st : State E.n)
    {i j : Fin (lpM G)} {e : Sym2 (Fin E.n)}
    (hi : lpHidF G i = some e) (hj : lpHidF G j = some e) :
    lpVec G st.1 i = lpVec G st.1 j ∧ lpVec G st.2 i = lpVec G st.2 j :=
  ⟨public_copy_eq G st.1 hi hj, public_copy_eq G st.2 hi hj⟩

/-- A constant positive parameter is a licensed schedule, so centering batches are executable. -/
theorem constant_schedule (H : Regime G P bc) {t : ℝ} (ht : 0 < t)
    (hb : |t| ≤ 16 * E.n / E.ε) : Schedule P (fun _ => t) := by
  have ha : 0 ≤ 1 / (2 * P.L) * P.Δ / 16 := by
    have := H.L_ge; have := H.Δ_pos; positivity
  exact ⟨fun _ => ht, fun _ => hb,
    fun _ => by simpa [div_self ht.ne'] using ha,
    fun _ => by simpa [div_self ht.ne'] using ha⟩

end
end CutQueryComplexity.ImplicitLP.PathFollowing

#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.batch_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.run_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.run_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.run_copy_eq
