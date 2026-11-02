import CutQueryComplexity.Probability.Truncation
import CutQueryComplexity.Probability.Expectation
import CutQueryComplexity.StarContraction2022.Recovery.RecoverAll
import Mathlib.Tactic

/-!
# Finite query clocks and exact completion coupling

Generic operational truncation lemmas are instantiated by the bucket and full
recovery programs below. Their finite expected-cost and positive-query progress
proofs discharge the generic premises. A horizon of q+1 query-bearing rounds
excludes unfinished outputs from paths surviving a q-query cap. The final
constructor caps original cut queries at a fixed universal linear bound.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Recovery

open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {I A O : Type} {q : ℕ}

private theorem map_equal_on_support {α β : Type} (p : PMF α) {f g : α → β}
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  ext y
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ p.support
  · rw [h x hx]
  · have hz : p x = 0 := by simpa only [PMF.mem_support_iff, not_not] using hx
    simp [hz]

/-- A real bounded query tree, followed by a public completion check. Neither
its clock nor its completion predicate is selected using the hidden input. -/
def finiteCompleteCap (T : RTree I A O q) (clock : ℕ) (complete : O → Prop) :
    RTree I A (Option O) clock :=
  (T.truncate clock).map fun out => out.bind fun x => if complete x then some x else none

theorem finiteCompleteCap_eval (T : RTree I A O q) (clock : ℕ) (complete : O → Prop)
    (read : I → A) :
    (finiteCompleteCap T clock complete).eval read =
      (RTree.run read T).map
        (fun out => if out.2 ≤ clock ∧ complete out.1 then some out.1 else none) := by
  rw [finiteCompleteCap, RTree.eval_map, RTree.eval_truncate, PMF.map_comp]
  congr 1
  funext out
  by_cases hc : out.2 ≤ clock <;> by_cases hd : complete out.1 <;>
    simp [Function.comp_def, hc, hd]

/-- Positive query progress discharges this supported-output condition for the
actual q+1-round solver. The extra completion guard then causes no further abort. -/
theorem finiteCompleteCap_same_clock (T : RTree I A O q) (clock : ℕ)
    (complete : O → Prop) (read : I → A)
    (hunfinished : ∀ out ∈ (RTree.run read T).support,
      ¬complete out.1 → clock < out.2) :
    (finiteCompleteCap T clock complete).eval read = (T.truncate clock).eval read := by
  rw [finiteCompleteCap_eval, RTree.eval_truncate]
  apply map_equal_on_support
  intro out hout
  by_cases hc : out.2 ≤ clock
  · have hd : complete out.1 := by
      by_contra hd
      exact (Nat.not_lt.mpr hc) (hunfinished out hout hd)
    simp [hc, hd]
  · simp [hc]

/-- Every oracle, including inconsistent real replies, obeys the literal clock. -/
theorem finiteCompleteCap_every_oracle (T : RTree I A O q) (clock : ℕ)
    (complete : O → Prop) (read : I → A) {out : Option O × ℕ}
    (hout : out ∈ (RTree.run read (finiteCompleteCap T clock complete)).support) :
    out.2 ≤ clock := RTree.cost_le _ _ hout

/-- The abort debit is proved from a finite run's actual expected cost. There is
no assumed infinite solver and no completion probability conditioned on a cap. -/
theorem finiteCompleteCap_abort_le (T : RTree I A O q) (clock : ℕ)
    (complete : O → Prop) (read : I → A) {η : ℝ≥0∞}
    (hunfinished : ∀ out ∈ (RTree.run read T).support,
      ¬complete out.1 → clock < out.2)
    (hcost : T.expectedQueries read ≤ (clock+1 : ℝ≥0∞)*η) :
    mass ((finiteCompleteCap T clock complete).eval read) (fun out => out = none) ≤ η := by
  rw [finiteCompleteCap_same_clock T clock complete read hunfinished]
  exact RTree.truncate_abort_le T clock read hcost

/-- Bad completed outputs of the capped run are a subset of bad outputs of its
uncapped finite approximation. This statement never conditions on clock success. -/
theorem finiteCompleteCap_bad_le (T : RTree I A O q) (clock : ℕ)
    (complete Bad : O → Prop) (read : I → A) :
    mass ((finiteCompleteCap T clock complete).eval read)
      (fun out => out.elim False Bad) ≤ mass (T.eval read) Bad := by
  rw [finiteCompleteCap_eval, mass_map, RTree.eval, mass_map]
  apply mass_mono
  intro out hbad
  by_cases hc : out.2 ≤ clock ∧ complete out.1
  · simpa only [ite_eq_left hc, Option.elim_some] using hbad
  · simp only [ite_eq_right hc, Option.elim_none] at hbad

theorem finiteCompleteCap_expect_le (T : RTree I A O q) (clock : ℕ)
    (complete : O → Prop) (read : I → A) (f : O → ℝ≥0∞) :
    expect ((finiteCompleteCap T clock complete).eval read) (fun out => out.elim 0 f) ≤
      expect (T.eval read) f := by
  rw [finiteCompleteCap_eval,expect_map,RTree.eval,expect_map]
  apply expect_mono_on_support
  intro out _
  by_cases hc : out.2 ≤ clock ∧ complete out.1
  · simp only [ite_eq_left hc,Option.elim_some,le_refl]
  · simp only [ite_eq_right hc,Option.elim_none,zero_le]

/-- Failure is bounded by the pre-cap bad-output law plus the explicit clock
abort debit. The uncapped law is not silently re-used after conditioning. -/
theorem finiteCompleteCap_failure_le (T : RTree I A O q) (clock : ℕ)
    (complete Good : O → Prop) (read : I → A) {δ η : ℝ≥0∞}
    (hunfinished : ∀ out ∈ (RTree.run read T).support,
      ¬complete out.1 → clock < out.2)
    (hbad : mass (T.eval read) (fun x => ¬Good x) ≤ δ)
    (hcost : T.expectedQueries read ≤ (clock+1 : ℝ≥0∞)*η) :
    mass ((finiteCompleteCap T clock complete).eval read)
      (fun out => ¬out.elim False Good) ≤ δ+η := by
  have he : (fun out : Option O => ¬out.elim False Good) =
      (fun out => out.elim False (fun x => ¬Good x) ∨ out = none) := by
    funext out
    cases out <;> simp
  rw [he]
  exact (mass_or_le _ _ _).trans (add_le_add
    ((finiteCompleteCap_bad_le T clock complete (fun x => ¬Good x) read).trans hbad)
    (finiteCompleteCap_abort_le T clock complete read hunfinished hcost))

/-- A fixed public clock for an explicitly proved nonnegative cost expression. -/
def hundredClock (B : ℝ) : ℕ := 100*⌈B⌉₊

theorem hundredClock_pays {B : ℝ} (hB : 0 ≤ B) :
    ENNReal.ofReal B ≤ (hundredClock B + 1 : ℝ≥0∞) * (100 : ℝ≥0∞)⁻¹ := by
  have hc : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have hr : B ≤ (((hundredClock B : ℕ) : ℝ)+1)*(1/100 : ℝ) := by
    unfold hundredClock
    push_cast
    linarith
  have h100 : ENNReal.ofReal (1/100 : ℝ) = (100 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]
  calc
    ENNReal.ofReal B ≤ ENNReal.ofReal (((hundredClock B : ℝ)+1)*(1/100 : ℝ)) :=
      ENNReal.ofReal_le_ofReal hr
    _ = (hundredClock B+1 : ℝ≥0∞)*(100 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_mul (by positivity), h100,
        ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]

section Bucket

variable {R C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- Exactly clock+1 public rounds suffice: an unfinished supported execution
would have spent more queries than the clock allows. -/
def cappedBucketTree (r k clock : ℕ) :
    RTree (BipartiteQuery R C) ℝ (Option (BucketState R C)) clock :=
  finiteCompleteCap (learnBucketRounds r k (clock+1) BucketState.initial) clock
    BucketState.complete

theorem cappedBucketTree_every_oracle (r k clock : ℕ)
    (read : BipartiteQuery R C → ℝ) {out : Option (BucketState R C) × ℕ}
    (hout : out ∈ (RTree.run read (cappedBucketTree r k clock)).support) : out.2 ≤ clock :=
  RTree.cost_le _ _ hout

/-- The positive-query requirement is discharged for the concrete bucket tree.
No horizon-tail term is hidden in its completion guard. -/
theorem cappedBucketTree_same_clock (M : BooleanMatrix R C) (r k clock : ℕ) :
    (cappedBucketTree (R := R) (C := C) r k clock).eval (fun q => (bilinear M q : ℝ)) =
      ((learnBucketRounds r k (clock+1) (BucketState.initial : BucketState R C)).truncate clock).eval
        (fun q => (bilinear M q : ℝ)) := by
  apply finiteCompleteCap_same_clock
  intro out hout hnot
  obtain ⟨hf,_,hprogress⟩ := learnBucketRounds_progress M r k (clock+1)
    BucketState.initial rfl hout
  have hp : out.1.pending.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    exact hnot ⟨hf,he⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self clock) (hprogress hp)

/-- A generic finite Markov interface. The public B specialization below
supplies the cost proof from the implemented sparse measurement program. -/
theorem cappedBucketTree_abort_le_of_expected (M : BooleanMatrix R C) (r k clock : ℕ)
    {η : ℝ≥0∞}
    (hcost : (learnBucketRounds r k (clock+1) (BucketState.initial : BucketState R C)).expectedQueries
      (fun q => (bilinear M q : ℝ)) ≤ (clock+1 : ℝ≥0∞)*η) :
    mass ((cappedBucketTree (R := R) (C := C) r k clock).eval
      (fun q => (bilinear M q : ℝ))) (fun out => out = none) ≤ η := by
  rw [cappedBucketTree_same_clock]
  exact RTree.truncate_abort_le _ _ _ hcost

/-- Any non-aborting capped output is an explicit table of k distinct true
neighbors. Range validation and the decoder belong to the same queried tree. -/
theorem cappedBucketTree_true_neighbors (M : BooleanMatrix R C) (r k clock : ℕ)
    (st : BucketState R C)
    (hst : some st ∈ ((cappedBucketTree (R := R) (C := C) r k clock).eval
      (fun q => (bilinear M q : ℝ))).support) :
    ∀ u, ∃ N, st.learned u = some N ∧ k ≤ N.card ∧ ∀ v ∈ N, M u v = true := by
  rw [cappedBucketTree, finiteCompleteCap_eval] at hst
  obtain ⟨out,hout,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hst
  by_cases hc : out.2 ≤ clock ∧ out.1.complete
  · simp only [ite_eq_left hc, Option.some.injEq] at he
    subst st
    exact learnBucketRounds_completed_correct M r k (clock+1) hout hc.2
  · simp only [ite_eq_right hc] at he
    cases he


/-- The public primitive-B clock is fixed before the hidden Boolean matrix. -/
def bucketClock (R C : Type) [Fintype R] [Fintype C] (k : ℕ) : ℕ :=
  hundredClock (bucketExpectedBound R C k)

/-- The finite primitive uses clock+1 rounds, so its own positive query progress
proves agreement with ordinary query-fuel truncation. -/
def bucketTree (r k : ℕ) : RTree (BipartiteQuery R C) ℝ
    (Option (BucketState R C)) (bucketClock R C k) :=
  cappedBucketTree r k (bucketClock R C k)

theorem bucketTree_every_oracle (r k : ℕ) (read : BipartiteQuery R C → ℝ)
    {out : Option (BucketState R C) × ℕ}
    (hout : out ∈ (RTree.run read (bucketTree (R := R) (C := C) r k)).support) :
    out.2 ≤ bucketClock R C k := RTree.cost_le _ _ hout

/-- The 1/100 clock debit is derived for the actual finite bucket program with
the fixed constant 2^40. There is no supplied expected-cost premise. -/
theorem bucketTree_abort_le (M : BooleanMatrix R C) (r k : ℕ)
    (hk : 10 ≤ k) (hkr : k ≤ r) (hs : 1 ≤ Fintype.card R) (ht : 1 ≤ Fintype.card C)
    (hdegree : ∀ u, r ≤ sampleCount (M u) Finset.univ ∧
      sampleCount (M u) Finset.univ ≤ 2*r) :
    mass ((bucketTree (R := R) (C := C) r k).eval (fun q => (bilinear M q : ℝ)))
      (fun out => out = none) ≤ (100 : ℝ≥0∞)⁻¹ := by
  apply cappedBucketTree_abort_le_of_expected
  exact (learnBucketRounds_expected_bound M r k _ hk hkr hs ht hdegree).trans
    (hundredClock_pays (bucketExpectedBound_nonneg (R := R) (C := C) k hs ht))

theorem bucketTree_true_neighbors (M : BooleanMatrix R C) (r k : ℕ)
    (st : BucketState R C)
    (hst : some st ∈ ((bucketTree (R := R) (C := C) r k).eval
      (fun q => (bilinear M q : ℝ))).support) :
    ∀ u, ∃ N, st.learned u = some N ∧ k ≤ N.card ∧ ∀ v ∈ N, M u v = true :=
  cappedBucketTree_true_neighbors M r k (bucketClock R C k) st hst

/-- An arbitrary bad-output event is transferred from the uncapped finite law
without conditioning the row distribution on global clock success. -/
theorem bucketTree_bad_le (M : BooleanMatrix R C) (r k : ℕ)
    (Bad : BucketState R C → Prop) :
    mass ((bucketTree (R := R) (C := C) r k).eval (fun q => (bilinear M q : ℝ)))
      (fun out => out.elim False Bad) ≤
    mass ((learnBucketRounds r k (bucketClock R C k+1)
      (BucketState.initial : BucketState R C)).eval (fun q => (bilinear M q : ℝ))) Bad :=
  finiteCompleteCap_bad_le _ _ BucketState.complete Bad _

end Bucket

section Recover

variable {V R C : Type} [Fintype V] [DecidableEq V]
  [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- The actual original-cut recovery program. It runs a finite approximation
and stops at the fixed linear query clock; its constructor has no hidden graph,
degree promise, successful-transcript selector or expected-cost argument. -/
def recoverTree (row : R ↪ V) (col : C ↪ V) (k : ℕ) :
    RTree (Finset V) ℝ (Option (BucketState R C)) (recoverClock R C k) :=
  finiteCompleteCap
    (simulateOriginal row col (recoverRounds (R := R) (C := C) k (recoverClock R C k+1)))
    (recoverClock R C k) BucketState.complete

/-- The literal every-answer bound includes inconsistent real cut replies. -/
theorem recoverTree_every_oracle (row : R ↪ V) (col : C ↪ V) (k : ℕ)
    (read : Finset V → ℝ) {out : Option (BucketState R C) × ℕ}
    (hout : out ∈ (RTree.run read (recoverTree row col k)).support) :
    out.2 ≤ recoveryHardCoefficient*k*(Fintype.card R+Fintype.card C) :=
  RTree.cost_le _ _ hout

theorem recoverClock_pays (k : ℕ) :
    ENNReal.ofReal ((recoveryCoefficient : ℝ)*k*(Fintype.card R+Fintype.card C)) ≤
      (recoverClock R C k+1 : ℝ≥0∞)*(100 : ℝ≥0∞)⁻¹ := by
  have hn : 100*(recoveryCoefficient*k*(Fintype.card R+Fintype.card C)) ≤
      recoverClock R C k := by
    unfold recoverClock recoveryHardCoefficient
    nlinarith
  have hnR : 100*((recoveryCoefficient : ℝ)*k*(Fintype.card R+Fintype.card C)) ≤
      (recoverClock R C k : ℝ) := by exact_mod_cast hn
  have hr : (recoveryCoefficient : ℝ)*k*(Fintype.card R+Fintype.card C) ≤
      ((recoverClock R C k : ℝ)+1)*(1/100 : ℝ) := by linarith
  have h100 : ENNReal.ofReal (1/100 : ℝ) = (100 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]
  calc
    ENNReal.ofReal ((recoveryCoefficient : ℝ)*k*(Fintype.card R+Fintype.card C)) ≤
        ENNReal.ofReal (((recoverClock R C k : ℝ)+1)*(1/100 : ℝ)) :=
      ENNReal.ofReal_le_ofReal hr
    _ = (recoverClock R C k+1 : ℝ≥0∞)*(100 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_mul (by positivity), h100,
        ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]

/-- The finite q+1 horizon is enough even after the exact three-cut
substitution. Thus the completion guard adds no unaccounted failure event. -/
theorem recoverTree_unfinished_cost (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (k : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees (graphMatrix row col G) u)
    {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run G.toWeighted.cut
      (simulateOriginal row col (recoverRounds (R := R) (C := C) k
        (recoverClock R C k+1)))).support)
    (hunfinished : ¬out.1.complete) : recoverClock R C k < out.2 := by
  rw [simulateOriginal_run] at hout
  have hread : originalBilinearRead row col G.toWeighted.cut =
      fun q => (bilinear (graphMatrix row col G) q : ℝ) := by
    funext q
    exact originalBilinearRead_honest row col hdisjoint G q
  rw [hread] at hout
  obtain ⟨next,hnext,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  have h := recoverRounds_unfinished_cost (graphMatrix row col G) k
    (recoverClock R C k+1) hk hdegree hnext hunfinished
  dsimp only
  omega

theorem recoverTree_same_clock (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (k : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees (graphMatrix row col G) u) :
    (recoverTree row col k).eval G.toWeighted.cut =
      ((simulateOriginal row col (recoverRounds (R := R) (C := C) k
        (recoverClock R C k+1))).truncate (recoverClock R C k)).eval G.toWeighted.cut := by
  apply finiteCompleteCap_same_clock
  intro out hout hunfinished
  exact recoverTree_unfinished_cost row col hdisjoint G k hk hdegree hout hunfinished

/-- The 1/100 abort debit follows from the proved finite expected query cost,
including the measured degree table and all three original cuts per count. -/
theorem recoverTree_abort_le (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (k : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees (graphMatrix row col G) u) :
    mass ((recoverTree row col k).eval G.toWeighted.cut) (fun out => out = none) ≤
      (100 : ℝ≥0∞)⁻¹ := by
  apply finiteCompleteCap_abort_le
  · intro out hout hunfinished
    exact recoverTree_unfinished_cost row col hdisjoint G k hk hdegree hout hunfinished
  · exact (recoverRounds_original_expected_bound row col hdisjoint G k _ hk hdegree).trans
      (recoverClock_pays (R := R) (C := C) k)

theorem recoverTree_true_neighbors (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (k : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees (graphMatrix row col G) u)
    (st : BucketState R C) (hst : some st ∈ ((recoverTree row col k).eval G.toWeighted.cut).support) :
    ∀ u, ∃ N, st.learned u = some N ∧ k ≤ N.card ∧
      ∀ c ∈ N, (G.w (row u) (col c) : ℕ) = 1 := by
  rw [recoverTree,finiteCompleteCap_eval] at hst
  obtain ⟨out,hout,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hst
  by_cases hc : out.2 ≤ recoverClock R C k ∧ out.1.complete
  · rw [ite_eq_left hc,Option.some.injEq] at he
    subst st
    rw [simulateOriginal_run] at hout
    have hread : originalBilinearRead row col G.toWeighted.cut =
        fun q => (bilinear (graphMatrix row col G) q : ℝ) := by
      funext q
      exact originalBilinearRead_honest row col hdisjoint G q
    rw [hread] at hout
    obtain ⟨next,hnext,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    have heval : next.1 ∈ ((recoverRounds (R := R) (C := C) k (recoverClock R C k+1)).eval
        (fun q => (bilinear (graphMatrix row col G) q : ℝ))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨next,hnext,rfl⟩
    intro u
    obtain ⟨N,hN,hsize,htrue⟩ := recoverRounds_true_neighbors
      (graphMatrix row col G) k _ hk hdegree heval hc.2 u
    exact ⟨N,hN,hsize,fun c hc => by simpa only [graphMatrix,decide_eq_true_eq] using htrue c hc⟩
  · simp only [ite_eq_right hc] at he
    cases he

/-- Transfer an unconditional bad-output event from the finite process.
This does not assert any row distribution conditioned on cap success. -/
theorem recoverTree_bad_le (row : R ↪ V) (col : C ↪ V)
    (k : ℕ) (read : Finset V → ℝ) (Bad : BucketState R C → Prop) :
    mass ((recoverTree row col k).eval read) (fun out => out.elim False Bad) ≤
      mass ((simulateOriginal row col (recoverRounds (R := R) (C := C) k
        (recoverClock R C k+1))).eval read) Bad :=
  finiteCompleteCap_bad_le _ _ BucketState.complete Bad _

/-- Actual original-query recovery retains the unconditional row-tail bound;
its separate abort debit is not used to condition or renormalize this law. -/
theorem recoverTree_row_ratio_tail (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (k : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees (graphMatrix row col G) u)
    (u : R) (Z : Finset C) (hZ : Z ⊆ rowNeighbors (graphMatrix row col G u))
    (eps : ℝ) (heps : 0 < eps) :
    mass ((recoverTree row col k).eval G.toWeighted.cut)
      (fun out => out.elim False (fun st => (st.learned u).elim False (fun S =>
        (Z.card : ℝ)/(rowNeighbors (graphMatrix row col G u)).card+eps <
          CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S))) ≤
      ENNReal.ofReal (((Z.card : ℝ)/(rowNeighbors (graphMatrix row col G u)).card)/k/eps^2) := by
  have h := recoverTree_bad_le row col k G.toWeighted.cut
    (fun st => (st.learned u).elim False (fun S =>
      (Z.card : ℝ)/(rowNeighbors (graphMatrix row col G u)).card+eps <
        CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S))
  rw [simulateOriginal_eval] at h
  have hread : originalBilinearRead row col G.toWeighted.cut =
      fun q => (bilinear (graphMatrix row col G) q : ℝ) := by
    funext q
    exact originalBilinearRead_honest row col hdisjoint G q
  rw [hread] at h
  exact h.trans (recoverRounds_row_ratio_tail (graphMatrix row col G) k _ hk hdegree u Z hZ eps heps)

theorem recoverTree_row_ratio_mean (row : R ↪ V) (col : C ↪ V)
    (hdisjoint : ∀ u v, row u ≠ col v) (G : SimpleInput V) (k : ℕ)
    (hk : 10 ≤ k) (hdegree : ∀ u, k ≤ fullDegrees (graphMatrix row col G) u)
    (u : R) (Z : Finset C) (hZ : Z ⊆ rowNeighbors (graphMatrix row col G u)) :
    expect ((recoverTree row col k).eval G.toWeighted.cut)
      (fun out => out.elim 0 (fun st => (st.learned u).elim 0 (fun S =>
        ENNReal.ofReal (CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S)))) ≤
      ENNReal.ofReal ((Z.card : ℝ)/(rowNeighbors (graphMatrix row col G u)).card) := by
  have h := finiteCompleteCap_expect_le
    (simulateOriginal row col (recoverRounds (R := R) (C := C) k (recoverClock R C k+1)))
    (recoverClock R C k) BucketState.complete G.toWeighted.cut
    (fun st => (st.learned u).elim 0 (fun S =>
      ENNReal.ofReal (CutQueryComplexity.StarContraction2022.Probability.crossingRatio Z S)))
  rw [simulateOriginal_eval] at h
  have hread : originalBilinearRead row col G.toWeighted.cut =
      fun q => (bilinear (graphMatrix row col G) q : ℝ) := by
    funext q
    exact originalBilinearRead_honest row col hdisjoint G q
  rw [hread] at h
  exact h.trans (recoverRounds_row_ratio_mean (graphMatrix row col G) k _ hk hdegree u Z hZ)

end Recover

end
end CutQueryComplexity.StarContraction2022.Recovery

#print axioms CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_eval
#print axioms CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_same_clock
#print axioms CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_every_oracle
#print axioms CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_abort_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_bad_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_failure_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.hundredClock_pays
#print axioms CutQueryComplexity.StarContraction2022.Recovery.cappedBucketTree_every_oracle
#print axioms CutQueryComplexity.StarContraction2022.Recovery.cappedBucketTree_same_clock
#print axioms CutQueryComplexity.StarContraction2022.Recovery.cappedBucketTree_true_neighbors

#print axioms CutQueryComplexity.StarContraction2022.Recovery.bucketTree_every_oracle
#print axioms CutQueryComplexity.StarContraction2022.Recovery.bucketTree_abort_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.bucketTree_true_neighbors
#print axioms CutQueryComplexity.StarContraction2022.Recovery.bucketTree_bad_le

#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverTree_every_oracle
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverClock_pays
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverTree_unfinished_cost
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverTree_same_clock
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverTree_abort_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverTree_true_neighbors
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverTree_bad_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_expect_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverTree_row_ratio_tail
#print axioms CutQueryComplexity.StarContraction2022.Recovery.recoverTree_row_ratio_mean
