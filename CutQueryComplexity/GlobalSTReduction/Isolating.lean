import CutQueryComplexity.GlobalSTReduction.Contractions

/-! # Isolating cuts from arbitrary minimum s-t shores (Phase 2)

The program is the existing call-language twin `isolatingValuesCall R`: one
group-separator call per bit of the terminal labels, intersection cells
(`isolatingCell`), one guarded source–proxy call per cell, and one value query
per returned shore. Nothing is canonicalized at run time.

* `holds_isolatingValuesCall`: if every call returns *some* minimum shore of its
  contracted instance and `|R| ≥ 2`, then for every `v ∈ R` the returned shore
  is a minimum isolating shore of `v` (`IsMinTraceCut G R {v}`) and the returned
  value is its exact cut value. An inclusion-minimal isolating optimum is used
  only as a witness inside the proof (it lies in the cell by uncrossing).
* `holds_isolatingValuesCall_any`: for arbitrary replies, every returned value
  is the oracle's answer on the returned shore.
* `cost_isolatingValuesCall`: charged cost at most
  `(⌈log₂ |R|⌉ + 2) Q |V| + |R|` for every history, using size regularity only
  at `|V|`; `calls_isolatingValuesCall`: at most `⌈log₂ |R|⌉ + |R|` calls.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction
noncomputable section
open scoped Classical BigOperators
open WeightedGraph GHReduction GHReduction.Randomized
open Certificate (bitClass)

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Correctness -/

/-- Minimum replies give minimum bit separators. -/
theorem holds_bitSeparatorCall (G : WeightedGraph V) (R : Finset V) :
    Holds G.cut (optReply G)
      (fun cuts : Fin (Nat.clog 2 R.card) → Finset V =>
        ∀ j, IsMinTraceCut G R (bitClass R j.val true) (cuts j))
      (CallProg.bitSeparatorCall R) := by
  apply holds_tableProgram
  intro j
  have h := holds_groupSeparatorCall G (Certificate.disjoint_bitClass R j.val)
  rwa [bitClass_union] at h

/-- Minimum replies give a minimum isolating shore for every terminal. -/
theorem holds_isolatingCall (G : WeightedGraph V) (R : Finset V) (hR : 2 ≤ R.card) :
    Holds G.cut (optReply G)
      (fun shores : R → Finset V => ∀ v : R, IsMinTraceCut G R {v.val} (shores v))
      (CallProg.isolatingCall R) := by
  rw [CallProg.isolatingCall, holds_bind]
  refine (holds_bitSeparatorCall G R).mono (fun cuts hcuts => ?_)
  refine holds_finiteTable (post := fun (v : R) X => IsMinTraceCut G R {v.val} X) (fun v => ?_)
  have hv := terminal_mem_cell G R cuts hcuts v.property
  have hp := isolatingCell_proper G R cuts hcuts hR v.property
  have hPR := isolatingCell_trace G R cuts hcuts v.property
  obtain ⟨C, hC⟩ := exists_canonicalTraceCut G (Finset.singleton_subset_iff.mpr v.property)
  have hCP := canonical_iso_subset_cell G R cuts hcuts v.property hC
  exact holds_isolatingLocalCall G hv hp hPR hC.1 hCP

/-- Minimum replies give, for every terminal, a minimum isolating shore and its value. -/
theorem holds_isolatingValuesCall (G : WeightedGraph V) (R : Finset V) (hR : 2 ≤ R.card) :
    Holds G.cut (optReply G)
      (fun table : R → Finset V × ℝ => ∀ v : R,
        IsMinTraceCut G R {v.val} (table v).1 ∧ (table v).2 = G.cut (table v).1)
      (CallProg.isolatingValuesCall R) := by
  rw [CallProg.isolatingValuesCall, holds_bind]
  refine (holds_isolatingCall G R hR).mono (fun shores hs => ?_)
  refine holds_finiteTable
    (post := fun (v : R) (c : Finset V × ℝ) => IsMinTraceCut G R {v.val} c.1 ∧ c.2 = G.cut c.1) (fun v => ?_)
  rw [holds_map]
  exact ⟨hs v, rfl⟩

/-- For arbitrary replies, every returned value is the oracle's answer on its shore. -/
theorem holds_isolatingValuesCall_any (read : Finset V → ℝ) (R : Finset V) :
    Holds read (anyReply V)
      (fun table : R → Finset V × ℝ => ∀ v : R, (table v).2 = read (table v).1)
      (CallProg.isolatingValuesCall R) := by
  rw [CallProg.isolatingValuesCall, holds_bind]
  refine (holds_true _).mono (fun shores _ => ?_)
  refine holds_finiteTable (post := fun (_ : R) (c : Finset V × ℝ) => c.2 = read c.1) (fun v => ?_)
  rw [holds_map]
  rfl

/-! ### Charges -/

theorem cost_bitSeparatorCall {Q : ℕ → ℕ} (R : Finset V)
    (hQ : SizeRegular (Fintype.card V) Q) :
    CostWithin Q (CallProg.bitSeparatorCall R) (Nat.clog 2 R.card * Q (Fintype.card V)) := by
  have h := within_tableProgram (c := fun _ : Fin (Nat.clog 2 R.card) => Q (Fintype.card V))
    (fun j => cost_groupSeparatorCall (Certificate.disjoint_bitClass R j.val) hQ)
  rw [CallProg.bitSeparatorCall]
  simpa using h

theorem calls_bitSeparatorCall (R : Finset V) :
    CallsWithin (CallProg.bitSeparatorCall R) (Nat.clog 2 R.card) := by
  have h := within_tableProgram (wq := 0) (wc := fun _ => 1)
    (c := fun _ : Fin (Nat.clog 2 R.card) => 1)
    (fun j => calls_groupSeparatorCall (bitClass R j.val true) (bitClass R j.val false))
  rw [CallProg.bitSeparatorCall]
  simpa using h

theorem cost_isolatingCall {Q : ℕ → ℕ} (R : Finset V) (hn : 0 < Fintype.card V)
    (hQ : SizeRegular (Fintype.card V) Q) :
    CostWithin Q (CallProg.isolatingCall R) ((Nat.clog 2 R.card + 2) * Q (Fintype.card V)) := by
  have h := within_bind (c₂ := 2 * Q (Fintype.card V)) (cost_bitSeparatorCall R hQ)
    (f := fun cuts => CallProg.finiteTable
      (fun v : R => CallProg.isolatingLocalCall (isolatingCell R cuts v.val) v.val))
    (fun cuts => (within_finiteTable (fun v : R => cost_isolatingLocalCall Q _ v.val)).mono (by
      calc
        _ = ∑ v ∈ R, localCharge Q (isolatingCell R cuts v) v := by
          rw [Finset.sum_coe_sort_eq_attach]
          exact Finset.sum_attach R (fun v => localCharge Q (isolatingCell R cuts v) v)
        _ ≤ _ := isolatingLocal_totalCharge R cuts hn hQ))
  rw [CallProg.isolatingCall]
  exact h.mono (by ring_nf; exact le_rfl)

theorem calls_isolatingCall (R : Finset V) :
    CallsWithin (CallProg.isolatingCall R) (Nat.clog 2 R.card + R.card) := by
  have h := within_bind (c₂ := R.card) (calls_bitSeparatorCall R)
    (f := fun cuts => CallProg.finiteTable
      (fun v : R => CallProg.isolatingLocalCall (isolatingCell R cuts v.val) v.val))
    (fun cuts => (within_finiteTable (c := fun _ : R => 1)
      (fun v : R => calls_isolatingLocalCall _ v.val)).mono (by simp))
  rw [CallProg.isolatingCall]
  exact h

/-- The old isolating budget, for every history, at size regularity `|V|`. -/
theorem cost_isolatingValuesCall {Q : ℕ → ℕ} (R : Finset V) (hn : 0 < Fintype.card V)
    (hQ : SizeRegular (Fintype.card V) Q) :
    CostWithin Q (CallProg.isolatingValuesCall R)
      ((Nat.clog 2 R.card + 2) * Q (Fintype.card V) + R.card) := by
  have h := within_bind (c₂ := R.card) (cost_isolatingCall R hn hQ)
    (f := fun shores => CallProg.finiteTable (fun v : R =>
      (CallProg.ask (shores v)).map (fun value => (shores v, value))))
    (fun shores => (within_finiteTable (c := fun _ : R => 1)
      (fun v : R => within_map _ (within_ask _))).mono (by simp))
  rw [CallProg.isolatingValuesCall]
  exact h

theorem calls_isolatingValuesCall (R : Finset V) :
    CallsWithin (CallProg.isolatingValuesCall R) (Nat.clog 2 R.card + R.card) := by
  have h := within_bind (c₂ := 0) (calls_isolatingCall R)
    (f := fun shores => CallProg.finiteTable (fun v : R =>
      (CallProg.ask (shores v)).map (fun value => (shores v, value))))
    (fun shores => (within_finiteTable (c := fun _ : R => 0)
      (fun v : R => within_map _ (within_ask _))).mono (by simp))
  rw [CallProg.isolatingValuesCall]
  simpa using h

end
end CutQueryComplexity.GlobalSTReduction
