import CutQueryComplexity.Probability.Truncation
import CutQueryComplexity.Probability.Expectation
import Mathlib.Tactic

/-! # Charged finite rounds and the actual original-query cap

Part of the parallel threshold certificate. No full parallel algorithm,
expected C_P bound, or endpoint is asserted in this module.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

variable {O : Type} {b : ℕ}

/-- Charge a dummy original query at the beginning of every nonterminal round.
Its answer is ignored. This also covers otherwise zero-query rounds. -/
def chargeRound (T : RTree (Finset V) ℝ O b) : RTree (Finset V) ℝ O (b + 1) :=
  RTree.query ∅ (fun _ => T)

theorem chargeRound_eval (T : RTree (Finset V) ℝ O b) (read : Finset V → ℝ) :
    (chargeRound T).eval read = T.eval read := by simp [chargeRound]

theorem chargeRound_run (T : RTree (Finset V) ℝ O b) (read : Finset V → ℝ) :
    RTree.run read (chargeRound T) =
      (RTree.run read T).map (fun p => (p.1, p.2 + 1)) := by simp [chargeRound]

theorem chargeRound_positive (T : RTree (Finset V) ℝ O b) (read : Finset V → ℝ)
    {p : O × ℕ} (hp : p ∈ (RTree.run read (chargeRound T)).support) : 1 ≤ p.2 := by
  rw [chargeRound_run] at hp
  obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  omega

/-- The exact padding charge is one, and must be included before fixing C_P. -/
theorem chargeRound_expectedQueries (T : RTree (Finset V) ℝ O b) (read : Finset V → ℝ) :
    (chargeRound T).expectedQueries read = T.expectedQueries read + 1 := by
  change CutQueryComplexity.Probability.expect (RTree.run read (chargeRound T))
      (fun p => (p.2 : ℝ≥0∞)) =
    CutQueryComplexity.Probability.expect (RTree.run read T) (fun p => (p.2 : ℝ≥0∞)) + 1
  rw [chargeRound_run, CutQueryComplexity.Probability.expect_map]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [CutQueryComplexity.Probability.expect_add, CutQueryComplexity.Probability.expect_const]

namespace FiniteQueryFuel

variable {S O : Type} {b : ℕ}

/-- Execute a public round constructor with a finite round counter. `inl`
halts and `inr` continues. Each executed round pays a real original cut query
before the round body, even when that body would use zero queries. `none`
means counter exhaustion, distinct from any terminal failure encoded in O.
This generic constructor does not assert progress of the parallel algorithm. -/
def rounds (next : S → RTree (Finset V) ℝ (O ⊕ S) b) :
    (T : ℕ) → S → RTree (Finset V) ℝ (Option O) (T * (b + 1))
  | 0, _ => RTree.pure (PMF.pure none)
  | T + 1, s => ((chargeRound (next s)).bind fun action => match action with
      | .inl o => RTree.pure (PMF.pure (some o))
      | .inr t => rounds next T t).cast (by rw [Nat.succ_mul]; omega)

/-- Exhausting T rounds has spent at least T actual original queries on
every oracle path. No expected-cost or progress premise is involved. -/
theorem exhausted_cost (next : S → RTree (Finset V) ℝ (O ⊕ S) b)
    (T : ℕ) (s : S) (read : Finset V → ℝ) {out : Option O × ℕ}
    (hout : out ∈ (RTree.run read (rounds next T s)).support)
    (hex : out.1 = none) : T ≤ out.2 := by
  induction T generalizing s out with
  | zero => exact Nat.zero_le _
  | succ T ih =>
      rw [rounds, RTree.run_cast, RTree.run_bind] at hout
      obtain ⟨⟨action, c⟩, hfirst, htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨⟨res, d⟩, hrest, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htail
      have hpos : 1 ≤ c := chargeRound_positive (next s) read hfirst
      cases action with
      | inl o =>
          have he : (res, d) = (some o, 0) := by
            simpa only [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] using hrest
          have hr := congrArg Prod.fst he
          simp only [Prod.fst] at hr hex
          rw [hex] at hr
          cases hr
      | inr t =>
          have ht : T ≤ d := ih t hrest hex
          change T + 1 ≤ c + d
          omega

/-- The cap chooses its round counter as cap+1. Both parameters are public;
the resulting tree has exactly the advertised worst-case query index. -/
def capped (next : S → RTree (Finset V) ℝ (O ⊕ S) b) (cap : ℕ) (s : S) :
    RTree (Finset V) ℝ (Option O) cap :=
  ((rounds next (cap + 1) s).truncate cap).map Option.join

theorem capped_every_oracle (next : S → RTree (Finset V) ℝ (O ⊕ S) b)
    (cap : ℕ) (s : S) (read : Finset V → ℝ) {out : Option O × ℕ}
    (hout : out ∈ (RTree.run read (capped next cap s)).support) : out.2 ≤ cap :=
  RTree.cost_le _ _ hout

theorem capped_eval (next : S → RTree (Finset V) ℝ (O ⊕ S) b)
    (cap : ℕ) (s : S) (read : Finset V → ℝ) :
    (capped next cap s).eval read =
      (RTree.run read (rounds next (cap + 1) s)).map
        (fun out => if out.2 ≤ cap then out.1 else none) := by
  rw [capped, RTree.eval_map, RTree.eval_truncate, PMF.map_comp]
  congr 1
  funext out
  by_cases hc : out.2 ≤ cap <;> simp [Function.comp_def, hc]

/-- The finite round counter introduces no additional abort event beneath
the query cap: exhaustion itself costs at least cap+1 queries. Thus abort
is exactly the actual query-cost tail of the same finite program. -/
theorem capped_abort (next : S → RTree (Finset V) ℝ (O ⊕ S) b)
    (cap : ℕ) (s : S) (read : Finset V → ℝ) :
    CutQueryComplexity.Probability.mass ((capped next cap s).eval read) (fun o => o = none) =
      CutQueryComplexity.Probability.mass (RTree.run read (rounds next (cap + 1) s))
        (fun out => cap < out.2) := by
  rw [capped_eval, CutQueryComplexity.Probability.mass_map,
    CutQueryComplexity.Probability.mass_eq_tsum,
    CutQueryComplexity.Probability.mass_eq_tsum]
  apply tsum_congr
  intro out
  by_cases hout : out ∈ (RTree.run read (rounds next (cap + 1) s)).support
  · by_cases hc : out.2 ≤ cap
    · have hnone : out.1 ≠ none := by
        intro he
        have hh := exhausted_cost next (cap + 1) s read hout he
        omega
      simp only [if_pos hc, hnone, if_false, Nat.not_lt.mpr hc]
    · simp only [if_neg hc, Nat.lt_of_not_ge hc, if_true]
  · have hz : RTree.run read (rounds next (cap + 1) s) out = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hout
    simp only [hz, ite_self]

end FiniteQueryFuel


#print axioms chargeRound_eval
#print axioms chargeRound_positive
#print axioms chargeRound_expectedQueries
#print axioms FiniteQueryFuel.exhausted_cost
#print axioms FiniteQueryFuel.capped_every_oracle
#print axioms FiniteQueryFuel.capped_eval
#print axioms FiniteQueryFuel.capped_abort

end
end CutQueryComplexity.StarContraction2022.Certificates
