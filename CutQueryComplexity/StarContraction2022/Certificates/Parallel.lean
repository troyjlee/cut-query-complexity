import CutQueryComplexity.StarContraction2022.Certificates.Parallel.Charge
import CutQueryComplexity.StarContraction2022.Common.Threshold

/-! # Parallel threshold certificate — final assembly

Actual joint neighbor recovery, finite halving, explicit exhaustion charges,
and sharp expected phase charges live in Mixed, Halving, and Charge.

This module supplies the public geometric phase constructor, retained-credit
sum, finishing branch, and finite-core coefficient 2^60. The
zero-error completion charges its deterministic fallback to the already-paid
parallel tail, giving C_P = 2^61 and an exact cap of that same total program.
No P/cost/termination oracle is assumed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical ENNReal

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
variable {π : PublicQuotient V Q} {r : ℕ}

namespace ParallelState

/-- One absolute constant for the large-input parallel construction. The
constructor and its query proof below use the same finite recovery fuel. -/
def parallelConstant : ℕ := 1152921504606846976

/-- The public power guard pays for the true number of degree buckets,
including the low bucket and both rounding terms. -/
theorem parallel_slots_at_scale (n q scale : ℕ) (hn : 1 ≤ n)
    (hln : 1000 ≤ Real.log (n : ℝ))
    (hpower : (Real.log (n : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤ (q : ℝ))
    (hscale : (q : ℝ) / Real.log (n : ℝ) ≤ (scale : ℝ)) :
    Fintype.card (Option (Fin (highBucketCount n))) ≤ scale := by
  have hl : 0 < Real.log (n : ℝ) := by linarith
  have ht : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht1 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbase : Real.log (n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ ht).mpr
    exact mul_le_of_le_one_right hl.le ht1
  have hp : (Real.log (n : ℝ)) ^ ((5 : ℝ) / 2) ≤ (q : ℝ) :=
    (Real.rpow_le_rpow hl.le hbase (by norm_num)).trans hpower
  have hsqrt : 3 ≤ Real.sqrt (Real.log (n : ℝ)) := by
    have hs := Real.sq_sqrt hl.le
    have hs0 := Real.sqrt_nonneg (Real.log (n : ℝ))
    nlinarith
  have he : (Real.log (n : ℝ)) ^ ((5 : ℝ) / 2) =
      (Real.log (n : ℝ)) ^ 2 * Real.sqrt (Real.log (n : ℝ)) := by
    rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num,
      Real.rpow_add hl, Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [he] at hp
  have hq : 3 * (Real.log (n : ℝ)) ^ 2 ≤ (q : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (sq_nonneg (Real.log (n : ℝ)))]
  have hthree : 3 * Real.log (n : ℝ) ≤ (q : ℝ) / Real.log (n : ℝ) := by
    apply (le_div_iff₀ hl).mpr
    nlinarith
  have hc := Schedule.clog_le_twice_log_add_one n hn
  have hslots : (Fintype.card (Option (Fin (highBucketCount n))) : ℝ) ≤
      3 * Real.log (n : ℝ) := by
    rw [Fintype.card_option, Fintype.card_fin]
    unfold highBucketCount
    push_cast
    linarith
  exact_mod_cast hslots.trans (hthree.trans hscale)

/-- A numerical bound on the actual mixed-stage expression. Its denominator
contains every implemented degree bucket; no idealized bucket count appears. -/
theorem mixedStageBound_large (n q scale : ℕ) (hq : 2 ≤ q) (hqn : q ≤ n)
    (hln : 1000 ≤ Real.log (n : ℝ))
    (hpower : (Real.log (n : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤ (q : ℝ))
    (hscale : (q : ℝ) / Real.log (n : ℝ) ≤ (scale : ℝ)) :
    0 ≤ mixedStageBound n scale ∧ mixedStageBound n scale ≤
      81 * (mixedBucketConstant : ℝ) *
        ((scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ)) := by
  let J := Fintype.card (Option (Fin (highBucketCount n)))
  have hn : 2 ≤ n := hq.trans hqn
  have hl : 0 < Real.log (n : ℝ) := by linarith
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hql : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hJ : (0 : ℝ) < J := by
    simp only [J, Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    positivity
  have hslots : (J : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have hc := Schedule.clog_le_twice_log_add_one n (by omega)
    dsimp only [J]
    rw [Fintype.card_option, Fintype.card_fin]
    unfold highBucketCount
    push_cast
    linarith
  have hden := phase_denominator_slots (q : ℝ) (Real.log (n : ℝ)) (scale : ℝ) J
    (by linarith) hl hJ hslots hscale (parallel_power_logs n q hn hpower)
    (parallel_guard_log_reserve n q hln hpower)
  have hd : 0 < Real.log (2 * (scale : ℝ) / J) :=
    (div_pos hql (by norm_num)).trans_le hden
  have hlog : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hnR)]
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog0 : 0 ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_nonneg
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlogqn : Real.log (q : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hqn)
  have hs : (scale : ℝ) ≤ (scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ) := by
    apply (le_div_iff₀ hql).mpr
    exact mul_le_mul_of_nonneg_left hlogqn (Nat.cast_nonneg _)
  have hterm : 4 * (scale : ℝ) * Real.log (2 * (n : ℝ)) /
      Real.log (2 * (scale : ℝ) / J) ≤
        80 * ((scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ)) := by
    calc
      _ ≤ 8 * (scale : ℝ) * Real.log (n : ℝ) /
          Real.log (2 * (scale : ℝ) / J) := by
        apply div_le_div_of_nonneg_right _ hd.le
        nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4 * (scale : ℝ) by positivity)]
      _ ≤ 8 * (scale : ℝ) * Real.log (n : ℝ) / (Real.log (q : ℝ) / 10) :=
        div_le_div_of_nonneg_left (by positivity) (div_pos hql (by norm_num)) hden
      _ = _ := by field_simp; ring
  constructor
  · unfold mixedStageBound
    change 0 ≤ (mixedBucketConstant : ℝ) *
      ((scale : ℝ) + 4 * scale * Real.log (2 * (n : ℝ)) /
        Real.log (2 * (scale : ℝ) / J))
    positivity
  · unfold mixedStageBound
    change (mixedBucketConstant : ℝ) *
      ((scale : ℝ) + 4 * scale * Real.log (2 * (n : ℝ)) /
        Real.log (2 * (scale : ℝ) / J)) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hs hterm)
      (Nat.cast_nonneg mixedBucketConstant : (0 : ℝ) ≤ mixedBucketConstant)]

/-- The unit padding query and both representative scans/counts fit the
same scale envelope as the genuinely joint neighbor recovery. -/
theorem phaseRoundBound_large (n q scale : ℕ) (hq : 2 ≤ q) (hqn : q ≤ n)
    (hln : 1000 ≤ Real.log (n : ℝ))
    (hpower : (Real.log (n : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤ (q : ℝ))
    (hscale : (q : ℝ) / Real.log (n : ℝ) ≤ (scale : ℝ)) :
    phaseRoundBound n scale ≤ ENNReal.ofReal
      (36028797018963968 * ((scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ))) := by
  have hl : 0 < Real.log (n : ℝ) := by linarith
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hql : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hs0 : (0 : ℝ) < scale := (div_pos (by linarith : (0 : ℝ) < q) hl).trans_le hscale
  have hs1 : (1 : ℝ) ≤ scale := by
    have : 0 < scale := by exact_mod_cast hs0
    exact_mod_cast (show 1 ≤ scale by omega)
  have hlogqn := Real.log_le_log (by linarith : (0 : ℝ) < q)
    (show (q : ℝ) ≤ n by exact_mod_cast hqn)
  have hs : (scale : ℝ) ≤ (scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ) := by
    apply (le_div_iff₀ hql).mpr
    exact mul_le_mul_of_nonneg_left hlogqn hs0.le
  obtain ⟨hm0, hm⟩ := mixedStageBound_large n q scale hq hqn hln hpower hscale
  have he : ENNReal.ofReal (1 + 6 * (scale : ℝ) + mixedStageBound n scale) =
      phaseRoundBound n scale := by
    rw [ENNReal.ofReal_add (by positivity) hm0,
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num)]
    norm_num [phaseRoundBound]
  rw [← he]
  apply ENNReal.ofReal_le_ofReal
  norm_num [mixedBucketConstant] at hm
  nlinarith

/-- A public upper index for the finite implementation, separate from its
much smaller expected query count. No hidden graph occurs in this index. -/
def geometricBudget (V Q : Type) [Fintype V] [Fintype Q]
    (r cap steps : ℕ) : ℕ :=
  steps * ((cap + 1) * (scanFairRoundBudget V Q (cap + 1) + 1)) +
    (r * Fintype.card Q + 1) * finishStepBudget V

/-- Run actual parallel phases at successively halved public scales. The
low-scale branch completes the current residual forests. Every recovery and
phase horizon is cap+1; exhaustion is explicitly absent output. -/
def geometricPhases (hr : 0 < r) (cap : ℕ) : (steps scale : ℕ) →
    ParallelState π r → RTree (Finset V) ℝ (Option (WeightedGraph Q))
      (geometricBudget V Q r cap steps)
  | 0, _, s => (RTree.ofDeterministic (s.finishProgram hr)).cast (by
      simp only [geometricBudget, Nat.zero_mul, Nat.zero_add])
  | steps + 1, scale, s =>
      if (scale : ℝ) ≤ (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ) then
        (RTree.ofDeterministic (s.finishProgram hr)).weaken (by
          unfold geometricBudget; omega)
      else ((s.halvingPhase hr scale cap).bind fun out => match out with
        | none => RTree.pure (PMF.pure none)
        | some t => geometricPhases hr cap steps (scale / 2) t).cast (by
          unfold geometricBudget
          ring)

/-- Every successful output of the actual multi-phase program is an exact
threshold certificate. Finite recovery failure is kept separate. -/
theorem geometricPhases_success (hr : 0 < r) (cap steps scale : ℕ)
    (s : ParallelState π r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false)
    {H : WeightedGraph Q}
    (hH : some H ∈ ((geometricPhases hr cap steps scale s).eval G.toWeighted.cut).support) :
    IsThresholdCertificate r (π.graph G.toWeighted) H := by
  induction steps generalizing scale s H with
  | zero =>
      rw [geometricPhases, RTree.eval_cast, RTree.eval_ofDeterministic] at hH
      obtain ⟨K, he, hK⟩ := s.finishProgram_correct hr G hs hl hi hf
      rw [he] at hH
      have hHK : H = K := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp hH)
      simpa only [hHK] using hK
  | succ steps ih =>
      rw [geometricPhases] at hH
      by_cases hstop : (scale : ℝ) ≤
          (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ)
      · rw [if_pos hstop, RTree.eval_weaken, RTree.eval_ofDeterministic] at hH
        obtain ⟨K, he, hK⟩ := s.finishProgram_correct hr G hs hl hi hf
        rw [he] at hH
        have hHK : H = K := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp hH)
        simpa only [hHK] using hK
      · rw [if_neg hstop, RTree.eval_cast, RTree.eval_bind] at hH
        obtain ⟨out, hout, htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp hH
        cases out with
        | none => simp only [RTree.eval_pure, PMF.mem_support_pure_iff, reduceCtorEq] at htail
        | some t =>
            obtain ⟨htl, hts, hti, htcount⟩ := s.halvingPhase_success hr hl G hs hi scale cap hout
            have htf : t.failed = false := (s.halvingPhase_failed hr hl G hs hi scale cap hout).trans hf
            exact ih (scale / 2) t hts htl hti htf htail

/-- A failed honest multi-phase run has already exceeded the chosen cap.
This includes every internal finite B exhaustion and phase exhaustion. -/
theorem geometricPhases_none_cost (hr : 0 < r) (cap steps scale : ℕ)
    (s : ParallelState π r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false)
    (cost : ℕ)
    (hout : (none, cost) ∈
      (RTree.run G.toWeighted.cut (geometricPhases hr cap steps scale s)).support) :
    cap < cost := by
  induction steps generalizing scale s cost with
  | zero =>
      rw [geometricPhases, RTree.run_cast, RTree.run_ofDeterministic] at hout
      have he := congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hout)
      change none = (s.finishProgram hr).eval G.toWeighted.cut at he
      obtain ⟨H, hH, _⟩ := s.finishProgram_correct hr G hs hl hi hf
      rw [hH] at he
      cases he
  | succ steps ih =>
      rw [geometricPhases] at hout
      by_cases hstop : (scale : ℝ) ≤
          (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ)
      · rw [if_pos hstop, RTree.run_weaken, RTree.run_ofDeterministic] at hout
        have he := congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hout)
        change none = (s.finishProgram hr).eval G.toWeighted.cut at he
        obtain ⟨H, hH, _⟩ := s.finishProgram_correct hr G hs hl hi hf
        rw [hH] at he
        cases he
      · rw [if_neg hstop, RTree.run_cast, RTree.run_bind] at hout
        obtain ⟨⟨out, c⟩, hfirst, htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
        obtain ⟨⟨res, d⟩, hlast, he⟩ := (PMF.mem_support_map_iff _ _ _).mp htail
        have heres : res = none := congrArg Prod.fst he
        have hecost : c + d = cost := congrArg Prod.snd he
        subst res
        cases out with
        | none =>
            have hc := s.halvingPhase_none_cost hr hl G hs hi scale cap c hfirst
            omega
        | some t =>
            have heval : some t ∈ ((s.halvingPhase hr scale cap).eval G.toWeighted.cut).support := by
              rw [RTree.eval]
              exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(some t, c), hfirst, rfl⟩
            obtain ⟨htl, hts, hti, htcount⟩ := s.halvingPhase_success hr hl G hs hi scale cap heval
            have htf : t.failed = false :=
              (s.halvingPhase_failed hr hl G hs hi scale cap heval).trans hf
            have hd := ih (scale / 2) t hts htl hti htf d hlast
            omega

/-- Cap the same finite geometric program at the number of original cuts,
and flatten its explicit internal failure. No second failure coin is added. -/
def cappedGeometric (hr : 0 < r) (cap steps scale : ℕ) (s : ParallelState π r) :
    RTree (Finset V) ℝ (Option (WeightedGraph Q)) cap :=
  ((geometricPhases hr cap steps scale s).truncate cap).map Option.join

theorem cappedGeometric_eval (hr : 0 < r) (cap steps scale : ℕ)
    (s : ParallelState π r) (read : Finset V → ℝ) :
    (cappedGeometric hr cap steps scale s).eval read =
      (RTree.run read (geometricPhases hr cap steps scale s)).map
        (fun out => if out.2 ≤ cap then out.1 else none) := by
  rw [cappedGeometric, RTree.eval_map, RTree.eval_truncate, PMF.map_comp]
  congr 1
  funext out
  by_cases hc : out.2 ≤ cap <;> simp [Function.comp_def, hc]

/-- Worst-case costs are bounded on every oracle, without honesty premises. -/
theorem cappedGeometric_every_oracle (hr : 0 < r) (cap steps scale : ℕ)
    (s : ParallelState π r) (read : Finset V → ℝ) {out : Option (WeightedGraph Q) × ℕ}
    (hout : out ∈ (RTree.run read (cappedGeometric hr cap steps scale s)).support) :
    out.2 ≤ cap := RTree.cost_le _ _ hout

theorem cappedGeometric_success (hr : 0 < r) (cap steps scale : ℕ)
    (s : ParallelState π r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false)
    {H : WeightedGraph Q}
    (hH : some H ∈ ((cappedGeometric hr cap steps scale s).eval G.toWeighted.cut).support) :
    IsThresholdCertificate r (π.graph G.toWeighted) H := by
  rw [cappedGeometric_eval] at hH
  obtain ⟨out, hout, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hH
  by_cases hc : out.2 ≤ cap
  · rw [if_pos hc] at he
    apply geometricPhases_success hr cap steps scale s G hs hl hi hf
    rw [RTree.eval]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨out, hout, he⟩
  · rw [if_neg hc] at he
    cases he

/-- Exact honest abort event: the query tail of this very same finite
program. Its finite internal fuel contributes no separate error term. -/
theorem cappedGeometric_abort (hr : 0 < r) (cap steps scale : ℕ)
    (s : ParallelState π r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false) :
    CutQueryComplexity.Probability.mass
      ((cappedGeometric hr cap steps scale s).eval G.toWeighted.cut) (fun out => out = none) =
    CutQueryComplexity.Probability.mass
      (RTree.run G.toWeighted.cut (geometricPhases hr cap steps scale s))
      (fun out => cap < out.2) := by
  rw [cappedGeometric_eval, CutQueryComplexity.Probability.mass_map,
    CutQueryComplexity.Probability.mass_eq_tsum, CutQueryComplexity.Probability.mass_eq_tsum]
  apply tsum_congr
  intro out
  by_cases hout : out ∈
      (RTree.run G.toWeighted.cut (geometricPhases hr cap steps scale s)).support
  · by_cases hc : out.2 ≤ cap
    · have hnone : out.1 ≠ none := by
        intro he
        have hrun : (none, out.2) ∈
            (RTree.run G.toWeighted.cut (geometricPhases hr cap steps scale s)).support := by
          simpa only [← he, Prod.eta] using hout
        have hh := geometricPhases_none_cost hr cap steps scale s G hs hl hi hf out.2 hrun
        omega
      simp only [if_pos hc, hnone, if_false, Nat.not_lt.mpr hc]
    · simp only [if_neg hc, Nat.lt_of_not_ge hc, if_true]
  · have hz : RTree.run G.toWeighted.cut (geometricPhases hr cap steps scale s) out = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hout
    simp only [hz, ite_self]

/-- The geometric sum is paid once over all phases, rather than once per
layer or once per row bucket. -/
def geometricCharge (n q r scale : ℕ) : ℝ :=
  576460752303423488 * r * scale * Real.log (n : ℝ) / Real.log (q : ℝ)

def finishingCharge (n q r : ℕ) : ℝ :=
  18 * ((n : ℝ) + r * q * Real.log (n : ℝ) / Real.log (q : ℝ))

theorem geometricCharge_nonneg (n q r scale : ℕ) (hq : 2 ≤ q) (hqn : q ≤ n) :
    0 ≤ geometricCharge n q r scale := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  unfold geometricCharge
  have hln := (Real.log_pos hn1).le
  exact div_nonneg (by positivity) (Real.log_pos hq1).le

theorem finishingCharge_nonneg (n q r : ℕ) (hq : 2 ≤ q) (hqn : q ≤ n) :
    0 ≤ finishingCharge n q r := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  unfold finishingCharge
  have hln := (Real.log_pos hn1).le
  have hlq := (Real.log_pos hq1).le
  positivity

/-- Exact constant arithmetic for one halving plus the remaining geometric
sum. This is a numerical lemma applied to the proved actual phase charge. -/
theorem geometricCharge_step (n q r scale : ℕ) (hq : 2 ≤ q) (hqn : q ≤ n)
    (hln : 1000 ≤ Real.log (n : ℝ))
    (hpower : (Real.log (n : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤ (q : ℝ))
    (hscale : (q : ℝ) / Real.log (n : ℝ) ≤ (scale : ℝ)) :
    phaseRoundBound n scale * (8 * (r : ℝ≥0∞)) +
      ENNReal.ofReal (geometricCharge n q r (scale / 2) + finishingCharge n q r) ≤
      ENNReal.ofReal (geometricCharge n q r scale + finishingCharge n q r) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hql : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hl : 0 < Real.log (n : ℝ) := by linarith
  have hx : 0 ≤ (scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ) := by positivity
  have hhalf : 2 * ((scale / 2 : ℕ) : ℝ) ≤ scale := by
    exact_mod_cast (show 2 * (scale / 2) ≤ scale by omega)
  have hhalfCharge : geometricCharge n q r (scale / 2) ≤
      288230376151711744 * r * scale * Real.log (n : ℝ) / Real.log (q : ℝ) := by
    unfold geometricCharge
    apply (div_le_div_iff_of_pos_right hql).mpr
    nlinarith [mul_le_mul_of_nonneg_right hhalf
      (show 0 ≤ 288230376151711744 * (r : ℝ) * Real.log (n : ℝ) by positivity)]
  have hnum : (36028797018963968 *
      ((scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ))) * (8 * (r : ℝ)) +
      (geometricCharge n q r (scale / 2) + finishingCharge n q r) ≤
      geometricCharge n q r scale + finishingCharge n q r := by
    calc
      _ ≤ (36028797018963968 *
          ((scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ))) * (8 * (r : ℝ)) +
          (288230376151711744 * r * scale * Real.log (n : ℝ) / Real.log (q : ℝ) +
            finishingCharge n q r) :=
        add_le_add le_rfl (add_le_add hhalfCharge le_rfl)
      _ = _ := by unfold geometricCharge; ring
  have hmain := phaseRoundBound_large n q scale hq hqn hln hpower hscale
  have ht0 := add_nonneg (geometricCharge_nonneg n q r (scale / 2) hq hqn)
    (finishingCharge_nonneg n q r hq hqn)
  calc
    _ ≤ ENNReal.ofReal (36028797018963968 *
          ((scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ))) * (8 * (r : ℝ≥0∞)) +
        ENNReal.ofReal (geometricCharge n q r (scale / 2) + finishingCharge n q r) :=
      add_le_add (mul_le_mul_left hmain _) le_rfl
    _ = ENNReal.ofReal ((36028797018963968 *
          ((scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ))) * (8 * (r : ℝ)) +
        (geometricCharge n q r (scale / 2) + finishingCharge n q r)) := by
      rw [ENNReal.ofReal_add
        (p := (36028797018963968 *
          ((scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ))) * (8 * (r : ℝ)))
        (by positivity) ht0]
      congr 1
      symm
      rw [ENNReal.ofReal_mul
        (p := 36028797018963968 *
          ((scale : ℝ) * Real.log (n : ℝ) / Real.log (q : ℝ))) (by positivity)]
      congr 1
      norm_num [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hnum

theorem finishProgram_expected_at_scale (hr : 0 < r) (s : ParallelState π r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false)
    (hq : 2 ≤ Fintype.card Q) (hln : 1000 ≤ Real.log (Fintype.card V : ℝ))
    (hstop : ((s.liveBlocks (lastIndex hr)).card : ℝ) ≤
      (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ)) :
    (RTree.ofDeterministic (s.finishProgram hr)).expectedQueries G.toWeighted.cut ≤
      ENNReal.ofReal (finishingCharge (Fintype.card V) (Fintype.card Q) r) := by
  have hn : 1 ≤ Fintype.card V := by have := π.card_le; omega
  have hb := s.finishProgram_cost_at_scale hr G hs hl hi hf hn (by linarith)
    hq π.card_le hstop
  change CutQueryComplexity.Probability.expect
    (RTree.run G.toWeighted.cut (RTree.ofDeterministic (s.finishProgram hr)))
      (fun out => (out.2 : ℝ≥0∞)) ≤ _
  rw [RTree.run_ofDeterministic, CutQueryComplexity.Probability.expect_pure]
  simpa only [finishingCharge, ENNReal.ofReal_natCast, DTree.cost] using
    ENNReal.ofReal_le_ofReal hb

/-- The actual finite sequence has a cap-uniform expected cost. Retirement
credit telescopes across phases, and the natural scales contribute their
geometric sum. All drift, recovery and degree hypotheses are discharged by
the concrete phase theorems. -/
theorem geometricPhases_expected (hr : 0 < r) (cap steps scale : ℕ)
    (s : ParallelState π r) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) (hl : s.Laminar)
    (hi : s.InactiveSound hr G.toWeighted) (hf : s.failed = false)
    (hq : 2 ≤ Fintype.card Q) (hln : 1000 ≤ Real.log (Fintype.card V : ℝ))
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ))
    (hcount : (s.liveBlocks (lastIndex hr)).card ≤ scale)
    (hdepth : scale < 2 ^ steps) :
    (geometricPhases hr cap steps scale s).expectedQueries G.toWeighted.cut ≤
      ENNReal.ofReal (geometricCharge (Fintype.card V) (Fintype.card Q) r scale +
        finishingCharge (Fintype.card V) (Fintype.card Q) r) +
          3 * (retirementCredit (some s) : ℝ≥0∞) := by
  have hn : 1 ≤ Fintype.card V := by have := π.card_le; omega
  have hlpos : 0 < Real.log (Fintype.card V : ℝ) := by linarith
  have hstop0 : (0 : ℝ) ≤ (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ) := by
    positivity
  induction steps generalizing scale s with
  | zero =>
      have he : scale = 0 := by simp only [pow_zero] at hdepth; omega
      have hstop : ((s.liveBlocks (lastIndex hr)).card : ℝ) ≤
          (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ) := by
        have hz : (s.liveBlocks (lastIndex hr)).card = 0 := by omega
        simpa only [hz, Nat.cast_zero] using hstop0
      rw [geometricPhases, cast_expected]
      apply (s.finishProgram_expected_at_scale hr G hs hl hi hf hq hln hstop).trans
      apply le_add_of_le_left
      apply ENNReal.ofReal_le_ofReal
      have hh := geometricCharge_nonneg (Fintype.card V) (Fintype.card Q) r scale hq π.card_le
      linarith
  | succ steps ih =>
      rw [geometricPhases]
      by_cases hstop : (scale : ℝ) ≤
          (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ)
      · rw [if_pos hstop, weaken_expected]
        have hstop' : ((s.liveBlocks (lastIndex hr)).card : ℝ) ≤
            (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ) :=
          (show ((s.liveBlocks (lastIndex hr)).card : ℝ) ≤ scale by exact_mod_cast hcount).trans hstop
        apply (s.finishProgram_expected_at_scale hr G hs hl hi hf hq hln hstop').trans
        apply le_add_of_le_left
        apply ENNReal.ofReal_le_ofReal
        have hh := geometricCharge_nonneg (Fintype.card V) (Fintype.card Q) r scale hq π.card_le
        linarith
      · rw [if_neg hstop, cast_expected, bind_expected]
        have hscale : (Fintype.card Q : ℝ) / Real.log (Fintype.card V : ℝ) ≤ scale :=
          (lt_of_not_ge hstop).le
        have hscale0 : 0 < scale := by
          have : (0 : ℝ) < scale := hstop0.trans_lt (lt_of_not_ge hstop)
          exact_mod_cast this
        have hslots := parallel_slots_at_scale (Fintype.card V) (Fintype.card Q) scale
          hn hln hpower hscale
        have hdepth' : scale / 2 < 2 ^ steps := by
          rw [pow_succ] at hdepth
          omega
        let K : ℝ≥0∞ := ENNReal.ofReal
          (geometricCharge (Fintype.card V) (Fintype.card Q) r (scale / 2) +
            finishingCharge (Fintype.card V) (Fintype.card Q) r)
        have htail : CutQueryComplexity.Probability.expect
            ((s.halvingPhase hr scale cap).eval G.toWeighted.cut)
            (fun out => (match out with
              | none => RTree.pure (PMF.pure none)
              | some t => geometricPhases hr cap steps (scale / 2) t).expectedQueries G.toWeighted.cut) ≤
            K + 3 * CutQueryComplexity.Probability.expect
              ((s.halvingPhase hr scale cap).eval G.toWeighted.cut)
              (fun out => (retirementCredit out : ℝ≥0∞)) := by
          calc
            _ ≤ CutQueryComplexity.Probability.expect
                ((s.halvingPhase hr scale cap).eval G.toWeighted.cut)
                (fun out => K + 3 * (retirementCredit out : ℝ≥0∞)) := by
              apply CutQueryComplexity.Probability.expect_mono_on_support
              intro out hout
              cases out with
              | none => rw [pure_expected]; exact bot_le
              | some t =>
                  obtain ⟨htl, hts, hti, htc⟩ := s.halvingPhase_success hr hl G hs hi scale cap hout
                  have htf := (s.halvingPhase_failed hr hl G hs hi scale cap hout).trans hf
                  exact ih (scale / 2) t hts htl hti htf htc hdepth'
            _ = _ := by
              rw [CutQueryComplexity.Probability.expect_add,
                CutQueryComplexity.Probability.expect_const,
                CutQueryComplexity.Probability.expect_const_mul]
        have hp := s.halvingPhase_retirement_charge hr hl G hs hi scale cap hscale0 hn hcount hslots
        have hc := geometricCharge_step (Fintype.card V) (Fintype.card Q) r scale
          hq π.card_le hln hpower hscale
        calc
          _ ≤ (s.halvingPhase hr scale cap).expectedQueries G.toWeighted.cut +
              (K + 3 * CutQueryComplexity.Probability.expect
                ((s.halvingPhase hr scale cap).eval G.toWeighted.cut)
                (fun out => (retirementCredit out : ℝ≥0∞))) := add_le_add le_rfl htail
          _ = ((s.halvingPhase hr scale cap).expectedQueries G.toWeighted.cut +
              3 * CutQueryComplexity.Probability.expect
                ((s.halvingPhase hr scale cap).eval G.toWeighted.cut)
                (fun out => (retirementCredit out : ℝ≥0∞))) + K := by ac_rfl
          _ ≤ (phaseRoundBound (Fintype.card V) scale * (8 * (r : ℝ≥0∞)) +
                3 * (retirementCredit (some s) : ℝ≥0∞)) + K := add_le_add hp le_rfl
          _ = (phaseRoundBound (Fintype.card V) scale * (8 * (r : ℝ≥0∞)) + K) +
                3 * (retirementCredit (some s) : ℝ≥0∞) := by ac_rfl
          _ ≤ _ := add_le_add hc le_rfl

end ParallelState

open ParallelState

theorem initial_used_subgraph (π : PublicQuotient V Q) (r : ℕ) (G : WeightedGraph V) :
    (ParallelState.initial π r).usedGraph.IsSubgraph G := by
  intro u v
  simpa only [ParallelState.usedGraph, ParallelState.initial, EndpointForest.original,
    EndpointForest.empty, originalSum, WeightedGraph.finiteSum, WeightedGraph.zero_w,
    Finset.sum_const_zero] using G.nonneg u v

theorem initial_inactive_sound (π : PublicQuotient V Q) (r : ℕ)
    (hr : 0 < r) (G : WeightedGraph V) :
    (ParallelState.initial π r).InactiveSound hr G := by
  intro v hv
  simp only [ParallelState.initial, Finset.notMem_empty] at hv

/-- The implemented large-input program has one fixed numerical constant,
uniform over its finite query/recovery fuel. -/
theorem initial_geometric_expected (π : PublicQuotient V Q) (r cap : ℕ)
    (hr : 0 < r) (G : SimpleInput V) (hq : 2 ≤ Fintype.card Q)
    (hln : 1000 ≤ Real.log (Fintype.card V : ℝ))
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    (geometricPhases hr cap (Fintype.card Q) (Fintype.card Q) (ParallelState.initial π r)).expectedQueries
      G.toWeighted.cut ≤ ENNReal.ofReal
        ((parallelConstant : ℝ) * ((Fintype.card V : ℝ) + r * Fintype.card Q *
          Real.log (Fintype.card V : ℝ) / Real.log (Fintype.card Q : ℝ))) := by
  let s := ParallelState.initial π r
  have hg := geometricPhases_expected hr cap (Fintype.card Q) (Fintype.card Q) s G
    (initial_used_subgraph π r G.toWeighted) ParallelState.initial_laminar
    (initial_inactive_sound π r hr G.toWeighted) rfl hq hln hpower
    (s.liveBlocks_card_le (lastIndex hr)) Nat.lt_two_pow_self
  have hcredit : retirementCredit (some s) = Fintype.card V := by
    simp only [retirementCredit, s, ParallelState.initial, Finset.card_empty, Nat.sub_zero]
  rw [hcredit] at hg
  have hqR : (1 : ℝ) < Fintype.card Q := by exact_mod_cast (show 1 < Fintype.card Q by omega)
  have hlogq : 0 < Real.log (Fintype.card Q : ℝ) := Real.log_pos hqR
  have hlogn : 0 < Real.log (Fintype.card V : ℝ) := by linarith
  have hx : 0 ≤ (r : ℝ) * Fintype.card Q * Real.log (Fintype.card V : ℝ) /
      Real.log (Fintype.card Q : ℝ) := by positivity
  have hgeo := geometricCharge_nonneg (Fintype.card V) (Fintype.card Q) r
    (Fintype.card Q) hq π.card_le
  have hfinish := finishingCharge_nonneg (Fintype.card V) (Fintype.card Q) r hq π.card_le
  have he : ENNReal.ofReal
      (geometricCharge (Fintype.card V) (Fintype.card Q) r (Fintype.card Q) +
        finishingCharge (Fintype.card V) (Fintype.card Q) r) + 3 * (Fintype.card V : ℝ≥0∞) =
      ENNReal.ofReal
      (geometricCharge (Fintype.card V) (Fintype.card Q) r (Fintype.card Q) +
        finishingCharge (Fintype.card V) (Fintype.card Q) r + 3 * (Fintype.card V : ℝ)) := by
    rw [ENNReal.ofReal_add (add_nonneg hgeo hfinish) (by positivity),
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
  apply hg.trans
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  unfold geometricCharge finishingCharge parallelConstant
  norm_num only [Nat.cast_ofNat]
  ring_nf at hx ⊢
  linarith only [hx, hn0]

/-- The bounded numerical small-input exception uses the existing ordinary
residual-forest program. Its logarithmic factor is uniformly bounded here;
the large-input branch continues to use the actual parallel construction. -/
theorem sequential_expected_small (π : PublicQuotient V Q) (r : ℕ)
    (G : SimpleInput V) (hq : 2 ≤ Fintype.card Q)
    (hsmall : Real.log (Fintype.card V : ℝ) < 1000) :
    (RTree.ofDeterministic (sequentialCertificate π r)).expectedQueries G.toWeighted.cut ≤
      ENNReal.ofReal ((parallelConstant : ℝ) *
        ((Fintype.card V : ℝ) + r * Fintype.card Q *
          Real.log (Fintype.card V : ℝ) / Real.log (Fintype.card Q : ℝ))) := by
  have hqR : (1 : ℝ) < Fintype.card Q := by exact_mod_cast (show 1 < Fintype.card Q by omega)
  have hlogq : 0 < Real.log (Fintype.card Q : ℝ) := Real.log_pos hqR
  have hlogqn : Real.log (Fintype.card Q : ℝ) ≤ Real.log (Fintype.card V : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast π.card_le)
  have hc := Schedule.clog_le_twice_log_add_one (Fintype.card Q) (by omega)
  have hclog : (Nat.clog 2 (Fintype.card Q) : ℝ) + 1 ≤ 2002 := by linarith
  have hcost := sequentialCertificate_cost π r G.toWeighted.cut
  have hcostR : ((sequentialCertificate π r).cost G.toWeighted.cut : ℝ) ≤
      12 * r * Fintype.card Q * ((Nat.clog 2 (Fintype.card Q) : ℝ) + 1) := by
    exact_mod_cast hcost
  have hrq : (r : ℝ) * Fintype.card Q ≤
      (r : ℝ) * Fintype.card Q * Real.log (Fintype.card V : ℝ) /
        Real.log (Fintype.card Q : ℝ) := by
    apply (le_div_iff₀ hlogq).mpr
    exact mul_le_mul_of_nonneg_left hlogqn (by positivity)
  have hb : ((sequentialCertificate π r).cost G.toWeighted.cut : ℝ) ≤
      (parallelConstant : ℝ) * ((Fintype.card V : ℝ) + r * Fintype.card Q *
        Real.log (Fintype.card V : ℝ) / Real.log (Fintype.card Q : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hclog
      (show 0 ≤ 12 * (r : ℝ) * Fintype.card Q by positivity)
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hrq0 : 0 ≤ (r : ℝ) * Fintype.card Q := by positivity
    norm_num [parallelConstant]
    nlinarith
  change CutQueryComplexity.Probability.expect
    (RTree.run G.toWeighted.cut (RTree.ofDeterministic (sequentialCertificate π r)))
      (fun out => (out.2 : ℝ≥0∞)) ≤ _
  rw [RTree.run_ofDeterministic, CutQueryComplexity.Probability.expect_pure]
  simpa only [ENNReal.ofReal_natCast, DTree.cost] using ENNReal.ofReal_le_ofReal hb

theorem zero_threshold (G : WeightedGraph Q) : IsThresholdCertificate 0 G 0 := by
  refine ⟨?_, WeightedGraph.integral_zero, ?_, ?_⟩
  · intro u v
    simpa only [WeightedGraph.zero_w] using G.nonneg u v
  · simp
  · intro S
    simp [min_eq_left (G.cut_nonneg S)]

/-- Public finite upper index for all size branches. The expected bound below
does not charge this intentionally coarse index. -/
def parallelCoreBudget (V Q : Type) [Fintype V] [Fintype Q] (r cap : ℕ) : ℕ :=
  geometricBudget V Q r cap (Fintype.card Q) + r * forestBudget Q

/-- The finite original-query implementation, chosen before any input graph.
The sequential branch is limited to bounded logarithmic input size. -/
def parallelCore (π : PublicQuotient V Q) (r cap : ℕ) :
    RTree (Finset V) ℝ (Option (WeightedGraph Q)) (parallelCoreBudget V Q r cap) :=
  if hr : 0 < r then
    if 1000 ≤ Real.log (Fintype.card V : ℝ) then
      (geometricPhases hr cap (Fintype.card Q) (Fintype.card Q) (ParallelState.initial π r)).weaken
        (by unfold parallelCoreBudget; omega)
    else ((RTree.ofDeterministic (sequentialCertificate π r)).map some).weaken
      (by unfold parallelCoreBudget; omega)
  else RTree.pure (PMF.pure (some 0))

theorem parallelCore_success (π : PublicQuotient V Q) (r cap : ℕ) (G : SimpleInput V)
    {H : WeightedGraph Q} (hH : some H ∈ ((parallelCore π r cap).eval G.toWeighted.cut).support) :
    IsThresholdCertificate r (π.graph G.toWeighted) H := by
  rw [parallelCore] at hH
  by_cases hr : 0 < r
  · rw [dif_pos hr] at hH
    by_cases hlarge : 1000 ≤ Real.log (Fintype.card V : ℝ)
    · rw [if_pos hlarge, RTree.eval_weaken] at hH
      exact geometricPhases_success hr cap _ _ _ G (initial_used_subgraph π r G.toWeighted)
        ParallelState.initial_laminar (initial_inactive_sound π r hr G.toWeighted) rfl hH
    · rw [if_neg hlarge, RTree.eval_weaken, RTree.eval_map,
        RTree.eval_ofDeterministic, PMF.pure_map] at hH
      have he := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp hH)
      simpa only [he] using sequentialCertificate_correct π r G.toWeighted G.integral_toWeighted
  · rw [dif_neg hr, RTree.eval_pure] at hH
    have he := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp hH)
    have hr0 : r = 0 := by omega
    simpa only [he, hr0] using zero_threshold (π.graph G.toWeighted)

theorem parallelCore_none_cost (π : PublicQuotient V Q) (r cap cost : ℕ) (G : SimpleInput V)
    (hout : (none, cost) ∈ (RTree.run G.toWeighted.cut (parallelCore π r cap)).support) :
    cap < cost := by
  rw [parallelCore] at hout
  by_cases hr : 0 < r
  · rw [dif_pos hr] at hout
    by_cases hlarge : 1000 ≤ Real.log (Fintype.card V : ℝ)
    · rw [if_pos hlarge, RTree.run_weaken] at hout
      exact geometricPhases_none_cost hr cap _ _ _ G (initial_used_subgraph π r G.toWeighted)
        ParallelState.initial_laminar (initial_inactive_sound π r hr G.toWeighted) rfl cost hout
    · rw [if_neg hlarge, RTree.run_weaken, mapped_run,
        RTree.run_ofDeterministic, PMF.pure_map] at hout
      have he := congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hout)
      cases he
  · rw [dif_neg hr, RTree.run_pure, PMF.pure_map] at hout
    have he := congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hout)
    cases he

theorem parallelCore_expected (π : PublicQuotient V Q) (r cap : ℕ) (G : SimpleInput V)
    (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    (parallelCore π r cap).expectedQueries G.toWeighted.cut ≤ ENNReal.ofReal
      ((parallelConstant : ℝ) * ((Fintype.card V : ℝ) + r * Fintype.card Q *
        Real.log (Fintype.card V : ℝ) / Real.log (Fintype.card Q : ℝ))) := by
  rw [parallelCore]
  by_cases hr : 0 < r
  · rw [dif_pos hr]
    by_cases hlarge : 1000 ≤ Real.log (Fintype.card V : ℝ)
    · rw [if_pos hlarge, weaken_expected]
      exact initial_geometric_expected π r cap hr G hq hlarge hpower
    · rw [if_neg hlarge, weaken_expected, mapped_expected]
      exact sequential_expected_small π r G hq (lt_of_not_ge hlarge)
  · rw [dif_neg hr, pure_expected]
    exact bot_le

/-- Final public constructor: only π, r and the chosen original-query fuel
occur before execution. Quotient multiplicities are retained in the output. -/
def parallelFuel (π : PublicQuotient V Q) (r fuel : ℕ) :
    RTree (Finset V) ℝ (Option (WeightedGraph Q)) fuel :=
  ((parallelCore π r fuel).truncate fuel).map Option.join

theorem parallelFuel_every_oracle (π : PublicQuotient V Q) (r fuel : ℕ)
    (read : Finset V → ℝ) {out : Option (WeightedGraph Q) × ℕ}
    (hout : out ∈ (RTree.run read (parallelFuel π r fuel)).support) : out.2 ≤ fuel :=
  RTree.cost_le _ _ hout

theorem parallelFuel_eval (π : PublicQuotient V Q) (r fuel : ℕ) (read : Finset V → ℝ) :
    (parallelFuel π r fuel).eval read =
      (RTree.run read (parallelCore π r fuel)).map
        (fun out => if out.2 ≤ fuel then out.1 else none) := by
  rw [parallelFuel, RTree.eval_map, RTree.eval_truncate, PMF.map_comp]
  congr 1
  funext out
  by_cases hc : out.2 ≤ fuel <;> simp [Function.comp_def, hc]

theorem parallelFuel_success (π : PublicQuotient V Q) (r fuel : ℕ) (G : SimpleInput V)
    {H : WeightedGraph Q} (hH : some H ∈ ((parallelFuel π r fuel).eval G.toWeighted.cut).support) :
    IsThresholdCertificate r (π.graph G.toWeighted) H := by
  rw [parallelFuel_eval] at hH
  obtain ⟨out, hout, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hH
  by_cases hc : out.2 ≤ fuel
  · rw [if_pos hc] at he
    apply parallelCore_success π r fuel G
    rw [RTree.eval]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨out, hout, he⟩
  · rw [if_neg hc] at he
    cases he

theorem parallelFuel_abort (π : PublicQuotient V Q) (r fuel : ℕ) (G : SimpleInput V) :
    CutQueryComplexity.Probability.mass ((parallelFuel π r fuel).eval G.toWeighted.cut)
      (fun out => out = none) =
    CutQueryComplexity.Probability.mass (RTree.run G.toWeighted.cut (parallelCore π r fuel))
      (fun out => fuel < out.2) := by
  rw [parallelFuel_eval, CutQueryComplexity.Probability.mass_map,
    CutQueryComplexity.Probability.mass_eq_tsum, CutQueryComplexity.Probability.mass_eq_tsum]
  apply tsum_congr
  intro out
  by_cases hout : out ∈ (RTree.run G.toWeighted.cut (parallelCore π r fuel)).support
  · by_cases hc : out.2 ≤ fuel
    · have hnone : out.1 ≠ none := by
        intro he
        have hrun : (none, out.2) ∈ (RTree.run G.toWeighted.cut (parallelCore π r fuel)).support := by
          simpa only [← he, Prod.eta] using hout
        have hh := parallelCore_none_cost π r fuel out.2 G hrun
        omega
      simp only [if_pos hc, hnone, if_false, Nat.not_lt.mpr hc]
    · simp only [if_neg hc, Nat.lt_of_not_ge hc, if_true]
  · have hz : RTree.run G.toWeighted.cut (parallelCore π r fuel) out = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hout
    simp only [hz, ite_self]

/-- Uniform numerical tail bound for the implemented capped program, with
no cost, progress, independence, decoder or certificate premise. -/
theorem parallelFuel_tail (π : PublicQuotient V Q) (r fuel : ℕ) (G : SimpleInput V)
    (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    (fuel + 1 : ℝ≥0∞) * CutQueryComplexity.Probability.mass
      ((parallelFuel π r fuel).eval G.toWeighted.cut) (fun out => out = none) ≤
      ENNReal.ofReal ((parallelConstant : ℝ) * ((Fintype.card V : ℝ) + r * Fintype.card Q *
        Real.log (Fintype.card V : ℝ) / Real.log (Fintype.card Q : ℝ))) := by
  have hm := RTree.truncate_markov (parallelCore π r fuel) fuel G.toWeighted.cut
  rw [RTree.truncate_abort, ← parallelFuel_abort π r fuel G] at hm
  exact hm.trans (parallelCore_expected π r fuel G hq hpower)

/-- The size-only real envelope, with the proved absolute coefficient. -/
def parallelExpectedBound (V Q : Type) [Fintype V] [Fintype Q] (r : ℕ) : ℝ :=
  (parallelConstant : ℝ) * ((Fintype.card V : ℝ) + r * Fintype.card Q *
    Real.log (Fintype.card V : ℝ) / Real.log (Fintype.card Q : ℝ))

private theorem parallelFuel_error_from_public_cap (π : PublicQuotient V Q)
    (r fuel : ℕ) (G : SimpleInput V) (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) (ε : ℝ) (hε : 0 < ε)
    (hcap : parallelExpectedBound V Q r ≤ ((fuel : ℝ) + 1) * ε) :
    CutQueryComplexity.Probability.mass ((parallelFuel π r fuel).eval G.toWeighted.cut)
      (fun out => out = none) ≤ ENNReal.ofReal ε := by
  have hh := ENNReal.ofReal_le_ofReal hcap
  rw [ENNReal.ofReal_mul (show 0 ≤ (fuel : ℝ) + 1 by positivity)] at hh
  simp only [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
    ENNReal.ofReal_natCast, ENNReal.ofReal_one] at hh
  have hm := (parallelFuel_tail π r fuel G hq hpower).trans hh
  exact (ENNReal.mul_le_mul_iff_right (by simp : (fuel + 1 : ℝ≥0∞) ≠ 0)
    (by simp)).mp hm

/-- The explicit finite approximations have vanishing unfinished tails.
The horizon is not an assumed infinite or almost-surely terminating program. -/
theorem parallelFuel_vanishing (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ fuel₀ : ℕ, ∀ fuel, fuel₀ ≤ fuel → ∀ G : SimpleInput V,
      CutQueryComplexity.Probability.mass ((parallelFuel π r fuel).eval G.toWeighted.cut)
        (fun out => out = none) ≤ ENNReal.ofReal ε := by
  refine ⟨⌈parallelExpectedBound V Q r / ε⌉₊, ?_⟩
  intro fuel hfuel G
  apply parallelFuel_error_from_public_cap π r fuel G hq hpower ε hε
  have hc := (Nat.le_ceil (parallelExpectedBound V Q r / ε)).trans
    (show (⌈parallelExpectedBound V Q r / ε⌉₊ : ℝ) ≤ fuel by exact_mod_cast hfuel)
  have hh := (div_le_iff₀ hε).mp hc
  nlinarith

/-- A public fuel choice giving one-percent failure. -/
def parallelCertificateFuel (V Q : Type) [Fintype V] [Fintype Q] (r : ℕ) : ℕ :=
  100 * ⌈parallelExpectedBound V Q r⌉₊

theorem parallelFuel_one_percent (π : PublicQuotient V Q) (r : ℕ) (G : SimpleInput V)
    (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    CutQueryComplexity.Probability.mass
      ((parallelFuel π r (parallelCertificateFuel V Q r)).eval G.toWeighted.cut)
      (fun out => out = none) ≤ ENNReal.ofReal (1 / (100 : ℝ)) := by
  apply parallelFuel_error_from_public_cap π r _ G hq hpower (1 / (100 : ℝ)) (by norm_num)
  have hc := Nat.le_ceil (parallelExpectedBound V Q r)
  unfold parallelCertificateFuel
  push_cast
  linarith

/-- Literal public program before every hidden unit input, with an actual
all-oracle original-query cap and successful integral threshold certificate.
The expected bound and tail proofs above require no additional cost premise. -/
theorem exists_parallel_certificate (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    ∃ T : RTree (Finset V) ℝ (Option (WeightedGraph Q)) (parallelCertificateFuel V Q r),
      (∀ read out, out ∈ (RTree.run read T).support → out.2 ≤ parallelCertificateFuel V Q r) ∧
      ∀ G : SimpleInput V,
        (99 : ℝ) / 100 ≤
          (CutQueryComplexity.Probability.mass (T.eval G.toWeighted.cut) (fun out => out ≠ none)).toReal ∧
        ∀ H, some H ∈ (T.eval G.toWeighted.cut).support →
          IsThresholdCertificate r (π.graph G.toWeighted) H := by
  refine ⟨parallelFuel π r (parallelCertificateFuel V Q r), ?_, ?_⟩
  · intro read out hout
    exact parallelFuel_every_oracle π r _ read hout
  · intro G
    constructor
    · have hf := parallelFuel_one_percent π r G hq hpower
      have hh := CutQueryComplexity.Probability.success_of_failure_le
        ((parallelFuel π r (parallelCertificateFuel V Q r)).eval G.toWeighted.cut)
        (fun out => out ≠ none) (by norm_num : 0 ≤ (1 / (100 : ℝ))) (by simpa only [not_not] using hf)
      norm_num at hh ⊢
      exact hh
    · intro H hH
      exact parallelFuel_success π r _ G hH

/-- Complete an unfinished finite parallel run with the existing integral
certificate program. Its full public budget is used as the parallel core's
exhaustion threshold, so this branch is charged only on an expensive run. -/
def parallelCompletion (π : PublicQuotient V Q) (r : ℕ) :
    Option (WeightedGraph Q) → RTree (Finset V) ℝ (WeightedGraph Q) (r * forestBudget Q)
  | none => RTree.ofDeterministic (sequentialCertificate π r)
  | some H => RTree.pure (PMF.pure H)

/-- A finite, always-returning original-query program. The main work is the
parallel core; deterministic completion is used only after its costly tail. -/
def parallelCertificateProgram (π : PublicQuotient V Q) (r : ℕ) :
    RTree (Finset V) ℝ (WeightedGraph Q)
      (parallelCoreBudget V Q r (r * forestBudget Q) + r * forestBudget Q) :=
  (parallelCore π r (r * forestBudget Q)).bind (parallelCompletion π r)

theorem parallelCertificateProgram_correct (π : PublicQuotient V Q) (r : ℕ)
    (G : SimpleInput V) {H : WeightedGraph Q}
    (hH : H ∈ ((parallelCertificateProgram π r).eval G.toWeighted.cut).support) :
    IsThresholdCertificate r (π.graph G.toWeighted) H := by
  rw [parallelCertificateProgram, RTree.eval_bind] at hH
  obtain ⟨out, hout, hH⟩ := (PMF.mem_support_bind_iff _ _ _).mp hH
  cases out with
  | none =>
      rw [parallelCompletion, RTree.eval_ofDeterministic] at hH
      have he := (PMF.mem_support_pure_iff _ _).mp hH
      rw [he]
      exact sequentialCertificate_correct π r G.toWeighted G.integral_toWeighted
  | some K =>
      rw [parallelCompletion, RTree.eval_pure] at hH
      have he := (PMF.mem_support_pure_iff _ _).mp hH
      rw [he]
      exact parallelCore_success π r (r * forestBudget Q) G hout

/-- Pointwise charge of completion to the actual preceding parallel run.
No bound on a conditional expectation or independent failure event is used. -/
theorem parallelCompletion_expected_le (π : PublicQuotient V Q) (r : ℕ)
    (G : SimpleInput V) (out : Option (WeightedGraph Q) × ℕ)
    (hout : out ∈ (RTree.run G.toWeighted.cut
      (parallelCore π r (r * forestBudget Q))).support) :
    (parallelCompletion π r out.1).expectedQueries G.toWeighted.cut ≤ (out.2 : ℝ≥0∞) := by
  rcases out with ⟨out, cost⟩
  cases out with
  | none =>
      have hc := parallelCore_none_cost π r (r * forestBudget Q) cost G hout
      change (RTree.ofDeterministic (sequentialCertificate π r)).expectedQueries
        G.toWeighted.cut ≤ (cost : ℝ≥0∞)
      apply (RTree.expectedQueries_le_budget _ _).trans
      exact_mod_cast hc.le
  | some H =>
      change (RTree.pure (q := r * forestBudget Q) (PMF.pure H)).expectedQueries
        G.toWeighted.cut ≤ (cost : ℝ≥0∞)
      rw [pure_expected]
      exact bot_le

/-- Absolute coefficient of the total zero-error program, including its
tail-triggered completion. Its value is 2^61. -/
def parallelZeroErrorConstant : ℕ := 2 * parallelConstant

def parallelZeroErrorExpectedBound (V Q : Type) [Fintype V] [Fintype Q] (r : ℕ) : ℝ :=
  (parallelZeroErrorConstant : ℝ) * ((Fintype.card V : ℝ) + r * Fintype.card Q *
    Real.log (Fintype.card V : ℝ) / Real.log (Fintype.card Q : ℝ))

theorem parallelZeroErrorExpectedBound_eq :
    parallelZeroErrorExpectedBound V Q r = 2 * parallelExpectedBound V Q r := by
  unfold parallelZeroErrorExpectedBound parallelZeroErrorConstant parallelExpectedBound
  push_cast
  ring

/-- The actual total program meets the sharp parallel expectation. Even the
entire sequential completion costs at most the already-paid parallel queries
on every supported run on which it is invoked. -/
theorem parallelCertificateProgram_expected (π : PublicQuotient V Q) (r : ℕ)
    (G : SimpleInput V) (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    (parallelCertificateProgram π r).expectedQueries G.toWeighted.cut ≤
      ENNReal.ofReal (parallelZeroErrorExpectedBound V Q r) := by
  have htail : CutQueryComplexity.Probability.expect
      ((parallelCore π r (r * forestBudget Q)).eval G.toWeighted.cut)
      (fun out => (parallelCompletion π r out).expectedQueries G.toWeighted.cut) ≤
      (parallelCore π r (r * forestBudget Q)).expectedQueries G.toWeighted.cut := by
    rw [RTree.eval, CutQueryComplexity.Probability.expect_map]
    exact CutQueryComplexity.Probability.expect_mono_on_support _
      (parallelCompletion_expected_le π r G)
  have hcore : (parallelCore π r (r * forestBudget Q)).expectedQueries G.toWeighted.cut ≤
      ENNReal.ofReal (parallelExpectedBound V Q r) :=
    parallelCore_expected π r (r * forestBudget Q) G hq hpower
  have hqR : (1 : ℝ) < Fintype.card Q := by
    exact_mod_cast (show 1 < Fintype.card Q by omega)
  have hlogq : 0 < Real.log (Fintype.card Q : ℝ) := Real.log_pos hqR
  have hnR : (1 : ℝ) < Fintype.card V :=
    hqR.trans_le (by exact_mod_cast π.card_le)
  have hlogn : 0 < Real.log (Fintype.card V : ℝ) := Real.log_pos hnR
  have hB : 0 ≤ parallelExpectedBound V Q r := by
    unfold parallelExpectedBound
    positivity
  rw [parallelCertificateProgram, bind_expected]
  calc
    _ ≤ (parallelCore π r (r * forestBudget Q)).expectedQueries G.toWeighted.cut +
        (parallelCore π r (r * forestBudget Q)).expectedQueries G.toWeighted.cut :=
      add_le_add le_rfl htail
    _ ≤ ENNReal.ofReal (parallelExpectedBound V Q r) +
        ENNReal.ofReal (parallelExpectedBound V Q r) := add_le_add hcore hcore
    _ = ENNReal.ofReal (parallelZeroErrorExpectedBound V Q r) := by
      rw [← ENNReal.ofReal_add hB hB, parallelZeroErrorExpectedBound_eq]
      congr 1
      ring

/-- Literal zero-error public program before every hidden simple graph. Its
expected bound is sharp although its finite public index is deliberately coarse. -/
theorem exists_parallel_zero_error (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    ∃ T : RTree (Finset V) ℝ (WeightedGraph Q)
        (parallelCoreBudget V Q r (r * forestBudget Q) + r * forestBudget Q),
      ∀ G : SimpleInput V,
        T.expectedQueries G.toWeighted.cut ≤
          ENNReal.ofReal (parallelZeroErrorExpectedBound V Q r) ∧
        ∀ H, H ∈ (T.eval G.toWeighted.cut).support →
          IsThresholdCertificate r (π.graph G.toWeighted) H := by
  refine ⟨parallelCertificateProgram π r, ?_⟩
  intro G
  exact ⟨parallelCertificateProgram_expected π r G hq hpower,
    fun _ hH => parallelCertificateProgram_correct π r G hH⟩

/-- Every clock truncates the same total zero-error program. The chosen clock
does not change any internal random law or exhaustion threshold. -/
def parallelZeroErrorFuel (π : PublicQuotient V Q) (r fuel : ℕ) :
    RTree (Finset V) ℝ (Option (WeightedGraph Q)) fuel :=
  (parallelCertificateProgram π r).truncate fuel

theorem parallelZeroErrorFuel_every_oracle (π : PublicQuotient V Q) (r fuel : ℕ)
    (read : Finset V → ℝ) {out : Option (WeightedGraph Q) × ℕ}
    (hout : out ∈ (RTree.run read (parallelZeroErrorFuel π r fuel)).support) : out.2 ≤ fuel :=
  RTree.cost_le _ _ hout

theorem parallelZeroErrorFuel_success (π : PublicQuotient V Q) (r fuel : ℕ)
    (G : SimpleInput V) {H : WeightedGraph Q}
    (hH : some H ∈ ((parallelZeroErrorFuel π r fuel).eval G.toWeighted.cut).support) :
    IsThresholdCertificate r (π.graph G.toWeighted) H := by
  rw [parallelZeroErrorFuel, RTree.eval_truncate] at hH
  obtain ⟨out, hout, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hH
  by_cases hc : out.2 ≤ fuel
  · rw [if_pos hc] at he
    apply parallelCertificateProgram_correct π r G
    rw [RTree.eval]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨out, hout, Option.some.inj he⟩
  · rw [if_neg hc] at he
    cases he

/-- Exact coupling for every oracle, before imposing any honest-input law. -/
theorem parallelZeroErrorFuel_abort (π : PublicQuotient V Q) (r fuel : ℕ)
    (read : Finset V → ℝ) :
    CutQueryComplexity.Probability.mass ((parallelZeroErrorFuel π r fuel).eval read)
      (fun out => out = none) =
    CutQueryComplexity.Probability.mass (RTree.run read (parallelCertificateProgram π r))
      (fun out => fuel < out.2) :=
  RTree.truncate_abort _ _ _

theorem parallelZeroErrorFuel_tail (π : PublicQuotient V Q) (r fuel : ℕ)
    (G : SimpleInput V) (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    (fuel + 1 : ℝ≥0∞) * CutQueryComplexity.Probability.mass
      ((parallelZeroErrorFuel π r fuel).eval G.toWeighted.cut) (fun out => out = none) ≤
      ENNReal.ofReal (parallelZeroErrorExpectedBound V Q r) :=
  (RTree.truncate_markov (parallelCertificateProgram π r) fuel G.toWeighted.cut).trans
    (parallelCertificateProgram_expected π r G hq hpower)

/-- One-percent clock for the total program, fixed from public dimensions. -/
def parallelZeroErrorClock (V Q : Type) [Fintype V] [Fintype Q] (r : ℕ) : ℕ :=
  100 * ⌈parallelZeroErrorExpectedBound V Q r⌉₊

theorem parallelZeroErrorFuel_one_percent (π : PublicQuotient V Q) (r : ℕ)
    (G : SimpleInput V) (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    CutQueryComplexity.Probability.mass
      ((parallelZeroErrorFuel π r (parallelZeroErrorClock V Q r)).eval G.toWeighted.cut)
      (fun out => out = none) ≤ ENNReal.ofReal (1 / (100 : ℝ)) := by
  apply RTree.truncate_abort_le
  apply (parallelCertificateProgram_expected π r G hq hpower).trans
  have hcap : parallelZeroErrorExpectedBound V Q r ≤
      ((parallelZeroErrorClock V Q r : ℝ) + 1) * (1 / (100 : ℝ)) := by
    have hc := Nat.le_ceil (parallelZeroErrorExpectedBound V Q r)
    unfold parallelZeroErrorClock
    push_cast
    linarith
  have hh := ENNReal.ofReal_le_ofReal hcap
  rw [ENNReal.ofReal_mul (show 0 ≤ (parallelZeroErrorClock V Q r : ℝ) + 1 by positivity)] at hh
  simpa only [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
    ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hh

/-- The capped public certificate is the actual truncation of the zero-error
parallel program whose expectation was proved above. -/
theorem exists_parallel_zero_error_capped (π : PublicQuotient V Q) (r : ℕ)
    (hq : 2 ≤ Fintype.card Q)
    (hpower : (Real.log (Fintype.card V : ℝ) / Real.log 2) ^ ((5 : ℝ) / 2) ≤
      (Fintype.card Q : ℝ)) :
    ∃ T : RTree (Finset V) ℝ (Option (WeightedGraph Q)) (parallelZeroErrorClock V Q r),
      (∀ read out, out ∈ (RTree.run read T).support → out.2 ≤ parallelZeroErrorClock V Q r) ∧
      ∀ G : SimpleInput V,
        (99 : ℝ) / 100 ≤
          (CutQueryComplexity.Probability.mass (T.eval G.toWeighted.cut) (fun out => out ≠ none)).toReal ∧
        ∀ H, some H ∈ (T.eval G.toWeighted.cut).support →
          IsThresholdCertificate r (π.graph G.toWeighted) H := by
  refine ⟨parallelZeroErrorFuel π r (parallelZeroErrorClock V Q r), ?_, ?_⟩
  · intro read out hout
    exact parallelZeroErrorFuel_every_oracle π r _ read hout
  · intro G
    constructor
    · have hf := parallelZeroErrorFuel_one_percent π r G hq hpower
      have hh := CutQueryComplexity.Probability.success_of_failure_le
        ((parallelZeroErrorFuel π r (parallelZeroErrorClock V Q r)).eval G.toWeighted.cut)
        (fun out => out ≠ none) (by norm_num : 0 ≤ (1 / (100 : ℝ))) (by simpa only [not_not] using hf)
      norm_num at hh ⊢
      exact hh
    · intro H hH
      exact parallelZeroErrorFuel_success π r _ G hH

#print axioms ParallelState.parallel_slots_at_scale
#print axioms ParallelState.mixedStageBound_large
#print axioms ParallelState.phaseRoundBound_large
#print axioms ParallelState.geometricPhases_success
#print axioms ParallelState.geometricPhases_none_cost
#print axioms ParallelState.cappedGeometric_every_oracle
#print axioms ParallelState.cappedGeometric_success
#print axioms ParallelState.cappedGeometric_abort
#print axioms ParallelState.geometricCharge_step
#print axioms ParallelState.geometricPhases_expected
#print axioms initial_geometric_expected
#print axioms sequential_expected_small
#print axioms parallelCore_success
#print axioms parallelCore_none_cost
#print axioms parallelCore_expected
#print axioms parallelFuel_every_oracle
#print axioms parallelFuel_success
#print axioms parallelFuel_abort
#print axioms parallelFuel_tail
#print axioms parallelFuel_vanishing
#print axioms parallelFuel_one_percent
#print axioms exists_parallel_certificate
#print axioms parallelCertificateProgram_correct
#print axioms parallelCompletion_expected_le
#print axioms parallelZeroErrorExpectedBound_eq
#print axioms parallelCertificateProgram_expected
#print axioms exists_parallel_zero_error
#print axioms parallelZeroErrorFuel_every_oracle
#print axioms parallelZeroErrorFuel_success
#print axioms parallelZeroErrorFuel_abort
#print axioms parallelZeroErrorFuel_tail
#print axioms parallelZeroErrorFuel_one_percent
#print axioms exists_parallel_zero_error_capped

end
end CutQueryComplexity.StarContraction2022.Certificates
