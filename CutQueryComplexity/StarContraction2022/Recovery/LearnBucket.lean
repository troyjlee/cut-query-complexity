import CutQueryComplexity.Probability.FiniteEvents
import CutQueryComplexity.Probability.Expectation
import CutQueryComplexity.Probability.Truncation
import CutQueryComplexity.Probability.Chernoff
import CutQueryComplexity.StarContraction2022.Recovery.Decode
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-!
# Finite first-success sampling and bucket recovery

The law below belongs to the uncapped finite process. It is proved before any
query-clock conditioning. Rows may share every random proposal; only successive
rounds are independent. Operational sparse measurement and the uniform expected
cost estimate are proved later in this module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CutQueryComplexity.StarContraction2022.Recovery

open Finset Filter
open Probability
open scoped Classical NNReal ENNReal
noncomputable section

variable {Ω R : Type} [Fintype Ω] [DecidableEq Ω]

/-- The first accepted proposal among exactly `T` independent finite draws.
`none` records that no accepted proposal occurred within that finite horizon. -/
def firstSuccess (p : PMF (Option Ω)) : ℕ → PMF (Option Ω)
  | 0 => PMF.pure none
  | T+1 => p.bind fun o => match o with
    | none => firstSuccess p T
    | some x => PMF.pure (some x)

@[simp] theorem firstSuccess_none (p : PMF (Option Ω)) (T : ℕ) :
    firstSuccess p T none = p none ^ T := by
  induction T with
  | zero => simp [firstSuccess]
  | succ T ih =>
      simp only [firstSuccess, PMF.bind_apply, tsum_fintype, Fintype.sum_option]
      simp [ih, PMF.pure_apply, pow_succ, mul_comm]

/-- Exact finite first-success law. No event concerning other rows or the query
clock is present, and no infinite operational solver is assumed. -/
theorem firstSuccess_some (p : PMF (Option Ω)) (T : ℕ) (x : Ω) :
    firstSuccess p T (some x) =
      p (some x) * ∑ j ∈ range T, p none ^ j := by
  induction T with
  | zero => simp [firstSuccess, PMF.pure_apply]
  | succ T ih =>
      have hstep : firstSuccess p (T+1) (some x) =
          p none * firstSuccess p T (some x) + p (some x) := by
        simp [firstSuccess, PMF.bind_apply, tsum_fintype, Fintype.sum_option,
          PMF.pure_apply]
      rw [hstep, ih, sum_range_succ']
      simp only [pow_zero, pow_succ', ← mul_sum]
      ring

/-- The normalized finite law explicitly separates completion probability from
single-proposal acceptance. This is not a law conditioned on global cap success. -/
theorem firstSuccess_some_real (p : PMF (Option Ω)) (T : ℕ) (x : Ω)
    (hp : (p none).toReal < 1) :
    (firstSuccess p T (some x)).toReal =
      (1 - (p none).toReal ^ T) * ((p (some x)).toReal / (1 - (p none).toReal)) := by
  rw [firstSuccess_some, ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun j _ => ENNReal.pow_ne_top (p.apply_ne_top none))]
  simp only [ENNReal.toReal_pow]
  have hg := geom_sum_mul_neg ((p none).toReal) T
  have hd : 1 - (p none).toReal ≠ 0 := by linarith
  calc
    _ = (p (some x)).toReal *
        ((∑ j ∈ range T, (p none).toReal ^ j) * (1 - (p none).toReal)) /
          (1 - (p none).toReal) := by field_simp [hd]
    _ = (p (some x)).toReal * (1 - (p none).toReal ^ T) /
        (1 - (p none).toReal) := by rw [hg]
    _ = _ := by ring

/-- The limiting accepted-row law is derived from the finite approximations. -/
theorem firstSuccess_some_tendsto (p : PMF (Option Ω)) (x : Ω)
    (hp : (p none).toReal < 1) :
    Tendsto (fun T => (firstSuccess p T (some x)).toReal) atTop
      (nhds ((p (some x)).toReal / (1 - (p none).toReal))) := by
  simp_rw [firstSuccess_some_real p _ x hp]
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  simpa only [sub_zero, one_mul] using
    (hc.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hp)).mul_const
        ((p (some x)).toReal / (1 - (p none).toReal))

/-- A proposal is accepted using only its row predicate. -/
def rowProposal (μ : PMF Ω) (accept : Ω → Prop) : PMF (Option Ω) :=
  μ.map fun x => if accept x then some x else none

theorem rowProposal_none (μ : PMF Ω) (accept : Ω → Prop) :
    rowProposal μ accept none = mass μ (fun x => ¬accept x) := by
  rw [rowProposal, PMF.map_apply, mass_eq_tsum]
  apply tsum_congr
  intro x
  by_cases hx : accept x <;> simp [hx]

/-- Joint finite process with shared proposals. Correlation between distinct rows
is retained; each row records its own first accepted proposal. -/
def rowSamples (μ : PMF Ω) (accept : R → Ω → Prop) : ℕ → PMF (R → Option Ω)
  | 0 => PMF.pure fun _ => none
  | T+1 => μ.bind fun x => (rowSamples μ accept T).map
      (fun later r => if accept r x then some x else later r)

/-- Shared randomness between rows does not change a fixed row's first-success
marginal. This identity precedes and is independent of truncation. -/
theorem rowSamples_marginal (μ : PMF Ω) (accept : R → Ω → Prop) (T : ℕ) (r : R) :
    (rowSamples μ accept T).map (fun out => out r) =
      firstSuccess (rowProposal μ (accept r)) T := by
  induction T with
  | zero => simp only [rowSamples, firstSuccess, PMF.pure_map]
  | succ T ih =>
      simp only [rowSamples, PMF.map_bind, PMF.map_comp, Function.comp_def,
        firstSuccess, rowProposal, PMF.bind_map]
      congr 1
      funext x
      by_cases ha : accept r x
      · simp only [ite_eq_left ha]
        exact PMF.map_const _ _
      · simpa only [ite_eq_right ha, rowProposal] using ih

@[simp] theorem rowSamples_pending (μ : PMF Ω) (accept : R → Ω → Prop) (T : ℕ) (r : R) :
    mass (rowSamples μ accept T) (fun out => out r = none) =
      rowProposal μ (accept r) none ^ T := by
  rw [← mass_map (rowSamples μ accept T) (fun out => out r) (fun o => o = none),
    rowSamples_marginal, mass_eq_tsum]
  simp [tsum_fintype, Fintype.sum_option, firstSuccess_none]

/-- Uniform geometric tail over all rows, without a row-independence premise. -/
theorem rowSamples_unfinished_le [Fintype R] (μ : PMF Ω) (accept : R → Ω → Prop)
    (T : ℕ) (h : ∀ r, rowProposal μ (accept r) none ≤ (2 : ℝ≥0∞)⁻¹) :
    mass (rowSamples μ accept T) (fun out => ∃ r, out r = none) ≤
      (Fintype.card R : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹)^T := by
  have ht := mass_failure_le_card_mul (rowSamples μ accept T) (univ : Finset R)
    (fun r out => out r ≠ none) (fun out => ∀ r, out r ≠ none)
    (((2 : ℝ≥0∞)⁻¹)^T)
    (fun _ _ hall r => hall r (mem_univ _))
    (fun r _ => by simpa only [not_not, rowSamples_pending] using
      pow_le_pow_left' (h r) T)
  simpa only [not_forall, not_not, card_univ] using ht

/-- Each row contributes at most two count queries in expectation, uniformly
in the chosen finite horizon, once its failure probability is at most one half. -/
theorem geometric_attempts_le_two {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1/2) (T : ℕ) :
    ∑ j ∈ range T, a^j ≤ 2 := by
  have hs : 0 ≤ ∑ j ∈ range T, a^j := sum_nonneg (fun _ _ => pow_nonneg ha _)
  have hg := geom_sum_mul_neg a T
  have hpow : 0 ≤ a^T := pow_nonneg ha _
  nlinarith

theorem geometric_attempts_ennreal_le_two (T : ℕ) :
    (∑ j ∈ range T, ((2 : ℝ≥0∞)⁻¹)^j) ≤ 2 := by
  have hfinite : ∀ j ∈ range T, ((2 : ℝ≥0∞)⁻¹)^j ≠ ∞ :=
    fun j _ => ENNReal.pow_ne_top (by norm_num)
  apply (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.mpr hfinite) (by norm_num)).mp
  rw [ENNReal.toReal_sum hfinite]
  simpa using geometric_attempts_le_two (a := (1 : ℝ)/2) (by norm_num) (by norm_num) T

def pendingRows [Fintype R] [DecidableEq R] (out : R → Option Ω) : Finset R :=
  univ.filter fun r => out r = none

/-- Linearity of expectation counts the real pending-row queries and does not
require independence between rows. -/
theorem rowSamples_expected_pending [Fintype R] [DecidableEq R]
    (μ : PMF Ω) (accept : R → Ω → Prop) (T : ℕ) :
    expect (rowSamples μ accept T) (fun out => ((pendingRows out).card : ℝ≥0∞)) =
      ∑ r, rowProposal μ (accept r) none ^ T := by
  have he : (fun out : R → Option Ω => ((pendingRows out).card : ℝ≥0∞)) =
      (fun out => ∑ r, if out r = none then (1 : ℝ≥0∞) else 0) := by
    funext out
    simp only [pendingRows,card_eq_sum_ones,sum_filter,Nat.cast_sum,
      Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [he,expect_sum]
  apply sum_congr rfl
  intro r _
  calc
    _ = mass (rowSamples μ accept T) (fun out => out r = none) := by
      rw [Probability.expect,mass_eq_tsum]
      apply tsum_congr
      intro out
      by_cases ho : out r = none <;> simp [ho]
    _ = _ := rowSamples_pending μ accept T r

/-- A uniform bound for every finite horizon, ready to attach to the count-query
component of the operational round program. -/
theorem rowSamples_total_expected_counts [Fintype R] [DecidableEq R]
    (μ : PMF Ω) (accept : R → Ω → Prop) (T : ℕ)
    (h : ∀ r, rowProposal μ (accept r) none ≤ (2 : ℝ≥0∞)⁻¹) :
    (∑ t ∈ range T, expect (rowSamples μ accept t)
      (fun out => ((pendingRows out).card : ℝ≥0∞))) ≤ 2*(Fintype.card R : ℝ≥0∞) := by
  simp_rw [rowSamples_expected_pending]
  rw [sum_comm]
  calc
    _ ≤ ∑ _r : R, (2 : ℝ≥0∞) := by
      apply sum_le_sum
      intro r _
      calc
        _ ≤ ∑ t ∈ range T, ((2 : ℝ≥0∞)⁻¹)^t := by
          apply sum_le_sum
          intro t _
          exact pow_le_pow_left' (h r) t
        _ ≤ 2 := geometric_attempts_ennreal_le_two T
    _ = _ := by simp [mul_comm]

section ColumnSampling

variable {C : Type} [DecidableEq C]

/-- A public finite coin, with its probability parameter constrained before
any graph is supplied. -/
def sampleCoin (p : ℝ≥0) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ((cond b p (1-p) : ℝ≥0) : ℝ≥0∞)) (by simp [hp])

@[simp] theorem sampleCoin_apply (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) :
    sampleCoin p hp b = cond b (p : ℝ≥0∞) ((1-p : ℝ≥0) : ℝ≥0∞) := by
  cases b <;> rfl

/-- Each listed column is sampled independently. The eventual caller supplies
`univ.toList`, so every original column is tossed exactly once. -/
def sampleColumns (p : ℝ≥0) (hp : p ≤ 1) : List C → PMF (Finset C)
  | [] => PMF.pure ∅
  | c :: cs => (sampleCoin p hp).bind fun b =>
      (sampleColumns p hp cs).map fun S => if b then insert c S else S

theorem sampleColumns_subset (p : ℝ≥0) (hp : p ≤ 1) (cs : List C)
    {S : Finset C} (hS : S ∈ (sampleColumns p hp cs).support) : S ⊆ cs.toFinset := by
  induction cs generalizing S with
  | nil =>
      have he := (PMF.mem_support_pure_iff _ _).mp hS
      subst S
      exact empty_subset _
  | cons c cs ih =>
      obtain ⟨b, _, hmap⟩ := (PMF.mem_support_bind_iff _ _ _).mp hS
      obtain ⟨T, hT, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
      have ht := ih hT
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, List.toFinset_cons]
      · exact ht.trans (subset_insert _ _)
      · exact insert_subset_insert c ht


private theorem map_insert_apply (μ : PMF (Finset C)) (c : C)
    (hc : ∀ S ∈ μ.support, c ∉ S) (S : Finset C) :
    (μ.map (insert c)) S = if c ∈ S then μ (S.erase c) else 0 := by
  rw [PMF.map_apply,tsum_eq_single (S.erase c)]
  · by_cases hcS : c ∈ S
    · simp only [insert_erase hcS,ite_true,ite_eq_left hcS]
    · have he : S ≠ insert c (S.erase c) := by
        intro he
        apply hcS
        rw [he]
        exact mem_insert_self _ _
      simp only [ite_eq_right he,ite_eq_right hcS]
  · intro T hT
    by_cases he : S = insert c T
    · by_cases hpos : T ∈ μ.support
      · have herase : S.erase c = T := by rw [he,erase_insert (hc T hpos)]
        exact (hT herase.symm).elim
      · have hz : μ T = 0 := by simpa only [PMF.mem_support_iff,not_not] using hpos
        simp only [hz,ite_self]
    · simp only [ite_eq_right he]

theorem sampleColumns_cons_apply (p : ℝ≥0) (hp : p ≤ 1) (c : C) (cs : List C)
    (hc : c ∉ cs.toFinset) (S : Finset C) :
    sampleColumns p hp (c::cs) S =
      if c ∈ S then (p : ℝ≥0∞)*sampleColumns p hp cs (S.erase c)
      else ((1-p : ℝ≥0) : ℝ≥0∞)*sampleColumns p hp cs S := by
  have ht : ∀ T ∈ (sampleColumns p hp cs).support, c ∉ T :=
    fun T hT hm => hc (sampleColumns_subset p hp cs hT hm)
  simp only [sampleColumns,PMF.bind_apply,tsum_fintype,Fintype.sum_bool,
    sampleCoin_apply,Bool.false_eq_true,↓reduceIte]
  change (p : ℝ≥0∞)*((sampleColumns p hp cs).map (insert c)) S +
    ((1-p : ℝ≥0) : ℝ≥0∞)*((sampleColumns p hp cs).map id) S = _
  rw [PMF.map_id,map_insert_apply _ _ ht]
  by_cases hcS : c ∈ S
  · have hz : sampleColumns p hp cs S = 0 := by
      by_contra h
      exact ht S h hcS
    simp only [ite_eq_left hcS,hz,mul_zero,zero_add,add_zero]
  · simp only [ite_eq_right hcS,mul_zero,zero_add,add_zero]

/-- Point masses of the implemented independent finite sampler. This equality
is the bridge to a Bernoulli-subset law, and holds at p=0 and p=1 as well. -/
theorem sampleColumns_apply (p : ℝ≥0) (hp : p ≤ 1) (cs : List C) (hcs : cs.Nodup)
    (S : Finset C) :
    sampleColumns p hp cs S = if S ⊆ cs.toFinset then
      (p : ℝ≥0∞)^S.card*((1-p : ℝ≥0) : ℝ≥0∞)^(cs.toFinset.card-S.card) else 0 := by
  induction cs generalizing S with
  | nil =>
      by_cases hS : S = ∅
      · subst S
        simp [sampleColumns,PMF.pure_apply]
      · simp [sampleColumns,PMF.pure_apply,hS,eq_comm]
  | cons c cs ih =>
      obtain ⟨hc,hcs⟩ := List.nodup_cons.mp hcs
      have hc' : c ∉ cs.toFinset := by simpa only [List.mem_toFinset] using hc
      by_cases hsub : S ⊆ (c::cs).toFinset
      · rw [ite_eq_left hsub,sampleColumns_cons_apply p hp c cs hc']
        by_cases hcS : c ∈ S
        · have herase : S.erase c ⊆ cs.toFinset := by
            intro x hx
            have hm := hsub ((mem_erase.mp hx).2)
            simp only [List.toFinset_cons,mem_insert] at hm
            exact hm.resolve_left (mem_erase.mp hx).1
          have hS : S.card = (S.erase c).card+1 := (card_erase_add_one hcS).symm
          have he : cs.toFinset.card+1-((S.erase c).card+1) =
              cs.toFinset.card-(S.erase c).card := by omega
          rw [ite_eq_left hcS,ih hcs,ite_eq_left herase,List.toFinset_cons,
            card_insert_of_notMem hc',hS,he,pow_succ]
          ring
        · have hS : S ⊆ cs.toFinset := by
            intro x hx
            have hm := hsub hx
            simp only [List.toFinset_cons,mem_insert] at hm
            exact hm.resolve_left (fun he => hcS (he ▸ hx))
          have hcard := card_le_card hS
          have he : cs.toFinset.card+1-S.card = (cs.toFinset.card-S.card)+1 := by omega
          rw [ite_eq_right hcS,ih hcs,ite_eq_left hS,List.toFinset_cons,
            card_insert_of_notMem hc',he,pow_succ]
          ring
      · rw [ite_eq_right hsub]
        by_contra h
        exact hsub (sampleColumns_subset p hp (c::cs) h)

/-- Removing public columns after sampling is identical to tossing coins only
for those columns. This is an equality of actual finite PMFs. -/
theorem sampleColumns_filter (p : ℝ≥0) (hp : p ≤ 1) (cs : List C)
    (keep : C → Prop) :
    (sampleColumns p hp cs).map (fun S => S.filter keep) =
      sampleColumns p hp (cs.filter fun c => decide (keep c)) := by
  induction cs with
  | nil => simp only [sampleColumns,PMF.pure_map,List.filter_nil,List.toFinset_nil,filter_empty]
  | cons c cs ih =>
      by_cases hc : keep c
      · have he : (fun S : Finset C => (insert c S).filter keep) =
            (fun S => insert c (S.filter keep)) := by funext S; simp [filter_insert,hc]
        simp only [List.filter_cons,decide_eq_true hc,↓reduceIte,sampleColumns,
          PMF.map_bind]
        congr 1
        funext b
        cases b
        · simp only [Bool.false_eq_true,↓reduceIte]
          change ((sampleColumns p hp cs).map id).map (fun S => S.filter keep) =
            (sampleColumns p hp (cs.filter fun c => decide (keep c))).map id
          simpa only [PMF.map_id] using ih
        · simp only [↓reduceIte,PMF.map_comp,Function.comp_def,he]
          have h := congrArg (fun μ : PMF (Finset C) => μ.map (insert c)) ih
          simpa only [PMF.map_comp,Function.comp_def] using h
      · have he : (fun S : Finset C => (insert c S).filter keep) =
            (fun S => S.filter keep) := by funext S; simp [filter_insert,hc]
        simp only [List.filter_cons,decide_eq_false hc,Bool.false_eq_true,↓reduceIte,sampleColumns,
          PMF.map_bind]
        have hcoin : (fun b : Bool =>
            ((sampleColumns p hp cs).map (fun S => if b then insert c S else S)).map
              (fun S => S.filter keep)) =
            (fun _ => (sampleColumns p hp cs).map (fun S => S.filter keep)) := by
          funext b
          cases b <;> simp only [Bool.false_eq_true,↓reduceIte,PMF.map_id,PMF.map_comp,
            Function.comp_def,he]
        rw [hcoin,PMF.bind_const,ih]

private theorem pmf_map_congr_support {α β : Type} (p : PMF α) {f g : α → β}
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  ext y
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ p.support
  · rw [h x hx]
  · have hz : p x = 0 := by simpa only [PMF.mem_support_iff, not_not] using hx
    simp [hz]

/-- A row count is used only in semantic proofs. The query program obtains this
number from the oracle and validates the answer before making any decision. -/
def sampleCount (row : C → Bool) (S : Finset C) : ℕ :=
  ∑ c ∈ S, if row c then 1 else 0

@[simp] theorem sampleCount_empty (row : C → Bool) : sampleCount row ∅ = 0 := by
  simp only [sampleCount,sum_empty]

theorem sampleCount_insert (row : C → Bool) (c : C) (S : Finset C) (hc : c ∉ S) :
    sampleCount row (insert c S) = (if row c then 1 else 0)+sampleCount row S := by
  simp only [sampleCount,sum_insert hc]

theorem sampleCount_le_card (row : C → Bool) (S : Finset C) :
    sampleCount row S ≤ S.card := by
  calc
    _ ≤ ∑ _c ∈ S, 1 := sum_le_sum (fun c _ => by split <;> omega)
    _ = _ := by simp

private def rowDraw (p : ℝ≥0) (hp : p ≤ 1) (present : Bool) : BoundedDraw :=
  BoundedDraw.ofMap (sampleCoin p hp)
    (fun b => if present && b then (1 : ℝ) else 0)
    (fun b _ => by cases present <;> cases b <;> norm_num)

private theorem rowDraw_mean (p : ℝ≥0) (hp : p ≤ 1) (present : Bool) :
    (rowDraw p hp present).mean = if present then (p : ℝ) else 0 := by
  change (expect ((sampleCoin p hp).map (fun b => if present && b then (1 : ℝ) else 0))
    ENNReal.ofReal).toReal = _
  rw [expect_map]
  cases present <;>
    simp [Probability.expect,tsum_fintype,Fintype.sum_bool,sampleCoin_apply]

/-- The actual finite column sampler has precisely the independent bounded-sum
law required by the existing Chernoff theorem. No sampling oracle is assumed. -/
theorem sampleColumns_count_law (p : ℝ≥0) (hp : p ≤ 1) (row : C → Bool)
    (cs : List C) (hcs : cs.Nodup) :
    (sampleColumns p hp cs).map (fun S => (sampleCount row S : ℝ)) =
      BoundedDraw.sumLaw (cs.map fun c => rowDraw p hp (row c)) := by
  induction cs with
  | nil => simp [sampleColumns, sampleCount, BoundedDraw.sumLaw, independentSum, PMF.pure_map]
  | cons c cs ih =>
      obtain ⟨hc, hcs⟩ := List.nodup_cons.mp hcs
      rw [sampleColumns, PMF.map_bind]
      change (sampleCoin p hp).bind (fun b =>
          ((sampleColumns p hp cs).map (fun S => if b then insert c S else S)).map
            (fun S => (sampleCount row S : ℝ))) =
        ((sampleCoin p hp).map (fun b => if row c && b then (1 : ℝ) else 0)).bind
          (fun x => (BoundedDraw.sumLaw (cs.map fun c => rowDraw p hp (row c))).map
            (fun y => x+y))
      rw [PMF.bind_map]
      congr 1
      funext b
      rw [← ih hcs]
      simp only [PMF.map_comp, Function.comp_def]
      apply pmf_map_congr_support
      intro S hS
      have hcS : c ∉ S := fun hm => hc (List.mem_toFinset.mp
        (sampleColumns_subset p hp cs hS hm))
      cases b <;> cases hrow : row c <;>
        simp [sampleCount_insert, hcS, hrow, Nat.cast_add]

private theorem rowDraw_sumMean (p : ℝ≥0) (hp : p ≤ 1) (row : C → Bool)
    (cs : List C) (hcs : cs.Nodup) :
    BoundedDraw.sumMean (cs.map fun c => rowDraw p hp (row c)) =
      (p : ℝ) * sampleCount row cs.toFinset := by
  induction cs with
  | nil => simp [BoundedDraw.sumMean, sampleCount]
  | cons c cs ih =>
      obtain ⟨hc, hcs⟩ := List.nodup_cons.mp hcs
      have hc' : c ∉ cs.toFinset := by simpa using hc
      change (rowDraw p hp (row c)).mean +
          BoundedDraw.sumMean (cs.map fun c => rowDraw p hp (row c)) = _
      rw [rowDraw_mean, ih hcs]
      cases hrow : row c <;>
        simp [sampleCount_insert, List.toFinset_cons, hc', hrow, Nat.cast_add, mul_add]

/-- Public proposal distribution, shared by every row in the bucket. -/
def columnProposal [Fintype C] (p : ℝ≥0) (hp : p ≤ 1) : PMF (Finset C) :=
  sampleColumns p hp (univ : Finset C).toList


/-- Exact one-row restriction of the actual proposal. On N this is precisely
the standard Bernoulli-subset point mass, with no conditional-law hypothesis. -/
theorem columnProposal_restrict_apply [Fintype C] (p : ℝ≥0) (hp : p ≤ 1)
    (N S : Finset C) :
    ((columnProposal (C := C) p hp).map (fun T => T ∩ N)) S =
      if S ⊆ N then (p : ℝ≥0∞)^S.card * ((1-p : ℝ≥0) : ℝ≥0∞)^(N.card-S.card) else 0 := by
  have he : (fun T : Finset C => T ∩ N) = (fun T => T.filter (· ∈ N)) := by
    funext T
    ext c
    simp
  rw [columnProposal,he]
  have hfilter := congrArg (fun μ : PMF (Finset C) => μ S)
    (sampleColumns_filter p hp (univ : Finset C).toList (fun c => c ∈ N))
  calc
    _ = sampleColumns p hp ((univ : Finset C).toList.filter (fun c => decide (c ∈ N))) S :=
      by
        convert hfilter using 1
        apply congrArg (fun μ : PMF (Finset C) => μ S)
        apply congrArg (fun f : Finset C → Finset C => (sampleColumns p hp (univ : Finset C).toList).map f)
        funext T
        ext c
        simp only [mem_filter]
        all_goals
          apply congrArg (fun cs : List C => sampleColumns p hp cs S)
          apply congrArg (fun f : C → Bool => (univ : Finset C).toList.filter f)
          funext c
          by_cases hc : c ∈ N <;> simp [hc]
    _ = _ := ?_
  have hnodup := List.Nodup.filter (fun c : C => decide (c ∈ N))
    (univ : Finset C).nodup_toList
  rw [sampleColumns_apply _ _ _ hnodup]
  have hN : ((Finset.univ : Finset C).toList.filter (fun c => decide (c ∈ N))).toFinset = N := by
    ext c
    simp
  rw [hN]

theorem columnProposal_expMoment [Fintype C] (p : ℝ≥0) (hp : p ≤ 1)
    (row : C → Bool) (t : ℝ) :
    expMoment (columnProposal (C := C) p hp) (fun S => (sampleCount row S : ℝ)) t ≤
      ENNReal.ofReal (Real.exp ((Real.exp t-1) *
        ((p : ℝ) * sampleCount row univ))) := by
  have hnodup := (univ : Finset C).nodup_toList
  have hlaw := sampleColumns_count_law p hp row (univ : Finset C).toList hnodup
  have hm := rowDraw_sumMean p hp row (univ : Finset C).toList hnodup
  simp only [toList_toFinset] at hm
  have h := BoundedDraw.expMoment_sumLaw_le
    ((univ : Finset C).toList.map fun c => rowDraw p hp (row c)) t
  rw [hm, ← hlaw, expMoment_map] at h
  exact h

/-- Lower-tail bound for a directly sampled row count. -/
theorem columnProposal_lower [Fintype C] (p : ℝ≥0) (hp : p ≤ 1)
    (row : C → Bool) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mass (columnProposal (C := C) p hp)
      (fun S => (sampleCount row S : ℝ) ≤ (1-ε)*((p : ℝ)*sampleCount row univ)) ≤
      ENNReal.ofReal (Real.exp (-(ε^2*((p : ℝ)*sampleCount row univ)/4))) :=
  chernoff_lower _ _ (by positivity) hε hε1 (columnProposal_expMoment p hp row _)

/-- Upper-tail bound for the same directly sampled row count. -/
theorem columnProposal_upper [Fintype C] (p : ℝ≥0) (hp : p ≤ 1)
    (row : C → Bool) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mass (columnProposal (C := C) p hp)
      (fun S => (1+ε)*((p : ℝ)*sampleCount row univ) ≤ (sampleCount row S : ℝ)) ≤
      ENNReal.ofReal (Real.exp (-(ε^2*((p : ℝ)*sampleCount row univ)/4))) :=
  chernoff_upper _ _ (by positivity) hε hε1 (columnProposal_expMoment p hp row _)

/-- The count window remains fixed while other rows leave the bucket. -/
def bucketAccept (k : ℕ) (row : C → Bool) (S : Finset C) : Prop :=
  k ≤ sampleCount row S ∧ sampleCount row S ≤ 8*k

private theorem exp_neg_five_quarters_le : Real.exp (-(5/4 : ℝ)) ≤ 1/3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5/4) 4
  norm_num [sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
  linarith

private theorem exp_neg_five_le : Real.exp (-5 : ℝ) ≤ 1/6 := by
  have h := Real.add_one_le_exp (5 : ℝ)
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
  linarith

/-- A promised non-full bucket accepts a fixed row with probability at least
one half, by concentration of its actual finite column sample. -/
theorem bucketAccept_failure_le_half [Fintype C] (p : ℝ≥0) (hp : p ≤ 1)
    (row : C → Bool) (k : ℕ) (hk : 10 ≤ k)
    (hlo : 2*(k : ℝ) ≤ (p : ℝ)*sampleCount row univ)
    (hhi : (p : ℝ)*sampleCount row univ ≤ 4*(k : ℝ)) :
    rowProposal (columnProposal (C := C) p hp) (bucketAccept k row) none ≤
      (2 : ℝ≥0∞)⁻¹ := by
  let μ : ℝ := (p : ℝ)*sampleCount row univ
  have hkR : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hlower := columnProposal_lower p hp row
    (ε := (1 : ℝ)/2) (by norm_num) (by norm_num)
  have hupper := columnProposal_upper p hp row
    (ε := (1 : ℝ)) (by norm_num) (by norm_num)
  have hl : mass (columnProposal (C := C) p hp)
      (fun S => (sampleCount row S : ℝ) ≤ μ/2) ≤ ENNReal.ofReal (1/3 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-μ/16)) := by
        have hthreshold : (1-(1 : ℝ)/2)*μ = μ/2 := by ring
        have hexponent : -((1/(2 : ℝ))^2*μ/4) = -μ/16 := by ring
        change mass (columnProposal (C := C) p hp)
          (fun S => (sampleCount row S : ℝ) ≤ (1-(1 : ℝ)/2)*μ) ≤
          ENNReal.ofReal (Real.exp (-((1/(2 : ℝ))^2*μ/4))) at hlower
        rw [hthreshold,hexponent] at hlower
        exact hlower
      _ ≤ ENNReal.ofReal (Real.exp (-(5/4 : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        dsimp [μ]
        linarith
      _ ≤ _ := ENNReal.ofReal_le_ofReal exp_neg_five_quarters_le
  have hu : mass (columnProposal (C := C) p hp)
      (fun S => 2*μ ≤ (sampleCount row S : ℝ)) ≤ ENNReal.ofReal (1/6 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-μ/4)) := by
        simpa only [one_add_one_eq_two,one_pow,one_mul,neg_div,μ] using hupper
      _ ≤ ENNReal.ofReal (Real.exp (-5 : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        dsimp [μ]
        linarith
      _ ≤ _ := ENNReal.ofReal_le_ofReal exp_neg_five_le
  rw [rowProposal_none]
  calc
    _ ≤ mass (columnProposal (C := C) p hp) (fun S =>
        (sampleCount row S : ℝ) ≤ μ/2 ∨ 2*μ ≤ (sampleCount row S : ℝ)) := by
      apply mass_mono
      intro S hbad
      rcases not_and_or.mp hbad with h | h
      · have h' : (sampleCount row S : ℝ) < k := by exact_mod_cast lt_of_not_ge h
        exact Or.inl (by dsimp [μ]; linarith)
      · have h' : 8*(k : ℝ) < sampleCount row S := by
          exact_mod_cast lt_of_not_ge h
        exact Or.inr (by dsimp [μ]; linarith)
    _ ≤ mass (columnProposal (C := C) p hp)
        (fun S => (sampleCount row S : ℝ) ≤ μ/2) +
        mass (columnProposal (C := C) p hp)
        (fun S => 2*μ ≤ (sampleCount row S : ℝ)) := mass_or_le _ _ _
    _ ≤ ENNReal.ofReal (1/3 : ℝ) + ENNReal.ofReal (1/6 : ℝ) := add_le_add hl hu
    _ = _ := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num only [show (1/3 : ℝ)+1/6 = 1/2 by norm_num]
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num

@[simp] theorem sampleCoin_one : sampleCoin 1 (by rfl) = PMF.pure true := by
  ext b
  cases b <;> norm_num [sampleCoin_apply, PMF.pure_apply]

/-- Full sampling is a deterministic finite proposal, including empty columns. -/
@[simp] theorem sampleColumns_one (cs : List C) :
    sampleColumns 1 (by rfl) cs = PMF.pure cs.toFinset := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [sampleColumns, ih, PMF.pure_bind, PMF.pure_map]

@[simp] theorem columnProposal_one [Fintype C] :
    columnProposal (C := C) 1 (by rfl) = PMF.pure univ := by
  simp [columnProposal]

theorem bucketAccept_full [Fintype C] (row : C → Bool) (r k : ℕ)
    (hkr : k ≤ r) (hrk : r ≤ 2*k)
    (hdlo : r ≤ sampleCount row univ) (hdhi : sampleCount row univ ≤ 2*r) :
    bucketAccept k row univ := by
  constructor <;> omega

end ColumnSampling

section PendingRoundBound

variable [Fintype R] [DecidableEq R]

/-- The query-bearing rounds of every finite approximation have a uniform
logarithmic expected count. The only row premise is a derived one-proposal
failure bound; no independence between different rows is used. -/
theorem rowSamples_expected_rounds (μ : PMF Ω) (accept : R → Ω → Prop)
    (T L : ℕ) (hL : Fintype.card R ≤ 2^L)
    (h : ∀ r, rowProposal μ (accept r) none ≤ (2 : ℝ≥0∞)⁻¹) :
    (∑ t ∈ range T, mass (rowSamples μ accept t) (fun out => ∃ r, out r = none)) ≤
      (L : ℝ≥0∞)+2 := by
  let f : ℕ → ℝ≥0∞ := fun t =>
    mass (rowSamples μ accept t) (fun out => ∃ r, out r = none)
  have hsum : (∑ t ∈ range T, f t) ≤ ∑ t ∈ range (L+T), f t :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => bot_le)
  apply hsum.trans
  rw [sum_range_add]
  have hfirst : (∑ t ∈ range L, f t) ≤ (L : ℝ≥0∞) := by
    calc
      _ ≤ ∑ _t ∈ range L, (1 : ℝ≥0∞) :=
        sum_le_sum (fun t _ => mass_le_one _ _)
      _ = _ := by simp
  have htail : (∑ t ∈ range T, f (L+t)) ≤ 2 := by
    calc
      _ ≤ ∑ t ∈ range T, ((2 : ℝ≥0∞)⁻¹)^t := by
        apply sum_le_sum
        intro t _
        have hn : (Fintype.card R : ℝ≥0∞) ≤ (2 : ℝ≥0∞)^L := by
          exact_mod_cast hL
        calc
          f (L+t) ≤ (Fintype.card R : ℝ≥0∞)*((2 : ℝ≥0∞)⁻¹)^(L+t) :=
            rowSamples_unfinished_le μ accept _ h
          _ ≤ (2 : ℝ≥0∞)^L*((2 : ℝ≥0∞)⁻¹)^(L+t) :=
            mul_le_mul hn le_rfl bot_le bot_le
          _ = _ := by
            rw [pow_add, ← mul_assoc, ← mul_pow]
            rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_pow,one_mul]
      _ ≤ _ := geometric_attempts_ennreal_le_two T
  exact add_le_add hfirst htail

end PendingRoundBound

section Operational

variable {C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- The operational state contains only observed information. `proposal` records
the first accepted public column set, for an exact coupling with the sampling
law. It is not chosen using the hidden matrix. -/
structure BucketState (R C : Type) where
  proposal : R → Option (Finset C)
  learned : R → Option (Finset C)
  failed : Bool

def BucketState.initial : BucketState R C := ⟨fun _ => none, fun _ => none, false⟩

def BucketState.pending (st : BucketState R C) : Finset R := pendingRows st.proposal

def BucketState.complete (st : BucketState R C) : Prop :=
  st.failed = false ∧ st.pending = ∅

def BucketState.abort (st : BucketState R C) : BucketState R C :=
  { st with failed := true }

/-- A single real oracle reply per pending row. Validation applies to this
bilinear row count, with exactly the sampled-column cardinality as its range. -/
def validateRowCounts (P : Finset R) (S : Finset C) (answers : R → ℝ) : Option (R → ℕ) :=
  if h : ∀ r ∈ P, ∃ j : Fin (S.card+1), validateCount S.card (answers r) = some j then
    some (fun r => if hr : r ∈ P then (Classical.choose (h r hr)).val else 0)
  else none

theorem validateRowCounts_sound {P : Finset R} {S : Finset C} {answers : R → ℝ}
    {counts : R → ℕ} (h : validateRowCounts P S answers = some counts) :
    ∀ r ∈ P, (counts r : ℝ) = answers r ∧ counts r ≤ S.card := by
  unfold validateRowCounts at h
  split_ifs at h with hall
  · have he := Option.some.inj h
    intro r hr
    rw [← congrFun he r, dite_eq_left hr]
    exact validateCount_spec (Classical.choose_spec (hall r hr))

theorem validateRowCounts_of_nat (P : Finset R) (S : Finset C) (counts : R → ℕ)
    (hcount : ∀ r ∈ P, counts r ≤ S.card) :
    validateRowCounts P S (fun r => (counts r : ℝ)) =
      some (fun r => if r ∈ P then counts r else 0) := by
  have hall : ∀ r ∈ P, ∃ j : Fin (S.card+1),
      validateCount S.card (counts r : ℝ) = some j := by
    intro r hr
    exact ⟨⟨counts r, Nat.lt_succ_of_le (hcount r hr)⟩,
      validateCount_of_nat _ _ (hcount r hr)⟩
  rw [validateRowCounts, dite_eq_left hall]
  congr 1
  funext r
  by_cases hr : r ∈ P
  · simp only [dite_eq_left hr, ite_eq_left hr]
    have he := (validateCount_spec (Classical.choose_spec (hall r hr))).1
    exact_mod_cast he
  · simp only [dite_eq_right hr, ite_eq_right hr]

def rowCountProgram (P : Finset R) (S : Finset C) :
    DTree (BipartiteQuery R C) ℝ (Option (R → ℕ)) P.card :=
  (((DTree.queryList (fun r => ({r},S)) (fun _ => (0 : ℝ)) P.toList).cast
    (by simp)).map (validateRowCounts P S))

set_option backward.isDefEq.respectTransparency false in
theorem rowCountProgram_run (P : Finset R) (S : Finset C)
    (read : BipartiteQuery R C → ℝ) :
    DTree.run read (rowCountProgram P S) =
      (validateRowCounts P S (fun r => if r ∈ P then read ({r},S) else 0), P.card) := by
  simp [rowCountProgram, DTree.queryList_run]

/-- Relabel each oracle question by one public question, preserving both its
answer and its actual cost. -/
def relabelQuestions {I J A O : Type} (f : I → J) :
    {q : ℕ} → DTree I A O q → DTree J A O q
  | 0, o => o
  | _+1, Sum.inl o => Sum.inl o
  | _+1, Sum.inr (i,next) => DTree.query (f i) fun a => relabelQuestions f (next a)

theorem relabelQuestions_run {I J A O : Type} {q : ℕ} (f : I → J)
    (T : DTree I A O q) (read : J → A) :
    DTree.run read (relabelQuestions f T) = DTree.run (read ∘ f) T := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rcases T with o | ⟨i,next⟩
      · rfl
      · change ((DTree.run read (relabelQuestions f (next (read (f i))))).1,
          (DTree.run read (relabelQuestions f (next (read (f i))))).2+1) = _
        rw [ih]
        rfl

def acceptedRows (k : ℕ) (P : Finset R) (counts : R → ℕ) : Finset R :=
  P.filter fun r => k ≤ counts r ∧ counts r ≤ 8*k

def effectiveSparsity (k : ℕ) (C : Type) [Fintype C] : ℕ := min (8*k) (Fintype.card C)

def liftBucketQuery (A : Finset R) (S : Finset C) (q : BipartiteQuery A C) :
    BipartiteQuery R C := (q.1.map (Function.Embedding.subtype _), q.2 ∩ S)

def maskedMatrix (M : BooleanMatrix R C) (A : Finset R) (S : Finset C) :
    BooleanMatrix A C := fun r c => M r.1 c && decide (c ∈ S)

theorem maskedMatrix_bilinear (M : BooleanMatrix R C) (A : Finset R) (S : Finset C)
    (q : BipartiteQuery A C) :
    bilinear M (liftBucketQuery A S q) = bilinear (maskedMatrix M A S) q := by
  simp only [bilinear, liftBucketQuery, sum_map, Function.Embedding.subtype_apply,
    maskedMatrix]
  apply sum_congr rfl
  intro r _
  rw [← filter_mem_eq_inter, sum_filter]
  apply sum_congr rfl
  intro c _
  by_cases hc : c ∈ S <;> simp [hc]

theorem sparseRawBudget_le_dimensions (ell : ℕ) :
    sparseRawBudget R C ell ≤ Fintype.card R * Fintype.card C :=
  Nat.mul_le_mul (minimumFamily_card_le_dimension (box R ell))
    (minimumFamily_card_le_dimension (sparse C ell))

def BucketState.record (st : BucketState R C) (A : Finset R) (S : Finset C)
    (N : BooleanMatrix A C) : BucketState R C where
  proposal r := if hr : r ∈ A then some S else st.proposal r
  learned r := if hr : r ∈ A then some (univ.filter fun c => N ⟨r,hr⟩ c) else st.learned r
  failed := st.failed

/-- The decoder for a batch really calls the constructed separating-measurement
program. Its coarse index is finite on every answer path; the sharper expected
bound will charge the actual family size to this batch. -/
def decodeAccepted (k : ℕ) (st : BucketState R C) (S : Finset C) (counts : R → ℕ) :
    DTree (BipartiteQuery R C) ℝ (BucketState R C)
      (Fintype.card R * Fintype.card C) :=
  let A := acceptedRows k st.pending counts
  if hA : A.Nonempty then
    ((relabelQuestions (liftBucketQuery A S)
      (sparseBilinearProgram (R := A) (C := C) (effectiveSparsity k C))).map
        (fun out => match out with
          | none => st.abort
          | some N => st.record A S N)).weaken (by
            apply (sparseRawBudget_le_dimensions (R := A) (C := C) _).trans
            exact Nat.mul_le_mul_right _ (Fintype.card_subtype_le _))
  else DTree.pure st

def bucketRoundBudget (R C : Type) [Fintype R] [Fintype C] : ℕ :=
  Fintype.card R + Fintype.card R * Fintype.card C

/-- A count/decode round after its public random proposal has been drawn. Empty
or failed states halt immediately. Every pending honest round queries a row. -/
def bucketRoundWith (k : ℕ) (st : BucketState R C) (S : Finset C) :
    DTree (BipartiteQuery R C) ℝ (BucketState R C) (bucketRoundBudget R C) :=
  if st.failed = true ∨ st.pending = ∅ then DTree.pure st else
    ((rowCountProgram st.pending S).bind (fun counts => match counts with
      | none => DTree.pure st.abort
      | some a => decodeAccepted k st S a)).weaken (by
        unfold bucketRoundBudget
        exact Nat.add_le_add_right (card_le_univ _) _)

/-- Fixed bucket probability. In the full branch `r ≤ 2k`, every column is
selected, and the same actual decoder learns the full row. -/
def bucketProbability (r k : ℕ) : ℝ≥0 := min ((2*k : ℝ≥0)/(r : ℝ≥0)) 1

theorem bucketProbability_le_one (r k : ℕ) : bucketProbability r k ≤ 1 := min_le_right _ _

theorem bucketProbability_nonfull (r k : ℕ) (hrk : 2*k < r) :
    (bucketProbability r k : ℝ) = 2*(k : ℝ)/(r : ℝ) := by
  have hr : (0 : ℝ≥0) < r := by exact_mod_cast (show 0 < r by omega)
  have hkr : (2*k : ℝ≥0) ≤ r := by exact_mod_cast hrk.le
  rw [bucketProbability, min_eq_left ((div_le_one hr).mpr hkr)]
  simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast]

theorem bucketProbability_full (r k : ℕ) (hr : 0 < r) (hrk : r ≤ 2*k) :
    bucketProbability r k = 1 := by
  have hr' : (0 : ℝ≥0) < r := by exact_mod_cast hr
  have hkr : (r : ℝ≥0) ≤ 2*k := by exact_mod_cast hrk
  exact min_eq_right ((one_le_div hr').mpr hkr)

/-- The per-row geometric premise is derived for the fixed public bucket
sampler, including full sampling. It is not an input to the recovery program. -/
theorem bucket_row_reject_le_half (row : C → Bool) (r k : ℕ)
    (hk : 10 ≤ k) (hkr : k ≤ r)
    (hdlo : r ≤ sampleCount row univ) (hdhi : sampleCount row univ ≤ 2*r) :
    rowProposal (columnProposal (C := C) (bucketProbability r k)
      (bucketProbability_le_one r k)) (bucketAccept k row) none ≤ (2 : ℝ≥0∞)⁻¹ := by
  by_cases hrk : r ≤ 2*k
  · have hfull := bucketProbability_full r k (by omega) hrk
    have hac := bucketAccept_full row r k hkr hrk hdlo hdhi
    rw [rowProposal_none]
    simpa only [hfull] using
      (show mass (columnProposal (C := C) 1 (by rfl))
        (fun S => ¬bucketAccept k row S) ≤ (2 : ℝ≥0∞)⁻¹ by
          rw [columnProposal_one,mass_pure]
          simp [hac])
  · have hrk' : 2*k < r := lt_of_not_ge hrk
    have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hdlo' : (r : ℝ) ≤ sampleCount row univ := by exact_mod_cast hdlo
    have hdhi' : (sampleCount row univ : ℝ) ≤ 2*(r : ℝ) := by exact_mod_cast hdhi
    have hq : (0 : ℝ) ≤ 2*(k : ℝ)/(r : ℝ) := by positivity
    have hlo := mul_le_mul_of_nonneg_left hdlo' hq
    have hhi := mul_le_mul_of_nonneg_left hdhi' hq
    have he1 : (2*(k : ℝ)/(r : ℝ))*(r : ℝ) = 2*(k : ℝ) := by field_simp
    have he2 : (2*(k : ℝ)/(r : ℝ))*(2*(r : ℝ)) = 4*(k : ℝ) := by
      field_simp
      <;> ring
    rw [he1] at hlo
    rw [he2] at hhi
    apply bucketAccept_failure_le_half _ _ row k hk
    · simpa only [bucketProbability_nonfull r k hrk'] using hlo
    · simpa only [bucketProbability_nonfull r k hrk'] using hhi

def bucketRound (r k : ℕ) (st : BucketState R C) :
    RTree (BipartiteQuery R C) ℝ (BucketState R C) (bucketRoundBudget R C) :=
  RTree.mix ((columnProposal (C := C) (bucketProbability r k)
    (bucketProbability_le_one r k)).map fun S => RTree.ofDeterministic (bucketRoundWith k st S))

/-- The solver is constructed at a finite round horizon. This is an operational
tree, not an assumed infinite Las Vegas program. Its public cap is independent
of the hidden matrix and of all oracle answers. -/
def learnBucketRounds (r k : ℕ) : (T : ℕ) → BucketState R C →
    RTree (BipartiteQuery R C) ℝ (BucketState R C) (T * bucketRoundBudget R C)
  | 0, st => RTree.pure (PMF.pure st)
  | T+1, st => ((bucketRound r k st).bind (learnBucketRounds r k T)).cast
      (by rw [Nat.succ_mul, Nat.add_comm])

theorem learnBucketRounds_every_oracle (r k T : ℕ) (st : BucketState R C)
    (read : BipartiteQuery R C → ℝ) {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run read (learnBucketRounds r k T st)).support) :
    out.2 ≤ T * bucketRoundBudget R C := RTree.cost_le _ _ hout

theorem BucketState.record_pending (st : BucketState R C) (A : Finset R) (S : Finset C)
    (N : BooleanMatrix A C) : (st.record A S N).pending = st.pending \ A := by
  ext r
  by_cases hr : r ∈ A <;>
    simp [BucketState.pending, pendingRows, BucketState.record, hr, and_comm]

theorem BucketState.record_card (st : BucketState R C) (A : Finset R) (S : Finset C)
    (N : BooleanMatrix A C) (hA : A ⊆ st.pending) :
    (st.record A S N).pending.card+A.card = st.pending.card := by
  rw [BucketState.record_pending]
  exact card_sdiff_add_card_eq_card hA

theorem BucketState.record_empty (st : BucketState R C) (S : Finset C)
    (N : BooleanMatrix (∅ : Finset R) C) : st.record ∅ S N = st := by
  cases st
  simp [BucketState.record]

theorem maskedMatrix_row (M : BooleanMatrix R C) (A : Finset R) (S : Finset C) (r : A) :
    measure univ (rowVector (maskedMatrix M A S) r) = sampleCount (M r.1) S := by
  calc
    _ = ∑ c, if c ∈ S then (if M r.1 c then 1 else 0 : ℕ) else 0 := by
      apply sum_congr rfl
      intro c _
      by_cases hc : c ∈ S <;> simp [rowVector, maskedMatrix, hc]
    _ = _ := sum_ite_mem_eq S _

/-- Hidden-matrix semantics are used exclusively in the correctness proof. -/
def honestRowCounts (M : BooleanMatrix R C) (P : Finset R) (S : Finset C) : R → ℕ :=
  fun r => if r ∈ P then sampleCount (M r) S else 0

theorem rowCountProgram_honest (M : BooleanMatrix R C) (P : Finset R) (S : Finset C) :
    DTree.run (fun q => (bilinear M q : ℝ)) (rowCountProgram P S) =
      (some (honestRowCounts M P S),P.card) := by
  rw [rowCountProgram_run]
  have he : (fun r => if r ∈ P then (bilinear M ({r},S) : ℝ) else 0) =
      (fun r => (honestRowCounts M P S r : ℝ)) := by
    funext r
    by_cases hr : r ∈ P <;> simp [honestRowCounts, bilinear, sampleCount, hr]
  rw [he, validateRowCounts_of_nat P S (honestRowCounts M P S) (by
    intro r hr
    simpa only [honestRowCounts, ite_eq_left hr] using sampleCount_le_card (M r) S)]
  congr 2
  funext r
  by_cases hr : r ∈ P <;> simp [honestRowCounts, hr]

def semanticAccepted (M : BooleanMatrix R C) (k : ℕ) (P : Finset R) (S : Finset C) :
    Finset R := P.filter fun r => bucketAccept k (M r) S

theorem acceptedRows_honest (M : BooleanMatrix R C) (k : ℕ) (P : Finset R) (S : Finset C) :
    acceptedRows k P (honestRowCounts M P S) = semanticAccepted M k P S := by
  ext r
  by_cases hr : r ∈ P <;>
    simp [acceptedRows, semanticAccepted, honestRowCounts, bucketAccept, hr]

theorem maskedMatrix_sparse_accepted (M : BooleanMatrix R C) (k : ℕ) (P : Finset R)
    (S : Finset C) :
    RowSparse (effectiveSparsity k C) (maskedMatrix M (semanticAccepted M k P S) S) := by
  intro r
  rw [maskedMatrix_row]
  apply le_min
  · exact (mem_filter.mp r.2).2.2
  · exact (sampleCount_le_card (M r.1) S).trans (card_le_univ S)

/-- Exact true-input batch behavior, with the actual constructed decoder cost.
No supplied sparse-oracle contract occurs in this proof. -/
theorem decodeAccepted_honest_run (M : BooleanMatrix R C) (k : ℕ)
    (st : BucketState R C) (S : Finset C) :
    let A := semanticAccepted M k st.pending S
    DTree.run (fun q => (bilinear M q : ℝ))
      (decodeAccepted k st S (honestRowCounts M st.pending S)) =
        (st.record A S (maskedMatrix M A S), sparseRawBudget A C (effectiveSparsity k C)) := by
  dsimp only
  let A := acceptedRows k st.pending (honestRowCounts M st.pending S)
  have hAeq : A = semanticAccepted M k st.pending S :=
    acceptedRows_honest M k st.pending S
  calc
    _ = (st.record A S (maskedMatrix M A S),sparseRawBudget A C (effectiveSparsity k C)) := by
      by_cases hA : A.Nonempty
      · have hA' : (acceptedRows k st.pending (honestRowCounts M st.pending S)).Nonempty := hA
        simp only [decodeAccepted,dite_eq_left hA',DTree.run_weaken,
          DTree.run_map,relabelQuestions_run]
        change (match (DTree.run ((fun q => (bilinear M q : ℝ)) ∘ liftBucketQuery A S)
            (sparseBilinearProgram (effectiveSparsity k C))).1 with
              | none => st.abort
              | some N => st.record A S N,
            (DTree.run ((fun q => (bilinear M q : ℝ)) ∘ liftBucketQuery A S)
              (sparseBilinearProgram (effectiveSparsity k C))).2) = _
        have hread : ((fun q => (bilinear M q : ℝ)) ∘ liftBucketQuery A S) =
            (fun q => (bilinear (maskedMatrix M A S) q : ℝ)) := by
          funext q
          simp only [Function.comp_apply,maskedMatrix_bilinear]
        rw [hread]
        have hsparse : RowSparse (effectiveSparsity k C) (maskedMatrix M A S) :=
          (congrArg (fun B : Finset R =>
            RowSparse (effectiveSparsity k C) (maskedMatrix M B S)) hAeq).mpr
              (maskedMatrix_sparse_accepted M k st.pending S)
        have hrun : DTree.run (fun q => (bilinear (maskedMatrix M A S) q : ℝ))
            (sparseBilinearProgram (R := A) (C := C) (effectiveSparsity k C)) =
              (some (maskedMatrix M A S),sparseRawBudget A C (effectiveSparsity k C)) :=
          Prod.ext (sparseBilinearProgram_correct _ hsparse) (sparseBilinearProgram_cost _ _)
        rw [hrun]
      · have hzero : A = ∅ := not_nonempty_iff_eq_empty.mp hA
        have hbudget : sparseRawBudget A C (effectiveSparsity k C) = 0 := by
          apply Nat.eq_zero_of_le_zero
          have h := sparseRawBudget_le_dimensions (R := A) (C := C) (effectiveSparsity k C)
          simpa only [hzero,Fintype.card_coe,card_empty,zero_mul] using h
        have hA' : ¬(acceptedRows k st.pending (honestRowCounts M st.pending S)).Nonempty := hA
        simp only [decodeAccepted,dite_eq_right hA',DTree.run_pure]
        change (st,0) = (st.record A S (maskedMatrix M A S),sparseRawBudget A C (effectiveSparsity k C))
        rw [hbudget]
        have hrecord : st.record A S (maskedMatrix M A S) = st :=
          (congrArg (fun B : Finset R => st.record B S (maskedMatrix M B S) = st) hzero).mpr
            (BucketState.record_empty st S (maskedMatrix M ∅ S))
        rw [hrecord]
    _ = _ := congrArg (fun B : Finset R =>
      (st.record B S (maskedMatrix M B S),sparseRawBudget B C (effectiveSparsity k C))) hAeq

def honestRound (M : BooleanMatrix R C) (k : ℕ) (st : BucketState R C) (S : Finset C) :
    BucketState R C × ℕ :=
  if st.failed = true ∨ st.pending = ∅ then (st,0) else
    let A := semanticAccepted M k st.pending S
    (st.record A S (maskedMatrix M A S),
      st.pending.card+sparseRawBudget A C (effectiveSparsity k C))

theorem bucketRoundWith_honest_run (M : BooleanMatrix R C) (k : ℕ)
    (st : BucketState R C) (S : Finset C) :
    DTree.run (fun q => (bilinear M q : ℝ)) (bucketRoundWith k st S) = honestRound M k st S := by
  by_cases ht : st.failed = true ∨ st.pending = ∅
  · simp [bucketRoundWith, honestRound, ht]
  · simp only [bucketRoundWith, honestRound, ite_eq_right ht, DTree.run_weaken,
      DTree.run_bind,DTree.eval,DTree.cost,rowCountProgram_honest,decodeAccepted_honest_run]

theorem honestRound_failed (M : BooleanMatrix R C) (k : ℕ) (st : BucketState R C)
    (S : Finset C) : (honestRound M k st S).1.failed = st.failed := by
  unfold honestRound
  split <;> rfl

/-- Positive query progress of the implemented solver, including proposals that
accept no row. This is the source of the q+1 finite-horizon cap argument. -/
theorem honestRound_positive (M : BooleanMatrix R C) (k : ℕ) (st : BucketState R C)
    (S : Finset C) (hf : st.failed = false) (hp : st.pending.Nonempty) :
    1 ≤ (honestRound M k st S).2 := by
  have ht : ¬(st.failed = true ∨ st.pending = ∅) := by simp [hf, hp.ne_empty]
  simp only [honestRound, ite_eq_right ht]
  have hcard : 0 < st.pending.card := card_pos.mpr hp
  omega

theorem honestRound_pending_subset (M : BooleanMatrix R C) (k : ℕ)
    (st : BucketState R C) (S : Finset C) :
    (honestRound M k st S).1.pending ⊆ st.pending := by
  unfold honestRound
  split
  · exact Subset.rfl
  · rw [BucketState.record_pending]
    exact sdiff_subset

theorem bucketRound_honest_run (M : BooleanMatrix R C) (r k : ℕ)
    (st : BucketState R C) :
    RTree.run (fun q => (bilinear M q : ℝ)) (bucketRound r k st) =
      (columnProposal (C := C) (bucketProbability r k) (bucketProbability_le_one r k)).map
        (honestRound M k st) := by
  simp only [bucketRound, RTree.run_mix, PMF.bind_map, Function.comp_def,
    RTree.run_ofDeterministic, bucketRoundWith_honest_run]
  rfl

/-- The actual finite solver cannot leave an unfinished row after T rounds
without spending at least T queries. It also preserves the pending-row subset
and has no honest-input validation failure. -/
theorem learnBucketRounds_progress (M : BooleanMatrix R C) (r k T : ℕ)
    (st : BucketState R C) (hf : st.failed = false) {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (learnBucketRounds r k T st)).support) :
    out.1.failed = false ∧ out.1.pending ⊆ st.pending ∧
      (out.1.pending.Nonempty → T ≤ out.2) := by
  induction T generalizing st out with
  | zero =>
      have he : out = (st,0) := by
        simpa only [learnBucketRounds, RTree.run_pure, PMF.pure_map,
          PMF.mem_support_pure_iff] using hout
      subst out
      exact ⟨hf, Subset.rfl, fun _ => Nat.zero_le _⟩
  | succ T ih =>
      rw [learnBucketRounds, RTree.run_cast, RTree.run_bind] at hout
      obtain ⟨first,hfirst,hlater⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨later,hrest,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hlater
      rw [bucketRound_honest_run] at hfirst
      obtain ⟨S,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfirst
      have hf' : (honestRound M k st S).1.failed = false := (honestRound_failed M k st S).trans hf
      obtain ⟨hlf,hsub,hprogress⟩ := ih _ hf' hrest
      refine ⟨hlf,hsub.trans (honestRound_pending_subset M k st S),?_⟩
      intro hnonempty
      have hp : st.pending.Nonempty := hnonempty.mono
        (hsub.trans (honestRound_pending_subset M k st S))
      have hfirstcost := honestRound_positive M k st S hf hp
      have hlatercost := hprogress hnonempty
      dsimp only [Prod.snd]
      omega

theorem sampleCount_eq_filter_card (row : C → Bool) (S : Finset C) :
    sampleCount row S = (S.filter fun c => row c).card := by
  simp only [sampleCount, card_eq_sum_ones, sum_filter]

theorem maskedMatrix_neighbors (M : BooleanMatrix R C) (A : Finset R) (S : Finset C)
    (r : A) : (univ.filter fun c => maskedMatrix M A S r c) = (S.filter fun c => M r.1 c) := by
  ext c
  by_cases hc : c ∈ S <;> simp [maskedMatrix, hc]

/-- Proof-only realization of the public learned table. Each recorded row is
exactly its first accepted sample's true neighbors and contains at least k. -/
def BucketInvariant (M : BooleanMatrix R C) (k : ℕ) (st : BucketState R C) : Prop :=
  st.failed = false ∧ ∀ r,
    (st.proposal r = none ↔ st.learned r = none) ∧
    ∀ S, st.proposal r = some S →
      st.learned r = some (S.filter fun c => M r c) ∧ k ≤ (S.filter fun c => M r c).card

theorem BucketInvariant.initial (M : BooleanMatrix R C) (k : ℕ) :
    BucketInvariant M k BucketState.initial := by
  simp [BucketInvariant, BucketState.initial]

theorem BucketInvariant.honestRound (M : BooleanMatrix R C) (k : ℕ)
    (st : BucketState R C) (S : Finset C) (h : BucketInvariant M k st) :
    BucketInvariant M k (honestRound M k st S).1 := by
  unfold CutQueryComplexity.StarContraction2022.Recovery.honestRound
  split
  · exact h
  · refine ⟨h.1,?_⟩
    intro r
    by_cases hr : r ∈ semanticAccepted M k st.pending S
    · simp only [BucketState.record, dite_eq_left hr, Option.some_ne_none, iff_self,
        true_and]
      intro T hT
      have hST : S = T := Option.some.inj hT
      subst T
      refine ⟨congrArg some (maskedMatrix_neighbors M _ S ⟨r,hr⟩),?_⟩
      rw [← sampleCount_eq_filter_card]
      exact (mem_filter.mp hr).2.1
    · simpa only [BucketState.record, dite_eq_right hr] using h.2 r

theorem learnBucketRounds_invariant (M : BooleanMatrix R C) (r k T : ℕ)
    (st : BucketState R C) (h : BucketInvariant M k st) {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (learnBucketRounds r k T st)).support) : BucketInvariant M k out.1 := by
  induction T generalizing st out with
  | zero =>
      have he : out = (st,0) := by
        simpa only [learnBucketRounds, RTree.run_pure, PMF.pure_map,
          PMF.mem_support_pure_iff] using hout
      subst out
      exact h
  | succ T ih =>
      rw [learnBucketRounds, RTree.run_cast, RTree.run_bind] at hout
      obtain ⟨first,hfirst,hlater⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨later,hrest,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hlater
      rw [bucketRound_honest_run] at hfirst
      obtain ⟨S,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfirst
      exact ih (out := later) _ (BucketInvariant.honestRound M k st S h) hrest

/-- Every completed output of the actual program contains k distinct true
neighbors per row. Random completion probabilities are proved separately. -/
theorem learnBucketRounds_completed_correct (M : BooleanMatrix R C) (r k T : ℕ)
    {out : BucketState R C × ℕ}
    (hout : out ∈ (RTree.run (fun q => (bilinear M q : ℝ))
      (learnBucketRounds r k T BucketState.initial)).support)
    (hc : out.1.complete) :
    ∀ u, ∃ N, out.1.learned u = some N ∧ k ≤ N.card ∧ ∀ v ∈ N, M u v = true := by
  have h := learnBucketRounds_invariant M r k T _ (BucketInvariant.initial M k) hout
  intro u
  have hp : out.1.proposal u ≠ none := by
    intro hp
    have hm : u ∈ out.1.pending := by simp [BucketState.pending,pendingRows,hp]
    rw [hc.2] at hm
    exact notMem_empty u hm
  obtain ⟨S,hS⟩ := Option.ne_none_iff_exists'.mp hp
  obtain ⟨hlearn,hsize⟩ := (h.2 u).2 S hS
  refine ⟨S.filter (fun v => M u v),hlearn,hsize,?_⟩
  intro v hv
  exact (mem_filter.mp hv).2

def keepRecorded {X : Type} (old later : R → Option X) : R → Option X :=
  fun u => (old u).or (later u)

theorem honestRound_proposal (M : BooleanMatrix R C) (k : ℕ) (st : BucketState R C)
    (S : Finset C) (hf : st.failed = false) (u : R) :
    (honestRound M k st S).1.proposal u =
      (st.proposal u).or (if bucketAccept k (M u) S then some S else none) := by
  by_cases ht : st.failed = true ∨ st.pending = ∅
  · have hp : st.pending = ∅ := ht.resolve_left (by simp [hf])
    have hn : st.proposal u ≠ none := by
      intro hn
      have hm : u ∈ st.pending := by simp [BucketState.pending,pendingRows,hn]
      rw [hp] at hm
      exact notMem_empty u hm
    cases hu : st.proposal u <;> simp [honestRound,ht,hu] at hn ⊢
  · simp only [honestRound,ite_eq_right ht,BucketState.record]
    cases hu : st.proposal u <;> by_cases ha : bucketAccept k (M u) S <;>
      simp [semanticAccepted,BucketState.pending,pendingRows,hu,ha]

theorem bucketRound_honest_eval (M : BooleanMatrix R C) (r k : ℕ)
    (st : BucketState R C) :
    (bucketRound r k st).eval (fun q => (bilinear M q : ℝ)) =
      (columnProposal (C := C) (bucketProbability r k) (bucketProbability_le_one r k)).map
        (fun S => (honestRound M k st S).1) := by
  simp only [RTree.eval,bucketRound_honest_run,PMF.map_comp,Function.comp_def]

/-- Exact proposal law of the actual query program, with arbitrary already
recorded rows. Its only semantic input here is absence of an earlier failure. -/
theorem learnBucketRounds_recorded_law (M : BooleanMatrix R C) (r k T : ℕ)
    (st : BucketState R C) (hf : st.failed = false) :
    ((learnBucketRounds r k T st).eval (fun q => (bilinear M q : ℝ))).map
        BucketState.proposal =
      (rowSamples (columnProposal (C := C) (bucketProbability r k)
        (bucketProbability_le_one r k)) (fun u S => bucketAccept k (M u) S) T).map
          (keepRecorded st.proposal) := by
  induction T generalizing st with
  | zero =>
      simp only [learnBucketRounds,RTree.eval_pure,PMF.pure_map,rowSamples]
      congr 1
      funext u
      cases hu : st.proposal u <;> simp only [keepRecorded,hu,Option.or]
  | succ T ih =>
      rw [learnBucketRounds,RTree.eval_cast,RTree.eval_bind,PMF.map_bind,
        bucketRound_honest_eval,PMF.bind_map]
      simp only [Function.comp_def]
      have hf' : ∀ S, (honestRound M k st S).1.failed = false :=
        fun S => (honestRound_failed M k st S).trans hf
      simp_rw [ih _ (hf' _)]
      rw [rowSamples,PMF.map_bind]
      congr 1
      funext S
      rw [PMF.map_comp]
      congr 1
      funext later u
      simp only [keepRecorded,Function.comp_def,honestRound_proposal M k st S hf u]
      cases hu : st.proposal u <;> by_cases ha : bucketAccept k (M u) S <;>
        simp [hu,ha]

/-- The sampling law is attached to the actual implementation before any cap
event is introduced. Other rows may share every sampled column proposal. -/
theorem learnBucketRounds_proposal_law (M : BooleanMatrix R C) (r k T : ℕ) :
    ((learnBucketRounds r k T (BucketState.initial : BucketState R C)).eval
      (fun q => (bilinear M q : ℝ))).map BucketState.proposal =
      rowSamples (columnProposal (C := C) (bucketProbability r k)
        (bucketProbability_le_one r k)) (fun u S => bucketAccept k (M u) S) T := by
  have h := learnBucketRounds_recorded_law M r k T BucketState.initial rfl
  have he : keepRecorded (BucketState.initial : BucketState R C).proposal = id := by
    funext later u
    rfl
  rw [he,PMF.map_id] at h
  exact h

theorem learnBucketRounds_row_law (M : BooleanMatrix R C) (r k T : ℕ) (u : R) :
    ((learnBucketRounds r k T (BucketState.initial : BucketState R C)).eval
      (fun q => (bilinear M q : ℝ))).map (fun st => st.proposal u) =
      firstSuccess (rowProposal (columnProposal (C := C) (bucketProbability r k)
        (bucketProbability_le_one r k)) (bucketAccept k (M u))) T := by
  rw [← rowSamples_marginal _ (fun u S => bucketAccept k (M u) S) T u,
    ← learnBucketRounds_proposal_law M r k T,PMF.map_comp]
  rfl

theorem learnBucketRounds_completion_tail (M : BooleanMatrix R C) (r k T : ℕ)
    (hk : 10 ≤ k) (hkr : k ≤ r)
    (hdegree : ∀ u, r ≤ sampleCount (M u) univ ∧ sampleCount (M u) univ ≤ 2*r) :
    mass ((learnBucketRounds r k T (BucketState.initial : BucketState R C)).eval
      (fun q => (bilinear M q : ℝ))) (fun st => st.pending.Nonempty) ≤
        (Fintype.card R : ℝ≥0∞)*((2 : ℝ≥0∞)⁻¹)^T := by
  have h := rowSamples_unfinished_le
    (columnProposal (C := C) (bucketProbability r k) (bucketProbability_le_one r k))
    (fun u S => bucketAccept k (M u) S) T
    (fun u => bucket_row_reject_le_half (M u) r k hk hkr (hdegree u).1 (hdegree u).2)
  rw [← learnBucketRounds_proposal_law M r k T,mass_map] at h
  simpa only [BucketState.pending,pendingRows,filter_nonempty_iff,mem_univ,true_and] using h

theorem learnBucketRounds_head_run (r k T : ℕ) (st : BucketState R C)
    (read : BipartiteQuery R C → ℝ) :
    RTree.run read (learnBucketRounds r k (T+1) st) =
      (RTree.run read (bucketRound r k st)).bind fun first =>
        (RTree.run read (learnBucketRounds r k T first.1)).map
          (fun later => (later.1,first.2+later.2)) := by
  rw [learnBucketRounds,RTree.run_cast,RTree.run_bind]

/-- A finite semigroup identity for the actual run, preserving accumulated cost.
It permits summing the cost of the last round over earlier output distributions. -/
theorem learnBucketRounds_snoc_run (r k T : ℕ) (st : BucketState R C)
    (read : BipartiteQuery R C → ℝ) :
    RTree.run read (learnBucketRounds r k (T+1) st) =
      (RTree.run read (learnBucketRounds r k T st)).bind fun before =>
        (RTree.run read (bucketRound r k before.1)).map
          (fun after => (after.1,before.2+after.2)) := by
  induction T generalizing st with
  | zero =>
      rw [learnBucketRounds_head_run]
      simp only [learnBucketRounds,RTree.run_pure,PMF.pure_map,PMF.pure_bind,
        PMF.bind_pure,PMF.map_comp,Function.comp_def,Nat.add_zero,Nat.zero_add] <;> rfl
  | succ T ih =>
      conv_lhs => rw [learnBucketRounds_head_run]
      conv_rhs => rw [learnBucketRounds_head_run]
      simp_rw [ih]
      simp only [PMF.map_bind,PMF.bind_map,PMF.bind_bind,PMF.map_comp,
        Function.comp_def,Nat.add_assoc]

theorem learnBucketRounds_snoc_eval (r k T : ℕ) (st : BucketState R C)
    (read : BipartiteQuery R C → ℝ) :
    (learnBucketRounds r k (T+1) st).eval read =
      ((learnBucketRounds r k T st).eval read).bind fun before =>
        (bucketRound r k before).eval read := by
  simp only [RTree.eval,learnBucketRounds_snoc_run,PMF.map_bind,PMF.map_comp,
    PMF.bind_map,Function.comp_def]

theorem learnBucketRounds_snoc_expected (r k T : ℕ) (st : BucketState R C)
    (read : BipartiteQuery R C → ℝ) :
    (learnBucketRounds r k (T+1) st).expectedQueries read =
      (learnBucketRounds r k T st).expectedQueries read +
        expect ((learnBucketRounds r k T st).eval read)
          (fun before => (bucketRound r k before).expectedQueries read) := by
  change expect (RTree.run read (learnBucketRounds r k (T+1) st)) (fun out => (out.2 : ℝ≥0∞)) = _
  rw [learnBucketRounds_snoc_run,expect_bind]
  simp only [expect_map,Nat.cast_add,expect_add,expect_const]
  change _ + expect (RTree.run read (learnBucketRounds r k T st))
    (fun x => (bucketRound r k x.1).expectedQueries read) =
    _ + expect ((RTree.run read (learnBucketRounds r k T st)).map Prod.fst)
      (fun x => (bucketRound r k x).expectedQueries read)
  simp only [expect_map] <;> rfl

end Operational

section DecoderAmortization

/-- The exact size-dependent denominator that must be retained for small
batches. Zero accepted rows require no decoder queries. -/
def decoderWeight (b : ℕ) : ℝ := if b = 0 then 0 else (b : ℝ)/Real.log (2*(b : ℝ))

theorem decoderWeight_nonneg (b : ℕ) : 0 ≤ decoderWeight b := by
  by_cases hb : b = 0
  · simp [decoderWeight, hb]
  · have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    simp only [decoderWeight, ite_eq_right hb]
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))

/-- Large batches are charged to their distinct rows. Small positive batches
are charged to the number of query-bearing rounds, using the same sparse
decoder even when the total number of rows is bounded. -/
theorem decoderWeight_affine (s b : ℕ) (hs : 1 ≤ s) :
    decoderWeight b ≤ 2*(b : ℝ)/Real.log (2*(s : ℝ)) +
      (Real.sqrt (s : ℝ)/Real.log 2)*(if b = 0 then 0 else 1) := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hw : 0 < Real.log (2*(s : ℝ)) := Real.log_pos (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hb : b = 0
  · simp [decoderWeight, hb]
  · have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    have hv : 0 < Real.log (2*(b : ℝ)) := Real.log_pos (by linarith)
    simp only [decoderWeight, ite_eq_right hb, mul_one]
    by_cases hlarge : Real.sqrt (s : ℝ) ≤ b
    · have hsq : (s : ℝ) ≤ (b : ℝ)^2 := by
        have hh := Real.sq_sqrt (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
        nlinarith [Real.sqrt_nonneg (s : ℝ)]
      have hlog : Real.log (2*(s : ℝ)) ≤ 2*Real.log (2*(b : ℝ)) := by
        have h := Real.log_le_log (by linarith : (0 : ℝ) < 2*(s : ℝ))
          (show 2*(s : ℝ) ≤ (2*(b : ℝ))^2 by nlinarith)
        simpa only [Real.log_pow, Nat.cast_ofNat] using h
      have hmain : (b : ℝ)/Real.log (2*(b : ℝ)) ≤
          2*(b : ℝ)/Real.log (2*(s : ℝ)) := by
        apply (div_le_div_iff₀ hv hw).mpr
        nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
      exact hmain.trans (le_add_of_nonneg_right (by positivity))
    · have hlog : Real.log 2 ≤ Real.log (2*(b : ℝ)) :=
        Real.log_le_log (by norm_num) (by linarith)
      have hmain : (b : ℝ)/Real.log (2*(b : ℝ)) ≤ Real.sqrt (s : ℝ)/Real.log 2 := by
        calc
          _ ≤ (b : ℝ)/Real.log 2 := div_le_div_of_nonneg_left (Nat.cast_nonneg _) h2 hlog
          _ ≤ _ := div_le_div_of_nonneg_right (le_of_not_ge hlarge) h2.le
      exact hmain.trans (le_add_of_nonneg_left (by positivity))

def rowLogHorizon (s : ℕ) : ℕ := ⌈Real.log (s : ℝ)/Real.log 2⌉₊

theorem rowLogHorizon_covers (s : ℕ) (hs : 1 ≤ s) : s ≤ 2^(rowLogHorizon s) := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (div_le_iff₀ h2).mp (Nat.le_ceil (Real.log (s : ℝ)/Real.log 2))
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_log (by linarith), Real.exp_nat_mul, Real.exp_log (by norm_num)] at he
  exact_mod_cast he

theorem rowLogHorizon_le (s : ℕ) (hs : 1 ≤ s) :
    (rowLogHorizon s : ℝ) ≤ Real.log (2*(s : ℝ))/Real.log 2+1 := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hsR
  have hc := (Nat.ceil_lt_add_one (div_nonneg hlog h2.le)).le
  apply hc.trans
  exact add_le_add (div_le_div_of_nonneg_right
    (Real.log_le_log (by linarith : (0 : ℝ) < s)
      (show (s : ℝ) ≤ 2*(s : ℝ) by linarith)) h2.le) (le_refl 1)

/-- The explicit constant for the expected small-batch charge. This estimate
is uniform in s; it never switches to dense full learning for small s. -/
theorem decoderWeight_round_bound (s : ℕ) (hs : 1 ≤ s) :
    2*(s : ℝ)/Real.log (2*(s : ℝ)) +
      (Real.sqrt (s : ℝ)/Real.log 2)*((rowLogHorizon s : ℝ)+2) ≤
        90*(s : ℝ)/Real.log (2*(s : ℝ)) := by
  let w := Real.log (2*(s : ℝ))
  let a := Real.sqrt (s : ℝ)
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hw : 0 < w := Real.log_pos (by linarith)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2 = (s : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hlog2 : (1 : ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hinv : (1 : ℝ)/Real.log 2 ≤ 2 := (div_le_iff₀ hlog2pos).mpr (by linarith)
  have hL := rowLogHorizon_le s hs
  have hwdiv : w/Real.log 2 ≤ 2*w := by
    have h := mul_le_mul_of_nonneg_left hinv hw.le
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm w 2] using h
  have hrounds : (rowLogHorizon s : ℝ)+2 ≤ 2*w+3 := by linarith
  have hascale : a/Real.log 2 ≤ 2*a := by
    have h := mul_le_mul_of_nonneg_left hinv ha
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm a 2] using h
  have hsmall : (a/Real.log 2)*((rowLogHorizon s : ℝ)+2) ≤ a*(4*w+6) := by
    calc
      _ ≤ (2*a)*(2*w+3) := mul_le_mul hascale hrounds (by positivity) (by positivity)
      _ = _ := by ring
  obtain ⟨hwsq, hwlin⟩ := log_double_bounds hsR
  have hm1 := mul_le_mul_of_nonneg_left hwsq (show 0 ≤ 4*a by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hwlin (show 0 ≤ 6*a by positivity)
  have hnum : (a*(4*w+6))*w ≤ 88*(s : ℝ) := by
    change w^2 ≤ 16*a at hwsq
    change w ≤ 4*a at hwlin
    change 4*a*w^2 ≤ 4*a*(16*a) at hm1
    change 6*a*w ≤ 6*a*(4*a) at hm2
    nlinarith
  have hdiv : a*(4*w+6) ≤ 88*(s : ℝ)/w := (le_div_iff₀ hw).mpr hnum
  calc
    _ ≤ 2*(s : ℝ)/w + 88*(s : ℝ)/w :=
      add_le_add (le_refl _) (hsmall.trans hdiv)
    _ = _ := by ring

end DecoderAmortization

section ExpectedCost

variable {C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

def decoderScale (k t : ℕ) : ℝ := 16777216*(8*(k : ℝ))*Real.log (2*(t : ℝ))

def acceptedRowCharge (s t k : ℕ) : ℝ := 2*decoderScale k t/Real.log (2*(s : ℝ))

def activeRoundCharge (s t k : ℕ) : ℝ := decoderScale k t*Real.sqrt (s : ℝ)/Real.log 2

theorem decoderScale_nonneg (k t : ℕ) (ht : 1 ≤ t) : 0 ≤ decoderScale k t := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))

theorem acceptedRowCharge_nonneg (s t k : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    0 ≤ acceptedRowCharge s t k := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  exact div_nonneg (mul_nonneg (by norm_num) (decoderScale_nonneg k t ht))
    (Real.log_nonneg (by linarith))

theorem activeRoundCharge_nonneg (s t k : ℕ) (ht : 1 ≤ t) :
    0 ≤ activeRoundCharge s t k := by
  exact div_nonneg (mul_nonneg (decoderScale_nonneg k t ht) (Real.sqrt_nonneg _))
    (Real.log_nonneg (by norm_num))

/-- The actual separating decoder cost, including the empty batch, has the
sharp denominator needed by the amortized analysis. -/
theorem sparseRawBudget_le_scaled_weight (k : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ Fintype.card C) :
    (sparseRawBudget R C (effectiveSparsity k C) : ℝ) ≤
      decoderScale k (Fintype.card C)*decoderWeight (Fintype.card R) := by
  by_cases hR : Fintype.card R = 0
  · have hz : sparseRawBudget R C (effectiveSparsity k C) = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hR,zero_mul] using
        (sparseRawBudget_le_dimensions (R := R) (C := C) (effectiveSparsity k C))
    simp [hz,hR,decoderWeight]
  · have hR1 : 1 ≤ Fintype.card R := by omega
    have hRR : (1 : ℝ) ≤ Fintype.card R := by exact_mod_cast hR1
    have htR : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast ht
    have hell : 1 ≤ effectiveSparsity k C := by unfold effectiveSparsity; omega
    have hellt : effectiveSparsity k C ≤ Fintype.card C := min_le_right _ _
    have hellk : (effectiveSparsity k C : ℝ) ≤ 8*(k : ℝ) := by
      exact_mod_cast min_le_left (8*k) (Fintype.card C)
    have hlogt : 0 ≤ Real.log (2*(Fintype.card C : ℝ)) := Real.log_nonneg (by linarith)
    have hlogs : 0 < Real.log (2*(Fintype.card R : ℝ)) := Real.log_pos (by linarith)
    calc
      _ ≤ 16777216*(effectiveSparsity k C : ℝ)*(Fintype.card R : ℝ)*
          Real.log (2*(Fintype.card C : ℝ))/Real.log (2*(Fintype.card R : ℝ)) :=
        sparseRawBudget_bound _ hR1 hell hellt
      _ ≤ 16777216*(8*(k : ℝ))*(Fintype.card R : ℝ)*
          Real.log (2*(Fintype.card C : ℝ))/Real.log (2*(Fintype.card R : ℝ)) := by gcongr
      _ = _ := by simp only [decoderScale,decoderWeight,ite_eq_right hR]; ring

/-- A batch is paid for by the distinct rows it removes and one active-round
charge. Both coefficients are public; the decoder is still the actual sparse
measurement program on all original columns. -/
theorem honestRound_amortized (M : BooleanMatrix R C) (k : ℕ) (st : BucketState R C)
    (S : Finset C) (hk : 1 ≤ k) (hs : 1 ≤ Fintype.card R) (ht : 1 ≤ Fintype.card C)
    (hf : st.failed = false) :
    ((honestRound M k st S).2 : ℝ) +
      acceptedRowCharge (Fintype.card R) (Fintype.card C) k *
        (honestRound M k st S).1.pending.card ≤
      (st.pending.card : ℝ) +
        acceptedRowCharge (Fintype.card R) (Fintype.card C) k*st.pending.card +
        activeRoundCharge (Fintype.card R) (Fintype.card C) k*
          (if st.pending.Nonempty then 1 else 0) := by
  by_cases hP : st.pending = ∅
  · simp [honestRound,hP]
  · have hP' : st.pending.Nonempty := nonempty_iff_ne_empty.mpr hP
    have hterminal : ¬(st.failed = true ∨ st.pending = ∅) := by simp [hf,hP]
    let A := semanticAccepted M k st.pending S
    have hA : A ⊆ st.pending := filter_subset _ _
    have hcard := BucketState.record_card st A S (maskedMatrix M A S) hA
    have hcardR : ((st.record A S (maskedMatrix M A S)).pending.card : ℝ)+A.card =
        st.pending.card := by exact_mod_cast hcard
    have hraw := sparseRawBudget_le_scaled_weight (R := A) (C := C) k hk ht
    simp only [Fintype.card_coe] at hraw
    have hw := decoderWeight_affine (Fintype.card R) A.card hs
    have hscale := decoderScale_nonneg k (Fintype.card C) ht
    have hscaled := mul_le_mul_of_nonneg_left hw hscale
    have hcharge :
        (sparseRawBudget A C (effectiveSparsity k C) : ℝ) ≤
          acceptedRowCharge (Fintype.card R) (Fintype.card C) k*A.card +
            activeRoundCharge (Fintype.card R) (Fintype.card C) k := by
      apply (hraw.trans hscaled).trans
      have ha := activeRoundCharge_nonneg (Fintype.card R) (Fintype.card C) k ht
      by_cases hA0 : A.card = 0
      · simpa only [ite_eq_left hA0,hA0,ite_true,Nat.cast_zero,mul_zero,zero_div,
          zero_add,add_zero] using ha
      · simp only [ite_eq_right hA0]
        dsimp only [acceptedRowCharge,activeRoundCharge]
        apply le_of_eq
        ring
    have hpotential := congrArg
      (fun x : ℝ => acceptedRowCharge (Fintype.card R) (Fintype.card C) k*x) hcardR
    simp only [honestRound,ite_eq_right hterminal,ite_eq_left hP',Nat.cast_add]
    dsimp only [A] at hcharge hpotential
    nlinarith

theorem bucketRound_amortized (M : BooleanMatrix R C) (r k : ℕ) (st : BucketState R C)
    (hk : 1 ≤ k) (hs : 1 ≤ Fintype.card R) (ht : 1 ≤ Fintype.card C)
    (hf : st.failed = false) :
    (bucketRound r k st).expectedQueries (fun q => (bilinear M q : ℝ)) +
      ENNReal.ofReal (acceptedRowCharge (Fintype.card R) (Fintype.card C) k)*
        expect ((bucketRound r k st).eval (fun q => (bilinear M q : ℝ)))
          (fun next => (next.pending.card : ℝ≥0∞)) ≤
      (st.pending.card : ℝ≥0∞) +
        ENNReal.ofReal (acceptedRowCharge (Fintype.card R) (Fintype.card C) k)*st.pending.card +
        ENNReal.ofReal (activeRoundCharge (Fintype.card R) (Fintype.card C) k)*
          (if st.pending.Nonempty then 1 else 0) := by
  have ha := acceptedRowCharge_nonneg (Fintype.card R) (Fintype.card C) k hs ht
  have hb := activeRoundCharge_nonneg (Fintype.card R) (Fintype.card C) k ht
  change expect (RTree.run _ (bucketRound r k st)) (fun out => (out.2 : ℝ≥0∞)) + _ ≤ _
  rw [bucketRound_honest_run,expect_map,bucketRound_honest_eval,expect_map,
    ← expect_const_mul,← expect_add]
  apply expect_le_of_le_on_support
  intro S _
  have h := ENNReal.ofReal_le_ofReal (honestRound_amortized M k st S hk hs ht hf)
  by_cases hP : st.pending.Nonempty
  · simpa only [ite_eq_left hP,mul_one,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg ha (Nat.cast_nonneg _)),
      ENNReal.ofReal_add (add_nonneg (Nat.cast_nonneg _) (mul_nonneg ha (Nat.cast_nonneg _))) hb,
      ENNReal.ofReal_natCast,ENNReal.ofReal_mul ha] using h
  · simpa only [ite_eq_right hP,mul_zero,add_zero,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg ha (Nat.cast_nonneg _)),
      ENNReal.ofReal_natCast,ENNReal.ofReal_mul ha] using h


/-- Honest executions preserve the no-abort flag, including after all rows
have completed and every subsequent public round costs zero. -/
theorem learnBucketRounds_eval_failed (M : BooleanMatrix R C) (r k T : ℕ)
    {st : BucketState R C}
    (hst : st ∈ ((learnBucketRounds r k T BucketState.initial).eval
      (fun q => (bilinear M q : ℝ))).support) : st.failed = false := by
  rw [RTree.eval] at hst
  obtain ⟨out,hout,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hst
  obtain ⟨hf,_,_⟩ := learnBucketRounds_progress M r k T BucketState.initial rfl hout
  simpa only [he] using hf

/-- Finite telescoping of the actual decoder and count-query costs. The
potential counts rows still pending, so each successful row is charged once. -/
theorem learnBucketRounds_amortized (M : BooleanMatrix R C) (r k T : ℕ)
    (hk : 1 ≤ k) (hs : 1 ≤ Fintype.card R) (ht : 1 ≤ Fintype.card C) :
    (learnBucketRounds r k T (BucketState.initial : BucketState R C)).expectedQueries
        (fun q => (bilinear M q : ℝ)) +
      ENNReal.ofReal (acceptedRowCharge (Fintype.card R) (Fintype.card C) k)*
        expect ((learnBucketRounds r k T BucketState.initial).eval
          (fun q => (bilinear M q : ℝ))) (fun st => (st.pending.card : ℝ≥0∞)) ≤
      (∑ j ∈ range T, expect ((learnBucketRounds r k j BucketState.initial).eval
        (fun q => (bilinear M q : ℝ))) (fun st => (st.pending.card : ℝ≥0∞))) +
      ENNReal.ofReal (acceptedRowCharge (Fintype.card R) (Fintype.card C) k)*Fintype.card R +
      ENNReal.ofReal (activeRoundCharge (Fintype.card R) (Fintype.card C) k)*
        ∑ j ∈ range T, mass ((learnBucketRounds r k j BucketState.initial).eval
          (fun q => (bilinear M q : ℝ))) (fun st => st.pending.Nonempty) := by
  let read : BipartiteQuery R C → ℝ := fun q => bilinear M q
  let a := ENNReal.ofReal (acceptedRowCharge (Fintype.card R) (Fintype.card C) k)
  let b := ENNReal.ofReal (activeRoundCharge (Fintype.card R) (Fintype.card C) k)
  let P : ℕ → PMF (BucketState R C) := fun j =>
    (learnBucketRounds r k j BucketState.initial).eval read
  let pending : BucketState R C → ℝ≥0∞ := fun st => st.pending.card
  let active : ℕ → ℝ≥0∞ := fun j => mass (P j) (fun st => st.pending.Nonempty)
  change _ + a*expect (P T) pending ≤
    (∑ j ∈ range T, expect (P j) pending) + a*Fintype.card R + b*∑ j ∈ range T, active j
  induction T with
  | zero =>
      change expect (RTree.run read (learnBucketRounds r k 0 BucketState.initial))
          (fun out => (out.2 : ℝ≥0∞)) + a*expect (P 0) pending ≤ _
      simp only [P,learnBucketRounds,RTree.run_pure,PMF.pure_map,RTree.eval_pure,
        expect_pure,Nat.cast_zero,pending,BucketState.initial,BucketState.pending,
        pendingRows,filter_true,card_univ,range_zero,sum_empty,mul_zero,zero_add,add_zero,le_refl]
  | succ T ih =>
      have hstep :
          (learnBucketRounds r k (T+1) (BucketState.initial : BucketState R C)).expectedQueries read +
            a*expect (P (T+1)) pending ≤
          ((learnBucketRounds r k T (BucketState.initial : BucketState R C)).expectedQueries read +
            a*expect (P T) pending) + expect (P T) pending + b*active T := by
        have hp : P (T+1) = (P T).bind (fun st => (bucketRound r k st).eval read) :=
          learnBucketRounds_snoc_eval r k T BucketState.initial read
        have hactive : expect (P T) (fun st => if st.pending.Nonempty then (1 : ℝ≥0∞) else 0) =
            active T := by
          rw [Probability.expect]
          dsimp only [active]
          rw [mass_eq_tsum]
          apply tsum_congr
          intro st
          by_cases hst : st.pending.Nonempty <;> simp [hst]
        rw [learnBucketRounds_snoc_expected,hp,expect_bind]
        calc
          _ = (learnBucketRounds r k T (BucketState.initial : BucketState R C)).expectedQueries read +
              expect (P T) (fun st => (bucketRound r k st).expectedQueries read +
                a*expect ((bucketRound r k st).eval read) pending) := by
            rw [expect_add,expect_const_mul]
            ac_rfl
          _ ≤ (learnBucketRounds r k T (BucketState.initial : BucketState R C)).expectedQueries read +
              expect (P T) (fun st => pending st+a*pending st+
                b*(if st.pending.Nonempty then 1 else 0)) := by
            apply add_le_add (le_refl _)
            apply expect_mono_on_support
            intro st hst
            exact bucketRound_amortized M r k st hk hs ht
              (learnBucketRounds_eval_failed M r k T hst)
          _ = _ := by
            simp only [expect_add,expect_const_mul,hactive]
            ac_rfl
      apply hstep.trans
      calc
        _ ≤ ((∑ j ∈ range T, expect (P j) pending)+a*Fintype.card R+
            b*∑ j ∈ range T, active j)+expect (P T) pending+b*active T :=
          add_le_add (add_le_add ih (le_refl _)) (le_refl _)
        _ = _ := by rw [sum_range_succ,sum_range_succ,mul_add]; ac_rfl

theorem learnBucketRounds_expected_pending (M : BooleanMatrix R C) (r k T : ℕ) :
    expect ((learnBucketRounds r k T (BucketState.initial : BucketState R C)).eval
      (fun q => (bilinear M q : ℝ))) (fun st => (st.pending.card : ℝ≥0∞)) =
    expect (rowSamples (columnProposal (C := C) (bucketProbability r k)
      (bucketProbability_le_one r k)) (fun u S => bucketAccept k (M u) S) T)
        (fun out => ((pendingRows out).card : ℝ≥0∞)) := by
  rw [← learnBucketRounds_proposal_law M r k T,expect_map]
  rfl

theorem learnBucketRounds_active_mass (M : BooleanMatrix R C) (r k T : ℕ) :
    mass ((learnBucketRounds r k T (BucketState.initial : BucketState R C)).eval
      (fun q => (bilinear M q : ℝ))) (fun st => st.pending.Nonempty) =
    mass (rowSamples (columnProposal (C := C) (bucketProbability r k)
      (bucketProbability_le_one r k)) (fun u S => bucketAccept k (M u) S) T)
        (fun out => ∃ u, out u = none) := by
  rw [← learnBucketRounds_proposal_law M r k T,mass_map]
  congr 1
  funext st
  simp only [BucketState.pending,pendingRows,filter_nonempty_iff,mem_univ,true_and]

/-- Geometric count-query and active-round sums are attached to the actual
query process through its previously proved first-success law. -/
theorem learnBucketRounds_expected_le_charges (M : BooleanMatrix R C) (r k T : ℕ)
    (hk : 10 ≤ k) (hkr : k ≤ r) (hs : 1 ≤ Fintype.card R) (ht : 1 ≤ Fintype.card C)
    (hdegree : ∀ u, r ≤ sampleCount (M u) univ ∧ sampleCount (M u) univ ≤ 2*r) :
    (learnBucketRounds r k T (BucketState.initial : BucketState R C)).expectedQueries
      (fun q => (bilinear M q : ℝ)) ≤
    2*(Fintype.card R : ℝ≥0∞) +
      ENNReal.ofReal (acceptedRowCharge (Fintype.card R) (Fintype.card C) k)*Fintype.card R +
      ENNReal.ofReal (activeRoundCharge (Fintype.card R) (Fintype.card C) k)*
        ((rowLogHorizon (Fintype.card R) : ℝ≥0∞)+2) := by
  have hrow := fun u => bucket_row_reject_le_half (M u) r k hk hkr
    (hdegree u).1 (hdegree u).2
  have hcounts := rowSamples_total_expected_counts
    (columnProposal (C := C) (bucketProbability r k) (bucketProbability_le_one r k))
    (fun u S => bucketAccept k (M u) S) T hrow
  have hrounds := rowSamples_expected_rounds
    (columnProposal (C := C) (bucketProbability r k) (bucketProbability_le_one r k))
    (fun u S => bucketAccept k (M u) S) T (rowLogHorizon (Fintype.card R))
    (rowLogHorizon_covers (Fintype.card R) hs) hrow
  have hamortized := learnBucketRounds_amortized M r k T (by omega) hs ht
  apply (le_add_of_nonneg_right (by positivity)).trans hamortized |>.trans
  apply add_le_add
  · apply add_le_add _ (le_refl _)
    simpa only [learnBucketRounds_expected_pending] using hcounts
  · exact mul_le_mul_right (by
      simpa only [learnBucketRounds_active_mass] using hrounds) _

/-- One fixed numerical constant for primitive B. -/
def bucketConstant : ℕ := 1099511627776

/-- A public bound, valid for every finite horizon. Its definition depends only
on the row and column alphabet sizes and the requested degree parameter. -/
def bucketExpectedBound (R C : Type) [Fintype R] [Fintype C] (k : ℕ) : ℝ :=
  (bucketConstant : ℝ)*((Fintype.card R : ℝ)+
    (k : ℝ)*Fintype.card R*Real.log (2*(Fintype.card C : ℝ))/
      Real.log (2*(Fintype.card R : ℝ)))

theorem bucketExpectedBound_nonneg (k : ℕ) (hs : 1 ≤ Fintype.card R)
    (ht : 1 ≤ Fintype.card C) : 0 ≤ bucketExpectedBound R C k := by
  have hsR : (1 : ℝ) ≤ Fintype.card R := by exact_mod_cast hs
  have htR : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast ht
  unfold bucketExpectedBound
  exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _)
    (div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
      (Real.log_nonneg (by linarith))))

theorem bucket_charges_le_bound (k : ℕ) (hs : 1 ≤ Fintype.card R) (ht : 1 ≤ Fintype.card C) :
    2*(Fintype.card R : ℝ)+
      acceptedRowCharge (Fintype.card R) (Fintype.card C) k*Fintype.card R+
      activeRoundCharge (Fintype.card R) (Fintype.card C) k*
        ((rowLogHorizon (Fintype.card R) : ℝ)+2) ≤ bucketExpectedBound R C k := by
  let s := Fintype.card R
  let t := Fintype.card C
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hscale := decoderScale_nonneg k t ht
  have hlog : 0 < Real.log (2*(s : ℝ)) := Real.log_pos (by linarith)
  have hlogt : 0 ≤ Real.log (2*(t : ℝ)) := Real.log_nonneg (by linarith)
  have hamort := mul_le_mul_of_nonneg_left (decoderWeight_round_bound s hs) hscale
  have hcharge :
      acceptedRowCharge s t k*(s : ℝ)+activeRoundCharge s t k*
        ((rowLogHorizon s : ℝ)+2) ≤
      (720*16777216 : ℝ)*((k : ℝ)*s*Real.log (2*(t : ℝ))/Real.log (2*(s : ℝ))) := by
    convert hamort using 1 <;> simp only [acceptedRowCharge,activeRoundCharge,decoderScale] <;> ring
  have hratio : 0 ≤ (k : ℝ)*s*Real.log (2*(t : ℝ))/Real.log (2*(s : ℝ)) := by positivity
  calc
    _ ≤ 2*(s : ℝ)+(720*16777216 : ℝ)*
        ((k : ℝ)*s*Real.log (2*(t : ℝ))/Real.log (2*(s : ℝ))) := by
          simpa only [add_assoc] using add_le_add (le_refl (2*(s : ℝ))) hcharge
    _ ≤ bucketExpectedBound R C k := by
      dsimp only [bucketExpectedBound,bucketConstant,s,t] at *
      norm_num at *
      nlinarith

/-- Primitive B's actual finite program has the proved uniform expected query
bound. No sparse recovery oracle, cost premise, or infinite solver is supplied.
The same estimate holds when the row alphabet is bounded and C is unbounded. -/
theorem learnBucketRounds_expected_bound (M : BooleanMatrix R C) (r k T : ℕ)
    (hk : 10 ≤ k) (hkr : k ≤ r) (hs : 1 ≤ Fintype.card R) (ht : 1 ≤ Fintype.card C)
    (hdegree : ∀ u, r ≤ sampleCount (M u) univ ∧ sampleCount (M u) univ ≤ 2*r) :
    (learnBucketRounds r k T (BucketState.initial : BucketState R C)).expectedQueries
      (fun q => (bilinear M q : ℝ)) ≤ ENNReal.ofReal (bucketExpectedBound R C k) := by
  have hcharges := learnBucketRounds_expected_le_charges M r k T hk hkr hs ht hdegree
  have ha := acceptedRowCharge_nonneg (Fintype.card R) (Fintype.card C) k hs ht
  have hb := activeRoundCharge_nonneg (Fintype.card R) (Fintype.card C) k ht
  have hreal := ENNReal.ofReal_le_ofReal (bucket_charges_le_bound (R := R) (C := C) k hs ht)
  have hENN :
      2*(Fintype.card R : ℝ≥0∞)+
        ENNReal.ofReal (acceptedRowCharge (Fintype.card R) (Fintype.card C) k)*Fintype.card R+
        ENNReal.ofReal (activeRoundCharge (Fintype.card R) (Fintype.card C) k)*
          ((rowLogHorizon (Fintype.card R) : ℝ≥0∞)+2) ≤
      ENNReal.ofReal (bucketExpectedBound R C k) := by
    rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hb (by positivity)),
      ENNReal.ofReal_add (by positivity) (mul_nonneg ha (Nat.cast_nonneg _)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul hb,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)] at hreal
    simpa only [ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat] using hreal
  exact hcharges.trans hENN

end ExpectedCost

end
end CutQueryComplexity.StarContraction2022.Recovery

#print axioms CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_none
#print axioms CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_some
#print axioms CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_some_tendsto
#print axioms CutQueryComplexity.StarContraction2022.Recovery.rowSamples_marginal
#print axioms CutQueryComplexity.StarContraction2022.Recovery.rowSamples_unfinished_le
#print axioms CutQueryComplexity.StarContraction2022.Recovery.rowSamples_total_expected_counts
#print axioms CutQueryComplexity.StarContraction2022.Recovery.sampleColumns_count_law
#print axioms CutQueryComplexity.StarContraction2022.Recovery.columnProposal_expMoment
#print axioms CutQueryComplexity.StarContraction2022.Recovery.columnProposal_lower
#print axioms CutQueryComplexity.StarContraction2022.Recovery.columnProposal_upper
#print axioms CutQueryComplexity.StarContraction2022.Recovery.bucketAccept_failure_le_half
#print axioms CutQueryComplexity.StarContraction2022.Recovery.rowSamples_expected_rounds
#print axioms CutQueryComplexity.StarContraction2022.Recovery.validateRowCounts_sound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.maskedMatrix_bilinear
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_every_oracle
#print axioms CutQueryComplexity.StarContraction2022.Recovery.bucket_row_reject_le_half
#print axioms CutQueryComplexity.StarContraction2022.Recovery.decoderWeight_affine
#print axioms CutQueryComplexity.StarContraction2022.Recovery.decoderWeight_round_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.bucketRoundWith_honest_run
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_progress
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_completed_correct
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_proposal_law
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_completion_tail
#print axioms CutQueryComplexity.StarContraction2022.Recovery.sparseRawBudget_le_scaled_weight
#print axioms CutQueryComplexity.StarContraction2022.Recovery.honestRound_amortized

#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_amortized
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_expected_le_charges
#print axioms CutQueryComplexity.StarContraction2022.Recovery.bucket_charges_le_bound
#print axioms CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_expected_bound

#print axioms CutQueryComplexity.StarContraction2022.Recovery.sampleColumns_apply
#print axioms CutQueryComplexity.StarContraction2022.Recovery.sampleColumns_filter
#print axioms CutQueryComplexity.StarContraction2022.Recovery.columnProposal_restrict_apply
