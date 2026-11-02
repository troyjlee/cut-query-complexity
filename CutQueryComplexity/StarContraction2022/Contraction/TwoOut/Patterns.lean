import CutQueryComplexity.StarContraction2022.Contraction.TwoOut.Exposure
import CutQueryComplexity.Probability.FiniteEvents
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Caught-position bounds for the actual stopped exposure

The probability argument conditions on the revealed history. It never
conditions on eventual closure or on a future component size. Finite history
fibers are summed before the union bound over specified caught positions.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.TwoOut

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

section FiniteHistories

variable {Ω H : Type*} [Fintype Ω]

/-- Exact total probability over the finite image of an arbitrary history.
The history type itself need not be finite. -/
theorem mass_sum_history (p : PMF Ω) (history : Ω → H) (P : Ω → Prop) :
    (∑ h ∈ univ.image history, mass p (fun w => history w = h ∧ P w)) = mass p P := by
  simp_rw [mass_eq_tsum, tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  have hw : history w ∈ univ.image history := mem_image.mpr ⟨w, mem_univ w, rfl⟩
  by_cases hp : P w <;> simp [hp, hw]

/-- A zero-supported fiber has zero event mass; no conditional distribution
is manufactured for such a fiber. -/
theorem mass_fiber_eq_zero (p : PMF Ω) (history : Ω → H) (h : H)
    (hn : ¬ ∃ w, history w = h ∧ w ∈ p.support) :
    mass p (fun w => history w = h) = 0 := by
  apply le_antisymm _ (by positivity)
  calc
    _ ≤ mass p (fun _ => False) := mass_mono_on_support p (fun w hw he => hn ⟨w, he, hw⟩)
    _ = 0 := mass_false p

/-- Integrate a next-event bound over the complete current history, retaining
an arbitrary event already determined by that history. -/
theorem history_inter_le (p : PMF Ω) (history : Ω → H) (Past Next : Ω → Prop)
    (c : ℝ≥0∞)
    (hpast : ∀ a b, history a = history b → (Past a ↔ Past b))
    (hnext : ∀ w (hw : w ∈ p.support),
      mass (p.filter {a | history a = history w} ⟨w, rfl, hw⟩) Next ≤ c) :
    mass p (fun w => Past w ∧ Next w) ≤ mass p Past * c := by
  rw [← mass_sum_history p history (fun w => Past w ∧ Next w),
    ← mass_sum_history p history Past, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro h _
  by_cases hex : ∃ w, history w = h ∧ w ∈ p.support
  · obtain ⟨w, rfl, hw⟩ := hex
    by_cases hp : Past w
    · have hleft : (fun a => history a = history w ∧ (Past a ∧ Next a)) =
          (fun a => history a = history w ∧ Next a) := by
        funext a
        apply propext
        constructor
        · exact fun ha => ⟨ha.1, ha.2.2⟩
        · intro ha
          exact ⟨ha.1, (hpast a w ha.1).mpr hp, ha.2⟩
      have hright : (fun a => history a = history w ∧ Past a) =
          (fun a => history a = history w) := by
        funext a
        apply propext
        exact ⟨fun ha => ha.1, fun ha => ⟨ha, (hpast a w ha).mpr hp⟩⟩
      rw [hleft, hright, Probability.mass_inter_eq_mul_filter p
        (fun a => history a = history w) Next ⟨w, rfl, hw⟩]
      exact mul_le_mul le_rfl (hnext w hw) (by positivity) (by positivity)
    · have hz : mass p (fun a => history a = history w ∧ (Past a ∧ Next a)) = 0 := by
        have he : (fun a => history a = history w ∧ (Past a ∧ Next a)) =
            (fun _ => False) := by
          funext a
          apply propext
          exact ⟨fun ha => hp ((hpast a w ha.1).mp ha.2.1), False.elim⟩
        rw [he, mass_false]
      rw [hz]
      positivity
  · have hz := mass_fiber_eq_zero p history h hex
    have hle : mass p (fun a => history a = h ∧ (Past a ∧ Next a)) ≤
        mass p (fun a => history a = h) := mass_mono p (fun _ ha => ha.1)
    exact (hle.trans_eq hz).trans (by positivity)

/-- Specified caught positions multiply their past-conditioned bounds. The
events themselves need not be independent. -/
theorem history_pattern_le (p : PMF Ω) (history : ℕ → Ω → H)
    (Caught : ℕ → Ω → Prop) (c : ℝ≥0∞)
    (hpast : ∀ i j, i < j → ∀ a b,
      history j a = history j b → (Caught i a ↔ Caught i b))
    (hnext : ∀ j w (hw : w ∈ p.support),
      mass (p.filter {a | history j a = history j w} ⟨w, rfl, hw⟩) (Caught j) ≤ c)
    (positions : Finset ℕ) :
    mass p (fun w => ∀ j ∈ positions, Caught j w) ≤ c ^ positions.card := by
  induction positions using Finset.induction_on_max with
  | empty => simp
  | insert j positions hj ih =>
    have hjnot : j ∉ positions := fun h => (hj j h).false
    have he : (fun w => ∀ i ∈ insert j positions, Caught i w) =
        (fun w => (∀ i ∈ positions, Caught i w) ∧ Caught j w) := by
      funext w
      simp only [mem_insert, forall_eq_or_imp, and_comm]
    rw [he, card_insert_of_notMem hjnot, pow_succ]
    apply (history_inter_le p (history j) _ (Caught j) c ?_ (hnext j)).trans
    · exact mul_le_mul ih le_rfl (by positivity) (by positivity)
    · intro a b hab
      constructor <;> intro h i hi
      · exact (hpast i j (hj i hi) a b hab).mp (h i hi)
      · exact (hpast i j (hj i hi) a b hab).mpr (h i hi)

/-- Counting the possible k specified positions gives the exact binomial
factor, with no independence assertion about the caught indicators. -/
theorem history_caught_count_le (p : PMF Ω) (history : ℕ → Ω → H)
    (Caught : ℕ → Ω → Prop) (c : ℝ≥0∞)
    (hpast : ∀ i j, i < j → ∀ a b,
      history j a = history j b → (Caught i a ↔ Caught i b))
    (hnext : ∀ j w (hw : w ∈ p.support),
      mass (p.filter {a | history j a = history j w} ⟨w, rfl, hw⟩) (Caught j) ≤ c)
    (T k : ℕ) :
    mass p (fun w => k ≤ ((range T).filter (fun j => Caught j w)).card) ≤
      (T.choose k : ℝ≥0∞) * c ^ k := by
  calc
    _ ≤ mass p (fun w => ∃ positions ∈ (range T).powersetCard k,
        ∀ j ∈ positions, Caught j w) := by
      apply mass_mono
      intro w hw
      obtain ⟨positions, hsub, hcard⟩ := exists_subset_card_eq hw
      refine ⟨positions, mem_powersetCard.mpr ⟨hsub.trans (filter_subset _ _), hcard⟩, ?_⟩
      exact fun j hj => (mem_filter.mp (hsub hj)).2
    _ ≤ ∑ positions ∈ (range T).powersetCard k,
        mass p (fun w => ∀ j ∈ positions, Caught j w) := mass_exists_finset_le p _ _
    _ ≤ ∑ _positions ∈ (range T).powersetCard k, c ^ k := by
      apply Finset.sum_le_sum
      intro positions hp
      simpa only [(mem_powersetCard.mp hp).2] using
        history_pattern_le p history Caught c hpast hnext positions
    _ = _ := by simp only [sum_const, card_powersetCard, card_range, nsmul_eq_mul]

end FiniteHistories

variable {V : Type} [Fintype V] [LinearOrder V]

theorem run_add (old : Finset V) (limit : ℕ) (tape : Tape V) (i j : ℕ) (E : Exposure V) :
    run old limit tape (i + j) E = run old limit tape j (run old limit tape i E) := by
  induction i generalizing E with
  | zero => simp only [zero_add, run]
  | succ i ih =>
    rw [Nat.succ_add, run, run, ih]

theorem run_succ_last (old : Finset V) (limit : ℕ) (tape : Tape V) (i : ℕ) (E : Exposure V) :
    run old limit tape (i + 1) E = step old limit tape (run old limit tape i E) := by
  rw [run_add]
  rfl

theorem run_exposed_mono_time (old : Finset V) (limit : ℕ) (tape : Tape V)
    {i j : ℕ} (hij : i ≤ j) (E : Exposure V) :
    (run old limit tape i E).exposed ⊆ (run old limit tape j E).exposed := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [run_add]
  exact run_exposed_mono old limit tape k _

theorem step_reached_card_le (old : Finset V) (limit : ℕ) (tape : Tape V)
    (E : Exposure V) (hE : E.reached.card ≤ limit) :
    (step old limit tape E).reached.card ≤ limit := by
  by_cases hs : E.Stopped
  · simpa only [step_of_stopped old limit tape E hs] using hE
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      cases ht : tape (E.pending.min' hp) with
      | none => exact hE
      | some v =>
        simp only [ht]
        split_ifs with ho hr hl
        · exact hE
        · exact hE
        · exact hE
        · rw [card_insert_of_notMem hr]
          omega
    · simpa only [dite_eq_right hp] using hE

theorem run_reached_card_le (old : Finset V) (limit : ℕ) (tape : Tape V) (fuel : ℕ)
    (E : Exposure V) (hE : E.reached.card ≤ limit) :
    (run old limit tape fuel E).reached.card ≤ limit := by
  induction fuel generalizing E with
  | zero => exact hE
  | succ fuel ih => exact ih _ (step_reached_card_le old limit tape E hE)

theorem step_reached_disjoint (old : Finset V) (limit : ℕ) (tape : Tape V)
    (E : Exposure V) (hE : Disjoint E.reached old) :
    Disjoint (step old limit tape E).reached old := by
  by_cases hs : E.Stopped
  · simpa only [step_of_stopped old limit tape E hs] using hE
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      cases ht : tape (E.pending.min' hp) with
      | none => exact hE
      | some v =>
        simp only [ht]
        split_ifs with ho hr hl
        · exact hE
        · exact hE
        · exact hE
        · exact disjoint_insert_left.mpr ⟨ho, hE⟩
    · simpa only [dite_eq_right hp] using hE

theorem run_reached_disjoint (old : Finset V) (limit : ℕ) (tape : Tape V) (fuel : ℕ)
    (E : Exposure V) (hE : Disjoint E.reached old) :
    Disjoint (run old limit tape fuel E).reached old := by
  induction fuel generalizing E with
  | zero => exact hE
  | succ fuel ih => exact ih _ (step_reached_disjoint old limit tape E hE)

/-- A caught indicator refers to the actual increment of the concrete
algorithm, so stopped padding has indicator zero. -/
def CaughtAt (old : Finset V) (limit : ℕ) (root : V) (j : ℕ) (tape : Tape V) : Prop :=
  (run old limit tape (j + 1) (initial root limit)).caught =
    (run old limit tape j (initial root limit)).caught + 1

theorem step_caught_cases (old : Finset V) (limit : ℕ) (tape : Tape V) (E : Exposure V) :
    (step old limit tape E).caught = E.caught ∨
      (step old limit tape E).caught = E.caught + 1 := by
  by_cases hs : E.Stopped
  · exact Or.inl (congrArg Exposure.caught (step_of_stopped old limit tape E hs))
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      cases ht : tape (E.pending.min' hp) with
      | none => exact Or.inl rfl
      | some v =>
        simp only [ht]
        split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl
    · simp only [dite_eq_right hp, true_or]

theorem caughtAt_history_determined (old : Finset V) (limit : ℕ) (root : V)
    (i j : ℕ) (hij : i < j) (tape reference : Tape V)
    (hh : history old limit root j tape = history old limit root j reference) :
    CaughtAt old limit root i tape ↔ CaughtAt old limit root i reference := by
  have hcyl := (history_eq_iff old limit root j tape reference).mp hh
  have hrun (k : ℕ) (hk : k ≤ j) :
      run old limit tape k (initial root limit) =
        run old limit reference k (initial root limit) :=
    run_eq_of_agree old limit tape reference k (initial root limit)
      (fun a ha => hcyl a (run_exposed_mono_time old limit reference hk _ ha))
  unfold CaughtAt
  rw [hrun i hij.le, hrun (i + 1) (by omega)]

theorem run_caught_eq_count (old : Finset V) (limit : ℕ) (root : V)
    (T : ℕ) (tape : Tape V) :
    (run old limit tape T (initial root limit)).caught =
      ((range T).filter (fun j => CaughtAt old limit root j tape)).card := by
  induction T with
  | zero => simp [run, initial]
  | succ T ih =>
    have hnot : T ∉ (range T).filter (fun j => CaughtAt old limit root j tape) := by simp
    rw [range_add_one, filter_insert]
    by_cases hc : CaughtAt old limit root T tape
    · rw [if_pos hc, card_insert_of_notMem hnot]
      exact hc.trans (congrArg (fun n => n + 1) ih)
    · rw [if_neg hc]
      have hs := step_caught_cases old limit tape (run old limit tape T (initial root limit))
      rw [← run_succ_last] at hs
      exact (hs.resolve_right hc).trans ih

/-- The bounded search has stopped after at most 2*limit reveals. -/
theorem run_twice_limit_stopped (old : Finset V) (limit : ℕ) (hlimit : 0 < limit)
    (root : V) (tape : Tape V) :
    (run old limit tape (2 * limit) (initial root limit)).Stopped := by
  by_contra hn
  let E := run old limit tape (2 * limit) (initial root limit)
  have hi : E.Inventory := run_inventory old limit tape _ (initial_inventory root limit)
  have he := run_exposed_card_of_active old limit tape (2 * limit)
    (initial_inventory root limit) hn
  have hr : E.reached.card ≤ limit := run_reached_card_le old limit tape _ _ (by
    simp only [initial, card_singleton]
    omega)
  have hp : E.pending.card + E.exposed.card = 2 * E.reached.card := by
    rw [← card_union_of_disjoint hi.disjoint, hi.partition]
    simp only [card_product, card_univ, Fintype.card_fin]
    omega
  have hx : E.exposed.card = 2 * limit := by simpa only [E, initial, card_empty, zero_add] using he
  have hz : E.pending = ∅ := card_eq_zero.mp (by omega)
  exact hn (Or.inr (Or.inr (Or.inr hz)))

theorem step_caught_hits (old : Finset V) (limit : ℕ) (tape : Tape V)
    (E : Exposure V) (hs : ¬ E.Stopped) (hp : E.pending.Nonempty)
    (hc : (step old limit tape E).caught = E.caught + 1) :
    ∃ v, tape (E.pending.min' hp) = some v ∧ v ∈ E.reached := by
  rw [step, if_neg hs, dite_eq_left hp] at hc
  cases ht : tape (E.pending.min' hp) with
  | none => simp only [ht] at hc; omega
  | some v =>
    simp only [ht] at hc
    split_ifs at hc with ho hr hl
    · change E.caught = E.caught + 1 at hc
      omega
    · exact ⟨v, rfl, hr⟩
    · change E.caught = E.caught + 1 at hc
      omega
    · change E.caught = E.caught + 1 at hc
      omega

/-- Apply the proved one-coordinate law to the actual caught indicator.
Deficient rows may be in the old set and need no degree premise. -/
theorem caughtAt_conditional_le (N : V → Finset V) (old : Finset V)
    (limit ell : ℕ) (hlimit : 0 < limit) (hell : 0 < ell)
    (root : V) (hroot : root ∉ old)
    (hdegree : ∀ v, v ∉ old → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v)
    (j : ℕ) (reference : Tape V) (href : reference ∈ (sample N).support) :
    mass ((sample N).filter
      {tape | history old limit root j tape = history old limit root j reference}
      ⟨reference, rfl, href⟩) (CaughtAt old limit root j) ≤
      ((limit - 1 : ℕ) : ℝ≥0∞) / ell := by
  let E := run old limit reference j (initial root limit)
  let μ := (sample N).filter
    {tape | history old limit root j tape = history old limit root j reference}
    ⟨reference, rfl, href⟩
  have hstate (tape : Tape V) (ht : tape ∈ μ.support) :
      run old limit tape j (initial root limit) = E := by
    have hh := (PMF.mem_support_filter_iff (p := sample N)
      (s := {tape | history old limit root j tape = history old limit root j reference})
      ⟨reference, rfl, href⟩).mp ht
    exact congrArg Prod.fst hh.1
  change mass μ _ ≤ _
  by_cases hs : E.Stopped
  · calc
      _ ≤ mass μ (fun _ => False) := by
        apply mass_mono_on_support
        intro tape ht hc
        rw [CaughtAt, run_succ_last, hstate tape ht, step_of_stopped old limit tape E hs] at hc
        omega
      _ = 0 := mass_false μ
      _ ≤ _ := by positivity
  · have hp : E.pending.Nonempty := nonempty_iff_ne_empty.mpr
      (fun he => hs (Or.inr (Or.inr (Or.inr he))))
    let a := E.pending.min' hp
    have ha : a ∈ E.pending := E.pending.min'_mem hp
    have hi : E.Inventory := run_inventory old limit reference j (initial_inventory root limit)
    have hd : Disjoint E.reached old := run_reached_disjoint old limit reference j _ (by
      simp [initial, hroot])
    have hsource : a.1 ∉ old := fun hv => disjoint_left.mp hd (hi.pending_source ha) hv
    have hr : E.reached.card ≤ limit := run_reached_card_le old limit reference j _ (by
      simp only [initial, card_singleton]
      omega)
    calc
      _ ≤ mass μ (fun tape => ∃ v, tape a = some v ∧ v ∈ E.reached) := by
        apply mass_mono_on_support
        intro tape ht hc
        rw [CaughtAt, run_succ_last, hstate tape ht] at hc
        exact step_caught_hits old limit tape E hs hp hc
      _ ≤ _ := history_caught_le N old limit root j reference href ell limit hell a ha
        (hdegree a.1 hsource) (hloop a.1) hr

/-- The literal caught-count tail for the actual killed search. All next
event bounds have been discharged from the independent neighbor tape. -/
theorem run_caught_tail (N : V → Finset V) (old : Finset V)
    (limit ell : ℕ) (hlimit : 0 < limit) (hell : 0 < ell)
    (root : V) (hroot : root ∉ old)
    (hdegree : ∀ v, v ∉ old → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v)
    (T k : ℕ) :
    mass (sample N) (fun tape => k ≤ (run old limit tape T (initial root limit)).caught) ≤
      (T.choose k : ℝ≥0∞) * (((limit - 1 : ℕ) : ℝ≥0∞) / ell) ^ k := by
  have he : (fun tape => k ≤ (run old limit tape T (initial root limit)).caught) =
      (fun tape => k ≤ ((range T).filter (fun j => CaughtAt old limit root j tape)).card) := by
    funext tape
    rw [run_caught_eq_count]
  rw [he]
  exact history_caught_count_le (sample N) (history old limit root) (CaughtAt old limit root) _
    (caughtAt_history_determined old limit root)
    (caughtAt_conditional_le N old limit ell hlimit hell root hroot hdegree hloop) T k

theorem phase_eq_run_twice (old : Finset V) (limit : ℕ)
    (hlimit : 0 < limit) (hcard : limit ≤ Fintype.card V) (root : V) (tape : Tape V) :
    phase old limit tape root = run old limit tape (2 * limit) (initial root limit) := by
  have hle : 2 * limit ≤ 2 * Fintype.card V + 1 := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [phase, hk, run_add,
    run_of_stopped old limit tape _ (run_twice_limit_stopped old limit hlimit root tape)]

/-- For each size x, the probability of a closed killed phase is bounded
by the genuine binomial caught-position count. No future-size conditioning
appears in the proof or in a probability premise. -/
theorem phase_closed_size_le (N : V → Finset V) (old : Finset V)
    (x ell : ℕ) (hx : 0 < x) (hcard : x ≤ Fintype.card V) (hell : 0 < ell)
    (root : V) (hroot : root ∉ old)
    (hdegree : ∀ v, v ∉ old → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v) :
    mass (sample N) (fun tape => (phase old x tape root).Clean ∧
        (phase old x tape root).reached.card = x) ≤
      ((2 * x).choose (x + 1) : ℝ≥0∞) * (((x - 1 : ℕ) : ℝ≥0∞) / ell) ^ (x + 1) := by
  apply (mass_mono (sample N) (Q := fun tape =>
    x + 1 ≤ (run old x tape (2 * x) (initial root x)).caught) ?_).trans
  · exact run_caught_tail N old x ell hx hell root hroot hdegree hloop (2 * x) (x + 1)
  · intro tape ht
    have hc := (phase_closed_caught old x tape root ht.1).2
    rw [ht.2, phase_eq_run_twice old x hx hcard root tape] at hc
    exact hc.ge

/-- The real-valued coefficient in the exact caught-position union bound. -/
def closedCoefficient (ell x : ℕ) : ℝ :=
  ((2 * x).choose (x + 1) : ℝ) * (((x - 1 : ℕ) : ℝ) / ell) ^ (x + 1)

theorem closedCoefficient_nonneg (ell x : ℕ) : 0 ≤ closedCoefficient ell x := by
  unfold closedCoefficient
  positivity

@[simp] theorem closedCoefficient_zero (ell : ℕ) : closedCoefficient ell 0 = 0 := by
  norm_num [closedCoefficient]

@[simp] theorem closedCoefficient_one (ell : ℕ) : closedCoefficient ell 1 = 0 := by
  norm_num [closedCoefficient]

theorem closedCoefficient_two (ell : ℕ) : closedCoefficient ell 2 = 4 / (ell : ℝ) ^ 3 := by
  norm_num [closedCoefficient, div_pow, div_eq_mul_inv]

theorem choose_closed_succ_le (x : ℕ) (hx : 1 ≤ x) :
    ((2 * (x + 1)).choose (x + 2) : ℝ) ≤ 4 * ((2 * x).choose (x + 1) : ℝ) := by
  have h₁ := Nat.choose_mul_succ_eq (2 * x) (x + 1)
  have h₂ := Nat.add_one_mul_choose_eq (2 * x + 1) (x + 1)
  have hsub : 2 * x + 1 - (x + 1) = x := by omega
  rw [hsub] at h₁
  have hn : 2 * x + 1 + 1 = 2 * (x + 1) := by omega
  rw [hn, show x + 1 + 1 = x + 2 by omega] at h₂
  have h₁R : ((2 * x).choose (x + 1) : ℝ) * (2 * x + 1) =
      ((2 * x + 1).choose (x + 1) : ℝ) * x := by exact_mod_cast h₁
  have h₂R : (2 * (x + 1) : ℝ) * ((2 * x + 1).choose (x + 1) : ℝ) =
      ((2 * (x + 1)).choose (x + 2) : ℝ) * (x + 2) := by exact_mod_cast h₂
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hrec : ((2 * (x + 1)).choose (x + 2) : ℝ) * ((x : ℝ) * (x + 2)) =
      ((2 * x).choose (x + 1) : ℝ) * ((2 * x + 2) * (2 * x + 1)) := by
    calc
      _ = (((2 * (x + 1)).choose (x + 2) : ℝ) * (x + 2)) * x := by ring
      _ = ((2 * (x + 1) : ℝ) * ((2 * x + 1).choose (x + 1) : ℝ)) * x := by rw [h₂R]
      _ = (2 * (x + 1) : ℝ) * (((2 * x + 1).choose (x + 1) : ℝ) * x) := by ring
      _ = _ := by rw [← h₁R]; ring
  have hfactor : (2 * (x : ℝ) + 2) * (2 * x + 1) ≤ 4 * (x * (x + 2)) := by nlinarith
  apply (mul_le_mul_iff_left₀ (show 0 < (x : ℝ) * (x + 2) by positivity)).mp
  rw [hrec]
  convert mul_le_mul_of_nonneg_left hfactor
    (Nat.cast_nonneg ((2 * x).choose (x + 1))) using 1 <;> ring

theorem ratio_power_le (x : ℕ) (hx : 2 ≤ x) :
    ((x : ℝ) / (x - 1)) ^ (x + 1) ≤ 4 * Real.exp 1 := by
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hpred : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hbase : (x : ℝ) / (x - 1) = 1 + (((x - 1 : ℕ) : ℝ))⁻¹ := by
    rw [hpred]
    field_simp [ne_of_gt (by linarith : 0 < (x : ℝ) - 1)]
    <;> ring
  have hb0 : 0 ≤ (x : ℝ) / (x - 1) :=
    div_nonneg (Nat.cast_nonneg x) (by linarith)
  have hb2 : (x : ℝ) / (x - 1) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < (x : ℝ) - 1)).mpr
    linarith
  have hpow : ((x : ℝ) / (x - 1)) ^ (x - 1) ≤ Real.exp 1 := by
    rw [hbase]
    exact Real.one_add_inv_pow_le_exp
  have hsq : ((x : ℝ) / (x - 1)) ^ 2 ≤ 4 := by nlinarith
  rw [show x + 1 = (x - 1) + 2 by omega, pow_add]
  calc
    _ ≤ Real.exp 1 * 4 := mul_le_mul hpow hsq (by positivity) (Real.exp_nonneg 1)
    _ = _ := by ring

/-- The adjacent coefficient estimate is derived from the binomial
recurrence and the elementary exponential bound. -/
theorem closedCoefficient_succ_le (ell x : ℕ) (hell : 0 < ell) (hx : 2 ≤ x) :
    closedCoefficient ell (x + 1) ≤
      (16 * Real.exp 1 * x / ell) * closedCoefficient ell x := by
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hpred : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hbase : (x : ℝ) / ell =
      (((x - 1 : ℕ) : ℝ) / ell) * ((x : ℝ) / (x - 1)) := by
    rw [hpred]
    field_simp [hellR.ne', ne_of_gt (by linarith : 0 < (x : ℝ) - 1)]
    <;> ring
  have hpow : ((x : ℝ) / ell) ^ (x + 1) =
      ((((x - 1 : ℕ) : ℝ) / ell) ^ (x + 1)) * (((x : ℝ) / (x - 1)) ^ (x + 1)) := by
    conv_lhs => rw [hbase]
    rw [mul_pow]
  calc
    closedCoefficient ell (x + 1) =
        ((2 * (x + 1)).choose (x + 2) : ℝ) * ((x : ℝ) / ell) ^ (x + 2) := by
      simp only [closedCoefficient, Nat.add_sub_cancel, show x + 1 + 1 = x + 2 by omega]
    _ ≤ (4 * ((2 * x).choose (x + 1) : ℝ)) * ((x : ℝ) / ell) ^ (x + 2) :=
      mul_le_mul_of_nonneg_right (choose_closed_succ_le x (by omega)) (by positivity)
    _ = (4 * closedCoefficient ell x * ((x : ℝ) / ell)) *
        ((x : ℝ) / (x - 1)) ^ (x + 1) := by
      rw [show x + 2 = (x + 1) + 1 by omega, pow_succ, hpow]
      unfold closedCoefficient
      ring
    _ ≤ (4 * closedCoefficient ell x * ((x : ℝ) / ell)) * (4 * Real.exp 1) :=
      mul_le_mul_of_nonneg_left (ratio_power_le x hx)
        (mul_nonneg (mul_nonneg (by norm_num) (closedCoefficient_nonneg ell x)) (by positivity))
    _ = _ := by ring

theorem closedCoefficient_half (ell x : ℕ) (hell : 0 < ell) (hx : 2 ≤ x)
    (hsmall : (x : ℝ) ≤ ell / (8 * Real.exp 1 ^ 3)) :
    closedCoefficient ell (x + 1) ≤ closedCoefficient ell x / 2 := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hepos := Real.exp_pos 1
  have hs : (x : ℝ) * (8 * Real.exp 1 ^ 3) ≤ ell :=
    (le_div_iff₀ (by positivity)).mp hsmall
  have he3 : 4 * Real.exp 1 ≤ Real.exp 1 ^ 3 := by
    nlinarith [mul_nonneg hepos.le (show 0 ≤ Real.exp 1 ^ 2 - 4 by nlinarith)]
  have hfactor : 16 * Real.exp 1 * x / ell ≤ 1 / 2 := by
    apply (div_le_iff₀ hellR).mpr
    nlinarith [mul_le_mul_of_nonneg_right he3 (Nat.cast_nonneg x)]
  calc
    _ ≤ (16 * Real.exp 1 * x / ell) * closedCoefficient ell x :=
      closedCoefficient_succ_le ell x hell hx
    _ ≤ (1 / 2) * closedCoefficient ell x :=
      mul_le_mul_of_nonneg_right hfactor (closedCoefficient_nonneg ell x)
    _ = _ := by ring

/-- Finite telescoping, so the estimate needs no infinite-process or
limiting-exposure assumption. -/
theorem sum_halving_le (f : ℕ → ℝ) (L : ℕ) (hf : ∀ x, 0 ≤ f x)
    (hzero : f 0 = 0) (hone : f 1 = 0)
    (hhalf : ∀ x, 2 ≤ x → x < L → f (x + 1) ≤ f x / 2) :
    (∑ x ∈ range (L + 1), f x) ≤ 2 * f 2 := by
  have htel : ∀ k, k + 2 ≤ L →
      (∑ x ∈ range (k + 3), f x) + f (k + 2) ≤ 2 * f 2 := by
    intro k
    induction k with
    | zero => intro _; simp [sum_range_succ, hzero, hone, two_mul]
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hstep := hhalf (k + 2) (by omega) (by omega)
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, sum_range_succ]
      simpa only [show k + 1 + 2 = k + 3 by omega] using
        (show (∑ x ∈ range (k + 3), f x) + f (k + 3) + f (k + 3) ≤ 2 * f 2 by
          linarith)
  by_cases hL : 2 ≤ L
  · have ht := htel (L - 2) (by omega)
    rw [show L - 2 + 3 = L + 1 by omega, show L - 2 + 2 = L by omega] at ht
    linarith [hf L]
  · have hL' : L = 0 ∨ L = 1 := by omega
    rcases hL' with rfl | rfl <;> simp [sum_range_succ, hzero, hone, hf 2]

/-- The source's small closed-phase coefficient sum, with its literal 8.
This is a finite numerical lemma, separate from conditioning across phases. -/
theorem sum_closedCoefficient_le (ell L : ℕ) (hell : 0 < ell)
    (hL : (L : ℝ) ≤ ell / (8 * Real.exp 1 ^ 3)) :
    (∑ x ∈ range (L + 1), closedCoefficient ell x) ≤ 8 / (ell : ℝ) ^ 3 := by
  calc
    _ ≤ 2 * closedCoefficient ell 2 := sum_halving_le _ L
      (closedCoefficient_nonneg ell) (closedCoefficient_zero ell) (closedCoefficient_one ell)
      (fun x hx hxL => closedCoefficient_half ell x hell hx
        ((by exact_mod_cast hxL.le : (x : ℝ) ≤ L).trans hL))
    _ = _ := by rw [closedCoefficient_two]; ring

/-- Lowering the kill limit does not alter a step whose reached set remains
within that limit. -/
theorem step_limit_eq (old : Finset V) (low high : ℕ) (hlim : low ≤ high)
    (tape : Tape V) (E : Exposure V)
    (hsize : (step old high tape E).reached.card ≤ low) :
    step old low tape E = step old high tape E := by
  by_cases hs : E.Stopped
  · rw [step_of_stopped old low tape E hs, step_of_stopped old high tape E hs]
  · by_cases hp : E.pending.Nonempty
    · rw [step, if_neg hs, dite_eq_left hp]
      rw [step, if_neg hs, dite_eq_left hp] at hsize ⊢
      cases ht : tape (E.pending.min' hp) with
      | none => simp only [ht]
      | some v =>
        simp only [ht] at hsize ⊢
        by_cases ho : v ∈ old
        · simp only [ho, ite_true]
        · simp only [ho, ite_false] at hsize ⊢
          by_cases hr : v ∈ E.reached
          · simp only [hr, ite_true]
          · simp only [hr, ite_false] at hsize ⊢
            by_cases hh : high ≤ E.reached.card
            · have hl : low ≤ E.reached.card := hlim.trans hh
              simp only [hh, hl, ite_true]
            · simp only [hh, ite_false] at hsize ⊢
              rw [card_insert_of_notMem hr] at hsize
              have hl : ¬ low ≤ E.reached.card := by omega
              simp only [hl, ite_false]
    · simp only [step, hs, ite_false, dite_eq_right hp]

theorem run_limit_eq (old : Finset V) (low high : ℕ) (hlim : low ≤ high)
    (tape : Tape V) (fuel : ℕ) (E : Exposure V)
    (hsize : (run old high tape fuel E).reached.card ≤ low) :
    run old low tape fuel E = run old high tape fuel E := by
  induction fuel generalizing E with
  | zero => rfl
  | succ fuel ih =>
    have hstep : (step old high tape E).reached.card ≤ low :=
      (card_le_card (run_reached_mono old high tape fuel (step old high tape E))).trans hsize
    simp only [run, step_limit_eq old low high hlim tape E hstep]
    exact ih _ hsize

theorem phase_limit_eq (old : Finset V) (low high : ℕ)
    (hlow : 0 < low) (hlim : low ≤ high) (tape : Tape V) (root : V)
    (hsize : (phase old high tape root).reached.card ≤ low) :
    phase old low tape root = phase old high tape root := by
  have hhigh : 0 < high := hlow.trans_le hlim
  have hi : initial root low = initial root high := by
    simp only [initial, Nat.ne_of_gt hlow, Nat.ne_of_gt hhigh, decide_false]
  unfold phase
  rw [hi]
  exact run_limit_eq old low high hlim tape _ _ hsize

/-- The untruncated phase is the same as its size-killed search on every
outcome that closes at that size. -/
theorem phase_full_size_le (N : V → Finset V) (old : Finset V)
    (ell x : ℕ) (hell : 0 < ell) (hx : 0 < x)
    (root : V) (hroot : root ∉ old)
    (hdegree : ∀ v, v ∉ old → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v) :
    mass (sample N) (fun tape => (phase old (Fintype.card V) tape root).Clean ∧
        (phase old (Fintype.card V) tape root).reached.card = x) ≤
      ENNReal.ofReal (closedCoefficient ell x) := by
  by_cases hxcard : x ≤ Fintype.card V
  · calc
      _ ≤ mass (sample N) (fun tape => (phase old x tape root).Clean ∧
          (phase old x tape root).reached.card = x) := by
        apply mass_mono
        intro tape ht
        have he := phase_limit_eq old x (Fintype.card V) hx hxcard tape root ht.2.le
        simpa only [he] using ht
      _ ≤ ((2 * x).choose (x + 1) : ℝ≥0∞) *
          (((x - 1 : ℕ) : ℝ≥0∞) / ell) ^ (x + 1) :=
        phase_closed_size_le N old x ell hx hxcard hell root hroot hdegree hloop
      _ = _ := by
        rw [closedCoefficient, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_div_of_pos (by exact_mod_cast hell : (0 : ℝ) < ell),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  · calc
      _ ≤ mass (sample N) (fun _ => False) := by
        apply mass_mono
        intro tape ht
        exact hxcard (ht.2 ▸ card_le_univ (phase old (Fintype.card V) tape root).reached)
      _ = 0 := mass_false _
      _ ≤ _ := by positivity

/-- Actual small-phase failure bound, before any multi-phase composition.
This result sums over possible final sizes rather than conditioning on one. -/
theorem phase_small_closed_le (N : V → Finset V) (old : Finset V)
    (ell L : ℕ) (hell : 0 < ell)
    (hL : (L : ℝ) ≤ ell / (8 * Real.exp 1 ^ 3))
    (root : V) (hroot : root ∉ old)
    (hdegree : ∀ v, v ∉ old → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v) :
    mass (sample N) (fun tape => (phase old (Fintype.card V) tape root).Clean ∧
        (phase old (Fintype.card V) tape root).reached.card ≤ L) ≤
      ENNReal.ofReal (8 / (ell : ℝ) ^ 3) := by
  let Event := fun x tape => (phase old (Fintype.card V) tape root).Clean ∧
    (phase old (Fintype.card V) tape root).reached.card = x
  calc
    _ ≤ mass (sample N) (fun tape => ∃ x ∈ range (L + 1), Event x tape) := by
      apply mass_mono
      intro tape ht
      exact ⟨_, mem_range.mpr (by omega), ht.1, rfl⟩
    _ ≤ ∑ x ∈ range (L + 1), mass (sample N) (Event x) := mass_exists_finset_le _ _ _
    _ ≤ ∑ x ∈ range (L + 1), ENNReal.ofReal (closedCoefficient ell x) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : 0 < x
      · exact phase_full_size_le N old ell x hell hx root hroot hdegree hloop
      · have hx0 : x = 0 := by omega
        subst x
        have hz : mass (sample N) (Event 0) = 0 := by
          apply le_antisymm _ (by positivity)
          calc
            _ ≤ mass (sample N) (fun _ => False) := by
              apply mass_mono
              intro tape ht
              have hr := phase_root_mem old (Fintype.card V) tape root
              rw [card_eq_zero.mp ht.2] at hr
              exact notMem_empty root hr
            _ = 0 := mass_false _
        rw [hz]
        positivity
    _ = ENNReal.ofReal (∑ x ∈ range (L + 1), closedCoefficient ell x) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => closedCoefficient_nonneg ell x)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (sum_closedCoefficient_le ell L hell hL)

#print axioms mass_sum_history
#print axioms history_inter_le
#print axioms history_pattern_le
#print axioms history_caught_count_le
#print axioms caughtAt_history_determined
#print axioms run_caught_eq_count
#print axioms run_twice_limit_stopped
#print axioms caughtAt_conditional_le
#print axioms run_caught_tail
#print axioms phase_closed_size_le
#print axioms closedCoefficient_succ_le
#print axioms closedCoefficient_half
#print axioms sum_closedCoefficient_le
#print axioms phase_limit_eq
#print axioms phase_full_size_le
#print axioms phase_small_closed_le

end
end CutQueryComplexity.StarContraction2022.Contraction.TwoOut
