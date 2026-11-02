import CutQueryComplexity.StarContraction2022.Contraction.TwoOut.Patterns

/-!
# Actual multi-phase processing and component charging

The processed set begins with the omitted outgoing rows. Every later phase
uses the fixed public predrawn tape, starts at the least unprocessed vertex,
and stops on its first contact with the old processed set. Its choices and
component representatives are constructed, not supplied by a size oracle.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.TwoOut

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [LinearOrder V]

def Exposure.TouchesOld (E : Exposure V) (tape : Tape V) (old : Finset V) (root : V) : Prop :=
  E.contact = true → ∃ v ∈ old, (selectedGraph tape).Reachable root v

theorem initial_touchesOld (old : Finset V) (limit : ℕ) (root : V) (tape : Tape V) :
    (initial root limit).TouchesOld tape old root := by
  simp [Exposure.TouchesOld, initial]

theorem step_touchesOld (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V)
    {E : Exposure V} (hi : E.Inventory) (hr : E.Rooted tape root)
    (ht : E.TouchesOld tape old root) :
    (step old limit tape E).TouchesOld tape old root := by
  by_cases hs : E.Stopped
  · simpa only [step_of_stopped old limit tape E hs] using ht
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      cases hdraw : tape (E.pending.min' hp) with
      | none => exact ht
      | some v =>
        simp only [hdraw]
        split_ifs with ho hv hl
        · intro _
          refine ⟨v, ho, ?_⟩
          have hsource := hr _ (hi.pending_source (E.pending.min'_mem hp))
          by_cases he : (E.pending.min' hp).1 = v
          · simpa only [he] using hsource
          · exact hsource.trans (selectedGraph_adj_of_draw tape he hdraw).reachable
        · exact ht
        · exact ht
        · exact ht
    · simpa only [dite_eq_right hp] using ht

theorem run_touchesOld (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V)
    (fuel : ℕ) {E : Exposure V} (hi : E.Inventory) (hr : E.Rooted tape root)
    (ht : E.TouchesOld tape old root) :
    (run old limit tape fuel E).TouchesOld tape old root := by
  induction fuel generalizing E with
  | zero => exact ht
  | succ fuel ih =>
    exact ih (step_inventory old limit tape hi)
      (step_rooted old limit tape root hi hr) (step_touchesOld old limit tape root hi hr ht)

theorem phase_touchesOld (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V) :
    (phase old limit tape root).TouchesOld tape old root :=
  run_touchesOld old limit tape root _ (initial_inventory root limit)
    (initial_rooted root limit tape) (initial_touchesOld old limit root tape)

structure ProcessState (V : Type) where
  processed : Finset V
  representatives : Finset V
  closedSizes : List ℕ

def processInitial (deficient : Finset V) : ProcessState V where
  processed := deficient
  representatives := deficient
  closedSizes := []

def ProcessState.remaining (P : ProcessState V) : Finset V := univ \ P.processed

/-- A contacting phase adds no representative. An invalid tape may create
an extra representative; honest-tape proofs separately rule out invalidity. -/
def advance (tape : Tape V) (P : ProcessState V) : ProcessState V :=
  if h : P.remaining.Nonempty then
    let root := P.remaining.min' h
    let E := phase P.processed (Fintype.card V) tape root
    { processed := P.processed ∪ E.reached
      representatives := if E.contact then P.representatives else insert root P.representatives
      closedSizes := if E.contact then P.closedSizes else E.reached.card :: P.closedSizes }
  else P

def process (tape : Tape V) : ℕ → ProcessState V → ProcessState V
  | 0, P => P
  | fuel + 1, P => process tape fuel (advance tape P)

def finish (deficient : Finset V) (tape : Tape V) : ProcessState V :=
  process tape (Fintype.card V) (processInitial deficient)

def ProcessState.Covers (P : ProcessState V) (tape : Tape V) : Prop :=
  ∀ v ∈ P.processed, ∃ r ∈ P.representatives, (selectedGraph tape).Reachable r v

theorem processInitial_covers (deficient : Finset V) (tape : Tape V) :
    (processInitial deficient).Covers tape := by
  intro v hv
  exact ⟨v, hv, SimpleGraph.Reachable.rfl⟩

theorem advance_processed_mono (tape : Tape V) (P : ProcessState V) :
    P.processed ⊆ (advance tape P).processed := by
  rw [advance]
  split_ifs <;> first | exact subset_union_left | exact Subset.rfl

theorem advance_representatives_mono (tape : Tape V) (P : ProcessState V) :
    P.representatives ⊆ (advance tape P).representatives := by
  by_cases hp : P.remaining.Nonempty
  · rw [advance, dite_eq_left hp]
    change P.representatives ⊆
      if (phase P.processed (Fintype.card V) tape (P.remaining.min' hp)).contact then
        P.representatives else insert (P.remaining.min' hp) P.representatives
    split_ifs
    · exact Subset.rfl
    · exact subset_insert (P.remaining.min' hp) P.representatives
  · simpa only [advance, dite_eq_right hp] using
      (Subset.rfl : P.representatives ⊆ P.representatives)

theorem advance_covers (tape : Tape V) (P : ProcessState V) (hP : P.Covers tape) :
    (advance tape P).Covers tape := by
  by_cases h : P.remaining.Nonempty
  · rw [advance, dite_eq_left h]
    let root := P.remaining.min' h
    let E := phase P.processed (Fintype.card V) tape root
    intro v hv
    change v ∈ P.processed ∪ E.reached at hv
    rcases mem_union.mp hv with hvold | hvnew
    · obtain ⟨r, hr, hrv⟩ := hP v hvold
      refine ⟨r, ?_, hrv⟩
      change r ∈ if E.contact then P.representatives else insert root P.representatives
      cases hc : E.contact <;> simp [hc, hr]
    · have hrv := phase_rooted P.processed (Fintype.card V) tape root v hvnew
      cases hc : E.contact
      · refine ⟨root, ?_, hrv⟩
        change root ∈ if E.contact then P.representatives else insert root P.representatives
        simp only [hc, Bool.false_eq_true, ite_false, mem_insert_self]
      · obtain ⟨w, hwold, hrw⟩ := phase_touchesOld P.processed (Fintype.card V) tape root hc
        obtain ⟨r, hr, hrw'⟩ := hP w hwold
        refine ⟨r, ?_, hrw'.trans (hrw.symm.trans hrv)⟩
        change r ∈ if E.contact then P.representatives else insert root P.representatives
        simpa only [hc, ite_true] using hr
  · simpa only [advance, dite_eq_right h] using hP

theorem process_covers (tape : Tape V) (fuel : ℕ) (P : ProcessState V) (hP : P.Covers tape) :
    (process tape fuel P).Covers tape := by
  induction fuel generalizing P with
  | zero => exact hP
  | succ fuel ih => exact ih _ (advance_covers tape P hP)

theorem advance_of_complete (tape : Tape V) (P : ProcessState V) (h : P.remaining = ∅) :
    advance tape P = P := by
  simp only [advance, h, Finset.not_nonempty_empty, dite_false]

theorem process_of_complete (tape : Tape V) (P : ProcessState V)
    (h : P.remaining = ∅) (fuel : ℕ) : process tape fuel P = P := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [process, advance_of_complete tape P h] using ih

theorem advance_processed_strict (tape : Tape V) (P : ProcessState V)
    (h : P.remaining.Nonempty) : P.processed.card < (advance tape P).processed.card := by
  let root := P.remaining.min' h
  have hr : root ∉ P.processed := (mem_sdiff.mp (P.remaining.min'_mem h)).2
  have hroot := phase_root_mem P.processed (Fintype.card V) tape root
  have hsub : insert root P.processed ⊆
      P.processed ∪ (phase P.processed (Fintype.card V) tape root).reached := by
    intro v hv
    rcases mem_insert.mp hv with he | hvP
    · subst v
      exact mem_union_right _ hroot
    · exact mem_union_left _ hvP
  rw [advance, dite_eq_left h]
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hr] at hcard
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hcard

theorem process_processed_lower (tape : Tape V) (fuel : ℕ) (P : ProcessState V)
    (hactive : (process tape fuel P).remaining.Nonempty) :
    P.processed.card + fuel ≤ (process tape fuel P).processed.card := by
  induction fuel generalizing P with
  | zero => simp only [process, add_zero, le_refl]
  | succ fuel ih =>
    have hp : P.remaining.Nonempty := by
      by_contra hn
      have he := not_nonempty_iff_eq_empty.mp hn
      rw [process_of_complete tape P he] at hactive
      exact hn hactive
    have hnext := ih (advance tape P) hactive
    have hstrict := advance_processed_strict tape P hp
    change P.processed.card + (fuel + 1) ≤ (process tape fuel (advance tape P)).processed.card
    omega

/-- The fixed ambient number of phases suffices on every tape. -/
theorem finish_complete (deficient : Finset V) (tape : Tape V) :
    (finish deficient tape).remaining = ∅ := by
  by_contra hn
  have hp := nonempty_iff_ne_empty.mpr hn
  have hlow := process_processed_lower tape (Fintype.card V) (processInitial deficient) hp
  obtain ⟨v, hv⟩ := hp
  have hvout := (mem_sdiff.mp hv).2
  have hproper : (finish deficient tape).processed ⊂ univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, fun he => hvout (he.symm ▸ mem_univ v)⟩
  have hcard := card_lt_card hproper
  rw [card_univ] at hcard
  change deficient.card + Fintype.card V ≤ (finish deficient tape).processed.card at hlow
  omega

theorem finish_processed (deficient : Finset V) (tape : Tape V) :
    (finish deficient tape).processed = univ := by
  have h := finish_complete deficient tape
  apply Subset.antisymm (subset_univ _)
  exact sdiff_eq_empty_iff_subset.mp h

theorem componentCount_le_representatives (P : ProcessState V) (tape : Tape V)
    (hP : P.Covers tape) (hcomplete : P.processed = univ) :
    componentCount tape ≤ P.representatives.card := by
  have hsurj : Function.Surjective (fun r : {r // r ∈ P.representatives} =>
      (selectedGraph tape).connectedComponentMk r.val) := by
    intro C
    obtain ⟨v, rfl⟩ := Quot.exists_rep C
    obtain ⟨r, hr, hrv⟩ := hP v (hcomplete.symm ▸ mem_univ v)
    exact ⟨⟨r, hr⟩, SimpleGraph.ConnectedComponent.sound hrv⟩
  simpa only [componentCount, Fintype.card_coe] using Fintype.card_le_of_surjective _ hsurj

theorem advance_representatives_bound (tape : Tape V) (P : ProcessState V) (base : ℕ)
    (hP : P.representatives.card ≤ base + P.closedSizes.length) :
    (advance tape P).representatives.card ≤ base + (advance tape P).closedSizes.length := by
  rw [advance]
  split_ifs with h
  · cases hc : (phase P.processed (Fintype.card V) tape (P.remaining.min' h)).contact
    · simp only [hc, Bool.false_eq_true, ite_false, List.length_cons]
      have hi := card_insert_le (P.remaining.min' h) P.representatives
      omega
    · simpa only [hc, ite_true] using hP
  · exact hP

theorem process_representatives_bound (tape : Tape V) (fuel : ℕ) (P : ProcessState V) (base : ℕ)
    (hP : P.representatives.card ≤ base + P.closedSizes.length) :
    (process tape fuel P).representatives.card ≤ base + (process tape fuel P).closedSizes.length := by
  induction fuel generalizing P with
  | zero => exact hP
  | succ fuel ih => exact ih _ (advance_representatives_bound tape P base hP)

/-- An actual contacting phase creates no new component. Only the listed
noncontacting phases can increase the representative count. -/
theorem componentCount_le_closed (deficient : Finset V) (tape : Tape V) :
    componentCount tape ≤ deficient.card + (finish deficient tape).closedSizes.length := by
  apply (componentCount_le_representatives (finish deficient tape) tape
    (process_covers tape _ _ (processInitial_covers deficient tape))
    (finish_processed deficient tape)).trans
  exact process_representatives_bound tape _ _ deficient.card (by simp [processInitial])

/-- Reached vertices are new, so the recorded total closed volume cannot
exceed the ambient number of vertices. -/
theorem advance_volume_bound (tape : Tape V) (P : ProcessState V) (base : ℕ)
    (hP : base + P.closedSizes.sum ≤ P.processed.card) :
    base + (advance tape P).closedSizes.sum ≤ (advance tape P).processed.card := by
  by_cases h : P.remaining.Nonempty
  · let root := P.remaining.min' h
    let E := phase P.processed (Fintype.card V) tape root
    have hr : root ∉ P.processed := (mem_sdiff.mp (P.remaining.min'_mem h)).2
    have hd : Disjoint E.reached P.processed := run_reached_disjoint P.processed
      (Fintype.card V) tape _ _ (by simp [initial, hr])
    rw [advance, dite_eq_left h]
    change base + (if E.contact then P.closedSizes else E.reached.card :: P.closedSizes).sum ≤
      (P.processed ∪ E.reached).card
    rw [card_union_of_disjoint hd.symm]
    cases hc : E.contact <;> simp only [hc, Bool.false_eq_true, ite_false, ite_true, List.sum_cons]
    · omega
    · omega
  · simpa only [advance, dite_eq_right h] using hP

theorem process_volume_bound (tape : Tape V) (fuel : ℕ) (P : ProcessState V) (base : ℕ)
    (hP : base + P.closedSizes.sum ≤ P.processed.card) :
    base + (process tape fuel P).closedSizes.sum ≤ (process tape fuel P).processed.card := by
  induction fuel generalizing P with
  | zero => exact hP
  | succ fuel ih => exact ih _ (advance_volume_bound tape P base hP)

theorem finish_volume_le (deficient : Finset V) (tape : Tape V) :
    deficient.card + (finish deficient tape).closedSizes.sum ≤ Fintype.card V := by
  have h := process_volume_bound tape (Fintype.card V) (processInitial deficient)
    deficient.card (by simp [processInitial])
  change deficient.card + (finish deficient tape).closedSizes.sum ≤
    (finish deficient tape).processed.card at h
  simpa only [finish_processed, card_univ] using h

theorem process_processed_mono (tape : Tape V) (fuel : ℕ) (P : ProcessState V) :
    P.processed ⊆ (process tape fuel P).processed := by
  induction fuel generalizing P with
  | zero => exact Subset.rfl
  | succ fuel ih => exact (advance_processed_mono tape P).trans (ih (advance tape P))

theorem advance_eq_of_agree (tape reference : Tape V) (P : ProcessState V)
    (h : ∀ a, a.1 ∈ (advance reference P).processed → tape a = reference a) :
    advance tape P = advance reference P := by
  by_cases hp : P.remaining.Nonempty
  · let root := P.remaining.min' hp
    have he : phase P.processed (Fintype.card V) tape root =
        phase P.processed (Fintype.card V) reference root := by
      apply run_eq_of_agree
      intro a ha
      apply h a
      have hs := (phase_inventory P.processed (Fintype.card V) reference root).exposed_source ha
      simpa only [advance, dite_eq_left hp] using mem_union_right P.processed hs
    simp only [advance, dite_eq_left hp]
    rw [he]
  · simp only [advance, dite_eq_right hp]

/-- The complete processing state is determined by draw rows whose sources
have already been processed. No future phase event is included. -/
theorem process_eq_of_agree (tape reference : Tape V) (fuel : ℕ) (P : ProcessState V)
    (h : ∀ a, a.1 ∈ (process reference fuel P).processed → tape a = reference a) :
    process tape fuel P = process reference fuel P := by
  induction fuel generalizing P with
  | zero => rfl
  | succ fuel ih =>
    have hs : advance tape P = advance reference P := advance_eq_of_agree tape reference P
      (fun a ha => h a (process_processed_mono reference fuel (advance reference P) ha))
    simp only [process, hs]
    exact ih (advance reference P) h

/-- Refine the past by recording both draw slots of every processed source,
including its unused slot after an early contact. These are past source rows;
all unprocessed rows retain their product law. -/
def processHistory (fuel : ℕ) (P : ProcessState V) (tape : Tape V) :
    ProcessState V × ((V × Fin 2) → Option (Option V)) :=
  let out := process tape fuel P
  (out, fun a => if a.1 ∈ out.processed then some (tape a) else none)

theorem processHistory_eq_iff (fuel : ℕ) (P : ProcessState V) (tape reference : Tape V) :
    processHistory fuel P tape = processHistory fuel P reference ↔
      Cylinder ((process reference fuel P).processed ×ˢ univ) reference tape := by
  constructor
  · intro hh a ha
    have he := congrArg Prod.fst hh
    change process tape fuel P = process reference fuel P at he
    have ho := congrArg
      (fun H : ProcessState V × ((V × Fin 2) → Option (Option V)) => H.2 a) hh
    have ham := (mem_product.mp ha).1
    simpa only [processHistory, he, ham, ite_true, Option.some.injEq] using ho
  · intro hh
    have he : process tape fuel P = process reference fuel P := process_eq_of_agree
      tape reference fuel P (fun a ha => hh a (mem_product.mpr ⟨ha, mem_univ _⟩))
    apply Prod.ext
    · exact he
    · funext a
      change (if a.1 ∈ (process tape fuel P).processed then some (tape a) else none) =
        (if a.1 ∈ (process reference fuel P).processed then some (reference a) else none)
      rw [he]
      by_cases ha : a.1 ∈ (process reference fuel P).processed
      · simp only [ha, ite_true, hh a (mem_product.mpr ⟨ha, mem_univ _⟩)]
      · simp only [ha, ite_false]

section ProductFreezing

variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]

theorem mass_point (p : PMF A) (a : A) : mass p (fun b => b = a) = p a := by
  rw [mass_eq_tsum]
  simp

theorem product_map_coordinates (p : I → PMF A) (f : I → A → B) :
    (Probability.product p).map (fun tape i => f i (tape i)) =
      Probability.product (fun i => (p i).map (f i)) := by
  ext tape : 1
  rw [← mass_point, mass_map]
  have he : (fun x : I → A => (fun i => f i (x i)) = tape) =
      (fun x => ∀ i, f i (x i) = tape i) := by
    funext x
    exact propext ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [he, Probability.mass_product p (fun i a => f i a = tape i), Probability.product_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [← mass_map (p i) (f i) (fun b => b = tape i), mass_point]

def freezeCoordinates (J : Finset I) (reference tape : I → A) : I → A :=
  fun i => if i ∈ J then reference i else tape i

theorem freeze_product (p : I → PMF A) (J : Finset I) (reference : I → A) :
    (Probability.product p).map (freezeCoordinates J reference) =
      Probability.product (fun i => if i ∈ J then PMF.pure (reference i) else p i) := by
  change (Probability.product p).map (fun tape i => if i ∈ J then reference i else tape i) = _
  rw [product_map_coordinates p (fun i a => if i ∈ J then reference i else a)]
  congr 1
  funext i
  by_cases hi : i ∈ J
  · simp only [hi, ite_true]
    exact PMF.map_const (p i) (reference i)
  · simp only [hi, ite_false]
    exact PMF.map_id (p i)

/-- Conditioning on actual exposed coordinates equals overwriting just
those coordinates of a fresh product tape. All other coordinates stay fresh. -/
theorem condition_cylinder_freeze (p : I → PMF A) (J : Finset I) (reference : I → A)
    (href : reference ∈ (Probability.product p).support) :
    (Probability.product p).filter {tape | Cylinder J reference tape}
      (cylinder_supported p reference href J) =
      (Probability.product p).map (freezeCoordinates J reference) := by
  have hcoord : ∀ i, ∃ a, (i ∈ J → a = reference i) ∧ a ∈ (p i).support := by
    intro i
    exact ⟨reference i, fun _ => rfl, (Probability.mem_support_product p reference).mp href i⟩
  have hfilter : (Probability.product p).filter {tape | Cylinder J reference tape}
      (cylinder_supported p reference href J) =
      Probability.product (fun i => (p i).filter {a | i ∈ J → a = reference i} (hcoord i)) :=
    Probability.condition_product p (fun i a => i ∈ J → a = reference i) hcoord
  rw [hfilter, freeze_product]
  congr 1
  funext i
  by_cases hi : i ∈ J
  · rw [if_pos hi]
    ext a : 1
    rw [Probability.filter_apply_mass]
    simp only [hi, true_implies, mass_point, PMF.pure_apply]
    by_cases ha : a = reference i
    · subst a
      simp only [ite_true]
      exact ENNReal.div_self
        ((PMF.mem_support_iff (p i) (reference i)).mp
          ((Probability.mem_support_product p reference).mp href i))
        ((p i).apply_ne_top _)
    · simp only [ha, Ne.symm ha, ite_false, ENNReal.zero_div]
  · rw [if_neg hi]
    ext a : 1
    rw [Probability.filter_apply_mass]
    simp only [hi, false_implies, ite_true, mass_true, div_one]

end ProductFreezing

theorem phase_freeze_old (old : Finset V) (limit : ℕ) (root : V) (hroot : root ∉ old)
    (reference tape : Tape V) :
    phase old limit (freezeCoordinates (old ×ˢ univ) reference tape) root =
      phase old limit tape root := by
  apply run_eq_of_agree
  intro a ha
  have hs := (phase_inventory old limit tape root).exposed_source ha
  have hd : Disjoint (phase old limit tape root).reached old :=
    run_reached_disjoint old limit tape _ _ (by simp [initial, hroot])
  have hnot : a.1 ∉ old := fun ho => disjoint_left.mp hd hs ho
  simp only [freezeCoordinates, mem_product, hnot, false_and, ite_false]

/-- The next phase has its original unconditional phase law after fixing
the entire previous processing history. The old processed set and next root
are fixed parameters only after conditioning on that actual history. -/
theorem processHistory_phase_mass (N : V → Finset V) (fuel : ℕ) (P : ProcessState V)
    (reference : Tape V) (href : reference ∈ (sample N).support)
    (root : V) (hroot : root ∉ (process reference fuel P).processed)
    (Q : Exposure V → Prop) :
    mass ((sample N).filter
      {tape | processHistory fuel P tape = processHistory fuel P reference}
      ⟨reference, rfl, href⟩)
      (fun tape => Q (phase (process reference fuel P).processed (Fintype.card V) tape root)) =
    mass (sample N)
      (fun tape => Q (phase (process reference fuel P).processed (Fintype.card V) tape root)) := by
  let J := (process reference fuel P).processed ×ˢ (univ : Finset (Fin 2))
  have hcyl : ∃ tape, Cylinder J reference tape ∧ tape ∈ (sample N).support :=
    ⟨reference, fun _ _ => rfl, href⟩
  have hevent : (fun tape => processHistory fuel P tape = processHistory fuel P reference) =
      (fun tape => Cylinder J reference tape) := by
    funext tape
    exact propext (processHistory_eq_iff fuel P tape reference)
  have hf : (sample N).filter
      {tape | processHistory fuel P tape = processHistory fuel P reference}
      ⟨reference, rfl, href⟩ = (sample N).filter {tape | Cylinder J reference tape} hcyl := by
    ext tape : 1
    rw [Probability.filter_apply_mass, Probability.filter_apply_mass]
    simp only [hevent, processHistory_eq_iff]
    rfl
  have hfreeze : (sample N).filter {tape | Cylinder J reference tape} hcyl =
      (sample N).map (freezeCoordinates J reference) :=
    condition_cylinder_freeze (fun a : V × Fin 2 => Probability.neighborDraw (N a.1))
      J reference href
  rw [hf, hfreeze, mass_map]
  congr 1
  funext tape
  rw [phase_freeze_old _ _ root hroot reference tape]

theorem step_full_overflow_false (old : Finset V) (tape : Tape V) (E : Exposure V)
    (ho : E.overflow = false) : (step old (Fintype.card V) tape E).overflow = false := by
  by_cases hs : E.Stopped
  · simpa only [step_of_stopped old _ tape E hs] using ho
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      cases ht : tape (E.pending.min' hp) with
      | none => exact ho
      | some v =>
        simp only [ht]
        split_ifs with hvold hvr hlim
        · exact ho
        · exact ho
        · have hb := card_le_univ (insert v E.reached)
          rw [card_insert_of_notMem hvr] at hb
          omega
        · exact ho
    · simpa only [dite_eq_right hp] using ho

theorem run_full_overflow_false (old : Finset V) (tape : Tape V) (fuel : ℕ)
    (E : Exposure V) (ho : E.overflow = false) :
    (run old (Fintype.card V) tape fuel E).overflow = false := by
  induction fuel generalizing E with
  | zero => exact ho
  | succ fuel ih => exact ih _ (step_full_overflow_false old tape E ho)

theorem step_invalid_false (N : V → Finset V) (old : Finset V) (limit : ℕ) (tape : Tape V)
    (htape : tape ∈ (sample N).support) (hN : ∀ v, v ∉ old → (N v).Nonempty)
    (E : Exposure V) (hi : E.Inventory) (hd : Disjoint E.reached old)
    (hv : E.invalid = false) : (step old limit tape E).invalid = false := by
  by_cases hs : E.Stopped
  · simpa only [step_of_stopped old limit tape E hs] using hv
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      have hsource : (E.pending.min' hp).1 ∉ old := fun h =>
        disjoint_left.mp hd (hi.pending_source (E.pending.min'_mem hp)) h
      have hdraw := (Probability.neighborTape_support N 2 tape).mp htape (E.pending.min' hp)
      cases ht : tape (E.pending.min' hp) with
      | none =>
        simp only [ht] at hdraw
        exact ((hN _ hsource).ne_empty hdraw).elim
      | some v =>
        simp only [ht]
        split_ifs <;> exact hv
    · simpa only [dite_eq_right hp] using hv

theorem run_invalid_false (N : V → Finset V) (old : Finset V) (limit : ℕ) (tape : Tape V)
    (htape : tape ∈ (sample N).support) (hN : ∀ v, v ∉ old → (N v).Nonempty)
    (fuel : ℕ) (E : Exposure V) (hi : E.Inventory) (hd : Disjoint E.reached old)
    (hv : E.invalid = false) : (run old limit tape fuel E).invalid = false := by
  induction fuel generalizing E with
  | zero => exact hv
  | succ fuel ih =>
    exact ih _ (step_inventory old limit tape hi)
      (step_reached_disjoint old limit tape E hd) (step_invalid_false N old limit tape htape hN E hi hd hv)

/-- With omitted rows already processed, honest noncontacting phases are
exactly the clean closed phases counted by the probability argument. -/
theorem phase_clean_iff_contact_false (N : V → Finset V) (old : Finset V)
    (tape : Tape V) (htape : tape ∈ (sample N).support)
    (hN : ∀ v, v ∉ old → (N v).Nonempty) (root : V) (hroot : root ∉ old) :
    (phase old (Fintype.card V) tape root).Clean ↔
      (phase old (Fintype.card V) tape root).contact = false := by
  have hn : Fintype.card V ≠ 0 := by
    letI : Nonempty V := ⟨root⟩
    exact Fintype.card_ne_zero
  have ho : (phase old (Fintype.card V) tape root).overflow = false :=
    run_full_overflow_false old tape _ _ (by simp [initial, hn])
  have hv : (phase old (Fintype.card V) tape root).invalid = false :=
    run_invalid_false N old _ tape htape hN _ _ (initial_inventory root _)
      (by simp [initial, hroot]) rfl
  simp only [Exposure.Clean, ho, hv, and_true]

def smallCount (L : ℕ) (P : ProcessState V) : ℕ :=
  (P.closedSizes.filter (fun x => decide (x ≤ L))).length

def SmallNext (L : ℕ) (tape : Tape V) (P : ProcessState V) : Prop :=
  if h : P.remaining.Nonempty then
    let E := phase P.processed (Fintype.card V) tape (P.remaining.min' h)
    E.contact = false ∧ E.reached.card ≤ L
  else False

def SmallAt (deficient : Finset V) (L fuel : ℕ) (tape : Tape V) : Prop :=
  SmallNext L tape (process tape fuel (processInitial deficient))

theorem advance_smallCount (L : ℕ) (tape : Tape V) (P : ProcessState V) :
    smallCount L (advance tape P) = smallCount L P + if SmallNext L tape P then 1 else 0 := by
  by_cases hp : P.remaining.Nonempty
  · rw [advance, dite_eq_left hp]
    cases hc : (phase P.processed (Fintype.card V) tape (P.remaining.min' hp)).contact
    · by_cases hsize : (phase P.processed (Fintype.card V) tape (P.remaining.min' hp)).reached.card ≤ L
      · simp [smallCount, SmallNext, hp, hc, hsize]
      · simp [smallCount, SmallNext, hp, hc, hsize]
    · simp [smallCount, SmallNext, hp, hc]
  · simp [advance, SmallNext, hp]

theorem process_add (tape : Tape V) (i j : ℕ) (P : ProcessState V) :
    process tape (i + j) P = process tape j (process tape i P) := by
  induction i generalizing P with
  | zero => simp only [zero_add, process]
  | succ i ih => rw [Nat.succ_add, process, process, ih]

theorem process_succ_last (tape : Tape V) (i : ℕ) (P : ProcessState V) :
    process tape (i + 1) P = advance tape (process tape i P) := by
  rw [process_add]
  rfl

theorem process_smallCount (L fuel : ℕ) (tape : Tape V) (P : ProcessState V) :
    smallCount L (process tape fuel P) = smallCount L P +
      ∑ i ∈ range fuel, if SmallNext L tape (process tape i P) then 1 else 0 := by
  induction fuel with
  | zero => simp [process]
  | succ fuel ih => rw [process_succ_last, advance_smallCount, ih, sum_range_succ]; omega

theorem finish_smallCount (deficient : Finset V) (L : ℕ) (tape : Tape V) :
    smallCount L (finish deficient tape) =
      ∑ i ∈ range (Fintype.card V), if SmallAt deficient L i tape then 1 else 0 := by
  change smallCount L (process tape (Fintype.card V) (processInitial deficient)) = _
  rw [process_smallCount]
  have hz : smallCount L (processInitial deficient) = 0 := rfl
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : SmallAt deficient L i tape
  · have h' : SmallNext L tape (process tape i (processInitial deficient)) := h
    simp only [h, h', ite_true]
  · have h' : ¬ SmallNext L tape (process tape i (processInitial deficient)) := h
    simp only [h, h', ite_false]

/-- Uniform conditional bound after every actual processed history. This
is the missing conditioning step in a marginal-probability multiplication. -/
theorem smallAt_conditional_le (N : V → Finset V) (deficient : Finset V)
    (ell L : ℕ) (hell : 0 < ell) (hL : (L : ℝ) ≤ ell / (8 * Real.exp 1 ^ 3))
    (hdegree : ∀ v, v ∉ deficient → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v)
    (fuel : ℕ) (reference : Tape V) (href : reference ∈ (sample N).support) :
    mass ((sample N).filter
      {tape | processHistory fuel (processInitial deficient) tape =
        processHistory fuel (processInitial deficient) reference}
      ⟨reference, rfl, href⟩) (SmallAt deficient L fuel) ≤
      ENNReal.ofReal (8 / (ell : ℝ) ^ 3) := by
  let P := process reference fuel (processInitial deficient)
  let μ := (sample N).filter
    {tape | processHistory fuel (processInitial deficient) tape =
      processHistory fuel (processInitial deficient) reference} ⟨reference, rfl, href⟩
  have hstate (tape : Tape V) (ht : tape ∈ μ.support) :
      process tape fuel (processInitial deficient) = P := by
    exact congrArg Prod.fst ((PMF.mem_support_filter_iff (p := sample N)
      (s := {tape | processHistory fuel (processInitial deficient) tape =
        processHistory fuel (processInitial deficient) reference})
      ⟨reference, rfl, href⟩).mp ht).1
  have hsub : deficient ⊆ P.processed := process_processed_mono reference fuel (processInitial deficient)
  have hdeg : ∀ v, v ∉ P.processed → ell ≤ (N v).card :=
    fun v hv => hdegree v (fun hd => hv (hsub hd))
  change mass μ _ ≤ _
  by_cases hp : P.remaining.Nonempty
  · let root := P.remaining.min' hp
    have hr : root ∉ P.processed := (mem_sdiff.mp (P.remaining.min'_mem hp)).2
    let Q := fun E : Exposure V => E.Clean ∧ E.reached.card ≤ L
    calc
      _ ≤ mass μ (fun tape => Q (phase P.processed (Fintype.card V) tape root)) := by
        apply mass_mono_on_support
        intro tape ht hsmall
        have htp := ((PMF.mem_support_filter_iff (p := sample N)
          (s := {tape | processHistory fuel (processInitial deficient) tape =
            processHistory fuel (processInitial deficient) reference})
          ⟨reference, rfl, href⟩).mp ht).2
        rw [SmallAt, hstate tape ht, SmallNext, dite_eq_left hp] at hsmall
        exact ⟨(phase_clean_iff_contact_false N P.processed tape htp
          (fun v hv => card_pos.mp (hell.trans_le (hdeg v hv))) root hr).mpr hsmall.1, hsmall.2⟩
      _ = mass (sample N) (fun tape => Q (phase P.processed (Fintype.card V) tape root)) :=
        processHistory_phase_mass N fuel (processInitial deficient) reference href root hr Q
      _ ≤ _ := phase_small_closed_le N P.processed ell L hell hL root hr hdeg hloop
  · calc
      _ ≤ mass μ (fun _ => False) := by
        apply mass_mono_on_support
        intro tape ht hsmall
        simpa only [SmallAt, hstate tape ht, SmallNext, dite_eq_right hp] using hsmall
      _ = 0 := mass_false _
      _ ≤ _ := by positivity

/-- Each stage is bounded after the whole earlier history. Linearity below
therefore remains valid even though different phases are dependent. -/
theorem smallAt_mass_le (N : V → Finset V) (deficient : Finset V)
    (ell L : ℕ) (hell : 0 < ell) (hL : (L : ℝ) ≤ ell / (8 * Real.exp 1 ^ 3))
    (hdegree : ∀ v, v ∉ deficient → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v)
    (fuel : ℕ) :
    mass (sample N) (SmallAt deficient L fuel) ≤ ENNReal.ofReal (8 / (ell : ℝ) ^ 3) := by
  simpa only [true_and, mass_true, one_mul] using history_inter_le (sample N)
    (processHistory fuel (processInitial deficient)) (fun _ => True) (SmallAt deficient L fuel)
    (ENNReal.ofReal (8 / (ell : ℝ) ^ 3)) (fun _ _ _ => Iff.rfl)
    (smallAt_conditional_le N deficient ell L hell hL hdegree hloop fuel)

theorem expect_smallCount_le (N : V → Finset V) (deficient : Finset V)
    (ell L : ℕ) (hell : 0 < ell) (hL : (L : ℝ) ≤ ell / (8 * Real.exp 1 ^ 3))
    (hdegree : ∀ v, v ∉ deficient → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v) :
    expect (sample N) (fun tape => (smallCount L (finish deficient tape) : ℝ≥0∞)) ≤
      (Fintype.card V : ℝ≥0∞) * ENNReal.ofReal (8 / (ell : ℝ) ^ 3) := by
  have he (tape : Tape V) : (smallCount L (finish deficient tape) : ℝ≥0∞) =
      ∑ i ∈ range (Fintype.card V), if SmallAt deficient L i tape then (1 : ℝ≥0∞) else 0 := by
    rw [finish_smallCount, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  calc
    _ = expect (sample N) (fun tape => ∑ i ∈ range (Fintype.card V),
        if SmallAt deficient L i tape then (1 : ℝ≥0∞) else 0) :=
      expect_congr_on_support _ (fun tape _ => he tape)
    _ = ∑ i ∈ range (Fintype.card V), mass (sample N) (SmallAt deficient L i) := by
      calc
        _ = ∑ i ∈ range (Fintype.card V), expect (sample N)
            (fun tape => if SmallAt deficient L i tape then (1 : ℝ≥0∞) else 0) := expect_sum _ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          simpa only [one_mul] using CutQueryComplexity.Probability.expect_indicator
            (sample N) (SmallAt deficient L i) 1
    _ ≤ ∑ _i ∈ range (Fintype.card V), ENNReal.ofReal (8 / (ell : ℝ) ^ 3) :=
      Finset.sum_le_sum (fun i _ => smallAt_mass_le N deficient ell L hell hL hdegree hloop i)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]

def largeCount (L : ℕ) (P : ProcessState V) : ℕ :=
  (P.closedSizes.filter (fun x => decide (L < x))).length

theorem closedSizes_length_split (L : ℕ) (xs : List ℕ) :
    xs.length = (xs.filter (fun x => decide (x ≤ L))).length +
      (xs.filter (fun x => decide (L < x))).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x ≤ L
    · simp only [List.length_cons, List.filter_cons, hx, decide_true,
        not_lt_of_ge hx, decide_false, Bool.false_eq_true, ite_true, ite_false, List.length_cons]
      omega
    · have hLx : L < x := by omega
      simp only [List.length_cons, List.filter_cons, hx, decide_false,
        hLx, decide_true, Bool.false_eq_true, ite_true, ite_false, List.length_cons]
      omega

theorem largeCount_volume (L : ℕ) (xs : List ℕ) :
    (L + 1) * (xs.filter (fun x => decide (L < x))).length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : L < x
    · simp only [List.filter_cons, hx, decide_true, ite_true, List.length_cons,
        List.sum_cons, Nat.mul_add, Nat.mul_one]
      omega
    · simp only [List.filter_cons, hx, decide_false, Bool.false_eq_true, ite_false, List.sum_cons]
      omega

theorem componentCount_le_small_add (deficient : Finset V) (L : ℕ) (tape : Tape V) :
    (componentCount tape : ℝ) ≤ deficient.card + smallCount L (finish deficient tape) +
      (Fintype.card V : ℝ) / (L + 1) := by
  let P := finish deficient tape
  have hlen : P.closedSizes.length = smallCount L P + largeCount L P :=
    closedSizes_length_split L P.closedSizes
  have hc := componentCount_le_closed deficient tape
  change componentCount tape ≤ deficient.card + P.closedSizes.length at hc
  rw [hlen] at hc
  have hv := finish_volume_le deficient tape
  change deficient.card + P.closedSizes.sum ≤ Fintype.card V at hv
  have hl : (L + 1) * largeCount L P ≤ Fintype.card V :=
    (largeCount_volume L P.closedSizes).trans (by change P.closedSizes.sum ≤ _; omega)
  have hlR : (largeCount L P : ℝ) ≤ (Fintype.card V : ℝ) / (L + 1) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < L + 1)).mpr
    exact_mod_cast (show largeCount L P * (L + 1) ≤ Fintype.card V by simpa [Nat.mul_comm] using hl)
  have hcR : (componentCount tape : ℝ) ≤ deficient.card +
      ((smallCount L P : ℝ) + (largeCount L P : ℝ)) := by exact_mod_cast hc
  change (componentCount tape : ℝ) ≤ deficient.card + smallCount L P + _
  linarith

def smallLimit (ell : ℕ) : ℕ := ⌊(ell : ℝ) / (8 * Real.exp 1 ^ 3)⌋₊

theorem smallLimit_le (ell : ℕ) :
    (smallLimit ell : ℝ) ≤ ell / (8 * Real.exp 1 ^ 3) :=
  Nat.floor_le (by positivity)

theorem large_phase_bound (ell : ℕ) (hell : 0 < ell) :
    (Fintype.card V : ℝ) / (smallLimit ell + 1) ≤
      8 * Real.exp 1 ^ 3 * Fintype.card V / ell := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hfloor : (ell : ℝ) / (8 * Real.exp 1 ^ 3) < smallLimit ell + 1 :=
    Nat.lt_floor_add_one _
  have hmul : (ell : ℝ) ≤ (smallLimit ell + 1) * (8 * Real.exp 1 ^ 3) :=
    ((div_lt_iff₀ (by positivity)).mp hfloor).le
  apply (le_div_iff₀ hellR).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < smallLimit ell + 1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg (Fintype.card V))]

theorem smallCount_tail (N : V → Finset V) (deficient : Finset V)
    (ell : ℕ) (hell : 0 < ell) (hn : 0 < Fintype.card V)
    (hdegree : ∀ v, v ∉ deficient → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v) :
    mass (sample N) (fun tape => (Fintype.card V : ℝ) / ell <
      smallCount (smallLimit ell) (finish deficient tape)) ≤
      ENNReal.ofReal (8 / (ell : ℝ) ^ 2) := by
  let L := smallLimit ell
  let a : ℝ≥0∞ := ENNReal.ofReal ((Fintype.card V : ℝ) / ell)
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have ha0 : a ≠ 0 := by dsimp [a]; positivity
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hmark := mul_mass_le_expect (sample N)
    (fun tape => (Fintype.card V : ℝ) / ell < smallCount L (finish deficient tape))
    (fun tape => (smallCount L (finish deficient tape) : ℝ≥0∞)) a (by
      intro tape _ ht
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal ht.le)
  calc
    _ ≤ expect (sample N) (fun tape => (smallCount L (finish deficient tape) : ℝ≥0∞)) / a := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hat)).mpr
      simpa only [mul_comm] using hmark
    _ ≤ ((Fintype.card V : ℝ≥0∞) * ENNReal.ofReal (8 / (ell : ℝ) ^ 3)) / a :=
      ENNReal.div_le_div
        (expect_smallCount_le N deficient ell L hell (smallLimit_le ell) hdegree hloop) le_rfl
    _ = _ := by
      rw [show (Fintype.card V : ℝ≥0∞) = ENNReal.ofReal (Fintype.card V : ℝ) by simp,
        ← ENNReal.ofReal_mul hnR.le]
      change ENNReal.ofReal ((Fintype.card V : ℝ) * (8 / (ell : ℝ) ^ 3)) /
        ENNReal.ofReal ((Fintype.card V : ℝ) / ell) = _
      rw [← ENNReal.ofReal_div_of_pos (div_pos hnR hellR)]
      congr 1
      field_simp [hellR.ne', hnR.ne']
      <;> ring

/-- The corrected two-out component tail. The tape, phases, stopping,
conditional histories, component representatives and numerical bound are
all constructed above. No component-size or good-event oracle is a premise. -/
theorem componentCount_tail (N : V → Finset V) (deficient : Finset V)
    (ell : ℕ) (hell : 0 < ell)
    (hdegree : ∀ v, v ∉ deficient → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v) :
    mass (sample N) (fun tape => (deficient.card : ℝ) +
      (8 * Real.exp 1 ^ 3 + 1) * Fintype.card V / ell < componentCount tape) ≤
      ENNReal.ofReal (8 / (ell : ℝ) ^ 2) := by
  by_cases hn : 0 < Fintype.card V
  · apply (mass_mono (sample N) (Q := fun tape => (Fintype.card V : ℝ) / ell <
      smallCount (smallLimit ell) (finish deficient tape)) ?_).trans
    · exact smallCount_tail N deficient ell hell hn hdegree hloop
    · intro tape ht
      have hc := componentCount_le_small_add deficient (smallLimit ell) tape
      have hl := large_phase_bound (V := V) ell hell
      have he : (8 * Real.exp 1 ^ 3 + 1) * (Fintype.card V : ℝ) / ell =
          8 * Real.exp 1 ^ 3 * Fintype.card V / ell + (Fintype.card V : ℝ) / ell := by ring
      rw [he] at ht
      linarith
  · have hn0 : Fintype.card V = 0 := by omega
    calc
      _ ≤ mass (sample N) (fun _ => False) := by
        apply mass_mono
        intro tape ht
        have hc : componentCount tape = 0 := by have := componentCount_le tape; omega
        have hd : deficient.card = 0 := by have := card_le_univ deficient; omega
        simpa only [hn0, hc, hd, Nat.cast_zero, mul_zero, zero_div, add_zero, lt_self_iff_false] using ht
      _ = 0 := mass_false _
      _ ≤ _ := by positivity

theorem componentCount_tail_of_forty (N : V → Finset V) (deficient : Finset V)
    (ell : ℕ) (hell : 40 ≤ ell)
    (hdegree : ∀ v, v ∉ deficient → ell ≤ (N v).card) (hloop : ∀ v, v ∉ N v) :
    mass (sample N) (fun tape => (deficient.card : ℝ) +
      (8 * Real.exp 1 ^ 3 + 1) * Fintype.card V / ell < componentCount tape) ≤
      (200 : ℝ≥0∞)⁻¹ := by
  apply (componentCount_tail N deficient ell (by omega) hdegree hloop).trans
  have hellR : (40 : ℝ) ≤ ell := by exact_mod_cast hell
  have hr : 8 / (ell : ℝ) ^ 2 ≤ 1 / 200 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (ell : ℝ) ^ 2)).mpr
    nlinarith [sq_nonneg ((ell : ℝ) - 40)]
  have hcast : ENNReal.ofReal ((1 : ℝ) / 200) = (200 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 200)]
    norm_num [one_div]
  exact (ENNReal.ofReal_le_ofReal hr).trans_eq hcast

#print axioms phase_touchesOld
#print axioms advance
#print axioms finish_complete
#print axioms componentCount_le_closed
#print axioms finish_volume_le
#print axioms processHistory_eq_iff
#print axioms condition_cylinder_freeze
#print axioms processHistory_phase_mass
#print axioms phase_clean_iff_contact_false
#print axioms finish_smallCount
#print axioms smallAt_conditional_le
#print axioms expect_smallCount_le
#print axioms componentCount_le_small_add
#print axioms smallCount_tail
#print axioms componentCount_tail
#print axioms componentCount_tail_of_forty

end
end CutQueryComplexity.StarContraction2022.Contraction.TwoOut
