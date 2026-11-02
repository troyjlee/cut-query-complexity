import CutQueryComplexity.StarContraction2022.Probability.Product
import CutQueryComplexity.StarContraction2022.Common.Quotient
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex

/-!
# Actual finite stopped exposure of a predrawn two-out tape

The tape is sampled from explicit learned neighbor lists. A phase stops as
soon as it touches the old processed set. Its killed version also stops before
adding a vertex beyond its public size limit. Empty outgoing rows are marked
invalid if exposed; they remain possible target vertices throughout.

The probability and component-tail arguments are separate from these concrete
public data and operations. No exploration, goodness, or size oracle is stored.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.TwoOut

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [LinearOrder V]

/-- The public exposure order is lexicographic on source and draw index.
The usual product order is only partial, so the order is supplied explicitly. -/
instance coordinateLinearOrder : LinearOrder (V × Fin 2) :=
  inferInstanceAs (LinearOrder (V ×ₗ Fin 2))

abbrev Tape (V : Type) := V × Fin 2 → Option V

def sample (N : V → Finset V) : PMF (Tape V) := Probability.neighborTape N 2

def slots (v : V) : Finset (V × Fin 2) := {v} ×ˢ univ

@[simp] theorem mem_slots (v : V) (a : V × Fin 2) : a ∈ slots v ↔ a.1 = v := by
  simp only [slots, mem_product, mem_singleton, mem_univ, and_true]

@[simp] theorem slots_card (v : V) : (slots v).card = 2 := by simp [slots]

/-- All entries are finite public data; the cut and the hidden graph are absent. -/
structure Exposure (V : Type) where
  reached : Finset V
  pending : Finset (V × Fin 2)
  exposed : Finset (V × Fin 2)
  caught : ℕ
  discoveries : ℕ
  contact : Bool
  overflow : Bool
  invalid : Bool

def Exposure.Stopped (E : Exposure V) : Prop :=
  E.contact = true ∨ E.overflow = true ∨ E.invalid = true ∨ E.pending = ∅

def initial (root : V) (limit : ℕ) : Exposure V where
  reached := {root}
  pending := slots root
  exposed := ∅
  caught := 0
  discoveries := 0
  contact := false
  overflow := decide (limit = 0)
  invalid := false

/-- Deterministic smallest-coordinate exposure. Both draws of a fresh vertex
are queued. The old processed set is tested before any further exploration. -/
def step (old : Finset V) (limit : ℕ) (tape : Tape V) (E : Exposure V) : Exposure V :=
  if E.Stopped then E else
  if h : E.pending.Nonempty then
    let a := E.pending.min' h
    let base := { E with pending := E.pending.erase a, exposed := insert a E.exposed }
    match tape a with
    | none => { base with invalid := true }
    | some v =>
      if v ∈ old then { base with contact := true }
      else if v ∈ E.reached then { base with caught := E.caught + 1 }
      else if limit ≤ E.reached.card then { base with overflow := true }
      else
        { base with
          reached := insert v E.reached
          pending := base.pending ∪ slots v
          discoveries := E.discoveries + 1 }
  else E

/-- Public fixed fuel. A stopped state is absorbing, so padding performs no
further reveal and never charges an empty test as a new random draw. -/
def run (old : Finset V) (limit : ℕ) (tape : Tape V) : ℕ → Exposure V → Exposure V
  | 0, E => E
  | fuel + 1, E => run old limit tape fuel (step old limit tape E)

def phase (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V) : Exposure V :=
  run old limit tape (2 * Fintype.card V + 1) (initial root limit)

/-- Pending and exposed coordinates partition exactly the two slots of all
reached vertices. In particular, no coordinate may be exposed twice. -/
structure Exposure.Inventory (E : Exposure V) : Prop where
  partition : E.pending ∪ E.exposed = E.reached ×ˢ univ
  disjoint : Disjoint E.pending E.exposed

theorem initial_inventory (root : V) (limit : ℕ) : (initial root limit).Inventory := by
  constructor <;> simp [initial, slots]

theorem Exposure.Inventory.pending_source {E : Exposure V} (h : E.Inventory)
    {a : V × Fin 2} (ha : a ∈ E.pending) : a.1 ∈ E.reached := by
  have hp : a ∈ E.pending ∪ E.exposed := mem_union_left _ ha
  rw [h.partition] at hp
  exact (mem_product.mp hp).1

theorem Exposure.Inventory.exposed_source {E : Exposure V} (h : E.Inventory)
    {a : V × Fin 2} (ha : a ∈ E.exposed) : a.1 ∈ E.reached := by
  have hp : a ∈ E.pending ∪ E.exposed := mem_union_right _ ha
  rw [h.partition] at hp
  exact (mem_product.mp hp).1

theorem Exposure.Inventory.transfer {E : Exposure V} (h : E.Inventory)
    {a : V × Fin 2} (ha : a ∈ E.pending) :
    ({ E with pending := E.pending.erase a, exposed := insert a E.exposed } : Exposure V).Inventory := by
  constructor
  · change E.pending.erase a ∪ insert a E.exposed = E.reached ×ˢ univ
    rw [← h.partition]
    ext b
    by_cases hb : b = a
    · subst b
      simp [ha]
    · simp [hb]
  · apply disjoint_left.mpr
    intro b hb hx
    rcases mem_insert.mp hx with hba | hbX
    · exact (mem_erase.mp hb).1 hba
    · exact disjoint_left.mp h.disjoint (mem_of_mem_erase hb) hbX

theorem Exposure.Inventory.add_vertex {E : Exposure V} (h : E.Inventory)
    {v : V} (hv : v ∉ E.reached) :
    ({ E with
        reached := insert v E.reached
        pending := E.pending ∪ slots v } : Exposure V).Inventory := by
  constructor
  · change (E.pending ∪ slots v) ∪ E.exposed = insert v E.reached ×ˢ univ
    rw [union_right_comm, h.partition]
    ext a
    simp only [mem_union, mem_product, mem_univ, and_true, mem_slots, mem_insert]
    tauto
  · apply disjoint_left.mpr
    intro a ha hx
    rcases mem_union.mp ha with hp | hs
    · exact disjoint_left.mp h.disjoint hp hx
    · have haV := (mem_slots v a).mp hs
      exact hv (haV ▸ h.exposed_source hx)

theorem step_inventory (old : Finset V) (limit : ℕ) (tape : Tape V)
    {E : Exposure V} (hE : E.Inventory) : (step old limit tape E).Inventory := by
  by_cases hs : E.Stopped
  · simpa only [step, hs, ite_true] using hE
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      have hb := hE.transfer (E.pending.min'_mem hp)
      cases ht : tape (E.pending.min' hp) with
      | none =>
        simp only [ht]
        exact ⟨hb.partition, hb.disjoint⟩
      | some v =>
        simp only [ht]
        split_ifs with ho hr hl
        · exact ⟨hb.partition, hb.disjoint⟩
        · exact ⟨hb.partition, hb.disjoint⟩
        · exact ⟨hb.partition, hb.disjoint⟩
        · have hi := hb.add_vertex hr
          exact ⟨hi.partition, hi.disjoint⟩
    · simpa only [dite_eq_right hp] using hE

theorem run_inventory (old : Finset V) (limit : ℕ) (tape : Tape V)
    (fuel : ℕ) {E : Exposure V} (hE : E.Inventory) : (run old limit tape fuel E).Inventory := by
  induction fuel generalizing E with
  | zero => exact hE
  | succ fuel ih => exact ih (step_inventory old limit tape hE)

theorem phase_inventory (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V) :
    (phase old limit tape root).Inventory :=
  run_inventory old limit tape _ (initial_inventory root limit)

theorem step_exposed_card (old : Finset V) (limit : ℕ) (tape : Tape V)
    {E : Exposure V} (hE : E.Inventory) (hs : ¬ E.Stopped) :
    (step old limit tape E).exposed.card = E.exposed.card + 1 := by
  have hp : E.pending.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    exact hs (Or.inr (Or.inr (Or.inr he)))
  have ha : E.pending.min' hp ∉ E.exposed :=
    fun hx => disjoint_left.mp hE.disjoint (E.pending.min'_mem hp) hx
  rw [step, if_neg hs, dite_eq_left hp]
  cases ht : tape (E.pending.min' hp) with
  | none =>
    simp only [ht]
    exact card_insert_of_notMem ha
  | some v =>
    simp only [ht]
    split_ifs <;> exact card_insert_of_notMem ha

@[simp] theorem step_of_stopped (old : Finset V) (limit : ℕ) (tape : Tape V)
    (E : Exposure V) (hE : E.Stopped) : step old limit tape E = E := by
  simp only [step, hE, ite_true]

theorem run_of_stopped (old : Finset V) (limit : ℕ) (tape : Tape V)
    (E : Exposure V) (hE : E.Stopped) (fuel : ℕ) : run old limit tape fuel E = E := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, step_of_stopped old limit tape E hE] using ih

theorem run_exposed_card_of_active (old : Finset V) (limit : ℕ) (tape : Tape V)
    (fuel : ℕ) {E : Exposure V} (hE : E.Inventory)
    (hactive : ¬ (run old limit tape fuel E).Stopped) :
    (run old limit tape fuel E).exposed.card = E.exposed.card + fuel := by
  induction fuel generalizing E with
  | zero => simp [run]
  | succ fuel ih =>
    have hs : ¬ E.Stopped := by
      intro hstop
      rw [run_of_stopped old limit tape E hstop] at hactive
      exact hactive hstop
    have hi := ih (step_inventory old limit tape hE) hactive
    change (run old limit tape fuel (step old limit tape E)).exposed.card = _
    rw [hi, step_exposed_card old limit tape hE hs]
    omega

/-- Public fuel is sufficient on every tape, including invalid tapes. The
extra final iteration is absorbing and reveals no extra coordinate. -/
theorem phase_stopped (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V) :
    (phase old limit tape root).Stopped := by
  by_contra hs
  have hc := run_exposed_card_of_active old limit tape (2 * Fintype.card V + 1)
    (initial_inventory root limit) hs
  have hb := card_le_univ (phase old limit tape root).exposed
  simp only [Fintype.card_prod, Fintype.card_fin] at hb
  change (phase old limit tape root).exposed.card = 0 + (2 * Fintype.card V + 1) at hc
  omega

def Exposure.Clean (E : Exposure V) : Prop :=
  E.contact = false ∧ E.overflow = false ∧ E.invalid = false

def Exposure.Balanced (E : Exposure V) : Prop :=
  E.exposed.card + 1 = E.reached.card + E.caught

theorem initial_balanced (root : V) (limit : ℕ) : (initial root limit).Balanced := by
  simp [Exposure.Balanced, initial]

theorem Exposure.stopped_of_not_clean (E : Exposure V) (h : ¬ E.Clean) : E.Stopped := by
  cases hc : E.contact <;> cases ho : E.overflow <;> cases hi : E.invalid <;>
    simp_all [Exposure.Clean, Exposure.Stopped]

theorem run_clean_start (old : Finset V) (limit : ℕ) (tape : Tape V)
    (fuel : ℕ) (E : Exposure V) (h : (run old limit tape fuel E).Clean) : E.Clean := by
  by_contra hn
  rw [run_of_stopped old limit tape E (E.stopped_of_not_clean hn)] at h
  exact hn h

theorem step_balanced (old : Finset V) (limit : ℕ) (tape : Tape V)
    {E : Exposure V} (hE : E.Inventory) (hb : E.Balanced)
    (hc : (step old limit tape E).Clean) : (step old limit tape E).Balanced := by
  by_cases hs : E.Stopped
  · simpa only [step_of_stopped old limit tape E hs] using hb
  · have hp : E.pending.Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      exact fun he => hs (Or.inr (Or.inr (Or.inr he)))
    have ha : E.pending.min' hp ∉ E.exposed :=
      fun hx => disjoint_left.mp hE.disjoint (E.pending.min'_mem hp) hx
    rw [step, if_neg hs, dite_eq_left hp] at hc ⊢
    cases ht : tape (E.pending.min' hp) with
    | none => simp [ht, Exposure.Clean] at hc
    | some v =>
      simp only [ht] at hc ⊢
      split_ifs with ho hr hl
      · simp [ho, Exposure.Clean] at hc
      · change (insert (E.pending.min' hp) E.exposed).card + 1 =
          E.reached.card + (E.caught + 1)
        rw [card_insert_of_notMem ha]
        unfold Exposure.Balanced at hb
        omega
      · simp [ho, hr, hl, Exposure.Clean] at hc
      · change (insert (E.pending.min' hp) E.exposed).card + 1 =
          (insert v E.reached).card + E.caught
        rw [card_insert_of_notMem ha, card_insert_of_notMem hr]
        unfold Exposure.Balanced at hb
        omega

theorem run_balanced (old : Finset V) (limit : ℕ) (tape : Tape V) (fuel : ℕ)
    {E : Exposure V} (hE : E.Inventory) (hb : E.Balanced)
    (hc : (run old limit tape fuel E).Clean) : (run old limit tape fuel E).Balanced := by
  induction fuel generalizing E with
  | zero => exact hb
  | succ fuel ih =>
    have hstep : (step old limit tape E).Clean := run_clean_start old limit tape fuel _ hc
    exact ih (step_inventory old limit tape hE) (step_balanced old limit tape hE hb hstep) hc

/-- A closed phase of size x requires exactly x+1 caught draws among its 2x
exposed coordinates. This is proved for the actual bounded exploration. -/
theorem phase_closed_caught (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V)
    (hc : (phase old limit tape root).Clean) :
    (phase old limit tape root).exposed.card = 2 * (phase old limit tape root).reached.card ∧
      (phase old limit tape root).caught = (phase old limit tape root).reached.card + 1 := by
  have hs := phase_stopped old limit tape root
  have hp : (phase old limit tape root).pending = ∅ := by
    rcases hs with h | h | h | h
    · simp [hc.1] at h
    · simp [hc.2.1] at h
    · simp [hc.2.2] at h
    · exact h
  have hi := (phase_inventory old limit tape root).partition
  rw [hp, empty_union] at hi
  have hcard := congrArg Finset.card hi
  simp only [card_product, card_univ, Fintype.card_fin] at hcard
  have hb := run_balanced old limit tape _ (initial_inventory root limit)
    (initial_balanced root limit) hc
  change (phase old limit tape root).exposed.card + 1 =
    (phase old limit tape root).reached.card + (phase old limit tape root).caught at hb
  omega

theorem step_reached_mono (old : Finset V) (limit : ℕ) (tape : Tape V)
    (E : Exposure V) : E.reached ⊆ (step old limit tape E).reached := by
  by_cases hs : E.Stopped
  · rw [step_of_stopped old limit tape E hs]
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      cases ht : tape (E.pending.min' hp) with
      | none => exact Subset.rfl
      | some v =>
        simp only [ht]
        split_ifs <;> first | exact Subset.rfl | exact subset_insert _ _
    · simp only [dite_eq_right hp]
      exact Subset.rfl

theorem step_exposed_mono (old : Finset V) (limit : ℕ) (tape : Tape V)
    (E : Exposure V) : E.exposed ⊆ (step old limit tape E).exposed := by
  by_cases hs : E.Stopped
  · rw [step_of_stopped old limit tape E hs]
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      cases ht : tape (E.pending.min' hp) with
      | none => exact subset_insert _ _
      | some v =>
        simp only [ht]
        split_ifs <;> exact subset_insert _ _
    · simp only [dite_eq_right hp]
      exact Subset.rfl

theorem run_reached_mono (old : Finset V) (limit : ℕ) (tape : Tape V)
    (fuel : ℕ) (E : Exposure V) : E.reached ⊆ (run old limit tape fuel E).reached := by
  induction fuel generalizing E with
  | zero => exact Subset.rfl
  | succ fuel ih =>
    exact (step_reached_mono old limit tape E).trans (ih (step old limit tape E))

theorem run_exposed_mono (old : Finset V) (limit : ℕ) (tape : Tape V)
    (fuel : ℕ) (E : Exposure V) : E.exposed ⊆ (run old limit tape fuel E).exposed := by
  induction fuel generalizing E with
  | zero => exact Subset.rfl
  | succ fuel ih =>
    exact (step_exposed_mono old limit tape E).trans (ih (step old limit tape E))

/-- Two tapes which agree on the coordinates actually inspected in one step
produce the same next state. Agreement on future coordinates is unnecessary. -/
theorem step_eq_of_agree (old : Finset V) (limit : ℕ) (tape reference : Tape V)
    (E : Exposure V)
    (h : ∀ a ∈ (step old limit reference E).exposed, tape a = reference a) :
    step old limit tape E = step old limit reference E := by
  by_cases hs : E.Stopped
  · rw [step_of_stopped old limit tape E hs, step_of_stopped old limit reference E hs]
  · by_cases hp : E.pending.Nonempty
    · have ha : E.pending.min' hp ∈ (step old limit reference E).exposed := by
        rw [step, if_neg hs, dite_eq_left hp]
        cases ht : reference (E.pending.min' hp) with
        | none =>
          simp only [ht]
          exact mem_insert_self (E.pending.min' hp) E.exposed
        | some v =>
          simp only [ht]
          split_ifs <;> exact mem_insert_self (E.pending.min' hp) E.exposed
      simp only [step, hs, ite_false, dite_eq_left hp, h _ ha]
    · simp only [step, hs, ite_false, dite_eq_right hp]

/-- The complete state is determined by the finite answers in its own
exposure history. This is the actual adaptive algorithm's cylinder property. -/
theorem run_eq_of_agree (old : Finset V) (limit : ℕ) (tape reference : Tape V)
    (fuel : ℕ) (E : Exposure V)
    (h : ∀ a ∈ (run old limit reference fuel E).exposed, tape a = reference a) :
    run old limit tape fuel E = run old limit reference fuel E := by
  induction fuel generalizing E with
  | zero => rfl
  | succ fuel ih =>
    have hstep : step old limit tape E = step old limit reference E :=
      step_eq_of_agree old limit tape reference E (fun a ha =>
        h a (run_exposed_mono old limit reference fuel (step old limit reference E) ha))
    simp only [run, hstep]
    exact ih (step old limit reference E) h

section CoordinateLaws

variable {I A : Type*} [Fintype I] [Fintype A]

/-- A rectangular event fixes precisely the revealed coordinates. -/
def Cylinder (E : Finset I) (reference tape : I → A) : Prop :=
  ∀ i ∈ E, tape i = reference i

theorem cylinder_supported (p : I → PMF A) (reference : I → A)
    (href : reference ∈ (Probability.product p).support) (E : Finset I) :
    ∃ tape, Cylinder E reference tape ∧ tape ∈ (Probability.product p).support :=
  ⟨reference, fun _ _ => rfl, href⟩

theorem product_coordinate_mass (p : I → PMF A) (a : I) (P : A → Prop) :
    mass (Probability.product p) (fun tape => P (tape a)) = mass (p a) P := by
  have he : (fun tape : I → A => P (tape a)) =
      (fun tape => ∀ i, i = a → P (tape i)) := by
    funext tape
    apply propext
    constructor
    · intro h i hi
      simpa only [hi] using h
    · intro h
      exact h a rfl
  rw [he, Probability.mass_product p (fun i v => i = a → P v)]
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · exact fun h => (h (mem_univ a)).elim

/-- Conditioning on any supported cylinder leaves each unrevealed coordinate
with its original law. The conditioning law is constructed by PMF.filter. -/
theorem condition_cylinder_coordinate (p : I → PMF A) (reference : I → A)
    (href : reference ∈ (Probability.product p).support) (E : Finset I)
    (a : I) (ha : a ∉ E) (P : A → Prop) :
    mass ((Probability.product p).filter {tape | Cylinder E reference tape}
      (cylinder_supported p reference href E)) (fun tape => P (tape a)) =
      mass (p a) P := by
  have hcoord : ∀ i, ∃ v, (i ∈ E → v = reference i) ∧ v ∈ (p i).support := by
    intro i
    exact ⟨reference i, fun _ => rfl, (Probability.mem_support_product p reference).mp href i⟩
  have hfilter : (Probability.product p).filter {tape | Cylinder E reference tape}
      (cylinder_supported p reference href E) =
      Probability.product (fun i => (p i).filter {v | i ∈ E → v = reference i} (hcoord i)) :=
    Probability.condition_product p (fun i v => i ∈ E → v = reference i) hcoord
  rw [hfilter, product_coordinate_mass]
  have hfree : (p a).filter {v | a ∈ E → v = reference a} (hcoord a) = p a := by
    ext v : 1
    rw [Probability.filter_apply_mass]
    simp [ha]
  rw [hfree]

end CoordinateLaws

/-- The past records both the actual state and each revealed answer. It has
no component-size, eventual-closure, or good-cut information. -/
def history (old : Finset V) (limit : ℕ) (root : V) (fuel : ℕ) (tape : Tape V) :
    Exposure V × ((V × Fin 2) → Option (Option V)) :=
  let E := run old limit tape fuel (initial root limit)
  (E, fun a => if a ∈ E.exposed then some (tape a) else none)

theorem history_eq_iff (old : Finset V) (limit : ℕ) (root : V) (fuel : ℕ)
    (tape reference : Tape V) :
    history old limit root fuel tape = history old limit root fuel reference ↔
      Cylinder (run old limit reference fuel (initial root limit)).exposed reference tape := by
  constructor
  · intro hh a ha
    have he := congrArg Prod.fst hh
    change run old limit tape fuel (initial root limit) =
      run old limit reference fuel (initial root limit) at he
    have ho := congrArg (fun H : Exposure V × ((V × Fin 2) → Option (Option V)) => H.2 a) hh
    simpa only [history, he, ha, ite_true, Option.some.injEq] using ho
  · intro hh
    have he := run_eq_of_agree old limit tape reference fuel (initial root limit) hh
    apply Prod.ext
    · exact he
    · funext a
      change (if a ∈ (run old limit tape fuel (initial root limit)).exposed then some (tape a) else none) =
        (if a ∈ (run old limit reference fuel (initial root limit)).exposed then some (reference a) else none)
      rw [he]
      by_cases ha : a ∈ (run old limit reference fuel (initial root limit)).exposed
      · simp only [ha, ite_true, hh a ha]
      · simp only [ha, ite_false]

/-- Conditional uniformity is valid for the actual adaptive past, before
specifying any future closure or component event. -/
theorem history_unexposed_mass (N : V → Finset V) (old : Finset V) (limit : ℕ)
    (root : V) (fuel : ℕ) (reference : Tape V) (href : reference ∈ (sample N).support)
    (a : V × Fin 2) (ha : a ∉ (run old limit reference fuel (initial root limit)).exposed)
    (P : Option V → Prop) :
    mass ((sample N).filter
      {tape | history old limit root fuel tape = history old limit root fuel reference}
      ⟨reference, rfl, href⟩) (fun tape => P (tape a)) =
      mass (Probability.neighborDraw (N a.1)) P := by
  let E := (run old limit reference fuel (initial root limit)).exposed
  have hevent : (fun tape => history old limit root fuel tape =
      history old limit root fuel reference) = (fun tape => Cylinder E reference tape) := by
    funext tape
    exact propext (history_eq_iff old limit root fuel tape reference)
  have hcyl : ∃ tape, Cylinder E reference tape ∧ tape ∈ (sample N).support :=
    ⟨reference, fun _ _ => rfl, href⟩
  have hfilter : (sample N).filter
      {tape | history old limit root fuel tape = history old limit root fuel reference}
      ⟨reference, rfl, href⟩ =
      (sample N).filter {tape | Cylinder E reference tape} hcyl := by
    ext tape : 1
    rw [Probability.filter_apply_mass, Probability.filter_apply_mass]
    simp only [hevent, history_eq_iff]
    rfl
  rw [hfilter]
  exact condition_cylinder_coordinate
    (fun a : V × Fin 2 => Probability.neighborDraw (N a.1)) reference href E a ha P

theorem mass_neighborDraw_hits (N R : Finset V) (hN : N.Nonempty) :
    mass (Probability.neighborDraw N) (fun o => ∃ v, o = some v ∧ v ∈ R) =
      ((N ∩ R).card : ℝ≥0∞) / N.card := by
  rw [Probability.neighborDraw, dite_eq_left hN, mass_map]
  have he : (fun u : V => ∃ v, some u = some v ∧ v ∈ R) = fun u => u ∈ R := by
    funext u
    simp only [Option.some.injEq]
    exact propext ⟨fun ⟨v, huv, hv⟩ => huv.symm ▸ hv, fun hu => ⟨u, rfl, hu⟩⟩
  rw [he, Probability.mass_uniform N hN (fun u => u ∈ R)]
  apply congrArg (fun S : Finset V => (S.card : ℝ≥0∞) / N.card)
  ext v
  simp

/-- The exact past-conditioned caught probability is bounded by (x-1)/ell.
The source is already reached and the row is loopless, giving the essential
minus one. This does not condition on the phase eventually closing. -/
theorem history_caught_le (N : V → Finset V) (old : Finset V) (limit : ℕ)
    (root : V) (fuel : ℕ) (reference : Tape V) (href : reference ∈ (sample N).support)
    (ell x : ℕ) (hell : 0 < ell) (a : V × Fin 2)
    (ha : a ∈ (run old limit reference fuel (initial root limit)).pending)
    (hdegree : ell ≤ (N a.1).card) (hloop : a.1 ∉ N a.1)
    (hsize : (run old limit reference fuel (initial root limit)).reached.card ≤ x) :
    mass ((sample N).filter
      {tape | history old limit root fuel tape = history old limit root fuel reference}
      ⟨reference, rfl, href⟩)
      (fun tape => ∃ v, tape a = some v ∧
        v ∈ (run old limit reference fuel (initial root limit)).reached) ≤
      ((x - 1 : ℕ) : ℝ≥0∞) / ell := by
  have hi := run_inventory old limit reference fuel (initial_inventory root limit)
  have hfree : a ∉ (run old limit reference fuel (initial root limit)).exposed :=
    fun hx => disjoint_left.mp hi.disjoint ha hx
  have hN : (N a.1).Nonempty := card_pos.mp (hell.trans_le hdegree)
  rw [history_unexposed_mass N old limit root fuel reference href a hfree
    (fun o => ∃ v, o = some v ∧
      v ∈ (run old limit reference fuel (initial root limit)).reached),
    mass_neighborDraw_hits _ _ hN]
  apply ENNReal.div_le_div
  · have hsub : N a.1 ∩ (run old limit reference fuel (initial root limit)).reached ⊆
        (run old limit reference fuel (initial root limit)).reached.erase a.1 := by
      intro v hv
      obtain ⟨hvN, hvR⟩ := mem_inter.mp hv
      refine mem_erase.mpr ⟨?_, hvR⟩
      intro he
      exact hloop (he ▸ hvN)
    have hcard := card_le_card hsub
    rw [card_erase_of_mem (hi.pending_source ha)] at hcard
    exact_mod_cast (show (N a.1 ∩ (run old limit reference fuel (initial root limit)).reached).card ≤
      x - 1 by omega)
  · exact_mod_cast hdegree

theorem phase_root_mem (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V) :
    root ∈ (phase old limit tape root).reached :=
  run_reached_mono old limit tape _ _ (mem_singleton_self root)

def Exposure.Keeps (E : Exposure V) (tape : Tape V) : Prop :=
  ∀ a ∈ E.exposed, ∃ v, tape a = some v ∧ v ∈ E.reached

theorem initial_keeps (root : V) (limit : ℕ) (tape : Tape V) :
    (initial root limit).Keeps tape := by simp [Exposure.Keeps, initial]

theorem Exposure.Keeps.add_draw {E : Exposure V} {tape : Tape V} (h : E.Keeps tape)
    (R : Finset V) (hR : E.reached ⊆ R) (a : V × Fin 2) (v : V)
    (ha : tape a = some v) (hv : v ∈ R) :
    ({ E with reached := R, exposed := insert a E.exposed } : Exposure V).Keeps tape := by
  intro b hb
  rcases mem_insert.mp hb with hba | hbE
  · subst b
    exact ⟨v, ha, hv⟩
  · obtain ⟨w, hw, hwE⟩ := h b hbE
    exact ⟨w, hw, hR hwE⟩

theorem step_keeps (old : Finset V) (limit : ℕ) (tape : Tape V)
    {E : Exposure V} (hk : E.Keeps tape) (hc : (step old limit tape E).Clean) :
    (step old limit tape E).Keeps tape := by
  by_cases hs : E.Stopped
  · simpa only [step_of_stopped old limit tape E hs] using hk
  · rw [step, if_neg hs] at hc ⊢
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp] at hc ⊢
      cases ht : tape (E.pending.min' hp) with
      | none => simp [ht, Exposure.Clean] at hc
      | some v =>
        simp only [ht] at hc ⊢
        split_ifs with ho hr hl
        · simp [ho, Exposure.Clean] at hc
        · exact hk.add_draw E.reached Subset.rfl _ v ht hr
        · simp [ho, hr, hl, Exposure.Clean] at hc
        · exact hk.add_draw (insert v E.reached) (subset_insert _ _) _ v ht (mem_insert_self _ _)
    · simpa only [dite_eq_right hp] using hk

theorem run_keeps (old : Finset V) (limit : ℕ) (tape : Tape V) (fuel : ℕ)
    {E : Exposure V} (hk : E.Keeps tape) (hc : (run old limit tape fuel E).Clean) :
    (run old limit tape fuel E).Keeps tape := by
  induction fuel generalizing E with
  | zero => exact hk
  | succ fuel ih =>
    exact ih (step_keeps old limit tape hk (run_clean_start old limit tape fuel _ hc)) hc

theorem phase_closed_successor (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V)
    (hc : (phase old limit tape root).Clean) {v : V}
    (hv : v ∈ (phase old limit tape root).reached) (i : Fin 2) :
    ∃ w, tape (v, i) = some w ∧ w ∈ (phase old limit tape root).reached := by
  have hp : (phase old limit tape root).pending = ∅ := by
    rcases phase_stopped old limit tape root with h | h | h | h
    · simp [hc.1] at h
    · simp [hc.2.1] at h
    · simp [hc.2.2] at h
    · exact h
  have hmem : (v, i) ∈ (phase old limit tape root).exposed := by
    have hh : (v, i) ∈ (phase old limit tape root).reached ×ˢ univ :=
      mem_product.mpr ⟨hv, mem_univ _⟩
    rw [← (phase_inventory old limit tape root).partition, hp, empty_union] at hh
    exact hh
  exact run_keeps old limit tape _ (initial_keeps root limit tape) hc (v, i) hmem

/-- A loopless tape cannot close a singleton phase. This proves the zero
first term in the later small-phase probability sum. -/
theorem phase_closed_two_le (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V)
    (hloop : ∀ a, tape a ≠ some a.1) (hc : (phase old limit tape root).Clean) :
    2 ≤ (phase old limit tape root).reached.card := by
  have hr := phase_root_mem old limit tape root
  obtain ⟨w, hw, hwR⟩ := phase_closed_successor old limit tape root hc hr 0
  have hne : root ≠ w := by
    intro he
    subst w
    exact hloop (root, 0) hw
  exact one_lt_card.mpr ⟨root, hr, w, hwR, hne⟩

/-- The actual undirected graph selected by the complete predrawn tape. -/
def selectedGraph (tape : Tape V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((∃ i, tape (u, i) = some v) ∨ ∃ i, tape (v, i) = some u)
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

theorem selectedGraph_adj_of_draw (tape : Tape V) {u v : V} {i : Fin 2}
    (huv : u ≠ v) (hdraw : tape (u, i) = some v) : (selectedGraph tape).Adj u v :=
  ⟨huv, Or.inl ⟨i, hdraw⟩⟩

def Exposure.Rooted (E : Exposure V) (tape : Tape V) (root : V) : Prop :=
  ∀ v ∈ E.reached, (selectedGraph tape).Reachable root v

theorem initial_rooted (root : V) (limit : ℕ) (tape : Tape V) :
    (initial root limit).Rooted tape root := by
  intro v hv
  have he : v = root := mem_singleton.mp hv
  subst v
  exact SimpleGraph.Reachable.rfl

theorem step_rooted (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V)
    {E : Exposure V} (hE : E.Inventory) (hr : E.Rooted tape root) :
    (step old limit tape E).Rooted tape root := by
  by_cases hs : E.Stopped
  · simpa only [step_of_stopped old limit tape E hs] using hr
  · rw [step, if_neg hs]
    by_cases hp : E.pending.Nonempty
    · simp only [dite_eq_left hp]
      have ha := hE.pending_source (E.pending.min'_mem hp)
      cases ht : tape (E.pending.min' hp) with
      | none => exact hr
      | some v =>
        simp only [ht]
        split_ifs with ho hv hl
        · exact hr
        · exact hr
        · exact hr
        · intro w hw
          rcases mem_insert.mp hw with hwv | hwE
          · subst w
            have hne : (E.pending.min' hp).1 ≠ v := by
              intro he
              exact hv (he ▸ ha)
            exact (hr _ ha).trans (selectedGraph_adj_of_draw tape hne ht).reachable
          · exact hr w hwE
    · simpa only [dite_eq_right hp] using hr

theorem run_rooted (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V)
    (fuel : ℕ) {E : Exposure V} (hE : E.Inventory) (hr : E.Rooted tape root) :
    (run old limit tape fuel E).Rooted tape root := by
  induction fuel generalizing E with
  | zero => exact hr
  | succ fuel ih =>
    exact ih (step_inventory old limit tape hE) (step_rooted old limit tape root hE hr)

/-- Every vertex newly reached in the actual phase belongs to the root's
selected-edge component; unrevealed edges can only merge these components. -/
theorem phase_rooted (old : Finset V) (limit : ℕ) (tape : Tape V) (root : V) :
    (phase old limit tape root).Rooted tape root :=
  run_rooted old limit tape root _ (initial_inventory root limit) (initial_rooted root limit tape)

def Avoids (S : Finset V) (tape : Tape V) : Prop :=
  ∀ a v, tape a = some v → (a.1 ∈ S ↔ v ∈ S)

theorem selectedGraph_adj_sameSide {S : Finset V} {tape : Tape V}
    (h : Avoids S tape) {u v : V} (huv : (selectedGraph tape).Adj u v) :
    u ∈ S ↔ v ∈ S := by
  rcases huv.2 with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact h (u, i) v hi
  · exact (h (v, i) u hi).symm

/-- Avoidance preserves the fixed cut on entire connected components, not
merely on the individually sampled edges. -/
theorem selectedGraph_reachable_sameSide {S : Finset V} {tape : Tape V}
    (h : Avoids S tape) {u v : V} (huv : (selectedGraph tape).Reachable u v) :
    u ∈ S ↔ v ∈ S := by
  obtain ⟨walk⟩ := huv
  induction walk with
  | nil => exact Iff.rfl
  | cons hadj walk ih => exact (selectedGraph_adj_sameSide h hadj).trans ih

theorem selectedGraph_component_sameSide {S : Finset V} {tape : Tape V}
    (h : Avoids S tape) {u v : V}
    (he : (selectedGraph tape).connectedComponentMk u =
      (selectedGraph tape).connectedComponentMk v) : u ∈ S ↔ v ∈ S :=
  selectedGraph_reachable_sameSide h (SimpleGraph.ConnectedComponent.exact he)

def componentCount (tape : Tape V) : ℕ := Fintype.card (selectedGraph tape).ConnectedComponent

theorem componentCount_le (tape : Tape V) : componentCount tape ≤ Fintype.card V := by
  apply Fintype.card_le_of_surjective (selectedGraph tape).connectedComponentMk
  intro C
  exact Quot.exists_rep C

/-- The actual component map reuses Common's public quotient interface.
It stores only the sampled tape's map and surjectivity, never a hidden graph. -/
def publicQuotient (tape : Tape V) :
    PublicQuotient V (selectedGraph tape).ConnectedComponent where
  map := (selectedGraph tape).connectedComponentMk
  onto := fun C => Quot.exists_rep C

theorem publicQuotient_respects {S : Finset V} {tape : Tape V}
    (h : Avoids S tape) : RespectsBlocks (publicQuotient tape).map S := by
  intro u v huv
  exact selectedGraph_component_sameSide h huv

/-- Every surviving actual minimum is preserved by the constructed public
component quotient. This is the cut/value transfer used after the size bound. -/
theorem publicQuotient_preserves_minimum (tape : Tape V) (G : WeightedGraph V)
    (S : Finset V) (hS : IsMinCut G S) (h : Avoids S tape) :
    IsMinCut ((publicQuotient tape).graph G) (S.image (publicQuotient tape).map) ∧
      mincutValue ((publicQuotient tape).graph G) = mincutValue G ∧
      2 ≤ componentCount tape := by
  have hr := publicQuotient_respects h
  exact ⟨(publicQuotient tape).project_minimum hS hr,
    (publicQuotient tape).mincut_eq hS hr,
    (publicQuotient tape).two_le_card_of_survives hr hS.1⟩

#print axioms sample
#print axioms phase_inventory
#print axioms step_exposed_card
#print axioms phase_stopped
#print axioms phase_closed_caught
#print axioms phase_closed_successor
#print axioms phase_closed_two_le
#print axioms phase_rooted
#print axioms run_of_stopped
#print axioms run_reached_mono
#print axioms run_exposed_mono
#print axioms run_eq_of_agree
#print axioms condition_cylinder_coordinate
#print axioms history_eq_iff
#print axioms history_unexposed_mass
#print axioms history_caught_le
#print axioms selectedGraph_component_sameSide
#print axioms componentCount_le
#print axioms publicQuotient_respects
#print axioms publicQuotient_preserves_minimum

end
end CutQueryComplexity.StarContraction2022.Contraction.TwoOut
