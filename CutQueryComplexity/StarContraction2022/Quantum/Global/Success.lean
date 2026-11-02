import CutQueryComplexity.StarContraction2022.Quantum.Global.Program

/-! # Correctness of the executed global quantum program

Finite event arithmetic is applied to the actual joint Born law. In particular,
the high-case amplification is deduced from its product law, not assumed.
-/
set_option autoImplicit false
namespace CutQueryComplexity.StarContraction2022.Quantum.Global
noncomputable section
open QuantumQueryComplexity ProductPrograms
open scoped Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

section FiniteEvents
open scoped Classical
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]

def eventMass (P : A → ℝ) (E : A → Prop) : ℝ := ∑ a, if E a then P a else 0

theorem eventMass_nonneg {P : A → ℝ} (hP : ∀ a, 0 ≤ P a) (E : A → Prop) :
    0 ≤ eventMass P E := Finset.sum_nonneg fun a _ => by split_ifs <;> simp_all

theorem le_eventMass {P : A → ℝ} (hP : ∀ a, 0 ≤ P a) (E : A → Prop) (a : A) (ha : E a) :
    P a ≤ eventMass P E := by
  unfold eventMass
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if E b then P b else 0)
    (fun b _ => by split_ifs <;> simp_all) (Finset.mem_univ a)
  simpa only [ite_eq_left ha] using h

theorem eventMass_congr_event (P : A → ℝ) {E F : A → Prop} (h : ∀ a, E a ↔ F a) :
    eventMass P E = eventMass P F := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro a _
  rw [h a]

theorem eventMass_compl (P : A → ℝ) (E : A → Prop) (hP : ∑ a, P a = 1) :
    eventMass P (fun a => ¬ E a) = 1 - eventMass P E := by
  have h : eventMass P (fun a => ¬ E a) + eventMass P E = 1 := by
    rw [eventMass, eventMass, ← Finset.sum_add_distrib, ← hP]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : E a <;> simp [ha]
  linarith

theorem eventMass_mono_support {P : A → ℝ} (hP : ∀ a, 0 ≤ P a) {E F : A → Prop}
    (h : ∀ a, 0 < P a → E a → F a) : eventMass P E ≤ eventMass P F := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : 0 < P a
  · by_cases he : E a
    · simp [he, h a hp he]
    · simp [he, ite_nonneg (hP a) (le_refl 0)]
  · have hz : P a = 0 := le_antisymm (le_of_not_gt hp) (hP a)
    simp [hz]

theorem eventMass_fibre [DecidableEq B] (P : A → ℝ) (f : A → B) (E : B → Prop) :
    eventMass (fun b => ∑ a ∈ Finset.univ.filter (fun a => f a = b), P a) E =
      eventMass P (fun a => E (f a)) := by
  simp only [eventMass, Finset.sum_filter]
  calc
    _ = ∑ b, ∑ a, if f a = b then (if E b then P a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : E b <;> simp [hb]
    _ = ∑ a, ∑ b, if f a = b then (if E b then P a else 0) else 0 := Finset.sum_comm
    _ = _ := by simp

omit [Fintype B] in
theorem positive_fibre [DecidableEq B] {P : A → ℝ} (hP : ∀ a, 0 ≤ P a) (f : A → B) (b : B)
    (h : 0 < ∑ a ∈ Finset.univ.filter (fun a => f a = b), P a) :
    ∃ a, f a = b ∧ 0 < P a := by
  obtain ⟨a, ha, hp⟩ := (Finset.sum_pos_iff_of_nonneg (fun a _ => hP a)).mp h
  exact ⟨a, (Finset.mem_filter.mp ha).2, hp⟩

theorem eventMass_product [DecidableEq I] (P : I → A → ℝ) (E : I → A → Prop) :
    eventMass (fun y : I → A => ∏ i, P i (y i)) (fun y => ∀ i, E i (y i)) =
      ∏ i, eventMass (P i) (E i) := by
  simp only [eventMass]
  calc
    _ = ∑ y : I → A, ∏ i, if E i (y i) then P i (y i) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Fintype.prod_ite_zero]
    _ = _ := (Fintype.prod_sum (fun i a => if E i a then P i a else 0)).symm

theorem eventMass_coordinate [DecidableEq I] (P : I → A → ℝ)
    (hP : ∀ i, ∑ a, P i a = 1) (i : I) (E : A → Prop) :
    eventMass (fun y : I → A => ∏ j, P j (y j)) (fun y => E (y i)) = eventMass (P i) E := by
  have h := eventMass_product P (fun j a => if j = i then E a else True)
  have he (y : I → A) : (∀ j, if j = i then E (y j) else True) ↔ E (y i) := by
    constructor
    · intro hy; simpa using hy i
    · intro hy j; by_cases hj : j = i <;> simp_all
  simp_rw [he] at h
  rw [h]
  have ht (j : I) : eventMass (P j) (fun a => if j = i then E a else True) =
      if j = i then eventMass (P i) E else 1 := by
    by_cases hj : j = i
    · subst j; simp
    · simp [hj, eventMass, hP j]
  simp_rw [ht]
  simp

end FiniteEvents

theorem realizes_sum {I S X O : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype X] [Fintype O] [DecidableEq O]
    {read : X → I → S} {q : ℕ} {P : X → O → ℝ} (h : Realizes read q P) (x : X) :
    ∑ o, P x o = 1 := by
  obtain ⟨W, hF, hD, T, hT⟩ := h
  simp_rw [← hT x]
  exact T.sum_prob _ _

variable {n : ℕ}

theorem component_nonneg (n t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (i : Fin (K + 2)) (c : Candidate n) :
    0 ≤ componentLaw n t K ht eta i read c := (component_realizes n t K ht eta i).nonneg read c

theorem component_sum (n t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (i : Fin (K + 2)) :
    ∑ c, componentLaw n t K ht eta i read c = 1 := realizes_sum (component_realizes n t K ht eta i) read

theorem chooseCandidate_mem (a b : Candidate n) : chooseCandidate a b = a ∨ chooseCandidate a b = b := by
  cases a with
  | none => simp [chooseCandidate]
  | some a => cases b with
    | none => simp [chooseCandidate]
    | some b => simp only [chooseCandidate]; split_ifs <;> simp

theorem chooseCandidate_sound (G : CapacityGraph (Fin n) 1) {a b : Candidate n}
    (ha : CandidateSound G a) (hb : CandidateSound G b) : CandidateSound G (chooseCandidate a b) := by
  rcases chooseCandidate_mem a b with h | h <;> simpa only [h]

theorem chooseCandidate_le_left (S : Finset (Fin n)) (a : CutAnswer n 1) (b : Candidate n) :
    ∃ T c, chooseCandidate (some (S, a)) b = some (T, c) ∧ decodeCutAnswer c ≤ decodeCutAnswer a := by
  cases b with
  | none => exact ⟨S, a, rfl, le_rfl⟩
  | some b =>
    rcases b with ⟨T, c⟩
    simp only [chooseCandidate]
    split_ifs with h
    · exact ⟨S, a, rfl, le_rfl⟩
    · exact ⟨T, c, rfl, (le_of_not_ge h)⟩

theorem chooseCandidate_le_right (a : Candidate n) (T : Finset (Fin n)) (b : CutAnswer n 1) :
    ∃ S c, chooseCandidate a (some (T, b)) = some (S, c) ∧ decodeCutAnswer c ≤ decodeCutAnswer b := by
  cases a with
  | none => exact ⟨T, b, rfl, le_rfl⟩
  | some a =>
    rcases a with ⟨S, c⟩
    simp only [chooseCandidate]
    split_ifs with h
    · exact ⟨S, c, rfl, h⟩
    · exact ⟨T, b, rfl, le_rfl⟩

theorem bestList_sound (G : CapacityGraph (Fin n) 1) (xs : List (Candidate n))
    (h : ∀ c ∈ xs, CandidateSound G c) : CandidateSound G (bestList xs) := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    exact chooseCandidate_sound G (h a (by simp)) (ih (fun c hc => h c (by simp [hc])))

theorem bestList_le_mem (xs : List (Candidate n)) (S : Finset (Fin n)) (a : CutAnswer n 1)
    (h : some (S, a) ∈ xs) :
    ∃ T b, bestList xs = some (T, b) ∧ decodeCutAnswer b ≤ decodeCutAnswer a := by
  induction xs with
  | nil => simp at h
  | cons c xs ih =>
    rcases List.mem_cons.mp h with h | h
    · subst c; exact chooseCandidate_le_left S a (bestList xs)
    · obtain ⟨T, b, hb, hle⟩ := ih h
      obtain ⟨U, d, hd, hbd⟩ := chooseCandidate_le_right c T b
      refine ⟨U, d, ?_, hbd.trans hle⟩
      change chooseCandidate c (bestList xs) = some (U, d)
      rw [hb]
      exact hd

theorem minimum_of_sound (G : CapacityGraph (Fin n) 1) (S : Finset (Fin n)) (a : CutAnswer n 1)
    (hs : CandidateSound G (some (S, a))) (hm : decodeCutAnswer a = mincutValue G.toWeighted) :
    Forest.LowMinimumCandidate G (some (S, a)) := by
  refine ⟨S, a, rfl, ⟨hs.1, ?_⟩, hs.2, hm⟩
  intro T hT
  rw [← hs.2, hm]
  exact mincutValue_le G.toWeighted hT

theorem selectCandidate_sound (G : CapacityGraph (Fin n) 1) {K : ℕ} (y : Batch n K)
    (h : ∀ i, CandidateSound G (y i)) : CandidateSound G (selectCandidate y) := by
  apply bestList_sound
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact h i

theorem selectCandidate_minimum (G : CapacityGraph (Fin n) 1) {K : ℕ} (y : Batch n K)
    (hs : ∀ i, CandidateSound G (y i)) (i : Fin (K + 2))
    (hm : Forest.LowMinimumCandidate G (y i)) : Forest.LowMinimumCandidate G (selectCandidate y) := by
  obtain ⟨S, a, ha, _, _, hval⟩ := hm
  obtain ⟨T, b, hb, hle⟩ := bestList_le_mem (List.ofFn y) S a (List.mem_ofFn.mpr ⟨i, ha⟩)
  have hb' : selectCandidate y = some (T, b) := hb
  have hsound := selectCandidate_sound G y hs
  rw [hb'] at hsound ⊢
  apply minimum_of_sound G T b hsound
  exact le_antisymm (hle.trans_eq hval) (candidateSound_mincut_le hsound)

/-- Exact output checks, derived from the actual physical producer supports. -/
theorem singleton_sound (hn : 2 ≤ n) (t : ℕ) (ht : 0 < t) (G : CapacityGraph (Fin n) 1)
    (c : Candidate n) (h : 0 < singletonLaw n t ht (capacityRead G) c) : CandidateSound G c := by
  rw [singletonLaw] at h
  obtain ⟨w, hw, hp⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun w _ => (minimumDegreeWitnessAlg n t ht).prob_nonneg (capacityRead G)
      (minimumDegreeWitnessQueries n t) w)).mp h
  have hw := (Finset.mem_filter.mp hw).2
  obtain ⟨v, rfl⟩ := minimumDegreeWitnessAlg_sound n (by omega) t ht (capacityRead G) w hp
  rw [← hw]
  exact ⟨properShore_singleton v (by simpa using hn), decode_capacityRead G {v}⟩

theorem tree_sound {q : ℕ} (T : ProductTree n (Candidate n) q) (G : CapacityGraph (Fin n) 1)
    (hs : ProductTreeSound T G) (c : Candidate n)
    (h : 0 < (productTreeAlg T).prob (capacityRead G) (physicalQueries n q) c) : CandidateSound G c := by
  apply hs c
  rw [productTreeAlg_prob] at h
  change 0 < ((T.eval (productRead G)) c).toReal at h
  rw [PMF.mem_support_iff]
  intro hz
  simp [hz] at h

theorem component_sound (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (i : Fin (K + 2)) (c : Candidate n)
    (h : 0 < componentLaw n t K ht eta i (capacityRead G) c) : CandidateSound G c := by
  revert h
  refine Fin.cases (singleton_sound hn t ht G c) (fun j => ?_) i
  refine Fin.cases ?_ (fun _ => ?_) j
  · exact tree_sound _ G (Forest.lowCandidate_sound n (rootThreshold n) eta G) c
  · exact tree_sound _ G (UniformStars.highCandidate_sound n G) c

theorem joint_supported (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (y : Batch n K)
    (h : 0 < jointLaw n t K ht eta (capacityRead G) y) : ∀ i, CandidateSound G (y i) := by
  intro i
  apply component_sound hn t K ht eta G i
  apply lt_of_le_of_ne (component_nonneg n t K ht eta (capacityRead G) i (y i))
  exact Ne.symm ((Finset.prod_ne_zero_iff.mp (ne_of_gt h)) i (Finset.mem_univ i))

theorem globalAlg_sound (n t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (c : Candidate n)
    (h : 0 < (globalAlg n t K ht eta).prob (capacityRead G) (globalQueries n t K eta) c) :
    CandidateSound G c := by
  rw [globalAlg_law, globalLaw] at h
  by_cases hn : 2 ≤ n
  · rw [ite_eq_left hn] at h
    obtain ⟨y, hy, hp⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun y _ => (joint_realizes n t K ht eta).nonneg (capacityRead G) y)).mp h
    have hy := (Finset.mem_filter.mp hy).2
    rw [← hy]
    exact selectCandidate_sound G y (joint_supported hn t K ht eta G y hp)
  · rw [ite_eq_right hn] at h
    by_cases hc : c = none
    · subst c; trivial
    · simp [hc] at h

theorem global_event_joint (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (E : Candidate n → Prop) :
    eventMass (globalLaw n t K ht eta read) E =
      eventMass (jointLaw n t K ht eta read) (fun y => E (selectCandidate y)) := by
  unfold globalLaw
  simp only [ite_eq_left hn]
  exact eventMass_fibre _ _ _

theorem singleton_event (t : ℕ) (ht : 0 < t) (read : AnswerTable n) (E : Candidate n → Prop) :
    eventMass (singletonLaw n t ht read) E =
      eventMass (fun w => (minimumDegreeWitnessAlg n t ht).prob read (minimumDegreeWitnessQueries n t) w)
        (fun w => E (witnessCandidate w)) := by
  exact eventMass_fibre _ _ _

/-- A failed selected result implies failure of each actual trial on that
supported joint transcript. No conditional success hypothesis is supplied. -/
theorem selected_failure_coordinate (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) (i : Fin (K + 2)) :
    eventMass (globalLaw n t K ht eta (capacityRead G)) (fun c => ¬ Forest.LowMinimumCandidate G c) ≤
      eventMass (componentLaw n t K ht eta i (capacityRead G)) (fun c => ¬ Forest.LowMinimumCandidate G c) := by
  rw [global_event_joint hn]
  rw [← eventMass_coordinate (fun j => componentLaw n t K ht eta j (capacityRead G))
    (component_sum n t K ht eta (capacityRead G)) i]
  apply eventMass_mono_support ((joint_realizes n t K ht eta).nonneg (capacityRead G))
  intro y hy hfail hmin
  exact hfail (selectCandidate_minimum G y (joint_supported hn t K ht eta G y hy) i hmin)

/-- Rectangles of the K executed high outputs have exactly the product law,
also conditional on arbitrary singleton/low output events. -/
theorem joint_event_factorization (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (E₀ E₁ E : Candidate n → Prop) :
    eventMass (jointLaw n t K ht eta read)
      (fun y => E₀ (y 0) ∧ E₁ (y (Fin.succ 0)) ∧ ∀ i : Fin K, E (y i.succ.succ)) =
      eventMass (singletonLaw n t ht read) E₀ * eventMass (lowLaw n eta read) E₁ *
        eventMass (highLaw n read) E ^ K := by
  unfold jointLaw
  have h := eventMass_product (fun i => componentLaw n t K ht eta i read)
    (Fin.cons E₀ (Fin.cons E₁ (fun _ : Fin K => E)))
  simpa only [jointLaw, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.prod_univ_succ, componentLaw, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_assoc] using h

theorem joint_high_failure (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (E : Candidate n → Prop) :
    eventMass (jointLaw n t K ht eta read) (fun y => ∀ i : Fin K, ¬ E (y i.succ.succ)) =
      eventMass (highLaw n read) (fun c => ¬ E c) ^ K := by
  calc
    _ = eventMass (jointLaw n t K ht eta read)
        (fun y => True ∧ True ∧ ∀ i : Fin K, ¬ E (y i.succ.succ)) := by
      apply eventMass_congr_event
      intro y
      simp only [true_and]
    _ = eventMass (singletonLaw n t ht read) (fun _ => True) *
        eventMass (lowLaw n eta read) (fun _ => True) *
        eventMass (highLaw n read) (fun c => ¬ E c) ^ K :=
      joint_event_factorization t K ht eta read (fun _ => True) (fun _ => True) (fun c => ¬ E c)
    _ = _ := by
      have h₀ : eventMass (singletonLaw n t ht read) (fun _ => True) = 1 := by
        simpa only [eventMass, ite_true] using realizes_sum (singleton_realizes n t ht) read
      have h₁ : eventMass (lowLaw n eta read) (fun _ => True) = 1 := by
        simpa only [eventMass, ite_true] using realizes_sum (low_realizes n eta) read
      rw [h₀, h₁, one_mul, one_mul]

theorem selected_failure_high (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (G : CapacityGraph (Fin n) 1) :
    eventMass (globalLaw n t K ht eta (capacityRead G)) (fun c => ¬ Forest.LowMinimumCandidate G c) ≤
      eventMass (highLaw n (capacityRead G)) (fun c => ¬ Forest.LowMinimumCandidate G c) ^ K := by
  rw [global_event_joint hn, ← joint_high_failure t K ht eta (capacityRead G)]
  apply eventMass_mono_support ((joint_realizes n t K ht eta).nonneg (capacityRead G))
  intro y hy hfail i hmin
  exact hfail (selectCandidate_minimum G y (joint_supported hn t K ht eta G y hy) i.succ.succ hmin)

theorem high_minimum_is_low (G : CapacityGraph (Fin n) 1) (c : Candidate n)
    (h : UniformStars.MinimumCandidate G c) : Forest.LowMinimumCandidate G c := by
  obtain ⟨r, hr, hs, hm, hv⟩ := h
  cases c with
  | none => simp [decodeFiniteCutResult] at hr
  | some c =>
    rcases c with ⟨S, a⟩
    have he : (⟨S, decodeCutAnswer a⟩ : CutResult (Fin n)) = r := Option.some.inj hr
    subst r
    exact ⟨S, a, rfl, hm, hs.2, hv⟩

theorem singleton_success (hn : 2 ≤ n) (t : ℕ) (ht : 0 < t)
    (G : CapacityGraph (Fin n) 1)
    (heq : mincutValue G.toWeighted = ((minimumDegreeValue G : ℕ) : ℝ)) :
    1 - (8 / 9 : ℝ) ^ t ≤ eventMass (singletonLaw n t ht (capacityRead G)) (Forest.LowMinimumCandidate G) := by
  classical
  obtain ⟨v, hv, _, hp⟩ := minimumDegreeWitnessAlg_honest_minimum (by omega) t ht G
  have hmin : Forest.LowMinimumCandidate G (witnessCandidate (some (v, capacityRead G {v}))) := by
    apply minimum_of_sound G {v} (capacityRead G {v})
    · exact ⟨properShore_singleton v (by simpa using hn), decode_capacityRead G {v}⟩
    · rw [decode_capacityRead, CapacityGraph.toWeighted_cut, hv]
      exact heq.symm
  rw [singleton_event]
  exact hp.trans (le_eventMass
    (fun w => (minimumDegreeWitnessAlg n t ht).prob_nonneg (capacityRead G)
      (minimumDegreeWitnessQueries n t) w) _ _ hmin)

theorem low_success (hn : 2 ≤ n) (eta : ℝ) (heta : 0 < eta)
    (G : CapacityGraph (Fin n) 1) (hlt : mincutValue G.toWeighted < rootThreshold n) :
    1 - eta ≤ eventMass (lowLaw n eta (capacityRead G)) (Forest.LowMinimumCandidate G) := by
  have h := Forest.lowCandidate_physical_successProb n (rootThreshold n) eta heta G hn hlt
  rw [goodProb_eq_sum] at h
  exact h

theorem high_success (hn : 2 ≤ n) (G : CapacityGraph (Fin n) 1)
    (hroot : (rootThreshold n : ℝ) ≤ ((minimumDegreeValue G : ℕ) : ℝ))
    (hlt : mincutValue G.toWeighted < ((minimumDegreeValue G : ℕ) : ℝ)) :
    UniformStars.pstar ≤ eventMass (highLaw n (capacityRead G)) (Forest.LowMinimumCandidate G) := by
  have hdegree (v : Fin n) : ((minimumDegreeValue G : ℕ) : ℝ) ≤ G.toWeighted.degree v := by
    rw [← WeightedGraph.cut_singleton, CapacityGraph.toWeighted_cut]
    exact_mod_cast minimumDegreeValue_le (by omega) G v
  have h := UniformStars.highCandidate_physical_success G _ hn hroot hdegree hlt
  rw [productTreeRoutine_state, goodProb_eq_sum] at h
  apply h.trans
  apply eventMass_mono_support ((high_realizes n).nonneg (capacityRead G))
  intro c _ hc
  exact high_minimum_is_low G c hc

/-- Every simple graph is covered by these three analytic cases; the circuit
itself never tests the hidden degree or minimum-cut value. -/
theorem graph_cases (hn : 2 ≤ n) (G : CapacityGraph (Fin n) 1) :
    mincutValue G.toWeighted = ((minimumDegreeValue G : ℕ) : ℝ) ∨
    mincutValue G.toWeighted < rootThreshold n ∨
    (mincutValue G.toWeighted < ((minimumDegreeValue G : ℕ) : ℝ) ∧
      (rootThreshold n : ℝ) ≤ ((minimumDegreeValue G : ℕ) : ℝ)) := by
  obtain ⟨v, hv⟩ := minimumDegreeValue_attained (by omega) G
  have hle := mincutValue_le G.toWeighted (properShore_singleton v (by simpa using hn))
  rw [CapacityGraph.toWeighted_cut, hv] at hle
  by_cases heq : mincutValue G.toWeighted = ((minimumDegreeValue G : ℕ) : ℝ)
  · exact Or.inl heq
  · by_cases hlt : mincutValue G.toWeighted < rootThreshold n
    · exact Or.inr (Or.inl hlt)
    · exact Or.inr (Or.inr ⟨lt_of_le_of_ne hle heq, (le_of_not_gt hlt).trans hle⟩)

/-- Exact conditional law after any positive-probability event of the first
two producer outputs, including inconsistent physical answer tables. -/
theorem joint_conditional_high (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (E₀ E₁ E : Candidate n → Prop)
    (hprefix : 0 < eventMass (jointLaw n t K ht eta read)
      (fun y => E₀ (y 0) ∧ E₁ (y (Fin.succ 0)))) :
    eventMass (jointLaw n t K ht eta read)
      (fun y => E₀ (y 0) ∧ E₁ (y (Fin.succ 0)) ∧ ∀ i : Fin K, E (y i.succ.succ)) /
      eventMass (jointLaw n t K ht eta read) (fun y => E₀ (y 0) ∧ E₁ (y (Fin.succ 0))) =
        eventMass (highLaw n read) E ^ K := by
  have hden : eventMass (jointLaw n t K ht eta read)
      (fun y => E₀ (y 0) ∧ E₁ (y (Fin.succ 0))) =
      eventMass (singletonLaw n t ht read) E₀ * eventMass (lowLaw n eta read) E₁ := by
    calc
      _ = eventMass (jointLaw n t K ht eta read)
          (fun y => E₀ (y 0) ∧ E₁ (y (Fin.succ 0)) ∧ ∀ _ : Fin K, True) := by
        apply eventMass_congr_event
        intro y
        simp
      _ = _ := by
        rw [joint_event_factorization t K ht eta read E₀ E₁ (fun _ => True)]
        have hhigh : eventMass (highLaw n read) (fun _ => True) = 1 := by
          simpa only [eventMass, ite_true] using realizes_sum (high_realizes n) read
        rw [hhigh, one_pow, mul_one]
  apply (div_eq_iff (ne_of_gt hprefix)).mpr
  rw [joint_event_factorization, hden]
  ring

/-- Parameter conditions are public numerical error choices. All execution,
support, independence and graph correctness facts are derived above. -/
theorem global_success_of_errors (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (heta : 0 < eta) (hetab : eta ≤ 1 / 3) (htb : (8 / 9 : ℝ) ^ t ≤ 1 / 3)
    (hKb : (1 - UniformStars.pstar) ^ K ≤ 1 / 3) (G : CapacityGraph (Fin n) 1) :
    2 / 3 ≤ eventMass (globalLaw n t K ht eta (capacityRead G)) (Forest.LowMinimumCandidate G) := by
  have hcomp := eventMass_compl (globalLaw n t K ht eta (capacityRead G))
    (Forest.LowMinimumCandidate G) (realizes_sum (global_realizes n t K ht eta) (capacityRead G))
  suffices hfail : eventMass (globalLaw n t K ht eta (capacityRead G))
      (fun c => ¬ Forest.LowMinimumCandidate G c) ≤ 1 / 3 by linarith
  rcases graph_cases hn G with heq | hlow | ⟨hlt, hroot⟩
  · have hs := singleton_success hn t ht G heq
    have hc := eventMass_compl (singletonLaw n t ht (capacityRead G))
      (Forest.LowMinimumCandidate G) (realizes_sum (singleton_realizes n t ht) (capacityRead G))
    have hf := selected_failure_coordinate hn t K ht eta G 0
    change eventMass (globalLaw n t K ht eta (capacityRead G))
      (fun c => ¬ Forest.LowMinimumCandidate G c) ≤
      eventMass (singletonLaw n t ht (capacityRead G)) (fun c => ¬ Forest.LowMinimumCandidate G c) at hf
    linarith
  · have hs := low_success hn eta heta G hlow
    have hc := eventMass_compl (lowLaw n eta (capacityRead G))
      (Forest.LowMinimumCandidate G) (realizes_sum (low_realizes n eta) (capacityRead G))
    have hf := selected_failure_coordinate hn t K ht eta G (Fin.succ 0)
    change eventMass (globalLaw n t K ht eta (capacityRead G))
      (fun c => ¬ Forest.LowMinimumCandidate G c) ≤
      eventMass (lowLaw n eta (capacityRead G)) (fun c => ¬ Forest.LowMinimumCandidate G c) at hf
    linarith
  · have hs := high_success hn G hroot hlt
    have hc := eventMass_compl (highLaw n (capacityRead G))
      (Forest.LowMinimumCandidate G) (realizes_sum (high_realizes n) (capacityRead G))
    have he : eventMass (highLaw n (capacityRead G)) (fun c => ¬ Forest.LowMinimumCandidate G c) ≤
        1 - UniformStars.pstar := by linarith
    have hp := pow_le_pow_left₀
      (eventMass_nonneg ((high_realizes n).nonneg (capacityRead G)) (fun c => ¬ Forest.LowMinimumCandidate G c)) he K
    exact (selected_failure_high hn t K ht eta G).trans (hp.trans hKb)

theorem exists_public_high_trials : ∃ K : ℕ, (1 - UniformStars.pstar) ^ K ≤ 1 / 3 := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 3)
    (by linarith [UniformStars.pstar_pos] : 1 - UniformStars.pstar < 1)
  exact ⟨K, le_of_lt hK⟩

/-- Fixed once and for all, before n and the hidden graph. -/
def publicHighTrials : ℕ := exists_public_high_trials.choose

theorem publicHighTrials_error : (1 - UniformStars.pstar) ^ publicHighTrials ≤ 1 / 3 :=
  exists_public_high_trials.choose_spec

theorem public_singleton_error : (8 / 9 : ℝ) ^ 12 ≤ 1 / 3 := by norm_num

open scoped Classical in
/-- The actual final physical state returns a proper minimum shore and its
exact original cut value with probability at least two thirds. -/
theorem globalRoutine_public_success (n : ℕ) (G : CapacityGraph (Fin n) 1) (hn : 2 ≤ n) :
    2 / 3 ≤ goodProb (globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).readout
      (Forest.LowMinimumCandidate G)
      ((globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).run (capacityRead G) *ᵥ
        (globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).init) := by
  rw [globalRoutine_event_law]
  exact global_success_of_errors hn 12 publicHighTrials (by norm_num) (1 / 3)
    (by norm_num) le_rfl public_singleton_error publicHighTrials_error G

open scoped Classical in
/-- Literal program-before-input contract. The single fixed K precedes n;
the circuit precedes G. The schedule and normalization hold for every native
answer table, and supported outputs are always truthful. No cost envelope
from the separate Global.CostBounds module is assumed here. -/
theorem exists_public_global_program :
    ∃ K : ℕ, ∀ n : ℕ, ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : CutQAlg n 1 (Candidate n) Work)
      (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) Work),
      R.len = globalQueries n 12 K (1 / 3) ∧ T.step = R.step ∧
      (∀ read : AnswerTable n, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ (G : CapacityGraph (Fin n) 1) (c : Candidate n),
        0 < T.prob (capacityRead G) R.len c → CandidateSound G c) ∧
      (∀ (G : CapacityGraph (Fin n) 1), 2 ≤ n →
        2 / 3 ≤ goodProb T.readout (Forest.LowMinimumCandidate G) (R.run (capacityRead G) *ᵥ T.init)) ∧
      (n < 2 → R.len = 0 ∧ ∀ read : AnswerTable n, T.prob read R.len none = 1) := by
  refine ⟨publicHighTrials, fun n => ⟨globalWork n 12 publicHighTrials (by norm_num) (1 / 3),
    inferInstance, inferInstance, globalAlg n 12 publicHighTrials (by norm_num) (1 / 3),
    globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3), rfl, rfl, ?_, ?_, ?_, ?_⟩⟩
  · intro read
    exact ⟨globalRoutine_state _ _ _ _ _ read, globalRoutine_normalized _ _ _ _ _ read⟩
  · intro G c h
    exact globalAlg_sound _ _ _ _ _ G c h
  · intro G hn
    exact globalRoutine_public_success n G hn
  · intro hn
    have hlen : (globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).len = 0 := by
      simp [globalQueries, Nat.not_le.mpr hn]
    refine ⟨hlen, fun read => ?_⟩
    rw [hlen]
    exact (global_small hn 12 publicHighTrials (by norm_num) (1 / 3) read).2

#print axioms globalAlg_sound
#print axioms joint_event_factorization
#print axioms joint_conditional_high
#print axioms selected_failure_high
#print axioms singleton_success
#print axioms low_success
#print axioms high_success
#print axioms graph_cases
#print axioms global_success_of_errors
#print axioms publicHighTrials_error
#print axioms globalRoutine_public_success
#print axioms exists_public_global_program
end
end CutQueryComplexity.StarContraction2022.Quantum.Global
