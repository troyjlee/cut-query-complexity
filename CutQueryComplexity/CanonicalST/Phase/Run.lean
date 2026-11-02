import CutQueryComplexity.CanonicalST.Phase.State
import CutQueryComplexity.CanonicalST.Phase.Budget
import CutQueryComplexity.CanonicalST.LongEdge.Search
import CutQueryComplexity.CanonicalST.Augmentation.Progress

/-!
# Actual canonical-witness phases with public fuel

The executable operations use the fixed core, the learned state, public target
and deficit, and earlier oracle answers. A feasible target is not an input.
The sparse augmentation theorem is used only to refute a target when the
actual long-edge search reports absence.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Phase

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def witnesses (A : CoreData V) (s t : V) (f k : ℕ) (P : State V) :=
  Witness.canonicalWitnesses A.C A.K s t P.L (f - k / 2 - 1)

def potential (A : CoreData V) (s t : V) (f k : ℕ) (P : State V) : V → ℚ :=
  Witness.potential (canonicalFamily A.C A.K s t) (P.graph A) (f - k / 2 - 1)

def threshold (V : Type) [Fintype V] (k : ℕ) : ℚ :=
  Augmentation.phaseDelta (Fintype.card V) k

def stepBudget (V : Type) [Fintype V] (k : ℕ) : ℕ :=
  LongEdge.longEdgeBudget V (threshold V k)

def fuel (V : Type) [Fintype V] (D k : ℕ) : ℕ :=
  contractionFuel (threshold V k) (Witness.phaseCountBits (Fintype.card V) D k)

def queryBudget (V : Type) [Fintype V] (D k : ℕ) : ℕ :=
  fuel V D k * stepBudget V k

inductive Outcome where
  | success
  | refuted
  | pending
  | invalid
  deriving DecidableEq

structure Result (V : Type) where
  state : State V
  outcome : Outcome

def step (A : CoreData V) (s t : V) (f k : ℕ) (P : State V) :
    DTree (Finset V) ℝ (Result V) (stepBudget V k) :=
  if witnesses A s t f k P = ∅ then DTree.pure ⟨P, .success⟩
  else
    (LongEdge.deletionLongEdge (P.graph A) (potential A s t f k P) (threshold V k)).map
      fun answer => match answer with
      | none => ⟨P, .refuted⟩
      | some (u, v) => match learn A P u v with
        | none => ⟨P, .invalid⟩
        | some Q => ⟨Q, .pending⟩

/-- Every invocation consumes a fixed public slot, even for malformed answers.
The zero-fuel branch still performs the free witness-emptiness test. -/
def run (A : CoreData V) (s t : V) (f k : ℕ) : (slots : ℕ) → State V →
    DTree (Finset V) ℝ (Result V) (slots * stepBudget V k)
  | 0, P => DTree.pure ⟨P, if witnesses A s t f k P = ∅ then .success else .pending⟩
  | slots + 1, P =>
      ((step A s t f k P).bind fun r =>
        match r.outcome with
        | .pending => run A s t f k slots r.state
        | _ => DTree.pure r).cast (by ring)

def program (A : CoreData V) (s t : V) (D f k : ℕ) (P : State V) :
    DTree (Finset V) ℝ (Result V) (queryBudget V D k) :=
  run A s t f k (fuel V D k) P

theorem program_cost (A : CoreData V) (s t : V) (D f k : ℕ) (P : State V)
    (read : Finset V → ℝ) : (program A s t D f k P).cost read ≤ queryBudget V D k :=
  DTree.cost_le _ _

def Lower (A : CoreData V) (P : State V) (s t : V) (f k : ℕ) : Prop :=
  (f : ℝ) - (k : ℝ) ≤ Augmentation.terminalValue (P.graph A) s t

theorem lower_mono {A : CoreData V} {P Q : State V} {s t : V} (hst : s ≠ t)
    {f k : ℕ} (h : Lower A P s t f k) (hPQ : (P.graph A).IsSubgraph (Q.graph A)) :
    Lower A Q s t f k := h.trans (Augmentation.terminalValue_mono hst hPQ)

theorem lower_cut {A : CoreData V} {P : State V} {s t : V} (hst : s ≠ t)
    {f k : ℕ} (hkf : k ≤ f) (h : Lower A P s t f k)
    {S : Finset V} (ht : t ∈ S) (hs : s ∉ S) :
    ((f - k : ℕ) : ℝ) ≤ (P.graph A).cut S := by
  have hc := Augmentation.terminalValue_le_cut (P.graph A) hst
    (mem_compl.mpr hs) (show t ∉ Sᶜ by simpa using ht)
  rw [(P.graph A).cut_compl] at hc
  rw [Nat.cast_sub hkf]
  exact h.trans hc

theorem witnesses_card_bound {G : WeightedGraph V} {D : ℕ} {A : CoreData V}
    (hA : CoreSpec G D A) {P : State V} (hP : Invariant G A P)
    {s t : V} (hst : s ≠ t) {f k : ℕ} (hD : 2 ≤ D)
    (hk : 1 ≤ k) (hkf : k ≤ f) (hfn : f ≤ Fintype.card V - 1)
    (hlower : Lower A P s t f k) :
    (witnesses A s t f k P).card ≤ 2 ^ Witness.phaseCountBits (Fintype.card V) D k :=
  Witness.phase_canonicalWitnesses_card_le_two_pow A.C A.K A.J P.L hst A.J_unit
    hA.J_supported hP.supported hP.seed_le hP.unit hD hk hkf hfn hA.min_degree
    (fun _ ht hs => lower_cut hst hkf hlower ht hs)

theorem empty_success {G : WeightedGraph V} {A : CoreData V} {P : State V}
    (hP : Invariant G A P) {s t : V} (hst : s ≠ t) {f k : ℕ}
    (hk : 1 ≤ k) (hkf : k ≤ f) (hfn : f ≤ Fintype.card V - 1)
    (he : witnesses A s t f k P = ∅) :
    ((f - k / 2 : ℕ) : ℝ) ≤ Augmentation.terminalValue (P.graph A) s t := by
  have hb : f - k / 2 - 1 ≤ Fintype.card V - 1 := by omega
  have hcut := (Witness.canonicalWitnesses_empty_iff A.C A.K P.L hst hP.unit hb
    hP.supported).mp he
  have hshore := Augmentation.terminalShore_spec (P.graph A) hst
  have h := hcut (Augmentation.terminalShore (P.graph A) s t)ᶜ
    (mem_compl.mpr hshore.2.1) (show s ∉ (Augmentation.terminalShore (P.graph A) s t)ᶜ by
      simpa using hshore.1)
  have heq : f - k / 2 - 1 + 1 = f - k / 2 := by omega
  simpa only [heq, State.graph, WeightedGraph.cut_compl, Augmentation.terminalValue] using h

/-- Absence is a refutation, proved without a feasibility promise. -/
theorem search_refutes {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {A : CoreData V} {P : State V} (hP : Invariant G A P)
    {s t : V} (hst : s ≠ t) {f k : ℕ}
    (hk : 1 ≤ k) (hkf : k ≤ f) (hfn : f ≤ Fintype.card V - 1)
    (hlower : Lower A P s t f k) (hne : (witnesses A s t f k P).Nonempty)
    (he : (LongEdge.deletionLongEdge (P.graph A) (potential A s t f k P)
      (threshold V k)).eval G.cut = none) : Augmentation.terminalValue G s t < f := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hδ : 0 < threshold V k := Augmentation.phaseDelta_pos hn hk
  have hφ (v : V) : 0 ≤ potential A s t f k P v ∧ potential A s t f k P v ≤ 1 :=
    ⟨Witness.potential_nonneg _ _ _ _, Witness.potential_le_one _ _ _ _⟩
  have hsearch := LongEdge.deletionLongEdge_correct G (P.graph A) hP.subgraph
    (potential A s t f k P) hδ hφ
  rw [he] at hsearch
  by_contra hnot
  obtain ⟨u, v, hactual, hzero, hlong⟩ := Augmentation.exists_long_unknown_edge
    A.C A.K P.L G hst hP.unit hG hP.subgraph hP.supported hk hkf hfn hlower
    (not_lt.mp hnot) hne
  have hpos : 0 < (G.subtract (P.graph A)).w u v := by
    change 0 < max 0 (G.w u v - (A.K.add P.L).w u v)
    rw [hactual, hzero]
    norm_num
  exact (not_lt_of_ge hlong) (hsearch u v hpos)

theorem learn_contracts {A : CoreData V} {P Q : State V} {s t : V} (hst : s ≠ t)
    {f k : ℕ} (hk : 1 ≤ k) (hkf : k ≤ f) (hfn : f ≤ Fintype.card V - 1)
    (hunit : AllPairsAudit.Unweighted (P.graph A)) (hlower : Lower A P s t f k)
    (hne : (witnesses A s t f k P).Nonempty) {u v : V}
    (hlearn : learn A P u v = some Q)
    (hlen : threshold V k / 2 ≤ |potential A s t f k P u - potential A s t f k P v|) :
    ((witnesses A s t f k Q).card : ℚ) ≤
      (1 - threshold V k / 4) * (witnesses A s t f k P).card := by
  obtain ⟨e, he, hg, hQ⟩ := learn_success hlearn
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hpossible : ∀ S ∈ canonicalFamily A.C A.K s t, f ≤ (Witness.possiblePairs S).card := by
    intro S hS
    obtain ⟨ht, hs⟩ := canonicalFamily_terminal A.C A.K hst hS
    exact hfn.trans (Witness.possiblePairs_card_ge ht hs)
  have hknown : ∀ S ∈ canonicalFamily A.C A.K s t,
      f - k ≤ (Witness.knownPairs (P.graph A) S).card := by
    intro S hS
    obtain ⟨ht, hs⟩ := canonicalFamily_terminal A.C A.K hst hS
    have hc := lower_cut hst hkf hlower ht hs
    rw [← Witness.knownPairs_card_eq_cut hunit] at hc
    exact_mod_cast hc
  have hz : (P.graph A).w e.val.1 e.val.2 = 0 := by simpa only [he] using hg.2.2.2
  have hl : threshold V k / 2 ≤
      |potential A s t f k P e.val.1 - potential A s t f k P e.val.2| := by
    simpa only [he] using hlen
  have hc := Witness.phase_witness_contraction (canonicalFamily A.C A.K s t)
    (P.graph A) e hk hkf hpossible hknown hz hne
    (Augmentation.phaseDelta_pos hn hk).le hl
  rw [hQ]
  change ((Witness.paddedWitnesses (canonicalFamily A.C A.K s t)
      ((P.insert e).graph A) (f - k / 2 - 1)).card : ℚ) ≤ _
  rw [State.graph_insert]
  exact hc

/-- The one-step alternatives concern the actual tree output. -/
structure StepSpec (G : WeightedGraph V) (A : CoreData V) (s t : V) (f k : ℕ)
    (P : State V) (r : Result V) : Prop where
  invariant : Invariant G A r.state
  grows : (P.graph A).IsSubgraph (r.state.graph A)
  result : match r.outcome with
    | .success => ((f - k / 2 : ℕ) : ℝ) ≤ Augmentation.terminalValue (r.state.graph A) s t
    | .refuted => Augmentation.terminalValue G s t < f
    | .pending => ((witnesses A s t f k r.state).card : ℚ) ≤
        (1 - threshold V k / 4) * (witnesses A s t f k P).card
    | .invalid => False

theorem step_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {D : ℕ} {A : CoreData V} (hA : CoreSpec G D A)
    {P : State V} (hP : Invariant G A P) {s t : V} (hst : s ≠ t)
    {f k : ℕ} (hk : 1 ≤ k) (hkf : k ≤ f) (hfn : f ≤ Fintype.card V - 1)
    (hlower : Lower A P s t f k) :
    StepSpec G A s t f k P ((step A s t f k P).eval G.cut) := by
  by_cases hw : witnesses A s t f k P = ∅
  · dsimp only [step, stepBudget]
    simp only [ite_eq_left hw, DTree.eval_pure]
    exact ⟨hP, fun _ _ => le_rfl, empty_success hP hst hk hkf hfn hw⟩
  · have hne : (witnesses A s t f k P).Nonempty := nonempty_iff_ne_empty.mpr hw
    have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
    have hδ : 0 < threshold V k := Augmentation.phaseDelta_pos hn hk
    have hφ (v : V) : 0 ≤ potential A s t f k P v ∧ potential A s t f k P v ≤ 1 :=
      ⟨Witness.potential_nonneg _ _ _ _, Witness.potential_le_one _ _ _ _⟩
    dsimp only [step, stepBudget]
    simp only [ite_eq_right hw, DTree.eval_map]
    cases he : (LongEdge.deletionLongEdge (P.graph A) (potential A s t f k P)
        (threshold V k)).eval G.cut with
    | none =>
        exact ⟨hP, fun _ _ => le_rfl, search_refutes hG hP hst hk hkf hfn hlower hne he⟩
    | some pair =>
        rcases pair with ⟨u, v⟩
        obtain ⟨hz, hactual, hlen⟩ := LongEdge.deletionLongEdge_found_unit G (P.graph A)
          hG hP.unit hP.subgraph (potential A s t f k P) hδ hφ he
        obtain ⟨Q, hQ, hi, hm⟩ := learn_actual hA hP hactual hz
        simp only [hQ]
        exact ⟨hi, hm, learn_contracts hst hk hkf hfn hP.unit hlower hne hQ hlen⟩

/-- A pending result is possible only after every allotted query step
succeeded, and records their actual cumulative witness contraction. -/
structure RunSpec (G : WeightedGraph V) (A : CoreData V) (s t : V) (f k slots : ℕ)
    (P : State V) (r : Result V) : Prop where
  invariant : Invariant G A r.state
  grows : (P.graph A).IsSubgraph (r.state.graph A)
  result : match r.outcome with
    | .success => ((f - k / 2 : ℕ) : ℝ) ≤ Augmentation.terminalValue (r.state.graph A) s t
    | .refuted => Augmentation.terminalValue G s t < f
    | .pending => (witnesses A s t f k r.state).Nonempty ∧
        ((witnesses A s t f k r.state).card : ℚ) ≤
          (1 - threshold V k / 4) ^ slots * (witnesses A s t f k P).card
    | .invalid => False

theorem run_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {D : ℕ} {A : CoreData V} (hA : CoreSpec G D A)
    {P : State V} (hP : Invariant G A P) {s t : V} (hst : s ≠ t)
    {f k : ℕ} (hk : 1 ≤ k) (hkf : k ≤ f) (hfn : f ≤ Fintype.card V - 1)
    (hlower : Lower A P s t f k) (slots : ℕ) :
    RunSpec G A s t f k slots P ((run A s t f k slots P).eval G.cut) := by
  induction slots generalizing P with
  | zero =>
      by_cases hw : witnesses A s t f k P = ∅
      · simp only [run, DTree.eval_pure, ite_eq_left hw]
        exact ⟨hP, fun _ _ => le_rfl, empty_success hP hst hk hkf hfn hw⟩
      · simp only [run, DTree.eval_pure, ite_eq_right hw]
        refine ⟨hP, fun _ _ => le_rfl, nonempty_iff_ne_empty.mpr hw, ?_⟩
        simp only [pow_zero, one_mul, le_refl]
  | succ slots ih =>
      let r := (step A s t f k P).eval G.cut
      have hs : StepSpec G A s t f k P r := step_correct hG hA hP hst hk hkf hfn hlower
      have hl : Lower A r.state s t f k := lower_mono hst hlower hs.grows
      rw [run, DTree.eval_cast, DTree.eval_bind]
      change RunSpec G A s t f k (slots + 1) P
        ((match r.outcome with
          | .pending => run A s t f k slots r.state
          | _ => DTree.pure r).eval G.cut)
      cases ho : r.outcome with
      | success =>
          rw [DTree.eval_pure]
          exact ⟨hs.invariant, hs.grows, by simpa only [ho] using hs.result⟩
      | refuted =>
          rw [DTree.eval_pure]
          exact ⟨hs.invariant, hs.grows, by simpa only [ho] using hs.result⟩
      | invalid =>
          exact False.elim (by simpa only [ho] using hs.result)
      | pending =>
          have hi := ih hs.invariant hl
          refine ⟨hi.invariant, fun u v => (hs.grows u v).trans (hi.grows u v), ?_⟩
          cases hf : ((run A s t f k slots r.state).eval G.cut).outcome with
          | success => simpa only [hf] using hi.result
          | refuted => simpa only [hf] using hi.result
          | invalid => simpa only [hf] using hi.result
          | pending =>
              have hi' : (witnesses A s t f k ((run A s t f k slots r.state).eval G.cut).state).Nonempty ∧
                  ((witnesses A s t f k ((run A s t f k slots r.state).eval G.cut).state).card : ℚ) ≤
                    (1 - threshold V k / 4) ^ slots * (witnesses A s t f k r.state).card := by
                simpa only [hf] using hi.result
              have hs' : ((witnesses A s t f k r.state).card : ℚ) ≤
                  (1 - threshold V k / 4) * (witnesses A s t f k P).card := by
                simpa only [ho] using hs.result
              have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
              have hd : threshold V k ≤ 1 / 2 :=
                Augmentation.phaseDelta_le_half hn hk (by omega)
              have hbase : 0 ≤ 1 - threshold V k / 4 := by linarith
              refine ⟨hi'.1, hi'.2.trans ?_⟩
              calc
                (1 - threshold V k / 4) ^ slots * (witnesses A s t f k r.state).card ≤
                    (1 - threshold V k / 4) ^ slots *
                      ((1 - threshold V k / 4) * (witnesses A s t f k P).card) :=
                  mul_le_mul_of_nonneg_left hs' (pow_nonneg hbase _)
                _ = _ := by rw [pow_succ]; ring

/-- Honest execution either improves the actual learned lower bound or
refutes the target. There is no target-feasibility or assumed phase premise. -/
structure ProgramSpec (G : WeightedGraph V) (A : CoreData V) (s t : V) (f k : ℕ)
    (P : State V) (r : Result V) : Prop where
  invariant : Invariant G A r.state
  grows : (P.graph A).IsSubgraph (r.state.graph A)
  result : match r.outcome with
    | .success => ((f - k / 2 : ℕ) : ℝ) ≤ Augmentation.terminalValue (r.state.graph A) s t
    | .refuted => Augmentation.terminalValue G s t < f
    | _ => False

theorem program_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {D : ℕ} {A : CoreData V} (hA : CoreSpec G D A)
    {P : State V} (hP : Invariant G A P) {s t : V} (hst : s ≠ t)
    {f k : ℕ} (hD : 2 ≤ D) (hk : 1 ≤ k) (hkf : k ≤ f)
    (hfn : f ≤ Fintype.card V - 1) (hlower : Lower A P s t f k) :
    ProgramSpec G A s t f k P ((program A s t D f k P).eval G.cut) := by
  have hr := run_correct hG hA hP hst hk hkf hfn hlower (fuel V D k)
  change RunSpec G A s t f k (fuel V D k) P ((program A s t D f k P).eval G.cut) at hr
  refine ⟨hr.invariant, hr.grows, ?_⟩
  cases ho : ((program A s t D f k P).eval G.cut).outcome with
  | success => simpa only [ho] using hr.result
  | refuted => simpa only [ho] using hr.result
  | invalid => simpa only [ho] using hr.result
  | pending =>
      have hp : (witnesses A s t f k ((program A s t D f k P).eval G.cut).state).Nonempty ∧
          ((witnesses A s t f k ((program A s t D f k P).eval G.cut).state).card : ℚ) ≤
            (1 - threshold V k / 4) ^ fuel V D k * (witnesses A s t f k P).card := by
        simpa only [ho] using hr.result
      have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
      have hd : 0 < threshold V k := Augmentation.phaseDelta_pos hn hk
      have hd4 : threshold V k ≤ 4 :=
        (Augmentation.phaseDelta_le_half hn hk (by omega)).trans (by norm_num)
      have hcount := witnesses_card_bound hA hP hst hD hk hkf hfn hlower
      have hz := contracted_card_eq_zero hd hd4
        (Witness.phaseCountBits (Fintype.card V) D k) (witnesses A s t f k P).card
        (witnesses A s t f k ((program A s t D f k P).eval G.cut).state).card hcount hp.2
      have hpos := card_pos.mpr hp.1
      omega

end
end CutQueryComplexity.CanonicalST.Phase

#print axioms CutQueryComplexity.CanonicalST.Phase.program_cost
#print axioms CutQueryComplexity.CanonicalST.Phase.witnesses_card_bound
#print axioms CutQueryComplexity.CanonicalST.Phase.search_refutes
#print axioms CutQueryComplexity.CanonicalST.Phase.learn_contracts
#print axioms CutQueryComplexity.CanonicalST.Phase.step_correct
#print axioms CutQueryComplexity.CanonicalST.Phase.run_correct
#print axioms CutQueryComplexity.CanonicalST.Phase.program_correct
