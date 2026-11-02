import CutQueryComplexity.CanonicalST.Phase.Run

/-!
# Geometric deficit reduction and public target decisions

Each successful phase halves the public deficit. Learned edges are retained
when a target is refuted as well as when it succeeds. The phase interfaces
used here are proved operational specifications, not input promises of
target feasibility.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST.Decision

open Finset WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def stagesBudget (V : Type) [Fintype V] (D : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | rounds + 1, k =>
      if k = 0 then 0 else Phase.queryBudget V D k + stagesBudget V D rounds (k / 2)

def stages (A : CoreData V) (s t : V) (D f : ℕ) :
    (rounds k : ℕ) → Phase.State V →
      DTree (Finset V) ℝ (Phase.Result V) (stagesBudget V D rounds k)
  | 0, k, P => DTree.pure ⟨P, if k = 0 then .success else .pending⟩
  | rounds + 1, k, P =>
      if hk : k = 0 then DTree.pure ⟨P, .success⟩
      else
        ((Phase.program A s t D f k P).bind fun r =>
          match r.outcome with
          | .success => stages A s t D f rounds (k / 2) r.state
          | _ => DTree.pure r).cast (by simp only [stagesBudget, ite_eq_right hk])

def rounds (V : Type) [Fintype V] : ℕ := Nat.clog 2 (Fintype.card V)

def queryBudget (V : Type) [Fintype V] (D f : ℕ) : ℕ :=
  stagesBudget V D (rounds V) f

def program (A : CoreData V) (s t : V) (D f : ℕ) (P : Phase.State V) :
    DTree (Finset V) ℝ (Phase.Result V) (queryBudget V D f) :=
  stages A s t D f (rounds V) f P

theorem program_cost (A : CoreData V) (s t : V) (D f : ℕ) (P : Phase.State V)
    (read : Finset V → ℝ) : (program A s t D f P).cost read ≤ queryBudget V D f :=
  DTree.cost_le _ _

structure Spec (G : WeightedGraph V) (A : CoreData V) (s t : V) (f : ℕ)
    (P : Phase.State V) (r : Phase.Result V) : Prop where
  invariant : Phase.Invariant G A r.state
  grows : (P.graph A).IsSubgraph (r.state.graph A)
  result : match r.outcome with
    | .success => (f : ℝ) ≤ Augmentation.terminalValue (r.state.graph A) s t
    | .refuted => Augmentation.terminalValue G s t < f
    | _ => False

theorem stages_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {D : ℕ} {A : CoreData V} (hA : CoreSpec G D A) (hD : 2 ≤ D)
    {P : Phase.State V} (hP : Phase.Invariant G A P) {s t : V} (hst : s ≠ t)
    {f k : ℕ} (hkf : k ≤ f) (hfn : f ≤ Fintype.card V - 1)
    (hlower : Phase.Lower A P s t f k) (r : ℕ) (hkr : k < 2 ^ r) :
    Spec G A s t f P ((stages A s t D f r k P).eval G.cut) := by
  induction r generalizing P k with
  | zero =>
      have hk : k = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using hkr
      subst k
      simp only [stages, DTree.eval_pure, ↓reduceIte]
      refine ⟨hP, fun _ _ => le_rfl, ?_⟩
      simpa only [Phase.Lower, Nat.cast_zero, sub_zero] using hlower
  | succ r ih =>
      by_cases hk : k = 0
      · subst k
        simp only [stages, ↓reduceDIte, DTree.eval_pure]
        refine ⟨hP, fun _ _ => le_rfl, ?_⟩
        simpa only [Phase.Lower, Nat.cast_zero, sub_zero] using hlower
      · have hkpos : 1 ≤ k := by omega
        have hhalf : k / 2 ≤ f := (Nat.div_le_self _ _).trans hkf
        have hhr : k / 2 < 2 ^ r := by
          rw [pow_succ] at hkr
          omega
        let out := (Phase.program A s t D f k P).eval G.cut
        have hp : Phase.ProgramSpec G A s t f k P out :=
          Phase.program_correct hG hA hP hst hD hkpos hkf hfn hlower
        simp only [stages, dite_eq_right hk, DTree.eval_cast, DTree.eval_bind]
        change Spec G A s t f P
          ((match out.outcome with
            | .success => stages A s t D f r (k / 2) out.state
            | _ => DTree.pure out).eval G.cut)
        cases ho : out.outcome with
        | success =>
            have hl : Phase.Lower A out.state s t f (k / 2) := by
              have h : ((f - k / 2 : ℕ) : ℝ) ≤
                  Augmentation.terminalValue (out.state.graph A) s t := by
                simpa only [ho] using hp.result
              simpa only [Phase.Lower, Nat.cast_sub hhalf] using h
            have hi := ih hp.invariant hhalf hl hhr
            exact ⟨hi.invariant, fun u v => (hp.grows u v).trans (hi.grows u v), hi.result⟩
        | refuted =>
            rw [DTree.eval_pure]
            exact ⟨hp.invariant, hp.grows, by simpa only [ho] using hp.result⟩
        | pending => exact False.elim (by simpa only [ho] using hp.result)
        | invalid => exact False.elim (by simpa only [ho] using hp.result)

theorem program_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {D : ℕ} {A : CoreData V} (hA : CoreSpec G D A) (hD : 2 ≤ D)
    {P : Phase.State V} (hP : Phase.Invariant G A P) {s t : V} (hst : s ≠ t)
    {f : ℕ} (hfn : f ≤ Fintype.card V - 1) :
    Spec G A s t f P ((program A s t D f P).eval G.cut) := by
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hf : f < Fintype.card V := by omega
  have hpow : f < 2 ^ rounds V := hf.trans_le (Nat.le_pow_clog (by decide) _)
  exact stages_correct hG hA hD hP hst le_rfl hfn
    (by simpa only [Phase.Lower, sub_self] using Augmentation.terminalValue_nonneg (P.graph A) s t)
    (rounds V) hpow

/-- A public maximum, not a sum over all targets: the binary search pays for
one decision at each round. -/
def uniformBudget (V : Type) [Fintype V] (D : ℕ) : ℕ :=
  (range (Fintype.card V)).sup (queryBudget V D)

theorem queryBudget_le_uniform {f : ℕ} (hf : f < Fintype.card V) (D : ℕ) :
    queryBudget V D f ≤ uniformBudget V D := Finset.le_sup (f := queryBudget V D) (mem_range.mpr hf)

structure SearchResult (V : Type) where
  state : Phase.State V
  value : ℕ

/-- Free arithmetic and earlier answers choose the midpoint. Invalid branches
abort; they cannot increase the fixed uniform budget of the next decision. -/
def search (A : CoreData V) (s t : V) (D : ℕ) :
    (depth lo hi : ℕ) → Phase.State V →
      DTree (Finset V) ℝ (Option (SearchResult V)) (depth * uniformBudget V D)
  | 0, lo, hi, P => DTree.pure (if hi ≤ lo + 1 then some ⟨P, lo⟩ else none)
  | depth + 1, lo, hi, P =>
      if hi ≤ lo + 1 then DTree.pure (some ⟨P, lo⟩)
      else if hm : (lo + hi) / 2 < Fintype.card V then
        (((program A s t D ((lo + hi) / 2) P).weaken (queryBudget_le_uniform hm D)).bind
          fun r => match r.outcome with
          | .success => search A s t D depth ((lo + hi) / 2) hi r.state
          | .refuted => search A s t D depth lo ((lo + hi) / 2) r.state
          | _ => DTree.pure none).cast (by ring)
      else DTree.pure none

def searchBudget (V : Type) [Fintype V] (D : ℕ) : ℕ := rounds V * uniformBudget V D

def searchProgram (A : CoreData V) (s t : V) (D : ℕ) (P : Phase.State V) :
    DTree (Finset V) ℝ (Option (SearchResult V)) (searchBudget V D) :=
  search A s t D (rounds V) 0 (Fintype.card V) P

theorem searchProgram_cost (A : CoreData V) (s t : V) (D : ℕ) (P : Phase.State V)
    (read : Finset V → ℝ) : (searchProgram A s t D P).cost read ≤ searchBudget V D :=
  DTree.cost_le _ _

structure SearchSpec (G : WeightedGraph V) (A : CoreData V) (s t : V)
    (P : Phase.State V) (r : SearchResult V) : Prop where
  invariant : Phase.Invariant G A r.state
  grows : (P.graph A).IsSubgraph (r.state.graph A)
  value_eq : (r.value : ℝ) = Augmentation.terminalValue G s t
  learned_eq : Augmentation.terminalValue (r.state.graph A) s t =
    Augmentation.terminalValue G s t

private theorem closed_interval {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {A : CoreData V} {P : Phase.State V} (hP : Phase.Invariant G A P)
    {s t : V} (hst : s ≠ t) {lo hi : ℕ}
    (hlower : (lo : ℝ) ≤ Augmentation.terminalValue (P.graph A) s t)
    (hupper : Augmentation.terminalValue G s t < hi) (hclose : hi ≤ lo + 1) :
    SearchSpec G A s t P ⟨P, lo⟩ := by
  have hmono := Augmentation.terminalValue_mono hst hP.subgraph
  have hloG : (lo : ℝ) ≤ Augmentation.terminalValue G s t := hlower.trans hmono
  obtain ⟨z, hz⟩ := Augmentation.terminalValue_integer hG s t
  have hloZ : (lo : ℤ) ≤ z := by rw [hz] at hloG; exact_mod_cast hloG
  have hhiZ : z < (hi : ℤ) := by rw [hz] at hupper; exact_mod_cast hupper
  have hcZ : (hi : ℤ) ≤ (lo : ℤ) + 1 := by exact_mod_cast hclose
  have heZ : z = (lo : ℤ) := by omega
  have he : (lo : ℝ) = Augmentation.terminalValue G s t := by simp [hz, heZ]
  refine ⟨hP, fun _ _ => le_rfl, he, le_antisymm hmono ?_⟩
  simpa only [← he] using hlower

private theorem weakened_eval {I A O : Type} {q r : ℕ} (T : DTree I A O q)
    (h : q ≤ r) (read : I → A) : (T.weaken h).eval read = T.eval read := by
  simp only [DTree.eval, DTree.run_weaken]

theorem search_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {D : ℕ} {A : CoreData V} (hA : CoreSpec G D A) (hD : 2 ≤ D)
    {P : Phase.State V} (hP : Phase.Invariant G A P) {s t : V} (hst : s ≠ t)
    {lo hi : ℕ} (hlohi : lo < hi) (hhi : hi ≤ Fintype.card V)
    (hlower : (lo : ℝ) ≤ Augmentation.terminalValue (P.graph A) s t)
    (hupper : Augmentation.terminalValue G s t < hi)
    (depth : ℕ) (hwidth : hi - lo ≤ 2 ^ depth) :
    ∃ r, (search A s t D depth lo hi P).eval G.cut = some r ∧ SearchSpec G A s t P r := by
  induction depth generalizing P lo hi with
  | zero =>
      have hc : hi ≤ lo + 1 := by
        have hw : hi - lo ≤ 1 := by simpa only [pow_zero] using hwidth
        omega
      refine ⟨⟨P, lo⟩, ?_, closed_interval hG hP hst hlower hupper hc⟩
      simp only [search, DTree.eval_pure, ite_eq_left hc]
  | succ depth ih =>
      by_cases hc : hi ≤ lo + 1
      · refine ⟨⟨P, lo⟩, ?_, closed_interval hG hP hst hlower hupper hc⟩
        simp only [search, ite_eq_left hc, DTree.eval_pure]
      · let mid := (lo + hi) / 2
        have hlm : lo < mid := by dsimp [mid]; omega
        have hmh : mid < hi := by dsimp [mid]; omega
        have hmn : mid < Fintype.card V := hmh.trans_le hhi
        have hmf : mid ≤ Fintype.card V - 1 := by omega
        have hw₁ : hi - mid ≤ 2 ^ depth := by
          rw [pow_succ] at hwidth
          dsimp [mid]
          omega
        have hw₂ : mid - lo ≤ 2 ^ depth := by
          rw [pow_succ] at hwidth
          dsimp [mid]
          omega
        let out := (program A s t D mid P).eval G.cut
        have hd : Spec G A s t mid P out := program_correct hG hA hD hP hst hmf
        have he : (search A s t D (depth + 1) lo hi P).eval G.cut =
            (match out.outcome with
              | .success => (search A s t D depth mid hi out.state).eval G.cut
              | .refuted => (search A s t D depth lo mid out.state).eval G.cut
              | _ => none) := by
          have hguard : (lo + hi) / 2 < Fintype.card V := hmn
          simp only [search, ite_eq_right hc, dite_eq_left hguard, DTree.eval_cast,
            DTree.eval_bind, weakened_eval]
          change (match out.outcome with
            | .success => search A s t D depth mid hi out.state
            | .refuted => search A s t D depth lo mid out.state
            | _ => DTree.pure none).eval G.cut = _
          cases out.outcome <;> simp only [DTree.eval_pure]
        cases ho : out.outcome with
        | success =>
            have hlow : (mid : ℝ) ≤ Augmentation.terminalValue (out.state.graph A) s t := by
              simpa only [ho] using hd.result
            obtain ⟨r, hr, hspec⟩ := ih hd.invariant hmh hhi hlow hupper hw₁
            refine ⟨r, ?_, hspec.invariant,
              fun u v => (hd.grows u v).trans (hspec.grows u v), hspec.value_eq, hspec.learned_eq⟩
            rw [ho] at he
            exact he.trans hr
        | refuted =>
            have hupp : Augmentation.terminalValue G s t < mid := by
              simpa only [ho] using hd.result
            have hlow : (lo : ℝ) ≤ Augmentation.terminalValue (out.state.graph A) s t :=
              hlower.trans (Augmentation.terminalValue_mono hst hd.grows)
            obtain ⟨r, hr, hspec⟩ := ih hd.invariant hlm hmn.le hlow hupp hw₂
            refine ⟨r, ?_, hspec.invariant,
              fun u v => (hd.grows u v).trans (hspec.grows u v), hspec.value_eq, hspec.learned_eq⟩
            rw [ho] at he
            exact he.trans hr
        | pending => exact False.elim (by simpa only [ho] using hd.result)
        | invalid => exact False.elim (by simpa only [ho] using hd.result)

theorem searchProgram_correct {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G)
    {D : ℕ} {A : CoreData V} (hA : CoreSpec G D A) (hD : 2 ≤ D)
    {P : Phase.State V} (hP : Phase.Invariant G A P) {s t : V} (hst : s ≠ t)
    (hupper : Augmentation.terminalValue G s t < Fintype.card V) :
    ∃ r, (searchProgram A s t D P).eval G.cut = some r ∧ SearchSpec G A s t P r := by
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  exact search_correct hG hA hD hP hst hn le_rfl
    (by simpa using Augmentation.terminalValue_nonneg (P.graph A) s t) hupper
    (rounds V) (by simpa only [rounds, Nat.sub_zero] using Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card V))

end
end CutQueryComplexity.CanonicalST.Decision

#print axioms CutQueryComplexity.CanonicalST.Decision.program_cost
#print axioms CutQueryComplexity.CanonicalST.Decision.stages_correct
#print axioms CutQueryComplexity.CanonicalST.Decision.program_correct
#print axioms CutQueryComplexity.CanonicalST.Decision.searchProgram_cost
#print axioms CutQueryComplexity.CanonicalST.Decision.search_correct
#print axioms CutQueryComplexity.CanonicalST.Decision.searchProgram_correct
