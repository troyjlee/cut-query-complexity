import CutQueryComplexity.GHReduction.Randomized.Isolating
import CutQueryComplexity.GHReduction.RandomRepetition
import CutQueryComplexity.GHReduction.DependentRandomTable
import CutQueryComplexity.GHReduction.RealizedCosts
import CutQueryComplexity.Probability.Truncation

/-! # Plumbing for call trees

The analogues, for `CallTree`, of the randomized combinators the reduction uses:
`randomTable`, `dependentRandomTable`, `randomRepeat`, `truncate` and
`contract` (the twin of `contractProgram`). A mixture `RTree.mix (μ.map f)` is
`random μ f`, and a compiled deterministic piece `RTree.ofDeterministic
((Prog.toDTree p q).map g)` is `(compile Q p' q).map g`.

`idealRun G T` is the ideal run with its charged cost: one per cut query and
`Q k` per call. Its output marginal is `interpIdeal G T`, and every supported
cost is at most the budget. It is the analogue of `RTree.run`, with the same
composition laws, so realized-cost arguments carry over.

The comparison lemmas `interpIdeal_*_eq` are the bridges at each combinator: if
the components of a twin have the ideal laws of the old components, so does the
twin.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability

namespace CallTree

variable {V : Type} {Q : ℕ → ℕ} {O P : Type}

/-! ### Combinators -/

section Tables

variable {J : Type} [DecidableEq J] {q : ℕ}

/-- Twin of `randomTableAux`. -/
def randomTableAux (fallback : O) (f : J → CallTree V Q O q) :
    (L : List J) → CallTree V Q (J → O) (L.length * q)
  | [] => up (Nat.zero_le _) (pure (PMF.pure (fun _ => fallback)))
  | j :: L => ((f j).bind (fun value =>
      (randomTableAux fallback f L).map (fun output => Function.update output j value))).cast
        (by simp only [List.length_cons, Nat.succ_mul]; omega)

/-- Twin of `randomTable`. -/
def randomTable [Fintype J] (fallback : O) (f : J → CallTree V Q O q) :
    CallTree V Q (J → O) (Fintype.card J * q) :=
  (randomTableAux fallback f (Finset.univ : Finset J).toList).cast (by simp)

variable {D : J → Type}

/-- Twin of `dependentRandomTableAux`. -/
def dependentRandomTableAux (fallback : (j : J) → D j) (f : (j : J) → CallTree V Q (D j) q) :
    (L : List J) → CallTree V Q ((j : J) → D j) (L.length * q)
  | [] => up (Nat.zero_le _) (pure (PMF.pure fallback))
  | j :: L => ((f j).bind (fun value =>
      (dependentRandomTableAux fallback f L).map (fun output => Function.update output j value))).cast
        (by simp only [List.length_cons, Nat.succ_mul]; omega)

/-- Twin of `dependentRandomTable`. -/
def dependentRandomTable [Fintype J] (fallback : (j : J) → D j)
    (f : (j : J) → CallTree V Q (D j) q) : CallTree V Q ((j : J) → D j) (Fintype.card J * q) :=
  (dependentRandomTableAux fallback f (Finset.univ : Finset J).toList).cast (by simp)

end Tables

/-- Twin of `randomRepeat`. -/
def randomRepeat {q : ℕ} (T : CallTree V Q O q) : (h : ℕ) → CallTree V Q (List O) (h * q)
  | 0 => up (Nat.zero_le _) (pure (PMF.pure []))
  | h + 1 => (T.bind (fun output => (randomRepeat T h).map (List.cons output))).cast
      (by rw [Nat.succ_mul, Nat.add_comm])

/-- Stop when the charged budget `k` would be exceeded, reporting absence. -/
def truncate : {q : ℕ} → CallTree V Q O q → (k : ℕ) → CallTree V Q (Option O) k
  | _, ret o, k => up (Nat.zero_le k) (ret (some o))
  | _, query _ _, 0 => ret none
  | _, query S next, k + 1 => query S (fun a => truncate (next a) k)
  | _, call c π s t hst next, k =>
      if h : Q c ≤ k then
        up (by omega) (call c π s t hst (fun S => truncate (next S) (k - Q c)))
      else up (Nat.zero_le k) (ret none)
  | _, random μ next, k => random μ (fun i => truncate (next i) k)
  | _, up _ T, k => truncate T k

variable [Fintype V] [DecidableEq V]

/-- Twin of `contractProgram`: pull every query and call back along a public map. -/
def contract {B : Type} [Fintype B] [DecidableEq B] (f : V → B) :
    {q : ℕ} → CallTree B Q O q → CallTree V Q O q
  | _, ret o => ret o
  | _, query S next => query (pull f S) (fun a => contract f (next a))
  | _, call k π s t hst next => call k (fun v => π (f v)) s t hst (fun S => contract f (next S))
  | _, random μ next => random μ (fun i => contract f (next i))
  | _, up h T => up h (contract f T)

/-! ### The ideal run with its charged cost -/

/-- The ideal run, keeping the charged cost. -/
def idealRun (G : WeightedGraph V) : {q : ℕ} → CallTree V Q O q → PMF (O × ℕ)
  | _, ret o => PMF.pure (o, 0)
  | _, query S next => (idealRun G (next (G.cut S))).map (fun p => (p.1, p.2 + 1))
  | _, call k π s t _ next =>
      (idealRun G (next (idealShore (G.contract π) s t))).map (fun p => (p.1, p.2 + Q k))
  | _, random μ next => μ.bind (fun i => idealRun G (next i))
  | _, up _ T => idealRun G T

theorem idealRun_fst (G : WeightedGraph V) {q : ℕ} (T : CallTree V Q O q) :
    (idealRun G T).map Prod.fst = interpIdeal G T := by
  induction T with
  | ret o => simp [idealRun, interpIdeal, PMF.pure_map]
  | query S next ih => simp only [idealRun, interpIdeal, PMF.map_comp, Function.comp_def, ← ih]
  | call k π s t hst next ih =>
      simp only [idealRun, interpIdeal, PMF.map_comp, Function.comp_def, ← ih]
  | random μ next ih => simp only [idealRun, interpIdeal, PMF.map_bind, ih]
  | up h T ih => simp only [idealRun, interpIdeal, ih]

theorem idealRun_cost_le (G : WeightedGraph V) {q : ℕ} (T : CallTree V Q O q) {p : O × ℕ}
    (hp : p ∈ (idealRun G T).support) : p.2 ≤ q := by
  induction T generalizing p with
  | ret o =>
      simp only [idealRun, PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp
      rfl
  | query S next ih =>
      simp only [idealRun, PMF.support_map, Set.mem_image] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      exact Nat.add_le_add_right (ih _ hp') 1
  | call k π s t hst next ih =>
      simp only [idealRun, PMF.support_map, Set.mem_image] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      exact Nat.add_le_add_right (ih _ hp') _
  | random μ next ih =>
      simp only [idealRun, PMF.mem_support_bind_iff] at hp
      obtain ⟨i, _, hp⟩ := hp
      exact ih i hp
  | up h T ih => exact (ih hp).trans h


/-! ### Composition laws of the ideal run -/

@[simp] theorem idealRun_up (G : WeightedGraph V) {q r : ℕ} (h : q ≤ r) (T : CallTree V Q O q) :
    idealRun G (up h T) = idealRun G T := rfl

@[simp] theorem idealRun_cast (G : WeightedGraph V) {q r : ℕ} (h : q = r) (T : CallTree V Q O q) :
    idealRun G (T.cast h) = idealRun G T := rfl

@[simp] theorem idealRun_weaken (G : WeightedGraph V) {q r : ℕ} (h : q ≤ r)
    (T : CallTree V Q O q) : idealRun G (T.weaken h) = idealRun G T := rfl

@[simp] theorem idealRun_random (G : WeightedGraph V) {q : ℕ} {ι : Type} (μ : PMF ι)
    (next : ι → CallTree V Q O q) :
    idealRun G (random μ next) = μ.bind (fun i => idealRun G (next i)) := rfl

@[simp] theorem idealRun_pure (G : WeightedGraph V) (μ : PMF O) :
    idealRun G (pure (V := V) (Q := Q) μ) = μ.map (fun o => (o, 0)) := by
  simp only [pure, idealRun]
  rfl

theorem idealRun_bind (G : WeightedGraph V) {r : ℕ} (f : O → CallTree V Q P r) {q : ℕ}
    (T : CallTree V Q O q) :
    idealRun G (T.bind f) = (idealRun G T).bind (fun p =>
      (idealRun G (f p.1)).map (fun t => (t.1, p.2 + t.2))) := by
  induction T with
  | ret o =>
      simp only [bind, idealRun, PMF.pure_bind, Nat.zero_add]
      exact (PMF.map_id _).symm
  | query S next ih =>
      simp only [bind, idealRun, ih, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      congr 1
      funext p
      congr 1
      funext t
      simp only [Prod.mk.injEq, true_and]
      omega
  | call k π s t hst next ih =>
      simp only [bind, idealRun, ih, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      congr 1
      funext p
      congr 1
      funext t
      simp only [Prod.mk.injEq, true_and]
      omega
  | random μ next ih => simp only [bind, idealRun, ih, PMF.bind_bind]
  | up h T ih => simp only [bind, idealRun, ih]

@[simp] theorem idealRun_map (G : WeightedGraph V) {q : ℕ} (f : O → P) (T : CallTree V Q O q) :
    idealRun G (T.map f) = (idealRun G T).map (fun p => (f p.1, p.2)) := by
  simp only [map, idealRun_cast, idealRun_bind, idealRun, PMF.pure_map, Nat.add_zero]
  rfl

@[simp] theorem idealRun_contract {B : Type} [Fintype B] [DecidableEq B] (G : WeightedGraph V)
    (f : V → B) {q : ℕ} (T : CallTree B Q O q) :
    idealRun G (contract f T) = idealRun (G.contract f) T := by
  induction T with
  | ret o => rfl
  | query S next ih => simp only [contract, idealRun, ih, cut_contract]
  | call k π s t hst next ih => simp only [contract, idealRun, ih, contract_contract]
  | random μ next ih => simp only [contract, idealRun, ih]
  | up h T ih => simp only [contract, idealRun, ih]

theorem idealRun_compile (G : WeightedGraph V) (p : CallProg V O) (q : ℕ)
    (h : CallProg.idealCost G Q p ≤ q) :
    idealRun G (CallProg.compile Q p q) =
      PMF.pure (some (CallProg.idealEval G p), CallProg.idealCost G Q p) := by
  induction p generalizing q with
  | pure a => simp [CallProg.compile, idealRun, CallProg.idealEval, CallProg.idealCost]
  | query S next ih =>
      cases q with
      | zero => simp [CallProg.idealCost] at h
      | succ q =>
          simp only [CallProg.compile, idealRun, CallProg.idealEval, CallProg.idealCost]
          rw [ih _ q (by simp only [CallProg.idealCost] at h; omega), PMF.pure_map]
  | call k π s t hst next ih =>
      have hk : Q k ≤ q := by simp only [CallProg.idealCost] at h; omega
      simp only [CallProg.compile, dite_eq_left hk, idealRun, CallProg.idealEval,
        CallProg.idealCost]
      rw [ih _ (q - Q k) (by simp only [CallProg.idealCost] at h; omega), PMF.pure_map]

/-- Exact coupling of the truncated tree with the charged cost of the ideal run. -/
theorem interpIdeal_truncate (G : WeightedGraph V) {q : ℕ} (T : CallTree V Q O q) (k : ℕ) :
    interpIdeal G (T.truncate k) =
      (idealRun G T).map (fun p => if p.2 ≤ k then some p.1 else none) := by
  induction T generalizing k with
  | ret o => simp [truncate, interpIdeal, idealRun, PMF.pure_map]
  | query S next ih =>
      cases k with
      | zero =>
          simp only [truncate, interpIdeal, idealRun, PMF.map_comp, Function.comp_def,
            Nat.add_one_le_iff, Nat.not_lt_zero, ite_false]
          exact (PMF.map_const _ none).symm
      | succ k =>
          simp only [truncate, interpIdeal, idealRun, PMF.map_comp, Function.comp_def, ih,
            Nat.add_le_add_iff_right]
  | call c π s t hst next ih =>
      by_cases hc : Q c ≤ k
      · simp only [truncate, dite_eq_left hc, interpIdeal, idealRun, PMF.map_comp,
          Function.comp_def, ih]
        congr 1
        funext p
        have : p.2 ≤ k - Q c ↔ p.2 + Q c ≤ k := by omega
        simp only [this]
      · simp only [truncate, dite_eq_right hc, interpIdeal, idealRun, PMF.map_comp,
          Function.comp_def]
        have : ∀ p : O × ℕ, ¬p.2 + Q c ≤ k := fun p => by omega
        simp only [this, ite_false]
        exact (PMF.map_const _ none).symm
  | random μ next ih => simp only [truncate, interpIdeal, idealRun, ih, PMF.map_bind]
  | up h T ih => simp only [truncate, idealRun, ih]

/-! ### Ideal laws of the combinators -/

@[simp] theorem interpIdeal_pure (G : WeightedGraph V) (μ : PMF O) :
    interpIdeal G (pure (V := V) (Q := Q) μ) = μ := by
  simp only [pure, interpIdeal]
  exact PMF.bind_pure μ

@[simp] theorem interpIdeal_up (G : WeightedGraph V) {q r : ℕ} (h : q ≤ r)
    (T : CallTree V Q O q) : interpIdeal G (up h T) = interpIdeal G T := rfl

@[simp] theorem interpIdeal_cast (G : WeightedGraph V) {q r : ℕ} (h : q = r)
    (T : CallTree V Q O q) : interpIdeal G (T.cast h) = interpIdeal G T := rfl

@[simp] theorem interpIdeal_weaken (G : WeightedGraph V) {q r : ℕ} (h : q ≤ r)
    (T : CallTree V Q O q) : interpIdeal G (T.weaken h) = interpIdeal G T := rfl

@[simp] theorem interpIdeal_random (G : WeightedGraph V) {q : ℕ} {ι : Type} (μ : PMF ι)
    (next : ι → CallTree V Q O q) :
    interpIdeal G (random μ next) = μ.bind (fun i => interpIdeal G (next i)) := rfl

@[simp] theorem interpIdeal_contract {B : Type} [Fintype B] [DecidableEq B]
    (G : WeightedGraph V) (f : V → B) {q : ℕ} (T : CallTree B Q O q) :
    interpIdeal G (contract f T) = interpIdeal (G.contract f) T := by
  rw [← idealRun_fst, ← idealRun_fst, idealRun_contract]

/-- A law that agrees on the support of the first step. -/
theorem bind_congr_support {α β : Type} (μ : PMF α) {f g : α → PMF β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.bind f = μ.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ μ.support
  · rw [h a ha]
  · have hz : μ a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp only [hz, zero_mul]

/-! ### Bridges at each combinator

Each lemma: if the components of a twin have the ideal laws of the old
components (on the support of earlier steps), so does the twin. -/

theorem bind_eq {q r q' r' : ℕ} {G : WeightedGraph V} {T : CallTree V Q O q}
    {T' : RTree (Finset V) ℝ O q'} {f : O → CallTree V Q P r} {f' : O → RTree (Finset V) ℝ P r'}
    (hT : interpIdeal G T = T'.eval G.cut)
    (hf : ∀ o ∈ (T'.eval G.cut).support, interpIdeal G (f o) = (f' o).eval G.cut) :
    interpIdeal G (T.bind f) = (T'.bind f').eval G.cut := by
  rw [interpIdeal_bind, RTree.eval_bind, hT]
  exact bind_congr_support _ hf

theorem map_eq {q q' : ℕ} {G : WeightedGraph V} {T : CallTree V Q O q}
    {T' : RTree (Finset V) ℝ O q'} (f : O → P) (hT : interpIdeal G T = T'.eval G.cut) :
    interpIdeal G (T.map f) = (T'.map f).eval G.cut := by
  rw [interpIdeal_map, RTree.eval_map, hT]

theorem random_eq {q q' : ℕ} {ι : Type} {G : WeightedGraph V} (μ : PMF ι)
    {next : ι → CallTree V Q O q} {next' : ι → RTree (Finset V) ℝ O q'}
    (h : ∀ i ∈ μ.support, interpIdeal G (next i) = (next' i).eval G.cut) :
    interpIdeal G (random μ next) = (RTree.mix (μ.map next')).eval G.cut := by
  rw [interpIdeal_random, RTree.eval_mix, PMF.bind_map]
  exact bind_congr_support _ h

theorem pure_eq {q : ℕ} (G : WeightedGraph V) (μ : PMF O) :
    interpIdeal G (pure (V := V) (Q := Q) μ) = (RTree.pure (q := q) μ).eval G.cut := by
  simp

theorem compile_eq {q q' : ℕ} {G : WeightedGraph V} {p : CallProg V O}
    {p' : Prog (Finset V) ℝ O} (hp : Prog.eval G.cut p' = CallProg.idealEval G p)
    (hcost : CallProg.idealCost G Q p ≤ q) (hcost' : Prog.cost G.cut p' ≤ q') :
    interpIdeal G (CallProg.compile Q p q) =
      (RTree.ofDeterministic (Prog.toDTree p' q')).eval G.cut := by
  rw [CallProg.interpIdeal_compile G Q p q hcost, RTree.eval_ofDeterministic,
    Prog.toDTree_eval _ _ _ hcost', hp]

theorem randomTableAux_eq {J : Type} [DecidableEq J] {q q' : ℕ} {G : WeightedGraph V}
    (fallback : O) {f : J → CallTree V Q O q} {f' : J → RTree (Finset V) ℝ O q'} (L : List J)
    (h : ∀ j ∈ L, interpIdeal G (f j) = (f' j).eval G.cut) :
    interpIdeal G (randomTableAux fallback f L) =
      (GHReduction.randomTableAux fallback f' L).eval G.cut := by
  induction L with
  | nil => simp [randomTableAux, GHReduction.randomTableAux]
  | cons j L ih =>
      simp only [randomTableAux, GHReduction.randomTableAux, interpIdeal_cast, RTree.eval_cast]
      exact bind_eq (h j List.mem_cons_self) (fun o _ =>
        map_eq _ (ih (fun k hk => h k (List.mem_cons_of_mem _ hk))))

theorem randomTable_eq {J : Type} [DecidableEq J] [Fintype J] {q q' : ℕ} {G : WeightedGraph V}
    (fallback : O) {f : J → CallTree V Q O q} {f' : J → RTree (Finset V) ℝ O q'}
    (h : ∀ j, interpIdeal G (f j) = (f' j).eval G.cut) :
    interpIdeal G (randomTable fallback f) = (GHReduction.randomTable fallback f').eval G.cut := by
  simp only [randomTable, GHReduction.randomTable, interpIdeal_cast, RTree.eval_cast]
  exact randomTableAux_eq fallback _ (fun j _ => h j)

theorem dependentRandomTableAux_eq {J : Type} [DecidableEq J] {D : J → Type} {q q' : ℕ}
    {G : WeightedGraph V} (fallback : (j : J) → D j) {f : (j : J) → CallTree V Q (D j) q}
    {f' : (j : J) → RTree (Finset V) ℝ (D j) q'} (L : List J)
    (h : ∀ j ∈ L, interpIdeal G (f j) = (f' j).eval G.cut) :
    interpIdeal G (dependentRandomTableAux fallback f L) =
      (GHReduction.dependentRandomTableAux fallback f' L).eval G.cut := by
  induction L with
  | nil => simp [dependentRandomTableAux, GHReduction.dependentRandomTableAux]
  | cons j L ih =>
      simp only [dependentRandomTableAux, GHReduction.dependentRandomTableAux, interpIdeal_cast,
        RTree.eval_cast]
      exact bind_eq (h j List.mem_cons_self) (fun o _ =>
        map_eq _ (ih (fun k hk => h k (List.mem_cons_of_mem _ hk))))

theorem dependentRandomTable_eq {J : Type} [DecidableEq J] [Fintype J] {D : J → Type}
    {q q' : ℕ} {G : WeightedGraph V} (fallback : (j : J) → D j)
    {f : (j : J) → CallTree V Q (D j) q} {f' : (j : J) → RTree (Finset V) ℝ (D j) q'}
    (h : ∀ j, interpIdeal G (f j) = (f' j).eval G.cut) :
    interpIdeal G (dependentRandomTable fallback f) =
      (GHReduction.dependentRandomTable fallback f').eval G.cut := by
  simp only [dependentRandomTable, GHReduction.dependentRandomTable, interpIdeal_cast,
    RTree.eval_cast]
  exact dependentRandomTableAux_eq fallback _ (fun j _ => h j)

theorem randomRepeat_eq {q q' : ℕ} {G : WeightedGraph V} {T : CallTree V Q O q}
    {T' : RTree (Finset V) ℝ O q'} (hT : interpIdeal G T = T'.eval G.cut) (h : ℕ) :
    interpIdeal G (randomRepeat T h) = (GHReduction.randomRepeat T' h).eval G.cut := by
  induction h with
  | zero => simp [randomRepeat, GHReduction.randomRepeat]
  | succ h ih =>
      simp only [randomRepeat, GHReduction.randomRepeat, interpIdeal_cast, RTree.eval_cast]
      exact bind_eq hT (fun o _ => map_eq _ ih)

theorem contract_eq {B : Type} [Fintype B] [DecidableEq B] {q q' : ℕ} {G : WeightedGraph V}
    (f : V → B) {T : CallTree B Q O q} {T' : RTree (Finset B) ℝ O q'}
    (hT : interpIdeal (G.contract f) T = T'.eval (G.contract f).cut) :
    interpIdeal G (contract f T) = (contractProgram f T').eval G.cut := by
  rw [interpIdeal_contract, contractProgram_eval, hT]

theorem map_congr_support {α β : Type} (μ : PMF α) {f g : α → β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.map f = μ.map g := by
  simp only [PMF.map]
  exact bind_congr_support _ (fun a ha => by rw [Function.comp_apply, Function.comp_apply, h a ha])

/-- At a truncation site, neither side truncates on a supported run. -/
theorem truncate_eq {q q' k k' : ℕ} {G : WeightedGraph V} {T : CallTree V Q O q}
    {T' : RTree (Finset V) ℝ O q'} (hT : interpIdeal G T = T'.eval G.cut)
    (hcost : ∀ p ∈ (idealRun G T).support, p.2 ≤ k)
    (hcost' : ∀ p ∈ (RTree.run G.cut T').support, p.2 ≤ k') :
    interpIdeal G (T.truncate k) = (T'.truncate k').eval G.cut := by
  rw [interpIdeal_truncate, RTree.eval_truncate,
    map_congr_support _ (fun p hp => ite_eq_left (hcost p hp)),
    map_congr_support _ (fun p hp => ite_eq_left (hcost' p hp))]
  have h1 : (idealRun G T).map (fun p => some p.1) = (interpIdeal G T).map some := by
    rw [← idealRun_fst, PMF.map_comp]
    rfl
  have h2 : (RTree.run G.cut T').map (fun p => some p.1) = (T'.eval G.cut).map some := by
    rw [RTree.eval, PMF.map_comp]
    rfl
  rw [h1, h2, hT]

/-! ### Realized charged costs

The analogues of `random_bind_cost`, `random_map_cost`, `randomTable_cost`,
`dependentRandomTable_cost` and `randomRepeat_cost`, for the ideal run. -/

theorem idealRun_bind_cost {q r : ℕ} (G : WeightedGraph V) (T : CallTree V Q O q)
    (f : O → CallTree V Q P r) (scale firstBudget nextBudget : ℕ)
    (hfirst : ∀ p ∈ (idealRun G T).support, scale * p.2 ≤ firstBudget)
    (hnext : ∀ p ∈ (idealRun G T).support,
      ∀ s ∈ (idealRun G (f p.1)).support, scale * s.2 ≤ nextBudget)
    {p : P × ℕ} (hp : p ∈ (idealRun G (T.bind f)).support) :
    scale * p.2 ≤ firstBudget + nextBudget := by
  rw [idealRun_bind] at hp
  obtain ⟨first, hf, hMapped⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  obtain ⟨next, hn, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hMapped
  rw [← heq, Nat.mul_add]
  exact Nat.add_le_add (hfirst first hf) (hnext first hf next hn)

theorem idealRun_map_cost {q : ℕ} (G : WeightedGraph V) (T : CallTree V Q O q) (f : O → P)
    (scale budget : ℕ) (hcost : ∀ p ∈ (idealRun G T).support, scale * p.2 ≤ budget)
    {p : P × ℕ} (hp : p ∈ (idealRun G (T.map f)).support) : scale * p.2 ≤ budget := by
  rw [idealRun_map] at hp
  obtain ⟨out, hout, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  rw [← heq]
  exact hcost out hout

theorem idealRun_output_support {q : ℕ} (G : WeightedGraph V) (T : CallTree V Q O q)
    {p : O × ℕ} (hp : p ∈ (idealRun G T).support) : p.1 ∈ (interpIdeal G T).support := by
  rw [← idealRun_fst]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨p, hp, rfl⟩

theorem idealRun_pure_cost (G : WeightedGraph V) (μ : PMF O) {p : O × ℕ}
    (hp : p ∈ (idealRun G (pure (V := V) (Q := Q) μ)).support) : p.2 = 0 := by
  rw [idealRun_pure] at hp
  obtain ⟨o, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  rfl

theorem randomTableAux_cost {J : Type} [DecidableEq J] {q : ℕ} (G : WeightedGraph V)
    (fallback : O) (f : J → CallTree V Q O q) (L : List J) (scale : ℕ) (budget : J → ℕ)
    (hf : ∀ j ∈ L, ∀ p ∈ (idealRun G (f j)).support, scale * p.2 ≤ budget j)
    {p : (J → O) × ℕ} (hp : p ∈ (idealRun G (randomTableAux fallback f L)).support) :
    scale * p.2 ≤ (L.map budget).sum := by
  induction L generalizing p with
  | nil =>
      simp only [randomTableAux, idealRun_up] at hp
      simp [idealRun_pure_cost G _ hp]
  | cons j L ih =>
      simp only [randomTableAux, idealRun_cast] at hp
      have h := idealRun_bind_cost G _ _ scale (budget j) ((L.map budget).sum)
        (hf j List.mem_cons_self)
        (fun _ _ s hs => idealRun_map_cost G _ _ scale _
          (fun t ht => ih (fun k hk => hf k (List.mem_cons_of_mem _ hk)) ht) hs) hp
      simpa only [List.map_cons, List.sum_cons] using h

theorem randomTable_cost {J : Type} [DecidableEq J] [Fintype J] {q : ℕ} (G : WeightedGraph V)
    (fallback : O) (f : J → CallTree V Q O q) (scale : ℕ) (budget : J → ℕ)
    (hf : ∀ j, ∀ p ∈ (idealRun G (f j)).support, scale * p.2 ≤ budget j)
    {p : (J → O) × ℕ} (hp : p ∈ (idealRun G (randomTable fallback f)).support) :
    scale * p.2 ≤ ∑ j, budget j := by
  have h := randomTableAux_cost G fallback f Finset.univ.toList scale budget
    (fun j _ => hf j) (by simpa only [randomTable, idealRun_cast] using hp)
  simpa only [Finset.sum_map_toList] using h

theorem dependentRandomTableAux_cost {J : Type} [DecidableEq J] {D : J → Type} {q : ℕ}
    (G : WeightedGraph V) (fallback : (j : J) → D j) (f : (j : J) → CallTree V Q (D j) q)
    (L : List J) (scale : ℕ) (budget : J → ℕ)
    (hf : ∀ j ∈ L, ∀ p ∈ (idealRun G (f j)).support, scale * p.2 ≤ budget j)
    {p : ((j : J) → D j) × ℕ}
    (hp : p ∈ (idealRun G (dependentRandomTableAux fallback f L)).support) :
    scale * p.2 ≤ (L.map budget).sum := by
  induction L generalizing p with
  | nil =>
      simp only [dependentRandomTableAux, idealRun_up] at hp
      simp [idealRun_pure_cost G _ hp]
  | cons j L ih =>
      simp only [dependentRandomTableAux, idealRun_cast] at hp
      have h := idealRun_bind_cost G _ _ scale (budget j) ((L.map budget).sum)
        (hf j List.mem_cons_self)
        (fun _ _ s hs => idealRun_map_cost G _ _ scale _
          (fun t ht => ih (fun k hk => hf k (List.mem_cons_of_mem _ hk)) ht) hs) hp
      simpa only [List.map_cons, List.sum_cons] using h

theorem dependentRandomTable_cost {J : Type} [DecidableEq J] [Fintype J] {D : J → Type} {q : ℕ}
    (G : WeightedGraph V) (fallback : (j : J) → D j) (f : (j : J) → CallTree V Q (D j) q)
    (scale : ℕ) (budget : J → ℕ)
    (hf : ∀ j, ∀ p ∈ (idealRun G (f j)).support, scale * p.2 ≤ budget j)
    {p : ((j : J) → D j) × ℕ}
    (hp : p ∈ (idealRun G (dependentRandomTable fallback f)).support) :
    scale * p.2 ≤ ∑ j, budget j := by
  have h := dependentRandomTableAux_cost G fallback f Finset.univ.toList scale budget
    (fun j _ => hf j) (by simpa only [dependentRandomTable, idealRun_cast] using hp)
  simpa only [Finset.sum_map_toList] using h

theorem randomRepeat_cost {q : ℕ} (G : WeightedGraph V) (T : CallTree V Q O q) (h : ℕ)
    (scale budget : ℕ) (hcost : ∀ p ∈ (idealRun G T).support, scale * p.2 ≤ budget)
    {p : List O × ℕ} (hp : p ∈ (idealRun G (randomRepeat T h)).support) :
    scale * p.2 ≤ h * budget := by
  induction h generalizing p with
  | zero =>
      simp only [randomRepeat, idealRun_up] at hp
      simp [idealRun_pure_cost G _ hp]
  | succ h ih =>
      simp only [randomRepeat, idealRun_cast] at hp
      have hb := idealRun_bind_cost G _ _ scale budget (h * budget) hcost
        (fun _ _ s hs => idealRun_map_cost G _ _ scale _ (fun t ht => ih ht) hs) hp
      simpa only [Nat.succ_mul, Nat.add_comm] using hb

end CallTree
end
end CutQueryComplexity.GHReduction.Randomized
