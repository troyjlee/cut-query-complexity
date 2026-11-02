import CutQueryComplexity.GHReduction.Randomized.CallTree
import CutQueryComplexity.GHReduction.Contractions

/-! # Meanings of a call tree

* `interpRand P`: the randomized program. Each call node runs the family's
  program `P k s t` afresh on the contracted oracle, so different calls use
  independent randomness. Its budget is the call tree's index, so every run on
  every oracle respects it (`interpRand_cost_le`).
* The deterministic meaning is `interpRand A.toRandom.program` for an exact
  `CanonicalSTFamily A`.
* `interpIdeal G`: the output law when every cut query is answered by `G.cut`
  and every call by the canonical shore of `G.contract π`. It is a proof device
  and is never run.

`eval_interpRand_of_exact` (G1): a family that never fails gives exactly the
ideal law. `mass_interpRand_le` (G2): a family that fails with probability at
most `δ` per call changes the probability of any event by at most `δ · q`. The
proof is an induction over the tree, so the calls may depend on earlier
answers and coins. Each call consumes at least one unit of the budget, so `q`
bounds the number of calls along every run.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal
open WeightedGraph Probability

/-- The canonical s-t shore, chosen semantically. Used only by the ideal meaning. -/
def idealShore {k : ℕ} (H : WeightedGraph (Fin k)) (s t : Fin k) : Finset (Fin k) :=
  if h : s = t then ∅ else Classical.choose (exists_canonicalSTCut H h)

theorem idealShore_spec {k : ℕ} (H : WeightedGraph (Fin k)) {s t : Fin k} (hst : s ≠ t) :
    IsCanonicalSTCut H s t (idealShore H s t) := by
  rw [idealShore, dite_eq_right hst]
  exact Classical.choose_spec (exists_canonicalSTCut H hst)

theorem eq_idealShore {k : ℕ} {H : WeightedGraph (Fin k)} {s t : Fin k} (hst : s ≠ t)
    {S : Finset (Fin k)} (hS : IsCanonicalSTCut H s t S) : S = idealShore H s t :=
  canonicalSTCut_unique H hS (idealShore_spec H hst)

/-- A law that gives no mass outside `a` is the point mass at `a`. -/
theorem eq_pure_of_mass_ne_eq_zero {α : Type*} (p : PMF α) (a : α)
    (h : mass p (fun x => x ≠ a) = 0) : p = PMF.pure a := by
  have hdisj := (p.toOuterMeasure_apply_eq_zero_iff {x | x ≠ a}).mp h
  have hsub : p.support ⊆ {a} := fun x hx => by
    by_contra hne
    exact Set.disjoint_left.mp hdisj hx hne
  have hsupp : p.support = {a} := by
    refine Set.Subset.antisymm hsub ?_
    obtain ⟨y, hy⟩ := p.support_nonempty
    have hya : y = a := hsub hy
    subst hya
    exact Set.singleton_subset_iff.mpr hy
  ext x
  by_cases hx : x = a
  · subst hx
    rw [(p.apply_eq_one_iff x).mpr hsupp, PMF.pure_apply_self]
  · rw [PMF.pure_apply_of_ne _ _ hx, (p.apply_eq_zero_iff x).mpr (by rw [hsupp]; exact hx)]

/-- An exact deterministic family never fails. -/
theorem _root_.CutQueryComplexity.GHReduction.CanonicalSTFamily.toRandom_failsAtMost_zero
    {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q) : A.toRandom.program.FailsAtMost M 0 := by
  intro k s t hst G hint hcap
  simp [CanonicalSTFamily.toRandom, RTree.eval_ofDeterministic, A.correct k s t hst G hint hcap]

variable {V : Type} [Fintype V] [DecidableEq V] {Q : ℕ → ℕ} {O P : Type}

/-- The family's promise on every contraction follows from the input promise. -/
theorem call_promise {M : ℕ} (G : WeightedGraph V) (hG : InputPromise M G) {k : ℕ}
    (π : V → Fin k) :
    (G.contract π).IsIntegral ∧ ∀ u v, (G.contract π).w u v ≤ M :=
  ⟨integral_contract G hG.1 π, (contract_capacity_bounds G π hG.2).1⟩

namespace CallTree

/-- The ideal output law. -/
def interpIdeal (G : WeightedGraph V) : {q : ℕ} → CallTree V Q O q → PMF O
  | _, ret o => PMF.pure o
  | _, query S next => interpIdeal G (next (G.cut S))
  | _, call _ π s t _ next => interpIdeal G (next (idealShore (G.contract π) s t))
  | _, random μ next => μ.bind (fun i => interpIdeal G (next i))
  | _, up _ T => interpIdeal G T

/-- One s-t call, compiled to cut queries on `V` through the public contraction. -/
def callProgram (P : STPrograms Q) {k : ℕ} (π : V → Fin k) (s t : Fin k) :
    RTree (Finset V) ℝ (Finset (Fin k)) (Q k) :=
  contractProgram π (P k s t)

/-- The randomized program. -/
def interpRand (P : STPrograms Q) : {q : ℕ} → CallTree V Q O q → RTree (Finset V) ℝ O q
  | _, ret o => RTree.pure (q := 0) (PMF.pure o)
  | _, query S next => RTree.query S (fun a => interpRand P (next a))
  | _, call _ π s t _ next =>
      ((callProgram P π s t).bind (fun S => interpRand P (next S))).cast (Nat.add_comm _ _)
  | _, random μ next => RTree.mix (μ.map (fun i => interpRand P (next i)))
  | _, up h T => (interpRand P T).weaken h

omit [DecidableEq V] in
/-- (G3) The budget is a cap on every run, on every oracle. -/
theorem interpRand_cost_le (P : STPrograms Q) {q : ℕ} (T : CallTree V Q O q)
    (read : Finset V → ℝ) {out : O × ℕ} (hout : out ∈ (RTree.run read (interpRand P T)).support) :
    out.2 ≤ q :=
  RTree.cost_le _ read hout

/-! ### Evaluation equations -/

theorem callProgram_eval (P : STPrograms Q) (G : WeightedGraph V) {k : ℕ} (π : V → Fin k)
    (s t : Fin k) :
    (callProgram P π s t).eval G.cut = (P k s t).eval (G.contract π).cut :=
  contractProgram_eval G π (P k s t)

omit [DecidableEq V] in
@[simp] theorem eval_interpRand_ret (P : STPrograms Q) (o : O) (read : Finset V → ℝ) :
    (interpRand P (ret o : CallTree V Q O 0)).eval read = PMF.pure o := by
  simp [interpRand]

omit [DecidableEq V] in
@[simp] theorem eval_interpRand_query (P : STPrograms Q) {q : ℕ} (S : Finset V)
    (next : ℝ → CallTree V Q O q) (read : Finset V → ℝ) :
    (interpRand P (query S next)).eval read = (interpRand P (next (read S))).eval read := by
  simp [interpRand]

omit [DecidableEq V] in
@[simp] theorem eval_interpRand_call (P : STPrograms Q) {q k : ℕ} (π : V → Fin k)
    (s t : Fin k) (hst : s ≠ t) (next : Finset (Fin k) → CallTree V Q O q)
    (read : Finset V → ℝ) :
    (interpRand P (call k π s t hst next)).eval read =
      ((callProgram P π s t).eval read).bind (fun S => (interpRand P (next S)).eval read) := by
  simp [interpRand]

omit [DecidableEq V] in
@[simp] theorem eval_interpRand_random (P : STPrograms Q) {q : ℕ} {ι : Type} (μ : PMF ι)
    (next : ι → CallTree V Q O q) (read : Finset V → ℝ) :
    (interpRand P (random μ next)).eval read =
      μ.bind (fun i => (interpRand P (next i)).eval read) := by
  simp [interpRand, PMF.bind_map, Function.comp_def]

omit [DecidableEq V] in
@[simp] theorem eval_interpRand_up (P : STPrograms Q) {q r : ℕ} (h : q ≤ r)
    (T : CallTree V Q O q) (read : Finset V → ℝ) :
    (interpRand P (up h T)).eval read = (interpRand P T).eval read := by
  simp [interpRand]

/-! ### The main comparisons -/

/-- One call misses the ideal shore with probability at most `δ`. -/
theorem callProgram_mass_ne {M : ℕ} {P : STPrograms Q} {δ : ℝ≥0∞} (hP : P.FailsAtMost M δ)
    (G : WeightedGraph V) (hG : InputPromise M G) {k : ℕ} (π : V → Fin k) {s t : Fin k}
    (hst : s ≠ t) :
    mass ((callProgram P π s t).eval G.cut) (fun S => S ≠ idealShore (G.contract π) s t) ≤ δ := by
  rw [callProgram_eval]
  refine le_trans (mass_mono _ ?_)
    (hP k s t hst _ (call_promise G hG π).1 (call_promise G hG π).2)
  intro S hne hcan
  exact hne (eq_idealShore hst hcan)

/-- (G1) A family that never fails gives exactly the ideal law. -/
theorem eval_interpRand_of_exact {M : ℕ} {P : STPrograms Q} (hP : P.FailsAtMost M 0)
    (G : WeightedGraph V) (hG : InputPromise M G) {q : ℕ} (T : CallTree V Q O q) :
    (interpRand P T).eval G.cut = interpIdeal G T := by
  induction T with
  | ret o => simp [interpIdeal]
  | query S next ih =>
      rw [eval_interpRand_query, ih]
      rfl
  | call k π s t hst next ih =>
      rw [eval_interpRand_call,
        eq_pure_of_mass_ne_eq_zero _ _ (nonpos_iff_eq_zero.mp (callProgram_mass_ne hP G hG π hst)),
        PMF.pure_bind, ih]
      rfl
  | random μ next ih =>
      rw [eval_interpRand_random]
      simp only [interpIdeal, ih]
  | up h T ih =>
      rw [eval_interpRand_up, ih]
      rfl

/-- (G2) Structural union bound: every event has at most its ideal probability
plus `δ` times the budget. -/
theorem mass_interpRand_le {M : ℕ} {P : STPrograms Q} {δ : ℝ≥0∞} (hP : P.FailsAtMost M δ)
    (hQ : ∀ k, 1 ≤ k → 1 ≤ Q k) (G : WeightedGraph V) (hG : InputPromise M G) {q : ℕ}
    (T : CallTree V Q O q) (Bad : O → Prop) :
    mass ((interpRand P T).eval G.cut) Bad ≤ mass (interpIdeal G T) Bad + δ * q := by
  induction T with
  | ret o => simp [interpIdeal]
  | query S next ih =>
      rw [eval_interpRand_query]
      refine (ih (G.cut S)).trans ?_
      simp only [interpIdeal]
      gcongr
      exact_mod_cast Nat.le_succ _
  | @call q k π s t hst next ih =>
      rw [eval_interpRand_call]
      have hk : 1 ≤ Q k := hQ k (by have := s.pos; omega)
      refine (mass_bind_le_add _ _ (fun S => S ≠ idealShore (G.contract π) s t) Bad
        (ε := mass (interpIdeal G (next (idealShore (G.contract π) s t))) Bad + δ * q)
        (callProgram_mass_ne hP G hG π hst) (fun S hS => ?_)).trans ?_
      · rw [not_not] at hS
        rw [hS]
        exact ih _
      · calc
          δ + (mass (interpIdeal G (next (idealShore (G.contract π) s t))) Bad + δ * q) =
              mass (interpIdeal G (call k π s t hst next)) Bad + δ * ((q + 1 : ℕ) : ℝ≥0∞) := by
            simp only [interpIdeal]
            push_cast
            ring
          _ ≤ _ := by
            have hle : q + 1 ≤ q + Q k := Nat.add_le_add_left hk q
            gcongr
  | @random q ι μ next ih =>
      rw [eval_interpRand_random, mass_bind]
      simp only [interpIdeal, mass_bind]
      calc
        ∑' i, μ i * mass ((interpRand P (next i)).eval G.cut) Bad ≤
            ∑' i, μ i * (mass (interpIdeal G (next i)) Bad + δ * q) :=
          ENNReal.tsum_le_tsum (fun i => by gcongr; exact ih i)
        _ = (∑' i, μ i * mass (interpIdeal G (next i)) Bad) + (∑' i, μ i) * (δ * q) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        _ = _ := by rw [PMF.tsum_coe, one_mul]
  | up h T ih =>
      rw [eval_interpRand_up]
      refine ih.trans ?_
      simp only [interpIdeal]
      gcongr

/-! ### Composition -/

theorem interpIdeal_bind (G : WeightedGraph V) {r : ℕ} (f : O → CallTree V Q P r) {q : ℕ}
    (T : CallTree V Q O q) :
    interpIdeal G (T.bind f) = (interpIdeal G T).bind (fun o => interpIdeal G (f o)) := by
  induction T with
  | ret o => simp [bind, interpIdeal]
  | query S next ih => simp only [bind, interpIdeal, ih]
  | call k π s t hst next ih => simp only [bind, interpIdeal, ih]
  | random μ next ih => simp only [bind, interpIdeal, ih, PMF.bind_bind]
  | up h T ih => simp only [bind, interpIdeal, ih]

omit [DecidableEq V] in
theorem eval_interpRand_bind (P' : STPrograms Q) (read : Finset V → ℝ) {r : ℕ}
    (f : O → CallTree V Q P r) {q : ℕ} (T : CallTree V Q O q) :
    (interpRand P' (T.bind f)).eval read =
      ((interpRand P' T).eval read).bind (fun o => (interpRand P' (f o)).eval read) := by
  induction T with
  | ret o => simp [bind]
  | query S next ih => simp only [bind, eval_interpRand_up, eval_interpRand_query, ih]
  | call k π s t hst next ih =>
      simp only [bind, eval_interpRand_up, eval_interpRand_call, ih, PMF.bind_bind]
  | random μ next ih => simp only [bind, eval_interpRand_random, ih, PMF.bind_bind]
  | up h T ih => simp only [bind, eval_interpRand_up, ih]

theorem interpIdeal_map (G : WeightedGraph V) {q : ℕ} (f : O → P) (T : CallTree V Q O q) :
    interpIdeal G (T.map f) = (interpIdeal G T).map f := by
  simp only [map, cast, interpIdeal, interpIdeal_bind]
  rfl

omit [DecidableEq V] in
theorem eval_interpRand_map (P' : STPrograms Q) (read : Finset V → ℝ) {q : ℕ} (f : O → P)
    (T : CallTree V Q O q) :
    (interpRand P' (T.map f)).eval read = ((interpRand P' T).eval read).map f := by
  simp only [map, cast, eval_interpRand_up, eval_interpRand_bind, eval_interpRand_ret]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Fintype V] [DecidableEq V] in
theorem rtree_eval_zero (T : RTree (Finset V) ℝ O 0) (read : Finset V → ℝ) : T.eval read = T := by
  have h : ∀ p : PMF O, PMF.map Prod.fst (PMF.map (fun o => (o, 0)) p) = p := fun p => by
    rw [PMF.map_comp]
    exact PMF.map_id p
  exact h T

set_option backward.isDefEq.respectTransparency false in
omit [Fintype V] [DecidableEq V] in
/-- The output law of a randomized tree, one level down. -/
theorem rtree_eval_succ {q : ℕ} (T : RTree (Finset V) ℝ O (q + 1)) (read : Finset V → ℝ) :
    T.eval read = PMF.bind T (fun action => match action with
      | Sum.inl o => PMF.pure o
      | Sum.inr (S, next) => (next (read S)).eval read) := by
  unfold RTree.eval
  simp only [RTree.run]
  rw [PMF.map_bind]
  congr 1
  funext action
  rcases action with o | ⟨S, next⟩
  · simp [PMF.pure_map]
  · simp [PMF.map_comp, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
/-- A call-free tree has its own law under the ideal meaning. -/
theorem interpIdeal_ofRTree (G : WeightedGraph V) {q : ℕ} (T : RTree (Finset V) ℝ O q) :
    interpIdeal G (ofRTree (Q := Q) T) = T.eval G.cut := by
  induction q with
  | zero =>
      rw [rtree_eval_zero]
      simp only [ofRTree, interpIdeal]
      exact PMF.bind_pure T
  | succ q ih =>
      rw [rtree_eval_succ]
      simp only [ofRTree, interpIdeal]
      congr 1
      funext action
      rcases action with o | ⟨S, next⟩
      · rfl
      · exact ih _

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq V] in
/-- A call-free tree keeps its law under the randomized meaning. -/
theorem eval_interpRand_ofRTree (P' : STPrograms Q) (read : Finset V → ℝ) {q : ℕ}
    (T : RTree (Finset V) ℝ O q) :
    (interpRand P' (ofRTree (Q := Q) T)).eval read = T.eval read := by
  induction q with
  | zero =>
      have h : (interpRand P' (ofRTree (Q := Q) T)).eval read = PMF.bind T PMF.pure := by
        simp only [ofRTree, eval_interpRand_random, eval_interpRand_ret]
      rw [h, rtree_eval_zero T]
      exact PMF.bind_pure T
  | succ q ih =>
      conv_rhs => rw [rtree_eval_succ T]
      simp only [ofRTree, eval_interpRand_random]
      congr 1
      funext action
      rcases action with o | ⟨S, next⟩
      · simp
      · simp only [eval_interpRand_query]
        exact ih _

end CallTree
end
end CutQueryComplexity.GHReduction.Randomized
