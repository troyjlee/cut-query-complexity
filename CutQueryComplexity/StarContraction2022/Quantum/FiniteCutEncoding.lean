import CutQueryComplexity.Model.RandomizedComposition
import CutQueryComplexity.Quantum.Model
import CutQueryComplexity.StarContraction2022.Common.Basic

/-! # Finite answer and output encoding for real-answer cut trees

The transformations are public and retain the complete output/count law.
Only the honest-input losslessness theorem assumes soundness of supported
results. No graph, solver or cost certificate is an input to a constructor.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum

noncomputable section
open scoped Classical

variable {I A B O P : Type} {q : ℕ}

/-- Restrict the answer alphabet without changing questions or random choices. -/
def mapAnswers (decode : B → A) : {q : ℕ} → RTree I A O q → RTree I B O q
  | 0, T => T
  | k + 1, T => PMF.map (fun action : O ⊕ (I × (A → RTree I A O k)) =>
      match action with
      | Sum.inl o => Sum.inl o
      | Sum.inr (i, next) => Sum.inr (i, fun b => mapAnswers decode (next (decode b)))) T

@[simp] theorem mapAnswers_zero (decode : B → A) (T : RTree I A O 0) :
    mapAnswers decode T = (show PMF O from T) := rfl

/-- Exact joint law for every finite or infinite answer table. -/
theorem run_mapAnswers (decode : B → A) (T : RTree I A O q) (read : I → B) :
    RTree.run read (mapAnswers decode T) = RTree.run (decode ∘ read) T := by
  induction q with
  | zero => rfl
  | succ q ih =>
      let lift : O ⊕ (I × (A → RTree I A O q)) →
          O ⊕ (I × (B → RTree I B O q)) := fun action => match action with
        | Sum.inl o => Sum.inl o
        | Sum.inr (i, next) => Sum.inr (i, fun b => mapAnswers decode (next (decode b)))
      let step : O ⊕ (I × (B → RTree I B O q)) → PMF (O × ℕ) :=
        fun action => match action with
        | Sum.inl o => PMF.pure (o, 0)
        | Sum.inr (i, next) =>
            (RTree.run read (next (read i))).map (fun p => (p.1, p.2 + 1))
      change PMF.bind (PMF.map lift T) step = _
      calc
        _ = PMF.bind T (step ∘ lift) := PMF.bind_map T lift step
        _ = _ := by
          change PMF.bind T (step ∘ lift) = PMF.bind T _
          apply congrArg (fun k => PMF.bind T k)
          funext action
          rcases action with o | ⟨i, next⟩
          · rfl
          · dsimp only [Function.comp_def, lift, step]
            rw [ih]
            simp only [Function.comp_def]

/-- The existing free output map also preserves the realized count exactly. -/
theorem run_map_outputs (f : O → P) (T : RTree I A O q) (read : I → A) :
    RTree.run read (T.map f) =
      (RTree.run read T).map (fun p => (f p.1, p.2)) := by
  rw [RTree.map, RTree.run_cast, RTree.run_bind]
  simp only [RTree.run_pure, PMF.pure_map, Nat.add_zero]
  rfl

theorem mapAnswers_count_law (decode : B → A) (T : RTree I A O q) (read : I → B) :
    (RTree.run read (mapAnswers decode T)).map Prod.snd =
      (RTree.run (decode ∘ read) T).map Prod.snd := by
  rw [run_mapAnswers]

private theorem pmf_map_congr_support {X Y : Type} (p : PMF X) {f g : X → Y}
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  ext y
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ p.support
  · rw [h x hx]
  · have hz : p x = 0 := by simpa only [PMF.mem_support_iff, not_not] using hx
    simp [hz]

/-- Real output values are replaced by a genuinely finite public alphabet. -/
abbrev FiniteCutResult (n W : ℕ) := Option (Finset (Fin n) × CutAnswer n W)

abbrev OptionalCutTree (n q : ℕ) :=
  RTree (Finset (Fin n)) ℝ (Option (CutResult (Fin n))) q

abbrev TotalCutTree (n q : ℕ) :=
  RTree (Finset (Fin n)) ℝ (CutResult (Fin n)) q

variable {n W : ℕ}

def decodeCutAnswer (a : CutAnswer n W) : ℝ := ((a : ℕ) : ℝ)

theorem decodeCutAnswer_range (a : CutAnswer n W) :
    0 ≤ decodeCutAnswer a ∧ decodeCutAnswer a ≤ ((W * n * n : ℕ) : ℝ) := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  change ((a : ℕ) : ℝ) ≤ ((W * n * n : ℕ) : ℝ)
  exact_mod_cast Nat.le_of_lt_succ a.isLt

@[simp] theorem decode_capacityRead (G : CapacityGraph (Fin n) W)
    (S : Finset (Fin n)) : decodeCutAnswer (capacityRead G S) = G.toWeighted.cut S := by
  rw [CapacityGraph.toWeighted_cut]
  rfl

theorem decode_capacityRead_fun (G : CapacityGraph (Fin n) W) :
    decodeCutAnswer ∘ capacityRead G = G.toWeighted.cut := by
  funext S
  exact decode_capacityRead G S

theorem decodeCutAnswer_of_bound_zero (h : W * n * n = 0) (a : CutAnswer n W) :
    decodeCutAnswer a = 0 := by
  have hlt := a.isLt
  have ha : (a : ℕ) = 0 := by omega
  simp [decodeCutAnswer, ha]

@[simp] theorem decodeCutAnswer_zero_weight (a : CutAnswer n 0) :
    decodeCutAnswer a = 0 :=
  decodeCutAnswer_of_bound_zero (by simp) a

@[simp] theorem decodeCutAnswer_zero_vertices (a : CutAnswer 0 W) :
    decodeCutAnswer a = 0 :=
  decodeCutAnswer_of_bound_zero (by simp) a

/-- Pure validation; the original shore is retained and no value query is made. -/
def encodeCutResult (W : ℕ) (r : CutResult (Fin n)) : FiniteCutResult n W :=
  (validateCount (W * n * n) r.value).map (fun a => (r.shore, a))

def encodeOptionalCutResult (W : ℕ) (r : Option (CutResult (Fin n))) :
    FiniteCutResult n W := r.bind (encodeCutResult W)

def decodeFiniteCutResult (r : FiniteCutResult n W) : Option (CutResult (Fin n)) :=
  r.map (fun p => ⟨p.1, decodeCutAnswer p.2⟩)

@[simp] theorem encodeOptionalCutResult_none :
    encodeOptionalCutResult W (none : Option (CutResult (Fin n))) = none := rfl

@[simp] theorem encodeOptionalCutResult_some (r : CutResult (Fin n)) :
    encodeOptionalCutResult W (some r) = encodeCutResult W r := rfl

@[simp] theorem decodeFiniteCutResult_none :
    decodeFiniteCutResult (none : FiniteCutResult n W) = none := rfl

@[simp] theorem decodeFiniteCutResult_some (S : Finset (Fin n)) (a : CutAnswer n W) :
    decodeFiniteCutResult (some (S, a)) = some ⟨S, decodeCutAnswer a⟩ := rfl

theorem encodeCutResult_spec {r : CutResult (Fin n)} {e : Finset (Fin n) × CutAnswer n W}
    (h : encodeCutResult W r = some e) :
    e.1 = r.shore ∧ decodeCutAnswer e.2 = r.value := by
  cases hv : validateCount (W * n * n) r.value with
  | none => simp [encodeCutResult, hv] at h
  | some a =>
      have he : (r.shore, a) = e :=
        Option.some.inj (by simpa only [encodeCutResult, hv, Option.map_some] using h)
      refine ⟨(congrArg Prod.fst he).symm, ?_⟩
      rw [← congrArg Prod.snd he]
      exact (validateCount_spec hv).1

theorem encodeCutResult_eq_none_iff (r : CutResult (Fin n)) :
    encodeCutResult W r = none ↔
      ¬ ∃ a : CutAnswer n W, decodeCutAnswer a = r.value := by
  unfold encodeCutResult validateCount
  split_ifs with h <;> simp [decodeCutAnswer, h]

theorem encodeCutResult_reject (r : CutResult (Fin n))
    (h : r.value < 0 ∨ ((W * n * n : ℕ) : ℝ) < r.value) :
    encodeCutResult W r = none := by
  rw [encodeCutResult, validateCount_reject h]
  rfl

theorem encodeCutResult_of_answer (W : ℕ) (r : CutResult (Fin n))
    (a : CutAnswer n W) (h : r.value = decodeCutAnswer a) :
    encodeCutResult W r = some (r.shore, a) := by
  simp [encodeCutResult, h, decodeCutAnswer]

theorem decode_encodeCutResult_of_answer (W : ℕ) (r : CutResult (Fin n))
    (a : CutAnswer n W) (h : r.value = decodeCutAnswer a) :
    decodeFiniteCutResult (encodeCutResult W r) = some r := by
  rw [encodeCutResult_of_answer W r a h, decodeFiniteCutResult_some, ← h]

@[simp] theorem encode_decodeFiniteCutResult (r : FiniteCutResult n W) :
    encodeOptionalCutResult W (decodeFiniteCutResult r) = r := by
  rcases r with _ | ⟨S, a⟩
  · rfl
  · simp [encodeOptionalCutResult, decodeFiniteCutResult, encodeCutResult, decodeCutAnswer]

/-- The actual capacity cut bound discharges representability of a sound result. -/
theorem decode_encodeCutResult_sound (G : CapacityGraph (Fin n) W)
    (r : CutResult (Fin n)) (h : r.Sound G.toWeighted) :
    decodeFiniteCutResult (encodeCutResult W r) = some r :=
  decode_encodeCutResult_of_answer W r (capacityRead G r.shore)
    (h.2.trans (decode_capacityRead G r.shore).symm)

/-- Public finite tree: one finite answer per original cut, followed by pure validation. -/
def finiteCutTree (W : ℕ) (T : OptionalCutTree n q) :
    RTree (Finset (Fin n)) (CutAnswer n W) (FiniteCutResult n W) q :=
  (mapAnswers (decodeCutAnswer (n := n) (W := W)) T).map (encodeOptionalCutResult W)

def finiteCutTreeTotal (W : ℕ) (T : TotalCutTree n q) :
    RTree (Finset (Fin n)) (CutAnswer n W) (FiniteCutResult n W) q :=
  finiteCutTree W (T.map some)

theorem finiteCutTree_run (T : OptionalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) :
    RTree.run read (finiteCutTree W T) =
      (RTree.run (decodeCutAnswer ∘ read) T).map
        (fun p => (encodeOptionalCutResult W p.1, p.2)) := by
  rw [finiteCutTree, run_map_outputs, run_mapAnswers]

theorem finiteCutTreeTotal_run (T : TotalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) :
    RTree.run read (finiteCutTreeTotal W T) =
      (RTree.run (decodeCutAnswer ∘ read) T).map
        (fun p => (encodeCutResult W p.1, p.2)) := by
  rw [finiteCutTreeTotal, finiteCutTree_run, run_map_outputs, PMF.map_comp]
  rfl

theorem finiteCutTree_count_law (T : OptionalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) :
    (RTree.run read (finiteCutTree W T)).map Prod.snd =
      (RTree.run (decodeCutAnswer ∘ read) T).map Prod.snd := by
  rw [finiteCutTree_run, PMF.map_comp]
  rfl

theorem finiteCutTreeTotal_count_law (T : TotalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) :
    (RTree.run read (finiteCutTreeTotal W T)).map Prod.snd =
      (RTree.run (decodeCutAnswer ∘ read) T).map Prod.snd := by
  rw [finiteCutTreeTotal_run, PMF.map_comp]
  rfl

theorem finiteCutTree_cost_le (T : OptionalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) {p : FiniteCutResult n W × ℕ}
    (hp : p ∈ (RTree.run read (finiteCutTree W T)).support) : p.2 ≤ q :=
  RTree.cost_le _ _ hp

/-- Explicit proof-side correctness premise for a generic source tree. -/
def CutTreeSound (T : OptionalCutTree n q) (G : WeightedGraph (Fin n)) : Prop :=
  ∀ r c, (some r, c) ∈ (RTree.run G.cut T).support → r.Sound G

def TotalCutTreeSound (T : TotalCutTree n q) (G : WeightedGraph (Fin n)) : Prop :=
  ∀ r c, (r, c) ∈ (RTree.run G.cut T).support → r.Sound G

theorem totalCutTreeSound_map_some (T : TotalCutTree n q) (G : WeightedGraph (Fin n))
    (h : TotalCutTreeSound T G) : CutTreeSound (T.map some) G := by
  intro r c hp
  rw [run_map_outputs] at hp
  obtain ⟨⟨out, k⟩, hout, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  have ho : out = r := Option.some.inj (congrArg Prod.fst he)
  have hk : k = c := congrArg Prod.snd he
  subst r
  subst c
  exact h out k hout

theorem finiteCutTree_decoded_run (T : OptionalCutTree n q)
    (G : CapacityGraph (Fin n) W) (h : CutTreeSound T G.toWeighted) :
    (RTree.run (capacityRead G) (finiteCutTree W T)).map
      (fun p => (decodeFiniteCutResult p.1, p.2)) = RTree.run G.toWeighted.cut T := by
  rw [finiteCutTree_run, decode_capacityRead_fun, PMF.map_comp]
  calc
    _ = (RTree.run G.toWeighted.cut T).map id := by
      apply pmf_map_congr_support
      rintro ⟨out, c⟩ hp
      cases out with
      | none => rfl
      | some r =>
          exact Prod.ext (decode_encodeCutResult_sound G r (h r c hp)) rfl
    _ = _ := PMF.map_id _

theorem finiteCutTreeTotal_decoded_run (T : TotalCutTree n q)
    (G : CapacityGraph (Fin n) W) (h : TotalCutTreeSound T G.toWeighted) :
    (RTree.run (capacityRead G) (finiteCutTreeTotal W T)).map
      (fun p => (decodeFiniteCutResult p.1, p.2)) =
        (RTree.run G.toWeighted.cut T).map (fun p => (some p.1, p.2)) := by
  rw [finiteCutTreeTotal,
    finiteCutTree_decoded_run (T.map some) G (totalCutTreeSound_map_some T G.toWeighted h)]
  exact run_map_outputs some T G.toWeighted.cut

theorem finiteCutTree_successProb (T : OptionalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) (Good : FiniteCutResult n W → Prop) :
    (finiteCutTree W T).successProb read Good =
      T.successProb (decodeCutAnswer ∘ read) (fun out => Good (encodeOptionalCutResult W out)) := by
  rw [RTree.successProb, finiteCutTree_run, PMF.toOuterMeasure_map_apply]
  rfl

theorem finiteCutTree_successProb_honest (T : OptionalCutTree n q)
    (G : CapacityGraph (Fin n) W) (h : CutTreeSound T G.toWeighted)
    (Good : Option (CutResult (Fin n)) → Prop) :
    (finiteCutTree W T).successProb (capacityRead G)
      (fun e => Good (decodeFiniteCutResult e)) = T.successProb G.toWeighted.cut Good := by
  have heq := congrArg
    (fun p : PMF (Option (CutResult (Fin n)) × ℕ) =>
      (p.toOuterMeasure {out | Good out.1}).toReal)
    (finiteCutTree_decoded_run T G h)
  rw [PMF.toOuterMeasure_map_apply] at heq
  exact heq

theorem finiteCutTreeTotal_successProb_honest (T : TotalCutTree n q)
    (G : CapacityGraph (Fin n) W) (h : TotalCutTreeSound T G.toWeighted)
    (Good : Option (CutResult (Fin n)) → Prop) :
    (finiteCutTreeTotal W T).successProb (capacityRead G)
      (fun e => Good (decodeFiniteCutResult e)) =
        T.successProb G.toWeighted.cut (fun r => Good (some r)) := by
  have heq := congrArg
    (fun p : PMF (Option (CutResult (Fin n)) × ℕ) =>
      (p.toOuterMeasure {out | Good out.1}).toReal)
    (finiteCutTreeTotal_decoded_run T G h)
  simp only [PMF.toOuterMeasure_map_apply] at heq
  exact heq

/-- At budget zero the original output PMF is validated without an oracle call. -/
theorem finiteCutTree_zero_run (T : OptionalCutTree n 0)
    (read : Finset (Fin n) → CutAnswer n W) :
    RTree.run read (finiteCutTree W T) =
      (show PMF (Option (CutResult (Fin n))) from T).map
        (fun out => (encodeOptionalCutResult W out, 0)) := by
  rw [finiteCutTree_run]
  change ((show PMF (Option (CutResult (Fin n))) from T).map
    (fun out => (out, (0 : ℕ)))).map _ = _
  rw [PMF.map_comp]
  rfl

theorem no_properShore_small (hn : n ≤ 1) (S : Finset (Fin n)) : ¬ ProperShore S := by
  intro h
  have hpos : 0 < S.card := Finset.card_pos.mpr h.1
  apply h.2
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ S)
  simpa only [Finset.card_univ, Fintype.card_fin] using (show n ≤ S.card by omega)

/-- The n=0/1 boundary cannot manufacture a sound proper shore. -/
theorem small_sound_outputs_none (T : OptionalCutTree n q)
    (G : WeightedGraph (Fin n)) (hn : n ≤ 1) (h : CutTreeSound T G)
    {p : Option (CutResult (Fin n)) × ℕ} (hp : p ∈ (RTree.run G.cut T).support) :
    p.1 = none := by
  rcases p with ⟨out, c⟩
  cases out with
  | none => rfl
  | some r => exact False.elim (no_properShore_small hn r.shore (h r c hp).1)

#print axioms run_mapAnswers
#print axioms run_map_outputs
#print axioms mapAnswers_count_law
#print axioms decodeCutAnswer_range
#print axioms decode_capacityRead
#print axioms decodeCutAnswer_zero_weight
#print axioms decodeCutAnswer_zero_vertices
#print axioms encodeCutResult_spec
#print axioms encodeCutResult_eq_none_iff
#print axioms encodeCutResult_reject
#print axioms encode_decodeFiniteCutResult
#print axioms decode_encodeCutResult_sound
#print axioms finiteCutTree_run
#print axioms finiteCutTreeTotal_run
#print axioms finiteCutTree_count_law
#print axioms finiteCutTreeTotal_count_law
#print axioms finiteCutTree_cost_le
#print axioms finiteCutTree_decoded_run
#print axioms finiteCutTreeTotal_decoded_run
#print axioms finiteCutTree_successProb
#print axioms finiteCutTree_successProb_honest
#print axioms finiteCutTreeTotal_successProb_honest
#print axioms finiteCutTree_zero_run
#print axioms small_sound_outputs_none

end
end CutQueryComplexity.StarContraction2022.Quantum
