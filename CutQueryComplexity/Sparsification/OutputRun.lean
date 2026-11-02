import CutQueryComplexity.Sparsification.OutputSample

/-! # The output-sampling program

For each recorded event, `eventDraws` queries the cut of the merged set, computes
the residual mass `M` from the event's cache, and takes `r = ⌈cM/β⌉` output draws
of weight `M/r`, provided `r ≤ R₂`. Events with no residual mass contribute the
zero graph. `outRun` processes the event list in order and adds the sampled
graphs; it aborts with `none` if a cap binds.

`outRun_eval` proves that when every cache is exact and no cap binds, the output
law is exactly `some` of the counted sample of the event buckets. The draws use
fresh randomness and depend only on the recorded events.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V]

/-! ### Sums of draw lists -/

omit [Fintype V] in
theorem independentGraphSum_append (L₁ L₂ : List (PMF (WeightedGraph V))) :
    independentGraphSum (L₁ ++ L₂) =
      (independentGraphSum L₁).bind (fun X => (independentGraphSum L₂).map (X + ·)) := by
  induction L₁ with
  | nil =>
      simp only [List.nil_append, independentGraphSum, PMF.pure_bind, WeightedGraph.zero_add]
      exact (PMF.map_id _).symm
  | cons p L₁ ih =>
      simp only [List.cons_append, independentGraphSum, ih, PMF.bind_bind, PMF.map_bind]
      congr 1
      funext X
      rw [PMF.bind_map]
      simp only [Function.comp_def, PMF.map_comp]
      congr 1
      funext Y
      congr 1
      funext Z
      exact (WeightedGraph.add_assoc X Y Z).symm

namespace CountedBucket

theorem sampleLaw_cons (b : CountedBucket V) (bs : List (CountedBucket V)) :
    sampleLaw (b :: bs) = (sampleLaw [b]).bind (fun X => (sampleLaw bs).map (X + ·)) := by
  simp only [sampleLaw, expanded, List.flatMap_cons, List.map_append, List.flatMap_nil,
    List.append_nil]
  exact independentGraphSum_append _ _

end CountedBucket

/-! ### Per-event program -/

/-- Number of output draws for an event, from its computed mass. -/
def outCount (c : ℝ) (e : MergeEvent V) (M : ℝ) : ℕ := ⌈c * M / e.β⌉₊

omit [Fintype V] in
theorem outCount_pos {c : ℝ} (hc : 0 < c) {e : MergeEvent V} (hβ : 0 < e.β) {M : ℝ}
    (hM : 0 < M) : 0 < outCount c e M := Nat.ceil_pos.mpr (by positivity)

/-- One event: one cut query, then capped output draws. -/
def eventDraws (c : ℝ) (R₂ : ℕ) (e : MergeEvent V) :
    RTree (Finset V) ℝ (Option (WeightedGraph V))
      (R₂ * residualDrawCost (searchDepth V) (searchDepth V) + 1) :=
  RTree.query (pull e.π e.group) fun cut =>
    if hM : 0 < cachedMass e.cache e.group cut then
      if hr : outCount c e (cachedMass e.cache e.group cut) ≤ R₂ then
        ((sumDraws (sampleResidual (searchDepth V) (searchDepth V) e.π e.cache e.group)
          (outDraw (cachedMass e.cache e.group cut / outCount c e (cachedMass e.cache e.group cut))
            (div_nonneg hM.le (Nat.cast_nonneg _)))
          (outCount c e (cachedMass e.cache e.group cut))).weaken
            (Nat.mul_le_mul_right _ hr)).map some
      else RTree.pure (PMF.pure none)
    else RTree.pure (PMF.pure (some 0))

abbrev outStepBudget (V : Type) [Fintype V] (R₂ : ℕ) : ℕ :=
  R₂ * residualDrawCost (searchDepth V) (searchDepth V) + 1

/-- All events in order, with the sampled graphs added. -/
def outRun (c : ℝ) (R₂ : ℕ) : (L : List (MergeEvent V)) →
    RTree (Finset V) ℝ (Option (WeightedGraph V)) (L.length * outStepBudget V R₂)
  | [] => RTree.pure (PMF.pure (some 0))
  | e :: L => ((eventDraws c R₂ e).bind fun o => match o with
      | none => (RTree.pure (PMF.pure none) :
          RTree (Finset V) ℝ (Option (WeightedGraph V)) (L.length * outStepBudget V R₂))
      | some X => (outRun c R₂ L).map (Option.map (X + ·))).cast (by simp [List.length_cons]; ring)

/-! ### Output laws -/

/-- The bucket of an event, when its residual mass is positive. -/
def eventBucket (G : WeightedGraph V) (c : ℝ) (hc : 0 < c) (e : MergeEvent V) :
    Option (CountedBucket V) :=
  if h : 0 < (G.contract e.π).internalMass e.group ∧ 0 < e.β then
    some (outBucket G e.π e.group (outCount c e ((G.contract e.π).internalMass e.group))
      (outCount_pos hc h.2 h.1) h.1)
  else none

def eventBuckets (G : WeightedGraph V) (c : ℝ) (hc : 0 < c) (L : List (MergeEvent V)) :
    List (CountedBucket V) := L.filterMap (eventBucket G c hc)

/-- The per-event law, with the computed mass abstracted by an equation. -/
theorem eventDraws_sample (G : WeightedGraph V) (c : ℝ) (hc : 0 < c) (e : MergeEvent V)
    (hcache : ∀ b, e.cache b = G.cut (fiber e.π b)) (hβ : 0 < e.β) (m : ℝ)
    (hm : m = (G.contract e.π).internalMass e.group) (hM : 0 < m) :
    (sumDraws (sampleResidual (searchDepth V) (searchDepth V) e.π e.cache e.group)
        (outDraw (m / outCount c e m) (div_nonneg hM.le (Nat.cast_nonneg _)))
        (outCount c e m)).eval G.cut =
      CountedBucket.sampleLaw [outBucket G e.π e.group (outCount c e m)
        (outCount_pos hc hβ hM) (hm ▸ hM)] := by
  subst hm
  have hB : Fintype.card V ≤ 2 ^ searchDepth V := Nat.le_pow_clog (by decide) _
  exact outDraws_eval G _ _ e.π e.cache hcache e.group hB hB _ _ hM

theorem eventDraws_eval (G : WeightedGraph V) (c : ℝ) (hc : 0 < c) (R₂ : ℕ) (e : MergeEvent V)
    (hcache : ∀ b, e.cache b = G.cut (fiber e.π b)) (hβ : 0 < e.β)
    (hcap : 0 < (G.contract e.π).internalMass e.group →
      outCount c e ((G.contract e.π).internalMass e.group) ≤ R₂) :
    (eventDraws c R₂ e).eval G.cut =
      match eventBucket G c hc e with
      | some b => (CountedBucket.sampleLaw [b]).map some
      | none => PMF.pure (some 0) := by
  have hm := cachedMass_eq G e.π e.cache hcache e.group
  rw [eventDraws, RTree.eval_query]
  unfold eventBucket
  by_cases hM : 0 < cachedMass e.cache e.group (G.cut (pull e.π e.group))
  · have hM' : 0 < (G.contract e.π).internalMass e.group := hm ▸ hM
    have hr : outCount c e (cachedMass e.cache e.group (G.cut (pull e.π e.group))) ≤ R₂ := by
      rw [hm]; exact hcap hM'
    simp only [hM, hr, ↓reduceDIte, hM', hβ, and_self, RTree.eval_map, RTree.eval_weaken]
    rw [eventDraws_sample G c hc e hcache hβ _ hm hM]
    congr 2
    simp only [hm]
  · have hM' : ¬(0 < (G.contract e.π).internalMass e.group ∧ 0 < e.β) := by
      rw [← hm]; exact fun h => hM h.1
    simp only [hM, ↓reduceDIte, hM', RTree.eval_pure]

/-- **Output law.** With exact caches, positive labels, and caps that never bind, the
output is `some` of the counted sample of the event buckets. -/
theorem outRun_eval (G : WeightedGraph V) (c : ℝ) (hc : 0 < c) (R₂ : ℕ)
    (L : List (MergeEvent V))
    (hL : ∀ e ∈ L, (∀ b, e.cache b = G.cut (fiber e.π b)) ∧ 0 < e.β ∧
      (0 < (G.contract e.π).internalMass e.group →
        outCount c e ((G.contract e.π).internalMass e.group) ≤ R₂)) :
    (outRun c R₂ L).eval G.cut = (CountedBucket.sampleLaw (eventBuckets G c hc L)).map some := by
  induction L with
  | nil =>
      simp [outRun, eventBuckets, CountedBucket.sampleLaw, CountedBucket.expanded,
        independentGraphSum, PMF.pure_map]
  | cons e L ih =>
      obtain ⟨hcache, hβ, hcap⟩ := hL e List.mem_cons_self
      have ih' := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))
      rw [outRun, RTree.eval_cast, RTree.eval_bind,
        eventDraws_eval G c hc R₂ e hcache hβ hcap]
      simp only [eventBuckets, List.filterMap_cons]
      cases hb : eventBucket G c hc e with
      | none =>
          simp only [PMF.pure_bind, RTree.eval_map, ih', PMF.map_comp]
          unfold eventBuckets
          congr 1
          funext X
          simp [WeightedGraph.zero_add]
      | some b =>
          simp only [PMF.bind_map, Function.comp_def, RTree.eval_map, ih', PMF.map_comp]
          rw [CountedBucket.sampleLaw_cons b (List.filterMap (eventBucket G c hc) L), PMF.map_bind]
          unfold eventBuckets
          congr 1
          funext X
          rw [PMF.map_comp]
          rfl

end
end CutQueryComplexity.WeightedGraph
