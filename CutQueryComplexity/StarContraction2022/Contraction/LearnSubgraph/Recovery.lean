import CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph
import CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.RecoveryMoments

/-!
# Actual two-direction capped recovery

Sources, targets, and their embeddings for the two recovery directions, and
the capped recovery program built from them.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph

open Finset WeightedGraph
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

/-- Retained sources of one color. The opposite target class is not intersected
with keep: an omitted source remains available as a target. -/
def directionSources (keep : Finset U) (c : U → Bool) (b : Bool) : Finset U :=
  keep.filter fun u => c u = b

def directionTargets (c : U → Bool) (b : Bool) : Finset U :=
  univ.filter fun u => c u ≠ b

@[simp] theorem mem_directionSources (keep : Finset U) (c : U → Bool) (b : Bool) (u : U) :
    u ∈ directionSources keep c b ↔ u ∈ keep ∧ c u = b := by
  simp [directionSources]

@[simp] theorem mem_directionTargets (c : U → Bool) (b : Bool) (u : U) :
    u ∈ directionTargets c b ↔ c u ≠ b := by simp [directionTargets]

def sourceEmbedding (vertex : U ↪ V) (keep : Finset U) (c : U → Bool) (b : Bool) :
    directionSources keep c b ↪ V :=
  (Function.Embedding.subtype (· ∈ directionSources keep c b)).trans vertex

def targetEmbedding (vertex : U ↪ V) (c : U → Bool) (b : Bool) :
    directionTargets c b ↪ V :=
  (Function.Embedding.subtype (· ∈ directionTargets c b)).trans vertex

theorem source_target_disjoint (vertex : U ↪ V) (keep : Finset U) (c : U → Bool) (b : Bool)
    (u : directionSources keep c b) (v : directionTargets c b) :
    sourceEmbedding vertex keep c b u ≠ targetEmbedding vertex c b v := by
  intro he
  have huv : u.val = v.val := vertex.injective he
  have hs := (mem_directionSources keep c b u.val).mp u.property
  have ht := (mem_directionTargets c b v.val).mp v.property
  exact ht (huv ▸ hs.2)

theorem direction_card_le (keep : Finset U) (c : U → Bool) (b : Bool) :
    Fintype.card (directionSources keep c b) + Fintype.card (directionTargets c b) ≤
      Fintype.card U := by
  have hd : Disjoint (directionSources keep c b) (directionTargets c b) := by
    apply disjoint_left.mpr
    intro u hs ht
    exact (mem_directionTargets c b u).mp ht ((mem_directionSources keep c b u).mp hs).2
  simpa only [Fintype.card_coe, card_union_of_disjoint hd] using
    card_le_univ (directionSources keep c b ∪ directionTargets c b)

theorem sources_disjoint (keep : Finset U) (c : U → Bool) :
    Disjoint (directionSources keep c false) (directionSources keep c true) := by
  apply disjoint_left.mpr
  intro u h0 h1
  have h0 := ((mem_directionSources keep c false u).mp h0).2
  have h1 := ((mem_directionSources keep c true u).mp h1).2
  simp_all

theorem sources_union (keep : Finset U) (c : U → Bool) :
    directionSources keep c false ∪ directionSources keep c true = keep := by
  ext u
  cases hc : c u <;> simp [hc]

abbrev DirectionState (keep : Finset U) (c : U → Bool) (b : Bool) :=
  Recovery.BucketState (directionSources keep c b) (directionTargets c b)

abbrev DirectionPair (keep : Finset U) (c : U → Bool) :=
  DirectionState keep c false × DirectionState keep c true

abbrev RawDirectionPair (keep : Finset U) (c : U → Bool) :=
  Option (DirectionState keep c false) × Option (DirectionState keep c true)

def combineDirections {keep : Finset U} {c : U → Bool}
    (raw : RawDirectionPair keep c) : Option (DirectionPair keep c) :=
  raw.1.bind fun a => raw.2.map fun b => (a, b)

@[simp] theorem combineDirections_none {keep : Finset U} {c : U → Bool}
    (raw : RawDirectionPair keep c) :
    combineDirections raw = none ↔ raw.1 = none ∨ raw.2 = none := by
  rcases raw with ⟨a,b⟩
  cases a <;> cases b <;> simp [combineDirections]

/-- One complete cap, weakened only to the uniform public vertex bound. -/
def directionTree (vertex : U ↪ V) (keep : Finset U) (c : U → Bool) (b : Bool) (h : ℕ) :
    RTree (Finset V) ℝ (Option (DirectionState keep c b))
      (Recovery.recoveryHardCoefficient * h * Fintype.card U) :=
  (Recovery.recoverTree (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) h).weaken
    (Nat.mul_le_mul_left _ (direction_card_le keep c b))

theorem directionTree_eval (vertex : U ↪ V) (keep : Finset U) (c : U → Bool) (b : Bool)
    (h : ℕ) (read : Finset V → ℝ) :
    (directionTree vertex keep c b h).eval read =
      (Recovery.recoverTree (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) h).eval read := by
  exact RTree.eval_weaken _ _ _

/-- Two real recovery calls with fresh randomness. The second call is public
and independent of the first output, even when the first cap aborts. -/
def rawDirections (vertex : U ↪ V) (keep : Finset U) (c : U → Bool) (h : ℕ) :
    RTree (Finset V) ℝ (RawDirectionPair keep c)
      (2 * Recovery.recoveryHardCoefficient * h * Fintype.card U) :=
  ((directionTree vertex keep c false h).bind fun a =>
    (directionTree vertex keep c true h).map fun b => (a,b)).cast (by ring)

theorem rawDirections_eval (vertex : U ↪ V) (keep : Finset U) (c : U → Bool)
    (h : ℕ) (read : Finset V → ℝ) :
    (rawDirections vertex keep c h).eval read =
      ((directionTree vertex keep c false h).eval read).bind fun a =>
        ((directionTree vertex keep c true h).eval read).map fun b => (a,b) := by
  simp only [rawDirections, RTree.eval_cast, RTree.eval_bind, RTree.eval_map]

def twoDirections (vertex : U ↪ V) (keep : Finset U) (c : U → Bool) (h : ℕ) :
    RTree (Finset V) ℝ (Option (DirectionPair keep c))
      (2 * Recovery.recoveryHardCoefficient * h * Fintype.card U) :=
  (rawDirections vertex keep c h).map combineDirections

/-- The output preserves both complete observed bucket states, not a chosen
"good" graph. Subsequent replacement draws may condition on this whole value. -/
structure LearnedTranscript (U : Type) [Fintype U] [DecidableEq U] where
  color : U → Bool
  opposite : U → ℝ
  keep : Finset U
  states : DirectionPair keep color

/-- Directly measure the cross sums in the original graph. This avoids a
second three-query simulation layer when U is an induced vertex set. -/
def oppositeStatisticsOn (vertex : U ↪ V) (c : U → Bool) :
    DTree (Finset V) ℝ (U → ℝ) (3 * Fintype.card U) :=
  ((DTree.queryAll (fun u : U => ({vertex u} : Finset V)) (fun _ => (0 : ℝ))).bind fun a =>
    (DTree.queryAll (fun u => (oppositeSet c u).map vertex) (fun _ => (0 : ℝ))).bind fun b =>
      (DTree.queryAll (fun u => ({vertex u} : Finset V) ∪ (oppositeSet c u).map vertex)
        (fun _ => (0 : ℝ))).map fun d u => (a u + b u - d u) / 2).cast (by omega)

theorem oppositeStatisticsOn_eval (vertex : U ↪ V) (G : WeightedGraph V) (c : U → Bool) :
    (oppositeStatisticsOn vertex c).eval G.cut =
      fun u => ∑ v ∈ oppositeSet c u, G.w (vertex u) (vertex v) := by
  simp only [oppositeStatisticsOn, DTree.eval, DTree.run_cast, DTree.run_bind,
    DTree.run_map, DTree.queryAll_run]
  funext u
  have hdisjoint : Disjoint ({vertex u} : Finset V) ((oppositeSet c u).map vertex) := by
    apply disjoint_singleton_left.mpr
    intro hu
    obtain ⟨v,hv,he⟩ := mem_map.mp hu
    have huv : v = u := vertex.injective he
    exact self_not_mem_oppositeSet c u (huv ▸ hv)
  simpa only [WeightedGraph.cross, sum_singleton, sum_map] using
    (G.cross_eq_three_cuts hdisjoint).symm

def measuredExtraOmissions (h : ℕ) (degree : U → ℕ) (opposite : U → ℝ) : Finset U :=
  univ.filter fun u => 4 * h ≤ degree u ∧ opposite u < h

def extraOmissionGuard (h : ℕ) (degree : U → ℕ) (opposite : U → ℝ) : Prop :=
  ((measuredExtraOmissions h degree opposite).card : ℝ) ≤ (Fintype.card U : ℝ) / h

/-- Every guard is computed from public parameters and measured answers. -/
def recoverAfterColor (vertex : U ↪ V) (degree : U → ℕ) (c : U → Bool)
    (h : ℕ) (opposite : U → ℝ) :
    RTree (Finset V) ℝ (Option (LearnedTranscript U))
      (2 * Recovery.recoveryHardCoefficient * h * Fintype.card U) :=
  if extraOmissionGuard h degree opposite then
    (twoDirections vertex (retainedRows h degree opposite) c h).map fun out =>
      out.map fun states => ⟨c,opposite,retainedRows h degree opposite,states⟩
  else RTree.pure (PMF.pure none)

def learnSubgraphBudget (U : Type) [Fintype U] (h : ℕ) : ℕ :=
  3 * Fintype.card U + 2 * Recovery.recoveryHardCoefficient * h * Fintype.card U

/-- Fair coloring, three original cross-sum families, the public omission
guard, then two capped original-query recoveries. No hidden graph is an input. -/
def learnSubgraphProgram (vertex : U ↪ V) (degree : U → ℕ) (h : ℕ) :
    RTree (Finset V) ℝ (Option (LearnedTranscript U)) (learnSubgraphBudget U h) :=
  RTree.mix ((colors (V := U)).map fun c =>
    (RTree.ofDeterministic (oppositeStatisticsOn vertex c)).bind
      (recoverAfterColor vertex degree c h))

theorem learnSubgraphProgram_every_oracle (vertex : U ↪ V) (degree : U → ℕ) (h : ℕ)
    (read : Finset V → ℝ) {out : Option (LearnedTranscript U) × ℕ}
    (hout : out ∈ (RTree.run read (learnSubgraphProgram vertex degree h)).support) :
    out.2 ≤ 3 * Fintype.card U + 2 * Recovery.recoveryHardCoefficient * h * Fintype.card U :=
  RTree.cost_le _ _ hout

theorem learnSubgraphProgram_eval (vertex : U ↪ V) (degree : U → ℕ) (h : ℕ)
    (read : Finset V → ℝ) :
    (learnSubgraphProgram vertex degree h).eval read =
      (colors (V := U)).bind fun c =>
        (recoverAfterColor vertex degree c h ((oppositeStatisticsOn vertex c).eval read)).eval read := by
  have he (c : U → Bool) : (RTree.ofDeterministic (oppositeStatisticsOn vertex c)).eval read =
      PMF.pure ((oppositeStatisticsOn vertex c).eval read) := by
    simp [RTree.eval, DTree.eval, PMF.pure_map]
  change (RTree.mix ((colors (V := U)).map fun c =>
    (RTree.ofDeterministic (oppositeStatisticsOn vertex c)).bind
      (recoverAfterColor vertex degree c h))).eval read = _
  rw [RTree.eval_mix, PMF.bind_map]
  simp only [Function.comp_def, RTree.eval_bind, he, PMF.pure_bind]

/-- Analysis-only true neighbor rows under the public embedding. -/
def originalRowsOn (vertex : U ↪ V) (G : SimpleInput V) (u : U) : Finset U :=
  univ.filter fun v => (G.w (vertex u) (vertex v) : ℕ) = 1

@[simp] theorem mem_originalRowsOn (vertex : U ↪ V) (G : SimpleInput V) (u v : U) :
    v ∈ originalRowsOn vertex G u ↔ (G.w (vertex u) (vertex v) : ℕ) = 1 := by
  simp [originalRowsOn]

theorem originalRowsOn_loopless (vertex : U ↪ V) (G : SimpleInput V) (u : U) :
    u ∉ originalRowsOn vertex G u := by simp [originalRowsOn, G.diag]

theorem oppositeStatisticsOn_unit (vertex : U ↪ V) (G : SimpleInput V) (c : U → Bool) :
    (oppositeStatisticsOn vertex c).eval G.toWeighted.cut =
      fun u => ((oppositeRows (originalRowsOn vertex G) c u).card : ℝ) := by
  rw [oppositeStatisticsOn_eval]
  funext u
  have he : oppositeRows (originalRowsOn vertex G) c u =
      (oppositeSet c u).filter (fun v => (G.w (vertex u) (vertex v) : ℕ) = 1) := by
    ext v
    simp [oppositeRows, and_comm]
  rw [he, card_eq_sum_ones, Nat.cast_sum]
  rw [sum_filter]
  apply sum_congr rfl
  intro v _
  have hb := (G.w (vertex u) (vertex v)).isLt
  by_cases hv : (G.w (vertex u) (vertex v) : ℕ) = 1
  · simp [hv, CapacityGraph.toWeighted]
  · have hz : (G.w (vertex u) (vertex v) : ℕ) = 0 := by omega
    simp [hv, hz, CapacityGraph.toWeighted]

theorem measuredExtraOmissions_unit (vertex : U ↪ V) (G : SimpleInput V)
    (c : U → Bool) (h : ℕ) :
    measuredExtraOmissions h (fun u => (originalRowsOn vertex G u).card)
      ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut) =
      extraOmissions (originalRowsOn vertex G) h c := by
  rw [oppositeStatisticsOn_unit]
  ext u
  simp only [measuredExtraOmissions, extraOmissions, mem_filter, mem_univ, true_and,
    oppositeRows_filter, Nat.cast_lt]

/-- A successful transcript is turned into explicit true neighbor lists by
forgetting only the color-subtype wrappers. Both bucket states remain stored. -/
def LearnedTranscript.rows (T : LearnedTranscript U) (u : U) : Finset U :=
  if hu : u ∈ directionSources T.keep T.color false then
    ((T.states.1.learned ⟨u,hu⟩).getD ∅).map
      (Function.Embedding.subtype (· ∈ directionTargets T.color false))
  else if hu : u ∈ directionSources T.keep T.color true then
    ((T.states.2.learned ⟨u,hu⟩).getD ∅).map
      (Function.Embedding.subtype (· ∈ directionTargets T.color true))
  else ∅

/-- Omitted sources stay zero; this does not remove them as targets. -/
theorem LearnedTranscript.rows_outside (T : LearnedTranscript U) (u : U) (hu : u ∉ T.keep) :
    T.rows u = ∅ := by
  simp [LearnedTranscript.rows, hu]


/-- The proof-only Boolean row is exactly the opposite-color original row,
with the public target subtype wrappers removed. -/
theorem directionNeighbors_map (vertex : U ↪ V) (G : SimpleInput V)
    (keep : Finset U) (c : U → Bool) (b : Bool) (u : directionSources keep c b) :
    (Recovery.rowNeighbors
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G u)).map
        (Function.Embedding.subtype (· ∈ directionTargets c b)) =
      oppositeRows (originalRowsOn vertex G) c u.val := by
  have hu := ((mem_directionSources keep c b u.val).mp u.property).2
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
    have hn : (G.w (vertex u.val) (vertex w.val) : ℕ) = 1 := by
      simpa [Recovery.rowNeighbors, Recovery.graphMatrix, sourceEmbedding, targetEmbedding] using hw
    apply mem_inter.mpr
    refine ⟨(mem_originalRowsOn vertex G u.val w.val).mpr hn, ?_⟩
    apply (mem_oppositeSet c u.val w.val).mpr
    simpa only [hu] using (mem_directionTargets c b w.val).mp w.property
  · intro hv
    rcases mem_inter.mp hv with ⟨hN,hc⟩
    have hcb : c v ≠ b := by
      simpa only [hu] using (mem_oppositeSet c u.val v).mp hc
    let w : directionTargets c b := ⟨v,(mem_directionTargets c b v).mpr hcb⟩
    apply mem_map.mpr
    refine ⟨w,?_,rfl⟩
    have hN := (mem_originalRowsOn vertex G u.val v).mp hN
    simpa [Recovery.rowNeighbors, Recovery.graphMatrix, sourceEmbedding, targetEmbedding, w] using hN

theorem directionNeighbors_card (vertex : U ↪ V) (G : SimpleInput V)
    (keep : Finset U) (c : U → Bool) (b : Bool) (u : directionSources keep c b) :
    (Recovery.rowNeighbors
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G u)).card =
      (oppositeRows (originalRowsOn vertex G) c u.val).card := by
  simpa only [card_map] using congrArg Finset.card (directionNeighbors_map vertex G keep c b u)

theorem direction_fullDegrees (vertex : U ↪ V) (G : SimpleInput V)
    (keep : Finset U) (c : U → Bool) (b : Bool) (u : directionSources keep c b) :
    Recovery.fullDegrees
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G) u =
      (oppositeRows (originalRowsOn vertex G) c u.val).card := by
  simp only [Recovery.fullDegrees, Recovery.sampleCount_eq_restriction, univ_inter]
  exact directionNeighbors_card vertex G keep c b u

/-- The actual measured public keep test supplies every recovery degree
premise. No suitable input row table is supplied to either recovery program. -/
theorem retained_direction_degree (vertex : U ↪ V) (G : SimpleInput V)
    (c : U → Bool) (h : ℕ) (b : Bool)
    (u : directionSources
      (retainedRows h (fun v => (originalRowsOn vertex G v).card)
        ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut)) c b) :
    h ≤ Recovery.fullDegrees
      (Recovery.graphMatrix (sourceEmbedding vertex
        (retainedRows h (fun v => (originalRowsOn vertex G v).card)
          ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut)) c b)
        (targetEmbedding vertex c b) G) u := by
  rw [direction_fullDegrees]
  have hk := ((mem_directionSources _ c b u.val).mp u.property).1
  have hm : (h : ℝ) ≤ (oppositeStatisticsOn vertex c).eval G.toWeighted.cut u.val :=
    (mem_filter.mp hk).2.2
  have he := congrFun (oppositeStatisticsOn_unit vertex G c) u.val
  have hm' : (h : ℝ) ≤ (oppositeRows (originalRowsOn vertex G) c u.val).card :=
    hm.trans_eq he
  exact_mod_cast hm'



/-- Fixed-cut crossing columns in one true directional row. This is analysis
only; it is never supplied to the recovery or query program. -/
def directionCrossing (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) (b : Bool) (u : directionSources keep c b) :
    Finset (directionTargets c b) :=
  (Recovery.rowNeighbors
    (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G u)).filter
      fun v => v.val ∈ crossingSet S u.val

theorem directionCrossing_subset (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) (b : Bool) (u : directionSources keep c b) :
    directionCrossing vertex G S keep c b u ⊆ Recovery.rowNeighbors
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G u) :=
  filter_subset _ _

theorem direction_baseRatio (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) (b : Bool) (u : directionSources keep c b) :
    ((directionCrossing vertex G S keep c b u).card : ℝ) /
      (Recovery.rowNeighbors
        (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G u)).card =
      rowFraction (oppositeRows (originalRowsOn vertex G) c) S u.val := by
  unfold rowFraction Probability.crossingRatio
  apply congrArg₂ (fun a b : ℕ => (a : ℝ) / (b : ℝ))
  · apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      have hv' : v ∈ Recovery.rowNeighbors (Recovery.graphMatrix
          (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G u) ∧
          v.val ∈ crossingSet S u.val := by
        simpa only [directionCrossing, mem_filter] using hv
      have hn : v.val ∈ oppositeRows (originalRowsOn vertex G) c u.val := by
        rw [← directionNeighbors_map vertex G keep c b u]
        exact mem_map.mpr ⟨v, hv'.1, rfl⟩
      simp only [mem_inter]
      exact ⟨hv'.2, hn⟩
    · intro v _ w _ he
      exact Subtype.ext he
    · intro v hv
      have hv' : v ∈ crossingSet S u.val ∧
          v ∈ oppositeRows (originalRowsOn vertex G) c u.val := by
        simpa only [mem_inter] using hv
      have hn : v ∈ (Recovery.rowNeighbors (Recovery.graphMatrix
          (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G u)).map
          (Function.Embedding.subtype (· ∈ directionTargets c b)) := by
        rw [directionNeighbors_map vertex G keep c b u]
        exact hv'.2
      obtain ⟨w, hw, he⟩ := mem_map.mp hn
      change w.val = v at he
      refine ⟨w, ?_, he⟩
      simp only [directionCrossing, mem_filter]
      exact ⟨hw, he.symm ▸ hv'.1⟩
  · simpa only [card_map] using
      congrArg Finset.card (directionNeighbors_map vertex G keep c b u)

/-- Every supported successful cap exposes actual original neighbors of
cardinality at least h; subtype erasure preserves both facts. -/
theorem directionTree_supported_rows (vertex : U ↪ V) (G : SimpleInput V)
    (keep : Finset U) (c : U → Bool) (b : Bool) (h : ℕ) (hh : 10 ≤ h)
    (hdegree : ∀ u, h ≤ Recovery.fullDegrees
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G) u)
    (st : DirectionState keep c b)
    (hst : some st ∈ ((directionTree vertex keep c b h).eval G.toWeighted.cut).support) :
    ∀ u : directionSources keep c b, ∃ N,
      st.learned u = some N ∧ h ≤ N.card ∧
      N.map (Function.Embedding.subtype (· ∈ directionTargets c b)) ⊆ originalRowsOn vertex G u.val := by
  rw [directionTree_eval] at hst
  intro u
  obtain ⟨N,hN,hsize,htrue⟩ := Recovery.recoverTree_true_neighbors _ _
    (source_target_disjoint vertex keep c b) G h hh hdegree st hst u
  refine ⟨N,hN,hsize,?_⟩
  intro v hv
  obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
  apply (mem_originalRowsOn vertex G u.val w.val).mpr
  exact htrue w hw


theorem pair_expect_fst {A B : Type} (p : PMF A) (q : PMF B) (f : A → ℝ≥0∞) :
    expect (p.bind fun a => q.map fun b => (a,b)) (fun out => f out.1) = expect p f := by
  simp only [expect_bind, expect_map, expect_const]

theorem pair_expect_snd {A B : Type} (p : PMF A) (q : PMF B) (f : B → ℝ≥0∞) :
    expect (p.bind fun a => q.map fun b => (a,b)) (fun out => f out.2) = expect q f := by
  simp only [expect_bind, expect_map, expect_const]

theorem pair_mass_fst {A B : Type} (p : PMF A) (q : PMF B) (P : A → Prop) :
    mass (p.bind fun a => q.map fun b => (a,b)) (fun out => P out.1) = mass p P := by
  calc
    _ = expect (p.bind fun a => q.map fun b => (a,b))
        (fun out => if P out.1 then 1 else 0) := by
      simpa only [one_mul] using
        (expect_indicator (p.bind fun a => q.map fun b => (a,b))
          (fun out : A × B => P out.1) 1).symm
    _ = expect p (fun a => if P a then 1 else 0) :=
      pair_expect_fst p q (fun a => if P a then (1 : ℝ≥0∞) else 0)
    _ = _ := by simpa only [one_mul] using expect_indicator p P 1

theorem pair_mass_snd {A B : Type} (p : PMF A) (q : PMF B) (P : B → Prop) :
    mass (p.bind fun a => q.map fun b => (a,b)) (fun out => P out.2) = mass q P := by
  calc
    _ = expect (p.bind fun a => q.map fun b => (a,b))
        (fun out => if P out.2 then 1 else 0) := by
      simpa only [one_mul] using
        (expect_indicator (p.bind fun a => q.map fun b => (a,b))
          (fun out : A × B => P out.2) 1).symm
    _ = expect q (fun b => if P b then 1 else 0) :=
      pair_expect_snd p q (fun b => if P b then (1 : ℝ≥0∞) else 0)
    _ = _ := by simpa only [one_mul] using expect_indicator q P 1

/-- Each direction pays one hundredth of abort probability, separately from
all row mean/tail estimates. Both calls are the actual public capped programs. -/
theorem twoDirections_abort (vertex : U ↪ V) (G : SimpleInput V)
    (keep : Finset U) (c : U → Bool) (h : ℕ) (hh : 10 ≤ h)
    (hdegree : ∀ (b : Bool) (u : directionSources keep c b),
      h ≤ Recovery.fullDegrees
        (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G) u) :
    mass ((twoDirections vertex keep c h).eval G.toWeighted.cut) (fun out => out = none) ≤
      (2 / 100 : ℝ≥0∞) := by
  rw [twoDirections, RTree.eval_map, mass_map]
  simp_rw [combineDirections_none]
  calc
    _ ≤ mass ((rawDirections vertex keep c h).eval G.toWeighted.cut) (fun out => out.1 = none) +
        mass ((rawDirections vertex keep c h).eval G.toWeighted.cut) (fun out => out.2 = none) :=
      mass_or_le _ _ _
    _ = mass ((directionTree vertex keep c false h).eval G.toWeighted.cut) (fun out => out = none) +
        mass ((directionTree vertex keep c true h).eval G.toWeighted.cut) (fun out => out = none) := by
      rw [rawDirections_eval,
        pair_mass_fst ((directionTree vertex keep c false h).eval G.toWeighted.cut)
          ((directionTree vertex keep c true h).eval G.toWeighted.cut) (fun out => out = none),
        pair_mass_snd ((directionTree vertex keep c false h).eval G.toWeighted.cut)
          ((directionTree vertex keep c true h).eval G.toWeighted.cut) (fun out => out = none)]
    _ ≤ (100 : ℝ≥0∞)⁻¹ + (100 : ℝ≥0∞)⁻¹ := by
      rw [directionTree_eval, directionTree_eval]
      apply add_le_add
      · exact Recovery.recoverTree_abort_le _ _ (source_target_disjoint vertex keep c false)
          G h hh (hdegree false)
      · exact Recovery.recoverTree_abort_le _ _ (source_target_disjoint vertex keep c true)
          G h hh (hdegree true)
    _ = _ := by
      calc
        _ = ENNReal.ofReal ((1 / 100 : ℝ) + 1 / 100) := by
          have hone : ENNReal.ofReal (1 / 100 : ℝ) = (100 : ℝ≥0∞)⁻¹ := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num [one_div]
          rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
          simp only [hone]
        _ = _ := by
          rw [show (1 / 100 : ℝ) + 1 / 100 = 2 / 100 by norm_num,
            ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
          norm_num


abbrev DirectionIndex (keep : Finset U) (c : U → Bool) :=
  directionSources keep c false ⊕ directionSources keep c true

def pairBaseRatio (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) : DirectionIndex keep c → ℝ :=
  Sum.elim (fun u => rowFraction (oppositeRows (originalRowsOn vertex G) c) S u.val)
    (fun u => rowFraction (oppositeRows (originalRowsOn vertex G) c) S u.val)

def pairRatio (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) (out : RawDirectionPair keep c) : DirectionIndex keep c → ℝ :=
  Sum.elim
    (fun u => recoveredRatio u (directionCrossing vertex G S keep c false u) out.1)
    (fun u => recoveredRatio u (directionCrossing vertex G S keep c true u) out.2)

theorem pairBaseRatio_sum (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) :
    (∑ i, pairBaseRatio vertex G S keep c i) =
      ∑ u ∈ keep, rowFraction (oppositeRows (originalRowsOn vertex G) c) S u := by
  rw [Fintype.sum_sum_type]
  change (∑ u : directionSources keep c false,
      rowFraction (oppositeRows (originalRowsOn vertex G) c) S u.val) +
    (∑ u : directionSources keep c true,
      rowFraction (oppositeRows (originalRowsOn vertex G) c) S u.val) = _
  rw [sum_coe_sort, sum_coe_sort, ← sum_union (sources_disjoint keep c), sources_union]

/-- The sum ranges over BOTH directions before Markov is applied. The
only independence used is the explicit bind/map law of the two program calls. -/
theorem pairRatio_mean (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) (h : ℕ) (hh : 10 ≤ h)
    (hdegree : ∀ (b : Bool) (u : directionSources keep c b), h ≤ Recovery.fullDegrees
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G) u)
    (i : DirectionIndex keep c) :
    expect ((rawDirections vertex keep c h).eval G.toWeighted.cut)
      (fun out => ENNReal.ofReal (pairRatio vertex G S keep c out i)) ≤
      ENNReal.ofReal (pairBaseRatio vertex G S keep c i) := by
  rcases i with u | u
  · simp only [pairRatio, pairBaseRatio, Sum.elim_inl, rawDirections_eval]
    rw [pair_expect_fst ((directionTree vertex keep c false h).eval G.toWeighted.cut)
      ((directionTree vertex keep c true h).eval G.toWeighted.cut)
      (fun out => ENNReal.ofReal (recoveredRatio u
        (directionCrossing vertex G S keep c false u) out)), directionTree_eval]
    rw [← direction_baseRatio vertex G S keep c false u]
    exact recoveredRatio_mean _ _ (source_target_disjoint vertex keep c false) G h hh
      (hdegree false) u _ (directionCrossing_subset vertex G S keep c false u)
  · simp only [pairRatio, pairBaseRatio, Sum.elim_inr, rawDirections_eval]
    rw [pair_expect_snd ((directionTree vertex keep c false h).eval G.toWeighted.cut)
      ((directionTree vertex keep c true h).eval G.toWeighted.cut)
      (fun out => ENNReal.ofReal (recoveredRatio u
        (directionCrossing vertex G S keep c true u) out)), directionTree_eval]
    rw [← direction_baseRatio vertex G S keep c true u]
    exact recoveredRatio_mean _ _ (source_target_disjoint vertex keep c true) G h hh
      (hdegree true) u _ (directionCrossing_subset vertex G S keep c true u)

theorem pairRatio_tail (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) (h : ℕ) (hh : 10 ≤ h)
    (hdegree : ∀ (b : Bool) (u : directionSources keep c b), h ≤ Recovery.fullDegrees
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G) u)
    {alpha : ℝ} (hmax : ∀ u ∈ keep, rowFraction (oppositeRows (originalRowsOn vertex G) c) S u ≤ alpha)
    (i : DirectionIndex keep c) :
    mass ((rawDirections vertex keep c h).eval G.toWeighted.cut)
      (fun out => alpha + 1 / 10 < pairRatio vertex G S keep c out i) ≤
      200 * ENNReal.ofReal (pairBaseRatio vertex G S keep c i) / (h : ℝ≥0∞) := by
  have hm : pairBaseRatio vertex G S keep c i ≤ alpha := by
    rcases i with u | u
    · exact hmax u.val ((mem_directionSources keep c false u.val).mp u.property).1
    · exact hmax u.val ((mem_directionSources keep c true u.val).mp u.property).1
  apply le_trans (mass_mono _ (Q := fun out =>
    pairBaseRatio vertex G S keep c i + 1 / 10 < pairRatio vertex G S keep c out i) (fun out hout => by
      have hshift : pairBaseRatio vertex G S keep c i + (1 / 10 : ℝ) ≤ alpha + 1 / 10 := by
        linarith
      exact hshift.trans_lt hout))
  rcases i with u | u
  · simp only [pairRatio, pairBaseRatio, Sum.elim_inl, rawDirections_eval]
    rw [pair_mass_fst ((directionTree vertex keep c false h).eval G.toWeighted.cut)
      ((directionTree vertex keep c true h).eval G.toWeighted.cut)
      (fun out => rowFraction (oppositeRows (originalRowsOn vertex G) c) S u.val + 1 / 10 <
        recoveredRatio u (directionCrossing vertex G S keep c false u) out), directionTree_eval]
    rw [← direction_baseRatio vertex G S keep c false u]
    exact recoveredRatio_tail _ _ (source_target_disjoint vertex keep c false) G h hh
      (hdegree false) u _ (directionCrossing_subset vertex G S keep c false u)
  · simp only [pairRatio, pairBaseRatio, Sum.elim_inr, rawDirections_eval]
    rw [pair_mass_snd ((directionTree vertex keep c false h).eval G.toWeighted.cut)
      ((directionTree vertex keep c true h).eval G.toWeighted.cut)
      (fun out => rowFraction (oppositeRows (originalRowsOn vertex G) c) S u.val + 1 / 10 <
        recoveredRatio u (directionCrossing vertex G S keep c true u) out), directionTree_eval]
    rw [← direction_baseRatio vertex G S keep c true u]
    exact recoveredRatio_tail _ _ (source_target_disjoint vertex keep c true) G h hh
      (hdegree true) u _ (directionCrossing_subset vertex G S keep c true u)

/-- The actual combined recovery law has a single one-tenth Markov debit.
There is no multiplication of dependent row-success probabilities. -/
theorem rawDirections_ratio_failure (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) (h : ℕ) (hh : 10 ≤ h)
    (hdegree : ∀ (b : Bool) (u : directionSources keep c b), h ≤ Recovery.fullDegrees
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G) u)
    {alpha beta : ℝ} (hb : 0 < beta)
    (hmax : ∀ u ∈ keep, rowFraction (oppositeRows (originalRowsOn vertex G) c) S u ≤ alpha)
    (hsum : (∑ u ∈ keep, rowFraction (oppositeRows (originalRowsOn vertex G) c) S u) ≤ beta) :
    mass ((rawDirections vertex keep c h).eval G.toWeighted.cut)
      (fun out => ¬ ((∀ i, pairRatio vertex G S keep c out i ≤ alpha + 1 / 10) ∧
        (∑ i, pairRatio vertex G S keep c out i) ≤ 10 * beta)) ≤
      1 / 10 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  apply row_moment_failure_bound _ _ (pairBaseRatio vertex G S keep c) h hb
  · intro i
    rcases i with u | u <;> exact rowFraction_nonneg _ _ _
  · intro out i
    rcases i with u | u <;> exact recoveredRatio_nonneg _ _ _
  · rw [pairBaseRatio_sum]
    exact hsum
  · exact pairRatio_mean vertex G S keep c h hh hdegree
  · exact pairRatio_tail vertex G S keep c h hh hdegree hmax


/-- Statistical quality of the actual observed directional samples. Its
conversion to the explicit ambient row table uses true-neighbor support. -/
def recoveredQuality (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) (alpha beta : ℝ) (out : RawDirectionPair keep c) : Prop :=
  (∀ i, pairRatio vertex G S keep c out i ≤ alpha) ∧
    (∑ i, pairRatio vertex G S keep c out i) ≤ beta

def LearnedTranscript.quality (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (alpha beta : ℝ) (T : LearnedTranscript U) : Prop :=
  recoveredQuality vertex G S T.keep T.color alpha beta (some T.states.1, some T.states.2)

/-- The actual pair program is simultaneously non-aborting and good except
for the sum of the separate cap and statistical debits. -/
theorem twoDirections_quality_failure (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (keep : Finset U) (c : U → Bool) (h : ℕ) (hh : 10 ≤ h)
    (hdegree : ∀ (b : Bool) (u : directionSources keep c b), h ≤ Recovery.fullDegrees
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G) u)
    {alpha beta : ℝ} (hb : 0 < beta)
    (hmax : ∀ u ∈ keep, rowFraction (oppositeRows (originalRowsOn vertex G) c) S u ≤ alpha)
    (hsum : (∑ u ∈ keep, rowFraction (oppositeRows (originalRowsOn vertex G) c) S u) ≤ beta) :
    mass ((twoDirections vertex keep c h).eval G.toWeighted.cut)
      (fun out => ¬ out.elim False (fun st => recoveredQuality vertex G S keep c
        (alpha + 1 / 10) (10 * beta) (some st.1, some st.2))) ≤
      12 / 100 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  have habort := twoDirections_abort vertex G keep c h hh hdegree
  rw [twoDirections, RTree.eval_map, mass_map] at habort ⊢
  calc
    _ ≤ mass ((rawDirections vertex keep c h).eval G.toWeighted.cut)
        (fun raw => combineDirections raw = none ∨
          ¬ recoveredQuality vertex G S keep c (alpha + 1 / 10) (10 * beta) raw) := by
      apply mass_mono
      intro raw hraw
      rcases raw with ⟨a,b⟩
      cases a <;> cases b <;> simp_all [combineDirections]
    _ ≤ mass ((rawDirections vertex keep c h).eval G.toWeighted.cut)
          (fun raw => combineDirections raw = none) +
        mass ((rawDirections vertex keep c h).eval G.toWeighted.cut)
          (fun raw => ¬ recoveredQuality vertex G S keep c (alpha + 1 / 10) (10 * beta) raw) :=
      mass_or_le _ _ _
    _ ≤ 2 / 100 + (1 / 10 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞)) :=
      add_le_add habort (rawDirections_ratio_failure vertex G S keep c h hh hdegree hb hmax hsum)
    _ = _ := by
      have he : (2 / 100 : ℝ≥0∞) + 1 / 10 = 12 / 100 := by
        calc
          _ = ENNReal.ofReal ((2 / 100 : ℝ) + 1 / 10) := by
            rw [ENNReal.ofReal_add (by norm_num) (by norm_num),
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100),
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
            norm_num
          _ = _ := by
            rw [show (2 / 100 : ℝ) + 1 / 10 = 12 / 100 by norm_num,
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num
      rw [← add_assoc, he]

/-- The public omission guard is bounded jointly with color quality. It is
not inferred from a later small-number-of-zero-rows conclusion. -/
theorem color_guard_failure (N : U → Finset U) (S : Finset U) (h : ℕ) (hh : 35 ≤ h)
    (hloop : ∀ u, u ∉ N u) {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 < beta)
    (hgood : GoodRows alpha beta N S) :
    mass (colors (V := U)) (fun c => ¬ (GoodRows (alpha + 1 / 10) (10 * beta)
      (coloredRows h N c) S ∧ ((extraOmissions N h c).card : ℝ) ≤ (Fintype.card U : ℝ) / h)) ≤
      11 / 100 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  calc
    _ ≤ mass (colors (V := U)) (fun c =>
        ¬ GoodRows (alpha + 1 / 10) (10 * beta) (coloredRows h N c) S ∨
          (Fintype.card U : ℝ) / h < (extraOmissions N h c).card) := by
      apply mass_mono
      intro c hc
      by_contra hn
      apply hc
      constructor
      · by_contra hg
        exact hn (Or.inl hg)
      · by_contra he
        exact hn (Or.inr (lt_of_not_ge he))
    _ ≤ mass (colors (V := U)) (fun c =>
          ¬ GoodRows (alpha + 1 / 10) (10 * beta) (coloredRows h N c) S) +
        mass (colors (V := U)) (fun c => (Fintype.card U : ℝ) / h < (extraOmissions N h c).card) :=
      mass_or_le _ _ _
    _ ≤ (1 / 10 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞)) + 1 / 100 :=
      add_le_add (coloredRows_good_failure h N S hloop ha hb hgood)
        (extraOmissions_failure_le N h hh hloop)
    _ = _ := by
      have he : (1 / 10 : ℝ≥0∞) + 1 / 100 = 11 / 100 := by
        calc
          _ = ENNReal.ofReal ((1 / 10 : ℝ) + 1 / 100) := by
            rw [ENNReal.ofReal_add (by norm_num) (by norm_num),
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10),
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num
          _ = _ := by
            rw [show (1 / 10 : ℝ) + 1 / 100 = 11 / 100 by norm_num,
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num
      rw [add_right_comm, he]

theorem sum_omitted_fractions (keep : Finset U) (N : U → Finset U) (S : Finset U) :
    (∑ u, rowFraction (omitRows keep N) S u) = ∑ u ∈ keep, rowFraction N S u := by
  simp_rw [rowFraction_omit]
  rw [← sum_filter]
  simp

/-- Fixed-color correctness of the actual guarded two-direction recovery.
All source-degree premises are discharged by the actual measured keep test. -/
theorem recoverAfterColor_quality_failure (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (c : U → Bool) (h : ℕ) (hh : 35 ≤ h)
    {alpha beta : ℝ} (hb : 0 < beta)
    (hcolor : GoodRows (alpha + 1 / 10) (10 * beta)
      (coloredRows h (originalRowsOn vertex G) c) S)
    (hextra : ((extraOmissions (originalRowsOn vertex G) h c).card : ℝ) ≤
      (Fintype.card U : ℝ) / h) :
    mass ((recoverAfterColor vertex (fun u => (originalRowsOn vertex G u).card) c h
        ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut)).eval G.toWeighted.cut)
      (fun out => ¬ out.elim False (LearnedTranscript.quality vertex G S (alpha + 1 / 5) (100 * beta))) ≤
      12 / 100 + 2000 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  let keep := retainedRows h (fun u => (originalRowsOn vertex G u).card)
    ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut)
  have hguard : extraOmissionGuard h (fun u => (originalRowsOn vertex G u).card)
      ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut) := by
    simpa only [extraOmissionGuard, measuredExtraOmissions_unit] using hextra
  have hcolored : coloredRows h (originalRowsOn vertex G) c =
      omitRows keep (oppositeRows (originalRowsOn vertex G) c) := by
    dsimp [keep]
    rw [oppositeStatisticsOn_unit]
    rfl
  have hm : ∀ u ∈ keep, rowFraction (oppositeRows (originalRowsOn vertex G) c) S u ≤ alpha + 1 / 10 := by
    intro u hu
    have hx := hcolor.1 u
    rw [hcolored, rowFraction_omit, if_pos hu] at hx
    exact hx
  have hs : (∑ u ∈ keep, rowFraction (oppositeRows (originalRowsOn vertex G) c) S u) ≤ 10 * beta := by
    have hx := hcolor.2
    rw [hcolored, sum_omitted_fractions] at hx
    exact hx
  have hrec := twoDirections_quality_failure vertex G S keep c h (by omega)
    (retained_direction_degree vertex G c h) (by positivity : 0 < 10 * beta) hm hs
  have hα : alpha + 1 / 10 + 1 / 10 = alpha + 1 / 5 := by ring
  have hβ : 10 * (10 * beta) = 100 * beta := by ring
  rw [hα,hβ] at hrec
  rw [recoverAfterColor, if_pos hguard, RTree.eval_map, mass_map]
  have he : (fun out : Option (DirectionPair keep c) =>
      ¬ (out.map fun states => LearnedTranscript.mk c
        ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut) keep states).elim False
          (LearnedTranscript.quality vertex G S (alpha + 1 / 5) (100 * beta))) =
      fun out => ¬ out.elim False (fun st => recoveredQuality vertex G S keep c
        (alpha + 1 / 5) (100 * beta) (some st.1,some st.2)) := by
    funext out
    cases out <;> rfl
  change mass ((twoDirections vertex keep c h).eval G.toWeighted.cut) _ ≤ _
  rw [he]
  calc
    _ ≤ _ := hrec
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
      rw [← mul_assoc]
      norm_num

/-- Literal source probability debit for the actual public program and full
returned transcript. Conversion from these sample ratios to GoodRows and the
zero-row count is a separate support theorem, not an assumed success oracle. -/
theorem learnSubgraphProgram_quality_failure (vertex : U ↪ V) (G : SimpleInput V)
    (S : Finset U) (degree : U → ℕ) (h : ℕ) (hh : 35 ≤ h)
    (hdegree : degree = fun u => (originalRowsOn vertex G u).card)
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 < beta)
    (hgood : GoodRows alpha beta (originalRowsOn vertex G) S) :
    mass ((learnSubgraphProgram vertex degree h).eval G.toWeighted.cut)
      (fun out => ¬ out.elim False (LearnedTranscript.quality vertex G S (alpha + 1 / 5) (100 * beta))) ≤
      23 / 100 + 2200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  subst degree
  rw [learnSubgraphProgram_eval]
  have hc := color_guard_failure (originalRowsOn vertex G) S h hh
    (originalRowsOn_loopless vertex G) ha hb hgood
  have hm := mass_bind_le_add (colors (V := U))
    (fun c => (recoverAfterColor vertex (fun u => (originalRowsOn vertex G u).card) c h
      ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut)).eval G.toWeighted.cut)
    (fun c => ¬ (GoodRows (alpha + 1 / 10) (10 * beta)
      (coloredRows h (originalRowsOn vertex G) c) S ∧
        ((extraOmissions (originalRowsOn vertex G) h c).card : ℝ) ≤ (Fintype.card U : ℝ) / h))
    (fun out => ¬ out.elim False (LearnedTranscript.quality vertex G S (alpha + 1 / 5) (100 * beta)))
    hc (fun c hg => recoverAfterColor_quality_failure vertex G S c h hh hb
      (not_not.mp hg).1 (not_not.mp hg).2)
  apply hm.trans_eq
  calc
    (11 / 100 + 200 * ENNReal.ofReal beta / (h : ℝ≥0∞)) +
        (12 / 100 + 2000 * ENNReal.ofReal beta / (h : ℝ≥0∞)) =
      (11 / 100 + 12 / 100) +
        ((200 * ENNReal.ofReal beta + 2000 * ENNReal.ofReal beta) / (h : ℝ≥0∞)) := by
      rw [add_add_add_comm, ENNReal.add_div]
    _ = _ := by
      have he : (11 / 100 : ℝ≥0∞) + 12 / 100 = 23 / 100 := by
        calc
          _ = ENNReal.ofReal ((11 / 100 : ℝ) + 12 / 100) := by
            rw [ENNReal.ofReal_add (by norm_num) (by norm_num)]
            simp only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100),
              ENNReal.ofReal_ofNat]
          _ = _ := by
            rw [show (11 / 100 : ℝ) + 12 / 100 = 23 / 100 by norm_num,
              ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
            norm_num
      rw [he, ← add_mul]
      norm_num


@[simp] theorem combineDirections_some_iff {keep : Finset U} {c : U → Bool}
    (raw : RawDirectionPair keep c) (st : DirectionPair keep c) :
    combineDirections raw = some st ↔ raw = (some st.1,some st.2) := by
  rcases raw with ⟨a,b⟩
  rcases st with ⟨x,y⟩
  cases a <;> cases b <;> simp [combineDirections]

theorem pair_support_iff {A B : Type} (p : PMF A) (q : PMF B) (a : A) (b : B) :
    (a,b) ∈ (p.bind fun x => q.map fun y => (x,y)).support ↔ a ∈ p.support ∧ b ∈ q.support := by
  simp [PMF.mem_support_bind_iff, PMF.mem_support_map_iff, and_comm]

theorem twoDirections_supported (vertex : U ↪ V) (keep : Finset U) (c : U → Bool) (h : ℕ)
    (read : Finset V → ℝ) (st : DirectionPair keep c)
    (hst : some st ∈ ((twoDirections vertex keep c h).eval read).support) :
    some st.1 ∈ ((directionTree vertex keep c false h).eval read).support ∧
      some st.2 ∈ ((directionTree vertex keep c true h).eval read).support := by
  rw [twoDirections, RTree.eval_map] at hst
  obtain ⟨raw,hraw,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hst
  have heraw := (combineDirections_some_iff raw st).mp he
  rw [heraw,rawDirections_eval] at hraw
  exact (pair_support_iff _ _ _ _).mp hraw

theorem LearnedTranscript.rows_false (T : LearnedTranscript U)
    (u : directionSources T.keep T.color false) :
    T.rows u.val = ((T.states.1.learned u).getD ∅).map
      (Function.Embedding.subtype (· ∈ directionTargets T.color false)) := by
  simp only [LearnedTranscript.rows, dif_pos u.property]

theorem LearnedTranscript.rows_true (T : LearnedTranscript U)
    (u : directionSources T.keep T.color true) :
    T.rows u.val = ((T.states.2.learned u).getD ∅).map
      (Function.Embedding.subtype (· ∈ directionTargets T.color true)) := by
  have hn : u.val ∉ directionSources T.keep T.color false := by
    intro hf
    exact (disjoint_left.mp (sources_disjoint T.keep T.color)) hf u.property
  simp only [LearnedTranscript.rows, dif_neg hn, dif_pos u.property]

/-- Literal supported-output properties of the actual two recovery calls. -/
theorem transcript_supported_rows (vertex : U ↪ V) (G : SimpleInput V)
    (keep : Finset U) (c : U → Bool) (opposite : U → ℝ) (h : ℕ) (hh : 10 ≤ h)
    (hdegree : ∀ (b : Bool) (u : directionSources keep c b), h ≤ Recovery.fullDegrees
      (Recovery.graphMatrix (sourceEmbedding vertex keep c b) (targetEmbedding vertex c b) G) u)
    (st : DirectionPair keep c)
    (hst : some st ∈ ((twoDirections vertex keep c h).eval G.toWeighted.cut).support) :
    let T : LearnedTranscript U := ⟨c,opposite,keep,st⟩
    (∀ u, T.rows u ⊆ originalRowsOn vertex G u) ∧
      (∀ u ∈ keep, h ≤ (T.rows u).card) := by
  let T : LearnedTranscript U := ⟨c,opposite,keep,st⟩
  have hboth := twoDirections_supported vertex keep c h G.toWeighted.cut st hst
  have hfalse := directionTree_supported_rows vertex G keep c false h hh (hdegree false) st.1 hboth.1
  have htrue := directionTree_supported_rows vertex G keep c true h hh (hdegree true) st.2 hboth.2
  have hkept : ∀ u ∈ keep, h ≤ (T.rows u).card ∧ T.rows u ⊆ originalRowsOn vertex G u := by
    intro u hu
    cases hc : c u with
    | false =>
        let x : directionSources keep c false := ⟨u,(mem_directionSources keep c false u).mpr ⟨hu,hc⟩⟩
        obtain ⟨N,hN,hsize,hsub⟩ := hfalse x
        have he := T.rows_false x
        rw [hN,Option.getD_some] at he
        exact ⟨by rw [he,card_map]; exact hsize, he.symm ▸ hsub⟩
    | true =>
        let x : directionSources keep c true := ⟨u,(mem_directionSources keep c true u).mpr ⟨hu,hc⟩⟩
        obtain ⟨N,hN,hsize,hsub⟩ := htrue x
        have he := T.rows_true x
        rw [hN,Option.getD_some] at he
        exact ⟨by rw [he,card_map]; exact hsize, he.symm ▸ hsub⟩
  constructor
  · intro u
    by_cases hu : u ∈ keep
    · exact (hkept u hu).2
    · rw [T.rows_outside u hu]
      exact empty_subset _
  · intro u hu
    exact (hkept u hu).1


def DirectionIndex.vertex {keep : Finset U} {c : U → Bool} : DirectionIndex keep c → U :=
  Sum.elim Subtype.val Subtype.val

/-- The statistical ratio is the ratio of the actual returned ambient list.
The original graph enters only through its proved true-neighbor support. -/
theorem transcript_pairRatio (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (T : LearnedTranscript U) (htrue : ∀ u, T.rows u ⊆ originalRowsOn vertex G u)
    (i : DirectionIndex T.keep T.color) :
    pairRatio vertex G S T.keep T.color (some T.states.1,some T.states.2) i =
      rowFraction T.rows S i.vertex := by
  have ratio_map (b : Bool) (u : directionSources T.keep T.color b)
      (N : Finset (directionTargets T.color b))
      (hN : N ⊆ Recovery.rowNeighbors (Recovery.graphMatrix
        (sourceEmbedding vertex T.keep T.color b) (targetEmbedding vertex T.color b) G u)) :
      Probability.crossingRatio (directionCrossing vertex G S T.keep T.color b u) N =
        Probability.crossingRatio (crossingSet S u.val)
          (N.map (Function.Embedding.subtype (· ∈ directionTargets T.color b))) := by
    unfold Probability.crossingRatio
    apply congrArg₂ (fun a b : ℕ => (a : ℝ) / (b : ℝ))
    · apply Finset.card_bij (fun v _ => v.val)
      · intro v hv
        simp only [mem_inter, directionCrossing, mem_filter] at hv
        simp only [mem_inter, mem_map]
        exact ⟨hv.1.2, v, hv.2, rfl⟩
      · intro v _ w _ he
        exact Subtype.ext he
      · intro v hv
        simp only [mem_inter, mem_map] at hv
        obtain ⟨hc, w, hw, he⟩ := hv
        change w.val = v at he
        refine ⟨w, ?_, he⟩
        simp only [mem_inter, directionCrossing, mem_filter]
        exact ⟨⟨hN hw, he.symm ▸ hc⟩, hw⟩
    · simp only [card_map]
  rcases i with u | u
  · let N := (T.states.1.learned u).getD ∅
    have he : T.rows u.val = N.map
        (Function.Embedding.subtype (· ∈ directionTargets T.color false)) := T.rows_false u
    have hN : N ⊆ Recovery.rowNeighbors (Recovery.graphMatrix
        (sourceEmbedding vertex T.keep T.color false) (targetEmbedding vertex T.color false) G u) := by
      intro v hv
      have hm : v.val ∈ T.rows u.val := by
        rw [he]
        exact mem_map.mpr ⟨v,hv,rfl⟩
      have ht := (mem_originalRowsOn vertex G u.val v.val).mp (htrue u.val hm)
      simpa [Recovery.rowNeighbors, Recovery.graphMatrix, sourceEmbedding, targetEmbedding] using ht
    simp only [pairRatio,Sum.elim_inl,recoveredRatio_some,DirectionIndex.vertex]
    change Probability.crossingRatio (directionCrossing vertex G S T.keep T.color false u) N = _
    rw [rowFraction,he]
    exact ratio_map false u N hN
  · let N := (T.states.2.learned u).getD ∅
    have he : T.rows u.val = N.map
        (Function.Embedding.subtype (· ∈ directionTargets T.color true)) := T.rows_true u
    have hN : N ⊆ Recovery.rowNeighbors (Recovery.graphMatrix
        (sourceEmbedding vertex T.keep T.color true) (targetEmbedding vertex T.color true) G u) := by
      intro v hv
      have hm : v.val ∈ T.rows u.val := by
        rw [he]
        exact mem_map.mpr ⟨v,hv,rfl⟩
      have ht := (mem_originalRowsOn vertex G u.val v.val).mp (htrue u.val hm)
      simpa [Recovery.rowNeighbors, Recovery.graphMatrix, sourceEmbedding, targetEmbedding] using ht
    simp only [pairRatio,Sum.elim_inr,recoveredRatio_some,DirectionIndex.vertex]
    change Probability.crossingRatio (directionCrossing vertex G S T.keep T.color true u) N = _
    rw [rowFraction,he]
    exact ratio_map true u N hN

theorem transcript_quality_goodRows (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (T : LearnedTranscript U) (htrue : ∀ u, T.rows u ⊆ originalRowsOn vertex G u)
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hq : T.quality vertex G S alpha beta) :
    GoodRows alpha beta T.rows S := by
  constructor
  · intro u
    by_cases hu : u ∈ T.keep
    · cases hc : T.color u with
      | false =>
          let x : directionSources T.keep T.color false := ⟨u,by simp [hu,hc]⟩
          have hi := hq.1 (Sum.inl x)
          rw [transcript_pairRatio vertex G S T htrue] at hi
          exact hi
      | true =>
          let x : directionSources T.keep T.color true := ⟨u,by simp [hu,hc]⟩
          have hi := hq.1 (Sum.inr x)
          rw [transcript_pairRatio vertex G S T htrue] at hi
          exact hi
    · simpa [rowFraction,T.rows_outside u hu] using ha
  · have he : (∑ i, pairRatio vertex G S T.keep T.color (some T.states.1,some T.states.2) i) =
        ∑ u ∈ T.keep, rowFraction T.rows S u := by
      simp_rw [transcript_pairRatio vertex G S T htrue]
      rw [Fintype.sum_sum_type]
      change (∑ u : directionSources T.keep T.color false, rowFraction T.rows S u.val) +
        (∑ u : directionSources T.keep T.color true, rowFraction T.rows S u.val) = _
      rw [sum_coe_sort,sum_coe_sort,← sum_union (sources_disjoint T.keep T.color),sources_union]
    have hz : (∑ u ∈ T.keep, rowFraction T.rows S u) = ∑ u, rowFraction T.rows S u := by
      apply sum_subset (subset_univ _)
      intro u _ hu
      simp [rowFraction,T.rows_outside u hu]
    exact hz ▸ he ▸ hq.2

/-- Supported outputs of the public guard preserve exactly the measured
color/keep data and are supported successful outputs of the two actual calls. -/
theorem recoverAfterColor_supported (vertex : U ↪ V) (degree : U → ℕ) (c : U → Bool)
    (h : ℕ) (opposite : U → ℝ) (read : Finset V → ℝ) (T : LearnedTranscript U)
    (hT : some T ∈ ((recoverAfterColor vertex degree c h opposite).eval read).support) :
    extraOmissionGuard h degree opposite ∧ ∃ st : DirectionPair (retainedRows h degree opposite) c,
      some st ∈ ((twoDirections vertex (retainedRows h degree opposite) c h).eval read).support ∧
        T = ⟨c,opposite,retainedRows h degree opposite,st⟩ := by
  by_cases hg : extraOmissionGuard h degree opposite
  · rw [recoverAfterColor,if_pos hg,RTree.eval_map] at hT
    obtain ⟨out,hout,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hT
    cases out with
    | none => simp at he
    | some st =>
        simp only [Option.map_some,Option.some.injEq] at he
        exact ⟨hg,st,hout,he.symm⟩
  · simp [recoverAfterColor,hg] at hT

/-- Every successful supported output has actual neighbors of degree at
least h on retained rows. The omitted-row count uses one shared keep set. -/
theorem learnSubgraphProgram_output_spec (vertex : U ↪ V) (G : SimpleInput V)
    (degree : U → ℕ) (h : ℕ) (hh : 35 ≤ h)
    (hdegree : degree = fun u => (originalRowsOn vertex G u).card)
    (tau : ℕ) (hlow : (lowSources (originalRowsOn vertex G) h).card ≤ tau)
    (T : LearnedTranscript U)
    (hT : some T ∈ ((learnSubgraphProgram vertex degree h).eval G.toWeighted.cut).support) :
    (∀ u, T.rows u ⊆ originalRowsOn vertex G u) ∧
      (∀ u, T.rows u ≠ ∅ → h ≤ (T.rows u).card) ∧
      ((zeroSources T.rows).card : ℝ) ≤ tau + (Fintype.card U : ℝ) / h := by
  subst degree
  rw [learnSubgraphProgram_eval] at hT
  obtain ⟨c,_,hc⟩ := (PMF.mem_support_bind_iff _ _ _).mp hT
  obtain ⟨hg,st,hst,rfl⟩ := recoverAfterColor_supported vertex
    (fun u => (originalRowsOn vertex G u).card) c h _ G.toWeighted.cut T hc
  let keep := retainedRows h (fun u => (originalRowsOn vertex G u).card)
    ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut)
  let T : LearnedTranscript U := ⟨c,(oppositeStatisticsOn vertex c).eval G.toWeighted.cut,keep,st⟩
  have hrows := transcript_supported_rows vertex G keep c
    ((oppositeStatisticsOn vertex c).eval G.toWeighted.cut) h (by omega)
    (retained_direction_degree vertex G c h) st hst
  have htrue : ∀ u, T.rows u ⊆ originalRowsOn vertex G u := hrows.1
  have hsize : ∀ u ∈ keep, h ≤ (T.rows u).card := hrows.2
  have hz : zeroSources T.rows ⊆ zeroSources (coloredRows h (originalRowsOn vertex G) c) := by
    intro u hu
    have hu0 : T.rows u = ∅ := (mem_filter.mp hu).2
    have hnot : u ∉ keep := by
      intro hk
      have hs := hsize u hk
      rw [hu0,card_empty] at hs
      omega
    have he : coloredRows h (originalRowsOn vertex G) c =
        omitRows keep (oppositeRows (originalRowsOn vertex G) c) := by
      dsimp [keep]
      rw [oppositeStatisticsOn_unit]
      rfl
    apply mem_filter.mpr
    exact ⟨mem_univ _,by rw [he,omitRows_removed keep _ hnot]⟩
  have hextra : ((extraOmissions (originalRowsOn vertex G) h c).card : ℝ) ≤
      (Fintype.card U : ℝ) / h := by
    simpa only [extraOmissionGuard,measuredExtraOmissions_unit] using hg
  refine ⟨htrue,?_,?_⟩
  · intro u hne
    apply hsize
    by_contra hu
    exact hne (T.rows_outside u hu)
  · calc
      ((zeroSources T.rows).card : ℝ) ≤
          (zeroSources (coloredRows h (originalRowsOn vertex G) c)).card := by
        exact_mod_cast card_le_card hz
      _ ≤ _ := coloredRows_zero_real_le h (by omega) (originalRowsOn vertex G) c tau hlow hextra

def LearnedResult (vertex : U ↪ V) (G : SimpleInput V) (S : Finset U)
    (h tau : ℕ) (alpha beta : ℝ) (out : Option (LearnedTranscript U)) : Prop :=
  ∃ T, out = some T ∧ GoodRows alpha beta T.rows S ∧
    (∀ u, T.rows u ⊆ originalRowsOn vertex G u) ∧
    (∀ u, T.rows u ≠ ∅ → h ≤ (T.rows u).card) ∧
    ((zeroSources T.rows).card : ℝ) ≤ tau + (Fintype.card U : ℝ) / h

/-- Actual public LearnSubgraph: true recovered rows, the source's literal
23/100+2200β/h failure debit, and no assumption of any successful output. -/
theorem learnSubgraphProgram_failure (vertex : U ↪ V) (G : SimpleInput V)
    (S : Finset U) (degree : U → ℕ) (h tau : ℕ) (hh : 35 ≤ h)
    (hdegree : degree = fun u => (originalRowsOn vertex G u).card)
    (hlow : (lowSources (originalRowsOn vertex G) h).card ≤ tau)
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 < beta)
    (hgood : GoodRows alpha beta (originalRowsOn vertex G) S) :
    mass ((learnSubgraphProgram vertex degree h).eval G.toWeighted.cut)
      (fun out => ¬ LearnedResult vertex G S h tau (alpha + 1 / 5) (100 * beta) out) ≤
      23 / 100 + 2200 * ENNReal.ofReal beta / (h : ℝ≥0∞) := by
  apply le_trans (mass_mono_on_support _ ?_)
    (learnSubgraphProgram_quality_failure vertex G S degree h hh hdegree ha hb hgood)
  intro out hout hbad
  intro hq
  cases out with
  | none => exact hq
  | some T =>
      have hs := learnSubgraphProgram_output_spec vertex G degree h hh hdegree tau hlow T hout
      apply hbad
      refine ⟨T,rfl,?_,hs⟩
      exact transcript_quality_goodRows vertex G S T hs.1 (by linarith) hq

/-- The schedule h≥10000β pays the literal failure formula and leaves at
least one half success, uniformly for the actual original-cut program. -/
theorem learnSubgraphProgram_success_half (vertex : U ↪ V) (G : SimpleInput V)
    (S : Finset U) (degree : U → ℕ) (h tau : ℕ) (hh : 35 ≤ h)
    (hdegree : degree = fun u => (originalRowsOn vertex G u).card)
    (hlow : (lowSources (originalRowsOn vertex G) h).card ≤ tau)
    {alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 < beta)
    (hgood : GoodRows alpha beta (originalRowsOn vertex G) S)
    (hheight : 10000 * beta ≤ h) :
    (1 / 2 : ℝ) ≤ (mass ((learnSubgraphProgram vertex degree h).eval G.toWeighted.cut)
      (LearnedResult vertex G S h tau (alpha + 1 / 5) (100 * beta))).toReal := by
  have hfail := learnSubgraphProgram_failure vertex G S degree h tau hh hdegree hlow ha hb hgood
  have hhR : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
  have hfrac : 2200 * beta / (h : ℝ) ≤ 22 / 100 := by
    apply (div_le_iff₀ hhR).mpr
    nlinarith
  have hbound : (23 / 100 : ℝ≥0∞) + 2200 * ENNReal.ofReal beta / (h : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
    have he : (23 / 100 : ℝ≥0∞) + 2200 * ENNReal.ofReal beta / (h : ℝ≥0∞) =
        ENNReal.ofReal (23 / 100 + 2200 * beta / (h : ℝ)) := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 23 / 100) (by positivity),
        ENNReal.ofReal_div_of_pos hhR, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2200),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
      norm_num
    rw [he]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hs := success_of_failure_le _
    (LearnedResult vertex G S h tau (alpha + 1 / 5) (100 * beta))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (hfail.trans hbound)
  norm_num at hs ⊢
  exact hs


#print axioms direction_card_le
#print axioms sources_union
#print axioms source_target_disjoint
#print axioms rawDirections_eval
#print axioms oppositeStatisticsOn_eval
#print axioms learnSubgraphProgram_every_oracle
#print axioms learnSubgraphProgram_eval
#print axioms oppositeStatisticsOn_unit
#print axioms measuredExtraOmissions_unit
#print axioms pair_expect_fst
#print axioms pair_expect_snd
#print axioms pair_mass_fst
#print axioms pair_mass_snd
#print axioms twoDirections_abort
#print axioms pairBaseRatio_sum
#print axioms pairRatio_mean
#print axioms pairRatio_tail
#print axioms rawDirections_ratio_failure
#print axioms twoDirections_quality_failure
#print axioms color_guard_failure
#print axioms recoverAfterColor_quality_failure
#print axioms learnSubgraphProgram_quality_failure
#print axioms twoDirections_supported
#print axioms transcript_supported_rows
#print axioms transcript_pairRatio
#print axioms transcript_quality_goodRows
#print axioms learnSubgraphProgram_output_spec
#print axioms learnSubgraphProgram_failure
#print axioms learnSubgraphProgram_success_half
#print axioms directionNeighbors_map
#print axioms direction_fullDegrees
#print axioms retained_direction_degree
#print axioms direction_baseRatio
#print axioms directionTree_supported_rows

end
end CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph
