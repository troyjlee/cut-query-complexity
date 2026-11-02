import CutQueryComplexity.StarContraction2022.Certificates.Parallel.Queries
import CutQueryComplexity.StarContraction2022.Certificates.Parallel.Color
import CutQueryComplexity.StarContraction2022.Recovery.LearnBucket

/-! # Actual joint original-residual neighbor batches

Part of the parallel threshold certificate. The whole parallel C_P bound and
the capped certificate endpoint are in `Certificates/Parallel.lean`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical ENNReal

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
variable {π : PublicQuotient V Q} {r : ℕ}

theorem mapped_run {I A O P : Type} {b : ℕ}
    (tree : RTree I A O b) (f : O → P) (read : I → A) :
    RTree.run read (tree.map f) =
      (RTree.run read tree).map (fun out => (f out.1, out.2)) := by
  simp [RTree.map, RTree.run_bind, PMF.map, Function.comp_def]

theorem mapped_expected {I A O P : Type} {b : ℕ}
    (tree : RTree I A O b) (f : O → P) (read : I → A) :
    (tree.map f).expectedQueries read = tree.expectedQueries read := by
  change CutQueryComplexity.Probability.expect (RTree.run read (tree.map f))
    (fun out => (out.2 : ℝ≥0∞)) = _
  rw [mapped_run, CutQueryComplexity.Probability.expect_map]
  rfl

private theorem bind_expected_le {I A O P : Type} {b c : ℕ}
    (tree : RTree I A O b) (after : O → RTree I A P c) (read : I → A)
    (B : ℝ≥0∞) (hB : ∀ o, (after o).expectedQueries read ≤ B) :
    (tree.bind after).expectedQueries read ≤ tree.expectedQueries read + B := by
  change CutQueryComplexity.Probability.expect (RTree.run read (tree.bind after))
    (fun out => (out.2 : ℝ≥0∞)) ≤ _
  rw [RTree.run_bind, CutQueryComplexity.Probability.expect_bind]
  simp only [CutQueryComplexity.Probability.expect_map, Nat.cast_add,
    CutQueryComplexity.Probability.expect_add, CutQueryComplexity.Probability.expect_const]
  change tree.expectedQueries read +
      CutQueryComplexity.Probability.expect (RTree.run read tree)
        (fun out => (after out.1).expectedQueries read) ≤ tree.expectedQueries read + B
  exact add_le_add le_rfl
    (CutQueryComplexity.Probability.expect_le_of_le_on_support _ (fun out _ => hB out.1))

theorem bind_expected {I A O P : Type} {b c : ℕ}
    (tree : RTree I A O b) (after : O → RTree I A P c) (read : I → A) :
    (tree.bind after).expectedQueries read = tree.expectedQueries read +
      CutQueryComplexity.Probability.expect (tree.eval read)
        (fun o => (after o).expectedQueries read) := by
  change CutQueryComplexity.Probability.expect (RTree.run read (tree.bind after))
    (fun out => (out.2 : ℝ≥0∞)) = _
  rw [RTree.run_bind, CutQueryComplexity.Probability.expect_bind]
  simp only [CutQueryComplexity.Probability.expect_map, Nat.cast_add,
    CutQueryComplexity.Probability.expect_add, CutQueryComplexity.Probability.expect_const]
  simp only [RTree.eval, CutQueryComplexity.Probability.expect_map]
  rfl

theorem weaken_expected {I A O : Type} {b c : ℕ}
    (tree : RTree I A O b) (h : b ≤ c) (read : I → A) :
    (tree.weaken h).expectedQueries read = tree.expectedQueries read := by
  simp only [RTree.expectedQueries, RTree.run_weaken]

theorem cast_expected {I A O : Type} {b c : ℕ}
    (tree : RTree I A O b) (h : b = c) (read : I → A) :
    (tree.cast h).expectedQueries read = tree.expectedQueries read := by
  simp only [RTree.expectedQueries, RTree.run_cast]

theorem mixture_expected {I A O : Type} {b : ℕ}
    (trees : PMF (RTree I A O b)) (read : I → A) :
    (RTree.mix trees).expectedQueries read =
      CutQueryComplexity.Probability.expect trees (fun tree => tree.expectedQueries read) := by
  change CutQueryComplexity.Probability.expect (RTree.run read (RTree.mix trees))
    (fun out => (out.2 : ℝ≥0∞)) = _
  rw [RTree.run_mix, CutQueryComplexity.Probability.expect_bind]
  rfl

theorem pure_expected {I A O : Type} {b : ℕ}
    (p : PMF O) (read : I → A) :
    (RTree.pure (q := b) p).expectedQueries read = 0 := by
  change CutQueryComplexity.Probability.expect (RTree.run read (RTree.pure (q := b) p))
    (fun out => (out.2 : ℝ≥0∞)) = 0
  rw [RTree.run_pure, CutQueryComplexity.Probability.expect_map]
  simp only [Nat.cast_zero, CutQueryComplexity.Probability.expect_const]

namespace NeighborCollection

variable {I : Type} {b : ℕ}

def join (left right : V → Option V) (u : V) : Option V :=
  match left u with
  | none => right u
  | some v => some v

def Good (rows cols : Finset V) (edge : V → V → Prop) (next : V → Option V) : Prop :=
  (∀ u ∈ rows, ∃ v ∈ cols, next u = some v ∧ edge u v) ∧
    (∀ u ∉ rows, next u = none)

theorem good_join (A B cols : Finset V) (edge : V → V → Prop)
    (left right : V → Option V) (hl : Good A cols edge left) (hr : Good B cols edge right) :
    Good (A ∪ B) cols edge (join left right) := by
  constructor
  · intro u hu
    by_cases ha : u ∈ A
    · obtain ⟨v, hv, he, hedge⟩ := hl.1 u ha
      exact ⟨v, hv, by simp only [join, he], hedge⟩
    · have hb : u ∈ B := (Finset.mem_union.mp hu).resolve_left ha
      obtain ⟨v, hv, he, hedge⟩ := hr.1 u hb
      exact ⟨v, hv, by simp only [join, hl.2 u ha, he], hedge⟩
  · intro u hu
    have ha : u ∉ A := fun h => hu (Finset.mem_union_left B h)
    have hb : u ∉ B := fun h => hu (Finset.mem_union_right A h)
    simp only [join, hl.2 u ha, hr.2 u hb]

def rows (bucket : I → Finset V) : List I → Finset V
  | [] => ∅
  | i :: rest => bucket i ∪ rows bucket rest

theorem mem_rows (bucket : I → Finset V) (indices : List I) (u : V) :
    u ∈ rows bucket indices ↔ ∃ i ∈ indices, u ∈ bucket i := by
  induction indices with
  | nil => simp [rows]
  | cons i rest ih => simp [rows, ih]

theorem rows_toList [DecidableEq I] (bucket : I → Finset V) (indices : Finset I) :
    rows bucket indices.toList = indices.biUnion bucket := by
  ext u
  simp only [mem_rows, Finset.mem_toList, Finset.mem_biUnion]

def collect (call : I → RTree (Finset V) ℝ (Option (V → Option V)) b) :
    (indices : List I) →
      RTree (Finset V) ℝ (Option (V → Option V)) (indices.length * b)
  | [] => RTree.pure (PMF.pure (some (fun _ => none)))
  | i :: rest => ((call i).bind fun first => match first with
      | none => RTree.pure (PMF.pure none)
      | some first => (collect call rest).map (fun last => last.map (join first))).cast
        (by simp only [List.length_cons, Nat.succ_mul]; omega)

/-- Successful collection has a true neighbor for the union of the queried
buckets. This is proved from supported outputs of the actual calls. -/
theorem complete (call : I → RTree (Finset V) ℝ (Option (V → Option V)) b)
    (bucket : I → Finset V) (cols : Finset V) (edge : V → V → Prop)
    (read : Finset V → ℝ)
    (hcall : ∀ i next cost, (some next, cost) ∈ (RTree.run read (call i)).support →
      Good (bucket i) cols edge next)
    (indices : List I) (next : V → Option V) (cost : ℕ)
    (hout : (some next, cost) ∈ (RTree.run read (collect call indices)).support) :
    Good (rows bucket indices) cols edge next := by
  induction indices generalizing next cost with
  | nil =>
      have he : (some next, cost) = (some (fun _ => none), 0) := by
        simpa only [collect, RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] using hout
      have hn : next = (fun _ => none) := Option.some.inj (congrArg Prod.fst he)
      subst next
      exact ⟨by simp [rows], by simp⟩
  | cons i rest ih =>
      rw [collect, RTree.run_cast, RTree.run_bind] at hout
      obtain ⟨⟨first, c⟩, hfirst, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨⟨last, d⟩, hlast, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      have heLast : last = some next := congrArg Prod.fst he
      cases first with
      | none =>
          have hz : (last, d) = (none, 0) := by
            simpa only [RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] using hlast
          have hn := congrArg Prod.fst hz
          rw [heLast] at hn
          cases hn
      | some first =>
          rw [mapped_run] at hlast
          obtain ⟨⟨tail, e⟩, htail, heTail⟩ := (PMF.mem_support_map_iff _ _ _).mp hlast
          have ht : tail.map (join first) = some next :=
            (congrArg Prod.fst heTail).trans heLast
          cases tail with
          | none => cases ht
          | some tail =>
              have hn : join first tail = next := Option.some.inj ht
              rw [← hn]
              exact good_join _ _ cols edge first tail (hcall i first c hfirst) (ih tail e htail)

/-- Any explicit inner failure carries the lower bound on its own actual
query count through the whole collection. Prior queries only add cost. -/
theorem none_cost (call : I → RTree (Finset V) ℝ (Option (V → Option V)) b)
    (read : Finset V → ℝ) (fuel : ℕ)
    (hcall : ∀ i cost, (none, cost) ∈ (RTree.run read (call i)).support → fuel ≤ cost)
    (indices : List I) (cost : ℕ)
    (hout : (none, cost) ∈ (RTree.run read (collect call indices)).support) : fuel ≤ cost := by
  induction indices generalizing cost with
  | nil =>
      have he : ((none : Option (V → Option V)), cost) =
          (some (fun _ : V => (none : Option V)), 0) := by
        simpa only [collect, RTree.run_pure, PMF.pure_map, PMF.mem_support_pure_iff] using hout
      have hn := congrArg Prod.fst he
      cases hn
  | cons i rest ih =>
      rw [collect, RTree.run_cast, RTree.run_bind] at hout
      obtain ⟨⟨first, c⟩, hfirst, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨⟨last, d⟩, hlast, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      have heLast : last = none := congrArg Prod.fst he
      have heCost : c + d = cost := congrArg Prod.snd he
      cases first with
      | none =>
          have hc := hcall i c hfirst
          omega
      | some first =>
          rw [mapped_run] at hlast
          obtain ⟨⟨tail, e⟩, htail, heTail⟩ := (PMF.mem_support_map_iff _ _ _).mp hlast
          have ht : tail.map (join first) = none := (congrArg Prod.fst heTail).trans heLast
          have hed : e = d := congrArg Prod.snd heTail
          cases tail with
          | none =>
              have hc := ih e htail
              omega
          | some tail => cases ht

/-- Collection spends at most the sum of the expected costs of its actual
calls. Early failure can save queries; no independence of bucket outputs or
success events is assumed. -/
theorem expected_le_sum (call : I → RTree (Finset V) ℝ (Option (V → Option V)) b)
    (read : Finset V → ℝ) (indices : List I) :
    (collect call indices).expectedQueries read ≤
      (indices.map (fun i => (call i).expectedQueries read)).sum := by
  induction indices with
  | nil =>
      change CutQueryComplexity.Probability.expect (RTree.run read (collect call []))
        (fun out => (out.2 : ℝ≥0∞)) ≤ _
      simp only [collect, RTree.run_pure, PMF.pure_map,
        CutQueryComplexity.Probability.expect_pure, List.map_nil, List.sum_nil,
        Nat.cast_zero, le_refl]
  | cons i rest ih =>
      let after : Option (V → Option V) →
          RTree (Finset V) ℝ (Option (V → Option V)) (rest.length * b) := fun first =>
        match first with
        | none => RTree.pure (PMF.pure none)
        | some first => (collect call rest).map (fun last => last.map (join first))
      have hafter : ∀ first, (after first).expectedQueries read ≤
          (rest.map (fun i => (call i).expectedQueries read)).sum := by
        intro first
        cases first with
        | none =>
            change CutQueryComplexity.Probability.expect
              (RTree.run read (RTree.pure (q := rest.length * b) (PMF.pure none)))
              (fun out : Option (V → Option V) × ℕ => (out.2 : ℝ≥0∞)) ≤ _
            simp only [RTree.run_pure, PMF.pure_map,
              CutQueryComplexity.Probability.expect_pure, Nat.cast_zero]
            exact bot_le
        | some first =>
            change ((collect call rest).map (fun last => last.map (join first))).expectedQueries read ≤ _
            rw [mapped_expected]
            exact ih
      have hb := bind_expected_le (call i) after read _ hafter
      simpa only [collect, RTree.expectedQueries, RTree.run_cast,
        List.map_cons, List.sum_cons] using hb

end NeighborCollection

namespace ParallelState

/-- Select an original neighbor from an actually returned finite set.
Missing and empty returned rows stay explicit; no hidden graph is inspected. -/
def learnedSetNext (rows cols : Finset V) (table : rows → Option (Finset cols))
    (u : V) : Option V :=
  if hu : u ∈ rows then (table ⟨u, hu⟩).bind fun N =>
    if hN : N.Nonempty then some (Classical.choose hN).val else none
  else none

theorem learnedSetNext_outside (rows cols : Finset V)
    (table : rows → Option (Finset cols)) {u : V} (hu : u ∉ rows) :
    learnedSetNext rows cols table u = none := by
  simp only [learnedSetNext, dif_neg hu]

theorem learnedSetNext_present (rows cols : Finset V)
    (table : rows → Option (Finset cols)) (u : rows) (N : Finset cols)
    (hN : table u = some N) (hne : N.Nonempty) :
    ∃ v : cols, v ∈ N ∧ learnedSetNext rows cols table u.val = some v.val := by
  refine ⟨Classical.choose hne, Classical.choose_spec hne, ?_⟩
  simp only [learnedSetNext, dif_pos u.property, hN, Option.bind, dif_pos hne]

/-- Public finite clock for a single actual high-degree recovery call.
The expected-cost proof must use B's sharp m log(n)/log(m) bound instead. -/
def highBucketBudget (rows cols : Finset V) (T : ℕ) : ℕ :=
  T * Recovery.bucketRoundBudget rows cols * 3

/-- The public finite recovery call for one set of queried rows. Only the
original residual table is Boolean; quotient capacities are never queried as
Boolean entries. A failed finite completion remains an explicit `none`. -/
def selectedBucketNeighbors (s : ParallelState π r) (rows cols : Finset V)
    (radius T : ℕ) : RTree (Finset V) ℝ (Option (V → Option V))
      (highBucketBudget rows cols T) :=
  if rows = ∅ then RTree.pure (PMF.pure (some (fun _ => none)))
  else (s.simulateResidual (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ cols))
    (Recovery.learnBucketRounds radius 10 T Recovery.BucketState.initial)).map
      (fun out => if out.complete then some (learnedSetNext rows cols out.learned) else none)

theorem selectedBucketNeighbors_empty (s : ParallelState π r) (cols : Finset V)
    (radius T : ℕ) (read : Finset V → ℝ) :
    RTree.run read (s.selectedBucketNeighbors ∅ cols radius T) =
      PMF.pure (some (fun _ => none), 0) := by
  simp [selectedBucketNeighbors, highBucketBudget, RTree.run_pure, PMF.pure_map]

/-- Exact distributional simulation, including the factor of three in the
actual original-cut query count. -/
theorem selectedBucketNeighbors_honest_run (s : ParallelState π r)
    (rows cols : Finset V) (radius T : ℕ) (hne : rows ≠ ∅)
    (hdis : ∀ u : rows, ∀ v : cols, u.val ≠ v.val)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    RTree.run G.toWeighted.cut (s.selectedBucketNeighbors rows cols radius T) =
      (RTree.run (fun q => (Recovery.bilinear
        (s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
          (Function.Embedding.subtype (· ∈ cols)) G) q : ℝ))
        (Recovery.learnBucketRounds radius 10 T Recovery.BucketState.initial)).map
          (fun out =>
            (if out.1.complete then some (learnedSetNext rows cols out.1.learned) else none,
              out.2 * 3)) := by
  simp only [selectedBucketNeighbors, if_neg hne]
  change RTree.run G.toWeighted.cut
      ((s.simulateResidual (Function.Embedding.subtype (· ∈ rows))
        (Function.Embedding.subtype (· ∈ cols))
        (Recovery.learnBucketRounds radius 10 T Recovery.BucketState.initial)).map
          (fun out => if out.complete then some (learnedSetNext rows cols out.learned) else none)) = _
  rw [mapped_run, s.simulateResidual_honest _ _ hdis _ G hs]
  simp only [PMF.map_comp, Function.comp_def]

/-- Every reported completed table supplies a true original residual
neighbor for each requested row, with no assertion that a finite run must
complete. This theorem requires no degree promise. -/
theorem selectedBucketNeighbors_complete (s : ParallelState π r)
    (rows cols : Finset V) (radius T : ℕ)
    (hdis : ∀ u : rows, ∀ v : cols, u.val ≠ v.val)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (next : V → Option V) (cost : ℕ)
    (hout : (some next, cost) ∈
      (RTree.run G.toWeighted.cut (s.selectedBucketNeighbors rows cols radius T)).support) :
    (∀ u ∈ rows, ∃ v ∈ cols, next u = some v ∧
      0 < (G.toWeighted.subtract s.usedGraph).w u v) ∧
      (∀ u ∉ rows, next u = none) := by
  by_cases hne : rows = ∅
  · subst rows
    rw [s.selectedBucketNeighbors_empty] at hout
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    have heNext : next = (fun _ => none) := Option.some.inj (congrArg Prod.fst he)
    subst next
    exact ⟨by simp, by simp⟩
  · rw [s.selectedBucketNeighbors_honest_run rows cols radius T hne hdis G hs] at hout
    obtain ⟨out, hrun, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    have heOut := congrArg Prod.fst he
    dsimp only at heOut
    have hc : out.1.complete := by
      by_contra hc
      simp only [if_neg hc] at heOut
      cases heOut
    have hnext : learnedSetNext rows cols out.1.learned = next :=
      Option.some.inj (by simpa only [if_pos hc] using heOut)
    have hlearn := Recovery.learnBucketRounds_completed_correct _ radius 10 T hrun hc
    constructor
    · intro u hu
      obtain ⟨N, hN, hcard, htrue⟩ := hlearn ⟨u, hu⟩
      have hNne : N.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v, hv, heV⟩ := learnedSetNext_present rows cols out.1.learned ⟨u, hu⟩ N hN hNne
      refine ⟨v.val, v.property, ?_, ?_⟩
      · simpa only [hnext] using heV
      · have hp := htrue v hv
        change decide (0 < (G.toWeighted.subtract s.usedGraph).w u v.val) = true at hp
        exact of_decide_eq_true hp
    · intro u hu
      rw [← hnext]
      exact learnedSetNext_outside rows cols out.1.learned hu

/-- An honest unfinished inner recovery run cannot hide beneath its fuel:
each of its T nonterminal rounds spent a virtual query, and each virtual query
is exactly three original cuts. This does not depend on a tail estimate. -/
theorem selectedBucketNeighbors_none_cost (s : ParallelState π r)
    (rows cols : Finset V) (radius T : ℕ)
    (hdis : ∀ u : rows, ∀ v : cols, u.val ≠ v.val)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (cost : ℕ)
    (hout : (none, cost) ∈
      (RTree.run G.toWeighted.cut (s.selectedBucketNeighbors rows cols radius T)).support) :
    3 * T ≤ cost := by
  by_cases hne : rows = ∅
  · subst rows
    rw [s.selectedBucketNeighbors_empty] at hout
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    have hn := congrArg Prod.fst he
    cases hn
  · rw [s.selectedBucketNeighbors_honest_run rows cols radius T hne hdis G hs] at hout
    obtain ⟨out, hrun, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    have heOut := congrArg Prod.fst he
    have heCost := congrArg Prod.snd he
    dsimp only at heOut heCost
    have hc : ¬out.1.complete := by
      intro hc
      simp only [if_pos hc] at heOut
      cases heOut
    obtain ⟨hf, _, hprogress⟩ :=
      Recovery.learnBucketRounds_progress _ radius 10 T Recovery.BucketState.initial rfl hrun
    have hp : out.1.pending.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hz => hc ⟨hf, hz⟩
    have hT := hprogress hp
    omega

/-- The actual original-query cost retains B's sharp joint row denominator.
This internal stage lemma will be applied to the degrees already queried by
`colorRows`, rather than exposed as a premise of the final P theorem. -/
theorem selectedBucketNeighbors_expected (s : ParallelState π r)
    (rows cols : Finset V) (radius T : ℕ)
    (hdis : ∀ u : rows, ∀ v : cols, u.val ≠ v.val)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hradius : 10 ≤ radius) (hm : 1 ≤ rows.card) (hn : 1 ≤ cols.card)
    (hdegree : ∀ u : rows,
      radius ≤ Recovery.sampleCount
        (s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
          (Function.Embedding.subtype (· ∈ cols)) G u) Finset.univ ∧
      Recovery.sampleCount
        (s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
          (Function.Embedding.subtype (· ∈ cols)) G u) Finset.univ ≤ 2 * radius) :
    (s.selectedBucketNeighbors rows cols radius T).expectedQueries G.toWeighted.cut ≤
      3 * ENNReal.ofReal (Recovery.bucketExpectedBound rows cols 10) := by
  have hne : rows ≠ ∅ := by intro he; simp only [he, Finset.card_empty] at hm; omega
  simp only [selectedBucketNeighbors, if_neg hne]
  change ((s.simulateResidual (Function.Embedding.subtype (· ∈ rows))
      (Function.Embedding.subtype (· ∈ cols))
      (Recovery.learnBucketRounds radius 10 T Recovery.BucketState.initial)).map
        (fun out => if out.complete then some (learnedSetNext rows cols out.learned) else none)).expectedQueries
      G.toWeighted.cut ≤ _
  rw [mapped_expected, s.simulateResidual_expected]
  have he : (fun q => (s.residualBilinearCall
      (Function.Embedding.subtype (· ∈ rows)) (Function.Embedding.subtype (· ∈ cols)) q).eval
      G.toWeighted.cut) =
      (fun q => (Recovery.bilinear
        (s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
          (Function.Embedding.subtype (· ∈ cols)) G) q : ℝ)) :=
    funext (s.residualBilinearCall_honest _ _ hdis G hs)
  rw [he]
  have hbound := Recovery.learnBucketRounds_expected_bound
    (s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
      (Function.Embedding.subtype (· ∈ cols)) G)
    radius 10 T (by omega) hradius
    (by simpa only [Fintype.card_coe] using hm)
    (by simpa only [Fintype.card_coe] using hn) hdegree
  exact mul_le_mul le_rfl hbound bot_le bot_le

/-- Query the original residual through the actual finite degree-bucket
primitive, then select from its returned neighbor sets. All inputs precede G;
the degree partition is the one computed from preceding count answers.
The empty-row branch makes no query. -/
def highBucketNeighbors (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) (i T : ℕ) :
    RTree (Finset V) ℝ (Option (V → Option V))
      (highBucketBudget (highColorRows (π := π) color reps answers i)
        (blueVertices (π := π) color) T) :=
  s.selectedBucketNeighbors (highColorRows (π := π) color reps answers i)
    (blueVertices (π := π) color) (10 * 2 ^ i) T

theorem highBucketNeighbors_every_oracle (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (answers : V → Option (Fin (Fintype.card V + 1))) (i T : ℕ)
    (read : Finset V → ℝ) {out : Option (V → Option V) × ℕ}
    (hout : out ∈ (RTree.run read (s.highBucketNeighbors color reps answers i T)).support) :
    out.2 ≤ highBucketBudget (highColorRows (π := π) color reps answers i)
      (blueVertices (π := π) color) T := RTree.cost_le _ _ hout

theorem highBucketNeighbors_empty (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (answers : V → Option (Fin (Fintype.card V + 1))) (i T : ℕ)
    (hrows : highColorRows (π := π) color reps answers i = ∅) (read : Finset V → ℝ) :
    RTree.run read (s.highBucketNeighbors color reps answers i T) =
      PMF.pure (some (fun _ => none), 0) := by
  unfold highBucketNeighbors
  dsimp only [highBucketBudget]
  rw [hrows]
  exact s.selectedBucketNeighbors_empty _ _ _ _

theorem highColorRows_separate (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) (i : ℕ)
    (u : highColorRows (π := π) color reps answers i)
    (v : blueVertices (π := π) color) : u.val ≠ v.val := by
  intro he
  have ht := (highColorRows_red color reps answers i u.property).2
  have hf := (Finset.mem_filter.mp v.property).2
  rw [he, hf] at ht
  cases ht

/-- Query-selected high-degree recovery has no under-fuel honest failure. -/
theorem highBucketNeighbors_none_cost (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (answers : V → Option (Fin (Fintype.card V + 1))) (i T : ℕ)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (cost : ℕ)
    (hout : (none, cost) ∈
      (RTree.run G.toWeighted.cut (s.highBucketNeighbors color reps answers i T)).support) :
    3 * T ≤ cost :=
  s.selectedBucketNeighbors_none_cost _ _ _ _
    (highColorRows_separate color reps answers i) G hs cost hout

theorem highBucketNeighbors_complete (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (answers : V → Option (Fin (Fintype.card V + 1))) (i T : ℕ)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (next : V → Option V) (cost : ℕ)
    (hout : (some next, cost) ∈
      (RTree.run G.toWeighted.cut (s.highBucketNeighbors color reps answers i T)).support) :
    (∀ u ∈ highColorRows (π := π) color reps answers i,
      ∃ v ∈ blueVertices (π := π) color,
        next u = some v ∧ 0 < (G.toWeighted.subtract s.usedGraph).w u v) ∧
      (∀ u ∉ highColorRows (π := π) color reps answers i, next u = none) :=
  s.selectedBucketNeighbors_complete _ _ _ _
    (highColorRows_separate color reps answers i) G hs next cost hout

/-- Every degree hypothesis of B follows from the preceding actual count
answers. The endpoint alphabet remains original vertices, and the logarithmic
denominator is the size of this very bucket. -/
theorem highBucketNeighbors_expected (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (i T : ℕ) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hm : 1 ≤ (highColorRows (π := π) color reps
      ((s.colorRows color reps).eval G.toWeighted.cut) i).card) :
    (s.highBucketNeighbors color reps ((s.colorRows color reps).eval G.toWeighted.cut) i T).expectedQueries
      G.toWeighted.cut ≤
        3 * ENNReal.ofReal (Recovery.bucketExpectedBound
          (highColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut) i)
          (blueVertices (π := π) color) 10) := by
  let rows := highColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut) i
  let cols := blueVertices (π := π) color
  let M := s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ cols)) G
  have hdegree : ∀ u : rows, 10 * 2 ^ i ≤ Recovery.sampleCount (M u) Finset.univ ∧
      Recovery.sampleCount (M u) Finset.univ ≤ 2 * (10 * 2 ^ i) := by
    intro u
    simpa only [Recovery.sampleCount, Recovery.measure, Recovery.rowVector] using
      s.highColorRows_degree color reps i G hs u
  have hpow : 0 < (2 : ℕ) ^ i := pow_pos (by norm_num) _
  have hradius : 10 ≤ 10 * 2 ^ i := by omega
  have hm' : 1 ≤ rows.card := hm
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < rows.card by omega)
  have hcols : 1 ≤ cols.card := by
    have hlo := (hdegree ⟨u, hu⟩).1
    have hhi := Recovery.sampleCount_le_card (M ⟨u, hu⟩) Finset.univ
    simp only [Finset.card_univ, Fintype.card_coe] at hhi
    omega
  exact s.selectedBucketNeighbors_expected rows cols (10 * 2 ^ i) T
    (highColorRows_separate color reps _ i) G hs hradius hm hcols hdegree

/-- Low-degree recovery returns a table without changing any forest. This
keeps its residual identical to the one used by every high-degree bucket. -/
def lowBucketNeighbors (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) :
    DTree (Finset V) ℝ (Option (V → Option V))
      (lowRowUpdateBudget (lowColorRows (π := π) color reps answers)
        (blueVertices (π := π) color)) :=
  let rows := lowColorRows (π := π) color reps answers
  let cols := blueVertices (π := π) color
  (s.checkedLowDegreeResidual (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ cols))).map
      (fun out => out.map (learnedNext rows cols))

theorem lowBucketNeighbors_honest (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    let rows := lowColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut)
    let cols := blueVertices (π := π) color
    (s.lowBucketNeighbors color reps ((s.colorRows color reps).eval G.toWeighted.cut)).eval
      G.toWeighted.cut = some (learnedNext rows cols
        (s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
          (Function.Embedding.subtype (· ∈ cols)) G)) := by
  dsimp only
  have hdis : ∀ u : lowColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut),
      ∀ v : blueVertices (π := π) color, u.val ≠ v.val := by
    intro u v he
    have ht := (lowColorRows_red color reps _ u.property).2
    have hf := (Finset.mem_filter.mp v.property).2
    rw [he, hf] at ht
    cases ht
  let rows := lowColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut)
  let cols := blueVertices (π := π) color
  change ((s.checkedLowDegreeResidual (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ cols))).map
      (fun out => out.map (learnedNext rows cols))).eval G.toWeighted.cut = _
  rw [DTree.eval_map,
    s.checkedLowDegreeResidual_correct _ _ hdis G hs (s.lowColorRows_degree color reps G hs)]
  rfl

theorem lowBucketNeighbors_complete (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (next : V → Option V)
    (hout : (s.lowBucketNeighbors color reps ((s.colorRows color reps).eval G.toWeighted.cut)).eval
      G.toWeighted.cut = some next) :
    NeighborCollection.Good
      (lowColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut))
      (blueVertices (π := π) color)
      (fun u v => 0 < (G.toWeighted.subtract s.usedGraph).w u v) next := by
  let rows := lowColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut)
  let cols := blueVertices (π := π) color
  let M := s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ cols)) G
  have hn : learnedNext rows cols M = next :=
    Option.some.inj ((s.lowBucketNeighbors_honest color reps G hs).symm.trans hout)
  rw [← hn]
  constructor
  · intro u hu
    obtain ⟨v, hv⟩ := s.learnedNext_residual_complete rows cols G hu
      (s.lowColorRows_positive color reps G hs hu)
    have hp := s.learnedNext_residual_some rows cols G hv
    exact ⟨v, hp.2.1, hv, hp.2.2⟩
  · intro u hu
    change u ∉ rows at hu
    simp only [learnedNext, dif_neg hu]

/-- A deliberately loose finite index, used solely to type the finite query
tree. All subsequent expected-cost bounds use actual bucket costs. -/
def oneBucketBudget (V : Type) [Fintype V] (T : ℕ) : ℕ :=
  (T + 1) * (3 * Fintype.card V + 3 * Fintype.card V * Fintype.card V)

theorem highBucketBudget_le (rows cols : Finset V) (T : ℕ) :
    highBucketBudget rows cols T ≤ oneBucketBudget V T := by
  have hm : Fintype.card rows ≤ Fintype.card V := Fintype.card_subtype_le _
  have hn : Fintype.card cols ≤ Fintype.card V := Fintype.card_subtype_le _
  have hb : Recovery.bucketRoundBudget rows cols ≤
      Fintype.card V + Fintype.card V * Fintype.card V :=
    Nat.add_le_add hm (Nat.mul_le_mul hm hn)
  have hh := Nat.mul_le_mul_right 3 (Nat.mul_le_mul_left T hb)
  unfold highBucketBudget oneBucketBudget
  apply hh.trans
  nlinarith

theorem lowBucketBudget_le (rows cols : Finset V) (T : ℕ) :
    lowRowUpdateBudget rows cols ≤ oneBucketBudget V T := by
  apply (lowRowUpdateBudget_le rows cols).trans
  unfold oneBucketBudget
  simpa only [one_mul] using Nat.mul_le_mul_right
    (3 * Fintype.card V + 3 * Fintype.card V * Fintype.card V)
    (show 1 ≤ T + 1 by omega)

/-- One call for the actual queried partition. `none` is the low bucket;
`some i` is the dyadic high bucket. No call mutates the common residual state. -/
def bucketCall (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) (T : ℕ) :
    Option (Fin (highBucketCount (Fintype.card V))) →
      RTree (Finset V) ℝ (Option (V → Option V)) (oneBucketBudget V T)
  | none => (RTree.ofDeterministic (s.lowBucketNeighbors color reps answers)).weaken
      (lowBucketBudget_le _ _ T)
  | some i => (s.highBucketNeighbors color reps answers i.val T).weaken
      (highBucketBudget_le _ _ T)

theorem bucketCall_complete (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (T : ℕ) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (i : Option (Fin (highBucketCount (Fintype.card V)))) (next : V → Option V) (cost : ℕ)
    (hout : (some next, cost) ∈ (RTree.run G.toWeighted.cut
      (s.bucketCall color reps ((s.colorRows color reps).eval G.toWeighted.cut) T i)).support) :
    NeighborCollection.Good
      (colorBucket (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut) i)
      (blueVertices (π := π) color)
      (fun u v => 0 < (G.toWeighted.subtract s.usedGraph).w u v) next := by
  cases i with
  | none =>
      rw [bucketCall, RTree.run_weaken, RTree.run_ofDeterministic] at hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      exact s.lowBucketNeighbors_complete color reps G hs next (congrArg Prod.fst he).symm
  | some i =>
      rw [bucketCall, RTree.run_weaken] at hout
      exact s.highBucketNeighbors_complete color reps _ i.val T G hs next cost hout

theorem bucketCall_none_cost (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (T : ℕ) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (i : Option (Fin (highBucketCount (Fintype.card V)))) (cost : ℕ)
    (hout : (none, cost) ∈ (RTree.run G.toWeighted.cut
      (s.bucketCall color reps ((s.colorRows color reps).eval G.toWeighted.cut) T i)).support) :
    3 * T ≤ cost := by
  cases i with
  | none =>
      rw [bucketCall, RTree.run_weaken, RTree.run_ofDeterministic] at hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      have hn := congrArg Prod.fst he
      change none = (s.lowBucketNeighbors color reps
        ((s.colorRows color reps).eval G.toWeighted.cut)).eval G.toWeighted.cut at hn
      rw [s.lowBucketNeighbors_honest color reps G hs] at hn
      cases hn
  | some i =>
      rw [bucketCall, RTree.run_weaken] at hout
      exact s.highBucketNeighbors_none_cost color reps _ i.val T G hs cost hout

def jointBucketNeighbors (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) (T : ℕ) :
    RTree (Finset V) ℝ (Option (V → Option V))
      ((Finset.univ.toList : List (Option (Fin (highBucketCount (Fintype.card V))))).length *
        oneBucketBudget V T) :=
  NeighborCollection.collect (s.bucketCall color reps answers T) Finset.univ.toList

theorem jointBucketNeighbors_complete (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (T : ℕ) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (next : V → Option V) (cost : ℕ)
    (hout : (some next, cost) ∈ (RTree.run G.toWeighted.cut
      (s.jointBucketNeighbors color reps ((s.colorRows color reps).eval G.toWeighted.cut) T)).support) :
    NeighborCollection.Good
      (positiveColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut))
      (blueVertices (π := π) color)
      (fun u v => 0 < (G.toWeighted.subtract s.usedGraph).w u v) next := by
  have hh := NeighborCollection.complete
    (s.bucketCall color reps ((s.colorRows color reps).eval G.toWeighted.cut) T)
    (colorBucket (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut))
    (blueVertices (π := π) color)
    (fun u v => 0 < (G.toWeighted.subtract s.usedGraph).w u v) G.toWeighted.cut
    (s.bucketCall_complete color reps T G hs) Finset.univ.toList next cost hout
  rw [NeighborCollection.rows_toList, colorBucket_union] at hh
  exact hh

theorem jointBucketNeighbors_none_cost (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (T : ℕ) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (cost : ℕ) (hout : (none, cost) ∈ (RTree.run G.toWeighted.cut
      (s.jointBucketNeighbors color reps ((s.colorRows color reps).eval G.toWeighted.cut) T)).support) :
    3 * T ≤ cost :=
  NeighborCollection.none_cost
    (s.bucketCall color reps ((s.colorRows color reps).eval G.toWeighted.cut) T)
    G.toWeighted.cut (3 * T) (s.bucketCall_none_cost color reps T G hs)
    Finset.univ.toList cost hout

theorem jointBucketNeighbors_expected_le_sum (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (answers : V → Option (Fin (Fintype.card V + 1))) (T : ℕ)
    (read : Finset V → ℝ) :
    (s.jointBucketNeighbors color reps answers T).expectedQueries read ≤
      ((Finset.univ.toList : List (Option (Fin (highBucketCount (Fintype.card V))))).map
        (fun i => (s.bucketCall color reps answers T i).expectedQueries read)).sum :=
  NeighborCollection.expected_le_sum _ _ _

/-- The mixed update makes every low/high recovery call on the same residual,
then performs exactly one validated least-layer insertion batch. -/
def mixedUpdate (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) (T : ℕ) :
    RTree (Finset V) ℝ (Option (ParallelState π r))
      ((Finset.univ.toList : List (Option (Fin (highBucketCount (Fintype.card V))))).length *
        oneBucketBudget V T) :=
  (s.jointBucketNeighbors color reps answers T).map fun out =>
    out.bind (s.assembleNeighbors color (positiveColorRows (π := π) color reps answers))

/-- The one actual mixed batch either progresses once per positive queried
row, or its explicit finite recovery failure costs at least 3T queries.
In particular, failed finite completion is not called a certificate. -/
theorem mixedUpdate_honest (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (color : Q → Bool) (reps : Finset V) (T : ℕ)
    (hcolor : ∀ u v, (s.forests (lastIndex hr)).quotient.Reachable u v → color u = color v)
    (hsep : ∀ u ∈ reps, ∀ v ∈ reps, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) {out : Option (ParallelState π r) × ℕ}
    (hout : out ∈ (RTree.run G.toWeighted.cut
      (s.mixedUpdate color reps ((s.colorRows color reps).eval G.toWeighted.cut) T)).support) :
    match out.1 with
    | none => 3 * T ≤ out.2
    | some t => t.Laminar ∧ t.usedGraph.IsSubgraph G.toWeighted ∧
        t.InactiveSound hr G.toWeighted ∧
        t.edgeCount = s.edgeCount + (positiveColorRows (π := π) color reps
          ((s.colorRows color reps).eval G.toWeighted.cut)).card ∧
        t.livePotential + (positiveColorRows (π := π) color reps
          ((s.colorRows color reps).eval G.toWeighted.cut)).card ≤ s.livePotential := by
  rw [mixedUpdate, mapped_run] at hout
  obtain ⟨⟨table, cost⟩, htable, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  cases table with
  | none =>
      have hout : out = (none, cost) := he.symm
      rw [hout]
      exact s.jointBucketNeighbors_none_cost color reps T G hs cost htable
  | some next =>
      let rows := positiveColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut)
      have hg := s.jointBucketNeighbors_complete color reps T G hs next cost htable
      have hred : ∀ u ∈ rows, u ∈ reps ∧ color (π.map u) = true := by
        intro u hu
        exact Finset.mem_filter.mp (Finset.mem_filter.mp hu).1
      have htab : NeighborTable (π := π) color rows next := by
        intro u hu
        obtain ⟨v, hv, hn, _⟩ := hg.1 u hu
        exact ⟨v, hn, (hred u hu).2, (Finset.mem_filter.mp hv).2⟩
      have hpositive : ∀ u ∈ rows, ∀ v, next u = some v →
          0 < (G.toWeighted.subtract s.usedGraph).w u v := by
        intro u hu v hv
        obtain ⟨w, _, hw, hp⟩ := hg.1 u hu
        have hew : w = v := Option.some.inj (hw.symm.trans hv)
        exact hew ▸ hp
      have hsep' : ∀ u ∈ rows, ∀ v ∈ rows, u ≠ v →
          ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) := by
        intro u hu v hv hne
        exact hsep u (hred u hu).1 v (hred v hv).1 hne
      obtain ⟨t, ht, htl, hts, hti, hcount, hpotential⟩ :=
        s.assembleNeighbors_honest hr hl color rows next htab hcolor hsep' G hs hi hpositive
      have hout : out = (some t, cost) := by
        change (s.assembleNeighbors color rows next, cost) = out at he
        rw [ht] at he
        exact he.symm
      rw [hout]
      exact ⟨htl, hts, hti, hcount, hpotential⟩

/-- Positive representatives from distinct finest components inject into
the actual live blocks. No abstract representative-count premise is needed. -/
theorem representatives_card_le_potential (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hi : s.InactiveSound hr G.toWeighted) (reps : Finset V)
    (hsep : ∀ u ∈ reps, ∀ v ∈ reps, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (hpositive : ∀ u ∈ reps, ∃ v,
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) ∧
        0 < (G.toWeighted.subtract s.usedGraph).w u v) :
    reps.card ≤ s.livePotential := by
  have ha : ∀ u ∈ reps, u ∉ s.inactive := by
    intro u hu
    obtain ⟨v, hv, hp⟩ := hpositive u hu
    exact (s.positive_endpoints_active hr G.toWeighted hi hv hp).1
  let f : reps → {B : Finset V // B ∈ s.liveBlocks (lastIndex hr)} := fun u =>
    ⟨s.block (lastIndex hr) u.val, s.block_mem_live _ (ha u.val u.property)⟩
  have hf : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    by_contra hne
    have hb : s.block (lastIndex hr) u.val = s.block (lastIndex hr) v.val :=
      congrArg Subtype.val he
    exact hsep u.val u.property v.val v.property hne
      ((s.block_eq_iff _ _ _).mp hb)
  have hcard : reps.card ≤ (s.liveBlocks (lastIndex hr)).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  apply hcard.trans
  exact Finset.single_le_sum (fun i hi => Nat.zero_le ((s.liveBlocks i).card))
    (Finset.mem_univ (lastIndex hr))

/-- Explicit failure has zero stopped potential; it still remains a failure
and its separate actual-cost lower bound is required before cap coupling. -/
def resultPotential : Option (ParallelState π r) → ℕ
  | none => 0
  | some s => s.livePotential

theorem mixedUpdate_potential (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (color : Q → Bool) (reps : Finset V) (T : ℕ)
    (hcolor : ∀ u v, (s.forests (lastIndex hr)).quotient.Reachable u v → color u = color v)
    (hsep : ∀ u ∈ reps, ∀ v ∈ reps, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted)
    (hpositive : ∀ u ∈ reps, ∃ v,
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) ∧
        0 < (G.toWeighted.subtract s.usedGraph).w u v) :
    CutQueryComplexity.Probability.expect
      ((s.mixedUpdate color reps ((s.colorRows color reps).eval G.toWeighted.cut) T).eval
        G.toWeighted.cut) (fun out => (resultPotential out : ℝ≥0∞)) +
      ((positiveColorRows (π := π) color reps
        ((s.colorRows color reps).eval G.toWeighted.cut)).card : ℝ≥0∞) ≤
      (s.livePotential : ℝ≥0∞) := by
  let rows := positiveColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut)
  have hrows : rows.card ≤ s.livePotential := by
    have hcard : rows.card ≤ reps.card :=
      (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)
    exact hcard.trans (s.representatives_card_le_potential hr G hi reps hsep hpositive)
  have hpoint {out : Option (ParallelState π r) × ℕ}
      (hout : out ∈ (RTree.run G.toWeighted.cut
        (s.mixedUpdate color reps ((s.colorRows color reps).eval G.toWeighted.cut) T)).support) :
      resultPotential out.1 + rows.card ≤ s.livePotential := by
    have hg := s.mixedUpdate_honest hr hl color reps T hcolor hsep G hs hi hout
    cases he : out.1 with
    | none => simpa only [he, resultPotential, Nat.zero_add] using hrows
    | some t =>
        rw [he] at hg
        simpa only [he, resultPotential] using hg.2.2.2.2
  have he : CutQueryComplexity.Probability.expect
      (RTree.run G.toWeighted.cut
        (s.mixedUpdate color reps ((s.colorRows color reps).eval G.toWeighted.cut) T))
      (fun out => (resultPotential out.1 : ℝ≥0∞) + (rows.card : ℝ≥0∞)) ≤
        (s.livePotential : ℝ≥0∞) := by
    apply CutQueryComplexity.Probability.expect_le_of_le_on_support
    intro out hout
    exact_mod_cast hpoint hout
  simpa only [RTree.eval, CutQueryComplexity.Probability.expect_map,
    CutQueryComplexity.Probability.expect_add, CutQueryComplexity.Probability.expect_const] using he

def fairBatchBudget (V : Type) [Fintype V] (T : ℕ) : ℕ :=
  3 * Fintype.card V +
    Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) * oneBucketBudget V T

/-- Actual fresh component colors, actual queried row counts, actual mixed
recovery, and one least-layer insertion batch. The graph is absent from the
constructor, including its random distribution and finite query clock. -/
def fairBatch (s : ParallelState π r) (hr : 0 < r) (reps : Finset V) (T : ℕ) :
    RTree (Finset V) ℝ (Option (ParallelState π r)) (fairBatchBudget V T) :=
  RTree.mix ((componentBits (Q := Q)).map fun tape =>
    let color := componentColor (s.forests (lastIndex hr)).quotient tape
    ((RTree.ofDeterministic (s.colorRows color reps)).weaken (by
      have hh := Finset.card_le_univ (redRepresentatives (π := π) color reps)
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 3 hh)).bind fun answers =>
        (s.mixedUpdate color reps answers T).cast (by simp))

theorem fairBatch_eval (s : ParallelState π r) (hr : 0 < r) (reps : Finset V)
    (T : ℕ) (read : Finset V → ℝ) :
    (s.fairBatch hr reps T).eval read = (componentBits (Q := Q)).bind fun tape =>
      let color := componentColor (s.forests (lastIndex hr)).quotient tape
      (s.mixedUpdate color reps ((s.colorRows color reps).eval read) T).eval read := by
  dsimp only [fairBatch, fairBatchBudget]
  simp only [RTree.eval_mix, PMF.bind_map, Function.comp_def,
    RTree.eval_bind, RTree.eval_weaken, RTree.eval_ofDeterministic,
    PMF.pure_bind, RTree.eval_cast]

/-- The preceding count queries and random colors cannot conceal a finite
bucket exhaustion: an honest `none` still costs at least 3T original cuts. -/
theorem fairBatch_none_cost (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (reps : Finset V) (T cost : ℕ)
    (hsep : ∀ u ∈ reps, ∀ v ∈ reps, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (hout : (none, cost) ∈ (RTree.run G.toWeighted.cut (s.fairBatch hr reps T)).support) :
    3 * T ≤ cost := by
  dsimp only [fairBatch, fairBatchBudget] at hout
  simp only [RTree.run_mix, PMF.bind_map, Function.comp_def] at hout
  obtain ⟨tape, htape, hprog⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  let color := componentColor (s.forests (lastIndex hr)).quotient tape
  rw [RTree.run_bind] at hprog
  obtain ⟨⟨answers, c⟩, hfirst, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hprog
  rw [RTree.run_weaken, RTree.run_ofDeterministic] at hfirst
  have ha := (PMF.mem_support_pure_iff _ _).mp hfirst
  have haE : answers = (s.colorRows color reps).eval G.toWeighted.cut := congrArg Prod.fst ha
  obtain ⟨⟨result, d⟩, hresult, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  rw [RTree.run_cast] at hresult
  have heResult : result = none := congrArg Prod.fst he
  have heCost : c + d = cost := congrArg Prod.snd he
  rw [haE] at hresult
  have step := s.mixedUpdate_honest hr hl color reps T
    (fun u v h => componentColor_constant _ tape h) hsep G hs hi hresult
  rw [heResult] at step
  omega

/-- The quarter progress estimate now belongs to the actual finite public
color/recovery/update program, with no supplied neighbor or drift table.
Explicit finite recovery failures have zero stopped potential and are covered
separately by their actual query-cost lower bound. -/
theorem fairBatch_potential (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (reps : Finset V) (T : ℕ)
    (hsep : ∀ u ∈ reps, ∀ v ∈ reps, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (hpositive : ∀ u ∈ reps, ∃ v,
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) ∧
        0 < (G.toWeighted.subtract s.usedGraph).w u v) :
    CutQueryComplexity.Probability.expect ((s.fairBatch hr reps T).eval G.toWeighted.cut)
      (fun out => (resultPotential out : ℝ≥0∞)) + (reps.card : ℝ≥0∞) / 4 ≤
        (s.livePotential : ℝ≥0∞) := by
  let F := (s.forests (lastIndex hr)).quotient
  let C := fun tape => componentColor F tape
  let A := fun tape => positiveColorRows (π := π) (C tape) reps
    ((s.colorRows (C tape) reps).eval G.toWeighted.cut)
  let p := fun tape =>
    (s.mixedUpdate (C tape) reps ((s.colorRows (C tape) reps).eval G.toWeighted.cut) T).eval
      G.toWeighted.cut
  have hstep (tape : Finset Q → Bool) :
      CutQueryComplexity.Probability.expect (p tape)
        (fun out => (resultPotential out : ℝ≥0∞)) + ((A tape).card : ℝ≥0∞) ≤
          (s.livePotential : ℝ≥0∞) :=
    s.mixedUpdate_potential hr hl (C tape) reps T
      (fun u v h => componentColor_constant F tape h) hsep G hs hi hpositive
  have havg : CutQueryComplexity.Probability.expect (componentBits (Q := Q))
      (fun tape => CutQueryComplexity.Probability.expect (p tape)
        (fun out => (resultPotential out : ℝ≥0∞))) +
      CutQueryComplexity.Probability.expect (componentBits (Q := Q))
        (fun tape => ((A tape).card : ℝ≥0∞)) ≤ (s.livePotential : ℝ≥0∞) := by
    rw [← CutQueryComplexity.Probability.expect_add]
    exact CutQueryComplexity.Probability.expect_le_of_le_on_support _ (fun tape _ => hstep tape)
  have hcount := s.colorRows_favorable_expect hr G hs reps hpositive
  have hh := (add_le_add (le_refl _) hcount).trans havg
  rw [s.fairBatch_eval hr reps T G.toWeighted.cut,
    CutQueryComplexity.Probability.expect_bind]
  exact hh

/-- Actual first-fit insertion preserves all old connectivity. -/
theorem insertFirst_reachable (s : ParallelState π r) (e : OriginalEdge π)
    {t : ParallelState π r} (ht : s.insertFirst e = some t) (i : Fin r)
    {u v : Q} (huv : (s.forests i).quotient.Reachable u v) :
    (t.forests i).quotient.Reachable u v := by
  unfold insertFirst at ht
  split at ht
  next h =>
    cases Option.some.inj ht
    exact s.insertAt_reachable _ e _ i huv
  next h => cases ht

theorem insertBatch_reachable (s : ParallelState π r) (es : List (OriginalEdge π))
    {t : ParallelState π r} (ht : s.insertBatch es = some t) (i : Fin r)
    {u v : Q} (huv : (s.forests i).quotient.Reachable u v) :
    (t.forests i).quotient.Reachable u v := by
  induction es generalizing s with
  | nil =>
      have he : s = t := Option.some.inj ht
      simpa only [he] using huv
  | cons e es ih =>
      cases he : s.insertFirst e with
      | none =>
          simp only [insertBatch, he, Option.bind_none] at ht
          cases ht
      | some a =>
          have htail : a.insertBatch es = some t := by
            simpa only [insertBatch, he, Option.bind_some] using ht
          exact ih a htail (s.insertFirst_reachable e he i huv)

/-- A returned table causes only merges. Inactive vertices are unchanged;
this statement is independent of the oracle used to produce the table. -/
theorem assembleNeighbors_monotone (s : ParallelState π r) (color : Q → Bool)
    (rows : Finset V) (next : V → Option V) {t : ParallelState π r}
    (ht : s.assembleNeighbors color rows next = some t) :
    t.inactive = s.inactive ∧
      (∀ i u v, (s.forests i).quotient.Reachable u v →
        (t.forests i).quotient.Reachable u v) := by
  unfold assembleNeighbors at ht
  split at ht
  next h =>
    exact ⟨s.insertBatch_inactive _ ht, fun i u v huv => s.insertBatch_reachable _ ht i huv⟩
  next h => cases ht

theorem mixedUpdate_liveBlocks_mono (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (answers : V → Option (Fin (Fintype.card V + 1))) (T : ℕ)
    (read : Finset V → ℝ) {t : ParallelState π r}
    (ht : some t ∈ ((s.mixedUpdate color reps answers T).eval read).support) (i : Fin r) :
    (t.liveBlocks i).card ≤ (s.liveBlocks i).card := by
  rw [mixedUpdate, RTree.eval_map] at ht
  obtain ⟨table, htable, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  cases table with
  | none => cases he
  | some next =>
      have ha : s.assembleNeighbors color (positiveColorRows (π := π) color reps answers)
          next = some t := he
      obtain ⟨hi, hconn⟩ := s.assembleNeighbors_monotone color _ next ha
      exact s.liveBlocks_card_mono_of t i (fun v hv => by simpa only [hi] using hv) (hconn i)

theorem fairBatch_liveBlocks_mono (s : ParallelState π r) (hr : 0 < r)
    (reps : Finset V) (T : ℕ) (read : Finset V → ℝ) {t : ParallelState π r}
    (ht : some t ∈ ((s.fairBatch hr reps T).eval read).support) (i : Fin r) :
    (t.liveBlocks i).card ≤ (s.liveBlocks i).card := by
  rw [s.fairBatch_eval hr reps T read] at ht
  obtain ⟨tape, htape, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
  exact s.mixedUpdate_liveBlocks_mono _ reps _ T read hout i

/-- The actual supported successful batch preserves the graph and forest
invariants needed by the next round, and never increases any live count. -/
theorem fairBatch_success (s : ParallelState π r) (hr : 0 < r) (hl : s.Laminar)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) (reps : Finset V) (T : ℕ)
    (hsep : ∀ u ∈ reps, ∀ v ∈ reps, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    {t : ParallelState π r}
    (ht : some t ∈ ((s.fairBatch hr reps T).eval G.toWeighted.cut).support) :
    t.Laminar ∧ t.usedGraph.IsSubgraph G.toWeighted ∧
      t.InactiveSound hr G.toWeighted ∧ t.livePotential ≤ s.livePotential ∧
      (∀ i, (t.liveBlocks i).card ≤ (s.liveBlocks i).card) := by
  have hmono := s.fairBatch_liveBlocks_mono hr reps T G.toWeighted.cut ht
  rw [s.fairBatch_eval hr reps T G.toWeighted.cut] at ht
  obtain ⟨tape, htape, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
  rw [RTree.eval] at hout
  obtain ⟨⟨result, cost⟩, hrun, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  have he' : result = some t := he
  have hg := s.mixedUpdate_honest hr hl _ reps T
    (fun u v h => componentColor_constant _ tape h) hsep G hs hi hrun
  rw [he'] at hg
  exact ⟨hg.1, hg.2.1, hg.2.2.1, (Nat.le_add_right _ _).trans hg.2.2.2.2, hmono⟩

theorem insertBatch_failed (s : ParallelState π r) (es : List (OriginalEdge π))
    {t : ParallelState π r} (ht : s.insertBatch es = some t) : t.failed = s.failed := by
  induction es generalizing s with
  | nil => exact congrArg ParallelState.failed (Option.some.inj ht).symm
  | cons e es ih =>
      cases he : s.insertFirst e with
      | none =>
          simp only [insertBatch, he, Option.bind_none] at ht
          cases ht
      | some u =>
          have htail : u.insertBatch es = some t := by
            simpa only [insertBatch, he, Option.bind_some] using ht
          exact (ih u htail).trans (s.insertFirst_failed e he)

theorem mixedUpdate_failed (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (answers : V → Option (Fin (Fintype.card V + 1))) (T : ℕ)
    (read : Finset V → ℝ) {t : ParallelState π r}
    (ht : some t ∈ ((s.mixedUpdate color reps answers T).eval read).support) :
    t.failed = s.failed := by
  rw [mixedUpdate, RTree.eval_map] at ht
  obtain ⟨table, htable, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  cases table with
  | none => cases he
  | some next =>
      change s.assembleNeighbors color (positiveColorRows (π := π) color reps answers) next = some t at he
      unfold assembleNeighbors at he
      split at he
      next h => exact s.insertBatch_failed _ he
      next h => cases he

theorem fairBatch_failed (s : ParallelState π r) (hr : 0 < r) (reps : Finset V)
    (T : ℕ) (read : Finset V → ℝ) {t : ParallelState π r}
    (ht : some t ∈ ((s.fairBatch hr reps T).eval read).support) : t.failed = s.failed := by
  rw [s.fairBatch_eval hr reps T read] at ht
  obtain ⟨tape, htape, hstep⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
  exact s.mixedUpdate_failed _ reps _ T read hstep

end ParallelState

#print axioms NeighborCollection.complete
#print axioms NeighborCollection.none_cost
#print axioms NeighborCollection.expected_le_sum
#print axioms ParallelState.learnedSetNext_present
#print axioms ParallelState.highBucketNeighbors_every_oracle
#print axioms ParallelState.highBucketNeighbors_empty
#print axioms ParallelState.selectedBucketNeighbors_honest_run
#print axioms ParallelState.selectedBucketNeighbors_complete
#print axioms ParallelState.selectedBucketNeighbors_none_cost
#print axioms ParallelState.selectedBucketNeighbors_expected
#print axioms ParallelState.highBucketNeighbors_none_cost
#print axioms ParallelState.highBucketNeighbors_complete
#print axioms ParallelState.highBucketNeighbors_expected
#print axioms ParallelState.lowBucketNeighbors_honest
#print axioms ParallelState.lowBucketNeighbors_complete
#print axioms ParallelState.bucketCall_complete
#print axioms ParallelState.bucketCall_none_cost
#print axioms ParallelState.jointBucketNeighbors_complete
#print axioms ParallelState.jointBucketNeighbors_none_cost
#print axioms ParallelState.jointBucketNeighbors_expected_le_sum
#print axioms ParallelState.mixedUpdate_honest
#print axioms ParallelState.representatives_card_le_potential
#print axioms ParallelState.mixedUpdate_potential
#print axioms ParallelState.fairBatch_eval
#print axioms ParallelState.fairBatch_none_cost
#print axioms ParallelState.fairBatch_potential
#print axioms ParallelState.insertFirst_reachable
#print axioms ParallelState.insertBatch_reachable
#print axioms ParallelState.assembleNeighbors_monotone
#print axioms ParallelState.mixedUpdate_liveBlocks_mono
#print axioms ParallelState.fairBatch_liveBlocks_mono
#print axioms ParallelState.fairBatch_success
#print axioms ParallelState.insertBatch_failed
#print axioms ParallelState.mixedUpdate_failed
#print axioms ParallelState.fairBatch_failed

end
end CutQueryComplexity.StarContraction2022.Certificates
