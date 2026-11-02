import CutQueryComplexity.GHReduction.ThresholdProgram

/-! # One public outer-pivot step

Every sampled level executes the actual isolating program and queries its shore
values. Public guards validate indices, orientation, size, exact reported value,
and disjointness. One level of maximum terminal coverage is retained, together
with all its individual accepted shores. No constructor takes the hidden graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.OuterPivot
noncomputable section
open scoped Classical BigOperators
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

structure Batch (V : Type) where
  accepted : Finset V
  shore : V → Finset V
  value : V → ℝ

def Batch.empty : Batch V := ⟨∅, fun _ => ∅, fun _ => 0⟩

def Batch.covered (B : Batch V) (U : Finset V) : Finset V :=
  B.accepted.biUnion (fun v => B.shore v ∩ U)

@[simp] theorem Batch.mem_covered (B : Batch V) (U : Finset V) (x : V) :
    x ∈ B.covered U ↔ ∃ v ∈ B.accepted, x ∈ B.shore v ∩ U := by
  simp [Batch.covered]

@[simp] theorem Batch.empty_covered (U : Finset V) : (Batch.empty : Batch V).covered U = ∅ := by
  simp [Batch.covered, Batch.empty]

theorem Batch.covered_subset (B : Batch V) (U : Finset V) : B.covered U ⊆ U := by
  intro x hx
  obtain ⟨v, _, hv⟩ := (B.mem_covered U x).mp hx
  exact (Finset.mem_inter.mp hv).2

structure WellFormed (U : Finset V) (s : V) (values : V → Option ℝ) (B : Batch V) : Prop where
  indices : B.accepted ⊆ U.erase s
  contains : ∀ v ∈ B.accepted, v ∈ B.shore v
  excludes : ∀ v ∈ B.accepted, s ∉ B.shore v
  small : ∀ v ∈ B.accepted, 2 * (B.shore v ∩ U).card ≤ U.card
  «matches» : ∀ v ∈ B.accepted, values v = some (B.value v)
  disjoint : (B.accepted : Set V).PairwiseDisjoint B.shore

theorem empty_wellFormed (U : Finset V) (s : V) (values : V → Option ℝ) :
    WellFormed U s values Batch.empty := by
  constructor <;> simp [Batch.empty, Set.PairwiseDisjoint, Set.Pairwise]

theorem WellFormed.source_not_covered {U : Finset V} {s : V} {values : V → Option ℝ}
    {B : Batch V} (h : WellFormed U s values B) : s ∉ B.covered U := by
  intro hs
  obtain ⟨v, hv, hs⟩ := (B.mem_covered U s).mp hs
  exact h.excludes v hv (Finset.mem_inter.mp hs).1

def acceptedCut (U : Finset V) (s : V) (values : V → Option ℝ) (v : V)
    (cut : Finset V × ℝ) : Prop :=
  v ∈ U ∧ v ≠ s ∧ v ∈ cut.1 ∧ s ∉ cut.1 ∧
    2 * (cut.1 ∩ U).card ≤ U.card ∧ values v = some cut.2

def extendCuts {R : Finset V} (cuts : R → Finset V × ℝ) (v : V) : Finset V × ℝ :=
  if hv : v ∈ R then cuts ⟨v, hv⟩ else (∅, 0)

@[simp] theorem extendCuts_mem {R : Finset V} (cuts : R → Finset V × ℝ)
    (v : V) (hv : v ∈ R) : extendCuts cuts v = cuts ⟨v, hv⟩ := by
  simp [extendCuts, hv]

def DisjointCuts {R : Finset V} (cuts : R → Finset V × ℝ) : Prop :=
  ∀ v w : R, v ≠ w → Disjoint (cuts v).1 (cuts w).1

def rawBatch (U R : Finset V) (s : V) (values : V → Option ℝ)
    (cuts : R → Finset V × ℝ) : Batch V where
  accepted := R.filter (fun v => acceptedCut U s values v (extendCuts cuts v))
  shore := fun v => (extendCuts cuts v).1
  value := fun v => (extendCuts cuts v).2

/-- A malformed public table cannot create overlapping recursive children. -/
def prepareBatch (U R : Finset V) (s : V) (values : V → Option ℝ)
    (cuts : R → Finset V × ℝ) : Batch V :=
  if DisjointCuts cuts then rawBatch U R s values cuts else Batch.empty

theorem rawBatch_wellFormed (U R : Finset V) (s : V) (values : V → Option ℝ)
    (cuts : R → Finset V × ℝ) (hd : DisjointCuts cuts) :
    WellFormed U s values (rawBatch U R s values cuts) := by
  have hacc (v : V) (hv : v ∈ (rawBatch U R s values cuts).accepted) :
      v ∈ R ∧ acceptedCut U s values v (extendCuts cuts v) := Finset.mem_filter.mp hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact Finset.mem_erase.mpr ⟨(hacc v hv).2.2.1, (hacc v hv).2.1⟩
  · intro v hv
    exact (hacc v hv).2.2.2.1
  · intro v hv
    exact (hacc v hv).2.2.2.2.1
  · intro v hv
    exact (hacc v hv).2.2.2.2.2.1
  · intro v hv
    exact (hacc v hv).2.2.2.2.2.2
  · intro v hv w hw hvw
    change Disjoint (extendCuts cuts v).1 (extendCuts cuts w).1
    rw [extendCuts_mem cuts v (hacc v hv).1, extendCuts_mem cuts w (hacc w hw).1]
    exact hd _ _ (fun he => hvw (congrArg Subtype.val he))

theorem prepareBatch_wellFormed (U R : Finset V) (s : V) (values : V → Option ℝ)
    (cuts : R → Finset V × ℝ) : WellFormed U s values (prepareBatch U R s values cuts) := by
  by_cases hd : DisjointCuts cuts
  · simpa only [prepareBatch, hd, ite_true] using rawBatch_wellFormed U R s values cuts hd
  · simpa only [prepareBatch, hd, ite_false] using empty_wellFormed U s values

/-- Honest values turn a queried and value-tested shore into an original
minimum cut. This implication does not rely on the primitive being correct. -/
theorem prepareBatch_correct (G : WeightedGraph V) (U R : Finset V) (s : V)
    (values : V → Option ℝ) (cuts : R → Finset V × ℝ)
    (hvalues : ∀ v ∈ U.erase s, values v = some (stValue G v s))
    (hquery : ∀ v : R, (cuts v).2 = G.cut (cuts v).1) :
    ∀ v ∈ (prepareBatch U R s values cuts).accepted,
      IsSTMinCut G v s ((prepareBatch U R s values cuts).shore v) ∧
        (prepareBatch U R s values cuts).value v =
          G.cut ((prepareBatch U R s values cuts).shore v) := by
  by_cases hd : DisjointCuts cuts
  · rw [prepareBatch, if_pos hd]
    intro v hv
    have hform := rawBatch_wellFormed U R s values cuts hd
    have hvR := (Finset.mem_filter.mp hv).1
    have hval : (rawBatch U R s values cuts).value v =
        G.cut ((rawBatch U R s values cuts).shore v) := by
      simpa only [rawBatch, extendCuts_mem cuts v hvR] using hquery ⟨v, hvR⟩
    have heq : G.cut ((rawBatch U R s values cuts).shore v) = stValue G v s := by
      have hopt := hvalues v (hform.indices hv)
      rw [hform.matches v hv, hval] at hopt
      exact Option.some.inj hopt
    refine ⟨⟨hform.contains v hv, hform.excludes v hv, ?_⟩, hval⟩
    intro T hvT hsT
    rw [heq]
    exact stValue_le G hvT hsT
  · simp [prepareBatch, hd, Batch.empty]

def levelProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U R : Finset V) (s : V) (values : V → Option ℝ) : Prog (Finset V) ℝ (Batch V) :=
  if 2 ≤ R.card then
    (isolatingValuesProgram family R).map (prepareBatch U R s values)
  else Prog.pure Batch.empty

theorem levelProgram_wellFormed {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U R : Finset V) (s : V) (values : V → Option ℝ) (read : Finset V → ℝ) :
    WellFormed U s values (Prog.eval read (levelProgram family U R s values)) := by
  by_cases hR : 2 ≤ R.card
  · simpa only [levelProgram, hR, ite_true, Prog.eval_map] using
      prepareBatch_wellFormed U R s values (Prog.eval read (isolatingValuesProgram family R))
  · simpa only [levelProgram, hR, ite_false, Prog.eval_pure] using empty_wellFormed U s values

theorem levelProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (U R : Finset V) (s : V) (values : V → Option ℝ)
    (hvalues : ∀ v ∈ U.erase s, values v = some (stValue G v s)) :
    ∀ v ∈ (Prog.eval G.cut (levelProgram family U R s values)).accepted,
      IsSTMinCut G v s ((Prog.eval G.cut (levelProgram family U R s values)).shore v) ∧
        (Prog.eval G.cut (levelProgram family U R s values)).value v =
          G.cut ((Prog.eval G.cut (levelProgram family U R s values)).shore v) := by
  by_cases hR : 2 ≤ R.card
  · simpa only [levelProgram, hR, ite_true, Prog.eval_map] using
      prepareBatch_correct G U R s values (Prog.eval G.cut (isolatingValuesProgram family R))
        hvalues (isolatingValuesProgram_value family G R)
  · simp [levelProgram, hR, Batch.empty]

theorem isolatingValues_disjoint {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (R : Finset V) (hR : 2 ≤ R.card) :
    DisjointCuts (Prog.eval G.cut (isolatingValuesProgram family R)) := by
  intro v w hvw
  apply canonical_trace_disjoint G _
    (isolatingValuesProgram_correct family G hG R hR v).1
    (isolatingValuesProgram_correct family G hG R hR w).1
  simp only [Finset.disjoint_singleton, Finset.mem_singleton]
  exact fun he => hvw (Subtype.ext he)

/-- A canonical singleton hit survives every public guard and contributes its
entire terminal trace to this level's actual coverage. -/
theorem levelProgram_hit {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {U R C : Finset V} {s v : V}
    (values : V → Option ℝ) (hsR : s ∈ R) (hvU : v ∈ U)
    (hC : IsCanonicalSTCut G v s C) (htrace : C ∩ R = {v})
    (hvalue : values v = some (stValue G v s)) (hsize : 2 * (C ∩ U).card ≤ U.card) :
    C ∩ U ⊆ (Prog.eval G.cut (levelProgram family U R s values)).covered U := by
  have hvR : v ∈ R := by
    have : v ∈ C ∩ R := by rw [htrace]; simp
    exact (Finset.mem_inter.mp this).2
  have hvs : v ≠ s := fun he => hC.1.2.1 (he ▸ hC.1.1)
  have hR : 2 ≤ R.card := by
    have hsub : ({s, v} : Finset V) ⊆ R := by simp [Finset.insert_subset_iff, hsR, hvR]
    have hc := Finset.card_le_card hsub
    simpa [Ne.symm hvs] using hc
  let cuts := Prog.eval G.cut (isolatingValuesProgram family R)
  have hd : DisjointCuts cuts := isolatingValues_disjoint family G hG R hR
  have he : (cuts ⟨v, hvR⟩).1 = C := canonicalIso_eq_pair G hsR hvs hC htrace
    (isolatingValuesProgram_correct family G hG R hR ⟨v, hvR⟩).1
  have hval : (cuts ⟨v, hvR⟩).2 = stValue G v s := by
    rw [isolatingValuesProgram_value family G R ⟨v, hvR⟩, he,
      stValue_eq_of_minCut G hC.1]
  have hacc : acceptedCut U s values v (extendCuts cuts v) := by
    rw [extendCuts_mem cuts v hvR]
    exact ⟨hvU, hvs, by simpa only [he] using hC.1.1,
      by simpa only [he] using hC.1.2.1,
      by simpa only [he] using hsize, by simpa only [hval] using hvalue⟩
  intro x hx
  simp only [levelProgram, hR, ite_true, Prog.eval_map]
  change x ∈ (prepareBatch U R s values cuts).covered U
  rw [prepareBatch, if_pos hd]
  apply (Batch.mem_covered _ _ _).mpr
  refine ⟨v, Finset.mem_filter.mpr ⟨hvR, hacc⟩, ?_⟩
  simpa only [rawBatch, extendCuts_mem cuts v hvR, he] using hx

structure Output (V : Type) (levels : ℕ) where
  level : Fin (levels + 1)
  batch : Batch V

/-- The finite maximum depends only on the publicly returned batches. -/
def bestLevel (U : Finset V) {levels : ℕ} (batches : Fin (levels + 1) → Batch V) :
    Fin (levels + 1) :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun i => ((batches i).covered U).card) Finset.univ_nonempty)

theorem bestLevel_max (U : Finset V) {levels : ℕ} (batches : Fin (levels + 1) → Batch V)
    (i : Fin (levels + 1)) :
    ((batches i).covered U).card ≤ ((batches (bestLevel U batches)).covered U).card :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun j => ((batches j).covered U).card) Finset.univ_nonempty)).2 i (Finset.mem_univ i)

def selectLevel (U : Finset V) {levels : ℕ} (batches : Fin (levels + 1) → Batch V) :
    Output V levels := ⟨bestLevel U batches, batches (bestLevel U batches)⟩

def stepProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) : Prog (Finset V) ℝ (Output V levels) :=
  (tableProgram (levels + 1) (fun i =>
    levelProgram family U (levelSample U s i.val seed) s values)).map (selectLevel U)

@[simp] theorem stepProgram_eval {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (read : Finset V → ℝ) :
    Prog.eval read (stepProgram family U s values levels seed) =
      selectLevel U (fun i : Fin (levels + 1) =>
        Prog.eval read (levelProgram family U (levelSample U s i.val seed) s values)) := by
  simp [stepProgram]

theorem stepProgram_wellFormed {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (read : Finset V → ℝ) :
    WellFormed U s values (Prog.eval read (stepProgram family U s values levels seed)).batch := by
  rw [stepProgram_eval]
  exact levelProgram_wellFormed family U _ s values read

theorem stepProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels)
    (hvalues : ∀ v ∈ U.erase s, values v = some (stValue G v s)) :
    ∀ v ∈ (Prog.eval G.cut (stepProgram family U s values levels seed)).batch.accepted,
      IsSTMinCut G v s ((Prog.eval G.cut (stepProgram family U s values levels seed)).batch.shore v) ∧
        (Prog.eval G.cut (stepProgram family U s values levels seed)).batch.value v =
          G.cut ((Prog.eval G.cut (stepProgram family U s values levels seed)).batch.shore v) := by
  rw [stepProgram_eval]
  exact levelProgram_correct family G U _ s values hvalues

theorem level_coverage_le_step {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (read : Finset V → ℝ) (i : Fin (levels + 1)) :
    ((Prog.eval read (levelProgram family U (levelSample U s i.val seed) s values)).covered U).card ≤
      ((Prog.eval read (stepProgram family U s values levels seed)).batch.covered U).card := by
  conv_rhs => rw [stepProgram_eval]
  exact bestLevel_max U (fun j : Fin (levels + 1) =>
    Prog.eval read (levelProgram family U (levelSample U s j.val seed) s values)) i

theorem levelProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U R : Finset V) (s : V) (values : V → Option ℝ) (read : Finset V → ℝ) :
    n * Prog.cost read (levelProgram family U R s values) ≤
      (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) := by
  have he : Prog.cost read (levelProgram family U R s values) =
      Prog.cost read (thresholdLevelProgram family U R s 0 0) := by
    by_cases hR : 2 ≤ R.card <;> simp [levelProgram, thresholdLevelProgram, hR]
  rw [he]
  exact thresholdLevelProgram_cost_scaled family hvn hQ U R s 0 0 read

theorem stepProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (read : Finset V → ℝ) :
    n * Prog.cost read (stepProgram family U s values levels seed) ≤
      (levels + 1) * ((Nat.clog 2 n + 3) * Fintype.card V * (Q n + n)) := by
  simp only [stepProgram, Prog.cost_map, tableProgram_cost, Finset.mul_sum]
  calc
    _ ≤ ∑ _i : Fin (levels + 1), (Nat.clog 2 n + 3) * Fintype.card V * (Q n + n) :=
      Finset.sum_le_sum (fun i _ => levelProgram_cost_scaled family hvn hQ U _ s values read)
    _ = _ := by simp

def stepBudget (Q : ℕ → ℕ) (n levels : ℕ) : ℕ :=
  (levels + 1) * (Nat.clog 2 n + 3) * (Q n + n)

theorem stepProgram_cost {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (read : Finset V → ℝ) :
    Prog.cost read (stepProgram family U s values levels seed) ≤ stepBudget Q n levels := by
  haveI : Nonempty V := ⟨s⟩
  have hn : 0 < n := lt_of_lt_of_le Fintype.card_pos hvn
  have h := stepProgram_cost_scaled family hvn hQ U s values levels seed read
  have hmul := Nat.mul_le_mul_left (stepBudget Q n levels) hvn
  have hfinal : n * Prog.cost read (stepProgram family U s values levels seed) ≤
      n * stepBudget Q n levels := by
    unfold stepBudget at *
    nlinarith
  by_contra hnot
  have hstrict : stepBudget Q n levels + 1 ≤
      Prog.cost read (stepProgram family U s values levels seed) := by omega
  have hscaled := Nat.mul_le_mul_left n hstrict
  nlinarith

/-- Public hard cap for arbitrary answer histories; the graph is not an input. -/
def stepTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) :
    DTree (Finset V) ℝ (Option (Output V levels)) (stepBudget Q n levels) :=
  Prog.toDTree (stepProgram family U s values levels seed) (stepBudget Q n levels)

theorem stepTree_eval {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (read : Finset V → ℝ) :
    (stepTree family n U s values levels seed).eval read =
      some (Prog.eval read (stepProgram family U s values levels seed)) :=
  Prog.toDTree_eval read _ _ (stepProgram_cost family hvn hQ U s values levels seed read)

/-- Public fallback if a capped execution runs out of budget. -/
def Output.empty (levels : ℕ) : Output V levels :=
  ⟨⟨0, Nat.succ_pos levels⟩, Batch.empty⟩

/-- Fresh public seed, one already-returned source vector, and an unconditional
query cap. No vector for a different pivot is an algorithmic argument. -/
def randomStepTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ) :
    RTree (Finset V) ℝ (Output V levels) (stepBudget Q n levels) :=
  RTree.mix ((thresholdSeedPMF V levels).map (fun seed => RTree.ofDeterministic
    ((stepTree family n U s values levels seed).map
      (fun output => output.getD (Output.empty levels)))))

theorem randomStepTree_eval {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ) (read : Finset V → ℝ) :
    (randomStepTree family n U s values levels).eval read =
      (thresholdSeedPMF V levels).map (fun seed =>
        Prog.eval read (stepProgram family U s values levels seed)) := by
  simp only [randomStepTree, RTree.eval_mix, PMF.bind_map, Function.comp_def]
  have he (seed : ThresholdSeed V levels) :
      (RTree.ofDeterministic ((stepTree family n U s values levels seed).map
        (fun output => output.getD (Output.empty levels)))).eval read =
      PMF.pure (Prog.eval read (stepProgram family U s values levels seed)) := by
    simp only [RTree.eval_ofDeterministic,
      DTree.eval_map, stepTree_eval family hvn hQ, Option.getD_some]
  simp_rw [he]
  rfl

theorem randomStepTree_correct {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (hvalues : ∀ v ∈ U.erase s, values v = some (stValue G v s)) {output : Output V levels}
    (hout : output ∈ ((randomStepTree family n U s values levels).eval G.cut).support) :
    WellFormed U s values output.batch ∧
      ∀ v ∈ output.batch.accepted, IsSTMinCut G v s (output.batch.shore v) ∧
        output.batch.value v = G.cut (output.batch.shore v) := by
  rw [randomStepTree_eval family hvn hQ] at hout
  obtain ⟨seed, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact ⟨stepProgram_wellFormed family U s values levels seed G.cut,
    stepProgram_correct family G U s values levels seed hvalues⟩

#print axioms prepareBatch_correct
#print axioms levelProgram_hit
#print axioms stepProgram_wellFormed
#print axioms stepProgram_correct
#print axioms stepProgram_cost_scaled
#print axioms stepTree_eval
#print axioms randomStepTree_eval
#print axioms randomStepTree_correct

end
end CutQueryComplexity.GHReduction.OuterPivot
