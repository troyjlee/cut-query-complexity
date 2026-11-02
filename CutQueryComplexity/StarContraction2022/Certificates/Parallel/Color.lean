import CutQueryComplexity.StarContraction2022.Certificates.Parallel.Queries
import CutQueryComplexity.StarContraction2022.Certificates.ParallelProgress
import CutQueryComplexity.StarContraction2022.Common.Constants
import Mathlib.Data.Nat.Log

/-! # Query-defined colors, mixed degree buckets, and low-degree updates

Part of the parallel threshold certificate. No full parallel algorithm,
expected C_P bound, or endpoint is asserted in this module.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Certificates

noncomputable section
open scoped Classical ENNReal

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
variable {π : PublicQuotient V Q} {r : ℕ}

namespace ParallelState

/-- Public red representatives and blue original vertices. The quotient is
used only for component labels; every queried endpoint remains original. -/
def redRepresentatives (color : Q → Bool) (reps : Finset V) : Finset V :=
  reps.filter fun u => color (π.map u) = true

def blueVertices (color : Q → Bool) : Finset V :=
  Finset.univ.filter fun v => color (π.map v) = false

theorem red_blue_disjoint (color : Q → Bool) (reps : Finset V) :
    Disjoint (redRepresentatives (π := π) color reps) (blueVertices (π := π) color) := by
  apply Finset.disjoint_left.mpr
  intro v hr hb
  have ht := (Finset.mem_filter.mp hr).2
  have hf := (Finset.mem_filter.mp hb).2
  rw [ht] at hf
  cases hf

/-- A derived blue-row count is validated only after its three original
queries. No bound or integrality test is imposed on a raw cut answer. -/
def blueProbe (s : ParallelState π r) (color : Q → Bool) (u : V) :
    DTree (Finset V) ℝ (Option (Fin (Fintype.card V + 1))) 3 :=
  (s.residualCrossQuery {u} (blueVertices (π := π) color)).map
    (validateCount (Fintype.card V))

theorem blueProbe_eval (s : ParallelState π r) (color : Q → Bool) (u : V)
    (hu : color (π.map u) = true) (G : WeightedGraph V)
    (hs : s.usedGraph.IsSubgraph G) :
    (s.blueProbe color u).eval G.cut = validateCount (Fintype.card V)
      ((G.subtract s.usedGraph).cross {u} (blueVertices (π := π) color)) := by
  rw [blueProbe, DTree.eval_map, s.residualCrossQuery_eval G hs]
  apply Finset.disjoint_left.mpr
  intro v hv hb
  have he : v = u := Finset.mem_singleton.mp hv
  subst v
  have hf := (Finset.mem_filter.mp hb).2
  rw [hu] at hf
  cases hf

theorem blueProbe_honest (s : ParallelState π r) (color : Q → Bool) (u : V)
    (hu : color (π.map u) = true) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    ∃ k : Fin (Fintype.card V + 1),
      (s.blueProbe color u).eval G.toWeighted.cut = some k ∧
      (G.toWeighted.subtract s.usedGraph).cross {u} (blueVertices (π := π) color) =
        (k : ℕ) := by
  obtain ⟨k, hk, he⟩ := s.residual_row_count G hs u (blueVertices (π := π) color)
  refine ⟨⟨k, Nat.lt_succ_of_le hk⟩, ?_, he⟩
  rw [s.blueProbe_eval color u hu G.toWeighted hs, he]
  exact validateCount_of_nat _ _ hk

theorem blueProbe_positive_iff (s : ParallelState π r) (color : Q → Bool) (u : V)
    (hu : color (π.map u) = true) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    (∃ k : Fin (Fintype.card V + 1),
      (s.blueProbe color u).eval G.toWeighted.cut = some k ∧ 0 < k.val) ↔
    ∃ v, 0 < (G.toWeighted.subtract s.usedGraph).w u v ∧
      color (π.map v) = false := by
  constructor
  · rintro ⟨k, he, hk⟩
    rw [s.blueProbe_eval color u hu G.toWeighted hs] at he
    have hp : 0 < (G.toWeighted.subtract s.usedGraph).cross {u}
        (blueVertices (π := π) color) := by
      rw [← (validateCount_spec he).1]
      exact_mod_cast hk
    obtain ⟨a, ha, v, hv, hpv⟩ :=
      ((G.toWeighted.subtract s.usedGraph).cross_pos_iff _ _).mp hp
    have hea : a = u := Finset.mem_singleton.mp ha
    subst a
    exact ⟨v, hpv, (Finset.mem_filter.mp hv).2⟩
  · rintro ⟨v, hpv, hv⟩
    obtain ⟨k, he, hcount⟩ := s.blueProbe_honest color u hu G hs
    refine ⟨k, he, ?_⟩
    have hp : 0 < (G.toWeighted.subtract s.usedGraph).cross {u}
        (blueVertices (π := π) color) := by
      apply ((G.toWeighted.subtract s.usedGraph).cross_pos_iff _ _).mpr
      exact ⟨u, by simp, v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, hpv⟩
    rw [hcount] at hp
    exact_mod_cast hp

/-- Query precisely the red representatives. Unqueried table entries remain
`none`; invalid derived counts also remain explicit `none` values. -/
def colorRows (s : ParallelState π r) (color : Q → Bool) (reps : Finset V) :
    DTree (Finset V) ℝ (V → Option (Fin (Fintype.card V + 1)))
      ((redRepresentatives (π := π) color reps).card * 3) :=
  (((DTree.queryList (fun u : V => u) (fun _ => none)
    (redRepresentatives (π := π) color reps).toList).substitute
      (s.blueProbe color))).cast (by simp)

theorem colorRows_eval (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (read : Finset V → ℝ) (u : V) :
    (s.colorRows color reps).eval read u =
      if u ∈ redRepresentatives (π := π) color reps then
        (s.blueProbe color u).eval read else none := by
  rw [colorRows, DTree.eval_cast, DTree.eval_substitute]
  simp only [DTree.eval, DTree.queryList_run, Finset.mem_toList]

theorem colorRows_cost (s : ParallelState π r) (color : Q → Bool) (reps : Finset V)
    (read : Finset V → ℝ) : (s.colorRows color reps).cost read ≤ 3 * reps.card := by
  apply (DTree.cost_le _ _).trans
  have hc := Finset.card_filter_le reps (fun u => color (π.map u) = true)
  simpa only [redRepresentatives, Nat.mul_comm] using Nat.mul_le_mul_right 3 hc

/-- This public filter identifies the rows to be recovered. It depends on
actual queried counts and never on the hidden residual. -/
def positiveColorRows (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) : Finset V :=
  (redRepresentatives (π := π) color reps).filter fun u =>
    ∃ k, answers u = some k ∧ 0 < k.val

theorem positiveColorRows_honest (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (reps : Finset V) (tape : Finset Q → Bool) :
    positiveColorRows (π := π)
      (componentColor (s.forests (lastIndex hr)).quotient tape) reps
      ((s.colorRows (componentColor (s.forests (lastIndex hr)).quotient tape) reps).eval
        G.toWeighted.cut) = s.favorableRepresentatives hr G.toWeighted reps tape := by
  let color := componentColor (s.forests (lastIndex hr)).quotient tape
  change positiveColorRows (π := π) color reps
      ((s.colorRows color reps).eval G.toWeighted.cut) =
    reps.filter (fun u => color (π.map u) = true ∧
      ∃ v, 0 < (G.toWeighted.subtract s.usedGraph).w u v ∧ color (π.map v) = false)
  ext u
  constructor
  · intro hu
    obtain ⟨huR, k, he, hk⟩ := Finset.mem_filter.mp hu
    have hred := Finset.mem_filter.mp huR
    rw [s.colorRows_eval color reps G.toWeighted.cut u, if_pos huR] at he
    exact Finset.mem_filter.mpr ⟨hred.1, hred.2,
      (s.blueProbe_positive_iff color u hred.2 G hs).mp ⟨k, he, hk⟩⟩
  · intro hu
    obtain ⟨hu, hred, hpositive⟩ := Finset.mem_filter.mp hu
    have huR : u ∈ redRepresentatives (π := π) color reps :=
      Finset.mem_filter.mpr ⟨hu, hred⟩
    obtain ⟨k, he, hk⟩ := (s.blueProbe_positive_iff color u hred G hs).mpr hpositive
    refine Finset.mem_filter.mpr ⟨huR, k, ?_, hk⟩
    rw [s.colorRows_eval color reps G.toWeighted.cut u, if_pos huR]
    exact he

/-- The expected favorable-row lower bound now concerns the table returned
by actual original cut queries. Recovery is the next independent stage. -/
theorem colorRows_favorable_expect (s : ParallelState π r) (hr : 0 < r)
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) (reps : Finset V)
    (hrep : ∀ u ∈ reps, ∃ v,
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) ∧
        0 < (G.toWeighted.subtract s.usedGraph).w u v) :
    (reps.card : ℝ≥0∞) / 4 ≤ CutQueryComplexity.Probability.expect (componentBits (Q := Q))
      (fun tape => ((positiveColorRows (π := π)
        (componentColor (s.forests (lastIndex hr)).quotient tape) reps
        ((s.colorRows (componentColor (s.forests (lastIndex hr)).quotient tape) reps).eval
          G.toWeighted.cut)).card : ℝ≥0∞)) := by
  simp_rw [s.positiveColorRows_honest hr G hs reps]
  exact s.favorableRepresentatives_expect hr G.toWeighted reps hrep

/-- The small-degree bucket is selected from queried, validated counts.
Zero rows are excluded, and positive degrees below 10 are included. -/
def lowColorRows (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) : Finset V :=
  (positiveColorRows (π := π) color reps answers).filter fun u =>
    ∃ k, answers u = some k ∧ k.val ≤ 20

theorem lowColorRows_red (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) {u : V}
    (hu : u ∈ lowColorRows (π := π) color reps answers) :
    u ∈ reps ∧ color (π.map u) = true :=
  Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1

theorem lowColorRows_positive (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    {u : V} (hu : u ∈ lowColorRows (π := π) color reps
      ((s.colorRows color reps).eval G.toWeighted.cut)) :
    ∃ v ∈ blueVertices (π := π) color, 0 < (G.toWeighted.subtract s.usedGraph).w u v := by
  have hred := lowColorRows_red color reps _ hu
  have huR : u ∈ redRepresentatives (π := π) color reps := Finset.mem_filter.mpr hred
  obtain ⟨k, he, hk⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
  rw [s.colorRows_eval color reps G.toWeighted.cut u, if_pos huR] at he
  obtain ⟨v, hp, hv⟩ := (s.blueProbe_positive_iff color u hred.2 G hs).mp ⟨k, he, hk⟩
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, hp⟩

/-- The sparsity condition for the actual low-degree update follows from
the queried table. No hidden sparsity premise is supplied to this theorem. -/
theorem lowColorRows_degree (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted) :
    Recovery.RowSparse 20
      (s.residualMatrix
        (Function.Embedding.subtype (· ∈ lowColorRows (π := π) color reps
          ((s.colorRows color reps).eval G.toWeighted.cut)))
        (Function.Embedding.subtype (· ∈ blueVertices (π := π) color)) G) := by
  intro u
  have hred := lowColorRows_red color reps _ u.property
  have huR : u.val ∈ redRepresentatives (π := π) color reps := Finset.mem_filter.mpr hred
  obtain ⟨k, he, hk⟩ := (Finset.mem_filter.mp u.property).2
  rw [s.colorRows_eval color reps G.toWeighted.cut u.val, if_pos huR,
    s.blueProbe_eval color u.val hred.2 G.toWeighted hs] at he
  have hc := (validateCount_spec he).1
  have hm := s.residualMatrix_row
    (Function.Embedding.subtype (· ∈ lowColorRows (π := π) color reps
      ((s.colorRows color reps).eval G.toWeighted.cut)))
    (Function.Embedding.subtype (· ∈ blueVertices (π := π) color)) G hs u
  simp only [Function.Embedding.subtype_apply, Finset.univ_map_subtype,
    Finset.filter_mem_eq_inter, Finset.univ_inter] at hm
  have hkR : ((k.val : ℕ) : ℝ) ≤ 20 := by exact_mod_cast hk
  exact_mod_cast ((hm.trans hc.symm).le.trans hkR)

/-- A dimension-only number of high-degree buckets. The additional low
bucket is kept separately, so zero and bounded degrees are never forced into
the randomized degree-at-least-10 recovery primitive. -/
def highBucketCount (n : ℕ) : ℕ := 1 + Nat.clog 2 n

def highColorRows (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) (i : ℕ) : Finset V :=
  (positiveColorRows (π := π) color reps answers).filter fun u =>
    ∃ k, answers u = some k ∧ 20 < k.val ∧
      10 * 2 ^ i ≤ k.val ∧ k.val < 10 * 2 ^ (i + 1)

theorem highColorRows_red (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) (i : ℕ) {u : V}
    (hu : u ∈ highColorRows (π := π) color reps answers i) :
    u ∈ reps ∧ color (π.map u) = true :=
  Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1

/-- A degree-bucket premise for the actual residual table is obtained from
the queried count, including its lower bound. The bucket index is public. -/
theorem highColorRows_degree (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (i : ℕ) (G : SimpleInput V)
    (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (u : highColorRows (π := π) color reps
      ((s.colorRows color reps).eval G.toWeighted.cut) i) :
    let M := s.residualMatrix
      (Function.Embedding.subtype (· ∈ highColorRows (π := π) color reps
        ((s.colorRows color reps).eval G.toWeighted.cut) i))
      (Function.Embedding.subtype (· ∈ blueVertices (π := π) color)) G
    10 * 2 ^ i ≤ Recovery.measure Finset.univ (Recovery.rowVector M u) ∧
      Recovery.measure Finset.univ (Recovery.rowVector M u) ≤ 2 * (10 * 2 ^ i) := by
  have hred := highColorRows_red color reps _ i u.property
  have huR : u.val ∈ redRepresentatives (π := π) color reps := Finset.mem_filter.mpr hred
  obtain ⟨k, he, _, hklo, hkhi⟩ := (Finset.mem_filter.mp u.property).2
  rw [s.colorRows_eval color reps G.toWeighted.cut u.val, if_pos huR,
    s.blueProbe_eval color u.val hred.2 G.toWeighted hs] at he
  have hc := (validateCount_spec he).1
  have hm := s.residualMatrix_row
    (Function.Embedding.subtype (· ∈ highColorRows (π := π) color reps
      ((s.colorRows color reps).eval G.toWeighted.cut) i))
    (Function.Embedding.subtype (· ∈ blueVertices (π := π) color)) G hs u
  simp only [Function.Embedding.subtype_apply, Finset.univ_map_subtype,
    Finset.filter_mem_eq_inter, Finset.univ_inter] at hm
  have hcount : Recovery.measure Finset.univ (Recovery.rowVector
      (s.residualMatrix
        (Function.Embedding.subtype (· ∈ highColorRows (π := π) color reps
          ((s.colorRows color reps).eval G.toWeighted.cut) i))
        (Function.Embedding.subtype (· ∈ blueVertices (π := π) color)) G) u) = k.val := by
    exact_mod_cast hm.trans hc.symm
  dsimp only
  rw [hcount]
  refine ⟨hklo, ?_⟩
  rw [pow_succ] at hkhi
  nlinarith

theorem highColorRows_disjoint (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (highColorRows (π := π) color reps answers i)
      (highColorRows (π := π) color reps answers j) := by
  apply Finset.disjoint_left.mpr
  intro u hui huj
  obtain ⟨a, ha, _, hai, hia⟩ := (Finset.mem_filter.mp hui).2
  obtain ⟨b, hb, _, hbj, hjb⟩ := (Finset.mem_filter.mp huj).2
  have he : a = b := Option.some.inj (ha.symm.trans hb)
  subst b
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hp : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hh := Nat.mul_le_mul_left 10 hp
    omega
  · have hp : (2 : ℕ) ^ (j + 1) ≤ 2 ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hh := Nat.mul_le_mul_left 10 hp
    omega

theorem low_highColorRows_disjoint (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) (i : ℕ) :
    Disjoint (lowColorRows (π := π) color reps answers)
      (highColorRows (π := π) color reps answers i) := by
  apply Finset.disjoint_left.mpr
  intro u hul huh
  obtain ⟨a, ha, hla⟩ := (Finset.mem_filter.mp hul).2
  obtain ⟨b, hb, hhb, _, _⟩ := (Finset.mem_filter.mp huh).2
  have he : a = b := Option.some.inj (ha.symm.trans hb)
  subst b
  omega

/-- The bounded validated answer itself places each positive row in a
dimension-bounded bucket, on every oracle path, even before honesty is used. -/
theorem colorRows_bucket_cover (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) {u : V}
    (hu : u ∈ positiveColorRows (π := π) color reps answers) :
    u ∈ lowColorRows (π := π) color reps answers ∨
      ∃ i : Fin (highBucketCount (Fintype.card V)),
        u ∈ highColorRows (π := π) color reps answers i.val := by
  obtain ⟨k, hk, hkpos⟩ := (Finset.mem_filter.mp hu).2
  by_cases hlow : k.val ≤ 20
  · exact Or.inl (Finset.mem_filter.mpr ⟨hu, k, hk, hlow⟩)
  · have hhigh : 20 < k.val := by omega
    let i := Nat.log 2 (k.val / 10)
    have hquot : 0 < k.val / 10 := Nat.div_pos (by omega) (by norm_num)
    have hmin : 10 * 2 ^ i ≤ k.val := by
      have hh := (Nat.le_div_iff_mul_le (by norm_num : 0 < (10 : ℕ))).mp
        (Nat.pow_log_le_self 2 (Nat.ne_of_gt hquot))
      simpa only [i, Nat.mul_comm] using hh
    have hmax : k.val < 10 * 2 ^ (i + 1) := by
      have hh := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (10 : ℕ))).mp
        (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (k.val / 10))
      simpa only [i, Nat.succ_eq_add_one, Nat.mul_comm] using hh
    have hi : i < highBucketCount (Fintype.card V) := by
      have hm : i ≤ Nat.clog 2 (Fintype.card V) :=
        (Nat.log_mono_right ((Nat.div_le_self k.val 10).trans
          (Nat.le_of_lt_succ k.isLt))).trans (Nat.log_le_clog 2 (Fintype.card V))
      unfold highBucketCount
      omega
    exact Or.inr ⟨⟨i, hi⟩, Finset.mem_filter.mpr ⟨hu, k, hk, hhigh, hmin, hmax⟩⟩

/-- `none` names the deterministic low bucket; `some i` names a high bucket.
This entire partition is computed from the public returned count table. -/
def colorBucket (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) :
    Option (Fin (highBucketCount (Fintype.card V))) → Finset V
  | none => lowColorRows (π := π) color reps answers
  | some i => highColorRows (π := π) color reps answers i.val

theorem colorBucket_disjoint (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1)))
    {i j : Option (Fin (highBucketCount (Fintype.card V)))} (hij : i ≠ j) :
    Disjoint (colorBucket (π := π) color reps answers i)
      (colorBucket (π := π) color reps answers j) := by
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact low_highColorRows_disjoint color reps answers j.val
  | some i =>
      cases j with
      | none => exact (low_highColorRows_disjoint color reps answers i.val).symm
      | some j =>
          apply highColorRows_disjoint color reps answers
          intro he
          exact hij (congrArg some (Fin.ext he))

theorem colorBucket_union (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) :
    Finset.univ.biUnion (colorBucket (π := π) color reps answers) =
      positiveColorRows (π := π) color reps answers := by
  ext u
  constructor
  · intro hu
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hu
    cases i with
    | none => exact (Finset.mem_filter.mp hi).1
    | some i => exact (Finset.mem_filter.mp hi).1
  · intro hu
    rcases colorRows_bucket_cover color reps answers hu with hlo | ⟨i, hi⟩
    · exact Finset.mem_biUnion.mpr ⟨none, Finset.mem_univ _, hlo⟩
    · exact Finset.mem_biUnion.mpr ⟨some i, Finset.mem_univ _, hi⟩

/-- The joint bucket-size constraint follows from the actual query-defined
partition. It is not a supplied list of sizes in the eventual cost proof. -/
theorem colorBucket_card_sum (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) :
    (∑ i, (colorBucket (π := π) color reps answers i).card) =
      (positiveColorRows (π := π) color reps answers).card := by
  have hd : ((Finset.univ : Finset (Option (Fin (highBucketCount (Fintype.card V))))) :
      Set (Option (Fin (highBucketCount (Fintype.card V))))).PairwiseDisjoint
        (colorBucket (π := π) color reps answers) := by
    intro i _ j _ hij
    exact colorBucket_disjoint color reps answers hij
  have hh := Finset.card_biUnion hd
  rw [colorBucket_union] at hh
  exact hh.symm

theorem colorBucket_card_sum_le (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1))) :
    (∑ i, (colorBucket (π := π) color reps answers i).card) ≤ reps.card := by
  rw [colorBucket_card_sum]
  exact (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)

/-- The real logarithmic count includes both rounding and the low bucket.
It applies in the public large-n branch; no base-two factor is dropped. -/
theorem colorBucket_slots_le (hn : 1 ≤ Fintype.card V)
    (hl : 3 ≤ Real.log (Fintype.card V : ℝ)) :
    (Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) : ℝ) ≤
      3 * Real.log (Fintype.card V : ℝ) := by
  have hc := Schedule.clog_le_twice_log_add_one (Fintype.card V) hn
  rw [Fintype.card_option, Fintype.card_fin]
  simp only [highBucketCount, Nat.cast_add, Nat.cast_one]
  linarith

/-- The sharp row-weight estimate is instantiated with the actual public
bucket partition, including empty buckets and small favorable subsets. -/
theorem colorBucket_rowWeight_sum (color : Q → Bool) (reps : Finset V)
    (answers : V → Option (Fin (Fintype.card V + 1)))
    (hslots : Fintype.card (Option (Fin (highBucketCount (Fintype.card V)))) ≤ reps.card) :
    (∑ i, parallelRowWeight ((colorBucket (π := π) color reps answers i).card)) ≤
      4 * reps.card / Real.log (2 * (reps.card : ℝ) /
        Fintype.card (Option (Fin (highBucketCount (Fintype.card V))))) := by
  let I := Option (Fin (highBucketCount (Fintype.card V)))
  have hJ : (0 : ℝ) < Fintype.card I := by
    simp only [I, Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    positivity
  have hslotsR : (Fintype.card I : ℝ) ≤ reps.card := by exact_mod_cast hslots
  have hs : 1 ≤ (reps.card : ℝ) / Fintype.card I :=
    (le_div_iff₀ hJ).mpr (by simpa using hslotsR)
  have hm : (∑ i, ((colorBucket (π := π) color reps answers i).card : ℝ)) ≤ reps.card := by
    exact_mod_cast colorBucket_card_sum_le color reps answers
  have hJmul : (Fintype.card I : ℝ) * ((reps.card : ℝ) / Fintype.card I) ≤ reps.card := by
    have he : (Fintype.card I : ℝ) * ((reps.card : ℝ) / Fintype.card I) = reps.card := by
      field_simp
    exact he.le
  have hh := parallelRowWeight_sum
    (fun i => (colorBucket (π := π) color reps answers i).card)
    (reps.card : ℝ) ((reps.card : ℝ) / Fintype.card I) hs hm hJmul
  simpa only [mul_div_assoc] using hh

/-- Choose a neighbor only from an actually decoded public Boolean table.
This is local finite computation; it issues no graph-dependent query. -/
def learnedNext (rows cols : Finset V) (M : Recovery.BooleanMatrix rows cols)
    (u : V) : Option V :=
  if hu : u ∈ rows then
    if hv : ∃ v : cols, M ⟨u, hu⟩ v = true then some (Classical.choose hv).val else none
  else none

theorem learnedNext_residual_some (s : ParallelState π r) (rows cols : Finset V)
    (G : SimpleInput V) {u v : V}
    (hout : learnedNext rows cols
      (s.residualMatrix (Function.Embedding.subtype _) (Function.Embedding.subtype _) G) u =
        some v) :
    u ∈ rows ∧ v ∈ cols ∧ 0 < (G.toWeighted.subtract s.usedGraph).w u v := by
  unfold learnedNext at hout
  split at hout
  next hu =>
    split at hout
    next hv =>
      have he : (Classical.choose hv).val = v := Option.some.inj hout
      have hp := Classical.choose_spec hv
      have hw : 0 < (G.toWeighted.subtract s.usedGraph).w u (Classical.choose hv).val := by
        change decide (0 < (G.toWeighted.subtract s.usedGraph).w u
          (Classical.choose hv).val) = true at hp
        exact of_decide_eq_true hp
      exact ⟨hu, he ▸ (Classical.choose hv).property, he ▸ hw⟩
    next hv => cases hout
  next hu => cases hout

theorem learnedNext_residual_complete (s : ParallelState π r) (rows cols : Finset V)
    (G : SimpleInput V) {u : V} (hu : u ∈ rows)
    (hpositive : ∃ v ∈ cols, 0 < (G.toWeighted.subtract s.usedGraph).w u v) :
    ∃ v, learnedNext rows cols
      (s.residualMatrix (Function.Embedding.subtype _) (Function.Embedding.subtype _) G) u =
        some v := by
  obtain ⟨v, hv, hp⟩ := hpositive
  have hex : ∃ w : cols,
      s.residualMatrix (Function.Embedding.subtype _) (Function.Embedding.subtype _) G
        (⟨u, hu⟩ : rows) w = true := by
    exact ⟨⟨v, hv⟩, by simp [residualMatrix, hp]⟩
  exact ⟨(Classical.choose hex).val, by simp only [learnedNext, dif_pos hu, dif_pos hex]⟩

/-- The complete small-degree insertion stage: query degrees, decode the
true residual table, select actual original neighbors, and run least-layer
insertion. High-degree or invalid answers cause explicit rejection. -/
def lowRowUpdateBudget (rows cols : Finset V) : ℕ :=
  Fintype.card rows * 3 +
    Recovery.sparseRawBudget rows cols (min 20 (Fintype.card cols)) * 3

def lowRowUpdate (s : ParallelState π r) (color : Q → Bool) (rows : Finset V) :
    DTree (Finset V) ℝ (Option (ParallelState π r))
      (lowRowUpdateBudget rows (blueVertices (π := π) color)) :=
  (s.checkedLowDegreeResidual (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ blueVertices (π := π) color))).map fun out =>
      out.bind fun M => s.assembleNeighbors color rows
        (learnedNext rows (blueVertices (π := π) color) M)

theorem lowRowUpdate_every_oracle (s : ParallelState π r) (color : Q → Bool)
    (rows : Finset V) (read : Finset V → ℝ) :
    (s.lowRowUpdate color rows).cost read ≤
      lowRowUpdateBudget rows (blueVertices (π := π) color) := DTree.cost_le _ _

/-- Empty buckets make no cut query. This handles the zero-row case before
using any real logarithmic estimate for a positive row count. -/
theorem lowRowUpdate_empty_cost (s : ParallelState π r) (color : Q → Bool)
    (read : Finset V → ℝ) : (s.lowRowUpdate color ∅).cost read = 0 := by
  let cols := blueVertices (π := π) color
  have hraw : Recovery.sparseRawBudget (∅ : Finset V) cols (min 20 (Fintype.card cols)) = 0 := by
    have hh : Recovery.sparseRawBudget (∅ : Finset V) cols (min 20 (Fintype.card cols)) ≤
        Fintype.card (∅ : Finset V) * Fintype.card cols :=
      Nat.mul_le_mul (Recovery.minimumFamily_card_le_dimension
        (Recovery.box (∅ : Finset V) (min 20 (Fintype.card cols))))
        (Recovery.minimumFamily_card_le_dimension
          (Recovery.sparse cols (min 20 (Fintype.card cols))))
    exact Nat.eq_zero_of_le_zero (by
      simpa only [Fintype.card_coe, Finset.card_empty, Nat.zero_mul] using hh)
  have hh := s.lowRowUpdate_every_oracle color ∅ read
  change (s.lowRowUpdate color ∅).cost read ≤ lowRowUpdateBudget ∅ cols at hh
  have hbudget : lowRowUpdateBudget (∅ : Finset V) cols = 0 := by
    unfold lowRowUpdateBudget
    rw [hraw]
    simp only [Fintype.card_coe, Finset.card_empty, Nat.zero_mul, Nat.add_zero]
  exact Nat.eq_zero_of_le_zero (hh.trans hbudget.le)

/-- Every small-degree positive row is processed by the real query program.
The hypotheses concern residual degrees and component membership; the output
forest, inserted edges, and potential decrease are conclusions. -/
theorem lowRowUpdate_honest (s : ParallelState π r) (hr : 0 < r)
    (hl : s.Laminar) (color : Q → Bool) (rows : Finset V)
    (hred : ∀ u ∈ rows, color (π.map u) = true)
    (hcolor : ∀ u v, (s.forests (lastIndex hr)).quotient.Reachable u v → color u = color v)
    (hsep : ∀ u ∈ rows, ∀ v ∈ rows, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted)
    (hpositive : ∀ u ∈ rows, ∃ v ∈ blueVertices (π := π) color,
      0 < (G.toWeighted.subtract s.usedGraph).w u v)
    (hdegree : Recovery.RowSparse 20
      (s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
        (Function.Embedding.subtype (· ∈ blueVertices (π := π) color)) G)) :
    ∃ t, (s.lowRowUpdate color rows).eval G.toWeighted.cut = some t ∧ t.Laminar ∧
      t.usedGraph.IsSubgraph G.toWeighted ∧ t.InactiveSound hr G.toWeighted ∧
      t.edgeCount = s.edgeCount + rows.card ∧
      t.livePotential + rows.card ≤ s.livePotential := by
  let cols := blueVertices (π := π) color
  let M := s.residualMatrix (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ cols)) G
  let next := learnedNext rows cols M
  have hdis : ∀ u : rows, ∀ v : cols, u.val ≠ v.val := by
    intro u v he
    have ht := hred u.val u.property
    have hf := (Finset.mem_filter.mp v.property).2
    rw [he, hf] at ht
    cases ht
  have hlearn := s.checkedLowDegreeResidual_correct
    (Function.Embedding.subtype (· ∈ rows)) (Function.Embedding.subtype (· ∈ cols))
    hdis G hs hdegree
  have htab : NeighborTable (π := π) color rows next := by
    intro u hu
    obtain ⟨v, hv⟩ := s.learnedNext_residual_complete rows cols G hu (hpositive u hu)
    have hvprop := s.learnedNext_residual_some rows cols G hv
    exact ⟨v, hv, hred u hu, (Finset.mem_filter.mp hvprop.2.1).2⟩
  have hp : ∀ u ∈ rows, ∀ v, next u = some v →
      0 < (G.toWeighted.subtract s.usedGraph).w u v := by
    intro u hu v hv
    exact (s.learnedNext_residual_some rows cols G hv).2.2
  obtain ⟨t, ht, htl, hts, hti, hcount, hpot⟩ :=
    s.assembleNeighbors_honest hr hl color rows next htab hcolor hsep G hs hi hp
  refine ⟨t, ?_, htl, hts, hti, hcount, hpot⟩
  change ((s.checkedLowDegreeResidual (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ cols))).map (fun out =>
      out.bind fun M => s.assembleNeighbors color rows (learnedNext rows cols M))).eval
        G.toWeighted.cut = some t
  rw [DTree.eval_map, hlearn]
  exact ht

theorem lowRowUpdate_cost_bound (s : ParallelState π r) (color : Q → Bool)
    (rows : Finset V) (hm : 1 ≤ rows.card)
    (hc : 1 ≤ (blueVertices (π := π) color).card) (read : Finset V → ℝ) :
    ((s.lowRowUpdate color rows).cost read : ℝ) ≤ 3 * rows.card +
      1006632960 * rows.card * Real.log (2 * ((blueVertices (π := π) color).card : ℝ)) /
        Real.log (2 * (rows.card : ℝ)) := by
  change (((s.checkedLowDegreeResidual (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ blueVertices (π := π) color))).map (fun out =>
      out.bind fun M => s.assembleNeighbors color rows
        (learnedNext rows (blueVertices (π := π) color) M))).cost read : ℝ) ≤ _
  rw [det_cost_map]
  simpa only [Fintype.card_coe] using s.checkedLowDegreeResidual_cost_bound
    (Function.Embedding.subtype (· ∈ rows))
    (Function.Embedding.subtype (· ∈ blueVertices (π := π) color))
    (by simpa only [Fintype.card_coe] using hm)
    (by simpa only [Fintype.card_coe] using hc) read

/-- A public finite index for composition. Expected-cost arguments use the
sharp actual-cost lemmas, rather than this deliberately coarse index. -/
theorem lowRowUpdateBudget_le (rows cols : Finset V) :
    lowRowUpdateBudget rows cols ≤ 3 * Fintype.card V + 3 * Fintype.card V * Fintype.card V := by
  have hrows : Fintype.card rows ≤ Fintype.card V := Fintype.card_subtype_le _
  have hcols : Fintype.card cols ≤ Fintype.card V := Fintype.card_subtype_le _
  have hsparse : Recovery.sparseRawBudget rows cols (min 20 (Fintype.card cols)) ≤
      Fintype.card rows * Fintype.card cols :=
    Nat.mul_le_mul (Recovery.minimumFamily_card_le_dimension
      (Recovery.box rows (min 20 (Fintype.card cols))))
      (Recovery.minimumFamily_card_le_dimension
        (Recovery.sparse cols (min 20 (Fintype.card cols))))
  have hh := Nat.mul_le_mul hrows hcols
  unfold lowRowUpdateBudget
  nlinarith

/-- This finite program obtains the small-degree bucket from actual query
answers and immediately processes it. Its constructor takes only public data. -/
def colorLowUpdate (s : ParallelState π r) (color : Q → Bool) (reps : Finset V) :
    DTree (Finset V) ℝ (Option (ParallelState π r))
      (3 * Fintype.card V + (3 * Fintype.card V + 3 * Fintype.card V * Fintype.card V)) :=
  ((s.colorRows color reps).weaken (by
    have hh := Finset.card_le_univ (redRepresentatives (π := π) color reps)
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 3 hh)).bind fun answers =>
      (s.lowRowUpdate color (lowColorRows (π := π) color reps answers)).weaken
        (lowRowUpdateBudget_le _ _)

theorem colorLowUpdate_eval (s : ParallelState π r) (color : Q → Bool)
    (reps : Finset V) (read : Finset V → ℝ) :
    (s.colorLowUpdate color reps).eval read =
      (s.lowRowUpdate color (lowColorRows (π := π) color reps
        ((s.colorRows color reps).eval read))).eval read := by
  have hhead : (redRepresentatives (π := π) color reps).card * 3 ≤
      3 * Fintype.card V := by
    have hh := Finset.card_le_univ (redRepresentatives (π := π) color reps)
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 3 hh
  let first : DTree (Finset V) ℝ (V → Option (Fin (Fintype.card V + 1)))
      (3 * Fintype.card V) := (s.colorRows color reps).weaken hhead
  let next : (V → Option (Fin (Fintype.card V + 1))) →
      DTree (Finset V) ℝ (Option (ParallelState π r))
        (3 * Fintype.card V + 3 * Fintype.card V * Fintype.card V) := fun answers =>
    (s.lowRowUpdate color (lowColorRows (π := π) color reps answers)).weaken
      (lowRowUpdateBudget_le _ _)
  have hfirst : first.eval read = (s.colorRows color reps).eval read :=
    congrArg Prod.fst (DTree.run_weaken hhead (s.colorRows color reps) read)
  have hnext (answers : V → Option (Fin (Fintype.card V + 1))) :
      (next answers).eval read =
        (s.lowRowUpdate color (lowColorRows (π := π) color reps answers)).eval read :=
    congrArg Prod.fst (DTree.run_weaken (lowRowUpdateBudget_le _ _)
      (s.lowRowUpdate color (lowColorRows (π := π) color reps answers)) read)
  change (first.bind next).eval read = _
  rw [DTree.eval_bind, hfirst]
  exact hnext _

/-- An actual two-stage query program discharges the low-degree premise.
The theorem has no supplied neighbor table, sparsity, certificate, or cost
assumption. Every inserted name comes from the decoded original residual. -/
theorem colorLowUpdate_honest (s : ParallelState π r) (hr : 0 < r)
    (hl : s.Laminar) (color : Q → Bool) (reps : Finset V)
    (hcolor : ∀ u v, (s.forests (lastIndex hr)).quotient.Reachable u v → color u = color v)
    (hsep : ∀ u ∈ reps, ∀ v ∈ reps, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v))
    (G : SimpleInput V) (hs : s.usedGraph.IsSubgraph G.toWeighted)
    (hi : s.InactiveSound hr G.toWeighted) :
    ∃ t, (s.colorLowUpdate color reps).eval G.toWeighted.cut = some t ∧ t.Laminar ∧
      t.usedGraph.IsSubgraph G.toWeighted ∧ t.InactiveSound hr G.toWeighted ∧
      t.edgeCount = s.edgeCount + (lowColorRows (π := π) color reps
        ((s.colorRows color reps).eval G.toWeighted.cut)).card ∧
      t.livePotential + (lowColorRows (π := π) color reps
        ((s.colorRows color reps).eval G.toWeighted.cut)).card ≤ s.livePotential := by
  let rows := lowColorRows (π := π) color reps ((s.colorRows color reps).eval G.toWeighted.cut)
  have hred : ∀ u ∈ rows, color (π.map u) = true :=
    fun u hu => (lowColorRows_red color reps _ hu).2
  have hsep' : ∀ u ∈ rows, ∀ v ∈ rows, u ≠ v →
      ¬(s.forests (lastIndex hr)).quotient.Reachable (π.map u) (π.map v) := by
    intro u hu v hv hne
    exact hsep u (lowColorRows_red color reps _ hu).1 v
      (lowColorRows_red color reps _ hv).1 hne
  obtain ⟨t, ht, htl, hts, hti, hcount, hpot⟩ :=
    s.lowRowUpdate_honest hr hl color rows hred hcolor hsep' G hs hi
      (fun u hu => s.lowColorRows_positive color reps G hs hu)
      (s.lowColorRows_degree color reps G hs)
  exact ⟨t, (s.colorLowUpdate_eval color reps G.toWeighted.cut).trans ht,
    htl, hts, hti, hcount, hpot⟩

end ParallelState

#print axioms ParallelState.red_blue_disjoint
#print axioms ParallelState.blueProbe_honest
#print axioms ParallelState.blueProbe_positive_iff
#print axioms ParallelState.colorRows_eval
#print axioms ParallelState.colorRows_cost
#print axioms ParallelState.positiveColorRows_honest
#print axioms ParallelState.colorRows_favorable_expect
#print axioms ParallelState.lowColorRows_positive
#print axioms ParallelState.lowColorRows_degree
#print axioms ParallelState.highColorRows_degree
#print axioms ParallelState.highColorRows_disjoint
#print axioms ParallelState.low_highColorRows_disjoint
#print axioms ParallelState.colorRows_bucket_cover
#print axioms ParallelState.colorBucket_disjoint
#print axioms ParallelState.colorBucket_union
#print axioms ParallelState.colorBucket_card_sum
#print axioms ParallelState.colorBucket_card_sum_le
#print axioms ParallelState.colorBucket_slots_le
#print axioms ParallelState.colorBucket_rowWeight_sum
#print axioms ParallelState.learnedNext_residual_some
#print axioms ParallelState.learnedNext_residual_complete
#print axioms ParallelState.lowRowUpdate_every_oracle
#print axioms ParallelState.lowRowUpdate_empty_cost
#print axioms ParallelState.lowRowUpdate_honest
#print axioms ParallelState.lowRowUpdate_cost_bound
#print axioms ParallelState.lowRowUpdateBudget_le
#print axioms ParallelState.colorLowUpdate_eval
#print axioms ParallelState.colorLowUpdate_honest

end
end CutQueryComplexity.StarContraction2022.Certificates
