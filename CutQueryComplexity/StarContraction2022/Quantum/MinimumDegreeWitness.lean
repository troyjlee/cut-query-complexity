import CutQueryComplexity.StarContraction2022.Quantum.TaggedQuery
import CutQueryComplexity.StarContraction2022.Quantum.MinimumDegree
import CutQueryComplexity.Problem.Basic
import Mathlib.Data.Prod.Lex

/-! # Public quantum minimum-degree vertex with a verified singleton value

The ordered letter contains a degree and its public vertex index. Read-all
establishes attainability before the cardinality-free maximum theorem supplies
a bounded native circuit. The circuit is padded, repeated by physical plurality,
and transported by the proved two-query tagged adapter. One final physical
singleton query guarantees truthful outputs on every table, including failed
minimum-finding runs. Every construction precedes the table or hidden graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum
noncomputable section
open QuantumQueryComplexity
open scoped Matrix

local instance witnessBasisDecidableEq {I A W : Type} [DecidableEq I]
    [DecidableEq A] [DecidableEq W] : DecidableEq (QBasis I A W) :=
  inferInstanceAs (DecidableEq (Option I × Option A × W))

local instance witnessPQDecidableEq {I A W : Type} [DecidableEq I]
    [DecidableEq A] [DecidableEq W] (k : ℕ) : DecidableEq (PQWork I A W k) :=
  inferInstanceAs (DecidableEq (W × (Option I × Option A) × (Fin k → Option A)))

/-- Lexicographic value/index alphabet; reversing its order finds the minimum
value and then the least public vertex attaining that value. -/
abbrev DegreeTag (n : ℕ) := CutAnswer n 1 ×ₗ Fin n

def degreeTag {n : ℕ} (v : Fin n) (a : CutAnswer n 1) : DegreeTag n := toLex (a, v)

def singletonTaggedRead (n : ℕ) (read : Finset (Fin n) → CutAnswer n 1) :
    Fin n → DegreeTag n := fun v => degreeTag v (read {v})

def minimumTagged (n : ℕ) (hn : 0 < n) (x : Fin n → DegreeTag n) : DegreeTag n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact maxFun (A := OrderDual (DegreeTag n)) x

theorem minimumTagged_le (n : ℕ) (hn : 0 < n) (x : Fin n → DegreeTag n) (v : Fin n) :
    minimumTagged n hn x ≤ x v := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact le_maxFun (A := OrderDual (DegreeTag n)) x v

theorem minimumTagged_attained (n : ℕ) (hn : 0 < n) (x : Fin n → DegreeTag n) :
    ∃ v, x v = minimumTagged n hn x := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact exists_eq_maxFun (A := OrderDual (DegreeTag n)) x

/-- The target letter itself contains a vertex with its actual singleton value. -/
theorem minimumTagged_singleton_spec (n : ℕ) (hn : 0 < n)
    (read : Finset (Fin n) → CutAnswer n 1) :
    let m := minimumTagged n hn (singletonTaggedRead n read)
    (ofLex m).1 = read {(ofLex m).2} ∧ ∀ v, (ofLex m).1 ≤ read {v} := by
  dsimp only
  constructor
  · obtain ⟨v, hv⟩ := minimumTagged_attained n hn (singletonTaggedRead n read)
    rw [← hv]
    rfl
  · intro v
    exact Prod.Lex.monotone_fst _ _ (minimumTagged_le n hn (singletonTaggedRead n read) v)

theorem minimumTagged_tie_break (n : ℕ) (hn : 0 < n)
    (read : Finset (Fin n) → CutAnswer n 1) (v : Fin n)
    (hv : read {v} = (ofLex (minimumTagged n hn (singletonTaggedRead n read))).1) :
    (ofLex (minimumTagged n hn (singletonTaggedRead n read))).2 ≤ v := by
  have h := (Prod.Lex.le_iff).mp (minimumTagged_le n hn (singletonTaggedRead n read) v)
  rcases h with h | h
  · exact False.elim ((ne_of_lt h) hv.symm)
  · exact h.2

theorem minimumTagged_value (n : ℕ) (hn : 0 < n)
    (read : Finset (Fin n) → CutAnswer n 1) :
    (ofLex (minimumTagged n hn (singletonTaggedRead n read))).1 =
      minimumSingletonValue n read := by
  have h := minimumTagged_singleton_spec n hn read
  apply le_antisymm
  · obtain ⟨v, hv⟩ := minimumSingletonValue_attained n hn read
    exact (h.2 v).trans_eq hv
  · rw [h.1]
    exact minimumSingletonValue_le n hn read _

def taggedMinimumReadAll (n : ℕ) (hn : 0 < n) :
    QAlg (Fin n) (DegreeTag n) (DegreeTag n) (QRec (Fin n) (DegreeTag n)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact readAllAlg (recDecode id (minimumTagged n hn))

theorem taggedMinimumReadAll_prob (n : ℕ) (hn : 0 < n) (x : Fin n → DegreeTag n) :
    (taggedMinimumReadAll n hn).prob x n (minimumTagged n hn x) = 1 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hd := recDecode_apply (read := id) (f := minimumTagged n hn)
    (fun a b h => congrArg (minimumTagged n hn) h) x
  change recDecode id (minimumTagged n hn) (fun i => some (x i)) = minimumTagged n hn x at hd
  have hp := readAllAlg_prob (recDecode id (minimumTagged n hn)) x
  rw [hd] at hp
  simpa only [taggedMinimumReadAll, Fintype.card_fin] using hp

theorem minimumTagged_counts_nonempty (n : ℕ) (hn : 0 < n) :
    (QueryCounts id (minimumTagged n hn) (1 / 3)).Nonempty := by
  refine ⟨n, mem_queryCounts (A := taggedMinimumReadAll n hn) ?_⟩
  intro x
  change 1 - (1 / 3 : ℝ) ≤ (taggedMinimumReadAll n hn).prob x n (minimumTagged n hn x)
  rw [taggedMinimumReadAll_prob]
  norm_num

/-- The existing bound is uniform in the enlarged tagged alphabet. -/
theorem minimumTagged_qQuery_le (n : ℕ) (hn : 0 < n) :
    qQuery (minimumTagged n hn) (1 / 3) ≤ minimumDegreeBaseBudget n := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hlength : qQuery (minimumTagged n hn) (1 / 3) ≤ n := by
    change qQuery (maxFun (ι := Fin n) (A := OrderDual (DegreeTag n))) (1 / 3) ≤ n
    simpa only [Fintype.card_fin] using
      (max_qQuery_upper_length (ι := Fin n) (A := OrderDual (DegreeTag n)))
  have hupper : (qQuery (minimumTagged n hn) (1 / 3) : ℝ) ≤
      8192 * (1 + 24 * Real.sqrt (n : ℝ)) := by
    change (qQuery (maxFun (ι := Fin n) (A := OrderDual (DegreeTag n)))
      (1 / 3) : ℝ) ≤ 8192 * (1 + 24 * Real.sqrt (n : ℝ))
    simpa only [Fintype.card_fin, uniformExtractionConstant] using
      (max_qQuery_upper (ι := Fin n) (A := OrderDual (DegreeTag n)))
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn'
  have hbound : (qQuery (minimumTagged n hn) (1 / 3) : ℝ) ≤
      204800 * Real.sqrt (n : ℝ) := by nlinarith
  have hceil : qQuery (minimumTagged n hn) (1 / 3) ≤
      ⌈204800 * Real.sqrt (n : ℝ)⌉₊ := by
    exact_mod_cast hbound.trans (Nat.le_ceil _)
  exact le_min hlength hceil

theorem exists_minimumTagged_base (n : ℕ) (hn : 0 < n) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : QAlg (Fin n) (DegreeTag n) (DegreeTag n) Work),
      ComputesWithErrorOn T (minimumDegreeBaseBudget n) id (minimumTagged n hn) (1 / 3) := by
  obtain ⟨Work, hF, hD, T, hT⟩ := exists_computes_qQueryOn (minimumTagged_counts_nonempty n hn)
  let := hF
  let := hD
  have hle := minimumTagged_qQuery_le n hn
  have hsplit : qQuery (minimumTagged n hn) (1 / 3) +
      (minimumDegreeBaseBudget n - qQuery (minimumTagged n hn) (1 / 3)) =
      minimumDegreeBaseBudget n := by omega
  refine ⟨CtrlWork (Fin n) Work, inferInstance, inferInstance,
    padAlg T (qQuery (minimumTagged n hn) (1 / 3))
      (minimumDegreeBaseBudget n - qQuery (minimumTagged n hn) (1 / 3)), ?_⟩
  simpa only [hsplit] using computesWithErrorOn_padAlg hT
    (minimumDegreeBaseBudget n - qQuery (minimumTagged n hn) (1 / 3))

theorem exists_minimumTagged_repeated (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : QAlg (Fin n) (DegreeTag n) (DegreeTag n) Work),
      ComputesWithErrorOn T (2 * t * minimumDegreeBaseBudget n) id
        (minimumTagged n hn) ((8 / 9 : ℝ) ^ t) := by
  obtain ⟨Work, hF, hD, T, hT⟩ :=
    amplify_plurality (exists_minimumTagged_base n hn) (2 * t - 1)
  have hcopies : 2 * t - 1 + 1 = 2 * t := by omega
  have hhalf : (2 * t - 1 + 2) / 2 = t := by omega
  have herr : (1 + (1 / 3 : ℝ)) ^ (2 * t) / 2 ^ t = (8 / 9 : ℝ) ^ t := by
    rw [pow_mul, ← div_pow]
    norm_num
  exact ⟨Work, hF, hD, T, by simpa only [hcopies, hhalf, herr] using hT⟩

def minimumTaggedWork (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t) : Type :=
  (exists_minimumTagged_repeated n hn t ht).choose

instance minimumTaggedWorkFintype (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t) :
    Fintype (minimumTaggedWork n hn t ht) :=
  (exists_minimumTagged_repeated n hn t ht).choose_spec.choose

instance minimumTaggedWorkDecidableEq (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t) :
    DecidableEq (minimumTaggedWork n hn t ht) :=
  (exists_minimumTagged_repeated n hn t ht).choose_spec.choose_spec.choose

def minimumTaggedAlg (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t) :
    QAlg (Fin n) (DegreeTag n) (DegreeTag n) (minimumTaggedWork n hn t ht) :=
  (exists_minimumTagged_repeated n hn t ht).choose_spec.choose_spec.choose_spec.choose

theorem minimumTaggedAlg_correct (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (x : Fin n → DegreeTag n) :
    1 - (8 / 9 : ℝ) ^ t ≤ (minimumTaggedAlg n hn t ht).prob x
      (2 * t * minimumDegreeBaseBudget n) (minimumTagged n hn x) :=
  (exists_minimumTagged_repeated n hn t ht).choose_spec.choose_spec.choose_spec.choose_spec x

/-- Public physical circuit, before any singleton answer table is supplied. -/
def minimumWitnessRaw (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t) :
    CutQAlg n 1 (DegreeTag n) (QBasis (Fin n) (DegreeTag n) (minimumTaggedWork n hn t ht)) :=
  taggedAlg (fun v : Fin n => ({v} : Finset (Fin n))) degreeTag
    (minimumTaggedAlg n hn t ht) (2 * t * minimumDegreeBaseBudget n)

theorem minimumWitnessRaw_state (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) :
    (minimumWitnessRaw n hn t ht).state read (4 * t * minimumDegreeBaseBudget n) =
      taggedEmbed ((minimumTaggedAlg n hn t ht).state (singletonTaggedRead n read)
        (2 * t * minimumDegreeBaseBudget n)) := by
  have h := taggedAlg_state (fun v : Fin n => ({v} : Finset (Fin n))) degreeTag
      (minimumTaggedAlg n hn t ht) (2 * t * minimumDegreeBaseBudget n) read
  rw [show 2 * (2 * t * minimumDegreeBaseBudget n) = 4 * t * minimumDegreeBaseBudget n by ring] at h
  exact h

theorem minimumWitnessRaw_prob (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) (o : DegreeTag n) :
    (minimumWitnessRaw n hn t ht).prob read (4 * t * minimumDegreeBaseBudget n) o =
      (minimumTaggedAlg n hn t ht).prob (singletonTaggedRead n read)
        (2 * t * minimumDegreeBaseBudget n) o := by
  have h := taggedAlg_prob (fun v : Fin n => ({v} : Finset (Fin n))) degreeTag
      (minimumTaggedAlg n hn t ht) (2 * t * minimumDegreeBaseBudget n) read o
  rw [show 2 * (2 * t * minimumDegreeBaseBudget n) = 4 * t * minimumDegreeBaseBudget n by ring] at h
  exact h

theorem minimumWitnessRaw_correct (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) :
    1 - (8 / 9 : ℝ) ^ t ≤ (minimumWitnessRaw n hn t ht).prob read
      (4 * t * minimumDegreeBaseBudget n) (minimumTagged n hn (singletonTaggedRead n read)) := by
  rw [minimumWitnessRaw_prob]
  exact minimumTaggedAlg_correct n hn t ht _

abbrev DegreeWitness (n : ℕ) := Option (Fin n × CutAnswer n 1)

/-- The verification query depends only on the announced public vertex. -/
def witnessVerifySelect {n : ℕ} (o : DegreeTag n) (_ : Fin 1) : Option (Finset (Fin n)) :=
  some {(ofLex o).2}

def witnessVerifyDecode {n : ℕ} (o : DegreeTag n) (ans : Fin 1 → Option (CutAnswer n 1)) :
    DegreeWitness n := (ans 0).map (fun a => ((ofLex o).2, a))

theorem witnessVerifyDecode_read {n : ℕ} (o : DegreeTag n)
    (read : Finset (Fin n) → CutAnswer n 1) :
    witnessVerifyDecode o (fun k => (witnessVerifySelect o k).map read) =
      some ((ofLex o).2, read {(ofLex o).2}) := rfl

/-- One extra implemented physical query makes every announced value truthful. -/
def minimumWitnessVerified (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t) :=
  (minimumWitnessRaw n hn t ht).postQuery witnessVerifySelect
    (4 * t * minimumDegreeBaseBudget n) witnessVerifyDecode

theorem minimumWitnessVerified_law (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) (out : DegreeWitness n) :
    (minimumWitnessVerified n hn t ht).prob read (4 * t * minimumDegreeBaseBudget n + 1) out =
      ∑ o ∈ Finset.univ.filter (fun o : DegreeTag n =>
        some ((ofLex o).2, read {(ofLex o).2}) = out),
        (minimumWitnessRaw n hn t ht).prob read (4 * t * minimumDegreeBaseBudget n) o := by
  exact postQuery_prob_eq_sum (minimumWitnessRaw n hn t ht) witnessVerifySelect
    (4 * t * minimumDegreeBaseBudget n) witnessVerifyDecode read out

theorem minimumWitnessVerified_sound (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) (out : DegreeWitness n)
    (h : 0 < (minimumWitnessVerified n hn t ht).prob read
      (4 * t * minimumDegreeBaseBudget n + 1) out) :
    ∃ v : Fin n, out = some (v, read {v}) := by
  obtain ⟨o, ho⟩ := postQuery_exists_of_pos (minimumWitnessRaw n hn t ht) witnessVerifySelect
    (4 * t * minimumDegreeBaseBudget n) witnessVerifyDecode read out h
  exact ⟨(ofLex o).2, ho.symm⟩

theorem minimumWitnessVerified_correct (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) :
    let m := minimumTagged n hn (singletonTaggedRead n read)
    1 - (8 / 9 : ℝ) ^ t ≤ (minimumWitnessVerified n hn t ht).prob read
      (4 * t * minimumDegreeBaseBudget n + 1) (some ((ofLex m).2, (ofLex m).1)) := by
  dsimp only
  let m := minimumTagged n hn (singletonTaggedRead n read)
  have hs := (minimumTagged_singleton_spec n hn read).1
  have hm : witnessVerifyDecode m (fun k => (witnessVerifySelect m k).map read) =
      some ((ofLex m).2, (ofLex m).1) := by
    rw [witnessVerifyDecode_read, ← hs]
  have h := sum_prob_le_postQuery (minimumWitnessRaw n hn t ht) witnessVerifySelect
    (4 * t * minimumDegreeBaseBudget n) witnessVerifyDecode read
    {m} {some ((ofLex m).2, (ofLex m).1)} (by
      intro o ho
      have ho' : o = m := by simpa only [Finset.mem_singleton] using ho
      subst o
      exact Finset.mem_singleton.mpr hm)
  simp only [Finset.sum_singleton] at h
  exact (minimumWitnessRaw_correct n hn t ht read).trans h

/-- Empty inputs return no vertex and use no queries. All other inputs pay
the two-call adapter for 2t base runs and one final physical verification. -/
def minimumDegreeWitnessQueries (n t : ℕ) : ℕ :=
  if n = 0 then 0 else 4 * t * minimumDegreeBaseBudget n + 1

@[simp] theorem minimumDegreeWitnessQueries_zero (t : ℕ) :
    minimumDegreeWitnessQueries 0 t = 0 := by simp [minimumDegreeWitnessQueries]

theorem minimumDegreeWitnessQueries_pos {n : ℕ} (hn : 0 < n) (t : ℕ) :
    minimumDegreeWitnessQueries n t = 4 * t * minimumDegreeBaseBudget n + 1 := by
  simp [minimumDegreeWitnessQueries, Nat.ne_of_gt hn]

theorem minimumDegreeWitnessQueries_le (n t : ℕ) :
    minimumDegreeWitnessQueries n t ≤ 4 * t * minimumDegreeBaseBudget n + 1 := by
  unfold minimumDegreeWitnessQueries
  split_ifs <;> omega

/-- This target is a specification of the output, never an input to a gate
or readout. The attaining vertex is encoded by the tagged minimum. -/
def minimumSingletonWitness (n : ℕ) (read : Finset (Fin n) → CutAnswer n 1) :
    DegreeWitness n :=
  if hn : 0 < n then
    let m := minimumTagged n hn (singletonTaggedRead n read)
    some ((ofLex m).2, (ofLex m).1)
  else none

/-- Exact finite Born law of the implemented verified tagged circuit, with
the actual constant-circuit law at n=0. -/
def minimumDegreeWitnessLaw (n t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) (out : DegreeWitness n) : ℝ :=
  if hn : 0 < n then
    ∑ o ∈ Finset.univ.filter (fun o : DegreeTag n =>
      some ((ofLex o).2, read {(ofLex o).2}) = out),
      (minimumWitnessRaw n hn t ht).prob read (4 * t * minimumDegreeBaseBudget n) o
  else if out = none then 1 else 0

/-- Existence is proved by the concrete tagged/post-query construction. The
algorithm is quantified before every table, and its full law is fixed. -/
theorem exists_minimumDegreeWitness_algorithm (n t : ℕ) (ht : 0 < t) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : CutQAlg n 1 (DegreeWitness n) Work),
      ∀ (read : Finset (Fin n) → CutAnswer n 1) (out : DegreeWitness n),
        T.prob read (minimumDegreeWitnessQueries n t) out =
          minimumDegreeWitnessLaw n t ht read out := by
  by_cases hn : 0 < n
  · refine ⟨PQWork (Finset (Fin n)) (CutAnswer n 1)
      (QBasis (Fin n) (DegreeTag n) (minimumTaggedWork n hn t ht)) 1,
      inferInstance, inferInstance, minimumWitnessVerified n hn t ht, ?_⟩
    intro read out
    rw [minimumDegreeWitnessQueries_pos hn, minimumDegreeWitnessLaw, dite_eq_left hn]
    exact minimumWitnessVerified_law n hn t ht read out
  · have hn0 : n = 0 := by omega
    subst n
    refine ⟨Unit, inferInstance, inferInstance,
      constAlg (Finset (Fin 0)) (CutAnswer 0 1) (none : DegreeWitness 0), ?_⟩
    intro read out
    have hout : out = none := by
      cases out with
      | none => rfl
      | some x => exact Fin.elim0 x.1
    subst out
    simp [minimumDegreeWitnessLaw, QAlg.prob, constAlg]

/-- Workspace chosen solely from the universal public construction. -/
def minimumDegreeWitnessWork (n t : ℕ) (ht : 0 < t) : Type :=
  (exists_minimumDegreeWitness_algorithm n t ht).choose

instance minimumDegreeWitnessWorkFintype (n t : ℕ) (ht : 0 < t) :
    Fintype (minimumDegreeWitnessWork n t ht) :=
  (exists_minimumDegreeWitness_algorithm n t ht).choose_spec.choose

instance minimumDegreeWitnessWorkDecidableEq (n t : ℕ) (ht : 0 < t) :
    DecidableEq (minimumDegreeWitnessWork n t ht) :=
  (exists_minimumDegreeWitness_algorithm n t ht).choose_spec.choose_spec.choose

def minimumDegreeWitnessAlg (n t : ℕ) (ht : 0 < t) :
    CutQAlg n 1 (DegreeWitness n) (minimumDegreeWitnessWork n t ht) :=
  (exists_minimumDegreeWitness_algorithm n t ht).choose_spec.choose_spec.choose_spec.choose

theorem minimumDegreeWitnessAlg_law (n t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) (out : DegreeWitness n) :
    (minimumDegreeWitnessAlg n t ht).prob read (minimumDegreeWitnessQueries n t) out =
      minimumDegreeWitnessLaw n t ht read out :=
  (exists_minimumDegreeWitness_algorithm n t ht).choose_spec.choose_spec.choose_spec.choose_spec read out

/-- For positive n the selected public circuit has the exact outcome law
of the explicitly constructed verification circuit. -/
theorem minimumDegreeWitnessAlg_verified_law (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) (out : DegreeWitness n) :
    (minimumDegreeWitnessAlg n t ht).prob read (minimumDegreeWitnessQueries n t) out =
      (minimumWitnessVerified n hn t ht).prob read
        (4 * t * minimumDegreeBaseBudget n + 1) out := by
  rw [minimumDegreeWitnessAlg_law, minimumDegreeWitnessLaw, dite_eq_left hn,
    minimumWitnessVerified_law]

@[simp] theorem minimumDegreeWitnessAlg_zero (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin 0) → CutAnswer 0 1) :
    (minimumDegreeWitnessAlg 0 t ht).prob read 0 none = 1 := by
  simpa only [minimumDegreeWitnessQueries_zero, minimumDegreeWitnessLaw,
    Nat.lt_irrefl, dite_false, ite_true] using minimumDegreeWitnessAlg_law 0 t ht read none

theorem minimumDegreeWitnessAlg_correct (n t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) :
    1 - (8 / 9 : ℝ) ^ t ≤ (minimumDegreeWitnessAlg n t ht).prob read
      (minimumDegreeWitnessQueries n t) (minimumSingletonWitness n read) := by
  by_cases hn : 0 < n
  · rw [minimumDegreeWitnessAlg_verified_law n hn, minimumSingletonWitness, dite_eq_left hn]
    exact minimumWitnessVerified_correct n hn t ht read
  · have hn0 : n = 0 := by omega
    subst n
    simp only [minimumDegreeWitnessQueries_zero, minimumSingletonWitness,
      Nat.lt_irrefl, dite_false, minimumDegreeWitnessAlg_zero]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 9) t]

/-- Every positive-probability output on every table is an actual vertex
paired with its queried singleton value, whether or not it is minimum. -/
theorem minimumDegreeWitnessAlg_sound (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) (out : DegreeWitness n)
    (h : 0 < (minimumDegreeWitnessAlg n t ht).prob read (minimumDegreeWitnessQueries n t) out) :
    ∃ v : Fin n, out = some (v, read {v}) := by
  rw [minimumDegreeWitnessAlg_verified_law n hn] at h
  exact minimumWitnessVerified_sound n hn t ht read out h

theorem minimumDegreeWitnessAlg_minimum (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) :
    ∃ v : Fin n, read {v} = minimumSingletonValue n read ∧
      (∀ u, read {v} ≤ read {u}) ∧
      1 - (8 / 9 : ℝ) ^ t ≤ (minimumDegreeWitnessAlg n t ht).prob read
        (minimumDegreeWitnessQueries n t) (some (v, read {v})) := by
  let m := minimumTagged n hn (singletonTaggedRead n read)
  have hs := minimumTagged_singleton_spec n hn read
  refine ⟨(ofLex m).2, ?_, ?_, ?_⟩
  · exact hs.1.symm.trans (minimumTagged_value n hn read)
  · intro u
    rw [← hs.1]
    exact hs.2 u
  · have h := minimumDegreeWitnessAlg_correct n t ht read
    rw [minimumSingletonWitness, dite_eq_left hn] at h
    simpa only [hs.1] using h

def minimumDegreeWitnessRoutine (n t : ℕ) (ht : 0 < t) :
    QRoutine (Finset (Fin n)) (CutAnswer n 1) (minimumDegreeWitnessWork n t ht) where
  len := minimumDegreeWitnessQueries n t
  step := (minimumDegreeWitnessAlg n t ht).step
  step_unitary := (minimumDegreeWitnessAlg n t ht).step_unitary

@[simp] theorem minimumDegreeWitnessRoutine_len (n t : ℕ) (ht : 0 < t) :
    (minimumDegreeWitnessRoutine n t ht).len =
      if n = 0 then 0 else 4 * t * minimumDegreeBaseBudget n + 1 := rfl

theorem minimumDegreeWitnessRoutine_cap (n t : ℕ) (ht : 0 < t) :
    (minimumDegreeWitnessRoutine n t ht).len ≤ 4 * t * minimumDegreeBaseBudget n + 1 :=
  minimumDegreeWitnessQueries_le n t

theorem minimumDegreeWitnessRoutine_state (n t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) :
    (minimumDegreeWitnessRoutine n t ht).run read *ᵥ (minimumDegreeWitnessAlg n t ht).init =
      (minimumDegreeWitnessAlg n t ht).state read (minimumDegreeWitnessQueries n t) :=
  ((minimumDegreeWitnessAlg n t ht).state_eq_runUpto (minimumDegreeWitnessRoutine n t ht)
    rfl read (minimumDegreeWitnessQueries n t)).symm

/-- Fixed public length and normalization hold also for inconsistent tables. -/
theorem minimumDegreeWitnessRoutine_normalized (n t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) :
    IsQState ((minimumDegreeWitnessRoutine n t ht).run read *ᵥ (minimumDegreeWitnessAlg n t ht).init) := by
  rw [minimumDegreeWitnessRoutine_state]
  exact (minimumDegreeWitnessAlg n t ht).state_isQState _ _

theorem minimumDegreeWitnessRoutine_event_law (n t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) (Good : DegreeWitness n → Prop) [DecidablePred Good] :
    goodProb (minimumDegreeWitnessAlg n t ht).readout Good
      ((minimumDegreeWitnessRoutine n t ht).run read *ᵥ (minimumDegreeWitnessAlg n t ht).init) =
      ∑ out : DegreeWitness n, if Good out then minimumDegreeWitnessLaw n t ht read out else 0 := by
  rw [minimumDegreeWitnessRoutine_state, goodProb_eq_sum]
  change (∑ out : DegreeWitness n, if Good out then
    (minimumDegreeWitnessAlg n t ht).prob read (minimumDegreeWitnessQueries n t) out else 0) = _
  simp_rw [minimumDegreeWitnessAlg_law]

/-- An honest returned singleton is proper and has its exact original value. -/
theorem minimumDegreeWitnessAlg_honest_sound {n : ℕ} (hn : 2 ≤ n) (t : ℕ) (ht : 0 < t)
    (G : CapacityGraph (Fin n) 1) {v : Fin n} {a : CutAnswer n 1}
    (h : 0 < (minimumDegreeWitnessAlg n t ht).prob (capacityRead G)
      (minimumDegreeWitnessQueries n t) (some (v, a))) :
    ProperShore ({v} : Finset (Fin n)) ∧ (a : ℕ) = G.cut {v} := by
  obtain ⟨u, hu⟩ := minimumDegreeWitnessAlg_sound n (by omega) t ht (capacityRead G) _ h
  have heq : (v, a) = (u, capacityRead G {u}) := Option.some.inj hu
  have hv : v = u := congrArg Prod.fst heq
  subst u
  have ha : a = capacityRead G {v} := congrArg Prod.snd heq
  exact ⟨properShore_singleton v (by simpa only [Fintype.card_fin] using hn),
    congrArg Fin.val ha⟩

theorem minimumDegreeWitnessAlg_honest_minimum {n : ℕ} (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (G : CapacityGraph (Fin n) 1) :
    ∃ v : Fin n, G.cut {v} = (minimumDegreeValue G : ℕ) ∧
      (∀ u, G.cut {v} ≤ G.cut {u}) ∧
      1 - (8 / 9 : ℝ) ^ t ≤ (minimumDegreeWitnessAlg n t ht).prob (capacityRead G)
        (minimumDegreeWitnessQueries n t) (some (v, capacityRead G {v})) := by
  obtain ⟨v, hv, hmin, hp⟩ := minimumDegreeWitnessAlg_minimum n hn t ht (capacityRead G)
  exact ⟨v, congrArg Fin.val hv, hmin, hp⟩

theorem minimumDegreeWitnessAlg_simple {n : ℕ} (hn : 0 < n) (t : ℕ) (ht : 0 < t)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ v : Fin n, G.degree v = G.minDegree ∧
      1 - (8 / 9 : ℝ) ^ t ≤ (minimumDegreeWitnessAlg n t ht).prob (simpleRead G)
        (minimumDegreeWitnessQueries n t) (some (v, simpleRead G {v})) := by
  obtain ⟨v, hv, _, hp⟩ := minimumDegreeWitnessAlg_honest_minimum hn t ht (SimpleGraph.toCapacity G)
  rw [simpleCapacity_singleton_degree, minimumDegreeValue_eq_minDegree] at hv
  exact ⟨v, hv, hp⟩

/-- Literal public-before-G endpoint. Every answer table has the same finite
schedule and normalized state; truthful outputs and a real minimum vertex
are properties of the implemented algorithm. The final +1 is explicit. -/
theorem exists_quantum_minimumDegree_witness (n t : ℕ) (ht : 0 < t) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : CutQAlg n 1 (DegreeWitness n) Work)
      (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) Work),
      R.len = minimumDegreeWitnessQueries n t ∧
      R.len ≤ 4 * t * minimumDegreeBaseBudget n + 1 ∧
      (∀ read, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ read out, T.prob read R.len out = minimumDegreeWitnessLaw n t ht read out) ∧
      (∀ (G : CapacityGraph (Fin n) 1),
        (∀ (_hn : 2 ≤ n) (v : Fin n) (a : CutAnswer n 1),
          0 < T.prob (capacityRead G) R.len (some (v, a)) →
          ProperShore ({v} : Finset (Fin n)) ∧ (a : ℕ) = G.cut {v}) ∧
        (0 < n → ∃ v : Fin n, G.cut {v} = (minimumDegreeValue G : ℕ) ∧
          (∀ u, G.cut {v} ≤ G.cut {u}) ∧
          1 - (8 / 9 : ℝ) ^ t ≤ T.prob (capacityRead G) R.len (some (v, capacityRead G {v})))) := by
  refine ⟨minimumDegreeWitnessWork n t ht, inferInstance, inferInstance,
    minimumDegreeWitnessAlg n t ht, minimumDegreeWitnessRoutine n t ht,
    rfl, minimumDegreeWitnessRoutine_cap n t ht, ?_, ?_, ?_⟩
  · intro read
    exact ⟨minimumDegreeWitnessRoutine_state n t ht read,
      minimumDegreeWitnessRoutine_normalized n t ht read⟩
  · exact minimumDegreeWitnessAlg_law n t ht
  · intro G
    exact ⟨fun hn v a h => minimumDegreeWitnessAlg_honest_sound hn t ht G h,
      fun hn => minimumDegreeWitnessAlg_honest_minimum hn t ht G⟩

#print axioms minimumTagged_singleton_spec
#print axioms minimumTagged_tie_break
#print axioms minimumTagged_value
#print axioms taggedMinimumReadAll_prob
#print axioms minimumTagged_counts_nonempty
#print axioms minimumTagged_qQuery_le
#print axioms exists_minimumTagged_base
#print axioms exists_minimumTagged_repeated
#print axioms minimumTaggedAlg_correct
#print axioms minimumWitnessRaw_state
#print axioms minimumWitnessRaw_prob
#print axioms minimumWitnessRaw_correct
#print axioms minimumWitnessVerified_law
#print axioms minimumWitnessVerified_sound
#print axioms minimumWitnessVerified_correct
#print axioms exists_minimumDegreeWitness_algorithm
#print axioms minimumDegreeWitnessAlg_law
#print axioms minimumDegreeWitnessAlg_zero
#print axioms minimumDegreeWitnessAlg_correct
#print axioms minimumDegreeWitnessAlg_sound
#print axioms minimumDegreeWitnessAlg_minimum
#print axioms minimumDegreeWitnessRoutine_len
#print axioms minimumDegreeWitnessRoutine_cap
#print axioms minimumDegreeWitnessRoutine_state
#print axioms minimumDegreeWitnessRoutine_normalized
#print axioms minimumDegreeWitnessRoutine_event_law
#print axioms minimumDegreeWitnessAlg_honest_sound
#print axioms minimumDegreeWitnessAlg_honest_minimum
#print axioms minimumDegreeWitnessAlg_simple
#print axioms exists_quantum_minimumDegree_witness

end
end CutQueryComplexity.StarContraction2022.Quantum
