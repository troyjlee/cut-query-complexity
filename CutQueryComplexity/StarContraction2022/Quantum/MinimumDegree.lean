import CutQueryComplexity.Quantum.Model
import CutQueryComplexity.StarContraction2022.Quantum.CoherentTransport
import QuantumQueryComplexity.Quantum.MaxApplications
import QuantumQueryComplexity.Quantum.ReadAll
import QuantumQueryComplexity.Quantum.Padding
import QuantumQueryComplexity.Quantum.Plurality
import Mathlib.Data.Nat.Log

/-! # A public quantum algorithm for the minimum-degree value

Read-all proves attainability before the native OrderDual maximum bound is
used. The attained algorithm is actually padded, repeated by the library's
independent plurality construction, and transported to singleton cut queries.
Every finite cut-answer table has the same public query count and a minimum
singleton-value guarantee. Honest graph replies give ordinary minimum degree.
The output is a value; no vertex, shore, forest or global min-cut is claimed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum

noncomputable section

open QuantumQueryComplexity
open scoped Matrix

/-- The minimum of a nonempty public tuple, expressed using the checked
maximum-value specification with the reversed value order. -/
def minimumLetter (n : ℕ) (hn : 0 < n) (x : Fin n → CutAnswer n 1) :
    CutAnswer n 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact maxFun (A := OrderDual (CutAnswer n 1)) x

theorem minimumLetter_le (n : ℕ) (hn : 0 < n)
    (x : Fin n → CutAnswer n 1) (v : Fin n) : minimumLetter n hn x ≤ x v := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact le_maxFun (A := OrderDual (CutAnswer n 1)) x v

theorem minimumLetter_attained (n : ℕ) (hn : 0 < n)
    (x : Fin n → CutAnswer n 1) : ∃ v, x v = minimumLetter n hn x := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact exists_eq_maxFun (A := OrderDual (CutAnswer n 1)) x

/-- The target for every answer table. There are no vertices when n=0, so its
specified value is zero; no read of the empty shore is required. -/
def minimumSingletonValue (n : ℕ) (read : Finset (Fin n) → CutAnswer n 1) :
    CutAnswer n 1 :=
  if hn : 0 < n then minimumLetter n hn (fun v => read {v}) else 0

theorem minimumSingletonValue_le (n : ℕ) (hn : 0 < n)
    (read : Finset (Fin n) → CutAnswer n 1) (v : Fin n) :
    minimumSingletonValue n read ≤ read {v} := by
  simpa only [minimumSingletonValue, dif_pos hn] using
    minimumLetter_le n hn (fun v => read {v}) v

theorem minimumSingletonValue_attained (n : ℕ) (hn : 0 < n)
    (read : Finset (Fin n) → CutAnswer n 1) :
    ∃ v, read {v} = minimumSingletonValue n read := by
  simpa only [minimumSingletonValue, dif_pos hn] using
    minimumLetter_attained n hn (fun v => read {v})

/-- The actual deterministic read-all quantum circuit, used to establish
nonemptiness of the achievable query counts. It contains no hidden graph. -/
def minimumReadAll (n : ℕ) (hn : 0 < n) :
    QAlg (Fin n) (CutAnswer n 1) (CutAnswer n 1) (QRec (Fin n) (CutAnswer n 1)) :=
  readAllAlg (recDecode id (minimumLetter n hn))

theorem minimumReadAll_prob (n : ℕ) (hn : 0 < n) (x : Fin n → CutAnswer n 1) :
    (minimumReadAll n hn).prob x n (minimumLetter n hn x) = 1 := by
  have hd := recDecode_apply (read := id) (f := minimumLetter n hn)
    (fun a b h => congrArg (minimumLetter n hn) h) x
  change recDecode id (minimumLetter n hn) (fun i => some (x i)) =
    minimumLetter n hn x at hd
  have hp := readAllAlg_prob (recDecode id (minimumLetter n hn)) x
  rw [hd] at hp
  simpa only [minimumReadAll, Fintype.card_fin] using hp

theorem minimumLetter_counts_nonempty (n : ℕ) (hn : 0 < n) :
    (QueryCounts id (minimumLetter n hn) (1 / 3)).Nonempty := by
  refine ⟨n, mem_queryCounts (A := minimumReadAll n hn) ?_⟩
  intro x
  change 1 - (1 / 3 : ℝ) ≤ (minimumReadAll n hn).prob x n (minimumLetter n hn x)
  rw [minimumReadAll_prob]
  norm_num

/-- The fixed public base count, including the exact read-all cap. -/
def minimumDegreeBaseBudget (n : ℕ) : ℕ :=
  min n ⌈204800 * Real.sqrt (n : ℝ)⌉₊

@[simp] theorem minimumDegreeBaseBudget_zero : minimumDegreeBaseBudget 0 = 0 := by
  simp [minimumDegreeBaseBudget]

theorem minimumDegreeBaseBudget_le_n (n : ℕ) : minimumDegreeBaseBudget n ≤ n :=
  Nat.min_le_left _ _

theorem minimumLetter_qQuery_le (n : ℕ) (hn : 0 < n) :
    qQuery (minimumLetter n hn) (1 / 3) ≤ minimumDegreeBaseBudget n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hlength : qQuery (minimumLetter n hn) (1 / 3) ≤ n := by
    change qQuery (maxFun (ι := Fin n) (A := OrderDual (CutAnswer n 1))) (1 / 3) ≤ n
    simpa only [Fintype.card_fin] using
      (max_qQuery_upper_length (ι := Fin n) (A := OrderDual (CutAnswer n 1)))
  have hupper : (qQuery (minimumLetter n hn) (1 / 3) : ℝ) ≤
      8192 * (1 + 24 * Real.sqrt (n : ℝ)) := by
    change (qQuery (maxFun (ι := Fin n) (A := OrderDual (CutAnswer n 1)))
      (1 / 3) : ℝ) ≤ 8192 * (1 + 24 * Real.sqrt (n : ℝ))
    simpa only [Fintype.card_fin, uniformExtractionConstant] using
      (max_qQuery_upper (ι := Fin n) (A := OrderDual (CutAnswer n 1)))
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn'
  have hbound : (qQuery (minimumLetter n hn) (1 / 3) : ℝ) ≤
      204800 * Real.sqrt (n : ℝ) := by nlinarith
  have hceil : qQuery (minimumLetter n hn) (1 / 3) ≤
      ⌈204800 * Real.sqrt (n : ℝ)⌉₊ := by
    exact_mod_cast hbound.trans (Nat.le_ceil _)
  exact le_min hlength hceil

/-- Attain the public minimum query count only after proving read-all
nonemptiness, then use the implemented parked-query padding circuit. -/
theorem exists_minimumLetter_base (n : ℕ) (hn : 0 < n) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : QAlg (Fin n) (CutAnswer n 1) (CutAnswer n 1) Work),
      ComputesWithErrorOn T (minimumDegreeBaseBudget n) id (minimumLetter n hn) (1 / 3) := by
  obtain ⟨Work, hF, hD, T, hT⟩ :=
    exists_computes_qQueryOn (minimumLetter_counts_nonempty n hn)
  letI := hF
  letI := hD
  have hle := minimumLetter_qQuery_le n hn
  have hsplit : qQuery (minimumLetter n hn) (1 / 3) +
      (minimumDegreeBaseBudget n - qQuery (minimumLetter n hn) (1 / 3)) =
      minimumDegreeBaseBudget n := by omega
  refine ⟨CtrlWork (Fin n) Work, inferInstance, inferInstance,
    padAlg T (qQuery (minimumLetter n hn) (1 / 3))
      (minimumDegreeBaseBudget n - qQuery (minimumLetter n hn) (1 / 3)), ?_⟩
  simpa only [hsplit] using computesWithErrorOn_padAlg hT
    (minimumDegreeBaseBudget n - qQuery (minimumLetter n hn) (1 / 3))

/-- Exactly 2t independent implemented runs. For an even number of runs the
plurality error formula is precisely (8/9)^t. -/
theorem exists_minimumLetter_repeated (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : 0 < t) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : QAlg (Fin n) (CutAnswer n 1) (CutAnswer n 1) Work),
      ComputesWithErrorOn T (2 * t * minimumDegreeBaseBudget n) id
        (minimumLetter n hn) ((8 / 9 : ℝ) ^ t) := by
  obtain ⟨Work, hF, hD, T, hT⟩ :=
    amplify_plurality (exists_minimumLetter_base n hn) (2 * t - 1)
  have hcopies : 2 * t - 1 + 1 = 2 * t := by omega
  have hhalf : (2 * t - 1 + 2) / 2 = t := by omega
  have herr : (1 + (1 / 3 : ℝ)) ^ (2 * t) / 2 ^ t = (8 / 9 : ℝ) ^ t := by
    rw [pow_mul, ← div_pow]
    norm_num
  refine ⟨Work, hF, hD, T, ?_⟩
  simpa only [hcopies, hhalf, herr] using hT

def minimumDegreeQueries (n t : ℕ) : ℕ := 2 * t * minimumDegreeBaseBudget n

/-- Full public-table guarantee. The singleton pullback costs exactly one cut
query per virtual query. The empty vertex set uses the actual constant circuit. -/
theorem exists_minimumDegree_algorithm (n t : ℕ) (ht : 0 < t) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : CutQAlg n 1 (CutAnswer n 1) Work),
      ∀ read : Finset (Fin n) → CutAnswer n 1,
        1 - (8 / 9 : ℝ) ^ t ≤
          T.prob read (minimumDegreeQueries n t) (minimumSingletonValue n read) := by
  by_cases hn : 0 < n
  · obtain ⟨Work, hF, hD, T, hT⟩ := exists_minimumLetter_repeated n hn t ht
    letI := hF
    letI := hD
    refine ⟨Option (Fin n) × Work, inferInstance, inferInstance,
      pullQueries (fun v : Fin n => ({v} : Finset (Fin n))) T
        (minimumDegreeQueries n t), ?_⟩
    intro read
    rw [pullQueries_prob]
    change 1 - (8 / 9 : ℝ) ^ t ≤ T.prob (fun v => read {v})
      (2 * t * minimumDegreeBaseBudget n) (minimumSingletonValue n read)
    simpa only [minimumSingletonValue, dif_pos hn, minimumDegreeQueries,
      Function.comp_apply, id_eq] using hT (fun v => read {v})
  · have hn0 : n = 0 := by omega
    subst n
    refine ⟨Unit, inferInstance, inferInstance,
      constAlg (Finset (Fin 0)) (CutAnswer 0 1) 0, ?_⟩
    intro read
    have he : 1 - (8 / 9 : ℝ) ^ t ≤ 1 := by
      linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 9) t]
    simpa [minimumDegreeQueries, minimumSingletonValue, QAlg.prob, constAlg] using he

/-- Publicly selected finite workspace. The existence theorem quantifies over
every answer table before this choice is made; no graph is used in the choice. -/
def minimumDegreeWork (n t : ℕ) (ht : 0 < t) : Type :=
  (exists_minimumDegree_algorithm n t ht).choose

instance minimumDegreeWorkFintype (n t : ℕ) (ht : 0 < t) :
    Fintype (minimumDegreeWork n t ht) :=
  (exists_minimumDegree_algorithm n t ht).choose_spec.choose

instance minimumDegreeWorkDecidableEq (n t : ℕ) (ht : 0 < t) :
    DecidableEq (minimumDegreeWork n t ht) :=
  (exists_minimumDegree_algorithm n t ht).choose_spec.choose_spec.choose

/-- The actual public algorithm, selected using only n, t and positivity. -/
def minimumDegreeAlg (n t : ℕ) (ht : 0 < t) :
    CutQAlg n 1 (CutAnswer n 1) (minimumDegreeWork n t ht) :=
  (exists_minimumDegree_algorithm n t ht).choose_spec.choose_spec.choose_spec.choose

theorem minimumDegreeAlg_correct (n t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) :
    1 - (8 / 9 : ℝ) ^ t ≤ (minimumDegreeAlg n t ht).prob read
      (minimumDegreeQueries n t) (minimumSingletonValue n read) :=
  (exists_minimumDegree_algorithm n t ht).choose_spec.choose_spec.choose_spec.choose_spec read

/-- A finite routine exposing the actual fixed query schedule. -/
def minimumDegreeRoutine (n t : ℕ) (ht : 0 < t) :
    QRoutine (Finset (Fin n)) (CutAnswer n 1) (minimumDegreeWork n t ht) where
  len := minimumDegreeQueries n t
  step := (minimumDegreeAlg n t ht).step
  step_unitary := (minimumDegreeAlg n t ht).step_unitary

@[simp] theorem minimumDegreeRoutine_len (n t : ℕ) (ht : 0 < t) :
    (minimumDegreeRoutine n t ht).len =
      2 * t * min n ⌈204800 * Real.sqrt (n : ℝ)⌉₊ := rfl

theorem minimumDegreeRoutine_state (n t : ℕ) (ht : 0 < t)
    (read : Finset (Fin n) → CutAnswer n 1) :
    (minimumDegreeRoutine n t ht).run read *ᵥ (minimumDegreeAlg n t ht).init =
      (minimumDegreeAlg n t ht).state read (minimumDegreeQueries n t) :=
  ((minimumDegreeAlg n t ht).state_eq_runUpto (minimumDegreeRoutine n t ht)
    rfl read (minimumDegreeQueries n t)).symm

/-- Honest minimum-degree letter for a simple unweighted capacity graph. -/
def minimumDegreeValue {n : ℕ} (G : CapacityGraph (Fin n) 1) : CutAnswer n 1 :=
  minimumSingletonValue n (capacityRead G)

theorem unitCapacity_singleton_le {n : ℕ} (G : CapacityGraph (Fin n) 1) (v : Fin n) :
    G.cut {v} ≤ n - 1 := by
  calc
    G.cut {v} = ∑ u ∈ ({v} : Finset (Fin n))ᶜ, (G.w v u : ℕ) := by
      simp [CapacityGraph.cut]
    _ ≤ ∑ _u ∈ ({v} : Finset (Fin n))ᶜ, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro u _
      have h := (G.w v u).isLt
      omega
    _ = n - 1 := by simp [Finset.card_compl]

theorem minimumDegreeValue_le {n : ℕ} (hn : 0 < n)
    (G : CapacityGraph (Fin n) 1) (v : Fin n) :
    (minimumDegreeValue G : ℕ) ≤ G.cut {v} :=
  minimumSingletonValue_le n hn (capacityRead G) v

theorem minimumDegreeValue_attained {n : ℕ} (hn : 0 < n)
    (G : CapacityGraph (Fin n) 1) : ∃ v, G.cut {v} = (minimumDegreeValue G : ℕ) := by
  obtain ⟨v, hv⟩ := minimumSingletonValue_attained n hn (capacityRead G)
  exact ⟨v, congrArg Fin.val hv⟩

theorem minimumDegreeValue_lt {n : ℕ} (hn : 0 < n) (G : CapacityGraph (Fin n) 1) :
    (minimumDegreeValue G : ℕ) < n := by
  have h := (minimumDegreeValue_le hn G ⟨0, hn⟩).trans
    (unitCapacity_singleton_le G ⟨0, hn⟩)
  omega

@[simp] theorem minimumDegreeValue_zero (G : CapacityGraph (Fin 0) 1) :
    minimumDegreeValue G = 0 := by simp [minimumDegreeValue, minimumSingletonValue]

@[simp] theorem minimumDegreeValue_one (G : CapacityGraph (Fin 1) 1) :
    minimumDegreeValue G = 0 := by
  apply Fin.ext
  have h := minimumDegreeValue_lt (by omega : 0 < 1) G
  simpa using Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)

theorem minimumDegreeValue_eq_zero_of_zero_degree {n : ℕ}
    (G : CapacityGraph (Fin n) 1) (v : Fin n) (hv : G.cut {v} = 0) :
    minimumDegreeValue G = 0 := by
  apply Fin.ext
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le v.val) v.isLt
  have h := minimumDegreeValue_le hn G v
  rw [hv] at h
  exact Nat.eq_zero_of_le_zero h

theorem simpleCapacity_singleton_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) :
    (SimpleGraph.toCapacity G).cut {v} = G.degree v := by
  classical
  have hw (u : Fin n) : ((SimpleGraph.toCapacity G).w v u : ℕ) =
      if G.Adj v u then 1 else 0 := by
    by_cases h : G.Adj v u <;> simp [SimpleGraph.toCapacity, h]
  simp only [CapacityGraph.cut, Finset.sum_singleton]
  simp_rw [hw]
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _ hu
  have huv : u = v := by simpa using hu
  subst u
  simp

/-- Ordinary natural minimum degree, with no connectedness or positive-degree
premise. The empty and one-vertex graphs follow the same zero convention. -/
theorem minimumDegreeValue_eq_minDegree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (minimumDegreeValue (SimpleGraph.toCapacity G) : ℕ) = G.minDegree := by
  by_cases hn : 0 < n
  · letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    apply le_antisymm
    · apply G.le_minDegree_of_forall_le_degree
      intro v
      rw [← simpleCapacity_singleton_degree G v]
      exact minimumDegreeValue_le hn _ v
    · obtain ⟨v, hv⟩ := minimumDegreeValue_attained hn (SimpleGraph.toCapacity G)
      rw [simpleCapacity_singleton_degree] at hv
      rw [← hv]
      exact G.minDegree_le_degree v
  · have hn0 : n = 0 := by omega
    subst n
    simp

theorem minimumDegreeAlg_honest (n t : ℕ) (ht : 0 < t)
    (G : CapacityGraph (Fin n) 1) :
    1 - (8 / 9 : ℝ) ^ t ≤ (minimumDegreeAlg n t ht).prob (capacityRead G)
      (minimumDegreeQueries n t) (minimumDegreeValue G) :=
  minimumDegreeAlg_correct n t ht (capacityRead G)

/-- The announced finite letter represents the ordinary natural minimum
degree. This concerns a value and does not return an attaining vertex. -/
theorem minimumDegreeAlg_simple (n t : ℕ) (ht : 0 < t)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ d : CutAnswer n 1, (d : ℕ) = G.minDegree ∧
      1 - (8 / 9 : ℝ) ^ t ≤ (minimumDegreeAlg n t ht).prob (simpleRead G)
        (minimumDegreeQueries n t) d := by
  exact ⟨minimumDegreeValue (SimpleGraph.toCapacity G),
    minimumDegreeValue_eq_minDegree G,
    minimumDegreeAlg_honest n t ht (SimpleGraph.toCapacity G)⟩

/-- A fully public fixed-count graph endpoint. -/
theorem exists_quantum_minimumDegree_value (n t : ℕ) (ht : 0 < t) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : CutQAlg n 1 (CutAnswer n 1) Work),
      ∀ G : CapacityGraph (Fin n) 1,
        1 - (8 / 9 : ℝ) ^ t ≤ T.prob (capacityRead G)
          (2 * t * min n ⌈204800 * Real.sqrt (n : ℝ)⌉₊) (minimumDegreeValue G) := by
  exact ⟨minimumDegreeWork n t ht, inferInstance, inferInstance,
    minimumDegreeAlg n t ht, minimumDegreeAlg_honest n t ht⟩

/-- A binary-log public confidence schedule, avoiding any hidden input data. -/
def minimumDegreeConfidenceBits (η : ℝ) : ℕ := Nat.clog 2 (⌈1 / η⌉₊ + 1) + 1

def minimumDegreeRepetitions (η : ℝ) : ℕ := 6 * minimumDegreeConfidenceBits η

theorem minimumDegreeRepetitions_pos (η : ℝ) : 0 < minimumDegreeRepetitions η := by
  unfold minimumDegreeRepetitions minimumDegreeConfidenceBits
  omega

theorem minimumDegreeError_six_mul (k : ℕ) :
    (8 / 9 : ℝ) ^ (6 * k) ≤ (1 / 2 : ℝ) ^ k := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by norm_num) k

theorem minimumDegreeConfidence_error {η : ℝ} (hη : 0 < η) :
    (8 / 9 : ℝ) ^ minimumDegreeRepetitions η ≤ η := by
  have hceil : 1 / η ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
  have hpowNat : ⌈1 / η⌉₊ + 1 ≤ 2 ^ minimumDegreeConfidenceBits η := by
    apply (Nat.le_pow_clog (by omega : 1 < 2) _).trans
    exact pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) (Nat.le_succ _)
  have hpowReal : 1 / η ≤ (2 : ℝ) ^ minimumDegreeConfidenceBits η := by
    have hc : (⌈1 / η⌉₊ : ℝ) + 1 ≤ (2 : ℝ) ^ minimumDegreeConfidenceBits η := by
      exact_mod_cast hpowNat
    linarith
  calc
    (8 / 9 : ℝ) ^ minimumDegreeRepetitions η ≤
        (1 / 2 : ℝ) ^ minimumDegreeConfidenceBits η := minimumDegreeError_six_mul _
    _ = 1 / (2 : ℝ) ^ minimumDegreeConfidenceBits η := by rw [div_pow, one_pow]
    _ ≤ 1 / (1 / η) := one_div_le_one_div_of_le (by positivity) hpowReal
    _ = η := by field_simp

/-- A named algorithm at an explicit positive tolerance. -/
def minimumDegreeToleranceAlg (n : ℕ) (η : ℝ) :
    CutQAlg n 1 (CutAnswer n 1)
      (minimumDegreeWork n (minimumDegreeRepetitions η) (minimumDegreeRepetitions_pos η)) :=
  minimumDegreeAlg n (minimumDegreeRepetitions η) (minimumDegreeRepetitions_pos η)

theorem minimumDegreeTolerance_correct (n : ℕ) {η : ℝ} (hη : 0 < η)
    (read : Finset (Fin n) → CutAnswer n 1) :
    1 - η ≤ (minimumDegreeToleranceAlg n η).prob read
      (12 * minimumDegreeConfidenceBits η * minimumDegreeBaseBudget n)
      (minimumSingletonValue n read) := by
  have h := (sub_le_sub_left (minimumDegreeConfidence_error hη) 1).trans
    (minimumDegreeAlg_correct n (minimumDegreeRepetitions η)
      (minimumDegreeRepetitions_pos η) read)
  simpa only [minimumDegreeToleranceAlg, minimumDegreeQueries,
    minimumDegreeRepetitions, ← mul_assoc, show 2 * 6 = (12 : ℕ) by omega] using h

theorem minimumDegreeTolerance_cost_le (n : ℕ) (η : ℝ) :
    12 * minimumDegreeConfidenceBits η * minimumDegreeBaseBudget n ≤
      12 * minimumDegreeConfidenceBits η * n :=
  Nat.mul_le_mul_left _ (minimumDegreeBaseBudget_le_n n)

theorem minimumDegreeTolerance_cost_le_sqrt (n : ℕ) (η : ℝ) :
    (12 * minimumDegreeConfidenceBits η * minimumDegreeBaseBudget n : ℝ) ≤
      12 * minimumDegreeConfidenceBits η * (204800 * Real.sqrt (n : ℝ) + 1) := by
  have hbase : (minimumDegreeBaseBudget n : ℝ) ≤
      204800 * Real.sqrt (n : ℝ) + 1 := by
    have hle : minimumDegreeBaseBudget n ≤ ⌈204800 * Real.sqrt (n : ℝ)⌉₊ :=
      Nat.min_le_right _ _
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 204800 * Real.sqrt (n : ℝ))
    exact (Nat.cast_le.mpr hle).trans hceil.le
  exact mul_le_mul_of_nonneg_left hbase (by positivity)

#print axioms minimumLetter_le
#print axioms minimumLetter_attained
#print axioms minimumReadAll_prob
#print axioms minimumLetter_counts_nonempty
#print axioms minimumLetter_qQuery_le
#print axioms exists_minimumLetter_base
#print axioms exists_minimumLetter_repeated
#print axioms exists_minimumDegree_algorithm
#print axioms minimumDegreeAlg_correct
#print axioms minimumDegreeRoutine_len
#print axioms minimumDegreeRoutine_state
#print axioms unitCapacity_singleton_le
#print axioms minimumDegreeValue_le
#print axioms minimumDegreeValue_attained
#print axioms minimumDegreeValue_lt
#print axioms minimumDegreeValue_zero
#print axioms minimumDegreeValue_one
#print axioms minimumDegreeValue_eq_zero_of_zero_degree
#print axioms simpleCapacity_singleton_degree
#print axioms minimumDegreeValue_eq_minDegree
#print axioms minimumDegreeAlg_honest
#print axioms minimumDegreeAlg_simple
#print axioms exists_quantum_minimumDegree_value
#print axioms minimumDegreeRepetitions_pos
#print axioms minimumDegreeError_six_mul
#print axioms minimumDegreeConfidence_error
#print axioms minimumDegreeTolerance_correct
#print axioms minimumDegreeTolerance_cost_le
#print axioms minimumDegreeTolerance_cost_le_sqrt

end

end CutQueryComplexity.StarContraction2022.Quantum
