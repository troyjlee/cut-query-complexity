import CutQueryComplexity.GHReduction.ApproximationValues
import CutQueryComplexity.GHReduction.SourceValues
import Mathlib.Algebra.Order.Ring.Pow

/-! # A finite public range of terminal-connectivity buckets

All bucketing is performed on the explicit approximator. The hidden integral
graph appears only in coverage and transfer proofs. Positive buckets have
positive terminal connectivity and a narrow enough true-value range for the
terminal guide packing theorem, including low-connectivity nonterminals.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

def bucketThreshold (j : ℕ) : ℝ := (1 / 2 : ℝ) * (101 / 100 : ℝ) ^ j

def bucketCount (M : ℕ) : ℕ := 100 * Nat.clog 2 (4 * (M + 1))

theorem bucketThreshold_pos (j : ℕ) : 0 < bucketThreshold j := by
  unfold bucketThreshold
  positivity

theorem bucketThreshold_succ (j : ℕ) :
    bucketThreshold (j + 1) = (101 / 100 : ℝ) * bucketThreshold j := by
  unfold bucketThreshold
  rw [pow_succ]
  ring

theorem bucketThreshold_mono : Monotone bucketThreshold := by
  apply monotone_nat_of_le_succ
  intro j
  rw [bucketThreshold_succ]
  have h := (bucketThreshold_pos j).le
  linarith

theorem bucketThreshold_last (M : ℕ) : (101 / 100 : ℝ) * M < bucketThreshold (bucketCount M) := by
  have h100 : (2 : ℝ) ≤ (101 / 100 : ℝ) ^ 100 := by
    have h := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1 / 100) 100
    convert h using 1 <;> norm_num
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h100
    (Nat.clog 2 (4 * (M + 1)))
  have hc : ((4 * (M + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (4 * (M + 1)) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (4 * (M + 1))
  have hpow := hc.trans hp
  unfold bucketThreshold bucketCount
  rw [pow_mul]
  push_cast at hpow
  have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

theorem exists_bucket_index {M : ℕ} {value : ℝ} (hlo : 1 / 2 ≤ value)
    (hhi : value < bucketThreshold (bucketCount M)) :
    ∃ j : Fin (bucketCount M), bucketThreshold j.val ≤ value ∧ value < bucketThreshold (j.val + 1) := by
  have hex : ∃ k : ℕ, value < bucketThreshold k := ⟨bucketCount M, hhi⟩
  let k := Nat.find hex
  have hk : value < bucketThreshold k := Nat.find_spec hex
  have hkJ : k ≤ bucketCount M := Nat.find_le hhi
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    norm_num [bucketThreshold] at hk
    linarith
  have hbelow : bucketThreshold (k - 1) ≤ value :=
    le_of_not_gt (Nat.find_min hex (show k - 1 < k by omega))
  refine ⟨⟨k - 1, by omega⟩, hbelow, ?_⟩
  simpa only [Nat.sub_add_cancel (show 1 ≤ k by omega)] using hk

variable {V : Type} [Fintype V] [DecidableEq V]

def sourceBucket (K : WeightedGraph V) (U : Finset V) (s : V) (j : ℕ) : Finset V :=
  U.filter (fun t => t ≠ s ∧ bucketThreshold j ≤ stValue K t s ∧
    stValue K t s < bucketThreshold (j + 1))

def bucketTerminals (K : WeightedGraph V) (U : Finset V) (s : V) (j : ℕ) : Finset V :=
  insert s (sourceBucket K U s j)

theorem sourceBucket_excludes (K : WeightedGraph V) (U : Finset V) (s : V) (j : ℕ) :
    s ∉ sourceBucket K U s j := by simp [sourceBucket]

theorem sourceBuckets_disjoint (K : WeightedGraph V) (U : Finset V) (s : V) :
    Pairwise (fun i j : ℕ => Disjoint (sourceBucket K U s i) (sourceBucket K U s j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro t hi hj
  have hi' := (Finset.mem_filter.mp hi).2.2
  have hj' := (Finset.mem_filter.mp hj).2.2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hle := (bucketThreshold_mono (show i + 1 ≤ j by omega)).trans hj'.1
    exact (not_lt_of_ge hle) hi'.2
  · have hle := (bucketThreshold_mono (show j + 1 ≤ i by omega)).trans hi'.1
    exact (not_lt_of_ge hle) hj'.2

theorem bucketTerminals_two_le (K : WeightedGraph V) (U : Finset V) (s : V) (j : ℕ)
    (hne : (sourceBucket K U s j).Nonempty) : 2 ≤ (bucketTerminals K U s j).card := by
  rw [bucketTerminals, Finset.card_insert_of_notMem (sourceBucket_excludes K U s j)]
  have h := hne.card_pos
  omega

theorem bucketTerminals_pos (K : WeightedGraph V) (U : Finset V) (s : V) (j : ℕ)
    (hne : (sourceBucket K U s j).Nonempty) : 0 < terminalMin K (bucketTerminals K U s j) := by
  apply (bucketThreshold_pos j).trans_le
  apply le_terminalMin_of_source K _ s (bucketTerminals_two_le K U s j hne) (by simp [bucketTerminals])
  intro t ht hts
  have hb : t ∈ sourceBucket K U s j := (Finset.mem_insert.mp ht).resolve_left hts
  exact (Finset.mem_filter.mp hb).2.2.1

theorem stValue_approximation_fixed (F K : WeightedGraph V)
    (happrox : ∀ S, (99 / 100 : ℝ) * F.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * F.cut S) {s t : V} (hst : s ≠ t) :
    (99 / 100 : ℝ) * stValue F s t ≤ stValue K s t ∧
      stValue K s t ≤ (101 / 100 : ℝ) * stValue F s t := by
  have ha : ∀ S, (1 - (1 / 100 : ℝ)) * F.cut S ≤ K.cut S ∧
      K.cut S ≤ (1 + (1 / 100 : ℝ)) * F.cut S := by
    intro S
    convert happrox S using 1 <;> norm_num
  have h := stValue_approximation F K (eps := (1 / 100 : ℝ)) (by norm_num) (by norm_num) ha hst
  convert h using 1 <;> norm_num

theorem sourceBucket_coverage {M : ℕ} (F K : WeightedGraph V) (hF : InputPromise M F)
    (happrox : ∀ S, (99 / 100 : ℝ) * F.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * F.cut S)
    (U : Finset V) (s : V) {t : V} (ht : t ∈ U) (hts : t ≠ s)
    (hpos : 0 < stValue F t s) : ∃ j : Fin (bucketCount M), t ∈ sourceBucket K U s j.val := by
  obtain ⟨value, hvalue⟩ := stValue_nat_of_integral F hF.1 hts
  have hone : (1 : ℝ) ≤ stValue F t s := by
    rw [hvalue] at hpos ⊢
    have hv : 0 < value := by exact_mod_cast hpos
    exact_mod_cast (show 1 ≤ value by omega)
  have hbound : stValue F t s ≤ M := by
    obtain ⟨S, _, hS⟩ := exists_stMinCut F hts
    rw [← hS]
    exact (cut_le_edgeMass F S).trans hF.2
  have ha := stValue_approximation_fixed F K happrox hts
  have hlo : (1 / 2 : ℝ) ≤ stValue K t s := by linarith
  have hhi : stValue K t s < bucketThreshold (bucketCount M) :=
    (ha.2.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))).trans_lt (bucketThreshold_last M)
  obtain ⟨j, hj⟩ := exists_bucket_index hlo hhi
  exact ⟨j, Finset.mem_filter.mpr ⟨ht, hts, hj⟩⟩

theorem sourceBucket_small_minCut (F K : WeightedGraph V)
    (happrox : ∀ S, (99 / 100 : ℝ) * F.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * F.cut S)
    (U : Finset V) (s : V) (j : ℕ) {t : V} (ht : t ∈ sourceBucket K U s j)
    {S : Finset V} (hS : IsSTMinCut F t s S) :
    F.cut S ≤ (11 / 10 : ℝ) * terminalMin F (bucketTerminals K U s j) := by
  have hne : (sourceBucket K U s j).Nonempty := ⟨t, ht⟩
  have hterminal : (100 / 101 : ℝ) * bucketThreshold j ≤ terminalMin F (bucketTerminals K U s j) := by
    apply le_terminalMin_of_source F _ s (bucketTerminals_two_le K U s j hne) (by simp [bucketTerminals])
    intro v hv hvs
    have hb := (Finset.mem_filter.mp ((Finset.mem_insert.mp hv).resolve_left hvs)).2.2.1
    have ha := stValue_approximation_fixed F K happrox hvs
    nlinarith
  have hts := (Finset.mem_filter.mp ht).2.1
  have hupper := (Finset.mem_filter.mp ht).2.2.2
  rw [bucketThreshold_succ] at hupper
  have ha := stValue_approximation_fixed F K happrox hts
  rw [stValue_eq_of_minCut F hS]
  have hpositive := bucketThreshold_pos j
  nlinarith

end
end CutQueryComplexity.GHReduction
