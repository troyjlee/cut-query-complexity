import CutQueryComplexity.GHReduction.SampledGuideCorrectness

/-! # The actual bucketed single-source value program

Finite minimization on `K` uses its explicit public representation. Positive
buckets invoke sampled terminal guides; zero approximate values are handled
separately and never invoke positive-connectivity packing. Every guide call
uses the actual weighted input graph through its cut oracle.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal BigOperators
open Probability

variable {V : Type} [Fintype V] [DecidableEq V]

theorem bucketTerminals_subset (K : WeightedGraph V) (U : Finset V) (s : V) (hs : s ∈ U) (j : ℕ) :
    bucketTerminals K U s j ⊆ U := by
  apply Finset.insert_subset_iff.mpr
  exact ⟨hs, Finset.filter_subset _ _⟩

@[simp] theorem bucketTerminals_erase (K : WeightedGraph V) (U : Finset V) (s : V) (j : ℕ) :
    (bucketTerminals K U s j).erase s = sourceBucket K U s j := by
  exact Finset.erase_insert (sourceBucket_excludes K U s j)

def bucketSourceTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials levels scale exponent : ℕ) (K : WeightedGraph V)
    (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) (j : ℕ) :
    RTree (Finset V) ℝ (V → Option ℝ)
      (samples * guideTwoBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) :=
  if hne : (sourceBucket K U s j).Nonempty then
    sampledGuideTree family n samples trials levels scale exponent K (bucketTerminals K U s j)
      ⟨s, Finset.mem_insert_self _ _⟩ (bucketTerminals_two_le K U s j hne)
      (bucketTerminals_pos K U s j hne) hvn
  else RTree.pure (PMF.pure (fun _ => none))

def zeroSourceEstimate (K : WeightedGraph V) (U : Finset V) (s t : V) : Option ℝ :=
  if t ∈ U ∧ t ≠ s ∧ stValue K t s = 0 then some 0 else none

def mergeBucketValues {M : ℕ} (K : WeightedGraph V) (U : Finset V) (s : V)
    (output : Fin (bucketCount M) → V → Option ℝ) (t : V) : Option ℝ :=
  bestEstimates (zeroSourceEstimate K U s t ::
    Finset.univ.toList.map (fun j : Fin (bucketCount M) => output j t))

def singleSourceBudget (M : ℕ) (Q : ℕ → ℕ) (n samples trials levels scale exponent : ℕ) : ℕ :=
  bucketCount M * (samples * guideTwoBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1)))

def singleSourceTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials levels scale exponent : ℕ) (K : WeightedGraph V)
    (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (V → Option ℝ) (singleSourceBudget M Q n samples trials levels scale exponent) :=
  ((randomTable (fun _ => none) (fun j : Fin (bucketCount M) =>
    bucketSourceTree family n samples trials levels scale exponent K U s hvn j.val)).map
      (mergeBucketValues K U s)).cast (by simp [singleSourceBudget])

def BucketSourceSuccess (G K : WeightedGraph V) (U : Finset V) (s : V) (j : ℕ)
    (output : V → Option ℝ) : Prop :=
  if (sourceBucket K U s j).Nonempty then SourceValuesSuccess G (bucketTerminals K U s j) s output
  else ∀ t, output t = none

theorem BucketSourceSuccess.above (G K : WeightedGraph V) (U : Finset V) (s : V) (j : ℕ)
    {output : V → Option ℝ} (h : BucketSourceSuccess G K U s j output) (t : V) :
    EstimateAbove (stValue G t s) (output t) := by
  by_cases hne : (sourceBucket K U s j).Nonempty
  · simp only [BucketSourceSuccess, hne, ite_true] at h
    exact h.1 t
  · simp only [BucketSourceSuccess, hne, ite_false] at h
    intro value hvalue
    rw [h t] at hvalue
    cases hvalue

theorem zeroSourceEstimate_above (G K : WeightedGraph V) (U : Finset V) (s t : V)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    EstimateAbove (stValue G t s) (zeroSourceEstimate K U s t) := by
  intro value hvalue
  by_cases hzero : t ∈ U ∧ t ≠ s ∧ stValue K t s = 0
  · have heq : value = 0 := by
      rw [zeroSourceEstimate, ite_eq_left hzero] at hvalue
      exact Option.some.inj hvalue.symm
    have ha := (stValue_approximation_fixed G K happrox hzero.2.1).1
    rw [hzero.2.2] at ha
    rw [heq]
    linarith
  · simp [zeroSourceEstimate, hzero] at hvalue

theorem mergeBucketValues_success {M : ℕ} (G K : WeightedGraph V) (hG : InputPromise M G)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S)
    (U : Finset V) (s : V) (output : Fin (bucketCount M) → V → Option ℝ)
    (hgood : ∀ j, BucketSourceSuccess G K U s j.val (output j)) :
    SourceValuesSuccess G U s (mergeBucketValues K U s output) := by
  have habove (t : V) : ∀ a ∈ (zeroSourceEstimate K U s t ::
      Finset.univ.toList.map (fun j : Fin (bucketCount M) => output j t)),
      EstimateAbove (stValue G t s) a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact zeroSourceEstimate_above G K U s t happrox
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
      exact (hgood j).above G K U s j.val t
  refine ⟨fun t => bestEstimates_above _ (habove t), ?_⟩
  intro t ht hts
  apply bestEstimates_exact _ (habove t)
  by_cases hz : stValue G t s = 0
  · have ha := (stValue_approximation_fixed G K happrox hts).2
    have hn := stValue_nonneg K t s
    have hzK : stValue K t s = 0 := by rw [hz] at ha; linarith
    have heq : zeroSourceEstimate K U s t = some (stValue G t s) := by
      simp [zeroSourceEstimate, ht, hts, hzK, hz]
    exact List.mem_cons.mpr (Or.inl heq.symm)
  · have hpos : 0 < stValue G t s := lt_of_le_of_ne (stValue_nonneg G t s) (Ne.symm hz)
    obtain ⟨j, hj⟩ := sourceBucket_coverage G K hG happrox U s ht hts hpos
    have hne : (sourceBucket K U s j.val).Nonempty := ⟨t, hj⟩
    have hb : SourceValuesSuccess G (bucketTerminals K U s j.val) s (output j) := by
      simpa only [BucketSourceSuccess, hne, ite_true] using hgood j
    have heq := hb.2 t (Finset.mem_insert_of_mem hj) hts
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, by simp, heq⟩)

theorem guideTwoError_mono_real (M trials scale exponent fuel : ℕ) {r n : ℕ} (hrn : r ≤ n) :
    guideTwoError M trials scale exponent fuel r ≤ guideTwoError M trials scale exponent fuel n := by
  unfold guideTwoError
  gcongr

def singleSourceError (M n samples trials scale exponent : ℕ) : ℝ≥0∞ :=
  (bucketCount M : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ samples +
    (samples : ℝ≥0∞) * guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) n)

theorem bucketSourceTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (samples trials levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V) (hs : s ∈ U)
    (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) (j : ℕ) :
    mass ((bucketSourceTree family n samples trials levels scale exponent K U s hvn j).eval G.cut)
      (fun output => ¬BucketSourceSuccess G K U s j output) ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ samples +
      (samples : ℝ≥0∞) * guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) n := by
  by_cases hne : (sourceBucket K U s j).Nonempty
  · have hsmall : ∀ t ∈ bucketTerminals K U s j, t ≠ s → ∀ S, IsSTMinCut G t s S →
        G.cut S ≤ (11 / 10 : ℝ) * terminalMin G (bucketTerminals K U s j) := by
      intro t ht hts S hS
      exact sourceBucket_small_minCut G K happrox U s j ((Finset.mem_insert.mp ht).resolve_left hts) hS
    have h := sampledGuideTree_failure_le family hQ hnscale samples trials levels exponent hlevels
      G K hG (bucketTerminals K U s j) ⟨s, Finset.mem_insert_self _ _⟩
      (bucketTerminals_two_le K U s j hne) (bucketTerminals_pos K U s j hne) hvn happrox hsmall
    simp only [bucketSourceTree, BucketSourceSuccess, hne, dite_true, ite_true]
    apply h.trans
    have hcard : (bucketTerminals K U s j).card ≤ n :=
      (Finset.card_le_card (bucketTerminals_subset K U s hs j)).trans (Finset.card_le_univ U |>.trans hvn)
    apply add_le_add
    · apply mul_le_mul' ?_ le_rfl
      exact_mod_cast (show ((bucketTerminals K U s j).erase s).card ≤ n from
        Finset.card_erase_le.trans hcard)
    · exact mul_le_mul' le_rfl (guideTwoError_mono_real _ _ _ _ _ hcard)
  · simp [bucketSourceTree, BucketSourceSuccess, hne]

theorem singleSourceTree_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (samples trials levels exponent : ℕ) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V) (hs : s ∈ U)
    (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    mass ((singleSourceTree family n samples trials levels scale exponent K U s hvn).eval G.cut)
      (fun output => ¬SourceValuesSuccess G U s output) ≤
      singleSourceError M n samples trials scale exponent := by
  have htable := randomTable_failure_le (fun _ => none)
    (fun j : Fin (bucketCount M) => bucketSourceTree family n samples trials levels scale exponent K U s hvn j.val)
    G.cut (fun j => BucketSourceSuccess G K U s j.val)
    (fun _ => (n : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ samples +
      (samples : ℝ≥0∞) * guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) n)
    (fun j => bucketSourceTree_failure_le family hQ hnscale samples trials levels exponent hlevels
      G K hG U s hs hvn happrox j.val)
  unfold singleSourceTree singleSourceBudget
  rw [RTree.eval_cast, RTree.eval_map, mass_map]
  apply le_trans (mass_mono _ ?_)
    (by simpa only [singleSourceError, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using htable)
  intro output hbad hgood
  exact hbad (mergeBucketValues_success G K hG happrox U s output hgood)

end
end CutQueryComplexity.GHReduction
