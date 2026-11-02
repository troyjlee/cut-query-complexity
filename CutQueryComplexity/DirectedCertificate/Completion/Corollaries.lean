import CutQueryComplexity.DirectedCertificate.Completion.Terminal
import CutQueryComplexity.DirectedCertificate.Completion.Spread
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

/-! # Paper 3 corollaries with explicit certificate scopes

Intrinsic parameters below are derived from the actual symmetrized pair
weights. They constrain the input only. Every witness certificate continues
to quantify over all nonnegative real weighted competitors of arbitrary
support, using only original outgoing-cut shores.
The unit-input results stated with this witness predicate are weighted-robust;
`exists_unit_domain_certificate` explicitly restricts competitors to the unit
domain for the ordinary domain-relative convention.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset WeightedDiGraph

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def symCapacities (G : WeightedDiGraph V) : Finset ℝ := by
  classical
  exact (univ : Finset (V × V)).image fun p => G.sym.w p.1 p.2

noncomputable def positiveSymCapacities (G : WeightedDiGraph V) : Finset ℝ :=
  (symCapacities G).filter fun x => 0 < x

/-- The actual largest symmetrized pair capacity, zero for an empty graph. -/
noncomputable def symMaximum (G : WeightedDiGraph V) : ℝ := by
  classical
  exact (insert 0 (symCapacities G)).max' (insert_nonempty _ _)

/-- The actual smallest positive symmetrized pair capacity, zero if absent. -/
noncomputable def symMinimumPositive (G : WeightedDiGraph V) : ℝ := by
  classical
  exact if h : (positiveSymCapacities G).Nonempty then
    (positiveSymCapacities G).min' h else 0

omit [DecidableEq V] in
theorem symCapacity_mem (G : WeightedDiGraph V) (u v : V) :
    G.sym.w u v ∈ symCapacities G := by
  classical
  exact mem_image.mpr ⟨(u, v), mem_univ _, rfl⟩

theorem pair_le_symMaximum (G : WeightedDiGraph V) (u v : V) :
    G.sym.w u v ≤ symMaximum G := by
  classical
  exact le_max' _ _ (mem_insert_of_mem (symCapacity_mem G u v))

theorem positiveSymCapacities_nonempty (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    (positiveSymCapacities G).Nonempty := by
  classical
  by_contra hnone
  have hz : ∀ u v, G.sym.w u v = 0 := by
    intro u v
    have hnot : ¬ 0 < G.sym.w u v := fun hpos =>
      hnone ⟨G.sym.w u v, mem_filter.mpr ⟨symCapacity_mem G u v, hpos⟩⟩
    linarith [G.sym.nonneg u v]
  have hc : ∀ u v, G.c u v = 0 := by
    intro u v
    have h := hz u v
    simp only [WeightedDiGraph.sym_w] at h
    linarith [G.nonneg u v, G.nonneg v u]
  obtain ⟨r⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hcut := G.minValue_le (properShore_singleton r hn)
  have ho : G.out {r} = 0 := by simp [WeightedDiGraph.out, hc]
  rw [ho] at hcut
  linarith

/-- Positive global value makes the source's intrinsic extrema well-defined. -/
theorem intrinsic_parameters (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    0 < symMinimumPositive G ∧ symMinimumPositive G ≤ symMaximum G ∧
      (∀ u v, G.sym.w u v ≤ symMaximum G) ∧
      ∀ u v, 0 < G.sym.w u v → symMinimumPositive G ≤ G.sym.w u v := by
  classical
  have hne := positiveSymCapacities_nonempty G hn hlam
  have hmem : symMinimumPositive G ∈ positiveSymCapacities G := by
    rw [symMinimumPositive, dite_eq_left hne]
    exact min'_mem _ _
  have hpos : 0 < symMinimumPositive G := (mem_filter.mp hmem).2
  have hupper : symMinimumPositive G ≤ symMaximum G := by
    obtain ⟨p, _, hp⟩ := mem_image.mp (mem_filter.mp hmem).1
    rw [← hp]
    exact pair_le_symMaximum G p.1 p.2
  refine ⟨hpos, hupper, pair_le_symMaximum G, fun u v huv => ?_⟩
  rw [symMinimumPositive, dite_eq_left hne]
  exact min'_le _ _ (mem_filter.mpr ⟨symCapacity_mem G u v, huv⟩)

theorem q_eq_zero_of_positive_lower_bound (G : WeightedDiGraph V) {t : ℝ}
    (hlower : ∀ u v, 0 < G.sym.w u v → t ≤ G.sym.w u v) : PruningData.q G t = 0 := by
  classical
  have hf : (univ.filter fun p : V × V => 0 < G.sym.w p.1 p.2 ∧ G.sym.w p.1 p.2 < t) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have h := (mem_filter.mp hp).2
    exact (not_lt_of_ge (hlower p.1 p.2 h.1)) h.2
  simp only [PruningData.q, hf, image_empty, card_empty]

/-- A minimum-size certificate exists because some finite certificate does.
It may be used uniformly for all later choices of threshold and bound. -/
theorem exists_card_minimal_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      ∀ Q' S', IsMinCutWitnessCertificate G Q' S' → Q.card ≤ Q'.card := by
  classical
  have hex : ∃ m : ℕ, ∃ Q S, IsMinCutWitnessCertificate G Q S ∧ Q.card = m := by
    obtain ⟨S, hS⟩ := all_shores_witnessCertificate G hn
    exact ⟨(univ : Finset (Finset V)).card, univ, S, hS, rfl⟩
  obtain ⟨Q, S, hcert, hcard⟩ := Nat.find_spec hex
  refine ⟨Q, S, hcert, fun Q' S' hcert' => ?_⟩
  rw [hcard]
  exact Nat.find_min' hex ⟨Q', S', hcert', rfl⟩

noncomputable def weightedHeadlineConstant : ℝ :=
  512 * (5 + (6 / Real.log 2 + 1) ^ 2 * (2 : ℝ) ^ ((1 : ℝ) / 3))

/-- Weighted headline on an arbitrary finite vertex type, with the same
explicit constant as the already accepted `Fin n` endpoint. -/
theorem exists_weighted_global_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, (Q.card : ℝ) ≤ weightedHeadlineConstant *
        (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3) ∧ IsMinCutWitnessCertificate G Q S := by
  classical
  obtain ⟨k, hk, hkn, hbudget⟩ := exists_optimized_budget 512 (Fintype.card V) hn
  obtain ⟨r⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨Q, S, hQ, hcert⟩ := exists_uniform_certificate G r hk hkn
  have hQR : (Q.card : ℝ) ≤ budget 512 (Fintype.card V) k := by exact_mod_cast hQ
  refine ⟨Q, S, hQR.trans ?_, hcert⟩
  simpa only [weightedHeadlineConstant, Nat.cast_ofNat] using hbudget

/-- One certificate attains the better weighted/quadratic bound and all
intrinsic thresholds simultaneously. Competitors remain unrestricted. -/
theorem exists_simultaneous_intrinsic_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) {U : ℝ}
    (hU : ∀ u v, G.sym.w u v ≤ U) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (20 * (Fintype.card V : ℝ) ^ 2) ∧
      ∀ t : ℝ, 0 < t → t ≤ U → (Q.card : ℝ) ≤
        1000 * ((PruningData.q G t : ℝ) + (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
          Real.sqrt (U / t)) := by
  obtain ⟨Q, S, hcert, hminimal⟩ := exists_card_minimal_witnessCertificate G hn
  have hbound : ∀ (Q' : Finset (Finset V)) (S' : Finset V) (b : ℝ),
      (Q'.card : ℝ) ≤ b → IsMinCutWitnessCertificate G Q' S' →
      (Q.card : ℝ) ≤ b := by
    intro Q' S' b hb hcert'
    have hle : (Q.card : ℝ) ≤ Q'.card := by exact_mod_cast hminimal Q' S' hcert'
    exact hle.trans hb
  refine ⟨Q, S, hcert, le_min ?_ ?_, fun t ht htU => ?_⟩
  · obtain ⟨Q', S', hQ', hcert'⟩ := exists_weighted_global_witnessCertificate G hn
    exact hbound Q' S' _ hQ' hcert'
  · obtain ⟨Q', S', hQ', hcert'⟩ := exists_quadratic_witnessCertificate G hn
    exact hbound Q' S' _ hQ' hcert'
  · obtain ⟨Q', S', hQ', hcert'⟩ := exists_trimmed_witnessCertificate G hn hlam hU ht htU
    exact hbound Q' S' _ hQ' hcert'

/-- The infimum form is justified by an actual minimum-size certificate;
the transcript is chosen before even the real threshold. -/
theorem exists_intrinsic_inf_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (sInf {b : ℝ | ∃ t : ℝ, 0 < t ∧ t ≤ symMaximum G ∧
          b = 1000 * ((PruningData.q G t : ℝ) + (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
            Real.sqrt (symMaximum G / t))}) := by
  obtain ⟨hnu, hnuU, hU, _⟩ := intrinsic_parameters G hn hlam
  have hUpos : 0 < symMaximum G := hnu.trans_le hnuU
  obtain ⟨Q, S, hcert, hbase, hthreshold⟩ := exists_simultaneous_intrinsic_certificate G hn hlam hU
  refine ⟨Q, S, hcert, le_min (hbase.trans (min_le_left _ _)) ?_⟩
  apply le_csInf
  · exact ⟨_, symMaximum G, hUpos, le_rfl, rfl⟩
  · rintro b ⟨t, ht, htU, rfl⟩
    exact hthreshold t ht htU

noncomputable def symSpread (G : WeightedDiGraph V) : ℝ :=
  symMaximum G / symMinimumPositive G

/-- The intrinsic ratio corollary, with the actual positive minimum and
maximum pair capacities. This strengthens the source by removing the log. -/
theorem exists_intrinsic_ratio_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (1000 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (symSpread G)) := by
  obtain ⟨hnu, hnuU, hU, hlower⟩ := intrinsic_parameters G hn hlam
  obtain ⟨Q, S, hcert, hbase, hthreshold⟩ := exists_simultaneous_intrinsic_certificate G hn hlam hU
  have hq := q_eq_zero_of_positive_lower_bound G hlower
  have hratio := hthreshold (symMinimumPositive G) hnu hnuU
  rw [hq, Nat.cast_zero, zero_add] at hratio
  refine ⟨Q, S, hcert, le_min (hbase.trans (min_le_left _ _)) ?_⟩
  simpa only [symSpread, mul_assoc] using hratio

/-- `cor:small`: an actual positive directed-weight lower bound is used
only to charge retained input capacities, never to restrict competitors. -/
theorem exists_min_positive_weight_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) {mu : ℝ} (hmu : 0 < mu)
    (hlower : ∀ u v, 0 < G.c u v → mu ≤ G.c u v) :
    ∃ Q S, (Q.card : ℝ) ≤ 60 * Fintype.card V +
        6 * Fintype.card V * G.minValue / mu + 1 ∧ IsMinCutWitnessCertificate G Q S := by
  have hpair : ∀ u v, 0 < G.sym.w u v → mu ≤ G.sym.w u v := by
    intro u v hpos
    by_cases huv : 0 < G.c u v
    · have h := hlower u v huv
      simp only [WeightedDiGraph.sym_w]
      linarith [G.nonneg v u]
    · have hz : G.c u v = 0 := le_antisymm (le_of_not_gt huv) (G.nonneg u v)
      have hrev : 0 < G.c v u := by simpa only [WeightedDiGraph.sym_w, hz, zero_add] using hpos
      have h := hlower v u hrev
      simp only [WeightedDiGraph.sym_w, hz, zero_add]
      exact h
  have hq := q_eq_zero_of_positive_lower_bound G hpair
  obtain ⟨Q, S, hQ, hcert⟩ := exists_threshold_witnessCertificate G hn hmu
  refine ⟨Q, S, ?_, hcert⟩
  simpa only [hq, Nat.cast_zero, mul_zero, add_zero] using hQ

/-- Tiny outliers are charged by their count, without affecting the spread
of the remaining pairs. The quadratic alternative is included explicitly. -/
theorem exists_outlier_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) {U t : ℝ} {k : ℕ}
    (hU : ∀ u v, G.sym.w u v ≤ U) (ht : 0 < t) (htU : t ≤ U)
    (houtliers : PruningData.q G t ≤ k) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (20 * (Fintype.card V : ℝ) ^ 2)
        (1000 * ((k : ℝ) + (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (U / t))) := by
  obtain ⟨Q, S, hcert, hbase, hthreshold⟩ := exists_simultaneous_intrinsic_certificate G hn hlam hU
  have hq : (PruningData.q G t : ℝ) ≤ k := by exact_mod_cast houtliers
  refine ⟨Q, S, hcert, le_min (hbase.trans (min_le_right _ _)) ?_⟩
  have h := hthreshold t ht htU
  linarith

theorem one_le_log_two_mul (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Real.log (2 * (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log (4 : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hfour] at hlog
  linarith [Real.log_two_gt_d9]

theorem sqrt_le_sqrt_mul_log (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ Real.sqrt (x * Real.log (2 * (n : ℝ))) := by
  apply Real.sqrt_le_sqrt
  have h := mul_le_mul_of_nonneg_left (one_le_log_two_mul n hn) hx
  simpa only [mul_one] using h

/-- The source's literal logarithmic trimmed bound, obtained from the
stronger constructed bound. No numerical or support premise is put on G'. -/
theorem exists_trimmed_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) {U t : ℝ}
    (hU : ∀ u v, G.sym.w u v ≤ U) (ht : 0 < t) (htU : t ≤ U) :
    ∃ Q S, (Q.card : ℝ) ≤ 1000 * ((PruningData.q G t : ℝ) +
        (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
          Real.sqrt ((U / t) * Real.log (2 * (Fintype.card V : ℝ)))) ∧
      IsMinCutWitnessCertificate G Q S := by
  obtain ⟨Q, S, hQ, hcert⟩ := exists_trimmed_witnessCertificate G hn hlam hU ht htU
  have hroot := sqrt_le_sqrt_mul_log (Fintype.card V) hn
    (div_nonneg (ht.trans_le htU).le ht.le)
  have hmul := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) by positivity)
  exact ⟨Q, S, hQ.trans (by linarith), hcert⟩

/-- The literal paper infimum/minimum form, now instantiated with the actual
symmetrized maximum and an actual fixed certificate before all thresholds. -/
theorem exists_intrinsic_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (sInf {b : ℝ | ∃ t : ℝ, 0 < t ∧ t ≤ symMaximum G ∧
          b = 1000 * ((PruningData.q G t : ℝ) + (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
            Real.sqrt ((symMaximum G / t) * Real.log (2 * (Fintype.card V : ℝ))))}) := by
  obtain ⟨hnu, hnuU, hU, _⟩ := intrinsic_parameters G hn hlam
  have hUpos : 0 < symMaximum G := hnu.trans_le hnuU
  obtain ⟨Q, S, hcert, hminimal⟩ := exists_card_minimal_witnessCertificate G hn
  refine ⟨Q, S, hcert, le_min ?_ ?_⟩
  · obtain ⟨Q', S', hQ', hcert'⟩ := exists_weighted_global_witnessCertificate G hn
    have hle : (Q.card : ℝ) ≤ Q'.card := by exact_mod_cast hminimal Q' S' hcert'
    exact hle.trans hQ'
  · apply le_csInf
    · exact ⟨_, symMaximum G, hUpos, le_rfl, rfl⟩
    · rintro b ⟨t, ht, htU, rfl⟩
      obtain ⟨Q', S', hQ', hcert'⟩ := exists_trimmed_paper_certificate G hn hlam hU ht htU
      have hle : (Q.card : ℝ) ≤ Q'.card := by exact_mod_cast hminimal Q' S' hcert'
      exact hle.trans hQ'

/-- The unit-capacity global corollary, with its original logarithmic order
and the full unrestricted competitor class; the stronger constant-600 bound
is the accepted `exists_unit_global_certificate`. -/
theorem exists_unit_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) :
    ∃ Q S, (Q.card : ℝ) ≤ 600 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
        Real.sqrt (Real.log (2 * (Fintype.card V : ℝ))) ∧ IsMinCutWitnessCertificate G Q S := by
  obtain ⟨Q, S, hQ, hcert⟩ := exists_unit_global_certificate G hn hunit
  have hroot : 1 ≤ Real.sqrt (Real.log (2 * (Fintype.card V : ℝ))) :=
    Real.le_sqrt_of_sq_le (by simpa using one_le_log_two_mul (Fintype.card V) hn)
  refine ⟨Q, S, hQ.trans ?_, hcert⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 600 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) by positivity)

/-- Ordinary unit-domain certificates follow by restricting the accepted
weighted-robust upper bound. This does not identify the two certificate notions
and makes no lower-bound claim about either competitor class. -/
theorem exists_unit_domain_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) :
    ∃ Q S, (Q.card : ℝ) ≤ 600 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) ∧ S ∈ Q ∧
      ∀ G' : WeightedDiGraph V, (∀ u v, G'.c u v = 0 ∨ G'.c u v = 1) →
        Consistent G G' Q → IsGlobalMinCut G' S ∧ G'.minValue = G.minValue := by
  obtain ⟨Q, S, hQ, hcert⟩ := exists_unit_global_certificate G hn hunit
  exact ⟨Q, S, hQ, hcert.1, fun G' _ hG' =>
    ⟨hcert.2 G' hG', hcert.isValueCertificate G' hG'⟩⟩

/-- The source's refined large-case expression follows from the stronger
common-source estimate. `M` may be the actual maximum capacity of `C.H`. -/
theorem exists_mass_large_paper_certificate {G : WeightedDiGraph V} (C : PruningCert G)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) {M : ℝ} (hMpos : 0 < M)
    (hM : ∀ u v, C.H.c u v ≤ M) :
    ∃ Q S, (Q.card : ℝ) ≤ 1200 * ((Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) +
        (Fintype.card V : ℝ) ^ 2 * M * Real.log (2 + G.minValue / M) / G.minValue) ∧
      IsMinCutWitnessCertificate G Q S := by
  obtain ⟨Q, S, hQ, hcert⟩ := exists_pruned_refined_large_certificate C hn hlam hMpos hM
  have hlog2 : Real.log 2 ≤ Real.log (2 + G.minValue / M) :=
    Real.log_le_log (by norm_num) (by linarith [div_pos hlam hMpos])
  have hlog : (1 : ℝ) / 2 ≤ Real.log (2 + G.minValue / M) := by
    linarith [Real.log_two_gt_d9]
  have hterm := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ (Fintype.card V : ℝ) ^ 2 * M / G.minValue by positivity)
  have hterm' : ((Fintype.card V : ℝ) ^ 2 * M / G.minValue) / 2 ≤
      (Fintype.card V : ℝ) ^ 2 * M * Real.log (2 + G.minValue / M) / G.minValue := by
    calc ((Fintype.card V : ℝ) ^ 2 * M / G.minValue) / 2
        = ((Fintype.card V : ℝ) ^ 2 * M / G.minValue) * ((1 : ℝ) / 2) := by ring
      _ ≤ ((Fintype.card V : ℝ) ^ 2 * M / G.minValue) *
          Real.log (2 + G.minValue / M) := hterm
      _ = (Fintype.card V : ℝ) ^ 2 * M *
          Real.log (2 + G.minValue / M) / G.minValue := by ring
  refine ⟨Q, S, hQ.trans ?_, hcert⟩
  have hpower : 0 ≤ (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  nlinarith

/-- Literal source ratio order using its intrinsic kappa, with unrestricted
competitors and the better arbitrary-weight bound retained. -/
theorem exists_intrinsic_ratio_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (1000 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
          Real.sqrt (symSpread G * Real.log (2 * (Fintype.card V : ℝ)))) := by
  obtain ⟨hnu, hnuU, _, _⟩ := intrinsic_parameters G hn hlam
  have hratio : 0 ≤ symSpread G := div_nonneg (hnu.trans_le hnuU).le hnu.le
  have hroot := sqrt_le_sqrt_mul_log (Fintype.card V) hn hratio
  have hterm := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 1000 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) by positivity)
  obtain ⟨Q, S, hcert, hQ⟩ := exists_intrinsic_ratio_certificate G hn hlam
  exact ⟨Q, S, hcert, le_min (hQ.trans (min_le_left _ _))
    ((hQ.trans (min_le_right _ _)).trans hterm)⟩

/-- The source's tiny-outlier corollary in its written logarithmic form. -/
theorem exists_outlier_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) {U t : ℝ} {k : ℕ}
    (hU : ∀ u v, G.sym.w u v ≤ U) (ht : 0 < t) (htU : t ≤ U)
    (houtliers : PruningData.q G t ≤ k) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (20 * (Fintype.card V : ℝ) ^ 2)
        (1000 * ((k : ℝ) + (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
          Real.sqrt ((U / t) * Real.log (2 * (Fintype.card V : ℝ))))) := by
  obtain ⟨Q, S, hcert, hQ⟩ := exists_outlier_certificate G hn hlam hU ht htU houtliers
  have hroot := sqrt_le_sqrt_mul_log (Fintype.card V) hn
    (div_nonneg (ht.trans_le htU).le ht.le)
  have hterm := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) by positivity)
  refine ⟨Q, S, hcert, le_min (hQ.trans (min_le_left _ _)) ?_⟩
  exact (hQ.trans (min_le_right _ _)).trans (by linarith)

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.intrinsic_parameters
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_simultaneous_intrinsic_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_inf_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_ratio_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_min_positive_weight_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_outlier_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_paper_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_unit_paper_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_unit_domain_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_mass_large_paper_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_ratio_paper_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_outlier_paper_certificate
