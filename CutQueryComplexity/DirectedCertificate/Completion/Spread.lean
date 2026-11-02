import CutQueryComplexity.DirectedCertificate.Completion.Main

set_option autoImplicit false

/-! # Intrinsic spread via retained mass and common sources

The first construction learns ordinary retained capacities; the second uses
query-enforced degree caps and the constructed common source set. Both choose
actual original outgoing-cut queries before unrestricted weighted competitors.
The common-source route replaces the source's sampled weighted centers.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset WeightedDiGraph

variable {V : Type} [Fintype V] [DecidableEq V]

theorem pruning_ret_pos {G : WeightedDiGraph V} (C : PruningCert G)
    {u v : V} (huv : (u, v) ∈ C.ret) : 0 < C.H.c u v := by
  rw [C.ret_H u v huv]
  have hz : G.sym.w u v ≠ 0 := by
    intro h
    have hs := C.O.sgn_zero u v h
    rw [C.ret_sgn u v huv] at hs
    norm_num at hs
  exact lt_of_le_of_ne (G.sym.nonneg u v) (Ne.symm hz)

/-- Fix only the ordinary retained arcs; fractional exceptional arcs are
already constants in the implicit graph. Include every domination query. -/
theorem exists_retained_witnessCertificate {G : WeightedDiGraph V} (C : PruningCert G)
    (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, (Q.card : ℝ) ≤ 30 * Fintype.card V + 3 * C.ret.card + 1 ∧
      IsMinCutWitnessCertificate G Q S := by
  classical
  obtain ⟨S, hS⟩ := exists_isGlobalMinCut G hn
  obtain ⟨Q, hQ, hfix⟩ := exists_fixed_arc_certificate C C.ret
  refine ⟨insert S (C.queries ∪ Q), S, ?_, mem_insert_self _ _, fun G' hG' => ?_⟩
  · have hc : ((insert S (C.queries ∪ Q)).card : ℝ) ≤
        C.queries.card + Q.card + 1 := by
      exact_mod_cast ((card_insert_le S _).trans
        (Nat.add_le_add_right (card_union_le C.queries Q) 1))
    have hq : (Q.card : ℝ) ≤ 3 * (C.ret.card : ℝ) := by exact_mod_cast hQ
    have hbase : (C.queries.card : ℝ) ≤ 30 * Fintype.card V := by
      exact_mod_cast C.card_queries
    linarith
  · have hC := hG'.mono (subset_union_left.trans (subset_insert S _))
    have hF := hfix G' (hG'.mono (subset_union_right.trans (subset_insert S _)))
    have hH : ∀ u v, (C.toGraph G').c u v = C.H.c u v := by
      intro u v
      by_cases he : IsExc C.E u v
      · simp only [C.toGraph_c, ite_eq_left he]
      · by_cases hr : (u, v) ∈ C.ret
        · exact hF u v hr
        · rw [C.toGraph_c, ite_eq_right he, ite_eq_right hr, C.H_zero u v he hr]
    refine ⟨hS.1, fun T hT => ?_⟩
    rw [hG' S (mem_insert_self _ _), hS.out_eq_minValue]
    calc G.minValue ≤ C.H.out T := C.lam_le_out T hT
      _ = (C.toGraph G').out T := by simp only [WeightedDiGraph.out, hH]
      _ ≤ G'.out T := C.out_le G' hC T

/-- The source's threshold alternative, with `q(t)` counting unordered
positive symmetrized pairs below `t`. No minimum-weight competitor promise. -/
theorem exists_threshold_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) {t : ℝ} (ht : 0 < t) :
    ∃ Q S, (Q.card : ℝ) ≤ 60 * Fintype.card V + 3 * PruningData.q G t +
        6 * Fintype.card V * G.minValue / t + 1 ∧ IsMinCutWitnessCertificate G Q S := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨C⟩ := exists_pruningCert G
  obtain ⟨Q, S, hQ, hcert⟩ := exists_retained_witnessCertificate C hn
  refine ⟨Q, S, hQ.trans ?_, hcert⟩
  have hret : C.ret.card ≤ (univ.filter fun p : V × V => 0 < C.H.c p.1 p.2).card := by
    apply card_le_card
    intro p hp
    exact mem_filter.mpr ⟨mem_univ _, pruning_ret_pos C hp⟩
  have hretR : (C.ret.card : ℝ) ≤
      (univ.filter fun p : V × V => 0 < C.H.c p.1 p.2).card := by exact_mod_cast hret
  have hsupp := C.card_supp_le t ht
  obtain ⟨A, hA⟩ := exists_isGlobalMinCut G hn
  have hlam : 0 ≤ G.minValue := (G.out_nonneg A).trans_eq hA.out_eq_minValue
  have hmass : 2 * (((Fintype.card V : ℝ) - 1) * G.minValue) / t ≤
      2 * Fintype.card V * G.minValue / t := by
    apply div_le_div_of_nonneg_right _ ht.le
    nlinarith
  calc 30 * (Fintype.card V : ℝ) + 3 * C.ret.card + 1
      ≤ 30 * Fintype.card V + 3 * (10 * Fintype.card V + PruningData.q G t +
          2 * (((Fintype.card V : ℝ) - 1) * G.minValue) / t) + 1 := by linarith
    _ ≤ 30 * Fintype.card V + 3 * (10 * Fintype.card V + PruningData.q G t +
          2 * Fintype.card V * G.minValue / t) + 1 := by linarith
    _ = 60 * Fintype.card V + 3 * PruningData.q G t +
        6 * Fintype.card V * G.minValue / t + 1 := by ring

/-- Quadratic fallback obtained by fixing the retained support, using only
the original cut compiler and without reconstructing directed arcs of `G`. -/
theorem exists_quadratic_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, (Q.card : ℝ) ≤ 20 * (Fintype.card V : ℝ) ^ 2 ∧
      IsMinCutWitnessCertificate G Q S := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨C⟩ := exists_pruningCert G
  obtain ⟨Q, S, hQ, hcert⟩ := exists_retained_witnessCertificate C hn
  refine ⟨Q, S, hQ.trans ?_, hcert⟩
  have hret : C.ret.card ≤ Fintype.card V * Fintype.card V := by
    simpa only [Fintype.card_prod] using card_le_univ C.ret
  have hretR : (C.ret.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast (show C.ret.card ≤ Fintype.card V ^ 2 by simpa [pow_two] using hret)
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  nlinarith

/-- Any bound on the original symmetrized pairs bounds every pruned arc,
including fractional exceptional arcs. -/
theorem pruned_arc_le_pair_bound {G : WeightedDiGraph V} (C : PruningCert G)
    {U : ℝ} (hU : ∀ u v, G.sym.w u v ≤ U) (u v : V) : C.H.c u v ≤ U := by
  have hp := C.O.toOrientationData.toGraph_sym_w (Consistent.refl G C.O.queries) u v
  simp only [WeightedDiGraph.sym_w] at hp
  have hpair := hU u v
  simp only [WeightedDiGraph.sym_w] at hpair
  linarith [C.H_le u v, (C.O.toGraph G).nonneg v u]

/-- General degree-cap/common-source assembly. The cap premise is on the
actual pruned input, and its competitor counterpart is enforced by queries. -/
theorem exists_global_certificate_of_pruned_cap {G : WeightedDiGraph V} (C : PruningCert G)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < Fintype.card V) (hlam : 0 < G.minValue)
    (hcap : ∀ u v, C.H.c u v ≤ (G.minValue / k) / 2) :
    ∃ Q S, (Q.card : ℝ) ≤ 39 * Fintype.card V + 12 * Fintype.card V * k +
        120 * Fintype.card V * ((ceilDiv (Fintype.card V) k : ℝ) + 1) + 1 ∧
      IsMinCutWitnessCertificate G Q S := by
  classical
  have hn : 2 ≤ Fintype.card V := by omega
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let r : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨Qs, hQs, hsmall⟩ := exists_degree_cap_small_certificate C hk hn hlam hcap
  obtain ⟨Ql, hQl, hlarge⟩ := exists_largeShore_certificate G r hk hkn.le
  obtain ⟨S, hS⟩ := exists_isGlobalMinCut G hn
  refine ⟨insert S (Qs ∪ Ql), S, ?_, mem_insert_self _ _, fun G' hG' => ?_⟩
  · have hln : Ql.card ≤ 120 * Fintype.card V * (ceilDiv (Fintype.card V) k + 1) := by
      calc Ql.card ≤ 30 * Fintype.card V *
          (4 * (FractionalForest.ceilA (Fintype.card V) k - 1) + 3) := hQl
        _ ≤ 30 * Fintype.card V * (4 * (ceilDiv (Fintype.card V) k + 1)) := by
          apply Nat.mul_le_mul_left (30 * Fintype.card V)
          change 4 * (ceilDiv (Fintype.card V) k - 1) + 3 ≤
            4 * (ceilDiv (Fintype.card V) k + 1)
          have hsub := Nat.sub_le (ceilDiv (Fintype.card V) k) 1
          omega
        _ = 120 * Fintype.card V * (ceilDiv (Fintype.card V) k + 1) := by ring
    have hl : (Ql.card : ℝ) ≤ 120 * Fintype.card V *
        ((ceilDiv (Fintype.card V) k : ℝ) + 1) := by exact_mod_cast hln
    have hc : ((insert S (Qs ∪ Ql)).card : ℝ) ≤ Qs.card + Ql.card + 1 := by
      exact_mod_cast ((card_insert_le S _).trans (Nat.add_le_add_right (card_union_le Qs Ql) 1))
    linarith
  · refine ⟨hS.1, fun T hT => ?_⟩
    rw [hG' S (mem_insert_self _ _), hS.out_eq_minValue]
    have hbase : Consistent G G' (Qs ∪ Ql) := hG'.mono (subset_insert S _)
    by_cases hs : T.card ≤ k ∨ Tᶜ.card ≤ k
    · exact hsmall G' (hbase.mono subset_union_left) T hT hs
    · push Not at hs
      exact hlarge G' (hbase.mono subset_union_right) T (by omega) (by omega)

/-- Rounding any real source parameter in `[1,n)` preserves its scale and
controls the entire degree-cap/common-source query budget. -/
theorem exists_fractional_source_parameter (n : ℕ) (hn : 2 ≤ n) {a : ℝ}
    (ha : 1 ≤ a) (han : a < n) :
    ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ (k : ℝ) ≤ a ∧
      39 * (n : ℝ) + 12 * n * k + 120 * n * ((ceilDiv n k : ℝ) + 1) + 1 ≤
        280 * n + 12 * n * a + 240 * n * ((n : ℝ) / a) := by
  let k : ℕ := ⌊a⌋₊
  have ha0 : 0 < a := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hk : 1 ≤ k := Nat.floor_pos.mpr ha
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hka : (k : ℝ) ≤ a := Nat.floor_le ha0.le
  have hkn : k < n := by exact_mod_cast hka.trans_lt han
  have hhalf : a ≤ 2 * (k : ℝ) := by
    have h := Nat.lt_floor_add_one a
    change a < (k : ℝ) + 1 at h
    linarith
  have hquotN : ceilDiv n k * k ≤ n + k :=
    (Nat.div_mul_le_self (n + k - 1) k).trans (Nat.sub_le _ _)
  have hquot : (ceilDiv n k : ℝ) * (k : ℝ) ≤ n + k := by exact_mod_cast hquotN
  have hnk : (n : ℝ) ≤ (2 * n / a) * k := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhalf hn0]
  have hceil : (ceilDiv n k : ℝ) ≤ 2 * n / a + 1 := by
    apply le_of_mul_le_mul_right (a := (k : ℝ)) ?_ hkR
    nlinarith
  have htermK := mul_le_mul_of_nonneg_left hka hn0
  have htermQ := mul_le_mul_of_nonneg_left hceil hn0
  have htermQ' : (n : ℝ) * (ceilDiv n k : ℝ) ≤ 2 * n * ((n : ℝ) / a) + n := by
    calc (n : ℝ) * (ceilDiv n k : ℝ) ≤ n * (2 * n / a + 1) := htermQ
      _ = 2 * n * ((n : ℝ) / a) + n := by ring
  refine ⟨k, hk, hkn, hka, ?_⟩
  nlinarith

theorem three_halves_eq_mul_half (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ) ^ ((3 : ℝ) / 2) =
      (n : ℝ) ^ ((1 : ℝ) + (1 : ℝ) / 2) := by norm_num
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_add hnR _ _
    _ = (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := by rw [Real.rpow_one]

theorem half_power_sq (n : ℕ) : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-- A stronger replacement for `prop:mass-large`: use the W4 common source
set instead of sampled centers. `M` bounds the actual pruned arcs only.
Every cap imposed on an arbitrary competitor is certified by cut queries. -/
theorem exists_pruned_refined_large_certificate {G : WeightedDiGraph V} (C : PruningCert G)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) {M : ℝ} (hMpos : 0 < M)
    (hM : ∀ u v, C.H.c u v ≤ M) :
    ∃ Q S, (Q.card : ℝ) ≤ 600 * ((Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) +
        (Fintype.card V : ℝ) ^ 2 * M / G.minValue) ∧
      IsMinCutWitnessCertificate G Q S := by
  let n := Fintype.card V
  let a : ℝ := (n : ℝ) ^ ((1 : ℝ) / 2)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := by linarith
  have ha1 : 1 ≤ a := Real.one_le_rpow hn1 (by norm_num)
  have han : a < n := Real.rpow_lt_self_of_one_lt hn2 (by norm_num)
  have hpower : (n : ℝ) ^ ((3 : ℝ) / 2) = n * a :=
    three_halves_eq_mul_half n (by omega)
  have hna := mul_le_mul_of_nonneg_left ha1 hn0.le
  have hmass0 : 0 ≤ (n : ℝ) ^ 2 * M / G.minValue := by positivity
  by_cases hlow : G.minValue < 2 * M
  · obtain ⟨Q, S, hQ, hcert⟩ := exists_quadratic_witnessCertificate G hn
    refine ⟨Q, S, hQ.trans ?_, hcert⟩
    have hbound : 20 * (n : ℝ) ^ 2 ≤ 40 * (n : ℝ) ^ 2 * M / G.minValue := by
      apply (le_div_iff₀ hlam).mpr
      nlinarith [mul_le_mul_of_nonneg_left hlow.le (show 0 ≤ 20 * (n : ℝ) ^ 2 by positivity)]
    have hbound' : 20 * (n : ℝ) ^ 2 ≤ 40 * ((n : ℝ) ^ 2 * M / G.minValue) := by
      convert hbound using 1 <;> ring
    change 20 * (n : ℝ) ^ 2 ≤ 600 * ((n : ℝ) ^ ((3 : ℝ) / 2) + (n : ℝ) ^ 2 * M / G.minValue)
    rw [hpower]
    nlinarith
  have hlamM : 2 * M ≤ G.minValue := le_of_not_gt hlow
  by_cases hhigh : 2 * M * a ≤ G.minValue
  · obtain ⟨k, hk, hkn, hka, hbudget⟩ := exists_unit_parameter n hn
    change (k : ℝ) ≤ a at hka
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hcap : ∀ u v, C.H.c u v ≤ (G.minValue / k) / 2 := by
      intro u v
      apply (hM u v).trans
      have hdiv : 2 * M ≤ G.minValue / k := (le_div_iff₀ hkR).mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hka (show 0 ≤ 2 * M by positivity)])
      linarith
    obtain ⟨Q, S, hQ, hcert⟩ := exists_global_certificate_of_pruned_cap C hk hkn hlam hcap
    refine ⟨Q, S, hQ.trans (hbudget.trans ?_), hcert⟩
    nlinarith
  · let b : ℝ := G.minValue / (2 * M)
    have h2M : 0 < 2 * M := by positivity
    have hb1 : 1 ≤ b := (le_div_iff₀ h2M).mpr (by linarith)
    have hba : b ≤ a := (div_le_iff₀ h2M).mpr (by linarith [le_of_not_ge hhigh])
    obtain ⟨k, hk, hkn, hkb, hbudget⟩ :=
      exists_fractional_source_parameter n hn hb1 (hba.trans_lt han)
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hcap : ∀ u v, C.H.c u v ≤ (G.minValue / k) / 2 := by
      intro u v
      apply (hM u v).trans
      have hprod : (k : ℝ) * (2 * M) ≤ G.minValue := (le_div_iff₀ h2M).mp hkb
      have hdiv : 2 * M ≤ G.minValue / k := (le_div_iff₀ hkR).mpr (by nlinarith)
      linarith
    obtain ⟨Q, S, hQ, hcert⟩ := exists_global_certificate_of_pruned_cap C hk hkn hlam hcap
    refine ⟨Q, S, hQ.trans (hbudget.trans ?_), hcert⟩
    have hterm := mul_le_mul_of_nonneg_left hba hn0.le
    have heq : (n : ℝ) * ((n : ℝ) / b) = 2 * ((n : ℝ) ^ 2 * M / G.minValue) := by
      dsimp [b]
      field_simp [ne_of_gt hlam, ne_of_gt hMpos]
      <;> ring
    change 280 * (n : ℝ) + 12 * n * b + 240 * n * ((n : ℝ) / b) ≤
      600 * ((n : ℝ) ^ ((3 : ℝ) / 2) + (n : ℝ) ^ 2 * M / G.minValue)
    rw [hpower]
    nlinarith

/-- The large-case estimate in terms of an intrinsic symmetrized-pair bound. -/
theorem exists_refined_large_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) {U : ℝ} (hUpos : 0 < U)
    (hU : ∀ u v, G.sym.w u v ≤ U) :
    ∃ Q S, (Q.card : ℝ) ≤ 600 * ((Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) +
        (Fintype.card V : ℝ) ^ 2 * U / G.minValue) ∧
      IsMinCutWitnessCertificate G Q S := by
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨C⟩ := exists_pruningCert G
  exact exists_pruned_refined_large_certificate C hn hlam hUpos
    (pruned_arc_le_pair_bound C hU)

theorem min_add_le_geometric {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    min (a + b) (c + d) ≤ a + c + Real.sqrt (b * d) := by
  by_cases hbd : b ≤ d
  · have hroot : b ≤ Real.sqrt (b * d) := Real.le_sqrt_of_sq_le (by
      nlinarith [mul_le_mul_of_nonneg_left hbd hb])
    exact (min_le_left _ _).trans (by linarith)
  · have hroot : d ≤ Real.sqrt (b * d) := Real.le_sqrt_of_sq_le (by
      nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge hbd) hd])
    exact (min_le_right _ _).trans (by linarith)

/-- The intrinsic trimmed certificate, strengthened by the common-source
route to remove the logarithm. Only actual input pair weights are bounded.
The query family is still uniform over all nonnegative competitors. -/
theorem exists_trimmed_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) {U t : ℝ}
    (hU : ∀ u v, G.sym.w u v ≤ U) (ht : 0 < t) (htU : t ≤ U) :
    ∃ Q S, (Q.card : ℝ) ≤ 1000 * ((PruningData.q G t : ℝ) +
        (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (U / t)) ∧
      IsMinCutWitnessCertificate G Q S := by
  have hUpos : 0 < U := ht.trans_le htU
  let n := Fintype.card V
  let q : ℝ := PruningData.q G t
  let a : ℝ := (n : ℝ) ^ ((1 : ℝ) / 2)
  let r : ℝ := Real.sqrt (U / t)
  let A : ℝ := 60 * n + 3 * q + 1
  let B : ℝ := 6 * n * G.minValue / t
  let C : ℝ := 600 * n * a
  let D : ℝ := 600 * (n : ℝ) ^ 2 * U / G.minValue
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have ha1 : 1 ≤ a := Real.one_le_rpow hn1 (by norm_num)
  have ha0 : 0 ≤ a := by linarith
  have hratio : 1 ≤ U / t := (le_div_iff₀ ht).mpr (by simpa using htU)
  have hr1 : 1 ≤ r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hr0 : 0 ≤ r := by linarith
  have hpower : (n : ℝ) ^ ((3 : ℝ) / 2) = n * a :=
    three_halves_eq_mul_half n (by omega)
  obtain ⟨Qt, St, hQt, hct⟩ := exists_threshold_witnessCertificate G hn ht
  obtain ⟨Ql, Sl, hQl, hcl⟩ := exists_refined_large_certificate G hn hlam hUpos hU
  have hleft : (Qt.card : ℝ) ≤ A + B := by
    dsimp [A, B, q, n]
    linarith
  have hright : (Ql.card : ℝ) ≤ C + D := by
    change (Ql.card : ℝ) ≤ 600 * ((n : ℝ) ^ ((3 : ℝ) / 2) +
      (n : ℝ) ^ 2 * U / G.minValue) at hQl
    rw [hpower] at hQl
    calc (Ql.card : ℝ) ≤ 600 * ((n : ℝ) * a + (n : ℝ) ^ 2 * U / G.minValue) := hQl
      _ = C + D := by dsimp [C, D]; ring
  have hchoice : ∃ Q S, (Q.card : ℝ) ≤ min (A + B) (C + D) ∧
      IsMinCutWitnessCertificate G Q S := by
    by_cases h : A + B ≤ C + D
    · exact ⟨Qt, St, by simpa only [min_eq_left h] using hleft, hct⟩
    · exact ⟨Ql, Sl, by simpa only [min_eq_right (le_of_not_ge h)] using hright, hcl⟩
  obtain ⟨Q, S, hQ, hcert⟩ := hchoice
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hprod : B * D = (60 * n * a * r) ^ 2 := by
    dsimp [B, D, a, r]
    rw [mul_pow, mul_pow, mul_pow, half_power_sq,
      Real.sq_sqrt (div_nonneg hUpos.le ht.le)]
    field_simp [ne_of_gt hlam, ne_of_gt ht]
    <;> ring
  have hroot : Real.sqrt (B * D) = 60 * n * a * r := by
    rw [hprod, Real.sqrt_sq (by positivity)]
  have hgeo := min_add_le_geometric hA hB hC hD
  rw [hroot] at hgeo
  have hna := mul_le_mul_of_nonneg_left ha1 hn0.le
  have hnar := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ (n : ℝ) * a by positivity)
  refine ⟨Q, S, hQ.trans (hgeo.trans ?_), hcert⟩
  change A + C + 60 * n * a * r ≤ 1000 * (q + (n : ℝ) ^ ((3 : ℝ) / 2) * r)
  rw [hpower]
  dsimp [A, C]
  nlinarith

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_retained_witnessCertificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_threshold_witnessCertificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_quadratic_witnessCertificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_global_certificate_of_pruned_cap
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_fractional_source_parameter
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_pruned_refined_large_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_refined_large_certificate
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_trimmed_witnessCertificate
