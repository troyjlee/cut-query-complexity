import CutQueryComplexity.DirectedCertificate.FlowMeasure

set_option autoImplicit false

/-! # Capacity bins and verification by actual cut queries

The finite binning argument used in `lem:mass-cap`. Bins are selected from the
input weights before a competitor is quantified. A bin total is a compiled
measurement, so nonnegativity certifies every constituent weight separately.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset WeightedDiGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Items of weight at most half the cap contain a bin with mass between half
the cap and the cap whenever their total mass reaches half the cap. -/
theorem exists_half_bin {ι : Type*} [DecidableEq ι] (w : ι → ℝ) {B : ℝ}
    (hB : 0 < B) (S : Finset ι) (hw : ∀ i ∈ S, w i ≤ B / 2)
    (hmass : B / 2 ≤ ∑ i ∈ S, w i) :
    ∃ T ⊆ S, B / 2 ≤ ∑ i ∈ T, w i ∧ ∑ i ∈ T, w i ≤ B := by
  revert hw hmass
  induction S using Finset.induction_on with
  | empty => intro _ hmass; simp only [sum_empty] at hmass; linarith
  | @insert a S ha ih =>
    intro hw hmass
    by_cases hs : B / 2 ≤ ∑ i ∈ S, w i
    · obtain ⟨T, hT, hlow, hupp⟩ := ih (fun i hi => hw i (mem_insert_of_mem hi)) hs
      exact ⟨T, hT.trans (subset_insert a S), hlow, hupp⟩
    · refine ⟨insert a S, subset_rfl, hmass, ?_⟩
      rw [sum_insert ha]
      have := hw a (mem_insert_self a S)
      linarith

/-- Finite capacity bins, including an explicit total-mass bound on their count.
The last bin may be small (or empty); all other bins pay at least `B/2`. -/
theorem exists_capacity_bins {ι : Type*} [DecidableEq ι] (w : ι → ℝ)
    {B : ℝ} (hB : 0 < B) (S : Finset ι)
    (hw0 : ∀ i ∈ S, 0 ≤ w i) (hw : ∀ i ∈ S, w i ≤ B / 2) :
    ∃ bins : List (Finset ι),
      (∀ T ∈ bins, T ⊆ S ∧ ∑ i ∈ T, w i ≤ B) ∧
      (∀ i ∈ S, ∃ T ∈ bins, i ∈ T) ∧
      (bins.length : ℝ) ≤ 1 + 2 * (∑ i ∈ S, w i) / B := by
  revert hw0 hw
  refine Finset.strongInductionOn S ?_
  intro S ih hw0 hw
  by_cases hs : ∑ i ∈ S, w i ≤ B
  · refine ⟨[S], ?_, ?_, ?_⟩
    · intro T hT
      have heq : T = S := List.mem_singleton.mp hT
      subst T
      exact ⟨subset_refl S, hs⟩
    · exact fun i hi => ⟨S, by simp, hi⟩
    · simp only [List.length_singleton, Nat.cast_one]
      have : 0 ≤ 2 * (∑ i ∈ S, w i) / B :=
        div_nonneg (mul_nonneg (by norm_num) (sum_nonneg hw0)) hB.le
      linarith
  · have hhalf : B / 2 ≤ ∑ i ∈ S, w i := by linarith
    obtain ⟨T, hTS, hTlow, hTupp⟩ := exists_half_bin w hB S hw hhalf
    have hTne : T.Nonempty := by
      by_contra ht
      rw [not_nonempty_iff_eq_empty.mp ht, sum_empty] at hTlow
      linarith
    obtain ⟨bins, hbins, hcover, hcount⟩ := ih (S \ T) (sdiff_ssubset hTS hTne)
      (fun i hi => hw0 i (mem_sdiff.mp hi).1) (fun i hi => hw i (mem_sdiff.mp hi).1)
    refine ⟨T :: bins, ?_, ?_, ?_⟩
    · intro U hU
      rcases List.mem_cons.mp hU with rfl | hU
      · exact ⟨hTS, hTupp⟩
      · exact ⟨(hbins U hU).1.trans sdiff_subset, (hbins U hU).2⟩
    · intro i hi
      by_cases hit : i ∈ T
      · exact ⟨T, List.mem_cons_self, hit⟩
      · obtain ⟨U, hU, hiU⟩ := hcover i (mem_sdiff.mpr ⟨hi, hit⟩)
        exact ⟨U, List.mem_cons_of_mem T hU, hiU⟩
    · have hsum : (∑ i ∈ S \ T, w i) + ∑ i ∈ T, w i = ∑ i ∈ S, w i :=
        sum_sdiff hTS
      have hpay : 1 ≤ 2 * (∑ i ∈ T, w i) / B := by
        apply (le_div_iff₀ hB).2
        linarith
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [← hsum, mul_add, add_div]
      linarith

/-- Fixing a nonnegative bin total bounds every entry in that bin. -/
theorem entry_le_of_bin_sum {ι : Type*} [DecidableEq ι] {w w' : ι → ℝ}
    {T : Finset ι} {i : ι} {B : ℝ} (hw' : ∀ j ∈ T, 0 ≤ w' j)
    (hi : i ∈ T) (hsum : ∑ j ∈ T, w' j = ∑ j ∈ T, w j)
    (hcap : ∑ j ∈ T, w j ≤ B) : w' i ≤ B := by
  calc w' i ≤ ∑ j ∈ T, w' j := single_le_sum hw' hi
    _ = ∑ j ∈ T, w j := hsum
    _ ≤ B := hcap

/-- Compile the bin construction to original outgoing-cut queries. The input
needs only a compiler for subset totals, not an arbitrary linear-query oracle. -/
theorem exists_compiled_capacity_cap {ι : Type*} [DecidableEq ι]
    (G : WeightedDiGraph V) (w : WeightedDiGraph V → ι → ℝ)
    (S : Finset ι) {B : ℝ} (hB : 0 < B) {c : ℕ}
    (M : ∀ T : Finset ι, Compiled G (fun G' => ∑ i ∈ T, w G' i))
    (hM : ∀ T, (M T).cost ≤ c)
    (hw0 : ∀ G' : WeightedDiGraph V, ∀ i ∈ S, 0 ≤ w G' i)
    (hw : ∀ i ∈ S, w G i ≤ B / 2) :
    ∃ Q : Finset (Finset V),
      (Q.card : ℝ) ≤ c * (1 + 2 * (∑ i ∈ S, w G i) / B) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ i ∈ S, w G' i ≤ B := by
  classical
  obtain ⟨bins, hbins, hcover, hcount⟩ := exists_capacity_bins (w G) hB S (hw0 G) hw
  let Q := bins.toFinset.biUnion fun T => (M T).shores
  have hQ : Q.card ≤ c * bins.length := by
    have hc : Q.card ≤ c * bins.toFinset.card :=
      card_biUnion_le_mul _ _ _ (fun T _ => hM T)
    exact hc.trans (Nat.mul_le_mul_left c bins.toFinset_card_le)
  refine ⟨Q, ?_, fun G' hG' i hi => ?_⟩
  · have hc : (Q.card : ℝ) ≤ c * (bins.length : ℝ) := by exact_mod_cast hQ
    exact hc.trans (mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg c))
  · obtain ⟨T, hT, hiT⟩ := hcover i hi
    have ht := hbins T hT
    exact entry_le_of_bin_sum (fun j hj => hw0 G' j (ht.1 hj)) hiT
      ((M T).fixes G' (consistent_biUnion.mp hG' T (List.mem_toFinset.mpr hT))) ht.2

/-- **Mass-cap verification for the actual pruned graph.** The original query
cost is bounded by total retained capacity. Competitors have no support or
capacity restriction; the conclusion is forced by the selected bin queries. -/
theorem exists_pruning_capacity_cap {G : WeightedDiGraph V} (C : PruningCert G)
    {B : ℝ} (hB : 0 < B) (hcap : ∀ u v, C.H.c u v ≤ B / 2) :
    ∃ Q : Finset (Finset V),
      (Q.card : ℝ) ≤ 3 * Fintype.card V + 6 * total C.H.c / B ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        ∀ u v, (C.toGraph G').c u v ≤ B := by
  classical
  have hex : ∀ u : V, ∃ Q : Finset (Finset V),
      (Q.card : ℝ) ≤ 3 * (1 + 2 * (∑ v, C.H.c u v) / B) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ v, (C.toGraph G').c u v ≤ B := by
    intro u
    obtain ⟨Q, hQ, hcert⟩ := exists_compiled_capacity_cap G
      (fun G' v => (C.toGraph G').c u v) univ hB (C.outStar u) (C.outStar_cost u)
      (fun G' v _ => (C.toGraph G').nonneg u v)
      (fun v _ => by rw [C.toGraph_self]; exact hcap u v)
    refine ⟨Q, ?_, fun G' hG' v => hcert G' hG' v (mem_univ v)⟩
    simpa only [C.toGraph_self, Nat.cast_ofNat] using hQ
  choose Q hQ hcert using hex
  refine ⟨univ.biUnion Q, ?_, fun G' hG' u v =>
    hcert u G' (consistent_biUnion.mp hG' u (mem_univ u)) v⟩
  have hc : ((univ.biUnion Q).card : ℝ) ≤ ∑ u, ((Q u).card : ℝ) := by
    exact_mod_cast (card_biUnion_le : (univ.biUnion Q).card ≤ ∑ u, (Q u).card)
  calc ((univ.biUnion Q).card : ℝ) ≤ ∑ u, ((Q u).card : ℝ) := hc
    _ ≤ ∑ u : V, 3 * (1 + 2 * (∑ v, C.H.c u v) / B) := sum_le_sum fun u _ => hQ u
    _ = 3 * Fintype.card V + 6 * total C.H.c / B := by
      simp only [total, mul_add, sum_add_distrib, ← mul_sum, ← sum_div,
        sum_const, card_univ, nsmul_eq_mul]
      ring

/-- The pruning theorem turns the preceding bound into the source's
`O(n + n λ / B)` bound, with explicit constants. -/
theorem exists_pruning_mass_cap {G : WeightedDiGraph V} (C : PruningCert G)
    {B : ℝ} (hB : 0 < B) (hcap : ∀ u v, C.H.c u v ≤ B / 2) :
    ∃ Q : Finset (Finset V),
      (Q.card : ℝ) ≤ 3 * Fintype.card V +
        12 * (((Fintype.card V : ℝ) - 1) * G.minValue) / B ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        ∀ u v, (C.toGraph G').c u v ≤ B := by
  obtain ⟨Q, hQ, hcert⟩ := exists_pruning_capacity_cap C hB hcap
  refine ⟨Q, hQ.trans ?_, hcert⟩
  have htotal := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left C.total_le (by norm_num : (0 : ℝ) ≤ 6)) hB.le
  calc 3 * Fintype.card V + 6 * total C.H.c / B
      ≤ 3 * Fintype.card V + 6 * (2 * (((Fintype.card V : ℝ) - 1) * G.minValue)) / B :=
        add_le_add le_rfl htotal
    _ = 3 * Fintype.card V + 12 * (((Fintype.card V : ℝ) - 1) * G.minValue) / B := by ring

/-- Restrict capacities to a fixed set of ordered pairs. The mask is chosen
from the input, so it is the same for every competitor. -/
noncomputable def maskGraph (H : WeightedDiGraph V) (E : Finset (V × V)) :
    WeightedDiGraph V where
  c u v := if (u, v) ∈ E then H.c u v else 0
  nonneg u v := by split_ifs <;> first | exact H.nonneg u v | exact le_rfl
  diag u := by simp [H.diag]

theorem maskGraph_split (H : WeightedDiGraph V) (E : Finset (V × V)) (u v : V) :
    H.c u v = (maskGraph H E).c u v + (maskGraph H Eᶜ).c u v := by
  by_cases h : (u, v) ∈ E <;> simp [maskGraph, h]

/-- A fixed mask is implemented by filtering the measured star, so it keeps
the pruning compiler's constant query cost. -/
noncomputable def maskedOutStar {G : WeightedDiGraph V} (C : PruningCert G)
    (E : Finset (V × V)) (u : V) (T : Finset V) :
    Compiled G (fun G' => ∑ v ∈ T, (maskGraph (C.toGraph G') E).c u v) :=
  (C.outStar u (T.filter fun v => (u, v) ∈ E)).congr fun G' => by
    simp only [sum_filter, maskGraph]

noncomputable def maskedInStar {G : WeightedDiGraph V} (C : PruningCert G)
    (E : Finset (V × V)) (v : V) (T : Finset V) :
    Compiled G (fun G' => ∑ u ∈ T, (maskGraph (C.toGraph G') E).c u v) :=
  (C.inStar v (T.filter fun u => (u, v) ∈ E)).congr fun G' => by
    simp only [sum_filter, maskGraph]

theorem maskedOutStar_cost {G : WeightedDiGraph V} (C : PruningCert G)
    (E : Finset (V × V)) (u : V) (T : Finset V) :
    (maskedOutStar C E u T).cost ≤ 3 := C.outStar_cost _ _

theorem maskedInStar_cost {G : WeightedDiGraph V} (C : PruningCert G)
    (E : Finset (V × V)) (v : V) (T : Finset V) :
    (maskedInStar C E v T).cost ≤ 3 := C.inStar_cost _ _

/-- The mass-cap lemma applies just to the chosen light arcs. Capacities on
the complementary heavy arcs need not satisfy its input cap. -/
theorem exists_masked_capacity_cap {G : WeightedDiGraph V} (C : PruningCert G)
    (E : Finset (V × V)) {B : ℝ} (hB : 0 < B)
    (hcap : ∀ u v, (u, v) ∈ E → C.H.c u v ≤ B / 2) :
    ∃ Q : Finset (Finset V),
      (Q.card : ℝ) ≤ 3 * Fintype.card V + 6 * total C.H.c / B ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        ∀ u v, (maskGraph (C.toGraph G') E).c u v ≤ B := by
  classical
  have hex : ∀ u : V, ∃ Q : Finset (Finset V),
      (Q.card : ℝ) ≤ 3 * (1 + 2 * (∑ v, C.H.c u v) / B) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        ∀ v, (maskGraph (C.toGraph G') E).c u v ≤ B := by
    intro u
    obtain ⟨Q, hQ, hcert⟩ := exists_compiled_capacity_cap G
      (fun G' v => (maskGraph (C.toGraph G') E).c u v) univ hB
      (maskedOutStar C E u) (maskedOutStar_cost C E u)
      (fun G' v _ => (maskGraph (C.toGraph G') E).nonneg u v)
      (fun v _ => by
        by_cases h : (u, v) ∈ E
        · simpa only [maskGraph, ite_eq_left h, C.toGraph_self] using hcap u v h
        · simp only [maskGraph, ite_eq_right h]; positivity)
    refine ⟨Q, hQ.trans ?_, fun G' hG' v => hcert G' hG' v (mem_univ v)⟩
    have hmass : (∑ v, (maskGraph (C.toGraph G) E).c u v) ≤ ∑ v, C.H.c u v := by
      apply sum_le_sum
      intro v _
      by_cases h : (u, v) ∈ E
      · simp [maskGraph, h, C.toGraph_self]
      · simpa [maskGraph, h] using C.H.nonneg u v
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 2)) hB.le
    norm_num only [Nat.cast_ofNat] at hQ ⊢
    linarith
  choose Q hQ hcert using hex
  refine ⟨univ.biUnion Q, ?_, fun G' hG' u v =>
    hcert u G' (consistent_biUnion.mp hG' u (mem_univ u)) v⟩
  have hc : ((univ.biUnion Q).card : ℝ) ≤ ∑ u, ((Q u).card : ℝ) := by
    exact_mod_cast (card_biUnion_le : (univ.biUnion Q).card ≤ ∑ u, (Q u).card)
  calc ((univ.biUnion Q).card : ℝ) ≤ ∑ u, ((Q u).card : ℝ) := hc
    _ ≤ ∑ u : V, 3 * (1 + 2 * (∑ v, C.H.c u v) / B) := sum_le_sum fun u _ => hQ u
    _ = 3 * Fintype.card V + 6 * total C.H.c / B := by
      simp only [total, mul_add, sum_add_distrib, ← mul_sum, ← sum_div,
        sum_const, card_univ, nsmul_eq_mul]
      ring

/-- Both degree vectors of a fixed residual mask are forced by `6n` original
outgoing-cut queries. This also supports the reversed comparison graph. -/
theorem exists_masked_degree_certificate {G : WeightedDiGraph V} (C : PruningCert G)
    (E : Finset (V × V)) :
    ∃ Q : Finset (Finset V), Q.card ≤ 6 * Fintype.card V ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ v,
        (maskGraph (C.toGraph G') E).outdeg v = (maskGraph C.H E).outdeg v ∧
        (maskGraph (C.toGraph G') E).indeg v = (maskGraph C.H E).indeg v := by
  classical
  let Qo : Finset (Finset V) := univ.biUnion fun v => (maskedOutStar C E v univ).shores
  let Qi : Finset (Finset V) := univ.biUnion fun v => (maskedInStar C E v univ).shores
  have ho : Qo.card ≤ 3 * Fintype.card V :=
    (card_biUnion_le_mul _ _ _ fun v _ => maskedOutStar_cost C E v univ).trans_eq (by rw [card_univ])
  have hi : Qi.card ≤ 3 * Fintype.card V :=
    (card_biUnion_le_mul _ _ _ fun v _ => maskedInStar_cost C E v univ).trans_eq (by rw [card_univ])
  refine ⟨Qo ∪ Qi, ?_, fun G' hG' v => ?_⟩
  · calc (Qo ∪ Qi).card ≤ Qo.card + Qi.card := card_union_le _ _
      _ ≤ 3 * Fintype.card V + 3 * Fintype.card V := Nat.add_le_add ho hi
      _ = 6 * Fintype.card V := by omega
  · have ho := (maskedOutStar C E v univ).fixes G'
      (consistent_biUnion.mp (hG'.mono subset_union_left) v (mem_univ v))
    have hi := (maskedInStar C E v univ).fixes G'
      (consistent_biUnion.mp (hG'.mono subset_union_right) v (mem_univ v))
    constructor
    · simpa only [WeightedDiGraph.outdeg, maskGraph, C.toGraph_self] using ho
    · simpa only [WeightedDiGraph.indeg, maskGraph, C.toGraph_self] using hi

/-- Fix any selected ordered capacities of the pruned graph, each through
its existing directed partial-star compiler. -/
theorem exists_fixed_arc_certificate {G : WeightedDiGraph V} (C : PruningCert G)
    (E : Finset (V × V)) :
    ∃ Q : Finset (Finset V), Q.card ≤ 3 * E.card ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        ∀ u v, (u, v) ∈ E → (C.toGraph G').c u v = C.H.c u v := by
  classical
  let Q := E.biUnion fun p => (C.outStar p.1 {p.2}).shores
  refine ⟨Q, card_biUnion_le_mul _ _ _ (fun p _ => C.outStar_cost _ _), ?_⟩
  intro G' hG' u v huv
  have h := (C.outStar u {v}).fixes G' (consistent_biUnion.mp hG' (u, v) huv)
  simpa only [sum_singleton, C.toGraph_self] using h

omit [DecidableEq V] in
/-- The number of arcs above a positive threshold is charged to actual mass. -/
theorem heavy_card_le (H : WeightedDiGraph V) {B : ℝ} (hB : 0 < B) :
    ((univ.filter fun p : V × V => B / 2 < H.c p.1 p.2).card : ℝ) ≤
      2 * total H.c / B := by
  classical
  let E := univ.filter fun p : V × V => B / 2 < H.c p.1 p.2
  have hl : (E.card : ℝ) * (B / 2) ≤ ∑ p ∈ E, H.c p.1 p.2 := by
    calc (E.card : ℝ) * (B / 2) = ∑ _p ∈ E, B / 2 := by simp
      _ ≤ ∑ p ∈ E, H.c p.1 p.2 := sum_le_sum fun p hp => (mem_filter.mp hp).2.le
  have hu : (∑ p ∈ E, H.c p.1 p.2) ≤ total H.c := by
    calc (∑ p ∈ E, H.c p.1 p.2) ≤ ∑ p : V × V, H.c p.1 p.2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ E) (fun p _ _ => H.nonneg _ _)
      _ = total H.c := by simp only [total, Fintype.sum_prod_type]
  apply (le_div_iff₀ hB).2
  change (E.card : ℝ) * B ≤ 2 * total H.c
  linarith

/-- **Complete fixed-heavy/light-residual preparation.** A single query family
is chosen from the input. Every consistent nonnegative competitor then splits
as the same heavy graph plus a capped residual with both degree vectors fixed.
The competitor has no independent support or capacity promise. -/
theorem exists_threshold_preparation {G : WeightedDiGraph V} (C : PruningCert G)
    {B : ℝ} (hB : 0 < B) :
    ∃ (K L : WeightedDiGraph V) (toResidual : WeightedDiGraph V → WeightedDiGraph V)
      (Q : Finset (Finset V)),
      (Q.card : ℝ) ≤ 9 * Fintype.card V + 12 * total C.H.c / B ∧
      (∀ u v, C.H.c u v = K.c u v + L.c u v) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        (∀ u v, (C.toGraph G').c u v = K.c u v + (toResidual G').c u v) ∧
        (∀ v, (toResidual G').outdeg v = L.outdeg v) ∧
        (∀ v, (toResidual G').indeg v = L.indeg v) ∧
        (∀ u v, (toResidual G').c u v ≤ B) := by
  classical
  let E := univ.filter fun p : V × V => B / 2 < C.H.c p.1 p.2
  obtain ⟨Qh, hQh, hheavy⟩ := exists_fixed_arc_certificate C E
  obtain ⟨Qc, hQc, hcap⟩ := exists_masked_capacity_cap C Eᶜ hB (by
    intro u v huv
    have hnot : ¬ B / 2 < C.H.c u v := by simpa [E] using huv
    exact le_of_not_gt hnot)
  obtain ⟨Qd, hQd, hdegree⟩ := exists_masked_degree_certificate C Eᶜ
  refine ⟨maskGraph C.H E, maskGraph C.H Eᶜ,
    fun G' => maskGraph (C.toGraph G') Eᶜ, Qh ∪ Qc ∪ Qd, ?_,
    maskGraph_split C.H E, fun G' hG' => ?_⟩
  · have hc : ((Qh ∪ Qc ∪ Qd).card : ℝ) ≤ Qh.card + Qc.card + Qd.card := by
      exact_mod_cast ((card_union_le (Qh ∪ Qc) Qd).trans
        (Nat.add_le_add_right (card_union_le Qh Qc) Qd.card))
    have hh : (Qh.card : ℝ) ≤ 3 * (E.card : ℝ) := by exact_mod_cast hQh
    have hd : (Qd.card : ℝ) ≤ 6 * Fintype.card V := by exact_mod_cast hQd
    have he : (E.card : ℝ) ≤ 2 * total C.H.c / B := heavy_card_le C.H hB
    have hh' : (Qh.card : ℝ) ≤ 6 * total C.H.c / B :=
      hh.trans ((mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))
    calc (((Qh ∪ Qc ∪ Qd).card : ℝ)) ≤ Qh.card + Qc.card + Qd.card := hc
      _ ≤ 6 * total C.H.c / B + (3 * Fintype.card V + 6 * total C.H.c / B) +
          6 * Fintype.card V := add_le_add (add_le_add hh' hQc) hd
      _ = 9 * Fintype.card V + 12 * total C.H.c / B := by ring
  · have hhh := hheavy G' (hG'.mono (subset_union_left.trans subset_union_left))
    have hcc := hcap G' (hG'.mono (subset_union_right.trans subset_union_left))
    have hdd := hdegree G' (hG'.mono subset_union_right)
    refine ⟨?_, fun v => (hdd v).1, fun v => (hdd v).2, hcc⟩
    intro u v
    by_cases h : (u, v) ∈ E
    · simpa [maskGraph, h] using hhh u v h
    · simp [maskGraph, h]

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_pruning_mass_cap

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_threshold_preparation
