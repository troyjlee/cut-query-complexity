import CutQueryComplexity.DirectedCertificate.Completion.SmallShore
import CutQueryComplexity.DirectedCertificate.Completion.Budget
import CutQueryComplexity.DirectedCertificate.Completion.Centroid
import CutQueryComplexity.DirectedCertificate.Completion.ConnectedTree
import CutQueryComplexity.DirectedCertificate.Completion.MassCap

set_option autoImplicit false

/-! # One fixed tree cover for all competitors' small violations

The packing, finite tree list, centroid decomposition and local flow
certificates are constructed from the original input before every competitor.
The weighted assembly targets the repository's uniform and headline budgets.
The unit-input refinement uses degree caps and the shared source flows.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset WeightedDiGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Real directed packing plus deterministic halving gives a fixed small tree
cover. No undirected packing theorem and no assumed coverage property is used. -/
theorem exists_comparison_tree_cover (A : WeightedDiGraph V) (r : V) {lam : ℝ}
    (hlam : 0 < lam) (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ A.out S)
    (k : ℕ) :
    ∃ trees : List (InArb r), trees.length ≤ k * Nat.clog 2 (Fintype.card V) + 1 ∧
      ∀ S ∈ comparisonFamily A r lam k, ∃ T ∈ trees, leavingCount T S = 1 := by
  classical
  obtain ⟨a, ha, hasum, hload⟩ := exists_inArb_packing A r lam hlam.le hcut
  have hstep : ∀ R ⊆ comparisonFamily A r lam k,
      ∃ T : InArb r, 2 * (R.filter fun S => ¬ leavingCount T S = 1).card ≤ R.card := by
    intro R hR
    apply exists_half_oneRespecting A hlam a ha hasum hload R
    intro S hS
    obtain ⟨hne, hr, -, hnear⟩ := mem_comparisonFamily.mp (hR hS)
    exact ⟨hne, hr, by linarith⟩
  obtain ⟨trees, hlen, hcover⟩ := exists_halving_cover (comparisonFamily A r lam k)
    (fun (T : InArb r) (S : Finset V) => leavingCount T S = 1) (by
      intro R hR
      obtain ⟨T, hT⟩ := hstep R hR
      refine ⟨T, ?_⟩
      -- The generic predicate and the concrete equality use different deciders.
      convert hT using 1 <;> congr)
  refine ⟨trees, ?_, hcover⟩
  rw [hlen]
  apply small_family_clog_le
  · exact Fintype.card_pos_iff.mpr ⟨r⟩
  · exact fun S hS => (mem_comparisonFamily.mp hS).1
  · exact fun S hS => (mem_comparisonFamily.mp hS).2.2.1

/-- **The W6 cover is chosen before every competitor.** The comparison graph
and tree list depend only on `K`, `L`, the original lower cut bound, `r` and `k`.
Every capped competitor with the fixed residual degrees uses this same list. -/
theorem exists_uniform_violation_tree_cover (H K L : WeightedDiGraph V)
    (hsplit : ∀ u v, H.c u v = K.c u v + L.c u v) (r : V)
    {lam : ℝ} (hlam : 0 < lam) (hcut : ∀ S, ProperShore S → lam ≤ H.out S)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ trees : List (InArb r), trees.length ≤ k * Nat.clog 2 (Fintype.card V) + 1 ∧
      ∀ H' L' : WeightedDiGraph V,
        (∀ u v, H'.c u v = K.c u v + L'.c u v) →
        (∀ u, L'.outdeg u = L.outdeg u) →
        (∀ u v, L'.c u v ≤ lam / (8 * (k : ℝ) ^ 2)) →
        ∀ S : Finset V, S.Nonempty → r ∉ S → S.card ≤ k → H'.out S < lam →
          ∃ T ∈ trees, leavingCount T S = 1 := by
  have hA : ∀ S : Finset V, S.Nonempty → r ∉ S →
      lam ≤ (comparisonGraph K L r).out S := by
    intro S hS hr
    exact (hcut S (properShore_of_not_mem hS hr)).trans (out_le_comparisonGraph hsplit hr)
  obtain ⟨trees, hlen, hcover⟩ := exists_comparison_tree_cover
    (comparisonGraph K L r) r hlam hA k
  refine ⟨trees, hlen, fun H' L' hsplit' hdeg hcap S hS hr hsize hviol => ?_⟩
  exact hcover S (violating_small_mem_comparisonFamily K L hlam.le hk
    hsplit' hdeg hcap hS hr hsize hviol)

/-- One-respecting shores supply the precise internal paths consumed by the
centroid decomposition, after converting the actual arborescence to a tree. -/
theorem parentConnected_of_oneRespecting {r : V} (T : InArb r) {S : Finset V}
    (hr : r ∉ S) (hone : leavingCount T S = 1) : ParentConnected (inArbTree T) S := by
  obtain ⟨x, hx, hpaths⟩ := oneRespecting_internal_paths T hr hone
  refine ⟨x, hx, fun v hv => ?_⟩
  have hmap : (fun a b => a ∈ S ∧ b ∈ S ∧ T.val a = some b) ≤
      (fun a b => a ∈ S ∧ b ∈ S ∧ (inArbTree T).parent a = b) :=
    fun _ _ hstep => ⟨hstep.1, hstep.2.1, inArbTree_parent T hstep.2.2⟩
  exact Relation.ReflTransGen.mono hmap v x (hpaths v hv)

/-- **Connected-tree cut certificate.** Both the logarithmic-volume centroid
decomposition and the local source flows are constructed. Tree edges need not
belong to the graph, and competitors range over all nonnegative graphs. -/
theorem exists_connected_tree_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {cost : ℕ}
    (M : ImplicitMeasures G toGraph cost) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (T : TwoRespecting.RootedTree V) (r : V) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 5 * cost * Fintype.card V * Nat.clog 2 (Fintype.card V) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        ParentConnected T S → r ∉ S → lam ≤ (toGraph G').out S := by
  classical
  let W := univ.erase r
  obtain ⟨nodes, hvalid, hvolume, hcover⟩ := exists_centroid_decomposition T W
  obtain ⟨Q, hQ, hcert⟩ := exists_separator_family_certificate M hlam hcut
    nodes Prod.fst Prod.snd r (fun p hp => (hvalid p hp).2)
    (fun p hp hr => (mem_erase.mp ((hvalid p hp).1 hr)).1 rfl)
  refine ⟨Q, hQ.trans ?_, fun G' hG' S hS hr => ?_⟩
  · have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
    have hW : W.card + 1 = Fintype.card V := by
      simp only [W, card_erase_of_mem (mem_univ r), card_univ]
      omega
    calc 5 * cost * (∑ p ∈ nodes, p.1.card)
        ≤ 5 * cost * (W.card * Nat.clog 2 (W.card + 1)) := Nat.mul_le_mul_left _ hvolume
      _ = 5 * cost * W.card * Nat.clog 2 (Fintype.card V) := by rw [hW]; ring
      _ ≤ 5 * cost * Fintype.card V * Nat.clog 2 (Fintype.card V) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (card_le_univ W))
  · apply hcert G' hG' S
    exact hcover S (fun v hv => mem_erase.mpr ⟨fun h => hr (h ▸ hv), mem_univ v⟩) hS

/-- Certify the shores one-respecting any tree in a fixed list. -/
theorem exists_tree_list_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {cost : ℕ}
    (M : ImplicitMeasures G toGraph cost) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (r : V) (trees : List (InArb r)) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 5 * cost * Fintype.card V * Nat.clog 2 (Fintype.card V) * trees.length ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        r ∉ S → (∃ T ∈ trees, leavingCount T S = 1) → lam ≤ (toGraph G').out S := by
  classical
  choose Q hQ hcert using fun T : InArb r =>
    exists_connected_tree_certificate M hlam hcut (inArbTree T) r
  refine ⟨trees.toFinset.biUnion Q, ?_, fun G' hG' S hr ⟨T, hT, hone⟩ => ?_⟩
  · exact (card_biUnion_le_mul _ _ _ (fun T _ => hQ T)).trans
      (Nat.mul_le_mul_left _ trees.toFinset_card_le)
  · exact hcert T G' (consistent_biUnion.mp hG' T (List.mem_toFinset.mpr hT)) S
      (parentConnected_of_oneRespecting T hr hone) hr

/-- The full tree-cover/centroid query construction for a prepared residual.
The preparation premises are structural equalities and entry caps; the
threshold-preparation theorem produces them from its separate query family. -/
theorem exists_prepared_small_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {cost : ℕ}
    (M : ImplicitMeasures G toGraph cost) (K L : WeightedDiGraph V)
    (hsplit : ∀ u v, (toGraph G).c u v = K.c u v + L.c u v)
    {lam : ℝ} (hlam : 0 < lam)
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (r : V) {k : ℕ} (hk : 1 ≤ k) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 5 * cost * Fintype.card V * Nat.clog 2 (Fintype.card V) *
        (k * Nat.clog 2 (Fintype.card V) + 1) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ L' : WeightedDiGraph V,
        (∀ u v, (toGraph G').c u v = K.c u v + L'.c u v) →
        (∀ v, L'.outdeg v = L.outdeg v) →
        (∀ u v, L'.c u v ≤ lam / (8 * (k : ℝ) ^ 2)) →
        ∀ S : Finset V, S.Nonempty → r ∉ S → S.card ≤ k → lam ≤ (toGraph G').out S := by
  obtain ⟨trees, hlength, hcover⟩ := exists_uniform_violation_tree_cover
    (toGraph G) K L hsplit r hlam hcut hk
  obtain ⟨Q, hQ, hcert⟩ := exists_tree_list_certificate M hlam.le hcut r trees
  refine ⟨Q, hQ.trans (Nat.mul_le_mul_left _ hlength), ?_⟩
  intro G' hG' L' hsplit' hdeg hcap S hS hr hsize
  by_contra hviol
  exact hviol (hcert G' hG' S hr
    (hcover (toGraph G') L' hsplit' hdeg hcap S hS hr hsize (lt_of_not_ge hviol)))

/-- **Small shores in the actual pruned graph.** Heavy/light preparation,
both fixed tree covers, centroid certificates and extra roots are all
constructed from the input, before quantifying over unrestricted competitors. -/
theorem exists_pruned_smallShore_certificate {G : WeightedDiGraph V} (C : PruningCert G)
    (r : V) {k : ℕ} (hk : 1 ≤ k) (hkn : k < Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q : Finset (Finset V),
      (Q.card : ℝ) ≤ 9 * Fintype.card V +
        12 * total C.H.c / (G.minValue / (8 * (k : ℝ) ^ 2)) +
        30 * Fintype.card V * (Nat.clog 2 (Fintype.card V) : ℝ) *
          (k * (Nat.clog 2 (Fintype.card V) : ℝ) + 1) +
        60 * Fintype.card V * (k + 1 : ℝ) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        ProperShore S → (S.card ≤ k ∨ Sᶜ.card ≤ k) → G.minValue ≤ (C.toGraph G').out S := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hB : 0 < G.minValue / (8 * (k : ℝ) ^ 2) := by positivity
  obtain ⟨K, L, toResidual, Qp, hQp, hsplit, hprep⟩ := exists_threshold_preparation C hB
  have hcut : ∀ S, ProperShore S → G.minValue ≤ (C.toGraph G).out S := by
    rw [C.toGraph_self_eq]
    exact C.lam_le_out
  have hsplit0 : ∀ u v, (C.toGraph G).c u v = K.c u v + L.c u v := by
    intro u v
    rw [C.toGraph_self]
    exact hsplit u v
  obtain ⟨Qf, hQf, hforward⟩ := exists_prepared_small_certificate
    C.measures K L hsplit0 hlam hcut r hk
  have hrevcut : ∀ S, ProperShore S → G.minValue ≤ (C.toGraph G).rev.out S := by
    intro S hS
    rw [WeightedDiGraph.rev_out]
    exact hcut Sᶜ (properShore_compl hS)
  obtain ⟨Qr, hQr, hreverse⟩ := exists_prepared_small_certificate
    (reverseMeasures C.measures) K.rev L.rev (fun u v => hsplit0 v u) hlam hrevcut r hk
  obtain ⟨Qt, hQt, hterminal⟩ := exists_root_small_both_certificate C.measures hcut r hkn
  refine ⟨((Qp ∪ Qf) ∪ Qr) ∪ Qt, ?_, fun G' hG' S hS hsmall => ?_⟩
  · have hc : ((((Qp ∪ Qf) ∪ Qr) ∪ Qt).card : ℝ) ≤
        Qp.card + Qf.card + Qr.card + Qt.card := by
      exact_mod_cast ((card_union_le ((Qp ∪ Qf) ∪ Qr) Qt).trans
        (Nat.add_le_add_right ((card_union_le (Qp ∪ Qf) Qr).trans
          (Nat.add_le_add_right (card_union_le Qp Qf) Qr.card)) Qt.card))
    have hf : (Qf.card : ℝ) ≤
        15 * Fintype.card V * (Nat.clog 2 (Fintype.card V) : ℝ) *
          (k * (Nat.clog 2 (Fintype.card V) : ℝ) + 1) := by exact_mod_cast hQf
    have hr : (Qr.card : ℝ) ≤
        15 * Fintype.card V * (Nat.clog 2 (Fintype.card V) : ℝ) *
          (k * (Nat.clog 2 (Fintype.card V) : ℝ) + 1) := by exact_mod_cast hQr
    have ht : (Qt.card : ℝ) ≤ 60 * Fintype.card V * (k + 1 : ℝ) := by exact_mod_cast hQt
    linarith
  · obtain ⟨hsplit', hout, hin, hcap⟩ := hprep G'
      (hG'.mono ((subset_union_left.trans subset_union_left).trans subset_union_left))
    have hf := hforward G'
      (hG'.mono ((subset_union_right.trans subset_union_left).trans subset_union_left))
      (toResidual G') hsplit' hout hcap
    have hr := hreverse G' (hG'.mono (subset_union_right.trans subset_union_left))
      (toResidual G').rev (fun u v => hsplit' v u) hin (fun u v => hcap v u)
    have ht := hterminal G' (hG'.mono subset_union_right)
    rcases hsmall with hs | hs
    · by_cases hrS : r ∈ S
      · exact ht S (Or.inl ⟨hrS, hs⟩)
      · exact hf S hS.1 hrS hs
    · by_cases hrS : r ∈ S
      · have h := hr Sᶜ (properShore_compl hS).1 (by simpa using hrS) hs
        simpa only [WeightedDiGraph.rev_out, compl_compl] using h
      · exact ht S (Or.inr ⟨hrS, hs⟩)

/-- **Small-shore cut certificate for the original graph.** All preprocessing
and domination queries are included, with an explicit polynomial/log budget. -/
theorem exists_smallShore_certificate (G : WeightedDiGraph V) (r : V)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 400 * Fintype.card V * k ^ 2 +
        60 * Fintype.card V * k * logL (Fintype.card V) ^ 2 ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        ProperShore S → (S.card ≤ k ∨ Sᶜ.card ≤ k) → G.minValue ≤ G'.out S := by
  classical
  by_cases hlam : 0 < G.minValue
  · let : Nonempty V := ⟨r⟩
    obtain ⟨C⟩ := exists_pruningCert G
    obtain ⟨Q, hQ, hcert⟩ := exists_pruned_smallShore_certificate C r hk hkn hlam
    refine ⟨C.queries ∪ Q, ?_, fun G' hG' S hS hsize => ?_⟩
    · have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hB : 0 < G.minValue / (8 * (k : ℝ) ^ 2) := by positivity
      have htotal : total C.H.c ≤ 2 * (Fintype.card V : ℝ) * G.minValue := by
        have h := C.total_le
        nlinarith
      have hmass : 12 * total C.H.c / (G.minValue / (8 * (k : ℝ) ^ 2)) ≤
          192 * (Fintype.card V : ℝ) * (k : ℝ) ^ 2 := by
        calc 12 * total C.H.c / (G.minValue / (8 * (k : ℝ) ^ 2))
            ≤ 12 * (2 * Fintype.card V * G.minValue) /
              (G.minValue / (8 * (k : ℝ) ^ 2)) :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htotal (by norm_num)) hB.le
          _ = 192 * (Fintype.card V : ℝ) * (k : ℝ) ^ 2 := by
            field_simp [ne_of_gt hlam, ne_of_gt hkR]
            <;> ring
      have hu : ((C.queries ∪ Q).card : ℝ) ≤ C.queries.card + Q.card := by
        exact_mod_cast card_union_le C.queries Q
      have hc : (C.queries.card : ℝ) ≤ 30 * Fintype.card V := by exact_mod_cast C.card_queries
      have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
      have hsmall := small_certificate_arithmetic (Fintype.card V) k hn hk
      have hbound : ((C.queries ∪ Q).card : ℝ) ≤
          400 * Fintype.card V * (k : ℝ) ^ 2 +
            60 * Fintype.card V * k * (logL (Fintype.card V) : ℝ) ^ 2 := by
        linarith
      exact_mod_cast hbound
    · exact (hcert G' (hG'.mono subset_union_right) S hS hsize).trans
        (C.out_le G' (hG'.mono subset_union_left) S)
  · refine ⟨∅, by simp, fun G' _ S _ _ => ?_⟩
    exact (le_of_not_gt hlam).trans (G'.out_nonneg S)

/-- **Complete parameterized weighted certificate.** The only graph and
parameter assumptions are those of the source theorem. Every auxiliary
packing, source set, flow, residual and tree cover is constructed. -/
theorem exists_uniform_certificate (G : WeightedDiGraph V) (r : V)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    ∃ Q S, Q.card ≤ budget 512 (Fintype.card V) k ∧ IsMinCutWitnessCertificate G Q S := by
  classical
  obtain ⟨Qs, hQs, hsmall⟩ := exists_smallShore_certificate G r hk hkn
  obtain ⟨Ql, hQl, hlarge⟩ := exists_largeShore_certificate G r hk hkn.le
  have hn : 2 ≤ Fintype.card V := by omega
  obtain ⟨S, hS⟩ := exists_isGlobalMinCut G hn
  refine ⟨insert S (Qs ∪ Ql), S, ?_, mem_insert_self _ _, fun G' hG' => ?_⟩
  · have hlargeBound : Ql.card ≤ 120 * Fintype.card V * (ceilDiv (Fintype.card V) k + 1) := by
      calc Ql.card ≤ 30 * Fintype.card V *
          (4 * (FractionalForest.ceilA (Fintype.card V) k - 1) + 3) := hQl
        _ ≤ 30 * Fintype.card V * (4 * (ceilDiv (Fintype.card V) k + 1)) := by
          apply Nat.mul_le_mul_left (30 * Fintype.card V)
          change 4 * (ceilDiv (Fintype.card V) k - 1) + 3 ≤
            4 * (ceilDiv (Fintype.card V) k + 1)
          have hsub := Nat.sub_le (ceilDiv (Fintype.card V) k) 1
          omega
        _ = 120 * Fintype.card V * (ceilDiv (Fintype.card V) k + 1) := by ring
    have hcard := (card_insert_le S (Qs ∪ Ql)).trans
      (Nat.add_le_add_right (card_union_le Qs Ql) 1)
    have hpositive : 1 ≤ Fintype.card V * k ^ 2 := by
      have hnpos : 0 < Fintype.card V := by omega
      have hkpos : 0 < k := by omega
      exact Nat.mul_pos hnpos (pow_pos hkpos _)
    unfold budget
    nlinarith [Nat.zero_le (Fintype.card V * k * logL (Fintype.card V) ^ 2),
      Nat.zero_le (Fintype.card V * (ceilDiv (Fintype.card V) k + 1))]
  · refine ⟨hS.1, fun T hT => ?_⟩
    rw [hG' S (mem_insert_self _ _), hS.out_eq_minValue]
    have hbase : Consistent G G' (Qs ∪ Ql) := hG'.mono (subset_insert S _)
    by_cases hs : T.card ≤ k ∨ Tᶜ.card ≤ k
    · exact hsmall G' (hbase.mono subset_union_left) T hT hs
    · push Not at hs
      exact hlarge G' (hbase.mono subset_union_right) T (by omega) (by omega)

/-- The repository's explicit W7 target, with universal natural constant 512. -/
theorem uniform_certificate_target : UniformCertificateTarget := by
  refine ⟨512, fun n G k hn hk hkn => ?_⟩
  let r : Fin n := ⟨0, by omega⟩
  obtain ⟨Q, S, hQ, hcert⟩ := exists_uniform_certificate G r hk (by simpa using hkn)
  exact ⟨Q, S, by simpa using hQ, hcert⟩

/-- The weighted global `O(n^(5/3))` endpoint, using the proved integer
parameter selection and logarithm-versus-power estimate. -/
theorem headline_certificate_target : HeadlineCertificateTarget := by
  refine ⟨512 * (5 + (6 / Real.log 2 + 1) ^ 2 * (2 : ℝ) ^ ((1 : ℝ) / 3)), ?_⟩
  intro n G hn
  obtain ⟨k, hk, hkn, hbudget⟩ := exists_optimized_budget 512 n hn
  let r : Fin n := ⟨0, by omega⟩
  obtain ⟨Q, S, hQ, hcert⟩ := exists_uniform_certificate G r hk (by simpa using hkn)
  have hQR : (Q.card : ℝ) ≤ budget 512 n k := by
    exact_mod_cast (show Q.card ≤ budget 512 n k from by simpa using hQ)
  refine ⟨Q, S, hQR.trans ?_, hcert⟩
  simpa only [Nat.cast_ofNat] using hbudget

/-! ## Unit-input refinement using degrees and query-enforced caps

These constructions retain unrestricted nonnegative competitors. The input
unit condition is used only to bound actual oriented arcs and to count the
ordinary retained support; exceptional fractional arcs are already fixed.
-/

/-- The pair-total identity bounds every pruned arc by two on a unit input. -/
theorem unit_pruned_arc_le_two {G : WeightedDiGraph V} (C : PruningCert G)
    (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) (u v : V) : C.H.c u v ≤ 2 := by
  have hu : G.c u v ≤ 1 := by rcases hunit u v with h | h <;> rw [h] <;> norm_num
  have hv : G.c v u ≤ 1 := by rcases hunit v u with h | h <;> rw [h] <;> norm_num
  have hp := C.O.toOrientationData.toGraph_sym_w (Consistent.refl G C.O.queries) u v
  simp only [WeightedDiGraph.sym_w] at hp
  linarith [C.H_le u v, (C.O.toGraph G).nonneg v u]

/-- Only ordinary retained arcs are charged as unit-size items. Exceptional
arcs may be fractional and are not used in this count. -/
theorem unit_ret_card_le_total {G : WeightedDiGraph V} (C : PruningCert G)
    (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) :
    (C.ret.card : ℝ) ≤ total C.H.c := by
  have hret : ∀ u v, (u, v) ∈ C.ret → 1 ≤ C.H.c u v := by
    intro u v huv
    rw [C.ret_H u v huv]
    have hz : G.sym.w u v ≠ 0 := by
      intro h
      have hs := C.O.sgn_zero u v h
      rw [C.ret_sgn u v huv] at hs
      norm_num at hs
    rcases hunit u v with hu | hu <;> rcases hunit v u with hv | hv
    · exact (hz (by simp [WeightedDiGraph.sym_w, hu, hv])).elim
    · norm_num [WeightedDiGraph.sym_w, hu, hv]
    · norm_num [WeightedDiGraph.sym_w, hu, hv]
    · norm_num [WeightedDiGraph.sym_w, hu, hv]
  calc (C.ret.card : ℝ) = ∑ _p ∈ C.ret, (1 : ℝ) := by simp
    _ ≤ ∑ p ∈ C.ret, C.H.c p.1 p.2 := sum_le_sum fun p hp => hret _ _ hp
    _ ≤ ∑ p : V × V, C.H.c p.1 p.2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ => C.H.nonneg _ _)
    _ = total C.H.c := by simp only [total, Fintype.sum_prod_type]

/-- Learning the ordinary retained support gives an exact witness certificate.
The implicit competitor graph is then completely fixed, including exceptional
arcs, and all domination queries are included. -/
theorem exists_unit_mass_certificate {G : WeightedDiGraph V} (C : PruningCert G)
    (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, (Q.card : ℝ) ≤ 30 * Fintype.card V +
        6 * Fintype.card V * G.minValue + 1 ∧ IsMinCutWitnessCertificate G Q S := by
  classical
  obtain ⟨S, hS⟩ := exists_isGlobalMinCut G hn
  have hlam : 0 ≤ G.minValue := (G.out_nonneg S).trans_eq hS.out_eq_minValue
  obtain ⟨Q, hQ, hfix⟩ := exists_fixed_arc_certificate C C.ret
  refine ⟨insert S (C.queries ∪ Q), S, ?_, mem_insert_self _ _, fun G' hG' => ?_⟩
  · have hc : ((insert S (C.queries ∪ Q)).card : ℝ) ≤
        C.queries.card + Q.card + 1 := by
      exact_mod_cast ((card_insert_le S _).trans
        (Nat.add_le_add_right (card_union_le C.queries Q) 1))
    have hq : (Q.card : ℝ) ≤ 3 * (C.ret.card : ℝ) := by exact_mod_cast hQ
    have hbase : (C.queries.card : ℝ) ≤ 30 * Fintype.card V := by exact_mod_cast C.card_queries
    have hret := unit_ret_card_le_total C hunit
    have htotal := C.total_le
    nlinarith
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

/-- A cap of `λ/k`, together with both fixed degree vectors, certifies all
small sides. The cap is forced by MassCap's original cut queries, including
on every originally zero ordered pair in the bin domain. -/
theorem exists_degree_cap_small_certificate {G : WeightedDiGraph V} (C : PruningCert G)
    {k : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue)
    (hcap : ∀ u v, C.H.c u v ≤ (G.minValue / k) / 2) :
    ∃ Q : Finset (Finset V),
      (Q.card : ℝ) ≤ 39 * Fintype.card V + 12 * Fintype.card V * k ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        ProperShore S → (S.card ≤ k ∨ Sᶜ.card ≤ k) → G.minValue ≤ G'.out S := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hB : 0 < G.minValue / k := div_pos hlam hkR
  obtain ⟨Qc, hQc, hcapacities⟩ := exists_pruning_capacity_cap C hB hcap
  obtain ⟨Qd, hQd, hdegrees⟩ := exists_masked_degree_certificate C univ
  refine ⟨(C.queries ∪ Qc) ∪ Qd, ?_, fun G' hG' S hS hsize => ?_⟩
  · have hc : (((C.queries ∪ Qc) ∪ Qd).card : ℝ) ≤
        C.queries.card + Qc.card + Qd.card := by
      exact_mod_cast ((card_union_le (C.queries ∪ Qc) Qd).trans
        (Nat.add_le_add_right (card_union_le C.queries Qc) Qd.card))
    have hbase : (C.queries.card : ℝ) ≤ 30 * Fintype.card V := by exact_mod_cast C.card_queries
    have hd : (Qd.card : ℝ) ≤ 6 * Fintype.card V := by exact_mod_cast hQd
    have htotal : total C.H.c ≤ 2 * Fintype.card V * G.minValue := by
      have h := C.total_le
      nlinarith
    have hm : 6 * total C.H.c / (G.minValue / k) ≤ 12 * Fintype.card V * k := by
      calc 6 * total C.H.c / (G.minValue / k)
          ≤ 6 * (2 * Fintype.card V * G.minValue) / (G.minValue / k) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htotal (by norm_num)) hB.le
        _ = 12 * Fintype.card V * k := by field_simp [ne_of_gt hlam, ne_of_gt hkR] <;> ring
    linarith
  · have hC := hG'.mono (subset_union_left.trans subset_union_left)
    have hcap' := hcapacities G' (hG'.mono (subset_union_right.trans subset_union_left))
    have hd := hdegrees G' (hG'.mono subset_union_right)
    have hout : ∀ v, G.minValue ≤ (C.toGraph G').outdeg v := by
      intro v
      have heq : (C.toGraph G').outdeg v = C.H.outdeg v := by
        simpa [maskGraph, WeightedDiGraph.outdeg] using (hd v).1
      rw [heq, ← WeightedDiGraph.out_singleton]
      exact C.lam_le_out _ (properShore_singleton v hn)
    have hin : ∀ v, G.minValue ≤ (C.toGraph G').rev.outdeg v := by
      intro v
      have heq : (C.toGraph G').indeg v = C.H.indeg v := by
        simpa [maskGraph, WeightedDiGraph.indeg] using (hd v).2
      change G.minValue ≤ (C.toGraph G').indeg v
      rw [heq, ← WeightedDiGraph.out_compl_singleton]
      exact C.lam_le_out _ (properShore_compl (properShore_singleton v hn))
    have hbound : ∀ T : Finset V, T.card ≤ k → G.minValue / k * T.card ≤ G.minValue := by
      intro T hT
      have ht : (T.card : ℝ) ≤ k := by exact_mod_cast hT
      calc G.minValue / k * T.card ≤ G.minValue / k * k := mul_le_mul_of_nonneg_left ht hB.le
        _ = G.minValue := by field_simp [ne_of_gt hkR]
    apply le_trans _ (C.out_le G' hC S)
    rcases hsize with hs | hs
    · exact degree_cap_cut_lower_bound (C.toGraph G') hout hcap' hS.1 (hbound S hs)
    · have h := degree_cap_cut_lower_bound (C.toGraph G').rev hin
        (fun u v => hcap' v u) (properShore_compl hS).1 (hbound Sᶜ hs)
      simpa only [WeightedDiGraph.rev_out, compl_compl] using h

/-- **Unit-input global certificate with unrestricted competitors.** The
low-value branch fixes only ordinary retained arcs. The high-value branch
combines query-enforced caps and degrees with the two shared source flows.
The resulting `O(n^(3/2))` estimate is a refinement of the logarithmic unit
bound; it places no capacity promise on a consistent competitor. -/
theorem exists_unit_global_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) :
    ∃ Q S, (Q.card : ℝ) ≤ 600 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) ∧
      IsMinCutWitnessCertificate G Q S := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let r : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨C⟩ := exists_pruningCert G
  have hn1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast (by omega : 1 ≤ Fintype.card V)
  have hn0 : (0 : ℝ) < Fintype.card V := by linarith
  let a : ℝ := (Fintype.card V : ℝ) ^ ((1 : ℝ) / 2)
  have ha1 : 1 ≤ a := Real.one_le_rpow hn1 (by norm_num)
  have hpower : (Fintype.card V : ℝ) * a =
      (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) := by
    dsimp [a]
    calc (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 2)
        = (Fintype.card V : ℝ) ^ (1 : ℝ) *
          (Fintype.card V : ℝ) ^ ((1 : ℝ) / 2) := by rw [Real.rpow_one]
      _ = (Fintype.card V : ℝ) ^ ((1 : ℝ) + (1 : ℝ) / 2) :=
        (Real.rpow_add hn0 _ _).symm
      _ = (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) := by norm_num
  by_cases hsmall : G.minValue < 4 * a
  · obtain ⟨Q, S, hQ, hcert⟩ := exists_unit_mass_certificate C hunit hn
    refine ⟨Q, S, hQ.trans ?_, hcert⟩
    have hm := mul_le_mul_of_nonneg_left hsmall.le
      (show (0 : ℝ) ≤ 6 * Fintype.card V by positivity)
    have hna := mul_le_mul_of_nonneg_left ha1 hn0.le
    rw [← hpower]
    nlinarith
  · have hlarge : 4 * a ≤ G.minValue := le_of_not_gt hsmall
    have hlam : 0 < G.minValue := by linarith
    obtain ⟨k, hk, hkn, hka, hbudget⟩ := exists_unit_parameter (Fintype.card V) hn
    change (k : ℝ) ≤ a at hka
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hcap : ∀ u v, C.H.c u v ≤ (G.minValue / k) / 2 := by
      intro u v
      apply (unit_pruned_arc_le_two C hunit u v).trans
      have hfour : (4 : ℝ) ≤ G.minValue / k := (le_div_iff₀ hkR).2 (by linarith)
      linarith
    obtain ⟨Qs, hQs, hsmallCert⟩ := exists_degree_cap_small_certificate C hk hn hlam hcap
    obtain ⟨Ql, hQl, hlargeCert⟩ := exists_largeShore_certificate G r hk hkn.le
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
      apply le_trans _ hbudget
      linarith
    · refine ⟨hS.1, fun T hT => ?_⟩
      rw [hG' S (mem_insert_self _ _), hS.out_eq_minValue]
      have hbase : Consistent G G' (Qs ∪ Ql) := hG'.mono (subset_insert S _)
      by_cases hs : T.card ≤ k ∨ Tᶜ.card ≤ k
      · exact hsmallCert G' (hbase.mono subset_union_left) T hT hs
      · push Not at hs
        exact hlargeCert G' (hbase.mono subset_union_right) T (by omega) (by omega)

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_comparison_tree_cover
#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_uniform_violation_tree_cover

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_connected_tree_certificate

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_prepared_small_certificate

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_pruned_smallShore_certificate

#print axioms CutQueryComplexity.DirectedCertificate.Completion.uniform_certificate_target

#print axioms CutQueryComplexity.DirectedCertificate.Completion.headline_certificate_target

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_unit_mass_certificate

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_degree_cap_small_certificate

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_unit_global_certificate
