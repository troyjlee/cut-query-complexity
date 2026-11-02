import CutQueryComplexity.DirectedCertificate.FlowMeasure
import CutQueryComplexity.DirectedCertificate.SourceSetMain

set_option autoImplicit false

/-! # Common-source certificates for all large shores

The large-shore part of Proposition 24 of paper P3
(`papers/P3/directed-cut-certificates.pdf`). The two shared flows are certified
separately. Terminal flows cover shores splitting the common source set.
All query sets consist of original outgoing shores and are chosen before the
unrestricted nonnegative competitor. No small-shore certificate is assumed in
`exists_largeShore_certificate`.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset WeightedDiGraph Certificate FractionalForest

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem properShore_compl {S : Finset V} (hS : ProperShore S) : ProperShore Sᶜ := by
  refine ⟨?_, ?_⟩
  · apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact hS.2 (by simpa using congrArg compl h)
  · intro h
    have : S = ∅ := by simpa using congrArg compl h
    exact hS.1.ne_empty this

/-- The divergence of an `s`--`t` flow over an `s`--`t` shore is its value. -/
theorem sum_netOut_st {H : WeightedDiGraph V} {f : V → V → ℝ} {s t : V}
    (hf : H.STFlow s t f) {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    ∑ v ∈ S, netOut f v = netOut f s := by
  rw [← sum_erase_add _ _ hs]
  have hz : ∑ v ∈ S.erase s, netOut f v = 0 :=
    sum_eq_zero fun v hv => hf.2 v (ne_of_mem_erase hv)
      (fun h => ht (h ▸ mem_of_mem_erase hv))
  rw [hz, zero_add]

/-- A genuine terminal-flow certificate compiled to original outgoing-cut queries. -/
theorem exists_terminal_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {c : ℕ}
    (M : ImplicitMeasures G toGraph c) {lam : ℝ}
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (s t : V) (hst : s ≠ t) :
    ∃ Q : Finset (Finset V), Q.card ≤ 5 * c * Fintype.card V ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        ∀ S : Finset V, s ∈ S → t ∉ S → lam ≤ (toGraph G').out S := by
  obtain ⟨f, A, hf, hsA, htA, hval⟩ := (toGraph G).exists_maxFlow_minCut hst
  have hlam : lam ≤ netOut f s := by
    rw [hval]
    exact hcut A (properShore_of_not_mem ⟨s, hsA⟩ htA)
  obtain ⟨Q, hQ, hcert⟩ := exists_implicitFlowCert M hf.1
  refine ⟨Q, hQ, fun G' hG' S hs ht => ?_⟩
  have h := hcert G' hG' S
  rw [sum_netOut_st hf hs ht] at h
  exact hlam.trans h

/-- Terminal flows between one fixed vertex and `R` certify every cut splitting `R`.
Each terminal flow has its own capacity budget; their sum need not be feasible. -/
theorem exists_root_split_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {c : ℕ}
    (M : ImplicitMeasures G toGraph c) {lam : ℝ}
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S) (r : V) (R : Finset V) :
    ∃ Q : Finset (Finset V), Q.card ≤ 10 * c * Fintype.card V * R.card ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        (∃ u ∈ R, u ∈ S) → (∃ v ∈ R, v ∉ S) → lam ≤ (toGraph G').out S := by
  classical
  have hpair : ∀ v : V, ∃ Q : Finset (Finset V),
      Q.card ≤ 10 * c * Fintype.card V ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        (r ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ r ∉ S) → lam ≤ (toGraph G').out S := by
    intro v
    by_cases hvr : v = r
    · refine ⟨∅, by simp, fun _ _ _ h => ?_⟩
      subst v
      rcases h with h | h <;> exact (h.2 h.1).elim
    · obtain ⟨Q₁, hQ₁, h₁⟩ := exists_terminal_certificate M hcut r v (Ne.symm hvr)
      obtain ⟨Q₂, hQ₂, h₂⟩ := exists_terminal_certificate M hcut v r hvr
      refine ⟨Q₁ ∪ Q₂, ?_, fun G' hG' S h => ?_⟩
      · calc (Q₁ ∪ Q₂).card ≤ Q₁.card + Q₂.card := card_union_le Q₁ Q₂
          _ ≤ 5 * c * Fintype.card V + 5 * c * Fintype.card V := Nat.add_le_add hQ₁ hQ₂
          _ = 10 * c * Fintype.card V := by ring
      · rcases h with ⟨hr, hv⟩ | ⟨hv, hr⟩
        · exact h₁ G' (hG'.mono subset_union_left) S hr hv
        · exact h₂ G' (hG'.mono subset_union_right) S hv hr
  choose Q hQ hcert using hpair
  refine ⟨R.biUnion Q, card_biUnion_le_mul R Q _ (fun v _ => hQ v),
    fun G' hG' S hin hout => ?_⟩
  by_cases hr : r ∈ S
  · obtain ⟨v, hvR, hvS⟩ := hout
    exact hcert v G' (consistent_biUnion.mp hG' v hvR) S (Or.inl ⟨hr, hvS⟩)
  · obtain ⟨u, huR, huS⟩ := hin
    exact hcert u G' (consistent_biUnion.mp hG' u huR) S (Or.inr ⟨huS, hr⟩)

omit [DecidableEq V] in
/-- The shared supply flow gives the exact cardinality lower bound off the roots. -/
theorem sum_netOut_supply {f : V → V → ℝ} {R S : Finset V} {b : ℝ}
    (hf : ∀ v, v ∉ R → netOut f v = b) (hSR : Disjoint S R) :
    ∑ v ∈ S, netOut f v = b * S.card := by
  rw [sum_congr rfl (fun v hv => hf v (fun h => disjoint_left.mp hSR hv h))]
  simp [mul_comm]

/-- The other shared flow gives the complementary lower bound on shores containing roots. -/
theorem sum_netOut_demand {H : WeightedDiGraph V} {f : V → V → ℝ}
    (hf : H.Feasible f) {R S : Finset V} {b : ℝ}
    (hnet : ∀ v, v ∉ R → netOut f v = -b) (hRS : R ⊆ S) :
    ∑ v ∈ S, netOut f v = b * Sᶜ.card := by
  have hd : Disjoint Sᶜ R := disjoint_left.mpr fun v hv hvR =>
    (mem_compl.mp hv) (hRS hvR)
  have hc := sum_netOut_supply hnet hd
  have hz := WeightedDiGraph.sum_univ_netOut hf.1
  rw [← sum_add_sum_compl S] at hz
  linarith

omit [Fintype V] [DecidableEq V] in
theorem le_div_mul_card {lam : ℝ} (hlam : 0 ≤ lam) {k : ℕ} (hk : 1 ≤ k)
    {S : Finset V} (hS : k ≤ S.card) : lam ≤ lam / k * S.card := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  calc lam = lam / k * (k : ℝ) := (div_mul_cancel₀ _ hk0).symm
    _ ≤ lam / k * S.card :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hS) (div_nonneg hlam (Nat.cast_nonneg k))

/-- Compose both shared flows and all root-terminal flows. The result covers all
shores whose two sides have at least `k` vertices, with no W6 premise. -/
theorem exists_source_route_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {c : ℕ}
    (M : ImplicitMeasures G toGraph c) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (r : V) (R : Finset V) {k : ℕ} (hk : 1 ≤ k)
    {f g : V → V → ℝ} (hf : (toGraph G).Feasible f)
    (hfv : ∀ v, v ∉ R → netOut f v = lam / k)
    (hg : (toGraph G).Feasible g) (hgv : ∀ v, v ∉ R → netOut g v = -(lam / k)) :
    ∃ Q : Finset (Finset V), Q.card ≤ 10 * c * Fintype.card V * (R.card + 1) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        k ≤ S.card → k ≤ Sᶜ.card → lam ≤ (toGraph G').out S := by
  classical
  obtain ⟨Qf, hQf, hcf⟩ := exists_implicitFlowCert M hf
  obtain ⟨Qg, hQg, hcg⟩ := exists_implicitFlowCert M hg
  obtain ⟨Qt, hQt, hct⟩ := exists_root_split_certificate M hcut r R
  refine ⟨Qf ∪ Qg ∪ Qt, ?_, fun G' hG' S hS hcS => ?_⟩
  · have hu₁ := card_union_le Qf Qg
    have hu₂ := card_union_le (Qf ∪ Qg) Qt
    calc (Qf ∪ Qg ∪ Qt).card ≤ 5 * c * Fintype.card V +
        5 * c * Fintype.card V + 10 * c * Fintype.card V * R.card := by omega
      _ = 10 * c * Fintype.card V * (R.card + 1) := by ring
  have hGf := (consistent_union.mp (consistent_union.mp hG').1).1
  have hGg := (consistent_union.mp (consistent_union.mp hG').1).2
  have hGt := (consistent_union.mp hG').2
  by_cases hdis : Disjoint S R
  · have h := hcf G' hGf S
    rw [sum_netOut_supply hfv hdis] at h
    exact (le_div_mul_card hlam hk hS).trans h
  · by_cases hRS : R ⊆ S
    · have h := hcg G' hGg S
      rw [sum_netOut_demand hg hgv hRS] at h
      exact (le_div_mul_card hlam hk hcS).trans h
    · apply hct G' hGt S
      · by_contra hn
        apply hdis
        exact disjoint_left.mpr fun v hv hvR => hn ⟨v, hvR, hv⟩
      · exact Finset.not_subset.mp hRS

/-- Select the two packings, common source set, shared flows and terminal flows
from the input. Its one query family works for every consistent competitor. -/
theorem exists_largeShore_implicit_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {c : ℕ}
    (M : ImplicitMeasures G toGraph c) {lam : ℝ} (hlam : 0 < lam)
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (r : V) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 10 * c * Fintype.card V * (4 * (ceilA (Fintype.card V) k - 1) + 2) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        k ≤ S.card → k ≤ Sᶜ.card → lam ≤ (toGraph G').out S := by
  obtain ⟨a, ha, hasum, haload⟩ := exists_inArb_packing (toGraph G) r lam hlam.le
    (fun S hS hr => hcut S (properShore_of_not_mem hS hr))
  obtain ⟨b, hb, hbsum, hbload⟩ := exists_outArb_packing (toGraph G) r lam hlam.le
    (fun S hS hr => hcut Sᶜ (properShore_compl (properShore_of_not_mem hS hr)))
  obtain ⟨R, -, hR, ⟨f, hf, hfv, -⟩, ⟨g, hg, hgv, -⟩⟩ :=
    small_source_set_flows_main (toGraph G) r hlam a b ha hasum haload hb hbsum hbload hk hkn
  obtain ⟨Q, hQ, hcert⟩ := exists_source_route_certificate M hlam.le hcut r R hk hf hfv hg hgv
  refine ⟨Q, hQ.trans ?_, hcert⟩
  exact Nat.mul_le_mul_left _ (by omega)

/-- **All large shores, against unrestricted nonnegative competitors.**
Pruning and all flow certificates are constructed; every measurement is an
original outgoing-cut query. Only the small-shore part of W6 remains separate. -/
theorem exists_largeShore_certificate (G : WeightedDiGraph V) (r : V)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 30 * Fintype.card V * (4 * (ceilA (Fintype.card V) k - 1) + 3) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        k ≤ S.card → k ≤ Sᶜ.card → G.minValue ≤ G'.out S := by
  classical
  by_cases hlam : 0 < G.minValue
  · let : Nonempty V := ⟨r⟩
    obtain ⟨C⟩ := exists_pruningCert G
    have hcut : ∀ S, ProperShore S → G.minValue ≤ (C.toGraph G).out S := by
      rw [C.toGraph_self_eq]
      exact C.lam_le_out
    obtain ⟨Q, hQ, hcert⟩ := exists_largeShore_implicit_certificate C.measures hlam hcut r hk hkn
    refine ⟨C.queries ∪ Q, ?_, fun G' hG' S hS hcS => ?_⟩
    · have hu := card_union_le C.queries Q
      have hC := C.card_queries
      calc (C.queries ∪ Q).card ≤ 30 * Fintype.card V +
          10 * 3 * Fintype.card V * (4 * (ceilA (Fintype.card V) k - 1) + 2) := by omega
        _ = 30 * Fintype.card V * (4 * (ceilA (Fintype.card V) k - 1) + 3) := by ring
    · exact (hcert G' (hG'.mono subset_union_right) S hS hcS).trans
        (C.out_le G' (hG'.mono subset_union_left) S)
  · refine ⟨∅, by simp, fun G' _ S _ _ => ?_⟩
    exact (le_of_not_gt hlam).trans (G'.out_nonneg S)

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_largeShore_certificate
