import CutQueryComplexity.DirectedCertificate.Completion.SourceRoute

set_option autoImplicit false

/-! # Local source certificates for the centroid reduction

The flow step of `lem:connected-tree` can be proved directly on the original
vertex type. Send flow from the chosen centroid to the complement of its
component, and transfer divergence only inside that component. This certifies
all shores contained in the component and containing the centroid, for
`5 c |W|` original outgoing-cut queries. No arbitrary cut oracle of the
implicit graph, auxiliary-vertex compiler, or simultaneous flow packing is
assumed.
-/

namespace CutQueryComplexity.DirectedCertificate.Completion

open Finset WeightedDiGraph Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Localize the directed flow certificate to shores inside `W`. The transfer
need only fix divergence and imbalance at vertices of `W`. -/
theorem exists_local_flow_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {c : ℕ}
    (M : ImplicitMeasures G toGraph c) (W : Finset V) {f : V → V → ℝ}
    (hf : (toGraph G).Feasible f) :
    ∃ Q : Finset (Finset V), Q.card ≤ 5 * c * W.card ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        ∀ S : Finset V, S ⊆ W → ∑ v ∈ S, netOut f v ≤ (toGraph G').out S := by
  obtain ⟨Q, hQ, htransfer⟩ := exists_implicitFlowTransfer M W hf
  refine ⟨Q, hQ, fun G' hG' S hSW => ?_⟩
  obtain ⟨⟨z', hz', hnet, -⟩, himb⟩ := htransfer G' hG'
  have hc := Certificate.sum_netOut_le_cut hz' Sᶜ
  rw [WeightedGraph.cut_compl] at hc
  have hzero := WeightedDiGraph.sum_univ_netOut hz'.1
  rw [← sum_add_sum_compl S] at hzero
  have hcut := (toGraph G').two_mul_out S
  rw [sum_congr rfl (fun v hv => himb v (hSW hv))] at hcut
  have hdiv : ∑ v ∈ S, netOut z' v =
      ∑ v ∈ S, (toGraph G).imbalance v - 2 * ∑ v ∈ S, netOut f v := by
    rw [sum_congr rfl (fun v hv => hnet v (hSW hv)), sum_sub_distrib, mul_sum]
  linarith

/-- A centroid-to-boundary flow of value `λ`. All vertices inside `W` other
than the centroid conserve flow, while vertices outside `W` absorb it. -/
theorem exists_local_source_flow (H : WeightedDiGraph V) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcut : ∀ S, ProperShore S → lam ≤ H.out S) (W : Finset V)
    (c r : V) (hcW : c ∈ W) (hrW : r ∉ W) :
    ∃ f : V → V → ℝ, H.Feasible f ∧ netOut f c = lam ∧
      ∀ v ∈ W, v ≠ c → netOut f v = 0 := by
  have hdis : Disjoint ({c} : Finset V) Wᶜ := by
    simp [hcW]
  obtain ⟨f, A, ⟨hf, hcons, hsource, -⟩, hAW, hval⟩ :=
    H.exists_maxFlow_network {c} Wᶜ hdis (fun _ => lam) (fun _ => hlam)
  have hAsub : A ⊆ W := by
    intro v hv
    by_contra hn
    exact disjoint_left.mp hAW hv (mem_compl.mpr hn)
  have hcap : netOut f c ≤ lam := hsource c (mem_singleton_self c)
  have hlow : lam ≤ netOut f c := by
    rw [sum_singleton] at hval
    by_cases hcA : c ∈ A
    · have hproper : ProperShore A :=
        properShore_of_not_mem ⟨c, hcA⟩ (fun hr => hrW (hAsub hr))
      have hz : ({c} : Finset V) \ A = ∅ :=
        sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr hcA)
      rw [hz, sum_empty, add_zero] at hval
      exact hval.symm ▸ hcut A hproper
    · have heq : ({c} : Finset V) \ A = {c} := by
        ext v
        simp only [mem_sdiff, mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro rfl
          exact ⟨rfl, hcA⟩
      rw [heq, sum_singleton] at hval
      linarith [H.out_nonneg A]
  refine ⟨f, hf, le_antisymm hcap hlow, fun v hv hvc => ?_⟩
  exact hcons v (by simpa using hvc) (by simpa using hv)

/-- **One node of the centroid certificate.** A single query family certifies
every shore inside `W` and containing `c`, for every nonnegative competitor. -/
theorem exists_local_source_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {cost : ℕ}
    (M : ImplicitMeasures G toGraph cost) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (W : Finset V) (c r : V) (hcW : c ∈ W) (hrW : r ∉ W) :
    ∃ Q : Finset (Finset V), Q.card ≤ 5 * cost * W.card ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        ∀ S : Finset V, S ⊆ W → c ∈ S → lam ≤ (toGraph G').out S := by
  obtain ⟨f, hf, hval, hcons⟩ := exists_local_source_flow (toGraph G) hlam hcut W c r hcW hrW
  obtain ⟨Q, hQ, hcert⟩ := exists_local_flow_certificate M W hf
  refine ⟨Q, hQ, fun G' hG' S hSW hcS => ?_⟩
  have hsum : ∑ v ∈ S, netOut f v = lam := by
    rw [← sum_erase_add _ _ hcS]
    have hz : ∑ v ∈ S.erase c, netOut f v = 0 :=
      sum_eq_zero fun v hv => hcons v (hSW (mem_of_mem_erase hv)) (ne_of_mem_erase hv)
    rw [hz, zero_add, hval]
  rw [← hsum]
  exact hcert G' hG' S hSW

/-- Local certificates add according to component volume. This is the exact
interface consumed by a centroid decomposition: its combinatorial work is to
bound `∑ i ∈ nodes, (component i).card` and to locate a node covering a shore. -/
theorem exists_separator_family_certificate {ι : Type*} [DecidableEq ι]
    {G : WeightedDiGraph V} {toGraph : WeightedDiGraph V → WeightedDiGraph V} {cost : ℕ}
    (M : ImplicitMeasures G toGraph cost) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (nodes : Finset ι) (component : ι → Finset V) (pivot : ι → V) (r : V)
    (hpivot : ∀ i ∈ nodes, pivot i ∈ component i)
    (hroot : ∀ i ∈ nodes, r ∉ component i) :
    ∃ Q : Finset (Finset V), Q.card ≤ 5 * cost * ∑ i ∈ nodes, (component i).card ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        (∃ i ∈ nodes, S ⊆ component i ∧ pivot i ∈ S) → lam ≤ (toGraph G').out S := by
  classical
  have hex : ∀ i : ι, ∃ Q : Finset (Finset V),
      Q.card ≤ 5 * cost * (component i).card ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        i ∈ nodes → S ⊆ component i → pivot i ∈ S → lam ≤ (toGraph G').out S := by
    intro i
    by_cases hi : i ∈ nodes
    · obtain ⟨Q, hQ, hcert⟩ := exists_local_source_certificate M hlam hcut
        (component i) (pivot i) r (hpivot i hi) (hroot i hi)
      exact ⟨Q, hQ, fun G' hG' S _ => hcert G' hG' S⟩
    · exact ⟨∅, by simp, fun _ _ _ h => (hi h).elim⟩
  choose Q hQ hcert using hex
  refine ⟨nodes.biUnion Q, ?_, fun G' hG' S ⟨i, hi, hsub, hp⟩ => ?_⟩
  · calc (nodes.biUnion Q).card ≤ ∑ i ∈ nodes, (Q i).card := card_biUnion_le
      _ ≤ ∑ i ∈ nodes, 5 * cost * (component i).card := sum_le_sum fun i _ => hQ i
      _ = 5 * cost * ∑ i ∈ nodes, (component i).card := (mul_sum ..).symm
  · exact hcert i G' (consistent_biUnion.mp hG' i hi) S hi hsub hp

/-- Reversal preserves the symmetrized partial-star compiler and exchanges the
in-degree and out-degree compilers. No new original query is required. -/
def reverseMeasures {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {cost : ℕ}
    (M : ImplicitMeasures G toGraph cost) :
    ImplicitMeasures G (fun G' => (toGraph G').rev) cost where
  symStar v T := (M.symStar v T).congr fun G' => by
    simp only [WeightedDiGraph.symStar, WeightedDiGraph.rev_sym_w]
  symStar_cost v T := M.symStar_cost v T
  outdeg v := (M.indeg v).congr fun _ => rfl
  outdeg_cost v := M.indeg_cost v
  indeg v := (M.outdeg v).congr fun _ => rfl
  indeg_cost v := M.outdeg_cost v

/-- Choose `k` further roots and certify all small shores containing the
original root. The pigeonhole argument and all terminal certificates are
constructed here. -/
theorem exists_root_small_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {cost : ℕ}
    (M : ImplicitMeasures G toGraph cost) {lam : ℝ}
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (r : V) {k : ℕ} (hkn : k < Fintype.card V) :
    ∃ Q : Finset (Finset V), Q.card ≤ 10 * cost * Fintype.card V * (k + 1) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        r ∈ S → S.card ≤ k → lam ≤ (toGraph G').out S := by
  classical
  have hk : k ≤ (univ.erase r).card := by
    simp only [card_erase_of_mem (mem_univ r), card_univ]
    omega
  obtain ⟨T, hT, hcard⟩ := exists_subset_card_eq hk
  have hrT : r ∉ T := fun hr => (mem_erase.mp (hT hr)).1 rfl
  have hRcard : (insert r T).card = k + 1 := by rw [card_insert_of_notMem hrT, hcard]
  obtain ⟨Q, hQ, hcert⟩ := exists_root_split_certificate M hcut r (insert r T)
  refine ⟨Q, by simpa only [hRcard] using hQ, fun G' hG' S hrS hsize => ?_⟩
  apply hcert G' hG' S ⟨r, mem_insert_self r T, hrS⟩
  by_contra hn
  push_neg at hn
  have hc := card_le_card (show insert r T ⊆ S from hn)
  rw [hRcard] at hc
  omega

/-- Both root-containing small shores and shores with root-containing small
complement are covered by original cut queries. This handles the extra-root
and reversal steps surrounding the root-avoiding W6 tree cover. -/
theorem exists_root_small_both_certificate {G : WeightedDiGraph V}
    {toGraph : WeightedDiGraph V → WeightedDiGraph V} {cost : ℕ}
    (M : ImplicitMeasures G toGraph cost) {lam : ℝ}
    (hcut : ∀ S, ProperShore S → lam ≤ (toGraph G).out S)
    (r : V) {k : ℕ} (hkn : k < Fintype.card V) :
    ∃ Q : Finset (Finset V), Q.card ≤ 20 * cost * Fintype.card V * (k + 1) ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q → ∀ S : Finset V,
        (r ∈ S ∧ S.card ≤ k) ∨ (r ∉ S ∧ Sᶜ.card ≤ k) → lam ≤ (toGraph G').out S := by
  have hrev : ∀ S, ProperShore S → lam ≤ ((toGraph G).rev).out S := by
    intro S hS
    rw [WeightedDiGraph.rev_out]
    exact hcut Sᶜ (properShore_compl hS)
  obtain ⟨Q, hQ, hcert⟩ := exists_root_small_certificate M hcut r hkn
  obtain ⟨Qr, hQr, hcertr⟩ := exists_root_small_certificate (reverseMeasures M) hrev r hkn
  refine ⟨Q ∪ Qr, ?_, fun G' hG' S hS => ?_⟩
  · calc (Q ∪ Qr).card ≤ Q.card + Qr.card := card_union_le _ _
      _ ≤ 10 * cost * Fintype.card V * (k + 1) +
          10 * cost * Fintype.card V * (k + 1) := Nat.add_le_add hQ hQr
      _ = 20 * cost * Fintype.card V * (k + 1) := by ring
  · rcases hS with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · exact hcert G' (hG'.mono subset_union_left) S hr hs
    · have h := hcertr G' (hG'.mono subset_union_right) Sᶜ (mem_compl.mpr hr) hs
      simpa only [WeightedDiGraph.rev_out, compl_compl] using h

end CutQueryComplexity.DirectedCertificate.Completion

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_separator_family_certificate

#print axioms CutQueryComplexity.DirectedCertificate.Completion.exists_root_small_both_certificate
