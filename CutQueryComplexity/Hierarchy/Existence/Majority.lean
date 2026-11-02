import CutQueryComplexity.Hierarchy.Children

/-! # Local cluster properties bound the representation cost (hierarchy plan, Milestone 1)

Fix the ambient graph `J`. For a cluster `P`, `out(U) = J.cut U` counts all edges leaving `U`,
including those leaving `P`.

* `Bandwidth J P λ`: every `U ⊆ P` with `4|U| ≤ 3|P|` has `out(U) ≤ λ · cross(U, P ∖ U)`.
* The child-weight condition at an internal node `x` with parameter `δ`: every `U` in its
  cluster with `2|U| ≤ |P|` has `∑_c cross(U ∩ C_c, C_cᶜ) ≤ δ · cross(U, P ∖ U)`, the sum over
  the children `c` of `x`.

`rep_le_of_local` proves that a hierarchy whose leaf clusters are the singletons, whose
clusters all have bandwidth `λ`, whose internal nodes have child weight `δ`, and whose depths
are at most `D` satisfies `R(S) ≤ (λ + δ)(D + 1) c_J(S)` for every shore `S`. The witness is
the majority labelling: a cluster gets `true` exactly when more than half of it lies in `S`.
No flow or routing argument is used.
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset TwoRespecting

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem cross_mono (J : WeightedGraph V) {S S' T T' : Finset V} (hS : S ⊆ S') (hT : T ⊆ T') :
    J.cross S T ≤ J.cross S' T' := by
  unfold cross
  calc ∑ u ∈ S, ∑ v ∈ T, J.w u v ≤ ∑ u ∈ S, ∑ v ∈ T', J.w u v :=
        sum_le_sum fun u _ => sum_le_sum_of_subset_of_nonneg hT fun v _ _ => J.nonneg u v
    _ ≤ ∑ u ∈ S', ∑ v ∈ T', J.w u v :=
        sum_le_sum_of_subset_of_nonneg hS fun u _ _ => sum_nonneg fun v _ => J.nonneg u v

theorem cross_le_cut (J : WeightedGraph V) {S T : Finset V} (h : Disjoint S T) :
    J.cross S T ≤ J.cut S := by
  rw [← cross_compl]
  exact cross_mono J le_rfl fun v hv => mem_compl.mpr fun hS => disjoint_left.mp h hS hv

/-- Bandwidth: small subsets of `P` have boundary at most `λ` times their cut inside `P`. -/
def Bandwidth (J : WeightedGraph V) (P : Finset V) (lam : ℝ) : Prop :=
  ∀ U ⊆ P, 4 * U.card ≤ 3 * P.card → J.cut U ≤ lam * J.cross U (P \ U)

/-- The cut of `S` inside a cluster `A`. -/
def inner (J : WeightedGraph V) (S A : Finset V) : ℝ := J.cross (S ∩ A) (A \ S)

theorem inner_nonneg (J : WeightedGraph V) (S A : Finset V) : 0 ≤ inner J S A :=
  J.cross_nonneg _ _

/-- A minority-labelled cluster: its boundary is its minority part's boundary plus `λ` times
its internal cut. -/
theorem cut_le_of_minority (J : WeightedGraph V) {C S : Finset V} {lam : ℝ}
    (hb : Bandwidth J C lam) (hmin : ¬ (2 * (S ∩ C).card > C.card)) :
    J.cut C ≤ J.cross (C \ S) Cᶜ + lam * inner J S C := by
  have hsplit : J.cut C = J.cross (C \ S) Cᶜ + J.cross (C ∩ S) Cᶜ := by
    rw [← cross_compl, ← cross_union_left J _ _ _ (disjoint_sdiff_inter C S), sdiff_union_inter]
  have h1 : J.cross (C ∩ S) Cᶜ ≤ J.cut (C ∩ S) :=
    cross_le_cut J (disjoint_left.mpr fun v hv hc => (mem_compl.mp hc) (mem_inter.mp hv).1)
  have h2 : J.cut (C ∩ S) ≤ lam * J.cross (C ∩ S) (C \ (C ∩ S)) := by
    refine hb _ inter_subset_left ?_
    rw [inter_comm] at hmin; omega
  have h3 : J.cross (C ∩ S) (C \ (C ∩ S)) = inner J S C := by
    unfold inner; congr 1 <;> ext v <;> (simp; try tauto)
  rw [h3] at h2
  linarith

/-- A majority-labelled cluster, symmetrically. -/
theorem cut_le_of_majority (J : WeightedGraph V) {C S : Finset V} {lam : ℝ}
    (hb : Bandwidth J C lam) (hmaj : 2 * (S ∩ C).card > C.card) :
    J.cut C ≤ J.cross (C ∩ S) Cᶜ + lam * inner J S C := by
  have hsplit : J.cut C = J.cross (C ∩ S) Cᶜ + J.cross (C \ S) Cᶜ := by
    rw [← cross_compl, ← cross_union_left J _ _ _ (disjoint_sdiff_inter C S).symm, union_comm,
      sdiff_union_inter]
  have h1 : J.cross (C \ S) Cᶜ ≤ J.cut (C \ S) :=
    cross_le_cut J (disjoint_left.mpr fun v hv hc => (mem_compl.mp hc) (mem_sdiff.mp hv).1)
  have hcard : (C \ S).card + (S ∩ C).card = C.card := by
    rw [inter_comm, card_sdiff_add_card_inter]
  have h2 : J.cut (C \ S) ≤ lam * J.cross (C \ S) (C \ (C \ S)) := by
    refine hb _ sdiff_subset ?_
    omega
  have h3 : J.cross (C \ S) (C \ (C \ S)) = inner J S C := by
    unfold inner; rw [J.cross_comm]; congr 1; ext v; simp [and_comm]
  rw [h3] at h2
  linarith

/-- Pairwise disjoint clusters have internal cuts summing to at most `c_J(S)`. -/
theorem sum_inner_le_cut (J : WeightedGraph V) (S : Finset V) {ι : Type} (Y : Finset ι)
    (A : ι → Finset V) (hdisj : (Y : Set ι).PairwiseDisjoint A) :
    ∑ y ∈ Y, inner J S (A y) ≤ J.cut S := by
  have hd' : (Y : Set ι).PairwiseDisjoint fun y => S ∩ A y :=
    fun y hy y' hy' hne => disjoint_left.mpr fun v hv hv' =>
      disjoint_left.mp (hdisj hy hy' hne) (mem_inter.mp hv).2 (mem_inter.mp hv').2
  calc ∑ y ∈ Y, inner J S (A y) ≤ ∑ y ∈ Y, J.cross (S ∩ A y) Sᶜ := by
        refine sum_le_sum fun y _ => cross_mono J le_rfl fun v hv => ?_
        exact mem_compl.mpr (mem_sdiff.mp hv).2
    _ = J.cross (Y.biUnion fun y => S ∩ A y) Sᶜ := by
        unfold cross; rw [sum_biUnion hd']
    _ ≤ J.cross S Sᶜ := cross_mono J (biUnion_subset.mpr fun y _ => inter_subset_left) le_rfl
    _ = J.cut S := cross_compl J S

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The majority label of a node. -/
def majority (H : Hier V N) (S : Finset V) (x : N) : Bool :=
  decide (2 * (S ∩ H.cluster x).card > (H.cluster x).card)

omit [Fintype V] [DecidableEq V] in
theorem labelCost_toReal_bool (H : Hier V N) (cap : N → ℝ) (f : N → Bool) :
    H.labelCost cap (toReal f) =
      ∑ x ∈ H.edges, if f x = f (H.T.parent x) then 0 else cap x := by
  unfold labelCost
  refine sum_congr rfl fun x _ => ?_
  cases hx : f x <;> cases hp : f (H.T.parent x) <;> simp [toReal, hx, hp]

/-- **Milestone 1.** Local bandwidth and child-weight properties bound the canonical
representation cost by `(λ + δ)(D + 1)` times every cut. -/
theorem rep_le_of_local (H : Hier V N) (J : WeightedGraph V) (S : Finset V) {lam δ : ℝ}
    {D : ℕ} (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hlc : H.LeafChildless)
    (hleaf : ∀ v, H.cluster (H.leaf v) = {v})
    (hband : ∀ x, Bandwidth J (H.cluster x) lam)
    (hchild : ∀ x, ¬ H.IsLeaf x → ∀ U ⊆ H.cluster x, 2 * U.card ≤ (H.cluster x).card →
      ∑ c ∈ H.children x, J.cross (U ∩ H.cluster c) (H.cluster c)ᶜ ≤
        δ * J.cross U (H.cluster x \ U))
    (hdepth : ∀ x, H.T.depth x ≤ D) :
    H.rep (H.canon J) S ≤ (lam + δ) * (D + 1) * J.cut S := by
  set ℓ := H.majority S
  have hext : H.Extends S ℓ := by
    intro v
    simp only [ℓ, majority, hleaf v]
    by_cases hv : v ∈ S <;> simp [hv]
  have hsub : ∀ {y c : N}, c ∈ H.children y → H.cluster c ⊆ H.cluster y := fun hc v hv =>
    mem_cluster.mpr (isAnc_of_mem_children hc (mem_cluster.mp hv))
  -- the cost at each parent
  have hnode : ∀ y, ∑ c ∈ H.children y, (if ℓ c = ℓ y then 0 else J.cut (H.cluster c)) ≤
      δ * inner J S (H.cluster y) + lam * ∑ c ∈ H.children y, inner J S (H.cluster c) := by
    intro y
    by_cases hy : H.IsLeaf y
    · obtain ⟨v, rfl⟩ := hy
      rw [hlc v, sum_empty, sum_empty, mul_zero, add_zero]
      exact mul_nonneg hδ (inner_nonneg _ _ _)
    set P := H.cluster y with hP
    set U := if ℓ y then P \ S else P ∩ S with hU
    have hUP : U ⊆ P := by simp only [hU]; split_ifs; exacts [sdiff_subset, inter_subset_left]
    have hUcard : 2 * U.card ≤ P.card := by
      simp only [hU]
      have hcard : (P \ S).card + (S ∩ P).card = P.card := by
        rw [inter_comm, card_sdiff_add_card_inter]
      by_cases h : ℓ y
      · rw [ite_eq_left h]; simp only [ℓ, majority, decide_eq_true_eq, ← hP] at h; omega
      · rw [ite_eq_right h, inter_comm P S]
        simp only [ℓ, majority, decide_eq_true_eq, ← hP, not_lt] at h
        omega
    have hUin : J.cross U (P \ U) = inner J S P := by
      simp only [hU, inner]
      split_ifs
      · rw [sdiff_sdiff_right_self, J.cross_comm, inter_comm]; rfl
      · rw [sdiff_inter_self_left, inter_comm]
    have hchildc : ∀ c ∈ H.children y, (if ℓ c = ℓ y then 0 else J.cut (H.cluster c)) ≤
        J.cross (U ∩ H.cluster c) (H.cluster c)ᶜ + lam * inner J S (H.cluster c) := by
      intro c hc
      have hcP := hsub hc
      by_cases heq : ℓ c = ℓ y
      · rw [ite_eq_left heq]
        exact add_nonneg (J.cross_nonneg _ _) (mul_nonneg hlam (inner_nonneg _ _ _))
      rw [ite_eq_right heq]
      by_cases hyl : ℓ y
      · have hcl : ℓ c = false := by
          cases h : ℓ c
          · rfl
          · exact absurd (h.trans hyl.symm) heq
        have hmin : ¬ (2 * (S ∩ H.cluster c).card > (H.cluster c).card) := by
          simpa [ℓ, majority] using hcl
        have hUc : U ∩ H.cluster c = H.cluster c \ S := by
          simp only [hU, ite_eq_left hyl]
          ext v; simp only [mem_inter, mem_sdiff]
          exact ⟨fun ⟨⟨_, h⟩, h'⟩ => ⟨h', h⟩, fun ⟨h', h⟩ => ⟨⟨hcP h', h⟩, h'⟩⟩
        rw [hUc]; exact cut_le_of_minority J (hband c) hmin
      · have hcl : ℓ c = true := by
          cases h : ℓ c
          · exact absurd (h.trans (Bool.eq_false_of_ne_true hyl).symm) heq
          · rfl
        have hmaj : 2 * (S ∩ H.cluster c).card > (H.cluster c).card := by
          simpa [ℓ, majority] using hcl
        have hUc : U ∩ H.cluster c = H.cluster c ∩ S := by
          simp only [hU, ite_eq_right hyl]
          ext v; simp only [mem_inter]
          exact ⟨fun ⟨⟨_, h⟩, h'⟩ => ⟨h', h⟩, fun ⟨h', h⟩ => ⟨⟨hcP h', h⟩, h'⟩⟩
        rw [hUc]; exact cut_le_of_majority J (hband c) hmaj
    calc ∑ c ∈ H.children y, (if ℓ c = ℓ y then 0 else J.cut (H.cluster c))
        ≤ ∑ c ∈ H.children y, (J.cross (U ∩ H.cluster c) (H.cluster c)ᶜ +
            lam * inner J S (H.cluster c)) := sum_le_sum hchildc
      _ = ∑ c ∈ H.children y, J.cross (U ∩ H.cluster c) (H.cluster c)ᶜ +
            lam * ∑ c ∈ H.children y, inner J S (H.cluster c) := by
          rw [sum_add_distrib, mul_sum]
      _ ≤ δ * J.cross U (P \ U) + lam * ∑ c ∈ H.children y, inner J S (H.cluster c) := by
          gcongr; exact hchild y hy U hUP hUcard
      _ = δ * inner J S P + lam * ∑ c ∈ H.children y, inner J S (H.cluster c) := by rw [hUin]
  -- the level sums
  have hlevel : ∑ y, inner J S (H.cluster y) ≤ (D + 1) * J.cut S := by
    have hfib : ∑ y, inner J S (H.cluster y) =
        ∑ d ∈ range (D + 1), ∑ y ∈ univ.filter (fun y => H.T.depth y = d),
          inner J S (H.cluster y) := by
      rw [sum_fiberwise_of_maps_to (g := H.T.depth) (t := range (D + 1))
        fun y _ => mem_range.mpr (Nat.lt_succ_of_le (hdepth y))]
    rw [hfib]
    calc ∑ d ∈ range (D + 1), ∑ y ∈ univ.filter (fun y => H.T.depth y = d),
          inner J S (H.cluster y)
        ≤ ∑ d ∈ range (D + 1), J.cut S := by
          refine sum_le_sum fun d _ => sum_inner_le_cut J S _ H.cluster ?_
          intro y hy y' hy' hne
          refine disjoint_left.mpr fun v hv hv' => hne ?_
          have h1 := mem_cluster.mp hv
          have h2 := mem_cluster.mp hv'
          have hd : H.T.depth y = H.T.depth y' := by
            rw [(mem_filter.mp hy).2, (mem_filter.mp hy').2]
          rcases RootedTree.isAnc_total_of_common h1 h2 with h | h
          · exact RootedTree.eq_of_isAnc_of_depth_eq h hd
          · exact (RootedTree.eq_of_isAnc_of_depth_eq h hd.symm).symm
      _ = (D + 1) * J.cut S := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hcut0 := J.cut_nonneg S
  have hI0 : 0 ≤ ∑ y, inner J S (H.cluster y) := sum_nonneg fun y _ => inner_nonneg _ _ _
  calc H.rep (H.canon J) S ≤ H.labelCost (H.canon J) (toReal ℓ) := H.rep_le _ hext
    _ = ∑ x ∈ H.edges, (if ℓ x = ℓ (H.T.parent x) then 0 else J.cut (H.cluster x)) := by
        rw [labelCost_toReal_bool]; rfl
    _ = ∑ y, ∑ c ∈ H.children y, (if ℓ c = ℓ y then 0 else J.cut (H.cluster c)) := by
        rw [sum_edges_eq_sum_children]
        refine sum_congr rfl fun y _ => sum_congr rfl fun c hc => ?_
        rw [(mem_children.mp hc).2]
    _ ≤ ∑ y, (δ * inner J S (H.cluster y) +
          lam * ∑ c ∈ H.children y, inner J S (H.cluster c)) := sum_le_sum fun y _ => hnode y
    _ = δ * ∑ y, inner J S (H.cluster y) + lam * ∑ x ∈ H.edges, inner J S (H.cluster x) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_edges_eq_sum_children]
    _ ≤ δ * ∑ y, inner J S (H.cluster y) + lam * ∑ y, inner J S (H.cluster y) := by
        gcongr
        · exact fun y _ _ => inner_nonneg _ _ _
        · exact subset_univ _
    _ = (lam + δ) * ∑ y, inner J S (H.cluster y) := by ring
    _ ≤ (lam + δ) * ((D + 1) * J.cut S) := by gcongr
    _ = (lam + δ) * (D + 1) * J.cut S := by ring

end Hier
end Hierarchy
end CutQueryComplexity
