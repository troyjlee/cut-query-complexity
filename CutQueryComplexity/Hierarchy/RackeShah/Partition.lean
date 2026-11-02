import CutQueryComplexity.Hierarchy.RackeShah.Transport

/-! # The exact partition-or-bottleneck alternative (Räcke–Shah, M3)

For `|S| ≥ 2`, a balanced partition `Ps` of `S` minimizing the potential
`Φ(Ps) = ∑_{C ∈ Ps} c_G(C)` exists over the finite nonempty set of balanced partitions.
Either it satisfies the expansion inequality with factor `f ≥ 4`
(`min(d_Ps(U), d_Ps(S ∖ U)) ≤ f c_G(U, S ∖ U)` for every `U`), or some violating small side `U`
is a bottleneck: merging `U` into one part changes the potential by at least
`d_Ps(U) − 2h − e` with `h = c_G(U, S ∖ U)` and `e = b_S(U)`, so minimality forces `e > 0` and
`f h ≤ 2e`. This is the `β = 1` form of the source's Lemma 2 with no running-time claim.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace RackeShah

open WeightedGraph Finset Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The potential of a partition: the total boundary of its parts. -/
noncomputable def pot (G : WeightedGraph V) (Ps : Finset (Finset V)) : ℝ := ∑ C ∈ Ps, G.cut C

/-- The expansion inequality of a partition of `S` with factor `f`. -/
def Expands (G : WeightedGraph V) (S : Finset V) (Ps : Finset (Finset V)) (f : ℝ) : Prop :=
  ∀ U : Finset V, min (∑ v ∈ U ∩ S, pd G Ps v) (∑ v ∈ S \ U, pd G Ps v) ≤
    f * G.cross (U ∩ S) (S \ U)

open Classical in
/-- The balanced partitions of `S`. -/
noncomputable def balancedPartitions (S : Finset V) : Finset (Finset (Finset V)) :=
  S.powerset.powerset.filter fun Ps => Balanced S Ps

omit [Fintype V] in
theorem mem_balancedPartitions {S : Finset V} {Ps : Finset (Finset V)} :
    Ps ∈ balancedPartitions S ↔ Balanced S Ps := by
  classical
  unfold balancedPartitions
  rw [mem_filter, mem_powerset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun C hC => mem_powerset.mpr (h.part.subset hC), h⟩

/-- Merging `U` into one part: `U` together with the nonempty remnants `C ∖ U`. -/
def mergeParts (Ps : Finset (Finset V)) (U : Finset V) : Finset (Finset V) :=
  insert U ((Ps.filter fun C => (C \ U).Nonempty).image fun C => C \ U)

omit [Fintype V] in
theorem balanced_mergeParts {S : Finset V} {Ps : Finset (Finset V)} (hB : Balanced S Ps)
    {U : Finset V} (hU : U ⊆ S) (hU0 : U.Nonempty) (hhalf : 2 * U.card ≤ S.card) :
    Balanced S (mergeParts Ps U) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact hU0
    · obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
      exact (mem_filter.mp hD).2
  · intro C hC D hD hne
    rw [Function.onFun]
    rcases mem_insert.mp hC with rfl | hC <;> rcases mem_insert.mp hD with rfl | hD
    · exact absurd rfl hne
    · obtain ⟨D', -, rfl⟩ := mem_image.mp hD
      exact disjoint_sdiff
    · obtain ⟨C', -, rfl⟩ := mem_image.mp hC
      exact disjoint_sdiff.symm
    · obtain ⟨C', hC', rfl⟩ := mem_image.mp hC
      obtain ⟨D', hD', rfl⟩ := mem_image.mp hD
      have hne' : C' ≠ D' := fun h => hne (by rw [h])
      exact (hB.part.disj (mem_filter.mp hC').1 (mem_filter.mp hD').1 hne').mono
        sdiff_subset sdiff_subset
  · ext v
    rw [mem_biUnion]
    constructor
    · rintro ⟨C, hC, hv⟩
      simp only [id] at hv
      rcases mem_insert.mp hC with rfl | hC
      · exact hU hv
      · obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
        exact hB.part.subset (mem_filter.mp hD).1 (mem_sdiff.mp hv).1
    · intro hv
      by_cases hvU : v ∈ U
      · exact ⟨U, mem_insert_self _ _, hvU⟩
      · have : v ∈ Ps.biUnion id := hB.part.union ▸ hv
        obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp this
        simp only [id] at hvC
        refine ⟨C \ U, mem_insert_of_mem (mem_image_of_mem _ (mem_filter.mpr ⟨hC, ⟨v, ?_⟩⟩)), ?_⟩
        · exact mem_sdiff.mpr ⟨hvC, hvU⟩
        · exact mem_sdiff.mpr ⟨hvC, hvU⟩
  · intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact hhalf
    · obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
      have := hB.half D (mem_filter.mp hD).1
      have := card_le_card (sdiff_subset : D \ U ⊆ D)
      omega

/-- The potential of the merged partition. -/
theorem pot_mergeParts (G : WeightedGraph V) {S : Finset V} {Ps : Finset (Finset V)}
    (hP : IsPart S Ps) (U : Finset V) :
    pot G (mergeParts Ps U) = G.cut U + ∑ C ∈ Ps, G.cut (C \ U) := by
  unfold pot mergeParts
  have hU : U ∉ (Ps.filter fun C => (C \ U).Nonempty).image fun C => C \ U := by
    intro h
    obtain ⟨D, hD, hDU⟩ := mem_image.mp h
    obtain ⟨v, hv⟩ := (mem_filter.mp hD).2
    have := hDU ▸ hv
    exact (mem_sdiff.mp hv).2 this
  rw [sum_insert hU, sum_image]
  · congr 1
    rw [sum_filter]
    refine sum_congr rfl fun C _ => ?_
    split_ifs with h
    · rfl
    · rw [not_nonempty_iff_eq_empty.mp h, cut_empty]
  · intro C hC D hD hCD
    obtain ⟨v, hv⟩ := (mem_filter.mp hC).2
    have hCD' : C \ U = D \ U := hCD
    have hvD : v ∈ D \ U := hCD' ▸ hv
    exact IsPart.eq_of_mem_of_inter (h := hP) (mem_filter.mp hC).1 (mem_filter.mp hD).1
      (mem_sdiff.mp hv).1 (mem_sdiff.mp hvD).1

omit [Fintype V] in
/-- Summing a function over the parts' remnants `C ∖ U` is summing over `S ∖ U`. -/
theorem sum_sdiff_parts {S : Finset V} {Ps : Finset (Finset V)} (hP : IsPart S Ps) (U : Finset V)
    (g : V → ℝ) : ∑ C ∈ Ps, ∑ v ∈ C \ U, g v = ∑ v ∈ S \ U, g v := by
  have hdisj : (Ps : Set (Finset V)).PairwiseDisjoint fun C => C \ U :=
    fun C hC D hD hne => (hP.disj hC hD hne).mono sdiff_subset sdiff_subset
  rw [← sum_biUnion hdisj]
  congr 1
  ext v
  rw [mem_biUnion, mem_sdiff]
  constructor
  · rintro ⟨C, hC, hv⟩
    exact ⟨hP.subset hC (mem_sdiff.mp hv).1, (mem_sdiff.mp hv).2⟩
  · rintro ⟨hvS, hvU⟩
    have : v ∈ Ps.biUnion id := hP.union ▸ hvS
    obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp this
    exact ⟨C, hC, mem_sdiff.mpr ⟨hvC, hvU⟩⟩

/-- **Accounting.** Merging `U` lowers the potential by at least `d_Ps(U) − 2h − e`. -/
theorem pot_sub_pot_mergeParts (G : WeightedGraph V) {S : Finset V} {Ps : Finset (Finset V)}
    (hP : IsPart S Ps) {U : Finset V} (hU : U ⊆ S) :
    ∑ v ∈ U, pd G Ps v - 2 * G.cross U (S \ U) - ∑ v ∈ U, bd G S v ≤
      pot G Ps - pot G (mergeParts Ps U) := by
  rw [pot_mergeParts G hP U, cut_eq_cross_add_bd G hU]
  unfold pot
  -- the difference of the two cuts of a part
  have hpart : ∀ C ∈ Ps, G.cut C - G.cut (C \ U) =
      G.cross (U ∩ C) Cᶜ - G.cross (C \ U) (C ∩ U) := by
    intro C _
    rw [cut_eq_cross_side_add G U C]
    have h2 : G.cut (C \ U) = G.cross (C \ U) Cᶜ + G.cross (C \ U) (C ∩ U) := by
      rw [← cross_compl]
      have hc : (C \ U)ᶜ = Cᶜ ∪ (C ∩ U) := by
        ext v; simp only [mem_compl, mem_sdiff, mem_union, mem_inter]; tauto
      have hd : Disjoint Cᶜ (C ∩ U) := by
        rw [disjoint_left]; intro v hv hv'; exact (mem_compl.mp hv) (mem_inter.mp hv').1
      rw [hc, cross_union_right G _ _ _ hd]
    rw [h2]; ring
  have hsum : ∑ C ∈ Ps, (G.cut C - G.cut (C \ U)) =
      ∑ v ∈ U, pd G Ps v - ∑ C ∈ Ps, G.cross (C \ U) (C ∩ U) := by
    rw [sum_congr rfl hpart, sum_sub_distrib, sum_pd]
  have hcross : ∑ C ∈ Ps, G.cross (C \ U) (C ∩ U) ≤ G.cross U (S \ U) := by
    calc ∑ C ∈ Ps, G.cross (C \ U) (C ∩ U) ≤ ∑ C ∈ Ps, G.cross (C \ U) U :=
          sum_le_sum fun C _ => cross_mono_right G _ inter_subset_right
      _ = ∑ C ∈ Ps, ∑ v ∈ C \ U, G.cross {v} U :=
          sum_congr rfl fun C _ => cross_eq_sum_singleton G _ _
      _ = ∑ v ∈ S \ U, G.cross {v} U := sum_sdiff_parts hP U _
      _ = G.cross (S \ U) U := (cross_eq_sum_singleton G _ _).symm
      _ = G.cross U (S \ U) := cross_comm G _ _
  rw [sum_sub_distrib] at hsum
  linarith

/-- The violating side can be taken small. -/
theorem exists_small_violation (G : WeightedGraph V) {S : Finset V} {Ps : Finset (Finset V)}
    {f : ℝ} (hnot : ¬ Expands G S Ps f) :
    ∃ U ⊆ S, 2 * U.card ≤ S.card ∧ f * G.cross U (S \ U) < ∑ v ∈ U, pd G Ps v := by
  unfold Expands at hnot
  push Not at hnot
  obtain ⟨U, hU⟩ := hnot
  rw [lt_min_iff] at hU
  obtain ⟨h1, h2⟩ := hU
  by_cases hc : 2 * (U ∩ S).card ≤ S.card
  · refine ⟨U ∩ S, inter_subset_right, hc, ?_⟩
    have : S \ (U ∩ S) = S \ U := by ext v; simp only [mem_sdiff, mem_inter]; tauto
    rw [this]; exact h1
  · refine ⟨S \ U, sdiff_subset, ?_, ?_⟩
    · have := card_sdiff_add_card_inter S U
      rw [inter_comm] at this
      omega
    · have h3 : S \ (S \ U) = U ∩ S := by
        ext v; simp only [mem_sdiff, mem_inter, not_and, not_not]; tauto
      rw [h3, cross_comm]
      exact h2

/-- **Partition or bottleneck.** -/
theorem exists_balanced_or_bottleneck (G : WeightedGraph V) {S : Finset V} (h2 : 2 ≤ S.card)
    {f : ℝ} (hf : 4 ≤ f) :
    (∃ Ps, Balanced S Ps ∧ Expands G S Ps f) ∨ ∃ U, Bottleneck G f S U := by
  have hne : (balancedPartitions S).Nonempty :=
    ⟨_, mem_balancedPartitions.mpr (balanced_singletons h2)⟩
  obtain ⟨Ps, hPs, hmin⟩ := exists_min_image (balancedPartitions S) (pot G) hne
  have hB : Balanced S Ps := mem_balancedPartitions.mp hPs
  by_cases hexp : Expands G S Ps f
  · exact Or.inl ⟨Ps, hB, hexp⟩
  right
  obtain ⟨U, hUS, hhalf, hviol⟩ := exists_small_violation G hexp
  set h := G.cross U (S \ U)
  set e := ∑ v ∈ U, bd G S v
  have hh0 : 0 ≤ h := G.cross_nonneg _ _
  have he0 : 0 ≤ e := sum_nonneg fun v _ => bd_nonneg G S v
  have hU0 : U.Nonempty := by
    rcases U.eq_empty_or_nonempty with rfl | hU0
    · exfalso
      simp only [sum_empty] at hviol
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ f) (G.cross_nonneg ∅ (S \ ∅))
      linarith
    · exact hU0
  -- minimality against the merged partition
  have hB' := balanced_mergeParts hB hUS hU0 hhalf
  have hle := hmin _ (mem_balancedPartitions.mpr hB')
  have hacc := pot_sub_pot_mergeParts G hB.part hUS
  have hkey : f * h < 2 * h + e := by linarith
  refine ⟨U, hUS, hhalf, ?_, ?_⟩
  · -- `e > 0`: otherwise `(f − 2) h < 0`
    rcases he0.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      rw [← hzero] at hkey
      nlinarith
  · -- `f h ≤ 2 e`
    by_contra hcon
    push Not at hcon
    nlinarith

end RackeShah
end Hierarchy
end CutQueryComplexity
