import CutQueryComplexity.GHReduction.GuideStructure
import CutQueryComplexity.GHReduction.GroupContraction

/-! # The actual centroid isolating call and repaired child accounting

When the centroid is real, its singleton is included among the isolating
terminal groups, even though it does not generate a same-parameter child.
Consequently every child shore contains precisely its own real guide group.
The two conserved quantities below are derived from the actual program output.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

namespace GuideTree

theorem centroid_not_mem_part (T : GuideTree V N) {P : Finset N} (hP : P ∈ T.parts) :
    T.centroid ∉ P := by
  rcases DirectedCertificate.Completion.separatorParts_cases _ _ _
    (Finset.mem_filter.mp hP).1 with rfl | ⟨v, hv, hp, rfl⟩
  · intro hc
    exact (Finset.mem_sdiff.mp hc).2
      (TwoRespecting.RootedTree.self_mem_subtree (T := centroidTree T.tree) T.centroid)
  · intro hc
    have hanc := TwoRespecting.RootedTree.mem_subtree.mp (Finset.mem_inter.mp hc).2
    have hdepth := hanc.depth_le
    have hparent := T.tree.depth_parent v hv
    change T.tree.depth v ≤ T.tree.depth T.centroid at hdepth
    change T.tree.parent v = T.centroid at hp
    rw [hp] at hparent
    omega

def isolationParts (T : GuideTree V N) : Finset (Finset N) :=
  if T.centroid ∈ T.real then insert {T.centroid} T.parts else T.parts

theorem part_mem_isolationParts (T : GuideTree V N) {P : Finset N} (hP : P ∈ T.parts) :
    P ∈ T.isolationParts := by
  unfold isolationParts
  split
  · exact Finset.mem_insert_of_mem hP
  · exact hP

theorem isolationPart_nonempty (T : GuideTree V N) {P : Finset N}
    (hP : P ∈ T.isolationParts) : P.Nonempty := by
  unfold isolationParts at hP
  split at hP
  · rcases Finset.mem_insert.mp hP with rfl | hP
    · exact Finset.singleton_nonempty _
    · exact T.part_nonempty hP
  · exact T.part_nonempty hP

theorem isolationPart_subset (T : GuideTree V N) {P : Finset N}
    (hP : P ∈ T.isolationParts) : P ⊆ T.real := by
  unfold isolationParts at hP
  split at hP
  next hc =>
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact Finset.singleton_subset_iff.mpr hc
    · exact T.part_subset hP
  · exact T.part_subset hP

theorem isolationParts_disjoint (T : GuideTree V N) :
    (T.isolationParts : Set (Finset N)).PairwiseDisjoint id := by
  intro P hP Q hQ hne
  unfold isolationParts at hP hQ
  split at hP <;> split at hQ
  · rcases Finset.mem_insert.mp hP with rfl | hP <;>
      rcases Finset.mem_insert.mp hQ with rfl | hQ
    · exact (hne rfl).elim
    · exact Finset.disjoint_singleton_left.mpr (T.centroid_not_mem_part hQ)
    · exact Finset.disjoint_singleton_right.mpr (T.centroid_not_mem_part hP)
    · exact T.parts_disjoint hP hQ hne
  · contradiction
  · contradiction
  · exact T.parts_disjoint hP hQ hne

theorem isolationParts_cover (T : GuideTree V N) {v : N} (hv : v ∈ T.real) :
    ∃ P ∈ T.isolationParts, v ∈ P := by
  by_cases hvc : v = T.centroid
  · subst v
    exact ⟨{T.centroid}, by simp [isolationParts, hv], by simp⟩
  · obtain ⟨P, hP, hvP⟩ := T.parts_cover_except_centroid hv hvc
    exact ⟨P, T.part_mem_isolationParts hP, hvP⟩

def isolationGroups (T : GuideTree V N) (P : T.isolationParts) : Finset V :=
  T.graphGroup P.val

theorem isolationGroups_disjoint (T : GuideTree V N) :
    Pairwise (fun P Q : T.isolationParts => Disjoint (T.isolationGroups P) (T.isolationGroups Q)) := by
  intro P Q hne
  have hpq : P.val ≠ Q.val := fun he => hne (Subtype.ext he)
  exact T.graphGroup_disjoint (T.isolationPart_subset P.property) (T.isolationPart_subset Q.property)
    (T.isolationParts_disjoint P.property Q.property hpq)

theorem isolationGroups_nonempty (T : GuideTree V N) (P : T.isolationParts) :
    (T.isolationGroups P).Nonempty := (T.isolationPart_nonempty P.property).image T.label

theorem isolationGroups_union (T : GuideTree V N) : groupUnion T.isolationGroups = T.realVertices := by
  ext v
  constructor
  · intro hv
    obtain ⟨P, _, hvP⟩ := Finset.mem_biUnion.mp hv
    exact T.graphGroup_subset (T.isolationPart_subset P.property) hvP
  · intro hv
    obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hv
    obtain ⟨P, hP, hxP⟩ := T.isolationParts_cover hx
    exact mem_groupUnion T.isolationGroups ⟨P, hP⟩
      (Finset.mem_image.mpr ⟨x, hxP, hxv⟩)

theorem isolationParts_two_le (T : GuideTree V N) (hlarge : 2 < T.real.card) :
    2 ≤ Fintype.card T.isolationParts := by
  simpa only [Fintype.card_coe] using (T.two_le_parts hlarge).trans
    (Finset.card_le_card (fun _ h => T.part_mem_isolationParts h))

theorem isolationParts_card_le (T : GuideTree V N) : Fintype.card T.isolationParts ≤ T.real.card := by
  have hd : ((Finset.univ : Finset T.isolationParts) : Set T.isolationParts).PairwiseDisjoint
      T.isolationGroups := by
    intro P _ Q _ hpq
    exact T.isolationGroups_disjoint hpq
  calc
    _ = ∑ _P : T.isolationParts, 1 := by simp
    _ ≤ ∑ P : T.isolationParts, (T.isolationGroups P).card :=
      Finset.sum_le_sum (fun P _ => (T.isolationGroups_nonempty P).card_pos)
    _ = (groupUnion T.isolationGroups).card := (Finset.card_biUnion hd).symm
    _ = T.real.card := by rw [T.isolationGroups_union, T.realVertices_card]

end GuideTree

def centroidShoreProgram {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (T : GuideTree V N) : Prog (Finset V) ℝ (T.parts → Finset V) :=
  (groupIsolatingProgram family T.isolationGroups).map
    (fun output P => output ⟨P.val, T.part_mem_isolationParts P.property⟩)

theorem centroidShoreProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (read : Finset V → ℝ) :
    n * Prog.cost read (centroidShoreProgram family T) ≤
      ((Nat.clog 2 n + 2) * Fintype.card V) * Q n := by
  rw [centroidShoreProgram, Prog.cost_map]
  have h := groupIsolatingProgram_cost_scaled family T.isolationGroups
    T.isolationGroups_disjoint T.isolationGroups_nonempty hvn hQ read
  apply h.trans
  apply Nat.mul_le_mul_right (Q n)
  apply Nat.mul_le_mul_right (Fintype.card V)
  exact Nat.add_le_add_right
    (Nat.clog_mono_right 2 (T.isolationParts_card_le.trans (T.real_card_le.trans hvn))) 2

theorem centroidShoreProgram_correct {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hlarge : 2 < T.real.card) (P : T.parts) :
    IsCanonicalTraceCut G T.realVertices (T.graphGroup P.val)
      (Prog.eval G.cut (centroidShoreProgram family T) P) := by
  have h := groupIsolatingProgram_correct family G hG T.isolationGroups
    T.isolationGroups_disjoint (T.isolationParts_two_le hlarge)
    ⟨P.val, T.part_mem_isolationParts P.property⟩
  simpa only [centroidShoreProgram, Prog.eval_map, T.isolationGroups_union,
    GuideTree.isolationGroups] using h

theorem centroidShoreProgram_disjoint {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hlarge : 2 < T.real.card) :
    Pairwise (fun P Q : T.parts => Disjoint
      (Prog.eval G.cut (centroidShoreProgram family T) P)
      (Prog.eval G.cut (centroidShoreProgram family T) Q)) := by
  intro P Q hpq
  have hne : P.val ≠ Q.val := fun he => hpq (Subtype.ext he)
  exact canonical_trace_disjoint G (T.graphGroups_disjoint P.property Q.property hne)
    (centroidShoreProgram_correct family G hG T hlarge P)
    (centroidShoreProgram_correct family G hG T hlarge Q)

/-- The repaired mass bound is now attached to the output of a query program,
not a presumed accounting property of unspecified recursive children. -/
theorem centroid_children_nonterminal_mass {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hlarge : 2 < T.real.card) :
    (∑ P : T.parts, ((Prog.eval G.cut (centroidShoreProgram family T) P).card + 1 -
      ((T.graphGroup P.val).card + 1))) ≤ Fintype.card V - T.real.card := by
  let S := Prog.eval G.cut (centroidShoreProgram family T)
  have hd : ((Finset.univ : Finset T.parts) : Set T.parts).PairwiseDisjoint S := by
    intro P _ Q _ hpq
    exact centroidShoreProgram_disjoint family G hG T hlarge hpq
  have htrace : ∀ P : T.parts, S P ∩ T.realVertices = T.graphGroup P.val :=
    fun P => (centroidShoreProgram_correct family G hG T hlarge P).1.1
  have h := sum_child_nonterminal_mass_le Finset.univ S T.realVertices hd
  simpa only [htrace, T.realVertices_card] using h

theorem centroid_children_real_potential {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hlarge : 2 < T.real.card) :
    (∑ P : T.parts, ((T.graphGroup P.val).card + 1 - 2)) ≤ T.real.card - 2 := by
  let S := Prog.eval G.cut (centroidShoreProgram family T)
  have hd : ((Finset.univ : Finset T.parts) : Set T.parts).PairwiseDisjoint S := by
    intro P _ Q _ hpq
    exact centroidShoreProgram_disjoint family G hG T hlarge hpq
  have htrace : ∀ P : T.parts, S P ∩ T.realVertices = T.graphGroup P.val :=
    fun P => (centroidShoreProgram_correct family G hG T hlarge P).1.1
  have hne : ∀ P ∈ (Finset.univ : Finset T.parts), (S P ∩ T.realVertices).Nonempty := by
    intro P _
    rw [htrace]
    exact (T.part_nonempty P.property).image T.label
  have ht : 2 ≤ (Finset.univ : Finset T.parts).card := by simpa using T.two_le_parts hlarge
  have h := sum_child_real_potential_le Finset.univ S T.realVertices hd hne ht
  simpa only [htrace, T.realVertices_card] using h

theorem centroid_children_total_size {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hlarge : 2 < T.real.card) :
    (∑ P : T.parts, ((Prog.eval G.cut (centroidShoreProgram family T) P).card + 1)) ≤
      Fintype.card V + T.real.card := by
  let S := Prog.eval G.cut (centroidShoreProgram family T)
  have hd : ((Finset.univ : Finset T.parts) : Set T.parts).PairwiseDisjoint S := by
    intro P _ Q _ hpq
    exact centroidShoreProgram_disjoint family G hG T hlarge hpq
  have hne : ∀ P ∈ (Finset.univ : Finset T.parts), (S P ∩ T.realVertices).Nonempty := by
    intro P _
    rw [(centroidShoreProgram_correct family G hG T hlarge P).1.1]
    exact (T.part_nonempty P.property).image T.label
  simpa only [T.realVertices_card] using sum_child_sizes_le Finset.univ S T.realVertices hd hne

theorem centroid_child_potential_halves (T : GuideTree V N) (P : T.parts) :
    2 * ((T.graphGroup P.val).card + 1 - 2) ≤ T.real.card - 2 := by
  apply child_potential_halves
  · exact ((T.part_nonempty P.property).image T.label).card_pos
  · simpa only [T.realVertices_card] using T.graphGroup_half P.property

end
end CutQueryComplexity.GHReduction
