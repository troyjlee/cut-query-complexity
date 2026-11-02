import CutQueryComplexity.Hierarchy.Existence.BalancedPartition

/-! # The recursive cluster family (hierarchy plan, Milestone 5, part 1)

Fix `J`, a bandwidth parameter `λ ≥ 1` with `4 β(|V|) ≤ λ`, and choose for every set `P` with
`|P| ≥ 2` and bandwidth `λ` a balanced partition `bpart P` (Milestone 4); other sets get no
parts. `clusters P` is `P` together with the clusters of its parts, by recursion on `|P|`.

For a *good* `P` (nonempty with bandwidth `λ`) the family `clusters P`:

* consists of good subsets of `P` (`clusters_good`);
* contains every singleton of `P` (`singleton_mem_clusters`);
* is laminar (`clusters_laminar`) and closed under taking the clusters below a member
  (`mem_clusters_of_subset`);
* has at most `2|P| − 1` members (`card_clusters_le`).
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

section Clusters

variable (J : WeightedGraph V) {lam : ℝ} (hlam1 : 1 ≤ lam)
  (hlamB : 4 * beta (Fintype.card V) ≤ lam)

open Classical in
/-- The chosen balanced partition of a good set with at least two vertices. -/
noncomputable def bpart (P : Finset V) : Finset (Finset V) :=
  if h : 2 ≤ P.card ∧ Bandwidth J P lam then
    Classical.choose (exists_balanced_partition J hlam1 hlamB h.1 h.2) else ∅

include hlam1 hlamB in
theorem bpart_spec {P : Finset V} (h2 : 2 ≤ P.card) (hb : Bandwidth J P lam) :
    IsPart P (bpart J hlam1 hlamB P) ∧ (∀ C ∈ bpart J hlam1 hlamB P, Bandwidth J C lam) ∧
      (∀ C ∈ bpart J hlam1 hlamB P, 6 * C.card ≤ 5 * P.card) ∧
      ∀ X ⊆ P, 2 * X.card ≤ P.card →
        ∑ C ∈ bpart J hlam1 hlamB P, J.cross (X ∩ C) Cᶜ ≤ 25 * lam * J.cross X (P \ X) := by
  classical
  have h : 2 ≤ P.card ∧ Bandwidth J P lam := ⟨h2, hb⟩
  simp only [bpart, dite_eq_left h]
  exact Classical.choose_spec (exists_balanced_partition J hlam1 hlamB h.1 h.2)

theorem bpart_card_lt {P C : Finset V} (hC : C ∈ bpart J hlam1 hlamB P) : C.card < P.card := by
  classical
  by_cases h : 2 ≤ P.card ∧ Bandwidth J P lam
  · have := (bpart_spec J hlam1 hlamB h.1 h.2).2.2.1 C hC
    omega
  · simp only [bpart, dite_eq_right h, Finset.notMem_empty] at hC

theorem bpart_eq_empty {P : Finset V} (h : ¬ (2 ≤ P.card ∧ Bandwidth J P lam)) :
    bpart J hlam1 hlamB P = ∅ := by
  classical
  simp only [bpart, dite_eq_right h]

/-- The cluster family below `P`. -/
noncomputable def clusters (P : Finset V) : Finset (Finset V) :=
  insert P ((bpart J hlam1 hlamB P).attach.biUnion fun C => clusters C.1)
termination_by P.card
decreasing_by exact bpart_card_lt J hlam1 hlamB C.2

theorem mem_clusters {P X : Finset V} :
    X ∈ clusters J hlam1 hlamB P ↔
      X = P ∨ ∃ C ∈ bpart J hlam1 hlamB P, X ∈ clusters J hlam1 hlamB C := by
  rw [clusters]
  simp only [mem_insert, mem_biUnion, mem_attach, true_and, Subtype.exists, exists_prop]

theorem self_mem_clusters (P : Finset V) : P ∈ clusters J hlam1 hlamB P :=
  (mem_clusters J hlam1 hlamB).mpr (Or.inl rfl)

/-- A good set: nonempty with bandwidth `λ`. -/
def Good (P : Finset V) : Prop := P.Nonempty ∧ Bandwidth J P lam

/-- The parts of a good set with at least two vertices are good. -/
theorem good_of_mem_bpart {P C : Finset V} (hC : C ∈ bpart J hlam1 hlamB P) :
    Good J (lam := lam) C := by
  classical
  by_cases h : 2 ≤ P.card ∧ Bandwidth J P lam
  · obtain ⟨hpart, hband, -, -⟩ := bpart_spec J hlam1 hlamB h.1 h.2
    exact ⟨hpart.nonempty C hC, hband C hC⟩
  · rw [bpart_eq_empty J hlam1 hlamB h] at hC; exact absurd hC (Finset.notMem_empty C)

theorem subset_of_mem_bpart {P C : Finset V} (hC : C ∈ bpart J hlam1 hlamB P) : C ⊆ P := by
  classical
  by_cases h : 2 ≤ P.card ∧ Bandwidth J P lam
  · exact (bpart_spec J hlam1 hlamB h.1 h.2).1.subset hC
  · rw [bpart_eq_empty J hlam1 hlamB h] at hC; exact absurd hC (Finset.notMem_empty C)

/-- Clusters are good subsets. -/
theorem clusters_good : ∀ (P : Finset V), Good J (lam := lam) P →
    ∀ X ∈ clusters J hlam1 hlamB P, X ⊆ P ∧ Good J (lam := lam) X := by
  intro P
  induction P using Finset.strongInduction with
  | H P ih =>
    intro hP X hX
    rcases (mem_clusters J hlam1 hlamB).mp hX with rfl | ⟨C, hC, hXC⟩
    · exact ⟨le_rfl, hP⟩
    · have hCP := subset_of_mem_bpart J hlam1 hlamB hC
      have hlt : C ⊂ P := ssubset_of_subset_of_ne hCP fun he => by
        have := bpart_card_lt J hlam1 hlamB hC; rw [he] at this; omega
      obtain ⟨h1, h2⟩ := ih C hlt (good_of_mem_bpart J hlam1 hlamB hC) X hXC
      exact ⟨h1.trans hCP, h2⟩

/-- Every singleton of a good set is a cluster. -/
theorem singleton_mem_clusters : ∀ (P : Finset V), Good J (lam := lam) P →
    ∀ v ∈ P, {v} ∈ clusters J hlam1 hlamB P := by
  intro P
  induction P using Finset.strongInduction with
  | H P ih =>
    intro hP v hv
    by_cases h2 : 2 ≤ P.card
    · obtain ⟨hpart, -, -, -⟩ := bpart_spec J hlam1 hlamB h2 hP.2
      rw [← hpart.union] at hv
      obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp hv
      have hCP := subset_of_mem_bpart J hlam1 hlamB hC
      have hlt : C ⊂ P := ssubset_of_subset_of_ne hCP fun he => by
        have := bpart_card_lt J hlam1 hlamB hC; rw [he] at this; omega
      exact (mem_clusters J hlam1 hlamB).mpr
        (Or.inr ⟨C, hC, ih C hlt (good_of_mem_bpart J hlam1 hlamB hC) v hvC⟩)
    · have : P = {v} := by
        have h1 : P.card = 1 := by have := hP.1.card_pos; omega
        obtain ⟨w, hw⟩ := card_eq_one.mp h1
        rw [hw] at hv ⊢; rw [mem_singleton.mp hv]
      rw [this]; exact self_mem_clusters J hlam1 hlamB _

/-- Two distinct parts are disjoint. -/
theorem disjoint_of_mem_bpart {P C C' : Finset V} (_hP : Good J (lam := lam) P)
    (hC : C ∈ bpart J hlam1 hlamB P) (hC' : C' ∈ bpart J hlam1 hlamB P) (hne : C ≠ C') :
    Disjoint C C' := by
  classical
  by_cases h : 2 ≤ P.card ∧ Bandwidth J P lam
  · exact (bpart_spec J hlam1 hlamB h.1 h.2).1.disj hC hC' hne
  · rw [bpart_eq_empty J hlam1 hlamB h] at hC; exact absurd hC (Finset.notMem_empty C)

/-- The cluster family is laminar. -/
theorem clusters_laminar : ∀ (P : Finset V), Good J (lam := lam) P →
    ∀ X ∈ clusters J hlam1 hlamB P, ∀ Y ∈ clusters J hlam1 hlamB P,
      X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y := by
  intro P
  induction P using Finset.strongInduction with
  | H P ih =>
    intro hP X hX Y hY
    have hsub := fun Z hZ => (clusters_good J hlam1 hlamB P hP Z hZ).1
    rcases (mem_clusters J hlam1 hlamB).mp hX with rfl | ⟨C, hC, hXC⟩
    · exact Or.inr (Or.inl (hsub Y hY))
    rcases (mem_clusters J hlam1 hlamB).mp hY with rfl | ⟨C', hC', hYC'⟩
    · exact Or.inl (hsub X hX)
    have hgC := good_of_mem_bpart J hlam1 hlamB hC
    have hXC' := (clusters_good J hlam1 hlamB C hgC X hXC).1
    by_cases hCC : C = C'
    · subst hCC
      have hlt : C ⊂ P := ssubset_of_subset_of_ne (subset_of_mem_bpart J hlam1 hlamB hC)
        fun he => by have := bpart_card_lt J hlam1 hlamB hC; rw [he] at this; omega
      exact ih C hlt hgC X hXC Y hYC'
    · have hYC'' := (clusters_good J hlam1 hlamB C' (good_of_mem_bpart J hlam1 hlamB hC') Y
        hYC').1
      exact Or.inr (Or.inr ((disjoint_of_mem_bpart J hlam1 hlamB hP hC hC' hCC).mono hXC' hYC''))

/-- Clusters contained in a member of the family are clusters below that member. -/
theorem mem_clusters_of_subset : ∀ (P : Finset V), Good J (lam := lam) P →
    ∀ X ∈ clusters J hlam1 hlamB P, ∀ Y ∈ clusters J hlam1 hlamB P, X ⊆ Y →
      X ∈ clusters J hlam1 hlamB Y := by
  intro P
  induction P using Finset.strongInduction with
  | H P ih =>
    intro hP X hX Y hY hXY
    rcases (mem_clusters J hlam1 hlamB).mp hY with rfl | ⟨C', hC', hYC'⟩
    · exact hX
    rcases (mem_clusters J hlam1 hlamB).mp hX with rfl | ⟨C, hC, hXC⟩
    · -- `P ⊆ Y ⊆ C' ⊊ P` is impossible
      have h1 := (clusters_good J hlam1 hlamB C' (good_of_mem_bpart J hlam1 hlamB hC') Y
        hYC').1
      have := card_le_card (hXY.trans h1)
      have := bpart_card_lt J hlam1 hlamB hC'
      omega
    have hgC := good_of_mem_bpart J hlam1 hlamB hC
    have hXC' := (clusters_good J hlam1 hlamB C hgC X hXC)
    have hYC'' := (clusters_good J hlam1 hlamB C' (good_of_mem_bpart J hlam1 hlamB hC') Y hYC').1
    have hCC : C = C' := by
      by_contra hne
      obtain ⟨v, hv⟩ := hXC'.2.1
      exact disjoint_left.mp (disjoint_of_mem_bpart J hlam1 hlamB hP hC hC' hne) (hXC'.1 hv)
        (hYC'' (hXY hv))
    subst hCC
    have hlt : C ⊂ P := ssubset_of_subset_of_ne (subset_of_mem_bpart J hlam1 hlamB hC)
      fun he => by have := bpart_card_lt J hlam1 hlamB hC; rw [he] at this; omega
    exact ih C hlt hgC X hXC Y hYC' hXY

/-- The clusters below a member are clusters. -/
theorem clusters_subset_of_mem : ∀ (P : Finset V), ∀ Y ∈ clusters J hlam1 hlamB P,
    clusters J hlam1 hlamB Y ⊆ clusters J hlam1 hlamB P := by
  intro P
  induction P using Finset.strongInduction with
  | H P ih =>
    intro Y hY
    rcases (mem_clusters J hlam1 hlamB).mp hY with rfl | ⟨C, hC, hYC⟩
    · exact le_rfl
    have hlt : C.card < P.card := bpart_card_lt J hlam1 hlamB hC
    have hCP : C ⊂ P := by
      by_cases hgood : 2 ≤ P.card ∧ Bandwidth J P lam
      · exact ssubset_of_subset_of_ne (subset_of_mem_bpart J hlam1 hlamB hC)
          fun he => by rw [he] at hlt; omega
      · rw [bpart_eq_empty J hlam1 hlamB hgood] at hC; exact absurd hC (Finset.notMem_empty C)
    intro Z hZ
    exact (mem_clusters J hlam1 hlamB).mpr (Or.inr ⟨C, hC, ih C hCP Y hYC hZ⟩)

/-- At most `2|P| − 1` clusters. -/
theorem card_clusters_le : ∀ (P : Finset V), Good J (lam := lam) P →
    (clusters J hlam1 hlamB P).card + 1 ≤ 2 * P.card := by
  intro P
  induction P using Finset.strongInduction with
  | H P ih =>
    intro hP
    rw [clusters]
    by_cases h2 : 2 ≤ P.card
    · obtain ⟨hpart, -, hsmall, -⟩ := bpart_spec J hlam1 hlamB h2 hP.2
      set Ps := bpart J hlam1 hlamB P
      have hsum : ∑ C ∈ Ps, (C.card : ℕ) = P.card := by
        have := card_biUnion hpart.disj
        rw [hpart.union] at this
        simpa using this.symm
      have hPs2 : 2 ≤ Ps.card := by
        by_contra hlt
        push Not at hlt
        have h6 : 6 * ∑ C ∈ Ps, C.card ≤ Ps.card * (5 * P.card) := by
          rw [mul_sum, ← smul_eq_mul, ← sum_const]
          exact sum_le_sum fun C hC => hsmall C hC
        have : Ps.card * (5 * P.card) ≤ 1 * (5 * P.card) := Nat.mul_le_mul_right _ (by omega)
        omega
      have hrec : ∀ C ∈ Ps, (clusters J hlam1 hlamB C).card + 1 ≤ 2 * C.card := fun C hC =>
        ih C (ssubset_of_subset_of_ne (hpart.subset hC) fun he => by
          have := bpart_card_lt J hlam1 hlamB hC; rw [he] at this; omega)
          (good_of_mem_bpart J hlam1 hlamB hC)
      calc (insert P (Ps.attach.biUnion fun C => clusters J hlam1 hlamB C.1)).card + 1
          ≤ (Ps.attach.biUnion fun C => clusters J hlam1 hlamB C.1).card + 2 := by
            have := card_insert_le P (Ps.attach.biUnion fun C => clusters J hlam1 hlamB C.1)
            omega
        _ ≤ ∑ C ∈ Ps.attach, (clusters J hlam1 hlamB C.1).card + 2 := by
            have := card_biUnion_le (s := Ps.attach) (t := fun C => clusters J hlam1 hlamB C.1)
            omega
        _ = ∑ C ∈ Ps, (clusters J hlam1 hlamB C).card + 2 := by
            rw [sum_attach Ps fun C => (clusters J hlam1 hlamB C).card]
        _ ≤ ∑ C ∈ Ps, (2 * C.card - 1) + 2 := by
            gcongr with C hC
            have := hrec C hC; omega
        _ ≤ 2 * P.card := by
            have h1 : ∑ C ∈ Ps, (2 * C.card - 1) + Ps.card = 2 * ∑ C ∈ Ps, C.card := by
              rw [card_eq_sum_ones, ← sum_add_distrib, mul_sum]
              refine sum_congr rfl fun C hC => ?_
              have := (hpart.nonempty C hC).card_pos; omega
            omega
    · rw [bpart_eq_empty J hlam1 hlamB (fun h => h2 h.1)]
      simp only [attach_empty, biUnion_empty, insert_empty, card_singleton]
      have := hP.1.card_pos; omega

end Clusters

end Hierarchy
end CutQueryComplexity
