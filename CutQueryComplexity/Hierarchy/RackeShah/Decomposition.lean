import CutQueryComplexity.Hierarchy.RackeShah.Basic

/-! # Certified decompositions (Räcke–Shah, M5, part A)

`Dec G Q X F` says that `F` is the family of clusters of a recursive decomposition of `X`:
either `X` is a singleton, or `X` has a balanced partition `Cs` into final children, each child
`D` carrying its own decomposition with family `Fs D`, and the load graph `Q X` satisfies the
local contract for `(X, Cs)`. The family is `insert X (Cs.biUnion Fs)`.

The structural consequences (`Dec.subset`, `Dec.nonempty_mem`, `Dec.singleton_mem`,
`Dec.laminar`) make the family a laminar cover of `X`; `Dec.parts_local` recovers the local
contract of every non-singleton member with respect to its maximal proper submembers
(`parts`), which is what the children of the laminar hierarchy are; `Dec.halving` bounds the
depth; and `Dec.congr` says the load function matters only on the family.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace RackeShah

open WeightedGraph Finset Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A recursive decomposition of `X` with cluster family `F` and load function `Q`. -/
inductive Dec (G : WeightedGraph V) (Q : Finset V → WeightedGraph V) :
    Finset V → Finset (Finset V) → Prop
  | leaf (v : V) : Dec G Q {v} {{v}}
  | node (X : Finset V) (Cs : Finset (Finset V)) (Fs : Finset V → Finset (Finset V))
      (h2 : 2 ≤ X.card) (hbal : Balanced X Cs)
      (hsub : ∀ D ∈ Cs, Dec G Q D (Fs D))
      (hloc : Local G X Cs (Q X)) :
      Dec G Q X (insert X (Cs.biUnion Fs))

/-- The maximal members of `F` strictly below `S`. -/
def parts (F : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  F.filter fun C => C ⊂ S ∧ ∀ Z ∈ F, C ⊂ Z → S ⊆ Z

theorem mem_parts {F : Finset (Finset V)} {S C : Finset V} :
    C ∈ parts F S ↔ C ∈ F ∧ C ⊂ S ∧ ∀ Z ∈ F, C ⊂ Z → S ⊆ Z := by
  simp [parts]

namespace Dec

variable {G : WeightedGraph V} {Q : Finset V → WeightedGraph V} {X : Finset V}
  {F : Finset (Finset V)}

theorem mem_self (h : Dec G Q X F) : X ∈ F := by
  cases h with
  | leaf v => exact mem_singleton_self _
  | node X Cs Fs h2 hbal hsub hloc => exact mem_insert_self _ _

theorem subset (h : Dec G Q X F) : ∀ S ∈ F, S ⊆ X := by
  induction h with
  | leaf v => intro S hS; rw [mem_singleton.mp hS]
  | node X Cs Fs h2 hbal hsub hloc ih =>
      intro S hS
      rcases mem_insert.mp hS with rfl | hS
      · exact subset_rfl
      · obtain ⟨D, hD, hSD⟩ := mem_biUnion.mp hS
        exact (ih D hD S hSD).trans (hbal.part.subset hD)

theorem nonempty_mem (h : Dec G Q X F) : ∀ S ∈ F, S.Nonempty := by
  induction h with
  | leaf v => intro S hS; rw [mem_singleton.mp hS]; exact singleton_nonempty v
  | node X Cs Fs h2 hbal hsub hloc ih =>
      intro S hS
      rcases mem_insert.mp hS with rfl | hS
      · exact card_pos.mp (by omega)
      · obtain ⟨D, hD, hSD⟩ := mem_biUnion.mp hS
        exact ih D hD S hSD

theorem nonempty (h : Dec G Q X F) : X.Nonempty := h.nonempty_mem X h.mem_self

theorem singleton_mem (h : Dec G Q X F) : ∀ v ∈ X, {v} ∈ F := by
  induction h with
  | leaf v => intro u hu; rw [mem_singleton.mp hu]; exact mem_singleton_self _
  | node X Cs Fs h2 hbal hsub hloc ih =>
      intro v hv
      have : v ∈ Cs.biUnion id := hbal.part.union ▸ hv
      obtain ⟨D, hD, hvD⟩ := mem_biUnion.mp this
      exact mem_insert_of_mem (mem_biUnion.mpr ⟨D, hD, ih D hD v hvD⟩)

theorem laminar (h : Dec G Q X F) :
    ∀ S ∈ F, ∀ T ∈ F, S ⊆ T ∨ T ⊆ S ∨ Disjoint S T := by
  induction h with
  | leaf v =>
      intro S hS T hT
      rw [mem_singleton.mp hS, mem_singleton.mp hT]
      exact Or.inl subset_rfl
  | node X Cs Fs h2 hbal hsub hloc ih =>
      intro S hS T hT
      rcases mem_insert.mp hS with rfl | hS
      · exact Or.inr (Or.inl ((node S Cs Fs h2 hbal hsub hloc).subset T hT))
      rcases mem_insert.mp hT with rfl | hT
      · exact Or.inl ((node T Cs Fs h2 hbal hsub hloc).subset S hS)
      obtain ⟨D, hD, hSD⟩ := mem_biUnion.mp hS
      obtain ⟨D', hD', hTD'⟩ := mem_biUnion.mp hT
      by_cases hDD : D = D'
      · subst hDD; exact ih D hD S hSD T hTD'
      · refine Or.inr (Or.inr ((hbal.part.disj hD hD' hDD).mono ?_ ?_))
        · exact (hsub D hD).subset S hSD
        · exact (hsub D' hD').subset T hTD'

/-- The parent cluster of a member of a child family is that child. -/
theorem eq_child_of_mem {Cs : Finset (Finset V)} {Fs : Finset V → Finset (Finset V)}
    (hbal : Balanced X Cs) (hsub : ∀ D ∈ Cs, Dec G Q D (Fs D)) {D D' S : Finset V}
    (hD : D ∈ Cs) (hD' : D' ∈ Cs) (hS : S ∈ Fs D) (hS' : S ⊆ D') : D = D' := by
  obtain ⟨v, hv⟩ := (hsub D hD).nonempty_mem S hS
  exact IsPart.eq_of_mem_of_inter (h := hbal.part) hD hD' ((hsub D hD).subset S hS hv) (hS' hv)

omit [Fintype V] in
/-- Children are strictly smaller than their parent. -/
theorem ssubset_of_balanced {Cs : Finset (Finset V)} (h2 : 2 ≤ X.card) (hbal : Balanced X Cs)
    {D : Finset V} (hD : D ∈ Cs) : D ⊂ X := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hbal.part.subset hD, fun he => ?_⟩
  have := hbal.half D hD
  rw [he] at this
  omega

/-- The maximal members below the top of a node are its children. -/
theorem parts_top {Cs : Finset (Finset V)} {Fs : Finset V → Finset (Finset V)}
    (h2 : 2 ≤ X.card) (hbal : Balanced X Cs) (hsub : ∀ D ∈ Cs, Dec G Q D (Fs D)) :
    parts (insert X (Cs.biUnion Fs)) X = Cs := by
  ext C
  rw [mem_parts]
  constructor
  · rintro ⟨hC, hCX, hmax⟩
    rcases mem_insert.mp hC with rfl | hC
    · exact absurd rfl (Finset.ssubset_iff_subset_ne.mp hCX).2
    obtain ⟨D, hD, hCD⟩ := mem_biUnion.mp hC
    have hCsub := (hsub D hD).subset C hCD
    by_cases hCDe : C = D
    · rw [hCDe]; exact hD
    · have hCD' : C ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hCsub, hCDe⟩
      have hXD := hmax D (mem_insert_of_mem (mem_biUnion.mpr ⟨D, hD, (hsub D hD).mem_self⟩)) hCD'
      exact absurd (subset_antisymm (hbal.part.subset hD) hXD)
        (Finset.ssubset_iff_subset_ne.mp (ssubset_of_balanced h2 hbal hD)).2
  · intro hC
    refine ⟨mem_insert_of_mem (mem_biUnion.mpr ⟨C, hC, (hsub C hC).mem_self⟩),
      ssubset_of_balanced h2 hbal hC, fun Z hZ hCZ => ?_⟩
    rcases mem_insert.mp hZ with rfl | hZ
    · exact subset_rfl
    obtain ⟨D', hD', hZD'⟩ := mem_biUnion.mp hZ
    have := eq_child_of_mem hbal hsub hC hD' (hsub C hC).mem_self
      (hCZ.1.trans ((hsub D' hD').subset Z hZD'))
    subst this
    exact absurd (subset_antisymm hCZ.1 ((hsub C hC).subset Z hZD'))
      (Finset.ssubset_iff_subset_ne.mp hCZ).2

/-- Below a child, the maximal members are computed in the child's family. -/
theorem parts_child {Cs : Finset (Finset V)} {Fs : Finset V → Finset (Finset V)}
    (hbal : Balanced X Cs) (hsub : ∀ D ∈ Cs, Dec G Q D (Fs D)) {D S : Finset V} (hD : D ∈ Cs)
    (hS : S ∈ Fs D) : parts (insert X (Cs.biUnion Fs)) S = parts (Fs D) S := by
  ext C
  rw [mem_parts, mem_parts]
  constructor
  · rintro ⟨hC, hCS, hmax⟩
    have hSD := (hsub D hD).subset S hS
    rcases mem_insert.mp hC with rfl | hC
    · exact absurd (hCS.trans_subset (hSD.trans (hbal.part.subset hD))) (ssubset_irrefl _)
    obtain ⟨D', hD', hCD'⟩ := mem_biUnion.mp hC
    have := eq_child_of_mem hbal hsub hD' hD hCD' (hCS.1.trans hSD)
    subst this
    exact ⟨hCD', hCS, fun Z hZ hCZ => hmax Z (mem_insert_of_mem (mem_biUnion.mpr ⟨D', hD', hZ⟩)) hCZ⟩
  · rintro ⟨hC, hCS, hmax⟩
    refine ⟨mem_insert_of_mem (mem_biUnion.mpr ⟨D, hD, hC⟩), hCS, fun Z hZ hCZ => ?_⟩
    rcases mem_insert.mp hZ with rfl | hZ
    · exact (hsub D hD).subset S hS |>.trans (hbal.part.subset hD)
    obtain ⟨D', hD', hZD'⟩ := mem_biUnion.mp hZ
    have := eq_child_of_mem hbal hsub hD hD' hC (hCZ.1.trans ((hsub D' hD').subset Z hZD'))
    subst this
    exact hmax Z hZD' hCZ

/-- Every non-singleton member satisfies the local contract with respect to its children. -/
theorem parts_local (h : Dec G Q X F) :
    ∀ S ∈ F, 2 ≤ S.card → Local G S (parts F S) (Q S) := by
  induction h with
  | leaf v =>
      intro S hS h2
      rw [mem_singleton.mp hS, card_singleton] at h2
      omega
  | node X Cs Fs h2 hbal hsub hloc ih =>
      intro S hS hS2
      rcases mem_insert.mp hS with rfl | hS
      · rw [parts_top h2 hbal hsub]; exact hloc
      · obtain ⟨D, hD, hSD⟩ := mem_biUnion.mp hS
        rw [parts_child hbal hsub hD hSD]
        exact ih D hD S hSD hS2

/-- The members of a child family are not the top. -/
theorem top_notMem_biUnion {Cs : Finset (Finset V)} {Fs : Finset V → Finset (Finset V)}
    (h2 : 2 ≤ X.card) (hbal : Balanced X Cs) (hsub : ∀ D ∈ Cs, Dec G Q D (Fs D)) :
    X ∉ Cs.biUnion Fs := by
  intro hX
  obtain ⟨D, hD, hXD⟩ := mem_biUnion.mp hX
  have := (hsub D hD).subset X hXD
  exact (Finset.ssubset_iff_subset_ne.mp (ssubset_of_balanced h2 hbal hD)).2
    (subset_antisymm (hbal.part.subset hD) this)

/-- Child families are pairwise disjoint. -/
theorem pairwiseDisjoint_families {Cs : Finset (Finset V)} {Fs : Finset V → Finset (Finset V)}
    (hbal : Balanced X Cs) (hsub : ∀ D ∈ Cs, Dec G Q D (Fs D)) :
    (Cs : Set (Finset V)).PairwiseDisjoint Fs := by
  intro D hD D' hD' hne
  rw [Function.onFun, disjoint_left]
  intro S hS hS'
  exact hne (eq_child_of_mem hbal hsub hD hD' hS ((hsub D' hD').subset S hS'))

/-- The load function matters only on the family. -/
theorem congr {Q' : Finset V → WeightedGraph V} (h : Dec G Q X F) (hQ : ∀ S ∈ F, Q' S = Q S) :
    Dec G Q' X F := by
  induction h with
  | leaf v => exact leaf v
  | node X Cs Fs h2 hbal hsub hloc ih =>
      refine node X Cs Fs h2 hbal (fun D hD => ih D hD fun S hS => hQ S ?_) ?_
      · exact mem_insert_of_mem (mem_biUnion.mpr ⟨D, hD, hS⟩)
      · rw [hQ X (mem_insert_self _ _)]; exact hloc

/-- **Halving.** A member with `d` strict supersets in the family has at most `|X| / 2^d`
vertices. -/
theorem halving (h : Dec G Q X F) :
    ∀ S ∈ F, 2 ^ (F.filter fun T => S ⊂ T).card * S.card ≤ X.card := by
  induction h with
  | leaf v =>
      intro S hS
      rw [mem_singleton.mp hS]
      have : ({{v}} : Finset (Finset V)).filter (fun T => {v} ⊂ T) = ∅ := by
        ext T
        simp only [mem_filter, mem_singleton, Finset.notMem_empty, iff_false, not_and]
        rintro rfl
        exact ssubset_irrefl _
      rw [this, card_empty, pow_zero, one_mul]
  | node X Cs Fs h2 hbal hsub hloc ih =>
      intro S hS
      rcases mem_insert.mp hS with rfl | hS
      · have : (insert S (Cs.biUnion Fs)).filter (fun T => S ⊂ T) = ∅ := by
          ext T
          simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hT hST
          exact (Finset.ssubset_iff_subset_ne.mp hST).2
            (subset_antisymm hST.1 ((node S Cs Fs h2 hbal hsub hloc).subset T hT))
        rw [this, card_empty, pow_zero, one_mul]
      · obtain ⟨D, hD, hSD⟩ := mem_biUnion.mp hS
        have hSD' := (hsub D hD).subset S hSD
        -- the strict supersets of `S` are `X` and those in the family of `D`
        have hfilt : (insert X (Cs.biUnion Fs)).filter (fun T => S ⊂ T) =
            insert X ((Fs D).filter fun T => S ⊂ T) := by
          ext T
          simp only [mem_filter, mem_insert, mem_biUnion]
          constructor
          · rintro ⟨rfl | ⟨D', hD', hTD'⟩, hST⟩
            · exact Or.inl rfl
            · have := eq_child_of_mem hbal hsub hD hD' hSD (hST.1.trans ((hsub D' hD').subset T hTD'))
              subst this
              exact Or.inr ⟨hTD', hST⟩
          · rintro (rfl | ⟨hT, hST⟩)
            · exact ⟨Or.inl rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hSD'.trans (hbal.part.subset hD),
                fun he => (Finset.ssubset_iff_subset_ne.mp (ssubset_of_balanced h2 hbal hD)).2
                  (subset_antisymm (hbal.part.subset hD) (he ▸ hSD'))⟩⟩
            · exact ⟨Or.inr ⟨D, hD, hT⟩, hST⟩
        have hXnot : X ∉ (Fs D).filter fun T => S ⊂ T := by
          intro hX
          have := (hsub D hD).subset X (mem_filter.mp hX).1
          exact (Finset.ssubset_iff_subset_ne.mp (ssubset_of_balanced h2 hbal hD)).2
            (subset_antisymm (hbal.part.subset hD) this)
        rw [hfilt, card_insert_of_notMem hXnot, pow_succ]
        have h1 := ih D hD S hSD
        have h2' := hbal.half D hD
        calc 2 ^ ((Fs D).filter fun T => S ⊂ T).card * 2 * S.card
            = 2 * (2 ^ ((Fs D).filter fun T => S ⊂ T).card * S.card) := by ring
          _ ≤ 2 * D.card := Nat.mul_le_mul_left 2 h1
          _ ≤ X.card := h2'

end Dec

end RackeShah
end Hierarchy
end CutQueryComplexity
