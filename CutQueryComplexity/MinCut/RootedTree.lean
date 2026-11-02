import CutQueryComplexity.Problem.Basic

/-! # Rooted spanning trees and the shapes of 2-respecting cuts

A rooted spanning tree is a parent map whose depth decreases by one toward the
root. `D v` is the set of vertices below `v`. For a vertex set `S`, `crossSet S`
lists the non-root vertices whose parent edge has exactly one endpoint in `S`.

The **parity lemma** `mem_iff_parity` says that `v ∈ S` exactly when `root ∈ S`
agrees with the parity of crossing edges on the path from `v` to the root.
Consequently, if a set is crossed by one tree edge it is a subtree up to
complement; if it is crossed by two, it is the union of two disjoint subtrees or
the difference of two nested ones (`cut_of_crossSet_one`, `cut_of_crossSet_two`).
Every proper set is crossed by some tree edge.
-/

namespace CutQueryComplexity

/-- A spanning tree given by a parent map and a depth function. -/
structure RootedTree (V : Type) where
  root : V
  parent : V → V
  depth : V → ℕ
  parent_root : parent root = root
  depth_root : depth root = 0
  depth_parent : ∀ v, v ≠ root → depth (parent v) + 1 = depth v

namespace RootedTree

noncomputable section
open scoped Classical
variable {V : Type} (T : RootedTree V)

/-- `a` is an ancestor of `v`, or equal to it. -/
def IsAnc (a v : V) : Prop := ∃ k, T.parent^[k] v = a

theorem depth_eq_zero_iff (v : V) : T.depth v = 0 ↔ v = T.root := by
  constructor
  · intro h
    by_contra hv
    have := T.depth_parent v hv
    omega
  · rintro rfl
    exact T.depth_root

theorem iterate_root (k : ℕ) : T.parent^[k] T.root = T.root := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, T.parent_root]

theorem depth_iterate (v : V) (k : ℕ) : T.depth (T.parent^[k] v) = T.depth v - k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      by_cases h : T.parent^[k] v = T.root
      · rw [h, T.parent_root, T.depth_root]
        rw [h, T.depth_root] at ih
        omega
      · have := T.depth_parent _ h
        omega

theorem iterate_depth (v : V) : T.parent^[T.depth v] v = T.root :=
  (T.depth_eq_zero_iff _).mp (by rw [depth_iterate]; omega)

theorem isAnc_refl (v : V) : T.IsAnc v v := ⟨0, rfl⟩

theorem isAnc_parent (v : V) : T.IsAnc (T.parent v) v := ⟨1, rfl⟩

theorem isAnc_root (v : V) : T.IsAnc T.root v := ⟨T.depth v, T.iterate_depth v⟩

theorem IsAnc.trans {a b c : V} (hab : T.IsAnc a b) (hbc : T.IsAnc b c) : T.IsAnc a c := by
  obtain ⟨i, rfl⟩ := hab
  obtain ⟨j, rfl⟩ := hbc
  exact ⟨i + j, by rw [Function.iterate_add_apply]⟩

theorem IsAnc.depth_le {a v : V} (h : T.IsAnc a v) : T.depth a ≤ T.depth v := by
  obtain ⟨k, rfl⟩ := h
  rw [depth_iterate]
  omega

/-- Ancestors of a vertex form a chain. -/
theorem isAnc_total {a b v : V} (ha : T.IsAnc a v) (hb : T.IsAnc b v) :
    T.IsAnc a b ∨ T.IsAnc b a := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rcases le_total i j with h | h
  · right
    exact ⟨j - i, by rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]⟩
  · left
    exact ⟨i - j, by rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]⟩

theorem isAnc_antisymm {a b : V} (hab : T.IsAnc a b) (hba : T.IsAnc b a) : a = b := by
  have h1 := hab.depth_le
  have h2 := hba.depth_le
  obtain ⟨k, rfl⟩ := hab
  rw [depth_iterate] at h1 h2
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · have hb : T.depth b = 0 := by omega
    rw [(T.depth_eq_zero_iff b).mp hb, iterate_root]

theorem isAnc_root_iff (a : V) : T.IsAnc a T.root ↔ a = T.root := by
  constructor
  · rintro ⟨k, rfl⟩
    exact T.iterate_root k
  · rintro rfl
    exact T.isAnc_refl _

/-- Ancestors of a non-root vertex: itself, or ancestors of its parent. -/
theorem isAnc_iff_of_ne_root {a v : V} (hv : v ≠ T.root) :
    T.IsAnc a v ↔ a = v ∨ T.IsAnc a (T.parent v) := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases k with _ | k
    · exact Or.inl rfl
    · exact Or.inr ⟨k, by rw [Function.iterate_succ_apply]⟩
  · rintro (rfl | h)
    · exact T.isAnc_refl _
    · exact h.trans _ (T.isAnc_parent v)

/-! ### Subtrees -/

/-- The vertices below `a`, including `a`. -/
def D (a : V) [Fintype V] : Finset V := Finset.univ.filter (T.IsAnc a)

variable [Fintype V]

@[simp] theorem mem_D (a v : V) : v ∈ T.D a ↔ T.IsAnc a v := by simp [D]

theorem self_mem_D (a : V) : a ∈ T.D a := (T.mem_D a a).mpr (T.isAnc_refl a)

theorem root_not_mem_D {a : V} (ha : a ≠ T.root) : T.root ∉ T.D a := by
  rw [mem_D, isAnc_root_iff]
  exact ha

theorem D_subset {a b : V} (h : b ∈ T.D a) : T.D b ⊆ T.D a := fun v hv =>
  (T.mem_D a v).mpr (((T.mem_D a b).mp h).trans _ ((T.mem_D b v).mp hv))

/-- Subtrees are nested or disjoint. -/
theorem D_laminar (a b : V) : Disjoint (T.D a) (T.D b) ∨ b ∈ T.D a ∨ a ∈ T.D b := by
  by_cases h : (T.D a ∩ T.D b).Nonempty
  · obtain ⟨v, hv⟩ := h
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hv
    rcases T.isAnc_total ((T.mem_D a v).mp ha) ((T.mem_D b v).mp hb) with h | h
    · exact Or.inr (Or.inl ((T.mem_D a b).mpr h))
    · exact Or.inr (Or.inr ((T.mem_D b a).mpr h))
  · exact Or.inl (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp h))

theorem D_proper {a : V} (ha : a ≠ T.root) : ProperShore (T.D a) :=
  ⟨⟨a, T.self_mem_D a⟩, fun h => T.root_not_mem_D ha (h ▸ Finset.mem_univ _)⟩

/-! ### Crossing tree edges and the parity lemma -/

/-- The parent edge of `v` has exactly one endpoint in `S`. -/
def Crosses (S : Finset V) (v : V) : Prop := v ≠ T.root ∧ ¬(v ∈ S ↔ T.parent v ∈ S)

def crossSet (S : Finset V) : Finset V := Finset.univ.filter (T.Crosses S)

/-- Crossing tree edges on the path from `v` to the root. -/
def crossAbove (S : Finset V) (v : V) : Finset V := (T.crossSet S).filter (fun u => T.IsAnc u v)

theorem crossAbove_root (S : Finset V) : T.crossAbove S T.root = ∅ := by
  ext u
  simp only [crossAbove, crossSet, Crosses, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_and]
  intro hu h
  exact absurd ((T.isAnc_root_iff u).mp h) hu.1

theorem crossAbove_of_ne_root (S : Finset V) {v : V} (hv : v ≠ T.root) :
    (T.crossAbove S v).card =
      (T.crossAbove S (T.parent v)).card + if T.Crosses S v then 1 else 0 := by
  have hset : T.crossAbove S v =
      (T.crossAbove S (T.parent v)) ∪ (if T.Crosses S v then {v} else ∅) := by
    ext u
    simp only [crossAbove, crossSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    rw [T.isAnc_iff_of_ne_root hv]
    split_ifs with hc
    · simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨hu, rfl | h⟩
        · exact Or.inr rfl
        · exact Or.inl ⟨hu, h⟩
      · rintro (⟨hu, h⟩ | rfl)
        · exact ⟨hu, Or.inr h⟩
        · exact ⟨hc, Or.inl rfl⟩
    · simp only [Finset.notMem_empty, or_false]
      constructor
      · rintro ⟨hu, rfl | h⟩
        · exact (hc hu).elim
        · exact ⟨hu, h⟩
      · rintro ⟨hu, h⟩
        exact ⟨hu, Or.inr h⟩
  have hdisj : Disjoint (T.crossAbove S (T.parent v)) (if T.Crosses S v then {v} else ∅) := by
    split_ifs
    · rw [Finset.disjoint_singleton_right]
      intro h
      have := (Finset.mem_filter.mp h).2
      have := this.depth_le
      have := T.depth_parent v hv
      omega
    · exact Finset.disjoint_empty_right _
  rw [hset, Finset.card_union_of_disjoint hdisj]
  split_ifs <;> simp

/-- **Parity lemma.** -/
theorem mem_iff_parity (S : Finset V) (v : V) :
    v ∈ S ↔ (T.root ∈ S ↔ Even (T.crossAbove S v).card) := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ d ih =>
  by_cases hv : v = T.root
  · subst hv
    rw [crossAbove_root]
    simp
  · have hp := T.depth_parent v hv
    have ih' := ih (T.depth (T.parent v)) (by omega) (T.parent v) rfl
    rw [T.crossAbove_of_ne_root S hv]
    by_cases hc : T.Crosses S v
    · simp only [hc, ↓reduceIte, Nat.even_add_one]
      have : ¬(v ∈ S ↔ T.parent v ∈ S) := hc.2
      tauto
    · simp only [hc, ↓reduceIte, add_zero]
      have : (v ∈ S ↔ T.parent v ∈ S) := by
        by_contra h
        exact hc ⟨hv, h⟩
      tauto

/-- A tree crosses every proper set. -/
theorem crossSet_nonempty {S : Finset V} (hS : ProperShore S) : (T.crossSet S).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hall : ∀ v, v ∈ S ↔ T.root ∈ S := by
    intro v
    have := T.mem_iff_parity S v
    have he : T.crossAbove S v = ∅ := by
      simp [crossAbove, h]
    rw [he] at this
    simpa using this
  obtain ⟨⟨a, ha⟩, hne⟩ := hS
  apply hne
  ext v
  simp only [Finset.mem_univ, iff_true]
  exact (hall v).mpr ((hall a).mp ha)

/-! ### Shapes of 1- and 2-respecting cuts -/

/-- With the root outside `S`, membership is the parity of crossings above. -/
theorem mem_iff_odd {S : Finset V} (hr : T.root ∉ S) (v : V) :
    v ∈ S ↔ ¬Even (T.crossAbove S v).card := by
  rw [T.mem_iff_parity S v]
  tauto

theorem eq_D_of_crossSet_one {S : Finset V} {a : V} (hr : T.root ∉ S)
    (h : T.crossSet S = {a}) : S = T.D a := by
  ext v
  rw [T.mem_iff_odd hr v, mem_D]
  have hc : T.crossAbove S v = if T.IsAnc a v then {a} else ∅ := by
    ext u
    simp only [crossAbove, h, Finset.mem_filter, Finset.mem_singleton]
    split_ifs with ha
    · simp only [Finset.mem_singleton, and_iff_left_iff_imp]
      rintro rfl
      exact ha
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro rfl
      exact ha
  rw [hc]
  split_ifs with ha <;> simp [ha]

theorem eq_symmDiff_of_crossSet_two {S : Finset V} {a b : V} (hr : T.root ∉ S) (hab : a ≠ b)
    (h : T.crossSet S = {a, b}) : ∀ v, v ∈ S ↔ ¬(v ∈ T.D a ↔ v ∈ T.D b) := by
  intro v
  rw [T.mem_iff_odd hr v, mem_D, mem_D]
  have hc : (T.crossAbove S v).card = (if T.IsAnc a v then 1 else 0) +
      (if T.IsAnc b v then 1 else 0) := by
    have : T.crossAbove S v = ({a, b} : Finset V).filter (fun u => T.IsAnc u v) := by
      simp [crossAbove, h]
    rw [this, Finset.filter_insert, Finset.filter_singleton]
    split_ifs with h1 h2 h2 <;> simp [hab]
  rw [hc]
  split_ifs with h1 h2 h2 <;> simp [h1, h2]

theorem crossSet_compl (S : Finset V) : T.crossSet Sᶜ = T.crossSet S := by
  ext v
  simp only [crossSet, Crosses, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  tauto

theorem ne_root_of_mem_crossSet {S : Finset V} {a : V} (h : a ∈ T.crossSet S) : a ≠ T.root :=
  (Finset.mem_filter.mp h).2.1

/-- **Shapes of cuts crossed by at most two tree edges.** -/
theorem two_respect_shape (G : WeightedGraph V) {S : Finset V} (hS : ProperShore S)
    (hcard : (T.crossSet S).card ≤ 2) :
    (∃ a, a ≠ T.root ∧ G.cut S = G.cut (T.D a)) ∨
    (∃ a b, a ≠ T.root ∧ b ≠ T.root ∧ a ≠ b ∧ Disjoint (T.D a) (T.D b) ∧
      G.cut S = G.cut (T.D a ∪ T.D b)) ∨
    (∃ a b, a ≠ T.root ∧ b ≠ T.root ∧ b ≠ a ∧ b ∈ T.D a ∧
      G.cut S = G.cut (T.D a \ T.D b)) := by
  -- Work with the side not containing the root.
  wlog hr : T.root ∉ S generalizing S
  · have hc : ProperShore Sᶜ := ⟨by
        obtain ⟨_, hne⟩ := hS
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hne (by rw [← compl_compl S, h, Finset.compl_empty]), by
        intro h
        obtain ⟨⟨a, ha⟩, _⟩ := hS
        have : a ∈ Sᶜ := h ▸ Finset.mem_univ a
        exact (Finset.mem_compl.mp this) ha⟩
    have := this hc (by rwa [crossSet_compl]) (by simpa using hr)
    simpa only [WeightedGraph.cut_compl, crossSet_compl] using this
  have hne := T.crossSet_nonempty hS
  rcases Nat.lt_or_ge (T.crossSet S).card 2 with h1 | h2
  · have h1' : (T.crossSet S).card = 1 := by have := hne.card_pos; omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1'
    left
    exact ⟨a, T.ne_root_of_mem_crossSet (by rw [ha]; simp),
      by rw [T.eq_D_of_crossSet_one hr ha]⟩
  · obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp (le_antisymm hcard h2)
    have ha : a ≠ T.root := T.ne_root_of_mem_crossSet (by rw [hset]; simp)
    have hb : b ≠ T.root := T.ne_root_of_mem_crossSet (by rw [hset]; simp)
    have hmem := T.eq_symmDiff_of_crossSet_two hr hab hset
    rcases T.D_laminar a b with hd | hba | hab'
    · right; left
      refine ⟨a, b, ha, hb, hab, hd, ?_⟩
      congr 1
      ext v
      rw [hmem v, Finset.mem_union]
      have hdv : v ∈ T.D a → v ∉ T.D b := fun h => Finset.disjoint_left.mp hd h
      tauto
    · right; right
      refine ⟨a, b, ha, hb, Ne.symm hab, hba, ?_⟩
      congr 1
      ext v
      rw [hmem v, Finset.mem_sdiff]
      have hsub : v ∈ T.D b → v ∈ T.D a := fun h => T.D_subset hba h
      tauto
    · right; right
      refine ⟨b, a, hb, ha, hab, hab', ?_⟩
      congr 1
      ext v
      rw [hmem v, Finset.mem_sdiff]
      have hsub : v ∈ T.D a → v ∈ T.D b := fun h => T.D_subset hab' h
      tauto

end
end RootedTree
end CutQueryComplexity
