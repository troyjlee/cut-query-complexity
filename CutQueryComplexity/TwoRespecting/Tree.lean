import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Basic
import Mathlib.Data.List.Lex

/-! # Rooted spanning trees, subtrees, and a preorder

A rooted tree on `V` is given by a parent map and a depth function witnessing
acyclicity. Every vertex is in the tree. Ancestry is reflexive. The descendant
set `subtree v` is the shore of the tree edge above `v`.

`rootPath v` lists the ancestors of `v` from the root. Comparing root paths
lexicographically gives a depth-first preorder: ancestors precede descendants,
and every subtree is an interval (`isAnc_of_between`). This is the only property
of the preorder used by the majority-subtree search.
-/

namespace CutQueryComplexity
namespace TwoRespecting

/-- A rooted spanning tree on `V`. -/
structure RootedTree (V : Type) where
  root : V
  parent : V → V
  depth : V → ℕ
  parent_root : parent root = root
  depth_root : depth root = 0
  depth_parent : ∀ v, v ≠ root → depth (parent v) + 1 = depth v

namespace RootedTree

variable {V : Type} (T : RootedTree V)

/-- `u` is an ancestor of `v`, reflexively. -/
def IsAnc (u v : V) : Prop := ∃ k, T.parent^[k] v = u

variable {T}

theorem eq_root_of_depth_eq_zero {v : V} (h : T.depth v = 0) : v = T.root := by
  by_contra hv
  have := T.depth_parent v hv
  omega

theorem depth_pos {v : V} (hv : v ≠ T.root) : 0 < T.depth v := by
  have := T.depth_parent v hv
  omega

theorem depth_iterate (v : V) : ∀ k, k ≤ T.depth v →
    T.depth (T.parent^[k] v) = T.depth v - k
  | 0, _ => by simp
  | k + 1, hk => by
      rw [Function.iterate_succ_apply']
      have ih := depth_iterate v k (by omega)
      have hne : T.parent^[k] v ≠ T.root := by
        intro h
        rw [h, T.depth_root] at ih
        omega
      have := T.depth_parent _ hne
      omega

theorem iterate_depth (v : V) : T.parent^[T.depth v] v = T.root :=
  eq_root_of_depth_eq_zero (by rw [depth_iterate v _ le_rfl]; simp)

theorem iterate_root (k : ℕ) : T.parent^[k] T.root = T.root :=
  Function.iterate_fixed T.parent_root k

theorem iterate_of_depth_le (v : V) {k : ℕ} (hk : T.depth v ≤ k) :
    T.parent^[k] v = T.root := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm, Function.iterate_add_apply, iterate_depth, iterate_root]

@[refl] theorem isAnc_refl (v : V) : T.IsAnc v v := ⟨0, rfl⟩

theorem isAnc_trans {u v w : V} (h₁ : T.IsAnc u v) (h₂ : T.IsAnc v w) : T.IsAnc u w := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  exact ⟨a + b, by rw [Function.iterate_add_apply]⟩

theorem isAnc_root (v : V) : T.IsAnc T.root v := ⟨T.depth v, iterate_depth v⟩

theorem isAnc_parent (v : V) : T.IsAnc (T.parent v) v := ⟨1, rfl⟩

theorem IsAnc.depth_le {u v : V} (h : T.IsAnc u v) : T.depth u ≤ T.depth v := by
  obtain ⟨k, rfl⟩ := h
  by_cases hk : k ≤ T.depth v
  · rw [depth_iterate v k hk]; omega
  · rw [iterate_of_depth_le v (by omega), T.depth_root]; omega

/-- An ancestor is determined by its depth. -/
theorem IsAnc.eq_iterate {u v : V} (h : T.IsAnc u v) :
    u = T.parent^[T.depth v - T.depth u] v := by
  obtain ⟨k, rfl⟩ := h
  by_cases hk : k ≤ T.depth v
  · rw [depth_iterate v k hk]
    congr 1
    omega
  · rw [iterate_of_depth_le v (by omega), T.depth_root, Nat.sub_zero, iterate_depth]

theorem isAnc_antisymm {u v : V} (h₁ : T.IsAnc u v) (h₂ : T.IsAnc v u) : u = v := by
  have hd := le_antisymm h₁.depth_le h₂.depth_le
  rw [h₁.eq_iterate, hd, Nat.sub_self, Function.iterate_zero_apply]

/-- Two ancestors of a common vertex are comparable. -/
theorem isAnc_total_of_common {u u' x : V} (h : T.IsAnc u x) (h' : T.IsAnc u' x) :
    T.IsAnc u u' ∨ T.IsAnc u' u := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, rfl⟩ := h'
  rcases le_total a b with hab | hab
  · right
    exact ⟨b - a, by rw [← Function.iterate_add_apply]; congr 1; omega⟩
  · left
    exact ⟨a - b, by rw [← Function.iterate_add_apply]; congr 1; omega⟩

/-- A proper ancestor of `v` is an ancestor of its parent. -/
theorem IsAnc.isAnc_parent_of_ne {u v : V} (h : T.IsAnc u v) (hne : u ≠ v) :
    T.IsAnc u (T.parent v) := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | zero => exact absurd rfl hne
  | succ k => exact ⟨k, by rw [Function.iterate_succ_apply]⟩

theorem IsAnc.eq_root_of_isAnc_root {v : V} (h : T.IsAnc v T.root) : v = T.root :=
  isAnc_antisymm h (isAnc_root v)

theorem isAnc_iff_eq_or_isAnc_parent {u v : V} :
    T.IsAnc u v ↔ u = v ∨ (v ≠ T.root ∧ T.IsAnc u (T.parent v)) := by
  constructor
  · intro h
    by_cases huv : u = v
    · exact Or.inl huv
    · refine Or.inr ⟨fun hv => huv ?_, h.isAnc_parent_of_ne huv⟩
      subst hv
      exact h.eq_root_of_isAnc_root
  · rintro (rfl | ⟨-, h⟩)
    · exact isAnc_refl u
    · exact isAnc_trans h (isAnc_parent v)

theorem parent_ne_self {v : V} (hv : v ≠ T.root) : T.parent v ≠ v := by
  intro h
  have := T.depth_parent v hv
  rw [h] at this
  omega

theorem isAnc_iff_iterate {u v : V} :
    T.IsAnc u v ↔ T.depth u ≤ T.depth v ∧ T.parent^[T.depth v - T.depth u] v = u :=
  ⟨fun h => ⟨h.depth_le, h.eq_iterate.symm⟩, fun h => ⟨_, h.2⟩⟩

instance decIsAnc [DecidableEq V] (T : RootedTree V) : DecidableRel T.IsAnc := fun _ _ =>
  decidable_of_iff _ isAnc_iff_iterate.symm

section Finite

variable [Fintype V] [DecidableEq V]

open Classical in
/-- The descendants of `v`, including `v`: the shore of the tree edge above `v`. -/
noncomputable def subtree (T : RootedTree V) (v : V) : Finset V :=
  Finset.univ.filter (T.IsAnc v)

@[simp] theorem mem_subtree {v x : V} : x ∈ T.subtree v ↔ T.IsAnc v x := by
  classical
  simp [subtree]

theorem self_mem_subtree (v : V) : v ∈ T.subtree v := mem_subtree.mpr (isAnc_refl v)

theorem subtree_root : T.subtree T.root = Finset.univ := by
  ext x; simp [isAnc_root]

theorem subtree_subset {u v : V} (h : T.IsAnc u v) : T.subtree v ⊆ T.subtree u :=
  fun _ hx => mem_subtree.mpr (isAnc_trans h (mem_subtree.mp hx))

/-- Subtrees of incomparable vertices are disjoint. -/
theorem disjoint_subtree {u v : V} (h₁ : ¬ T.IsAnc u v) (h₂ : ¬ T.IsAnc v u) :
    Disjoint (T.subtree u) (T.subtree v) := by
  rw [Finset.disjoint_left]
  intro x hu hv
  rcases isAnc_total_of_common (mem_subtree.mp hu) (mem_subtree.mp hv) with h | h
  · exact h₁ h
  · exact h₂ h

theorem subtree_ssubset {u v : V} (h : T.IsAnc u v) (hne : u ≠ v) :
    T.subtree v ⊂ T.subtree u := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subtree_subset h, fun heq => hne ?_⟩
  have : u ∈ T.subtree v := heq ▸ self_mem_subtree u
  exact isAnc_antisymm h (mem_subtree.mp this)

theorem subtree_ne_univ {v : V} (hv : v ≠ T.root) : T.subtree v ≠ Finset.univ := by
  intro h
  have : T.root ∈ T.subtree v := h ▸ Finset.mem_univ _
  exact hv (mem_subtree.mp this).eq_root_of_isAnc_root

theorem subtree_nonempty (v : V) : (T.subtree v).Nonempty := ⟨v, self_mem_subtree v⟩

end Finite

/-! ### Root paths and the preorder -/

section RootPath

variable [DecidableEq V]

/-- The ancestors of `v`, listed from the root down to `v`. -/
def rootPath (T : RootedTree V) (v : V) : List V :=
  if _h : v = T.root then [T.root] else T.rootPath (T.parent v) ++ [v]
termination_by T.depth v
decreasing_by have := T.depth_parent v _h; omega

theorem rootPath_root : T.rootPath T.root = [T.root] := by
  rw [rootPath]; simp

theorem rootPath_of_ne {v : V} (hv : v ≠ T.root) :
    T.rootPath v = T.rootPath (T.parent v) ++ [v] := by
  rw [rootPath]; simp [hv]

theorem mem_rootPath {v x : V} : x ∈ T.rootPath v ↔ T.IsAnc x v := by
  induction hd : T.depth v generalizing v with
  | zero =>
      have hv := eq_root_of_depth_eq_zero hd
      subst hv
      rw [rootPath_root, List.mem_singleton]
      exact ⟨fun h => h ▸ isAnc_refl _, fun h => h.eq_root_of_isAnc_root⟩
  | succ d ih =>
      have hv : v ≠ T.root := by
        intro h; rw [h, T.depth_root] at hd; omega
      have hdp : T.depth (T.parent v) = d := by have := T.depth_parent v hv; omega
      rw [rootPath_of_ne hv, List.mem_append, ih hdp, List.mem_singleton]
      constructor
      · rintro (h | rfl)
        · exact isAnc_trans h (isAnc_parent v)
        · exact isAnc_refl x
      · intro h
        by_cases hxv : x = v
        · exact Or.inr hxv
        · exact Or.inl (h.isAnc_parent_of_ne hxv)

theorem self_mem_rootPath (v : V) : v ∈ T.rootPath v := mem_rootPath.mpr (isAnc_refl v)

theorem rootPath_prefix {u v : V} (h : T.IsAnc u v) : T.rootPath u <+: T.rootPath v := by
  induction hd : T.depth v generalizing v with
  | zero =>
      have hv := eq_root_of_depth_eq_zero hd
      subst hv
      rw [h.eq_root_of_isAnc_root]
  | succ d ih =>
      by_cases huv : u = v
      · rw [huv]
      · have hv : v ≠ T.root := by
          intro h'; rw [h', T.depth_root] at hd; omega
        have hdp : T.depth (T.parent v) = d := by have := T.depth_parent v hv; omega
        rw [rootPath_of_ne hv]
        exact (ih (h.isAnc_parent_of_ne huv) hdp).trans (List.prefix_append _ _)

theorem rootPath_injective : Function.Injective T.rootPath := by
  intro u v h
  have h₁ : T.IsAnc u v := mem_rootPath.mp (h ▸ self_mem_rootPath u)
  have h₂ : T.IsAnc v u := mem_rootPath.mp (h ▸ self_mem_rootPath v)
  exact isAnc_antisymm h₁ h₂

end RootPath

section ListOrder

variable {α : Type} [LinearOrder α]

theorem List.le_of_prefix : ∀ {p x : List α}, p <+: x → p ≤ x
  | [], _, _ => not_lt.mp (List.not_lt_nil _)
  | a :: p, x, h => by
      obtain ⟨t, rfl⟩ := h
      refine not_lt.mp fun hlt => ?_
      rw [List.cons_append, List.cons_lt_cons_iff] at hlt
      rcases hlt with hlt | ⟨-, hlt⟩
      · exact lt_irrefl a hlt
      · exact absurd (List.le_of_prefix (List.prefix_append p t)) (not_le.mpr hlt)

/-- Lists sharing a prefix form an interval in the lexicographic order. -/
theorem List.prefix_of_between : ∀ {p x y z : List α}, p <+: x → p <+: z → x ≤ y → y ≤ z →
    p <+: y
  | [], _, _, _, _, _, _, _ => List.nil_prefix
  | a :: p, x, y, z, hx, hz, hxy, hyz => by
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨z', rfl⟩ := hz
      cases y with
      | nil => exact absurd hxy (not_le.mpr (List.nil_lt_cons _ _))
      | cons b y' =>
          rw [← not_lt, List.cons_append, List.cons_lt_cons_iff] at hxy hyz
          have hab : a = b := by
            rcases lt_trichotomy a b with h | h | h
            · exact absurd (Or.inl h) hyz
            · exact h
            · exact absurd (Or.inl h) hxy
          subst hab
          have hxy' : p ++ x' ≤ y' := not_lt.mp fun h => hxy (Or.inr ⟨rfl, h⟩)
          have hyz' : y' ≤ p ++ z' := not_lt.mp fun h => hyz (Or.inr ⟨rfl, h⟩)
          exact (List.prefix_cons_inj a).mpr
            (List.prefix_of_between (List.prefix_append p x') (List.prefix_append p z') hxy' hyz')

end ListOrder

section Preorder

variable [DecidableEq V] [LinearOrder V]

/-- Ancestors precede descendants in the preorder. -/
theorem rootPath_le_of_isAnc {u v : V} (h : T.IsAnc u v) : T.rootPath u ≤ T.rootPath v :=
  List.le_of_prefix (rootPath_prefix h)

theorem rootPath_lt_of_isAnc {u v : V} (h : T.IsAnc u v) (hne : u ≠ v) :
    T.rootPath u < T.rootPath v :=
  lt_of_le_of_ne (rootPath_le_of_isAnc h) (fun he => hne (rootPath_injective he))

/-- Every subtree is an interval of the preorder. -/
theorem isAnc_of_between {u x y z : V} (hx : T.IsAnc u x) (hz : T.IsAnc u z)
    (hxy : T.rootPath x ≤ T.rootPath y) (hyz : T.rootPath y ≤ T.rootPath z) :
    T.IsAnc u y :=
  mem_rootPath.mp ((List.prefix_of_between (rootPath_prefix hx) (rootPath_prefix hz)
    hxy hyz).subset (self_mem_rootPath u))

/-- On comparable vertices, the preorder is the ancestry order. -/
theorem isAnc_of_rootPath_le {u v : V} (hc : T.IsAnc u v ∨ T.IsAnc v u)
    (hle : T.rootPath u ≤ T.rootPath v) : T.IsAnc u v := by
  rcases hc with h | h
  · exact h
  · by_cases huv : v = u
    · exact huv ▸ isAnc_refl v
    · exact absurd hle (not_le.mpr (rootPath_lt_of_isAnc h huv))

end Preorder

end RootedTree

/-- Vertices of `T` carrying the depth-first preorder of root paths. -/
def Pre {V : Type} (_T : RootedTree V) : Type := V

namespace Pre

variable {V : Type} {T : RootedTree V}

/-- View a vertex in the preorder. -/
def of (T : RootedTree V) (v : V) : Pre T := v

/-- The underlying vertex. -/
def val (v : Pre T) : V := v

instance [DecidableEq V] : DecidableEq (Pre T) := inferInstanceAs (DecidableEq V)

instance [Fintype V] : Fintype (Pre T) := inferInstanceAs (Fintype V)

noncomputable instance [DecidableEq V] [LinearOrder V] : LinearOrder (Pre T) :=
  LinearOrder.lift' (fun v : Pre T => T.rootPath (val v)) RootedTree.rootPath_injective

theorem le_iff [DecidableEq V] [LinearOrder V] {u v : Pre T} : u ≤ v ↔ T.rootPath u.val ≤ T.rootPath v.val := Iff.rfl

theorem lt_iff [DecidableEq V] [LinearOrder V] {u v : Pre T} : u < v ↔ T.rootPath u.val < T.rootPath v.val := Iff.rfl

@[simp] theorem val_of (v : V) : (of T v).val = v := rfl

@[simp] theorem of_val (v : Pre T) : of T v.val = v := rfl

end Pre

end TwoRespecting
end CutQueryComplexity
