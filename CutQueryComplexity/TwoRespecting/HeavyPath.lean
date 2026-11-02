import CutQueryComplexity.TwoRespecting.Tree
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-! # Heavy-path decomposition of the tree edges

Tree edges are identified with non-root vertices. At every vertex the child of
largest subtree (ties broken by the vertex order) is heavy. A *top* vertex is a
non-root vertex that is light or a child of the root; `head v` is the nearest top
ancestor of `v`. The paths `{v | head v = h}` partition the non-root vertices.

Main facts:
* `head_eq_of_between`: a path is convex along root paths;
* `isAnc_total_of_head_eq`: each path is a chain;
* `card_headsAbove_le`: the non-root ancestors of any vertex meet at most
  `Nat.log 2 n + 1` paths.
-/

namespace CutQueryComplexity
namespace TwoRespecting
namespace RootedTree

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (T : RootedTree V)

/-- Number of vertices in the subtree of `v`. -/
noncomputable def size (v : V) : ℕ := (T.subtree v).card

/-- `v` is the heavy child of its parent. -/
def IsHeavy (v : V) : Prop :=
  v ≠ T.root ∧ ∀ u, u ≠ T.root → T.parent u = T.parent v →
    T.size u < T.size v ∨ (T.size u = T.size v ∧ v ≤ u)

/-- `v` starts a heavy path: it is light or a child of the root. -/
def IsTop (v : V) : Prop := v ≠ T.root ∧ (¬ T.IsHeavy v ∨ T.parent v = T.root)

variable {T}

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
/-- An ancestor at the same or greater depth is the vertex itself. -/
theorem eq_of_isAnc_of_depth_le {u v : V} (h : T.IsAnc u v) (hd : T.depth v ≤ T.depth u) :
    u = v := by
  have hd' : T.depth v - T.depth u = 0 := by omega
  rw [h.eq_iterate, hd', Function.iterate_zero_apply]

omit [LinearOrder V] in
theorem size_pos (v : V) : 0 < T.size v := Finset.card_pos.mpr (subtree_nonempty v)

omit [LinearOrder V] in
theorem size_le_card (v : V) : T.size v ≤ Fintype.card V := Finset.card_le_univ _

omit [LinearOrder V] in
theorem size_root : T.size T.root = Fintype.card V := by
  simp [size, subtree_root]

omit [LinearOrder V] in
theorem size_le_of_isAnc {u v : V} (h : T.IsAnc u v) : T.size v ≤ T.size u :=
  Finset.card_le_card (subtree_subset h)

theorem heavy_unique {u v : V} (hu : T.IsHeavy u) (hv : T.IsHeavy v)
    (hp : T.parent u = T.parent v) : u = v := by
  rcases hv.2 u hu.1 hp with h | ⟨h1, h2⟩
  · rcases hu.2 v hv.1 hp.symm with h' | ⟨h1', _⟩ <;> omega
  · rcases hu.2 v hv.1 hp.symm with h' | ⟨_, h2'⟩
    · omega
    · exact le_antisymm h2' h2

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
/-- Distinct children of one vertex are incomparable. -/
theorem not_isAnc_of_siblings {u v : V} (hu : u ≠ T.root) (_hv : v ≠ T.root)
    (hp : T.parent u = T.parent v) (hne : u ≠ v) : ¬ T.IsAnc u v := by
  intro h
  have h' := h.isAnc_parent_of_ne hne
  rw [← hp] at h'
  have := h'.depth_le
  have := T.depth_parent u hu
  omega

/-- A light child has less than half of its parent's subtree. -/
theorem two_mul_size_lt_of_light {v : V} (hv : v ≠ T.root) (hl : ¬ T.IsHeavy v) :
    2 * T.size v < T.size (T.parent v) := by
  unfold IsHeavy at hl
  push Not at hl
  obtain ⟨u, hu, hp, hbig⟩ := hl hv
  have huv : u ≠ v := fun h => by subst h; exact lt_irrefl _ (hbig.2 rfl)
  have hsz : T.size v ≤ T.size u := hbig.1
  have hdisj : Disjoint (T.subtree u) (T.subtree v) :=
    disjoint_subtree (not_isAnc_of_siblings hu hv hp huv)
      (not_isAnc_of_siblings hv hu hp.symm huv.symm)
  have hsub : T.subtree u ∪ T.subtree v ⊆ (T.subtree (T.parent v)).erase (T.parent v) := by
    intro x hx
    rw [Finset.mem_erase, mem_subtree]
    rcases Finset.mem_union.mp hx with hx | hx
    · have hux := mem_subtree.mp hx
      refine ⟨fun h => ?_, hp ▸ isAnc_trans (isAnc_parent u) hux⟩
      subst h
      have := hux.depth_le
      have := T.depth_parent u hu
      rw [hp] at this
      omega
    · have hvx := mem_subtree.mp hx
      refine ⟨fun h => ?_, isAnc_trans (isAnc_parent v) hvx⟩
      subst h
      have := hvx.depth_le
      have := T.depth_parent v hv
      omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (self_mem_subtree _)] at this
  have h2 : (T.subtree v).card ≤ (T.subtree u).card := hsz
  have h3 : 0 < (T.subtree (T.parent v)).card := Finset.card_pos.mpr (subtree_nonempty _)
  show 2 * (T.subtree v).card < (T.subtree (T.parent v)).card
  omega

theorem exists_top {v : V} (hv : v ≠ T.root) : ∃ k, T.IsTop (T.parent^[k] v) := by
  refine ⟨T.depth v - 1, ?_, Or.inr ?_⟩
  · intro h
    have := depth_iterate (T := T) v (T.depth v - 1) (by omega)
    rw [h, T.depth_root] at this
    have := depth_pos hv
    omega
  · apply eq_root_of_depth_eq_zero
    have hne : T.parent^[T.depth v - 1] v ≠ T.root := by
      intro h
      have := depth_iterate (T := T) v (T.depth v - 1) (by omega)
      rw [h, T.depth_root] at this
      have := depth_pos hv
      omega
    have h1 := depth_iterate (T := T) v (T.depth v - 1) (by omega)
    have h2 := T.depth_parent _ hne
    have := depth_pos hv
    omega

variable (T)

open Classical in
/-- The top of the heavy path containing the edge above `v`. -/
noncomputable def head (v : V) : V :=
  if hv : v = T.root then T.root else T.parent^[Nat.find (exists_top hv)] v

variable {T}

theorem head_spec {v : V} (hv : v ≠ T.root) :
    T.IsTop (T.head v) ∧ T.IsAnc (T.head v) v ∧
      ∀ w, T.IsAnc (T.head v) w → T.IsAnc w v → w ≠ T.head v → ¬ T.IsTop w := by
  classical
  have hdef : T.head v = T.parent^[Nat.find (exists_top hv)] v := by
    simp [head, hv]
  refine ⟨hdef ▸ Nat.find_spec (exists_top hv), ⟨_, hdef.symm⟩, ?_⟩
  intro w hhw hwv hne htop
  obtain ⟨j, rfl⟩ := hwv
  have hk : j < Nat.find (exists_top hv) := by
    by_contra hge
    push Not at hge
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hge
    have : T.IsAnc (T.parent^[j] v) (T.head v) :=
      ⟨m, by rw [hdef, hm, add_comm, Function.iterate_add_apply]⟩
    exact hne (isAnc_antisymm this hhw)
  exact Nat.find_min (exists_top hv) hk htop

theorem head_ne_root {v : V} (hv : v ≠ T.root) : T.head v ≠ T.root := (head_spec hv).1.1

theorem isAnc_head {v : V} (hv : v ≠ T.root) : T.IsAnc (T.head v) v := (head_spec hv).2.1

/-- Characterization of the head as the nearest top ancestor. -/
theorem head_eq_of {v x : V} (hv : v ≠ T.root) (hx : T.IsTop x) (hxv : T.IsAnc x v)
    (hbetween : ∀ w, T.IsAnc x w → T.IsAnc w v → w ≠ x → ¬ T.IsTop w) : T.head v = x := by
  obtain ⟨htop, hanc, hmin⟩ := head_spec hv
  rcases isAnc_total_of_common hanc hxv with h | h
  · by_contra hne
    exact hmin x h hxv (Ne.symm hne) hx
  · by_contra hne
    exact hbetween _ h hanc hne htop

/-- Paths are convex: every vertex between a head and a path member is on the path. -/
theorem head_eq_of_between {v w : V} (hv : v ≠ T.root) (hhw : T.IsAnc (T.head v) w)
    (hwv : T.IsAnc w v) : T.head w = T.head v := by
  have hw : w ≠ T.root := fun h => head_ne_root hv
    (isAnc_antisymm (h ▸ hhw) (isAnc_root _))
  obtain ⟨htop, -, hmin⟩ := head_spec hv
  exact head_eq_of hw htop hhw fun u hu huw hne => hmin u hu (isAnc_trans huw hwv) hne

/-- A non-top non-root vertex continues its parent's path. -/
theorem head_eq_head_parent {v : V} (hv : v ≠ T.root) (hnt : ¬ T.IsTop v) :
    T.head v = T.head (T.parent v) := by
  have hne : T.head v ≠ v := fun h => hnt (h ▸ (head_spec hv).1)
  exact (head_eq_of_between hv ((isAnc_head hv).isAnc_parent_of_ne hne)
    (isAnc_parent v)).symm

/-- Each heavy path is a chain. -/
theorem isAnc_of_head_eq_of_depth_le : ∀ (n : ℕ) {u v : V}, T.depth v ≤ n →
    u ≠ T.root → v ≠ T.root → T.head u = T.head v → T.depth u ≤ T.depth v → T.IsAnc u v
  | 0, u, v, hd, _, hv, _, _ => absurd (eq_root_of_depth_eq_zero (Nat.le_zero.mp hd)) hv
  | n + 1, u, v, hd, hu, hv, hh, hdu => by
      by_cases hvtop : T.IsTop v
      · -- `v` is its own head, and `u` lies below it
        have hvh : T.head v = v :=
          head_eq_of hv hvtop (isAnc_refl v) fun w hw hwv hne =>
            absurd (isAnc_antisymm hw hwv) (Ne.symm hne)
        have huv : T.IsAnc v u := hvh ▸ hh ▸ isAnc_head hu
        have heq : v = u := eq_of_isAnc_of_depth_le huv hdu
        exact heq ▸ isAnc_refl v
      · have hpv : T.parent v ≠ T.root := by
          intro h
          exact hvtop ⟨hv, Or.inr h⟩
        have hvheavy : T.IsHeavy v := by
          by_contra hl
          exact hvtop ⟨hv, Or.inl hl⟩
        have hhp : T.head (T.parent v) = T.head v := (head_eq_head_parent hv hvtop).symm
        have hdp : T.depth (T.parent v) ≤ n := by have := T.depth_parent v hv; omega
        rcases Nat.lt_or_ge (T.depth u) (T.depth v) with hlt | hge
        · have hdu' : T.depth u ≤ T.depth (T.parent v) := by
            have := T.depth_parent v hv; omega
          exact isAnc_trans (isAnc_of_head_eq_of_depth_le n hdp hu hpv (hh.trans hhp.symm)
            hdu') (isAnc_parent v)
        · -- equal depths: `u` is also a heavy non-top vertex, and the parents coincide
          have hdeq : T.depth u = T.depth v := le_antisymm hdu hge
          have hutop : ¬ T.IsTop u := by
            intro hut
            have huh : T.head u = u :=
              head_eq_of hu hut (isAnc_refl u) fun w hw hwu hne =>
                absurd (isAnc_antisymm hw hwu) (Ne.symm hne)
            have hanc : T.IsAnc u v := huh ▸ hh ▸ isAnc_head hv
            have heq : u = v := eq_of_isAnc_of_depth_le hanc hdeq.ge
            exact hvtop (heq ▸ hut)
          have hpu : T.parent u ≠ T.root := fun h => hutop ⟨hu, Or.inr h⟩
          have huheavy : T.IsHeavy u := by
            by_contra hl
            exact hutop ⟨hu, Or.inl hl⟩
          have hhpu : T.head (T.parent u) = T.head u := (head_eq_head_parent hu hutop).symm
          have hdpu : T.depth (T.parent u) = T.depth (T.parent v) := by
            have := T.depth_parent u hu; have := T.depth_parent v hv; omega
          have hpanc := isAnc_of_head_eq_of_depth_le n hdp hpu hpv
            (hhpu.trans (hh.trans hhp.symm)) hdpu.le
          have hpeq : T.parent u = T.parent v := eq_of_isAnc_of_depth_le hpanc hdpu.ge
          exact heavy_unique huheavy hvheavy hpeq ▸ isAnc_refl u

theorem isAnc_total_of_head_eq {u v : V} (hu : u ≠ T.root) (hv : v ≠ T.root)
    (hh : T.head u = T.head v) : T.IsAnc u v ∨ T.IsAnc v u := by
  rcases le_total (T.depth u) (T.depth v) with h | h
  · exact Or.inl (isAnc_of_head_eq_of_depth_le _ le_rfl hu hv hh h)
  · exact Or.inr (isAnc_of_head_eq_of_depth_le _ le_rfl hv hu hh.symm h)

/-! ### Counting paths on a root path -/

variable (T)

open Classical in
/-- Light non-root ancestors of `v`. -/
noncomputable def lightAbove (v : V) : Finset V :=
  Finset.univ.filter fun w => w ≠ T.root ∧ ¬ T.IsHeavy w ∧ T.IsAnc w v

open Classical in
/-- Heads of the paths met by the non-root ancestors of `v`. -/
noncomputable def headsAbove (v : V) : Finset V :=
  (Finset.univ.filter fun w => w ≠ T.root ∧ T.IsAnc w v).image T.head

variable {T}

theorem pow_card_lightAbove_mul_size : ∀ (n : ℕ) (v : V), T.depth v ≤ n →
    2 ^ (T.lightAbove v).card * T.size v ≤ Fintype.card V
  | 0, v, hd => by
      have hv := eq_root_of_depth_eq_zero (Nat.le_zero.mp hd)
      subst hv
      have : T.lightAbove T.root = ∅ := by
        ext w
        simp only [lightAbove, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and]
        intro hw _ hanc
        exact hw hanc.eq_root_of_isAnc_root
      rw [this, size_root]; simp
  | n + 1, v, hd => by
      by_cases hv : v = T.root
      · subst hv; exact pow_card_lightAbove_mul_size 0 T.root (by rw [T.depth_root])
      have hdp : T.depth (T.parent v) ≤ n := by have := T.depth_parent v hv; omega
      have ih := pow_card_lightAbove_mul_size n (T.parent v) hdp
      have hsub : T.lightAbove v ⊆ insert v (T.lightAbove (T.parent v)) := by
        intro w hw
        simp only [lightAbove, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert] at hw ⊢
        rcases isAnc_iff_eq_or_isAnc_parent.mp hw.2.2 with h | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨hw.1, hw.2.1, h⟩
      by_cases hl : T.IsHeavy v
      · have heq : T.lightAbove v ⊆ T.lightAbove (T.parent v) := by
          intro w hw
          rcases Finset.mem_insert.mp (hsub hw) with rfl | h
          · simp [lightAbove] at hw; exact absurd hl hw.2.1
          · exact h
        have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) (Finset.card_le_card heq)
        have h2 := size_le_of_isAnc (isAnc_parent (T := T) v)
        calc 2 ^ (T.lightAbove v).card * T.size v
            ≤ 2 ^ (T.lightAbove (T.parent v)).card * T.size (T.parent v) :=
              Nat.mul_le_mul h1 h2
          _ ≤ Fintype.card V := ih
      · have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        have h2 := two_mul_size_lt_of_light hv hl
        calc 2 ^ (T.lightAbove v).card * T.size v
            ≤ 2 ^ ((T.lightAbove (T.parent v)).card + 1) * T.size v :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hc)
          _ = 2 ^ (T.lightAbove (T.parent v)).card * (2 * T.size v) := by
              rw [Nat.pow_succ]; ring
          _ ≤ 2 ^ (T.lightAbove (T.parent v)).card * T.size (T.parent v) :=
              Nat.mul_le_mul_left _ h2.le
          _ ≤ Fintype.card V := ih

theorem card_lightAbove_le (v : V) : (T.lightAbove v).card ≤ Nat.log 2 (Fintype.card V) := by
  apply Nat.le_log_of_pow_le (by decide)
  have := pow_card_lightAbove_mul_size (T := T) _ v le_rfl
  have := size_pos (T := T) v
  calc 2 ^ (T.lightAbove v).card ≤ 2 ^ (T.lightAbove v).card * T.size v :=
        Nat.le_mul_of_pos_right _ (size_pos v)
    _ ≤ _ := by assumption

/-- Any root path meets at most `Nat.log 2 n + 1` heavy paths. -/
theorem card_headsAbove_le (v : V) : (T.headsAbove v).card ≤ Nat.log 2 (Fintype.card V) + 1 := by
  classical
  -- every head above `v` is a top ancestor of `v`: light, or the child of the root on the path
  let R : Finset V := Finset.univ.filter fun w => w ≠ T.root ∧ T.parent w = T.root ∧ T.IsAnc w v
  have hR : R.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hda : T.depth a = 1 := by
      have := T.depth_parent a ha.1; rw [ha.2.1, T.depth_root] at this; omega
    have hdb : T.depth b = 1 := by
      have := T.depth_parent b hb.1; rw [hb.2.1, T.depth_root] at this; omega
    rcases isAnc_total_of_common ha.2.2 hb.2.2 with h | h
    · exact eq_of_isAnc_of_depth_le h (by omega)
    · exact (eq_of_isAnc_of_depth_le h (by omega)).symm
  have hsub : T.headsAbove v ⊆ T.lightAbove v ∪ R := by
    intro h hh
    simp only [headsAbove, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hh
    obtain ⟨w, ⟨hw, hwv⟩, rfl⟩ := hh
    obtain ⟨⟨hne, hor⟩, hanc, -⟩ := head_spec hw
    have hhv := isAnc_trans hanc hwv
    rcases hor with hl | hp
    · exact Finset.mem_union_left _ (by simp [lightAbove, hne, hl, hhv])
    · exact Finset.mem_union_right _ (by simp [R, hne, hp, hhv])
  calc (T.headsAbove v).card ≤ (T.lightAbove v ∪ R).card := Finset.card_le_card hsub
    _ ≤ (T.lightAbove v).card + R.card := Finset.card_union_le _ _
    _ ≤ Nat.log 2 (Fintype.card V) + 1 := by have := card_lightAbove_le (T := T) v; omega

end RootedTree
end TwoRespecting
end CutQueryComplexity
