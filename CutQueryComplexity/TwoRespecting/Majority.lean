import CutQueryComplexity.TwoRespecting.Tree
import CutQueryComplexity.Search.BinarySearch
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Majority-subtree search (Lemma 36 of the deterministic mincut paper)

Let `μ` be a monotone set function on the vertices whose values on disjoint sets
add to at most the total `D = μ univ > 0`. A vertex is *heavy* if its subtree
has `μ`-mass more than `D/2`. The heavy vertices are exactly the ancestors of
one vertex `c`. `majoritySearch` finds `c` by two binary searches: first over
preorder prefixes, then along a root path. Each step evaluates `μ` once.
-/

namespace CutQueryComplexity
namespace TwoRespecting

open Search Search.Comp RootedTree

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- A monotone, subadditive-on-disjoint-sets set function. -/
structure SubMeasure (μ : Finset V → ℝ) : Prop where
  mono : ∀ {X Y : Finset V}, X ⊆ Y → μ X ≤ μ Y
  disj : ∀ {X Y : Finset V}, Disjoint X Y → μ X + μ Y ≤ μ Finset.univ

namespace RootedTree

variable (T : RootedTree V)

/-- Vertices weakly before `y` in the preorder. -/
noncomputable def prefixSet (y : Pre T) : Finset V :=
  Finset.univ.filter fun x => Pre.of T x ≤ y

/-- All vertices, sorted in preorder. -/
noncomputable def preList : List (Pre T) := (Finset.univ : Finset (Pre T)).sort (· ≤ ·)

variable {T}

theorem mem_preList (y : Pre T) : y ∈ T.preList := by
  simp [preList]

theorem preList_pairwise_lt : T.preList.Pairwise (· < ·) := by
  have h := Finset.pairwise_sort (Finset.univ : Finset (Pre T)) (· ≤ ·)
  have hnd := Finset.sort_nodup (Finset.univ : Finset (Pre T)) (· ≤ ·)
  exact (h.and hnd).imp fun ⟨hle, hne⟩ => lt_of_le_of_ne hle hne

theorem length_preList : T.preList.length = Fintype.card V := by
  simp [preList, Finset.length_sort]; rfl

omit [Fintype V] [LinearOrder V] in
theorem rootPath_pairwise_isAnc : ∀ (n : ℕ) (v : V), T.depth v ≤ n →
    (T.rootPath v).Pairwise fun a b => T.IsAnc a b ∧ a ≠ b
  | 0, v, h => by
      have hv := eq_root_of_depth_eq_zero (Nat.le_zero.mp h)
      subst hv
      rw [rootPath_root]; exact List.pairwise_singleton _ _
  | n + 1, v, h => by
      by_cases hv : v = T.root
      · subst hv; rw [rootPath_root]; exact List.pairwise_singleton _ _
      · have hdp : T.depth (T.parent v) ≤ n := by have := T.depth_parent v hv; omega
        rw [rootPath_of_ne hv, List.pairwise_append]
        refine ⟨rootPath_pairwise_isAnc n _ hdp, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        have hanc := mem_rootPath.mp ha
        refine ⟨isAnc_trans hanc (isAnc_parent _), fun hab => ?_⟩
        subst hab
        have := hanc.depth_le
        have := T.depth_parent a hv
        omega

omit [Fintype V] [LinearOrder V] in
theorem rootPath_nodup (v : V) : (T.rootPath v).Nodup :=
  (rootPath_pairwise_isAnc (T.depth v) v le_rfl).imp fun h => h.2

omit [LinearOrder V] in
theorem length_rootPath_le (v : V) : (T.rootPath v).length ≤ Fintype.card V := by
  rw [← List.toFinset_card_of_nodup (rootPath_nodup v)]
  exact Finset.card_le_univ _

end RootedTree

section Search

variable {Q A : Type} (T : RootedTree V)

/-- Find the deepest vertex whose subtree has more than half of the total mass `D`. -/
noncomputable def majoritySearch (meas : Finset V → Comp Q A ℝ) (D : ℝ) : Comp Q A V :=
  (findFirst (fun y : Pre T => (meas (T.prefixSet y)).map fun m => decide (D < 2 * m))
      T.preList).bind fun oy =>
    match oy with
    | none => Comp.pure T.root
    | some y =>
        (findFirst (fun x => (meas (T.subtree x)).map fun m => decide ¬ D < 2 * m)
            (T.rootPath y.val)).map fun ox =>
          match ox with
          | none => y.val
          | some x => T.parent x

variable {T}

theorem majoritySearch_spec (o : Q → A) (meas : Finset V → Comp Q A ℝ) {μ : Finset V → ℝ}
    (hμ : SubMeasure μ) (hD : 0 < μ Finset.univ)
    (hmeas : ∀ X, (meas X).eval o = μ X ∧ (meas X).cost o ≤ 2) :
    (∀ u, μ Finset.univ < 2 * μ (T.subtree u) ↔
        T.IsAnc u ((majoritySearch T meas (μ Finset.univ)).eval o)) ∧
      (majoritySearch T meas (μ Finset.univ)).cost o ≤
        4 * (Nat.log 2 (Fintype.card V) + 1) := by
  set D := μ Finset.univ
  -- First search: the first preorder prefix of mass more than `D/2`.
  have h1 := findFirst_spec o
    (fun y : Pre T => (meas (T.prefixSet y)).map fun m => decide (D < 2 * m))
    (fun y => D < 2 * μ (T.prefixSet y)) 2 _ T.preList le_rfl
    (fun y _ => by simp [(hmeas _).1, (hmeas _).2])
    (preList_pairwise_lt.imp fun {a b} hab h => lt_of_lt_of_le h (by
      have := hμ.mono (show T.prefixSet a ⊆ T.prefixSet b from fun x hx => by
        simp only [RootedTree.prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact le_trans hx (le_of_lt hab))
      linarith))
  obtain ⟨-, hsome1, hcost1⟩ := h1
  -- The last vertex in preorder passes the first test.
  obtain ⟨ymax, hymax⟩ : ∃ y : Pre T, ∀ z : Pre T, z ≤ y :=
    ⟨(Finset.univ : Finset (Pre T)).max' ⟨Pre.of T T.root, Finset.mem_univ _⟩,
      fun z => Finset.le_max' _ z (Finset.mem_univ z)⟩
  have hpmax : D < 2 * μ (T.prefixSet ymax) := by
    have : T.prefixSet ymax = Finset.univ := by
      ext x; simp [RootedTree.prefixSet, hymax (Pre.of T x)]
    rw [this]; linarith
  obtain ⟨L₁, y, L₂, hLsplit, hpy, hL₁, hev1⟩ := hsome1 ymax (mem_preList ymax) hpmax
  have hbefore : ∀ z : Pre T, z < y → ¬ D < 2 * μ (T.prefixSet z) := by
    intro z hzy hz
    have hzL := mem_preList z
    rw [hLsplit] at hzL
    rcases List.mem_append.mp hzL with hz1 | hz2
    · exact hL₁ z hz1 hz
    · have hpw := hLsplit ▸ (preList_pairwise_lt (T := T))
      rw [List.pairwise_append] at hpw
      rcases List.mem_cons.mp hz2 with rfl | hz2
      · exact lt_irrefl _ hzy
      · exact absurd (lt_trans hzy ((List.pairwise_cons.mp hpw.2.1).1 z hz2)) (lt_irrefl _)
  -- Every heavy vertex is an ancestor of `y`.
  have hheavy_anc : ∀ u, D < 2 * μ (T.subtree u) → T.IsAnc u y.val := by
    intro u hu
    obtain ⟨s, hs, hsmax⟩ := (T.subtree u).exists_max_image (fun x => Pre.of T x)
      (subtree_nonempty u)
    have hsub_pre : T.subtree u ⊆ T.prefixSet (Pre.of T s) := fun x hx => by
      simp only [RootedTree.prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsmax x hx
    have hys : y ≤ Pre.of T s := by
      by_contra hlt
      exact hbefore _ (lt_of_not_ge hlt)
        (lt_of_lt_of_le hu (by linarith [hμ.mono hsub_pre]))
    have huy : Pre.of T u ≤ y := by
      by_contra hlt
      have hlt := lt_of_not_ge hlt
      have hdisj : Disjoint (T.prefixSet y) (T.subtree u) := by
        rw [Finset.disjoint_left]
        intro x hx hxu
        simp only [RootedTree.prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have : Pre.of T u ≤ Pre.of T x := rootPath_le_of_isAnc (mem_subtree.mp hxu)
        exact absurd (lt_of_le_of_lt (le_trans this hx) hlt) (lt_irrefl _)
      have := hμ.disj hdisj
      linarith
    exact isAnc_of_between (isAnc_refl u) (mem_subtree.mp hs) huy hys
  -- Second search along the root path of `y`.
  have hpath := rootPath_pairwise_isAnc (T := T) (T.depth y.val) y.val le_rfl
  have h2 := findFirst_spec o
    (fun x => (meas (T.subtree x)).map fun m => decide ¬ D < 2 * m)
    (fun x => ¬ D < 2 * μ (T.subtree x)) 2 _ (T.rootPath y.val) le_rfl
    (fun x _ => by simp [(hmeas _).1, (hmeas _).2])
    (hpath.imp fun {a b} hab ha hb => ha (lt_of_lt_of_le hb (by
      linarith [hμ.mono (subtree_subset (T := T) hab.1)])))
  obtain ⟨hnone2, hsome2, hcost2⟩ := h2
  have hrootheavy : D < 2 * μ (T.subtree T.root) := by rw [subtree_root]; linarith
  refine ⟨?_, ?_⟩
  · intro u
    simp only [majoritySearch, eval_bind, hev1, eval_map]
    by_cases hex : ∃ x ∈ T.rootPath y.val, ¬ D < 2 * μ (T.subtree x)
    · obtain ⟨x0, hx0, hpx0⟩ := hex
      obtain ⟨P₁, x, P₂, hPsplit, hpx, hP₁, hev2⟩ := hsome2 x0 hx0 hpx0
      rw [hev2]
      simp only
      have hxroot : x ≠ T.root := fun h => hpx (h ▸ hrootheavy)
      have hpw := hPsplit ▸ hpath
      rw [List.pairwise_append, List.pairwise_cons] at hpw
      have hxy : T.IsAnc x y.val := mem_rootPath.mp (hPsplit ▸ by simp)
      constructor
      · intro hu
        have huy := hheavy_anc u hu
        have huP : u ∈ P₁ ++ x :: P₂ := hPsplit ▸ mem_rootPath.mpr huy
        rcases List.mem_append.mp huP with hu1 | hu2
        · exact (hpw.2.2 u hu1 x (by simp)).1.isAnc_parent_of_ne (hpw.2.2 u hu1 x (by simp)).2
        · exfalso
          have hxu : T.IsAnc x u := by
            rcases List.mem_cons.mp hu2 with rfl | hu2
            · exact isAnc_refl _
            · exact (hpw.2.1.1 u hu2).1
          exact hpx (lt_of_lt_of_le hu (by linarith [hμ.mono (subtree_subset (T := T) hxu)]))
      · intro hu
        have hux : T.IsAnc u x := isAnc_trans hu (isAnc_parent x)
        have huP : u ∈ P₁ ++ x :: P₂ := hPsplit ▸ mem_rootPath.mpr (isAnc_trans hux hxy)
        rcases List.mem_append.mp huP with hu1 | hu2
        · by_contra hnot
          exact hP₁ u hu1 hnot
        · exfalso
          have hxu : T.IsAnc x u := by
            rcases List.mem_cons.mp hu2 with rfl | hu2
            · exact isAnc_refl _
            · exact (hpw.2.1.1 u hu2).1
          have heq := isAnc_antisymm hxu hux
          subst heq
          have h1 := hu.depth_le
          have h2 := T.depth_parent _ hxroot
          omega
    · push Not at hex
      rw [hnone2 fun x hx => by simpa using hex x hx]
      simp only
      constructor
      · exact hheavy_anc u
      · intro hu
        exact hex u (mem_rootPath.mpr hu)
  · simp only [majoritySearch, cost_bind, hev1, cost_map]
    have hlen := length_rootPath_le (T := T) y.val
    have hl2 : Nat.log 2 (T.rootPath y.val).length ≤ Nat.log 2 (Fintype.card V) :=
      Nat.log_mono_right hlen
    rw [length_preList] at hcost1
    omega

/-- The cost bound of the majority search holds for every oracle. -/
theorem majoritySearch_cost (o : Q → A) (meas : Finset V → Comp Q A ℝ) (D : ℝ)
    (hmeas : ∀ X, (meas X).cost o ≤ 2) :
    (majoritySearch T meas D).cost o ≤ 4 * (Nat.log 2 (Fintype.card V) + 1) := by
  have h1 := findFirst_cost o
    (fun y : Pre T => (meas (T.prefixSet y)).map fun m => decide (D < 2 * m)) 2 _
    T.preList le_rfl (fun y _ => by simp [hmeas])
  rw [length_preList] at h1
  simp only [majoritySearch, cost_bind]
  split
  · simp; omega
  · rename_i y _
    simp only [cost_map]
    have h2 := findFirst_cost o
      (fun x => (meas (T.subtree x)).map fun m => decide ¬ D < 2 * m) 2 _
      (T.rootPath y.val) le_rfl (fun x _ => by simp [hmeas])
    have hl2 : Nat.log 2 (T.rootPath y.val).length ≤ Nat.log 2 (Fintype.card V) :=
      Nat.log_mono_right (length_rootPath_le y.val)
    omega

end Search

end TwoRespecting
end CutQueryComplexity
