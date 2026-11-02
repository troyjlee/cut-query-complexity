import CutQueryComplexity.TwoRespecting.Main

/-! # Weak majority subtrees and weak interest (all-minima plan, M3)

The single-cut search of `TwoRespecting.Main` uses *strict* majority: `u` is heavy for a measure
`μ` of total `D > 0` when `D < 2 μ(subtree u)`, and the heavy vertices are the ancestors of one
vertex. Reporting every minimum cut needs the *weak* version `D ≤ 2 μ(subtree u)`, since a
minimum two-edge cut can tie one of its one-edge cuts. Two disjoint subtrees can then both have
mass exactly `D/2`, so the weak-heavy vertices form the union of two root paths.

For a sum of nonnegative vertex weights (`IsVertexSum`) with total `D > 0`:

* `quantileSearch` finds the first preorder vertex whose prefix has mass at least `D/3`
  (resp. `2D/3`) by binary search;
* every subtree of mass at least `D/2` contains one of the two quantile vertices
  (`weak_heavy_cover`): a subtree is a preorder interval, and an interval avoiding both has
  mass at most `D/3`;
* `deepestWeak` finds, by binary search along a root path, the deepest weak-heavy ancestor;
* `weakMajoritySearch_spec`: the weak-heavy vertices are exactly the ancestors of the two
  returned vertices, with at most `8 (⌊log₂ n⌋ + 1)` evaluations of the measure.

`muOut` and `muIn` are vertex sums (`isVertexSum_muOut`, `isVertexSum_muIn`). The weak interest
lemmas (`interest_indep_weak`, `interest_nested_below_weak`, `interest_nested_above_weak`) and
`mutual_weak_interest` show that a pair cut no heavier than both of its one-edge cuts makes each
edge weakly interested in the other's heavy path. The interest sets `interestW` have at most
`4 (⌊log₂ n⌋ + 1)` paths.
-/

set_option autoImplicit false

namespace CutQueryComplexity
namespace TwoRespecting

open Search Search.Comp RootedTree WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-! ### Sums of nonnegative vertex weights -/

/-- A set function that is a sum of nonnegative vertex weights. -/
def IsVertexSum (μ : Finset V → ℝ) : Prop :=
  ∃ g : V → ℝ, (∀ x, 0 ≤ g x) ∧ ∀ X, μ X = ∑ x ∈ X, g x

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem IsVertexSum.mono {μ : Finset V → ℝ} (hμ : IsVertexSum μ) {X Y : Finset V}
    (h : X ⊆ Y) : μ X ≤ μ Y := by
  obtain ⟨g, hg, he⟩ := hμ
  rw [he, he]
  exact Finset.sum_le_sum_of_subset_of_nonneg h fun x _ _ => hg x

omit [Fintype V] [DecidableEq V] [LinearOrder V] in
theorem IsVertexSum.nonneg {μ : Finset V → ℝ} (hμ : IsVertexSum μ) (X : Finset V) : 0 ≤ μ X := by
  obtain ⟨g, hg, he⟩ := hμ
  rw [he]
  exact Finset.sum_nonneg fun x _ => hg x

omit [Fintype V] [LinearOrder V] in
/-- Disjoint parts of a set have at most its mass in total. -/
theorem IsVertexSum.add_le {μ : Finset V → ℝ} (hμ : IsVertexSum μ) {X Y Z : Finset V}
    (hd : Disjoint X Y) (h : X ∪ Y ⊆ Z) : μ X + μ Y ≤ μ Z := by
  have hm := hμ.mono h
  obtain ⟨g, hg, he⟩ := hμ
  rw [he, he, ← Finset.sum_union hd, ← he]
  exact hm

omit [Fintype V] [LinearOrder V] in
/-- `muOut G A` is the sum over `y ∉ A` of the weight from `A` to `y`. -/
theorem isVertexSum_muOut (G : WeightedGraph V) (A : Finset V) : IsVertexSum (muOut G A) := by
  refine ⟨fun y => if y ∈ A then 0 else ∑ a ∈ A, G.w a y, fun y => ?_, fun X => ?_⟩
  · dsimp only
    split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg fun a _ => G.nonneg a y
  · unfold muOut cross
    conv_lhs => rw [Finset.sum_comm]
    have hX : X \ A = X.filter fun y => y ∉ A := by
      ext y; simp [Finset.mem_sdiff]
    rw [hX, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ A <;> simp [hy]

omit [LinearOrder V] in
/-- `muIn G A` is the sum over `x ∈ A` of the weight from `x` out of `A`. -/
theorem isVertexSum_muIn (G : WeightedGraph V) (A : Finset V) : IsVertexSum (muIn G A) := by
  refine ⟨fun x => if x ∈ A then ∑ b ∈ Aᶜ, G.w x b else 0, fun x => ?_, fun X => ?_⟩
  · dsimp only
    split_ifs
    · exact Finset.sum_nonneg fun b _ => G.nonneg x b
    · exact le_rfl
  · unfold muIn cross
    have hX : A ∩ X = X.filter fun x => x ∈ A := by
      ext x; simp [and_comm]
    rw [hX, Finset.sum_filter]

/-! ### The search -/

section Search

variable {Q A : Type} (T : RootedTree V)

/-- The first preorder vertex whose prefix has at least `k/3` of the total mass `D`. -/
noncomputable def quantileSearch (meas : Finset V → Comp Q A ℝ) (D k : ℝ) : Comp Q A V :=
  (findFirst (fun y : Pre T => (meas (T.prefixSet y)).map fun m => decide (k * D ≤ 3 * m))
      T.preList).map fun oy =>
    match oy with
    | none => T.root
    | some y => y.val

/-- The deepest ancestor of `y` whose subtree has at least half of the total mass `D`. -/
noncomputable def deepestWeak (meas : Finset V → Comp Q A ℝ) (D : ℝ) (y : V) : Comp Q A V :=
  (findFirst (fun x => (meas (T.subtree x)).map fun m => decide (2 * m < D))
      (T.rootPath y)).map fun ox =>
    match ox with
    | none => y
    | some x => T.parent x

/-- **Weak majority search.** Two quantile searches and two root-path searches; the weak-heavy
vertices are the ancestors of the two returned vertices. -/
noncomputable def weakMajoritySearch (meas : Finset V → Comp Q A ℝ) (D : ℝ) :
    Comp Q A (V × V) :=
  (quantileSearch T meas D 1).bind fun y₁ =>
    (quantileSearch T meas D 2).bind fun y₂ =>
      (deepestWeak T meas D y₁).bind fun c₁ =>
        (deepestWeak T meas D y₂).map fun c₂ => (c₁, c₂)

variable {T}

theorem quantileSearch_cost (o : Q → A) (meas : Finset V → Comp Q A ℝ) (D k : ℝ)
    (hmeas : ∀ X, (meas X).cost o ≤ 2) :
    (quantileSearch T meas D k).cost o ≤ 2 * (Nat.log 2 (Fintype.card V) + 1) := by
  have h1 := findFirst_cost o
    (fun y : Pre T => (meas (T.prefixSet y)).map fun m => decide (k * D ≤ 3 * m)) 2 _
    T.preList le_rfl (fun y _ => by simp [hmeas])
  rw [length_preList] at h1
  simpa [quantileSearch] using h1

omit [LinearOrder V] in
theorem deepestWeak_cost (o : Q → A) (meas : Finset V → Comp Q A ℝ) (D : ℝ) (y : V)
    (hmeas : ∀ X, (meas X).cost o ≤ 2) :
    (deepestWeak T meas D y).cost o ≤ 2 * (Nat.log 2 (Fintype.card V) + 1) := by
  have h2 := findFirst_cost o
    (fun x => (meas (T.subtree x)).map fun m => decide (2 * m < D)) 2 _
    (T.rootPath y) le_rfl (fun x _ => by simp [hmeas])
  have hl2 : Nat.log 2 (T.rootPath y).length ≤ Nat.log 2 (Fintype.card V) :=
    Nat.log_mono_right (length_rootPath_le y)
  simp only [deepestWeak, cost_map]
  have : 2 * (Nat.log 2 (T.rootPath y).length + 1) ≤ 2 * (Nat.log 2 (Fintype.card V) + 1) := by
    omega
  exact h2.trans this

/-- The cost bound of the weak majority search holds for every oracle. -/
theorem weakMajoritySearch_cost (o : Q → A) (meas : Finset V → Comp Q A ℝ) (D : ℝ)
    (hmeas : ∀ X, (meas X).cost o ≤ 2) :
    (weakMajoritySearch T meas D).cost o ≤ 8 * (Nat.log 2 (Fintype.card V) + 1) := by
  simp only [weakMajoritySearch, cost_bind, cost_map]
  have h1 := quantileSearch_cost (T := T) o meas D 1 hmeas
  have h2 := quantileSearch_cost (T := T) o meas D 2 hmeas
  have h3 := deepestWeak_cost (T := T) o meas D ((quantileSearch T meas D 1).eval o) hmeas
  have h4 := deepestWeak_cost (T := T) o meas D ((quantileSearch T meas D 2).eval o) hmeas
  omega

/-- The quantile search returns the first preorder vertex whose prefix has at least `k/3` of
the mass. -/
theorem quantileSearch_spec (o : Q → A) (meas : Finset V → Comp Q A ℝ) {μ : Finset V → ℝ}
    (hμ : IsVertexSum μ) (hmeas : ∀ X, (meas X).eval o = μ X ∧ (meas X).cost o ≤ 2)
    {k : ℝ} (hk : k ≤ 3) :
    k * μ Finset.univ ≤
        3 * μ (T.prefixSet (Pre.of T ((quantileSearch T meas (μ Finset.univ) k).eval o))) ∧
      ∀ z : Pre T, z < Pre.of T ((quantileSearch T meas (μ Finset.univ) k).eval o) →
        3 * μ (T.prefixSet z) < k * μ Finset.univ := by
  set D := μ Finset.univ
  have hD0 : 0 ≤ D := hμ.nonneg _
  have h1 := findFirst_spec o
    (fun y : Pre T => (meas (T.prefixSet y)).map fun m => decide (k * D ≤ 3 * m))
    (fun y => k * D ≤ 3 * μ (T.prefixSet y)) 2 _ T.preList le_rfl
    (fun y _ => by simp [(hmeas _).1, (hmeas _).2])
    (preList_pairwise_lt.imp fun {a b} hab h => le_trans h (by
      have := hμ.mono (show T.prefixSet a ⊆ T.prefixSet b from fun x hx => by
        simp only [RootedTree.prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact le_trans hx (le_of_lt hab))
      linarith))
  obtain ⟨-, hsome1, -⟩ := h1
  obtain ⟨ymax, hymax⟩ : ∃ y : Pre T, ∀ z : Pre T, z ≤ y :=
    ⟨(Finset.univ : Finset (Pre T)).max' ⟨Pre.of T T.root, Finset.mem_univ _⟩,
      fun z => Finset.le_max' _ z (Finset.mem_univ z)⟩
  have hpmax : k * D ≤ 3 * μ (T.prefixSet ymax) := by
    have : T.prefixSet ymax = Finset.univ := by
      ext x; simp [RootedTree.prefixSet, hymax (Pre.of T x)]
    rw [this]; nlinarith
  obtain ⟨L₁, y, L₂, hLsplit, hpy, hL₁, hev1⟩ := hsome1 ymax (mem_preList ymax) hpmax
  have hval : (quantileSearch T meas D k).eval o = y.val := by
    simp only [quantileSearch, eval_map, hev1]
  rw [hval, Pre.of_val]
  refine ⟨hpy, fun z hzy => ?_⟩
  have hzL := mem_preList z
  rw [hLsplit] at hzL
  rcases List.mem_append.mp hzL with hz1 | hz2
  · exact lt_of_not_ge (hL₁ z hz1)
  · have hpw := hLsplit ▸ (preList_pairwise_lt (T := T))
    rw [List.pairwise_append] at hpw
    rcases List.mem_cons.mp hz2 with rfl | hz2
    · exact absurd hzy (lt_irrefl _)
    · exact absurd (lt_trans hzy ((List.pairwise_cons.mp hpw.2.1).1 z hz2)) (lt_irrefl _)

omit [LinearOrder V] in
/-- The deepest weak-heavy ancestor: on the root path of `y`, the weak-heavy vertices are the
ancestors of the returned vertex. -/
theorem deepestWeak_spec (o : Q → A) (meas : Finset V → Comp Q A ℝ) {μ : Finset V → ℝ}
    (hμ : IsVertexSum μ) (hmeas : ∀ X, (meas X).eval o = μ X ∧ (meas X).cost o ≤ 2) (y : V) :
    (∀ u, T.IsAnc u y → (μ Finset.univ ≤ 2 * μ (T.subtree u) ↔
        T.IsAnc u ((deepestWeak T meas (μ Finset.univ) y).eval o))) ∧
      T.IsAnc ((deepestWeak T meas (μ Finset.univ) y).eval o) y := by
  set D := μ Finset.univ
  have hD0 : 0 ≤ D := hμ.nonneg _
  have hpath := rootPath_pairwise_isAnc (T := T) (T.depth y) y le_rfl
  have h2 := findFirst_spec o
    (fun x => (meas (T.subtree x)).map fun m => decide (2 * m < D))
    (fun x => 2 * μ (T.subtree x) < D) 2 _ (T.rootPath y) le_rfl
    (fun x _ => by simp [(hmeas _).1, (hmeas _).2])
    (hpath.imp fun {a b} hab ha => lt_of_le_of_lt (by
      linarith [hμ.mono (subtree_subset (T := T) hab.1)]) ha)
  obtain ⟨hnone2, hsome2, -⟩ := h2
  have hrootheavy : D ≤ 2 * μ (T.subtree T.root) := by rw [subtree_root]; linarith
  by_cases hex : ∃ x ∈ T.rootPath y, 2 * μ (T.subtree x) < D
  · obtain ⟨x0, hx0, hpx0⟩ := hex
    obtain ⟨P₁, x, P₂, hPsplit, hpx, hP₁, hev2⟩ := hsome2 x0 hx0 hpx0
    have hval : (deepestWeak T meas D y).eval o = T.parent x := by
      simp only [deepestWeak, eval_map, hev2]
    rw [hval]
    have hxroot : x ≠ T.root := fun h => by rw [h] at hpx; linarith
    have hpw := hPsplit ▸ hpath
    rw [List.pairwise_append, List.pairwise_cons] at hpw
    have hxy : T.IsAnc x y := mem_rootPath.mp (hPsplit ▸ by simp)
    have hbelow : ∀ u ∈ x :: P₂, T.IsAnc x u := by
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact isAnc_refl _
      · exact (hpw.2.1.1 u hu).1
    refine ⟨fun u hu => ⟨fun hheavy => ?_, fun hu' => ?_⟩, isAnc_trans (isAnc_parent x) hxy⟩
    · have huP : u ∈ P₁ ++ x :: P₂ := hPsplit ▸ mem_rootPath.mpr hu
      rcases List.mem_append.mp huP with hu1 | hu2
      · exact (hpw.2.2 u hu1 x (by simp)).1.isAnc_parent_of_ne (hpw.2.2 u hu1 x (by simp)).2
      · exfalso
        have := hμ.mono (subtree_subset (T := T) (hbelow u hu2))
        linarith
    · have hux : T.IsAnc u x := isAnc_trans hu' (isAnc_parent x)
      have huP : u ∈ P₁ ++ x :: P₂ := hPsplit ▸ mem_rootPath.mpr (isAnc_trans hux hxy)
      rcases List.mem_append.mp huP with hu1 | hu2
      · exact not_lt.mp (hP₁ u hu1)
      · exfalso
        have heq := isAnc_antisymm (hbelow u hu2) hux
        subst heq
        have h1 := hu'.depth_le
        have h2 := T.depth_parent _ hxroot
        omega
  · push Not at hex
    have hval : (deepestWeak T meas D y).eval o = y := by
      simp only [deepestWeak, eval_map, hnone2 fun x hx => not_lt.mpr (hex x hx)]
    rw [hval]
    exact ⟨fun u hu => ⟨fun _ => hu, fun _ => hex u (mem_rootPath.mpr hu)⟩, isAnc_refl y⟩

omit [Fintype V] in
theorem pre_le_of_isAnc {u x : V} (h : T.IsAnc u x) :
    Pre.of T u ≤ Pre.of T x :=
  rootPath_le_of_isAnc h

/-- **The two quantiles cover every weak-heavy vertex.** If `y₁` (resp. `y₂`) is the first
preorder vertex whose prefix has at least `D/3` (resp. `2D/3`) of the mass, every subtree of
mass at least `D/2` contains `y₁` or `y₂`. -/
theorem weak_heavy_cover {μ : Finset V → ℝ} (hμ : IsVertexSum μ) (hD : 0 < μ Finset.univ)
    {y₁ y₂ : Pre T}
    (h1 : 1 * μ Finset.univ ≤ 3 * μ (T.prefixSet y₁))
    (h1' : ∀ z, z < y₁ → 3 * μ (T.prefixSet z) < 1 * μ Finset.univ)
    (h2 : 2 * μ Finset.univ ≤ 3 * μ (T.prefixSet y₂))
    (h2' : ∀ z, z < y₂ → 3 * μ (T.prefixSet z) < 2 * μ Finset.univ)
    {u : V} (hu : μ Finset.univ ≤ 2 * μ (T.subtree u)) :
    T.IsAnc u y₁.val ∨ T.IsAnc u y₂.val := by
  set D := μ Finset.univ
  have hy12 : y₁ ≤ y₂ := by
    by_contra hlt
    have := h1' y₂ (lt_of_not_ge hlt)
    linarith
  obtain ⟨s, hs, hsmax⟩ := (T.subtree u).exists_max_image (fun x => Pre.of T x)
    (subtree_nonempty u)
  have hus : Pre.of T u ≤ Pre.of T s := pre_le_of_isAnc (mem_subtree.mp hs)
  -- the subtree of `u` is the preorder interval from `u` to `s`
  have hinterval : ∀ x : V, Pre.of T u ≤ Pre.of T x → Pre.of T x ≤ Pre.of T s → T.IsAnc u x :=
    fun x hux hxs => isAnc_of_between (isAnc_refl u) (mem_subtree.mp hs) hux hxs
  have hsub_pre : T.subtree u ⊆ T.prefixSet (Pre.of T s) := fun x hx => by
    simp only [RootedTree.prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsmax x hx
  have hdisj : ∀ y : Pre T, y < Pre.of T u → Disjoint (T.subtree u) (T.prefixSet y) := by
    intro y hy
    rw [Finset.disjoint_left]
    intro x hxu hxy
    simp only [RootedTree.prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    exact absurd (lt_of_le_of_lt (le_trans (pre_le_of_isAnc (mem_subtree.mp hxu)) hxy) hy)
      (lt_irrefl _)
  have hpre_mono : ∀ a b : Pre T, a ≤ b → T.prefixSet a ⊆ T.prefixSet b := fun a b hab x hx => by
    simp only [RootedTree.prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact le_trans hx hab
  -- a vertex outside the subtree lies before `u` or after `s`
  have hout : ∀ y : Pre T, ¬ T.IsAnc u y.val → y < Pre.of T u ∨ Pre.of T s < y := by
    intro y hy
    by_contra hc
    push Not at hc
    exact hy (hinterval y.val hc.1 hc.2)
  by_contra hnot
  push Not at hnot
  rcases hout y₁ hnot.1 with hy1 | hy1 <;> rcases hout y₂ hnot.2 with hy2 | hy2
  · -- both quantiles before `u`: the subtree misses the first two thirds
    have := hμ.add_le (hdisj y₂ hy2) (Finset.subset_univ _)
    linarith
  · -- `y₁` before `u`, `y₂` after the subtree
    have hle := hμ.add_le (hdisj y₁ hy1)
      (Finset.union_subset hsub_pre (hpre_mono _ _ (le_of_lt (lt_of_lt_of_le hy1 hus))))
    have := h2' _ hy2
    linarith
  · exact absurd (lt_of_lt_of_le (lt_of_lt_of_le hy2 hus) (le_trans (le_of_lt hy1) hy12))
      (lt_irrefl _)
  · -- both quantiles after the subtree: it lies in the first third
    have := hμ.mono hsub_pre
    have := h1' _ hy1
    linarith

/-- **Weak majority search.** For a sum of nonnegative vertex weights with positive total `D`
whose evaluations cost at most two queries, the vertices `u` with `D ≤ 2 μ(subtree u)` are
exactly the ancestors of the two returned vertices, using at most `8 (⌊log₂ n⌋ + 1)` queries. -/
theorem weakMajoritySearch_spec (o : Q → A) (meas : Finset V → Comp Q A ℝ) {μ : Finset V → ℝ}
    (hμ : IsVertexSum μ) (hD : 0 < μ Finset.univ)
    (hmeas : ∀ X, (meas X).eval o = μ X ∧ (meas X).cost o ≤ 2) :
    (∀ u, μ Finset.univ ≤ 2 * μ (T.subtree u) ↔
        T.IsAnc u ((weakMajoritySearch T meas (μ Finset.univ)).eval o).1 ∨
          T.IsAnc u ((weakMajoritySearch T meas (μ Finset.univ)).eval o).2) ∧
      (weakMajoritySearch T meas (μ Finset.univ)).cost o ≤
        8 * (Nat.log 2 (Fintype.card V) + 1) := by
  set D := μ Finset.univ
  refine ⟨fun u => ?_, weakMajoritySearch_cost o meas D fun X => (hmeas X).2⟩
  obtain ⟨q1, q1'⟩ := quantileSearch_spec (T := T) o meas hμ hmeas (k := 1) (by norm_num)
  obtain ⟨q2, q2'⟩ := quantileSearch_spec (T := T) o meas hμ hmeas (k := 2) (by norm_num)
  set y₁ := (quantileSearch T meas D 1).eval o
  set y₂ := (quantileSearch T meas D 2).eval o
  obtain ⟨d1, d1'⟩ := deepestWeak_spec (T := T) o meas hμ hmeas y₁
  obtain ⟨d2, d2'⟩ := deepestWeak_spec (T := T) o meas hμ hmeas y₂
  have heval : (weakMajoritySearch T meas D).eval o =
      ((deepestWeak T meas D y₁).eval o, (deepestWeak T meas D y₂).eval o) := by
    simp [weakMajoritySearch, y₁, y₂]
  rw [heval]
  constructor
  · intro hu
    rcases weak_heavy_cover (T := T) hμ hD q1 q1' q2 q2' hu with h | h
    · exact Or.inl ((d1 u h).mp hu)
    · exact Or.inr ((d2 u h).mp hu)
  · rintro (h | h)
    · exact (d1 u (isAnc_trans h d1')).mpr h
    · exact (d2 u (isAnc_trans h d2')).mpr h

end Search

/-! ### Weak interest -/

section Interest

variable {T : RootedTree V}

omit [LinearOrder V] in
/-- Weak Lemma 35, independent edges. -/
theorem interest_indep_weak (G : WeightedGraph V) {e f : V} (h₁ : ¬ T.IsAnc e f)
    (h₂ : ¬ T.IsAnc f e) (hle : G.cut (T.pairShore e f) ≤ G.cut (T.subtree f)) :
    G.cut (T.subtree e) ≤ 2 * muOut G (T.subtree e) (T.subtree f) := by
  rw [pairShore_of_indep h₁ h₂, cut_union_of_disjoint G (disjoint_subtree h₁ h₂)] at hle
  have : T.subtree f \ T.subtree e = T.subtree f :=
    Finset.sdiff_eq_self_of_disjoint (disjoint_subtree h₁ h₂).symm
  rw [muOut, this]
  linarith

omit [LinearOrder V] in
/-- Weak Lemma 35, nested edges (`e` above `f`): `f` is weakly heavy for `muIn` of `e`. -/
theorem interest_nested_below_weak (G : WeightedGraph V) {e f : V} (h : T.IsAnc e f)
    (hle : G.cut (T.pairShore e f) ≤ G.cut (T.subtree f)) :
    G.cut (T.subtree e) ≤ 2 * muIn G (T.subtree e) (T.subtree f) := by
  rw [pairShore_of_isAnc h, cut_sdiff_of_subset G (subtree_subset h)] at hle
  have : T.subtree e ∩ T.subtree f = T.subtree f := Finset.inter_eq_right.mpr (subtree_subset h)
  rw [muIn, this]
  linarith

omit [LinearOrder V] in
/-- Weak Lemma 35, nested edges: the lower edge is weakly interested in the upper. -/
theorem interest_nested_above_weak (G : WeightedGraph V) {e f : V} (h : T.IsAnc e f) :
    G.cut (T.subtree f) ≤ 2 * muIn G (T.subtree f) (T.subtree e) := by
  have : T.subtree f ∩ T.subtree e = T.subtree f := Finset.inter_eq_left.mpr (subtree_subset h)
  rw [muIn, this, cross_compl]
  linarith [G.cut_nonneg (T.subtree f)]

end Interest

/-! ### Edge information with weak interest -/

section Info

variable (T : RootedTree V)

/-- One cut query and two weak majority searches for the tree edge above `e`; the queried
one-edge cut value is returned with the four path endpoints. -/
noncomputable def edgeInfoW (e : V) : Comp (Finset V) ℝ (ℝ × (V × V) × (V × V)) :=
  (ask (T.subtree e)).bind fun a =>
    (weakMajoritySearch T (measOut (T.subtree e) a) a).bind fun c =>
      (weakMajoritySearch T (measIn (T.subtree e) a) a).map fun d => (a, c, d)

/-- Heavy paths an edge is weakly interested in, other than its own. -/
noncomputable def interestW (info : V → Option (ℝ × (V × V) × (V × V))) (e : V) : Finset V :=
  match info e with
  | none => ∅
  | some x => (T.headsAbove x.2.1.1 ∪ T.headsAbove x.2.1.2 ∪
      T.headsAbove x.2.2.1 ∪ T.headsAbove x.2.2.2).erase (T.head e)

/-- The edge information computed on the genuine oracle. -/
noncomputable def infoW (G : WeightedGraph V) : V → Option (ℝ × (V × V) × (V × V)) :=
  (tabulate (edgeInfoW T) T.edgeList).eval G.cut

variable {T}

theorem infoW_eq (G : WeightedGraph V) {e : V} (he : e ≠ T.root) :
    infoW T G e = some (G.cut (T.subtree e),
      (weakMajoritySearch T (measOut (T.subtree e) (G.cut (T.subtree e)))
          (G.cut (T.subtree e))).eval G.cut,
      (weakMajoritySearch T (measIn (T.subtree e) (G.cut (T.subtree e)))
          (G.cut (T.subtree e))).eval G.cut) := by
  simp [infoW, mem_edgeList.mpr he, edgeInfoW]

theorem edgeInfoW_cost (o : Finset V → ℝ) (e : V) :
    (edgeInfoW T e).cost o ≤ 16 * (Nat.log 2 (Fintype.card V) + 1) + 1 := by
  simp only [edgeInfoW, cost_bind, cost_ask, cost_map, eval_ask]
  have h1 := weakMajoritySearch_cost (T := T) o (measOut (T.subtree e) (o (T.subtree e)))
    (o (T.subtree e)) fun X => (measOut_cost o _ _ X).le
  have h2 := weakMajoritySearch_cost (T := T) o (measIn (T.subtree e) (o (T.subtree e)))
    (o (T.subtree e)) fun X => (measIn_cost o _ _ X).le
  omega

theorem card_interestW_le (info : V → Option (ℝ × (V × V) × (V × V))) (e : V) :
    (interestW T info e).card ≤ 4 * (Nat.log 2 (Fintype.card V) + 1) := by
  unfold interestW
  split
  · simp
  · rename_i x _
    have h1 := card_headsAbove_le (T := T) x.2.1.1
    have h2 := card_headsAbove_le (T := T) x.2.1.2
    have h3 := card_headsAbove_le (T := T) x.2.2.1
    have h4 := card_headsAbove_le (T := T) x.2.2.2
    calc _ ≤ (T.headsAbove x.2.1.1 ∪ T.headsAbove x.2.1.2 ∪
            T.headsAbove x.2.2.1 ∪ T.headsAbove x.2.2.2).card := Finset.card_erase_le
      _ ≤ (T.headsAbove x.2.1.1 ∪ T.headsAbove x.2.1.2 ∪ T.headsAbove x.2.2.1).card +
            (T.headsAbove x.2.2.2).card := Finset.card_union_le _ _
      _ ≤ (T.headsAbove x.2.1.1 ∪ T.headsAbove x.2.1.2).card + (T.headsAbove x.2.2.1).card +
            (T.headsAbove x.2.2.2).card := by
          have := Finset.card_union_le (T.headsAbove x.2.1.1 ∪ T.headsAbove x.2.1.2)
            (T.headsAbove x.2.2.1)
          omega
      _ ≤ _ := by
          have := Finset.card_union_le (T.headsAbove x.2.1.1) (T.headsAbove x.2.1.2)
          omega

/-- Weak interest along a boundary measure puts the other edge's path in the interest set. -/
theorem head_mem_interestW (G : WeightedGraph V) {e f : V} (he : e ≠ T.root) (hf : f ≠ T.root)
    (hhead : T.head f ≠ T.head e) (hpos : 0 < G.cut (T.subtree e))
    (hint : G.cut (T.subtree e) ≤ 2 * muOut G (T.subtree e) (T.subtree f) ∨
      G.cut (T.subtree e) ≤ 2 * muIn G (T.subtree e) (T.subtree f)) :
    T.head f ∈ interestW T (infoW T G) e := by
  simp only [interestW, infoW_eq G he]
  rw [Finset.mem_erase]
  refine ⟨hhead, ?_⟩
  have hheads : ∀ c : V, T.IsAnc f c → T.head f ∈ T.headsAbove c := fun c hfc => by
    classical
    simp only [RootedTree.headsAbove, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨f, ⟨hf, hfc⟩, rfl⟩
  simp only [Finset.mem_union]
  rcases hint with h | h
  · have hs := (weakMajoritySearch_spec (T := T) G.cut _ (isVertexSum_muOut G (T.subtree e))
      (by rwa [muOut_univ]) (measOut_spec G (T.subtree e))).1 f
    rw [muOut_univ] at hs
    rcases hs.mp h with h' | h'
    · exact Or.inl (Or.inl (Or.inl (hheads _ h')))
    · exact Or.inl (Or.inl (Or.inr (hheads _ h')))
  · have hs := (weakMajoritySearch_spec (T := T) G.cut _ (isVertexSum_muIn G (T.subtree e))
      (by rwa [muIn_univ]) (measIn_spec G (T.subtree e))).1 f
    rw [muIn_univ] at hs
    rcases hs.mp h with h' | h'
    · exact Or.inl (Or.inr (hheads _ h'))
    · exact Or.inr (hheads _ h')

/-- **Mutual weak interest.** A pair of edges on different heavy paths whose pair cut is no
heavier than either positive one-edge cut puts each edge in the other's weak interest list. -/
theorem mutual_weak_interest (G : WeightedGraph V) {e f : V} (he : e ≠ T.root)
    (hf : f ≠ T.root) (hhead : T.head e ≠ T.head f)
    (hpe : 0 < G.cut (T.subtree e)) (hpf : 0 < G.cut (T.subtree f))
    (hlee : T.pairCut G e f ≤ G.cut (T.subtree e))
    (hlef : T.pairCut G e f ≤ G.cut (T.subtree f)) :
    T.head f ∈ interestW T (infoW T G) e ∧ T.head e ∈ interestW T (infoW T G) f := by
  have hlef' : G.cut (T.pairShore f e) ≤ G.cut (T.subtree e) := by
    rw [pairShore_comm]; exact hlee
  by_cases hef : T.IsAnc e f
  · exact ⟨head_mem_interestW G he hf (Ne.symm hhead) hpe
        (Or.inr (interest_nested_below_weak G hef hlef)),
      head_mem_interestW G hf he hhead hpf (Or.inr (interest_nested_above_weak G hef))⟩
  · by_cases hfe : T.IsAnc f e
    · exact ⟨head_mem_interestW G he hf (Ne.symm hhead) hpe
          (Or.inr (interest_nested_above_weak G hfe)),
        head_mem_interestW G hf he hhead hpf
          (Or.inr (interest_nested_below_weak G hfe hlef'))⟩
    · exact ⟨head_mem_interestW G he hf (Ne.symm hhead) hpe
          (Or.inl (interest_indep_weak G hef hfe hlef)),
        head_mem_interestW G hf he hhead hpf (Or.inl (interest_indep_weak G hfe hef hlef'))⟩

end Info

end TwoRespecting
end CutQueryComplexity
