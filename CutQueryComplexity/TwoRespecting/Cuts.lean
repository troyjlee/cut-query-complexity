import CutQueryComplexity.Graph.Operations
import CutQueryComplexity.TwoRespecting.Majority
import CutQueryComplexity.Search.SMAWK

/-! # Cut identities, boundary measures, interest, and Monge rectangles

For a hidden weighted graph `G` and the tree edge above a non-root vertex `e`,
write `A e = subtree e` and `a e = cut (A e)`. The shore crossing exactly the tree
edges above `e` and `f` is `A e ∆ A f`, whose cut is `K e f`.

* `measOut`/`measIn`: the two boundary measures of `A e`, each evaluated with two
  cut queries once `a e` is known (paper eqs. for `μ^out`, `μ^in`).
* `interest_indep`/`interest_nested`: if `K e f` is below every one-edge cut,
  each edge is heavy for a boundary measure of the other (Lemma 35).
* `isMonge_indep`/`isMonge_nested`: the two Monge cases of Lemma 37, derived
  from submodularity of the cut function.
-/

namespace CutQueryComplexity
namespace TwoRespecting

open Search Search.Comp RootedTree WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Two cut identities -/

theorem cut_union_of_disjoint (G : WeightedGraph V) {A B : Finset V} (h : Disjoint A B) :
    G.cut (A ∪ B) = G.cut A + G.cut B - 2 * G.cross A B := by
  rw [G.cross_eq_three_cuts h]; ring

theorem cut_sdiff_of_subset (G : WeightedGraph V) {A B : Finset V} (h : B ⊆ A) :
    G.cut (A \ B) = G.cut A + G.cut B - 2 * G.cross B Aᶜ := by
  have hA : A = (A \ B) ∪ B := (Finset.sdiff_union_of_subset h).symm
  have hd1 : Disjoint (A \ B) B := Finset.sdiff_disjoint
  have hc1 : (A \ B)ᶜ = Aᶜ ∪ B := by
    ext x; simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]; tauto
  have hc2 : Bᶜ = (A \ B) ∪ Aᶜ := by
    ext x; simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · intro hx; by_cases hxA : x ∈ A <;> tauto
    · rintro (⟨-, hx⟩ | hx)
      · exact hx
      · exact fun hb => hx (h hb)
  have hdA : Disjoint Aᶜ B := Finset.disjoint_left.mpr fun x hx hb => (Finset.mem_compl.mp hx) (h hb)
  have hdB : Disjoint (A \ B) Aᶜ :=
    Finset.disjoint_left.mpr fun x hx hc => (Finset.mem_compl.mp hc) (Finset.mem_sdiff.mp hx).1
  have e1 : G.cut (A \ B) = G.cross (A \ B) Aᶜ + G.cross (A \ B) B := by
    rw [← cross_compl, hc1, G.cross_union_right _ _ _ hdA]
  have e2 : G.cut A = G.cross (A \ B) Aᶜ + G.cross B Aᶜ := by
    conv_lhs => rw [← cross_compl, hA]
    rw [G.cross_union_left _ _ _ hd1, ← hA]
  have e3 : G.cut B = G.cross B (A \ B) + G.cross B Aᶜ := by
    rw [← cross_compl, hc2, G.cross_union_right _ _ _ hdB]
  rw [e1, e2, e3, G.cross_comm B (A \ B)]
  ring

/-! ### Boundary measures and their oracles -/

/-- Weight from `A` to the part of `X` outside `A`. -/
def muOut (G : WeightedGraph V) (A X : Finset V) : ℝ := G.cross A (X \ A)

/-- Weight from the part of `X` inside `A` to the outside of `A`. -/
def muIn (G : WeightedGraph V) (A X : Finset V) : ℝ := G.cross (A ∩ X) Aᶜ

omit [Fintype V] [DecidableEq V] in
theorem cross_mono_right (G : WeightedGraph V) (S : Finset V) {X Y : Finset V} (h : X ⊆ Y) :
    G.cross S X ≤ G.cross S Y :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => G.nonneg _ _

omit [Fintype V] [DecidableEq V] in
theorem cross_mono_left (G : WeightedGraph V) {X Y : Finset V} (T : Finset V) (h : X ⊆ Y) :
    G.cross X T ≤ G.cross Y T :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ =>
    Finset.sum_nonneg fun _ _ => G.nonneg _ _

theorem subMeasure_muOut (G : WeightedGraph V) (A : Finset V) : SubMeasure (muOut G A) where
  mono h := cross_mono_right G A (Finset.sdiff_subset_sdiff h le_rfl)
  disj {X Y} h := by
    unfold muOut
    rw [← G.cross_union_right _ _ _ (Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset h))]
    exact cross_mono_right G A (fun x hx => by
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
      rcases hx with hx | hx <;> exact hx.2)

theorem subMeasure_muIn (G : WeightedGraph V) (A : Finset V) : SubMeasure (muIn G A) where
  mono h := cross_mono_left G _ (Finset.inter_subset_inter_left h)
  disj {X Y} h := by
    unfold muIn
    rw [← G.cross_union_left _ _ _ (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right h))]
    exact cross_mono_left G _ (fun x hx => by
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_univ, and_true] at hx ⊢
      rcases hx with hx | hx <;> exact hx.1)

@[simp] theorem muOut_univ (G : WeightedGraph V) (A : Finset V) :
    muOut G A Finset.univ = G.cut A := by
  simp [muOut, cut, cross, Finset.compl_eq_univ_sdiff]

@[simp] theorem muIn_univ (G : WeightedGraph V) (A : Finset V) :
    muIn G A Finset.univ = G.cut A := by
  simp [muIn, cut, cross]

/-- Two cut queries evaluate `muOut`, given `a = cut A`. -/
noncomputable def measOut (A : Finset V) (a : ℝ) (X : Finset V) : Comp (Finset V) ℝ ℝ :=
  (ask (X \ A)).bind fun p => (ask (A ∪ X)).bind fun q => Comp.pure ((a + p - q) / 2)

/-- Two cut queries evaluate `muIn`, given `a = cut A`. -/
noncomputable def measIn (A : Finset V) (a : ℝ) (X : Finset V) : Comp (Finset V) ℝ ℝ :=
  (ask (A ∩ X)).bind fun p => (ask (A \ X)).bind fun q => Comp.pure ((a + p - q) / 2)

theorem measOut_spec (G : WeightedGraph V) (A X : Finset V) :
    (measOut A (G.cut A) X).eval G.cut = muOut G A X ∧
      (measOut A (G.cut A) X).cost G.cut ≤ 2 := by
  refine ⟨?_, by simp [measOut]⟩
  simp only [measOut, eval_bind, eval_ask, eval_pure, muOut]
  have hd : Disjoint A (X \ A) := Finset.disjoint_sdiff
  rw [G.cross_eq_three_cuts hd, Finset.union_sdiff_self_eq_union]

theorem measIn_spec (G : WeightedGraph V) (A X : Finset V) :
    (measIn A (G.cut A) X).eval G.cut = muIn G A X ∧
      (measIn A (G.cut A) X).cost G.cut ≤ 2 := by
  refine ⟨?_, by simp [measIn]⟩
  simp only [measIn, eval_bind, eval_ask, eval_pure, muIn]
  have hd : Disjoint (A ∩ X) Aᶜ :=
    Finset.disjoint_left.mpr fun x hx hc => (Finset.mem_compl.mp hc) (Finset.mem_inter.mp hx).1
  rw [G.cross_eq_three_cuts hd, G.cut_compl]
  have : A ∩ X ∪ Aᶜ = (A \ X)ᶜ := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  rw [this, G.cut_compl]
  ring

/-! ### Shores of two tree edges -/

variable [LinearOrder V] (T : RootedTree V)

/-- The cut of the shore crossing exactly the tree edges above `e` and `f`. -/
noncomputable def RootedTree.pairShore (e f : V) : Finset V :=
  symmDiff (T.subtree e) (T.subtree f)

variable {T}

omit [LinearOrder V] in
theorem pairShore_comm (e f : V) : T.pairShore e f = T.pairShore f e := symmDiff_comm _ _

omit [LinearOrder V] in
theorem pairShore_of_indep {e f : V} (h₁ : ¬ T.IsAnc e f) (h₂ : ¬ T.IsAnc f e) :
    T.pairShore e f = T.subtree e ∪ T.subtree f :=
  (disjoint_subtree h₁ h₂).symmDiff_eq_sup

omit [LinearOrder V] in
theorem pairShore_of_isAnc {e f : V} (h : T.IsAnc e f) :
    T.pairShore e f = T.subtree e \ T.subtree f :=
  symmDiff_of_ge (subtree_subset h)

omit [LinearOrder V] in
/-- Lemma 35, independent edges: an improving pair is mutually interested. -/
theorem interest_indep (G : WeightedGraph V) {e f : V} (h₁ : ¬ T.IsAnc e f)
    (h₂ : ¬ T.IsAnc f e) {lam : ℝ} (hlt : G.cut (T.pairShore e f) < lam)
    (hf : lam ≤ G.cut (T.subtree f)) :
    G.cut (T.subtree e) < 2 * muOut G (T.subtree e) (T.subtree f) := by
  rw [pairShore_of_indep h₁ h₂, cut_union_of_disjoint G (disjoint_subtree h₁ h₂)] at hlt
  have : T.subtree f \ T.subtree e = T.subtree f :=
    Finset.sdiff_eq_self_of_disjoint (disjoint_subtree h₁ h₂).symm
  rw [muOut, this]
  linarith

omit [LinearOrder V] in
/-- Lemma 35, nested edges (`e` strictly above `f`): `f` is heavy for `muIn` of `e`. -/
theorem interest_nested_below (G : WeightedGraph V) {e f : V} (h : T.IsAnc e f)
    {lam : ℝ} (hlt : G.cut (T.pairShore e f) < lam) (hf : lam ≤ G.cut (T.subtree f)) :
    G.cut (T.subtree e) < 2 * muIn G (T.subtree e) (T.subtree f) := by
  rw [pairShore_of_isAnc h, cut_sdiff_of_subset G (subtree_subset h)] at hlt
  have : T.subtree e ∩ T.subtree f = T.subtree f := Finset.inter_eq_right.mpr (subtree_subset h)
  rw [muIn, this]
  linarith

omit [LinearOrder V] in
/-- Lemma 35, nested edges: the lower edge is automatically interested in the upper. -/
theorem interest_nested_above (G : WeightedGraph V) {e f : V} (h : T.IsAnc e f)
    (hpos : 0 < G.cut (T.subtree f)) :
    G.cut (T.subtree f) < 2 * muIn G (T.subtree f) (T.subtree e) := by
  have : T.subtree f ∩ T.subtree e = T.subtree f := Finset.inter_eq_left.mpr (subtree_subset h)
  rw [muIn, this, cross_compl]
  linarith

/-! ### Monge rectangles (Lemma 37) -/

/-- The entry `K e f` of a pair-cut matrix. -/
noncomputable def RootedTree.pairCut (G : WeightedGraph V) (e f : V) : ℝ :=
  G.cut (T.pairShore e f)

omit [LinearOrder V] in
/-- Independent case: rows go down one chain, columns down another, and every row is
independent of every column. -/
theorem pairCut_monge_indep (G : WeightedGraph V) {e e' f f' : V}
    (he : T.IsAnc e e') (hf : T.IsAnc f f')
    (hind : ∀ x ∈ ({e, e'} : Finset V), ∀ y ∈ ({f, f'} : Finset V),
      ¬ T.IsAnc x y ∧ ¬ T.IsAnc y x) :
    T.pairCut G e f + T.pairCut G e' f' ≤
      T.pairCut G e f' + T.pairCut G e' f := by
  have i1 := hind e (by simp) f (by simp)
  have i2 := hind e (by simp) f' (by simp)
  have i3 := hind e' (by simp) f (by simp)
  have i4 := hind e' (by simp) f' (by simp)
  unfold RootedTree.pairCut
  rw [pairShore_of_indep i1.1 i1.2, pairShore_of_indep i2.1 i2.2,
    pairShore_of_indep i3.1 i3.2, pairShore_of_indep i4.1 i4.2]
  have hsub := G.cut_submodular (T.subtree e ∪ T.subtree f') (T.subtree e' ∪ T.subtree f)
  have hA := subtree_subset he
  have hB := subtree_subset hf
  have hd1 := disjoint_subtree i1.1 i1.2
  have hd4 := disjoint_subtree i4.1 i4.2
  have hunion : (T.subtree e ∪ T.subtree f') ∪ (T.subtree e' ∪ T.subtree f) =
      T.subtree e ∪ T.subtree f := by
    ext x; simp only [Finset.mem_union]
    constructor
    · rintro ((h | h) | (h | h))
      · exact Or.inl h
      · exact Or.inr (hB h)
      · exact Or.inl (hA h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hinter : (T.subtree e ∪ T.subtree f') ∩ (T.subtree e' ∪ T.subtree f) =
      T.subtree e' ∪ T.subtree f' := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨h | h, h' | h'⟩
      · exact Or.inl h'
      · exact absurd h' (Finset.disjoint_left.mp hd1 h)
      · exact Or.inr h
      · exact Or.inr h
    · rintro (h | h)
      · exact ⟨Or.inl (hA h), Or.inl h⟩
      · exact ⟨Or.inr h, Or.inr (hB h)⟩
  rw [hunion, hinter] at hsub
  linarith

omit [LinearOrder V] in
/-- Nested case: rows go down a chain, columns go up a chain, and every row is an
ancestor of every column. -/
theorem pairCut_monge_nested (G : WeightedGraph V) {e e' f f' : V}
    (he : T.IsAnc e e') (hf : T.IsAnc f' f) (hef : T.IsAnc e' f') :
    T.pairCut G e f + T.pairCut G e' f' ≤
      T.pairCut G e f' + T.pairCut G e' f := by
  have hef' : T.IsAnc e' f := isAnc_trans hef hf
  unfold RootedTree.pairCut
  rw [pairShore_of_isAnc (isAnc_trans he hef'), pairShore_of_isAnc hef,
    pairShore_of_isAnc (isAnc_trans he hef), pairShore_of_isAnc hef']
  have hA := subtree_subset he
  have hB := subtree_subset hf
  have hC := subtree_subset hef
  have hsub := G.cut_submodular (T.subtree e \ T.subtree f') (T.subtree e' \ T.subtree f)
  have hunion : (T.subtree e \ T.subtree f') ∪ (T.subtree e' \ T.subtree f) =
      T.subtree e \ T.subtree f := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact ⟨h, fun hx => h' (hB hx)⟩
      · exact ⟨hA h, h'⟩
    · rintro ⟨h, h'⟩
      by_cases hx : x ∈ T.subtree f'
      · exact Or.inr ⟨hC hx, h'⟩
      · exact Or.inl ⟨h, hx⟩
  have hinter : (T.subtree e \ T.subtree f') ∩ (T.subtree e' \ T.subtree f) =
      T.subtree e' \ T.subtree f' := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨-, h⟩, h', -⟩
      exact ⟨h', h⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨hA h, h'⟩, h, fun hx => h' (hB hx)⟩
  rw [hunion, hinter] at hsub
  linarith

end TwoRespecting
end CutQueryComplexity
