import CutQueryComplexity.GHReduction.FrontierAssemblyProgram
import CutQueryComplexity.GHReduction.FrontierRoundGeometry

/-! # Attachment compatibility with actual frontier cuts

A recursive block tree identifies every pair of original vertices that lie
on the opposite side of one frontier edge. This is a proposition about its
attachment map, not an input field of the algorithm. The lemmas below transfer
it through relabeling and through the actual edge-shore system. Old auxiliary
maps are constant on these opposite sides, so subsequent joins cannot split
an old attachment class.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B C : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

def ForestCompatible (p : V → B) (T : RootedTree B) (forest : B → PackedSteinerTree V) : Prop :=
  ∀ b e, e ≠ T.root → ∀ x y,
    ¬(b ∈ T.D e ↔ p x ∈ T.D e) → ¬(b ∈ T.D e ↔ p y ∈ T.D e) →
      (forest b).value.attach x = (forest b).value.attach y

theorem leafFrontierForest_compatible (state : PublicFrontierState V) :
    ForestCompatible state.block state.tree (leafFrontierForest state) := by
  intro b e he x y hx hy
  rfl

theorem ForestCompatible.unrelabel (p : V → B) (T : RootedTree B) (e : B ≃ C)
    (forest : C → PackedSteinerTree V)
    (h : ForestCompatible (e ∘ p) (relabelRootedTree T e) forest) :
    ForestCompatible p T (fun b => forest (e b)) := by
  intro b u hu x y hx hy
  have heu : e u ≠ (relabelRootedTree T e).root := fun he => hu (e.injective he)
  apply h (e b) (e u) heu x y
  · simpa only [relabelRootedTree_subtree, mem_pull, Equiv.symm_apply_apply,
      Function.comp_apply] using hx
  · simpa only [relabelRootedTree_subtree, mem_pull, Equiv.symm_apply_apply,
      Function.comp_apply] using hy

theorem edgeShore_is_fundamental (T : RootedTree B) (F : Finset (B × B))
    (hTF : ∀ v, v ≠ T.root → SpanTree.Adj F (T.parent v) v)
    (shore : B × B → Finset B) (hshore : EdgeShoreSystem F shore)
    {e : B × B} (he : e ∈ F) :
    ∃ v, v ≠ T.root ∧ (T.D v = shore e ∨ T.D v = (shore e)ᶜ) := by
  obtain ⟨ha, hb, honly⟩ := hshore e he
  have hproper : ProperShore (shore e) :=
    ⟨⟨e.1, ha⟩, fun hfull => hb (hfull ▸ Finset.mem_univ _)⟩
  obtain ⟨v, hv⟩ := T.crossSet_nonempty hproper
  have hcross : T.Crosses (shore e) v := (Finset.mem_filter.mp hv).2
  have hselcross : ¬((selectedParentEdge T F v).1 ∈ shore e ↔
      (selectedParentEdge T F v).2 ∈ shore e) := by
    rcases selectedParentEdge_endpoints T F v with hd | hd
    · simpa only [hd] using hcross.2
    · simpa only [hd, iff_comm] using hcross.2
  have hsel : selectedParentEdge T F v = e :=
    honly _ (selectedParentEdge_mem T F (hTF v hcross.1)) hselcross
  refine ⟨v, hcross.1, ?_⟩
  simpa only [hsel] using edgeShore_fundamental T F hTF shore hshore hcross.1

theorem ForestCompatible.on_edgeShore (p : V → B) (T : RootedTree B)
    (forest : B → PackedSteinerTree V) (h : ForestCompatible p T forest)
    (F : Finset (B × B)) (hTF : ∀ v, v ≠ T.root → SpanTree.Adj F (T.parent v) v)
    (shore : B × B → Finset B) (hshore : EdgeShoreSystem F shore)
    {e : B × B} (he : e ∈ F) (b : B) (x y : V)
    (hx : ¬(b ∈ shore e ↔ p x ∈ shore e)) (hy : ¬(b ∈ shore e ↔ p y ∈ shore e)) :
    (forest b).value.attach x = (forest b).value.attach y := by
  obtain ⟨v, hv, hS | hS⟩ := edgeShore_is_fundamental T F hTF shore hshore he
  · exact h b v hv x y (by simpa only [hS] using hx) (by simpa only [hS] using hy)
  · exact h b v hv x y (by simpa only [hS, Finset.mem_compl, not_iff_not] using hx)
      (by simpa only [hS, Finset.mem_compl, not_iff_not] using hy)

theorem subtree_subset_frontierBranch (T : RootedTree B) (b e : B) (hb : b ∉ T.D e) :
    ∃ f : frontierProxies T b, T.D e ⊆ frontierBranch T b f := by
  have heb : e ≠ b := by
    intro he
    subst e
    exact hb (T.self_mem_D b)
  let f := frontierProxy T b e heb
  have hmem := mem_frontierProxy_branch T b e heb
  change e ∈ frontierBranch T b f at hmem
  by_cases hfb : f.val = b
  · have hebD : e ∉ T.D b := by simpa only [frontierBranch, hfb, ite_true, Finset.mem_compl] using hmem
    have hdisj : Disjoint (T.D e) (T.D b) := by
      rcases T.D_laminar e b with hd | hbe | heb'
      · exact hd
      · exact (hb hbe).elim
      · exact (hebD heb').elim
    refine ⟨f, ?_⟩
    intro x hx
    simp only [frontierBranch, hfb, ite_true, Finset.mem_compl]
    exact fun hxb => Finset.disjoint_left.mp hdisj hx hxb
  · have hef : e ∈ T.D f.val := by simpa only [frontierBranch, hfb, ite_false] using hmem
    exact ⟨f, by simpa only [frontierBranch, hfb, ite_false] using T.D_subset hef⟩

theorem compl_subtree_subset_frontierBranch (T : RootedTree B) (b e : B)
    (he : e ≠ T.root) (hb : b ∈ T.D e) :
    ∃ f : frontierProxies T b, (T.D e)ᶜ ⊆ frontierBranch T b f := by
  have hb0 : b ≠ T.root := fun h => T.root_not_mem_D he (h ▸ hb)
  let f : frontierProxies T b := ⟨b, (mem_frontierProxies T b b).mpr ⟨hb0, Or.inl rfl⟩⟩
  refine ⟨f, ?_⟩
  intro x hx
  simp only [frontierBranch, f, ite_true, Finset.mem_compl]
  exact fun hxb => (Finset.mem_compl.mp hx) (T.D_subset hb hxb)

theorem frontierMap_opposite_edge (p : V → B) (T : RootedTree B) (b e : B)
    (he : e ≠ T.root) (x y : V)
    (hx : ¬(b ∈ T.D e ↔ p x ∈ T.D e)) (hy : ¬(b ∈ T.D e ↔ p y ∈ T.D e)) :
    frontierMap p T b x = frontierMap p T b y := by
  by_cases hb : b ∈ T.D e
  · have hxout : p x ∈ (T.D e)ᶜ := Finset.mem_compl.mpr (by simpa only [hb, true_iff] using hx)
    have hyout : p y ∈ (T.D e)ᶜ := Finset.mem_compl.mpr (by simpa only [hb, true_iff] using hy)
    obtain ⟨f, hf⟩ := compl_subtree_subset_frontierBranch T b e he hb
    rw [(frontierMap_eq_inr p T b x f).mpr (hf hxout),
      (frontierMap_eq_inr p T b y f).mpr (hf hyout)]
  · have hxin : p x ∈ T.D e := by simpa only [hb, false_iff, not_not] using hx
    have hyin : p y ∈ T.D e := by simpa only [hb, false_iff, not_not] using hy
    obtain ⟨f, hf⟩ := subtree_subset_frontierBranch T b e hb
    rw [(frontierMap_eq_inr p T b x f).mpr (hf hxin),
      (frontierMap_eq_inr p T b y f).mpr (hf hyin)]

theorem assembleDisjointStar_attach (r : V) (child : V → PackedSteinerTree V)
    (S : V → Finset V) (value : V → ℝ) (L : List V) (x y : V) :
    ∀ base out, assembleDisjointStar base r child S value L = some out →
      base.value.attach x = base.value.attach y →
      (∀ i ∈ L, (child i).value.attach x = (child i).value.attach y) →
      (∀ i ∈ L, x ∈ S i ↔ y ∈ S i) → out.value.attach x = out.value.attach y := by
  induction L with
  | nil =>
      intro base out hout hbase _ _
      have he : base = out := Option.some.inj hout
      exact he ▸ hbase
  | cons i L ih =>
      intro base out hout hbase hchild hside
      cases hm : checkedSteinerJoin base (child i) (S i)ᶜ r i (value i) with
      | none => simp only [assembleDisjointStar, starAssemblySteps, List.map_cons,
          assembleSteinerSteps, hm, Option.bind_none, reduceCtorEq] at hout
      | some middle =>
          have hmiddle : middle.value.attach x = middle.value.attach y := by
            by_cases hx : x ∈ S i
            · have hy : y ∈ S i := (hside i (by simp)).mp hx
              exact checkedSteinerJoin_attach_right base (child i) (S i)ᶜ r i (value i) hm
                (by simpa only [Finset.mem_compl, not_not] using hx)
                (by simpa only [Finset.mem_compl, not_not] using hy) (hchild i (by simp))
            · have hy : y ∉ S i := fun hy => hx ((hside i (by simp)).mpr hy)
              exact checkedSteinerJoin_attach_left base (child i) (S i)ᶜ r i (value i) hm
                (Finset.mem_compl.mpr hx) (Finset.mem_compl.mpr hy) hbase
          apply ih middle out ?_ hmiddle
            (fun j hj => hchild j (List.mem_cons_of_mem _ hj))
            (fun j hj => hside j (List.mem_cons_of_mem _ hj))
          simpa only [assembleDisjointStar, starAssemblySteps, List.map_cons,
            assembleSteinerSteps, hm, Option.bind_some] using hout

end
end CutQueryComplexity.GHReduction
