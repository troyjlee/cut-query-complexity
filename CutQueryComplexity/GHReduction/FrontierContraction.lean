import CutQueryComplexity.GHReduction.PartialTree
import CutQueryComplexity.GHReduction.GuideStructure
import CutQueryComplexity.GHReduction.Specification

/-! # The actual auxiliary graph of a partial-tree block

Deleting a block of the public tree leaves one component per incident edge.
The contraction keeps every original vertex of that block separately and maps
every other original vertex to its component's incident-edge proxy. Thus the
previous frontier cardinality formula counts the real quotient vertex types.
No cut-preservation invariant is assumed in this construction; that is a
separate obligation for minimum-cut computations inside these quotients.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

/-- The block component opposite `b` across one incident parent edge. -/
def frontierBranch (T : RootedTree B) (b : B) (e : frontierProxies T b) : Finset B :=
  if e.val = b then (T.D b)ᶜ else T.D e.val

theorem frontierBranch_excludes (T : RootedTree B) (b : B) (e : frontierProxies T b) :
    b ∉ frontierBranch T b e := by
  obtain ⟨heroot, heb | hparent⟩ := (mem_frontierProxies T b e.val).mp e.property
  · simp [frontierBranch, heb, T.self_mem_D]
  · by_cases heb : e.val = b
    · simp [frontierBranch, heb, T.self_mem_D]
    · simp only [frontierBranch, heb, ite_false, RootedTree.mem_D]
      intro hanc
      have hdepth := hanc.depth_le
      have hstep := T.depth_parent e.val heroot
      rw [hparent] at hstep
      omega

theorem frontierBranch_nonempty (T : RootedTree B) (b : B) (e : frontierProxies T b) :
    (frontierBranch T b e).Nonempty := by
  by_cases heb : e.val = b
  · have hb : b ≠ T.root := heb ▸ ((mem_frontierProxies T b e.val).mp e.property).1
    refine ⟨T.root, ?_⟩
    simp only [frontierBranch, heb, ite_true, Finset.mem_compl]
    exact T.root_not_mem_D hb
  · exact ⟨e.val, by simpa only [frontierBranch, heb, ite_false] using T.self_mem_D e.val⟩

theorem frontierBranch_child_subset (T : RootedTree B) (b : B) (e : frontierProxies T b)
    (heb : e.val ≠ b) : frontierBranch T b e ⊆ T.D b := by
  have hparent := ((mem_frontierProxies T b e.val).mp e.property).2.resolve_left heb
  have hanc : T.IsAnc b e.val := ⟨1, hparent⟩
  simpa only [frontierBranch, heb, ite_false] using T.D_subset ((T.mem_D _ _).mpr hanc)

theorem frontierBranches_disjoint (T : RootedTree B) (b : B)
    {e f : frontierProxies T b} (hef : e ≠ f) :
    Disjoint (frontierBranch T b e) (frontierBranch T b f) := by
  have hefval : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  by_cases heb : e.val = b
  · have hfb : f.val ≠ b := fun h => hefval (heb.trans h.symm)
    apply Finset.disjoint_left.mpr
    intro x hxe hxf
    have hxnot : x ∉ T.D b := by simpa only [frontierBranch, heb, ite_true, Finset.mem_compl] using hxe
    exact hxnot (frontierBranch_child_subset T b f hfb hxf)
  · by_cases hfb : f.val = b
    · apply Finset.disjoint_left.mpr
      intro x hxe hxf
      have hxnot : x ∉ T.D b := by simpa only [frontierBranch, hfb, ite_true, Finset.mem_compl] using hxf
      exact hxnot (frontierBranch_child_subset T b e heb hxe)
    · obtain ⟨he0, heparent⟩ := (mem_frontierProxies T b e.val).mp e.property
      obtain ⟨hf0, hfparent⟩ := (mem_frontierProxies T b f.val).mp f.property
      have hdisj := DirectedCertificate.Completion.disjoint_child_subtrees (centroidTree T)
        he0 hf0 (heparent.resolve_left heb) (hfparent.resolve_left hfb) hefval
      have hsubtree (v : B) : (centroidTree T).subtree v = T.D v := by
        ext x
        rw [TwoRespecting.RootedTree.mem_subtree, T.mem_D]
        rfl
      rw [hsubtree, hsubtree] at hdisj
      simpa only [frontierBranch, heb, hfb, ite_false] using hdisj

theorem exists_frontierBranch (T : RootedTree B) (b c : B) (hcb : c ≠ b) :
    ∃ e : frontierProxies T b, c ∈ frontierBranch T b e := by
  by_cases hanc : T.IsAnc b c
  · obtain ⟨e, he0, heparent, heanc⟩ :=
      DirectedCertificate.Completion.exists_child_ancestor (centroidTree T) hanc hcb
    change T.parent e = b at heparent
    change T.IsAnc e c at heanc
    have heb : e ≠ b := by
      intro heb
      have hstep := T.depth_parent e he0
      rw [heparent, heb] at hstep
      omega
    let proxy : frontierProxies T b := ⟨e, (mem_frontierProxies T b e).mpr ⟨he0, Or.inr heparent⟩⟩
    refine ⟨proxy, ?_⟩
    simpa only [frontierBranch, proxy, heb, ite_false, RootedTree.mem_D] using heanc
  · have hb0 : b ≠ T.root := by
      intro hb
      exact hanc (hb.symm ▸ T.isAnc_root c)
    let proxy : frontierProxies T b := ⟨b, (mem_frontierProxies T b b).mpr ⟨hb0, Or.inl rfl⟩⟩
    exact ⟨proxy, by simpa only [frontierBranch, proxy, ite_true, Finset.mem_compl, RootedTree.mem_D] using hanc⟩

def frontierProxy (T : RootedTree B) (b c : B) (hcb : c ≠ b) : frontierProxies T b :=
  Classical.choose (exists_frontierBranch T b c hcb)

theorem mem_frontierProxy_branch (T : RootedTree B) (b c : B) (hcb : c ≠ b) :
    c ∈ frontierBranch T b (frontierProxy T b c hcb) :=
  Classical.choose_spec (exists_frontierBranch T b c hcb)

theorem frontierProxy_eq_iff (T : RootedTree B) (b c : B) (hcb : c ≠ b)
    (e : frontierProxies T b) : frontierProxy T b c hcb = e ↔ c ∈ frontierBranch T b e := by
  constructor
  · intro he
    simpa only [he] using mem_frontierProxy_branch T b c hcb
  · intro hc
    by_contra hne
    exact Finset.disjoint_left.mp (frontierBranches_disjoint T b hne)
      (mem_frontierProxy_branch T b c hcb) hc

/-- The only inputs are the public partition and public tree topology. -/
def frontierMap (p : V → B) (T : RootedTree B) (b : B) (v : V) : FrontierVertex p T b :=
  if hv : p v = b then Sum.inl ⟨v, (mem_fiber p b v).mpr hv⟩
  else Sum.inr (frontierProxy T b (p v) hv)

theorem frontierMap_eq_inl (p : V → B) (T : RootedTree B) (b : B) (v : V) (u : fiber p b) :
    frontierMap p T b v = Sum.inl u ↔ v = u.val := by
  change ((if h : p v = b then Sum.inl ⟨v, (mem_fiber p b v).mpr h⟩
    else Sum.inr (frontierProxy T b (p v) h)) : (fiber p b) ⊕ (frontierProxies T b)) =
      Sum.inl u ↔ v = u.val
  by_cases hv : p v = b
  · rw [dite_eq_left hv]
    simp only [Sum.inl.injEq, Subtype.ext_iff]
  · have hu : p u.val = b := (mem_fiber p b u.val).mp u.property
    have hne : v ≠ u.val := fun he => hv (he.symm ▸ hu)
    simp [hv, hne]

theorem frontierMap_eq_inr (p : V → B) (T : RootedTree B) (b : B) (v : V)
    (e : frontierProxies T b) :
    frontierMap p T b v = Sum.inr e ↔ p v ∈ frontierBranch T b e := by
  change ((if h : p v = b then Sum.inl ⟨v, (mem_fiber p b v).mpr h⟩
    else Sum.inr (frontierProxy T b (p v) h)) : (fiber p b) ⊕ (frontierProxies T b)) =
      Sum.inr e ↔ p v ∈ frontierBranch T b e
  by_cases hv : p v = b
  · rw [dite_eq_left hv]
    simp only [Sum.inl_ne_inr, false_iff, hv]
    exact frontierBranch_excludes T b e
  · rw [dite_eq_right hv]
    simp only [Sum.inr.injEq]
    exact frontierProxy_eq_iff T b (p v) hv e

theorem frontierMap_surjective (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) : Function.Surjective (frontierMap p T b) := by
  intro z
  cases z with
  | inl u => exact ⟨u.val, (frontierMap_eq_inl p T b u.val u).mpr rfl⟩
  | inr e =>
    obtain ⟨c, hc⟩ := frontierBranch_nonempty T b e
    obtain ⟨v, hv⟩ := hp c
    exact ⟨v, (frontierMap_eq_inr p T b v e).mpr (hv.symm ▸ hc)⟩

theorem frontierMap_original_fiber (p : V → B) (T : RootedTree B) (b : B) (u : fiber p b) :
    fiber (frontierMap p T b) (Sum.inl u) = {u.val} := by
  ext v
  simpa only [Finset.mem_singleton] using
    (mem_fiber (frontierMap p T b) (Sum.inl u) v).trans (frontierMap_eq_inl p T b v u)

theorem frontierMap_proxy_fiber (p : V → B) (T : RootedTree B) (b : B)
    (e : frontierProxies T b) :
    fiber (frontierMap p T b) (Sum.inr e) = pull p (frontierBranch T b e) := by
  ext v
  exact (mem_fiber (frontierMap p T b) (Sum.inr e) v).trans
    ((frontierMap_eq_inr p T b v e).trans (mem_pull p (frontierBranch T b e) v).symm)

theorem frontier_contraction_promise {M : ℕ} (G : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (T : RootedTree B) (b : B) :
    InputPromise M (G.contract (frontierMap p T b)) :=
  ⟨integral_contract G hG.1 _, (edgeMass_contract_le G _).trans hG.2⟩

theorem frontier_contraction_cut (G : WeightedGraph V) (p : V → B) (T : RootedTree B)
    (b : B) (S : Finset (FrontierVertex p T b)) :
    (G.contract (frontierMap p T b)).cut S = G.cut (pull (frontierMap p T b) S) :=
  cut_contract G _ S

/-- Surjectivity and the exact type count are now facts about the same graph
used by the oracle simulation, not unrelated scalar bookkeeping. -/
theorem actual_frontier_vertex_sum (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) :
    (∀ b, Function.Surjective (frontierMap p T b)) ∧
      (∑ b, Fintype.card (FrontierVertex p T b)) =
        Fintype.card V + 2 * (Fintype.card B - 1) ∧
      (∑ b, Fintype.card (FrontierVertex p T b)) ≤ 3 * Fintype.card V :=
  ⟨fun b => frontierMap_surjective p hp T b,
    frontier_vertex_sum p T, frontier_vertex_sum_le p hp T⟩

end
end CutQueryComplexity.GHReduction
