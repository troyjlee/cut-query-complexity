import CutQueryComplexity.Hierarchy.RackeShah.Basic
import CutQueryComplexity.Hierarchy.Children
import CutQueryComplexity.Hierarchy.TerminalCuts

/-! # The weighted-majority bound and the transfer lemma (Räcke–Shah, M1)

`rep_le_two_mul_sum_cut`: for a hierarchy with childless terminal nodes and nonempty clusters,
if every internal node `x` carries a load graph `Q x` satisfying the local contract with respect
to its children's clusters, then for every shore `A`

  `R(A) ≤ 2 ∑_x c_{Q x}(A)`

with canonical capacities. The labelling of `A` puts each internal node on the side of larger
children's boundary measure, and each terminal node on its prescribed side. At an internal node
whose minority side is `T`, the crossed children's canonical capacities split into the part on
the `T` side, charged to the node's local cut, and the part on the other side, charged to the
crossed child's own local cut (zero for a terminal child, whose cluster lies entirely on one
side). Each local cut is charged at most twice.

`local_of_flow` is the transfer lemma: if the measure of a refinement `Ps₁` of `Ps₀` is routed by
a flow feasible in `q` to a receiving function at most `A` times the measure of `Ps₀`, and `Ps₀`
satisfies the expansion inequality with factor `f`, then `Ps₁` satisfies the local contract with
the load graph `A f G[S] + q`.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace RackeShah

open WeightedGraph Finset Certificate

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

/-! ## Children clusters as a partition -/

/-- The clusters of the children of a node. -/
def childParts (H : Hier V N) (x : N) : Finset (Finset V) := (H.children x).image H.cluster

theorem cluster_leaf_of_leafChildless (H : Hier V N) (hlc : H.LeafChildless) (v : V) :
    H.cluster (H.leaf v) = {v} := by
  ext u
  rw [Hier.mem_cluster, mem_singleton]
  constructor
  · intro h
    by_contra hne
    have hne' : H.leaf v ≠ H.leaf u := fun he => hne (H.leaf_inj he).symm
    obtain ⟨c, hc, -⟩ := Hier.exists_child h hne'
    rw [hlc v] at hc
    exact notMem_empty c hc
  · rintro rfl
    exact TwoRespecting.RootedTree.isAnc_refl _

omit [DecidableEq V] in
theorem cluster_injOn_children (H : Hier V N) (hne : ∀ x, (H.cluster x).Nonempty) (x : N) :
    Set.InjOn H.cluster (H.children x : Set N) := by
  intro c hc d hd hcd
  obtain ⟨v, hv⟩ := hne c
  have hvd : v ∈ H.cluster d := hcd ▸ hv
  exact Hier.child_unique hc hd (Hier.mem_cluster.mp hv) (Hier.mem_cluster.mp hvd)

theorem childParts_isPart (H : Hier V N) (hne : ∀ x, (H.cluster x).Nonempty) {x : N}
    (hx : ¬ H.IsLeaf x) : IsPart (H.cluster x) (childParts H x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨c, -, rfl⟩ := mem_image.mp hC
    exact hne c
  · intro C hC D hD hCD
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hC
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hD
    rw [Function.onFun, disjoint_left]
    intro v hvc hvd
    exact hCD (congrArg H.cluster
      (Hier.child_unique hc hd (Hier.mem_cluster.mp hvc) (Hier.mem_cluster.mp hvd)))
  · ext v
    rw [mem_biUnion]
    constructor
    · rintro ⟨C, hC, hv⟩
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hC
      simp only [id] at hv
      exact Hier.mem_cluster.mpr (Hier.isAnc_of_mem_children hc (Hier.mem_cluster.mp hv))
    · intro hv
      have hne' : x ≠ H.leaf v := fun he => hx ⟨v, he.symm⟩
      obtain ⟨c, hc, hcv⟩ := Hier.exists_child (Hier.mem_cluster.mp hv) hne'
      exact ⟨H.cluster c, mem_image_of_mem _ hc, Hier.mem_cluster.mpr hcv⟩

theorem sum_childParts (H : Hier V N) (hne : ∀ x, (H.cluster x).Nonempty) (x : N)
    (g : Finset V → ℝ) : ∑ C ∈ childParts H x, g C = ∑ c ∈ H.children x, g (H.cluster c) :=
  sum_image (cluster_injOn_children H hne x)

/-! ## The majority labelling -/

/-- Label internal nodes by the side of larger children's boundary measure, terminal nodes by
their prescribed side. -/
noncomputable def majLabel (H : Hier V N) (G : WeightedGraph V) (A : Finset V) (x : N) : Bool :=
  if H.IsLeaf x then decide (H.cluster x ⊆ A)
  else decide (∑ v ∈ H.cluster x \ A, pd G (childParts H x) v <
    ∑ v ∈ H.cluster x ∩ A, pd G (childParts H x) v)

theorem majLabel_extends (H : Hier V N) (hlc : H.LeafChildless) (G : WeightedGraph V)
    (A : Finset V) : H.Extends A (majLabel H G A) := by
  intro v
  have hl : H.IsLeaf (H.leaf v) := ⟨v, rfl⟩
  have hc : H.cluster (H.leaf v) ⊆ A ↔ v ∈ A := by
    rw [cluster_leaf_of_leafChildless H hlc, singleton_subset_iff]
  simp only [majLabel, ite_eq_left hl, hc]

/-- For an internal node `c` and a side `T` with the smaller children's measure, the boundary of
`T ∩ C` is at most the local cut of `T`. -/
theorem cross_side_le_cut (H : Hier V N) (G : WeightedGraph V) (Q : N → WeightedGraph V)
    (hne : ∀ x, (H.cluster x).Nonempty)
    (hloc : ∀ x, ¬ H.IsLeaf x → Local G (H.cluster x) (childParts H x) (Q x)) {c : N}
    (hc : ¬ H.IsLeaf c) (T : Finset V)
    (hT : ∑ v ∈ T ∩ H.cluster c, pd G (childParts H c) v ≤
      ∑ v ∈ H.cluster c \ T, pd G (childParts H c) v) :
    G.cross (T ∩ H.cluster c) (H.cluster c)ᶜ ≤ (Q c).cut T := by
  have hP := childParts_isPart H hne hc
  calc G.cross (T ∩ H.cluster c) (H.cluster c)ᶜ
      = ∑ v ∈ T ∩ H.cluster c, bd G (H.cluster c) v := by
        rw [sum_bd, inter_assoc, inter_self]
    _ ≤ ∑ v ∈ T ∩ H.cluster c, pd G (childParts H c) v :=
        sum_le_sum fun v hv => bd_le_pd G hP (mem_inter.mp hv).2
    _ ≤ min (∑ v ∈ T ∩ H.cluster c, pd G (childParts H c) v)
          (∑ v ∈ H.cluster c \ T, pd G (childParts H c) v) := le_min le_rfl hT
    _ ≤ (Q c).cut T := (hloc c hc).cut T

/-- The charging at one internal node, for a minority side `T`. -/
theorem node_charge (H : Hier V N) (G : WeightedGraph V) (Q : N → WeightedGraph V)
    (hne : ∀ x, (H.cluster x).Nonempty)
    (hloc : ∀ x, ¬ H.IsLeaf x → Local G (H.cluster x) (childParts H x) (Q x)) {u : N}
    (hu : ¬ H.IsLeaf u) (ℓ : N → Bool) (A T : Finset V)
    (hmin : ∑ v ∈ T ∩ H.cluster u, pd G (childParts H u) v ≤
      ∑ v ∈ H.cluster u \ T, pd G (childParts H u) v)
    (hcross : ∀ c ∈ H.children u, ℓ c ≠ ℓ u →
      G.cross (H.cluster c \ T) (H.cluster c)ᶜ ≤ if H.IsLeaf c then 0 else (Q c).cut A) :
    (∑ c ∈ H.children u, if ℓ c ≠ ℓ u then G.cut (H.cluster c) else 0) ≤
      (Q u).cut T + ∑ c ∈ H.children u, if H.IsLeaf c then 0 else (Q c).cut A := by
  have hsplit : ∀ c, G.cut (H.cluster c) =
      G.cross (T ∩ H.cluster c) (H.cluster c)ᶜ + G.cross (H.cluster c \ T) (H.cluster c)ᶜ :=
    fun c => cut_eq_cross_side_add G T (H.cluster c)
  have h1 : (∑ c ∈ H.children u, if ℓ c ≠ ℓ u then G.cross (T ∩ H.cluster c) (H.cluster c)ᶜ else 0)
      ≤ (Q u).cut T := by
    calc _ ≤ ∑ c ∈ H.children u, G.cross (T ∩ H.cluster c) (H.cluster c)ᶜ :=
          sum_le_sum fun c _ => by split <;> simp [G.cross_nonneg]
      _ = ∑ v ∈ T ∩ H.cluster u, pd G (childParts H u) v := by
          rw [sum_pd, sum_childParts H hne]
          refine sum_congr rfl fun c hc => ?_
          have hsub := (childParts_isPart H hne hu).subset (mem_image_of_mem H.cluster hc)
          have hset : (T ∩ H.cluster u) ∩ H.cluster c = T ∩ H.cluster c := by
            ext v; simp only [mem_inter]; constructor
            · rintro ⟨⟨hT, -⟩, hc⟩; exact ⟨hT, hc⟩
            · rintro ⟨hT, hc⟩; exact ⟨⟨hT, hsub hc⟩, hc⟩
          rw [hset]
      _ ≤ min _ _ := le_min le_rfl hmin
      _ ≤ (Q u).cut T := (hloc u hu).cut T
  have h2 : (∑ c ∈ H.children u, if ℓ c ≠ ℓ u then G.cross (H.cluster c \ T) (H.cluster c)ᶜ else 0)
      ≤ ∑ c ∈ H.children u, if H.IsLeaf c then 0 else (Q c).cut A := by
    refine sum_le_sum fun c hc => ?_
    by_cases h : ℓ c ≠ ℓ u
    · rw [ite_eq_left h]; exact hcross c hc h
    · rw [ite_eq_right h]
      split <;> simp [(Q c).cut_nonneg]
  calc (∑ c ∈ H.children u, if ℓ c ≠ ℓ u then G.cut (H.cluster c) else 0)
      = (∑ c ∈ H.children u, if ℓ c ≠ ℓ u then G.cross (T ∩ H.cluster c) (H.cluster c)ᶜ else 0) +
        ∑ c ∈ H.children u, if ℓ c ≠ ℓ u then G.cross (H.cluster c \ T) (H.cluster c)ᶜ else 0 := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun c _ => ?_
        split_ifs <;> simp [hsplit c]
    _ ≤ _ := add_le_add h1 h2

/-- The crossed children of an internal node are charged to its local cut and to their own. -/
theorem crossed_children_le (H : Hier V N) (hlc : H.LeafChildless) (G : WeightedGraph V)
    (Q : N → WeightedGraph V) (hne : ∀ x, (H.cluster x).Nonempty)
    (hloc : ∀ x, ¬ H.IsLeaf x → Local G (H.cluster x) (childParts H x) (Q x)) {u : N}
    (hu : ¬ H.IsLeaf u) (A : Finset V) :
    (∑ c ∈ H.children u, if majLabel H G A c ≠ majLabel H G A u then G.cut (H.cluster c) else 0)
      ≤ (Q u).cut A + ∑ c ∈ H.children u, if H.IsLeaf c then 0 else (Q c).cut A := by
  set ℓ := majLabel H G A
  have hℓu : ℓ u = decide (∑ v ∈ H.cluster u \ A, pd G (childParts H u) v <
      ∑ v ∈ H.cluster u ∩ A, pd G (childParts H u) v) := by
    simp only [ℓ, majLabel, ite_eq_right hu]
  have hℓc : ∀ c, ¬ H.IsLeaf c → ℓ c = decide (∑ v ∈ H.cluster c \ A, pd G (childParts H c) v <
      ∑ v ∈ H.cluster c ∩ A, pd G (childParts H c) v) := by
    intro c hc; simp only [ℓ, majLabel, ite_eq_right hc]
  have hℓl : ∀ c, H.IsLeaf c → ℓ c = decide (H.cluster c ⊆ A) := by
    intro c hc; simp only [ℓ, majLabel, ite_eq_left hc]
  have hAc : ∀ C : Finset V, C \ Aᶜ = A ∩ C := by
    intro C; ext v; simp only [mem_sdiff, mem_compl, mem_inter, not_not]; tauto
  have hAi : ∀ C : Finset V, Aᶜ ∩ C = C \ A := by
    intro C; ext v; simp only [mem_inter, mem_compl, mem_sdiff]; tauto
  have hleaf_cluster : ∀ c, H.IsLeaf c → ∃ v, H.cluster c = {v} := by
    rintro c ⟨v, rfl⟩; exact ⟨v, cluster_leaf_of_leafChildless H hlc v⟩
  by_cases hmaj : ∑ v ∈ H.cluster u \ A, pd G (childParts H u) v <
      ∑ v ∈ H.cluster u ∩ A, pd G (childParts H u) v
  · -- the node is black: the minority side is `Aᶜ`, crossed children are white
    have hu' : ℓ u = true := by rw [hℓu, decide_eq_true hmaj]
    have := node_charge H G Q hne hloc hu ℓ A Aᶜ (by rw [hAi, hAc, inter_comm]; exact hmaj.le) ?_
    · rwa [cut_compl] at this
    intro c hc hcu
    rw [hu'] at hcu
    rw [hAc]
    split_ifs with hl
    · obtain ⟨v, hv⟩ := hleaf_cluster c hl
      have hiff : H.cluster c ⊆ A ↔ v ∈ A := by rw [hv, singleton_subset_iff]
      rw [hℓl c hl] at hcu
      simp only [hiff] at hcu
      have hvA : v ∉ A := fun h => hcu (by simp [h])
      rw [hv]
      have : A ∩ {v} = ∅ := by ext w; simp only [mem_inter, mem_singleton, notMem_empty, iff_false, not_and]; rintro hw rfl; exact hvA hw
      rw [this]; simp
    · rw [hℓc c hl] at hcu
      have hle : ∑ v ∈ H.cluster c ∩ A, pd G (childParts H c) v ≤
          ∑ v ∈ H.cluster c \ A, pd G (childParts H c) v := by
        by_contra h; push Not at h
        exact hcu (by rw [decide_eq_true h])
      have := cross_side_le_cut H G Q hne hloc hl A (by rw [inter_comm]; exact hle)
      exact this
  · -- the node is white: the minority side is `A`, crossed children are black
    have hu' : ℓ u = false := by rw [hℓu, decide_eq_false hmaj]
    push Not at hmaj
    refine node_charge H G Q hne hloc hu ℓ A A (by rw [inter_comm]; exact hmaj) ?_
    intro c hc hcu
    rw [hu'] at hcu
    split_ifs with hl
    · obtain ⟨v, hv⟩ := hleaf_cluster c hl
      have hiff : H.cluster c ⊆ A ↔ v ∈ A := by rw [hv, singleton_subset_iff]
      rw [hℓl c hl] at hcu
      simp only [hiff] at hcu
      have hvA : v ∈ A := by
        by_contra h
        exact hcu (by simp [h])
      rw [hv]
      have : ({v} : Finset V) \ A = ∅ := by ext w; simp only [mem_sdiff, mem_singleton, notMem_empty, iff_false, not_and]; rintro rfl; exact fun h => h hvA
      rw [this]; simp
    · rw [hℓc c hl] at hcu
      have hlt : ∑ v ∈ H.cluster c \ A, pd G (childParts H c) v <
          ∑ v ∈ H.cluster c ∩ A, pd G (childParts H c) v := by
        by_contra h
        exact hcu (by rw [decide_eq_false h])
      have := cross_side_le_cut H G Q hne hloc hl Aᶜ (by rw [hAi, hAc, inter_comm]; exact hlt.le)
      rw [hAi, cut_compl] at this
      exact this

/-- **Weighted majority.** With canonical capacities, every shore costs at most twice the total
local load cut. -/
theorem rep_le_two_mul_sum_cut (H : Hier V N) (hlc : H.LeafChildless) (G : WeightedGraph V)
    (Q : N → WeightedGraph V) (hne : ∀ x, (H.cluster x).Nonempty)
    (hloc : ∀ x, ¬ H.IsLeaf x → Local G (H.cluster x) (childParts H x) (Q x)) (A : Finset V) :
    H.rep (H.canon G) A ≤ 2 * ∑ x, (Q x).cut A := by
  refine (H.rep_le _ (majLabel_extends H hlc G A)).trans ?_
  rw [Hier.labelCost_eq_sum_crossed, Hier.crossed, sum_filter, Hier.sum_edges_eq_sum_children]
  set ℓ := majLabel H G A
  calc (∑ u, ∑ c ∈ H.children u, if ℓ c ≠ ℓ (H.T.parent c) then H.canon G c else 0)
      = ∑ u, ∑ c ∈ H.children u, if ℓ c ≠ ℓ u then G.cut (H.cluster c) else 0 := by
        refine sum_congr rfl fun u _ => sum_congr rfl fun c hc => ?_
        rw [(Hier.mem_children.mp hc).2]; rfl
    _ ≤ ∑ u, ((Q u).cut A + ∑ c ∈ H.children u, if H.IsLeaf c then 0 else (Q c).cut A) := by
        refine sum_le_sum fun u _ => ?_
        by_cases hu : H.IsLeaf u
        · obtain ⟨v, rfl⟩ := hu
          rw [hlc v, sum_empty, sum_empty, _root_.add_zero]
          exact (Q _).cut_nonneg A
        · exact crossed_children_le H hlc G Q hne hloc hu A
    _ = ∑ u, (Q u).cut A + ∑ c ∈ H.edges, if H.IsLeaf c then 0 else (Q c).cut A := by
        rw [sum_add_distrib, Hier.sum_edges_eq_sum_children]
    _ ≤ ∑ u, (Q u).cut A + ∑ c, (Q c).cut A := by
        gcongr
        refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun c _ _ => ?_).trans
          (sum_le_sum fun c _ => ?_)
        · split <;> simp [(Q c).cut_nonneg]
        · split <;> simp [(Q c).cut_nonneg]
    _ = 2 * ∑ x, (Q x).cut A := by ring

/-! ## The transfer lemma -/

/-- **Transfer.** Routing the refined measure to at most `A` times the coarse measure through a
flow feasible in `q` turns the expansion inequality of the coarse partition into the local
contract of the refined one, with load graph `A f G[S] + q`. -/
theorem local_of_flow (G : WeightedGraph V) (S : Finset V) (Ps₀ Ps₁ : Finset (Finset V))
    {f A : ℝ} (hf : 0 ≤ f) (hA : 0 ≤ A)
    (q : WeightedGraph V) (hq : Supported q S) (F : V → V → ℝ) (hF : Feasible q F) (r : V → ℝ)
    (hdiv : ∀ v ∈ S, netOut F v = pd G Ps₁ v - r v) (hr : ∀ v ∈ S, r v ≤ A * pd G Ps₀ v)
    (hexp : ∀ U : Finset V, min (∑ v ∈ U ∩ S, pd G Ps₀ v) (∑ v ∈ S \ U, pd G Ps₀ v) ≤
      f * G.cross (U ∩ S) (S \ U)) :
    Local G S Ps₁ (((G.induce S).scale (A * f) (mul_nonneg hA hf)).add q) := by
  refine ⟨(Supported.induce G S).scale _ _ |>.add hq, fun U => ?_⟩
  -- weak duality on a side `X ⊆ S`
  have hside : ∀ X ⊆ S, ∑ v ∈ X, pd G Ps₁ v ≤ q.cut X + A * ∑ v ∈ X, pd G Ps₀ v := by
    intro X hX
    have h1 : ∑ v ∈ X, pd G Ps₁ v = ∑ v ∈ X, netOut F v + ∑ v ∈ X, r v := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun v hv => by rw [hdiv v (hX hv)]; ring
    have h2 := sum_netOut_le_cut hF X
    have h3 : ∑ v ∈ X, r v ≤ A * ∑ v ∈ X, pd G Ps₀ v := by
      rw [mul_sum]; exact sum_le_sum fun v hv => hr v (hX hv)
    linarith
  rw [cut_add, cut_scale, induce_cut_eq_cross]
  have hq1 : q.cut (U ∩ S) = q.cut U := hq.cut_inter U
  have hq2 : q.cut (S \ U) = q.cut U := hq.cut_sdiff U
  have hU := hside (U ∩ S) inter_subset_right
  have hU' := hside (S \ U) sdiff_subset
  rw [hq1] at hU
  rw [hq2] at hU'
  have he := hexp U
  rcases le_total (∑ v ∈ U ∩ S, pd G Ps₀ v) (∑ v ∈ S \ U, pd G Ps₀ v) with h | h
  · rw [min_eq_left h] at he
    calc min (∑ v ∈ U ∩ S, pd G Ps₁ v) (∑ v ∈ S \ U, pd G Ps₁ v)
        ≤ ∑ v ∈ U ∩ S, pd G Ps₁ v := min_le_left _ _
      _ ≤ q.cut U + A * ∑ v ∈ U ∩ S, pd G Ps₀ v := hU
      _ ≤ q.cut U + A * (f * G.cross (U ∩ S) (S \ U)) := by gcongr
      _ = _ := by ring
  · rw [min_eq_right h] at he
    calc min (∑ v ∈ U ∩ S, pd G Ps₁ v) (∑ v ∈ S \ U, pd G Ps₁ v)
        ≤ ∑ v ∈ S \ U, pd G Ps₁ v := min_le_right _ _
      _ ≤ q.cut U + A * ∑ v ∈ S \ U, pd G Ps₀ v := hU'
      _ ≤ q.cut U + A * (f * G.cross (U ∩ S) (S \ U)) := by gcongr
      _ = _ := by ring

end RackeShah
end Hierarchy
end CutQueryComplexity
