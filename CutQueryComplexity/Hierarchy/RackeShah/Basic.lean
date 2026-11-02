import CutQueryComplexity.Graph.EdgeSum
import CutQueryComplexity.Certificate.Flow
import CutQueryComplexity.Hierarchy.Existence.BandwidthPartition

/-! # Boundary measures, supported load graphs and the local contract (Räcke–Shah, M0)

Two boundary weights on the vertices of a cluster `S` of the fixed graph `G`:

* `bd G S v`, the weight of the edges from `v` to the outside of `S` (zero outside `S`);
* `pd G Ps v = bd G (P v) v` for a partition `Ps` of `S`, where `P v` is the part containing `v`;
  it counts the edges leaving the part of `v`, including those leaving `S`.

`Supported Q S` says the load graph `Q` has edges only inside `S`; its cut of any shore is then
the cross weight between the two sides inside `S`. `Local G S Ps Q` is the local cut condition
`min(d_Ps(U ∩ S), d_Ps(S ∖ U)) ≤ c_Q(U)` for every `U`, and `Balanced S Ps` a partition of `S`
into parts of at most half its size.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace RackeShah

open WeightedGraph Finset Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Cross weights -/

omit [Fintype V] [DecidableEq V] in
theorem cross_mono_right (G : WeightedGraph V) (S : Finset V) {T T' : Finset V} (h : T ⊆ T') :
    G.cross S T ≤ G.cross S T' :=
  sum_le_sum fun _ _ => sum_le_sum_of_subset_of_nonneg h fun _ _ _ => G.nonneg _ _

omit [Fintype V] [DecidableEq V] in
theorem cross_mono_left (G : WeightedGraph V) {S S' : Finset V} (h : S ⊆ S') (T : Finset V) :
    G.cross S T ≤ G.cross S' T :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => sum_nonneg fun _ _ => G.nonneg _ _

omit [Fintype V] [DecidableEq V] in
theorem cross_eq_sum_singleton (G : WeightedGraph V) (S T : Finset V) :
    G.cross S T = ∑ v ∈ S, G.cross {v} T := by
  simp [cross]

/-! ## Boundary weight of a cluster -/

/-- The weight of the edges from `v` to the outside of `S`; zero outside `S`. -/
noncomputable def bd (G : WeightedGraph V) (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then G.cross {v} Sᶜ else 0

theorem bd_nonneg (G : WeightedGraph V) (S : Finset V) (v : V) : 0 ≤ bd G S v := by
  unfold bd; split <;> simp [G.cross_nonneg]

theorem bd_of_mem (G : WeightedGraph V) {S : Finset V} {v : V} (hv : v ∈ S) :
    bd G S v = G.cross {v} Sᶜ := by simp [bd, hv]

theorem bd_of_notMem (G : WeightedGraph V) {S : Finset V} {v : V} (hv : v ∉ S) : bd G S v = 0 := by
  simp [bd, hv]

theorem sum_bd (G : WeightedGraph V) (S U : Finset V) :
    ∑ v ∈ U, bd G S v = G.cross (U ∩ S) Sᶜ := by
  unfold bd
  rw [← sum_filter, filter_mem_eq_inter, cross_eq_sum_singleton]

theorem sum_bd_self (G : WeightedGraph V) (S : Finset V) : ∑ v ∈ S, bd G S v = G.cut S := by
  rw [sum_bd, inter_self, cross_compl]

/-- A smaller cluster has a larger boundary at each of its vertices. -/
theorem bd_mono (G : WeightedGraph V) {C S : Finset V} (hCS : C ⊆ S) {v : V} (hv : v ∈ C) :
    bd G S v ≤ bd G C v := by
  rw [bd_of_mem G (hCS hv), bd_of_mem G hv]
  exact cross_mono_right G _ (compl_subset_compl.mpr hCS)

/-- The boundary of `W ⊆ X` at `v ∈ W` is the boundary of `X` plus the edges into `X ∖ W`. -/
theorem bd_split (G : WeightedGraph V) {W X : Finset V} (hW : W ⊆ X) {v : V} (hv : v ∈ W) :
    bd G W v = bd G X v + G.cross {v} (X \ W) := by
  rw [bd_of_mem G hv, bd_of_mem G (hW hv)]
  have hc : Wᶜ = Xᶜ ∪ (X \ W) := by
    ext u; simp only [mem_compl, mem_union, mem_sdiff]; tauto
  have hd : Disjoint Xᶜ (X \ W) := by
    rw [disjoint_left]; intro u hu hu'; exact (mem_compl.mp hu) (mem_sdiff.mp hu').1
  rw [hc, cross_union_right G _ _ _ hd]

/-! ## Boundary measure of a partition -/

/-- The weight of the edges leaving the part of `v`. -/
noncomputable def pd (G : WeightedGraph V) (Ps : Finset (Finset V)) (v : V) : ℝ :=
  ∑ C ∈ Ps, bd G C v

theorem pd_nonneg (G : WeightedGraph V) (Ps : Finset (Finset V)) (v : V) : 0 ≤ pd G Ps v :=
  sum_nonneg fun _ _ => bd_nonneg G _ v

theorem pd_eq_of_mem (G : WeightedGraph V) {S : Finset V} {Ps : Finset (Finset V)}
    (hP : IsPart S Ps) {C : Finset V} (hC : C ∈ Ps) {v : V} (hv : v ∈ C) :
    pd G Ps v = bd G C v := by
  unfold pd
  rw [sum_eq_single C]
  · intro D hD hDC
    exact bd_of_notMem G fun hvD => hDC (IsPart.eq_of_mem_of_inter (h := hP) hD hC hvD hv)
  · intro h; exact absurd hC h

theorem pd_of_notMem (G : WeightedGraph V) {S : Finset V} {Ps : Finset (Finset V)}
    (hP : IsPart S Ps) {v : V} (hv : v ∉ S) : pd G Ps v = 0 :=
  sum_eq_zero fun _ hC => bd_of_notMem G fun hvC => hv (hP.subset hC hvC)

/-- Refining a cluster raises the boundary measure at every vertex. -/
theorem bd_le_pd (G : WeightedGraph V) {S : Finset V} {Ps : Finset (Finset V)} (hP : IsPart S Ps)
    {v : V} (hv : v ∈ S) : bd G S v ≤ pd G Ps v := by
  have : v ∈ Ps.biUnion id := hP.union ▸ hv
  obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp this
  rw [pd_eq_of_mem G hP hC hvC]
  exact bd_mono G (hP.subset hC) hvC

theorem sum_pd (G : WeightedGraph V) (Ps : Finset (Finset V)) (U : Finset V) :
    ∑ v ∈ U, pd G Ps v = ∑ C ∈ Ps, G.cross (U ∩ C) Cᶜ := by
  unfold pd
  rw [sum_comm]
  exact sum_congr rfl fun C _ => sum_bd G C U

theorem sum_pd_inter (G : WeightedGraph V) {S : Finset V} {Ps : Finset (Finset V)}
    (hP : IsPart S Ps) (U : Finset V) : ∑ v ∈ U ∩ S, pd G Ps v = ∑ v ∈ U, pd G Ps v := by
  rw [← sum_filter_add_sum_filter_not U (fun v => v ∈ S), filter_mem_eq_inter]
  rw [sum_eq_zero (s := U.filter fun v => v ∉ S) fun v hv => pd_of_notMem G hP (mem_filter.mp hv).2,
    _root_.add_zero]

theorem sum_pd_nonneg (G : WeightedGraph V) (Ps : Finset (Finset V)) (U : Finset V) :
    0 ≤ ∑ v ∈ U, pd G Ps v :=
  sum_nonneg fun v _ => pd_nonneg G Ps v

/-- The measure of the whole cluster is the total boundary of the parts. -/
theorem sum_pd_self (G : WeightedGraph V) {S : Finset V} {Ps : Finset (Finset V)} (hP : IsPart S Ps) :
    ∑ v ∈ S, pd G Ps v = ∑ C ∈ Ps, G.cut C := by
  rw [sum_pd]
  exact sum_congr rfl fun C hC => by rw [inter_eq_right.mpr (hP.subset hC), cross_compl]

/-! ## Supported load graphs -/

/-- A load graph with edges only inside `S`. -/
def Supported (Q : WeightedGraph V) (S : Finset V) : Prop :=
  ∀ u v, (u ∉ S ∨ v ∉ S) → Q.w u v = 0

namespace Supported

variable {Q : WeightedGraph V} {S : Finset V}

omit [Fintype V] in
theorem cross_eq (h : Supported Q S) (A B : Finset V) :
    Q.cross A B = Q.cross (A ∩ S) (B ∩ S) := by
  unfold cross
  rw [← sum_filter_add_sum_filter_not A (fun u => u ∈ S), filter_mem_eq_inter]
  rw [sum_eq_zero (s := A.filter fun u => u ∉ S) fun u hu => sum_eq_zero fun v _ =>
    h u v (Or.inl (mem_filter.mp hu).2), _root_.add_zero]
  refine sum_congr rfl fun u hu => ?_
  rw [← sum_filter_add_sum_filter_not B (fun v => v ∈ S), filter_mem_eq_inter]
  rw [sum_eq_zero (s := B.filter fun v => v ∉ S) fun v hv => h u v (Or.inr (mem_filter.mp hv).2),
    _root_.add_zero]

theorem cut_eq (h : Supported Q S) (U : Finset V) : Q.cut U = Q.cross (U ∩ S) (S \ U) := by
  rw [← cross_compl, h.cross_eq]
  congr 1
  ext v; simp only [mem_inter, mem_compl, mem_sdiff]; tauto

theorem cut_sdiff (h : Supported Q S) (U : Finset V) : Q.cut (S \ U) = Q.cut U := by
  rw [h.cut_eq, h.cut_eq U, cross_comm]
  congr 1
  · ext v; simp only [mem_inter, mem_sdiff]; tauto
  · ext v; simp only [mem_inter, mem_sdiff]; tauto

theorem cut_inter (h : Supported Q S) (U : Finset V) : Q.cut (U ∩ S) = Q.cut U := by
  rw [h.cut_eq, h.cut_eq U]
  congr 1
  · ext v; simp only [mem_inter]; tauto
  · ext v; simp only [mem_inter, mem_sdiff]; tauto

omit [Fintype V] [DecidableEq V] in
theorem add {Q' : WeightedGraph V} (h : Supported Q S) (h' : Supported Q' S) :
    Supported (Q.add Q') S := by
  intro u v huv
  show Q.w u v + Q'.w u v = 0
  rw [h u v huv, h' u v huv, _root_.add_zero]

omit [Fintype V] [DecidableEq V] in
theorem scale (h : Supported Q S) (c : ℝ) (hc : 0 ≤ c) : Supported (Q.scale c hc) S := by
  intro u v huv
  show c * Q.w u v = 0
  rw [h u v huv, mul_zero]

omit [Fintype V] [DecidableEq V] in
theorem mono {T : Finset V} (h : Supported Q S) (hST : S ⊆ T) : Supported Q T := by
  intro u v huv
  apply h u v
  rcases huv with hu | hv
  · exact Or.inl fun h' => hu (hST h')
  · exact Or.inr fun h' => hv (hST h')

omit [Fintype V] [DecidableEq V] in
theorem zero (S : Finset V) : Supported (0 : WeightedGraph V) S := fun _ _ _ => rfl

omit [Fintype V] in
theorem induce (G : WeightedGraph V) (S : Finset V) : Supported (G.induce S) S := by
  intro u v huv
  show (if u ∈ S ∧ v ∈ S then G.w u v else 0) = 0
  rw [ite_eq_right]
  rintro ⟨hu, hv⟩
  rcases huv with h | h
  · exact h hu
  · exact h hv

omit [DecidableEq V] in
/-- A flow feasible in a load graph supported in `S` conserves flow outside `S`. -/
theorem netOut_eq_zero (h : Supported Q S) {F : V → V → ℝ} (hF : Feasible Q F) {v : V}
    (hv : v ∉ S) : netOut F v = 0 := by
  unfold netOut
  refine sum_eq_zero fun u _ => ?_
  have := hF.2 v u
  rw [h v u (Or.inl hv)] at this
  exact abs_nonpos_iff.mp this

omit [Fintype V] [DecidableEq V] in
theorem w_eq_zero (h : Supported Q S) {u v : V} (huv : ¬ (u ∈ S ∧ v ∈ S)) : Q.w u v = 0 := by
  apply h u v
  by_cases hu : u ∈ S
  · exact Or.inr fun hv => huv ⟨hu, hv⟩
  · exact Or.inl hu

end Supported

omit [Fintype V] in
theorem induce_w (G : WeightedGraph V) (S : Finset V) (u v : V) :
    (G.induce S).w u v = if u ∈ S ∧ v ∈ S then G.w u v else 0 := rfl

theorem induce_w_le (G : WeightedGraph V) (S : Finset V) (u v : V) :
    (G.induce S).w u v ≤ G.w u v := by
  rw [induce_w]; split <;> simp [G.nonneg]

omit [Fintype V] [DecidableEq V] in
theorem scale_w (G : WeightedGraph V) (c : ℝ) (hc : 0 ≤ c) (u v : V) :
    (G.scale c hc).w u v = c * G.w u v := rfl

theorem induce_cut_eq_cross (G : WeightedGraph V) (S U : Finset V) :
    (G.induce S).cut U = G.cross (U ∩ S) (S \ U) :=
  cut_induce G S U

omit [Fintype V] in
theorem inter_union_sdiff_eq (T C : Finset V) : (T ∩ C) ∪ (C \ T) = C := by
  ext v; simp only [mem_union, mem_inter, mem_sdiff]; tauto

omit [Fintype V] in
theorem disjoint_inter_sdiff (T C : Finset V) : Disjoint (T ∩ C) (C \ T) := by
  rw [disjoint_left]; intro v hv hv'; exact (mem_sdiff.mp hv').2 (mem_inter.mp hv).1

/-- A cut splits along any side `T`. -/
theorem cut_eq_cross_side_add (G : WeightedGraph V) (T C : Finset V) :
    G.cut C = G.cross (T ∩ C) Cᶜ + G.cross (C \ T) Cᶜ := by
  rw [← cross_compl, ← cross_union_left G _ _ _ (disjoint_inter_sdiff T C), inter_union_sdiff_eq]

/-- The cut of `U ⊆ S` splits into the part inside `S` and the boundary of `S`. -/
theorem cut_eq_cross_add_bd (G : WeightedGraph V) {U S : Finset V} (hU : U ⊆ S) :
    G.cut U = G.cross U (S \ U) + ∑ v ∈ U, bd G S v := by
  rw [sum_bd, inter_eq_left.mpr hU, ← cross_compl]
  have hc : Uᶜ = (S \ U) ∪ Sᶜ := by
    ext v; simp only [mem_compl, mem_union, mem_sdiff]
    constructor
    · intro hv; by_cases hs : v ∈ S
      · exact Or.inl ⟨hs, hv⟩
      · exact Or.inr hs
    · rintro (⟨-, hv⟩ | hv)
      · exact hv
      · exact fun h => hv (hU h)
  have hd : Disjoint (S \ U) Sᶜ := by
    rw [disjoint_left]; intro v hv hv'; exact (mem_compl.mp hv') (mem_sdiff.mp hv).1
  rw [hc, cross_union_right G _ _ _ hd]

/-! ## The local contract and balanced partitions -/

/-- The local cut condition of a cluster `S` with final parts `Ps` and load graph `Q`. -/
structure Local (G : WeightedGraph V) (S : Finset V) (Ps : Finset (Finset V))
    (Q : WeightedGraph V) : Prop where
  supp : Supported Q S
  cut : ∀ U : Finset V,
    min (∑ v ∈ U ∩ S, pd G Ps v) (∑ v ∈ S \ U, pd G Ps v) ≤ Q.cut U

/-- A partition of `S` into nonempty parts of at most half its size. -/
structure Balanced (S : Finset V) (Ps : Finset (Finset V)) : Prop where
  part : IsPart S Ps
  half : ∀ C ∈ Ps, 2 * C.card ≤ S.card

omit [Fintype V] in
/-- The partition of `S` into singletons is balanced when `|S| ≥ 2`. -/
theorem balanced_singletons {S : Finset V} (h2 : 2 ≤ S.card) :
    Balanced S (S.image fun v => ({v} : Finset V)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro C hC
    obtain ⟨v, -, rfl⟩ := mem_image.mp hC
    exact singleton_nonempty v
  · intro C hC D hD hne
    obtain ⟨v, -, rfl⟩ := mem_image.mp hC
    obtain ⟨w, -, rfl⟩ := mem_image.mp hD
    exact disjoint_singleton.mpr fun h => hne (by rw [h])
  · ext v
    simp only [mem_biUnion, mem_image, id]
    constructor
    · rintro ⟨C, ⟨w, hw, rfl⟩, hv⟩
      rw [mem_singleton.mp hv]; exact hw
    · intro hv; exact ⟨{v}, ⟨v, hv, rfl⟩, mem_singleton_self v⟩
  · intro C hC
    obtain ⟨v, -, rfl⟩ := mem_image.mp hC
    rw [card_singleton]; omega

end RackeShah
end Hierarchy
end CutQueryComplexity
