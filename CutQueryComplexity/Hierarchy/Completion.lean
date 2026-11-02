import CutQueryComplexity.Hierarchy.Error
import CutQueryComplexity.Discovery.Quantile
import CutQueryComplexity.TwoRespecting.Cuts
import CutQueryComplexity.Search.Subst

/-! # Completion without a depth factor (Lemma 17)

Order the vertices by the preorder of their leaves; every cluster is then an
interval. For each tree edge `x` with cluster `A`, query `d_A = c_G(A)` and run the
quantile checkpoints (Lemma 16) on both boundary measures of `A`,
`μ^out_A(X) = w(A, X ∖ A)` and `μ^in_A(X) = w(A ∩ X, Aᶜ)`, each prefix mass costing
two cut queries. Any nonnegative graph `F` matching the recorded cluster cuts and
prefix masses satisfies `|M_F(A,B) − M_G(A,B)| ≤ (2/q) min(d_A, d_B)` for all
clusters `A, B` (`completion_spec`). The completion is chosen offline.
-/

namespace CutQueryComplexity
namespace Hierarchy

open TwoRespecting WeightedGraph Search Search.Comp Discovery Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Interactions in terms of boundary measures -/

/-- The cluster interaction is the weight inside both sets to outside both, minus the
weight between the two differences. -/
theorem interact_eq (G : WeightedGraph V) (A B : Finset V) :
    interact G A B = G.cross (A ∩ B) (A ∪ B)ᶜ - G.cross (A \ B) (B \ A) := by
  unfold interact cutForm ind
  have h : (∑ u, ∑ v, G.w u v * (((if u ∈ A then (1 : ℝ) else 0) - (if v ∈ A then 1 else 0)) *
      ((if u ∈ B then (1 : ℝ) else 0) - (if v ∈ B then 1 else 0)))) =
      (G.cross (A ∩ B) (A ∪ B)ᶜ + G.cross (A ∪ B)ᶜ (A ∩ B)) -
        (G.cross (A \ B) (B \ A) + G.cross (B \ A) (A \ B)) := by
    simp only [cross_eq_sum_ite, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases ha : u ∈ A <;> by_cases hb : u ∈ B <;> by_cases hc : v ∈ A <;>
      by_cases hd : v ∈ B <;> simp [ha, hb, hc, hd]
  rw [h, G.cross_comm (A ∪ B)ᶜ, G.cross_comm (B \ A)]
  ring

theorem interact_of_disjoint (G : WeightedGraph V) {A B : Finset V} (h : Disjoint A B) :
    interact G A B = - muOut G A B := by
  rw [interact_eq, Finset.disjoint_iff_inter_eq_empty.mp h, muOut,
    Finset.sdiff_eq_self_of_disjoint h, Finset.sdiff_eq_self_of_disjoint h.symm]
  simp

theorem interact_of_subset (G : WeightedGraph V) {A B : Finset V} (h : B ⊆ A) :
    interact G A B = muIn G A B := by
  rw [interact_eq, Finset.union_eq_left.mpr h, Finset.sdiff_eq_empty_iff_subset.mpr h, muIn]
  simp

theorem interact_of_supset (G : WeightedGraph V) {A B : Finset V} (h : A ⊆ B) :
    interact G A B = G.cut A - muOut G A B := by
  rw [interact_eq, Finset.inter_eq_left.mpr h, Finset.union_eq_right.mpr h,
    Finset.sdiff_eq_empty_iff_subset.mpr h, muOut]
  have hsplit : G.cut A = G.cross A Bᶜ + G.cross A (B \ A) := by
    rw [← cross_compl, ← G.cross_union_right]
    · congr 1; ext v; simp only [mem_compl, mem_union, mem_sdiff]; tauto
    · exact Finset.disjoint_left.mpr fun v h1 h2 => (mem_compl.mp h1) (mem_sdiff.mp h2).1
  simp only [cross_empty_left, sub_zero]
  linarith

theorem muOut_le_cut (G : WeightedGraph V) (A X : Finset V) : muOut G A X ≤ G.cut A := by
  rw [muOut, ← cross_compl]
  exact cross_mono_right G A fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2

theorem muIn_le_cut (G : WeightedGraph V) (A X : Finset V) : muIn G A X ≤ G.cut A := by
  rw [muIn, ← cross_compl]
  exact cross_mono_left G _ Finset.inter_subset_left

theorem muOut_nonneg (G : WeightedGraph V) (A X : Finset V) : 0 ≤ muOut G A X :=
  G.cross_nonneg _ _

theorem muIn_nonneg (G : WeightedGraph V) (A X : Finset V) : 0 ≤ muIn G A X :=
  G.cross_nonneg _ _

/-! ### Point masses -/

/-- Point mass of `μ^out_A` at `v`. -/
def massOut (G : WeightedGraph V) (A : Finset V) (v : V) : ℝ :=
  if v ∈ A then 0 else ∑ u ∈ A, G.w u v

/-- Point mass of `μ^in_A` at `v`. -/
def massIn (G : WeightedGraph V) (A : Finset V) (v : V) : ℝ :=
  if v ∈ A then ∑ u ∈ Aᶜ, G.w v u else 0

omit [Fintype V] in
theorem muOut_eq_sum (G : WeightedGraph V) (A X : Finset V) :
    muOut G A X = ∑ v ∈ X, massOut G A v := by
  unfold muOut cross massOut
  rw [Finset.sum_comm, Finset.sdiff_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => by split_ifs <;> simp_all

theorem muIn_eq_sum (G : WeightedGraph V) (A X : Finset V) :
    muIn G A X = ∑ v ∈ X, massIn G A v := by
  unfold muIn cross massIn
  rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]

omit [Fintype V] in
theorem massOut_nonneg (G : WeightedGraph V) (A : Finset V) (v : V) : 0 ≤ massOut G A v := by
  unfold massOut; split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg fun u _ => G.nonneg u v

theorem massIn_nonneg (G : WeightedGraph V) (A : Finset V) (v : V) : 0 ≤ massIn G A v := by
  unfold massIn; split_ifs
  · exact Finset.sum_nonneg fun u _ => G.nonneg v u
  · exact le_rfl

namespace Hier

variable {N : Type} [Fintype N] [DecidableEq N] [LinearOrder N] (H : Hier V N)

/-! ### The leaf preorder and cluster intervals -/

/-- Preorder key of a vertex: the root path of its leaf. -/
def key (v : V) : List N := H.T.rootPath (H.leaf v)

/-- Position of a vertex in the leaf preorder. -/
def idx (v : V) : ℕ := (Finset.univ.filter fun u => H.key u < H.key v).card

/-- The first `k` vertices of the leaf preorder. -/
def prefixSet (k : ℕ) : Finset V := Finset.univ.filter fun v => H.idx v < k

/-- Point masses moved to preorder positions. -/
def posMass (m : V → ℝ) (i : ℕ) : ℝ := ∑ v ∈ Finset.univ.filter (fun v => H.idx v = i), m v

variable {H}

omit [Fintype V] [Fintype N] [DecidableEq V] [LinearOrder N] in
theorem key_injective : Function.Injective H.key := fun _ _ h =>
  H.leaf_inj (RootedTree.rootPath_injective h)

omit [DecidableEq V] [Fintype N] in
theorem idx_lt_of_key_lt {u v : V} (h : H.key u < H.key v) : H.idx u < H.idx v := by
  unfold idx
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun w hw => ?_, fun he => ?_⟩)
  · simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact lt_trans hw h
  · have : u ∈ Finset.univ.filter fun w => H.key w < H.key v := by simp [h]
    rw [← he] at this
    simp at this

omit [DecidableEq V] [Fintype N] in
theorem key_le_of_idx_le {u v : V} (h : H.idx u ≤ H.idx v) : H.key u ≤ H.key v := by
  by_contra hlt
  have := idx_lt_of_key_lt (lt_of_not_ge hlt)
  omega

omit [DecidableEq V] [Fintype N] in
theorem idx_lt_card (v : V) : H.idx v < Fintype.card V := by
  unfold idx
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩)
  intro he
  have : v ∈ Finset.univ.filter fun w => H.key w < H.key v := by rw [he]; exact mem_univ v
  simp at this

omit [DecidableEq V] [Fintype N] in
theorem idx_injective : Function.Injective H.idx := by
  intro u v h
  apply key_injective (H := H)
  exact le_antisymm (key_le_of_idx_le h.le) (key_le_of_idx_le h.ge)

omit [DecidableEq V] [Fintype N] in
/-- Every cluster is an interval of positions. -/
theorem exists_cluster_interval (x : N) :
    ∃ a b, a ≤ b ∧ b ≤ Fintype.card V ∧ ∀ v, v ∈ H.cluster x ↔ a ≤ H.idx v ∧ H.idx v < b := by
  by_cases hne : (H.cluster x).Nonempty
  · obtain ⟨lo, hlo, hlomin⟩ := (H.cluster x).exists_min_image H.idx hne
    obtain ⟨hi, hhi, hhimax⟩ := (H.cluster x).exists_max_image H.idx hne
    have hlohi := hlomin hi hhi
    have hhin := idx_lt_card (H := H) hi
    refine ⟨H.idx lo, H.idx hi + 1, by omega, by omega, fun v => ⟨fun hv => ⟨hlomin v hv, by
      have := hhimax v hv; omega⟩, fun ⟨h1, h2⟩ => ?_⟩⟩
    rw [mem_cluster] at hlo hhi ⊢
    exact RootedTree.isAnc_of_between hlo hhi (key_le_of_idx_le h1)
      (key_le_of_idx_le (by omega))
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨0, 0, le_rfl, Nat.zero_le _, fun v => by simp [hne]⟩

omit [LinearOrder N] [DecidableEq V] [Fintype N] in
/-- Two clusters are nested or disjoint. -/
theorem cluster_laminar (x y : N) :
    H.cluster x ⊆ H.cluster y ∨ H.cluster y ⊆ H.cluster x ∨
      Disjoint (H.cluster x) (H.cluster y) := by
  by_cases hxy : H.T.IsAnc x y
  · exact Or.inr (Or.inl fun v hv => mem_cluster.mpr
      (RootedTree.isAnc_trans hxy (mem_cluster.mp hv)))
  by_cases hyx : H.T.IsAnc y x
  · exact Or.inl fun v hv => mem_cluster.mpr (RootedTree.isAnc_trans hyx (mem_cluster.mp hv))
  refine Or.inr (Or.inr (Finset.disjoint_left.mpr fun v hx hy => ?_))
  rcases RootedTree.isAnc_total_of_common (mem_cluster.mp hx) (mem_cluster.mp hy) with h | h
  · exact hxy h
  · exact hyx h

omit [DecidableEq V] [Fintype N] in
theorem pre_posMass (m : V → ℝ) (k : ℕ) : pre (H.posMass m) k = ∑ v ∈ H.prefixSet k, m v := by
  unfold pre posMass prefixSet
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter fun v => H.idx v < k)
    (t := range k) (g := H.idx) (fun v hv => by simpa using hv)]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr ?_ fun _ _ => rfl
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_range] at hi ⊢
  constructor
  · rintro rfl; exact ⟨hi, rfl⟩
  · rintro ⟨-, h⟩; exact h

omit [DecidableEq V] [Fintype N] in
theorem sum_Ico_posMass (m : V → ℝ) {a b : ℕ} :
    ∑ i ∈ Ico a b, H.posMass m i = ∑ v ∈ Finset.univ.filter (fun v => a ≤ H.idx v ∧ H.idx v < b),
      m v := by
  unfold posMass
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter fun v => a ≤ H.idx v ∧ H.idx v < b)
    (t := Ico a b) (g := H.idx) (fun v hv => by simpa using hv)]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr ?_ fun _ _ => rfl
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_Ico] at hi ⊢
  constructor
  · rintro rfl; exact ⟨hi, rfl⟩
  · rintro ⟨-, h⟩; exact h

omit [DecidableEq V] [Fintype N] in
theorem posMass_nonneg {m : V → ℝ} (hm : ∀ v, 0 ≤ m v) (i : ℕ) : 0 ≤ H.posMass m i :=
  Finset.sum_nonneg fun v _ => hm v

omit [DecidableEq V] [Fintype N] in
theorem prefixSet_card : H.prefixSet (Fintype.card V) = Finset.univ := by
  ext v; simp [prefixSet, idx_lt_card]

omit [DecidableEq V] [Fintype N] in
/-- On a cluster interval, a boundary measure is a sum of position masses. -/
theorem sum_cluster_eq {x : N} {a b : ℕ}
    (hab : ∀ v, v ∈ H.cluster x ↔ a ≤ H.idx v ∧ H.idx v < b) (m : V → ℝ) :
    ∑ v ∈ H.cluster x, m v = ∑ i ∈ Ico a b, H.posMass m i := by
  rw [sum_Ico_posMass]
  exact Finset.sum_congr (by ext v; simp [hab v]) fun _ _ => rfl

/-! ### The query program -/

variable (H)

/-- The checkpoints of both boundary measures, given the cluster cut `a`. -/
noncomputable def clusterRest (q : ℕ) (x : N) (a : ℝ) :
    Comp (Finset V) ℝ (ℝ × List (ℕ × ℝ) × List (ℕ × ℝ)) :=
  if a ≤ 0 then Comp.pure (a, [], []) else
    (subst (fun k => measOut (H.cluster x) a (H.prefixSet k))
        (quantileCheckpoints (Fintype.card V) q a)).bind fun lo =>
      (subst (fun k => measIn (H.cluster x) a (H.prefixSet k))
          (quantileCheckpoints (Fintype.card V) q a)).map fun li => (a, lo, li)

/-- Query a cluster cut and the checkpoints of both boundary measures. -/
noncomputable def clusterData (q : ℕ) (x : N) :
    Comp (Finset V) ℝ (ℝ × List (ℕ × ℝ) × List (ℕ × ℝ)) :=
  (ask (H.cluster x)).bind (H.clusterRest q x)

/-- A graph fits the recorded data. -/
def Fits (D : N → Option (ℝ × List (ℕ × ℝ) × List (ℕ × ℝ))) (F : WeightedGraph V) : Prop :=
  ∀ x ∈ H.edges, ∃ a lo li, D x = some (a, lo, li) ∧ F.cut (H.cluster x) = a ∧
    (∀ p ∈ lo, muOut F (H.cluster x) (H.prefixSet p.1) = p.2) ∧
    ∀ p ∈ li, muIn F (H.cluster x) (H.prefixSet p.1) = p.2

open Classical in
/-- An offline completion consistent with the recorded data. -/
noncomputable def completionOf (D : N → Option (ℝ × List (ℕ × ℝ) × List (ℕ × ℝ))) :
    WeightedGraph V :=
  if h : ∃ F, H.Fits D F then Classical.choose h else G0
where G0 : WeightedGraph V := ⟨fun _ _ => 0, fun _ _ => rfl, fun _ _ => le_rfl, fun _ => rfl⟩

/-- **Lemma 17**: the completion program. -/
noncomputable def completion (q : ℕ) : Comp (Finset V) ℝ (WeightedGraph V) :=
  (tabulate (H.clusterData q) H.edges.toList).map H.completionOf

variable {H}

omit [Fintype N] in
theorem clusterData_eval (G : WeightedGraph V) (q : ℕ) (x : N) :
    ∃ lo li, (H.clusterData q x).eval G.cut = (G.cut (H.cluster x), lo, li) ∧
      (∀ p ∈ lo, muOut G (H.cluster x) (H.prefixSet p.1) = p.2) ∧
      (∀ p ∈ li, muIn G (H.cluster x) (H.prefixSet p.1) = p.2) ∧
      (0 < G.cut (H.cluster x) → 1 ≤ q →
        (∀ ν : ℕ → ℝ, (∀ i < Fintype.card V, 0 ≤ ν i) →
          (∀ p ∈ lo, pre ν p.1 = p.2) → ∀ a b, a ≤ b → b ≤ Fintype.card V →
            |∑ i ∈ Ico a b, H.posMass (massOut G (H.cluster x)) i - ∑ i ∈ Ico a b, ν i| ≤
              2 * G.cut (H.cluster x) / q) ∧
        (∀ ν : ℕ → ℝ, (∀ i < Fintype.card V, 0 ≤ ν i) →
          (∀ p ∈ li, pre ν p.1 = p.2) → ∀ a b, a ≤ b → b ≤ Fintype.card V →
            |∑ i ∈ Ico a b, H.posMass (massIn G (H.cluster x)) i - ∑ i ∈ Ico a b, ν i| ≤
              2 * G.cut (H.cluster x) / q)) ∧
      (H.clusterData q x).cost G.cut ≤ 1 + 4 * ((q - 1) * (Nat.log 2 (Fintype.card V) + 3)) := by
  set A := H.cluster x
  set n := Fintype.card V
  set a := G.cut A
  have hoOut : ∀ k, (measOut A a (H.prefixSet k)).eval G.cut =
      pre (H.posMass (massOut G A)) k := fun k => by
    rw [(measOut_spec G A _).1, pre_posMass, muOut_eq_sum]
  have hoIn : ∀ k, (measIn A a (H.prefixSet k)).eval G.cut =
      pre (H.posMass (massIn G A)) k := fun k => by
    rw [(measIn_spec G A _).1, pre_posMass, muIn_eq_sum]
  have htotOut : pre (H.posMass (massOut G A)) n = a := by
    rw [pre_posMass, prefixSet_card, ← muOut_eq_sum, muOut_univ]
  have htotIn : pre (H.posMass (massIn G A)) n = a := by
    rw [pre_posMass, prefixSet_card, ← muIn_eq_sum, muIn_univ]
  have hunf : H.clusterData q x = (ask A).bind (H.clusterRest q x) := rfl
  by_cases ha : a ≤ 0
  · have hr : H.clusterRest q x a = Comp.pure (a, [], []) := by simp [clusterRest, ha]
    refine ⟨[], [], ?_, by simp, by simp, fun hpos => absurd hpos (not_lt.mpr ha), ?_⟩
    · rw [hunf, eval_bind, eval_ask, hr]; rfl
    · rw [hunf, cost_bind, eval_ask, hr, cost_ask, cost_pure]; omega
  · have hapos : 0 < a := lt_of_not_ge ha
    set lo := (quantileCheckpoints n q a).eval fun k => pre (H.posMass (massOut G A)) k
    set li := (quantileCheckpoints n q a).eval fun k => pre (H.posMass (massIn G A)) k
    have hevalOut := eval_subst (fun k => measOut A a (H.prefixSet k)) G.cut _ hoOut
      (quantileCheckpoints n q a)
    have hevalIn := eval_subst (fun k => measIn A a (H.prefixSet k)) G.cut _ hoIn
      (quantileCheckpoints n q a)
    have hcostOut := cost_subst_le (fun k => measOut A a (H.prefixSet k)) G.cut _ hoOut
      (fun k => (measOut_spec G A _).2) (quantileCheckpoints n q a)
    have hcostIn := cost_subst_le (fun k => measIn A a (H.prefixSet k)) G.cut _ hoIn
      (fun k => (measIn_spec G A _).2) (quantileCheckpoints n q a)
    have hnnOut : ∀ i < n, 0 ≤ H.posMass (massOut G A) i :=
      fun i _ => posMass_nonneg (massOut_nonneg G A) i
    have hnnIn : ∀ i < n, 0 ≤ H.posMass (massIn G A) i :=
      fun i _ => posMass_nonneg (massIn_nonneg G A) i
    have hr : H.clusterRest q x a =
        (subst (fun k => measOut A a (H.prefixSet k)) (quantileCheckpoints n q a)).bind fun lo =>
          (subst (fun k => measIn A a (H.prefixSet k)) (quantileCheckpoints n q a)).map
            fun li => (a, lo, li) := by simp [clusterRest, ha, A, n]
    refine ⟨lo, li, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hunf, eval_bind, eval_ask, hr, eval_bind, eval_map, hevalOut, hevalIn]
    · intro p hp
      by_cases hq : 1 ≤ q
      · have := (quantileCheckpoints_spec hnnOut (fun k _ => rfl) hq
          (by rw [htotOut]; exact hapos)).1
        rw [htotOut] at this
        obtain ⟨-, h2⟩ := this p hp
        rw [h2, pre_posMass, muOut_eq_sum]
      · -- with `q = 0` there are no thresholds; only the free checkpoints are recorded
        have hq0 : q = 0 := by omega
        subst hq0
        simp [lo, quantileCheckpoints, thresholdCheckpoints] at hp
        rcases hp with rfl | rfl
        · simp [prefixSet, muOut]
        · rw [← htotOut, pre_posMass, muOut_eq_sum]
    · intro p hp
      by_cases hq : 1 ≤ q
      · have := (quantileCheckpoints_spec hnnIn (fun k _ => rfl) hq
          (by rw [htotIn]; exact hapos)).1
        rw [htotIn] at this
        obtain ⟨-, h2⟩ := this p hp
        rw [h2, pre_posMass, muIn_eq_sum]
      · have hq0 : q = 0 := by omega
        subst hq0
        simp [li, quantileCheckpoints, thresholdCheckpoints] at hp
        rcases hp with rfl | rfl
        · simp [prefixSet, muIn]
        · rw [← htotIn, pre_posMass, muIn_eq_sum]
    · intro _ hq
      have hO := (quantileCheckpoints_spec hnnOut (fun k _ => rfl) hq
        (by rw [htotOut]; exact hapos)).2.2.1
      have hI := (quantileCheckpoints_spec hnnIn (fun k _ => rfl) hq
        (by rw [htotIn]; exact hapos)).2.2.1
      rw [htotOut] at hO
      rw [htotIn] at hI
      exact ⟨hO, hI⟩
    · rw [hunf, cost_bind, eval_ask, hr, cost_ask, cost_bind, cost_map]
      set B := (q - 1) * (Nat.log 2 n + 3)
      by_cases hq : 1 ≤ q
      · have hO := (quantileCheckpoints_spec hnnOut (fun k _ => rfl) hq
          (by rw [htotOut]; exact hapos)).2.2.2
        have hI := (quantileCheckpoints_spec hnnIn (fun k _ => rfl) hq
          (by rw [htotIn]; exact hapos)).2.2.2
        rw [htotOut] at hO
        rw [htotIn] at hI
        omega
      · have hq0 : q = 0 := by omega
        subst hq0
        have hO : (quantileCheckpoints n 0 a).cost (pre (H.posMass (massOut G A))) = 0 := by
          simp [quantileCheckpoints]
        have hI : (quantileCheckpoints n 0 a).cost (pre (H.posMass (massIn G A))) = 0 := by
          simp [quantileCheckpoints]
        omega

/-! ### The completion guarantee -/

omit [Fintype N] in
/-- Error of a boundary measure on another cluster, from the checkpoint guarantee. -/
theorem measure_error {F G : WeightedGraph V} {A B : Finset V} {q : ℕ} (hq : 1 ≤ q)
    {μF μG : Finset V → ℝ} {mF mG : V → ℝ}
    (hmF : ∀ X, μF X = ∑ v ∈ X, mF v) (hmG : ∀ X, μG X = ∑ v ∈ X, mG v)
    (hmFnn : ∀ v, 0 ≤ mF v) (hFle : μF B ≤ F.cut A) (hGle : μG B ≤ G.cut A)
    (hFnn : 0 ≤ μF B) (hGnn : 0 ≤ μG B) (hcutF : F.cut A = G.cut A)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ Fintype.card V)
    (hB : ∀ v, v ∈ B ↔ a ≤ H.idx v ∧ H.idx v < b) (lo : List (ℕ × ℝ))
    (hlo : ∀ p ∈ lo, μF (H.prefixSet p.1) = p.2)
    (hcheck : 0 < G.cut A → 1 ≤ q →
      ∀ ν : ℕ → ℝ, (∀ i < Fintype.card V, 0 ≤ ν i) → (∀ p ∈ lo, pre ν p.1 = p.2) →
        ∀ a b, a ≤ b → b ≤ Fintype.card V →
          |∑ i ∈ Ico a b, H.posMass mG i - ∑ i ∈ Ico a b, ν i| ≤ 2 * G.cut A / q) :
    |μF B - μG B| ≤ 2 * G.cut A / q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  rcases (G.cut_nonneg A).lt_or_eq with hpos | hzero
  · have hsumB : ∀ m : V → ℝ, ∑ v ∈ B, m v = ∑ i ∈ Ico a b, H.posMass m i := by
      intro m
      rw [sum_Ico_posMass]
      exact Finset.sum_congr (by ext v; simp [hB v]) fun _ _ => rfl
    have := hcheck hpos hq (H.posMass mF) (fun i _ => posMass_nonneg hmFnn i)
      (fun p hp => by rw [pre_posMass, ← hmF]; exact hlo p hp) a b hab hb
    rw [hmF, hmG, hsumB, hsumB, abs_sub_comm]
    exact this
  · -- a cluster of cut zero: both measures vanish
    have h0F : F.cut A = 0 := hcutF.trans hzero.symm
    have h1 : μF B = 0 := le_antisymm (hFle.trans h0F.le) hFnn
    have h2 : μG B = 0 := le_antisymm (hGle.trans hzero.symm.le) hGnn
    rw [h1, h2, ← hzero]; simp

omit [Fintype N] in
/-- One direction of the interaction bound: error at most `2 d_A / q`. -/
theorem interact_error_left {F G : WeightedGraph V} {q : ℕ} (hq : 1 ≤ q) {x y : N}
    (hcutF : F.cut (H.cluster x) = G.cut (H.cluster x)) (lo li : List (ℕ × ℝ))
    (hlo : ∀ p ∈ lo, muOut F (H.cluster x) (H.prefixSet p.1) = p.2)
    (hli : ∀ p ∈ li, muIn F (H.cluster x) (H.prefixSet p.1) = p.2)
    (hcheck : 0 < G.cut (H.cluster x) → 1 ≤ q →
      (∀ ν : ℕ → ℝ, (∀ i < Fintype.card V, 0 ≤ ν i) → (∀ p ∈ lo, pre ν p.1 = p.2) →
        ∀ a b, a ≤ b → b ≤ Fintype.card V →
          |∑ i ∈ Ico a b, H.posMass (massOut G (H.cluster x)) i - ∑ i ∈ Ico a b, ν i| ≤
            2 * G.cut (H.cluster x) / q) ∧
      (∀ ν : ℕ → ℝ, (∀ i < Fintype.card V, 0 ≤ ν i) → (∀ p ∈ li, pre ν p.1 = p.2) →
        ∀ a b, a ≤ b → b ≤ Fintype.card V →
          |∑ i ∈ Ico a b, H.posMass (massIn G (H.cluster x)) i - ∑ i ∈ Ico a b, ν i| ≤
            2 * G.cut (H.cluster x) / q)) :
    |interact F (H.cluster x) (H.cluster y) - interact G (H.cluster x) (H.cluster y)| ≤
      2 * G.cut (H.cluster x) / q := by
  set A := H.cluster x
  set B := H.cluster y
  obtain ⟨a, b, hab, hb, hB⟩ := exists_cluster_interval (H := H) y
  have eOut := measure_error (H := H) (F := F) (G := G) (A := A) (B := B) hq
    (muOut_eq_sum F A) (muOut_eq_sum G A) (massOut_nonneg F A) (muOut_le_cut F A B)
    (muOut_le_cut G A B) (muOut_nonneg F A B) (muOut_nonneg G A B) hcutF hab hb hB lo hlo
    (fun h1 h2 => (hcheck h1 h2).1)
  have eIn := measure_error (H := H) (F := F) (G := G) (A := A) (B := B) hq
    (muIn_eq_sum F A) (muIn_eq_sum G A) (massIn_nonneg F A) (muIn_le_cut F A B)
    (muIn_le_cut G A B) (muIn_nonneg F A B) (muIn_nonneg G A B) hcutF hab hb hB li hli
    (fun h1 h2 => (hcheck h1 h2).2)
  rcases cluster_laminar (H := H) x y with h | h | h
  · rw [interact_of_supset F h, interact_of_supset G h, hcutF]
    rw [show G.cut A - muOut F A B - (G.cut A - muOut G A B) = -(muOut F A B - muOut G A B)
      by ring, abs_neg]
    exact eOut
  · rw [interact_of_subset F h, interact_of_subset G h]
    exact eIn
  · rw [interact_of_disjoint F h, interact_of_disjoint G h,
      show -muOut F A B - -muOut G A B = -(muOut F A B - muOut G A B) by ring, abs_neg]
    exact eOut

/-- **Lemma 17.** The completion matches every cluster cut and every pair of cluster
interactions up to `(2/q) min(d_A, d_B)`, using at most
`|edges| (1 + 4 (q−1)(⌊log₂ n⌋ + 3))` cut queries. -/
theorem completion_spec (G : WeightedGraph V) {q : ℕ} (hq : 1 ≤ q) :
    (∀ x ∈ H.edges, ((H.completion q).eval G.cut).cut (H.cluster x) = G.cut (H.cluster x)) ∧
    (∀ x ∈ H.edges, ∀ y ∈ H.edges,
      |interact ((H.completion q).eval G.cut) (H.cluster x) (H.cluster y) -
        interact G (H.cluster x) (H.cluster y)| ≤
          2 / q * min (H.canon G x) (H.canon G y)) ∧
    (H.completion q).cost G.cut ≤
      H.edges.card * (1 + 4 * ((q - 1) * (Nat.log 2 (Fintype.card V) + 3))) := by
  classical
  set D := (tabulate (H.clusterData q) H.edges.toList).eval G.cut
  have hD : ∀ x ∈ H.edges, D x = some ((H.clusterData q x).eval G.cut) := fun x hx => by
    simp [D, Finset.mem_toList.mpr hx]
  have hGfits : H.Fits D G := by
    intro x hx
    obtain ⟨lo, li, heq, hlo, hli, -⟩ := clusterData_eval (H := H) G q x
    exact ⟨_, lo, li, (hD x hx).trans (by rw [heq]), rfl, hlo, hli⟩
  have hex : ∃ F, H.Fits D F := ⟨G, hGfits⟩
  set F := (H.completion q).eval G.cut
  have hFdef : F = Classical.choose hex := by
    simp only [F, completion, eval_map, completionOf]
    rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hFfits : H.Fits D F := hFdef ▸ Classical.choose_spec hex
  -- the data recorded for each cluster
  have hdata : ∀ x ∈ H.edges, F.cut (H.cluster x) = G.cut (H.cluster x) ∧
      ∃ lo li : List (ℕ × ℝ), (∀ p ∈ lo, muOut F (H.cluster x) (H.prefixSet p.1) = p.2) ∧
        (∀ p ∈ li, muIn F (H.cluster x) (H.prefixSet p.1) = p.2) ∧
        (0 < G.cut (H.cluster x) → 1 ≤ q →
          (∀ ν : ℕ → ℝ, (∀ i < Fintype.card V, 0 ≤ ν i) → (∀ p ∈ lo, pre ν p.1 = p.2) →
            ∀ a b, a ≤ b → b ≤ Fintype.card V →
              |∑ i ∈ Ico a b, H.posMass (massOut G (H.cluster x)) i - ∑ i ∈ Ico a b, ν i| ≤
                2 * G.cut (H.cluster x) / q) ∧
          (∀ ν : ℕ → ℝ, (∀ i < Fintype.card V, 0 ≤ ν i) → (∀ p ∈ li, pre ν p.1 = p.2) →
            ∀ a b, a ≤ b → b ≤ Fintype.card V →
              |∑ i ∈ Ico a b, H.posMass (massIn G (H.cluster x)) i - ∑ i ∈ Ico a b, ν i| ≤
                2 * G.cut (H.cluster x) / q)) := by
    intro x hx
    obtain ⟨a, lo', li', hDx, hcut, hlo', hli'⟩ := hFfits x hx
    obtain ⟨lo, li, heq, -, -, hcheck, -⟩ := clusterData_eval (H := H) G q x
    rw [hD x hx, heq] at hDx
    simp only [Option.some.injEq, Prod.mk.injEq] at hDx
    obtain ⟨ha, rfl, rfl⟩ := hDx
    exact ⟨hcut.trans ha.symm, lo, li, hlo', hli', hcheck⟩
  refine ⟨fun x hx => (hdata x hx).1, fun x hx y hy => ?_, ?_⟩
  · obtain ⟨hcx, lox, lix, hlox, hlix, hchkx⟩ := hdata x hx
    obtain ⟨hcy, loy, liy, hloy, hliy, hchky⟩ := hdata y hy
    have h1 := interact_error_left (H := H) (y := y) hq hcx lox lix hlox hlix hchkx
    have h2 := interact_error_left (H := H) (y := x) hq hcy loy liy hloy hliy hchky
    rw [show interact F (H.cluster y) (H.cluster x) = interact F (H.cluster x) (H.cluster y) by
        unfold interact; rw [cutForm_comm],
      show interact G (H.cluster y) (H.cluster x) = interact G (H.cluster x) (H.cluster y) by
        unfold interact; rw [cutForm_comm]] at h2
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min ?_ ?_
    · calc _ ≤ 2 * G.cut (H.cluster x) / q := h1
        _ = 2 / q * H.canon G x := by unfold canon; ring
    · calc _ ≤ 2 * G.cut (H.cluster y) / q := h2
        _ = 2 / q * H.canon G y := by unfold canon; ring
  · simp only [completion, cost_map]
    have := cost_tabulate_le G.cut (H.clusterData q) H.edges.toList
      (c := 1 + 4 * ((q - 1) * (Nat.log 2 (Fintype.card V) + 3)))
      fun x _ => by obtain ⟨_, _, -, -, -, -, h⟩ := clusterData_eval (H := H) G q x; exact h
    rwa [Finset.length_toList, Nat.mul_comm] at this

/-- **Lemmas 17 and 18 combined.** If the minimum cut `λ` of `G` is positive, the
completion `F` satisfies `|c_F(S) − c_G(S)| ≤ (2/q) R(S)² / λ` for every shore. -/
theorem completion_cut_error (G : WeightedGraph V) {q : ℕ} (hq : 1 ≤ q)
    (hlam : 0 < mincutValue G) (S : Finset V) :
    |((H.completion q).eval G.cut).cut S - G.cut S| ≤
      2 / q * H.rep (H.canon G) S ^ 2 / mincutValue G := by
  obtain ⟨-, hM, -⟩ := completion_spec (H := H) G hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have := cut_error_le (H := H) ((H.completion q).eval G.cut) G (η := 2 / q)
    (by positivity) hlam (fun x hx => mincutValue_le G hx) hM S
  simpa [mul_div_assoc] using this

end Hier
end Hierarchy
end CutQueryComplexity
