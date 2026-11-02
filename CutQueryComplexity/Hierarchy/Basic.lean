import CutQueryComplexity.TwoRespecting.Tree
import CutQueryComplexity.Graph.Operations

/-! # Hierarchies and representation cost

A hierarchy over the vertex set `V` is a rooted tree on a node type `N` together
with an injective leaf map `V → N`. The cluster of a node is the set of vertices
whose leaves lie below it. Given capacities on the tree edges (the edge above a
non-root node), the representation cost `R(S)` of a shore is the minimum cost of a
binary labelling of the nodes that extends the indicator of `S` on the leaves
(paper, eq. (R)).

* `telescope`: a node label is the root label plus the label changes on the tree
  edges above it.
* `cut_eq_half_sum_abs`: `c_G(S) = ½ ∑ w(u,v) |1_S u − 1_S v|`.
* `cut_le_labelCost`: with canonical capacities `c_G(cluster x)`, every extending
  labelling costs at least `c_G(S)`; hence `c_G(S) ≤ R(S)` (Lemma 18, second part).
-/

namespace CutQueryComplexity
namespace Hierarchy

open TwoRespecting WeightedGraph

/-- A hierarchy: a rooted tree on the nodes `N` and an injective leaf map. -/
structure Hier (V N : Type) where
  T : RootedTree N
  leaf : V → N
  leaf_inj : Function.Injective leaf

namespace Hier

variable {V N : Type} [Fintype N] [DecidableEq N]
variable (H : Hier V N)

/-- The tree edges, as their lower nodes. -/
def edges : Finset N := Finset.univ.erase H.T.root

/-- Cost of a real-valued node labelling under edge capacities `cap`. -/
def labelCost (cap : N → ℝ) (ℓ : N → ℝ) : ℝ :=
  ∑ x ∈ H.edges, cap x * |ℓ x - ℓ (H.T.parent x)|

/-- A binary labelling as a real-valued one. -/
def toReal (ℓ : N → Bool) : N → ℝ := fun x => if ℓ x then 1 else 0

@[simp] theorem mem_edges {x : N} : x ∈ H.edges ↔ x ≠ H.T.root := by simp [edges]

theorem labelCost_nonneg {cap : N → ℝ} (hcap : ∀ x, 0 ≤ cap x) (ℓ : N → ℝ) :
    0 ≤ H.labelCost cap ℓ :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hcap x) (abs_nonneg _)

variable {H} in
/-- A label is the root label plus the label changes on the edges above it. -/
theorem telescope (ℓ : N → ℝ) : ∀ (n : ℕ) (y : N), H.T.depth y ≤ n →
    ℓ y = ℓ H.T.root + ∑ x ∈ H.edges, if H.T.IsAnc x y then ℓ x - ℓ (H.T.parent x) else 0
  | 0, y, hy => by
      have hyr := RootedTree.eq_root_of_depth_eq_zero (Nat.le_zero.mp hy)
      subst hyr
      rw [Finset.sum_eq_zero fun x hx => by
        rw [ite_eq_right fun h => absurd h.eq_root_of_isAnc_root ((mem_edges H).mp hx)]]
      ring
  | n + 1, y, hy => by
      by_cases hyr : y = H.T.root
      · subst hyr; exact telescope ℓ 0 _ (by rw [H.T.depth_root])
      have hdp : H.T.depth (H.T.parent y) ≤ n := by have := H.T.depth_parent y hyr; omega
      have ih := telescope ℓ n _ hdp
      have hyE : y ∈ H.edges := (mem_edges H).mpr hyr
      have hsplit : (∑ x ∈ H.edges, if H.T.IsAnc x y then ℓ x - ℓ (H.T.parent x) else 0) =
          (ℓ y - ℓ (H.T.parent y)) +
            ∑ x ∈ H.edges, if H.T.IsAnc x (H.T.parent y) then ℓ x - ℓ (H.T.parent x) else 0 := by
        rw [← Finset.add_sum_erase _ _ hyE, ite_eq_left (RootedTree.isAnc_refl y)]
        congr 1
        rw [← Finset.add_sum_erase _ (fun x => if H.T.IsAnc x (H.T.parent y) then
          ℓ x - ℓ (H.T.parent x) else 0) hyE]
        have hnot : ¬ H.T.IsAnc y (H.T.parent y) := fun h => by
          have := h.depth_le; have := H.T.depth_parent y hyr; omega
        rw [ite_eq_right hnot, zero_add]
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxy : x ≠ y := Finset.ne_of_mem_erase hx
        have : H.T.IsAnc x y ↔ H.T.IsAnc x (H.T.parent y) := by
          rw [RootedTree.isAnc_iff_eq_or_isAnc_parent]
          exact ⟨fun h => (h.resolve_left hxy).2, fun h => Or.inr ⟨hyr, h⟩⟩
        simp only [this]
      rw [hsplit]; linarith

variable [Fintype V] [DecidableEq V]

/-- Vertices whose leaves lie below `x`. -/
def cluster (x : N) : Finset V := Finset.univ.filter fun v => H.T.IsAnc x (H.leaf v)

/-- A binary labelling extends the indicator of `S` on the leaves. -/
def Extends (S : Finset V) (ℓ : N → Bool) : Prop := ∀ v, ℓ (H.leaf v) = decide (v ∈ S)

instance (S : Finset V) : DecidablePred (H.Extends S) := fun ℓ => by
  unfold Extends; infer_instance

/-- Canonical capacities: the cut of each cluster. -/
def canon (G : WeightedGraph V) : N → ℝ := fun x => G.cut (H.cluster x)

theorem extends_nonempty (S : Finset V) :
    (Finset.univ.filter (H.Extends S)).Nonempty := by
  classical
  refine ⟨fun x => decide (∃ v ∈ S, H.leaf v = x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro v
  simp only [decide_eq_decide]
  constructor
  · rintro ⟨u, hu, huv⟩
    exact H.leaf_inj huv ▸ hu
  · intro hv; exact ⟨v, hv, rfl⟩

/-- Representation cost: the cheapest extension of `S` to the tree. -/
noncomputable def rep (cap : N → ℝ) (S : Finset V) : ℝ :=
  (Finset.univ.filter (H.Extends S)).inf' (H.extends_nonempty S)
    fun ℓ => H.labelCost cap (toReal ℓ)

variable {H}

omit [Fintype N] [DecidableEq V] in
@[simp] theorem mem_cluster {x : N} {v : V} : v ∈ H.cluster x ↔ H.T.IsAnc x (H.leaf v) := by
  simp [cluster]

theorem rep_le (cap : N → ℝ) {S : Finset V} {ℓ : N → Bool} (h : H.Extends S ℓ) :
    H.rep cap S ≤ H.labelCost cap (toReal ℓ) :=
  Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem exists_rep_eq (cap : N → ℝ) (S : Finset V) :
    ∃ ℓ, H.Extends S ℓ ∧ H.rep cap S = H.labelCost cap (toReal ℓ) := by
  obtain ⟨ℓ, hℓ, heq⟩ := Finset.exists_mem_eq_inf' (H.extends_nonempty S)
    fun ℓ => H.labelCost cap (toReal ℓ)
  exact ⟨ℓ, (Finset.mem_filter.mp hℓ).2, heq⟩

theorem rep_nonneg {cap : N → ℝ} (hcap : ∀ x, 0 ≤ cap x) (S : Finset V) : 0 ≤ H.rep cap S := by
  obtain ⟨ℓ, -, heq⟩ := H.exists_rep_eq cap S
  rw [heq]; exact H.labelCost_nonneg hcap _

/-! ### Indicators from labellings -/

/-- The indicator of an extended shore decomposes over the clusters. -/
theorem indicator_decomp {S : Finset V} {ℓ : N → Bool} (h : H.Extends S ℓ) (v : V) :
    (if v ∈ S then (1 : ℝ) else 0) = toReal ℓ H.T.root +
      ∑ x ∈ H.edges, (if v ∈ H.cluster x then (1 : ℝ) else 0) *
        (toReal ℓ x - toReal ℓ (H.T.parent x)) := by
  have := telescope (H := H) (toReal ℓ) _ (H.leaf v) le_rfl
  have hv : toReal ℓ (H.leaf v) = if v ∈ S then 1 else 0 := by
    simp only [toReal, h v, decide_eq_true_eq]
  rw [← hv, this]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mem_cluster]
  split_ifs <;> ring

/-! ### Cuts as sums of absolute differences -/

omit [Fintype N] [DecidableEq N] in
theorem two_mul_cut_eq_sum_abs (G : WeightedGraph V) (S : Finset V) :
    2 * G.cut S = ∑ u, ∑ v, G.w u v *
      |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then 1 else 0)| := by
  have h1 := G.cut_eq_sum_ite S
  have h2 := G.cut_eq_sum_ite Sᶜ
  rw [G.cut_compl] at h2
  have : (∑ u, ∑ v, G.w u v * |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then 1 else 0)|) =
      (∑ u, ∑ v, if u ∈ S ∧ v ∉ S then G.w u v else 0) +
        ∑ u, ∑ v, if u ∈ Sᶜ ∧ v ∉ Sᶜ then G.w u v else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]
  rw [this, ← h1, ← h2]; ring

omit [Fintype N] [DecidableEq N] in
/-- The cut of `S` is at most a weighted sum of cuts of sets whose signed combination
is the indicator of `S` up to a constant. -/
theorem cut_le_of_decomp (G : WeightedGraph V) (S : Finset V) {ι : Type} (I : Finset ι)
    (A : ι → Finset V) (δ : ι → ℝ) (c : ℝ)
    (hdec : ∀ v, (if v ∈ S then (1 : ℝ) else 0) =
      c + ∑ i ∈ I, (if v ∈ A i then (1 : ℝ) else 0) * δ i) :
    G.cut S ≤ ∑ i ∈ I, |δ i| * G.cut (A i) := by
  have key : 2 * G.cut S ≤ ∑ i ∈ I, |δ i| * (2 * G.cut (A i)) := by
    rw [two_mul_cut_eq_sum_abs]
    simp only [two_mul_cut_eq_sum_abs, Finset.mul_sum]
    calc ∑ u, ∑ v, G.w u v * |(if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then 1 else 0)|
        ≤ ∑ u, ∑ v, ∑ i ∈ I, |δ i| * (G.w u v *
            |(if u ∈ A i then (1 : ℝ) else 0) - (if v ∈ A i then 1 else 0)|) := by
          refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
          have hdiff : (if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then 1 else 0) =
              ∑ i ∈ I, ((if u ∈ A i then (1 : ℝ) else 0) - (if v ∈ A i then 1 else 0)) * δ i := by
            rw [hdec u, hdec v, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [hdiff]
          refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (G.nonneg u v)).trans
            (le_of_eq ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [abs_mul]; ring
      _ = ∑ i ∈ I, ∑ u, ∑ v, |δ i| * (G.w u v *
            |(if u ∈ A i then (1 : ℝ) else 0) - (if v ∈ A i then 1 else 0)|) := by
          calc _ = ∑ u, ∑ i ∈ I, ∑ v, |δ i| * (G.w u v *
                |(if u ∈ A i then (1 : ℝ) else 0) - (if v ∈ A i then 1 else 0)|) :=
                Finset.sum_congr rfl fun u _ => Finset.sum_comm
            _ = _ := Finset.sum_comm
  have h2 : ∑ i ∈ I, |δ i| * (2 * G.cut (A i)) = 2 * ∑ i ∈ I, |δ i| * G.cut (A i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- **Representation cost dominates cuts.** With canonical capacities, every labelling
extending `S` costs at least `c_G(S)`. -/
theorem cut_le_labelCost (G : WeightedGraph V) {S : Finset V} {ℓ : N → Bool}
    (h : H.Extends S ℓ) : G.cut S ≤ H.labelCost (H.canon G) (toReal ℓ) := by
  have := cut_le_of_decomp G S H.edges H.cluster
    (fun x => toReal ℓ x - toReal ℓ (H.T.parent x)) (toReal ℓ H.T.root) (indicator_decomp h)
  refine this.trans (le_of_eq ?_)
  unfold labelCost canon
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem cut_le_rep (G : WeightedGraph V) (S : Finset V) : G.cut S ≤ H.rep (H.canon G) S := by
  obtain ⟨ℓ, hℓ, heq⟩ := H.exists_rep_eq (H.canon G) S
  rw [heq]; exact cut_le_labelCost G hℓ

end Hier
end Hierarchy
end CutQueryComplexity
