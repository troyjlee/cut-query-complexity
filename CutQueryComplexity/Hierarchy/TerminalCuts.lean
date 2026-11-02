import CutQueryComplexity.Hierarchy.Initial
import CutQueryComplexity.Hierarchy.Children
import CutQueryComplexity.TwoRespecting.Respect

/-! # Representation costs: fundamental clusters, monotonicity, complements, parity

Facts about the representation cost `R(S) = H.rep cap S` of a hierarchy with arbitrary
nonnegative capacities, used to compare an input hierarchy with its canonical normalization.

* `rep_cluster_le`: the cluster of a nonroot node `x` costs at most `cap x` (label the subtree
  of `x` by one; only the edge above `x` is crossed, even with terminals at internal nodes).
* `rep_mono`: larger capacities on the tree edges give larger representation costs.
* `rep_compl`, `rep_symmDiff_le`: `R(Sᶜ) = R(S)` and `R(S ∆ T) ≤ R(S) + R(T)`.
* `rep_parityShore_le`: the parity shore of a finite family (vertices covered an odd number of
  times) costs at most the sum of the family's costs.
* `extends_parity`: a labelling extending `S` writes `S` as the parity shore of the clusters of
  its crossed edges, complemented when the root is labelled one.
* `rep_le_rep_of_clusters`: if every cluster of `H` below a tree edge `x` has `Q`-cost at most
  `cap x`, then every shore has `Q`-cost at most its `H`-cost under `cap`.
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace Hier

open TwoRespecting WeightedGraph Finset

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N] {H : Hier V N}

/-! ## Monotonicity and trivial shores -/

theorem rep_mono {cap cap' : N → ℝ} (h : ∀ x ∈ H.edges, cap x ≤ cap' x) (S : Finset V) :
    H.rep cap S ≤ H.rep cap' S := by
  obtain ⟨ℓ, hℓ, heq⟩ := H.exists_rep_eq cap' S
  rw [heq]
  exact (H.rep_le cap hℓ).trans (H.labelCost_mono h _)

omit [Fintype V] [DecidableEq V] in
theorem labelCost_const (cap : N → ℝ) (b : Bool) :
    H.labelCost cap (toReal fun _ => b) = 0 := by
  unfold labelCost; simp [toReal]

theorem rep_empty_le (cap : N → ℝ) : H.rep cap ∅ ≤ 0 := by
  have h : H.Extends ∅ fun _ => false := fun v => by simp
  exact (H.rep_le cap h).trans (le_of_eq (labelCost_const cap false))

theorem rep_univ_le (cap : N → ℝ) : H.rep cap univ ≤ 0 := by
  have h : H.Extends univ fun _ => true := fun v => by simp
  exact (H.rep_le cap h).trans (le_of_eq (labelCost_const cap true))

omit [Fintype N] [DecidableEq V] in
theorem cluster_root : H.cluster H.T.root = univ := by
  ext v; simp [mem_cluster, RootedTree.isAnc_root]

/-! ## Fundamental clusters -/

/-- The labelling that is one exactly on the subtree of `x`. -/
def subtreeLabel (H : Hier V N) (x : N) : N → Bool := fun y => decide (H.T.IsAnc x y)

omit [Fintype N] in
theorem subtreeLabel_extends (x : N) : H.Extends (H.cluster x) (H.subtreeLabel x) := by
  intro v; simp [subtreeLabel, mem_cluster]

omit [Fintype V] [DecidableEq V] in
/-- Labelling the subtree of a nonroot node `x` by one crosses only the edge above `x`. -/
theorem labelCost_subtreeLabel (cap : N → ℝ) {x : N} (hx : x ≠ H.T.root) :
    H.labelCost cap (toReal (H.subtreeLabel x)) = cap x := by
  unfold labelCost
  rw [Finset.sum_eq_single x]
  · have h1 : H.T.IsAnc x x := RootedTree.isAnc_refl x
    have h2 : ¬ H.T.IsAnc x (H.T.parent x) := fun h => by
      have := h.depth_le
      have := H.T.depth_parent x hx
      omega
    simp [toReal, subtreeLabel, h1, h2]
  · intro y hy hyx
    have hyr : y ≠ H.T.root := (mem_edges H).mp hy
    have : H.T.IsAnc x y ↔ H.T.IsAnc x (H.T.parent y) := by
      rw [RootedTree.isAnc_iff_eq_or_isAnc_parent (u := x) (v := y)]
      constructor
      · rintro (rfl | ⟨-, h⟩)
        · exact absurd rfl hyx
        · exact h
      · intro h; exact Or.inr ⟨hyr, h⟩
    simp [toReal, subtreeLabel, this]
  · intro hx'; exact absurd ((mem_edges H).mpr hx) hx'

/-- The cluster of a nonroot node costs at most the capacity of the edge above it. -/
theorem rep_cluster_le (cap : N → ℝ) {x : N} (hx : x ≠ H.T.root) :
    H.rep cap (H.cluster x) ≤ cap x :=
  (H.rep_le cap (subtreeLabel_extends x)).trans (le_of_eq (labelCost_subtreeLabel cap hx))

/-- Under cut domination, canonical capacities are at most the given ones on the edges. -/
theorem canon_le_of_dom {G : WeightedGraph V} {cap : N → ℝ}
    (hdom : ∀ S, G.cut S ≤ H.rep cap S) {x : N} (hx : x ≠ H.T.root) :
    H.canon G x ≤ cap x :=
  (hdom _).trans (rep_cluster_le cap hx)

/-! ## Complements and symmetric differences -/

omit [Fintype V] [DecidableEq V] in
theorem labelCost_not (cap : N → ℝ) (ℓ : N → Bool) :
    H.labelCost cap (toReal fun x => !ℓ x) = H.labelCost cap (toReal ℓ) := by
  unfold labelCost
  refine sum_congr rfl fun x _ => ?_
  rcases Bool.eq_false_or_eq_true (ℓ x) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (ℓ (H.T.parent x)) with h2 | h2 <;> simp [toReal, h1, h2]

theorem rep_compl_le (cap : N → ℝ) (S : Finset V) : H.rep cap Sᶜ ≤ H.rep cap S := by
  obtain ⟨ℓ, hℓ, heq⟩ := H.exists_rep_eq cap S
  have h : H.Extends Sᶜ fun x => !ℓ x := by
    intro v
    show (!ℓ (H.leaf v)) = decide (v ∈ Sᶜ)
    rw [hℓ v]; simp [decide_not]
  rw [heq, ← labelCost_not]
  exact H.rep_le cap h

theorem rep_compl (cap : N → ℝ) (S : Finset V) : H.rep cap Sᶜ = H.rep cap S :=
  le_antisymm (rep_compl_le cap S) (by simpa using rep_compl_le cap Sᶜ)

omit [Fintype V] [DecidableEq V] in
theorem labelCost_xor_le {cap : N → ℝ} (hcap : ∀ x ∈ H.edges, 0 ≤ cap x) (ℓ₁ ℓ₂ : N → Bool) :
    H.labelCost cap (toReal fun x => xor (ℓ₁ x) (ℓ₂ x)) ≤
      H.labelCost cap (toReal ℓ₁) + H.labelCost cap (toReal ℓ₂) := by
  unfold labelCost
  rw [← sum_add_distrib]
  refine sum_le_sum fun x hx => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hcap x hx)
  rcases Bool.eq_false_or_eq_true (ℓ₁ x) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (ℓ₁ (H.T.parent x)) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (ℓ₂ x) with h3 | h3 <;>
    rcases Bool.eq_false_or_eq_true (ℓ₂ (H.T.parent x)) with h4 | h4 <;>
    simp [toReal, h1, h2, h3, h4]

theorem rep_symmDiff_le {cap : N → ℝ} (hcap : ∀ x ∈ H.edges, 0 ≤ cap x) (S T : Finset V) :
    H.rep cap (symmDiff S T) ≤ H.rep cap S + H.rep cap T := by
  obtain ⟨ℓ₁, h₁, e₁⟩ := H.exists_rep_eq cap S
  obtain ⟨ℓ₂, h₂, e₂⟩ := H.exists_rep_eq cap T
  have h : H.Extends (symmDiff S T) fun x => xor (ℓ₁ x) (ℓ₂ x) := by
    intro v
    show xor (ℓ₁ (H.leaf v)) (ℓ₂ (H.leaf v)) = _
    rw [h₁ v, h₂ v]
    by_cases hS : v ∈ S <;> by_cases hT : v ∈ T <;> simp [Finset.mem_symmDiff, hS, hT]
  rw [e₁, e₂]
  exact (H.rep_le cap h).trans (labelCost_xor_le hcap ℓ₁ ℓ₂)

/-! ## Parity shores -/

/-- The vertices covered by an odd number of members of a finite family. -/
def parityShore {ι : Type} [DecidableEq ι] (E : Finset ι) (A : ι → Finset V) : Finset V :=
  univ.filter fun v => Odd (E.filter fun x => v ∈ A x).card

omit [Fintype N] [DecidableEq N] in
@[simp] theorem mem_parityShore {ι : Type} [DecidableEq ι] {E : Finset ι} {A : ι → Finset V}
    {v : V} : v ∈ parityShore E A ↔ Odd (E.filter fun x => v ∈ A x).card := by
  simp [parityShore]

omit [Fintype N] [DecidableEq N] in
theorem parityShore_empty {ι : Type} [DecidableEq ι] (A : ι → Finset V) :
    parityShore (∅ : Finset ι) A = ∅ := by
  ext v; simp

omit [Fintype N] [DecidableEq N] in
theorem parityShore_insert {ι : Type} [DecidableEq ι] {E : Finset ι} {x : ι} (hx : x ∉ E)
    (A : ι → Finset V) : parityShore (insert x E) A = symmDiff (parityShore E A) (A x) := by
  ext v
  rw [Finset.mem_symmDiff, mem_parityShore, mem_parityShore, Finset.filter_insert]
  by_cases hv : v ∈ A x
  · rw [ite_eq_left hv, card_insert_of_notMem (fun h => hx (mem_filter.mp h).1), Nat.odd_add_one]
    tauto
  · rw [ite_eq_right hv]
    tauto

theorem rep_parityShore_le {cap : N → ℝ} (hcap : ∀ x ∈ H.edges, 0 ≤ cap x) {ι : Type}
    [DecidableEq ι] (E : Finset ι) (A : ι → Finset V) :
    H.rep cap (parityShore E A) ≤ ∑ x ∈ E, H.rep cap (A x) := by
  induction E using Finset.induction_on with
  | empty => rw [parityShore_empty, sum_empty]; exact rep_empty_le cap
  | insert x E hx ih =>
      rw [parityShore_insert hx, sum_insert hx]
      have := rep_symmDiff_le hcap (parityShore E A) (A x)
      linarith

/-! ## Crossed edges of a labelling and the parity transfer -/

/-- The tree edges whose endpoints get different labels. -/
def crossed (H : Hier V N) (ℓ : N → Bool) : Finset N :=
  H.edges.filter fun x => ℓ x ≠ ℓ (H.T.parent x)

omit [Fintype V] [DecidableEq V] in
theorem labelCost_eq_sum_crossed (cap : N → ℝ) (ℓ : N → Bool) :
    H.labelCost cap (toReal ℓ) = ∑ x ∈ H.crossed ℓ, cap x := by
  unfold labelCost crossed
  rw [sum_filter]
  refine sum_congr rfl fun x _ => ?_
  rcases Bool.eq_false_or_eq_true (ℓ x) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (ℓ (H.T.parent x)) with h2 | h2 <;> simp [toReal, h1, h2]

omit [Fintype V] [DecidableEq V] in
/-- The crossed edges of a labelling are the crossed edges of its node set. -/
theorem crossedEdges_filter (ℓ : N → Bool) :
    H.T.crossedEdges (univ.filter fun y => ℓ y = true) = H.crossed ℓ := by
  ext x
  simp only [mem_crossedEdges, crossed, mem_filter, mem_edges, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 (by rw [h])⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h => h2 ?_⟩
    rcases Bool.eq_false_or_eq_true (ℓ x) with h3 | h3 <;>
      rcases Bool.eq_false_or_eq_true (ℓ (H.T.parent x)) with h4 | h4 <;> simp_all

/-- A labelling extending `S` presents `S` as the parity shore of the clusters of its crossed
edges, complemented when the root is labelled one. -/
theorem extends_parity {S : Finset V} {ℓ : N → Bool} (h : H.Extends S ℓ) :
    S = if ℓ H.T.root then (parityShore (H.crossed ℓ) H.cluster)ᶜ
      else parityShore (H.crossed ℓ) H.cluster := by
  ext v
  have hpar := mem_iff_parity (T := H.T) (univ.filter fun y => ℓ y = true) _ (H.leaf v) le_rfl
  rw [crossedEdges_filter] at hpar
  simp only [mem_filter, mem_univ, true_and] at hpar
  have hfilt : ((H.crossed ℓ).filter fun d => H.T.IsAnc d (H.leaf v)) =
      (H.crossed ℓ).filter fun x => v ∈ H.cluster x := by
    refine filter_congr fun x _ => ?_
    rw [mem_cluster]
  rw [hfilt] at hpar
  have hv : v ∈ S ↔ ℓ (H.leaf v) = true := by rw [h v]; simp
  rw [hv, hpar]
  split_ifs with hr
  · rw [mem_compl, mem_parityShore, hr, ← Nat.not_even_iff_odd, not_not]
    exact Iff.rfl.trans (by simp)
  · rw [mem_parityShore, ← Nat.not_even_iff_odd]
    simp only [Bool.not_eq_true] at hr
    rw [hr]
    simp

/-! ## Comparison of two hierarchies through the clusters of one of them -/

/-- If every cluster of `H` under a tree edge `x` has `Q`-cost at most `cap x`, then every shore
has `Q`-cost at most its `H`-cost under `cap`. -/
theorem rep_le_rep_of_clusters {M : Type} [Fintype M] [DecidableEq M] (Q : Hier V M)
    {capQ : M → ℝ} (hQ : ∀ x ∈ Q.edges, 0 ≤ capQ x) {cap : N → ℝ}
    (hcl : ∀ x ∈ H.edges, Q.rep capQ (H.cluster x) ≤ cap x) (S : Finset V) :
    Q.rep capQ S ≤ H.rep cap S := by
  obtain ⟨ℓ, hℓ, heq⟩ := H.exists_rep_eq cap S
  rw [heq, labelCost_eq_sum_crossed]
  have hS := extends_parity hℓ
  have hpar : Q.rep capQ (parityShore (H.crossed ℓ) H.cluster) ≤ ∑ x ∈ H.crossed ℓ, cap x :=
    (rep_parityShore_le hQ _ _).trans (sum_le_sum fun x hx => hcl x (mem_filter.mp hx).1)
  rw [hS]
  split_ifs
  · rw [rep_compl]; exact hpar
  · exact hpar

end Hier
end Hierarchy
end CutQueryComplexity
