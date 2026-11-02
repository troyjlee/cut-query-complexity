import CutQueryComplexity.MinCut.RootedTree
import CutQueryComplexity.Graph.Operations
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Partial-tree frontier vertex types

Each block keeps its original vertices and one proxy for each incident tree
edge. The topology is an unweighted rooted tree, so zero-capacity edges remain
present. This module supplies the exact finite vertex types and their counts.
Cut-safe refinement and the component-to-proxy contraction map must be proved
before applying this count to a recursive GH run.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical
open WeightedGraph

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

/-- Parent edges incident to a block, identified by their nonroot child. -/
def frontierProxies (T : RootedTree B) (b : B) : Finset B :=
  (Finset.univ.erase T.root).filter (fun e => e = b ∨ T.parent e = b)

@[simp] theorem mem_frontierProxies (T : RootedTree B) (b e : B) :
    e ∈ frontierProxies T b ↔ e ≠ T.root ∧ (e = b ∨ T.parent e = b) := by
  simp [frontierProxies]

theorem parent_ne_child (T : RootedTree B) {e : B} (he : e ≠ T.root) :
    T.parent e ≠ e := by
  intro h
  have hd := T.depth_parent e he
  rw [h] at hd
  omega

/-- A literal finite label type: originals in the block, and incident proxies. -/
def FrontierVertex (p : V → B) (T : RootedTree B) (b : B) :=
  (fiber p b) ⊕ (frontierProxies T b)

instance frontierVertexFintype (p : V → B) (T : RootedTree B) (b : B) :
    Fintype (FrontierVertex p T b) := inferInstanceAs (Fintype (_ ⊕ _))

instance frontierVertexDecidableEq (p : V → B) (T : RootedTree B) (b : B) :
    DecidableEq (FrontierVertex p T b) := inferInstanceAs (DecidableEq (_ ⊕ _))

theorem frontierVertex_card (p : V → B) (T : RootedTree B) (b : B) :
    Fintype.card (FrontierVertex p T b) = (fiber p b).card + (frontierProxies T b).card := by
  let e : FrontierVertex p T b ≃ ((fiber p b) ⊕ (frontierProxies T b)) := Equiv.refl _
  calc
    Fintype.card (FrontierVertex p T b) =
        Fintype.card ((fiber p b) ⊕ (frontierProxies T b)) := Fintype.card_congr e
    _ = _ := by simp only [Fintype.card_sum, Fintype.card_coe]

theorem sum_fiber_card (p : V → B) :
    (∑ b, (fiber p b).card) = Fintype.card V := by
  simp only [fiber, pull, Finset.card_filter, Finset.mem_singleton]
  rw [Finset.sum_comm]
  simp

/-- Every nonroot edge creates exactly two proxies, even if its eventual
cut-tree weight is zero. -/
theorem sum_frontierProxies_card (T : RootedTree B) :
    (∑ b, (frontierProxies T b).card) = 2 * (Fintype.card B - 1) := by
  simp only [frontierProxies, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ _e ∈ Finset.univ.erase T.root, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      have hne : e ≠ T.parent e := (parent_ne_child T (Finset.mem_erase.mp he).1).symm
      have hends : Finset.univ.filter (fun b => e = b ∨ T.parent e = b) =
          ({e, T.parent e} : Finset B) := by
        ext b
        simp [eq_comm]
      rw [← Finset.card_filter (fun b => e = b ∨ T.parent e = b) Finset.univ, hends]
      exact Finset.card_pair hne
    _ = _ := by simp [Nat.mul_comm]

/-- Exact complete-frontier count; retaining frozen singleton blocks is safe. -/
theorem frontier_vertex_sum (p : V → B) (T : RootedTree B) :
    (∑ b, Fintype.card (FrontierVertex p T b)) =
      Fintype.card V + 2 * (Fintype.card B - 1) := by
  simp_rw [frontierVertex_card]
  rw [Finset.sum_add_distrib, sum_fiber_card, sum_frontierProxies_card]

theorem frontier_vertex_sum_le (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) :
    (∑ b, Fintype.card (FrontierVertex p T b)) ≤ 3 * Fintype.card V := by
  rw [frontier_vertex_sum]
  have hc := Fintype.card_le_of_surjective p hp
  omega

theorem frontier_fiber_nonempty (p : V → B) (hp : Function.Surjective p) (b : B) :
    (fiber p b).Nonempty := by
  obtain ⟨v, hv⟩ := hp b
  exact ⟨v, (mem_fiber p b v).mpr hv⟩

/-- Every individual auxiliary label type also has size at most the original
input, as required for the primitive's size-regularity hypothesis. -/
theorem frontierVertex_card_le (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) : Fintype.card (FrontierVertex p T b) ≤ Fintype.card V := by
  have hpcount : (frontierProxies T b).card ≤ Fintype.card B - 1 := by
    have h := Finset.card_le_card (Finset.filter_subset (s := Finset.univ.erase T.root)
      (p := fun e => e = b ∨ T.parent e = b))
    simpa [frontierProxies] using h
  have hother : (Finset.univ.erase b).card ≤
      ∑ c ∈ Finset.univ.erase b, (fiber p c).card := by
    calc
      _ = ∑ _c ∈ Finset.univ.erase b, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun c _ => (frontier_fiber_nonempty p hp c).card_pos)
  have hsplit : (∑ c ∈ Finset.univ.erase b, (fiber p c).card) + (fiber p b).card =
      Fintype.card V := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ b), sum_fiber_card]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ] at hother
  rw [frontierVertex_card]
  omega

/-- Every auxiliary instance contains an original vertex, even at a frozen
singleton block. Together with the upper bound this licenses size regularity. -/
theorem frontierVertex_card_bounds (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) :
    1 ≤ Fintype.card (FrontierVertex p T b) ∧
      Fintype.card (FrontierVertex p T b) ≤ Fintype.card V := by
  refine ⟨?_, frontierVertex_card_le p hp T b⟩
  rw [frontierVertex_card]
  have h := (frontier_fiber_nonempty p hp b).card_pos
  omega

/-- A public subset of active blocks inherits the complete-frontier bound;
frozen blocks can be omitted without a separate accounting assumption. -/
theorem frontier_vertex_active_sum_le (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (active : Finset B) :
    (∑ b ∈ active, Fintype.card (FrontierVertex p T b)) ≤ 3 * Fintype.card V := by
  refine le_trans ?_ (frontier_vertex_sum_le p hp T)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active)
    (fun _ _ _ => Nat.zero_le _)

#print axioms mem_frontierProxies
#print axioms parent_ne_child
#print axioms frontierVertex_card
#print axioms sum_fiber_card
#print axioms sum_frontierProxies_card
#print axioms frontier_vertex_sum
#print axioms frontier_vertex_sum_le
#print axioms frontier_fiber_nonempty
#print axioms frontierVertex_card_le
#print axioms frontierVertex_card_bounds
#print axioms frontier_vertex_active_sum_le

end
end CutQueryComplexity.GHReduction
