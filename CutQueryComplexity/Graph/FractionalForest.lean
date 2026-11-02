import CutQueryComplexity.Graph.Weighted

/-!
# Fractional forests (W2 infrastructure)

`x(E(S))` counts each unordered pair once: half the symmetric double sum
(the diagonal is zero). A fractional forest satisfies `x(E(S)) ≤ |S| - 1`
for every nonempty `S`.
-/

namespace CutQueryComplexity

open Finset CutQueryComplexity

variable {V : Type*}

namespace FractionalForest

/-- Internal mass `x(E(S))`, each unordered pair counted once. -/
noncomputable def mass (G : WeightedGraph V) (S : Finset V) : ℝ :=
  (∑ u ∈ S, ∑ v ∈ S, G.w u v) / 2

/-- Fractional-forest inequalities. -/
def IsFractionalForest (G : WeightedGraph V) : Prop :=
  ∀ S : Finset V, S.Nonempty → mass G S ≤ (S.card : ℝ) - 1

theorem mass_nonneg (G : WeightedGraph V) (S : Finset V) : 0 ≤ mass G S :=
  div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => G.nonneg _ _) zero_le_two

@[simp] theorem mass_empty (G : WeightedGraph V) : mass G ∅ = 0 := by simp [mass]

@[simp] theorem mass_singleton (G : WeightedGraph V) (v : V) : mass G {v} = 0 := by
  simp [mass, G.diag]

/-- With unordered pairs: `x(E({u,v})) = x_{uv}` for `u ≠ v`. -/
theorem mass_pair [DecidableEq V] (G : WeightedGraph V) {u v : V} (h : u ≠ v) :
    mass G {u, v} = G.w u v := by
  simp [mass, Finset.sum_pair h, G.diag, G.symm v u]

theorem mass_mono (G : WeightedGraph V) {S T : Finset V} (h : S ⊆ T) :
    mass G S ≤ mass G T := by
  unfold mass
  apply div_le_div_of_nonneg_right _ zero_le_two
  calc ∑ u ∈ S, ∑ v ∈ S, G.w u v ≤ ∑ u ∈ S, ∑ v ∈ T, G.w u v :=
        sum_le_sum fun u _ => sum_le_sum_of_subset_of_nonneg h fun _ _ _ => G.nonneg _ _
    _ ≤ ∑ u ∈ T, ∑ v ∈ T, G.w u v :=
        sum_le_sum_of_subset_of_nonneg h fun _ _ _ =>
          sum_nonneg fun _ _ => G.nonneg _ _

/-- Weights of a fractional forest are at most one. -/
theorem IsFractionalForest.w_le_one [DecidableEq V] {G : WeightedGraph V}
    (hG : IsFractionalForest G) (u v : V) : G.w u v ≤ 1 := by
  by_cases h : u = v
  · subst h; rw [G.diag]; exact zero_le_one
  · have := hG {u, v} (insert_nonempty _ _)
    rw [mass_pair G h, Finset.card_pair h] at this
    norm_num at this
    exact this

/-- Supermodularity of internal mass. -/
theorem mass_supermodular [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (S T : Finset V) :
    mass G S + mass G T ≤ mass G (S ∪ T) + mass G (S ∩ T) := by
  have hind : ∀ A : Finset V, ∑ u ∈ A, ∑ v ∈ A, G.w u v =
      ∑ u, ∑ v, (if u ∈ A ∧ v ∈ A then G.w u v else 0) := by
    intro A
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ A)]
    simp only [filter_mem_eq_inter, univ_inter]
    rw [Finset.sum_eq_zero (s := univ.filter (· ∉ A)) (fun u hu => by
      simp only [mem_filter] at hu
      exact Finset.sum_eq_zero fun v _ => by simp [hu.2]), add_zero]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ A)]
    simp only [filter_mem_eq_inter, univ_inter]
    rw [Finset.sum_eq_zero (s := univ.filter (· ∉ A)) (fun v hv => by
      simp only [mem_filter] at hv
      simp [hv.2]), add_zero]
    exact Finset.sum_congr rfl fun v hv => by simp [hu, hv]
  unfold mass
  rw [hind S, hind T, hind (S ∪ T), hind (S ∩ T), ← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ zero_le_two
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
  have hw := G.nonneg u v
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases hu' : u ∈ T <;>
    by_cases hv' : v ∈ T <;> simp [hu, hv, hu', hv', hw]

end FractionalForest

end CutQueryComplexity
