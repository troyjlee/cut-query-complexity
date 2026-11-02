import CutQueryComplexity.CanonicalST.Augmentation.MaxFlow
import Mathlib.Tactic

/-!
# A weak global skeleton need not approximate terminal cuts

Paper 02, Proposition 4. The four vertices are `0 = x`, `1 = s`,
`2 = a`, and `3 = t`. The unit graph is a triangle on `s,a,t` with
the pendant edge `sx`. The weighted graph keeps the path `x,s,a,t`,
with weights `1,M,M`. For every real `M >= 1`, both global minima
and both cuts at `{x}` equal one, while the terminal minima are two
and `M`. Containment is of supports, not domination of capacities.
-/

set_option autoImplicit false

namespace CutQueryComplexity.CanonicalST

open Finset WeightedGraph
open scoped Classical
noncomputable section

namespace SkeletonCounterexample

/-- A weighted path `0,1,2,3`, with an optional chord `1,3`. -/
def graph (M c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c) : WeightedGraph (Fin 4) where
  w u v :=
    if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) then 1
    else if (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
      (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) then M
    else if (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) then c else 0
  symm u v := by fin_cases u <;> fin_cases v <;> rfl
  nonneg u v := by split_ifs <;> positivity
  diag v := by fin_cases v <;> rfl

/-- The indicator that an unordered pair crosses a shore. -/
def sep (S : Finset (Fin 4)) (u v : Fin 4) : ℝ :=
  if (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) then 1 else 0

theorem cut_graph (M c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c) (S : Finset (Fin 4)) :
    (graph M c hM hc).cut S =
      sep S 0 1 + M * (sep S 1 2 + sep S 2 3) + c * sep S 1 3 := by
  rw [WeightedGraph.cut_eq_sum_ite]
  simp only [Fin.sum_univ_succ]
  by_cases h0 : (0 : Fin 4) ∈ S <;> by_cases h1 : (1 : Fin 4) ∈ S <;>
    by_cases h2 : (2 : Fin 4) ∈ S <;> by_cases h3 : (3 : Fin 4) ∈ S <;>
    norm_num [graph, sep, h0, h1, h2, h3] <;> ring

theorem cut_pendant (M c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c) :
    (graph M c hM hc).cut {0} = 1 := by
  rw [cut_graph]
  norm_num [sep]

theorem cut_terminal_shore (M c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c) :
    (graph M c hM hc).cut {0, 1} = M + c := by
  rw [cut_graph]
  norm_num [sep]

private theorem proper_membership (S : Finset (Fin 4)) (hS : ProperShore S) :
    ((0 : Fin 4) ∈ S ∨ 1 ∈ S ∨ 2 ∈ S ∨ 3 ∈ S) ∧
      (0 ∉ S ∨ 1 ∉ S ∨ 2 ∉ S ∨ 3 ∉ S) := by
  constructor
  · obtain ⟨v, hv⟩ := hS.1
    fin_cases v <;> simp_all
  · by_contra h
    push Not at h
    apply hS.2
    ext v
    fin_cases v <;> simp_all

theorem one_le_cut (M c : ℝ) (hM : 1 ≤ M) (hc : 0 ≤ c)
    (S : Finset (Fin 4)) (hS : ProperShore S) :
    1 ≤ (graph M c (by linarith) hc).cut S := by
  obtain ⟨hne, hproper⟩ := proper_membership S hS
  rw [cut_graph]
  by_cases h0 : (0 : Fin 4) ∈ S <;> by_cases h1 : (1 : Fin 4) ∈ S <;>
    by_cases h2 : (2 : Fin 4) ∈ S <;> by_cases h3 : (3 : Fin 4) ∈ S <;>
    simp_all [sep] <;> linarith

theorem terminal_cut_lower (M c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (S : Finset (Fin 4)) (hs : 1 ∈ S) (ht : 3 ∉ S) :
    M + c ≤ (graph M c hM hc).cut S := by
  rw [cut_graph]
  by_cases hx : (0 : Fin 4) ∈ S <;> by_cases ha : (2 : Fin 4) ∈ S <;>
    simp [sep, hs, ht, hx, ha]

theorem pendant_isMinCut (M c : ℝ) (hM : 1 ≤ M) (hc : 0 ≤ c) :
    IsMinCut (graph M c (by linarith) hc) {0} := by
  refine ⟨properShore_singleton _ (by decide), ?_⟩
  intro S hS
  rw [cut_pendant]
  exact one_le_cut M c hM hc S hS

theorem global_value (M c : ℝ) (hM : 1 ≤ M) (hc : 0 ≤ c) :
    mincutValue (graph M c (by linarith) hc) = 1 := by
  let G := graph M c (by linarith) hc
  have hp : ProperShore ({0} : Finset (Fin 4)) := properShore_singleton _ (by decide)
  apply le_antisymm
  · simpa only [G, cut_pendant] using mincutValue_le G hp
  · obtain ⟨S, hS, he⟩ := exists_isMinCut G ⟨{0}, (mem_properShores _).mpr hp⟩
    rw [← he]
    exact one_le_cut M c hM hc S hS.1

theorem terminal_value (M c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c) :
    Augmentation.terminalValue (graph M c hM hc) 1 3 = M + c := by
  let G := graph M c hM hc
  apply le_antisymm
  · have h := Augmentation.terminalValue_le_cut G (by decide : (1 : Fin 4) ≠ 3)
      (S := {0, 1}) (by simp) (by norm_num)
    simpa only [G, cut_terminal_shore] using h
  · have h := Augmentation.terminalShore_spec G (by decide : (1 : Fin 4) ≠ 3)
    exact terminal_cut_lower M c hM hc _ h.1 h.2.1

/-- The fixed simple unit input graph. -/
def unitGraph : WeightedGraph (Fin 4) := graph 1 1 (by norm_num) (by norm_num)

/-- The retained weighted path; its positive support is contained in `unitGraph`. -/
def skeleton (M : ℝ) (hM : 1 ≤ M) : WeightedGraph (Fin 4) :=
  graph M 0 (by linarith) (by norm_num)

theorem unitGraph_unweighted : AllPairsAudit.Unweighted unitGraph := by
  intro u v
  fin_cases u <;> fin_cases v <;> norm_num [unitGraph, graph]

theorem skeleton_support_le (M : ℝ) (hM : 1 ≤ M) :
    (skeleton M hM).support ≤ unitGraph.support := by
  intro u v
  fin_cases u <;> fin_cases v <;>
    norm_num [WeightedGraph.support, skeleton, unitGraph, graph]

end SkeletonCounterexample

/-- **Paper 02, Proposition 4.** Even exact preservation of a global minimum
and containment of positive-edge supports do not control a prescribed
terminal minimum. The parameter is any real `M >= 1`, with no integrality
or upper-bound assumption. Vertices `0,1,2,3` are `x,s,a,t`, respectively. -/
theorem exists_weakSkeleton_terminal_gap (M : ℝ) (hM : 1 ≤ M) :
    ∃ G B : WeightedGraph (Fin 4),
      AllPairsAudit.Unweighted G ∧ B.support ≤ G.support ∧
      mincutValue B = 1 ∧ mincutValue G = 1 ∧
      B.cut {0} = 1 ∧ G.cut {0} = 1 ∧
      Augmentation.terminalValue G 1 3 = 2 ∧
      Augmentation.terminalValue B 1 3 = M := by
  refine ⟨SkeletonCounterexample.unitGraph, SkeletonCounterexample.skeleton M hM,
    SkeletonCounterexample.unitGraph_unweighted,
    SkeletonCounterexample.skeleton_support_le M hM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact SkeletonCounterexample.global_value M 0 hM (by norm_num)
  · exact SkeletonCounterexample.global_value 1 1 (by norm_num) (by norm_num)
  · exact SkeletonCounterexample.cut_pendant M 0 (by linarith) (by norm_num)
  · exact SkeletonCounterexample.cut_pendant 1 1 (by norm_num) (by norm_num)
  · simpa only [SkeletonCounterexample.unitGraph, one_add_one_eq_two] using
      SkeletonCounterexample.terminal_value 1 1 (by norm_num) (by norm_num)
  · simpa only [SkeletonCounterexample.skeleton, add_zero] using
      SkeletonCounterexample.terminal_value M 0 (by linarith) (by norm_num)

end
end CutQueryComplexity.CanonicalST

#print axioms CutQueryComplexity.CanonicalST.exists_weakSkeleton_terminal_gap
