import CutQueryComplexity.AllMinCuts.Basic
import CutQueryComplexity.SupportForest.Endpoint

/-! # The minimum cuts of a disconnected graph (all-minima plan, M6)

From a correct positive-support forest (`SupportForest.Correct G fo`), a shore has cut value
zero exactly when it is a union of classes of the learned map `fo.r`
(`cut_eq_zero_iff_sat`): a zero cut cannot separate two vertices joined by a support path, and
no positive edge leaves a union of support components. When the support is disconnected,
`λ(G) = 0` and the minimum cuts are exactly the proper unions of classes; `zeroOutput fo.r`
lists them by filtering all shores with tests that depend only on `fo.r`, with no query
(`zeroOutput_correct`). The family can have `2^c − 2` members for `c` components.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllMinCuts

open WeightedGraph DetMinCut SupportForest Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Zero cuts are the unions of support components.** -/
theorem cut_eq_zero_iff_sat {G : WeightedGraph V} {fo : SupportForest.Output V}
    (h : SupportForest.Correct G fo) (S : Finset V) : G.cut S = 0 ↔ Sat fo.r S := by
  constructor
  · intro hz x y hxy
    have hr := (h.fiber_iff x y).mp hxy
    exact ⟨fun hx => reachable_mem_of_cut_zero G S hz hx hr,
      fun hy => reachable_mem_of_cut_zero G S hz hy hr.symm⟩
  · intro hsat
    rw [cut_eq_zero_iff_no_support_edge]
    intro u hu v hv hadj
    exact hv ((hsat u v ((h.fiber_iff u v).mpr hadj.reachable)).mp hu)

open Classical in
/-- The proper unions of the classes of `r`, with value zero. -/
noncomputable def zeroOutput (r : V → V) : AllMinCuts.Output V :=
  ⟨(properShores V).filter (Sat r), 0⟩

/-- On a graph with disconnected support, the zero family of a correct forest is correct. -/
theorem zeroOutput_correct {G : WeightedGraph V} {fo : SupportForest.Output V}
    (h : SupportForest.Correct G fo) (hn : 2 ≤ Fintype.card V)
    (hc : ¬ G.support.Connected) : AllMinCuts.Correct G (zeroOutput fo.r) := by
  have h0 : mincutValue G = 0 := by
    have hnpos := (support_connected_iff_pos G hn).not.mp hc
    have := mincutValue_nonneg G
    push Not at hnpos
    linarith
  refine ⟨h0.symm, fun S => ?_⟩
  rw [isMinCut_iff, h0, cut_eq_zero_iff_sat h S]
  classical
  simp [zeroOutput, mem_filter, mem_properShores]

end CutQueryComplexity.AllMinCuts
