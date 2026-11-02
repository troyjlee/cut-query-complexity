import CutQueryComplexity.DirectedUnitST.Repair.HeavyTerminal

/-!
# Scaled middle-layer geometry

Dividing capacities and a feasible flow by a positive public scale preserves
the residual arcs. This is used only in the geometric proof. Operational
phase amounts remain unscaled natural numbers, so their eventual positivity
proof is not weakened by this normalization. Terminal-star capacities are
unrestricted throughout.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset Certificate DirectedCertificate DirectedUnitST.Repair

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Proof-side capacity normalization; this does not issue a query. -/
noncomputable def divideNetwork (G : WeightedDiGraph V) (C : ℝ) (hC : 0 ≤ C) :
    WeightedDiGraph V where
  c u v := G.c u v / C
  nonneg u v := div_nonneg (G.nonneg u v) hC
  diag v := by rw [G.diag, zero_div]

noncomputable def divideFlow (f : V → V → ℝ) (C : ℝ) : V → V → ℝ :=
  fun u v => f u v / C

theorem divideFlow_isFlow {f : V → V → ℝ} (hf : IsFlow f) (C : ℝ) :
    IsFlow (divideFlow f C) := by
  intro u v
  simp only [divideFlow, hf u v, neg_div]

theorem netOut_divideFlow (f : V → V → ℝ) (C : ℝ) (v : V) :
    netOut (divideFlow f C) v = netOut f v / C := by
  simp only [netOut, divideFlow, sum_div]

theorem divideFlow_feasible {G : WeightedDiGraph V} {f : V → V → ℝ}
    (hf : G.Feasible f) (C : ℝ) (hC : 0 ≤ C) :
    (divideNetwork G C hC).Feasible (divideFlow f C) := by
  refine ⟨divideFlow_isFlow hf.1 C, ?_⟩
  intro u v
  exact div_le_div_of_nonneg_right (hf.2 u v) hC

theorem divideFlow_stFlow {G : WeightedDiGraph V} {s t : V} {f : V → V → ℝ}
    (hf : G.STFlow s t f) (C : ℝ) (hC : 0 ≤ C) :
    (divideNetwork G C hC).STFlow s t (divideFlow f C) := by
  refine ⟨divideFlow_feasible hf.1 C hC, ?_⟩
  intro v hvs hvt
  rw [netOut_divideFlow, hf.2 v hvs hvt, zero_div]

theorem divideFlow_residual_capacity {G : WeightedDiGraph V} {f : V → V → ℝ}
    (hf : G.Feasible f) (C : ℝ) (hC : 0 ≤ C) (u v : V) :
    (residual (divideNetwork G C hC) (divideFlow f C)
      (divideFlow_feasible hf C hC)).c u v = (residual G f hf).c u v / C := by
  change G.c u v / C - f u v / C = (G.c u v - f u v) / C
  exact (sub_div _ _ _).symm

theorem divideFlow_residual_pos_iff {G : WeightedDiGraph V} {f : V → V → ℝ}
    (hf : G.Feasible f) (C : ℝ) (hC : 0 < C) (u v : V) :
    0 < (residual (divideNetwork G C hC.le) (divideFlow f C)
      (divideFlow_feasible hf C hC.le)).c u v ↔ 0 < (residual G f hf).c u v := by
  rw [divideFlow_residual_capacity]
  exact div_pos_iff_of_pos_right hC

/-- Internal opposite-pair capacity at most `2*C` gives a remaining flow
deficit at most `8*C*q^2/d^2`. The target is any feasible flow, including the
final flow of an early-stopped finite history; no optimum is assumed. -/
theorem scaled_residual_middle_layer_deficit (G : WeightedDiGraph V) (C : ℝ)
    (hC : 0 < C) (s t : V) (target current : V → V → ℝ)
    (htarget : G.STFlow s t target) (hcurrent : G.STFlow s t current)
    (level : V → ℕ) (d : ℕ)
    (hlevel : ∀ u v, 0 < (residual G current hcurrent.1).c u v →
      level v ≤ level u + 1)
    (hs : level s = 0) (ht : level t = d) (hd : 4 ≤ d)
    (hcap : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t →
      G.c u v + G.c v u ≤ 2 * C) :
    netOut target s - netOut current s ≤
      8 * C * ((internalVertices s t).card : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
  have htarget' := divideFlow_stFlow htarget C hC.le
  have hcurrent' := divideFlow_stFlow hcurrent C hC.le
  have hlevel' : ∀ u v,
      0 < (residual (divideNetwork G C hC.le) (divideFlow current C) hcurrent'.1).c u v →
      level v ≤ level u + 1 := by
    intro u v huv
    apply hlevel u v
    exact (divideFlow_residual_pos_iff hcurrent.1 C hC u v).mp huv
  have hcap' : ∀ u v, u ≠ s → u ≠ t → v ≠ s → v ≠ t →
      (divideNetwork G C hC.le).c u v + (divideNetwork G C hC.le).c v u ≤ 2 := by
    intro u v hus hut hvs hvt
    change G.c u v / C + G.c v u / C ≤ 2
    rw [← add_div]
    exact (div_le_iff₀ hC).mpr (hcap u v hus hut hvs hvt)
  have h := residual_middle_layer_deficit (divideNetwork G C hC.le) s t
    (divideFlow target C) (divideFlow current C) htarget' hcurrent' level d
    hlevel' hs ht hd hcap'
  rw [netOut_divideFlow, netOut_divideFlow, ← sub_div] at h
  have hmul := (div_le_iff₀ hC).mp h
  calc
    netOut target s - netOut current s ≤
        (8 * ((internalVertices s t).card : ℝ) ^ 2 / (d : ℝ) ^ 2) * C := hmul
    _ = 8 * C * ((internalVertices s t).card : ℝ) ^ 2 / (d : ℝ) ^ 2 := by ring

end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.divideFlow_stFlow
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.divideFlow_residual_pos_iff
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaled_residual_middle_layer_deficit
