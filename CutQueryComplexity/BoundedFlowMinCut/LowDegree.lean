import CutQueryComplexity.BoundedFlowMinCut.Basic
import CutQueryComplexity.Primitive.Certificate

/-! # The low-degree branch (M1)

Recover the threshold certificate `H` of `G` at threshold `2δ`, where `δ ≥ 1` is
the cut value of some singleton, and return a minimum proper shore of the
explicit graph `H`, chosen offline with no further query.

The shore transfers to `G`, not just the value. A minimizing shore `S` of `H`
has `H.cut S ≤ H.cut {v₀} ≤ δ < 2δ`. The certificate preserves cut values
truncated at `2δ`, so the strict margin forces `G.cut S = H.cut S`; and
`H ≤ G` makes `H.cut S ≤ H.cut T ≤ G.cut T` for every proper `T`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.BoundedFlowMinCut
noncomputable section
open scoped Classical
open WeightedGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A minimum proper shore of an explicit graph, chosen offline. -/
def offlineMinShore (H : WeightedGraph V) : Finset V :=
  if h : 2 ≤ Fintype.card V then Classical.choose (exists_isMinCut_of_two_le_card H h) else ∅

theorem offlineMinShore_spec (H : WeightedGraph V) (h : 2 ≤ Fintype.card V) :
    IsMinCut H (offlineMinShore H) := by
  rw [offlineMinShore, dite_eq_left h]
  exact Classical.choose_spec (exists_isMinCut_of_two_le_card H h)

/-- The low-degree program: a `2δ` threshold certificate, then an offline minimum shore. -/
def lowDegreeTree (δ : ℕ) : DTree (Finset V) ℝ (Finset V) (2 * δ * forestBudget V) :=
  (thresholdCertificate (2 * δ)).map offlineMinShore

omit [Fintype V] [DecidableEq V] in
theorem integral_of_unweighted {G : WeightedGraph V} (hG : AllPairsAudit.Unweighted G) :
    G.IsIntegral := fun u v => by
  rcases hG u v with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

/-- The low-degree program returns a global minimum cut of the input. -/
theorem lowDegree_correct (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (hn : 2 ≤ Fintype.card V) {δ : ℕ} (hδ : 1 ≤ δ) {v₀ : V} (hv₀ : G.cut {v₀} = δ) :
    IsMinCut G ((lowDegreeTree δ).eval G.cut) := by
  set H := (thresholdCertificate (2 * δ)).eval G.cut
  have hH := thresholdCertificate_correct (2 * δ) G (integral_of_unweighted hG)
  have hS := offlineMinShore_spec H hn
  rw [lowDegreeTree, DTree.eval_map]
  set S := offlineMinShore H
  have hHS : H.cut S ≤ δ :=
    (hS.2 {v₀} (properShore_singleton v₀ hn)).trans ((hH.1.cut_le {v₀}).trans hv₀.le)
  have hδpos : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hlt : H.cut S < ((2 * δ : ℕ) : ℝ) := by push_cast; linarith
  have heq : G.cut S = H.cut S := by
    have hmin := hH.2.2.2 S
    rw [min_eq_right hlt.le] at hmin
    by_cases hG2 : ((2 * δ : ℕ) : ℝ) ≤ G.cut S
    · rw [min_eq_left hG2] at hmin
      linarith
    · rw [min_eq_right (le_of_not_ge hG2)] at hmin
      exact hmin.symm
  refine ⟨hS.1, fun T hT => ?_⟩
  rw [heq]
  exact (hS.2 T hT).trans (hH.1.cut_le T)

omit [DecidableEq V] in
/-- The branch's cost cap is `O(n δ L)`. -/
theorem lowDegree_budget_le (δ : ℕ) :
    2 * δ * forestBudget V ≤ 24 * Fintype.card V * δ * logFactor (Fintype.card V) := by
  have h := searchDepth_add_one_le_logFactor (V := V)
  unfold forestBudget
  calc
    2 * δ * (12 * Fintype.card V * (searchDepth V + 1)) =
        24 * Fintype.card V * δ * (searchDepth V + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h

omit [DecidableEq V] in
/-- **Low-branch balance.** At or below the cutoff, the branch costs `O(n t L²)`. -/
theorem low_branch_balances {δ : ℕ} (hδ : δ ≤ cutoff (Fintype.card V)) :
    2 * δ * forestBudget V ≤
      24 * Fintype.card V * cutoffRoot (Fintype.card V) * logFactor (Fintype.card V) ^ 2 := by
  apply (lowDegree_budget_le (V := V) δ).trans
  calc
    24 * Fintype.card V * δ * logFactor (Fintype.card V) ≤
        24 * Fintype.card V * cutoff (Fintype.card V) * logFactor (Fintype.card V) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hδ)
    _ = _ := by unfold cutoff; ring

end
end CutQueryComplexity.BoundedFlowMinCut
