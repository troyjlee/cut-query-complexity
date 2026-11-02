import CutQueryComplexity.DetMinCut.Asymptotic
import CutQueryComplexity.DetMinCut.MainLog7
import CutQueryComplexity.DetMinCut.MainLog5
import CutQueryComplexity.Hierarchy.Existence
import CutQueryComplexity.Hierarchy.GuardTransfer
import CutQueryComplexity.Hierarchy.GuardDuality
import CutQueryComplexity.Hierarchy.Retract.TreeZeroExt

/-! # Deterministic weighted minimum cut without a hierarchy assumption

`Hierarchy.exists_hierarchyBound_sq` discharges Lemma 21 with distortion `1690 L(r)²` and
height `4 L(r)`. Substituting it:

* `deterministic_mincut_upper`: one deterministic decision tree per `n` with
  `O(n (⌊√n⌋ + 1) L(n)^16)` cut queries returns a minimum cut of every nonnegative weighted
  graph on `n` vertices, with no hypothesis;
* `deterministic_mincut_log7_of_constantGuard`: the paper's `O(n^{3/2} log^7 n)`, now
  conditional only on the constant-quality terminal cut guard (Lemma 19);
* `deterministic_mincut_log7_of_retractionBound`: the same, conditional only on a
  load-bounded distribution of retractions (`RetractionBound`), which implies the guard;
* `deterministic_mincut_log5_of_constantGuard`, `deterministic_mincut_log5_of_retractionBound`:
  `O(n^{3/2} log^5 n)`, using the quadratic distortion directly with `k = kLog5 N`;
* `deterministic_mincut_log5_of_treeZeroExt`: the same, conditional only on the aggregate tree
  inequality `TreeZeroExt`, via the minimax duality `retractionBound_of_treeZeroExt`;
* `deterministic_mincut_log5`: `O(n^{3/2} log^5 n)` with no hypothesis, using
  `Hierarchy.treeZeroExt_42` (`Hierarchy/Retract`).
-/

namespace CutQueryComplexity
namespace DetMinCut

open Hierarchy

theorem one_le_aSq (r : ℕ) : (1 : ℝ) ≤ 1690 * (logL r : ℝ) ^ 2 := by
  have : (1 : ℝ) ≤ (logL r : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast one_le_logL' r)
  linarith

theorem aSq_monotone : Monotone fun r : ℕ => 1690 * (logL r : ℝ) ^ 2 := by
  intro r s hrs
  have : (logL r : ℝ) ≤ logL s := by exact_mod_cast logL_mono hrs
  have h0 : (0 : ℝ) ≤ logL r := Nat.cast_nonneg _
  simp only
  nlinarith

theorem hSq_monotone : Monotone fun r : ℕ => 4 * logL r :=
  fun _ _ hrs => Nat.mul_le_mul_left 4 (logL_mono hrs)

/-- **Theorem 1, unconditional.** One deterministic decision tree per `n` with
`O(n (⌊√n⌋ + 1) L(n)^16)` cut queries returns a minimum cut of every nonnegative weighted
graph on `n ≥ 2` vertices. -/
theorem deterministic_mincut_upper :
    ∃ C : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∃ q : ℕ, (q : ℝ) ≤ C * Fintype.card V * (Nat.sqrt (Fintype.card V) + 1) *
          (logL (Fintype.card V) : ℝ) ^ 16 ∧
        ∃ D : DTree (Finset V) ℝ (Option (Finset V)) q,
          ∀ G : WeightedGraph V, ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_upper_of_hierarchyBound exists_hierarchyBound_sq one_le_aSq aSq_monotone
    hSq_monotone (A0 := 1690) (H0 := 4) (p := 2) (fun r => le_rfl)
    (fun r => by push_cast; exact le_rfl) (by norm_num)

/-- **Theorem 1 with exponent seven, conditional only on the constant-quality guard.** -/
theorem deterministic_mincut_log7_of_constantGuard {ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hcg : ConstantCutGuard ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (logL n : ℝ) ^ 7 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log7_fin_of_hierarchyBound_of_constantGuard exists_hierarchyBound_sq
    one_le_aSq aSq_monotone (A0 := 1690) (fun r => by
      have hL : (1 : ℝ) ≤ logL r := by exact_mod_cast one_le_logL' r
      have : (logL r : ℝ) ^ 2 ≤ (logL r : ℝ) ^ 3 := pow_le_pow_right₀ hL (by norm_num)
      linarith) hρ0 hcg

/-- **Theorem 1 with exponent seven, conditional only on a retraction bound.** -/
theorem deterministic_mincut_log7_of_retractionBound {ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hr : RetractionBound ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (logL n : ℝ) ^ 7 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log7_of_constantGuard hρ0
    (constantCutGuard_of_retractionBound (by linarith) hr)

/-- **Theorem 1 with exponent five, conditional only on the constant-quality guard.** -/
theorem deterministic_mincut_log5_of_constantGuard {ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hcg : ConstantCutGuard ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (logL n : ℝ) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log5_fin_of_hierarchyBound_of_constantGuard exists_hierarchyBound_sq
    one_le_aSq aSq_monotone (A0 := 1690) (fun _ => le_rfl) hρ0 hcg

/-- **Theorem 1 with exponent five, conditional only on a retraction bound.** -/
theorem deterministic_mincut_log5_of_retractionBound {ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hr : RetractionBound ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (logL n : ℝ) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log5_of_constantGuard hρ0
    (constantCutGuard_of_retractionBound (by linarith) hr)

/-- **Theorem 1 with exponent five, conditional only on the aggregate tree inequality.** -/
theorem deterministic_mincut_log5_of_treeZeroExt {α : ℝ} (hα : 1 ≤ α) (ht : TreeZeroExt α) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (logL n : ℝ) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log5_of_retractionBound hα (retractionBound_of_treeZeroExt ht)

/-- **Theorem 1 with exponent five, unconditional.** One deterministic decision tree per `n`
with `O(n (⌊√n⌋ + 1) L(n)^5)` cut queries returns a minimum cut of every nonnegative weighted
graph on `n ≥ 2` vertices. -/
theorem deterministic_mincut_log5 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (logL n : ℝ) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log5_of_treeZeroExt (by norm_num) treeZeroExt_42

end DetMinCut
end CutQueryComplexity
