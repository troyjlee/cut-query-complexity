import CutQueryComplexity.DetMinCut.MainLogLog
import CutQueryComplexity.DetMinCut.Unconditional
import CutQueryComplexity.Hierarchy.RackeShah.Existence
import CutQueryComplexity.TreeCutSparsifier.Endpoint

/-! # Deterministic weighted minimum cut with the Räcke–Shah hierarchy (log-log plan, M3)

`Hierarchy.RackeShah.rackeShah_hierarchyBound` discharges Lemma 21 with distortion
`268 L(r) L(L(r))` and height `2 L(r)`. Substituting it into the log-log main loop:

* `deterministic_mincut_log3loglog2_of_constantGuard`, `_of_retractionBound`,
  `_of_treeZeroExt`: `O(n^{3/2} L(n)³ L(L(n))²)` conditional on the guard in its three forms;
* `deterministic_mincut_log3loglog2`: the same with no hypothesis, via `treeZeroExt_42`;
* `deterministic_mincut_log3loglog2_real_log`: the cap in the paper's notation,
  `C n (√n + 1) log(2n)³ log(6 log(2n))²`, that is `O(n^{3/2} log³ n (log log n)²)`.

The log-five theorems of `Unconditional.lean` are unchanged.
-/

namespace CutQueryComplexity
namespace DetMinCut

open Hierarchy Hierarchy.RackeShah
open Hierarchy.RackeShah (KK)

theorem one_le_aLK (r : ℕ) : (1 : ℝ) ≤ rsConstant * (logL r : ℝ) * (logL (logL r) : ℝ) := by
  have hL : (1 : ℝ) ≤ logL r := by exact_mod_cast one_le_logL' r
  have hK : (1 : ℝ) ≤ logL (logL r) := by exact_mod_cast one_le_logL' (logL r)
  have hc : (1 : ℝ) ≤ rsConstant := by norm_num [rsConstant]
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc hL) hK

theorem aLK_monotone : Monotone fun r : ℕ => rsConstant * (logL r : ℝ) * (logL (logL r) : ℝ) := by
  intro r s hrs
  have hL : (logL r : ℝ) ≤ logL s := by exact_mod_cast logL_mono hrs
  have hK : (logL (logL r) : ℝ) ≤ logL (logL s) := by exact_mod_cast logL_mono (logL_mono hrs)
  have h0 : (0 : ℝ) ≤ logL r := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ logL (logL r) := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ rsConstant := by norm_num [rsConstant]
  simp only
  have h1 : rsConstant * (logL r : ℝ) ≤ rsConstant * logL s := by gcongr
  calc rsConstant * (logL r : ℝ) * (logL (logL r) : ℝ)
      ≤ rsConstant * (logL s : ℝ) * (logL (logL r) : ℝ) := by gcongr
    _ ≤ rsConstant * (logL s : ℝ) * (logL (logL s) : ℝ) := by gcongr

/-- **Theorem 1 with exponent `3 + 2 log log`, conditional only on the constant-quality
guard.** -/
theorem deterministic_mincut_log3loglog2_of_constantGuard {ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hcg : ConstantCutGuard ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log3loglog2_fin_of_hierarchyBound_of_constantGuard
    rackeShah_hierarchyBound one_le_aLK aLK_monotone (A0 := rsConstant) (fun _ => le_rfl)
    hρ0 hcg

/-- **Theorem 1 with exponent `3 + 2 log log`, conditional only on a retraction bound.** -/
theorem deterministic_mincut_log3loglog2_of_retractionBound {ρ0 : ℝ} (hρ0 : 1 ≤ ρ0)
    (hr : RetractionBound ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log3loglog2_of_constantGuard hρ0
    (constantCutGuard_of_retractionBound (by linarith) hr)

/-- **Theorem 1 with exponent `3 + 2 log log`, conditional only on the aggregate tree
inequality.** -/
theorem deterministic_mincut_log3loglog2_of_treeZeroExt {α : ℝ} (hα : 1 ≤ α)
    (ht : TreeZeroExt α) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log3loglog2_of_retractionBound hα (retractionBound_of_treeZeroExt ht)

/-- **Theorem 1 with exponent `3 + 2 log log`, unconditional.** One deterministic decision
tree per `n` with `O(n (⌊√n⌋ + 1) L(n)³ L(L(n))²)` cut queries returns a minimum cut of every
nonnegative weighted graph on `n ≥ 2` vertices. -/
theorem deterministic_mincut_log3loglog2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  deterministic_mincut_log3loglog2_of_treeZeroExt (by norm_num) treeZeroExt_42

/-! ## The natural-logarithm reading -/

/-- `L(L(n)) ≤ 3 log(6 log(2n))` for `n ≥ 2`. -/
theorem logL_logL_le_real_log {n : ℕ} (hn : 2 ≤ n) :
    (logL (logL n) : ℝ) ≤ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) := by
  have hL := TreeCutSparsifier.logL_le_real_log hn
  have hlog1 := TreeCutSparsifier.real_log_one hn
  have hL2 : 2 ≤ logL n := by
    have h1 : 4 ≤ 2 ^ logL n := le_two_pow_logL 2 |>.trans (Nat.pow_le_pow_right (by norm_num)
      (logL_mono hn))
    by_contra h
    push Not at h
    have : 2 ^ logL n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hK := TreeCutSparsifier.logL_le_real_log hL2
  have h2L : Real.log (2 * (logL n : ℝ)) ≤ Real.log (6 * Real.log (2 * (n : ℝ))) := by
    apply Real.log_le_log (by positivity)
    linarith
  linarith

/-- **The cap in the paper's notation**: `O(n^{3/2} log³ n (log log n)²)`. -/
theorem deterministic_mincut_log3loglog2_real_log :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S := by
  obtain ⟨C, hC, hall⟩ := deterministic_mincut_log3loglog2
  refine ⟨C * 3 ^ 5, by positivity, fun n hn => ?_⟩
  obtain ⟨q, hq, D, hD⟩ := hall n hn
  refine ⟨q, hq.trans ?_, D, hD⟩
  have hL := TreeCutSparsifier.logL_le_real_log hn
  have hK := logL_logL_le_real_log hn
  have hlog1 := TreeCutSparsifier.real_log_one hn
  have hlog6 : 0 ≤ Real.log (6 * Real.log (2 * (n : ℝ))) := by
    apply Real.log_nonneg; linarith
  have hL0 : (0 : ℝ) ≤ logL n := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ logL (logL n) := Nat.cast_nonneg _
  have hs : (0 : ℝ) ≤ (n : ℝ) * (Nat.sqrt n + 1) := by positivity
  have h3 : (logL n : ℝ) ^ 3 ≤ (3 * Real.log (2 * (n : ℝ))) ^ 3 := pow_le_pow_left₀ hL0 hL 3
  have h2 : (logL (logL n) : ℝ) ^ 2 ≤ (3 * Real.log (6 * Real.log (2 * (n : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ hK0 hK 2
  calc C * (n : ℝ) * (Nat.sqrt n + 1) * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2)
      ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * ((3 * Real.log (2 * (n : ℝ))) ^ 3 *
          (3 * Real.log (6 * Real.log (2 * (n : ℝ)))) ^ 2) := by
        gcongr
    _ = C * 3 ^ 5 * (n : ℝ) * (Nat.sqrt n + 1) *
          (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) := by ring

end DetMinCut
end CutQueryComplexity
