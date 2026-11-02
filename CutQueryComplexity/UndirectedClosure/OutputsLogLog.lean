import CutQueryComplexity.UndirectedClosure.Outputs
import CutQueryComplexity.DetMinCut.UnconditionalLogLog

/-! # Exact shore-and-value output with the log-log bound (log-log plan, M3) -/

set_option autoImplicit false

namespace CutQueryComplexity.UndirectedClosure

/-- The log-log global algorithm with both an optimum shore and its exact value. -/
theorem deterministic_mincut_shore_value_log3loglog2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n) × ℝ)) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), ∃ S,
            D.eval G.cut = some (S, mincutValue G) ∧ IsMinCut G S := by
  obtain ⟨C, hC, hsolve⟩ := DetMinCut.deterministic_mincut_log3loglog2
  refine ⟨C + 1, by linarith, fun n hn => ?_⟩
  obtain ⟨q, hq, D, hD⟩ := hsolve n hn
  refine ⟨q + 1, ?_, withShoreValue D, fun read => DTree.cost_le _ read, ?_⟩
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hs1 : (1 : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt n)]
    have hL1 : (1 : ℝ) ≤ (DetMinCut.logL n : ℝ) := by exact_mod_cast DetMinCut.one_le_logL' n
    have hK1 : (1 : ℝ) ≤ (DetMinCut.logL (DetMinCut.logL n) : ℝ) := by
      exact_mod_cast DetMinCut.one_le_logL' _
    have hbase : (1 : ℝ) ≤ (n : ℝ) * (Nat.sqrt n + 1) *
        ((DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hs1)
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hK1))
    push_cast
    nlinarith
  · intro G
    obtain ⟨S, heval, hS⟩ := hD G
    refine ⟨S, ?_, hS⟩
    rw [withShoreValue_eval, heval]
    simp only [Option.map_some, DetMinCut.isMinCut_of_sat hS]

end CutQueryComplexity.UndirectedClosure
