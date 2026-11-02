import CutQueryComplexity.UndirectedClosure.HierarchyBudgetLogLog
import CutQueryComplexity.TreeCutSparsifier.Canonicalization
import CutQueryComplexity.TreeCutSparsifier.Endpoint
import CutQueryComplexity.TreeCutSparsifier.Conversion
import CutQueryComplexity.DetMinCut.UnconditionalLogLog

/-! # The conversion theorem with the Räcke–Shah quality (log-log plan, M4)

`Conversion.lean` with the supplied-hierarchy program of `HierarchyBudgetLogLog`: an arbitrary
`B`-tree cut sparsifier is converted to a weak skeleton in `O(n B L(n)³ L(L(n))²)` queries
(`exists_conversion_log3loglog2_real_log3loglog2`), that is `O(n B log³ n (log log n)²)`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open WeightedGraph Hierarchy DetMinCut TwoRespecting UndirectedClosure Hierarchy.RackeShah

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Conversion with the Räcke–Shah quality.** -/
theorem exists_conversion_log3loglog2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ IsWeakSkeleton G F := by
  refine ⟨hierarchyConstantLL + 1, by linarith [hierarchyConstantLL_pos],
    fun n input B hn hB => ?_⟩
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn' : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  refine ⟨hierarchyBudgetLL (Fintype.card (Fin n)) B, by simpa using hierarchyBudgetLL_le hn' hB,
    suppliedHierarchyTreeLL (normalTopology input.tree) B, fun read => DTree.cost_le _ read,
    fun G hpos h => ?_⟩
  have hN := normalTopology_normal input.tree
  exact suppliedHierarchyTreeLL_correct _ B G hn' hpos hB hN.leaves (by have := hN.size; omega)
    (approximates_promise input G hn' h)

/-- The conversion cap in the paper's notation: `O(n B log³(2n) (log log)²)`. -/
theorem exists_conversion_log3loglog2_real_log :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B *
          (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ IsWeakSkeleton G F := by
  obtain ⟨C, hC, hall⟩ := exists_conversion_log3loglog2
  refine ⟨C * 3 ^ 5, by positivity, fun n input B hn hB => ?_⟩
  obtain ⟨q, hq, D, hcost, hcorrect⟩ := hall n input B hn hB
  refine ⟨q, hq.trans ?_, D, hcost, hcorrect⟩
  have hL := logL_le_real_log hn
  have hK := DetMinCut.logL_logL_le_real_log hn
  have hlog1 := real_log_one hn
  have hlog6 : 0 ≤ Real.log (6 * Real.log (2 * (n : ℝ))) := by
    apply Real.log_nonneg; linarith
  have hB0 : 0 ≤ B := by linarith
  have hL0 : (0 : ℝ) ≤ logL n := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ logL (logL n) := Nat.cast_nonneg _
  have h3 : (logL n : ℝ) ^ 3 ≤ (3 * Real.log (2 * (n : ℝ))) ^ 3 := pow_le_pow_left₀ hL0 hL 3
  have h2 : (logL (logL n) : ℝ) ^ 2 ≤ (3 * Real.log (6 * Real.log (2 * (n : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ hK0 hK 2
  calc C * n * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2)
      ≤ C * n * B * ((3 * Real.log (2 * (n : ℝ))) ^ 3 *
          (3 * Real.log (6 * Real.log (2 * (n : ℝ)))) ^ 2) := by gcongr
    _ = C * 3 ^ 5 * n * B *
          (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) := by ring

end CutQueryComplexity.TreeCutSparsifier
