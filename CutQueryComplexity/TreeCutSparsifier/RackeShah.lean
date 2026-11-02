import CutQueryComplexity.Hierarchy.RackeShah.Existence
import CutQueryComplexity.TreeCutSparsifier.Endpoint

/-! # Räcke–Shah trees as explicit tree cut sparsifiers

For a nonempty vertex set, the offline hierarchy of `rackeShah_hierarchyBound` with its
canonical capacities is `TreeData.Good` with factor `268 L(n) L(L(n))`
(`exists_good_tree_log_mul_loglog`). `logL_mul_logL_logL_le` reads the factor in natural
logarithms: for `n ≥ 2` it is at most `9 log(2n) log(6 log(2n)) = O(log n log log n)`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open DetMinCut Hierarchy Hierarchy.RackeShah

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The offline Räcke–Shah tree with canonical capacities is a good explicit tree. -/
theorem exists_good_tree_log_mul_loglog [Nonempty V] (G : WeightedGraph V) :
    ∃ P : Pkg V, P.m ≤ 2 * Fintype.card V + 1 ∧ P.H.LeafChildless ∧
      P.H.height ≤ 2 * logL (Fintype.card V) ∧
      (canonicalTree P G).Good G
        (rsConstant * logL (Fintype.card V) * logL (logL (Fintype.card V))) := by
  obtain ⟨hm, hlc, hht, hrep⟩ := hbPkg_spec rackeShah_hierarchyBound G
  refine ⟨hbPkg rackeShah_hierarchyBound G, hm, hlc, hht, ?_⟩
  refine canonicalTree_good _ G ?_ hlc hrep
  have := Fintype.card_pos (α := V)
  omega

/-- `L(n) L(L(n)) ≤ 9 log(2n) log(6 log(2n))` for `n ≥ 2`. -/
theorem logL_mul_logL_logL_le {n : ℕ} (hn : 2 ≤ n) :
    (logL n : ℝ) * (logL (logL n) : ℝ) ≤
      9 * Real.log (2 * (n : ℝ)) * Real.log (6 * Real.log (2 * (n : ℝ))) := by
  have hL := logL_le_real_log hn
  have hlog1 := real_log_one hn
  have hL2 : 2 ≤ logL n := by
    have h1 : 4 ≤ 2 ^ logL n := le_two_pow_logL 2 |>.trans (Nat.pow_le_pow_right (by norm_num)
      (logL_mono hn))
    by_contra h
    push Not at h
    have : 2 ^ logL n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hK := logL_le_real_log hL2
  have hLr : (0 : ℝ) ≤ logL n := Nat.cast_nonneg _
  have h2L : Real.log (2 * (logL n : ℝ)) ≤ Real.log (6 * Real.log (2 * (n : ℝ))) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hlog6 : 0 ≤ Real.log (6 * Real.log (2 * (n : ℝ))) := by
    apply Real.log_nonneg; linarith
  calc (logL n : ℝ) * (logL (logL n) : ℝ)
      ≤ (3 * Real.log (2 * (n : ℝ))) * (3 * Real.log (2 * (logL n : ℝ))) := by
        apply mul_le_mul hL hK (Nat.cast_nonneg _) (by positivity)
    _ ≤ (3 * Real.log (2 * (n : ℝ))) * (3 * Real.log (6 * Real.log (2 * (n : ℝ)))) := by
        gcongr
    _ = _ := by ring

end CutQueryComplexity.TreeCutSparsifier
