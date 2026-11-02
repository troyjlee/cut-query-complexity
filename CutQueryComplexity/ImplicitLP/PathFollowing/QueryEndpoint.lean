import CutQueryComplexity.ImplicitLP.PathFollowing.PrimitiveBudget

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 512

/-! # Explicit terminal and global directed-mincut query bounds

The programs and their success theorems are the actual calibrated finite runs.
The costs below hold for every answer oracle. Their only numerical inputs are
n and the requested failure probability. The constants are deliberately loose.
-/

namespace CutQueryComplexity.ImplicitLP.PathFollowing

open Real
noncomputable section

private theorem n_mul_sqrt_eq {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.sqrt n = (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow]
  calc (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) =
      (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hn0 _ _).symm
    _ = _ := by norm_num

/-- The literal finite terminal budget has the advertised power of n. -/
theorem calibrated_terminal_budget_le {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    let P := calibratedParams n s t ζ
    (((2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
      (2 * n * (3 + 3 * Sparsify.pK n) + 1) : ℕ) : ℝ) ≤
      2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * failureLog n ζ ^ 21 := by
  intro P
  let L := failureLog n ζ
  let B := (n : ℝ) * Real.sqrt n * L ^ 21
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL := (failureLog_spec hn hζ hζ1).1
  have hq : queryLog n ≤ L := by
    have hh := (failureLog_spec hn hζ hζ1).2.1
    rw [envelopeLog_eq n (by omega)] at hh
    linarith
  have hq0 : 0 ≤ queryLog n := le_trans (by norm_num : (0 : ℝ) ≤ 1) (queryLog_one_le hn)
  have hs : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hscale : 1 ≤ Real.sqrt (n : ℝ) * L ^ 6 := by
    have hh : 1 ≤ L ^ 6 := one_le_pow₀ hL
    nlinarith
  have hdown : (P.downSteps : ℝ) ≤ 2 ^ 74 * Real.sqrt n * L ^ 6 :=
    (calibratedDownSteps_le hn s t ζ).trans (by gcongr)
  have hup : (P.upSteps : ℝ) ≤ 2 ^ 74 * Real.sqrt n * L ^ 6 :=
    (calibratedUpSteps_le hn s t ζ).trans (by gcongr)
  have hphases : (P.downSteps : ℝ) + 1 + P.upSteps ≤ 2 ^ 76 * Real.sqrt n * L ^ 6 := by
    nlinarith
  have hfinal : (P.finalSteps : ℝ) ≤ 20 * L := (publicFinalCount_le hn).trans (by gcongr)
  obtain ⟨hnewton, hinit, hbatch⟩ := calibrated_primitive_budgets hn s t hζ hζ1
  change (P.newtonBudget : ℝ) ≤ 2 ^ 217 * n * L ^ 14 at hnewton
  change (P.initialBudget : ℝ) ≤ 2 ^ 224 * n * L ^ 15 at hinit
  change (P.batchBudget : ℝ) ≤ 2 ^ 226 * n * L ^ 15 at hbatch
  have hgrowth (k : ℕ) (hk : k ≤ 21) : (n : ℝ) * L ^ k ≤ B := by
    calc (n : ℝ) * L ^ k ≤ n * L ^ 21 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hk) hn0.le
      _ ≤ ((n : ℝ) * Real.sqrt n) * L ^ 21 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
  have hinit' : (P.initialBudget : ℝ) ≤ 2 ^ 224 * B := by
    exact hinit.trans (by nlinarith [hgrowth 15 (by norm_num)])
  have hpath : ((P.downSteps : ℝ) + 1 + P.upSteps) * P.batchBudget ≤ 2 ^ 302 * B := by
    have hh := mul_le_mul hphases hbatch (Nat.cast_nonneg _)
      (by positivity : 0 ≤ 2 ^ 76 * Real.sqrt n * L ^ 6)
    convert hh using 1 <;> dsimp [B] <;> ring
  have hcenter : (P.finalSteps : ℝ) * P.newtonBudget ≤ 2 ^ 222 * B := by
    have hh := mul_le_mul hfinal hnewton (Nat.cast_nonneg _) (by positivity : 0 ≤ 20 * L)
    have he : (20 * L) * (2 ^ 217 * n * L ^ 14) = (20 * 2 ^ 217) * ((n : ℝ) * L ^ 15) := by ring
    rw [he] at hh
    have hg := hgrowth 15 (by norm_num)
    nlinarith
  have hsolver : (P.solverBudget P.downSteps P.upSteps P.finalSteps : ℝ) ≤ 2 ^ 304 * B := by
    have he : (P.solverBudget P.downSteps P.upSteps P.finalSteps : ℝ) =
        (P.initialBudget : ℝ) + ((P.downSteps : ℝ) + 1 + P.upSteps) * P.batchBudget +
          (P.finalSteps : ℝ) * P.newtonBudget := by
      unfold Params.solverBudget
      push_cast
      ring
    rw [he]
    nlinarith
  have hsearch : ((3 + 3 * Sparsify.pK n : ℕ) : ℝ) ≤ 9 * L :=
    (extractionSearchFactor_le hn).trans (by gcongr)
  have hsmall : ((2 * n + (2 * n * (3 + 3 * Sparsify.pK n) + 1) : ℕ) : ℝ) ≤ 32 * B := by
    have hh := mul_le_mul_of_nonneg_left hsearch (by positivity : 0 ≤ 2 * (n : ℝ))
    have hg := hgrowth 1 (by norm_num)
    push_cast at hh ⊢
    simp only [pow_one] at hg
    have hprod : 2 ≤ (n : ℝ) * L := by nlinarith
    nlinarith
  have heq : (n : ℝ) ^ (3 / 2 : ℝ) * L ^ 21 = B := by
    rw [← n_mul_sqrt_eq (by omega : 0 < n)]
  have hcombine :
      (((2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
        (2 * n * (3 + 3 * Sparsify.pK n) + 1) : ℕ) : ℝ) =
      (P.solverBudget P.downSteps P.upSteps P.finalSteps : ℝ) +
        ((2 * n + (2 * n * (3 + 3 * Sparsify.pK n) + 1) : ℕ) : ℝ) := by
    push_cast
    ring
  change _ ≤ 2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * L ^ 21
  rw [hcombine, show (2 : ℝ) ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * L ^ 21 =
      2 ^ 310 * B by rw [mul_assoc, heq]]
  nlinarith only [hsmall, hsolver, hB]

/-- All-oracle terminal query count; exact local real arithmetic is free. -/
theorem calibratedTerminalSolver_query_bound {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (read : Finset (Fin n) → ℕ)
    {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run read (calibratedTerminalSolver n s t ζ)).support) :
    (out.2 : ℝ) ≤ 2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * failureLog n ζ ^ 21 := by
  have hc := calibratedTerminalSolver_cost_all_oracles n s t ζ read ho
  change out.2 ≤ (2 * n + (calibratedParams n s t ζ).solverBudget
    (calibratedParams n s t ζ).downSteps (calibratedParams n s t ζ).upSteps
    (calibratedParams n s t ζ).finalSteps) + (2 * n * (3 + 3 * Sparsify.pK n) + 1) at hc
  have hc' : (out.2 : ℝ) ≤
      (((2 * n + (calibratedParams n s t ζ).solverBudget
        (calibratedParams n s t ζ).downSteps (calibratedParams n s t ζ).upSteps
        (calibratedParams n s t ζ).finalSteps) + (2 * n * (3 + 3 * Sparsify.pK n) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hc
  exact hc'.trans (calibrated_terminal_budget_le hn s t hζ hζ1)

private theorem failureLog_half {n : ℕ} (hn : 2 ≤ n) {ζ : ℝ} (hζ : 0 < ζ) :
    failureLog n (ζ / 2) = 1 + failureLog n ζ := by
  have hH := queryHeight_two_le hn
  unfold failureLog
  rw [show queryHeight n / (ζ / 2) = 2 * (queryHeight n / ζ) by ring,
    Real.logb_mul (by norm_num) (by positivity),
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]

/-- The balanced actual global program has the target power, including learning and roots. -/
theorem balancedGlobalMinCut_query_bound {n : ℕ} (hn : 2 ≤ n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (read : Finset (Fin n) → ℕ)
    {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run read (balancedGlobalMinCut n hn ζ)).support) :
    (out.2 : ℝ) ≤ 2 ^ 340 * (n : ℝ) ^ (7 / 4 : ℝ) * failureLog n ζ ^ 22 := by
  let L := failureLog n ζ
  let P := calibratedGlobalParams n hn (ζ / 2)
  let Q : ℕ := (2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
    (2 * n * (3 + 3 * Sparsify.pK n) + 1)
  change (out.2 : ℝ) ≤ 2 ^ 340 * (n : ℝ) ^ (7 / 4 : ℝ) * L ^ 22
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL := (failureLog_spec hn hζ hζ1).1
  have hlog := (failureLog_spec hn hζ hζ1).2.2
  have hq : queryLog n ≤ L := by
    have hh := (failureLog_spec hn hζ hζ1).2.1
    rw [envelopeLog_eq n (by omega)] at hh
    linarith
  have hterm : (Q : ℝ) ≤ 2 ^ 331 * (n : ℝ) ^ (3 / 2 : ℝ) * L ^ 21 := by
    have hh := calibrated_terminal_budget_le hn (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      (by positivity : 0 < ζ / 2) (by linarith : ζ / 2 ≤ 1)
    have hf : failureLog n (ζ / 2) ≤ 2 * L := by rw [failureLog_half hn hζ]; linarith
    have hfp : 0 ≤ failureLog n (ζ / 2) := by rw [failureLog_half hn hζ]; linarith
    calc (Q : ℝ) ≤ 2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * failureLog n (ζ / 2) ^ 21 := hh
      _ ≤ 2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * (2 * L) ^ 21 := by gcongr
      _ = _ := by ring
  have hquarter : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hroot : 4 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log (2 / ζ) + 2 ≤
      6 * (n : ℝ) ^ (1 / 4 : ℝ) * L := by
    have hh := mul_le_mul_of_nonneg_left hlog
      (by positivity : 0 ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ))
    have hprod : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) * L := by nlinarith
    linarith
  have hpower : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) ^ (7 / 4 : ℝ) := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hrootcost : (4 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log (2 / ζ) + 2) * Q ≤
      (6 * 2 ^ 331) * (n : ℝ) ^ (7 / 4 : ℝ) * L ^ 22 := by
    have hh := mul_le_mul hroot hterm (Nat.cast_nonneg _)
      (by positivity : 0 ≤ 6 * (n : ℝ) ^ (1 / 4 : ℝ) * L)
    have he : (6 * (n : ℝ) ^ (1 / 4 : ℝ) * L) *
        (2 ^ 331 * (n : ℝ) ^ (3 / 2 : ℝ) * L ^ 21) =
        (6 * 2 ^ 331) * (n : ℝ) ^ (7 / 4 : ℝ) * L ^ 22 := by
      calc _ = (6 * 2 ^ 331) * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ)) * L ^ 22 := by ring
        _ = _ := by rw [hpower]
    rwa [he] at hh
  have hsmall : 96 * (n : ℝ) ^ (7 / 4 : ℝ) * queryLog n ≤
      96 * (n : ℝ) ^ (7 / 4 : ℝ) * L ^ 22 := by
    have hq22 : queryLog n ≤ L ^ 22 :=
      hq.trans (by simpa only [pow_one] using pow_le_pow_right₀ hL (by norm_num : 1 ≤ 22))
    gcongr
  have hc := balancedGlobalMinCut_cost_split hn hζ hζ1 read ho
  change (out.2 : ℝ) ≤ 96 * (n : ℝ) ^ (7 / 4 : ℝ) * queryLog n +
    (4 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log (2 / ζ) + 2) * Q at hc
  have hnonneg : 0 ≤ (n : ℝ) ^ (7 / 4 : ℝ) * L ^ 22 := by positivity
  nlinarith

/-- A single public program precedes the graph; it returns an exact minimum terminal
shore and value with the stated success probability and an unconditional query cap. -/
theorem directed_terminal_query_theorem {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
      out ∈ (RTree.run read (calibratedTerminalSolver n s t ζ)).support →
      (out.2 : ℝ) ≤ 2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * failureLog n ζ ^ 21) ∧
    (∀ G : DiGraph (Fin n), G.Simple →
      1 - ζ ≤ (calibratedTerminalSolver n s t ζ).successProb G.out (DirectedMincut.STGood s t G)) := by
  exact ⟨fun read _ ho => calibratedTerminalSolver_query_bound hn s t hζ hζ1 read ho,
    fun G hG => calibratedTerminalSolver_success hn s t hst hζ hζ1 G hG⟩

/-- The actual public balanced global-mincut program, with no solver or budget premise. -/
theorem directed_global_query_theorem {n : ℕ} (hn : 2 ≤ n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
      out ∈ (RTree.run read (balancedGlobalMinCut n hn ζ)).support →
      (out.2 : ℝ) ≤ 2 ^ 340 * (n : ℝ) ^ (7 / 4 : ℝ) * failureLog n ζ ^ 22) ∧
    (∀ G : DiGraph (Fin n), G.Simple →
      1 - ζ ≤ (balancedGlobalMinCut n hn ζ).successProb G.out (DirectedMincut.Opt G)) := by
  exact ⟨fun read _ ho => balancedGlobalMinCut_query_bound hn hζ hζ1 read ho,
    fun G hG => balancedGlobalMinCut_success hn hζ hζ1 G hG⟩

end
end CutQueryComplexity.ImplicitLP.PathFollowing

#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibrated_terminal_budget_le
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_query_bound
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.balancedGlobalMinCut_query_bound
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.directed_terminal_query_theorem
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.directed_global_query_theorem
