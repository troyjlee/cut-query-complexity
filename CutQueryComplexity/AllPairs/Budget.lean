import CutQueryComplexity.Sparsification.WeightedParams
import CutQueryComplexity.AllPairs.Recovery
import CutQueryComplexity.AllPairs.Padding
import CutQueryComplexity.AllPairs.Main
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Arithmetic for the actual all-pairs query budget

The estimates here expand the existing weighted sparsifier cap and the explicit
postprocessing cost. They charge both natural ceilings, every recovery query,
and the threefold vertex padding. No algorithmic or asymptotic bound is assumed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairs

open WeightedGraph
noncomputable section

/-- A single integer logarithm controlling all primitive budgets. -/
def budgetLog (n : ℕ) : ℕ := Nat.clog 2 (2 * n + 2) + 1

theorem budgetLog_one_le (n : ℕ) : 1 ≤ budgetLog n := by
  unfold budgetLog
  omega

theorem depth_add_one_le_budgetLog (n : ℕ) :
    Nat.clog 2 n + 1 ≤ budgetLog n := by
  exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1

private theorem real_log_nat_le_clog (n : ℕ) (hn : 0 < n) :
    Real.log (n : ℝ) ≤ Nat.clog 2 n := by
  have hp : (n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 n := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) n
  have hl := Real.log_le_log (Nat.cast_pos.mpr hn) hp
  rw [Real.log_pow] at hl
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  exact hl.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left htwo
      (Nat.cast_nonneg (Nat.clog 2 n) : (0 : ℝ) ≤ Nat.clog 2 n))

theorem log_baseB_le_budgetLog (V : Type) [Fintype V] :
    Real.log (baseB V) ≤ budgetLog (Fintype.card V) := by
  have h := real_log_nat_le_clog (2 * Fintype.card V + 2) (by omega)
  have hi : (Nat.clog 2 (2 * Fintype.card V + 2) : ℝ) ≤
      budgetLog (Fintype.card V) := by
    exact_mod_cast (show Nat.clog 2 (2 * Fintype.card V + 2) ≤
      budgetLog (Fintype.card V) by unfold budgetLog; omega)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, baseB] using h.trans hi

theorem paramρ_budget_bounds (V : Type) [Fintype V] {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ paramρ V s ∧
      paramρ V s ≤ 128 * (s + 8) * budgetLog (Fintype.card V) := by
  have hlog := (log_baseB_pos V).le
  constructor
  · unfold paramρ
    positivity
  · exact mul_le_mul_of_nonneg_left (log_baseB_le_budgetLog V) (by positivity)

private theorem paramc_half_eq (V : Type) [Fintype V] (s : ℝ) :
    paramc V s (1 / 2) = 32 * (2 * Real.log (2 * Fintype.card V) +
      Real.log 4 + (s + 1) * Real.log (baseB V)) := by
  have hB : 0 < baseB V := by linarith [baseB_ge V]
  have hδ : 0 < paramδ V s := Real.rpow_pos_of_pos hB _
  unfold paramc
  rw [Real.log_div (by norm_num) (ne_of_gt hδ), paramδ, Real.log_rpow hB]
  ring

theorem paramc_half_budget_bounds (V : Type) [Fintype V]
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ paramc V s (1 / 2) ∧
      paramc V s (1 / 2) ≤ 32 * (s + 8) * budgetLog (Fintype.card V) := by
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hB2 := baseB_ge V
  have hB0 : 0 < baseB V := by linarith
  have hlog0 := (log_baseB_pos V).le
  have hlogN0 : 0 ≤ Real.log (2 * Fintype.card V) :=
    Real.log_nonneg (by linarith)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hN : Real.log (2 * Fintype.card V) ≤ Real.log (baseB V) :=
    Real.log_le_log (by linarith) (by simp only [baseB]; linarith)
  have h4 : Real.log 4 ≤ 2 * Real.log (baseB V) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (show 4 ≤ baseB V ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  rw [paramc_half_eq]
  constructor
  · positivity
  · calc
      _ ≤ 32 * (s + 8) * Real.log (baseB V) := by nlinarith only [hN, h4, hlog0]
      _ ≤ _ := mul_le_mul_of_nonneg_left (log_baseB_le_budgetLog V) (by positivity)

theorem log_poly_le_budgetLog (n : ℕ) :
    Nat.log 2 (2 * n ^ 4) ≤ 5 * budgetLog n := by
  have hL := budgetLog_one_le n
  have hd : Nat.clog 2 n ≤ budgetLog n := by
    have := depth_add_one_le_budgetLog n
    omega
  have hn : n ≤ 2 ^ budgetLog n := (Nat.le_pow_clog (by norm_num) n).trans
    (Nat.pow_le_pow_right (by norm_num) hd)
  have htwo : 2 ≤ 2 ^ budgetLog n := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hL
  apply (Nat.log_le_clog 2 _).trans
  apply Nat.clog_le_of_le_pow
  calc
    2 * n ^ 4 ≤ (2 ^ budgetLog n) * (2 ^ budgetLog n) ^ 4 :=
      Nat.mul_le_mul htwo (Nat.pow_le_pow_left hn 4)
    _ = 2 ^ (5 * budgetLog n) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

theorem residualDrawCost_le_budgetLog (V : Type) [Fintype V] :
    residualDrawCost (searchDepth V) (searchDepth V) ≤ 27 * budgetLog (Fintype.card V) := by
  have hd := depth_add_one_le_budgetLog (Fintype.card V)
  have hL := budgetLog_one_le (Fintype.card V)
  dsimp only [residualDrawCost, searchDepth]
  omega

theorem approxKruskalBudget_le_budgetLog (V : Type) [Fintype V] :
    approxKruskalBudget V ≤ 17 * Fintype.card V * budgetLog (Fintype.card V) := by
  classical
  have hd := depth_add_one_le_budgetLog (Fintype.card V)
  have hL := budgetLog_one_le (Fintype.card V)
  calc
    _ ≤ Fintype.card V * (6 * searchDepth V + 11) := approxKruskalBudget_le
    _ ≤ Fintype.card V * (17 * budgetLog (Fintype.card V)) := by
      apply Nat.mul_le_mul_left
      dsimp only [searchDepth]
      omega
    _ = _ := by ring

private theorem budget_scale_lower (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    8 * ((n : ℝ) * budgetLog n) ≤ (s + 8) * n * (budgetLog n : ℝ) ^ 2 := by
  have hL : (1 : ℝ) ≤ budgetLog n := by exact_mod_cast budgetLog_one_le n
  have hLL : (budgetLog n : ℝ) ≤ (budgetLog n : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ (s + 8) * ((n : ℝ) * budgetLog n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (s + 8) * n * budgetLog n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hLL (by positivity)

theorem estBound_paramρ_le (V : Type) [Fintype V] {s : ℝ} (hs : 0 ≤ s) :
    estBound V (paramρ V s) ≤
      27650 * (s + 8) * Fintype.card V * (budgetLog (Fintype.card V) : ℝ) ^ 2 := by
  let n := Fintype.card V
  let L : ℝ := budgetLog n
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast budgetLog_one_le n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hq : (Nat.log 2 (2 * Fintype.card V ^ 4) : ℝ) ≤ 5 * L := by
    dsimp only [L, n]
    exact_mod_cast log_poly_le_budgetLog (Fintype.card V)
  have hD : (residualDrawCost (searchDepth V) (searchDepth V) : ℝ) ≤ 27 * L := by
    dsimp only [L, n]
    exact_mod_cast residualDrawCost_le_budgetLog V
  obtain ⟨hρ0, hρ⟩ := paramρ_budget_bounds V hs
  have hfirst : 2 * ((Fintype.card V - 1 : ℕ) : ℝ) *
      Nat.log 2 (2 * Fintype.card V ^ 4) ≤ 10 * n * L := by
    calc
      _ ≤ 2 * (n : ℝ) * (5 * L) := by gcongr
      _ = _ := by ring
  have hmain : (residualDrawCost (searchDepth V) (searchDepth V) : ℝ) *
      (8 * paramρ V s * (Fintype.card V - 1 : ℕ)) ≤ 27648 * (s + 8) * n * L ^ 2 := by
    calc
      _ ≤ (27 * L) * (8 * (128 * (s + 8) * L) * n) := by gcongr
      _ = _ := by ring
  have hscale : 8 * ((n : ℝ) * L) ≤ (s + 8) * n * L ^ 2 := budget_scale_lower n hs
  have hnL : (n : ℝ) ≤ n * L := by nlinarith only [mul_nonneg hn (sub_nonneg.mpr hL)]
  change _ ≤ 27650 * (s + 8) * n * L ^ 2
  unfold estBound
  change _ + _ + (n : ℝ) ≤ _
  nlinarith only [hfirst, hmain, hscale, hnL]

theorem outBound_paramc_le (V : Type) [Fintype V]
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    outBound V (paramc V s (1 / 2)) ≤
      3460 * (s + 8) * Fintype.card V * (budgetLog (Fintype.card V) : ℝ) ^ 2 := by
  let n := Fintype.card V
  let L : ℝ := budgetLog n
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast budgetLog_one_le n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hD : (residualDrawCost (searchDepth V) (searchDepth V) : ℝ) ≤ 27 * L := by
    dsimp only [L, n]
    exact_mod_cast residualDrawCost_le_budgetLog V
  obtain ⟨hc0, hc⟩ := paramc_half_budget_bounds V hn hs
  have hmain : (residualDrawCost (searchDepth V) (searchDepth V) : ℝ) *
      (4 * paramc V s (1 / 2) * (Fintype.card V - 1 : ℕ) + Fintype.card V) ≤
        3456 * (s + 8) * n * L ^ 2 + 27 * n * L := by
    calc
      _ ≤ (27 * L) * (4 * (32 * (s + 8) * L) * n + n) := by gcongr
      _ = _ := by ring
  have hscale : 8 * ((n : ℝ) * L) ≤ (s + 8) * n * L ^ 2 := budget_scale_lower n hs
  have hnL : (n : ℝ) ≤ n * L := by nlinarith only [mul_nonneg hn0 (sub_nonneg.mpr hL)]
  change _ ≤ 3460 * (s + 8) * n * L ^ 2
  unfold outBound
  change (n : ℝ) + _ ≤ _
  nlinarith only [hmain, hscale, hnL]

/-- The actual capped weighted sparsifier, including both natural ceilings. -/
theorem capQ_public_le (V : Type) [Fintype V]
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    (capQ V (paramρ V s) (paramc V s (1 / 2)) : ℝ) ≤
      40000 * (s + 8) * Fintype.card V * (budgetLog (Fintype.card V) : ℝ) ^ 2 := by
  let n := Fintype.card V
  let L : ℝ := budgetLog n
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast budgetLog_one_le n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hK : (approxKruskalBudget V : ℝ) ≤ 17 * n * L := by
    dsimp only [L, n]
    exact_mod_cast approxKruskalBudget_le_budgetLog V
  have hρ0 := (paramρ_budget_bounds V hs).1
  have hc0 := (paramc_half_budget_bounds V hn hs).1
  have he0 : 0 ≤ estBound V (paramρ V s) := by unfold estBound; positivity
  have ho0 : 0 ≤ outBound V (paramc V s (1 / 2)) := by unfold outBound; positivity
  have heceil := (Nat.ceil_lt_add_one he0).le
  have hoceil := (Nat.ceil_lt_add_one ho0).le
  have he := estBound_paramρ_le V hs
  have ho := outBound_paramc_le V hn hs
  have hscale : 8 * ((n : ℝ) * L) ≤ (s + 8) * n * L ^ 2 := budget_scale_lower n hs
  have hnL : (n : ℝ) ≤ n * L := by nlinarith only [mul_nonneg hn0 (sub_nonneg.mpr hL)]
  have hB0 : 0 ≤ (s + 8) * n * L ^ 2 := by positivity
  change _ ≤ 40000 * (s + 8) * n * L ^ 2
  simp only [capQ, Nat.cast_add]
  change (approxKruskalBudget V : ℝ) + (n : ℝ) + _ + _ ≤ _
  change _ ≤ 27650 * (s + 8) * n * L ^ 2 at he
  change _ ≤ 3460 * (s + 8) * n * L ^ 2 at ho
  nlinarith only [hK, heceil, hoceil, he, ho, hscale, hnL, hnR, hB0]

/-- Explicit shaving, degree measurement, and global capped recovery cost. -/
theorem post_cost_le (n : ℕ) :
    5 * n + (n + 2 * ((98 * Nat.clog 2 n + 60) * n * (Nat.sqrt (2 * n) + 1))) *
      ((Nat.clog 2 n + 1) * 3) ≤
        2000 * n * (Nat.sqrt (2 * n) + 1) * (budgetLog n) ^ 2 := by
  let L := budgetLog n
  let t := Nat.sqrt (2 * n) + 1
  have hL : 1 ≤ L := budgetLog_one_le n
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hd : Nat.clog 2 n + 1 ≤ L := depth_add_one_le_budgetLog n
  have hcoef : 98 * Nat.clog 2 n + 60 ≤ 158 * L := by omega
  have hM : (98 * Nat.clog 2 n + 60) * n * t ≤ 158 * n * t * L := by
    calc
      _ ≤ (158 * L) * n * t := by gcongr
      _ = _ := by ring
  have hnL : n ≤ n * t * L := by
    calc n = n * 1 * 1 := by ring
         _ ≤ n * t * L := by gcongr
  have hnL2 : n ≤ n * t * L ^ 2 := by
    calc n = n * 1 * 1 := by ring
         _ ≤ n * t * L ^ 2 := by gcongr; exact one_le_pow₀ hL
  have hinside : n + 2 * ((98 * Nat.clog 2 n + 60) * n * t) ≤ 317 * n * t * L := by
    nlinarith only [hM, hnL]
  have hproduct := Nat.mul_le_mul hinside (Nat.mul_le_mul_right 3 hd)
  change 5 * n + (n + 2 * ((98 * Nat.clog 2 n + 60) * n * t)) *
    ((Nat.clog 2 n + 1) * 3) ≤ 2000 * n * t * L ^ 2
  calc
    _ ≤ 956 * n * t * L ^ 2 := by nlinarith only [hproduct, hnL2]
    _ ≤ _ := by gcongr; norm_num

/-- The existing sparsifier cap plus the exact explicit postprocessing expression. -/
theorem combined_cost_le (V : Type) [Fintype V]
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    (capQ V (paramρ V s) (paramc V s (1 / 2)) : ℝ) +
      ((5 * Fintype.card V +
        (Fintype.card V + 2 * ((98 * Nat.clog 2 (Fintype.card V) + 60) *
          Fintype.card V * (Nat.sqrt (2 * Fintype.card V) + 1))) *
          ((Nat.clog 2 (Fintype.card V) + 1) * 3) : ℕ) : ℝ) ≤
      42000 * (s + 8) * Fintype.card V * (Nat.sqrt (2 * Fintype.card V) + 1) *
        (budgetLog (Fintype.card V) : ℝ) ^ 2 := by
  let n := Fintype.card V
  let L : ℝ := budgetLog n
  let t : ℝ := Nat.sqrt (2 * n) + 1
  have ht : 1 ≤ t := by
    have h0 : (0 : ℝ) ≤ Nat.sqrt (2 * n) := Nat.cast_nonneg _
    dsimp only [t]
    linarith
  have hs1 : 1 ≤ s + 8 := by linarith
  have hcap := capQ_public_le V hn hs
  have hpost : ((5 * n + (n + 2 * ((98 * Nat.clog 2 n + 60) * n *
      (Nat.sqrt (2 * n) + 1))) * ((Nat.clog 2 n + 1) * 3) : ℕ) : ℝ) ≤
      2000 * n * t * L ^ 2 := by
    dsimp only [t, L]
    exact_mod_cast post_cost_le n
  have hcap' : (capQ V (paramρ V s) (paramc V s (1 / 2)) : ℝ) ≤
      40000 * (s + 8) * n * t * L ^ 2 := by
    calc
      _ ≤ 40000 * (s + 8) * n * L ^ 2 := hcap
      _ = 40000 * (s + 8) * n * 1 * L ^ 2 := by ring
      _ ≤ _ := by gcongr
  have hpost' : 2000 * (n : ℝ) * t * L ^ 2 ≤ 2000 * (s + 8) * n * t * L ^ 2 := by
    calc
      _ = 2000 * 1 * (n : ℝ) * t * L ^ 2 := by ring
      _ ≤ _ := by gcongr
  change _ ≤ 42000 * (s + 8) * n * t * L ^ 2
  nlinarith only [hcap', hpost, hpost']

theorem budgetLog_padded_le (n : ℕ) (hn : 1 ≤ n) :
    budgetLog (3 * n) ≤ Nat.clog 2 n + 4 := by
  have hp : 2 * (3 * n) + 2 ≤ 2 ^ (Nat.clog 2 n + 3) := by
    calc
      _ ≤ 8 * n := by omega
      _ ≤ 8 * (2 ^ Nat.clog 2 n) := Nat.mul_le_mul_left 8 (Nat.le_pow_clog (by norm_num) n)
      _ = _ := by rw [pow_add]; ring
  have hc := Nat.clog_le_of_le_pow hp
  unfold budgetLog
  omega

theorem padded_threshold_le (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.sqrt (2 * (3 * n)) + 1 : ℕ) : ℝ) ≤ 4 * Real.sqrt (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hnR
  have hr2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hm : (Nat.sqrt (2 * (3 * n)) : ℝ) ^ 2 ≤ 6 * n := by
    have h : (Nat.sqrt (2 * (3 * n)) : ℝ) ^ 2 ≤ ((2 * (3 * n) : ℕ) : ℝ) := by
      exact_mod_cast Nat.sqrt_le' (2 * (3 * n))
    push_cast at h
    nlinarith only [h]
  have hm3 : (Nat.sqrt (2 * (3 * n)) : ℝ) ≤ 3 * Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
    nlinarith only [hm, hr2, hnR]
  push_cast
  linarith

/-- The complete explicit cost expression on the padded vertex type. -/
theorem padded_combined_cost_le (V : Type) [Fintype V]
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    (capQ (Padded V) (paramρ (Padded V) s) (paramc (Padded V) s (1 / 2)) : ℝ) +
      ((5 * Fintype.card (Padded V) +
        (Fintype.card (Padded V) + 2 * ((98 * Nat.clog 2 (Fintype.card (Padded V)) + 60) *
          Fintype.card (Padded V) * (Nat.sqrt (2 * Fintype.card (Padded V)) + 1))) *
          ((Nat.clog 2 (Fintype.card (Padded V)) + 1) * 3) : ℕ) : ℝ) ≤
      600000 * (s + 8) * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) *
        ((Nat.clog 2 (Fintype.card V) : ℝ) + 4) ^ 2 := by
  have hnP : 1 ≤ Fintype.card (Padded V) := by rw [padded_card]; omega
  have h := combined_cost_le (Padded V) hnP hs
  have hL : (budgetLog (3 * Fintype.card V) : ℝ) ≤
      (Nat.clog 2 (Fintype.card V) : ℝ) + 4 := by
    exact_mod_cast budgetLog_padded_le (Fintype.card V) hn
  have ht : (Nat.sqrt (2 * (3 * Fintype.card V)) : ℝ) + 1 ≤
      4 * Real.sqrt (Fintype.card V : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using padded_threshold_le (Fintype.card V) hn
  calc
    _ ≤ 42000 * (s + 8) * (3 * (Fintype.card V : ℝ)) *
        ((Nat.sqrt (2 * (3 * Fintype.card V)) : ℝ) + 1) *
        (budgetLog (3 * Fintype.card V) : ℝ) ^ 2 := by
      simpa only [padded_card, Nat.cast_mul, Nat.cast_ofNat] using h
    _ ≤ 42000 * (s + 8) * (3 * (Fintype.card V : ℝ)) *
        (4 * Real.sqrt (Fintype.card V : ℝ)) *
        ((Nat.clog 2 (Fintype.card V) : ℝ) + 4) ^ 2 := by gcongr
    _ = 504000 * (s + 8) * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) *
        ((Nat.clog 2 (Fintype.card V) : ℝ) + 4) ^ 2 := by ring
    _ ≤ _ := by gcongr; norm_num

/-- The query budget of the actual public program, including triangle padding. -/
theorem allPairsBudget_le (V : Type) [Fintype V]
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    (allPairsBudget V s : ℝ) ≤
      600000 * (s + 8) * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) *
        ((Nat.clog 2 (Fintype.card V) : ℝ) + 4) ^ 2 := by
  have hpost : postBudget (Padded V) =
      5 * Fintype.card (Padded V) +
        (Fintype.card (Padded V) + 2 * ((98 * Nat.clog 2 (Fintype.card (Padded V)) + 60) *
          Fintype.card (Padded V) * (Nat.sqrt (2 * Fintype.card (Padded V)) + 1))) *
          ((Nat.clog 2 (Fintype.card (Padded V)) + 1) * 3) := by
    dsimp only [postBudget, starRecoveryBudget, recoveryBudget, publicEdgeCap,
      publicThreshold, searchDepth]
    omega
  change ((capQ (Padded V) (paramρ (Padded V) s) (paramc (Padded V) s (1 / 2)) +
    postBudget (Padded V) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_add, hpost]
  exact padded_combined_cost_le V hn hs

/-- The explicit cap holds for every supported run against every cut oracle. -/
theorem allPairsProgram_cost_bound {V : Type} [Fintype V] [DecidableEq V]
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) (oracle : Finset V → ℝ)
    {out : Option (Answers V) × ℕ}
    (ho : out ∈ (RTree.run oracle (allPairsProgram s)).support) :
    (out.2 : ℝ) ≤
      600000 * (s + 8) * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) *
        ((Nat.clog 2 (Fintype.card V) : ℝ) + 4) ^ 2 := by
  have hcost : (out.2 : ℝ) ≤ (allPairsBudget V s : ℝ) :=
    Nat.cast_le.mpr (allPairsProgram_cost s oracle ho)
  exact hcost.trans (allPairsBudget_le V hn hs)

/-- One public program has an unconditional run-cost cap and simultaneously
returns optimal shores and their exact values for all distinct terminal pairs,
except with the stated probability. -/
theorem allPairsProgram_spec (V : Type) [Fintype V] [DecidableEq V]
    (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    (∀ (oracle : Finset V → ℝ) (out : Option (Answers V) × ℕ),
      out ∈ (RTree.run oracle (allPairsProgram s)).support →
      (out.2 : ℝ) ≤
        600000 * (s + 8) * Fintype.card V * Real.sqrt (Fintype.card V : ℝ) *
          ((Nat.clog 2 (Fintype.card V) : ℝ) + 4) ^ 2) ∧
    (∀ G : WeightedGraph V, AllPairsAudit.Unweighted G →
      Probability.mass ((allPairsProgram s).eval G.cut) (fun o => ¬Successful G o) ≤
        ENNReal.ofReal ((6 * (Fintype.card V : ℝ) + 2) ^ (-s))) := by
  constructor
  · intro oracle out ho
    exact allPairsProgram_cost_bound hn hs oracle ho
  · intro G hG
    exact allPairsProgram_failure_explicit G hG hn hs

#print axioms paramc_half_budget_bounds
#print axioms capQ_public_le
#print axioms post_cost_le
#print axioms combined_cost_le
#print axioms budgetLog_padded_le
#print axioms padded_threshold_le
#print axioms padded_combined_cost_le
#print axioms allPairsBudget_le
#print axioms allPairsProgram_cost_bound
#print axioms allPairsProgram_spec

end
end CutQueryComplexity.AllPairs
