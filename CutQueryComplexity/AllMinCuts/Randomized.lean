import CutQueryComplexity.AllMinCuts.TwoStage
import CutQueryComplexity.MinCut.WeightedEndpoint

/-! # All minimum cuts with a randomized cut sparsifier

Karger's approach finds one minimum cut; its first stage, an explicit graph approximating every
cut, already serves all minimum cuts at once. `randomAllMinCuts s`:

1. runs the existing randomized cut sparsifier (`WeightedGraph.sparsify`, analysed by
   `sparsify_whp`) at accuracy `ε = 1/20`; it returns `none` on failure;
2. offline on the explicit sparsifier `H`: if `λ(H) = 0`, the zero cuts of `G` and `H` coincide,
   and the family of `H` (`familyOf H`) is output without a query; otherwise `λ(G) > 0`, the
   rescaled graph `H' = (20/19) H` satisfies `λ(H') ≥ λ(G)` and `c_{H'}(S) ≤ (21/19) λ(G)` on every
   minimum cut `S` (an `AllMinCutSkeleton`), and the deterministic `coverReport H'` returns the
   complete family (`reportStage_spec`).

`randomAllMinCuts_correct`: on every nonnegative weighted graph with `n ≥ 2`, the output is the
exact value and the complete family except with probability at most `(2n+2)^{-s}`, the
sparsifier's failure bound. `randomized_all_mincuts`: one public `RTree` per `n` and `s`, with at
most `C (s+8) n log(2n)²` queries on every run and every oracle.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllMinCuts

open WeightedGraph Search Search.Comp Hierarchy DetMinCut TwoRespecting Probability Finset
open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The sparsifier at accuracy `1/20` -/

/-- The randomized cut sparsifier of the library at accuracy `1/20` and failure exponent `s`. -/
noncomputable def sparsifierAll (V : Type) [Fintype V] (s : ℝ) :
    RTree (Finset V) ℝ (Option (WeightedGraph V))
      (capQ V (paramρ V s) (paramc V s (1 / 20))) :=
  sparsify (paramρ V s) (paramc V s (1 / 20)) (paramR V s)
    ⌈2 * paramc V s (1 / 20) * (Fintype.card V : ℝ) ^ 2⌉₊
    (capQ V (paramρ V s) (paramc V s (1 / 20)))

/-- The sparsifier succeeds except with probability `(2n+2)^{-s}`. -/
theorem sparsifierAll_whp (G : WeightedGraph V) (hn : 1 ≤ Fintype.card V) {s : ℝ}
    (hs : 0 ≤ s) :
    mass ((sparsifierAll V s).eval G.cut)
        (fun o => ¬∃ X, o = some X ∧
          IsSparseCutSparsifier (1 / 20) (edgeBound V (paramc V s (1 / 20))) G X) ≤
      ENNReal.ofReal (baseB V ^ (-s)) := by
  unfold sparsifierAll
  convert sparsify_whp G hn hs (ε := 1 / 20) (by norm_num) (by norm_num)

/-! ## The deterministic second stage -/

variable [LinearOrder V]

/-- Offline on an explicit approximation `H`: the zero family of `H` if `λ(H) = 0`, and otherwise
the cover reporter on `H` rescaled by `20/19`. -/
noncomputable def reportStage (H : WeightedGraph V) : Comp (Finset V) ℝ (Output V) :=
  if mincutValue H = 0 then Comp.pure (familyOf H)
  else coverReport (H.scale (20 / 19) (by norm_num))

/-- **The second stage.** If `H` approximates every cut of `G` within `1 ± 1/20`, the stage
returns the value and the complete family of minimum cuts of `G`, within `reportBound n`
queries. -/
theorem reportStage_spec (G H : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (hH : ∀ S, (1 - 1 / 20) * G.cut S ≤ H.cut S ∧ H.cut S ≤ (1 + 1 / 20) * G.cut S) :
    Correct G ((reportStage H).eval G.cut) ∧
      (reportStage H).cost G.cut ≤ reportBound (Fintype.card V) := by
  unfold reportStage
  split_ifs with h0
  · -- `λ(H) = 0`: the zero cuts of `G` and `H` coincide
    refine ⟨?_, by simp⟩
    have hzero : ∀ T, H.cut T = 0 ↔ G.cut T = 0 := by
      intro T
      have h1 := (hH T).1
      have h2 := (hH T).2
      have hG := G.cut_nonneg T
      have hHn := H.cut_nonneg T
      constructor
      · intro hT; rw [hT] at h1; linarith
      · intro hT; rw [hT] at h2; linarith
    obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card H hn
    have hlam : mincutValue G = 0 :=
      mincutValue_eq_zero_of_cut_eq_zero G hS.1 ((hzero S).mp ((isMinCut_of_sat hS).trans h0))
    rw [eval_pure]
    refine ⟨by simp [familyOf, h0, hlam], fun T => ?_⟩
    rw [isMinCut_iff, hlam, ← hzero T]
    classical
    simp [familyOf, mem_filter, mem_properShores, h0]
  · -- `λ(H) > 0`: then `λ(G) > 0` and the rescaled sparsifier is an all-minimum-cut skeleton
    have hpos : 0 < mincutValue G := by
      by_contra hle
      have hG0 : mincutValue G = 0 := le_antisymm (not_lt.mp hle) (mincutValue_nonneg G)
      obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G hn
      have hGS : G.cut S = 0 := (isMinCut_of_sat hS).trans hG0
      have hHS : H.cut S = 0 := by
        have h2 := (hH S).2
        rw [hGS] at h2
        linarith [H.cut_nonneg S]
      exact h0 (mincutValue_eq_zero_of_cut_eq_zero H hS.1 hHS)
    have hskel : AllMinCutSkeleton G (H.scale (20 / 19) (by norm_num)) := by
      refine ⟨le_mincutValue _ hn fun T hT => ?_, fun S hS => ?_⟩
      · rw [cut_scale]
        have h1 := (hH T).1
        have h2 := mincutValue_le G hT
        linarith
      · rw [cut_scale, ← isMinCut_of_sat hS]
        have h1 := (hH S).2
        have h2 := G.cut_nonneg S
        linarith
    exact coverReport_spec G _ hn hpos hskel

/-! ## The randomized program -/

/-- **All minimum cuts, randomized.** The sparsifier, then the deterministic second stage
compiled at the public cap `reportBound n`. -/
noncomputable def randomAllMinCuts (s : ℝ) :
    RTree (Finset V) ℝ (Option (Output V))
      (capQ V (paramρ V s) (paramc V s (1 / 20)) + reportBound (Fintype.card V)) :=
  (sparsifierAll V s).bind fun oH => match oH with
    | none => RTree.pure (PMF.pure none)
    | some H => RTree.ofDeterministic ((reportStage H).toDTree (reportBound (Fintype.card V)))

/-- **Correctness.** On every nonnegative weighted graph with `n ≥ 2` vertices, the output is the
exact minimum-cut value with the complete family of minimum cuts, except with probability at most
`(2n+2)^{-s}`. -/
theorem randomAllMinCuts_correct (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) {s : ℝ}
    (hs : 0 ≤ s) :
    mass ((randomAllMinCuts s).eval G.cut) (fun o => ¬∃ out, o = some out ∧ Correct G out) ≤
      ENNReal.ofReal (baseB V ^ (-s)) := by
  rw [randomAllMinCuts, RTree.eval_bind]
  refine le_trans (mass_bind_le_add _ _ _ _ (ε := 0) (sparsifierAll_whp G (by omega) hs)
    fun oH hoH => ?_) (by simp)
  push Not at hoH
  obtain ⟨H, rfl, hsp⟩ := hoH
  obtain ⟨hcorr, hcost⟩ := reportStage_spec G H hn hsp.1.2
  simp only [RTree.eval_ofDeterministic, toDTree_eval G.cut _ hcost, mass_pure]
  simp [hcorr]

/-! ## The query cap -/

omit [DecidableEq V] [LinearOrder V] in
theorem paramc_twentieth (s : ℝ) : paramc V s (1 / 20) = 100 * paramc V s (1 / 2) := by
  unfold paramc
  ring

omit [DecidableEq V] [LinearOrder V] in
theorem outBound_twentieth_le (s : ℝ) :
    outBound V (paramc V s (1 / 20)) ≤ 100 * outBound V (paramc V s (1 / 2)) := by
  rw [paramc_twentieth]
  unfold outBound
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ residualDrawCost (searchDepth V) (searchDepth V) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hn hd]

omit [DecidableEq V] [LinearOrder V] in
theorem capQ_twentieth_le (s : ℝ) :
    capQ V (paramρ V s) (paramc V s (1 / 20)) ≤
      100 * capQ V (paramρ V s) (paramc V s (1 / 2)) := by
  have hc : ⌈outBound V (paramc V s (1 / 20))⌉₊ ≤
      100 * ⌈outBound V (paramc V s (1 / 2))⌉₊ := by
    apply Nat.ceil_le.mpr
    calc
      _ ≤ 100 * outBound V (paramc V s (1 / 2)) := outBound_twentieth_le s
      _ ≤ 100 * (⌈outBound V (paramc V s (1 / 2))⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)
      _ = _ := by push_cast; rfl
  unfold capQ
  omega

/-- The cover reporter costs at most `4846 n budgetLog(n)²`. -/
theorem reportBound_le_budgetLog (n : ℕ) (hn : 1 ≤ n) :
    (reportBound n : ℝ) ≤ 4846 * n * (AllPairs.budgetLog n : ℝ) ^ 2 := by
  have hd : (Nat.clog 2 n + 1 : ℕ) ≤ AllPairs.budgetLog n := AllPairs.depth_add_one_le_budgetLog n
  have hL1 : 1 ≤ AllPairs.budgetLog n := AllPairs.budgetLog_one_le n
  have hcov : coverSize n ≤ 15 * AllPairs.budgetLog n := by
    unfold coverSize; omega
  have hC : Nat.clog 2 n + 1 ≤ AllPairs.budgetLog n := hd
  set L := AllPairs.budgetLog n
  set C := Nat.clog 2 n
  have h1 : coverSize n * (72 * n * (C + 1) + 1) ≤ 15 * L * (73 * n * L) := by
    apply Nat.mul_le_mul hcov
    have : 72 * n * (C + 1) ≤ 72 * n * L := Nat.mul_le_mul_left _ hC
    have : 1 ≤ n * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have h2 : coverSize n * (250 * n * (C + 1)) ≤ 15 * L * (250 * n * L) :=
    Nat.mul_le_mul hcov (Nat.mul_le_mul_left _ hC)
  have h3 : 1 ≤ n * L ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hnat : reportBound n ≤ 4846 * n * L ^ 2 := by
    unfold reportBound skelBound
    nlinarith
  exact_mod_cast hnat

/-- The public cap of the randomized reporter. -/
noncomputable def randomBudget (V : Type) [Fintype V] (s : ℝ) : ℕ :=
  capQ V (paramρ V s) (paramc V s (1 / 20)) + reportBound (Fintype.card V)

omit [DecidableEq V] [LinearOrder V] in
theorem randomBudget_le (hn : 2 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    (randomBudget V s : ℝ) ≤
      200000000 * (s + 8) * Fintype.card V * Real.log (2 * (Fintype.card V : ℝ)) ^ 2 := by
  set n := Fintype.card V
  set L : ℝ := ((AllPairs.budgetLog n : ℕ) : ℝ)
  have hL1 : (1 : ℝ) ≤ L := by
    show (1 : ℝ) ≤ ((AllPairs.budgetLog n : ℕ) : ℝ)
    exact_mod_cast AllPairs.budgetLog_one_le n
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcap : (capQ V (paramρ V s) (paramc V s (1 / 20)) : ℝ) ≤
      4000000 * (s + 8) * n * L ^ 2 := by
    calc
      _ ≤ 100 * (capQ V (paramρ V s) (paramc V s (1 / 2)) : ℝ) := by
        exact_mod_cast capQ_twentieth_le (V := V) s
      _ ≤ 100 * (40000 * (s + 8) * n * L ^ 2) :=
        mul_le_mul_of_nonneg_left (AllPairs.capQ_public_le V (by omega) hs) (by norm_num)
      _ = _ := by ring
  have hrep : (reportBound n : ℝ) ≤ 4846 * n * L ^ 2 := reportBound_le_budgetLog n (by omega)
  have hlog : L ≤ 6 * Real.log (2 * (n : ℝ)) :=
    WeightedMinCut.Endpoint.budgetLog_realLog n hn
  have hL0 : 0 ≤ L := by linarith
  have hL2 : L ^ 2 ≤ 36 * Real.log (2 * (n : ℝ)) ^ 2 := by nlinarith
  have hs8 : (8 : ℝ) ≤ s + 8 := by linarith
  have hnL : 0 ≤ (n : ℝ) * L ^ 2 := by positivity
  have hsum : (randomBudget V s : ℝ) ≤ 4010000 * (s + 8) * n * L ^ 2 := by
    unfold randomBudget
    push_cast
    nlinarith
  calc (randomBudget V s : ℝ) ≤ 4010000 * (s + 8) * n * L ^ 2 := hsum
    _ ≤ 4010000 * (s + 8) * n * (36 * Real.log (2 * (n : ℝ)) ^ 2) := by gcongr
    _ ≤ 200000000 * (s + 8) * n * Real.log (2 * (n : ℝ)) ^ 2 := by
        have : 0 ≤ (s + 8) * n * Real.log (2 * (n : ℝ)) ^ 2 := by positivity
        nlinarith

/-! ## The endpoint -/

/-- **All minimum cuts in `O(n log² n)` randomized cut queries.** For every `n ≥ 2` and `s ≥ 0`,
one public randomized query tree with at most `C (s+8) n log(2n)²` queries on every run and every
oracle returns, on every nonnegative weighted graph on `Fin n`, the minimum-cut value and the
complete family of minimum cuts, except with probability at most `(2n+2)^{-s}`. -/
theorem randomized_all_mincuts :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ s : ℝ, 0 ≤ s →
      ∃ q : ℕ, (q : ℝ) ≤ C * (s + 8) * n * Real.log (2 * (n : ℝ)) ^ 2 ∧
        ∃ T : RTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
          (∀ read : Finset (Fin n) → ℝ, ∀ r ∈ (RTree.run read T).support, r.2 ≤ q) ∧
          ∀ G : WeightedGraph (Fin n),
            mass (T.eval G.cut) (fun o => ¬∃ out, o = some out ∧ Correct G out) ≤
              ENNReal.ofReal ((2 * (n : ℝ) + 2) ^ (-s)) := by
  refine ⟨200000000, by norm_num, fun n hn s hs => ?_⟩
  have hn' : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  refine ⟨randomBudget (Fin n) s, by simpa using randomBudget_le hn' hs,
    randomAllMinCuts (V := Fin n) s, fun read r hr => RTree.cost_le _ read hr, fun G => ?_⟩
  have h := randomAllMinCuts_correct (V := Fin n) G hn' hs
  simp only [baseB, Fintype.card_fin] at h
  exact h

end CutQueryComplexity.AllMinCuts
