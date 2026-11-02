import CutQueryComplexity.TreeCutSparsifier.UnconditionalLL
import CutQueryComplexity.TreeCutSparsifier.ConversionLogLog
import CutQueryComplexity.DetMinCut.MainLog7

/-! # The two-stage composition (log-log plan, M6)

The manuscript's derivation of the deterministic bound from Theorem 5 and the conversion
theorem, as a second route to `O(n^{3/2} L(n)³ L(L(n))²)` beside the fused main loop of
`DetMinCut.UnconditionalLogLog`. On a graph `G` with `n ≥ 2` vertices, `twoStage α x₀`:

1. runs the positive-support forest routine (`SupportForest.program`); a disconnected
   support yields a proper shore of cut value zero, which is a minimum cut;
2. otherwise `0 < λ(G)`, and `learnLL α` (Theorem 5) returns a safe partition `r` and an
   explicit `α`-tree cut sparsifier of the quotient `G/r` (`Correct G α`);
3. `convertStage α out` runs the supplied-hierarchy conversion program on the normalized
   topology of that tree (`suppliedHierarchyProgLL`), which returns a weak skeleton of `G/r`
   since `λ(G/r) = λ(G) > 0` (`safePartition_mincutValue`) and the tree approximates some
   minimum cut of `G/r` within `α` (`approximates_promise`); then the tree cover and the
   two-respecting search (`skeletonMinCut`) return a minimum cut `T` of `G/r`. Every quotient
   query is one original query on the union of the classes in it (`mapQ (pull (proj r))`);
4. `pull (proj r) T` is a minimum cut of `G` (`isMinCut_pull_of_safePartition`): its value is
   `λ(G/r) = λ(G)`.

`twoStageAuto` runs `twoStage` at `α = ⌊√n⌋` when that is admissible, and otherwise (only for
`⌊√n⌋ < 2 discoveryConstantLL L(n)² L(L(n))²`, a finite range of `n`) learns the whole graph
and minimizes offline (`offlineMinCut`, `n + n²` queries). Queries: `forestBudget n ≤ 7 n L(n)`,
learning `budgetLL n ⌊√n⌋ = O((n² / √n) L³ K²)`, conversion `O(n √n L³ K²)`, and the skeleton
search `skelBound n = O(n L²)`; in all `twoStageBudget n ≤ (twoStageConstant + 1) n (⌊√n⌋ + 1)
L(n)³ L(L(n))²`.

`deterministic_mincut_two_stage` has the statement of `deterministic_mincut_log3loglog2` (up to
the constant) and `deterministic_mincut_two_stage_real_log` that of
`deterministic_mincut_log3loglog2_real_log`; neither existing theorem changes.
-/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open WeightedGraph Search Search.Comp Hierarchy DetMinCut TwoRespecting UndirectedClosure
  SupportForest Finset
open Hierarchy.RackeShah (KK)

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Lifting a minimum cut of a safe quotient -/

/-- A minimum cut of a safe quotient pulls back to a minimum cut of the input: its value is
`λ(G/r) = λ(G)`. -/
theorem isMinCut_pull_of_safePartition (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    {r : V → V} (hs : SafePartition G r) {T : Finset (Cls r)}
    (hT : IsMinCut (quot G r) T) : IsMinCut G (pull (proj r) T) := by
  refine ⟨properShore_pull _ (proj_surjective _) hT.1, fun S hS => ?_⟩
  calc G.cut (pull (proj r) T) = (quot G r).cut T := (cut_contract _ _ _).symm
    _ = mincutValue (quot G r) := isMinCut_of_sat hT
    _ = mincutValue G := safePartition_mincutValue G hn hs
    _ ≤ G.cut S := mincutValue_le G hS

/-! ## The conversion stage on the learned quotient -/

/-- Convert the learned tree of the quotient to a weak skeleton of the quotient, search it, and
pull the resulting shore back; each quotient query is one original query. The hierarchy
topology is the normalized topology of the learned tree, selected from the learned data alone. -/
noncomputable def convertStage [Nonempty V] (α : ℝ) (out : Output V) :
    Comp (Finset V) ℝ (Finset V) :=
  have : Nonempty (Cls out.r) := ⟨proj out.r (Classical.arbitrary V)⟩
  (mapQ (pull (proj out.r))
    ((suppliedHierarchyProgLL (normalTopology out.data.tree) α).bind fun H =>
      @skeletonMinCut _ _ _ (clsOrder out.r) H)).map (pull (proj out.r))

/-- The quotient cap of the conversion stage, on the quotient size `N`. -/
noncomputable def convertCap (N : ℕ) (α : ℝ) : ℝ :=
  hierarchyConstantLL * N * α * ((logL N : ℝ) ^ 3 * (logL (logL N) : ℝ) ^ 2) + skelBound N

theorem convertCap_nonneg {N : ℕ} {α : ℝ} (hα : 0 ≤ α) : 0 ≤ convertCap N α := by
  have := hierarchyConstantLL_pos
  unfold convertCap; positivity

theorem convertCap_mono {N n : ℕ} (hNn : N ≤ n) {α : ℝ} (hα : 0 ≤ α) :
    convertCap N α ≤ convertCap n α := by
  have hc := hierarchyConstantLL_pos
  have hL : (logL N : ℝ) ≤ logL n := by exact_mod_cast logL_mono hNn
  have hK : (logL (logL N) : ℝ) ≤ logL (logL n) := by exact_mod_cast logL_mono (logL_mono hNn)
  have hN : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hsk : (skelBound N : ℝ) ≤ skelBound n := by exact_mod_cast skelBound_mono hNn
  have hL0 : (0 : ℝ) ≤ logL N := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ logL (logL N) := Nat.cast_nonneg _
  unfold convertCap
  gcongr

/-- **The conversion stage.** On a correct Theorem 5 output of a graph with positive minimum
cut, the result is a minimum cut of `G`, with the cap `convertCap N α` on the quotient size
`N = |Cls r| ≤ n`. -/
theorem convertStage_spec [Nonempty V] {α : ℝ} (hα : 1 ≤ α) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) {out : Output V}
    (hout : Correct G α out) :
    IsMinCut G ((convertStage α out).eval G.cut) ∧
    ((convertStage α out).cost G.cut : ℝ) ≤ convertCap (Fintype.card (Cls out.r)) α := by
  obtain ⟨hs, hgood⟩ := hout
  have : Nonempty (Cls out.r) := ⟨proj out.r (Classical.arbitrary V)⟩
  have hN2 : 2 ≤ Fintype.card (Cls out.r) := safePartition_two_le_card G hn hs
  have hqpos : 0 < mincutValue (quot G out.r) := safePartition_quotient_positive G hn hs hpos
  have hcutq : G.cut ∘ pull (proj out.r) = (quot G out.r).cut := by
    funext T; exact (cut_contract G (proj out.r) T).symm
  have hNorm := normalTopology_normal out.data.tree
  have hprom := approximates_promise out.data (quot G out.r) hN2 hgood.approximates
  obtain ⟨hskel, hccost⟩ := suppliedHierarchyProgLL_spec (normalTopology out.data.tree) α
    (quot G out.r) hN2 hqpos hα hNorm.leaves (by have := hNorm.size; omega) hprom
  simp only [convertStage, eval_map, cost_map, eval_mapQ, cost_mapQ, hcutq, eval_bind, cost_bind]
  set H := (suppliedHierarchyProgLL (normalTopology out.data.tree) α).eval (quot G out.r).cut
  refine ⟨isMinCut_pull_of_safePartition G hn hs
    (@skeletonMinCut_correct _ _ _ (clsOrder out.r) (quot G out.r) H hN2 hskel), ?_⟩
  have hsk : ((@skeletonMinCut _ _ _ (clsOrder out.r) H).cost (quot G out.r).cut : ℝ) ≤
      skelBound (Fintype.card (Cls out.r)) := by
    exact_mod_cast @skeletonMinCut_cost _ _ _ (clsOrder out.r) (quot G out.r) H
  unfold convertCap
  push_cast
  linarith

/-! ## The two-stage program -/

variable [LinearOrder V]

/-- **The two-stage algorithm.** The forest precheck, then Theorem 5 and the conversion stage. -/
noncomputable def twoStage [Nonempty V] (α : ℝ) (x₀ : V) : Comp (Finset V) ℝ (Finset V) :=
  (SupportForest.program (V := V)).bind fun fo =>
    match fo.test x₀ with
    | some S => Comp.pure S
    | none => (learnLL α).bind (convertStage α)

/-- **Correctness and cost of the two-stage algorithm** for admissible `α`: a minimum cut of
every nonnegative weighted graph, within the forest cap, the Theorem 5 cap and the conversion
cap. -/
theorem twoStage_spec [Nonempty V] {α : ℝ} (hα : AdmissibleLL (Fintype.card V) α)
    (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (x₀ : V) :
    IsMinCut G ((twoStage α x₀).eval G.cut) ∧
    ((twoStage α x₀).cost G.cut : ℝ) ≤
      forestBudget (Fintype.card V) + budgetLL (Fintype.card V) α +
        convertCap (Fintype.card V) α := by
  have hα1 := (admissibleLL_bounds hα).1
  obtain ⟨hc, hcost⟩ := SupportForest.program_spec (V := V) G
  have hfc : ((SupportForest.program (V := V)).cost G.cut : ℝ) ≤ forestBudget (Fintype.card V) := by
    exact_mod_cast hcost
  have hcc := convertCap_nonneg (N := Fintype.card V) (α := α) (by linarith)
  simp only [twoStage, eval_bind, cost_bind]
  by_cases hconn : G.support.Connected
  · rw [hc.test_of_connected x₀ hconn]
    have hpos : 0 < mincutValue G := (support_connected_iff_pos G hn).mp hconn
    obtain ⟨hl, hlcost⟩ := learnLL_spec hα G hn hpos
    simp only [eval_bind, cost_bind]
    obtain ⟨hmin, hccost⟩ := convertStage_spec hα1 G hn hpos hl
    refine ⟨hmin, ?_⟩
    have hlcostR := (Nat.cast_le (α := ℝ)).mpr hlcost
    have hmono := convertCap_mono (card_cls_le ((learnLL α).eval G.cut).r) (α := α) (by linarith)
    push_cast
    linarith
  · obtain ⟨S, hS, hprop, hzero⟩ := hc.test_of_not_connected x₀ hconn
    rw [hS]
    simp only [eval_pure, cost_pure, Nat.add_zero]
    refine ⟨(isMinCut_of_cut_eq_zero G hprop hzero).1, ?_⟩
    have h0 : (0 : ℝ) ≤ budgetLL (Fintype.card V) α := Nat.cast_nonneg _
    linarith

/-! ## The offline fallback -/

/-- Learn the whole graph (`n + n²` queries) and minimize its cuts offline. -/
noncomputable def offlineMinCut : Comp (Finset V) ℝ (Finset V) :=
  (learnContract (id : V → V) univ).map bestCut

theorem offlineMinCut_spec (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    IsMinCut G ((offlineMinCut (V := V)).eval G.cut) ∧
    (offlineMinCut (V := V)).cost G.cut ≤ Fintype.card V + Fintype.card V * Fintype.card V := by
  simp only [offlineMinCut, eval_map, cost_map]
  rw [learnContract_eval G id (fun _ => mem_univ _), contract_id]
  refine ⟨bestCut_spec G hn, ?_⟩
  have := learnContract_cost G (id : V → V) univ
  rwa [card_univ] at this

/-! ## The algorithm at `α = ⌊√n⌋` and its budget -/

open Classical in
/-- **The two-stage algorithm at `α = ⌊√n⌋`**, with the offline fallback for the finitely many
sizes at which `⌊√n⌋` is not admissible. The branch is decided from `n` alone. -/
noncomputable def twoStageAuto [Nonempty V] (x₀ : V) : Comp (Finset V) ℝ (Finset V) :=
  if AdmissibleLL (Fintype.card V) (Nat.sqrt (Fintype.card V) : ℝ) then
    twoStage (Nat.sqrt (Fintype.card V) : ℝ) x₀
  else offlineMinCut

/-- The constant of the two-stage cap. -/
noncomputable def twoStageConstant : ℝ :=
  7 + 3 * queryConstantLL + hierarchyConstantLL + 2900 + 2 * discoveryConstantLL + 1

theorem twoStageConstant_pos : 0 < twoStageConstant := by
  have := hierarchyConstantLL_pos
  unfold twoStageConstant queryConstantLL discoveryConstantLL
  linarith

/-- The public query budget of `twoStageAuto` on `n` vertices. -/
noncomputable def twoStageBudget (n : ℕ) : ℕ :=
  ⌈twoStageConstant * n * (Nat.sqrt n + 1) * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2)⌉₊

theorem twoStageBudget_le {n : ℕ} (hn : 2 ≤ n) :
    (twoStageBudget n : ℝ) ≤
      (twoStageConstant + 1) * n * (Nat.sqrt n + 1) *
        ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs1 : (1 : ℝ) ≤ Nat.sqrt n + 1 := by
    have : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
    linarith
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hK1 : (1 : ℝ) ≤ (logL (logL n) : ℝ) := by exact_mod_cast one_le_logL' _
  have hbase : (1 : ℝ) ≤ (n : ℝ) * (Nat.sqrt n + 1) *
      ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hs1)
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hK1))
  have hc := twoStageConstant_pos
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ twoStageConstant * n * (Nat.sqrt n + 1) *
      ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) by positivity)
  unfold twoStageBudget
  nlinarith

/-- The arithmetic of the admissible branch: the three caps at `α = ⌊√n⌋` are within
`(7 + 3 queryConstantLL + hierarchyConstantLL + 2900) n (⌊√n⌋ + 1) L(n)³ L(L(n))²`. -/
theorem admissible_branch_le {n : ℕ} (hn : 2 ≤ n)
    (hα : AdmissibleLL n (Nat.sqrt n : ℝ)) :
    (forestBudget n : ℝ) + budgetLL n (Nat.sqrt n : ℝ) + convertCap n (Nat.sqrt n : ℝ) ≤
      (7 + 3 * queryConstantLL + hierarchyConstantLL + 2900) * n * (Nat.sqrt n + 1) *
        ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsN : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
  have hs : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hsN
  have hs0 : (0 : ℝ) < Nat.sqrt n := by linarith
  have hnlt : (n : ℝ) < (Nat.sqrt n + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hK1 : (1 : ℝ) ≤ (logL (logL n) : ℝ) := by exact_mod_cast one_le_logL' _
  set P : ℝ := (logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2 with hP
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hK1)
  have hLP : (logL n : ℝ) ≤ P := by
    have h13 : (logL n : ℝ) ≤ (logL n : ℝ) ^ 3 := by
      simpa using pow_le_pow_right₀ hL1 (show 1 ≤ 3 by norm_num)
    have hK2 : 1 ≤ (logL (logL n) : ℝ) ^ 2 := one_le_pow₀ hK1
    have h3 : 0 ≤ (logL n : ℝ) ^ 3 := by positivity
    rw [hP]; nlinarith
  have hL2P : (logL n : ℝ) ^ 2 ≤ P := by
    have h23 : (logL n : ℝ) ^ 2 ≤ (logL n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
    have hK2 : 1 ≤ (logL (logL n) : ℝ) ^ 2 := one_le_pow₀ hK1
    have h3 : 0 ≤ (logL n : ℝ) ^ 3 := by positivity
    rw [hP]; nlinarith
  set Z : ℝ := n * (Nat.sqrt n + 1) * P with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hnLZ : (n : ℝ) * logL n ≤ Z := by
    rw [hZ]
    calc (n : ℝ) * logL n = n * 1 * logL n := by ring
      _ ≤ n * (Nat.sqrt n + 1) * P := by gcongr; linarith
  have hnL2Z : (n : ℝ) * (logL n : ℝ) ^ 2 ≤ Z := by
    rw [hZ]
    calc (n : ℝ) * (logL n : ℝ) ^ 2 = n * 1 * (logL n : ℝ) ^ 2 := by ring
      _ ≤ n * (Nat.sqrt n + 1) * P := by gcongr; linarith
  -- the forest cap
  have hF : (forestBudget n : ℝ) ≤ 7 * Z := by
    have h1 : (forestBudget n : ℝ) ≤ 7 * n * logL n := by
      exact_mod_cast forestBudget_le_linear_log n
    linarith
  -- Theorem 5 at `α = ⌊√n⌋`: `n² / ⌊√n⌋ ≤ 3 n (⌊√n⌋ + 1)`
  have hB : (budgetLL n (Nat.sqrt n : ℝ) : ℝ) ≤ 3 * queryConstantLL * Z := by
    have h1 := budgetLL_le (by omega) hα
    have hqc : 0 ≤ queryConstantLL := by norm_num [queryConstantLL, discoveryConstantLL]
    have hdiv : (n : ℝ) ^ 2 / Nat.sqrt n ≤ 3 * n * (Nat.sqrt n + 1) := by
      rw [div_le_iff₀ hs0]
      have : (n : ℝ) ≤ 3 * (Nat.sqrt n + 1) * Nat.sqrt n := by nlinarith
      nlinarith
    have hKK : (KK n : ℝ) = logL (logL n) := by rw [KK_eq]
    rw [hKK] at h1
    calc (budgetLL n (Nat.sqrt n : ℝ) : ℝ)
        ≤ queryConstantLL * ((n : ℝ) ^ 2 / Nat.sqrt n) * P := h1
      _ ≤ queryConstantLL * (3 * n * (Nat.sqrt n + 1)) * P := by gcongr
      _ = 3 * queryConstantLL * Z := by rw [hZ]; ring
  -- the conversion cap and the skeleton search
  have hC : convertCap n (Nat.sqrt n : ℝ) ≤ (hierarchyConstantLL + 2900) * Z := by
    have hc := hierarchyConstantLL_pos
    have hconv : hierarchyConstantLL * n * Nat.sqrt n * P ≤ hierarchyConstantLL * Z := by
      rw [hZ]
      calc hierarchyConstantLL * n * Nat.sqrt n * P
          = hierarchyConstantLL * (n * Nat.sqrt n * P) := by ring
        _ ≤ hierarchyConstantLL * (n * (Nat.sqrt n + 1) * P) := by gcongr; linarith
    have hclog : (Nat.clog 2 n : ℝ) ≤ logL n := by exact_mod_cast clog_le_logL (le_refl n)
    have hsk : (skelBound n : ℝ) ≤ 2900 * Z := by
      have h1 : (skelBound n : ℝ) ≤ 2900 * (n * (logL n : ℝ) ^ 2) := by
        unfold skelBound TwoRespecting.coverSize
        push_cast
        have hnL : (1 : ℝ) ≤ n * logL n := one_le_mul_of_one_le_of_one_le hn1 hL1
        have : (5 : ℝ) * ((Nat.clog 2 n : ℝ) + 3) * (72 * n * ((Nat.clog 2 n : ℝ) + 1) + 1) ≤
            5 * (4 * logL n) * (145 * n * logL n) := by
          gcongr
          · linarith
          · nlinarith
        nlinarith
      linarith
    unfold convertCap
    linarith
  calc (forestBudget n : ℝ) + budgetLL n (Nat.sqrt n : ℝ) + convertCap n (Nat.sqrt n : ℝ)
      ≤ 7 * Z + 3 * queryConstantLL * Z + (hierarchyConstantLL + 2900) * Z := by linarith
    _ = (7 + 3 * queryConstantLL + hierarchyConstantLL + 2900) * n * (Nat.sqrt n + 1) * P := by
        rw [hZ]; ring

/-- The arithmetic of the fallback branch: when `⌊√n⌋` is not admissible, `n + n² ≤
(2 discoveryConstantLL + 1) n (⌊√n⌋ + 1) L(n)³ L(L(n))²`. -/
theorem fallback_branch_le {n : ℕ} (hn : 2 ≤ n)
    (hα : ¬ AdmissibleLL n (Nat.sqrt n : ℝ)) :
    ((n + n * n : ℕ) : ℝ) ≤
      (2 * discoveryConstantLL + 1) * n * (Nat.sqrt n + 1) *
        ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs0 : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  have hnlt : (n : ℝ) < (Nat.sqrt n + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
  have hsq : (Nat.sqrt n : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hK1 : (1 : ℝ) ≤ (logL (logL n) : ℝ) := by exact_mod_cast one_le_logL' _
  have hD : 0 < discoveryConstantLL := by norm_num [discoveryConstantLL]
  -- not admissible means the lower threshold fails
  have hlt : (Nat.sqrt n : ℝ) < 2 * discoveryConstantLL * unitLL n := by
    by_contra h
    push Not at h
    exact hα ⟨h, hsq⟩
  have hunit : unitLL n ≤ (logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2 := by
    unfold unitLL
    rw [KK_eq]
    have h23 : (logL n : ℝ) ^ 2 ≤ (logL n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
    have hK2 : 0 ≤ (logL (logL n) : ℝ) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right h23 hK2
  set P : ℝ := (logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2 with hP
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hK1)
  have hsP : (Nat.sqrt n : ℝ) + 1 ≤ (2 * discoveryConstantLL + 1) * P := by
    have hu := unitLL_pos n
    nlinarith
  have hnle : (n : ℝ) + 1 ≤ (Nat.sqrt n + 1) ^ 2 := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_succ_sqrt' n)
  have hnn : ((n + n * n : ℕ) : ℝ) ≤ n * (Nat.sqrt n + 1) * ((Nat.sqrt n : ℝ) + 1) := by
    push_cast
    have := mul_le_mul_of_nonneg_left hnle (by linarith : (0 : ℝ) ≤ n)
    nlinarith
  calc ((n + n * n : ℕ) : ℝ) ≤ n * (Nat.sqrt n + 1) * ((Nat.sqrt n : ℝ) + 1) := hnn
    _ ≤ n * (Nat.sqrt n + 1) * ((2 * discoveryConstantLL + 1) * P) := by gcongr
    _ = (2 * discoveryConstantLL + 1) * n * (Nat.sqrt n + 1) * P := by ring

/-- **Correctness and cost of `twoStageAuto`**: a minimum cut of every nonnegative weighted
graph on `n ≥ 2` vertices within `twoStageBudget n` queries. -/
theorem twoStageAuto_spec [Nonempty V] (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (x₀ : V) :
    IsMinCut G ((twoStageAuto x₀).eval G.cut) ∧
    (twoStageAuto x₀).cost G.cut ≤ twoStageBudget (Fintype.card V) := by
  set n := Fintype.card V with hndef
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hK1 : (1 : ℝ) ≤ (logL (logL n) : ℝ) := by exact_mod_cast one_le_logL' _
  have hP1 : (1 : ℝ) ≤ (logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hK1)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hs1 : (0 : ℝ) ≤ Nat.sqrt n + 1 := by positivity
  have hbase : (0 : ℝ) ≤ (n : ℝ) * (Nat.sqrt n + 1) *
      ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by positivity
  have hqc : 0 ≤ queryConstantLL := by norm_num [queryConstantLL, discoveryConstantLL]
  have hhc := hierarchyConstantLL_pos
  have hD : 0 ≤ discoveryConstantLL := by norm_num [discoveryConstantLL]
  unfold twoStageAuto
  split_ifs with hα
  · obtain ⟨hmin, hcost⟩ := twoStage_spec hα G hn x₀
    refine ⟨hmin, ?_⟩
    have h1 := admissible_branch_le hn hα
    refine Nat.cast_le.mp (le_trans ?_ (Nat.le_ceil _))
    have hrest : 0 ≤ (2 * discoveryConstantLL + 1) * n * (Nat.sqrt n + 1) *
        ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by positivity
    unfold twoStageConstant
    nlinarith
  · obtain ⟨hmin, hcost⟩ := offlineMinCut_spec G hn
    refine ⟨hmin, ?_⟩
    have h1 := fallback_branch_le hn hα
    refine Nat.cast_le.mp (le_trans ?_ (Nat.le_ceil _))
    have hcostR : (((offlineMinCut (V := V)).cost G.cut : ℕ) : ℝ) ≤ ((n + n * n : ℕ) : ℝ) := by
      exact_mod_cast hcost
    have hrest : 0 ≤ (7 + 3 * queryConstantLL + hierarchyConstantLL + 2900) * n *
        (Nat.sqrt n + 1) * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by positivity
    unfold twoStageConstant
    nlinarith

/-! ## The endpoints -/

/-- **Theorem 1 with exponent `3 + 2 log log`, by the two-stage composition.** One
deterministic decision tree per `n ≥ 2` with `O(n (⌊√n⌋ + 1) L(n)³ L(L(n))²)` cut queries
returns a minimum cut of every nonnegative weighted graph on `n` vertices: the statement of
`DetMinCut.deterministic_mincut_log3loglog2`, reached through Theorem 5 (`learnLL`) and the
conversion theorem (`suppliedHierarchyProgLL`) instead of the fused main loop. -/
theorem deterministic_mincut_two_stage :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S := by
  refine ⟨twoStageConstant + 1, by linarith [twoStageConstant_pos], fun n hn => ?_⟩
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨twoStageBudget n, twoStageBudget_le hn,
    (twoStageAuto (V := Fin n) ⟨0, by omega⟩).toDTree (twoStageBudget n), fun G => ?_⟩
  have hs := twoStageAuto_spec (V := Fin n) G (by simpa using hn) ⟨0, by omega⟩
  exact ⟨_, toDTree_eval _ _ (by simpa using hs.2), hs.1⟩

/-- **The two-stage cap in the paper's notation**: `O(n^{3/2} log³ n (log log n)²)`. -/
theorem deterministic_mincut_two_stage_real_log :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S := by
  obtain ⟨C, hC, hall⟩ := deterministic_mincut_two_stage
  refine ⟨C * 3 ^ 5, by positivity, fun n hn => ?_⟩
  obtain ⟨q, hq, D, hD⟩ := hall n hn
  refine ⟨q, hq.trans ?_, D, hD⟩
  have hL := logL_le_real_log hn
  have hK := DetMinCut.logL_logL_le_real_log hn
  have hlog1 := real_log_one hn
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

end CutQueryComplexity.TreeCutSparsifier
