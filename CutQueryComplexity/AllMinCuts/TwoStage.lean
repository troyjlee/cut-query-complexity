import CutQueryComplexity.AllMinCuts.Cover
import CutQueryComplexity.AllMinCuts.Conversion
import CutQueryComplexity.AllMinCuts.Support
import CutQueryComplexity.TreeCutSparsifier.TwoStage

/-! # The two-stage algorithm for all minimum cuts (all-minima plan, M6)

On a graph `G` with `n ≥ 2` vertices, `allTwoStage α x₀`:

1. runs the positive-support forest routine (`SupportForest.program`); if the support is
   disconnected, `λ(G) = 0` and the zero family `zeroOutput fo.r` is returned with no further
   query;
2. otherwise `0 < λ(G)`, and `learnLL α` (Theorem 5) returns a safe partition `r` and an explicit
   `α`-tree cut sparsifier of the quotient `G/r`;
3. `positiveStage α out` runs the existing supplied-hierarchy program on the normalized topology
   of that tree, which yields an `AllMinCutSkeleton` of `G/r` (`conversion_allMinCuts`), then
   `coverReport` on the quotient, which returns the complete family of `G/r`
   (`coverReport_spec`); every quotient query is one original query on the union of the classes
   in it (`mapQ (pull (proj r))`);
4. the family is pulled back to `G` (`Correct.pullOutput`), which is exact because `r` is safe.

`allTwoStageAuto` runs `allTwoStage` at `α = ⌊√n⌋` when that is admissible, and otherwise
learns the whole graph (`n + n²` queries) and lists its minimum cuts offline (`offlineAll`);
the fallback never queries the candidate shores. The cap is `allBudget n ≤ (allConstant + 1)
n (⌊√n⌋ + 1) L(n)³ L(L(n))²` (`allTwoStageAuto_spec`), where `allConstant` is the two-stage
constant plus `10001` for the reporting stage.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllMinCuts

open WeightedGraph Search Search.Comp Hierarchy DetMinCut TwoRespecting UndirectedClosure Finset
open TreeCutSparsifier (learnLL learnLL_spec budgetLL budgetLL_le AdmissibleLL admissibleLL_bounds
  convertCap convertCap_mono convertCap_nonneg admissible_branch_le fallback_branch_le
  twoStageConstant twoStageConstant_pos safePartition_two_le_card
  safePartition_quotient_positive queryConstantLL discoveryConstantLL contract_id)
open SupportForest (forestBudget)

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The positive branch on the learned quotient -/

/-- Convert the learned tree of the quotient to an all-minimum-cut skeleton, report the complete
family of the quotient, and pull it back; each quotient query is one original query. -/
noncomputable def positiveStage [Nonempty V] (α : ℝ) (out : TreeCutSparsifier.Output V) :
    Comp (Finset V) ℝ (Output V) :=
  have : Nonempty (Cls out.r) := ⟨proj out.r (Classical.arbitrary V)⟩
  (mapQ (pull (proj out.r))
    ((suppliedHierarchyProgLL (normalTopology out.data.tree) α).bind fun H =>
      @coverReport _ _ _ (clsOrder out.r) H)).map (pullOutput out.r)

/-- The cap of the positive branch on the quotient size `N`: the conversion cap of the
single-cut two-stage algorithm plus the extra reporting work. -/
noncomputable def allConvertCap (N : ℕ) (α : ℝ) : ℝ :=
  convertCap N α + ((1 + coverSize N * (250 * N * (Nat.clog 2 N + 1)) : ℕ) : ℝ)

theorem allConvertCap_nonneg {N : ℕ} {α : ℝ} (hα : 0 ≤ α) : 0 ≤ allConvertCap N α := by
  have := convertCap_nonneg (N := N) hα
  unfold allConvertCap; positivity

theorem allConvertCap_mono {N n : ℕ} (hNn : N ≤ n) {α : ℝ} (hα : 0 ≤ α) :
    allConvertCap N α ≤ allConvertCap n α := by
  have h1 := convertCap_mono hNn hα
  have h2 : 1 + coverSize N * (250 * N * (Nat.clog 2 N + 1)) ≤
      1 + coverSize n * (250 * n * (Nat.clog 2 n + 1)) := by
    unfold coverSize
    have := Nat.clog_mono_right 2 hNn
    gcongr
  have h2' : ((1 + coverSize N * (250 * N * (Nat.clog 2 N + 1)) : ℕ) : ℝ) ≤
      ((1 + coverSize n * (250 * n * (Nat.clog 2 n + 1)) : ℕ) : ℝ) := by exact_mod_cast h2
  unfold allConvertCap
  linarith

/-- **The positive branch.** On a correct Theorem 5 output of a graph with positive minimum cut,
the result is the complete family of minimum cuts of `G` with the value `λ(G)`, within
`allConvertCap N α` queries for the quotient size `N`. -/
theorem positiveStage_spec [Nonempty V] {α : ℝ} (hα : 1 ≤ α) (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (hpos : 0 < mincutValue G) {out : TreeCutSparsifier.Output V}
    (hout : TreeCutSparsifier.Correct G α out) :
    Correct G ((positiveStage α out).eval G.cut) ∧
    ((positiveStage α out).cost G.cut : ℝ) ≤ allConvertCap (Fintype.card (Cls out.r)) α := by
  obtain ⟨hs, hgood⟩ := hout
  have : Nonempty (Cls out.r) := ⟨proj out.r (Classical.arbitrary V)⟩
  have hN2 : 2 ≤ Fintype.card (Cls out.r) := safePartition_two_le_card G hn hs
  have hqpos : 0 < mincutValue (quot G out.r) := safePartition_quotient_positive G hn hs hpos
  have hcutq : G.cut ∘ pull (proj out.r) = (quot G out.r).cut := by
    funext T; exact (cut_contract G (proj out.r) T).symm
  obtain ⟨hskel, hccost⟩ := conversion_allMinCuts out.data (quot G out.r) hN2 hqpos hα
    hgood.approximates
  simp only [positiveStage, eval_map, cost_map, eval_mapQ, cost_mapQ, hcutq, eval_bind, cost_bind]
  set H := (suppliedHierarchyProgLL (normalTopology out.data.tree) α).eval (quot G out.r).cut
  obtain ⟨hcorr, hrc⟩ := @coverReport_spec _ _ _ (clsOrder out.r) (quot G out.r) H hN2 hqpos hskel
  refine ⟨hcorr.pullOutput hn hs, ?_⟩
  have hrcR : ((@coverReport _ _ _ (clsOrder out.r) H).cost (quot G out.r).cut : ℝ) ≤
      reportBound (Fintype.card (Cls out.r)) := by exact_mod_cast hrc
  unfold allConvertCap convertCap
  unfold reportBound at hrcR
  push_cast at hrcR ⊢
  linarith

/-! ## The offline fallback -/

open Classical in
/-- The value and the complete family of minimum cuts of an explicit graph, offline. -/
noncomputable def familyOf (H : WeightedGraph V) : Output V :=
  ⟨(properShores V).filter fun S => H.cut S = mincutValue H, mincutValue H⟩

theorem familyOf_correct (G : WeightedGraph V) : Correct G (familyOf G) := by
  refine ⟨rfl, fun S => ?_⟩
  rw [isMinCut_iff]
  classical
  simp [familyOf, mem_filter, mem_properShores]

variable [LinearOrder V]

/-- Learn the whole graph (`n + n²` queries) and list its minimum cuts offline. -/
noncomputable def offlineAll : Comp (Finset V) ℝ (Output V) :=
  (learnContract (id : V → V) univ).map familyOf

theorem offlineAll_spec (G : WeightedGraph V) :
    Correct G ((offlineAll (V := V)).eval G.cut) ∧
    (offlineAll (V := V)).cost G.cut ≤ Fintype.card V + Fintype.card V * Fintype.card V := by
  simp only [offlineAll, eval_map, cost_map]
  rw [learnContract_eval G id (fun _ => mem_univ _), contract_id]
  refine ⟨familyOf_correct G, ?_⟩
  have := learnContract_cost G (id : V → V) univ
  rwa [card_univ] at this

/-! ## The two-stage program -/

/-- **The two-stage algorithm for all minimum cuts.** The forest precheck with the zero family,
then Theorem 5 and the positive branch. -/
noncomputable def allTwoStage [Nonempty V] (α : ℝ) (x₀ : V) : Comp (Finset V) ℝ (Output V) :=
  (SupportForest.program (V := V)).bind fun fo =>
    match fo.test x₀ with
    | some _ => Comp.pure (zeroOutput fo.r)
    | none => (learnLL α).bind (positiveStage α)

/-- **Correctness and cost of the two-stage algorithm** for admissible `α`: the complete family
of minimum cuts of every nonnegative weighted graph, within the forest cap, the Theorem 5 cap and
the positive-branch cap. -/
theorem allTwoStage_spec [Nonempty V] {α : ℝ} (hα : AdmissibleLL (Fintype.card V) α)
    (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (x₀ : V) :
    Correct G ((allTwoStage α x₀).eval G.cut) ∧
    ((allTwoStage α x₀).cost G.cut : ℝ) ≤
      forestBudget (Fintype.card V) + budgetLL (Fintype.card V) α +
        allConvertCap (Fintype.card V) α := by
  have hα1 := (admissibleLL_bounds hα).1
  obtain ⟨hc, hcost⟩ := SupportForest.program_spec (V := V) G
  have hfc : ((SupportForest.program (V := V)).cost G.cut : ℝ) ≤
      forestBudget (Fintype.card V) := by
    exact_mod_cast hcost
  have hcc := allConvertCap_nonneg (N := Fintype.card V) (α := α) (by linarith)
  simp only [allTwoStage, eval_bind, cost_bind]
  by_cases hconn : G.support.Connected
  · rw [hc.test_of_connected x₀ hconn]
    have hpos : 0 < mincutValue G := (SupportForest.support_connected_iff_pos G hn).mp hconn
    obtain ⟨hl, hlcost⟩ := learnLL_spec hα G hn hpos
    simp only [eval_bind, cost_bind]
    obtain ⟨hcorr, hccost⟩ := positiveStage_spec hα1 G hn hpos hl
    refine ⟨hcorr, ?_⟩
    have hlcostR := (Nat.cast_le (α := ℝ)).mpr hlcost
    have hmono := allConvertCap_mono (card_cls_le ((learnLL α).eval G.cut).r) (α := α)
      (by linarith)
    push_cast
    linarith
  · obtain ⟨S, hS, -, -⟩ := hc.test_of_not_connected x₀ hconn
    rw [hS]
    simp only [eval_pure, cost_pure, Nat.add_zero]
    refine ⟨zeroOutput_correct hc hn hconn, ?_⟩
    have h0 : (0 : ℝ) ≤ budgetLL (Fintype.card V) α := Nat.cast_nonneg _
    linarith

/-! ## The algorithm at `α = ⌊√n⌋` and its budget -/

open Classical in
/-- **The two-stage algorithm for all minimum cuts at `α = ⌊√n⌋`**, with the offline fallback
for the finitely many sizes at which `⌊√n⌋` is not admissible. The branch is decided from `n`
alone. -/
noncomputable def allTwoStageAuto [Nonempty V] (x₀ : V) : Comp (Finset V) ℝ (Output V) :=
  if AdmissibleLL (Fintype.card V) (Nat.sqrt (Fintype.card V) : ℝ) then
    allTwoStage (Nat.sqrt (Fintype.card V) : ℝ) x₀
  else offlineAll

/-- The constant of the all-minimum-cut cap: the two-stage constant and `10001` for the
reporting stage. -/
noncomputable def allConstant : ℝ := twoStageConstant + 10001

theorem allConstant_pos : 0 < allConstant := by
  have := twoStageConstant_pos
  unfold allConstant; linarith

/-- The public query budget of `allTwoStageAuto` on `n` vertices. -/
noncomputable def allBudget (n : ℕ) : ℕ :=
  ⌈allConstant * n * (Nat.sqrt n + 1) * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2)⌉₊

theorem allBudget_le {n : ℕ} (hn : 2 ≤ n) :
    (allBudget n : ℝ) ≤
      (allConstant + 1) * n * (Nat.sqrt n + 1) *
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
  have hc := allConstant_pos
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ allConstant * n * (Nat.sqrt n + 1) *
      ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) by positivity)
  unfold allBudget
  nlinarith

/-- The extra reporting work is within `10001 n (⌊√n⌋ + 1) L(n)³ L(L(n))²`. -/
theorem extraCap_le {n : ℕ} (hn : 2 ≤ n) :
    ((1 + coverSize n * (250 * n * (Nat.clog 2 n + 1)) : ℕ) : ℝ) ≤
      10001 * (n * (Nat.sqrt n + 1) * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hK1 : (1 : ℝ) ≤ (logL (logL n) : ℝ) := by exact_mod_cast one_le_logL' _
  have hclog : (Nat.clog 2 n : ℝ) ≤ logL n := by exact_mod_cast clog_le_logL (le_refl n)
  have hC0 : (0 : ℝ) ≤ Nat.clog 2 n := Nat.cast_nonneg _
  set L : ℝ := (logL n : ℝ)
  set C : ℝ := (Nat.clog 2 n : ℝ)
  set P : ℝ := L ^ 3 * (logL (logL n) : ℝ) ^ 2 with hP
  have hL2P : L ^ 2 ≤ P := by
    have h23 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
    have hK2 : 1 ≤ (logL (logL n) : ℝ) ^ 2 := one_le_pow₀ hK1
    have h3 : 0 ≤ L ^ 3 := by positivity
    rw [hP]; nlinarith
  have hZ : (n : ℝ) * L ^ 2 ≤ n * (Nat.sqrt n + 1) * P := by
    calc (n : ℝ) * L ^ 2 = n * 1 * L ^ 2 := by ring
      _ ≤ n * (Nat.sqrt n + 1) * P := by
          gcongr
          · have : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
            linarith
  have h1 : (5 : ℝ) * (C + 3) ≤ 20 * L := by linarith
  have h2 : (250 : ℝ) * n * (C + 1) ≤ 500 * n * L := by nlinarith
  have h3 : (5 * (C + 3)) * (250 * n * (C + 1)) ≤ (20 * L) * (500 * n * L) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have hnL2 : (1 : ℝ) ≤ n * L ^ 2 := one_le_mul_of_one_le_of_one_le hn1 (one_le_pow₀ hL1)
  unfold coverSize
  push_cast
  nlinarith

/-- **Correctness and cost of `allTwoStageAuto`**: the value and the complete family of minimum
cuts of every nonnegative weighted graph on `n ≥ 2` vertices within `allBudget n` queries. -/
theorem allTwoStageAuto_spec [Nonempty V] (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (x₀ : V) :
    Correct G ((allTwoStageAuto x₀).eval G.cut) ∧
    (allTwoStageAuto x₀).cost G.cut ≤ allBudget (Fintype.card V) := by
  set n := Fintype.card V with hndef
  have hL1 : (1 : ℝ) ≤ (logL n : ℝ) := by exact_mod_cast one_le_logL' n
  have hK1 : (1 : ℝ) ≤ (logL (logL n) : ℝ) := by exact_mod_cast one_le_logL' _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hs1 : (0 : ℝ) ≤ Nat.sqrt n + 1 := by positivity
  have hbase : (0 : ℝ) ≤ (n : ℝ) * (Nat.sqrt n + 1) *
      ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by positivity
  have hqc : 0 ≤ queryConstantLL := by norm_num [queryConstantLL, discoveryConstantLL]
  have hhc := hierarchyConstantLL_pos
  have hD : 0 ≤ discoveryConstantLL := by norm_num [discoveryConstantLL]
  have hextra := extraCap_le hn
  unfold allTwoStageAuto
  split_ifs with hα
  · obtain ⟨hcorr, hcost⟩ := allTwoStage_spec hα G hn x₀
    refine ⟨hcorr, ?_⟩
    have h1 := admissible_branch_le hn hα
    refine Nat.cast_le.mp (le_trans ?_ (Nat.le_ceil _))
    have hrest : 0 ≤ (2 * discoveryConstantLL + 1) * n * (Nat.sqrt n + 1) *
        ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by positivity
    unfold allConvertCap at hcost
    unfold allConstant twoStageConstant
    nlinarith
  · obtain ⟨hcorr, hcost⟩ := offlineAll_spec G
    refine ⟨hcorr, ?_⟩
    have h1 := fallback_branch_le hn hα
    refine Nat.cast_le.mp (le_trans ?_ (Nat.le_ceil _))
    have hcostR : (((offlineAll (V := V)).cost G.cut : ℕ) : ℝ) ≤ ((n + n * n : ℕ) : ℝ) := by
      exact_mod_cast hcost
    have hrest : 0 ≤ (7 + 3 * queryConstantLL + hierarchyConstantLL + 2900 + 10001) * n *
        (Nat.sqrt n + 1) * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) := by positivity
    unfold allConstant twoStageConstant
    nlinarith

end CutQueryComplexity.AllMinCuts
