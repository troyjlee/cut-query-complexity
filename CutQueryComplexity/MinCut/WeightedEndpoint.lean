import CutQueryComplexity.MinCut.Weighted
import CutQueryComplexity.AllPairs.Budget
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! A public constant-error weighted global-mincut program with original value
verification. All weights remain arbitrary nonnegative reals. The existing
weighted algorithm is followed by an actual original-cut query. Its complete
all-reply cap is bounded by a stronger O(n log²(2n)) envelope. -/
namespace CutQueryComplexity.WeightedMinCut.Endpoint
open WeightedGraph Probability
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V : Type} [Fintype V]

/-- The exact cap of the algorithm and its final verification query. -/
def queryBudget (V : Type) [Fintype V] : ℕ :=
  capQ V (paramρ V 1) (paramc V 1 (1 / 16)) + 8 * treeBudget V + 1

/-- Query the original shore to report its exact original numerical value. -/
def verify (o : Option (Finset V)) :
    RTree (Finset V) ℝ (Option (AllPairs.STAnswer V)) 1 :=
  match o with
  | none => RTree.pure (PMF.pure none)
  | some S => RTree.query S fun value => RTree.pure (PMF.pure (some ⟨S, value⟩))

def program (hn : 2 ≤ Fintype.card V) :
    RTree (Finset V) ℝ (Option (AllPairs.STAnswer V)) (queryBudget V) :=
  (weightedMinCut hn 1 8).bind verify

omit [Fintype V] in
/-- The executed final query is charged once precisely when a shore exists. -/
theorem verify_run (read : Finset V → ℝ) (o : Option (Finset V)) :
    RTree.run read (verify o) = PMF.pure
      (o.map (fun S => (⟨S, read S⟩ : AllPairs.STAnswer V)), if o.isSome then 1 else 0) := by
  cases o <;> simp [verify, RTree.run_query, RTree.run_pure, PMF.pure_map]

/-- Literal execution law relative to the public weighted program. -/
theorem program_run (hn : 2 ≤ Fintype.card V) (read : Finset V → ℝ) :
    RTree.run read (program hn) =
      (RTree.run read (weightedMinCut hn 1 8)).map (fun p =>
        (p.1.map (fun S => (⟨S, read S⟩ : AllPairs.STAnswer V)),
          p.2 + if p.1.isSome then 1 else 0)) := by
  simp [program, RTree.run_bind, verify_run, PMF.map, Function.comp_def]

omit [Fintype V] in
theorem verify_eval (read : Finset V → ℝ) (o : Option (Finset V)) :
    (verify o).eval read =
      PMF.pure (o.map (fun S => (⟨S, read S⟩ : AllPairs.STAnswer V))) := by
  simp [RTree.eval, verify_run, PMF.pure_map]

theorem program_eval (hn : 2 ≤ Fintype.card V) (read : Finset V → ℝ) :
    (program hn).eval read = ((weightedMinCut hn 1 8).eval read).map
      (Option.map fun S => (⟨S, read S⟩ : AllPairs.STAnswer V)) := by
  simp [program, RTree.eval_bind, verify_eval, PMF.map, Function.comp_def]

/-- Successful output includes both an original minimum shore and its exact value. -/
def Good (G : WeightedGraph V) (o : Option (AllPairs.STAnswer V)) : Prop :=
  ∃ a, o = some a ∧ IsMinCut G a.shore ∧ a.value = G.cut a.shore

theorem program_failure (hn : 2 ≤ Fintype.card V) (G : WeightedGraph V) :
    mass ((program hn).eval G.cut) (fun o => ¬Good G o) ≤ ENNReal.ofReal (1 / 3 : ℝ) := by
  have he : mass ((program hn).eval G.cut) (fun o => ¬Good G o) =
      mass ((weightedMinCut hn 1 8).eval G.cut)
        (fun o => ¬∃ S, o = some S ∧ IsMinCut G S) := by
    rw [program_eval, mass_map]
    congr 1
    funext o
    cases o <;> simp [Good]
  rw [he]
  apply (weightedMinCut_correct G hn (by norm_num : (0 : ℝ) ≤ 1) 8).trans
  have hB : (6 : ℝ) ≤ baseB V := by
    have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    simp only [baseB]; linarith
  have hi : baseB V ^ (-(1 : ℝ)) ≤ 1 / 6 := by
    rw [Real.rpow_neg_one]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) hB
  calc
    _ ≤ ENNReal.ofReal (1 / 6 : ℝ) + ENNReal.ofReal ((34 / 45 : ℝ) ^ 8) := by
      gcongr
    _ ≤ ENNReal.ofReal (1 / 3 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem paramc_sixteenth (s : ℝ) : paramc V s (1 / 16) = 64 * paramc V s (1 / 2) := by
  unfold paramc
  ring

theorem outBound_sixteenth_le (s : ℝ) :
    outBound V (paramc V s (1 / 16)) ≤ 64 * outBound V (paramc V s (1 / 2)) := by
  rw [paramc_sixteenth]
  unfold outBound
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ residualDrawCost (searchDepth V) (searchDepth V) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hn hd]

theorem capQ_sixteenth_le (s : ℝ) :
    capQ V (paramρ V s) (paramc V s (1 / 16)) ≤
      64 * capQ V (paramρ V s) (paramc V s (1 / 2)) := by
  have hc : ⌈outBound V (paramc V s (1 / 16))⌉₊ ≤
      64 * ⌈outBound V (paramc V s (1 / 2))⌉₊ := by
    apply Nat.ceil_le.mpr
    calc
      _ ≤ 64 * outBound V (paramc V s (1 / 2)) := outBound_sixteenth_le s
      _ ≤ 64 * (⌈outBound V (paramc V s (1 / 2))⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)
      _ = _ := by push_cast; rfl
  unfold capQ
  omega

theorem queryBudget_integerLog (hn : 2 ≤ Fintype.card V) :
    (queryBudget V : ℝ) ≤
      24000000 * Fintype.card V * (AllPairs.budgetLog (Fintype.card V) : ℝ) ^ 2 := by
  let n := Fintype.card V
  let L : ℝ := AllPairs.budgetLog n
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast AllPairs.budgetLog_one_le n
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hd : (Nat.clog 2 n + 1 : ℕ) ≤ AllPairs.budgetLog n :=
    AllPairs.depth_add_one_le_budgetLog n
  have hcap : (capQ V (paramρ V 1) (paramc V 1 (1 / 16)) : ℝ) ≤
      23040000 * n * L ^ 2 := by
    calc
      _ ≤ 64 * (capQ V (paramρ V 1) (paramc V 1 (1 / 2)) : ℝ) := by
        exact_mod_cast capQ_sixteenth_le (V := V) 1
      _ ≤ 64 * (40000 * (1 + 8) * n * L ^ 2) :=
        mul_le_mul_of_nonneg_left
          (AllPairs.capQ_public_le V (by omega) (by norm_num : (0 : ℝ) ≤ 1)) (by norm_num)
      _ = _ := by ring
  have ht : (8 * treeBudget V : ℕ) ≤ 576 * n * AllPairs.budgetLog n := by
    unfold treeBudget
    nlinarith [Nat.mul_le_mul_left (576 * n) hd]
  have htR : (8 * treeBudget V : ℕ) ≤ (576 * n * L : ℝ) := by
    dsimp [L]
    exact_mod_cast ht
  have htR' : (8 * treeBudget V : ℕ) ≤ (576 * n * L ^ 2 : ℝ) :=
    htR.trans (mul_le_mul_of_nonneg_left hLL (by positivity))
  have hscale : 1 ≤ (n : ℝ) * L ^ 2 := by nlinarith
  simp only [queryBudget, Nat.cast_add]
  change _ ≤ 24000000 * n * L ^ 2
  nlinarith only [hcap, htR', hscale]

/-- Conversion to a natural-log envelope with an explicit universal constant. -/
theorem budgetLog_realLog (n : ℕ) (hn : 2 ≤ n) :
    (AllPairs.budgetLog n : ℝ) ≤ 6 * Real.log (2 * (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hln : 1 ≤ Real.log (2 * (n : ℝ)) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (show 4 ≤ 2 * (n : ℝ) by linarith)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    norm_num at h
    linarith
  have hb : (1 : ℝ) ≤ (2 * n + 2 : ℕ) := by push_cast; linarith
  have hc : (Nat.clog 2 (2 * n + 2) : ℝ) ≤ Real.logb 2 (2 * n + 2 : ℕ) + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hb)).le
  have hlogB : Real.log (2 * n + 2 : ℕ) ≤ 2 * Real.log (2 * (n : ℝ)) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 * n + 2 : ℕ))
      (show ((2 * n + 2 : ℕ) : ℝ) ≤ (2 * (n : ℝ)) ^ 2 by push_cast; nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hquot : Real.logb 2 (2 * n + 2 : ℕ) ≤ 4 * Real.log (2 * (n : ℝ)) := by
    rw [Real.logb, div_le_iff₀ (by linarith : 0 < Real.log 2)]
    nlinarith
  unfold AllPairs.budgetLog
  push_cast
  linarith

theorem queryBudget_logSquared (hn : 2 ≤ Fintype.card V) :
    (queryBudget V : ℝ) ≤
      1000000000 * Fintype.card V * Real.log (2 * (Fintype.card V : ℝ)) ^ 2 := by
  have hb := queryBudget_integerLog (V := V) hn
  have hl := budgetLog_realLog (Fintype.card V) hn
  calc
    _ ≤ 24000000 * Fintype.card V * (AllPairs.budgetLog (Fintype.card V) : ℝ) ^ 2 := hb
    _ ≤ 24000000 * Fintype.card V * (6 * Real.log (2 * (Fintype.card V : ℝ))) ^ 2 := by
      gcongr
    _ ≤ _ := by
      have hnonneg : 0 ≤ (Fintype.card V : ℝ) *
          Real.log (2 * (Fintype.card V : ℝ)) ^ 2 := by positivity
      nlinarith only [hnonneg]


/-- One actual public program for all nonnegative real weighted inputs. -/
theorem weighted_global (hn : 2 ≤ Fintype.card V) :
    ∃ P : RTree (Finset V) ℝ (Option (AllPairs.STAnswer V)) (queryBudget V),
      P = program hn ∧
      (∀ read : Finset V → ℝ, ∀ r ∈ (RTree.run read P).support,
        (r.2 : ℝ) ≤ 1000000000 * Fintype.card V *
          Real.log (2 * (Fintype.card V : ℝ)) ^ 2) ∧
      ∀ G : WeightedGraph V,
        mass (P.eval G.cut) (fun o => ¬∃ a, o = some a ∧
          IsMinCut G a.shore ∧ a.value = G.cut a.shore) ≤ ENNReal.ofReal (1 / 3 : ℝ) := by
  refine ⟨program hn, rfl, fun read r hr => ?_, fun G => program_failure hn G⟩
  exact (Nat.cast_le.mpr (RTree.cost_le _ read hr)).trans (queryBudget_logSquared hn)

end
end CutQueryComplexity.WeightedMinCut.Endpoint
