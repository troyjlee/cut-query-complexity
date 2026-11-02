import CutQueryComplexity.StarContraction2022.Common.Quotient
import CutQueryComplexity.StarContraction2022.Common.Constants
import CutQueryComplexity.MinCut.Weighted

/-! # The implemented weighted solver at failure exponent three

The budget below is the index of the existing query program, expanded from its
source definitions. The graph is absent from every program constructor. Lifting
and verifying the returned shore adds exactly one original cut query.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.WeightedAdapter

noncomputable section
open scoped Classical ENNReal
open Probability WeightedGraph

variable {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]

def budget (Q : Type) [Fintype Q] : ℕ :=
  WeightedGraph.capQ Q (WeightedGraph.paramρ Q 3)
      (WeightedGraph.paramc Q 3 WeightedMinCut.eps) +
    WeightedMinCut.rounds Q 3 * WeightedMinCut.treeBudget Q

def solver (hq : 2 ≤ Fintype.card Q) :
    RTree (Finset Q) ℝ (Option (Finset Q)) (budget Q) :=
  WeightedMinCut.weightedMinCut hq 3 (WeightedMinCut.rounds Q 3)

def postprocess (π : PublicQuotient V Q) (o : Option (Finset Q)) :
    DTree (Finset V) ℝ (Option (CutResult V)) 1 :=
  match o with
  | none => DTree.pure none
  | some S => verifyShore (π.lift S)

def program (π : PublicQuotient V Q) (hq : 2 ≤ Fintype.card Q) :
    RTree (Finset V) ℝ (Option (CutResult V)) (budget Q + 1) :=
  (π.compile (solver hq)).bind fun o => RTree.ofDeterministic (postprocess π o)

theorem source_cost (hq : 2 ≤ Fintype.card Q) (read : Finset Q → ℝ)
    {out : Option (Finset Q) × ℕ} (hout : out ∈ (RTree.run read (solver hq)).support) :
    out.2 ≤ budget Q := RTree.cost_le _ read hout

theorem program_cost (π : PublicQuotient V Q) (hq : 2 ≤ Fintype.card Q)
    (read : Finset V → ℝ) {out : Option (CutResult V) × ℕ}
    (hout : out ∈ (RTree.run read (program π hq)).support) :
    out.2 ≤ budget Q + 1 := RTree.cost_le _ read hout

theorem postprocess_sound (π : PublicQuotient V Q) (G : WeightedGraph V)
    (o : Option (Finset Q)) {out : CutResult V}
    (h : (postprocess π o).eval G.cut = some out) : out.Sound G := by
  cases o with
  | none => simp [postprocess] at h
  | some S => exact verifyShore_sound G _ h

theorem program_sound (π : PublicQuotient V Q) (hq : 2 ≤ Fintype.card Q)
    (G : WeightedGraph V) {out : CutResult V}
    (h : some out ∈ ((program π hq).eval G.cut).support) : out.Sound G := by
  rw [program, RTree.eval_bind, PMF.mem_support_bind_iff] at h
  obtain ⟨o, _, ho⟩ := h
  rw [RTree.eval_ofDeterministic, PMF.mem_support_pure_iff] at ho
  exact postprocess_sound π G o ho.symm

theorem postprocess_good (π : PublicQuotient V Q) (G : WeightedGraph V)
    {S : Finset V} (hS : IsMinCut G S) (hs : RespectsBlocks π.map S)
    {T : Finset Q} (hT : IsMinCut (π.graph G) T) :
    ∃ out, (postprocess π (some T)).eval G.cut = some out ∧
      out.Sound G ∧ IsMinCut G out.shore ∧ out.value = mincutValue G := by
  have h := π.lift_minimum hS hs hT
  refine ⟨⟨π.lift T, G.cut (π.lift T)⟩, ?_, ⟨h.1, rfl⟩, h,
    cut_eq_mincut_of_isMinCut h⟩
  simp [postprocess, verifyShore_eval, h.1]

/-- The source theorem, specialized to the actual routine, gives failure < 1%. -/
theorem solver_failure (hq : 2 ≤ Fintype.card Q) (G : WeightedGraph Q) :
    mass ((solver hq).eval G.cut) (fun o => ¬∃ S, o = some S ∧ IsMinCut G S) ≤
      ENNReal.ofReal (1 / 100) := by
  have hdec : (fun x y : Q => Classical.propDecidable (x = y)) =
      (inferInstance : DecidableEq Q) := Subsingleton.elim _ _
  have hsource := WeightedMinCut.weightedMinCut_whp G hq
    (by norm_num : (0 : ℝ) ≤ 3)
  rw [hdec] at hsource
  refine hsource.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hB : (6 : ℝ) ≤ WeightedGraph.baseB Q := by
    have : (2 : ℝ) ≤ Fintype.card Q := by exact_mod_cast hq
    dsimp [WeightedGraph.baseB]
    linarith
  have hB0 : 0 < WeightedGraph.baseB Q := by linarith
  rw [Real.rpow_neg hB0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, ← div_eq_mul_inv]
  have hc : (216 : ℝ) ≤ WeightedGraph.baseB Q ^ 3 := by
    calc
      (216 : ℝ) = 6 ^ 3 := by norm_num
      _ ≤ WeightedGraph.baseB Q ^ 3 := pow_le_pow_left₀ (by norm_num) hB 3
  rw [div_le_iff₀ (pow_pos hB0 3)]
  linarith

theorem program_failure (π : PublicQuotient V Q) (hq : 2 ≤ Fintype.card Q)
    (G : WeightedGraph V) {S : Finset V} (hS : IsMinCut G S)
    (hs : RespectsBlocks π.map S) :
    mass ((program π hq).eval G.cut)
      (fun o => ¬∃ out, o = some out ∧ out.Sound G ∧ IsMinCut G out.shore ∧
        out.value = mincutValue G) ≤ ENNReal.ofReal (1 / 100) := by
  rw [program, RTree.eval_bind, π.compile_eval]
  have h := mass_bind_le_add ((solver hq).eval (π.graph G).cut)
    (fun o => (RTree.ofDeterministic (postprocess π o)).eval G.cut)
    (fun o => ¬∃ T, o = some T ∧ IsMinCut (π.graph G) T)
    (fun o => ¬∃ out, o = some out ∧ out.Sound G ∧ IsMinCut G out.shore ∧
      out.value = mincutValue G)
    (ε := 0) (solver_failure hq (π.graph G)) (by
      intro o ho
      push_neg at ho
      obtain ⟨T, rfl, hT⟩ := ho
      rw [RTree.eval_ofDeterministic, mass_pure]
      have hg := postprocess_good π G hS hs hT
      simp [hg])
  simpa only [_root_.add_zero] using h

/-! The following arithmetic bounds the exact source index, not a promised cost. -/

private theorem paramc_eq :
    WeightedGraph.paramc Q 3 WeightedMinCut.eps =
      2048 * (2 * Real.log (2 * (Fintype.card Q : ℝ)) + Real.log 4 +
        4 * Real.log (WeightedGraph.baseB Q)) := by
  have hB : 0 < WeightedGraph.baseB Q := by linarith [WeightedGraph.baseB_ge Q]
  unfold WeightedGraph.paramc WeightedGraph.paramδ WeightedMinCut.eps
  rw [Real.log_div (by norm_num) (Real.rpow_pos_of_pos hB _).ne', Real.log_rpow hB]
  ring

theorem paramc_le (hq : 2 ≤ Fintype.card Q) :
    WeightedGraph.paramc Q 3 WeightedMinCut.eps ≤
      14336 * Real.log (WeightedGraph.baseB Q) := by
  have hq : (2 : ℝ) ≤ Fintype.card Q := by exact_mod_cast hq
  have hqB : 2 * (Fintype.card Q : ℝ) ≤ WeightedGraph.baseB Q := by
    dsimp [WeightedGraph.baseB]; linarith
  have h4B : (4 : ℝ) ≤ WeightedGraph.baseB Q := by
    dsimp [WeightedGraph.baseB]; linarith
  have h1 := Real.log_le_log (show 0 < 2 * (Fintype.card Q : ℝ) by positivity) hqB
  have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4B
  rw [paramc_eq]
  linarith

theorem source_log_le (q : ℕ) (hq : 2 ≤ q) :
    (Nat.log 2 (2 * q ^ 4) : ℝ) ≤ 9 * Real.log (2 * (q : ℝ) + 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl20 : 0 < Real.log (2 : ℝ) := by linarith
  have hlog := Real.natLog_le_logb (2 * q ^ 4) 2
  norm_num only [Nat.cast_ofNat] at hlog
  have he : Real.logb 2 (2 * q ^ 4 : ℕ) = 1 + 4 * (Real.log (q : ℝ) / Real.log 2) := by
    rw [Real.logb]
    push_cast
    rw [Real.log_mul (by norm_num) (pow_pos hq0 4).ne', Real.log_pow]
    field_simp [hl20.ne'] <;> ring
  rw [he] at hlog
  have hratio : Real.log (q : ℝ) / Real.log 2 ≤ 2 * Real.log q := by
    rw [div_le_iff₀ (by linarith : 0 < Real.log 2)]
    nlinarith [mul_nonneg hlogq (sub_nonneg.mpr hl2.le)]
  have hbase := Schedule.log_base_ge_one q hq
  have hle := Real.log_le_log hq0 (show (q : ℝ) ≤ 2 * q + 2 by linarith)
  linarith

theorem source_budget_le (hq : 2 ≤ Fintype.card Q) :
    (budget Q : ℝ) ≤ 5000000 * Fintype.card Q *
      (Real.log (WeightedGraph.baseB Q)) ^ 2 := by
  let q := Fintype.card Q
  let u := Real.log (WeightedGraph.baseB Q)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hu1 : 1 ≤ u := Schedule.log_base_ge_one q hq
  have hu0 : 0 ≤ u := by linarith
  have hL : (searchDepth Q : ℝ) ≤ 3 * u := Schedule.clog_le_three_log_base q hq
  have hD : (residualDrawCost (searchDepth Q) (searchDepth Q) : ℝ) ≤ 63 * u := by
    dsimp [residualDrawCost]
    push_cast
    linarith
  have hK : (approxKruskalBudget Q : ℝ) ≤ 29 * q * u := by
    have h := approxKruskalBudget_le (V := Q)
    have h' : (approxKruskalBudget Q : ℝ) ≤
        q * (6 * (searchDepth Q : ℝ) + 11) := by exact_mod_cast h
    calc
      _ ≤ (q : ℝ) * (6 * (searchDepth Q : ℝ) + 11) := h'
      _ ≤ q * (29 * u) := by gcongr; linarith
      _ = _ := by ring
  have hρ : WeightedGraph.paramρ Q 3 = 1408 * u := by
    dsimp [WeightedGraph.paramρ, u]; ring
  have hc := paramc_le (Q := Q) hq
  change WeightedGraph.paramc Q 3 WeightedMinCut.eps ≤ 14336 * u at hc
  have hc0 : 0 ≤ WeightedGraph.paramc Q 3 WeightedMinCut.eps := by
    rw [paramc_eq]
    have hlogq : 0 ≤ Real.log (2 * (Fintype.card Q : ℝ)) :=
      Real.log_nonneg (by change 1 ≤ 2 * (q : ℝ); linarith)
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    change 0 ≤ 2048 * (2 * Real.log (2 * (Fintype.card Q : ℝ)) + Real.log 4 + 4 * u)
    positivity
  have hsub : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
  have hlog := source_log_le q hq
  change (Nat.log 2 (2 * q ^ 4) : ℝ) ≤ 9 * u at hlog
  have husq : u ≤ u ^ 2 := by nlinarith
  have hu1sq : 1 ≤ u ^ 2 := by nlinarith
  have hqu : (q : ℝ) * u ≤ q * u ^ 2 := mul_le_mul_of_nonneg_left husq hq0
  have hq : (q : ℝ) ≤ q * u ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1sq hq0
  have htwo : (2 : ℝ) ≤ q * u ^ 2 := hq2.trans hq
  have hest0 : 0 ≤ WeightedGraph.estBound Q (WeightedGraph.paramρ Q 3) := by
    unfold WeightedGraph.estBound
    rw [hρ]
    positivity
  have hest : WeightedGraph.estBound Q (WeightedGraph.paramρ Q 3) ≤
      709651 * q * u ^ 2 := by
    unfold WeightedGraph.estBound
    rw [hρ]
    calc
      _ ≤ 2 * (q : ℝ) * (9 * u) + (63 * u) * (8 * (1408 * u) * q) + q := by
        gcongr
      _ ≤ 709651 * q * u ^ 2 := by nlinarith
  have hout0 : 0 ≤ WeightedGraph.outBound Q (WeightedGraph.paramc Q 3 WeightedMinCut.eps) := by
    unfold WeightedGraph.outBound
    positivity
  have hout : WeightedGraph.outBound Q (WeightedGraph.paramc Q 3 WeightedMinCut.eps) ≤
      3612736 * q * u ^ 2 := by
    unfold WeightedGraph.outBound
    calc
      _ ≤ (q : ℝ) + (63 * u) * (4 * (14336 * u) * q + q) := by gcongr
      _ ≤ 3612736 * q * u ^ 2 := by nlinarith
  have hcap : (WeightedGraph.capQ Q (WeightedGraph.paramρ Q 3)
      (WeightedGraph.paramc Q 3 WeightedMinCut.eps) : ℝ) ≤ 4322418 * q * u ^ 2 := by
    have he := (Nat.ceil_lt_add_one hest0).le
    have ho := (Nat.ceil_lt_add_one hout0).le
    unfold WeightedGraph.capQ
    push_cast
    nlinarith
  have hden : (1 / 5 : ℝ) ≤ Real.log (45 / 34) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 34 / 45)
    have he : (34 / 45 : ℝ) = (45 / 34)⁻¹ := by norm_num
    rw [he, Real.log_inv] at h
    linarith
  have hr : (WeightedMinCut.rounds Q 3 : ℝ) ≤ 16 * u := by
    have hden0 : 0 < Real.log (45 / 34 : ℝ) := by linarith
    have hfrac : 3 * u / Real.log (45 / 34) ≤ 15 * u := by
      rw [div_le_iff₀ hden0]
      nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hden)]
    have hceil := (Nat.ceil_lt_add_one
      (div_nonneg (mul_nonneg (show (0 : ℝ) ≤ 3 by norm_num) hu0) hden0.le)).le
    change (WeightedMinCut.rounds Q 3 : ℝ) ≤ _ at hceil
    linarith
  have ht : (WeightedMinCut.treeBudget Q : ℝ) ≤ 288 * q * u := by
    unfold WeightedMinCut.treeBudget
    push_cast
    change 72 * (q : ℝ) * ((searchDepth Q : ℝ) + 1) ≤ _
    calc
      _ ≤ 72 * (q : ℝ) * (4 * u) := by gcongr; linarith
      _ = _ := by ring
  have hrt : (WeightedMinCut.rounds Q 3 : ℝ) * WeightedMinCut.treeBudget Q ≤
      4608 * q * u ^ 2 := by
    calc
      _ ≤ (16 * u) * (288 * q * u) := by gcongr
      _ = _ := by ring
  unfold budget
  push_cast
  change _ ≤ 5000000 * q * u ^ 2
  nlinarith [mul_nonneg hq0 (sq_nonneg u)]

theorem program_cost_log (π : PublicQuotient V Q) (hq : 2 ≤ Fintype.card Q)
    (read : Finset V → ℝ) {out : Option (CutResult V) × ℕ}
    (hout : out ∈ (RTree.run read (program π hq)).support) :
    (out.2 : ℝ) ≤ 5000000 * Fintype.card Q *
      (Real.log (WeightedGraph.baseB Q)) ^ 2 + 1 := by
  have hc : (out.2 : ℝ) ≤ (budget Q : ℝ) + 1 := by
    exact_mod_cast program_cost π hq read hout
  have hb := source_budget_le hq
  linarith

theorem program_cost_high (π : PublicQuotient V Q) (d : ℕ)
    (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (h : Schedule.HighGuard (Fintype.card V) d (Fintype.card Q))
    (read : Finset V → ℝ) {out : Option (CutResult V) × ℕ}
    (hout : out ∈ (RTree.run read (program π h.2.1)).support) :
    (out.2 : ℝ) ≤ (Schedule.weightedCoefficient : ℝ) * Fintype.card V + 1 := by
  have hc := program_cost_log π h.2.1 read hout
  have hb := Schedule.high_weighted_envelope _ _ _ hn h
  change 5000000 * Fintype.card Q * (Real.log (WeightedGraph.baseB Q)) ^ 2 ≤
    (Schedule.weightedCoefficient : ℝ) * Fintype.card V at hb
  linarith

theorem source_budget_high (d : ℕ)
    (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (h : Schedule.HighGuard (Fintype.card V) d (Fintype.card Q)) :
    budget Q ≤ Schedule.weightedCoefficient * Fintype.card V := by
  have hb := (source_budget_le h.2.1).trans (Schedule.high_weighted_envelope _ _ _ hn h)
  exact_mod_cast hb

/-- A fixed all-answer cap, with every size test evaluated from public data. -/
def guardedProgram (π : PublicQuotient V Q) (d : ℕ) :
    RTree (Finset V) ℝ (Option (CutResult V))
      (Schedule.weightedCoefficient * Fintype.card V + 1) :=
  if hn : Schedule.sizeCutoff ≤ Fintype.card V then
    if h : Schedule.HighGuard (Fintype.card V) d (Fintype.card Q) then
      (program π h.2.1).weaken (Nat.add_le_add_right (source_budget_high d hn h) 1)
    else RTree.pure (PMF.pure none)
  else RTree.pure (PMF.pure none)

theorem guardedProgram_cost (π : PublicQuotient V Q) (d : ℕ)
    (read : Finset V → ℝ) {out : Option (CutResult V) × ℕ}
    (hout : out ∈ (RTree.run read (guardedProgram π d)).support) :
    out.2 ≤ Schedule.weightedCoefficient * Fintype.card V + 1 :=
  RTree.cost_le _ read hout

theorem guardedProgram_eval (π : PublicQuotient V Q) (d : ℕ)
    (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (h : Schedule.HighGuard (Fintype.card V) d (Fintype.card Q))
    (read : Finset V → ℝ) :
    (guardedProgram π d).eval read = (program π h.2.1).eval read := by
  simp only [guardedProgram, dif_pos hn, dif_pos h, RTree.eval_weaken]

theorem guardedProgram_sound (π : PublicQuotient V Q) (d : ℕ)
    (G : WeightedGraph V) {out : CutResult V}
    (hout : some out ∈ ((guardedProgram π d).eval G.cut).support) : out.Sound G := by
  unfold guardedProgram at hout
  split_ifs at hout with hn h
  · rw [RTree.eval_weaken] at hout
    exact program_sound π h.2.1 G hout
  · simp [RTree.eval_pure] at hout
  · simp [RTree.eval_pure] at hout

theorem guardedProgram_failure (π : PublicQuotient V Q) (d : ℕ)
    (hn : Schedule.sizeCutoff ≤ Fintype.card V)
    (h : Schedule.HighGuard (Fintype.card V) d (Fintype.card Q))
    (G : WeightedGraph V) {S : Finset V} (hS : IsMinCut G S)
    (hs : RespectsBlocks π.map S) :
    mass ((guardedProgram π d).eval G.cut)
      (fun o => ¬∃ out, o = some out ∧ out.Sound G ∧ IsMinCut G out.shore ∧
        out.value = mincutValue G) ≤ ENNReal.ofReal (1 / 100) := by
  rw [guardedProgram_eval π d hn h]
  exact program_failure π h.2.1 G hS hs

#print axioms source_cost
#print axioms program_cost
#print axioms program_sound
#print axioms postprocess_good
#print axioms solver_failure
#print axioms program_failure
#print axioms source_budget_le
#print axioms program_cost_log
#print axioms program_cost_high
#print axioms source_budget_high
#print axioms guardedProgram_cost
#print axioms guardedProgram_sound
#print axioms guardedProgram_failure

end
end CutQueryComplexity.StarContraction2022.WeightedAdapter
