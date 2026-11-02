import CutQueryComplexity.DirectedUnitST.Endpoint.Budget
import CutQueryComplexity.DirectedUnitST.Endpoint.Program
import CutQueryComplexity.DirectedUnitST.Preparation.Main
import CutQueryComplexity.DirectedUnitST.Blocking.Main

/-! # Deterministic directed unit terminal mincut by outgoing-cut queries

The tree is fixed by the vertex count and terminals before the hidden graph.
It prepares a public integral representation, routes its public discrepancy
under a fixed budget, and solves the terminal problem on the returned state.
The terminal tree already includes the original shore-value query.

All answer histories obey the same public cap. Honest-input supply estimates
are used only to prove that the discrepancy repair is not truncated. Hidden
represented graphs and feasible flows occur only in the correctness proofs.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Endpoint

open Finset Certificate DirectedCertificate

noncomputable section

/-- Identify the operational budget with the independently checked arithmetic. -/
theorem repairBudget_fin (n R : ℕ) :
    Blocking.repairBudget (Fin n) R = repairQueries n R := by
  simp only [Blocking.repairBudget, repairQueries, Blocking.repairBound,
    repairFormula, Blocking.node_card, Fintype.card_fin,
    Blocking.edgeQueryBound, edgeFactor, Nat.cast_add, Nat.cast_ofNat]

def terminalStageBudget (n : ℕ) : ℕ :=
  Blocking.repairBudget (Fin n) (Fintype.card (Fin n)) + 1

def continuationBudget (n : ℕ) : ℕ :=
  Blocking.repairBudget (Fin n) (supplyCap n) + terminalStageBudget n

def rawBudget (n : ℕ) : ℕ :=
  Preparation.queryBudget n (Preparation.cubicScale n) + continuationBudget n

theorem continuationBudget_eq (n : ℕ) :
    continuationBudget n = repairQueries n (supplyCap n) + (repairQueries n n + 1) := by
  simp only [continuationBudget, terminalStageBudget, Fintype.card_fin, repairBudget_fin]

/-- The returned public residual state selects the second solve. -/
def terminalAfterRepair (n : ℕ) (s t : Fin n) :
    Option (Blocking.SolveResult (Fin n)) →
      DTree (Finset (Fin n)) ℕ (Option (Blocking.TerminalResult (Fin n)))
        (terminalStageBudget n)
  | none => DTree.pure none
  | some result => Blocking.terminalTreeNat result.network.internal s t

/-- The reported demand cannot change either continuation's public budget. -/
def repairAndSolve (n : ℕ) (s t : Fin n) (out : Preparation.Output n) :
    DTree (Finset (Fin n)) ℕ (Option (Blocking.TerminalResult (Fin n)))
      (continuationBudget n) :=
  (Blocking.cappedDiscrepancyRepairTreeNat out.state
    (Blocking.integerDemand out.demand) (supplyCap n)).bind (terminalAfterRepair n s t)

def rawUnitSTTree (n : ℕ) (s t : Fin n) :
    DTree (Finset (Fin n)) ℕ (Option (Blocking.TerminalResult (Fin n))) (rawBudget n) :=
  (Preparation.fiveThirdsIntegralProg n).bind (repairAndSolve n s t)

/-- The sharp preparation estimate holds for every oracle. The continuation
indices, including the cap on an arbitrary reported demand, are fixed by n. -/
theorem rawUnitSTTree_cost {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    (read : Finset (Fin n) → ℕ) :
    (rawUnitSTTree n s t).cost read ≤ headlineQueries n := by
  have hc : (rawUnitSTTree n s t).cost read ≤
      (Preparation.fiveThirdsIntegralProg n).cost read + continuationBudget n :=
    tree_bind_cost_le (Preparation.fiveThirdsIntegralProg n) (repairAndSolve n s t) read
  rw [continuationBudget_eq] at hc
  apply hc.trans
  apply combined_cost_le_headline hn
  simpa only [Acceleration.scheduleBits] using Preparation.fiveThirdsIntegralProg_cost hn read

/-- The final public tree has a budget depending only on n. -/
def unitSTTree (n : ℕ) (s t : Fin n) :
    DTree (Finset (Fin n)) ℕ (Option (Blocking.TerminalResult (Fin n))) (headlineQueries n) :=
  cappedOptionTree (rawUnitSTTree n s t) (headlineQueries n)

theorem unitSTTree_cost (n : ℕ) (s t : Fin n) (read : Finset (Fin n) → ℕ) :
    (unitSTTree n s t).cost read ≤ headlineQueries n := DTree.cost_le _ _

/-- Even an inconsistent oracle's raw execution fits the outer cap. -/
theorem unitSTTree_eval {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    (read : Finset (Fin n) → ℕ) :
    (unitSTTree n s t).eval read = (rawUnitSTTree n s t).eval read :=
  cappedOptionTree_eval _ _ read (rawUnitSTTree_cost hn s t read)

theorem unitSTTree_cost_real {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    (read : Finset (Fin n) → ℕ) :
    ((unitSTTree n s t).cost read : ℝ) ≤
      2049 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2 := by
  have hc : ((unitSTTree n s t).cost read : ℝ) ≤ (headlineQueries n : ℝ) :=
    Nat.cast_le.mpr (unitSTTree_cost n s t read)
  have hceil : (headlineQueries n : ℝ) ≤
      2048 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ (5 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  have hl := logScale_one_le n
  have hl2 : (1 : ℝ) ≤ (logScale n : ℝ) ^ 2 := by nlinarith
  have hone := one_le_mul_of_one_le_of_one_le hp hl2
  nlinarith

/-- Honest supply justifies nontruncation, separately from every-oracle cost. -/
theorem prepared_supply_le_cap {n : ℕ} {G : DiGraph (Fin n)}
    {H : WeightedDiGraph (Fin n)} {out : Preparation.Output n}
    (h : Preparation.PreparationSpec G H out) :
    Blocking.totalSupply (Blocking.integerDemand out.demand) ≤ supplyCap n := by
  have he := Blocking.totalSupply_integerDemand out.demand h.demand_integer
  apply supply_le_cap
  · rw [he]
    nlinarith [h.coarse_volume, sq_nonneg (n : ℝ)]
  · rw [he]
    exact h.volume

/-- Compose the actual discrepancy-repair output with the actual second solve.
Cut equivalence is derived from the returned flow, not supplied as a premise. -/
theorem repairAndSolve_correct {n : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (out : Preparation.Output n) (H : WeightedDiGraph (Fin n))
    (h : Preparation.PreparationSpec G H out) (s t : Fin n) (hst : s ≠ t) :
    ∃ result, (repairAndSolve n s t out).eval G.out = some result ∧
      s ∈ result.shore ∧ t ∉ result.shore ∧ result.value = (G.out result.shore : ℝ) ∧
      ∀ W : Finset (Fin n), s ∈ W → t ∉ W → G.out result.shore ≤ G.out W := by
  have hq (v : Fin n) : (Blocking.integerDemand out.demand v : ℝ) = out.demand v :=
    Blocking.integerDemand_cast out.demand h.demand_integer v
  have hR : (Blocking.totalSupply (Blocking.integerDemand out.demand) : ℝ) ≤
      (n : ℝ) ^ 2 := by
    rw [Blocking.totalSupply_integerDemand out.demand h.demand_integer]
    nlinarith [h.coarse_volume, sq_nonneg (n : ℝ)]
  obtain ⟨f, hf, hdiv⟩ := h.feasible
  have hdivq (v : Fin n) : netOut f v = (Blocking.integerDemand out.demand v : ℝ) :=
    (hdiv v).trans (hq v).symm
  obtain ⟨repair, he, hfeas, hnet, hreal, hint, hcap⟩ :=
    Blocking.cappedDiscrepancyRepairTree_continue (Preparation.realGraph G) H out.state
      h.realizes (Blocking.integerDemand out.demand) h.integral h.pairBounded
      (by simpa only [Fintype.card_fin] using hR) f hf hdivq
      (supplyCap n) (prepared_supply_le_cap h)
  have hnetDemand (v : Fin n) : netOut (Blocking.internalFlow repair) v = out.demand v :=
    (hnet v).trans (hq v)
  have hcuts (W : Finset (Fin n)) :
      (Repair.residual H (Blocking.internalFlow repair) hfeas).out W =
        (Preparation.realGraph G).out W :=
    (h.restores_cuts _ hfeas hnetDemand W).trans (Preparation.realGraph_out G W).symm
  have hunit (u v : Fin n) : (Preparation.realGraph G).c u v ≤ 1 := by
    change (G.c u v : ℝ) ≤ 1
    exact_mod_cast hG u v
  obtain ⟨result, hterm, hs, ht, hvalue, hmin⟩ :=
    Blocking.terminalTree_unit_correct (Preparation.realGraph G)
      (Repair.residual H (Blocking.internalFlow repair) hfeas) repair.network.internal
      hreal hint hcap hcuts hunit s t hst
  have hread : (fun S : Finset (Fin n) => (G.out S : ℝ)) =
      (Preparation.realGraph G).out := funext fun S => (Preparation.realGraph_out G S).symm
  have heNat : (Blocking.cappedDiscrepancyRepairTreeNat out.state
      (Blocking.integerDemand out.demand) (supplyCap n)).eval G.out = some repair := by
    rw [Blocking.cappedDiscrepancyRepairTreeNat_eval, hread]
    exact he
  have htermNat : (Blocking.terminalTreeNat repair.network.internal s t).eval G.out =
      some result := by
    rw [Blocking.terminalTreeNat_eval, hread]
    exact hterm
  refine ⟨result, ?_, hs, ht, ?_, ?_⟩
  · change ((Blocking.cappedDiscrepancyRepairTreeNat out.state
      (Blocking.integerDemand out.demand) (supplyCap n)).bind
        (terminalAfterRepair n s t)).eval G.out = some result
    rw [DTree.eval_bind, heNat]
    exact htermNat
  · simpa only [Preparation.realGraph_out] using hvalue
  · intro W hWs hWt
    simpa only [Preparation.realGraph_out, Nat.cast_le] using hmin W hWs hWt

theorem rawUnitSTTree_correct {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    (G : DiGraph (Fin n)) (hG : G.Simple) :
    ∃ result, (rawUnitSTTree n s t).eval G.out = some result ∧
      s ∈ result.shore ∧ t ∉ result.shore ∧ result.value = (G.out result.shore : ℝ) ∧
      ∀ W : Finset (Fin n), s ∈ W → t ∉ W → G.out result.shore ≤ G.out W := by
  obtain ⟨H, h⟩ := Preparation.fiveThirdsIntegralProg_correct G hG hn
  obtain ⟨result, he, hs, ht, hvalue, hmin⟩ :=
    repairAndSolve_correct G hG ((Preparation.fiveThirdsIntegralProg n).eval G.out) H h s t hst
  refine ⟨result, ?_, hs, ht, hvalue, hmin⟩
  change ((Preparation.fiveThirdsIntegralProg n).bind (repairAndSolve n s t)).eval G.out =
    some result
  exact (DTree.eval_bind (Preparation.fiveThirdsIntegralProg n) (repairAndSolve n s t) G.out).trans he

/-- No representation, transshipment, or algorithmic guarantee is assumed here:
all are constructed by the public tree and its checked component proofs. -/
theorem unitSTTree_correct {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    (G : DiGraph (Fin n)) (hG : G.Simple) :
    ∃ result, (unitSTTree n s t).eval G.out = some result ∧
      s ∈ result.shore ∧ t ∉ result.shore ∧ result.value = (G.out result.shore : ℝ) ∧
      ∀ W : Finset (Fin n), s ∈ W → t ∉ W → G.out result.shore ≤ G.out W := by
  simpa only [unitSTTree_eval hn s t G.out] using rawUnitSTTree_correct hn s t hst G hG

/-- Convert the already queried exact value to Nat without another query. -/
def unitSTNatTree (n : ℕ) (s t : Fin n) :
    DTree (Finset (Fin n)) ℕ (Option (Finset (Fin n) × ℕ)) (headlineQueries n) :=
  (unitSTTree n s t).map (Option.map fun result => (result.shore, ⌊result.value⌋₊))

theorem unitSTNatTree_cost (n : ℕ) (s t : Fin n) (read : Finset (Fin n) → ℕ) :
    (unitSTNatTree n s t).cost read ≤ headlineQueries n := DTree.cost_le _ _

theorem unitSTNatTree_cost_real {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    (read : Finset (Fin n) → ℕ) :
    ((unitSTNatTree n s t).cost read : ℝ) ≤
      2049 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2 := by
  have he : (unitSTNatTree n s t).cost read = (unitSTTree n s t).cost read := by
    simp only [unitSTNatTree, DTree.cost, DTree.run_map]
  rw [he]
  exact unitSTTree_cost_real hn s t read

theorem unitSTNatTree_correct {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    (G : DiGraph (Fin n)) (hG : G.Simple) :
    ∃ S : Finset (Fin n), (unitSTNatTree n s t).eval G.out = some (S, G.out S) ∧
      s ∈ S ∧ t ∉ S ∧ ∀ W : Finset (Fin n), s ∈ W → t ∉ W → G.out S ≤ G.out W := by
  obtain ⟨result, he, hs, ht, hvalue, hmin⟩ := unitSTTree_correct hn s t hst G hG
  refine ⟨result.shore, ?_, hs, ht, hmin⟩
  simp only [unitSTNatTree, DTree.eval_map, he, Option.map_some, hvalue, Nat.floor_natCast]

/-- One deterministic program is chosen before the hidden input. Its fixed cap
holds for every oracle, while every simple directed graph yields an exact
minimum separating shore and its original natural outgoing-cut value. -/
theorem exists_unitST_query_program {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t) :
    ∃ T : DTree (Finset (Fin n)) ℕ (Option (Finset (Fin n) × ℕ)) (headlineQueries n),
      (∀ read : Finset (Fin n) → ℕ, T.cost read ≤ headlineQueries n ∧
        (T.cost read : ℝ) ≤ 2049 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2) ∧
      ∀ G : DiGraph (Fin n), G.Simple →
        ∃ S : Finset (Fin n), T.eval G.out = some (S, G.out S) ∧
          s ∈ S ∧ t ∉ S ∧ ∀ W : Finset (Fin n), s ∈ W → t ∉ W → G.out S ≤ G.out W := by
  refine ⟨unitSTNatTree n s t, ?_, ?_⟩
  · intro read
    exact ⟨unitSTNatTree_cost n s t read, unitSTNatTree_cost_real hn s t read⟩
  · intro G hG
    exact unitSTNatTree_correct hn s t hst G hG

end
end CutQueryComplexity.DirectedUnitST.Endpoint

#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.repairBudget_fin
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.rawUnitSTTree_cost
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.unitSTTree_eval
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.prepared_supply_le_cap
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.repairAndSolve_correct
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.unitSTTree_correct
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.unitSTNatTree_cost_real
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.unitSTNatTree_correct
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.exists_unitST_query_program
