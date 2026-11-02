import CutQueryComplexity.DirectedUnitST.Endpoint.Main

/-! # The terminal-independent representation built by the deterministic endpoint

`representationTree n` is the prefix of the endpoint tree that precedes the terminals:
preparation followed by the capped discrepancy repair. On every simple input it returns a
public state realizing an integral representation with the original outgoing-cut function.
In that state every unknown pair carries its pair total in the public direction, and every
other pair has a learned residual capacity. The prefix fits the endpoint's query cap, and
the endpoint program runs its terminal stage on the returned state.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Endpoint

open Finset Certificate DirectedCertificate

noncomputable section

def representationBudget (n : ℕ) : ℕ :=
  Preparation.queryBudget n (Preparation.cubicScale n) +
    Blocking.repairBudget (Fin n) (supplyCap n)

/-- Preparation and discrepancy repair. Neither depends on the terminals. -/
def representationTree (n : ℕ) :
    DTree (Finset (Fin n)) ℕ (Option (Blocking.SolveResult (Fin n))) (representationBudget n) :=
  (Preparation.fiveThirdsIntegralProg n).bind fun out =>
    Blocking.cappedDiscrepancyRepairTreeNat out.state
      (Blocking.integerDemand out.demand) (supplyCap n)

theorem representationTree_eval (n : ℕ) (read : Finset (Fin n) → ℕ) :
    (representationTree n).eval read =
      (Blocking.cappedDiscrepancyRepairTreeNat
        ((Preparation.fiveThirdsIntegralProg n).eval read).state
        (Blocking.integerDemand ((Preparation.fiveThirdsIntegralProg n).eval read).demand)
        (supplyCap n)).eval read :=
  DTree.eval_bind _ _ read

/-- The prefix is charged against the same public cap as the whole endpoint. -/
theorem representationTree_cost {n : ℕ} (hn : 2 ≤ n) (read : Finset (Fin n) → ℕ) :
    (representationTree n).cost read ≤ headlineQueries n := by
  have hc : (representationTree n).cost read ≤
      (Preparation.fiveThirdsIntegralProg n).cost read +
        Blocking.repairBudget (Fin n) (supplyCap n) :=
    tree_bind_cost_le _ _ read
  have hraw : (Preparation.fiveThirdsIntegralProg n).cost read + continuationBudget n ≤
      headlineQueries n := by
    rw [continuationBudget_eq]
    apply combined_cost_le_headline hn
    simpa only [Acceleration.scheduleBits] using Preparation.fiveThirdsIntegralProg_cost hn read
  have hr : Blocking.repairBudget (Fin n) (supplyCap n) ≤ continuationBudget n :=
    Nat.le_add_right _ _
  omega

theorem representationTree_cost_real {n : ℕ} (hn : 2 ≤ n) (read : Finset (Fin n) → ℕ) :
    ((representationTree n).cost read : ℝ) ≤
      2049 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2 := by
  have hc : ((representationTree n).cost read : ℝ) ≤ (headlineQueries n : ℝ) :=
    Nat.cast_le.mpr (representationTree_cost hn read)
  have hceil : (headlineQueries n : ℝ) ≤
      2048 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ (5 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  have hl := logScale_one_le n
  have hl2 : (1 : ℝ) ≤ (logScale n : ℝ) ^ 2 := by nlinarith
  have hone := one_le_mul_of_one_le_of_one_le hp hl2
  nlinarith

/-- The represented graph is the residual of the repair flow. Its cut function is derived
from the returned flow; no cut-equivalence premise is supplied. -/
theorem representationTree_correct {n : ℕ} (hn : 2 ≤ n) (G : DiGraph (Fin n))
    (hG : G.Simple) :
    ∃ result, (representationTree n).eval G.out = some result ∧
      ∃ K : WeightedDiGraph (Fin n),
        result.network.internal.Realizes (Preparation.realGraph G) K ∧
        (∀ u v, ∃ m : ℕ, K.c u v = m) ∧
        ∀ S : Finset (Fin n), K.out S = (G.out S : ℝ) := by
  obtain ⟨H, h⟩ := Preparation.fiveThirdsIntegralProg_correct G hG hn
  set out := (Preparation.fiveThirdsIntegralProg n).eval G.out
  have hq (v : Fin n) : (Blocking.integerDemand out.demand v : ℝ) = out.demand v :=
    Blocking.integerDemand_cast out.demand h.demand_integer v
  have hR : (Blocking.totalSupply (Blocking.integerDemand out.demand) : ℝ) ≤
      (n : ℝ) ^ 2 := by
    rw [Blocking.totalSupply_integerDemand out.demand h.demand_integer]
    nlinarith [h.coarse_volume, sq_nonneg (n : ℝ)]
  obtain ⟨f, hf, hdiv⟩ := h.feasible
  have hdivq (v : Fin n) : netOut f v = (Blocking.integerDemand out.demand v : ℝ) :=
    (hdiv v).trans (hq v).symm
  obtain ⟨repair, he, hfeas, hnet, hreal, hint, -⟩ :=
    Blocking.cappedDiscrepancyRepairTree_continue (Preparation.realGraph G) H out.state
      h.realizes (Blocking.integerDemand out.demand) h.integral h.pairBounded
      (by simpa only [Fintype.card_fin] using hR) f hf hdivq
      (supplyCap n) (prepared_supply_le_cap h)
  have hnetDemand (v : Fin n) : netOut (Blocking.internalFlow repair) v = out.demand v :=
    (hnet v).trans (hq v)
  have hread : (fun S : Finset (Fin n) => (G.out S : ℝ)) =
      (Preparation.realGraph G).out := funext fun S => (Preparation.realGraph_out G S).symm
  refine ⟨repair, ?_, Repair.residual H _ hfeas, hreal, hint,
    h.restores_cuts _ hfeas hnetDemand⟩
  rw [representationTree_eval, Blocking.cappedDiscrepancyRepairTreeNat_eval, hread]
  exact he

/-- The endpoint program of `exists_unitST_query_program` runs its terminal stage on the
state returned by `representationTree`. -/
theorem unitSTNatTree_eval_representation {n : ℕ} (hn : 2 ≤ n) (s t : Fin n)
    (read : Finset (Fin n) → ℕ) :
    (unitSTNatTree n s t).eval read =
      ((terminalAfterRepair n s t ((representationTree n).eval read)).eval read).map
        fun result => (result.shore, ⌊result.value⌋₊) := by
  have hraw : (rawUnitSTTree n s t).eval read =
      (repairAndSolve n s t ((Preparation.fiveThirdsIntegralProg n).eval read)).eval read :=
    DTree.eval_bind _ _ read
  have hcont (out : Preparation.Output n) : (repairAndSolve n s t out).eval read =
      (terminalAfterRepair n s t ((Blocking.cappedDiscrepancyRepairTreeNat out.state
        (Blocking.integerDemand out.demand) (supplyCap n)).eval read)).eval read :=
    DTree.eval_bind _ _ read
  simp only [unitSTNatTree, DTree.eval_map, unitSTTree_eval hn, hraw, hcont,
    representationTree_eval]

/-- One public tree, fixed by n before the hidden graph and within the endpoint's cap,
constructs an integral representation with the cut function of the input. Unknown pairs
are pure in a public direction and every other pair has a learned capacity. The endpoint
program continues from this tree's output, so the terminals are chosen afterwards. -/
theorem exists_unitST_representation {n : ℕ} (hn : 2 ≤ n) :
    ∃ P : DTree (Finset (Fin n)) ℕ (Option (Blocking.SolveResult (Fin n)))
        (representationBudget n),
      (∀ read : Finset (Fin n) → ℕ, P.cost read ≤ headlineQueries n ∧
        (P.cost read : ℝ) ≤ 2049 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2) ∧
      (∀ G : DiGraph (Fin n), G.Simple →
        ∃ result, P.eval G.out = some result ∧
          ∃ K : WeightedDiGraph (Fin n),
            result.network.internal.Realizes (Preparation.realGraph G) K ∧
            (∀ u v, ∃ m : ℕ, K.c u v = m) ∧
            ∀ S : Finset (Fin n), K.out S = (G.out S : ℝ)) ∧
      ∀ (s t : Fin n) (read : Finset (Fin n) → ℕ),
        (unitSTNatTree n s t).eval read =
          ((terminalAfterRepair n s t (P.eval read)).eval read).map
            fun result => (result.shore, ⌊result.value⌋₊) :=
  ⟨representationTree n,
    fun read => ⟨representationTree_cost hn read, representationTree_cost_real hn read⟩,
    fun G hG => representationTree_correct hn G hG,
    fun s t read => unitSTNatTree_eval_representation hn s t read⟩

end
end CutQueryComplexity.DirectedUnitST.Endpoint

#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.representationTree_eval
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.representationTree_cost
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.representationTree_cost_real
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.representationTree_correct
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.unitSTNatTree_eval_representation
#print axioms CutQueryComplexity.DirectedUnitST.Endpoint.exists_unitST_representation
