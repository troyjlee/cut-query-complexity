import CutQueryComplexity.GHReduction.Randomized.SourcePivots
import CutQueryComplexity.GHReduction.Main

/-! # Phase 3d, second part: the frontier recursion and the whole reduction

Twins of the frontier pivot round (`FrontierPivotRound`), its adaptive
execution (`FrontierExecution`), the reduction (`FrontierReduction`,
`OracleReduction`), and the top-level programs (`confidenceReduction`,
`weightedGHProgram`). The initial sparsifier is call-free and is embedded
unchanged with `CallTree.ofRTree`.

The only truncation on this path is `frontierPivotRoundCapped`, at the sharp
cap `3 * sourcePivotSharpBudget`. `frontierPivotRound_cost` is the twin's
realized-cost bound at that cap (the old `frontierPivotRound_cost`, at the
twin's charge), so neither side truncates on a supported run and the bridge
holds through the cap.

`weightedGHProgram_eq` is the end of Phase 3: for any exact family `E` with
size-regular cost and any promised graph, the twin of `weightedGHProgram` at
charge `Q` has the output law of `weightedGHProgram E`. Its budget index is
`weightedGHBudget n M b Q`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical ENNReal BigOperators
open WeightedGraph Probability OuterPivot

namespace Twin

open CallTree

section Round

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

/-- Twin of `frontierPivotCall`. -/
def frontierPivotCall (M : ℕ) (Q : ℕ → ℕ) (n samples trials guideLevels scale exponent levels : ℕ)
    (K : WeightedGraph V) (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (b : B) (hvn : Fintype.card V ≤ n) :
    CallTree V Q (Option (SourcePivotOutput (FrontierVertex p T b) levels))
      (sourcePivotBudget M Q n samples trials guideLevels scale exponent levels) :=
  if 2 ≤ (fiber p b).card then
    (CallTree.contract (frontierMap p T b)
      (sourcePivotTree M Q n samples trials guideLevels scale exponent levels
        (K.contract (frontierMap p T b)) (frontierTerminals p T b)
        (frontierTerminals_nonempty p hp T b) ((frontierVertex_card_le p hp T b).trans hvn))).map some
  else up (Nat.zero_le _) (CallTree.pure (PMF.pure none))

/-- Twin of `frontierPivotRound`. -/
def frontierPivotRound (M : ℕ) (Q : ℕ → ℕ) (n samples trials guideLevels scale exponent levels : ℕ)
    (K : WeightedGraph V) (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (hvn : Fintype.card V ≤ n) :
    CallTree V Q ((b : B) → Option (SourcePivotOutput (FrontierVertex p T b) levels))
      (Fintype.card B * sourcePivotBudget M Q n samples trials guideLevels scale exponent levels) :=
  CallTree.dependentRandomTable (fun _ => none)
    (fun b => frontierPivotCall M Q n samples trials guideLevels scale exponent levels K p hp T b hvn)

/-- Twin of `frontierPivotRoundCapped`: the same sharp cap, now on the charged cost. -/
def frontierPivotRoundCapped (M : ℕ) (Q : ℕ → ℕ)
    (n samples trials guideLevels scale exponent levels : ℕ)
    (K : WeightedGraph V) (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (hvn : Fintype.card V ≤ n) :
    CallTree V Q (Option ((b : B) → Option (SourcePivotOutput (FrontierVertex p T b) levels)))
      (3 * sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels) :=
  (frontierPivotRound M Q n samples trials guideLevels scale exponent levels K p hp T hvn).truncate
    (3 * sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels)

variable {M n : ℕ} {Q QE : ℕ → ℕ}

theorem frontierPivotCall_cost_scaled (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (b : B)
    (hvn : Fintype.card V ≤ n)
    {out : Option (SourcePivotOutput (FrontierVertex p T b) levels) × ℕ}
    (hout : out ∈ (idealRun G
      (frontierPivotCall M Q n samples trials guideLevels scale exponent levels K p hp T b hvn)).support) :
    n * out.2 ≤ Fintype.card (FrontierVertex p T b) *
      sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels := by
  by_cases hactive : 2 ≤ (fiber p b).card
  · simp only [frontierPivotCall, hactive, ite_true] at hout
    apply idealRun_map_cost G _ _ n _ ?_ hout
    intro call hcall
    rw [idealRun_contract] at hcall
    exact sourcePivotTree_cost_scaled hQ samples trials guideLevels scale exponent levels
      (G.contract (frontierMap p T b)) (K.contract (frontierMap p T b))
      (frontier_contraction_promise G hG p T b) _ _ _ hcall
  · simp only [frontierPivotCall, hactive, ite_false, idealRun_up] at hout
    simp [idealRun_pure_cost G _ hout]

theorem frontierPivotRound_cost_scaled (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n)
    {out : ((b : B) → Option (SourcePivotOutput (FrontierVertex p T b) levels)) × ℕ}
    (hout : out ∈ (idealRun G
      (frontierPivotRound M Q n samples trials guideLevels scale exponent levels K p hp T hvn)).support) :
    n * out.2 ≤ Fintype.card V *
      (3 * sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels) := by
  have h := CallTree.dependentRandomTable_cost G (fun _ => none)
    (fun b => frontierPivotCall M Q n samples trials guideLevels scale exponent levels K p hp T b hvn)
    n (fun b => Fintype.card (FrontierVertex p T b) *
      sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels)
    (fun b call hcall => frontierPivotCall_cost_scaled hQ samples trials guideLevels scale exponent
      levels G K hG p hp T b hvn hcall) hout
  rw [← Finset.sum_mul] at h
  have hsum := Nat.mul_le_mul_right
    (sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels)
    (frontier_vertex_sum_le p hp T)
  exact h.trans (by simpa only [Nat.mul_assoc, Nat.mul_comm 3] using hsum)

/-- On a promised graph, every supported ideal run of the frontier round stays
within the sharp cap at the twin's charge. -/
theorem frontierPivotRound_cost (hQ : SizeRegular n Q) (hn : 0 < n)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n)
    {out : ((b : B) → Option (SourcePivotOutput (FrontierVertex p T b) levels)) × ℕ}
    (hout : out ∈ (idealRun G
      (frontierPivotRound M Q n samples trials guideLevels scale exponent levels K p hp T hvn)).support) :
    out.2 ≤ 3 * sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels :=
  cost_le_of_scaled hn hvn (frontierPivotRound_cost_scaled hQ samples trials guideLevels scale
    exponent levels G K hG p hp T hvn hout)

variable (E : CanonicalSTFamily M QE)

theorem frontierPivotCall_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (b : B)
    (hvn : Fintype.card V ≤ n) :
    interpIdeal G
        (frontierPivotCall M Q n samples trials guideLevels scale exponent levels K p hp T b hvn) =
      (GHReduction.frontierPivotCall E n samples trials guideLevels scale exponent levels
        K p hp T b hvn).eval G.cut := by
  by_cases hactive : 2 ≤ (fiber p b).card
  · simp only [frontierPivotCall, GHReduction.frontierPivotCall, hactive, ite_true]
    exact map_eq _ (contract_eq _ (sourcePivotTree_eq E hQ hQE _
      (frontier_contraction_promise G hG p T b) samples trials guideLevels scale exponent levels
      _ _ _ _))
  · simp [frontierPivotCall, GHReduction.frontierPivotCall, hactive]

theorem frontierPivotRound_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n) :
    interpIdeal G
        (frontierPivotRound M Q n samples trials guideLevels scale exponent levels K p hp T hvn) =
      (GHReduction.frontierPivotRound E n samples trials guideLevels scale exponent levels
        K p hp T hvn).eval G.cut :=
  dependentRandomTable_eq _ (fun b =>
    frontierPivotCall_eq E hQ hQE samples trials guideLevels scale exponent levels G K hG p hp T b hvn)

theorem frontierPivotRoundCapped_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE) (hn : 0 < n)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n) :
    interpIdeal G
        (frontierPivotRoundCapped M Q n samples trials guideLevels scale exponent levels K p hp T hvn) =
      (GHReduction.frontierPivotRoundCapped E n samples trials guideLevels scale exponent levels
        K p hp T hvn).eval G.cut :=
  truncate_eq
    (frontierPivotRound_eq E hQ hQE samples trials guideLevels scale exponent levels G K hG p hp T hvn)
    (fun _ hout => frontierPivotRound_cost hQ hn samples trials guideLevels scale exponent levels
      G K hG p hp T hvn hout)
    (fun _ hout => GHReduction.frontierPivotRound_cost E hQE hn samples trials guideLevels scale
      exponent levels G K hG p hp T hvn hout)

end Round

section Execution

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Twin of `frontierStateStep`. -/
def frontierStateStep (M : ℕ) (Q : ℕ → ℕ) (n samples trials guideLevels scale exponent levels : ℕ)
    (K : WeightedGraph V) (hvn : Fintype.card V ≤ n) (state : PublicFrontierState V) :
    CallTree V Q (FrontierRoundRecord V levels)
      (frontierRoundBudget M Q n samples trials guideLevels scale exponent levels) :=
  (frontierPivotRoundCapped M Q n samples trials guideLevels scale exponent levels
    K state.block state.onto state.tree hvn).map (fun result => ⟨state, result⟩)

/-- Twin of `frontierExecution`. -/
def frontierExecution (M : ℕ) (Q : ℕ → ℕ) (n samples trials guideLevels scale exponent levels : ℕ)
    (K : WeightedGraph V) (hvn : Fintype.card V ≤ n) : (fuel : ℕ) → PublicFrontierState V →
      CallTree V Q (FrontierTrace V levels)
        (fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels)
  | 0, state => up (Nat.zero_le _) (CallTree.pure (PMF.pure ⟨state, []⟩))
  | fuel + 1, state =>
      ((frontierStateStep M Q n samples trials guideLevels scale exponent levels K hvn state).bind
        (fun record => (frontierExecution M Q n samples trials guideLevels scale exponent levels
          K hvn fuel record.after).map (fun tail => ⟨tail.endState, record :: tail.records⟩))).cast
            (by rw [Nat.succ_mul]; omega)

/-- Twin of `frontierReduction`. -/
def frontierReduction (M : ℕ) (Q : ℕ → ℕ)
    (n samples trials guideLevels scale exponent levels fuel : ℕ)
    (K : WeightedGraph V) (hvn : Fintype.card V ≤ n) (r : V) :
    CallTree V Q (Option (CutTree V))
      (fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels) :=
  (frontierExecution M Q n samples trials guideLevels scale exponent levels K hvn fuel
    (initialFrontierState r)).map assembleFrontierTrace

/-- Twin of `oracleReduction`: the sparsifier, then the frontier reduction on its output. -/
def oracleReduction (M : ℕ) (Q : ℕ → ℕ)
    (confidence : ℝ) (samples trials guideLevels scale exponent levels fuel : ℕ) (r : V) :
    CallTree V Q (Option (CutTree V))
      (reductionBudget V M Q confidence samples trials guideLevels scale exponent levels fuel) :=
  (CallTree.ofRTree (Q := Q) (reductionSparsifier V confidence)).bind (fun output =>
    match output with
    | none => up (Nat.zero_le _) (CallTree.pure (PMF.pure none))
    | some K => frontierReduction M Q (Fintype.card V) samples trials guideLevels scale exponent
        levels fuel K le_rfl r)

/-- Twin of `confidenceReduction`. -/
def confidenceReduction (M : ℕ) (Q : ℕ → ℕ) (b : ℕ) (r : V) :
    CallTree V Q (Option (CutTree V)) (confidenceBudget V M Q b) :=
  oracleReduction M Q ((b + 3 : ℕ) : ℝ) (confidenceSamples M (Fintype.card V) b)
    (confidenceTrials M (Fintype.card V) b) (thresholdLevels (Fintype.card V)) (Fintype.card V)
    (confidenceExponent M (Fintype.card V) b) (thresholdLevels (Fintype.card V))
    (confidenceDepth (Fintype.card V) b) r

variable {M n : ℕ} {Q QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)

theorem frontierStateStep_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE) (hn : 0 < n)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (state : PublicFrontierState V) :
    interpIdeal G (frontierStateStep M Q n samples trials guideLevels scale exponent levels K hvn state) =
      (GHReduction.frontierStateStep E n samples trials guideLevels scale exponent levels
        K hvn state).eval G.cut :=
  map_eq _ (frontierPivotRoundCapped_eq E hQ hQE hn samples trials guideLevels scale exponent levels
    G K hG state.block state.onto state.tree hvn)

theorem frontierExecution_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE) (hn : 0 < n)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n) (fuel : ℕ)
    (state : PublicFrontierState V) :
    interpIdeal G (frontierExecution M Q n samples trials guideLevels scale exponent levels
        K hvn fuel state) =
      (GHReduction.frontierExecution E n samples trials guideLevels scale exponent levels
        K hvn fuel state).eval G.cut := by
  induction fuel generalizing state with
  | zero => simp [frontierExecution, GHReduction.frontierExecution]
  | succ fuel ih =>
      simp only [frontierExecution, GHReduction.frontierExecution, interpIdeal_cast,
        RTree.eval_cast]
      exact bind_eq (frontierStateStep_eq E hQ hQE hn samples trials guideLevels scale exponent
        levels G K hG hvn state) (fun record _ => map_eq _ (ih _))

theorem frontierReduction_eq (hQ : SizeRegular n Q) (hQE : SizeRegular n QE) (hn : 0 < n)
    (samples trials guideLevels scale exponent levels fuel : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n) (r : V) :
    interpIdeal G (frontierReduction M Q n samples trials guideLevels scale exponent levels fuel
        K hvn r) =
      (GHReduction.frontierReduction E n samples trials guideLevels scale exponent levels fuel
        K hvn r).eval G.cut :=
  map_eq _ (frontierExecution_eq E hQ hQE hn samples trials guideLevels scale exponent levels
    G K hG hvn fuel _)

theorem oracleReduction_eq (hQ : SizeRegular (Fintype.card V) Q)
    (hQE : SizeRegular (Fintype.card V) QE)
    (confidence : ℝ) (samples trials guideLevels scale exponent levels fuel : ℕ) (r : V)
    (G : WeightedGraph V) (hG : InputPromise M G) :
    interpIdeal G (oracleReduction M Q confidence samples trials guideLevels scale exponent levels
        fuel r) =
      (GHReduction.oracleReduction E confidence samples trials guideLevels scale exponent levels
        fuel r).eval G.cut := by
  have : Nonempty V := ⟨r⟩
  refine bind_eq (interpIdeal_ofRTree G _) (fun output _ => ?_)
  cases output with
  | none => simp
  | some K =>
      exact frontierReduction_eq E hQ hQE Fintype.card_pos samples trials guideLevels scale
        exponent levels fuel G K hG le_rfl r

theorem confidenceReduction_eq (hQ : SizeRegular (Fintype.card V) Q)
    (hQE : SizeRegular (Fintype.card V) QE) (b : ℕ) (r : V)
    (G : WeightedGraph V) (hG : InputPromise M G) :
    interpIdeal G (confidenceReduction M Q b r) =
      (GHReduction.confidenceReduction E b r).eval G.cut :=
  oracleReduction_eq E hQ hQE _ _ _ _ _ _ _ _ r G hG

end Execution

section Top

attribute [local irreducible] RTree reductionPolynomialConstant confidenceBudget

/-- Twin of `weightedGHProgram`, at charge `Q`, with the same budget index. -/
def weightedGHProgram (M : ℕ) (Q : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n) (b : ℕ) :
    CallTree (Fin n) Q (Option (CutTree (Fin n))) (weightedGHBudget n M b Q) :=
  (confidenceReduction M Q b (⟨0, by omega⟩ : Fin n)).weaken (by
    simpa only [Fintype.card_fin, weightedGHBudget] using
      confidenceBudget_polylog (Fin n) (by simpa only [Fintype.card_fin] using (show 1 ≤ n by omega))
        M b Q)

/-- End of Phase 3. For every exact family `E` with size-regular cost and every
promised graph, the ideal law of the twin of the whole reduction, at any
size-regular charge `Q`, is the output law of `weightedGHProgram E`. -/
theorem weightedGHProgram_eq {n M : ℕ} {Q QE : ℕ → ℕ} (E : CanonicalSTFamily M QE)
    (hQ : SizeRegular n Q) (hQE : SizeRegular n QE) (hn : 2 ≤ n) (b : ℕ)
    (G : WeightedGraph (Fin n)) (hG : InputPromise M G) :
    interpIdeal G (weightedGHProgram M Q hn b) = (GHReduction.weightedGHProgram E hn b).eval G.cut := by
  rw [weightedGHProgram, GHReduction.weightedGHProgram, interpIdeal_weaken, RTree.eval_weaken]
  exact confidenceReduction_eq E (by simpa only [Fintype.card_fin] using hQ)
    (by simpa only [Fintype.card_fin] using hQE) b _ G hG

end Top

end Twin
end
end CutQueryComplexity.GHReduction.Randomized
