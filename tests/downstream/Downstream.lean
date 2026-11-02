import CutQueryComplexity

open CutQueryComplexity QuantumQueryComplexity
open scoped Classical ENNReal

example (n : ℕ) :
    deterministicComplexity (WeightedGraph.cut (V := Fin n)) (fun G H => H = G) ≤
      (n + n.choose 2 : ℕ) := by
  simpa only [Fintype.card_fin] using
    (deterministicComplexity_le (reconstruct_solves (V := Fin n)))

example (n W : ℕ) (u v : Fin n) (huv : u ≠ v) :
    quantumComplexity (capacityRead (n := n) (W := W))
      (fun G (w : ℝ) => w = (G.w u v : ℕ)) 0 ≤ 3 :=
  quantum_edgeRecovery_le huv

example (n W : ℕ) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : CutQAlg n W (WeightedGraph (Fin n)) Work),
      ComputesWithErrorOn T (n + n.choose 2) capacityRead CapacityGraph.toWeighted 0 :=
  capacityReconstruct_quantum

-- M2 endpoints are available through the public package, without private imports.
example {V : Type} [Fintype V] [DecidableEq V] :
    deterministicComplexity (WeightedGraph.cut (V := V)) IsSpanningForest ≤
      (12 * Fintype.card V * (searchDepth V + 1) : ℕ) :=
  deterministicComplexity_le spanningForest_solves

example {V : Type} [Fintype V] [DecidableEq V] {W : ℕ} (r : ℕ) (G : CapacityGraph V W) :
    IsThresholdCertificate r G.toWeighted
      ((thresholdCertificate r).eval G.toWeighted.cut) := thresholdCertificate_capacity r G

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    {S T : Finset V} (h : Disjoint S T) (hp : 0 < G.cross S T) (u v : V) :
    ((sampleCross (searchDepth V) S T).eval G.cut) (some (u, v)) =
      (if u ∈ S ∧ v ∈ T then ENNReal.ofReal (G.w u v) else 0) /
        ENNReal.ofReal (G.cross S T) := sampleCross_logarithmic G h hp u v

#check RTree.truncate_solves
#check RTree.bind_solves
#check Coherent.substitute_run

-- M3 strength and cached residual-mass APIs are exported publicly.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    (∑ u, ∑ v, G.w u v / G.strength u v) / 2 ≤ (Fintype.card V - 1 : ℕ) :=
  G.strength_sum_le

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) {κ : ℝ}
    {u v : V} (hκ : κ ≤ G.strength u v) :
    (G.trimWeak κ).strength u v = G.strength u v := G.strength_trimWeak hκ

example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (π : V → B) (cache : B → ℝ) (T : Finset B) :
    ∃ A : DTree (Finset V) ℝ ℝ 1, ∀ G : WeightedGraph V,
      (∀ b, cache b = G.cut (WeightedGraph.fiber π b)) →
        A.run G.cut = ((G.contract π).internalMass T, 1) :=
  ⟨residualMassQuery π cache T, fun G hc => residualMassQuery_run G π cache hc T⟩

#check WeightedGraph.strength_contract_of_lt
#check WeightedGraph.normalized_mincut_eq_one
#check IsSparseCutSparsifier.trans_quarter

-- Complete residual programs work without supplying a graph-dependent cache.
example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (π : V → B) (T : Finset B) :
    (sampleResidualFresh π T).SolvesWithError WeightedGraph.cut
      (fun G o => ResidualEdgeResult G π T o) 0 := sampleResidualFresh_solves π T

example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (G : WeightedGraph V) (π : V → B) (T : Finset B)
    (hp : 0 < (G.contract π).internalMass T) {u v : V}
    (hblock : π u ≠ π v) (hu : π u ∈ T) (hv : π v ∈ T) :
    ((sampleResidualFresh π T).eval G.cut) (some s(u, v)) =
      ENNReal.ofReal (G.w u v) / ENNReal.ofReal ((G.contract π).internalMass T) := by
  rw [sampleResidualFresh_law G π T hp (fun h => hblock (congrArg π h))]
  simp [hu, hv, hblock]

example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (π : V → B) :
    (findHeavyResidualFresh π).Solves WeightedGraph.cut (fun G o => HeavyResidualResult G π o) :=
  findHeavyResidualFresh_solves π

#check mergeBlockCache_run
#check blockMerge_history_le

-- The approximate Kruskal algorithm is uniform over arbitrary real-weight inputs.
example {V : Type} [Fintype V] [DecidableEq V] :
    (approxKruskal (V := V)).Solves WeightedGraph.cut IsApproxKruskalForest := approxKruskal_solves

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (u v : V) :
    (approxKruskal.eval G.cut).bottleneck u v ≤ G.strength u v ∧
      G.strength u v ≤ ((Fintype.card V : ℝ) ^ 2 / 2) *
        (approxKruskal.eval G.cut).bottleneck u v := approxKruskal_pair_bounds G u v

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    approxKruskal.cost G.cut ≤ Fintype.card V * (6 * searchDepth V + 11) :=
  (approxKruskal.cost_le G.cut).trans approxKruskalBudget_le

#check IsApproxKruskalForest.prw_bounds
#check approxKruskal_edge_bound
#check WeightedGraph.bottleneck_mem_edgeLevels

example (G : WeightedGraph (Fin 4)) : G.strongComponents.card ≤ 3 := by
  simpa using G.strongComponents_card_le

example (G X : WeightedGraph (Fin 4)) (hsupport : X.support ≤ G.support) (S : Finset (Fin 4)) :
    X.cut S = ∑ U ∈ G.strongComponents,
      G.componentCoefficient U * (G.strengthPiece X U).cut S :=
  G.strengthDecomposition_cut X hsupport S

#check WeightedGraph.exists_strengthDecomposition
#check WeightedGraph.normalized_component_mincut_eq_one
#check WeightedGraph.isCutSparsifier_of_scaledStrengthPieces

-- Mean identities and dependent-component failure accounting are public APIs.
example (p : PMF (WeightedGraph (Fin 4))) (G : WeightedGraph (Fin 4))
    (h : WeightedGraph.HasMean p G) (ε : ℝ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hpiece : ∀ U ∈ G.strongComponents,
      Probability.mass (G.strengthPieceLaw p U c hc.le)
        (fun Y => ¬IsCutSparsifier ε ((G.strengthPiece G U).scale c hc.le) Y) ≤ ENNReal.ofReal δ) :
    1 - 3 * δ ≤ (Probability.mass p (IsCutSparsifier ε G)).toReal := by
  simpa using h.sparsifier_success ε hc hδ hpiece

example {V : Type} [Fintype V] [DecidableEq V] (p : PMF (WeightedGraph V))
    (G : WeightedGraph V) (h : WeightedGraph.HasMean p G) (S : Finset V) :
    Probability.expect p (fun X => ENNReal.ofReal (X.cut S)) = ENNReal.ofReal (G.cut S) :=
  h.cut S

example (ps : List (PMF ℝ)) (a : ℝ) {t b : ℝ} (ht : 0 ≤ t)
    (h : (ps.map (fun p => Probability.expMoment p id t)).prod ≤ ENNReal.ofReal (Real.exp b)) :
    Probability.mass (Probability.independentSum ps) (fun x => a ≤ x) ≤
      ENNReal.ofReal (Real.exp (b - t * a)) :=
  Probability.upper_tail_le_exp _ id a ht
    (by rwa [Probability.expMoment_independentSum])

#check WeightedGraph.hasMean_expectedGraph
#check WeightedGraph.IsSmooth.exists_decomposition
#check RTree.sparsifier_solves_of_piece_bounds
#check Probability.expMoment_bind_add_le
#check Probability.lower_tail_le_exp

-- Bounded draws give concentration with the correct cut mean and an explicit exponential sum.
example (ds : List Probability.BoundedDraw) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Probability.mass (Probability.BoundedDraw.sumLaw ds)
      (fun x => (1 + ε) * Probability.BoundedDraw.sumMean ds ≤ x) ≤
      ENNReal.ofReal (Real.exp (-(ε ^ 2 * Probability.BoundedDraw.sumMean ds / 4))) :=
  Probability.BoundedDraw.sum_upper_tail ds hε hε1

example {V : Type} [Fintype V] [DecidableEq V] (p : PMF (WeightedGraph V))
    (G : WeightedGraph V) (h : WeightedGraph.HasMean p G) {ε c δ : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hd : ∀ U ∈ G.strongComponents,
      ∀ S ∈ ((G.strengthPiece G U).scale c hc.le).positiveLocalShores U,
        WeightedGraph.HasBoundedCutLaw (G.strengthPieceLaw p U c hc.le) S)
    (hcount : ∀ U ∈ G.strongComponents,
      ((G.strengthPiece G U).scale c hc.le).cutTailSum U ε ≤ ENNReal.ofReal δ) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤ (Probability.mass p (IsCutSparsifier ε G)).toReal :=
  h.sparsifier_success_of_cut_tail_bounds hε hε1 hc hδ hd hcount

#check Probability.BoundedDraw.expect_sumLaw_eq
#check Probability.BoundedDraw.sum_lower_tail
#check WeightedGraph.HasMean.cut_concentration
#check WeightedGraph.HasMean.sparsifier_failure_le_local_cut_sum

-- A concrete sampler supplies its own mean and bounded-cut witnesses.
example {V : Type} [Fintype V] [DecidableEq V]
    (bs : List (WeightedGraph.CountedBucket V)) {ε c δ : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hb : ∀ b ∈ bs, b.Admissible (WeightedGraph.CountedBucket.reference bs) c)
    (htail : ∀ U ∈ (WeightedGraph.CountedBucket.reference bs).strongComponents,
      (((WeightedGraph.CountedBucket.reference bs).strengthPiece
        (WeightedGraph.CountedBucket.reference bs) U).scale c hc.le).cutTailSum U ε ≤
        ENNReal.ofReal δ) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤
      (Probability.mass (WeightedGraph.CountedBucket.sampleLaw bs)
        (IsCutSparsifier ε (WeightedGraph.CountedBucket.reference bs))).toReal :=
  WeightedGraph.CountedBucket.sampleLaw_success_of_cut_tail_bounds bs hε hε1 hc hδ hb htail

#check WeightedGraph.CountedBucket.drawLaw_mean
#check WeightedGraph.CountedBucket.sampleLaw_mean
#check WeightedGraph.CountedBucket.sampleLaw_support
#check WeightedGraph.CountedBucket.admissible_of_count
#check WeightedGraph.CountedBucket.sampleLaw_boundedCutLaw

-- Weighted cut counting is proved and exported, including component-local bounds.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) {κ : ℝ}
    (hκ : 0 < κ) (hmin : ∀ S, ProperShore S → κ ≤ G.cut S) (k : ℕ) (hk : 1 ≤ k) :
    (G.nearMinShores κ k).card ≤ contractionCountBound (Fintype.card V) (2 * k) :=
  G.nearMinShores_card_le hκ hmin k hk

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (U : Finset V) (hG : G.induce U = G) (hκ : 0 < G.inducedMincut U)
    (k : ℕ) (hk : 1 ≤ k) :
    ((G.positiveLocalShores U).filter (fun S => G.cut S ≤ k * G.inducedMincut U)).card ≤
      (2 * U.card) ^ (2 * k) := G.positiveLocalShores_bounded_card U hG hκ k hk

#check WeightedGraph.strengthPiece_bounded_shores_card
