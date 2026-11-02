import CutQueryComplexity
import SLT.RMT.MatBern
import CutQueryComplexityChecks.AxiomAudit

/-! Milestone acceptance statements and a transitive audit of every production declaration. -/

open CutQueryComplexity QuantumQueryComplexity
open scoped Classical Matrix ENNReal

-- Degenerate inputs: reconstruction does not require positive mincut or even a vertex.
example (G : WeightedGraph (Fin 0)) : DTree.run G.cut reconstruct = (G, 0) := by
  simpa using reconstruct_run G

example (G : WeightedGraph (Fin 1)) : DTree.run G.cut reconstruct = (G, 1) := by
  simpa using reconstruct_run G

-- Singleton shores must remain valid global cuts, while being excluded from star contraction.
example : ProperShore ({0} : Finset (Fin 2)) := properShore_singleton 0 (by decide)

example : ¬ NontrivialShore ({0} : Finset (Fin 2)) := by simp [NontrivialShore]

example : mincutValue (0 : WeightedGraph (Fin 2)) = 0 :=
  mincutValue_eq_zero_of_cut_eq_zero _ (properShore_singleton 0 (by decide))
    (WeightedGraph.cut_zero _)

-- No algorithm for the impossible relation: infinity must not silently become zero.
example : deterministicComplexity (fun (_ : Unit) (_ : Unit) => ())
    (fun (_ : Unit) (_ : Unit) => False) = ⊤ := by
  have h : deterministicCounts (fun (_ : Unit) (_ : Unit) => ())
      (fun (_ : Unit) (_ : Unit) => False) = ∅ := by
    ext q
    simp only [deterministicCounts, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨T, hT⟩
    exact hT ()
  rw [deterministicComplexity, h, queryComplexity_empty]

-- Input-independent algorithms: the existential tree precedes the universally quantified graph.
example {V : Type} [Fintype V] [DecidableEq V] (u v : V) (h : u ≠ v) :
    ∃ T : DTree (Finset V) ℝ ℝ 3,
      ∀ G : WeightedGraph V, DTree.run G.cut T = (G.w u v, 3) :=
  ⟨edgeRecovery u v, fun G => edgeRecovery_run G h⟩

example (n : ℕ) :
    ∃ T : DTree (Finset (Fin n)) ℝ (WeightedGraph (Fin n)) (n + n.choose 2),
      T.Solves WeightedGraph.cut (fun G H => H = G) := by
  refine ⟨(reconstruct (V := Fin n)).cast (by simp only [Fintype.card_fin]), ?_⟩
  intro G
  simp [DTree.eval, reconstruct_run]

example (n W : ℕ) (u v : Fin n) (h : u ≠ v) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work) (T : CutQAlg n W ℝ Work),
      SolvesWithErrorOn T 3 capacityRead (fun G w => w = (G.w u v : ℕ)) 0 :=
  capacityEdgeRecovery_quantum h

-- The actual finite cut alphabet carries modular addition; arbitrary amplitudes are allowed.
example (n W : ℕ) (a : Finset (Fin n) → CutAnswer n W)
    (ψ : Encoding.AddBasis (Finset (Fin n)) (CutAnswer n W) Unit → ℂ) :
    oracleMat a *ᵥ (qPerm Encoding.shift *ᵥ
      (oracleMat a *ᵥ Encoding.embed Encoding.blankNative ψ)) =
      Encoding.embed Encoding.blankNative (qPerm (Encoding.addOracle a) *ᵥ ψ) :=
  Encoding.native_simulates_add a ψ

-- M2 programs are fixed before the hidden graph is supplied.
example {V : Type} [Fintype V] [DecidableEq V] :
    ∃ T : DTree (Finset V) ℝ (_root_.SimpleGraph V)
        (12 * Fintype.card V * (searchDepth V + 1)),
      ∀ G, IsSpanningForest G (T.eval G.cut) :=
  ⟨spanningForest, spanningForest_correct⟩

example {V : Type} [Fintype V] [DecidableEq V] (r : ℕ) :
    ∃ T : DTree (Finset V) ℝ (WeightedGraph V) (r * forestBudget V),
      ∀ G : WeightedGraph V, G.IsIntegral → IsThresholdCertificate r G (T.eval G.cut) :=
  ⟨thresholdCertificate r, thresholdCertificate_correct r⟩

example {V : Type} [Fintype V] [DecidableEq V] (S T : Finset V) (h : Disjoint S T) :
    ∃ A : RTree (Finset V) ℝ (Option (V × V)) (6 * (2 * searchDepth V + 1)),
      ∀ G : WeightedGraph V, 0 < G.cross S T → ∀ u v,
        (A.eval G.cut) (some (u, v)) =
          (if u ∈ S ∧ v ∈ T then ENNReal.ofReal (G.w u v) else 0) /
            ENNReal.ofReal (G.cross S T) :=
  ⟨sampleCross (searchDepth V) S T, fun G hp => sampleCross_logarithmic G h hp⟩

-- Zero cuts produce explicit absence, including an empty vertex type.
example : (sampleCross (searchDepth (Fin 0)) ∅ Finset.univ).eval
    (0 : WeightedGraph (Fin 0)).cut = PMF.pure none := by
  apply sampleCross_zero _ _ (by simp)
  simp

example (G : WeightedGraph (Fin 1)) :
    IsSpanningForest G (spanningForest.eval G.cut) := spanningForest_correct G

-- A cap is a new program of the smaller budget, with correctness and expected cost linked.
example {I A O X : Type} {q : ℕ} (T : RTree I A O q)
    (read : X → I → A) (Good : X → O → Prop) {B η : ℝ}
    (hB : 0 ≤ B) (hη : 0 < η) (hT : T.SolvesWithError read Good 0)
    (hcost : ∀ x, T.expectedQueries (read x) ≤ ENNReal.ofReal B) :
    ∃ S : RTree I A (Option O) ⌈B / η⌉₊,
      S.SolvesWithError read (fun x o => o.elim False (Good x)) η := by
  refine ⟨T.truncate ⌈B / η⌉₊, ?_⟩
  simpa using RTree.truncate_solves T read Good hB (le_refl 0) hη hT hcost

-- M3 structural prerequisites include real weights, nonedges, and empty inputs.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    (∑ u, ∑ v, G.w u v / G.strength u v) / 2 ≤ (Fintype.card V - 1 : ℕ) :=
  G.strength_sum_le

example (G : WeightedGraph (Fin 0)) :
    (∑ u, ∑ v, G.w u v / G.strength u v) / 2 ≤ (0 : ℝ) := by
  simpa using G.strength_sum_le

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (u v : V) :
    G.inducedMincut {u, v} = G.w u v := G.inducedMincut_pair u v

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    {u v : V} (hne : u ≠ v) (hnonedge : G.w u v = 0) (hp : 0 < mincutValue G) :
    G.w u v = 0 ∧ 0 < G.strength u v :=
  ⟨hnonedge, hp.trans_le (G.mincut_le_strength hne)⟩

example {V : Type} [Fintype V] [DecidableEq V] (u v : V) :
    (0 : WeightedGraph V).strength u v = 0 := WeightedGraph.strength_zero u v

example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (G : WeightedGraph V) (π : V → B) {κ : ℝ}
    (hblock : ∀ b, G.IsStrong κ (WeightedGraph.fiber π b)) {u v : V}
    (hne : π u ≠ π v) (hweak : G.strength u v < κ) :
    (G.contract π).strength (π u) (π v) = G.strength u v :=
  G.strength_contract_of_lt π hblock hne hweak

-- The residual program is fixed by the public partition and cached answers.
example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (π : V → B) (cache : B → ℝ) (T : Finset B) :
    ∃ A : DTree (Finset V) ℝ ℝ 1, ∀ G : WeightedGraph V,
      (∀ b, cache b = G.cut (WeightedGraph.fiber π b)) →
        A.run G.cut = ((G.contract π).internalMass T, 1) :=
  ⟨residualMassQuery π cache T, fun G hc => residualMassQuery_run G π cache hc T⟩

example {V : Type} [Fintype V] [DecidableEq V] {G H K : WeightedGraph V}
    {ε : ℝ} {m : ℕ} (h : IsCutSparsifier (ε / 4) G H)
    (h' : IsSparseCutSparsifier (ε / 4) m H K) (he : 0 ≤ ε) (he1 : ε ≤ 1) :
    IsSparseCutSparsifier ε m G K := h'.trans_quarter h he he1

-- The residual sampler obtains its own cache and is fixed before the hidden graph.
example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (π : V → B) (T : Finset B) :
    ∃ A : RTree (Finset V) ℝ (Option (Sym2 V))
        (Fintype.card B + residualSampleBudget V B),
      A.SolvesWithError WeightedGraph.cut (fun G o => ResidualEdgeResult G π T o) 0 :=
  ⟨sampleResidualFresh π T, sampleResidualFresh_solves π T⟩

-- Probabilities use original edge weights, even when quotient edges aggregate them.
example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (G : WeightedGraph V) (π : V → B) (T : Finset B)
    (hp : 0 < (G.contract π).internalMass T) {u v : V}
    (hblock : π u ≠ π v) (hu : π u ∈ T) (hv : π v ∈ T) :
    ((sampleResidualFresh π T).eval G.cut) (some s(u, v)) =
      ENNReal.ofReal (G.w u v) / ENNReal.ofReal ((G.contract π).internalMass T) := by
  rw [sampleResidualFresh_law G π T hp (fun h => hblock (congrArg π h))]
  simp [hu, hv, hblock]

-- A single remaining block has no surviving residual edges, even with internal edges.
example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (G : WeightedGraph V) (π : V → B) (b : B) :
    (sampleResidualFresh π {b}).eval G.cut = PMF.pure none := by
  rw [sampleResidualFresh_eval]
  exact sampleResidualEdge_zero G _ _ π _ (fun _ => rfl) _
    ((G.contract π).internalMass_of_card_le_one (by simp))

example : (sampleResidualFresh (id : Fin 0 → Fin 0) Finset.univ).eval
    (0 : WeightedGraph (Fin 0)).cut = PMF.pure none := by
  rw [sampleResidualFresh_eval]
  apply sampleResidualEdge_zero _ _ _ _ _ (fun _ => rfl)
  simp [WeightedGraph.internalMass, WeightedGraph.cross]

example {V : Type} [Fintype V] : residualSampleBudget V V = 18 * searchDepth V + 9 := by
  unfold residualSampleBudget
  omega

example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (π : V → B) :
    ∃ A : DTree (Finset V) ℝ (Option (V × V))
        (Fintype.card B + 6 * (searchDepth V + 1)),
      A.Solves WeightedGraph.cut (fun G o => HeavyResidualResult G π o) :=
  ⟨findHeavyResidualFresh π, findHeavyResidualFresh_solves π⟩

example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (G : WeightedGraph V) (π : V → B) (S : Finset B) {b : B} (hb : b ∈ S)
    (cache : B → ℝ) (hc : ∀ c, cache c = G.cut (WeightedGraph.fiber π c)) :
    (mergeBlockCache π S b cache).run G.cut =
      ((fun c => G.cut (WeightedGraph.fiber (mergeBlocks π S b) c)), 1) :=
  mergeBlockCache_run G π S hb cache hc

example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (π : ℕ → V → B) (m : ℕ) (h : ∀ i < m, IsBlockMerge (π i) (π (i + 1))) :
    m ≤ Fintype.card V - 1 := blockMerge_history_le π m h

-- One deterministic forest program estimates every pair, including nonedges.
example {V : Type} [Fintype V] [DecidableEq V] :
    ∃ A : DTree (Finset V) ℝ (WeightedGraph V) (approxKruskalBudget V),
      A.Solves WeightedGraph.cut IsApproxKruskalForest :=
  ⟨approxKruskal, approxKruskal_solves⟩

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (u v : V) :
    (approxKruskal.eval G.cut).bottleneck u v ≤ G.strength u v ∧
      G.strength u v ≤ ((Fintype.card V : ℝ) ^ 2 / 2) *
        (approxKruskal.eval G.cut).bottleneck u v := approxKruskal_pair_bounds G u v

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    IsSpanningForest G (approxKruskal.eval G.cut).support ∧
      (approxKruskal.eval G.cut).edgeCount ≤ Fintype.card V - 1 :=
  ⟨(approxKruskal_correct G).forest, approxKruskal_edge_bound G⟩

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) {u v : V}
    (hadj : (approxKruskal.eval G.cut).support.Adj u v) :
    (approxKruskal.eval G.cut).w u v = G.w u v :=
  ((approxKruskal_correct G).original u v).resolve_left hadj

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) {u v : V}
    (hne : u ≠ v) (hr : ¬G.support.Reachable u v) :
    (approxKruskal.eval G.cut).bottleneck u v = 0 := by
  apply (WeightedGraph.bottleneck_eq_zero_iff _ hne).mpr
  exact fun h => hr (h.mono (approxKruskal_correct G).forest.1)

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) {u v : V}
    (hnonedge : G.w u v = 0) (hp : 0 < G.strength u v) :
    G.w u v = 0 ∧ 0 < (approxKruskal.eval G.cut).bottleneck u v := by
  refine ⟨hnonedge, ?_⟩
  by_contra hb
  have he := (approxKruskal_correct G).estimate u v
  have hz := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (Fintype.card V : ℝ))
    (le_of_not_gt hb)
  linarith

example (G : WeightedGraph (Fin 0)) :
    (approxKruskal (V := Fin 0)).eval G.cut = 0 ∧ approxKruskal.cost G.cut = 0 := by
  constructor
  · ext u v; exact Fin.elim0 u
  · have h := approxKruskal_query_bound G
    simpa using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example (G : WeightedGraph (Fin 1)) : approxKruskal.run G.cut = (0, 1) := by
  have hstop (steps : ℕ) (hs : steps = 0) (cache : Fin 1 → ℝ) :
      (approxKruskalGrow steps (0 : WeightedGraph (Fin 1)) id cache).run G.cut = (0, 0) := by
    subst steps
    simp only [approxKruskalGrow, DTree.run_pure]
  have hg := hstop (Fintype.card (Fin 1) - 1) (by simp)
    (fun b => G.cut (WeightedGraph.fiber id b))
  simp only [approxKruskal, DTree.run_bind, DTree.eval, DTree.cost, cacheBlockCuts_run, hg]
  norm_num

example {V : Type} [Fintype V] [DecidableEq V] :
    approxKruskalBudget V ≤ Fintype.card V * (6 * searchDepth V + 11) := approxKruskalBudget_le

-- The BK structural decomposition is uniform in the supported outcome graph.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    G.strongComponents.card ≤ Fintype.card V - 1 ∧
      G.positiveStrengths.card ≤ Fintype.card V - 1 :=
  ⟨G.strongComponents_card_le, G.positiveStrengths_card_le⟩

example (G : WeightedGraph (Fin 0)) : G.strongComponents = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := G.strongComponents_card_le
  simpa using h

example (G : WeightedGraph (Fin 1)) : G.strongComponents = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := G.strongComponents_card_le
  simpa using h

example {V : Type} [Fintype V] [DecidableEq V] :
    (0 : WeightedGraph V).strongComponents = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro U hU
  have h := (0 : WeightedGraph V).strongComponents_mincut_mem_levels hU
  simpa using h

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) {u v : V}
    (hnonedge : G.w u v = 0) (hp : 0 < G.strength u v) :
    G.w u v = 0 ∧ G.strength u v ∈ G.positiveStrengths ∧
      (∑ U ∈ G.strongComponents,
        if u ∈ U ∧ v ∈ U then G.componentCoefficient U else 0) = G.strength u v :=
  ⟨hnonedge, (G.mem_positiveStrengths _).mpr ⟨hp, u, v, rfl⟩,
    G.sum_componentCoefficients_pair hp⟩

example {V : Type} [Fintype V] [DecidableEq V] (G X : WeightedGraph V)
    (hsupport : X.support ≤ G.support) {c : ℝ} (hc : 0 < c) (S : Finset V) :
    X.cut S = ∑ U ∈ G.strongComponents,
      (G.componentCoefficient U / c) * ((G.strengthPiece X U).scale c hc.le).cut S :=
  G.strengthDecomposition_scaled_cut X hsupport hc S

example {V : Type} [Fintype V] [DecidableEq V] (G X : WeightedGraph V)
    {c : ℝ} (hc : 0 < c) (hsmooth : ∀ u v, c * X.w u v ≤ G.strength u v)
    {U : Finset V} (hU : U ∈ G.strongComponents) :
    0 < G.componentCoefficient U / c ∧
      ((G.strengthPiece G U).scale c hc.le).inducedMincut U = c ∧
      ∀ u v, ((G.strengthPiece X U).scale c hc.le).w u v ≤ 1 :=
  ⟨G.strengthDecomposition_scaled_coefficient_pos hU hc,
    G.strengthPiece_reference_mincut hU c hc.le,
    G.strengthPiece_scaled_weight_le_one X hc.le hsmooth U⟩

example {V : Type} [Fintype V] [DecidableEq V] (G X : WeightedGraph V)
    (ε : ℝ) (hsupport : X.support ≤ G.support) {c : ℝ} (hc : 0 < c)
    (hpieces : ∀ U ∈ G.strongComponents,
      IsCutSparsifier ε ((G.strengthPiece G U).scale c hc.le)
        ((G.strengthPiece X U).scale c hc.le)) : IsCutSparsifier ε G X :=
  G.isCutSparsifier_of_scaledStrengthPieces X ε hsupport hc
    (fun U hU S => (hpieces U hU).2 S)

-- Expectations work without a finite outcome alphabet or finite vertex type.
example {V : Type} (p : PMF (WeightedGraph V)) (hf : WeightedGraph.HasFiniteMean p)
    (G : WeightedGraph V) (h : WeightedGraph.HasMean p G) :
    WeightedGraph.expectedGraph p hf = G :=
  (WeightedGraph.hasMean_expectedGraph p hf).unique h

example {V : Type} (p : PMF (WeightedGraph V)) (G X : WeightedGraph V)
    (h : WeightedGraph.HasMean p G) (hX : X ∈ p.support) {u v : V} (hz : G.w u v = 0) :
    X.w u v = 0 := by
  by_contra hx
  exact h.support hX hx hz

example {V : Type} [Fintype V] [DecidableEq V] (p : PMF (WeightedGraph V))
    (G : WeightedGraph V) (h : WeightedGraph.HasMean p G) (S : Finset V) :
    Probability.expect p (fun X => ENNReal.ofReal (X.cut S)) = ENNReal.ofReal (G.cut S) :=
  h.cut S

-- The expected piece has induced mincut c, even with isolated vertices outside U.
example {V : Type} [Fintype V] [DecidableEq V] (p : PMF (WeightedGraph V))
    (G : WeightedGraph V) (h : WeightedGraph.HasMean p G) {U : Finset V}
    (hU : U ∈ G.strongComponents) {c : ℝ} (hc : 0 < c) :
    ∃ H, WeightedGraph.HasMean (G.strengthPieceLaw p U c hc.le) H ∧
      H.inducedMincut U = c :=
  ⟨_, h.strengthPieceLaw U c hc.le, G.strengthPiece_reference_mincut hU c hc.le⟩

example {V : Type} [Fintype V] [DecidableEq V] (p : PMF (WeightedGraph V))
    (G : WeightedGraph V) {c : ℝ} (h : WeightedGraph.IsSmooth p G c) (hc : 0 < c)
    (U : Finset V) (Y : WeightedGraph V) (hY : Y ∈ (G.strengthPieceLaw p U c hc.le).support)
    (u v : V) : Y.w u v ≤ 1 := h.piece_bounded hc.le U hY u v

-- With at most one vertex there are no component failure events, for every real epsilon.
example {V : Type} [Fintype V] [DecidableEq V] (hv : Fintype.card V ≤ 1)
    (p : PMF (WeightedGraph V)) (G : WeightedGraph V) (h : WeightedGraph.HasMean p G)
    (ε : ℝ) : Probability.mass p (fun X => ¬IsCutSparsifier ε G X) = 0 := by
  have he : G.strongComponents = ∅ := Finset.card_eq_zero.mp
    (Nat.eq_zero_of_le_zero (by simpa only [Nat.sub_eq_zero_of_le hv] using
      G.strongComponents_card_le))
  refine le_antisymm ?_ (by positivity)
  simpa only [he, Finset.sum_empty] using h.sparsifier_failure_le_sum ε (c := 1) zero_lt_one

-- This is one fixed query program, with a bound uniform over all hidden input graphs.
example {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (T : RTree (Finset V) ℝ (WeightedGraph V) q) (ε : ℝ) {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 ≤ δ)
    (hmean : ∀ G : WeightedGraph V, WeightedGraph.HasMean (T.eval G.cut) G)
    (hpiece : ∀ (G : WeightedGraph V) U, U ∈ G.strongComponents →
      Probability.mass (G.strengthPieceLaw (T.eval G.cut) U c hc.le)
        (fun Y => ¬IsCutSparsifier ε ((G.strengthPiece G U).scale c hc.le) Y) ≤ ENNReal.ofReal δ) :
    T.SolvesWithError WeightedGraph.cut (IsCutSparsifier ε) ((Fintype.card V - 1 : ℕ) * δ) :=
  T.sparsifier_solves_of_piece_bounds ε hc hδ hmean hpiece

-- Conditional moment bounds allow the continuation's distribution to depend on the first draw.
example {α β : Type} (p : PMF α) (q : α → PMF β) (f : α → ℝ) (g : α → β → ℝ)
    {t A B : ℝ} (hp : Probability.expMoment p f t ≤ ENNReal.ofReal (Real.exp A))
    (hq : ∀ x ∈ p.support,
      Probability.expMoment (q x) (g x) t ≤ ENNReal.ofReal (Real.exp B)) :
    Probability.expMoment (p.bind (fun x => (q x).map (fun y => f x + g x y))) id t ≤
      ENNReal.ofReal (Real.exp (A + B)) := by
  rw [Probability.ofReal_exp_add]
  exact Probability.expMoment_bind_add_le p q f g t hp hq

example (p q : PMF ℝ) (t : ℝ) :
    Probability.expMoment (Probability.independentSum [p, q]) id t =
      Probability.expMoment p id t * Probability.expMoment q id t := by
  simp [Probability.expMoment_independentSum]

example {α : Type} (p : PMF α) (f : α → ℝ) (a b : ℝ)
    (h : Probability.expMoment p f 1 ≤ ENNReal.ofReal (Real.exp b)) :
    Probability.mass p (fun x => a ≤ f x) ≤ ENNReal.ofReal (Real.exp (b - a)) := by
  simpa only [one_mul] using Probability.upper_tail_le_exp p f a zero_le_one h

example {α : Type} (p : PMF α) (f : α → ℝ) (a b : ℝ)
    (h : Probability.expMoment p f (-1) ≤ ENNReal.ofReal (Real.exp b)) :
    Probability.mass p (fun x => f x ≤ a) ≤ ENNReal.ofReal (Real.exp (b + a)) := by
  simpa only [neg_one_mul, sub_neg_eq_add] using
    Probability.lower_tail_le_exp p f a (by norm_num : (-1 : ℝ) ≤ 0) h

-- Fractional draws, both signs of the moment parameter, and an empty sum are supported.
example {α : Type} (p : PMF α) (f : α → ℝ)
    (hf : ∀ x ∈ p.support, 0 ≤ f x ∧ f x ≤ 1) {μ : ℝ} (hμ : 0 ≤ μ)
    (hm : Probability.expect p (fun x => ENNReal.ofReal (f x)) = ENNReal.ofReal μ) (t : ℝ) :
    Probability.expMoment p f t ≤ ENNReal.ofReal (Real.exp ((Real.exp t - 1) * μ)) :=
  Probability.expMoment_le_of_unitInterval p f hf hμ hm t

example : Probability.BoundedDraw.sumMean
    [Probability.BoundedDraw.pure (1 / 2) (by norm_num) (by norm_num),
     Probability.BoundedDraw.pure (1 / 3) (by norm_num) (by norm_num)] = 5 / 6 := by
  norm_num [Probability.BoundedDraw.sumMean]

example : Probability.BoundedDraw.sumLaw [] = PMF.pure 0 := rfl

example (ds : List Probability.BoundedDraw) :
    Probability.expect (Probability.BoundedDraw.sumLaw ds) ENNReal.ofReal =
      ENNReal.ofReal (Probability.BoundedDraw.sumMean ds) :=
  Probability.BoundedDraw.expect_sumLaw_eq ds

example (ds : List Probability.BoundedDraw) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Probability.mass (Probability.BoundedDraw.sumLaw ds)
      (fun x => ¬((1 - ε) * Probability.BoundedDraw.sumMean ds ≤ x ∧
        x ≤ (1 + ε) * Probability.BoundedDraw.sumMean ds)) ≤
      2 * ENNReal.ofReal (Real.exp (-(ε ^ 2 * Probability.BoundedDraw.sumMean ds / 4))) :=
  Probability.BoundedDraw.sum_two_sided ds hε hε1

-- The mean of a cut's independent-sum representation is derived from HasMean.
example {V : Type} [Fintype V] [DecidableEq V] (p : PMF (WeightedGraph V))
    (G : WeightedGraph V) (h : WeightedGraph.HasMean p G) (S : Finset V)
    (ds : List Probability.BoundedDraw)
    (hlaw : p.map (fun X => X.cut S) = Probability.BoundedDraw.sumLaw ds) :
    Probability.BoundedDraw.sumMean ds = G.cut S := h.boundedCut_mean S ds hlaw

example {V : Type} [Fintype V] [DecidableEq V] (p : PMF (WeightedGraph V))
    (G : WeightedGraph V) (h : WeightedGraph.HasMean p G) (S : Finset V)
    (hd : WeightedGraph.HasBoundedCutLaw p S) :
    Probability.mass p (fun X => ¬((1 - (1 / 2 : ℝ)) * G.cut S ≤ X.cut S ∧
      X.cut S ≤ (1 + (1 / 2 : ℝ)) * G.cut S)) ≤
      2 * ENNReal.ofReal (Real.exp (-(G.cut S / 16))) := by
  have he : (1 / 2 : ℝ) ^ 2 * G.cut S / 4 = G.cut S / 16 := by ring
  simpa only [he] using h.cut_concentration S hd (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1)

example {V : Type} [Fintype V] [DecidableEq V] (U : Finset V) (ε : ℝ) :
    (0 : WeightedGraph V).cutTailSum U ε = 0 := by
  simp [WeightedGraph.cutTailSum, WeightedGraph.positiveLocalShores]

example {V : Type} [Fintype V] [DecidableEq V] (p : PMF (WeightedGraph V))
    (G X : WeightedGraph V) (h : WeightedGraph.HasMean p G) (hX : X ∈ p.support)
    (S : Finset V) (hz : G.cut S = 0) : X.cut S = 0 := h.cut_zero hX hz

-- Outside isolated vertices do not enter the shore family used by the union bound.
example {V : Type} [Fintype V] [DecidableEq V] (p : PMF (WeightedGraph V))
    (G : WeightedGraph V) (h : WeightedGraph.HasMean p G) (U : Finset V)
    (hG : G.induce U = G) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hd : ∀ S ∈ G.positiveLocalShores U, WeightedGraph.HasBoundedCutLaw p S) :
    Probability.mass p (fun X => ¬IsCutSparsifier ε G X) ≤ G.cutTailSum U ε :=
  h.sparsifier_failure_le_local_cut_sum U hG hε hε1 hd

-- Zero-weight categories are never sampled, including for fractional input weights.
example : Probability.categorical (fun b : Bool => if b then (1 / 2 : ℝ) else 0)
    (by intro b; cases b <;> norm_num) (by norm_num [Fintype.sum_bool]) = PMF.pure true := by
  ext b
  cases b <;> norm_num [Probability.categorical_apply, PMF.pure_apply, Fintype.sum_bool]

-- Two occurrences of the same edge accumulate; an overwrite would fail this check.
example {V : Type} (e : WeightedGraph.EdgeIndex V) :
    WeightedGraph.independentGraphSum
      [PMF.pure (WeightedGraph.edgeGraph e (1 / 2) (by norm_num)),
       PMF.pure (WeightedGraph.edgeGraph e (1 / 2) (by norm_num))] =
      PMF.pure (WeightedGraph.edgeGraph e 1 (by norm_num)) := by
  simp only [WeightedGraph.independentGraphSum, PMF.pure_bind, PMF.pure_map,
    WeightedGraph.add_zero]
  congr 1
  ext u v
  simp only [WeightedGraph.add_weight, WeightedGraph.edgeGraph]
  split_ifs <;> norm_num

example {V : Type} [Fintype V] :
    WeightedGraph.CountedBucket.sampleLaw ([] : List (WeightedGraph.CountedBucket V)) =
      PMF.pure 0 := rfl

example {V : Type} [Fintype V] (bs : List (WeightedGraph.CountedBucket V)) :
    WeightedGraph.HasMean (WeightedGraph.CountedBucket.sampleLaw bs)
      (WeightedGraph.CountedBucket.reference bs) := WeightedGraph.CountedBucket.sampleLaw_mean bs

example {V : Type} [Fintype V] (b : WeightedGraph.CountedBucket V) :
    (WeightedGraph.CountedBucket.expanded [b, b]).length = 2 * b.count := by
  rw [WeightedGraph.CountedBucket.expanded_length]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  omega

-- The numerical count condition constructs the law witness; no probability hypothesis is supplied.
example {V : Type} [Fintype V] [DecidableEq V] (bs : List (WeightedGraph.CountedBucket V))
    (G : WeightedGraph V) (c : ℝ) (hc : 0 ≤ c) (β : WeightedGraph.CountedBucket V → ℝ)
    (hβ : ∀ b ∈ bs, 0 < β b)
    (hk : ∀ b ∈ bs, ∀ e, 0 < b.weight e → β b ≤ G.strength e.val.1 e.val.2)
    (hr : ∀ b ∈ bs, c * b.mass / β b ≤ b.count) (U S : Finset V) :
    WeightedGraph.HasBoundedCutLaw
      (G.strengthPieceLaw (WeightedGraph.CountedBucket.sampleLaw bs) U c hc) S := by
  exact WeightedGraph.CountedBucket.sampleLaw_boundedCutLaw bs G c hc
    (fun b hb => b.admissible_of_count G c (hβ b hb) (hk b hb) (hr b hb)) U S

-- Cut counting uses real weights and a proved recurrence, including below its stopping threshold.
example (G : WeightedGraph (Fin 2))
    (hmin : ∀ S, ProperShore S → (1 / 2 : ℝ) ≤ G.cut S) :
    (G.nearMinShores (1 / 2) 3).card ≤ 4 := by
  simpa [contractionCountBound] using G.nearMinShores_card_le
    (by norm_num : (0 : ℝ) < 1 / 2) hmin 3 (by decide)

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) {κ : ℝ}
    (hκ : 0 < κ) (hmin : ∀ S, ProperShore S → κ ≤ G.cut S)
    (hn : 1 ≤ Fintype.card V) (k : ℕ) (hk : 1 ≤ k) :
    (G.nearMinShores κ k).card ≤ (2 * Fintype.card V) ^ (2 * k) :=
  G.nearMinShores_card_le_pow hκ hmin hn k hk

-- The two complementary shores of a fractional-weight edge are both counted.
example (G : WeightedGraph (Fin 2)) (hw : G.w 0 1 = 1 / 2) :
    ({0} : Finset (Fin 2)) ∈ G.nearMinShores (1 / 2) 1 ∧
      ({1} : Finset (Fin 2)) ∈ G.nearMinShores (1 / 2) 1 := by
  constructor
  · refine Finset.mem_filter.mpr ⟨(mem_properShores _).mpr
      (properShore_singleton 0 (by decide)), ?_⟩
    simp [WeightedGraph.cut_singleton, WeightedGraph.degree, WeightedGraph.diag,
      Fin.sum_univ_two, hw]
  · refine Finset.mem_filter.mpr ⟨(mem_properShores _).mpr
      (properShore_singleton 1 (by decide)), ?_⟩
    simp [WeightedGraph.cut_singleton, WeightedGraph.degree, WeightedGraph.diag,
      Fin.sum_univ_two, G.symm 1 0, hw]

-- Projection discards an outside vertex without introducing an isolated-vertex cut.
example (G : WeightedGraph (Fin 4)) :
    (G.onVertices {0, 1}).cut (WeightedGraph.projectShore {0, 1} {0, 3}) = G.w 0 1 := by
  have hi : ({0, 3} : Finset (Fin 4)) ∩ {0, 1} = {0} := by decide
  have hd : ({0, 1} : Finset (Fin 4)) \ {0, 3} = {1} := by decide
  rw [G.onVertices_cut_project, WeightedGraph.localCut, hi, hd]
  simp [WeightedGraph.cross]

-- Empty and singleton regions have no local shores, for every threshold (even zero).
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (U : Finset V) (hU : U.card ≤ 1) (κ : ℝ) (k : ℕ) :
    G.localNearMinShores U κ k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hn := ((WeightedGraph.mem_localShores _ _).mp (Finset.mem_filter.mp hS).1).two_le_card
  omega

-- The bound for a reference piece uses its own vertex count, with no cut-counting premise.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    {U : Finset V} (hU : U ∈ G.strongComponents) {c : ℝ} (hc : 0 < c)
    (k : ℕ) (hk : 1 ≤ k) :
    ((((G.strengthPiece G U).scale c hc.le).positiveLocalShores U).filter
      (fun S => ((G.strengthPiece G U).scale c hc.le).cut S ≤ k * c)).card ≤
        (2 * U.card) ^ (2 * k) := G.strengthPiece_bounded_shores_card hU hc k hk

-- Summed tails: explicit confidence for fixed buckets, with no cut-tail premise.
example {V : Type} [Fintype V] [DecidableEq V] (bs : List (WeightedGraph.CountedBucket V))
    {ε c δ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hb : ∀ b ∈ bs, b.Admissible (WeightedGraph.CountedBucket.reference bs) c)
    (hlog : 8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤
      (Probability.mass (WeightedGraph.CountedBucket.sampleLaw bs)
        (IsCutSparsifier ε (WeightedGraph.CountedBucket.reference bs))).toReal :=
  WeightedGraph.CountedBucket.sampleLaw_success_of_log bs hε hε1 hc hδ hδ2 hb hlog

-- The empty vertex type needs no logarithm of zero: the exponential condition is trivial.
example {c ε δ : ℝ} (hδ : 0 < δ) (h : 8 * Real.log (4 / δ) ≤ ε ^ 2 * c) :
    ((2 * 0 : ℕ) : ℝ) ^ 2 * Real.exp (-(ε ^ 2 * c / 8)) ≤ δ / 4 :=
  WeightedGraph.exp_condition_of_log hδ (by simpa using h)

-- Estimation soundness: a fixed family of at most |T|-1 light split cuts, no union over random sets.
example {V : Type} [Fintype V] [DecidableEq V] (bs : List (WeightedGraph.CountedBucket V))
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 ≤ ρ) (hb : ∀ b ∈ bs, ρ * (b.mass / b.count) ≤ κ)
    (T : Finset V) :
    Probability.mass (WeightedGraph.CountedBucket.sampleLaw bs)
      (fun X => ¬∀ K ⊆ T, X.IsStrong (3 * κ / 4) K →
        ∃ W, K ⊆ W ∧ W ⊆ T ∧ (WeightedGraph.CountedBucket.reference bs).IsStrong (κ / 2) W) ≤
      ((T.card - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ρ / 32))) :=
  WeightedGraph.CountedBucket.sampleLaw_sound bs hκ hρ hb T

-- A singleton region needs no split cut, so soundness holds with probability one.
example {V : Type} [Fintype V] [DecidableEq V] (Q : WeightedGraph V) (κ₀ : ℝ) (v : V) :
    ∃ D, Q.IsSplitFamily κ₀ {v} D ∧ D.length = 0 := by
  obtain ⟨D, hD, hl⟩ := Q.exists_splitFamily κ₀ {v}
  exact ⟨D, hD, by simpa using hl⟩

-- Estimation completeness: smoothness is needed only for draws inside the strong set.
example {V : Type} [Fintype V] [DecidableEq V] (bs : List (WeightedGraph.CountedBucket V))
    {κ ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2)
    (hb : ∀ b ∈ bs, ρ * (b.mass / b.count) ≤ κ) {C : Finset V}
    (hC : (WeightedGraph.CountedBucket.reference bs).IsStrong κ C)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ / 4) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤
      (Probability.mass (WeightedGraph.CountedBucket.sampleLaw bs)
        (fun X => X.IsStrong (3 * κ / 4) C)).toReal :=
  WeightedGraph.CountedBucket.sampleLaw_complete bs hρ hδ hδ2 hb hC hexp

-- The residual program: exact budget r * cost, fixed before the hidden graph, and its output law.
example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (T : Finset B) (a : ℝ) (ha : 0 ≤ a) (r : ℕ) :
    ∃ P : RTree (Finset V) ℝ (WeightedGraph B) (r * WeightedGraph.residualDrawCost kb kv),
      ∀ G : WeightedGraph V, P.eval G.cut = WeightedGraph.independentGraphSum
        (List.replicate r (((sampleResidual kb kv π cache T).eval G.cut).map
          (WeightedGraph.blockDraw π a ha))) :=
  ⟨WeightedGraph.residualDraws kb kv π cache T a ha r,
    fun G => WeightedGraph.residualDraws_eval G kb kv π cache T a ha r⟩

-- Soundness for the actual residual program, stated in the block quotient.
example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] (G : WeightedGraph V)
    (kb kv : ℕ) (π : V → B) (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (WeightedGraph.fiber π b))
    (T : Finset B) (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv)
    (hM : 0 < (G.contract π).internalMass T) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) :
    Probability.mass
      ((WeightedGraph.residualDraws kb kv π cache T
        ((G.contract π).internalMass T / ⌈ρ * (G.contract π).internalMass T / κ⌉₊)
        (by positivity) ⌈ρ * (G.contract π).internalMass T / κ⌉₊).eval G.cut)
      (fun X => ¬∀ K ⊆ T, X.IsStrong (3 * κ / 4) K →
        ∃ W, K ⊆ W ∧ W ⊆ T ∧ (G.contract π).IsStrong (κ / 2) W) ≤
      ((T.card - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ρ / 32))) :=
  WeightedGraph.residualDraws_sound G kb kv π cache hc T hB hV hM hκ hρ

-- One estimation call: one region query plus at most R capped draws, fixed before the graph.
noncomputable example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] (kb kv : ℕ) (π : V → B)
    (cache : B → ℝ) (T : Finset B) {κ : ℝ} (hκ : 0 < κ) (ρ : ℝ) (R : ℕ) :
    RTree (Finset V) ℝ (Option (WeightedGraph B)) (R * WeightedGraph.residualDrawCost kb kv + 1) :=
  WeightedGraph.estimateCall kb kv π cache T hκ ρ R

-- Soundness of a call needs only old region blocks inside true κ/2-components, not a cap.
example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] (G : WeightedGraph V)
    (kb kv : ℕ) (π : V → B) (cache : B → ℝ) (hc : ∀ b, cache b = G.cut (WeightedGraph.fiber π b))
    (T : Finset B) (hB : Fintype.card B ≤ 2 ^ kb) (hV : Fintype.card V ≤ 2 ^ kv) {κ ρ : ℝ}
    (hκ : 0 < κ) (hρ : 0 < ρ) (R : ℕ)
    (hblocks : ∀ u v, π u ∈ T → π u = π v → G.StrongRelated (κ / 2) u v) :
    Probability.mass ((WeightedGraph.estimateCall kb kv π cache T hκ ρ R).eval G.cut)
      (fun o => ∃ X, o = some X ∧ ¬∀ u v, π u ∈ T →
        X.StrongRelated (3 * κ / 4) (π u) (π v) → G.StrongRelated (κ / 2) u v) ≤
      ((T.card - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(ρ / 32))) :=
  WeightedGraph.estimateCall_sound G kb kv π cache hc T hB hV hκ hρ R hblocks

-- The skip rule: mass below κ leaves every κ-strong original set of the region in one block.
example {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] (G : WeightedGraph V)
    (π : V → B) {T : Finset B} {κ : ℝ} (hM : (G.contract π).internalMass T < κ)
    {U : Finset V} (hU : G.IsStrong κ U) (hUT : U.image π ⊆ T) {u v : V}
    (hu : u ∈ U) (hv : v ∈ U) : π u = π v :=
  WeightedGraph.same_block_of_mass_lt G π hM hU hUT hu hv

-- Regions: under the batch invariant, every κ-related pair is joined in the forest above D/n².
example {V : Type} [Fintype V] [DecidableEq V] {G H : WeightedGraph V}
    (hH : IsApproxKruskalForest G H) {π : V → V} {κ : ℝ}
    (hsep : G.Separated π (2 * κ)) (hrem : (WeightedGraph.remaining H π).Nonempty) {u v : V}
    (hr : G.StrongRelated κ u v) :
    (H.threshold (WeightedGraph.topLevel H π / (Fintype.card V : ℝ) ^ 2)).Reachable u v :=
  WeightedGraph.reachable_of_related_top hH (WeightedGraph.topLevel_pos H π hrem)
    (WeightedGraph.topLevel_lt hH hsep hrem) hr

-- End-to-end estimation: failure at most N times the per-call budget, with no independence
-- between calls assumed.
example {V : Type} [Fintype V] {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H) {ρ : ℝ}
    (hρ : 0 < ρ) {R : ℕ} (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (hδ2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    {cache : V → ℝ} (hc : ∀ b, cache b = G.cut (WeightedGraph.fiber (id : V → V) b)) {N : ℕ}
    (hN : WeightedGraph.runPot H (WeightedGraph.initState H cache) ≤ N) :
    Probability.mass ((WeightedGraph.estRun H ρ R N (WeightedGraph.initState H cache)).eval G.cut)
      (fun s => ¬WeightedGraph.EstSuccess G H s) ≤ N * WeightedGraph.callFailure V ρ δ₀ :=
  WeightedGraph.estRun_correct hH hρ hR hδ hδ2 hexp hc hN

-- Estimation budget on a successful run: near-linear, with no weight-ratio dependence.
example {V : Type} [Fintype V] {G H : WeightedGraph V} (hH : IsApproxKruskalForest G H)
    {s : WeightedGraph.EstState V} (h : WeightedGraph.EstSuccess' G H s) {ρ : ℝ} (hρ : 2 ≤ ρ)
    (R : ℕ) :
    (WeightedGraph.runAcc G ρ R s : ℝ) ≤
      2 * (Fintype.card V - 1 : ℕ) * Nat.log 2 (2 * Fintype.card V ^ 4) +
        WeightedGraph.residualDrawCost (searchDepth V) (searchDepth V) *
          (8 * ρ * (Fintype.card V - 1 : ℕ)) + Fintype.card V :=
  WeightedGraph.runAcc_le hH h hρ R

-- Headline: the capped weighted sparsifier, chosen before the graph, is correct on every
-- nonnegative real-weighted graph, with no weight-ratio or connectivity assumption.
example {V : Type} [Fintype V] {ρ c ε δ δ₀ : ℝ} (hρ : 2 ≤ ρ) {R : ℕ}
    (hR : ρ * (Fintype.card V : ℝ) ^ 2 ≤ R) (hδ₀ : 0 ≤ δ₀) (hδ₀2 : δ₀ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ρ / 128)) ≤ δ₀ / 4)
    (hc : 0 < c) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hlog : 8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    ∃ A : RTree (Finset V) ℝ (Option (WeightedGraph V)) (WeightedGraph.capQ V ρ c),
      ∀ G : WeightedGraph V, Probability.mass (A.eval G.cut)
        (fun o => ¬∃ X, o = some X ∧ IsCutSparsifier ε G X) ≤
          WeightedGraph.fuelBound V * WeightedGraph.callFailure V ρ δ₀ +
            ENNReal.ofReal ((Fintype.card V - 1 : ℕ) * δ) :=
  ⟨WeightedGraph.sparsify ρ c R ⌈2 * c * (Fintype.card V : ℝ) ^ 2⌉₊ (WeightedGraph.capQ V ρ c),
    fun G => WeightedGraph.sparsify_correct G hρ hR hδ₀ hδ₀2 hexp hc hε hε1 hδ hδ2 hlog⟩

-- Explicit parameters: one capped algorithm per (n, s, ε); failure at most (2n+2)^(-s), output a
-- sparse 1±ε cut sparsifier, for every nonnegative real-weighted graph.
example {V : Type} [Fintype V] (hn : 1 ≤ Fintype.card V) {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ A : RTree (Finset V) ℝ (Option (WeightedGraph V))
        (WeightedGraph.capQ V (WeightedGraph.paramρ V s) (WeightedGraph.paramc V s ε)),
      ∀ G : WeightedGraph V, Probability.mass (A.eval G.cut)
        (fun o => ¬∃ X, o = some X ∧ IsSparseCutSparsifier ε
          (WeightedGraph.edgeBound V (WeightedGraph.paramc V s ε)) G X) ≤
            ENNReal.ofReal (WeightedGraph.baseB V ^ (-s)) :=
  ⟨_, fun G => WeightedGraph.sparsify_whp G hn hs hε hε1⟩

-- Theorem 1 conditional on Lemma 21 (`HierarchyBound`): one deterministic decision tree with
-- `detBudget a h n` cut queries returns a minimum cut of every weighted graph on `n ≥ 2` vertices.
example {a : ℕ → ℝ} {h : ℕ → ℕ} (hb : Hierarchy.HierarchyBound a h) (ha : ∀ r, 1 ≤ a r)
    (hma : Monotone a) (hh : Monotone h) {V : Type} [Fintype V] [DecidableEq V]
    (hn : 2 ≤ Fintype.card V) :
    ∃ D : DTree (Finset V) ℝ (Option (Finset V)) (DetMinCut.detBudget a h (Fintype.card V)),
      ∀ G : WeightedGraph V, ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  DetMinCut.deterministic_mincut_of_hierarchyBound hb ha hma hh hn

-- T2 conditional on `HierarchyBound` with polylogarithmic distortion and height: one decision
-- tree per `n` with `O(n (⌊√n⌋ + 1) L(n)^(4p+8))` queries, `L(n) = max 1 ⌈log₂ 2n⌉`.
example {a : ℕ → ℝ} {h : ℕ → ℕ} (hb : Hierarchy.HierarchyBound a h) (ha : ∀ r, 1 ≤ a r)
    (hma : Monotone a) (hh : Monotone h) {A0 H0 : ℝ} {p : ℕ}
    (hA : ∀ r, a r ≤ A0 * (DetMinCut.logL r : ℝ) ^ p)
    (hH : ∀ r, (h r : ℝ) ≤ H0 * DetMinCut.logL r) (hH0 : 0 ≤ H0) :
    ∃ C : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∃ q : ℕ, (q : ℝ) ≤ C * Fintype.card V * (Nat.sqrt (Fintype.card V) + 1) *
          (DetMinCut.logL (Fintype.card V) : ℝ) ^ (4 * p + 8) ∧
        ∃ D : DTree (Finset V) ℝ (Option (Finset V)) q,
          ∀ G : WeightedGraph V, ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  DetMinCut.deterministic_mincut_upper_of_hierarchyBound hb ha hma hh hA hH hH0

-- The hypotheses of the T2 statement are satisfiable for Räcke's `p = 3`: `a = L³` has
-- `1 ≤ a r ≤ 1 · L(r)³` for every `r`, including `r = 0`.
example : (∀ r, (1 : ℝ) ≤ (DetMinCut.logL r : ℝ) ^ 3) ∧
    ∀ r, (DetMinCut.logL r : ℝ) ^ 3 ≤ 1 * (DetMinCut.logL r : ℝ) ^ 3 :=
  ⟨fun r => one_le_pow₀ (by exact_mod_cast DetMinCut.one_le_logL' r), fun r => by rw [one_mul]⟩

-- Theorem 1 with the paper's exponent seven, conditional on Lemma 21 (`HierarchyBound` with
-- cubic-log distortion) and a constant-quality terminal cut guard (Lemma 19). The tree `D` is
-- chosen for each `n` before the graph `G`.
example {a : ℕ → ℝ} {h : ℕ → ℕ} (hb : Hierarchy.HierarchyBound a h) (ha : ∀ r, 1 ≤ a r)
    (hma : Monotone a) {A0 ρ0 : ℝ} (hA : ∀ r, a r ≤ A0 * (DetMinCut.logL r : ℝ) ^ 3)
    (hρ0 : 1 ≤ ρ0) (hcg : Hierarchy.ConstantCutGuard ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (DetMinCut.logL n : ℝ) ^ 7 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  DetMinCut.deterministic_mincut_log7_fin_of_hierarchyBound_of_constantGuard hb ha hma hA hρ0 hcg

-- The cubic growth assumption of the log-seven statement is satisfiable, including `r = 0`.
example : ∀ r, (1 : ℝ) ≤ (DetMinCut.logL r : ℝ) ^ 3 ∧
    (DetMinCut.logL r : ℝ) ^ 3 ≤ 1 * (DetMinCut.logL r : ℝ) ^ 3 :=
  fun r => ⟨one_le_pow₀ (by exact_mod_cast DetMinCut.one_le_logL' r), by rw [one_mul]⟩

-- The tuned parameter is in range above the threshold.
example {N : ℕ} (h7 : DetMinCut.logL N ^ 7 ≤ Nat.sqrt N) :
    2 ≤ DetMinCut.kLog7 N ∧ (Nat.sqrt N : ℝ) / (DetMinCut.logL N : ℝ) ^ 6 ≤ DetMinCut.kLog7 N ∧
      (DetMinCut.kLog7 N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) / (DetMinCut.logL N : ℝ) ^ 6 :=
  ⟨DetMinCut.two_le_kLog7 N, DetMinCut.sqrt_div_le_kLog7 N, DetMinCut.kLog7_le_two_mul h7⟩

-- Lemma 21 is proved: quadratic-log distortion and logarithmic height, with no assumption.
example : Hierarchy.HierarchyBound (fun n => 1690 * (DetMinCut.logL n : ℝ) ^ 2)
    (fun n => 4 * DetMinCut.logL n) :=
  Hierarchy.exists_hierarchyBound_sq

-- The hierarchy theorem applies to the empty vertex type and to the zero graph.
example : ∃ m, ∃ H : Hierarchy.Hier Empty (Fin m), m ≤ 2 * Fintype.card Empty + 1 ∧
    H.LeafChildless ∧ H.height ≤ 4 * DetMinCut.logL (Fintype.card Empty) ∧
    ∀ S, H.rep (H.canon (0 : WeightedGraph Empty)) S ≤
      1690 * (DetMinCut.logL (Fintype.card Empty) : ℝ) ^ 2 * (0 : WeightedGraph Empty).cut S :=
  Hierarchy.exists_hierarchyBound_sq Empty 0

-- On the zero graph every representation cost vanishes.
example {V : Type} [Fintype V] [DecidableEq V] : ∃ m, ∃ H : Hierarchy.Hier V (Fin m),
    ∀ S, H.rep (H.canon (0 : WeightedGraph V)) S ≤ 0 := by
  obtain ⟨m, H, -, -, -, h⟩ := Hierarchy.exists_hierarchyBound_sq V (0 : WeightedGraph V)
  exact ⟨m, H, fun S => by simpa using h S⟩

-- Theorem 1 without a hierarchy assumption: `O(n^{3/2} log^16 n)` deterministic cut queries.
example : ∃ C : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
    ∃ q : ℕ, (q : ℝ) ≤ C * Fintype.card V * (Nat.sqrt (Fintype.card V) + 1) *
        (DetMinCut.logL (Fintype.card V) : ℝ) ^ 16 ∧
      ∃ D : DTree (Finset V) ℝ (Option (Finset V)) q,
        ∀ G : WeightedGraph V, ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  DetMinCut.deterministic_mincut_upper

-- A load-bounded distribution of retractions gives the constant-quality guard.
example {ρ0 : ℝ} (hρ0 : 0 ≤ ρ0) (h : Hierarchy.RetractionBound ρ0) :
    Hierarchy.ConstantCutGuard ρ0 :=
  Hierarchy.constantCutGuard_of_retractionBound hρ0 h

-- Exponent five, conditional only on the constant-quality guard: the quadratic hierarchy
-- distortion is used directly with `k = kLog5 N`.
example {ρ0 : ℝ} (hρ0 : 1 ≤ ρ0) (hcg : Hierarchy.ConstantCutGuard ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (DetMinCut.logL n : ℝ) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  DetMinCut.deterministic_mincut_log5_of_constantGuard hρ0 hcg

-- The aggregate tree inequality gives a load-bounded retraction distribution, including zero
-- capacities; with nonempty terminals a retraction always exists.
example {α : ℝ} (h : Hierarchy.TreeZeroExt α) : Hierarchy.RetractionBound α :=
  Hierarchy.retractionBound_of_treeZeroExt h

example {V N : Type} [Fintype N] [DecidableEq N] [Nonempty V] (H : Hierarchy.Hier V N) :
    ∃ f : N → V, H.Fixing f :=
  H.exists_fixing

-- The aggregate tree 0-extension bound, with constant `42`: zero capacities and zero lengths
-- allowed, nonempty terminal set.
example : Hierarchy.TreeZeroExt 42 := Hierarchy.treeZeroExt_42

-- The constant-quality terminal cut guard, with the constant outside every quantifier.
example : ∃ ρ0 : ℝ, 1 ≤ ρ0 ∧ Hierarchy.ConstantCutGuard ρ0 := Hierarchy.exists_constantCutGuard

-- Theorem 1 with exponent five and no hypothesis.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) * (DetMinCut.logL n : ℝ) ^ 5 ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
        ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  DetMinCut.deterministic_mincut_log5

-- Directed oracle algebra. Antiparallel arcs are
-- counted in both directions by the pair multiplicity.
example : (DiGraph.mk (V := Fin 2) (fun u v => if u ≠ v then 1 else 0)
    (by decide)).sym 0 1 = 2 := by decide

-- Three outgoing-cut queries give the pair count between disjoint shores.
example {V : Type} [Fintype V] [DecidableEq V] (G : DiGraph V) {A B : Finset V}
    (h : Disjoint A B) : (pairQuery A B).eval G.out = ∑ u ∈ A, ∑ v ∈ B, G.sym u v :=
  pairQuery_eval G h

-- The ordered search returns the first actual neighbor in the public order, with its
-- multiplicity, in `3 + 3 ⌈log₂ |V|⌉` queries; an empty list gives `none`.
example {V : Type} [Fintype V] [DecidableEq V] (G : DiGraph V) (v : V) {L : List V}
    (hL : L.Nodup) (hv : v ∉ L) :
    (firstNbr v (Nat.clog 2 (Fintype.card V)) L).eval G.out =
      (L.find? fun u => decide (0 < G.sym v u)).map fun u => (u, G.sym v u) :=
  firstNbr_correct_clog G v hL hv

example {V : Type} [Fintype V] [DecidableEq V] (G : DiGraph V) (v : V) (k : ℕ) :
    (firstNbr v k []).eval G.out = none := by
  rw [firstNbr_correct G v k List.nodup_nil (List.not_mem_nil) (by simp)]; rfl

-- Exact dyadic row aggregates in `6 B |V|` queries.
example {V : Type} [Fintype V] [DecidableEq V] (G : DiGraph V) (q : DyadicFormula V)
    (allow : V → V → Bool) (w : V) :
    (allRowsUniv q allow).eval G.out w =
      ∑ u ∈ rowCand allow w, (G.sym w u : ℝ) * q.val w u :=
  allRowsUniv_correct G q allow w

-- Spectral semantics (D2): energy is the Laplacian quadratic form for every real vector.
example {V : Type} [Fintype V] [DecidableEq V] (ω : Sym2 V → ℝ) (S : Finset (Sym2 V))
    (x : V → ℝ) : x ⬝ᵥ (Spectral.lap ω S *ᵥ x) = Spectral.energy ω S x :=
  Spectral.quad_lap ω S x

-- A spanner trial on an empty support selects nothing, for every coin sequence.
example {V κ : Type} [Fintype V] [DecidableEq V] [LinearOrder κ] (key : Sym2 V → κ)
    (hinj : Function.Injective key) (coins : ℕ → V → Bool) {k : ℕ} (hk : 1 ≤ k) :
    (Spanner.trial key coins ∅ k).H = ∅ :=
  Finset.subset_empty.mp (Spanner.trial_stretch (ℓ := fun _ => 0) hinj (fun _ _ _ => le_rfl)
    (by simp) coins hk).1

-- Stretch for every completed trial (source `lem:stretch`), with `α = 2k − 1`.
example {V κ : Type} [Fintype V] [DecidableEq V] [LinearOrder κ] (key : Sym2 V → κ)
    (ℓ : Sym2 V → ℝ) (hinj : Function.Injective key) (hmono : ∀ e f, key f ≤ key e → ℓ f ≤ ℓ e)
    (hℓ : ∀ e, 0 ≤ ℓ e) {E0 : Finset (Sym2 V)} (hE0 : ∀ a b, s(a, b) ∈ E0 → a ≠ b)
    (coins : ℕ → V → Bool) {k : ℕ} (hk : 1 ≤ k) {a b : V} (he : s(a, b) ∈ E0) :
    ∃ p : (Spectral.pairGraph (Spanner.trial key coins E0 k).H).Walk a b,
      p.IsPath ∧ (p.edges.map ℓ).sum ≤ (2 * k - 1 : ℕ) * ℓ s(a, b) :=
  Spanner.trial_path hinj hmono hℓ hE0 coins hk he

-- Directed mincut reductions (D5), conditional on an LP solver. The LP optimum is exactly
-- `−λ_st`, attained through a maximum flow.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] {G : DiGraph V} {s t : V}
    (hG : G.Simple) (hst : s ≠ t) :
    ∃ p : DirectedMincut.LPPoint V, DirectedMincut.Feasible G s t p ∧
      DirectedMincut.obj p = -(DirectedMincut.stMin G s t : ℝ) :=
  DirectedMincut.exists_feasible_obj_eq hG hst

-- Exact terminal mincut from any LP solver that is `ε`-optimal with probability `1 − ζ`, plus
-- `2n(3 + 3k) + 1` further queries.
example {V X : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (graph : X → DiGraph V)
    (hsimple : ∀ x, (graph x).Simple) {s t : V} (hst : s ≠ t) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) {τ ε ζ : ℝ} (hτ : 0 < τ)
    (hn : 8 * (Fintype.card V : ℝ) ^ 2 * τ ≤ 1) (hε : ε ≤ τ / 16) (hζ : 0 ≤ ζ) {qLP : ℕ}
    (lp : RTree (Finset V) ℕ (DirectedMincut.LPPoint V) qLP)
    (hlp : lp.SolvesWithError (fun x => (graph x).out)
      (fun x => DirectedMincut.LPGood s t ε (graph x)) ζ) :
    (lp.bind fun p => RTree.ofDeterministic (DirectedMincut.extract s t k τ p)).SolvesWithError
      (fun x => (graph x).out) (fun x => DirectedMincut.STGood s t (graph x)) ζ :=
  DirectedMincut.terminal_solves graph hsimple hst hk hτ hn hε hζ lp hlp

-- The global reduction: error at most `(1 − h/n)^K + ζ` for any terminal routine meeting its
-- contract on the original graph.
example {V X : Type} [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (graph : X → DiGraph V) (hsimple : ∀ x, (graph x).Simple) (hn : 2 ≤ Fintype.card V) {k : ℕ}
    (hk : Fintype.card V ≤ 2 ^ k) (h K : ℕ) (hh : h ≤ Fintype.card V) (a : V) {qst : ℕ}
    {T : V → V → RTree (Finset V) ℕ (Finset V × ℕ) qst} {ζ : ℝ}
    (hT : ∀ x, DirectedMincut.TermSpec (graph x) T ζ) (hζ : 0 ≤ ζ) :
    (DirectedMincut.global k h K a T).SolvesWithError (fun x => (graph x).out)
      (fun x => DirectedMincut.Opt (graph x)) ((1 - (h : ℝ) / Fintype.card V) ^ K + ζ) :=
  DirectedMincut.global_solves graph hsimple hn hk h K hh a hT hζ

-- One round of quarter sampling (D3), as a mass of the finite mask PMF: `K = 3λ`, variance at
-- most `3λ`, and `0 < δ ≤ 1` give `2n exp(−δ²/(8λ))`. Zero dimensions, no items, and `λ = 0`
-- are included.
example {n N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) ℝ) {lam δ : ℝ}
    (hsym : ∀ e, (A e).IsHermitian) (hpsd : ∀ e x, 0 ≤ x ⬝ᵥ (A e *ᵥ x))
    (hnorm : ∀ e, @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (A e) ≤ lam)
    (hsum : ∀ x, ∑ e, x ⬝ᵥ (A e *ᵥ x) ≤ x ⬝ᵥ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Probability.mass (Spectral.maskPMF N) fun ξ =>
      δ ≤ @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm
        (∑ e, Spectral.qsample A e ξ)).toReal ≤
      2 * n * Real.exp (-(δ ^ 2) / (8 * lam)) :=
  Spectral.quarter_tail_pmf A hsym hpsd hnorm hsum hδ hδ1

-- The conditional one-round guarantee (D3): with a fixed bundle and the bundle bound
-- `ω_e (x_u − x_v)² ≤ λ xᵀLx` on the remaining pairs, a fresh quarter mask keeps every energy
-- within `1 ± δ` outside probability `2n exp(−δ²/(8λ))`, for every real vector.
example {n N : ℕ} {ω : Sym2 (Fin n) → ℝ} (hω : ∀ e, 0 ≤ ω e) {E' : Finset (Sym2 (Fin n))}
    {p : Fin N → Sym2 (Fin n)} (hp : Function.Injective p) (hpE : ∀ i, p i ∈ E') {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hlev : ∀ i y, ω (p i) * Spectral.pairSq y (p i) ≤ lam * Spectral.energy ω E' y)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Probability.mass (Spectral.maskPMF N) fun ξ => ¬ ∀ x,
      |Spectral.sampledEnergy ω E' p ξ x - Spectral.energy ω E' x| ≤
        δ * Spectral.energy ω E' x).toReal ≤ 2 * n * Real.exp (-(δ ^ 2) / (8 * lam)) :=
  Spectral.one_round hω hp hpE hlam hlev hδ hδ1

-- Capped spanner trials (D3, source `lem:spanner`): `J` fresh trials of `capQ` queries each
-- fail with probability at most `2^{-J}`; every returned spanner is supported in the public
-- support, has at most `4n(K+1)` pairs, and has stretch `2K + 1`.
example {V κ : Type} [Fintype V] [DecidableEq V] [LinearOrder κ] {key : Sym2 V → κ}
    (hinj : Function.Injective key) {ℓ : Sym2 V → ℝ}
    (hmono : ∀ e f, key f ≤ key e → ℓ f ≤ ℓ e) (hℓ : ∀ e, 0 ≤ ℓ e) (G : DiGraph V) {K kq : ℕ}
    (hk : Fintype.card V ≤ 2 ^ kq) (hK : Fintype.card V ≤ 2 ^ K) (P : Sym2 V → Bool) (J : ℕ) :
    Probability.mass ((Spanner.amp key K kq P J).eval G.out) (fun o => o = none) ≤
        (2⁻¹ : ENNReal) ^ J ∧
      ∀ H, some H ∈ ((Spanner.amp key K kq P J).eval G.out).support →
        H ⊆ Spanner.support G P ∧ H.card ≤ Spanner.capH V K ∧
          ∀ a b, s(a, b) ∈ Spanner.support G P → ∃ p : (Spectral.pairGraph H).Walk a b,
            p.IsPath ∧ (p.edges.map ℓ).sum ≤ (2 * K + 1 : ℕ) * ℓ s(a, b) :=
  Spanner.amp_spanner hinj hmono hℓ G hk hK P J

-- The spectral primitive (D4, source `thm:main`): one randomized query program per public
-- parameter tuple; for every hidden digraph with pair multiplicities at most `C`, with
-- probability at least `1 − ζ` it returns weights `Q` with `(1 ± ε)` energies for every real
-- vector, supported on actual positive-weight pairs, each stored once as `c_e 4^r w_e`.
example {n : ℕ} {C ε ζ : ℝ} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ}
    (hn : 2 ≤ n) (hC : 1 ≤ C) (hCG : ∀ e, (Spanner.symS G e : ℝ) ≤ C) (hw0 : ∀ e, 0 ≤ w e)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hζ : 0 < ζ) (hζ2 : ζ ≤ 1 / 2) :
    Probability.mass ((Sparsify.sparsify w (Sparsify.pK n) (Sparsify.pJ n C ε ζ)
        (Sparsify.pt n C ε ζ) (Sparsify.pR n ζ)).eval G.out)
      (fun o => ¬ ∃ out, o = some out ∧
        (∀ x, (1 - ε) * Sparsify.E0 G w x ≤ Sparsify.Eo out x ∧
          Sparsify.Eo out x ≤ (1 + ε) * Sparsify.E0 G w x) ∧
        (∀ e, out e ≠ 0 → 0 < Spanner.symS G e ∧ 0 < w e) ∧
        (Finset.univ.filter fun e => out e ≠ 0).card ≤
          Sparsify.pR n ζ * (Sparsify.pt n C ε ζ * Spanner.capH (Fin n) (Sparsify.pK n)) ∧
        (∀ e, out e ≠ 0 → ∃ r' < Sparsify.pR n ζ,
          out e = (Spanner.symS G e : ℝ) * (4 : ℝ) ^ r' * w e)) ≤ ENNReal.ofReal ζ :=
  Sparsify.spectral_primitive hn hC hCG hw0 hε hε2 hζ hζ2

-- Its worst-case query budget is `O(C ε⁻² n D⁸)` and output size `O(C ε⁻² n D⁶)`,
-- `D = ln(2Cn/(εζ))`, with explicit constants.
example {n : ℕ} {C ε ζ : ℝ} (h : Sparsify.Hyp n C ε ζ) :
    ((Sparsify.pR n ζ * Sparsify.levelBudget (n := n) (Sparsify.pK n) (Sparsify.pJ n C ε ζ)
        (Sparsify.pt n C ε ζ) + 3 * n : ℕ) : ℝ) ≤
      2 * 10 ^ 10 * C / ε ^ 2 * n * Sparsify.Dlog n C ε ζ ^ 8 :=
  Sparsify.budget_le h

-- Every returned output (no probability attached) is supported on actual positive-weight pairs,
-- has at most `2·10^7 C ε⁻² n D⁶` pairs, and stores each pair once as `c_e 4^{r'} w_e`.
example {n : ℕ} {C ε ζ : ℝ} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ}
    (h : Sparsify.Hyp n C ε ζ) (hw0 : ∀ e, 0 ≤ w e) {out : Sym2 (Fin n) → ℝ}
    (hout : some out ∈ ((Sparsify.sparsify w (Sparsify.pK n) (Sparsify.pJ n C ε ζ)
      (Sparsify.pt n C ε ζ) (Sparsify.pR n ζ)).eval G.out).support) :
    (∀ e, 0 ≤ out e) ∧ (∀ e, out e ≠ 0 → 0 < Spanner.symS G e ∧ 0 < w e) ∧
      ((Finset.univ.filter fun e => out e ≠ 0).card : ℝ) ≤
        2 * 10 ^ 7 * C / ε ^ 2 * n * Sparsify.Dlog n C ε ζ ^ 6 ∧
      ∀ e, out e ≠ 0 → ∃ r' < Sparsify.pR n ζ,
        out e = (Spanner.symS G e : ℝ) * (4 : ℝ) ^ r' * w e :=
  Sparsify.spectral_primitive_support h hw0 hout

-- Dyadic inputs: every returned weight keeps the input exponent and gains at most
-- `2R + size C` mantissa bits.
example {n : ℕ} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ} {K J t : ℕ}
    (hw0 : ∀ e, 0 ≤ w e) (hK : n ≤ 2 ^ K) (R : ℕ) {C₀ : ℕ} (hC : ∀ e, Spanner.symS G e ≤ C₀)
    {m : Sym2 (Fin n) → ℕ} {z : Sym2 (Fin n) → ℤ} (hw : ∀ e, w e = m e * (2 : ℝ) ^ z e)
    {out : Sym2 (Fin n) → ℝ} (h : some out ∈ ((Sparsify.sparsify w K J t R).eval G.out).support)
    (e : Sym2 (Fin n)) :
    ∃ m' : ℕ, out e = m' * (2 : ℝ) ^ z e ∧
      Nat.size m' ≤ Nat.size (m e) + 2 * R + Nat.size C₀ :=
  Sparsify.sparsify_dyadic hw0 hK R hC hw h e

-- Lee–Sidford Lemma 25: for a symmetric idempotent `P` with positive
-- diagonal, `K = 2(Σ + cΛ)⁻¹Λ` satisfies `‖Kh‖_∞ + C‖Kh‖_σ ≤ β(1 + 1/C)(‖h‖_∞ + C‖h‖_σ)`
-- with `β = 2/(1+c)`; `c = 2/p − 1` gives `β = p`.
example {M : ℕ} {P : Matrix (Fin M) (Fin M) ℝ} (hsymm : Pᵀ = P) (hidem : P * P = P)
    (hpos : ∀ i, 0 < P i i) {p C : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hC : 0 < C)
    (h : Fin M → ℝ) :
    let σ : Fin M → ℝ := fun i => P i i
    let K : Matrix (Fin M) (Fin M) ℝ := (2 : ℝ) • ((Matrix.diagonal σ + (2 / p - 1) •
      (Matrix.diagonal σ - P ⊙ P))⁻¹ * (Matrix.diagonal σ - P ⊙ P))
    ‖K *ᵥ h‖ + C * ImplicitLP.wnorm σ (K *ᵥ h) ≤
      p * (1 + 1 / C) * (‖h‖ + C * ImplicitLP.wnorm σ h) := by
  intro σ K
  have hc : 0 ≤ 2 / p - 1 := by
    rw [sub_nonneg, le_div_iff₀ hp]; linarith
  have := ImplicitLP.proj_jacobian_mixed hsymm hidem hpos hc hC h
  rwa [ImplicitLP.beta_of_p hp] at this

-- Lee–Sidford Lemma 49: scaling rows by `e^{τh}` moves the leverage scores
-- at rate `2Λh`, with `Λ = Σ − P ⊙ P`.
example {M r : ℕ} (B : Matrix (Fin M) (Fin r) ℝ) (hB : (Bᵀ * B).det ≠ 0) (h : Fin M → ℝ)
    (i : Fin M) :
    HasDerivAt (fun τ => ImplicitLP.lev (Matrix.diagonal (fun j => Real.exp (τ * h j)) * B) i)
      (2 * ((Matrix.diagonal (fun j => ImplicitLP.proj B j j) -
        ImplicitLP.proj B ⊙ ImplicitLP.proj B) *ᵥ h) i) 0 :=
  ImplicitLP.hasDerivAt_lev B hB h i

-- Lee–Sidford audit: Lewis weights exist and are unique for `0 < p < 2` (contraction in log coordinates).
example {M r : ℕ} {B : Matrix (Fin M) (Fin r) ℝ} {p : ℝ} (hB : (Bᵀ * B).det ≠ 0)
    (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2) : ∃! w, ImplicitLP.IsLewis p B w :=
  ImplicitLP.lewis_exists_unique hB hrow hp0 hp2

-- Lee–Sidford Lemma 24 (audit gap G3): the log Lewis weights are differentiable in
-- the row scaling, with derivative `K h`, `K = 2(Σ + (2/p − 1)Λ)⁻¹Λ`.
example {M r : ℕ} {B : Matrix (Fin M) (Fin r) ℝ} {p : ℝ} (hB : (Bᵀ * B).det ≠ 0)
    (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2) (h : Fin M → ℝ) (i : Fin M) :
    let P := ImplicitLP.proj (Matrix.diagonal (fun j =>
      Real.exp ((1 / 2 - 1 / p) * ImplicitLP.lewisLog p B j)) * B)
    let σ : Fin M → ℝ := fun j => P j j
    let Λ : Matrix (Fin M) (Fin M) ℝ := Matrix.diagonal σ - P ⊙ P
    let K : Matrix (Fin M) (Fin M) ℝ := (2 : ℝ) • ((Matrix.diagonal σ + (2 / p - 1) • Λ)⁻¹ * Λ)
    HasDerivAt (fun τ => ImplicitLP.lewisLog p (Matrix.diagonal (fun j => Real.exp (τ * h j)) * B) i)
      ((K *ᵥ h) i) 0 :=
  ImplicitLP.hasDerivAt_lewisLog hB hrow hp0 hp2 h i

-- `eq:gmove` (repaired Lee–Sidford Lemma 16): with the audited draft's parameters
-- `p = 1 − 1/L₀`, `k = 2L₀`, `C_N = 48k` and any regularization `c₀ ≥ 0`, regularized Lewis weights
-- move by at most `(1 − 1/k + 4v)v` along an interior segment with `v = N_{g(x)}(S(x)d) ≤ 1/10`.
example {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {κ m : Fin M → ℝ} (hA : (Aᵀ * A).det ≠ 0)
    (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀) (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    {x d : Fin M → ℝ} (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ImplicitLP.Interior κ m (x + t • d))
    (hv : ImplicitLP.mixed (48 * (2 * L₀)) (ImplicitLP.gfun κ m (1 - 1 / L₀) c₀ A x)
      (fun i => ImplicitLP.barS κ m x i * d i) ≤ 1 / 10) :
    ImplicitLP.mixed (48 * (2 * L₀)) (ImplicitLP.gfun κ m (1 - 1 / L₀) c₀ A x)
        (fun i => Real.log (ImplicitLP.gfun κ m (1 - 1 / L₀) c₀ A (x + d) i) -
          Real.log (ImplicitLP.gfun κ m (1 - 1 / L₀) c₀ A x i)) ≤
      (1 - 1 / (2 * L₀) + 4 * ImplicitLP.mixed (48 * (2 * L₀))
        (ImplicitLP.gfun κ m (1 - 1 / L₀) c₀ A x) (fun i => ImplicitLP.barS κ m x i * d i)) *
        ImplicitLP.mixed (48 * (2 * L₀)) (ImplicitLP.gfun κ m (1 - 1 / L₀) c₀ A x)
          (fun i => ImplicitLP.barS κ m x i * d i) :=
  ImplicitLP.eq_gmove_note hA hrow hL hκ hc₀ hint hv

-- Lemma S of the Lee–Sidford audit (repair of audit gap G1): with `c₀ ≤ 1/(2M)` and `L₀ − 1 ≥ log₂(2M)`, the regularized
-- sensitivity is at most 16.
example {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0)
    {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hcM : c ≤ 1 / (2 * M)) (i : Fin M) :
    ImplicitLP.qform A (fun j => 1 / (Real.exp (ImplicitLP.lewisLog (1 - 1 / L₀) A j) + c)) i /
      (Real.exp (ImplicitLP.lewisLog (1 - 1 / L₀) A i) + c) ^ 2 ≤ 16 :=
  ImplicitLP.sens_note hA hrow hL hLM hc0 hcM i

-- `eq:projection` with the repaired regularization: `δ ≤ N_w(Sh) ≤ (1 + 1/(16k)) δ` for the
-- exact feasible Newton direction and weights within `[4/5, 5/4]` of `g`.
example {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {κ m : Fin M → ℝ} (hA : (Aᵀ * A).det ≠ 0)
    (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hcM : c₀ ≤ 1 / (2 * M)) {x : Fin M → ℝ}
    (hx : ImplicitLP.Interior κ m x) {w : Fin M → ℝ}
    (hlo : ∀ i, 4 / 5 * ImplicitLP.gfun κ m (1 - 1 / L₀) c₀ A x i ≤ w i)
    (hhi : ∀ i, w i ≤ 5 / 4 * ImplicitLP.gfun κ m (1 - 1 / L₀) c₀ A x i)
    {f h : Fin M → ℝ} {π₀ : Fin r → ℝ} (hh1 : Aᵀ *ᵥ h = 0)
    (hh2 : ∀ i, f i + w i * ImplicitLP.barS κ m x i ^ 2 * h i = (A *ᵥ π₀) i) :
    (⨅ ν, ImplicitLP.mixed (48 * (2 * L₀)) w
        (fun i => (f i - (A *ᵥ ν) i) / (w i * ImplicitLP.barS κ m x i))) ≤
      ImplicitLP.mixed (48 * (2 * L₀)) w (fun i => ImplicitLP.barS κ m x i * h i) ∧
    ImplicitLP.mixed (48 * (2 * L₀)) w (fun i => ImplicitLP.barS κ m x i * h i) ≤
      (1 + 1 / (16 * (2 * L₀))) * ⨅ ν, ImplicitLP.mixed (48 * (2 * L₀)) w
        (fun i => (f i - (A *ᵥ ν) i) / (w i * ImplicitLP.barS κ m x i)) :=
  ImplicitLP.eq_projection_note hA hrow hL hLM hκ hc₀ hcM hx hlo hhi hh1 hh2

-- `eq:gsize`: `Σ g = r + M c₀` and `c₀ < gᵢ ≤ 1 + c₀`.
example {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {p : ℝ} (hA : (Aᵀ * A).det ≠ 0)
    (hrow : ∀ i, A i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2) (c₀ : ℝ) :
    (∑ i, (Real.exp (ImplicitLP.lewisLog p A i) + c₀) = r + M * c₀) ∧
      ∀ i, c₀ < Real.exp (ImplicitLP.lewisLog p A i) + c₀ ∧
        Real.exp (ImplicitLP.lewisLog p A i) + c₀ ≤ 1 + c₀ :=
  ImplicitLP.eq_gsize hA hrow hp0 hp2 c₀

-- `eq:wmove` (Lee–Sidford Lemma 17), for any positive weights and `|φ'| ≤ S`.
example {M r : ℕ} {C : ℝ} {A : Matrix (Fin M) (Fin r) ℝ} {S dφ c : Fin M → ℝ} (hC : 0 < C)
    (hS : ∀ i, 0 < S i) (hdφ : ∀ i, |dφ i| ≤ S i) (t : ℝ) {w w' : Fin M → ℝ}
    (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    (ha : ImplicitLP.mixed C w (fun i => Real.log (w' i) - Real.log (w i)) ≤ 1 / 10) :
    ImplicitLP.cent C A S dφ c t w' ≤
      (1 + 4 * ImplicitLP.mixed C w (fun i => Real.log (w' i) - Real.log (w i))) *
        (ImplicitLP.cent C A S dφ c t w +
          ImplicitLP.mixed C w (fun i => Real.log (w' i) - Real.log (w i))) :=
  ImplicitLP.eq_wmove hC hS hdφ t hw hw' ha

-- Attainment (Lee–Sidford audit, gap G8): the centrality minimum over `ν` is attained.
example {M r : ℕ} {C : ℝ} {A : Matrix (Fin M) (Fin r) ℝ} {S dφ c : Fin M → ℝ} (hC : 0 < C)
    (hA : (Aᵀ * A).det ≠ 0) (hS : ∀ i, 0 < S i) (t : ℝ) {w : Fin M → ℝ} (hw : ∀ i, 0 < w i) :
    ∃ ν, ImplicitLP.cent C A S dφ c t w =
      ImplicitLP.mixed C w (fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i)) :=
  ImplicitLP.cent_attained hC hA hS t hw

-- Frozen-weight centers (Lee–Sidford audit, gap G8): given a strictly feasible point, the weighted barrier
-- objective has a minimizer, and minimizers are unique.
example {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c w : Fin M → ℝ} {t : ℝ}
    (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i) {x₀ : Fin M → ℝ}
    (hx₀ : x₀ ∈ ImplicitLP.Feasible A b κ m) :
    ∃! y, y ∈ ImplicitLP.Feasible A b κ m ∧ ∀ y' ∈ ImplicitLP.Feasible A b κ m,
      ImplicitLP.centerObj κ m c w t y ≤ ImplicitLP.centerObj κ m c w t y' := by
  obtain ⟨y, hy, hmin⟩ := ImplicitLP.center_exists (c := c) (t := t) hκ hw hx₀
  exact ⟨y, ⟨hy, hmin⟩, fun y' ⟨hy', hmin'⟩ =>
    ImplicitLP.center_unique hκ hw hy' hy hmin' hmin⟩

-- D7 `eq:newton` (`lem:newton`): a perturbed exactly-feasible Newton step with absolute error
-- `η` keeps the point interior and gives `δ_new ≤ 8δ² + 4η`; `η = 0` is allowed.
example {M r : ℕ} {κ m x w c : Fin M → ℝ} {t C : ℝ} {A : Matrix (Fin M) (Fin r) ℝ}
    (hκ : ∀ i, 0 < κ i) (hC : 0 < C) (hx : ImplicitLP.Interior κ m x) (hw : ∀ i, 0 < w i)
    {h e : Fin M → ℝ} {π₀ : Fin r → ℝ} (hh1 : Aᵀ *ᵥ h = 0)
    (hh2 : ∀ i, t * c i + w i * ImplicitLP.barDphi κ m x i +
      w i * ImplicitLP.barS κ m x i ^ 2 * h i = (A *ᵥ π₀) i)
    (he1 : Aᵀ *ᵥ e = 0) {γ δ η : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 17 / 16) (hδ : 0 ≤ δ)
    (hSh : ImplicitLP.mixed C w (fun i => ImplicitLP.barS κ m x i * h i) ≤ γ * δ)
    (he : ImplicitLP.mixed C w (fun i => ImplicitLP.barS κ m x i * e i) ≤ η)
    (ha : γ * δ + η ≤ 1 / 10) :
    ImplicitLP.Interior κ m (x + (h + e)) ∧ Aᵀ *ᵥ (h + e) = 0 ∧
      ImplicitLP.cent C A (ImplicitLP.barS κ m (x + (h + e)))
        (ImplicitLP.barDphi κ m (x + (h + e))) c t w ≤ 8 * δ ^ 2 + 4 * η :=
  ImplicitLP.eq_newton hκ hC hx hw hh1 hh2 he1 hγ0 hγ hδ hSh he ha

-- D7 exact repair through the explicit `+I_r` rows: `Aᵀd = 0` and
-- `‖d − h‖_∞ ≤ (1 + √2 M)‖h̃ − h‖_∞`.
example {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {ι : Fin r → Fin M}
    (hι : ImplicitLP.IdRows A ι) (hA : ∀ i j, |A i j| ≤ Real.sqrt 2) {h h' : Fin M → ℝ}
    (hh : Aᵀ *ᵥ h = 0) :
    Aᵀ *ᵥ ImplicitLP.repairDir A ι h' = 0 ∧
      ‖ImplicitLP.repairDir A ι h' - h‖ ≤ (1 + Real.sqrt 2 * M) * ‖h' - h‖ :=
  ⟨ImplicitLP.repair_feasible hι h', ImplicitLP.repair_error hι hA hh⟩

-- D7 inexact Lewis iteration: per-step error `ζ` gives `E_j ≤ (1 − p/2)^j E₀ + ζ/(p/2)`.
example {M r : ℕ} {B : Matrix (Fin M) (Fin r) ℝ} {p : ℝ} (hB : (Bᵀ * B).det ≠ 0)
    (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2) {ζ : ℝ} (hζ : 0 ≤ ζ)
    {y : ℕ → Fin M → ℝ} (hy : ∀ j, dist (y (j + 1)) (ImplicitLP.lewisMap p B (y j)) ≤ ζ) (j : ℕ) :
    dist (y j) (ImplicitLP.lewisLog p B) ≤
      (1 - p / 2) ^ j * dist (y 0) (ImplicitLP.lewisLog p B) + ζ / (p / 2) :=
  ImplicitLP.inexact_iter hB hrow hp0 hp2 hζ hy (ImplicitLP.lewisLog_fixed hB hrow hp0 hp2) j

-- D7 `eq:lewisfloor`: Lewis weights are bounded below by the least leverage score of `B`.
example {M r : ℕ} {B : Matrix (Fin M) (Fin r) ℝ} {p : ℝ} (hB : (Bᵀ * B).det ≠ 0)
    (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p) (hp2 : p < 2) {q : ℝ}
    (hq : ∀ k, q ≤ ImplicitLP.lev B k) (i : Fin M) :
    q ≤ Real.exp (ImplicitLP.lewisLog p B i) :=
  ImplicitLP.lewis_floor hB hrow hp0 hp2 hq i

-- D7 `lem:slack`: center slack from an interior reference.
example {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c w : Fin M → ℝ} {t : ℝ}
    (hκ : ∀ i, 0 < κ i) {wmin : ℝ} (hwmin : 0 < wmin) (hw : ∀ i, wmin ≤ w i)
    {xbar x₀ : Fin M → ℝ} (hxbar : xbar ∈ ImplicitLP.Feasible A b κ m)
    (hx₀ : x₀ ∈ ImplicitLP.Feasible A b κ m)
    (hmin : ∀ y ∈ ImplicitLP.Feasible A b κ m,
      ImplicitLP.centerObj κ m c w t xbar ≤ ImplicitLP.centerObj κ m c w t y)
    {s₀ U D : ℝ} (hs₀ : 0 < s₀) (hs0 : ∀ i, s₀ ≤ (Real.pi / 2 - |ImplicitLP.theta κ m x₀ i|) / κ i)
    (hU : ∀ i, Real.pi / κ i ≤ U) (hD : |t| * ‖c‖ * M * U + ∑ i, w i ≤ D) (i : Fin M) :
    min (s₀ / 2) (wmin * s₀ / (4 * D)) ≤ (Real.pi / 2 - |ImplicitLP.theta κ m xbar i|) / κ i :=
  ImplicitLP.lem_slack hκ hwmin hw hxbar hx₀ hmin hs₀ hs0 hU hD i

-- D7 the exact Newton direction exists, is feasible and stationary, and is unique.
example {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} (hA : (Aᵀ * A).det ≠ 0) {w S q : Fin M → ℝ}
    (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) :
    Aᵀ *ᵥ ImplicitLP.newtonDir A w S q = 0 ∧
      ∀ i, q i + w i * S i ^ 2 * ImplicitLP.newtonDir A w S q i =
        (A *ᵥ ImplicitLP.newtonPot A w S q) i :=
  ImplicitLP.newtonDir_spec hA hw hS

-- D7 `lem:center`: an approximately central point is close to the frozen-weight center, with
-- slacks within a factor two and `‖x − x̄‖_∞ ≤ 4U δ`.
example {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {b : Fin r → ℝ} {κ m c w : Fin M → ℝ} {t : ℝ}
    (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ U : ℝ} (hc₀ : 0 ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) (hUnn : 0 ≤ U) (hU : ∀ i, Real.pi / κ i ≤ U) {x : Fin M → ℝ}
    (hx : x ∈ ImplicitLP.Feasible A b κ m) (hw : ∀ i, 0 < w i)
    (hwin : ∀ i, |Real.log (w i) - Real.log (ImplicitLP.gfun κ m (1 - 1 / L₀) c₀ A x i)| ≤ 1 / 20)
    (hδ : ImplicitLP.cent (48 * (2 * L₀)) A (ImplicitLP.barS κ m x) (ImplicitLP.barDphi κ m x)
      c t w ≤ 1 / 1000)
    {xbar : Fin M → ℝ} (hxbar : xbar ∈ ImplicitLP.Feasible A b κ m)
    (hmin : ∀ y ∈ ImplicitLP.Feasible A b κ m,
      ImplicitLP.centerObj κ m c w t xbar ≤ ImplicitLP.centerObj κ m c w t y) :
    (∀ i, ImplicitLP.slk κ m x i / 2 ≤ ImplicitLP.slk κ m xbar i ∧
      ImplicitLP.slk κ m xbar i ≤ 2 * ImplicitLP.slk κ m x i) ∧
      ‖x - xbar‖ ≤ 4 * U * ImplicitLP.cent (48 * (2 * L₀)) A (ImplicitLP.barS κ m x)
        (ImplicitLP.barDphi κ m x) c t w :=
  ImplicitLP.lem_center hA hrow hL hLM hκ hc₀ hcM hUnn hU hx hw hwin hδ hxbar hmin

-- D7 `lem:chase`: chasing with an approximate sign-aligned support point decreases the
-- potential by a factor `1 − λ` up to additive `ξMC_*/(3Δ) + 2σ`.
example {M : ℕ} {U : Set (Fin M → ℝ)} {Cs T₀ : ℝ} (hU : ImplicitLP.ChaseSet U Cs T₀)
    {μ Δ ξ σ : ℝ} (hΔ : 0 < Δ) (hξ : 0 < ξ) (hξ8 : ξ ≤ 1 / 8) (hμ : μ = ξ / (12 * Δ))
    (hCs0 : 0 ≤ Cs) (hCsΔ : Cs ≤ Δ) (hT₀ : 1 ≤ T₀) (hσ0 : 0 ≤ σ) {X y u z v : Fin M → ℝ}
    (hu : u ∈ U) (hz : ∀ i, |z i - (y i + u i)| ≤ Δ) (hv : v ∈ U)
    (hal : ∀ i, 0 ≤ v i * (X i - z i))
    (hopt : ImplicitLP.supp U (ImplicitLP.potGrad μ (X - z)) - σ ≤
      ImplicitLP.potGrad μ (X - z) ⬝ᵥ v) :
    ImplicitLP.pot μ (X - (1 + ξ) • v - (y + u)) ≤
      (1 - ξ ^ 2 * Cs / (30 * Δ * T₀)) * ImplicitLP.pot μ (X - y) +
        ξ * M * Cs / (3 * Δ) + 2 * σ :=
  ImplicitLP.lem_chase hU hΔ hξ hξ8 hμ hCs0 hCsΔ hT₀ hσ0 hu hz hv hal hopt

-- D7 support oracle, fixed-τ evaluator contract (exact evaluations): a feasible, sign-aligned
-- `ẑ` with `ℓ = f_ρ(ẑ) ≤ G_ρ(τ) ≤ u` and `u − ℓ ≤ Λ²‖a‖₂/(ρ² 2ⁿ)`.
example {M : ℕ} {κ a : Fin M → ℝ} {ρ : ℝ} (hκ : ∀ i, 0 < κ i) (hρ : 0 < ρ) {τ Λ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hΛ : 0 ≤ Λ)
    (hΛr : ImplicitLP.euc (ImplicitLP.zlam a κ ρ τ Λ) ≤ 1 - τ) (n : ℕ) :
    ∃ zh : Fin M → ℝ, ∃ ℓ u : ℝ, zh ∈ ImplicitLP.Fset κ τ ∧ (∀ i, 0 ≤ a i * zh i) ∧
      ℓ = ImplicitLP.fobj a ρ zh ∧ ℓ ≤ ImplicitLP.Gval a κ ρ τ ∧ ImplicitLP.Gval a κ ρ τ ≤ u ∧
      u - ℓ ≤ Λ ^ 2 * ImplicitLP.euc a / (ρ ^ 2 * 2 ^ n) :=
  ImplicitLP.evaluator hκ hρ hτ hΛ hΛr n

-- Directed weighted certificates W2 (`lem:rooted-cover`): in a forest oriented toward its roots,
-- a cover with private witnesses satisfies `Σᵢ (|δ⁻(Tᵢ)| + |Tᵢ ∩ R|) ≥ m`.
example {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (F : FractionalForest.RootedForest V) (T : ι → Finset V) (hcov : ∀ v, ∃ i, v ∈ T i)
    (hpriv : ∀ i, ∃ v, v ∈ T i ∧ ∀ j, j ≠ i → v ∉ T j) :
    Fintype.card ι ≤ ∑ i, (F.inArcs (T i) + F.rootCount (T i)) :=
  F.rooted_cover T hcov hpriv

-- D7 item 5, the frozen normal solve: a `Good` D4 output preconditions `Πᵀ L_G Π + E`, and
-- `k` Richardson steps from `0` reach relative energy error `β²` once `2ᵏβ ≥ 1`.
example {r n : ℕ} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ} {K t R : ℕ} {δ ε : ℝ}
    {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G w K t δ R out) (hw0 : ∀ e, 0 ≤ w e)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    (Pz : Matrix (Fin n) (Fin r) ℝ) {E : Matrix (Fin r) (Fin r) ℝ} (hEs : Eᵀ = E)
    {dmin : ℝ} (hdmin : 0 < dmin) (hE : ∀ x, dmin * ImplicitLP.euc x ^ 2 ≤ x ⬝ᵥ (E *ᵥ x))
    (b xs : Fin r → ℝ)
    (hxs : (ImplicitLP.pullLap Pz (Sparsify.omegaR G w 0)
      (Finset.univ.filter fun e => Sparsify.P0 w e = true) + E) *ᵥ xs = b)
    {β : ℝ} (k : ℕ) (hk : 1 ≤ β * 2 ^ k) :
    let L := ImplicitLP.pullLap Pz (Sparsify.omegaR G w 0)
      (Finset.univ.filter fun e => Sparsify.P0 w e = true) + E
    let P := ImplicitLP.pullLap Pz out Finset.univ + E
    let step : (Fin r → ℝ) → Fin r → ℝ := fun x => x + P⁻¹ *ᵥ (b - L *ᵥ x)
    P.det ≠ 0 ∧ (step^[k] 0 - xs) ⬝ᵥ (L *ᵥ (step^[k] 0 - xs)) ≤ β ^ 2 * (xs ⬝ᵥ (L *ᵥ xs)) :=
  ImplicitLP.frozen_solve hgood hw0 hε0 hε hδlo hδhi Pz hEs hdmin hE b xs hxs k hk

-- D7 item 5 with rounding: a per-step error `τ` in `‖·‖_L` leaves `‖xₖ − x*‖_L ≤ 2⁻ᵏ‖x*‖_L + 2τ`.
example {r : ℕ} {L : Matrix (Fin r) (Fin r) ℝ} (hL : Lᵀ = L)
    (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (L *ᵥ x)) {step : (Fin r → ℝ) → Fin r → ℝ} {xs : Fin r → ℝ}
    (hc : ∀ x, ImplicitLP.enorm L (step x - xs) ≤ 1 / 2 * ImplicitLP.enorm L (x - xs))
    (x : ℕ → Fin r → ℝ) {τ : ℝ} (herr : ∀ j, ImplicitLP.enorm L (x (j + 1) - step (x j)) ≤ τ)
    (k : ℕ) :
    ImplicitLP.enorm L (x k - xs) ≤
      (1 / 2) ^ k * ImplicitLP.enorm L (x 0 - xs) + 2 * τ * (1 - (1 / 2) ^ k) :=
  ImplicitLP.richardson_inexact hL hpsd hc x herr k

-- D7 item 5 assembled: the LP's frozen normal matrix is the hidden Laplacian (D4's input
-- energy) plus the explicit part.
example {M n : ℕ} {A : Matrix (Fin M) (Fin n) ℝ} {D : Fin M → ℝ}
    (hid : Fin M → Option (Sym2 (Fin n))) (G : DiGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (hrow : ∀ i e, hid i = some e → Matrix.vecMulVec (A i) (A i) = Spectral.pairMat e)
    (hD : ∀ i e, hid i = some e → D i = w e) (hDpos : ∀ i, 0 < D i)
    (hcount : ∀ e, (Finset.univ.filter fun i => hid i = some e).card = Spanner.symS G e) :
    ImplicitLP.gram A D = Spectral.lap (Sparsify.omegaR G w 0)
      (Finset.univ.filter fun e => Sparsify.P0 w e = true) + ImplicitLP.explicitGram A D hid :=
  ImplicitLP.gram_split hid G w hrow hD hDpos hcount

-- D7 item 5 as a query program: `k` refinement steps cost at most `k · 6Bn` queries.
example {n : ℕ} (G : DiGraph (Fin n)) (w : Sym2 (Fin n) → ℝ) (ew : ℤ) (p B : ℕ)
    (E Pinv : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ) :
    (ImplicitLP.frozenSolveProg w ew p B E Pinv b k x).cost G.out ≤ k * (6 * B * n) :=
  ImplicitLP.frozenSolveProg_cost G w ew p B E Pinv b k x

-- W5 `lem:flow`: `18n` queries certify `d(S) ≤ F_{G'}(S)` in every consistent competitor.
example {V : Type*} [Fintype V] [DecidableEq V] (G : DirectedCertificate.WeightedDiGraph V)
    {f : V → V → ℝ} (hf : G.Feasible f) :
    ∃ Q : Finset (Finset V), Q.card ≤ 18 * Fintype.card V ∧
      ∀ G' : DirectedCertificate.WeightedDiGraph V, DirectedCertificate.Consistent G G' Q →
        ∀ S : Finset V, ∑ v ∈ S, Certificate.netOut f v ≤ G'.out S :=
  DirectedCertificate.exists_flowCert_directed G hf

-- D7: the directed LP's rows satisfy the split hypotheses, so its frozen Gram is the hidden
-- Laplacian plus the explicit part.
example {n : ℕ} (G : DiGraph (Fin n)) (s t : Fin n) {w : Sym2 (Fin n) → ℝ} {dq : ℝ}
    {dp dm : Fin n → ℝ} (hDpos : ∀ i, 0 < ImplicitLP.lpD G w dq dp dm i) :
    ImplicitLP.gram (ImplicitLP.lpA G s t) (ImplicitLP.lpD G w dq dp dm) =
      Spectral.lap (Sparsify.omegaR G w 0) (Finset.univ.filter fun e => Sparsify.P0 w e = true) +
        ImplicitLP.explicitGram (ImplicitLP.lpA G s t) (ImplicitLP.lpD G w dq dp dm)
          (ImplicitLP.lpHidF G) :=
  ImplicitLP.lp_gram_split G s t hDpos

-- Directed weighted certificates W0: a zero cut is a one-query witness certificate, and every
-- witness certificate is a value certificate.
example {V : Type*} [Fintype V] [DecidableEq V] (G : DirectedCertificate.WeightedDiGraph V)
    {S : Finset V} (hS : ProperShore S) (h0 : G.out S = 0) :
    DirectedCertificate.IsMinCutWitnessCertificate G {S} S :=
  DirectedCertificate.zero_witnessCertificate G hS h0

-- W1 cut algebra: `2F(S) = c_U(S) + β(S)`.
example {V : Type*} [Fintype V] [DecidableEq V] (G : DirectedCertificate.WeightedDiGraph V)
    (S : Finset V) : 2 * G.out S = G.sym.cut S + ∑ v ∈ S, G.imbalance v :=
  G.two_mul_out S

-- W3: if every nonempty shore avoiding `r` has outgoing capacity at least `λ`, some
-- nonnegative combination of in-arborescences toward `r` (over the fixed finite set `InArb r`)
-- has total weight exactly `λ` and arc loads within the capacities.
example {V : Type*} [Fintype V] [DecidableEq V] (G : DirectedCertificate.WeightedDiGraph V)
    (r : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S) :
    ∃ a : DirectedCertificate.InArb r → ℝ, (∀ T, 0 ≤ a T) ∧ (∑ T, a T = lam) ∧
      ∀ u v, DirectedCertificate.load a u v ≤ G.c u v :=
  DirectedCertificate.exists_inArb_packing G r lam hlam hcut

-- W3: some packing of value `λ` has minimum total load `λ(|V|−1)` and at most
-- `2(|V|−1)` free arcs `0 < y u v < c u v`.
example {V : Type*} [Fintype V] [DecidableEq V] (G : DirectedCertificate.WeightedDiGraph V)
    (r : V) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S : Finset V, S.Nonempty → r ∉ S → lam ≤ G.out S) :
    ∃ a : DirectedCertificate.InArb r → ℝ, (∀ T, 0 ≤ a T) ∧ (∑ T, a T = lam) ∧
      (∀ u v, DirectedCertificate.load a u v ≤ G.c u v) ∧
      DirectedCertificate.total (DirectedCertificate.load a) = lam * ((Fintype.card V : ℝ) - 1) ∧
      (DirectedCertificate.freeArcs G (DirectedCertificate.load a)).card ≤
        2 * (Fintype.card V - 1) :=
  DirectedCertificate.exists_sparse_inArb_packing G r lam hlam hcut

-- W4: logarithm-free forest deletion, with no remaining hypothesis.
example {V : Type*} [Fintype V] [DecidableEq V] {x : WeightedGraph V}
    (hx : FractionalForest.IsFractionalForest x) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∃ Z : Finset V,
      Z.card ≤ (if k = 1 then Fintype.card V - 1 else FractionalForest.budgetQ (Fintype.card V) k) ∧
      ∀ S ⊆ Zᶜ, FractionalForest.mass x S ≤ (1 - 1 / (k : ℝ)) * S.card :=
  FractionalForest.forest_deletion_main hx hk hkn

-- W4: the small common source set.
example {V : Type*} [Fintype V] [DecidableEq V] (H : DirectedCertificate.WeightedDiGraph V) (r : V)
    {lam : ℝ} (hlam : 0 < lam) (a b : DirectedCertificate.InArb r → ℝ) (ha : ∀ T, 0 ≤ a T)
    (hasum : ∑ T, a T = lam) (haload : ∀ u v, DirectedCertificate.load a u v ≤ H.c u v)
    (hb : ∀ T, 0 ≤ b T) (hbsum : ∑ T, b T = lam)
    (hbload : ∀ u v, DirectedCertificate.outLoad b u v ≤ H.c u v)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∃ R : Finset V, r ∈ R ∧ R.card ≤ 4 * (FractionalForest.ceilA (Fintype.card V) k - 1) + 1 ∧
      ∀ S : Finset V, Disjoint S R → lam / k * S.card ≤ H.out S ∧ lam / k * S.card ≤ H.out Sᶜ :=
  DirectedCertificate.small_source_set_main H r hlam a b ha hasum haload hb hbsum hbload hk hkn

-- The in-arborescence carrier: arcs `v → p v`, oriented toward the root.
example {V : Type*} [Fintype V] [DecidableEq V] (r : V) (p : V → Option V) :
    DirectedCertificate.IsInArb r p ↔
      p r = none ∧ (∀ v, v ≠ r → p v ≠ none) ∧ (∀ v, p v ≠ some v) ∧
        ∀ v, ∃ n : ℕ, (DirectedCertificate.parentStep p)^[n] (some v) = none :=
  ⟨fun h => ⟨h.root, h.nonroot, h.irrefl, h.acyclic⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

-- Directed weighted certificates W1: real-capacity max-flow/min-cut and the uniform supply form.
example {V : Type*} [Fintype V] [DecidableEq V] (G : DirectedCertificate.WeightedDiGraph V)
    {s t : V} (hst : s ≠ t) :
    ∃ f S, G.STFlow s t f ∧ s ∈ S ∧ t ∉ S ∧ Certificate.netOut f s = G.out S ∧
      (∀ g, G.STFlow s t g → Certificate.netOut g s ≤ Certificate.netOut f s) ∧
      (∀ S', s ∈ S' → t ∉ S' → G.out S ≤ G.out S') :=
  G.maxFlow_minCut hst

example {V : Type*} [Fintype V] [DecidableEq V] (G : DirectedCertificate.WeightedDiGraph V)
    (β : ℝ) (hβ : 0 ≤ β) (R : Finset V) :
    (∀ S, Disjoint S R → β * S.card ≤ G.out S) ↔
      ∃ f, G.Feasible f ∧ (∀ v, v ∉ R → Certificate.netOut f v = β) ∧
        ∀ v ∈ R, Certificate.netOut f v ≤ 0 :=
  G.uniform_supply_iff β hβ R

open CutQueryComplexityChecks.AxiomAudit

#audit_cut_axioms [
    CutQueryComplexity.Graph.Capacity,
    CutQueryComplexity.Graph.Bottleneck,
    CutQueryComplexity.Graph.EdgeInsertion,
    CutQueryComplexity.Graph.ForestFacts,
    CutQueryComplexity.Graph.Integral,
    CutQueryComplexity.Graph.InducedCut,
    CutQueryComplexity.Graph.StrongComponent,
    CutQueryComplexity.Graph.Mass,
    CutQueryComplexity.Graph.Operations,
    CutQueryComplexity.Graph.RandomMean,
    CutQueryComplexity.Graph.CutConcentration,
    CutQueryComplexity.Graph.EdgeSum,
    CutQueryComplexity.Graph.IndependentSum,
    CutQueryComplexity.Graph.RespectingCuts,
    CutQueryComplexity.Graph.ContractionCounting,
    CutQueryComplexity.Graph.VertexRestriction,
    CutQueryComplexity.Graph.Weighted,
    CutQueryComplexity.Model.Complexity,
    CutQueryComplexity.Model.Composition,
    CutQueryComplexity.Model.Deterministic,
    CutQueryComplexity.Model.Randomized,
    CutQueryComplexity.Model.RandomizedComposition,
    CutQueryComplexity.Model.RandomizedReduction,
    CutQueryComplexity.Model.Reduction,
    CutQueryComplexity.Primitive.BinarySearch,
    CutQueryComplexity.Primitive.Certificate,
    CutQueryComplexity.Primitive.CrossSearch,
    CutQueryComplexity.Primitive.Forest,
    CutQueryComplexity.Primitive.ForestPartition,
    CutQueryComplexity.Primitive.Learn,
    CutQueryComplexity.Primitive.Reductions,
    CutQueryComplexity.Primitive.Residual,
    CutQueryComplexity.Primitive.ResidualDegree,
    CutQueryComplexity.Primitive.ResidualSample,
    CutQueryComplexity.Primitive.ResidualEdge,
    CutQueryComplexity.Primitive.ResidualCache,
    CutQueryComplexity.Primitive.HeavySearch,
    CutQueryComplexity.Primitive.HeavyCross,
    CutQueryComplexity.Primitive.HeavyResidual,
    CutQueryComplexity.Primitive.SubsetSample,
    CutQueryComplexity.Primitive.WeightedSample,
    CutQueryComplexity.Probability.Events,
    CutQueryComplexity.Probability.Expectation,
    CutQueryComplexity.Probability.FiniteEvents,
    CutQueryComplexity.Probability.Exponential,
    CutQueryComplexity.Probability.BoundedDraw,
    CutQueryComplexity.Probability.Chernoff,
    CutQueryComplexity.Probability.Categorical,
    CutQueryComplexity.Probability.PairSample,
    CutQueryComplexity.Probability.OptionBind,
    CutQueryComplexity.Probability.UndirectedPair,
    CutQueryComplexity.Probability.Truncation,
    CutQueryComplexity.Probability.WeightedChoice,
    CutQueryComplexity.Problem.Basic,
    CutQueryComplexity.Problem.Sparsifier,
    CutQueryComplexity.Sparsification.Strength,
    CutQueryComplexity.Sparsification.StrengthRestriction,
    CutQueryComplexity.Sparsification.StrongContraction,
    CutQueryComplexity.Sparsification.StrengthSum,
    CutQueryComplexity.Sparsification.ResidualStrength,
    CutQueryComplexity.Sparsification.KruskalInvariant,
    CutQueryComplexity.Sparsification.ApproxKruskal,
    CutQueryComplexity.Sparsification.StrongComponentCount,
    CutQueryComplexity.Sparsification.StrengthLevels,
    CutQueryComplexity.Sparsification.StrengthCoefficients,
    CutQueryComplexity.Sparsification.ComponentNormalization,
    CutQueryComplexity.Sparsification.StrengthDecomposition,
    CutQueryComplexity.Sparsification.RandomDecomposition,
    CutQueryComplexity.Sparsification.ComponentConcentration,
    CutQueryComplexity.Sparsification.CountedSampling,
    CutQueryComplexity.Sparsification.CountedConcentration,
    CutQueryComplexity.Sparsification.CutCounting,
    CutQueryComplexity.Sparsification.LocalCutCounting,
    CutQueryComplexity.Sparsification.CutTailBound,
    CutQueryComplexity.Sparsification.EstimateSound,
    CutQueryComplexity.Sparsification.EstimateComplete,
    CutQueryComplexity.Sparsification.EstimateResidual,
    CutQueryComplexity.Sparsification.EstimateProgram,
    CutQueryComplexity.Sparsification.EstimateLift,
    CutQueryComplexity.Sparsification.EstimateCall,
    CutQueryComplexity.Sparsification.Window,
    CutQueryComplexity.Model.Iterate,
    CutQueryComplexity.Sparsification.Merge,
    CutQueryComplexity.Sparsification.EstimationRun,
    CutQueryComplexity.Sparsification.EstimationInvariant,
    CutQueryComplexity.Sparsification.EstimationTermination,
    CutQueryComplexity.Sparsification.EstimationEvents,
    CutQueryComplexity.Sparsification.EstimationCost,
    CutQueryComplexity.Sparsification.EstimationCharge,
    CutQueryComplexity.Sparsification.EstimationBudget,
    CutQueryComplexity.Sparsification.OutputSample,
    CutQueryComplexity.Sparsification.OutputRun,
    CutQueryComplexity.Sparsification.OutputCorrect,
    CutQueryComplexity.Sparsification.OutputBudget,
    CutQueryComplexity.Sparsification.OutputEdges,
    CutQueryComplexity.Sparsification.Weighted,
    CutQueryComplexity.Sparsification.WeightedParams,
    CutQueryComplexity.Model.Prog,
    CutQueryComplexity.MinCut.RootedTree,
    CutQueryComplexity.MinCut.Interest,
    CutQueryComplexity.MinCut.Search,
    CutQueryComplexity.Search.Comp,
    CutQueryComplexity.Search.SMAWK,
    CutQueryComplexity.Search.BinarySearch,
    CutQueryComplexity.Search.Combinators,
    CutQueryComplexity.TwoRespecting.Tree,
    CutQueryComplexity.TwoRespecting.Majority,
    CutQueryComplexity.TwoRespecting.HeavyPath,
    CutQueryComplexity.TwoRespecting.Cuts,
    CutQueryComplexity.TwoRespecting.Rect,
    CutQueryComplexity.TwoRespecting.Main,
    CutQueryComplexity.TwoRespecting.Respect,
    CutQueryComplexity.TwoRespecting.BFSTree,
    CutQueryComplexity.TwoRespecting.Packing,
    CutQueryComplexity.TwoRespecting.TreeCover,
    CutQueryComplexity.TwoRespecting.ProgInterface,
    CutQueryComplexity.Discovery.Quantile,
    CutQueryComplexity.Discovery.Normalization,
    CutQueryComplexity.Discovery.TreeCompression,
    CutQueryComplexity.Discovery.RowSearch,
    CutQueryComplexity.Discovery.ResidualPreparation,
    CutQueryComplexity.Discovery.Centers,
    CutQueryComplexity.Discovery.CenterSelection,
    CutQueryComplexity.Discovery.Auxiliary,
    CutQueryComplexity.Certificate.Flow,
    CutQueryComplexity.Certificate.MaxFlow,
    CutQueryComplexity.Certificate.FlowCert,
    CutQueryComplexity.Certificate.Isolating,
    CutQueryComplexity.Certificate.SplittingOff,
    CutQueryComplexity.Certificate.Halving,
    CutQueryComplexity.Certificate.Main,
    CutQueryComplexity.Certificate.LowerBound,
    CutQueryComplexity.Certificate.Windmill,
    CutQueryComplexity.Search.Subst,
    CutQueryComplexity.Hierarchy.Basic,
    CutQueryComplexity.Hierarchy.Children,
    CutQueryComplexity.Hierarchy.Error,
    CutQueryComplexity.Hierarchy.Completion,
    CutQueryComplexity.Hierarchy.RealError,
    CutQueryComplexity.Hierarchy.Supplied,
    CutQueryComplexity.Hierarchy.Guard,
    CutQueryComplexity.Hierarchy.Refine,
    CutQueryComplexity.Hierarchy.Initial,
    CutQueryComplexity.DetMinCut.Normalize,
    CutQueryComplexity.DetMinCut.Phase,
    CutQueryComplexity.DetMinCut.Main,
    CutQueryComplexity.DetMinCut.Asymptotic,
    CutQueryComplexity.Hierarchy.GuardConstant,
    CutQueryComplexity.DetMinCut.Parameters,
    CutQueryComplexity.DetMinCut.Budget,
    CutQueryComplexity.DetMinCut.MainLog7,
    CutQueryComplexity.DetMinCut.ParametersLog5,
    CutQueryComplexity.DetMinCut.BudgetLog5,
    CutQueryComplexity.DetMinCut.MainLog5,
    CutQueryComplexity.Hierarchy.Existence.Majority,
    CutQueryComplexity.Hierarchy.Existence.BandwidthPartition,
    CutQueryComplexity.Hierarchy.Existence.BalancedPartition,
    CutQueryComplexity.Hierarchy.Existence.Clusters,
    CutQueryComplexity.Hierarchy.Existence.Tree,
    CutQueryComplexity.Hierarchy.Existence,
    CutQueryComplexity.Hierarchy.GuardTransfer,
    CutQueryComplexity.Hierarchy.GuardDuality,
    CutQueryComplexity.Hierarchy.Retract.Grid,
    CutQueryComplexity.Hierarchy.Retract.Metric,
    CutQueryComplexity.Hierarchy.Retract.Bands,
    CutQueryComplexity.Hierarchy.Retract.Rounding,
    CutQueryComplexity.Hierarchy.Retract.TreeZeroExt,
    CutQueryComplexity.DetMinCut.Unconditional,
    CutQueryComplexity.Graph.Directed,
    CutQueryComplexity.Primitive.DirectedReductions,
    CutQueryComplexity.Primitive.OrderedSearch,
    CutQueryComplexity.Primitive.DyadicAggregate,
    CutQueryComplexity.Spectral.Energy,
    CutQueryComplexity.Spectral.Bundle,
    CutQueryComplexity.Spectral.MatrixNorm,
    CutQueryComplexity.Spectral.QuarterSampling,
    CutQueryComplexity.Spectral.Normalize,
    CutQueryComplexity.Spectral.OneRound,
    CutQueryComplexity.Spanner.Reach,
    CutQueryComplexity.Spanner.Trial,
    CutQueryComplexity.Spanner.Bundle,
    CutQueryComplexity.Spanner.Random,
    CutQueryComplexity.Spanner.Query,
    CutQueryComplexity.Spanner.Capped,
    CutQueryComplexity.Sparsify.Bundle,
    CutQueryComplexity.Sparsify.Level,
    CutQueryComplexity.Sparsify.Recursion,
    CutQueryComplexity.Sparsify.Main,
    CutQueryComplexity.Sparsify.Params,
    CutQueryComplexity.Sparsify.Asymptotic,
    CutQueryComplexity.Sparsify.Structure,
    CutQueryComplexity.ImplicitLP.LewisJacobian,
    CutQueryComplexity.ImplicitLP.MatrixCalculus,
    CutQueryComplexity.ImplicitLP.Leverage,
    CutQueryComplexity.ImplicitLP.Lewis,
    CutQueryComplexity.ImplicitLP.LewisDeriv,
    CutQueryComplexity.ImplicitLP.Movement,
    CutQueryComplexity.ImplicitLP.GMove,
    CutQueryComplexity.ImplicitLP.Projection,
    CutQueryComplexity.ImplicitLP.Size,
    CutQueryComplexity.ImplicitLP.Centrality,
    CutQueryComplexity.ImplicitLP.Barrier,
    CutQueryComplexity.ImplicitLP.Attain,
    CutQueryComplexity.ImplicitLP.Center,
    CutQueryComplexity.ImplicitLP.Newton,
    CutQueryComplexity.ImplicitLP.Repair,
    CutQueryComplexity.ImplicitLP.LewisIter,
    CutQueryComplexity.ImplicitLP.Slack,
    CutQueryComplexity.ImplicitLP.NewtonDir,
    CutQueryComplexity.ImplicitLP.CenterClose,
    CutQueryComplexity.ImplicitLP.SlackFloor,
    CutQueryComplexity.ImplicitLP.Chase,
    CutQueryComplexity.ImplicitLP.Batch,
    CutQueryComplexity.ImplicitLP.BatchFull,
    CutQueryComplexity.ImplicitLP.Support,
    CutQueryComplexity.ImplicitLP.Trisection,
    CutQueryComplexity.ImplicitLP.SupportMain,
    CutQueryComplexity.ImplicitLP.NormalPerturb,
    CutQueryComplexity.ImplicitLP.Refine,
    CutQueryComplexity.Graph.FractionalForest,
    CutQueryComplexity.FractionalForest.RootedCover,
    CutQueryComplexity.ImplicitLP.FrozenSolve,
    CutQueryComplexity.ImplicitLP.FrozenInexact,
    CutQueryComplexity.ImplicitLP.HiddenGram,
    CutQueryComplexity.ImplicitLP.FrozenQuery,
    CutQueryComplexity.ImplicitLP.Aggregate,
    CutQueryComplexity.ImplicitLP.LPRows,
    CutQueryComplexity.ImplicitLP.LewisLev,
    CutQueryComplexity.ImplicitLP.NewtonQuery,
    CutQueryComplexity.ImplicitLP.LewisFloor,
    CutQueryComplexity.ImplicitLP.SupportAgg,
    CutQueryComplexity.ImplicitLP.NormalBounds,
    CutQueryComplexity.ImplicitLP.NumericLP,
    CutQueryComplexity.ImplicitLP.NewtonStep,
    CutQueryComplexity.ImplicitLP.SupportRound,
    CutQueryComplexity.ImplicitLP.Precision,
    CutQueryComplexity.ImplicitLP.PublicParams,
    CutQueryComplexity.ImplicitLP.LewisStage,
    CutQueryComplexity.ImplicitLP.BatchPub,
    CutQueryComplexity.ImplicitLP.BatchProg,
    CutQueryComplexity.ImplicitLP.MixedEnvelope,
    CutQueryComplexity.Graph.WeightedDirected,
    CutQueryComplexity.DirectedCertificate.Basic,
    CutQueryComplexity.DirectedCertificate.Flow,
    CutQueryComplexity.Graph.ArborescencePacking,
    CutQueryComplexity.DirectedCertificate.SparseBranching,
    CutQueryComplexity.FractionalForest.Potential,
    CutQueryComplexity.FractionalForest.Deletion,
    CutQueryComplexity.DirectedCertificate.SourceSet,
    CutQueryComplexity.FractionalForest.Progress,
    CutQueryComplexity.DirectedCertificate.SourceSetMain,
    CutQueryComplexity.DirectedCertificate.FlowCert,
    CutQueryComplexity.DirectedCertificate.Orientation,
    CutQueryComplexity.DirectedCertificate.Pruning,
    CutQueryComplexity.DirectedCertificate.FlowMeasure,
    CutQueryComplexity.DirectedMincut.FlowDuality,
    CutQueryComplexity.DirectedMincut.LPReduction,
    CutQueryComplexity.DirectedMincut.Extraction,
    CutQueryComplexity.DirectedMincut.SmallShore,
    CutQueryComplexity.DirectedMincut.GlobalReduction,
    SLT.MatrixInfra.Basic,
    SLT.MatrixInfra.CourantFischer,
    SLT.MatrixInfra.MatCalc,
    SLT.RMT.Lieb,
    SLT.RMT.MatBern,
    CutQueryComplexity.MinCut.Contraction,
    CutQueryComplexity.MinCut.SpanTree,
    CutQueryComplexity.MinCut.TreePacking,
    CutQueryComplexity.MinCut.Weighted,
    CutQueryComplexity.Quantum.ClassicalCompiler,
    CutQueryComplexity.Quantum.Encoding,
    CutQueryComplexity.Quantum.Learn,
    CutQueryComplexity.Quantum.Model,
    CutQueryComplexity.Quantum.Reduction]
  pins [
    CutQueryComplexity.WeightedGraph.edge_eq_three_cuts,
    CutQueryComplexity.WeightedGraph.cut_submodular,
    CutQueryComplexity.CapacityGraph.cut_le,
    CutQueryComplexity.exists_isMinCut_of_two_le_card,
    CutQueryComplexity.DTree.cost_le,
    CutQueryComplexity.DTree.run_eq_of_agree,
    CutQueryComplexity.DTree.run_bind,
    CutQueryComplexity.RTree.cost_le,
    CutQueryComplexity.RTree.run_ofDeterministic,
    CutQueryComplexity.queryComplexity_empty,
    CutQueryComplexity.edgeRecovery_run,
    CutQueryComplexity.reconstruct_run,
    CutQueryComplexity.DTree.exists_quantum,
    CutQueryComplexity.Encoding.native_simulates_add,
    CutQueryComplexity.Encoding.add_simulates_native,
    CutQueryComplexity.capacityEdgeRecovery_quantum,
    CutQueryComplexity.capacityReconstruct_quantum,
    CutQueryComplexity.WeightedGraph.cut_contract,
    CutQueryComplexity.DTree.eval_substitute,
    CutQueryComplexity.RTree.run_bind,
    CutQueryComplexity.RTree.eval_substitute,
    CutQueryComplexity.RTree.bind_solves,
    CutQueryComplexity.crossQuery_run,
    CutQueryComplexity.inducedQuery_eval,
    CutQueryComplexity.deletionQuery_eval,
    CutQueryComplexity.findCross_logarithmic,
    CutQueryComplexity.sampleSubset_scaled,
    CutQueryComplexity.sampleNeighbor_uniform,
    CutQueryComplexity.sampleCross_logarithmic,
    CutQueryComplexity.sampleCross_zero,
    CutQueryComplexity.sampleCross_capacity,
    CutQueryComplexity.spanningForest_solves,
    CutQueryComplexity.thresholdCertificate_correct,
    CutQueryComplexity.IsThresholdCertificate.mincut_eq,
    CutQueryComplexity.RTree.eval_truncate,
    CutQueryComplexity.RTree.truncate_markov,
    CutQueryComplexity.RTree.truncate_solves,
    CutQueryComplexity.Coherent.substitute_run,
    CutQueryComplexity.WeightedGraph.exists_inducedMincut,
    CutQueryComplexity.WeightedGraph.IsStrong.union,
    CutQueryComplexity.WeightedGraph.strongComponent_strong,
    CutQueryComplexity.WeightedGraph.strongComponent_laminar,
    CutQueryComplexity.WeightedGraph.le_strength_iff,
    CutQueryComplexity.WeightedGraph.inducedMincut_pair,
    CutQueryComplexity.WeightedGraph.strength_induce_component,
    CutQueryComplexity.WeightedGraph.strength_trimWeak,
    CutQueryComplexity.WeightedGraph.strength_contract_of_lt,
    CutQueryComplexity.WeightedGraph.strength_sum_le,
    CutQueryComplexity.WeightedGraph.normalized_mincut_eq_one,
    CutQueryComplexity.WeightedGraph.residual_internalMass,
    CutQueryComplexity.WeightedGraph.residual_mass_formula,
    CutQueryComplexity.cacheBlockCuts_run,
    CutQueryComplexity.residualMassQuery_run,
    CutQueryComplexity.IsSparseCutSparsifier.trans_quarter,
    CutQueryComplexity.IsCutSparsifier.mincut_bounds,
    CutQueryComplexity.residualDegreeQuery_run,
    CutQueryComplexity.sampleResidual_scaled,
    CutQueryComplexity.sampleResidualEdge_law,
    CutQueryComplexity.sampleResidualEdge_zero,
    CutQueryComplexity.sampleResidualEdge_correct,
    CutQueryComplexity.sampleResidualFresh_law,
    CutQueryComplexity.sampleResidualFresh_solves,
    CutQueryComplexity.Probability.forgetOrientation_some,
    CutQueryComplexity.searchAverage_correct,
    CutQueryComplexity.findHeavyCross_correct,
    CutQueryComplexity.findHeavyResidual_correct,
    CutQueryComplexity.findHeavyResidualFresh_solves,
    CutQueryComplexity.mergeBlockCache_run,
    CutQueryComplexity.card_liveBlocks_merge,
    CutQueryComplexity.blockMerge_history_le,
    CutQueryComplexity.WeightedGraph.le_bottleneck_iff,
    CutQueryComplexity.WeightedGraph.bottleneck_pos_iff,
    CutQueryComplexity.WeightedGraph.bottleneck_le_strength,
    CutQueryComplexity.WeightedGraph.withEdge_true_weight,
    CutQueryComplexity.ForestPartition.merge_pair,
    CutQueryComplexity.WeightedGraph.blockCut_le_residualMass,
    CutQueryComplexity.WeightedGraph.strength_le_residualMass,
    CutQueryComplexity.KruskalInvariant.merge,
    CutQueryComplexity.IsApproxKruskalForest.prw_bounds,
    CutQueryComplexity.approxKruskal_solves,
    CutQueryComplexity.approxKruskal_query_bound,
    CutQueryComplexity.approxKruskal_pair_bounds,
    CutQueryComplexity.approxKruskal_edge_bound,
    CutQueryComplexity.WeightedGraph.strongComponents_at_mincut,
    CutQueryComplexity.WeightedGraph.strongComponents_subset_mincut_side,
    CutQueryComplexity.WeightedGraph.strongComponents_card_le,
    CutQueryComplexity.WeightedGraph.strength_component_mincut,
    CutQueryComplexity.WeightedGraph.positiveStrengths_card_le,
    CutQueryComplexity.sum_levelIncrements_le,
    CutQueryComplexity.WeightedGraph.sum_componentCoefficients_pair,
    CutQueryComplexity.WeightedGraph.componentCoefficient_pos,
    CutQueryComplexity.WeightedGraph.normalized_component_mincut_eq_one,
    CutQueryComplexity.WeightedGraph.inducedMincut_scale,
    CutQueryComplexity.WeightedGraph.strengthDecomposition_weight,
    CutQueryComplexity.WeightedGraph.strengthDecomposition_scaled_cut,
    CutQueryComplexity.WeightedGraph.strengthPiece_reference_mincut,
    CutQueryComplexity.WeightedGraph.strengthPiece_scaled_weight_le_one,
    CutQueryComplexity.WeightedGraph.exists_strengthDecomposition,
    CutQueryComplexity.WeightedGraph.isCutSparsifier_of_scaledStrengthPieces,
    CutQueryComplexity.Probability.expect_bind,
    CutQueryComplexity.Probability.expect_eq_zero_iff,
    CutQueryComplexity.Probability.mul_mass_le_expect,
    CutQueryComplexity.Probability.mass_failure_le_sum_bounds,
    CutQueryComplexity.Probability.expMoment_bind_add_le,
    CutQueryComplexity.Probability.expMoment_independentSum,
    CutQueryComplexity.Probability.upper_tail_le_exp,
    CutQueryComplexity.Probability.lower_tail_le_exp,
    CutQueryComplexity.WeightedGraph.hasMean_expectedGraph,
    CutQueryComplexity.WeightedGraph.HasMean.unique,
    CutQueryComplexity.WeightedGraph.HasMean.support,
    CutQueryComplexity.WeightedGraph.HasMean.cut,
    CutQueryComplexity.WeightedGraph.HasMean.strengthPieceLaw,
    CutQueryComplexity.WeightedGraph.IsSmooth.exists_decomposition,
    CutQueryComplexity.WeightedGraph.HasMean.sparsifier_failure_le_sum_bounds,
    CutQueryComplexity.WeightedGraph.HasMean.sparsifier_failure_le,
    CutQueryComplexity.WeightedGraph.HasMean.sparsifier_success,
    CutQueryComplexity.RTree.sparsifier_solves_of_piece_bounds,
    CutQueryComplexity.Probability.expMoment_le_of_unitInterval,
    CutQueryComplexity.Probability.BoundedDraw.expect_eq,
    CutQueryComplexity.Probability.BoundedDraw.expect_sumLaw_eq,
    CutQueryComplexity.Probability.BoundedDraw.expMoment_sumLaw_le,
    CutQueryComplexity.Probability.chernoff_upper,
    CutQueryComplexity.Probability.chernoff_lower,
    CutQueryComplexity.Probability.chernoff_two_sided,
    CutQueryComplexity.Probability.BoundedDraw.sum_two_sided,
    CutQueryComplexity.WeightedGraph.HasMean.cut_zero,
    CutQueryComplexity.WeightedGraph.HasMean.boundedCut_mean,
    CutQueryComplexity.WeightedGraph.HasMean.cut_concentration,
    CutQueryComplexity.WeightedGraph.cut_eq_inter_of_induce_eq,
    CutQueryComplexity.WeightedGraph.HasMean.sparsifier_failure_le_local_cut_sum,
    CutQueryComplexity.WeightedGraph.HasMean.sparsifier_failure_le_strength_cut_sum,
    CutQueryComplexity.WeightedGraph.HasMean.sparsifier_success_of_cut_tail_bounds,
    CutQueryComplexity.WeightedGraph.cut_edgeGraph,
    CutQueryComplexity.WeightedGraph.sumGraphs_replicate_scale,
    CutQueryComplexity.WeightedGraph.map_independentGraphSum,
    CutQueryComplexity.WeightedGraph.hasMean_independentGraphSum,
    CutQueryComplexity.WeightedGraph.independentGraphSum_boundedLaw,
    CutQueryComplexity.Probability.mem_support_categorical,
    CutQueryComplexity.Probability.expect_categorical,
    CutQueryComplexity.WeightedGraph.CountedBucket.drawLaw_mean,
    CutQueryComplexity.WeightedGraph.CountedBucket.expanded_length,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_mean,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_support,
    CutQueryComplexity.WeightedGraph.strengthPiece_edgeGraph_cut_le_one,
    CutQueryComplexity.WeightedGraph.CountedBucket.admissible_of_count,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_boundedCutLaw,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_failure_le_cut_sum,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_success_of_cut_tail_bounds,
    CutQueryComplexity.RespectsBlocks.pull_image,
    CutQueryComplexity.RespectsBlocks.merge_pair,
    CutQueryComplexity.card_respecting_le,
    CutQueryComplexity.liveBlocks_merge_pair_card,
    CutQueryComplexity.WeightedGraph.totalDegree_contract_ge,
    CutQueryComplexity.weighted_survivors_add_cuts,
    CutQueryComplexity.contraction_count_step,
    CutQueryComplexity.contractionCountBound_step,
    CutQueryComplexity.smallShoreFamily_card_le,
    CutQueryComplexity.WeightedGraph.nearMinShores_card_le,
    CutQueryComplexity.WeightedGraph.nearMinShores_card_le_pow,
    CutQueryComplexity.WeightedGraph.onVertices_cut_project,
    CutQueryComplexity.WeightedGraph.localNearMinShores_card_le,
    CutQueryComplexity.WeightedGraph.positiveLocalShores_bounded_card,
    CutQueryComplexity.WeightedGraph.strengthPiece_bounded_shores_card,
    CutQueryComplexity.WeightedGraph.sum_exp_le_of_threshold_count,
    CutQueryComplexity.WeightedGraph.strengthPiece_cutTailSum_le,
    CutQueryComplexity.WeightedGraph.strengthPiece_cutTailSum_le_of_exp,
    CutQueryComplexity.WeightedGraph.exp_condition_of_log,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_success_of_exp,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_success_of_log,
    CutQueryComplexity.Probability.BoundedDraw.sum_additive_upper_tail,
    CutQueryComplexity.WeightedGraph.exists_splitFamily,
    CutQueryComplexity.WeightedGraph.IsSplitFamily.strong_subset,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_light_cut,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_sound,
    CutQueryComplexity.WeightedGraph.IsStrong.le_strength_induce,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_induce_boundedCutLaw,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_induce_sparsifier,
    CutQueryComplexity.WeightedGraph.CountedBucket.sampleLaw_complete,
    CutQueryComplexity.WeightedGraph.sum_residualWeight,
    CutQueryComplexity.WeightedGraph.CountedBucket.residualBucket_reference,
    CutQueryComplexity.WeightedGraph.sampleResidual_blockLaw,
    CutQueryComplexity.WeightedGraph.CountedBucket.residualBucket_drawLaw,
    CutQueryComplexity.WeightedGraph.residualDraws_eval,
    CutQueryComplexity.WeightedGraph.CountedBucket.residualDraws_eval_eq_sampleLaw,
    CutQueryComplexity.WeightedGraph.drawCount_smooth,
    CutQueryComplexity.WeightedGraph.drawCount_le,
    CutQueryComplexity.WeightedGraph.residualDraws_sound,
    CutQueryComplexity.WeightedGraph.residualDraws_complete,
    CutQueryComplexity.WeightedGraph.IsStrong.subset_of_support,
    CutQueryComplexity.WeightedGraph.IsStrong.pullback_related,
    CutQueryComplexity.WeightedGraph.merged_strongRelated,
    CutQueryComplexity.WeightedGraph.card_le_one_of_mass_lt,
    CutQueryComplexity.WeightedGraph.same_block_of_mass_lt,
    CutQueryComplexity.WeightedGraph.residualDraws_merge_sound,
    CutQueryComplexity.WeightedGraph.residualDraws_merge_complete,
    CutQueryComplexity.WeightedGraph.cachedMass_eq,
    CutQueryComplexity.WeightedGraph.estimateCall_sound,
    CutQueryComplexity.WeightedGraph.estimateCall_complete,
    CutQueryComplexity.WeightedGraph.topLevel_lt,
    CutQueryComplexity.WeightedGraph.reachable_of_related,
    CutQueryComplexity.WeightedGraph.reachable_of_related_top,
    CutQueryComplexity.WeightedGraph.batch_step,
    CutQueryComplexity.WeightedGraph.next_scale_invariant,
    CutQueryComplexity.WeightedGraph.initial_invariant,
    CutQueryComplexity.WeightedGraph.label_bounds,
    CutQueryComplexity.WeightedGraph.top_contracted,
    CutQueryComplexity.RTree.iterate_failure_le,
    CutQueryComplexity.RTree.iterate_cost,
    CutQueryComplexity.WeightedGraph.merge_eq_iff,
    CutQueryComplexity.WeightedGraph.mergeMap_isLabeling,
    CutQueryComplexity.WeightedGraph.mergeCache_correct,
    CutQueryComplexity.WeightedGraph.card_liveLabels_merge,
    CutQueryComplexity.WeightedGraph.queryCuts_eval,
    CutQueryComplexity.WeightedGraph.estimateCall_support,
    CutQueryComplexity.WeightedGraph.internalMass_le,
    CutQueryComplexity.WeightedGraph.drawCount_le_cap,
    CutQueryComplexity.WeightedGraph.initState_good,
    CutQueryComplexity.WeightedGraph.boundary_good,
    CutQueryComplexity.WeightedGraph.afterCall_good,
    CutQueryComplexity.WeightedGraph.regionStep_failure,
    CutQueryComplexity.WeightedGraph.batchPot_boundary,
    CutQueryComplexity.WeightedGraph.batchPot_merge,
    CutQueryComplexity.WeightedGraph.estStep_failure,
    CutQueryComplexity.WeightedGraph.afterCall_events,
    CutQueryComplexity.WeightedGraph.estStep_events,
    CutQueryComplexity.WeightedGraph.estRun_correct,
    CutQueryComplexity.WeightedGraph.EstSuccess.same_block,
    CutQueryComplexity.WeightedGraph.estimateCall_cost,
    CutQueryComplexity.WeightedGraph.estStep_cost,
    CutQueryComplexity.WeightedGraph.estRun_cost,
    CutQueryComplexity.WeightedGraph.afterCall_charge,
    CutQueryComplexity.WeightedGraph.boundary_charge,
    CutQueryComplexity.WeightedGraph.estRun_correct',
    CutQueryComplexity.WeightedGraph.calls_length_le,
    CutQueryComplexity.WeightedGraph.draws_sum_le,
    CutQueryComplexity.WeightedGraph.runAcc_le,
    CutQueryComplexity.WeightedGraph.sampleResidual_origLaw,
    CutQueryComplexity.WeightedGraph.outBucket_drawLaw,
    CutQueryComplexity.WeightedGraph.outRun_eval,
    CutQueryComplexity.WeightedGraph.eventBuckets_reference,
    CutQueryComplexity.WeightedGraph.eventBuckets_admissible,
    CutQueryComplexity.WeightedGraph.outCount_le_cap,
    CutQueryComplexity.WeightedGraph.outRun_sparsifier,
    CutQueryComplexity.WeightedGraph.outRun_cost,
    CutQueryComplexity.WeightedGraph.outDraws_total_le,
    CutQueryComplexity.WeightedGraph.runPot_init_le,
    CutQueryComplexity.WeightedGraph.sparsifyCore_success,
    CutQueryComplexity.WeightedGraph.sparsifyCore_cost,
    CutQueryComplexity.WeightedGraph.coreGood_cost_le,
    CutQueryComplexity.WeightedGraph.sparsify_correct,
    CutQueryComplexity.WeightedGraph.sampleLaw_edgeCount_le,
    CutQueryComplexity.WeightedGraph.outRun_sparse,
    CutQueryComplexity.WeightedGraph.sparsify_sparse,
    CutQueryComplexity.WeightedGraph.fuelBound_le,
    CutQueryComplexity.WeightedGraph.sparsify_whp,
    CutQueryComplexity.Prog.toDTree_run,
    CutQueryComplexity.RootedTree.mem_iff_parity,
    CutQueryComplexity.RootedTree.crossSet_nonempty,
    CutQueryComplexity.RootedTree.two_respect_shape,
    CutQueryComplexity.Interest.pruning,
    CutQueryComplexity.Interest.sparsifier_interest,
    CutQueryComplexity.Interest.not_three_interested,
    CutQueryComplexity.Search.smawk_spec,
    CutQueryComplexity.Search.smawk_queryBound,
    CutQueryComplexity.Search.monge_min_queryBound,
    CutQueryComplexity.TwoRespecting.twoRespecting_queryBound,
    CutQueryComplexity.TwoRespecting.exists_tree_cover,
    CutQueryComplexity.TwoRespecting.weakSkeleton_minCut,
    CutQueryComplexity.TwoRespecting.minCut_of_weakSkeleton,
    CutQueryComplexity.TwoRespecting.twoRespectingProg_correct,
    CutQueryComplexity.TwoRespecting.twoRespectingProg_isSome,
    CutQueryComplexity.TwoRespecting.twoRespectingProg_cost,
    CutQueryComplexity.Discovery.quantileCheckpoints_spec,
    CutQueryComplexity.Discovery.heavyNeighbor_spec,
    CutQueryComplexity.Discovery.normalization_halves,
    CutQueryComplexity.Discovery.tree_compression,
    CutQueryComplexity.Discovery.residualRow_spec,
    CutQueryComplexity.Discovery.residualPrep_normalized,
    CutQueryComplexity.Discovery.centerSelection_normalized,
    CutQueryComplexity.Discovery.psi_lower,
    CutQueryComplexity.Discovery.psi_upper,
    CutQueryComplexity.Discovery.psi_eq_auxGraph,
    CutQueryComplexity.Certificate.exists_minCut_certificate,
    CutQueryComplexity.Certificate.exists_minCut_witnessCertificate,
    CutQueryComplexity.Certificate.certificateComplexity_le_bound,
    CutQueryComplexity.Certificate.certificateComplexity_near_linear,
    CutQueryComplexity.Certificate.certificateComplexity_le_one,
    CutQueryComplexity.Certificate.one_le_certificateComplexity,
    CutQueryComplexity.Certificate.certificateComplexity_eq_one,
    CutQueryComplexity.Certificate.certificateComplexity_le_cost,
    CutQueryComplexity.Certificate.certificateComplexity_le_minCutValueComplexity,
    CutQueryComplexity.Certificate.Windmill.exists_two_mul_sub_two_le_certificateComplexity,
    CutQueryComplexity.Certificate.Windmill.two_mul_card_sub_two_le_certificateComplexity,
    CutQueryComplexity.Certificate.Windmill.mincutValue_windmill,
    CutQueryComplexity.Certificate.Windmill.two_mul_sub_two_le_budget,
    CutQueryComplexity.Certificate.Windmill.two_mul_sub_two_le_minCutValueComplexity,
    CutQueryComplexity.Certificate.Windmill.two_mul_sub_three_le_shore_budget,
    CutQueryComplexity.Certificate.exists_certificate_card_eq,
    CutQueryComplexity.Search.Comp.cost_subst_le,
    CutQueryComplexity.Hierarchy.Hier.cut_le_rep,
    CutQueryComplexity.Hierarchy.Hier.cut_error_le,
    CutQueryComplexity.Hierarchy.Hier.completion_spec,
    CutQueryComplexity.Hierarchy.Hier.completion_cut_error_real,
    CutQueryComplexity.Hierarchy.Hier.supplied_cost,
    CutQueryComplexity.Hierarchy.Hier.supplied_weakSkeleton,
    CutQueryComplexity.Hierarchy.Hier.guard_lower,
    CutQueryComplexity.Hierarchy.Hier.guard_upper,
    CutQueryComplexity.Hierarchy.Hier.guardFor_of_leafChildless,
    CutQueryComplexity.Hierarchy.Hier.transfer_rep,
    CutQueryComplexity.Hierarchy.Hier.transfer_cut,
    CutQueryComplexity.Hierarchy.Hier.round_promise,
    CutQueryComplexity.Hierarchy.refine_spec,
    CutQueryComplexity.Hierarchy.refine_weakSkeleton,
    CutQueryComplexity.Hierarchy.Hier.exists_rounding,
    CutQueryComplexity.Hierarchy.Hier.rep_restrictInl_le,
    CutQueryComplexity.Hierarchy.Hier.restrictInl_promise,
    CutQueryComplexity.DetMinCut.learnContract_eval,
    CutQueryComplexity.DetMinCut.centerOf_eq,
    CutQueryComplexity.DetMinCut.auxOf_eq,
    CutQueryComplexity.DetMinCut.certify_branch,
    CutQueryComplexity.DetMinCut.phase_spec,
    CutQueryComplexity.DetMinCut.inv_merge,
    CutQueryComplexity.DetMinCut.normalize_spec,
    CutQueryComplexity.DetMinCut.halving,
    CutQueryComplexity.DetMinCut.mainLoop_spec,
    CutQueryComplexity.DetMinCut.detMinCut_spec,
    CutQueryComplexity.DetMinCut.deterministic_mincut_of_hierarchyBound,
    CutQueryComplexity.DetMinCut.phase_algebra,
    CutQueryComplexity.DetMinCut.phaseBound_le,
    CutQueryComplexity.DetMinCut.detBudget_le,
    CutQueryComplexity.DetMinCut.deterministic_mincut_upper_of_hierarchyBound,
    CutQueryComplexity.Hierarchy.refine_spec_of_good,
    CutQueryComplexity.Hierarchy.refine_weakSkeleton_of_good,
    CutQueryComplexity.Hierarchy.Hier.ConstantCutGuard.guardFor,
    CutQueryComplexity.DetMinCut.certify_branchG,
    CutQueryComplexity.DetMinCut.phase_specG,
    CutQueryComplexity.DetMinCut.exists_logL7_threshold,
    CutQueryComplexity.DetMinCut.kLog7_le_two_mul,
    CutQueryComplexity.DetMinCut.sqrt_div_le_kLog7,
    CutQueryComplexity.DetMinCut.phaseBoundR_const_le,
    CutQueryComplexity.DetMinCut.phaseBound_log7,
    CutQueryComplexity.DetMinCut.fallback_spec,
    CutQueryComplexity.DetMinCut.mainLoop7_spec,
    CutQueryComplexity.DetMinCut.detMinCut7_spec,
    CutQueryComplexity.DetMinCut.detBudget7_le,
    CutQueryComplexity.DetMinCut.deterministic_mincut_log7_of_hierarchyBound_of_constantGuard,
    CutQueryComplexity.DetMinCut.deterministic_mincut_log7_fin_of_hierarchyBound_of_constantGuard,
    CutQueryComplexity.Hierarchy.Hier.rep_le_of_local,
    CutQueryComplexity.Hierarchy.exists_bandwidth_partition,
    CutQueryComplexity.Hierarchy.uncross,
    CutQueryComplexity.Hierarchy.replace_le,
    CutQueryComplexity.Hierarchy.childWeight_le,
    CutQueryComplexity.Hierarchy.exists_balanced_partition,
    CutQueryComplexity.Hierarchy.clusters_laminar,
    CutQueryComplexity.Hierarchy.card_clusters_le,
    CutQueryComplexity.Hierarchy.isAnc_iff,
    CutQueryComplexity.Hierarchy.mem_children_iff,
    CutQueryComplexity.Hierarchy.rep_le_clusterHier,
    CutQueryComplexity.Hierarchy.Hier.rep_transfer_le,
    CutQueryComplexity.Hierarchy.depthN_le,
    CutQueryComplexity.Hierarchy.exists_hierarchyBound_sq,
    CutQueryComplexity.Hierarchy.exists_polylog_hierarchyBound,
    CutQueryComplexity.DetMinCut.deterministic_mincut_upper,
    CutQueryComplexity.DetMinCut.deterministic_mincut_log7_of_constantGuard,
    CutQueryComplexity.Hierarchy.Hier.cut_pushGraph,
    CutQueryComplexity.Hierarchy.Hier.rep_le_cut_mixGraph,
    CutQueryComplexity.Hierarchy.Hier.cut_le_of_load,
    CutQueryComplexity.Hierarchy.constantCutGuard_of_retractionBound,
    CutQueryComplexity.DetMinCut.deterministic_mincut_log7_of_retractionBound,
    CutQueryComplexity.DetMinCut.kLog5_le_two_mul,
    CutQueryComplexity.DetMinCut.sqrt_div_le_kLog5,
    CutQueryComplexity.DetMinCut.phaseBoundR_const_sq_le,
    CutQueryComplexity.DetMinCut.log5_algebra,
    CutQueryComplexity.DetMinCut.phaseBound_log5,
    CutQueryComplexity.DetMinCut.mainLoop5_spec,
    CutQueryComplexity.DetMinCut.detMinCut5_spec,
    CutQueryComplexity.DetMinCut.detBudget5_le,
    CutQueryComplexity.DetMinCut.deterministic_mincut_log5_of_hierarchyBound_of_constantGuard,
    CutQueryComplexity.DetMinCut.deterministic_mincut_log5_of_constantGuard,
    CutQueryComplexity.DetMinCut.deterministic_mincut_log5_of_retractionBound,
    CutQueryComplexity.Hierarchy.finite_minimax,
    CutQueryComplexity.Hierarchy.Hier.sum_mul_load_eq,
    CutQueryComplexity.Hierarchy.Hier.exists_fixing,
    CutQueryComplexity.Hierarchy.retractionBound_of_treeZeroExt,
    CutQueryComplexity.DetMinCut.deterministic_mincut_log5_of_treeZeroExt,
    CutQueryComplexity.Hierarchy.Retract.card_floor_ne_le,
    CutQueryComplexity.Hierarchy.Retract.logb_two_sub_le,
    CutQueryComplexity.Hierarchy.Retract.exists_le_of_forall_pos,
    CutQueryComplexity.Hierarchy.Hier.terminalDist_eq_nodeDist,
    CutQueryComplexity.Hierarchy.Hier.nodeDist_triangle,
    CutQueryComplexity.Hierarchy.Hier.nodeDist_of_isAnc,
    CutQueryComplexity.Hierarchy.Hier.nodeDist_parent,
    CutQueryComplexity.Hierarchy.Hier.dist_top_lt,
    CutQueryComplexity.Hierarchy.Hier.dist_round_le,
    CutQueryComplexity.Hierarchy.Hier.round_eq_round_parent,
    CutQueryComplexity.Hierarchy.Hier.sum_grid_edge_le,
    CutQueryComplexity.Hierarchy.Hier.exists_gridRound_le,
    CutQueryComplexity.Hierarchy.Hier.exists_fixing_cost_le_of_pos,
    CutQueryComplexity.Hierarchy.Hier.exists_fixing_cost_le,
    CutQueryComplexity.Hierarchy.treeZeroExt_42,
    CutQueryComplexity.Hierarchy.treeZeroExt_100,
    CutQueryComplexity.Hierarchy.constantCutGuard_42,
    CutQueryComplexity.Hierarchy.exists_constantCutGuard,
    CutQueryComplexity.DetMinCut.deterministic_mincut_log5,
    CutQueryComplexity.DetMinCut.logL,
    CutQueryComplexity.DiGraph.out_add_out,
    CutQueryComplexity.DiGraph.pairs_eq_out,
    CutQueryComplexity.DiGraph.two_mul_out,
    CutQueryComplexity.DiGraph.out_eq_sum_outdeg,
    CutQueryComplexity.pairQuery_eval,
    CutQueryComplexity.nbrCount_eval,
    CutQueryComplexity.searchFrom_correct,
    CutQueryComplexity.firstNbr_correct,
    CutQueryComplexity.firstNbr_correct_clog,
    CutQueryComplexity.firstNbrFilter_correct,
    CutQueryComplexity.rowAgg_correct,
    CutQueryComplexity.allRowsUniv_correct,
    CutQueryComplexity.pairAgg_correct,
    CutQueryComplexity.intFormula_val,
    CutQueryComplexity.Spectral.quad_lap,
    CutQueryComplexity.Spectral.loewner_iff,
    CutQueryComplexity.Spectral.lap_posSemidef,
    CutQueryComplexity.Spectral.lap_mulVec_eq_zero_iff,
    CutQueryComplexity.Spectral.psd_add_lower,
    CutQueryComplexity.Spectral.psd_add_upper,
    CutQueryComplexity.Spectral.sq_le_of_disjoint_paths,
    CutQueryComplexity.Spectral.pair_dominated,
    CutQueryComplexity.Spectral.pair_dominated_loewner,
    CutQueryComplexity.Spanner.Reach.exists_path,
    CutQueryComplexity.Spanner.inv_step,
    CutQueryComplexity.Spanner.trial_stretch,
    CutQueryComplexity.Spanner.trial_path,
    CutQueryComplexity.Spanner.spanners_disjoint,
    CutQueryComplexity.Spanner.bundle_dominated,
    CutQueryComplexity.DirectedMincut.netOut_le_out,
    CutQueryComplexity.DirectedMincut.exists_maxFlow_st,
    CutQueryComplexity.DirectedMincut.residual_cut,
    CutQueryComplexity.DirectedMincut.obj_ge,
    CutQueryComplexity.DirectedMincut.exists_feasible_obj_eq,
    CutQueryComplexity.DirectedMincut.near_opt,
    CutQueryComplexity.DirectedMincut.strict_start,
    CutQueryComplexity.DirectedMincut.extraction,
    CutQueryComplexity.DirectedMincut.bfs_correct,
    CutQueryComplexity.DirectedMincut.extract_correct,
    CutQueryComplexity.DirectedMincut.terminal_solves,
    CutQueryComplexity.DirectedMincut.le_out_of_card_le,
    CutQueryComplexity.DirectedMincut.le_out_of_card_compl_le,
    CutQueryComplexity.DirectedMincut.learn_correct,
    CutQueryComplexity.DirectedMincut.smallShore_correct,
    CutQueryComplexity.DirectedMincut.chain_opt,
    CutQueryComplexity.DirectedMincut.global_solves,
    CutQueryComplexity.DirectedMincut.extract_valid,
    CutQueryComplexity.DirectedMincut.termSpec_lpTerminal,
    RMT.matrix_bernstein_inequality_hdp_all,
    CutQueryComplexity.Spectral.abs_quad_le_norm,
    CutQueryComplexity.Spectral.norm_le_of_abs_quad_le,
    CutQueryComplexity.Spectral.sq_quad_le,
    CutQueryComplexity.Spectral.quad_sq_le,
    CutQueryComplexity.Spectral.maskPMF_toMeasure,
    CutQueryComplexity.Spectral.quarter_tail,
    CutQueryComplexity.Spectral.quarter_tail_pmf,
    CutQueryComplexity.Spectral.eigenvalues_nonneg,
    CutQueryComplexity.Spectral.matW_mul_mul_matW,
    CutQueryComplexity.Spectral.transfer,
    CutQueryComplexity.Spectral.sum_normPair_le,
    CutQueryComplexity.Spectral.norm_normPair_le,
    CutQueryComplexity.Spectral.kernel_pairs,
    CutQueryComplexity.Spectral.one_round,
    CutQueryComplexity.Spanner.mass_coins_eq,
    CutQueryComplexity.Spanner.expect_reportsOf_le,
    CutQueryComplexity.Spanner.expect_uniform_resample,
    CutQueryComplexity.Spanner.expect_clusters_le,
    CutQueryComplexity.Spanner.expect_trialReports_le,
    CutQueryComplexity.Spanner.mass_trialReports_gt,
    CutQueryComplexity.Spanner.vertexQ_correct,
    CutQueryComplexity.Spanner.phaseQ_correct,
    CutQueryComplexity.Spanner.trialQ_correct,
    CutQueryComplexity.Spanner.trialQ_cost,
    CutQueryComplexity.Spanner.card_trial_le,
    CutQueryComplexity.Spanner.capped_fail_le,
    CutQueryComplexity.Spanner.amp_fail_le,
    CutQueryComplexity.Spanner.amp_valid,
    CutQueryComplexity.Spanner.amp_spanner,
    CutQueryComplexity.Sparsify.bundleQ_fail_le,
    CutQueryComplexity.Sparsify.bundleQ_valid,
    CutQueryComplexity.Sparsify.ValidBundle.dominated,
    CutQueryComplexity.Sparsify.multQ_correct,
    CutQueryComplexity.Sparsify.next_energy,
    CutQueryComplexity.Sparsify.inv_next,
    CutQueryComplexity.Sparsify.levelQ_good,
    CutQueryComplexity.Sparsify.levelQ_expect,
    CutQueryComplexity.Sparsify.termQ_eval,
    CutQueryComplexity.Sparsify.runLevels_good,
    CutQueryComplexity.Sparsify.runLevels_expect,
    CutQueryComplexity.Sparsify.sparsify_fail_le,
    CutQueryComplexity.Sparsify.spectral_of_params,
    CutQueryComplexity.Sparsify.params_ok,
    CutQueryComplexity.Sparsify.spectral_primitive,
    CutQueryComplexity.Sparsify.bounds,
    CutQueryComplexity.Sparsify.budget_le,
    CutQueryComplexity.Sparsify.size_le,
    CutQueryComplexity.Sparsify.sinv_next,
    CutQueryComplexity.Sparsify.levelQ_support,
    CutQueryComplexity.Sparsify.runLevels_support,
    CutQueryComplexity.Sparsify.sparsify_support,
    CutQueryComplexity.Sparsify.spectral_primitive_support,
    CutQueryComplexity.Sparsify.stored_dyadic,
    CutQueryComplexity.Sparsify.sparsify_dyadic,
    CutQueryComplexity.ImplicitLP.diag_eq_sum_sq,
    CutQueryComplexity.ImplicitLP.sq_le_diag_mul,
    CutQueryComplexity.ImplicitLP.row_sq_le,
    CutQueryComplexity.ImplicitLP.hform_nonneg,
    CutQueryComplexity.ImplicitLP.hform_le_sform,
    CutQueryComplexity.ImplicitLP.proj_jacobian_bound,
    CutQueryComplexity.ImplicitLP.proj_jacobian_mixed,
    CutQueryComplexity.ImplicitLP.contDiffAt_inv_entry,
    CutQueryComplexity.ImplicitLP.hasDerivAt_inv_entry,
    CutQueryComplexity.ImplicitLP.proj_symm,
    CutQueryComplexity.ImplicitLP.proj_idem,
    CutQueryComplexity.ImplicitLP.hasDerivAt_lev,
    CutQueryComplexity.ImplicitLP.variational_le,
    CutQueryComplexity.ImplicitLP.invQuad_le_of_quad_le,
    CutQueryComplexity.ImplicitLP.lewisMap_contracting,
    CutQueryComplexity.ImplicitLP.isLewis_iff_fixed,
    CutQueryComplexity.ImplicitLP.lewis_exists_unique,
    CutQueryComplexity.ImplicitLP.lev_lewisLog,
    CutQueryComplexity.ImplicitLP.hasFDerivAt_lewisLog_scale,
    CutQueryComplexity.ImplicitLP.hasDerivAt_lewisLog,
    CutQueryComplexity.ImplicitLP.lewisLog_consistency,
    CutQueryComplexity.ImplicitLP.wnorm_add_le,
    CutQueryComplexity.ImplicitLP.mixed_le_of_le_exp,
    CutQueryComplexity.ImplicitLP.bootstrap,
    CutQueryComplexity.ImplicitLP.hasDerivAt_lewisLog_curve,
    CutQueryComplexity.ImplicitLP.hasDerivAt_sfun,
    CutQueryComplexity.ImplicitLP.barS_segment,
    CutQueryComplexity.ImplicitLP.mixed_ratio_le,
    CutQueryComplexity.ImplicitLP.closing,
    CutQueryComplexity.ImplicitLP.eq_gmove,
    CutQueryComplexity.ImplicitLP.note_consistency,
    CutQueryComplexity.ImplicitLP.eq_gmove_note,
    CutQueryComplexity.ImplicitLP.sq_dot_le_invQuad_mul,
    CutQueryComplexity.ImplicitLP.proj_mixed_bound,
    CutQueryComplexity.ImplicitLP.lev_le_one,
    CutQueryComplexity.ImplicitLP.sens_regLewis,
    CutQueryComplexity.ImplicitLP.sens_note,
    CutQueryComplexity.ImplicitLP.projection_contract,
    CutQueryComplexity.ImplicitLP.sens_window,
    CutQueryComplexity.ImplicitLP.gamma_bound,
    CutQueryComplexity.ImplicitLP.eq_projection_note,
    CutQueryComplexity.ImplicitLP.sum_lev,
    CutQueryComplexity.ImplicitLP.eq_gsize,
    CutQueryComplexity.ImplicitLP.eq_wmove,
    CutQueryComplexity.ImplicitLP.eq_tchange,
    CutQueryComplexity.ImplicitLP.mixed_dphi_le,
    CutQueryComplexity.ImplicitLP.abs_sin_mul_le_cos,
    CutQueryComplexity.ImplicitLP.barrier_bounds,
    CutQueryComplexity.ImplicitLP.slack_eq,
    CutQueryComplexity.ImplicitLP.eq_barrier,
    CutQueryComplexity.ImplicitLP.cent_attained,
    CutQueryComplexity.ImplicitLP.cos_mul_cos_lt,
    CutQueryComplexity.ImplicitLP.center_unique,
    CutQueryComplexity.ImplicitLP.center_exists,
    CutQueryComplexity.ImplicitLP.newton_coord,
    CutQueryComplexity.ImplicitLP.newton_bound,
    CutQueryComplexity.ImplicitLP.lem_newton,
    CutQueryComplexity.ImplicitLP.eq_newton,
    CutQueryComplexity.ImplicitLP.selector_spec,
    CutQueryComplexity.ImplicitLP.repair_feasible,
    CutQueryComplexity.ImplicitLP.repair_error,
    CutQueryComplexity.ImplicitLP.repair_mixed,
    CutQueryComplexity.ImplicitLP.lewisMap_eq_lev,
    CutQueryComplexity.ImplicitLP.inexact_iter,
    CutQueryComplexity.ImplicitLP.lewis_floor,
    CutQueryComplexity.ImplicitLP.restart_error,
    CutQueryComplexity.ImplicitLP.center_stationary,
    CutQueryComplexity.ImplicitLP.wall_bound,
    CutQueryComplexity.ImplicitLP.lem_slack,
    CutQueryComplexity.ImplicitLP.newtonDir_spec,
    CutQueryComplexity.ImplicitLP.newtonDir_unique,
    CutQueryComplexity.ImplicitLP.neg_log_cos_tangent,
    CutQueryComplexity.ImplicitLP.centerObj_ge_residual,
    CutQueryComplexity.ImplicitLP.segment_interior,
    CutQueryComplexity.ImplicitLP.center_step,
    CutQueryComplexity.ImplicitLP.slk_lip,
    CutQueryComplexity.ImplicitLP.lem_center,
    CutQueryComplexity.ImplicitLP.slack_floor,
    CutQueryComplexity.ImplicitLP.slack_floor_note,
    CutQueryComplexity.ImplicitLP.sinh_shift_upper,
    CutQueryComplexity.ImplicitLP.sinh_shift_lower,
    CutQueryComplexity.ImplicitLP.grad_upper,
    CutQueryComplexity.ImplicitLP.grad_lower,
    CutQueryComplexity.ImplicitLP.cosh_mvt,
    CutQueryComplexity.ImplicitLP.ChaseSet.supp_compare,
    CutQueryComplexity.ImplicitLP.lem_chase,
    CutQueryComplexity.ImplicitLP.chase_invariant,
    CutQueryComplexity.ImplicitLP.pot_coord_bound,
    CutQueryComplexity.ImplicitLP.mixedBall_chaseSet,
    CutQueryComplexity.ImplicitLP.batch_target_arith,
    CutQueryComplexity.ImplicitLP.batch_cap_arith,
    CutQueryComplexity.ImplicitLP.batch_primal,
    CutQueryComplexity.ImplicitLP.batch_weights,
    CutQueryComplexity.ImplicitLP.prop_batch,
    CutQueryComplexity.ImplicitLP.batch_tchange,
    CutQueryComplexity.ImplicitLP.support_normalize,
    CutQueryComplexity.ImplicitLP.split_iff,
    CutQueryComplexity.ImplicitLP.Gval_attained,
    CutQueryComplexity.ImplicitLP.Gval_lipschitz,
    CutQueryComplexity.ImplicitLP.Gval_concave,
    CutQueryComplexity.ImplicitLP.clip_quad_max,
    CutQueryComplexity.ImplicitLP.fobj_le_Dval,
    CutQueryComplexity.ImplicitLP.Gval_eq_zero_case,
    CutQueryComplexity.ImplicitLP.euc_zlam_sub,
    CutQueryComplexity.ImplicitLP.evaluator,
    CutQueryComplexity.ImplicitLP.rescale_feasible,
    CutQueryComplexity.ImplicitLP.concave_extrap,
    CutQueryComplexity.ImplicitLP.tstep_inv,
    CutQueryComplexity.ImplicitLP.trisect_bound,
    CutQueryComplexity.ImplicitLP.Gval_zero_le,
    CutQueryComplexity.ImplicitLP.round_down,
    CutQueryComplexity.ImplicitLP.support_main,
    CutQueryComplexity.ImplicitLP.solve_bound,
    CutQueryComplexity.ImplicitLP.direction_error,
    CutQueryComplexity.ImplicitLP.opnorm_le,
    CutQueryComplexity.ImplicitLP.opnorm_transpose_le,
    CutQueryComplexity.ImplicitLP.gram_ge_of_idRows,
    CutQueryComplexity.ImplicitLP.polar_cs,
    CutQueryComplexity.ImplicitLP.richardson_step,
    CutQueryComplexity.ImplicitLP.richardson_iter,
    CutQueryComplexity.ImplicitLP.precond_of_sparsifier,
    CutQueryComplexity.FractionalForest.RootedForest.rooted_cover,
    CutQueryComplexity.FractionalForest.RootedForest.rooted_cover_weighted,
    CutQueryComplexity.FractionalForest.root_concentration,
    CutQueryComplexity.FractionalForest.mass_supermodular,
    CutQueryComplexity.ImplicitLP.det_ne_zero_of_quad_pos,
    CutQueryComplexity.ImplicitLP.frozen_precond,
    CutQueryComplexity.ImplicitLP.frozen_solve,
    CutQueryComplexity.ImplicitLP.enorm_add_le,
    CutQueryComplexity.ImplicitLP.richardson_inexact,
    CutQueryComplexity.ImplicitLP.enorm_le_of_coord,
    CutQueryComplexity.ImplicitLP.frozen_solve_inexact,
    CutQueryComplexity.ImplicitLP.direction_error_core,
    CutQueryComplexity.ImplicitLP.gram_split,
    CutQueryComplexity.ImplicitLP.explicitGram_ge,
    CutQueryComplexity.ImplicitLP.lp_frozen_solve,
    CutQueryComplexity.ImplicitLP.lp_frozen_solve_inexact,
    CutQueryComplexity.ImplicitLP.direction_error_abs,
    CutQueryComplexity.ImplicitLP.lp_direction_error,
    CutQueryComplexity.ImplicitLP.lap_mulVec_apply,
    CutQueryComplexity.ImplicitLP.hiddenLap_apply,
    CutQueryComplexity.ImplicitLP.hiddenMatvec_correct,
    CutQueryComplexity.ImplicitLP.matvecFormula_val,
    CutQueryComplexity.ImplicitLP.roundGrid_enorm,
    CutQueryComplexity.ImplicitLP.frozenSolveProg_eval,
    CutQueryComplexity.ImplicitLP.bitOK_of_bound,
    CutQueryComplexity.ImplicitLP.lp_frozen_query_solve,
    CutQueryComplexity.ImplicitLP.frozenSolveProg_cost,
    CutQueryComplexity.ImplicitLP.certRow_err,
    CutQueryComplexity.ImplicitLP.certPair_err,
    CutQueryComplexity.ImplicitLP.floor_natAbs_lt,
    CutQueryComplexity.ImplicitLP.lpA_idRows,
    CutQueryComplexity.ImplicitLP.lp_hcount,
    CutQueryComplexity.ImplicitLP.lp_gram_split,
    CutQueryComplexity.ImplicitLP.lpA_transpose_lpVec,
    CutQueryComplexity.ImplicitLP.lp_rows_frozen_query_solve,
    CutQueryComplexity.ImplicitLP.invQuad_sandwich,
    CutQueryComplexity.ImplicitLP.abs_log_invQuad_sub_le,
    CutQueryComplexity.ImplicitLP.lewisMapApprox_err,
    CutQueryComplexity.ImplicitLP.lewis_inexact_lev,
    CutQueryComplexity.ImplicitLP.lewis_inexact_dyadic,
    CutQueryComplexity.ImplicitLP.lpLev_eq,
    CutQueryComplexity.ImplicitLP.lp_lewis_iter,
    CutQueryComplexity.ImplicitLP.lp_lewis_iter_note,
    CutQueryComplexity.ImplicitLP.divz_eq_row,
    CutQueryComplexity.ImplicitLP.hiddenDiv_exact,
    CutQueryComplexity.ImplicitLP.hiddenDiv_err,
    CutQueryComplexity.ImplicitLP.lp_transpose_eq_div,
    CutQueryComplexity.ImplicitLP.lev_ge_share,
    CutQueryComplexity.ImplicitLP.lev_ge_qstar,
    CutQueryComplexity.ImplicitLP.lewis_floor_qstar,
    CutQueryComplexity.ImplicitLP.hidden_sum_split,
    CutQueryComplexity.ImplicitLP.hiddenSumProg_err,
    CutQueryComplexity.ImplicitLP.ievaluator,
    CutQueryComplexity.ImplicitLP.support_of_eval,
    CutQueryComplexity.ImplicitLP.support_inexact,
    CutQueryComplexity.ImplicitLP.support_hidden,
    CutQueryComplexity.ImplicitLP.trisectProg_eval,
    CutQueryComplexity.ImplicitLP.supportProg_hidden,
    CutQueryComplexity.ImplicitLP.barrier_env,
    CutQueryComplexity.ImplicitLP.normalbounds,
    CutQueryComplexity.ImplicitLP.normalbounds_src,
    CutQueryComplexity.ImplicitLP.normalbounds_note,
    CutQueryComplexity.ImplicitLP.direction_error_note,
    CutQueryComplexity.ImplicitLP.direction_error_abs_note,
    CutQueryComplexity.ImplicitLP.lp_direction_error_note,
    CutQueryComplexity.ImplicitLP.lem_numeric_env,
    CutQueryComplexity.ImplicitLP.lem_numeric_note,
    CutQueryComplexity.ImplicitLP.lem_numeric_src,
    CutQueryComplexity.ImplicitLP.lem_numeric_abs_env,
    CutQueryComplexity.ImplicitLP.lem_numeric_query,
    CutQueryComplexity.ImplicitLP.lem_numeric_lp,
    CutQueryComplexity.ImplicitLP.weight_invariants,
    CutQueryComplexity.ImplicitLP.lem_numeric_query_inv,
    CutQueryComplexity.ImplicitLP.lem_numeric_lp_inv,
    CutQueryComplexity.ImplicitLP.explicitGram_lp,
    CutQueryComplexity.ImplicitLP.transposeProg_eval,
    CutQueryComplexity.ImplicitLP.newtonStepProg_cost,
    CutQueryComplexity.ImplicitLP.newtonStepProg_eval,
    CutQueryComplexity.ImplicitLP.query_xk_bound,
    CutQueryComplexity.ImplicitLP.newtonStep_numeric_lp,
    CutQueryComplexity.ImplicitLP.newtonStep_numeric_lp_inv,
    CutQueryComplexity.ImplicitLP.newtonProg_cost,
    CutQueryComplexity.ImplicitLP.newtonProg_fail_le,
    CutQueryComplexity.ImplicitLP.newtonProg_numeric_lp,
    CutQueryComplexity.ImplicitLP.lpRepPt_spec,
    CutQueryComplexity.ImplicitLP.lpHPt_spec,
    CutQueryComplexity.ImplicitLP.shrink_scalar,
    CutQueryComplexity.ImplicitLP.loss_scalar,
    CutQueryComplexity.ImplicitLP.truncDyadic_props,
    CutQueryComplexity.ImplicitLP.round_support,
    CutQueryComplexity.ImplicitLP.supportRoundProg_hidden,
    CutQueryComplexity.ImplicitLP.half_pow_iters_le,
    CutQueryComplexity.ImplicitLP.div_two_pow_bits_le,
    CutQueryComplexity.ImplicitLP.lt_two_pow_magBits,
    CutQueryComplexity.ImplicitLP.clog_le_log_add_one,
    CutQueryComplexity.ImplicitLP.sparsify_factor_bounds,
    CutQueryComplexity.ImplicitLP.freezeW_rel,
    CutQueryComplexity.ImplicitLP.freezeQ_abs,
    CutQueryComplexity.ImplicitLP.NewtonPub.Ppub_mul_β_le,
    CutQueryComplexity.ImplicitLP.NewtonPub.P_mono,
    CutQueryComplexity.ImplicitLP.solveDelta_spec,
    CutQueryComplexity.ImplicitLP.newtonStepPub_cost,
    CutQueryComplexity.ImplicitLP.newtonStep_public,
    CutQueryComplexity.ImplicitLP.newtonProgPub_cost,
    CutQueryComplexity.ImplicitLP.newtonPub_bits_log,
    CutQueryComplexity.ImplicitLP.newtonProgPub_numeric,
    CutQueryComplexity.ImplicitLP.supportRoundProg_hidden_gen,
    CutQueryComplexity.ImplicitLP.supportPub_hidden,
    CutQueryComplexity.ImplicitLP.supportPub_public,
    CutQueryComplexity.ImplicitLP.lewisLoop_cost,
    CutQueryComplexity.ImplicitLP.lewisLoop_fail_le,
    CutQueryComplexity.ImplicitLP.lewis_cap,
    CutQueryComplexity.ImplicitLP.lewis_cap_final,
    CutQueryComplexity.ImplicitLP.lewis_restart_lp,
    CutQueryComplexity.ImplicitLP.lpVec_invSlackPt,
    CutQueryComplexity.ImplicitLP.lewisStage,
    CutQueryComplexity.ImplicitLP.lpVec_gradPt,
    CutQueryComplexity.ImplicitLP.support_envelopes,
    CutQueryComplexity.ImplicitLP.supportPub_env,
    CutQueryComplexity.ImplicitLP.support_batch_form,
    CutQueryComplexity.ImplicitLP.potGrad_obs_bound,
    CutQueryComplexity.ImplicitLP.batch_support_inputs,
    CutQueryComplexity.ImplicitLP.batch_support_public,
    CutQueryComplexity.ImplicitLP.newtonPot_gram,
    CutQueryComplexity.ImplicitLP.lpVec_eq_lpD,
    CutQueryComplexity.ImplicitLP.batchProg_cost,
    CutQueryComplexity.ImplicitLP.batchProg_fail,
    CutQueryComplexity.ImplicitLP.batchGood_tchange,
    CutQueryComplexity.ImplicitLP.mixed_le_sum,
    CutQueryComplexity.ImplicitLP.mixed_le_public,
    CutQueryComplexity.DirectedCertificate.IsMinCutWitnessCertificate.isValueCertificate,
    CutQueryComplexity.DirectedCertificate.zero_witnessCertificate,
    CutQueryComplexity.DirectedCertificate.exists_zero_witnessCertificate,
    CutQueryComplexity.DirectedCertificate.budgetFreeCertificateTarget,
    CutQueryComplexity.DirectedCertificate.consistent_union,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.sym_cut,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.two_mul_out,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.symStar_eq,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.sym_w_eq_three_outs,
    CutQueryComplexity.DirectedCertificate.degrees_eq_of_consistent,
    CutQueryComplexity.DirectedCertificate.Measurement.compile_cost_le,
    CutQueryComplexity.DirectedCertificate.Measurement.compileAll_card_le,
    CutQueryComplexity.DirectedCertificate.directed_arc_not_determined,
    CutQueryComplexity.DirectedCertificate.edmonds_int,
    CutQueryComplexity.DirectedCertificate.exists_inArb_packing,
    CutQueryComplexity.DirectedCertificate.cut_of_inArb_packing,
    CutQueryComplexity.DirectedCertificate.inArb_packing_iff,
    CutQueryComplexity.DirectedCertificate.exists_outArb_packing,
    CutQueryComplexity.DirectedCertificate.outArb_packing_iff,
    CutQueryComplexity.DirectedCertificate.isLeast_total,
    CutQueryComplexity.DirectedCertificate.eq_load_of_total_eq,
    CutQueryComplexity.DirectedCertificate.laminar_card_le,
    CutQueryComplexity.DirectedCertificate.tight_rows_zero,
    CutQueryComplexity.DirectedCertificate.perturb_eq_zero,
    CutQueryComplexity.DirectedCertificate.exists_sparse_min_feasible,
    CutQueryComplexity.DirectedCertificate.exists_sparse_inArb_packing,
    CutQueryComplexity.DirectedCertificate.exists_sparse_outArb_packing,
    CutQueryComplexity.FractionalForest.budgetQ_le,
    CutQueryComplexity.FractionalForest.budgetQ_real,
    CutQueryComplexity.FractionalForest.budgetQ_eq_ceil,
    CutQueryComplexity.FractionalForest.Dpot_le_start,
    CutQueryComplexity.FractionalForest.violation_Dpot,
    CutQueryComplexity.FractionalForest.deletion_induction,
    CutQueryComplexity.FractionalForest.forest_deletion_of_three_le,
    CutQueryComplexity.FractionalForest.forest_deletion,
    CutQueryComplexity.FractionalForest.forest_deletion_uniform,
    CutQueryComplexity.DirectedCertificate.normForest_isFractionalForest,
    CutQueryComplexity.DirectedCertificate.mass_normForest_univ,
    CutQueryComplexity.DirectedCertificate.small_source_set,
    CutQueryComplexity.DirectedCertificate.small_source_set_flows,
    CutQueryComplexity.FractionalForest.Dpot_supermodular,
    CutQueryComplexity.FractionalForest.gain_mono,
    CutQueryComplexity.FractionalForest.densest_core,
    CutQueryComplexity.FractionalForest.exists_orientation,
    CutQueryComplexity.FractionalForest.uniform_roots,
    CutQueryComplexity.FractionalForest.loss_eq,
    CutQueryComplexity.FractionalForest.deletion_progress,
    CutQueryComplexity.FractionalForest.exists_gain_ge_div,
    CutQueryComplexity.FractionalForest.unit_progress,
    CutQueryComplexity.FractionalForest.forest_deletion_main,
    CutQueryComplexity.FractionalForest.forest_deletion_uniform_main,
    CutQueryComplexity.DirectedCertificate.small_source_set_main,
    CutQueryComplexity.DirectedCertificate.small_source_set_flows_main,
    CutQueryComplexity.DirectedCertificate.exists_flowTransfer_directed,
    CutQueryComplexity.DirectedCertificate.exists_flowCert_directed,
    CutQueryComplexity.DirectedCertificate.transferFlow_spec,
    CutQueryComplexity.DirectedCertificate.OrientationData.toGraph_ord,
    CutQueryComplexity.DirectedCertificate.OrientationData.toGraph_sym_w,
    CutQueryComplexity.DirectedCertificate.OrientationData.toGraph_c_zero,
    CutQueryComplexity.DirectedCertificate.OrientationCert.out_toGraph_self,
    CutQueryComplexity.DirectedCertificate.exists_orientationCert,
    CutQueryComplexity.DirectedCertificate.PruningData.lam_le_out_H,
    CutQueryComplexity.DirectedCertificate.PruningData.isGlobalMinCut_H,
    CutQueryComplexity.DirectedCertificate.PruningData.minValue_H,
    CutQueryComplexity.DirectedCertificate.PruningData.total_H_le,
    CutQueryComplexity.DirectedCertificate.PruningData.card_exc,
    CutQueryComplexity.DirectedCertificate.PruningData.ord_arc,
    CutQueryComplexity.DirectedCertificate.PruningData.card_queries,
    CutQueryComplexity.DirectedCertificate.PruningData.toGraph_le,
    CutQueryComplexity.DirectedCertificate.PruningData.out_toGraph_le,
    CutQueryComplexity.DirectedCertificate.PruningData.outStar_eq,
    CutQueryComplexity.DirectedCertificate.PruningData.symStar_eq,
    CutQueryComplexity.DirectedCertificate.PruningData.card_supp_le,
    CutQueryComplexity.DirectedCertificate.exists_pruningCert,
    CutQueryComplexity.DirectedCertificate.transferFlow_spec_premises,
    CutQueryComplexity.DirectedCertificate.FlowPremises.of_consistent,
    CutQueryComplexity.DirectedCertificate.exists_flowCert_premises,
    CutQueryComplexity.DirectedCertificate.exists_implicitFlowTransfer,
    CutQueryComplexity.DirectedCertificate.exists_implicitFlowCert,
    CutQueryComplexity.DirectedCertificate.PruningCert.exists_flowCert_H,
    CutQueryComplexity.DirectedCertificate.PruningCert.exists_flowTransfer_H,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.sum_netOut_le_out,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.exists_maxFlow_network,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.maxFlow_minCut,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.supply_iff,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.demand_iff,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.uniform_supply_iff,
    CutQueryComplexity.DirectedCertificate.WeightedDiGraph.uniform_demand_iff,
    CutQueryComplexity.Contraction.exists_connector,
    CutQueryComplexity.SpanTree.card_crossSet_le,
    CutQueryComplexity.TreePacking.exists_good_dist,
    CutQueryComplexity.TreePacking.exists_tree_family,
    CutQueryComplexity.TreePacking.markov_three,
    CutQueryComplexity.TreePacking.exists_tree_pmf,
    CutQueryComplexity.WeightedMinCut.iterate_fail_pow,
    CutQueryComplexity.WeightedMinCut.covers_tree,
    CutQueryComplexity.WeightedMinCut.stage2_correct,
    CutQueryComplexity.WeightedMinCut.weightedMinCut_correct,
    CutQueryComplexity.WeightedMinCut.weightedMinCut_whp]
