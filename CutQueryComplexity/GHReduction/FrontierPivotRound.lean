import CutQueryComplexity.GHReduction.SourcePivotCosts
import CutQueryComplexity.GHReduction.DependentRandomTable
import CutQueryComplexity.GHReduction.FrontierContraction
import CutQueryComplexity.GHReduction.RandomContractionCost

/-! # An executed pivot round on the actual complete frontier

Each active block calls the source-pivot program on its own component-proxy
contraction. Singletons make no queries. A dependent table executes all calls
on the same public frontier. The exact contraction simulator preserves their
realized costs, so the literal frontier count proves a round budget.

The public hard cap is then obtained by exact truncation, without a Markov
loss. The approximation hypothesis concerns one original public graph and
passes simultaneously to all actual contractions. Refining this output table
into the next frontier and final tree assembly are separate obligations.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators ENNReal
open WeightedGraph Probability

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

def frontierTerminals (p : V → B) (T : RootedTree B) (b : B) :
    Finset (FrontierVertex p T b) :=
  Finset.univ.image (fun u : fiber p b => Sum.inl u)

@[simp] theorem mem_frontierTerminals (p : V → B) (T : RootedTree B) (b : B)
    (z : FrontierVertex p T b) : z ∈ frontierTerminals p T b ↔ ∃ u, Sum.inl u = z := by
  constructor
  · intro hz
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hz
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

theorem frontierTerminals_card (p : V → B) (T : RootedTree B) (b : B) :
    (frontierTerminals p T b).card = (fiber p b).card := by
  change (Finset.univ.image
    (Sum.inl : fiber p b → (fiber p b) ⊕ (frontierProxies T b))).card = _
  rw [Finset.card_image_of_injective _ Sum.inl_injective]
  simp

theorem frontierTerminals_nonempty (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) : (frontierTerminals p T b).Nonempty := by
  obtain ⟨v, hv⟩ := frontier_fiber_nonempty p hp b
  refine ⟨Sum.inl ⟨v, hv⟩, ?_⟩
  exact (mem_frontierTerminals p T b _).mpr ⟨⟨v, hv⟩, rfl⟩

/-- Every graph parameter here is public: the partition, topology, explicit
approximator, and canonical solver code. -/
def frontierPivotCall {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent levels : ℕ)
    (K : WeightedGraph V) (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (b : B) (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (Option (SourcePivotOutput (FrontierVertex p T b) levels))
      (sourcePivotBudget M Q n samples trials guideLevels scale exponent levels) :=
  if 2 ≤ (fiber p b).card then
    (contractProgram (frontierMap p T b)
      (sourcePivotTree family n samples trials guideLevels scale exponent levels
        (K.contract (frontierMap p T b)) (frontierTerminals p T b)
        (frontierTerminals_nonempty p hp T b) ((frontierVertex_card_le p hp T b).trans hvn))).map some
  else RTree.pure (PMF.pure none)

def FrontierPivotGood (G : WeightedGraph V) (p : V → B) (T : RootedTree B) (b : B)
    {levels : ℕ} (out : Option (SourcePivotOutput (FrontierVertex p T b) levels)) : Prop :=
  if 2 ≤ (fiber p b).card then out.elim False
    (SourcePivotGood (G.contract (frontierMap p T b)) (frontierTerminals p T b))
  else out = none

theorem frontierPivotCall_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (b : B)
    (hvn : Fintype.card V ≤ n)
    {out : Option (SourcePivotOutput (FrontierVertex p T b) levels) × ℕ}
    (hout : out ∈ (RTree.run G.cut
      (frontierPivotCall family n samples trials guideLevels scale exponent levels K p hp T b hvn)).support) :
    n * out.2 ≤ Fintype.card (FrontierVertex p T b) *
      sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels := by
  by_cases hactive : 2 ≤ (fiber p b).card
  · simp only [frontierPivotCall, hactive, ite_true] at hout
    apply random_map_cost _ _ G.cut n _ ?_ hout
    intro call hcall
    rw [contractProgram_graph_run] at hcall
    exact sourcePivotTree_cost_scaled family hQ samples trials guideLevels scale exponent levels
      (G.contract (frontierMap p T b)) (K.contract (frontierMap p T b))
      (frontier_contraction_promise G hG p T b) _ _ _ hcall
  · simp only [frontierPivotCall, hactive, ite_false, RTree.run_pure, PMF.pure_map] at hout
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hout
    simp

theorem frontierPivotCall_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent levels : ℕ) (hlevels : thresholdLevels n ≤ guideLevels)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (b : B)
    (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    mass ((frontierPivotCall family n samples trials guideLevels scale exponent levels K p hp T b hvn).eval G.cut)
      (fun out => ¬FrontierPivotGood G p T b out) ≤
        singleSourceError M n samples trials scale exponent := by
  by_cases hactive : 2 ≤ (fiber p b).card
  · simp only [frontierPivotCall, hactive, ite_true, RTree.eval_map,
      contractProgram_eval, mass_map, FrontierPivotGood, hactive, ite_true, Option.elim_some]
    apply sourcePivotTree_failure_le family hQ hnscale samples trials guideLevels exponent levels
      hlevels _ _ (frontier_contraction_promise G hG p T b)
    intro S
    simpa only [cut_contract] using happrox (pull (frontierMap p T b) S)
  · simp [frontierPivotCall, FrontierPivotGood, hactive]

def frontierPivotRound {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent levels : ℕ)
    (K : WeightedGraph V) (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ ((b : B) → Option (SourcePivotOutput (FrontierVertex p T b) levels))
      (Fintype.card B * sourcePivotBudget M Q n samples trials guideLevels scale exponent levels) :=
  dependentRandomTable (fun _ => none)
    (fun b => frontierPivotCall family n samples trials guideLevels scale exponent levels K p hp T b hvn)

theorem frontierPivotRound_entry_support {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (samples trials guideLevels scale exponent levels : ℕ)
    (K : WeightedGraph V) (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (hvn : Fintype.card V ≤ n) (read : Finset V → ℝ)
    {out : (b : B) → Option (SourcePivotOutput (FrontierVertex p T b) levels)}
    (hout : out ∈ ((frontierPivotRound family n samples trials guideLevels scale exponent levels
      K p hp T hvn).eval read).support) (b : B) :
    out b ∈ ((frontierPivotCall family n samples trials guideLevels scale exponent levels
      K p hp T b hvn).eval read).support :=
  dependentRandomTable_entry_support _ _ read hout b

/-- The summands are precisely the graph types used by the calls above.
The proxy contribution is retained and the original global size is the only
size-regularity parameter. -/
theorem frontierPivotRound_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n)
    {out : ((b : B) → Option (SourcePivotOutput (FrontierVertex p T b) levels)) × ℕ}
    (hout : out ∈ (RTree.run G.cut
      (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn)).support) :
    n * out.2 ≤ Fintype.card V *
      (3 * sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels) := by
  have h := dependentRandomTable_cost (fun _ => none)
    (fun b => frontierPivotCall family n samples trials guideLevels scale exponent levels K p hp T b hvn)
    G.cut n (fun b => Fintype.card (FrontierVertex p T b) *
      sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels)
    (fun b call hcall => frontierPivotCall_cost_scaled family hQ samples trials guideLevels scale exponent levels
      G K hG p hp T b hvn hcall) hout
  rw [← Finset.sum_mul] at h
  have hsum := Nat.mul_le_mul_right
    (sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels)
    (frontier_vertex_sum_le p hp T)
  exact h.trans (by simpa only [Nat.mul_assoc, Nat.mul_comm 3] using hsum)

theorem frontierPivotRound_cost {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 0 < n)
    (samples trials guideLevels scale exponent levels : ℕ)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n)
    {out : ((b : B) → Option (SourcePivotOutput (FrontierVertex p T b) levels)) × ℕ}
    (hout : out ∈ (RTree.run G.cut
      (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn)).support) :
    out.2 ≤ 3 * sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels :=
  cost_le_of_scaled hn hvn (frontierPivotRound_cost_scaled family hQ samples trials guideLevels scale exponent
    levels G K hG p hp T hvn hout)

theorem frontierPivotRound_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent levels : ℕ) (hlevels : thresholdLevels n ≤ guideLevels)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    mass ((frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn).eval G.cut)
      (fun out => ¬∀ b, FrontierPivotGood G p T b (out b)) ≤
      (n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent := by
  have h := dependentRandomTable_failure_le (fun _ => none)
    (fun b => frontierPivotCall family n samples trials guideLevels scale exponent levels K p hp T b hvn)
    G.cut (fun b out => FrontierPivotGood G p T b out)
    (fun _ => singleSourceError M n samples trials scale exponent)
    (fun b => frontierPivotCall_failure_le family hQ hnscale samples trials guideLevels exponent levels
      hlevels G K hG p hp T b hvn happrox)
  apply h.trans
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply mul_le_mul' ?_ le_rfl
  exact_mod_cast (Fintype.card_le_of_surjective p hp).trans hvn

def frontierPivotRoundCapped {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n samples trials guideLevels scale exponent levels : ℕ)
    (K : WeightedGraph V) (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (hvn : Fintype.card V ≤ n) :
    RTree (Finset V) ℝ (Option ((b : B) → Option (SourcePivotOutput (FrontierVertex p T b) levels)))
      (3 * sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels) :=
  (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn).truncate
    (3 * sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels)

/-- Exact truncation adds no failure under a promised graph's cut oracle: the
realized-cost bound applies to every supported random execution, including
outputs with incorrect estimates. The capped tree's structural budget also
holds for arbitrary oracle answers, independently of this honest-oracle law. -/
theorem frontierPivotRoundCapped_failure_le {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q) (hn : 0 < n) (hnscale : n ≤ scale)
    (samples trials guideLevels exponent levels : ℕ) (hlevels : thresholdLevels n ≤ guideLevels)
    (G K : WeightedGraph V) (hG : InputPromise M G)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    mass ((frontierPivotRoundCapped family n samples trials guideLevels scale exponent levels K p hp T hvn).eval G.cut)
      (fun out => ¬out.elim False (fun table => ∀ b, FrontierPivotGood G p T b (table b))) ≤
      (n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent := by
  have hfailure := frontierPivotRound_failure_le family hQ hnscale samples trials guideLevels exponent levels
    hlevels G K hG p hp T hvn happrox
  rw [RTree.eval, mass_map] at hfailure
  rw [frontierPivotRoundCapped, RTree.eval_truncate, mass_map]
  apply le_trans (mass_mono_on_support _ ?_) hfailure
  intro out hout hbad
  have hcost := frontierPivotRound_cost family hQ hn samples trials guideLevels scale exponent levels
    G K hG p hp T hvn hout
  simpa only [hcost, ite_true, Option.elim_some] using hbad

end
end CutQueryComplexity.GHReduction
