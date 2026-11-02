import CutQueryComplexity.CanonicalST.SkeletonCounterexample
import CutQueryComplexity.TreeCutSparsifier.Endpoint
import CutQueryComplexity.TreeCutSparsifier.Unconditional
import CutQueryComplexity.TreeCutSparsifier.Conversion
import CutQueryComplexity.Hierarchy.RackeShah
import CutQueryComplexity.TreeCutSparsifier.RackeShah
import CutQueryComplexity.DetMinCut.UnconditionalLogLog
import CutQueryComplexity.UndirectedClosure.OutputsLogLog
import CutQueryComplexity.UndirectedClosure.HierarchyBudgetLogLog
import CutQueryComplexity.TreeCutSparsifier.ConversionLogLog
import CutQueryComplexity.TreeCutSparsifier.EndpointLL
import CutQueryComplexity.TreeCutSparsifier.UnconditionalLL
import CutQueryComplexity.TreeCutSparsifier.TwoStage
import CutQueryComplexity.AllMinCuts.Endpoint
import CutQueryComplexity.AllMinCuts.Count
import CutQueryComplexity.AllMinCuts.Randomized
import CutQueryComplexity.Certificate.Main
import CutQueryComplexity.Certificate.LowerBound
import CutQueryComplexity.Certificate.Windmill
import CutQueryComplexity.SupportForest.Endpoint
import CutQueryComplexityChecks.CoverageQuantum
import CutQueryComplexityChecks.CoverageClassical
import CutQueryComplexityChecks.CoverageQuantumReconstruction
import CutQueryComplexityChecks.CoverageProducers
import CutQueryComplexity
import CutQueryComplexityChecks.AxiomAudit

/-!
# Endpoint statements and transitive axiom audit

This file restates the public endpoints proved after the core library (all-pairs
and Gomory–Hu reductions, the deterministic APMC, directed certificates, the
implicit LP solver, star contraction and the coverage endpoints) and audits
their modules. It complements `CutQueryComplexityChecks.lean`, which audits the
remaining modules; the two module lists are disjoint. Run it with
`lake env lean --trust=0 CutQueryComplexityChecks/Endpoints.lean`.

Each listed module is audited in full. The certificate acceptance statements
construct their query families without a flow or packing premise. The calibrated
path-following programs construct their public numerical parameters and prove
finite terminal/global correctness and explicit asymptotic query bounds.
The general finite-box LP and full-state precision claims remain separate. No unfinished endpoint is represented by an assumed interface.
-/

set_option autoImplicit false

open CutQueryComplexity
open CutQueryComplexity.Certificate
open CutQueryComplexity.DirectedCertificate
open CutQueryComplexity.AllPairsAudit

example {V : Type*} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    (hG : Unweighted G) {s t x : V} {S : Finset V}
    (hS : MinimalST G s t S) (hx : x ∈ S) (hxs : x ≠ s)
    (hd : G.degree x = 2) : crossing G S x = 0 :=
  degree_two_crossing_zero hG hS hx hxs hd

example {V : Type*} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    (hG : Unweighted G) (hdeg : ∀ v, 2 ≤ G.degree v)
    {s t : V} {S : Finset V} (hS : MinimalST G s t S)
    (hbad : 5 * G.degree s < 6 * crossing G S s) :
    Friendly G (S.erase s) ∧ G.cut (S.erase s) ≤ 2 * G.degree s :=
  lemma34 hG hdeg hS hbad

example {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedDiGraph V) (r : V)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∃ Q : Finset (Finset V),
      Q.card ≤ 30 * Fintype.card V * (4 * (FractionalForest.ceilA (Fintype.card V) k - 1) + 3) ∧
      ∀ G' : WeightedDiGraph V, DirectedCertificate.Consistent G G' Q →
        ∀ S : Finset V, k ≤ S.card → k ≤ Sᶜ.card → G.minValue ≤ G'.out S :=
  DirectedCertificate.Completion.exists_largeShore_certificate G r hk hkn

example (n k : ℕ) (hk : 0 < k) :
    DirectedUnitST.SparseBand.BandGood (DirectedUnitST.SparseBand.selectOffsets n k) :=
  DirectedUnitST.SparseBand.selectOffsets_good n k hk

example {V : Type} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    (hG : Unweighted G) (hdeg : ∀ v, 2 ≤ G.degree v)
    (p : V → V) (hp : PreservesFriendly G p) (M : ℕ)
    (hM : (∑ b, G.cut (WeightedGraph.fiber p b)) ≤ 2 * (M : ℝ)) :
    ∃ out, (AllPairs.recoverAnswers p M).eval G.cut = some out ∧
      ∀ s t, s ≠ t → IsSTMinCut G s t (out s t).shore ∧
        (out s t).value = G.cut (out s t).shore :=
  AllPairs.recoverAnswers_correct hG hdeg p hp M hM

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hG : Unweighted G) (hn : 1 ≤ Fintype.card V) {s : ℝ} (hs : 0 ≤ s) :
    Probability.mass ((AllPairs.allPairsProgram s).eval G.cut)
      (fun answer => ¬∃ out, answer = some out ∧
        ∀ u v, u ≠ v → IsSTMinCut G u v (out u v).shore ∧
          (out u v).value = G.cut (out u v).shore) ≤
      ENNReal.ofReal ((6 * (Fintype.card V : ℝ) + 2) ^ (-s)) :=
  AllPairs.allPairsProgram_failure_explicit G hG hn hs

example {V : Type} [Fintype V] [DecidableEq V] (hn : 1 ≤ Fintype.card V)
    {s : ℝ} (hs : 0 ≤ s) (oracle : Finset V → ℝ)
    {out : Option (AllPairs.Answers V) × ℕ}
    (ho : out ∈ (RTree.run oracle (AllPairs.allPairsProgram s)).support) :
    (out.2 : ℝ) ≤ 600000 * (s + 8) * Fintype.card V *
      Real.sqrt (Fintype.card V : ℝ) * ((Nat.clog 2 (Fintype.card V) : ℝ) + 4) ^ 2 :=
  AllPairs.allPairsProgram_cost_bound hn hs oracle ho

example : ∃ C : ℝ, ∀ n : ℕ, ∀ G : WeightedDiGraph (Fin n), 2 ≤ n →
    ∃ Q : Finset (Finset (Fin n)), ∃ S : Finset (Fin n),
      (Q.card : ℝ) ≤ C * (n : ℝ) ^ ((5 : ℝ) / 3) ∧ S ∈ Q ∧
      ∀ G' : WeightedDiGraph (Fin n), (∀ T ∈ Q, G'.out T = G.out T) →
        ProperShore S ∧ ∀ T : Finset (Fin n), ProperShore T → G'.out S ≤ G'.out T :=
  DirectedCertificate.Completion.headline_certificate_target

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V,
      (Q.card : ℝ) ≤ 600 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) ∧ S ∈ Q ∧
      ∀ G' : WeightedDiGraph V, (∀ T ∈ Q, G'.out T = G.out T) →
        ProperShore S ∧ ∀ T : Finset V, ProperShore T → G'.out S ≤ G'.out T :=
  DirectedCertificate.Completion.exists_unit_global_certificate G hn hunit

#check @DirectedCertificate.Completion.uniform_certificate_target
#check @DirectedCertificate.Completion.headline_certificate_target
#check @DirectedCertificate.Completion.exists_unit_global_certificate

example {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedDiGraph V)
    {s t : V} (hst : s ≠ t) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V, ∃ lam : ℝ,
      Q.card ≤ 18 * Fintype.card V + 1 ∧ S ∈ Q ∧
      lam = DirectedCertificate.Completion.terminalValue G s t ∧ 0 ≤ lam ∧
      ∀ G' : WeightedDiGraph V, (∀ T ∈ Q, G'.out T = G.out T) →
        s ∈ S ∧ t ∉ S ∧ G'.out S = lam ∧
        DirectedCertificate.Completion.terminalValue G' s t = lam ∧
        ∀ T : Finset V, s ∈ T → t ∉ T → lam ≤ G'.out T :=
  DirectedCertificate.Completion.exists_exact_terminal_certificate G hst

#check @DirectedCertificate.Completion.exists_exact_terminal_certificate
#check @DirectedCertificate.Completion.exists_zero_terminal_certificate

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) {U t : ℝ}
    (hU : ∀ u v, G.sym.w u v ≤ U) (ht : 0 < t) (htU : t ≤ U) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V,
      (Q.card : ℝ) ≤ 1000 * ((PruningData.q G t : ℝ) +
        (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (U / t)) ∧ S ∈ Q ∧
      ∀ G' : WeightedDiGraph V, (∀ T ∈ Q, G'.out T = G.out T) →
        ProperShore S ∧ ∀ T : Finset V, ProperShore T → G'.out S ≤ G'.out T :=
  DirectedCertificate.Completion.exists_trimmed_witnessCertificate G hn hlam hU ht htU

#check @DirectedCertificate.Completion.exists_refined_large_certificate
#check @DirectedCertificate.Completion.exists_trimmed_witnessCertificate

open CutQueryComplexity.ImplicitLP.PathFollowing

/- The programs below are chosen from public n, terminals, accuracy and shore
threshold before the graph. The success statements expand the output contract;
the cost statements quantify over arbitrary answer oracles. -/
example {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (G : DiGraph (Fin n)) (hG : G.Simple) :
    1 - ζ ≤ (calibratedTerminalSolver n s t ζ).successProb G.out
      (fun out => s ∈ out.1 ∧ t ∉ out.1 ∧
        G.out out.1 = DirectedMincut.stMin G s t ∧ out.2 = G.out out.1) := by
  have hsuccess := calibratedTerminalSolver_success hn s t hst hζ hζ1 G hG
  unfold DirectedMincut.STGood at hsuccess
  exact hsuccess

example {n : ℕ} (hn : 2 ≤ n) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (h : ℕ) (hh : 0 < h) (hhn : h ≤ n)
    (G : DiGraph (Fin n)) (hG : G.Simple) :
    1 - ζ ≤ (calibratedGlobalMinCut n hn ζ h).successProb G.out
      (fun out => (out.1.Nonempty ∧ out.1 ≠ Finset.univ ∧ out.2 = G.out out.1) ∧
        G.out out.1 = DirectedMincut.globalMin G) := by
  have hsuccess := calibratedGlobalMinCut_success hn hζ hζ1 G hG h hh hhn
  unfold DirectedMincut.Opt DirectedMincut.Valid at hsuccess
  exact hsuccess

example (n : ℕ) (s t : Fin n) (ζ : ℝ) (oracle : Finset (Fin n) → ℕ)
    {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run oracle (calibratedTerminalSolver n s t ζ)).support) :
    let P := calibratedParams n s t ζ
    out.2 ≤ (2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
      (2 * n * (3 + 3 * Sparsify.pK n) + 1) :=
  calibratedTerminalSolver_cost_all_oracles n s t ζ oracle ho

example (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) (h : ℕ)
    (oracle : Finset (Fin n) → ℕ) {out : (Finset (Fin n) × ℕ) × ℕ}
    (ho : out ∈ (RTree.run oracle (calibratedGlobalMinCut n hn ζ h)).support) :
    let P := calibratedGlobalParams n hn (ζ / 2)
    out.2 ≤ 2 * n +
      (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) +
        (DirectedMincut.learnFuel (V := Fin n) h * (3 + 3 * Sparsify.pK n) + 1)) +
      2 * publicRootCount n h ζ * ((2 * n + P.solverBudget P.downSteps P.upSteps P.finalSteps) +
        (2 * n * (3 + 3 * Sparsify.pK n) + 1)) :=
  calibratedGlobalMinCut_cost_all_oracles n hn ζ h oracle ho

#check @calibratedTerminalSolver_success
#check @calibratedGlobalMinCut_success


/- The complete preparation program precedes every input graph. The hidden
integral realization is constructed only in the correctness proof. -/
example (n : ℕ) (hn : 2 ≤ n) :
    ∃ P : DTree (Finset (Fin n)) ℕ (DirectedUnitST.Preparation.Output n)
        (DirectedUnitST.Preparation.queryBudget n (DirectedUnitST.Preparation.cubicScale n)),
      (∀ read : Finset (Fin n) → ℕ, (P.cost read : ℝ) ≤
        256 * (n : ℝ) ^ (5 / 3 : ℝ) *
          ((DirectedUnitST.Acceleration.scheduleBits n : ℝ) + 1) ^ 2) ∧
      ∀ G : DiGraph (Fin n), G.Simple →
        ∃ H : DirectedCertificate.WeightedDiGraph (Fin n),
          DirectedUnitST.Preparation.PreparationSpec G H (P.eval G.out) := by
  refine ⟨DirectedUnitST.Preparation.fiveThirdsIntegralProg n, ?_, ?_⟩
  · exact fun read => DirectedUnitST.Preparation.fiveThirdsIntegralProg_cost hn read
  · exact fun G hG => DirectedUnitST.Preparation.fiveThirdsIntegralProg_correct G hG hn


/- Focused directed public-program acceptance (mirrored verbatim). -/
set_option exponentiation.threshold 512

example {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t) :
    ∃ T : DTree (Finset (Fin n)) ℕ (Option (Finset (Fin n) × ℕ))
        ⌈2048 * (n : ℝ) ^ (5 / 3 : ℝ) * ((Nat.clog 2 n + 4 : ℕ) : ℝ) ^ 2⌉₊,
      (∀ read : Finset (Fin n) → ℕ,
        T.cost read ≤ ⌈2048 * (n : ℝ) ^ (5 / 3 : ℝ) *
          ((Nat.clog 2 n + 4 : ℕ) : ℝ) ^ 2⌉₊ ∧
        (T.cost read : ℝ) ≤ 2049 * (n : ℝ) ^ (5 / 3 : ℝ) *
          ((Nat.clog 2 n + 4 : ℕ) : ℝ) ^ 2) ∧
      ∀ G : DiGraph (Fin n), G.Simple →
        ∃ S : Finset (Fin n), T.eval G.out = some (S, G.out S) ∧
          s ∈ S ∧ t ∉ S ∧
          ∀ W : Finset (Fin n), s ∈ W → t ∉ W → G.out S ≤ G.out W := by
  simpa only [DirectedUnitST.Endpoint.headlineQueries,
    DirectedUnitST.Endpoint.logScale] using
    DirectedUnitST.Endpoint.exists_unitST_query_program hn s t hst

example {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∃ (Q : ℕ) (P : RTree (Finset (Fin n)) ℕ (Finset (Fin n) × ℕ) Q),
      (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
        out ∈ (RTree.run read P).support →
        (out.2 : ℝ) ≤ 2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) *
          Real.logb 2 (2 * n / ζ) ^ 21) ∧
      (∀ G : DiGraph (Fin n), G.Simple →
        1 - ζ ≤ P.successProb G.out
          (fun out => s ∈ out.1 ∧ t ∉ out.1 ∧
            G.out out.1 = DirectedMincut.stMin G s t ∧ out.2 = G.out out.1)) := by
  refine ⟨_, calibratedTerminalSolver n s t ζ, ?_⟩
  have h := directed_terminal_query_theorem hn s t hst hζ hζ1
  unfold failureLog queryHeight DirectedMincut.STGood at h
  exact h

example {n : ℕ} (hn : 2 ≤ n) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∃ (Q : ℕ) (P : RTree (Finset (Fin n)) ℕ (Finset (Fin n) × ℕ) Q),
      (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
        out ∈ (RTree.run read P).support →
        (out.2 : ℝ) ≤ 2 ^ 340 * (n : ℝ) ^ (7 / 4 : ℝ) *
          Real.logb 2 (2 * n / ζ) ^ 22) ∧
      (∀ G : DiGraph (Fin n), G.Simple →
        1 - ζ ≤ P.successProb G.out
          (fun out => (out.1.Nonempty ∧ out.1 ≠ Finset.univ ∧ out.2 = G.out out.1) ∧
            G.out out.1 = DirectedMincut.globalMin G)) := by
  refine ⟨_, balancedGlobalMinCut n hn ζ, ?_⟩
  have h := directed_global_query_theorem hn hζ hζ1
  unfold failureLog queryHeight DirectedMincut.Opt DirectedMincut.Valid at h
  exact h

-- Eulerian directed weighted certificates, with the consistency and minimality
-- conditions unfolded.
example {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedCertificate.WeightedDiGraph V) (hn : 2 ≤ Fintype.card V)
    (hEuler : ∀ v, G.imbalance v = 0) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V,
      Q.card ≤ 2 * Fintype.card V +
        36 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧
      S ∈ Q ∧ (S.Nonempty ∧ S ≠ Finset.univ) ∧ G.out S = G.minValue ∧
      ∀ H : DirectedCertificate.WeightedDiGraph V,
        (∀ T ∈ Q, H.out T = G.out T) →
        (∀ v, H.imbalance v = 0) ∧
        ((S.Nonempty ∧ S ≠ Finset.univ) ∧
          ∀ T : Finset V, (T.Nonempty ∧ T ≠ Finset.univ) → H.out S ≤ H.out T) ∧
        H.out S = G.out S ∧ H.minValue = G.minValue := by
  simpa only [DirectedCertificate.Consistent, DirectedCertificate.IsGlobalMinCut,
    ProperShore] using
    DirectedCertificate.Completion.exists_exact_eulerian_certificate G hn hEuler


namespace PublicContracts1

open CutQueryComplexity CutQueryComplexity.DeterministicAPMCExpansion.Flow
open CutQueryComplexity.Certificate

-- The tree precedes the hidden graph in this literal public contract.
example {V : Type} [Fintype V] [DecidableEq V]
    (C R t : ℕ) (hC : 1 ≤ C) (hCR : C ≤ R) (ht : 1 ≤ t)
    (hqpos : 1 ≤ Fintype.card V) (hq : Fintype.card V ≤ t ^ 3) (a z : V → ℕ)
    (ha : (∑ v, a v) ≤ Fintype.card V * t) :
    ∃ tree : DTree (Finset V) ℝ (ExactResult V) (exactSharpBudget V R t),
      (∀ read, tree.cost read ≤ exactSharpBudget V R t) ∧
      ∀ G : WeightedGraph V, AllPairsAudit.Unweighted G →
        let result := tree.eval G.cut
        let H := directed (twoStar (scaledInternal G C) a z)
        result.finished = true ∧ H.STFlow source sink result.flow ∧
          source ∈ result.shore ∧ sink ∉ result.shore ∧
          (∀ u v, ∃ k : ℤ, result.flow u v = k) ∧
          (∀ S : Finset (NetworkVertex V), source ∈ S → sink ∉ S →
            H.out result.shore ≤ H.out S) ∧
          (∀ g, H.STFlow source sink g → netOut g source ≤ netOut result.flow source) := by
  refine ⟨scaledExactTree C R t a z, ?_, ?_⟩
  · intro read
    exact scaledExactTree_cost read C R t a z
  · intro G hG
    have hc := scaledExactTree_correct G hG C R t hC hCR ht hqpos hq a z ha
    exact ⟨hc.finished, hc.feasible, hc.source_mem, hc.sink_notMem,
      hc.flow_integer (twoStar_integral (scaledInternal_integral hG C) a z),
      hc.minimum_shore, hc.maximum_flow⟩

end PublicContracts1

-- Paper 02, Proposition 4: the arbitrary real parameter is not bounded above.
-- This literal restatement checks support containment and all six equalities.
example (M : ℝ) (hM : 1 ≤ M) :
    ∃ G B : WeightedGraph (Fin 4),
      AllPairsAudit.Unweighted G ∧ B.support ≤ G.support ∧
      mincutValue B = 1 ∧ mincutValue G = 1 ∧
      B.cut {0} = 1 ∧ G.cut {0} = 1 ∧
      CanonicalST.Augmentation.terminalValue G 1 3 = 2 ∧
      CanonicalST.Augmentation.terminalValue B 1 3 = M :=
  CanonicalST.exists_weakSkeleton_terminal_gap M hM

#audit_cut_axioms [
  CutQueryComplexity.DetMinCut.SafePartition,
  CutQueryComplexity.TreeCutSparsifier.Basic,
  CutQueryComplexity.TreeCutSparsifier.Normalization,
  CutQueryComplexity.TreeCutSparsifier.Certification,
  CutQueryComplexity.TreeCutSparsifier.Phase,
  CutQueryComplexity.TreeCutSparsifier.Parameters,
  CutQueryComplexity.TreeCutSparsifier.Budget,
  CutQueryComplexity.TreeCutSparsifier.Main,
  CutQueryComplexity.TreeCutSparsifier.Endpoint,
  CutQueryComplexity.TreeCutSparsifier.Unconditional,
  CutQueryComplexity.Hierarchy.TerminalCuts,
  CutQueryComplexity.Hierarchy.Laminar,
  CutQueryComplexity.Hierarchy.Canonicalize,
  CutQueryComplexity.TreeCutSparsifier.Canonicalization,
  CutQueryComplexity.TreeCutSparsifier.Conversion,
  CutQueryComplexity.Hierarchy.RackeShah.Basic,
  CutQueryComplexity.Hierarchy.RackeShah.WeightedMajority,
  CutQueryComplexity.Hierarchy.RackeShah.Transport,
  CutQueryComplexity.Hierarchy.RackeShah.Partition,
  CutQueryComplexity.Hierarchy.RackeShah.LogBounds,
  CutQueryComplexity.Hierarchy.RackeShah.Refinement,
  CutQueryComplexity.Hierarchy.RackeShah.Decomposition,
  CutQueryComplexity.Hierarchy.RackeShah.Construction,
  CutQueryComplexity.Hierarchy.RackeShah.Existence,
  CutQueryComplexity.TreeCutSparsifier.RackeShah,
  CutQueryComplexity.DetMinCut.ParametersLogLog,
  CutQueryComplexity.DetMinCut.BudgetLogLog,
  CutQueryComplexity.DetMinCut.MainLogLog,
  CutQueryComplexity.DetMinCut.UnconditionalLogLog,
  CutQueryComplexity.UndirectedClosure.OutputsLogLog,
  CutQueryComplexity.UndirectedClosure.HierarchyBudgetLogLog,
  CutQueryComplexity.TreeCutSparsifier.ConversionLogLog,
  CutQueryComplexity.TreeCutSparsifier.PhaseLL,
  CutQueryComplexity.TreeCutSparsifier.ParametersLL,
  CutQueryComplexity.TreeCutSparsifier.BudgetLL,
  CutQueryComplexity.TreeCutSparsifier.MainLL,
  CutQueryComplexity.TreeCutSparsifier.EndpointLL,
  CutQueryComplexity.TreeCutSparsifier.UnconditionalLL,
  CutQueryComplexity.TreeCutSparsifier.TwoStage,
  CutQueryComplexity.SupportForest.Support,
  CutQueryComplexity.SupportForest.FindPos,
  CutQueryComplexity.SupportForest.Rectangle,
  CutQueryComplexity.SupportForest.Round,
  CutQueryComplexity.SupportForest.Main,
  CutQueryComplexity.SupportForest.Endpoint,
  CutQueryComplexity.Search.MongeAllMinima,
  CutQueryComplexity.TwoRespecting.WeakMajority,
  CutQueryComplexity.TwoRespecting.AllMinimaRect,
  CutQueryComplexity.TwoRespecting.AllMinima,
  CutQueryComplexity.AllMinCuts.Basic,
  CutQueryComplexity.AllMinCuts.Skeleton,
  CutQueryComplexity.AllMinCuts.Conversion,
  CutQueryComplexity.AllMinCuts.Cover,
  CutQueryComplexity.AllMinCuts.Support,
  CutQueryComplexity.AllMinCuts.TwoStage,
  CutQueryComplexity.AllMinCuts.Endpoint,
  CutQueryComplexity.AllMinCuts.Count,
  CutQueryComplexity.AllMinCuts.Randomized,
  CutQueryComplexityChecks.CoverageProducers,
  CutQueryComplexityChecks.CoverageQuantumReconstruction,
  CutQueryComplexityChecks.CoverageClassical,
  CutQueryComplexityChecks.CoverageQuantum,
  CutQueryComplexity.Certificate.UnitAllPairs,
  CutQueryComplexity.Reconstruction.DirectedData,
  CutQueryComplexity.Reconstruction.CompressedDirected.Program,
  CutQueryComplexity.Reconstruction.CompressedDirected.Endpoint,
  CutQueryComplexity.Reconstruction.WeightedDirected.Program,
  CutQueryComplexity.Reconstruction.WeightedDirected.Endpoint,
  CutQueryComplexity.Reconstruction.WeightedUndirected,
  CutQueryComplexity.MinCut.WeightedEndpoint,
  CutQueryComplexity.Quantum.LinearReconstruction.Row,
  CutQueryComplexity.Quantum.LinearReconstruction.Graph,
  CutQueryComplexity.Quantum.LinearReconstruction.Endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.Oracle,
  CutQueryComplexity.Quantum.DirectedReconstruction.Program,
  CutQueryComplexity.Quantum.DirectedReconstruction.Endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.Capacity,
  CutQueryComplexity.AllPairsAudit.CutAlgebra,
  CutQueryComplexity.AllPairsAudit.MinimalShore,
  CutQueryComplexity.AllPairsAudit.Star,
  CutQueryComplexity.AllPairsAudit.Endpoint,
  CutQueryComplexity.DirectedUnitST.SparseBand.Basic,
  CutQueryComplexity.DirectedUnitST.SparseBand.Grid,
  CutQueryComplexity.DirectedUnitST.Repair.Basic,
  CutQueryComplexity.DirectedUnitST.Repair.HeavyTerminal,
  CutQueryComplexity.DirectedUnitST.Acceleration.Huber,
  CutQueryComplexity.ImplicitLP.PathFollowing.Invariant,
  CutQueryComplexity.ImplicitLP.PathFollowing.Run,
  CutQueryComplexity.DirectedCertificate.Completion.SourceRoute,
  CutQueryComplexity.DirectedCertificate.Completion.ConnectedTree,
  CutQueryComplexity.DirectedCertificate.Completion.MassCap,
  CutQueryComplexity.AllPairs.Recovery,
  CutQueryComplexity.AllPairs.Padding,
  CutQueryComplexity.AllPairs.Partition,
  CutQueryComplexity.AllPairs.Shaving,
  CutQueryComplexity.AllPairs.Representation,
  CutQueryComplexity.DirectedUnitST.SparseBand.Counting,
  CutQueryComplexity.DirectedUnitST.SparseBand.Certificate,
  CutQueryComplexity.DirectedUnitST.Acceleration.Lyapunov,
  CutQueryComplexity.DirectedUnitST.Acceleration.Quantization,
  CutQueryComplexity.DirectedUnitST.Repair.Height,
  CutQueryComplexity.DirectedUnitST.Repair.Dinic,
  CutQueryComplexity.DirectedUnitST.Repair.Decomposition,
  CutQueryComplexity.ImplicitLP.PathFollowing.Initialization,
  CutQueryComplexity.ImplicitLP.PathFollowing.Budget,
  CutQueryComplexity.DirectedCertificate.Completion.SmallShore,
  CutQueryComplexity.DirectedUnitST.Acceleration.Oracle,
  CutQueryComplexity.DirectedUnitST.Blocking.State,
  CutQueryComplexity.DirectedCertificate.Completion.Centroid,
  CutQueryComplexity.DirectedUnitST.Repair.ResidualSearch,
  CutQueryComplexity.AllPairs.Main,
  CutQueryComplexity.DirectedCertificate.Completion.Budget,
  CutQueryComplexity.AllPairs.Budget,
  CutQueryComplexity.ImplicitLP.PathFollowing.Main,
  CutQueryComplexity.DirectedUnitST.Blocking.BFS,
  CutQueryComplexity.DirectedUnitST.Preparation.Basic,
  CutQueryComplexity.DirectedUnitST.Repair.IntegralRounding,
  CutQueryComplexity.DirectedCertificate.Completion.Main,
  CutQueryComplexity.CanonicalST.Extension,
  CutQueryComplexity.DirectedCertificate.Completion.Terminal,
  CutQueryComplexity.DirectedUnitST.Preparation.Query,
  CutQueryComplexity.DirectedUnitST.Repair.Cost,
  CutQueryComplexity.CanonicalST.Basic,
  CutQueryComplexity.ImplicitLP.PathFollowing.Calibration,
  CutQueryComplexity.DirectedUnitST.Blocking.DFS,
  CutQueryComplexity.DirectedCertificate.Completion.Spread,
  CutQueryComplexity.DirectedUnitST.Preparation.Rounding,
  CutQueryComplexity.DirectedUnitST.Endpoint.Budget,
  CutQueryComplexity.CanonicalST.Rows,
  CutQueryComplexity.DirectedCertificate.Completion.Corollaries,
  CutQueryComplexity.DirectedUnitST.Blocking.Phase,
  CutQueryComplexity.DirectedUnitST.Preparation.Budget,
  CutQueryComplexity.DirectedUnitST.Endpoint.Program,
  CutQueryComplexity.CanonicalST.Core,
  CutQueryComplexity.ImplicitLP.PathFollowing.QueryBound,
  CutQueryComplexity.CanonicalST.Counting.Local,
  CutQueryComplexity.DirectedUnitST.Blocking.Run,
  CutQueryComplexity.DirectedUnitST.Preparation.Height,
  CutQueryComplexity.CanonicalST.Counting.Partition,
  CutQueryComplexity.DirectedUnitST.Preparation.Main,
  CutQueryComplexity.DirectedUnitST.Blocking.Cost,
  CutQueryComplexity.CanonicalST.LongEdge.Assignments,
  CutQueryComplexity.DirectedUnitST.Blocking.Main,
  CutQueryComplexity.UndirectedClosure.ConicSupport,
  CutQueryComplexity.ImplicitLP.PathFollowing.PrimitiveBudget,
  CutQueryComplexity.CanonicalST.LongEdge.Bins,
  CutQueryComplexity.CanonicalST.Counting.Global,
  CutQueryComplexity.DirectedUnitST.Endpoint.Main,
  CutQueryComplexity.ImplicitLP.PathFollowing.QueryEndpoint,
  CutQueryComplexity.UndirectedClosure.CertificateSkeleton,
  CutQueryComplexity.UndirectedClosure.Outputs,
  CutQueryComplexity.CanonicalST.Phase.State,
  CutQueryComplexity.CanonicalST.LongEdge.Search,
  CutQueryComplexity.CanonicalST.Counting.Main,
  CutQueryComplexity.CanonicalST.Augmentation.Support,
  CutQueryComplexity.CanonicalST.Phase.Budget,
  CutQueryComplexity.UndirectedClosure.HierarchyBudget,
  CutQueryComplexity.CanonicalST.Witness.Basic,
  CutQueryComplexity.CanonicalST.Augmentation.Cycles,
  CutQueryComplexity.CanonicalST.Witness.Count,
  CutQueryComplexity.ImplicitLP.GenericQuery.Basic,
  CutQueryComplexity.DirectedCertificate.Completion.Eulerian,
  CutQueryComplexity.CanonicalST.Augmentation.MaxFlow,
  CutQueryComplexity.ImplicitLP.GenericQuery.Rows,
  CutQueryComplexity.CanonicalST.Witness.Loss,
  CutQueryComplexity.Certificate.GomoryHu.Basic,
  CutQueryComplexity.Certificate.TreePattern.Costs,
  CutQueryComplexity.Certificate.GomoryHu.TerminalLower,
  CutQueryComplexity.GHReduction.Contractions,
  CutQueryComplexity.CanonicalST.Augmentation.Progress,
  CutQueryComplexity.CanonicalST.Reachability,
  CutQueryComplexity.ImplicitLP.GenericQuery.Query,
  CutQueryComplexity.ImplicitLP.GenericQuery.Scalars,
  CutQueryComplexity.Certificate.TreePattern.Tree,
  CutQueryComplexity.Certificate.GomoryHu.Contraction,
  CutQueryComplexity.Certificate.TreePattern.Enumeration.Basic,
  CutQueryComplexity.CanonicalST.Phase.Run,
  CutQueryComplexity.ImplicitLP.GenericQuery.Support,
  CutQueryComplexity.ImplicitLP.GenericQuery.Numeric,
  CutQueryComplexity.Certificate.TreePattern.Verify,
  CutQueryComplexity.CanonicalST.Decision,
  CutQueryComplexity.Certificate.GomoryHu.Decomposition,
  CutQueryComplexity.CanonicalST.Main,
  CutQueryComplexity.CanonicalST.Budget,
  CutQueryComplexity.CanonicalST.SkeletonCounterexample,
  CutQueryComplexity.ImplicitLP.GenericQuery.Box,
  CutQueryComplexity.Certificate.TreePattern.NormalForm,
  CutQueryComplexity.Certificate.TreePattern.Enumeration.Decoder,
  CutQueryComplexity.GHReduction.TerminalGuides,
  CutQueryComplexity.ImplicitLP.GenericQuery.PointOps,
  CutQueryComplexity.ImplicitLP.GenericQuery.BatchSupport,
  CutQueryComplexity.Certificate.TreePattern.Main,
  CutQueryComplexity.Certificate.GomoryHu.Degree,
  CutQueryComplexity.Certificate.TreePattern.Enumeration.Bijection,
  CutQueryComplexity.StarContraction2022.Common.Basic,
  CutQueryComplexity.StarContraction2022.Recovery.Separating,
  CutQueryComplexity.ImplicitLP.GenericQuery.Lewis,
  CutQueryComplexity.Certificate.TreePattern.Enumeration.Public,
  CutQueryComplexity.StarContraction2022.Common.Quotient,
  CutQueryComplexity.ImplicitLP.GenericQuery.Stage,
  CutQueryComplexity.Certificate.GomoryHu.Levels,
  CutQueryComplexity.Certificate.TreePattern.Bounds,
  CutQueryComplexity.StarContraction2022.Common.Threshold,
  CutQueryComplexity.ImplicitLP.GenericQuery.Newton,
  CutQueryComplexity.StarContraction2022.Probability.Product,
  CutQueryComplexity.StarContraction2022.Certificates.Semantics,
  CutQueryComplexity.ImplicitLP.GenericQuery.Batch,
  CutQueryComplexity.StarContraction2022.Recovery.Decode,
  CutQueryComplexity.StarContraction2022.Common.Constants,
  CutQueryComplexity.ImplicitLP.GenericQuery.Invariant,
  CutQueryComplexity.ImplicitLP.GenericQuery.Run,
  CutQueryComplexity.StarContraction2022.Probability.ConditionalRatio,
  CutQueryComplexity.GHReduction.GuideSampling,
  CutQueryComplexity.StarContraction2022.Adapters.Weighted,
  CutQueryComplexity.GHReduction.CanonicalCuts,
  CutQueryComplexity.StarContraction2022.Certificates.SmallQuotient,
  CutQueryComplexity.ImplicitLP.GenericQuery.Initialization,
  CutQueryComplexity.GHReduction.Specification,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState,
  CutQueryComplexity.GHReduction.OuterPivot.Balance,
  CutQueryComplexity.ImplicitLP.GenericQuery.Budget,
  CutQueryComplexity.GHReduction.Programs,
  CutQueryComplexity.GHReduction.IsolatingCells,
  CutQueryComplexity.ImplicitLP.GenericQuery.Solver,
  CutQueryComplexity.StarContraction2022.Recovery.LearnBucket,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters,
  CutQueryComplexity.GHReduction.ThresholdSampling,
  CutQueryComplexity.ImplicitLP.GenericQuery.Calibration,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.Exposure,
  CutQueryComplexity.StarContraction2022.Certificates.Parallel.Queries,
  CutQueryComplexity.GHReduction.TerminalContraction,
  CutQueryComplexity.StarContraction2022.Recovery.RecoverAll,
  CutQueryComplexity.ImplicitLP.GenericQuery.Bounds,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelProgress,
  CutQueryComplexity.StarContraction2022.Recovery.Capped,
  CutQueryComplexity.ImplicitLP.GenericQuery.PrimitiveBounds,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.Goodness,
  CutQueryComplexity.GHReduction.ShoreContraction,
  CutQueryComplexity.GHReduction.GuideBudget,
  CutQueryComplexity.DeterministicAPMCExpansion.Basic,
  CutQueryComplexity.GHReduction.GroupSeparator,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.Patterns,
  CutQueryComplexity.ImplicitLP.GenericQuery.ScheduleBounds,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.SubtypeQueries,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.RecoveryMoments,
  CutQueryComplexity.StarContraction2022.Certificates.Parallel.Color,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.CutAlgebra,
  CutQueryComplexity.GHReduction.Isolating,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Basic,
  CutQueryComplexity.GHReduction.SourceValues,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges,
  CutQueryComplexity.StarContraction2022.Certificates.Parallel.Scan,
  CutQueryComplexity.ImplicitLP.GenericQuery.SpectralBounds,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.Network,
  CutQueryComplexity.StarContraction2022.Quantum.MinimumDegree,
  CutQueryComplexity.ImplicitLP.GenericQuery.Endpoint,
  CutQueryComplexity.StarContraction2022.Certificates.Parallel.Fuel,
  CutQueryComplexity.GHReduction.GuideStructure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.StarCut,
  CutQueryComplexity.StarContraction2022.Certificates.Parallel.Mixed,
  CutQueryComplexity.GHReduction.CutTree,
  CutQueryComplexity.GHReduction.GuidePruning,
  CutQueryComplexity.StarContraction2022.Quantum.FinitePolicy,
  CutQueryComplexity.GHReduction.PartialTree,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.Components,
  CutQueryComplexity.StarContraction2022.Certificates.Parallel.Halving,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.ResidualSearch,
  CutQueryComplexity.GHReduction.Candidates,
  CutQueryComplexity.StarContraction2022.Quantum.RandomizedCompiler,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.QueryProg,
  CutQueryComplexity.GHReduction.CandidateLifting,
  CutQueryComplexity.GHReduction.BlockRefinement,
  CutQueryComplexity.StarContraction2022.Certificates.Parallel.Charge,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.Outside,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.BFS,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.Recovery,
  CutQueryComplexity.StarContraction2022.Certificates.Parallel,
  CutQueryComplexity.GHReduction.GuideBase,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.Centers,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.DFS,
  CutQueryComplexity.GHReduction.GroupContraction,
  CutQueryComplexity.GHReduction.BlockRefinementTree,
  CutQueryComplexity.StarContraction2022.Quantum.FiniteCutEncoding,
  CutQueryComplexity.StarContraction2022.Quantum.FiniteCutCompiler,
  CutQueryComplexity.GHReduction.GuideSplit,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.CutCertificate,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.Avoidance,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.Tail,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Basic,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.Attachments,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.Decode,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Sampling,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.UnitPhase,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Counts,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Quality,
  CutQueryComplexity.GHReduction.GuideOne,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.Recovery,
  CutQueryComplexity.GHReduction.CutUncrossing,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.Scaled,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.Budget,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.Exact,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactHistory,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.ScaledGeometry,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.ScaledTail,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.SharpBudget,
  CutQueryComplexity.GHReduction.GuideOneBudget,
  CutQueryComplexity.GHReduction.GuideOneComplete,
  CutQueryComplexity.GHReduction.GuideOneEndpoint,
  CutQueryComplexity.GHReduction.GuideOneGeometry,
  CutQueryComplexity.GHReduction.GuideRecurrence,
  CutQueryComplexity.StarContraction2022.Contraction.Uniform,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.Isolation,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Neighbors,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.NeighborsPhysical,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Budget,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Quotient,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Survival,
  CutQueryComplexity.StarContraction2022.Randomized.HighDegree,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.RouteCuts,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.RouteEndpoints,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.Routes,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Solver,
  CutQueryComplexity.GHReduction.FrontierContraction,
  CutQueryComplexity.GHReduction.GuideOneGlobal,
  CutQueryComplexity.GHReduction.GuidePruneSampling,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Program,
  CutQueryComplexity.StarContraction2022.Randomized.Main,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.Budget,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.Recover,
  CutQueryComplexity.StarContraction2022.Randomized.Budget,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.CloneAssignment,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Entropy,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Gap,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Leakage,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.SlotCounts,
  CutQueryComplexity.GHReduction.GuideTwoGeometry,
  CutQueryComplexity.GHReduction.ThresholdCuts,
  CutQueryComplexity.GHReduction.ThresholdEndpoint,
  CutQueryComplexity.GHReduction.ThresholdProbability,
  CutQueryComplexity.GHReduction.ThresholdProgram,
  CutQueryComplexity.GHReduction.ThresholdProgress,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.Round,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.Progress,
  CutQueryComplexity.DeterministicAPMCExpansion.AdditiveShaving,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Balanced,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.FullPlayer,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Player,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Pruning,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.DepthBudget,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.TreeAccounting,
  CutQueryComplexity.DeterministicAPMCExpansion.Padding,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.LocalParameters,
  CutQueryComplexity.GHReduction.Estimates,
  CutQueryComplexity.GHReduction.GuidePruneAmplification,
  CutQueryComplexity.GHReduction.GuideSourceSwitch,
  CutQueryComplexity.GHReduction.GuideTwoCases,
  CutQueryComplexity.GHReduction.RandomPrograms,
  CutQueryComplexity.GHReduction.RandomRepetition,
  CutQueryComplexity.GHReduction.RandomTableFailure,
  CutQueryComplexity.GHReduction.SourceMaximum,
  CutQueryComplexity.GHReduction.ThresholdAmplification,
  CutQueryComplexity.GHReduction.ThresholdElimination,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.CostBounds,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.Run,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Execute,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.HistoryTrace,
  CutQueryComplexity.DeterministicAPMCExpansion.MatchingRound,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Parameters,
  CutQueryComplexity.GHReduction.DependentRandomTable,
  CutQueryComplexity.GHReduction.DependentTableMarginals,
  CutQueryComplexity.GHReduction.GuideAuxiliaryCosts,
  CutQueryComplexity.GHReduction.GuideMaximum,
  CutQueryComplexity.GHReduction.GuideSwitchTree,
  CutQueryComplexity.GHReduction.RandomContractionCost,
  CutQueryComplexity.GHReduction.RealizedCosts,
  CutQueryComplexity.GHReduction.ThresholdCosts,
  CutQueryComplexity.GHReduction.TranscriptCap,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.LowCertificate,
  CutQueryComplexity.StarContraction2022.Quantum.MinimumDegreeWitness,
  CutQueryComplexity.StarContraction2022.Quantum.TaggedQuery,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.LocalNode,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.PartitionMap,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.Program,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.Semantics,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Node,
  CutQueryComplexity.GHReduction.ApproximationValues,
  CutQueryComplexity.GHReduction.ComponentRestriction,
  CutQueryComplexity.GHReduction.FrontierCutSafety,
  CutQueryComplexity.GHReduction.GeometricBuckets,
  CutQueryComplexity.GHReduction.GuideBranchCosts,
  CutQueryComplexity.GHReduction.GuideTwoBudget,
  CutQueryComplexity.GHReduction.GuideTwoComplete,
  CutQueryComplexity.GHReduction.GuideTwoEndpoint,
  CutQueryComplexity.GHReduction.GuideTwoExecution,
  CutQueryComplexity.GHReduction.GuideTwoLedger,
  CutQueryComplexity.GHReduction.GuideTwoProgram,
  CutQueryComplexity.GHReduction.GuideTwoSuccess,
  CutQueryComplexity.GHReduction.RoundRefinement,
  CutQueryComplexity.GHReduction.SteinerTree,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds,
  CutQueryComplexity.StarContraction2022.Quantum.Global.Program,
  CutQueryComplexity.StarContraction2022.Quantum.Global.Success,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Asymptotics,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Budget,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Endpoint,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Main,
  CutQueryComplexity.GHReduction.OuterPivot.Depth,
  CutQueryComplexity.GHReduction.OuterPivot.Progress,
  CutQueryComplexity.GHReduction.OuterPivot.Step,
  CutQueryComplexity.GHReduction.SampledGuideCorrectness,
  CutQueryComplexity.GHReduction.SampledGuides,
  CutQueryComplexity.GHReduction.SingleSource,
  CutQueryComplexity.GHReduction.SingleSourceBudget,
  CutQueryComplexity.GHReduction.SteinerContraction,
  CutQueryComplexity.GHReduction.SteinerEndpoint,
  CutQueryComplexity.GHReduction.TreeAssembly,
  CutQueryComplexity.GHReduction.TreeJoin,
  CutQueryComplexity.StarContraction2022.Quantum.Global.Endpoint,
  CutQueryComplexity.GHReduction.BlockRefinementCuts,
  CutQueryComplexity.GHReduction.DisjointStarAssembly,
  CutQueryComplexity.GHReduction.FrontierExecution,
  CutQueryComplexity.GHReduction.FrontierPivotRound,
  CutQueryComplexity.GHReduction.FrontierRoundState,
  CutQueryComplexity.GHReduction.RoundCutGeometry,
  CutQueryComplexity.GHReduction.SourcePivot,
  CutQueryComplexity.GHReduction.SourcePivotCosts,
  CutQueryComplexity.GHReduction.SourcePivotProgress,
  CutQueryComplexity.GHReduction.SteinerAssemblyFold,
  CutQueryComplexity.GHReduction.SteinerJoinInterfaces,
  CutQueryComplexity.GHReduction.TrackedPivotProgress,
  CutQueryComplexity.GHReduction.FrontierAssemblyProgram,
  CutQueryComplexity.GHReduction.FrontierRoundGeometry,
  CutQueryComplexity.GHReduction.FrontierSplitCorrectness,
  CutQueryComplexity.GHReduction.FrontierConditionalProgress,
  CutQueryComplexity.GHReduction.FrontierForestCompatibility,
  CutQueryComplexity.GHReduction.FrontierTermination,
  CutQueryComplexity.GHReduction.FrontierTrackedFibers,
  CutQueryComplexity.GHReduction.FrontierWitnessInduction,
  CutQueryComplexity.GHReduction.RoundForestAssembly,
  CutQueryComplexity.GHReduction.RoundForestGeometry,
  CutQueryComplexity.GHReduction.ConfidenceLogBounds,
  CutQueryComplexity.GHReduction.ConfidenceParameters,
  CutQueryComplexity.GHReduction.FrontierAssemblyCorrectness,
  CutQueryComplexity.GHReduction.FrontierReduction,
  CutQueryComplexity.GHReduction.LogArithmetic,
  CutQueryComplexity.GHReduction.Main,
  CutQueryComplexity.GHReduction.OracleReduction,
  CutQueryComplexity.GHReduction.PolynomialBudget,
  CutQueryComplexity.GHReduction.ReductionSparsifierBudget,
  CutQueryComplexity.GHReduction.TranscriptEndpoint,
  CutQueryComplexity.GHReduction.Randomized.Family,
  CutQueryComplexity.GHReduction.Randomized.Target,
  CutQueryComplexity.GHReduction.Randomized.CallTree,
  CutQueryComplexity.GHReduction.Randomized.Interpret,
  CutQueryComplexity.GHReduction.Randomized.CallProg,
  CutQueryComplexity.GHReduction.Randomized.CallOps,
  CutQueryComplexity.GHReduction.Randomized.Reference,
  CutQueryComplexity.GHReduction.Randomized.Primitives,
  CutQueryComplexity.GHReduction.Randomized.Isolating,
  CutQueryComplexity.GHReduction.Randomized.TreeOps,
  CutQueryComplexity.GHReduction.Randomized.Thresholds,
  CutQueryComplexity.GHReduction.Randomized.GuideCalls,
  CutQueryComplexity.GHReduction.Randomized.GuideTrees,
  CutQueryComplexity.GHReduction.Randomized.GuideCosts,
  CutQueryComplexity.GHReduction.Randomized.SourcePivots,
  CutQueryComplexity.GHReduction.Randomized.Frontier,
  CutQueryComplexity.GHReduction.Randomized.Main,
  CutQueryComplexity.BoundedFlowMinCut.Basic,
  CutQueryComplexity.BoundedFlowMinCut.LowDegree,
  CutQueryComplexity.BoundedFlowMinCut.Incidence,
  CutQueryComplexity.BoundedFlowMinCut.Dominating,
  CutQueryComplexity.BoundedFlowMinCut.Ordered,
  CutQueryComplexity.BoundedFlowMinCut.Flow.Basic,
  CutQueryComplexity.BoundedFlowMinCut.Flow.Forest,
  CutQueryComplexity.BoundedFlowMinCut.Flow.Shortcut,
  CutQueryComplexity.BoundedFlowMinCut.Flow.Repair,
  CutQueryComplexity.BoundedFlowMinCut.Flow.Program,
  CutQueryComplexity.BoundedFlowMinCut.Main,
  CutQueryComplexity.BoundedFlowMinCut.Asymptotics,
  CutQueryComplexity.BoundedFlowMinCut.Endpoint,
  CutQueryComplexity.GlobalSTReduction.Specification,
  CutQueryComplexity.GlobalSTReduction.Budget,
  CutQueryComplexity.GlobalSTReduction.Replies,
  CutQueryComplexity.GlobalSTReduction.Contractions,
  CutQueryComplexity.GlobalSTReduction.Isolating,
  CutQueryComplexity.GlobalSTReduction.Calls,
  CutQueryComplexity.GlobalSTReduction.Sampling,
  CutQueryComplexity.GlobalSTReduction.Program,
  CutQueryComplexity.GlobalSTReduction.Deterministic,
  CutQueryComplexity.GlobalSTReduction.Amplification,
  CutQueryComplexity.GlobalSTReduction.Randomized,
  CutQueryComplexity.GlobalSTReduction.Asymptotics,
  CutQueryComplexity.GlobalSTReduction.Examples,
  CutQueryComplexity.GlobalSTReduction.Main
] pins [
  CutQueryComplexity.DetMinCut.SafePartition,
  CutQueryComplexity.TreeCutSparsifier.normalize_safe,
  CutQueryComplexity.TreeCutSparsifier.learn_spec,
  CutQueryComplexity.TreeCutSparsifier.learn_tree_cut_sparsifier,
  CutQueryComplexity.TreeCutSparsifier.theorem5,
  CutQueryComplexity.TreeCutSparsifier.theorem5_or_zero_cut,
  CutQueryComplexity.Hierarchy.Hier.rep_cluster_le,
  CutQueryComplexity.Hierarchy.Hier.rep_le_rep_of_clusters,
  CutQueryComplexity.Hierarchy.card_node_le,
  CutQueryComplexity.Hierarchy.normalTopology_normal,
  CutQueryComplexity.Hierarchy.normalTopology_rep_le,
  CutQueryComplexity.TreeCutSparsifier.canonicalize_spec,
  CutQueryComplexity.TreeCutSparsifier.canonicalize_cost,
  CutQueryComplexity.TreeCutSparsifier.exists_canonicalization,
  CutQueryComplexity.TreeCutSparsifier.exists_conversion,
  CutQueryComplexity.TreeCutSparsifier.exists_conversion_log,
  CutQueryComplexity.Hierarchy.RackeShah.rep_le_two_mul_sum_cut,
  CutQueryComplexity.Hierarchy.RackeShah.local_of_flow,
  CutQueryComplexity.Hierarchy.RackeShah.exists_transport,
  CutQueryComplexity.Hierarchy.RackeShah.exists_splitCert,
  CutQueryComplexity.Hierarchy.RackeShah.exists_balanced_or_bottleneck,
  CutQueryComplexity.Hierarchy.RackeShah.Bprod_le_two,
  CutQueryComplexity.Hierarchy.RackeShah.ref_flow,
  CutQueryComplexity.Hierarchy.RackeShah.certified_of_partition,
  CutQueryComplexity.Hierarchy.RackeShah.exists_certified_univ,
  CutQueryComplexity.Hierarchy.RackeShah.rackeShah_hierarchyBound,
  CutQueryComplexity.Hierarchy.RackeShah.exists_hierarchyBound_log_mul_loglog,
  CutQueryComplexity.TreeCutSparsifier.exists_good_tree_log_mul_loglog,
  CutQueryComplexity.DetMinCut.phaseBoundR_const_LK_le,
  CutQueryComplexity.DetMinCut.phaseBound_LL,
  CutQueryComplexity.DetMinCut.deterministic_mincut_log3loglog2_fin_of_hierarchyBound_of_constantGuard,
  CutQueryComplexity.DetMinCut.deterministic_mincut_log3loglog2_of_constantGuard,
  CutQueryComplexity.DetMinCut.deterministic_mincut_log3loglog2,
  CutQueryComplexity.DetMinCut.deterministic_mincut_log3loglog2_real_log,
  CutQueryComplexity.UndirectedClosure.deterministic_mincut_shore_value_log3loglog2,
  CutQueryComplexity.UndirectedClosure.supplied_hierarchy_log3loglog2,
  CutQueryComplexity.TreeCutSparsifier.exists_conversion_log3loglog2,
  CutQueryComplexity.TreeCutSparsifier.exists_conversion_log3loglog2_real_log,
  CutQueryComplexity.TreeCutSparsifier.certifyLL,
  CutQueryComplexity.TreeCutSparsifier.phaseLL_spec,
  CutQueryComplexity.TreeCutSparsifier.mainLoopLL_spec,
  CutQueryComplexity.TreeCutSparsifier.learnLL_spec,
  CutQueryComplexity.TreeCutSparsifier.learn_tree_cut_sparsifier_LL,
  CutQueryComplexity.TreeCutSparsifier.theorem5LL,
  CutQueryComplexity.TreeCutSparsifier.theorem5LL_or_zero_cut,
  CutQueryComplexity.TreeCutSparsifier.isMinCut_pull_of_safePartition,
  CutQueryComplexity.TreeCutSparsifier.convertStage_spec,
  CutQueryComplexity.TreeCutSparsifier.twoStage_spec,
  CutQueryComplexity.TreeCutSparsifier.offlineMinCut_spec,
  CutQueryComplexity.TreeCutSparsifier.twoStageAuto_spec,
  CutQueryComplexity.TreeCutSparsifier.deterministic_mincut_two_stage,
  CutQueryComplexity.TreeCutSparsifier.deterministic_mincut_two_stage_real_log,
  CutQueryComplexity.TreeCutSparsifier.logL_mul_logL_logL_le,
  CutQueryComplexity.SupportForest.support_connected_iff_pos,
  CutQueryComplexity.SupportForest.isMinCut_of_cut_eq_zero,
  CutQueryComplexity.SupportForest.findPos_spec,
  CutQueryComplexity.SupportForest.loop_spec,
  CutQueryComplexity.SupportForest.program_spec,
  CutQueryComplexity.SupportForest.forestBudget_le_linear_log,
  CutQueryComplexity.SupportForest.exists_support_forest,
  CutQueryComplexity.SupportForest.exists_connectivity_test,
  CutQueryComplexity.Search.monge_equal_between_opposite_minima,
  CutQueryComplexity.Search.allMinima_cost,
  CutQueryComplexity.Search.allMinima_spec,
  CutQueryComplexity.Search.monge_allMinima_queryBound,
  CutQueryComplexity.TwoRespecting.weak_heavy_cover,
  CutQueryComplexity.TwoRespecting.weakMajoritySearch_spec,
  CutQueryComplexity.TwoRespecting.mutual_weak_interest,
  CutQueryComplexity.TwoRespecting.rectAll_spec,
  CutQueryComplexity.TwoRespecting.samePathAll_spec,
  CutQueryComplexity.TwoRespecting.diffBlockAll_spec,
  CutQueryComplexity.TwoRespecting.allTwoRespecting_cost,
  CutQueryComplexity.TwoRespecting.allTwoRespecting_spec,
  CutQueryComplexity.TwoRespecting.allTwoRespecting_correct_of_le,
  CutQueryComplexity.TwoRespecting.allMinTwoRespecting_spec,
  CutQueryComplexity.TwoRespecting.allMinTwoRespecting_queryBound,
  CutQueryComplexity.AllMinCuts.isMinCut_iff_exists_quot,
  CutQueryComplexity.AllMinCuts.Correct.pullOutput,
  CutQueryComplexity.AllMinCuts.refine_preserves_cut,
  CutQueryComplexity.AllMinCuts.suppliedHierarchyProgLL_allMinCuts,
  CutQueryComplexity.AllMinCuts.suppliedHierarchyTreeLL_allMinCuts,
  CutQueryComplexity.AllMinCuts.AllMinCutSkeleton.covers,
  CutQueryComplexity.AllMinCuts.conversion_allMinCuts,
  CutQueryComplexity.AllMinCuts.exists_conversion_allMinCuts,
  CutQueryComplexity.AllMinCuts.coverReport_spec,
  CutQueryComplexity.AllMinCuts.cut_eq_zero_iff_sat,
  CutQueryComplexity.AllMinCuts.zeroOutput_correct,
  CutQueryComplexity.AllMinCuts.positiveStage_spec,
  CutQueryComplexity.AllMinCuts.allTwoStage_spec,
  CutQueryComplexity.AllMinCuts.offlineAll_spec,
  CutQueryComplexity.AllMinCuts.allTwoStageAuto_spec,
  CutQueryComplexity.AllMinCuts.deterministic_all_mincuts_log3loglog2,
  CutQueryComplexity.AllMinCuts.deterministic_all_mincuts_log3loglog2_real_log,
  CutQueryComplexity.AllMinCuts.card_le_of_isMinCut,
  CutQueryComplexity.AllMinCuts.Correct.card_cuts_le,
  CutQueryComplexity.AllMinCuts.sparsifierAll_whp,
  CutQueryComplexity.AllMinCuts.reportStage_spec,
  CutQueryComplexity.AllMinCuts.randomAllMinCuts_correct,
  CutQueryComplexity.AllMinCuts.randomBudget_le,
  CutQueryComplexity.AllMinCuts.randomized_all_mincuts,
  CutQueryComplexity.AllPairsAudit.cut_erase,
  CutQueryComplexity.AllPairsAudit.crossing_erase_inside,
  CutQueryComplexity.AllPairsAudit.crossing_erase_outside,
  CutQueryComplexity.AllPairsAudit.nonterminal_half,
  CutQueryComplexity.AllPairsAudit.incident_integral,
  CutQueryComplexity.AllPairsAudit.degree_integral,
  CutQueryComplexity.AllPairsAudit.crossing_integral,
  CutQueryComplexity.AllPairsAudit.exists_minimal_inside,
  CutQueryComplexity.AllPairsAudit.exists_minimal_unfriendly_inside,
  CutQueryComplexity.AllPairsAudit.degree_two_crossing_zero,
  CutQueryComplexity.AllPairsAudit.lemma34,
  CutQueryComplexity.AllPairsAudit.exists_structured_minimum,
  CutQueryComplexity.AllPairsAudit.star_cut_energy,
  CutQueryComplexity.AllPairsAudit.star_cut_dominates,
  CutQueryComplexity.AllPairsAudit.star_cut_lift,
  CutQueryComplexity.AllPairsAudit.star_cut_lift_insert,
  CutQueryComplexity.AllPairsAudit.internalDegree_from_external,
  CutQueryComplexity.AllPairsAudit.star_vertex_bound,
  CutQueryComplexity.AllPairsAudit.exists_exact_minimum_lift,
  CutQueryComplexity.AllPairsAudit.exists_star_minimum,
  CutQueryComplexity.AllPairsAudit.star_minimum_extract,
  CutQueryComplexity.AllPairsAudit.all_pairs_minimum_values,
  CutQueryComplexity.AllPairsAudit.star_minimum_extract_simple,
  CutQueryComplexity.DirectedUnitST.SparseBand.offsetInt_bounds,
  CutQueryComplexity.DirectedUnitST.SparseBand.offsetRat_abs_le_one,
  CutQueryComplexity.DirectedUnitST.SparseBand.active_abs_sub_lt_two,
  CutQueryComplexity.DirectedUnitST.SparseBand.exists_component_translate,
  CutQueryComplexity.DirectedUnitST.SparseBand.exists_bounded_potential,
  CutQueryComplexity.DirectedUnitST.SparseBand.exists_grid_cover,
  CutQueryComplexity.DirectedUnitST.SparseBand.gridAccept_bandGood,
  CutQueryComplexity.DirectedUnitST.Repair.two_supply_of_sum_zero,
  CutQueryComplexity.DirectedUnitST.Repair.residual_pair_sum,
  CutQueryComplexity.DirectedUnitST.Repair.residual_capacityDiv,
  CutQueryComplexity.DirectedUnitST.Repair.residual_difference_feasible,
  CutQueryComplexity.DirectedUnitST.Repair.comparison_feasible,
  CutQueryComplexity.DirectedUnitST.Repair.comparison_divergence,
  CutQueryComplexity.DirectedUnitST.Repair.out_eq_rectangle,
  CutQueryComplexity.DirectedUnitST.Repair.feasible_supply_le_half_sq,
  CutQueryComplexity.DirectedUnitST.Repair.exists_small_rectangle_cut_in,
  CutQueryComplexity.DirectedUnitST.Repair.middle_crossing_internal,
  CutQueryComplexity.DirectedUnitST.Repair.middle_layer_deficit,
  CutQueryComplexity.DirectedUnitST.Repair.residual_middle_layer_deficit,
  CutQueryComplexity.DirectedUnitST.Acceleration.graphPotential_lower,
  CutQueryComplexity.DirectedUnitST.Acceleration.graphPotential_upper,
  CutQueryComplexity.DirectedUnitST.Acceleration.graphPotential_initial_energy,
  CutQueryComplexity.DirectedUnitST.Acceleration.graphPotential_exists_minimizer,
  CutQueryComplexity.DirectedUnitST.Acceleration.canonical_laplacian_bound,
  CutQueryComplexity.ImplicitLP.PathFollowing.public_copy_eq,
  CutQueryComplexity.ImplicitLP.PathFollowing.frozen_copy_eq,
  CutQueryComplexity.ImplicitLP.PathFollowing.logWindow_of_potential,
  CutQueryComplexity.ImplicitLP.PathFollowing.weight_bounds_of_potential,
  CutQueryComplexity.ImplicitLP.PathFollowing.mixedEnvelope_of_potential,
  CutQueryComplexity.ImplicitLP.PathFollowing.batchProg_fail_public,
  CutQueryComplexity.ImplicitLP.PathFollowing.batchGood_invariant,
  CutQueryComplexity.ImplicitLP.PathFollowing.batch_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.run_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.run_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.run_copy_eq,
  CutQueryComplexity.DirectedCertificate.Completion.exists_terminal_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_root_split_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_source_route_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_largeShore_implicit_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_largeShore_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_local_flow_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_local_source_flow,
  CutQueryComplexity.DirectedCertificate.Completion.exists_local_source_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_separator_family_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.reverseMeasures,
  CutQueryComplexity.DirectedCertificate.Completion.exists_root_small_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_root_small_both_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_capacity_bins,
  CutQueryComplexity.DirectedCertificate.Completion.exists_compiled_capacity_cap,
  CutQueryComplexity.DirectedCertificate.Completion.exists_pruning_capacity_cap,
  CutQueryComplexity.DirectedCertificate.Completion.exists_pruning_mass_cap,
  CutQueryComplexity.DirectedCertificate.Completion.exists_masked_capacity_cap,
  CutQueryComplexity.DirectedCertificate.Completion.exists_masked_degree_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_fixed_arc_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_threshold_preparation,
  CutQueryComplexity.AllPairs.recoverCapped_correct,
  CutQueryComplexity.AllPairs.recoverCapped_cost,
  CutQueryComplexity.AllPairs.padded_min_degree,
  CutQueryComplexity.AllPairs.padded_unweighted,
  CutQueryComplexity.AllPairs.padded_minimum_extract,
  CutQueryComplexity.AllPairs.padded_substitute_eval,
  CutQueryComplexity.AllPairs.clog_potential_split,
  CutQueryComplexity.AllPairs.exists_expandingPartition,
  CutQueryComplexity.AllPairs.partitionMap_idempotent,
  CutQueryComplexity.AllPairs.partitionMap_expands,
  CutQueryComplexity.AllPairs.partitionMap_boundary_le,
  CutQueryComplexity.AllPairs.shaveProgram_respects,
  CutQueryComplexity.AllPairs.shaveProgram_cost,
  CutQueryComplexity.AllPairs.shaveProgram_sparse_bound,
  CutQueryComplexity.AllPairs.recoverStar_correct,
  CutQueryComplexity.AllPairs.recoverStar_cost,
  CutQueryComplexity.AllPairs.recoverAnswers_correct,
  CutQueryComplexity.DirectedUnitST.SparseBand.offset_band_card_le_five,
  CutQueryComplexity.DirectedUnitST.SparseBand.finite_exp_moment,
  CutQueryComplexity.DirectedUnitST.SparseBand.exists_gridAccept,
  CutQueryComplexity.DirectedUnitST.SparseBand.mem_offsetCandidates,
  CutQueryComplexity.DirectedUnitST.SparseBand.selectOffsets_good,
  CutQueryComplexity.DirectedUnitST.SparseBand.rationalActivePairs_card_le,
  CutQueryComplexity.DirectedUnitST.SparseBand.coefficientMask_card_le,
  CutQueryComplexity.DirectedUnitST.SparseBand.selectOffsets,
  CutQueryComplexity.DirectedUnitST.SparseBand.offsetsProg_cost,
  CutQueryComplexity.DirectedUnitST.SparseBand.offsetsProg_good,
  CutQueryComplexity.DirectedUnitST.Acceleration.energy_step_exact,
  CutQueryComplexity.DirectedUnitST.Acceleration.huber_energy_step,
  CutQueryComplexity.DirectedUnitST.Acceleration.huber_trajectory_error,
  CutQueryComplexity.DirectedUnitST.Acceleration.fixed_schedule_below_one,
  CutQueryComplexity.DirectedUnitST.Acceleration.gradient_sq_le_gap,
  CutQueryComplexity.DirectedUnitST.Acceleration.final_l1_discrepancy,
  CutQueryComplexity.DirectedUnitST.Acceleration.quantize_error,
  CutQueryComplexity.DirectedUnitST.Acceleration.quantized_fractional_offset,
  CutQueryComplexity.DirectedUnitST.Acceleration.quantized_opposite_saturation,
  CutQueryComplexity.DirectedUnitST.Acceleration.quantized_positive_saturation,
  CutQueryComplexity.DirectedUnitST.Acceleration.signedPairs_skew,
  CutQueryComplexity.DirectedUnitST.Acceleration.star_error_sq_bound,
  CutQueryComplexity.DirectedUnitST.Repair.potential_height_tail,
  CutQueryComplexity.DirectedUnitST.Repair.potential_height_integer,
  CutQueryComplexity.DirectedUnitST.Repair.potential_height_strong,
  CutQueryComplexity.DirectedUnitST.Repair.potential_height,
  CutQueryComplexity.DirectedUnitST.Repair.representation_height,
  CutQueryComplexity.DirectedUnitST.Repair.phase_mass_eq,
  CutQueryComplexity.DirectedUnitST.Repair.phaseDelta_eq_forward,
  CutQueryComplexity.DirectedUnitST.Repair.residual_level_rise,
  CutQueryComplexity.DirectedUnitST.Repair.walk_length_strict,
  CutQueryComplexity.DirectedUnitST.Repair.discoveries_le_distance_value,
  CutQueryComplexity.DirectedUnitST.Repair.walkFlow_divergence,
  CutQueryComplexity.DirectedUnitST.Repair.walkFlow_values,
  CutQueryComplexity.DirectedUnitST.Repair.cycle_circulation_direction,
  CutQueryComplexity.ImplicitLP.PathFollowing.artificialCost_center,
  CutQueryComplexity.ImplicitLP.PathFollowing.strictStartProg_feasible,
  CutQueryComplexity.ImplicitLP.PathFollowing.strictStartProg_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.repaired_update_constraint,
  CutQueryComplexity.ImplicitLP.PathFollowing.rounded_repair_hidden,
  CutQueryComplexity.ImplicitLP.PathFollowing.initialWeights_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.lpVec_clipPairPoint,
  CutQueryComplexity.ImplicitLP.PathFollowing.clipPairPoint_feasible,
  CutQueryComplexity.ImplicitLP.PathFollowing.upSchedule_licensed,
  CutQueryComplexity.ImplicitLP.PathFollowing.downSchedule_licensed,
  CutQueryComplexity.ImplicitLP.PathFollowing.run_failure_of_per_call,
  CutQueryComplexity.ImplicitLP.PathFollowing.stepSize_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.downSchedule_public,
  CutQueryComplexity.ImplicitLP.PathFollowing.upSchedule_public,
  CutQueryComplexity.ImplicitLP.PathFollowing.phaseSteps_bound,
  CutQueryComplexity.ImplicitLP.PathFollowing.downSchedule_reaches,
  CutQueryComplexity.ImplicitLP.PathFollowing.initialPhase_licensed,
  CutQueryComplexity.ImplicitLP.PathFollowing.initialPhase_switch,
  CutQueryComplexity.ImplicitLP.PathFollowing.truePhase_licensed,
  CutQueryComplexity.ImplicitLP.PathFollowing.public_final_accuracy,
  CutQueryComplexity.ImplicitLP.PathFollowing.phaseSteps_public_bound,
  CutQueryComplexity.DirectedCertificate.Completion.violating_small_mem_comparisonFamily,
  CutQueryComplexity.DirectedCertificate.Completion.exists_half_oneRespecting,
  CutQueryComplexity.DirectedCertificate.Completion.oneRespecting_internal_paths,
  CutQueryComplexity.DirectedCertificate.Completion.degree_cap_cut_lower_bound,
  CutQueryComplexity.DirectedUnitST.Acceleration.gradientProg_correct,
  CutQueryComplexity.DirectedUnitST.Acceleration.publicCoefficients_active,
  CutQueryComplexity.DirectedUnitST.Acceleration.publicCoefficients_forward_rise,
  CutQueryComplexity.DirectedUnitST.Acceleration.publicCoefficients_reverse_rise,
  CutQueryComplexity.DirectedUnitST.Acceleration.measured_error_sq,
  CutQueryComplexity.DirectedUnitST.Acceleration.acceleratedRun_mean_zero,
  CutQueryComplexity.DirectedUnitST.Acceleration.acceleratedRun_energy_error,
  CutQueryComplexity.DirectedUnitST.Acceleration.acceleratedRun_gradient_bound,
  CutQueryComplexity.DirectedUnitST.Acceleration.acceleratedOutput_l1,
  CutQueryComplexity.DirectedUnitST.Acceleration.acceleratedOutput_regularized_divergence,
  CutQueryComplexity.DirectedUnitST.Acceleration.fixedMuOutput_l1,
  CutQueryComplexity.DirectedUnitST.Acceleration.fixedMuOutput_mean_zero,
  CutQueryComplexity.DirectedUnitST.Acceleration.queryPotentialProg_l1,
  CutQueryComplexity.DirectedUnitST.Acceleration.queryPotentialProg_cost,
  CutQueryComplexity.DirectedUnitST.Acceleration.queryPotentialProg_cost_sqrt,
  CutQueryComplexity.DirectedUnitST.Acceleration.queryPotentialProg_l1_explicit,
  CutQueryComplexity.DirectedUnitST.Acceleration.queryPotentialProg_gradient,
  CutQueryComplexity.DirectedUnitST.Acceleration.queryPotentialProg_regularized_divergence,
  CutQueryComplexity.DirectedUnitST.Acceleration.queryPotentialProg_mean_zero,
  CutQueryComplexity.DirectedUnitST.Blocking.State.Realizes.record,
  CutQueryComplexity.DirectedUnitST.Blocking.State.Realizes.learn,
  CutQueryComplexity.DirectedUnitST.Blocking.State.Realizes.applyFlow,
  CutQueryComplexity.DirectedUnitST.Blocking.State.Realizes.row,
  CutQueryComplexity.DirectedUnitST.Blocking.NetworkState.Realizes.learn,
  CutQueryComplexity.DirectedUnitST.Blocking.NetworkState.Realizes.applyFlow,
  CutQueryComplexity.DirectedCertificate.Completion.exists_subtree_centroid,
  CutQueryComplexity.DirectedCertificate.Completion.exists_restricted_subtree_centroid,
  CutQueryComplexity.DirectedCertificate.Completion.inArbTree,
  CutQueryComplexity.DirectedCertificate.Completion.exists_centroid_decomposition,
  CutQueryComplexity.DirectedUnitST.Repair.starProg_eval,
  CutQueryComplexity.DirectedUnitST.Repair.residualStarProg_eval,
  CutQueryComplexity.DirectedUnitST.Repair.residualStarProg_cost,
  CutQueryComplexity.DirectedUnitST.Repair.findPositiveProg_cost,
  CutQueryComplexity.DirectedUnitST.Repair.findPositiveProg_spec,
  CutQueryComplexity.DirectedUnitST.Repair.discoverPairProg_cost,
  CutQueryComplexity.DirectedUnitST.Repair.discoverPairProg_spec,
  CutQueryComplexity.DirectedUnitST.Repair.residualEdgeProg_cost,
  CutQueryComplexity.DirectedUnitST.Repair.residualEdgeProg_spec,
  CutQueryComplexity.DirectedUnitST.Repair.residualEdgeProg_none_iff,
  CutQueryComplexity.AllPairs.friendlyProgram_good,
  CutQueryComplexity.AllPairs.initialSparsifier_failure,
  CutQueryComplexity.AllPairs.minDegreeProgram_failure,
  CutQueryComplexity.AllPairs.allPairsProgram_failure,
  CutQueryComplexity.AllPairs.allPairsProgram_failure_explicit,
  CutQueryComplexity.AllPairs.allPairsProgram_cost,
  CutQueryComplexity.DirectedCertificate.Completion.small_family_card_le_pow,
  CutQueryComplexity.DirectedCertificate.Completion.exists_halving_cover,
  CutQueryComplexity.DirectedCertificate.Completion.small_family_clog_le,
  CutQueryComplexity.DirectedCertificate.Completion.logL_sq_le_cube_root,
  CutQueryComplexity.DirectedCertificate.Completion.small_certificate_arithmetic,
  CutQueryComplexity.DirectedCertificate.Completion.exists_optimized_budget,
  CutQueryComplexity.DirectedCertificate.Completion.exists_unit_parameter,
  CutQueryComplexity.AllPairs.paramc_half_budget_bounds,
  CutQueryComplexity.AllPairs.capQ_public_le,
  CutQueryComplexity.AllPairs.post_cost_le,
  CutQueryComplexity.AllPairs.combined_cost_le,
  CutQueryComplexity.AllPairs.budgetLog_padded_le,
  CutQueryComplexity.AllPairs.padded_threshold_le,
  CutQueryComplexity.AllPairs.padded_combined_cost_le,
  CutQueryComplexity.AllPairs.allPairsBudget_le,
  CutQueryComplexity.AllPairs.allPairsProgram_cost_bound,
  CutQueryComplexity.AllPairs.allPairsProgram_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.artificialCost_bound,
  CutQueryComplexity.ImplicitLP.PathFollowing.initializedRun_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.initializedRun_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.center_gap_closed,
  CutQueryComplexity.ImplicitLP.PathFollowing.objective_gap_from_centrality,
  CutQueryComplexity.ImplicitLP.PathFollowing.cent_cost_change,
  CutQueryComplexity.ImplicitLP.PathFollowing.center_step_inexact,
  CutQueryComplexity.ImplicitLP.PathFollowing.frozenStep_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.frozenRun_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.frozenRun_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.frozenRun_failure_from_invariant,
  CutQueryComplexity.ImplicitLP.PathFollowing.frozenRun_endpoint,
  CutQueryComplexity.ImplicitLP.PathFollowing.batchGood_changeCost,
  CutQueryComplexity.ImplicitLP.PathFollowing.batch_switch_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.pathSolver_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.pathSolver_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.strictStart_slack,
  CutQueryComplexity.ImplicitLP.PathFollowing.strictStart_barrier_feasible,
  CutQueryComplexity.ImplicitLP.PathFollowing.terminal_clip_feasible,
  CutQueryComplexity.ImplicitLP.PathFollowing.terminal_width_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.terminal_rows_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.PublicLicense.regime,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedDelta_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTolerance_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.terminalLP_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.terminalSolver_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.terminalSolver_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.terminalSolver_valid,
  CutQueryComplexity.ImplicitLP.PathFollowing.solverFailure_of_per_call,
  CutQueryComplexity.ImplicitLP.PathFollowing.d4Fail_antitone_accuracy,
  CutQueryComplexity.ImplicitLP.PathFollowing.d4Fail_public_parameters,
  CutQueryComplexity.ImplicitLP.PathFollowing.d4Fail_numerical_parameters,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicTerminalSolver_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicTerminalSolver_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicTerminalFamily_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicGlobalSolver_success,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicGlobalSolver_cost,
  CutQueryComplexity.DirectedUnitST.Blocking.networkEdgeProg_spec,
  CutQueryComplexity.DirectedUnitST.Blocking.networkEdgeProg_cost,
  CutQueryComplexity.DirectedUnitST.Blocking.networkSearch_spec,
  CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_complete,
  CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_cost,
  CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_level_rise,
  CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_shortest,
  CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_reachable,
  CutQueryComplexity.DirectedUnitST.Blocking.bfsProg_out_zero,
  CutQueryComplexity.DirectedUnitST.Preparation.representation_pair_sum,
  CutQueryComplexity.DirectedUnitST.Preparation.representation_pairBounded,
  CutQueryComplexity.DirectedUnitST.Preparation.representation_capacityDiv,
  CutQueryComplexity.DirectedUnitST.Preparation.representation_unlearned_integer,
  CutQueryComplexity.DirectedUnitST.Preparation.potentialRepresentation_rise,
  CutQueryComplexity.DirectedUnitST.Repair.fractional_two_neighbors,
  CutQueryComplexity.DirectedUnitST.Repair.fractional_support_cycle,
  CutQueryComplexity.DirectedUnitST.Repair.fractional_circulation_direction,
  CutQueryComplexity.DirectedUnitST.Repair.fractional_bounded_step,
  CutQueryComplexity.DirectedUnitST.Repair.bounded_integral_flow,
  CutQueryComplexity.DirectedUnitST.Repair.integer_comparison_discrepancy,
  CutQueryComplexity.DirectedUnitST.Repair.rootExtend_conserves,
  CutQueryComplexity.DirectedUnitST.Repair.root_restriction_divergence,
  CutQueryComplexity.DirectedUnitST.Repair.rounding_fixes_integer,
  CutQueryComplexity.DirectedUnitST.Repair.rounding_preserves_integer_bounds,
  CutQueryComplexity.DirectedUnitST.Repair.rounding_divergence_l1,
  CutQueryComplexity.DirectedUnitST.Repair.signed_flow_rounding,
  CutQueryComplexity.DirectedUnitST.Repair.learnedCorrection_zero,
  CutQueryComplexity.DirectedUnitST.Repair.learnedCorrection_divergence_l1,
  CutQueryComplexity.DirectedUnitST.Repair.learnedCorrection_realized_integer,
  CutQueryComplexity.DirectedUnitST.Repair.learnedCanonicalSubflow_background_integer,
  CutQueryComplexity.DirectedUnitST.Repair.roundedRepresentation_integer,
  CutQueryComplexity.DirectedUnitST.Repair.roundedRepresentation_pair_sum,
  CutQueryComplexity.DirectedUnitST.Repair.roundedRepresentation_positive,
  CutQueryComplexity.DirectedUnitST.Repair.roundedRepresentation_capacityDiv,
  CutQueryComplexity.DirectedCertificate.Completion.exists_comparison_tree_cover,
  CutQueryComplexity.DirectedCertificate.Completion.exists_uniform_violation_tree_cover,
  CutQueryComplexity.DirectedCertificate.Completion.exists_connected_tree_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_prepared_small_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_pruned_smallShore_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.uniform_certificate_target,
  CutQueryComplexity.DirectedCertificate.Completion.headline_certificate_target,
  CutQueryComplexity.DirectedCertificate.Completion.exists_unit_mass_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_degree_cap_small_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_unit_global_certificate,
  CutQueryComplexity.CanonicalST.canonicalExtension_spec,
  CutQueryComplexity.CanonicalST.canonicalExtension_min,
  CutQueryComplexity.CanonicalST.canonicalExtension_injective,
  CutQueryComplexity.CanonicalST.cut_eq_of_core_trace,
  CutQueryComplexity.CanonicalST.canonicalExtension_cut_add,
  CutQueryComplexity.CanonicalST.canonicalExtension_cut_le,
  CutQueryComplexity.CanonicalST.canonicalFamily_contains_optimum,
  CutQueryComplexity.CanonicalST.canonicalFamily_contains_output_optimum,
  CutQueryComplexity.DirectedCertificate.Completion.exists_optimal_terminal_flow,
  CutQueryComplexity.DirectedCertificate.Completion.exists_terminal_witnessCertificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_exact_terminal_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_zero_terminal_certificate,
  CutQueryComplexity.DirectedUnitST.Preparation.fractionalMask_card_le,
  CutQueryComplexity.DirectedUnitST.Preparation.measurePairs_eval,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_learned,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_singleton,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_learnedCapacity,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_cost,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_cost_sqrt,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_beta,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_regularized_divergence,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_measuredDivergence,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_l1,
  CutQueryComplexity.DirectedUnitST.Preparation.preparationProg_mean_zero,
  CutQueryComplexity.DirectedUnitST.Repair.phase_layercake,
  CutQueryComplexity.DirectedUnitST.Repair.tailMass_of_remaining_deficit,
  CutQueryComplexity.DirectedUnitST.Repair.inverse_square_tail,
  CutQueryComplexity.DirectedUnitST.Repair.phase_length_split,
  CutQueryComplexity.DirectedUnitST.Repair.phase_length_sqrt,
  CutQueryComplexity.DirectedUnitST.Repair.regularized_rounding_error,
  CutQueryComplexity.DirectedUnitST.Repair.phase_count_split,
  CutQueryComplexity.DirectedUnitST.Repair.phase_count_two_thirds,
  CutQueryComplexity.CanonicalST.CoreSpec.K_le,
  CutQueryComplexity.CanonicalST.CoreSpec.J_core_le,
  CutQueryComplexity.CanonicalST.CoreSpec.K_J_disjoint,
  CutQueryComplexity.CanonicalST.CoreSpec.K_add_J_le,
  CutQueryComplexity.CanonicalST.CoreSpec.K_add_J_unit,
  CutQueryComplexity.CanonicalST.CoreSpec.K_add_induce_eq,
  CutQueryComplexity.CanonicalST.CoreSpec.measuredDegree_eq,
  CutQueryComplexity.CanonicalST.CoreSpec.empty_core_learns_all,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicDelta_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicChaseMultiplier_grid,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedChase_grid,
  CutQueryComplexity.ImplicitLP.PathFollowing.batchSupport_grid,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicExtractionScale_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicCallFailure_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedParams_license,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedParams_finalTolerance,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedParams_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_failure,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_success,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalSolver_success,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalSolver_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicRootCount_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalMinCut_success,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalMinCut_cost,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_cost_all_oracles,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedGlobalMinCut_cost_all_oracles,
  CutQueryComplexity.DirectedUnitST.Blocking.StackPath.vertices_nodup,
  CutQueryComplexity.DirectedUnitST.Blocking.deadClosed_insert,
  CutQueryComplexity.DirectedUnitST.Blocking.dfsRun_cost,
  CutQueryComplexity.DirectedUnitST.Blocking.dfsProg_complete,
  CutQueryComplexity.DirectedUnitST.Blocking.dfsProg_exhausted_blocks,
  CutQueryComplexity.DirectedUnitST.Blocking.dfsProg_cost_charged,
  CutQueryComplexity.DirectedUnitST.Blocking.dfsProg_failedRows,
  CutQueryComplexity.DirectedCertificate.Completion.exists_retained_witnessCertificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_threshold_witnessCertificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_quadratic_witnessCertificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_global_certificate_of_pruned_cap,
  CutQueryComplexity.DirectedCertificate.Completion.exists_fractional_source_parameter,
  CutQueryComplexity.DirectedCertificate.Completion.exists_pruned_refined_large_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_refined_large_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_trimmed_witnessCertificate,
  CutQueryComplexity.DirectedUnitST.Preparation.outward_complementary,
  CutQueryComplexity.DirectedUnitST.Preparation.preparation_learnedTotal,
  CutQueryComplexity.DirectedUnitST.Preparation.realizedBase_unknown,
  CutQueryComplexity.DirectedUnitST.Preparation.baseState_realizes,
  CutQueryComplexity.DirectedUnitST.Preparation.publicSubflow_background_integer,
  CutQueryComplexity.DirectedUnitST.Preparation.publicCorrection_l1,
  CutQueryComplexity.DirectedUnitST.Preparation.roundedState_realizes,
  CutQueryComplexity.DirectedUnitST.Preparation.realizedRounded_natural,
  CutQueryComplexity.DirectedUnitST.Preparation.realizedRounded_capacityDiv,
  CutQueryComplexity.DirectedUnitST.Preparation.realizedRounded_rise,
  CutQueryComplexity.DirectedUnitST.Preparation.repairDemand_integer,
  CutQueryComplexity.DirectedUnitST.Preparation.repairDemand_feasible,
  CutQueryComplexity.DirectedUnitST.Preparation.repairDemand_sum_zero,
  CutQueryComplexity.DirectedUnitST.Preparation.integralPreparationProg_cost,
  CutQueryComplexity.DirectedUnitST.Endpoint.supply_le_cap,
  CutQueryComplexity.DirectedUnitST.Endpoint.repairQueries_mono,
  CutQueryComplexity.DirectedUnitST.Endpoint.sqrt_supplyCap_le,
  CutQueryComplexity.DirectedUnitST.Endpoint.repairStages_bound,
  CutQueryComplexity.DirectedUnitST.Endpoint.precision_log_bound,
  CutQueryComplexity.DirectedUnitST.Endpoint.combined_cost_bound,
  CutQueryComplexity.DirectedUnitST.Endpoint.combined_cost_le_headline,
  CutQueryComplexity.CanonicalST.rowPrefix_correct,
  CutQueryComplexity.CanonicalST.rowPrefix_cost,
  CutQueryComplexity.CanonicalST.rowPrefix_complete,
  CutQueryComplexity.CanonicalST.rowPrefix_card_le,
  CutQueryComplexity.CanonicalST.seedRows_sound,
  CutQueryComplexity.CanonicalST.seedRows_cost,
  CutQueryComplexity.CanonicalST.seedRows_card_le,
  CutQueryComplexity.CanonicalST.decodeRecovered_mass_le,
  CutQueryComplexity.CanonicalST.decodeRecovered_le,
  CutQueryComplexity.CanonicalST.seedRows_supported,
  CutQueryComplexity.CanonicalST.seedRows_min_degree,
  CutQueryComplexity.CanonicalST.seedRows_mass_le,
  CutQueryComplexity.DirectedCertificate.Completion.intrinsic_parameters,
  CutQueryComplexity.DirectedCertificate.Completion.exists_simultaneous_intrinsic_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_inf_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_ratio_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_min_positive_weight_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_outlier_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_paper_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_unit_paper_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_weighted_global_witnessCertificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_unit_domain_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_mass_large_paper_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_intrinsic_ratio_paper_certificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_outlier_paper_certificate,
  CutQueryComplexity.DirectedUnitST.Blocking.pathDelta_feasible,
  CutQueryComplexity.DirectedUnitST.Blocking.augment_realizes,
  CutQueryComplexity.DirectedUnitST.Blocking.augmentation_saturates,
  CutQueryComplexity.DirectedUnitST.Blocking.integralCap_residual,
  CutQueryComplexity.DirectedUnitST.Blocking.deadClosed_residual,
  CutQueryComplexity.DirectedUnitST.Blocking.phaseProg_complete,
  CutQueryComplexity.DirectedUnitST.Blocking.phaseProg_cost,
  CutQueryComplexity.DirectedUnitST.Blocking.phaseProg_cost_distance_value,
  CutQueryComplexity.DirectedUnitST.Preparation.cubicScale_bounds,
  CutQueryComplexity.DirectedUnitST.Preparation.bandBudget_real,
  CutQueryComplexity.DirectedUnitST.Preparation.fiveThirdsProg_cost,
  CutQueryComplexity.DirectedUnitST.Endpoint.treeProg_run,
  CutQueryComplexity.DirectedUnitST.Endpoint.tree_bind_cost,
  CutQueryComplexity.DirectedUnitST.Endpoint.tree_bind_cost_le,
  CutQueryComplexity.DirectedUnitST.Endpoint.capTree_eval,
  CutQueryComplexity.DirectedUnitST.Endpoint.capTree_cost,
  CutQueryComplexity.DirectedUnitST.Endpoint.cappedOptionTree_eval,
  CutQueryComplexity.DirectedUnitST.Endpoint.cappedOptionTree_cost_eq,
  CutQueryComplexity.CanonicalST.coreProgram_cost,
  CutQueryComplexity.CanonicalST.initialPeel_invariant,
  CutQueryComplexity.CanonicalST.seedProgram_spec,
  CutQueryComplexity.CanonicalST.peelStep_invariant,
  CutQueryComplexity.CanonicalST.peelProgram_correct,
  CutQueryComplexity.CanonicalST.coreProgram_correct,
  CutQueryComplexity.CanonicalST.coreProgram_spec,
  CutQueryComplexity.CanonicalST.coreProgram_canonical_optimum,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicLogSize_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicEnvelope_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicDelta_inv,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicDelta_inv_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedStepSize_inv_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedSwitch_inv_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedDownSteps_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedUpSteps_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicFinalCount_pow_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicFinalCount_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicTolerance_inv_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicTolerance_inv_polynomial,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicShoreSize_spec,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicShoreSize_lower,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicShoreSize_upper,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicShoreSize_ratio,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicRootCount_balanced,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicLearnFuel_balanced,
  CutQueryComplexity.ImplicitLP.PathFollowing.balancedLearningBudget_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.balancedGlobalMinCut_success,
  CutQueryComplexity.ImplicitLP.PathFollowing.balancedGlobalMinCut_cost_split,
  CutQueryComplexity.CanonicalST.Counting.budget_le_localScale,
  CutQueryComplexity.CanonicalST.Counting.localExponent_le,
  CutQueryComplexity.CanonicalST.Counting.localLabelings_card_le,
  CutQueryComplexity.DirectedUnitST.Blocking.PhaseCorrect.distance_strict,
  CutQueryComplexity.DirectedUnitST.Blocking.solveProg_cost,
  CutQueryComplexity.DirectedUnitST.Blocking.solveProg_complete,
  CutQueryComplexity.DirectedUnitST.Blocking.solveProg_min_cut,
  CutQueryComplexity.DirectedUnitST.Blocking.solveRun_flow_integer,
  CutQueryComplexity.DirectedUnitST.Preparation.preparation_height,
  CutQueryComplexity.DirectedUnitST.Preparation.preparation_supply_le_half_sq,
  CutQueryComplexity.DirectedUnitST.Preparation.rounded_regularized_error,
  CutQueryComplexity.DirectedUnitST.Preparation.integralPreparation_height,
  CutQueryComplexity.DirectedUnitST.Preparation.integralPreparation_supply_le_half_sq,
  CutQueryComplexity.CanonicalST.Counting.exists_connectedPartition,
  CutQueryComplexity.CanonicalST.Counting.interpartMass_eq_cross,
  CutQueryComplexity.CanonicalST.Counting.degree_le_block_card_add_cut,
  CutQueryComplexity.CanonicalST.Counting.partition_card_le,
  CutQueryComplexity.CanonicalST.Counting.exists_corePartition,
  CutQueryComplexity.DirectedUnitST.Preparation.out_eq_of_pair_sum_of_capacityDiv,
  CutQueryComplexity.DirectedUnitST.Preparation.repair_restores_cuts,
  CutQueryComplexity.DirectedUnitST.Preparation.fiveThirdsIntegralProg_cost,
  CutQueryComplexity.DirectedUnitST.Preparation.integralPreparation_volume_four_thirds,
  CutQueryComplexity.DirectedUnitST.Preparation.integralPreparation_repair_scale,
  CutQueryComplexity.DirectedUnitST.Preparation.fiveThirdsIntegralProg_correct,
  CutQueryComplexity.DirectedUnitST.Preparation.PreparationSpec.restores_cuts,
  CutQueryComplexity.DirectedUnitST.Blocking.PhaseHistory.flow,
  CutQueryComplexity.DirectedUnitST.Blocking.PhaseHistory.tail_bound,
  CutQueryComplexity.DirectedUnitST.Blocking.solveProg_history,
  CutQueryComplexity.DirectedUnitST.Blocking.solveProg_cost_sharp,
  CutQueryComplexity.CanonicalST.LongEdge.crossAssignment_proper,
  CutQueryComplexity.CanonicalST.LongEdge.depthFamily_spec,
  CutQueryComplexity.CanonicalST.LongEdge.family_length,
  CutQueryComplexity.CanonicalST.LongEdge.family_adjacent,
  CutQueryComplexity.CanonicalST.LongEdge.family_separates,
  CutQueryComplexity.DirectedUnitST.Blocking.repairProg_complete,
  CutQueryComplexity.DirectedUnitST.Blocking.repairProg_cost,
  CutQueryComplexity.DirectedUnitST.Blocking.repairTree_correct,
  CutQueryComplexity.DirectedUnitST.Blocking.repairProg_value_eq,
  CutQueryComplexity.DirectedUnitST.Blocking.augmentedState_realizes,
  CutQueryComplexity.DirectedUnitST.Blocking.discrepancyRepairTree_correct,
  CutQueryComplexity.DirectedUnitST.Blocking.terminalSolve_extract,
  CutQueryComplexity.DirectedUnitST.Blocking.terminalTree_correct,
  CutQueryComplexity.DirectedUnitST.Blocking.terminalTree_unit_correct,
  CutQueryComplexity.DirectedUnitST.Blocking.discrepancyRepairTree_continue,
  CutQueryComplexity.DirectedUnitST.Blocking.cappedDiscrepancyRepairTree_continue,
  CutQueryComplexity.DirectedUnitST.Blocking.cappedDiscrepancyRepairTreeNat_eval,
  CutQueryComplexity.DirectedUnitST.Blocking.terminalTreeNat_cost,
  CutQueryComplexity.UndirectedClosure.exists_positive_dependence,
  CutQueryComplexity.UndirectedClosure.nonneg_representation_erase,
  CutQueryComplexity.UndirectedClosure.exists_nonneg_independent_representation,
  CutQueryComplexity.UndirectedClosure.exists_nonneg_sparse_representation,
  CutQueryComplexity.UndirectedClosure.exists_nonneg_sparse_rows,
  CutQueryComplexity.ImplicitLP.PathFollowing.newton_scalar_envelopes,
  CutQueryComplexity.ImplicitLP.PathFollowing.newton_iteration_bits_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.newton_deterministic_budget_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicLewis_count_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicCallCount_envelope,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicSupport_bits_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.publicSupport_budget_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibrated_spectral_log_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibrated_spectral_budget_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibrated_primitive_budgets,
  CutQueryComplexity.CanonicalST.LongEdge.binIndex_lt_count,
  CutQueryComplexity.CanonicalST.LongEdge.binIndex_one_add,
  CutQueryComplexity.CanonicalST.LongEdge.bin_forward,
  CutQueryComplexity.CanonicalST.LongEdge.bin_backward,
  CutQueryComplexity.CanonicalST.LongEdge.binCount_clog_le,
  CutQueryComplexity.CanonicalST.Counting.jointFamilies_card_le,
  CutQueryComplexity.CanonicalST.Counting.internalBudget_cast,
  CutQueryComplexity.CanonicalST.Counting.sum_internalBudget_le,
  CutQueryComplexity.CanonicalST.Counting.blockTrace_injective,
  CutQueryComplexity.CanonicalST.Counting.jointExponent_le,
  CutQueryComplexity.CanonicalST.Counting.partitionLabelings_card_le,
  CutQueryComplexity.DirectedUnitST.Endpoint.repairBudget_fin,
  CutQueryComplexity.DirectedUnitST.Endpoint.rawUnitSTTree_cost,
  CutQueryComplexity.DirectedUnitST.Endpoint.unitSTTree_eval,
  CutQueryComplexity.DirectedUnitST.Endpoint.prepared_supply_le_cap,
  CutQueryComplexity.DirectedUnitST.Endpoint.repairAndSolve_correct,
  CutQueryComplexity.DirectedUnitST.Endpoint.unitSTTree_correct,
  CutQueryComplexity.DirectedUnitST.Endpoint.unitSTNatTree_cost_real,
  CutQueryComplexity.DirectedUnitST.Endpoint.unitSTNatTree_correct,
  CutQueryComplexity.DirectedUnitST.Endpoint.exists_unitST_query_program,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibrated_terminal_budget_le,
  CutQueryComplexity.ImplicitLP.PathFollowing.calibratedTerminalSolver_query_bound,
  CutQueryComplexity.ImplicitLP.PathFollowing.balancedGlobalMinCut_query_bound,
  CutQueryComplexity.ImplicitLP.PathFollowing.directed_terminal_query_theorem,
  CutQueryComplexity.ImplicitLP.PathFollowing.directed_global_query_theorem,
  CutQueryComplexity.UndirectedClosure.exists_sparse_completion,
  CutQueryComplexity.UndirectedClosure.sparseCompletion_edgeCount,
  CutQueryComplexity.UndirectedClosure.sparseCompletion_answers,
  CutQueryComplexity.UndirectedClosure.sparseCompletion_consistent,
  CutQueryComplexity.UndirectedClosure.sparseCompletionProg_eval,
  CutQueryComplexity.UndirectedClosure.sparseCompletionProg_cost,
  CutQueryComplexity.UndirectedClosure.certificate_to_skeleton,
  CutQueryComplexity.UndirectedClosure.witnessCertificate_to_skeleton,
  CutQueryComplexity.UndirectedClosure.exists_certificate_sparse_skeleton,
  CutQueryComplexity.UndirectedClosure.withShoreValue_eval,
  CutQueryComplexity.UndirectedClosure.withShoreValue_cost,
  CutQueryComplexity.UndirectedClosure.withShoreValue_cost_le,
  CutQueryComplexity.UndirectedClosure.deterministic_mincut_shore_value_log5,
  CutQueryComplexity.CanonicalST.Phase.initial_invariant,
  CutQueryComplexity.CanonicalST.Phase.State.graph_insert,
  CutQueryComplexity.CanonicalST.Phase.insert_invariant,
  CutQueryComplexity.CanonicalST.Phase.guard_of_actual,
  CutQueryComplexity.CanonicalST.Phase.learn_invariant,
  CutQueryComplexity.CanonicalST.Phase.learn_mono,
  CutQueryComplexity.CanonicalST.Phase.learn_actual,
  CutQueryComplexity.CanonicalST.LongEdge.tests_sound,
  CutQueryComplexity.CanonicalST.LongEdge.tests_cover,
  CutQueryComplexity.CanonicalST.LongEdge.scanTests_correct,
  CutQueryComplexity.CanonicalST.LongEdge.longEdge_correct,
  CutQueryComplexity.CanonicalST.LongEdge.longEdge_cost,
  CutQueryComplexity.CanonicalST.LongEdge.longEdgeBudget_le,
  CutQueryComplexity.CanonicalST.LongEdge.deletionLongEdge_correct,
  CutQueryComplexity.CanonicalST.LongEdge.deletionLongEdge_cost,
  CutQueryComplexity.CanonicalST.LongEdge.deletionLongEdge_found_unit,
  CutQueryComplexity.CanonicalST.Counting.empty_core_count,
  CutQueryComplexity.CanonicalST.Counting.smallCutLabelings_card_le,
  CutQueryComplexity.CanonicalST.Counting.canonicalTrace_injective,
  CutQueryComplexity.CanonicalST.Counting.canonicalTrace_cut_le,
  CutQueryComplexity.CanonicalST.Counting.canonicalFamily_card_le,
  CutQueryComplexity.CanonicalST.Counting.canonicalFamily_ambient_card_le,
  CutQueryComplexity.CanonicalST.Counting.countExponent_le_ambient,
  CutQueryComplexity.CanonicalST.Counting.canonicalFamily_ambientPower_card_le,
  CutQueryComplexity.CanonicalST.Augmentation.positive_sum_lower,
  CutQueryComplexity.CanonicalST.Augmentation.row_length_lower,
  CutQueryComplexity.CanonicalST.Augmentation.lengthEnergy_divergence,
  CutQueryComplexity.CanonicalST.Augmentation.lengthEnergy_st,
  CutQueryComplexity.CanonicalST.Augmentation.supportSize_sq_le,
  CutQueryComplexity.CanonicalST.Augmentation.supportSize_le,
  CutQueryComplexity.CanonicalST.Phase.contraction_reciprocal,
  CutQueryComplexity.CanonicalST.Phase.blockLength_half,
  CutQueryComplexity.CanonicalST.Phase.contractionFuel_lt_one,
  CutQueryComplexity.CanonicalST.Phase.contracted_card_eq_zero,
  CutQueryComplexity.CanonicalST.Phase.contractionFuel_le,
  CutQueryComplexity.UndirectedClosure.hierarchyGamma_calibration,
  CutQueryComplexity.UndirectedClosure.hierarchyRawBound_le,
  CutQueryComplexity.UndirectedClosure.hierarchyBudget_le,
  CutQueryComplexity.UndirectedClosure.suppliedHierarchyProg_spec,
  CutQueryComplexity.UndirectedClosure.suppliedHierarchyTree_correct,
  CutQueryComplexity.UndirectedClosure.suppliedHierarchyTree_cost,
  CutQueryComplexity.UndirectedClosure.supplied_hierarchy_log5,
  CutQueryComplexity.CanonicalST.Witness.possiblePairs_card_ge,
  CutQueryComplexity.CanonicalST.Witness.knownPairs_card_eq_cut,
  CutQueryComplexity.CanonicalST.Witness.paddingFamily_card,
  CutQueryComplexity.CanonicalST.Witness.paddingFamily_nonempty_iff,
  CutQueryComplexity.CanonicalST.Witness.canonicalWitnesses_nonempty_iff,
  CutQueryComplexity.CanonicalST.Witness.canonicalWitnesses_empty_iff,
  CutQueryComplexity.CanonicalST.Witness.potential_le_one,
  CutQueryComplexity.CanonicalST.Witness.canonical_potential_terminals,
  CutQueryComplexity.CanonicalST.Augmentation.flowBox_compact,
  CutQueryComplexity.CanonicalST.Augmentation.cycle_direction,
  CutQueryComplexity.CanonicalST.Augmentation.minimum_mass_noDirectedCycle,
  CutQueryComplexity.CanonicalST.Augmentation.exists_cycle_free_flow,
  CutQueryComplexity.CanonicalST.Augmentation.exists_cycle_free_integral_flow,
  CutQueryComplexity.CanonicalST.Augmentation.topological_numbering,
  CutQueryComplexity.CanonicalST.Witness.paddingFamily_card_eq_multiplicity,
  CutQueryComplexity.CanonicalST.Witness.paddedWitnesses_card_eq_sum,
  CutQueryComplexity.CanonicalST.Witness.potential_eq_weighted_sum,
  CutQueryComplexity.CanonicalST.Witness.paddingFamily_card_le_pow,
  CutQueryComplexity.CanonicalST.Witness.phase_paddedWitnesses_card_le,
  CutQueryComplexity.CanonicalST.Witness.phase_canonicalWitnesses_card_le,
  CutQueryComplexity.CanonicalST.Witness.phase_canonicalWitnesses_card_le_two_pow,
  CutQueryComplexity.ImplicitLP.GenericQuery.vec_hidden,
  CutQueryComplexity.ImplicitLP.GenericQuery.copy_eq,
  CutQueryComplexity.ImplicitLP.GenericQuery.hidden_count,
  CutQueryComplexity.ImplicitLP.GenericQuery.rowCount_eq,
  CutQueryComplexity.DirectedCertificate.Completion.eulerianQueries_card_le,
  CutQueryComplexity.DirectedCertificate.Completion.eulerian_of_consistent_degrees,
  CutQueryComplexity.DirectedCertificate.Completion.consistent_sym_of_symLiftQueries,
  CutQueryComplexity.DirectedCertificate.Completion.sym_cut_eq_two_out_of_eulerian,
  CutQueryComplexity.DirectedCertificate.Completion.isGlobalMinCut_of_sym_eulerian,
  CutQueryComplexity.DirectedCertificate.Completion.eulerian_witnessCertificate_of_sym,
  CutQueryComplexity.DirectedCertificate.Completion.exists_eulerian_witnessCertificate,
  CutQueryComplexity.DirectedCertificate.Completion.exists_exact_eulerian_certificate,
  CutQueryComplexity.CanonicalST.Augmentation.exists_flow_of_cut_lower,
  CutQueryComplexity.CanonicalST.Augmentation.exists_acyclic_integral_of_cut_lower,
  CutQueryComplexity.CanonicalST.Augmentation.exists_integral_maxFlow,
  CutQueryComplexity.CanonicalST.Augmentation.exists_maximumFlow,
  CutQueryComplexity.CanonicalST.Augmentation.maximumFlow_spec,
  CutQueryComplexity.CanonicalST.Augmentation.naturalPositive_div,
  CutQueryComplexity.CanonicalST.Augmentation.cycle_free_support_bound,
  CutQueryComplexity.CanonicalST.Augmentation.residualCapacity_cut,
  CutQueryComplexity.CanonicalST.Augmentation.add_residual_flow,
  CutQueryComplexity.CanonicalST.Augmentation.exists_residual_augmentation,
  CutQueryComplexity.CanonicalST.Augmentation.terminalValue_mono,
  CutQueryComplexity.CanonicalST.Augmentation.FlowSpec.unit_values,
  CutQueryComplexity.CanonicalST.Augmentation.FlowSpec.saturated_of_cut_eq,
  CutQueryComplexity.CanonicalST.Augmentation.FlowSpec.no_residual_path,
  CutQueryComplexity.CanonicalST.Augmentation.maximumFlow_no_residual_path,
  CutQueryComplexity.ImplicitLP.GenericQuery.matrix_idRows,
  CutQueryComplexity.ImplicitLP.GenericQuery.explicitGram_eq,
  CutQueryComplexity.ImplicitLP.GenericQuery.gram_eq,
  CutQueryComplexity.ImplicitLP.GenericQuery.transpose_vec,
  CutQueryComplexity.ImplicitLP.GenericQuery.matrix_mulVec,
  CutQueryComplexity.ImplicitLP.GenericQuery.vec_repairPoint,
  CutQueryComplexity.ImplicitLP.GenericQuery.repairPoint_feasible,
  CutQueryComplexity.ImplicitLP.GenericQuery.rowCount_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.matrix_row_bounds,
  CutQueryComplexity.ImplicitLP.GenericQuery.matrix_row_ne_zero,
  CutQueryComplexity.CanonicalST.Witness.padding_missing_card,
  CutQueryComplexity.CanonicalST.Witness.padding_missing_mul,
  CutQueryComplexity.CanonicalST.Witness.phase_padding_missing,
  CutQueryComplexity.CanonicalST.Witness.potential_separation,
  CutQueryComplexity.CanonicalST.Witness.paddedWitnesses_addEdge,
  CutQueryComplexity.CanonicalST.Witness.phase_witness_loss_count,
  CutQueryComplexity.CanonicalST.Witness.phase_witness_loss,
  CutQueryComplexity.CanonicalST.Witness.phase_witness_contraction,
  CutQueryComplexity.CanonicalST.Witness.addEdge_unit,
  CutQueryComplexity.CanonicalST.Witness.addEdge_le,
  CutQueryComplexity.CanonicalST.Witness.addEdge_supported,
  CutQueryComplexity.Certificate.GomoryHu.sum_degree,
  CutQueryComplexity.Certificate.GomoryHu.zero_tree_certificate,
  CutQueryComplexity.Certificate.GomoryHu.eq_of_consistent_allPairQueries,
  CutQueryComplexity.Certificate.GomoryHu.exists_quadratic_certificate,
  CutQueryComplexity.Certificate.TreePattern.pairIndex_injective,
  CutQueryComplexity.Certificate.TreePattern.publicCost_reverse,
  CutQueryComplexity.Certificate.TreePattern.abs_sum_signed_two_pow_lt,
  CutQueryComplexity.Certificate.TreePattern.signed_two_pow_sum_ne_zero,
  CutQueryComplexity.Certificate.TreePattern.signed_pairCost_sum_ne_zero,
  CutQueryComplexity.Certificate.GomoryHu.exists_halving_cutCondition_of_terminal_lower,
  CutQueryComplexity.Certificate.GomoryHu.exists_halving_of_terminal_lower,
  CutQueryComplexity.Certificate.GomoryHu.exists_halvingCert_of_terminal_lower,
  CutQueryComplexity.Certificate.GomoryHu.exists_terminal_lower_certificate,
  CutQueryComplexity.CanonicalST.Augmentation.unknownSupportGraph_le,
  CutQueryComplexity.CanonicalST.Augmentation.unknownSupportGraph_mass_le,
  CutQueryComplexity.CanonicalST.Augmentation.unknownSupportGraph_flow,
  CutQueryComplexity.CanonicalST.Augmentation.exists_sparse_augmentation,
  CutQueryComplexity.CanonicalST.Augmentation.FlowSpec.variation_lower,
  CutQueryComplexity.CanonicalST.Augmentation.witness_variation_le,
  CutQueryComplexity.CanonicalST.Augmentation.long_edge_of_variation,
  CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_pos,
  CutQueryComplexity.CanonicalST.Augmentation.exists_long_unknown_edge,
  CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_le_half,
  CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_ge_sqrt,
  CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_ge_reciprocal,
  CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_quarter_ge,
  CutQueryComplexity.CanonicalST.Augmentation.phaseDelta_four_div_le,
  CutQueryComplexity.CanonicalST.Reachability.usedGraph_le,
  CutQueryComplexity.CanonicalST.Reachability.residual_iff,
  CutQueryComplexity.CanonicalST.Reachability.searchUnused_correct,
  CutQueryComplexity.CanonicalST.Reachability.program_cost,
  CutQueryComplexity.CanonicalST.Reachability.run_correct,
  CutQueryComplexity.CanonicalST.Reachability.program_reaches,
  CutQueryComplexity.CanonicalST.Reachability.program_correct,
  CutQueryComplexity.ImplicitLP.GenericQuery.transposeProg_eval,
  CutQueryComplexity.ImplicitLP.GenericQuery.transposeProg_cost,
  CutQueryComplexity.ImplicitLP.GenericQuery.newtonStepProg_cost,
  CutQueryComplexity.ImplicitLP.GenericQuery.newtonStepProg_eval,
  CutQueryComplexity.ImplicitLP.GenericQuery.newtonStepProg_feasible,
  CutQueryComplexity.ImplicitLP.GenericQuery.original_row_count,
  CutQueryComplexity.ImplicitLP.GenericQuery.objective_l1,
  CutQueryComplexity.ImplicitLP.GenericQuery.lewis_floor_public,
  CutQueryComplexity.ImplicitLP.GenericQuery.final_error_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.finalCount_reaches,
  CutQueryComplexity.Certificate.TreePattern.walkCost_ne_zero_of_isTrail,
  CutQueryComplexity.Certificate.TreePattern.zeroGraph_isAcyclic,
  CutQueryComplexity.Certificate.TreePattern.treePotential_root,
  CutQueryComplexity.Certificate.TreePattern.treePotential_edge,
  CutQueryComplexity.Certificate.TreePattern.treePotential_unique,
  CutQueryComplexity.Certificate.TreePattern.zeroGraph_treePotential,
  CutQueryComplexity.Certificate.TreePattern.reducedCost_eq_zero_iff,
  CutQueryComplexity.Certificate.TreePattern.treeCorrection_netOut,
  CutQueryComplexity.Certificate.TreePattern.edgeSide_netOut,
  CutQueryComplexity.Certificate.TreePattern.treeSupported_flow_unique,
  CutQueryComplexity.Certificate.TreePattern.treeCorrection_unique,
  CutQueryComplexity.Certificate.GomoryHu.RootProtected.round_cut_le,
  CutQueryComplexity.Certificate.GomoryHu.exists_round_blocks,
  CutQueryComplexity.Certificate.GomoryHu.exists_quotient_round,
  CutQueryComplexity.Certificate.GomoryHu.lift_minCut,
  CutQueryComplexity.Certificate.GomoryHu.exists_rootProtected_certificate,
  CutQueryComplexity.Certificate.GomoryHu.BlockPartition.exists_protection_certificate,
  CutQueryComplexity.Certificate.GomoryHu.BlockPartition.exists_learned_quotient_certificate,
  CutQueryComplexity.Certificate.TreePattern.labelledTree_card_zero,
  CutQueryComplexity.Certificate.TreePattern.labelledTree_card_one,
  CutQueryComplexity.Certificate.TreePattern.Prufer.TreeOn.exists_leaf,
  CutQueryComplexity.Certificate.TreePattern.Prufer.TreeOn.erase_leaf,
  CutQueryComplexity.Certificate.TreePattern.Prufer.TreeOn.attach_leaf,
  CutQueryComplexity.Certificate.TreePattern.Prufer.reconstruct_leaf,
  CutQueryComplexity.CanonicalST.Phase.program_cost,
  CutQueryComplexity.CanonicalST.Phase.witnesses_card_bound,
  CutQueryComplexity.CanonicalST.Phase.search_refutes,
  CutQueryComplexity.CanonicalST.Phase.learn_contracts,
  CutQueryComplexity.CanonicalST.Phase.step_correct,
  CutQueryComplexity.CanonicalST.Phase.run_correct,
  CutQueryComplexity.CanonicalST.Phase.program_correct,
  CutQueryComplexity.ImplicitLP.GenericQuery.explSum_eq,
  CutQueryComplexity.ImplicitLP.GenericQuery.supportPub_eval,
  CutQueryComplexity.ImplicitLP.GenericQuery.supportPub_hidden,
  CutQueryComplexity.ImplicitLP.GenericQuery.supportPub_public,
  CutQueryComplexity.ImplicitLP.GenericQuery.supportPubProg_cost,
  CutQueryComplexity.ImplicitLP.GenericQuery.newtonStep_numeric,
  CutQueryComplexity.ImplicitLP.GenericQuery.newtonStep_numeric_inv,
  CutQueryComplexity.Certificate.TreePattern.flowQueries_card_le,
  CutQueryComplexity.Certificate.TreePattern.nonTreeFlow_isFlow,
  CutQueryComplexity.Certificate.TreePattern.nonTreeFlow_netOut,
  CutQueryComplexity.Certificate.TreePattern.accepts_sound,
  CutQueryComplexity.Certificate.TreePattern.accepts_transfer,
  CutQueryComplexity.Certificate.TreePattern.accepts_of_normalForm,
  CutQueryComplexity.Certificate.TreePattern.verifyFlow_eval,
  CutQueryComplexity.Certificate.TreePattern.verifyFlow_cost,
  CutQueryComplexity.CanonicalST.Decision.program_cost,
  CutQueryComplexity.CanonicalST.Decision.stages_correct,
  CutQueryComplexity.CanonicalST.Decision.program_correct,
  CutQueryComplexity.CanonicalST.Decision.searchProgram_cost,
  CutQueryComplexity.CanonicalST.Decision.search_correct,
  CutQueryComplexity.CanonicalST.Decision.searchProgram_correct,
  CutQueryComplexity.Certificate.GomoryHu.exists_path_crossing,
  CutQueryComplexity.Certificate.GomoryHu.exists_public_pair_shore,
  CutQueryComplexity.Certificate.GomoryHu.TreeCertificate.pair_shore,
  CutQueryComplexity.Certificate.GomoryHu.disjoint_frontier_volume,
  CutQueryComplexity.Certificate.GomoryHu.exists_connected_centroid,
  CutQueryComplexity.Certificate.GomoryHu.exists_pathClosed_centroid,
  CutQueryComplexity.Certificate.GomoryHu.frontierPartition,
  CutQueryComplexity.Certificate.GomoryHu.card_frontierVertex,
  CutQueryComplexity.Certificate.GomoryHu.frontier_protected,
  CutQueryComplexity.Certificate.GomoryHu.lift_frontier_minCut,
  CutQueryComplexity.CanonicalST.terminalValue_lt_card,
  CutQueryComplexity.CanonicalST.finish_correct,
  CutQueryComplexity.CanonicalST.terminalProgram_cost,
  CutQueryComplexity.CanonicalST.terminalProgram_correct,
  CutQueryComplexity.CanonicalST.exists_terminal_query_program,
  CutQueryComplexity.CanonicalST.phaseFuel_le,
  CutQueryComplexity.CanonicalST.phaseQueryBudget_le,
  CutQueryComplexity.CanonicalST.sqrtSum_le,
  CutQueryComplexity.CanonicalST.reciprocalSqrtSum_le,
  CutQueryComplexity.CanonicalST.decisionQueryBudget_le,
  CutQueryComplexity.CanonicalST.uniformBudget_le,
  CutQueryComplexity.CanonicalST.queryBudget_le,
  CutQueryComplexity.CanonicalST.headlineProgram_cost,
  CutQueryComplexity.CanonicalST.headlineProgram_correct,
  CutQueryComplexity.CanonicalST.exists_terminal_sqrt_program,
  CutQueryComplexity.CanonicalST.exists_weakSkeleton_terminal_gap,
  CutQueryComplexity.CanonicalST.SkeletonCounterexample.skeleton_support_le,
  CutQueryComplexity.CanonicalST.SkeletonCounterexample.global_value,
  CutQueryComplexity.CanonicalST.SkeletonCounterexample.terminal_value,
  CutQueryComplexity.ImplicitLP.GenericQuery.box_closed_iff,
  CutQueryComplexity.ImplicitLP.GenericQuery.original_slack,
  CutQueryComplexity.ImplicitLP.GenericQuery.initial_feasible,
  CutQueryComplexity.ImplicitLP.GenericQuery.initial_slack,
  CutQueryComplexity.ImplicitLP.GenericQuery.cost_norm_le,
  CutQueryComplexity.Certificate.TreePattern.DirectedWalk.exists_simple_le,
  CutQueryComplexity.Certificate.TreePattern.shortestCost_realized,
  CutQueryComplexity.Certificate.TreePattern.shortestCost_arc,
  CutQueryComplexity.Certificate.TreePattern.exists_residual_potential,
  CutQueryComplexity.Certificate.TreePattern.exists_minCost_flow,
  CutQueryComplexity.Certificate.TreePattern.minCost_closedWalk_nonneg,
  CutQueryComplexity.Certificate.TreePattern.exists_flow_complementary_potential,
  CutQueryComplexity.Certificate.TreePattern.exists_strict_zeroGraph_extension,
  CutQueryComplexity.Certificate.TreePattern.exists_sign_refining_tree,
  CutQueryComplexity.Certificate.TreePattern.normalForm_flow_unique,
  CutQueryComplexity.Certificate.TreePattern.exists_normalForm,
  CutQueryComplexity.Certificate.TreePattern.exists_accepting_tree,
  CutQueryComplexity.Certificate.TreePattern.Prufer.clique_tree_of_card_two,
  CutQueryComplexity.Certificate.TreePattern.Prufer.degree_congr_graph,
  CutQueryComplexity.Certificate.TreePattern.Prufer.attach_degree_new,
  CutQueryComplexity.Certificate.TreePattern.Prufer.attach_degree_old,
  CutQueryComplexity.Certificate.TreePattern.Prufer.decode_spec,
  CutQueryComplexity.Certificate.TreePattern.Prufer.decode_tree,
  CutQueryComplexity.Certificate.TreePattern.Prufer.decode_degree,
  CutQueryComplexity.Certificate.TreePattern.Prufer.available_eq_leaves,
  CutQueryComplexity.GHReduction.localShore_separates,
  CutQueryComplexity.GHReduction.mem_terminalShores,
  CutQueryComplexity.GHReduction.terminalShores_nonempty,
  CutQueryComplexity.GHReduction.terminalMin_nonneg,
  CutQueryComplexity.GHReduction.terminalMin_le,
  CutQueryComplexity.GHReduction.le_terminalMin,
  CutQueryComplexity.GHReduction.exists_terminalMin,
  CutQueryComplexity.GHReduction.onVertices_cut_eq_of_support,
  CutQueryComplexity.GHReduction.exists_terminalGuide_pmf,
  CutQueryComplexity.GHReduction.terminalGuidePMF_spec,
  CutQueryComplexity.GHReduction.terminalMin_lower_of_cut_lower,
  CutQueryComplexity.GHReduction.terminalMin_pos_of_approx,
  CutQueryComplexity.GHReduction.terminalGuidePMF_failure_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.vec_eq_weights,
  CutQueryComplexity.ImplicitLP.GenericQuery.vec_clipQPt,
  CutQueryComplexity.ImplicitLP.GenericQuery.vec_normDPt,
  CutQueryComplexity.ImplicitLP.GenericQuery.vec_normQPt,
  CutQueryComplexity.ImplicitLP.GenericQuery.vec_invSlackPt,
  CutQueryComplexity.ImplicitLP.GenericQuery.support_envelopes,
  CutQueryComplexity.ImplicitLP.GenericQuery.supportPub_env,
  CutQueryComplexity.ImplicitLP.GenericQuery.batch_support_public,
  CutQueryComplexity.Certificate.TreePattern.exists_matching_terminal_flow,
  CutQueryComplexity.Certificate.TreePattern.verifyFlow_exists_iff,
  CutQueryComplexity.Certificate.TreePattern.public_flow_patterns,
  CutQueryComplexity.Certificate.TreePattern.terminalShores_card,
  CutQueryComplexity.Certificate.TreePattern.terminalDescriptions_card,
  CutQueryComplexity.Certificate.TreePattern.terminal_certificate_of_accepts,
  CutQueryComplexity.Certificate.TreePattern.exists_terminal_tree_certificate,
  CutQueryComplexity.Certificate.TreePattern.verifyTerminal_eval,
  CutQueryComplexity.Certificate.TreePattern.verifyTerminal_cost,
  CutQueryComplexity.Certificate.TreePattern.verifyTerminal_sound,
  CutQueryComplexity.Certificate.TreePattern.exists_verified_terminal_certificate,
  CutQueryComplexity.Certificate.TreePattern.public_terminal_certificates,
  CutQueryComplexity.Certificate.GomoryHu.exists_refinement_certificate,
  CutQueryComplexity.Certificate.GomoryHu.frontier_refines_star,
  CutQueryComplexity.Certificate.GomoryHu.exists_centroid_step_certificate,
  CutQueryComplexity.Certificate.GomoryHu.separatorPart_boundary,
  CutQueryComplexity.Certificate.GomoryHu.exists_degree_certificate,
  CutQueryComplexity.Certificate.GomoryHu.sum_degree_sq_le,
  CutQueryComplexity.Certificate.TreePattern.Prufer.decode_injective,
  CutQueryComplexity.Certificate.TreePattern.Prufer.TreeOn.eq_clique_of_card_two,
  CutQueryComplexity.Certificate.TreePattern.Prufer.encode_spec,
  CutQueryComplexity.Certificate.TreePattern.Prufer.decode_encode,
  CutQueryComplexity.Certificate.TreePattern.Prufer.encode_decode,
  CutQueryComplexity.Certificate.TreePattern.Prufer.decode_surjective,
  CutQueryComplexity.StarContraction2022.validateCount_spec,
  CutQueryComplexity.StarContraction2022.validate_singleton,
  CutQueryComplexity.StarContraction2022.verifyShore_sound,
  CutQueryComplexity.StarContraction2022.verifyShore_cost,
  CutQueryComplexity.StarContraction2022.retain_sound,
  CutQueryComplexity.StarContraction2022.retain_preserves_minimum,
  CutQueryComplexity.StarContraction2022.Recovery.mem_box,
  CutQueryComplexity.StarContraction2022.Recovery.singletonFamily_separates,
  CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_separates,
  CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_card_le,
  CutQueryComplexity.StarContraction2022.Recovery.decode_sound,
  CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_decode,
  CutQueryComplexity.StarContraction2022.Recovery.sparse_decode,
  CutQueryComplexity.ImplicitLP.GenericQuery.explicitGram_lewis,
  CutQueryComplexity.ImplicitLP.GenericQuery.vec_lewisNewY,
  CutQueryComplexity.ImplicitLP.GenericQuery.lewis_step_err,
  CutQueryComplexity.ImplicitLP.GenericQuery.lewisLoop_cost,
  CutQueryComplexity.ImplicitLP.GenericQuery.lewisLoop_fail_le,
  CutQueryComplexity.Certificate.TreePattern.pruferDecode_injective,
  CutQueryComplexity.Certificate.TreePattern.pruferDecode_surjective,
  CutQueryComplexity.Certificate.TreePattern.pruferDecode_encode,
  CutQueryComplexity.Certificate.TreePattern.pruferEncode_decode,
  CutQueryComplexity.Certificate.TreePattern.pruferEncode_degree,
  CutQueryComplexity.Certificate.TreePattern.labelledTrees_card,
  CutQueryComplexity.StarContraction2022.PublicQuotient.proper_lift_iff,
  CutQueryComplexity.StarContraction2022.PublicQuotient.integral_graph,
  CutQueryComplexity.StarContraction2022.PublicQuotient.project_minimum,
  CutQueryComplexity.StarContraction2022.PublicQuotient.lift_minimum,
  CutQueryComplexity.StarContraction2022.PublicQuotient.mincut_eq,
  CutQueryComplexity.StarContraction2022.PublicQuotient.two_le_card_of_survives,
  CutQueryComplexity.StarContraction2022.PublicQuotient.compile_eval,
  CutQueryComplexity.StarContraction2022.PublicQuotient.compile_cost,
  CutQueryComplexity.ImplicitLP.GenericQuery.lewis_restart,
  CutQueryComplexity.ImplicitLP.GenericQuery.lewisStage,
  CutQueryComplexity.Certificate.GomoryHu.levelClass_pathClosed,
  CutQueryComplexity.Certificate.GomoryHu.levelParts_boundary_lt,
  CutQueryComplexity.Certificate.GomoryHu.FundamentalCorrect.level_terminal_lower,
  CutQueryComplexity.Certificate.GomoryHu.exists_frontier_terminal_certificate,
  CutQueryComplexity.Certificate.GomoryHu.exists_level_step_certificate,
  CutQueryComplexity.Certificate.GomoryHu.exists_level_certificate,
  CutQueryComplexity.Certificate.TreePattern.flowPatternFamily_card_le_cayley,
  CutQueryComplexity.Certificate.TreePattern.terminalDescriptions_card_cayley,
  CutQueryComplexity.Certificate.TreePattern.public_flow_patterns_cayley,
  CutQueryComplexity.Certificate.TreePattern.public_terminal_certificates_cayley,
  CutQueryComplexity.StarContraction2022.threshold_cut_eq_of_lt,
  CutQueryComplexity.StarContraction2022.threshold_minimum,
  CutQueryComplexity.StarContraction2022.threshold_lift_minimum,
  CutQueryComplexity.StarContraction2022.sequentialCertificate_correct,
  CutQueryComplexity.StarContraction2022.sequentialCertificate_cost,
  CutQueryComplexity.StarContraction2022.sequentialShore_correct,
  CutQueryComplexity.StarContraction2022.sequentialShore_cost,
  CutQueryComplexity.StarContraction2022.sequentialShore_sound,
  CutQueryComplexity.ImplicitLP.GenericQuery.freezeW_rel,
  CutQueryComplexity.ImplicitLP.GenericQuery.freezeQ_abs,
  CutQueryComplexity.ImplicitLP.GenericQuery.newtonProg_cost,
  CutQueryComplexity.ImplicitLP.GenericQuery.newtonProg_fail_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.newtonStep_public,
  CutQueryComplexity.ImplicitLP.GenericQuery.newtonProgPub_numeric,
  CutQueryComplexity.StarContraction2022.Probability.product,
  CutQueryComplexity.StarContraction2022.Probability.mass_product,
  CutQueryComplexity.StarContraction2022.Probability.condition_product,
  CutQueryComplexity.StarContraction2022.Probability.condition_uniformRows,
  CutQueryComplexity.StarContraction2022.Probability.neighborTape_support,
  CutQueryComplexity.StarContraction2022.Probability.neighborTape_avoidance,
  CutQueryComplexity.StarContraction2022.Probability.mass_bind_ge,
  CutQueryComplexity.StarContraction2022.Probability.mass_inter_eq_mul_filter,
  CutQueryComplexity.StarContraction2022.Certificates.forestSum_integral,
  CutQueryComplexity.StarContraction2022.Certificates.forestSum_edgeMass,
  CutQueryComplexity.StarContraction2022.Certificates.forestSum_edgeMass_le,
  CutQueryComplexity.StarContraction2022.Certificates.ResidualForestChain.acyclic,
  CutQueryComplexity.StarContraction2022.Certificates.residualForestChain_invariant,
  CutQueryComplexity.StarContraction2022.Certificates.residualForestChain_certificate,
  CutQueryComplexity.StarContraction2022.Certificates.empty_certificate,
  CutQueryComplexity.ImplicitLP.GenericQuery.batchProg_cost,
  CutQueryComplexity.ImplicitLP.GenericQuery.batchProg_fail,
  CutQueryComplexity.ImplicitLP.GenericQuery.batchGood_tchange,
  CutQueryComplexity.StarContraction2022.Recovery.positiveLevel_antichain,
  CutQueryComplexity.StarContraction2022.Recovery.centralBinom_square_bound,
  CutQueryComplexity.StarContraction2022.Recovery.middle_choose_square_bound,
  CutQueryComplexity.StarContraction2022.Recovery.positiveLevel_square_bound,
  CutQueryComplexity.StarContraction2022.Recovery.collision_card_le,
  CutQueryComplexity.StarContraction2022.Recovery.collision_square_bound,
  CutQueryComplexity.StarContraction2022.Recovery.collision_card_le_half,
  CutQueryComplexity.StarContraction2022.Recovery.exists_separating_of_collision_sum,
  CutQueryComplexity.StarContraction2022.Recovery.signedSmall_card_le,
  CutQueryComplexity.StarContraction2022.Recovery.differences_sparse_card_le,
  CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_box_card_le_samples,
  CutQueryComplexity.StarContraction2022.Recovery.minimumFamily_sparse_card_le_samples,
  CutQueryComplexity.StarContraction2022.Recovery.denseFamily_card_bound,
  CutQueryComplexity.StarContraction2022.Recovery.sparseFamily_card_bound,
  CutQueryComplexity.StarContraction2022.Recovery.sparseRawBudget_bound,
  CutQueryComplexity.StarContraction2022.Recovery.matrixSignature_injective,
  CutQueryComplexity.StarContraction2022.Recovery.validateMeasurements_sound,
  CutQueryComplexity.StarContraction2022.Recovery.sparseBilinearProgram_correct,
  CutQueryComplexity.StarContraction2022.Recovery.sparseBilinearProgram_cost,
  CutQueryComplexity.StarContraction2022.Schedule.attemptCoefficient_expand,
  CutQueryComplexity.StarContraction2022.Schedule.log_degree_ge,
  CutQueryComplexity.StarContraction2022.Schedule.log_size_ge,
  CutQueryComplexity.StarContraction2022.Schedule.centerProbability_le_one,
  CutQueryComplexity.StarContraction2022.Schedule.centerProbability_le_half,
  CutQueryComplexity.StarContraction2022.Schedule.twoOut_degree_envelope,
  CutQueryComplexity.StarContraction2022.Schedule.height_centers_le,
  CutQueryComplexity.StarContraction2022.Schedule.middle_component_guard,
  CutQueryComplexity.StarContraction2022.Schedule.high_component_guard,
  CutQueryComplexity.StarContraction2022.Schedule.high_weighted_envelope,
  CutQueryComplexity.StarContraction2022.Schedule.middle_small_envelope,
  CutQueryComplexity.StarContraction2022.Schedule.parallelEligible_of_cube,
  CutQueryComplexity.StarContraction2022.Schedule.middle_large_envelope,
  CutQueryComplexity.StarContraction2022.Schedule.capped_linear_envelope,
  CutQueryComplexity.StarContraction2022.Schedule.middle_parallelClock_le,
  CutQueryComplexity.StarContraction2022.Schedule.small_degree_parallelClock_le,
  CutQueryComplexity.StarContraction2022.Schedule.repetition_failure_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.public_copy_eq,
  CutQueryComplexity.ImplicitLP.GenericQuery.frozen_copy_eq,
  CutQueryComplexity.ImplicitLP.GenericQuery.logWindow_of_potential,
  CutQueryComplexity.ImplicitLP.GenericQuery.weight_bounds_of_potential,
  CutQueryComplexity.ImplicitLP.GenericQuery.mixedEnvelope_of_potential,
  CutQueryComplexity.ImplicitLP.GenericQuery.batchProg_fail_public,
  CutQueryComplexity.ImplicitLP.GenericQuery.batchGood_invariant,
  CutQueryComplexity.ImplicitLP.GenericQuery.batch_failure,
  CutQueryComplexity.ImplicitLP.GenericQuery.run_failure,
  CutQueryComplexity.ImplicitLP.GenericQuery.run_cost,
  CutQueryComplexity.ImplicitLP.GenericQuery.run_copy_eq,
  CutQueryComplexity.StarContraction2022.Probability.fixedSize_contains,
  CutQueryComplexity.StarContraction2022.Probability.expect_uniform_eq,
  CutQueryComplexity.StarContraction2022.Probability.sum_inter_choose,
  CutQueryComplexity.StarContraction2022.Probability.uniformMean_crossingCount,
  CutQueryComplexity.StarContraction2022.Probability.fixedSize_ratio_mean,
  CutQueryComplexity.StarContraction2022.Probability.fixedSize_full_ratio,
  CutQueryComplexity.StarContraction2022.Probability.uniformMean_crossingCount_sq,
  CutQueryComplexity.StarContraction2022.Probability.uniformMean_ratio_variance,
  CutQueryComplexity.StarContraction2022.Probability.uniformMean_ratio_variance_le,
  CutQueryComplexity.StarContraction2022.Probability.fixedSize_ratio_tail,
  CutQueryComplexity.StarContraction2022.Probability.sizeMixture_ratio_mean,
  CutQueryComplexity.StarContraction2022.Probability.sizeMixture_ratio_variance_le,
  CutQueryComplexity.StarContraction2022.Probability.sizeMixture_ratio_tail,
  CutQueryComplexity.StarContraction2022.Probability.acceptedSize_ratio_tail,
  CutQueryComplexity.StarContraction2022.Probability.bernoulliSubset,
  CutQueryComplexity.StarContraction2022.Probability.bernoulliSubset_size_mass,
  CutQueryComplexity.StarContraction2022.Probability.condition_bernoulliSubset_size,
  CutQueryComplexity.StarContraction2022.Probability.bernoulliSubset_eq_sizeMixture,
  CutQueryComplexity.StarContraction2022.Probability.bernoulliSubset_ratio_mean_le,
  CutQueryComplexity.StarContraction2022.Probability.condition_bernoulliSubset_window,
  CutQueryComplexity.StarContraction2022.Probability.acceptedBernoulli_ratio_tail,
  CutQueryComplexity.StarContraction2022.Probability.binomialSize_inverse_succ_le,
  CutQueryComplexity.StarContraction2022.Probability.binomialSize_positiveInverse_le,
  CutQueryComplexity.StarContraction2022.Probability.bernoulliSubset_ratio_tenth_tail,
  CutQueryComplexity.GHReduction.independentSamples_length,
  CutQueryComplexity.GHReduction.mass_all_independentSamples,
  CutQueryComplexity.GHReduction.mass_all_independentSamples_le,
  CutQueryComplexity.GHReduction.guideSampleProgram_eval,
  CutQueryComplexity.GHReduction.guideSampleProgram_cost,
  CutQueryComplexity.GHReduction.guideSampleProgram_length,
  CutQueryComplexity.GHReduction.guideSampleProgram_miss_le,
  CutQueryComplexity.GHReduction.guideSampleProgram_coverage,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.source_cost,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.program_cost,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.program_sound,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.postprocess_good,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.solver_failure,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.program_failure,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.source_budget_le,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.program_cost_log,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.program_cost_high,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.source_budget_high,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.guardedProgram_cost,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.guardedProgram_sound,
  CutQueryComplexity.StarContraction2022.WeightedAdapter.guardedProgram_failure,
  CutQueryComplexity.GHReduction.mem_stShores,
  CutQueryComplexity.GHReduction.stShores_nonempty,
  CutQueryComplexity.GHReduction.stValue_nonneg,
  CutQueryComplexity.GHReduction.stValue_le,
  CutQueryComplexity.GHReduction.exists_stMinCut,
  CutQueryComplexity.GHReduction.stValue_eq_of_minCut,
  CutQueryComplexity.GHReduction.stMinCut_compl,
  CutQueryComplexity.GHReduction.stMinCut_inter,
  CutQueryComplexity.GHReduction.exists_canonicalSTCut,
  CutQueryComplexity.GHReduction.canonicalSTCut_unique,
  CutQueryComplexity.GHReduction.trace_uncross,
  CutQueryComplexity.GHReduction.exists_canonicalTraceCut,
  CutQueryComplexity.GHReduction.canonical_trace_subset,
  CutQueryComplexity.GHReduction.canonical_trace_unique,
  CutQueryComplexity.GHReduction.minTrace_compl,
  CutQueryComplexity.GHReduction.canonical_trace_disjoint,
  CutQueryComplexity.GHReduction.stValue_triangle,
  CutQueryComplexity.GHReduction.stValue_source_switch,
  CutQueryComplexity.StarContraction2022.Certificates.smallQuotientShore_cost,
  CutQueryComplexity.StarContraction2022.Certificates.smallQuotientShore_sound,
  CutQueryComplexity.StarContraction2022.Certificates.smallQuotient_budget,
  CutQueryComplexity.StarContraction2022.Certificates.smallQuotientShore_correct,
  CutQueryComplexity.ImplicitLP.GenericQuery.artificialCost_center,
  CutQueryComplexity.ImplicitLP.GenericQuery.repaired_update_constraint,
  CutQueryComplexity.ImplicitLP.GenericQuery.rounded_repair_hidden,
  CutQueryComplexity.ImplicitLP.GenericQuery.initialWeights_failure,
  CutQueryComplexity.GHReduction.pull_equiv_image,
  CutQueryComplexity.GHReduction.stMinCut_equiv_image,
  CutQueryComplexity.GHReduction.stMinCut_equiv_pull,
  CutQueryComplexity.GHReduction.canonicalSTCut_equiv_pull,
  CutQueryComplexity.GHReduction.canonicalSTProgram_correct,
  CutQueryComplexity.GHReduction.canonicalSTProgram_cost,
  CutQueryComplexity.StarContraction2022.Certificates.OriginalEdge.contract_graph,
  CutQueryComplexity.StarContraction2022.Certificates.ForestTrace.acyclic,
  CutQueryComplexity.StarContraction2022.Certificates.ForestTrace.contract_eq,
  CutQueryComplexity.StarContraction2022.Certificates.ForestTrace.card_edges,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.usedGraph_integral,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.usedGraph_contract,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.quotientGraph_subgraph,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.complete_certificate,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.edgeCount_le,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertAt_usedGraph,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertFirst_laminar,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertFirst_edgeCount,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualCrossQuery_eval,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertAt_subgraph,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.quotientGraph_edgeMass,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residual_unit,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.exhausted_original_edge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.listed_edge_exhausted,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertAt_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.inactive_closed_in_earlier,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.retire_sound,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.retire_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertAt_inactiveSound,
  CutQueryComplexity.GHReduction.OuterPivot.canonical_opposite_disjoint,
  CutQueryComplexity.GHReduction.OuterPivot.canonicalShore_opposite_card,
  CutQueryComplexity.GHReduction.OuterPivot.balanced_pair,
  CutQueryComplexity.GHReduction.OuterPivot.balancedTargets_double_count,
  CutQueryComplexity.GHReduction.OuterPivot.pivot_balance,
  CutQueryComplexity.ImplicitLP.GenericQuery.upSchedule_licensed,
  CutQueryComplexity.ImplicitLP.GenericQuery.downSchedule_licensed,
  CutQueryComplexity.ImplicitLP.GenericQuery.run_failure_of_per_call,
  CutQueryComplexity.ImplicitLP.GenericQuery.stepSize_spec,
  CutQueryComplexity.ImplicitLP.GenericQuery.downSchedule_public,
  CutQueryComplexity.ImplicitLP.GenericQuery.upSchedule_public,
  CutQueryComplexity.ImplicitLP.GenericQuery.phaseSteps_bound,
  CutQueryComplexity.ImplicitLP.GenericQuery.downSchedule_reaches,
  CutQueryComplexity.ImplicitLP.GenericQuery.initialPhase_licensed,
  CutQueryComplexity.ImplicitLP.GenericQuery.initialPhase_switch,
  CutQueryComplexity.ImplicitLP.GenericQuery.truePhase_licensed,
  CutQueryComplexity.ImplicitLP.GenericQuery.public_final_accuracy,
  CutQueryComplexity.ImplicitLP.GenericQuery.phaseSteps_public_bound,
  CutQueryComplexity.GHReduction.liftDTree_run,
  CutQueryComplexity.GHReduction.liftDTree_cost_le,
  CutQueryComplexity.GHReduction.queryMap_run,
  CutQueryComplexity.GHReduction.sequenceList_cost_le,
  CutQueryComplexity.GHReduction.bitClass_union,
  CutQueryComplexity.GHReduction.bitClass_sdiff,
  CutQueryComplexity.GHReduction.isolatingCells_disjoint,
  CutQueryComplexity.GHReduction.isolatingCells_size,
  CutQueryComplexity.GHReduction.bitSide_min,
  CutQueryComplexity.GHReduction.terminal_mem_cell,
  CutQueryComplexity.GHReduction.isolatingCell_trace,
  CutQueryComplexity.GHReduction.canonical_iso_subset_cell,
  CutQueryComplexity.GHReduction.isolatingCell_proper,
  CutQueryComplexity.ImplicitLP.GenericQuery.artificialCost_bound,
  CutQueryComplexity.ImplicitLP.GenericQuery.batchGood_changeCost,
  CutQueryComplexity.ImplicitLP.GenericQuery.frozenRun_failure,
  CutQueryComplexity.ImplicitLP.GenericQuery.frozenRun_endpoint,
  CutQueryComplexity.ImplicitLP.GenericQuery.initializedRun_failure,
  CutQueryComplexity.ImplicitLP.GenericQuery.pathSolver_failure,
  CutQueryComplexity.ImplicitLP.GenericQuery.pathSolver_cost,
  CutQueryComplexity.ImplicitLP.GenericQuery.solverFailure_of_per_call,
  CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_none,
  CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_some,
  CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_some_tendsto,
  CutQueryComplexity.StarContraction2022.Recovery.rowSamples_marginal,
  CutQueryComplexity.StarContraction2022.Recovery.rowSamples_unfinished_le,
  CutQueryComplexity.StarContraction2022.Recovery.rowSamples_total_expected_counts,
  CutQueryComplexity.StarContraction2022.Recovery.sampleColumns_count_law,
  CutQueryComplexity.StarContraction2022.Recovery.columnProposal_expMoment,
  CutQueryComplexity.StarContraction2022.Recovery.columnProposal_lower,
  CutQueryComplexity.StarContraction2022.Recovery.columnProposal_upper,
  CutQueryComplexity.StarContraction2022.Recovery.bucketAccept_failure_le_half,
  CutQueryComplexity.StarContraction2022.Recovery.rowSamples_expected_rounds,
  CutQueryComplexity.StarContraction2022.Recovery.validateRowCounts_sound,
  CutQueryComplexity.StarContraction2022.Recovery.maskedMatrix_bilinear,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_every_oracle,
  CutQueryComplexity.StarContraction2022.Recovery.bucket_row_reject_le_half,
  CutQueryComplexity.StarContraction2022.Recovery.decoderWeight_affine,
  CutQueryComplexity.StarContraction2022.Recovery.decoderWeight_round_bound,
  CutQueryComplexity.StarContraction2022.Recovery.bucketRoundWith_honest_run,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_progress,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_completed_correct,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_proposal_law,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_completion_tail,
  CutQueryComplexity.StarContraction2022.Recovery.sparseRawBudget_le_scaled_weight,
  CutQueryComplexity.StarContraction2022.Recovery.honestRound_amortized,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_amortized,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_expected_le_charges,
  CutQueryComplexity.StarContraction2022.Recovery.bucket_charges_le_bound,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_expected_bound,
  CutQueryComplexity.StarContraction2022.Recovery.sampleColumns_apply,
  CutQueryComplexity.StarContraction2022.Recovery.sampleColumns_filter,
  CutQueryComplexity.StarContraction2022.Recovery.columnProposal_restrict_apply,
  CutQueryComplexity.StarContraction2022.Contraction.minimum_nontrivial,
  CutQueryComplexity.StarContraction2022.Contraction.centerBits_subset_law,
  CutQueryComplexity.StarContraction2022.Contraction.sampleCenters_restriction,
  CutQueryComplexity.StarContraction2022.Contraction.sampleCenters_ratio_mean_le,
  CutQueryComplexity.StarContraction2022.Contraction.sampleCenters_ratio_tenth_tail,
  CutQueryComplexity.StarContraction2022.Contraction.minimum_half_crossing,
  CutQueryComplexity.StarContraction2022.Contraction.minimum_fractions,
  CutQueryComplexity.StarContraction2022.Contraction.centerStatistics_eval,
  CutQueryComplexity.StarContraction2022.Contraction.centerStatistics_cost,
  CutQueryComplexity.StarContraction2022.Contraction.badSet_split,
  CutQueryComplexity.GHReduction.levelBits_card,
  CutQueryComplexity.GHReduction.levelSample_subset,
  CutQueryComplexity.GHReduction.source_mem_levelSample,
  CutQueryComplexity.GHReduction.levelSample_nested,
  CutQueryComplexity.GHReduction.levelSample_zero,
  CutQueryComplexity.GHReduction.mass_survives_set,
  CutQueryComplexity.GHReduction.mass_survives,
  CutQueryComplexity.GHReduction.mass_survives_pair,
  CutQueryComplexity.GHReduction.uniqueSurvivor_mass_bound,
  CutQueryComplexity.GHReduction.uniqueSurvivor_trace,
  CutQueryComplexity.ImplicitLP.GenericQuery.calibratedRegime,
  CutQueryComplexity.ImplicitLP.GenericQuery.calibrated_failure,
  CutQueryComplexity.ImplicitLP.GenericQuery.initial_numerical_floor,
  CutQueryComplexity.ImplicitLP.GenericQuery.solve_failure,
  CutQueryComplexity.ImplicitLP.GenericQuery.solve_success,
  CutQueryComplexity.ImplicitLP.GenericQuery.solve_cost,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.sample,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_inventory,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.step_exposed_card,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_stopped,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_closed_caught,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_closed_successor,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_closed_two_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_rooted,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.run_of_stopped,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.run_reached_mono,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.run_exposed_mono,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.run_eq_of_agree,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.condition_cylinder_coordinate,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.history_eq_iff,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.history_unexposed_mass,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.history_caught_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.selectedGraph_component_sameSide,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.componentCount_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.publicQuotient_respects,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.publicQuotient_preserves_minimum,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualMatrix_entry,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualMatrix_bilinear,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualMatrix_row,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualBilinearCall_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualBilinearCall_run,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.simulateResidual_run,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.simulateResidual_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.simulateResidual_expected,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.simulateResidual_every_oracle,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualDecode_correct,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualDecode_cost_bound,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowDegreeResidual_correct,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowDegreeResidual_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualDegrees_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.checkedLowDegreeResidual_sound,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.checkedLowDegreeResidual_correct,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.checkedLowDegreeResidual_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.checkedLowDegreeResidual_cost_bound,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residual_row_count,
  CutQueryComplexity.GHReduction.setCutMap_surjective,
  CutQueryComplexity.GHReduction.setCutVertex_card_le,
  CutQueryComplexity.GHReduction.setCutShore_source,
  CutQueryComplexity.GHReduction.setCutShore_sink,
  CutQueryComplexity.GHReduction.pull_setCutShore,
  CutQueryComplexity.GHReduction.trace_feasible,
  CutQueryComplexity.GHReduction.setCutPull_trace,
  CutQueryComplexity.GHReduction.minTrace_to_setCut,
  CutQueryComplexity.GHReduction.canonical_setCut_pull,
  CutQueryComplexity.GHReduction.setCutProgram_correct,
  CutQueryComplexity.StarContraction2022.Recovery.graphMatrix_bilinear,
  CutQueryComplexity.StarContraction2022.Recovery.validatedOriginalBilinearCall_honest,
  CutQueryComplexity.StarContraction2022.Recovery.validatedOriginalBilinearCall_reject,
  CutQueryComplexity.StarContraction2022.Recovery.simulateOriginal_run,
  CutQueryComplexity.StarContraction2022.Recovery.simulateOriginal_expected,
  CutQueryComplexity.StarContraction2022.Recovery.simulateOriginal_every_oracle,
  CutQueryComplexity.StarContraction2022.Recovery.rankSearch_correct,
  CutQueryComplexity.StarContraction2022.Recovery.rankSearch_every_oracle,
  CutQueryComplexity.StarContraction2022.Recovery.sum_bucketNumeric_le,
  CutQueryComplexity.StarContraction2022.Recovery.recoveryBucketCount_bound,
  CutQueryComplexity.StarContraction2022.Recovery.tinyRows_original_budget,
  CutQueryComplexity.StarContraction2022.Recovery.semanticRank_injective,
  CutQueryComplexity.StarContraction2022.Recovery.rankVertex_bijective,
  CutQueryComplexity.StarContraction2022.Recovery.drawRemaining_uniform,
  CutQueryComplexity.StarContraction2022.Recovery.learnRanks_every_oracle,
  CutQueryComplexity.StarContraction2022.Recovery.liftRows_run,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_every_oracle,
  CutQueryComplexity.StarContraction2022.Recovery.simulateOriginal_eval,
  CutQueryComplexity.StarContraction2022.Recovery.uniformSubset_step,
  CutQueryComplexity.StarContraction2022.Recovery.learnRanks_uniform,
  CutQueryComplexity.StarContraction2022.Recovery.columnProposal_restriction,
  CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_conditioned_real,
  CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_conditioned_bad_le,
  CutQueryComplexity.StarContraction2022.Recovery.firstSuccess_conditioned_expect_le,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_learned_law,
  CutQueryComplexity.StarContraction2022.Recovery.bucketRow_window_supported,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_row_ratio_tail,
  CutQueryComplexity.StarContraction2022.Recovery.learnBucketRounds_row_ratio_mean,
  CutQueryComplexity.StarContraction2022.Recovery.learnRanks_row_ratio_tail,
  CutQueryComplexity.StarContraction2022.Recovery.learnRanks_row_ratio_mean,
  CutQueryComplexity.StarContraction2022.Recovery.degreeBucket_cover,
  CutQueryComplexity.StarContraction2022.Recovery.degreeBucket_card_sum,
  CutQueryComplexity.StarContraction2022.Recovery.degreeBucket_numeric_sum,
  CutQueryComplexity.StarContraction2022.Recovery.recoverBuckets_learned_law,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRankRows_learned_law,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_invariant,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_true_neighbors,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_bucket_learned_law,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_rank_learned_law,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_row_ratio_tail,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_row_ratio_mean,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_unfinished_cost,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_expected_bound,
  CutQueryComplexity.StarContraction2022.Recovery.recoverRounds_original_expected_bound,
  CutQueryComplexity.ImplicitLP.GenericQuery.PublicHyp.height_inputs,
  CutQueryComplexity.ImplicitLP.GenericQuery.PublicHyp.logHeight_bounds,
  CutQueryComplexity.ImplicitLP.GenericQuery.publicLogSize_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.publicEnvelope_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.publicDelta_inv_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.publicTolerance_inv_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.base_scalar_envelopes,
  CutQueryComplexity.StarContraction2022.Certificates.Closed.sup_edge,
  CutQueryComplexity.StarContraction2022.Certificates.residualForestChain_of_closed,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residual_contract,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.complete_of_residualClosed,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.certificate_of_retired,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.liveBlocks_card_mono,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.livePotential_le,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.liveBlocks_card_mono_of,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.liveBlocks_card_lt_of_merge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.positive_endpoints_active,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertAt_livePotential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.retire_livePotential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertBatch_complete,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertBatch_laminar,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertBatch_edgeCount,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertStarBatch_complete,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertBatch_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertBatch_livePotential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertStarBatch_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.tableEdges_star,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.tableEdges_length,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.assembleNeighbors_honest,
  CutQueryComplexity.StarContraction2022.Certificates.componentBits_two,
  CutQueryComplexity.StarContraction2022.Certificates.componentColor_constant,
  CutQueryComplexity.StarContraction2022.Certificates.componentColor_red_blue,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.favorableRepresentatives_expect,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.assemble_favorable_expect,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteProgress.steps_active_back,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteProgress.steps_tail_le_active,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteProgress.steps_potential_tail,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteProgress.steps_weighted_tail,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteProgress.steps_potential_visits,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteProgress.activeVisits_bound,
  CutQueryComplexity.StarContraction2022.Certificates.roundPadding_envelope,
  CutQueryComplexity.StarContraction2022.Certificates.phase_denominator,
  CutQueryComplexity.StarContraction2022.Certificates.parallel_power_logs,
  CutQueryComplexity.StarContraction2022.Certificates.phase_denominator_of_guard,
  CutQueryComplexity.StarContraction2022.Certificates.phase_denominator_slots,
  CutQueryComplexity.StarContraction2022.Certificates.parallel_guard_log_reserve,
  CutQueryComplexity.StarContraction2022.Certificates.geometric_phase_charge,
  CutQueryComplexity.StarContraction2022.Certificates.parallelRowWeight_affine,
  CutQueryComplexity.StarContraction2022.Certificates.parallelRowWeight_sum,
  CutQueryComplexity.StarContraction2022.Certificates.parallelBucketWeight_sum,
  CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_eval,
  CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_same_clock,
  CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_every_oracle,
  CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_abort_le,
  CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_bad_le,
  CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_failure_le,
  CutQueryComplexity.StarContraction2022.Recovery.hundredClock_pays,
  CutQueryComplexity.StarContraction2022.Recovery.cappedBucketTree_every_oracle,
  CutQueryComplexity.StarContraction2022.Recovery.cappedBucketTree_same_clock,
  CutQueryComplexity.StarContraction2022.Recovery.cappedBucketTree_true_neighbors,
  CutQueryComplexity.StarContraction2022.Recovery.bucketTree_every_oracle,
  CutQueryComplexity.StarContraction2022.Recovery.bucketTree_abort_le,
  CutQueryComplexity.StarContraction2022.Recovery.bucketTree_true_neighbors,
  CutQueryComplexity.StarContraction2022.Recovery.bucketTree_bad_le,
  CutQueryComplexity.StarContraction2022.Recovery.recoverTree_every_oracle,
  CutQueryComplexity.StarContraction2022.Recovery.recoverClock_pays,
  CutQueryComplexity.StarContraction2022.Recovery.recoverTree_unfinished_cost,
  CutQueryComplexity.StarContraction2022.Recovery.recoverTree_same_clock,
  CutQueryComplexity.StarContraction2022.Recovery.recoverTree_abort_le,
  CutQueryComplexity.StarContraction2022.Recovery.recoverTree_true_neighbors,
  CutQueryComplexity.StarContraction2022.Recovery.recoverTree_bad_le,
  CutQueryComplexity.StarContraction2022.Recovery.finiteCompleteCap_expect_le,
  CutQueryComplexity.StarContraction2022.Recovery.recoverTree_row_ratio_tail,
  CutQueryComplexity.StarContraction2022.Recovery.recoverTree_row_ratio_mean,
  CutQueryComplexity.ImplicitLP.GenericQuery.publicLewis_count_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.newton_scalar_envelopes,
  CutQueryComplexity.ImplicitLP.GenericQuery.newton_iteration_bits_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.newton_deterministic_budget_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.publicSupport_bits_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.publicSupport_budget_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.bernoulli_power_moment,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.bernoulli_expMoment,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.bernoulli_expMoment_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.bernoulli_half_lower_tail,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.bernoulli_triple_upper_tail,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.bad_row_mass_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.expect_badRows_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.bad_exponential_debit,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.bad_guard_failure_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.center_guard_failure_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.ratio_sum_mean_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.ratio_sum_failure_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.ratio_max_failure_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.goodCenters_failure_le,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.goodCenters_success,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.inputRatio_eq,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.minimum_center_success,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.centerStatistics_input_eval,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.measuredBadSet_eval,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.checkedCenterStatistics_eval,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.centersProgram_eval,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.centersProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.SparseCenters.centersProgram_minimum_success,
  CutQueryComplexity.DeterministicAPMCExpansion.additiveExpands_of_small,
  CutQueryComplexity.DeterministicAPMCExpansion.additive_small_cut_side,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.mass_sum_history,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.history_inter_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.history_pattern_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.history_caught_count_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.caughtAt_history_determined,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.run_caught_eq_count,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.run_twice_limit_stopped,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.caughtAt_conditional_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.run_caught_tail,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_closed_size_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.closedCoefficient_succ_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.closedCoefficient_half,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.sum_closedCoefficient_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_limit_eq,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_full_size_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_small_closed_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.calibratedStepSize_inv_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.calibratedSwitch_envelope,
  CutQueryComplexity.ImplicitLP.GenericQuery.calibratedDownSteps_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.calibratedUpSteps_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.publicFinalCount_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.publicCallCount_envelope,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.partVertex_card,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.partNetwork_card,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.liftShore_compl,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.partGraph_unweighted,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.partGraph_cut_three,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.isSTMinCut_lift,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.isSTMinCut_restrict,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeQuery_run,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeQuery_eval,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeQuery_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeProgram_eval,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeProgram_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeProgram_cost_le,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.row_moment_failure_bound,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.recoveredRatio_mean,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.recoveredRatio_tail,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.recoverTree_good_rows_failure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.recoverTree_outside_success_half,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.crossingRatio_mapped,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.red_blue_disjoint,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.blueProbe_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.blueProbe_positive_iff,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorRows_eval,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorRows_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.positiveColorRows_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorRows_favorable_expect,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowColorRows_positive,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowColorRows_degree,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.highColorRows_degree,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.highColorRows_disjoint,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.low_highColorRows_disjoint,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorRows_bucket_cover,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorBucket_disjoint,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorBucket_union,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorBucket_card_sum,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorBucket_card_sum_le,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorBucket_slots_le,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorBucket_rowWeight_sum,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.learnedNext_residual_some,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.learnedNext_residual_complete,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowRowUpdate_every_oracle,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowRowUpdate_empty_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowRowUpdate_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowRowUpdate_cost_bound,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowRowUpdateBudget_le,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorLowUpdate_eval,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.colorLowUpdate_honest,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_flow_drain,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_size_boundary,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_boundary_strict,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_large_remainder,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.prune_induced_expansion,
  CutQueryComplexity.GHReduction.bitSeparatorProgram_correct,
  CutQueryComplexity.GHReduction.bitSeparatorProgram_cost,
  CutQueryComplexity.GHReduction.isolatingLocalProgram_cost,
  CutQueryComplexity.GHReduction.isolatingLocalProgram_correct,
  CutQueryComplexity.GHReduction.isolatingLocal_totalCharge,
  CutQueryComplexity.GHReduction.isolatingProgram_correct,
  CutQueryComplexity.GHReduction.isolatingProgram_cost,
  CutQueryComplexity.GHReduction.isolatingLocal_totalCharge_scaled,
  CutQueryComplexity.GHReduction.isolatingProgram_cost_scaled,
  CutQueryComplexity.GHReduction.isolatingValuesProgram_correct,
  CutQueryComplexity.GHReduction.isolatingValuesProgram_cost,
  CutQueryComplexity.GHReduction.isolatingTree_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.historyGraph_append_cut,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.walk_row_sum,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.walk_column_sum,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pruning_finish_quarter,
  CutQueryComplexity.GHReduction.cut_nat_of_integral,
  CutQueryComplexity.GHReduction.stValue_nat_of_integral,
  CutQueryComplexity.GHReduction.sourceValueNat_eq,
  CutQueryComplexity.GHReduction.sourceValueNat_le,
  CutQueryComplexity.GHReduction.selectVertex_mem,
  CutQueryComplexity.GHReduction.selectVertex_max_of_range,
  CutQueryComplexity.GHReduction.maximizer_high_lift,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.two_mul_pairCount,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.pairCount_eq_half,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.pairCount_eq_shore,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.markedGraph_cut,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.matching_cut_split,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.roundGraph_degree,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.roundDegree_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.roundGraph_sum_degrees,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.roundEdgeCount_zero_of_projected_loops,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_w,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_degree,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.degreeTable_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.sum_degrees,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.cut_le_degree_sum,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.edgeCount_le_budget,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.history_cut_split,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.history_cut_split_reverse,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_append_w,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_integral,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.edgeCount_zero_of_no_fake,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges.fakeGraph_zero_of_no_fake,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.residualNeighbor_positive,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.advanceVertex_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.vertexProbe_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.vertexProbe_zero,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.vertexProbe_positive,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanVertices_budget,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanVertices_forests,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanVertices_inactive_mono,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanVertices_cost_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.activeScan_cost_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.blockScan_cost_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanBlocks_forests,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanBlocks_inactive,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanBlocks_cost_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanBlocks_inactiveSound,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanBlocks_labels_sublist,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanBlocks_good,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representativeScan_cost_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representativeScan_good,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representativeScan_covers_live,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representativeScan_distinct_labels,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representativeScan_separated,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanVertices_inactiveSound,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanVertices_result,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanVertices_none_certificate,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanVertices_livePotential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.finishStep_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.finishStep_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.finishRounds_correct,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.finishRounds_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.finishRounds_cost_live,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.finishProgram_correct,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.finishProgram_cost_at_scale,
  CutQueryComplexity.ImplicitLP.GenericQuery.calibrated_spectral_log_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.calibrated_spectral_budget_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.calibrated_primitive_budgets,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.twoStarQuery_eval,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.residual_rectangle_query,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.internal_residual_pair_bound,
  CutQueryComplexity.StarContraction2022.Quantum.minimumLetter_le,
  CutQueryComplexity.StarContraction2022.Quantum.minimumLetter_attained,
  CutQueryComplexity.StarContraction2022.Quantum.minimumReadAll_prob,
  CutQueryComplexity.StarContraction2022.Quantum.minimumLetter_counts_nonempty,
  CutQueryComplexity.StarContraction2022.Quantum.minimumLetter_qQuery_le,
  CutQueryComplexity.StarContraction2022.Quantum.exists_minimumLetter_base,
  CutQueryComplexity.StarContraction2022.Quantum.exists_minimumLetter_repeated,
  CutQueryComplexity.StarContraction2022.Quantum.exists_minimumDegree_algorithm,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeAlg_correct,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeRoutine_len,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeRoutine_state,
  CutQueryComplexity.StarContraction2022.Quantum.unitCapacity_singleton_le,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeValue_le,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeValue_attained,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeValue_lt,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeValue_zero,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeValue_one,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeValue_eq_zero_of_zero_degree,
  CutQueryComplexity.StarContraction2022.Quantum.simpleCapacity_singleton_degree,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeValue_eq_minDegree,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeAlg_honest,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeAlg_simple,
  CutQueryComplexity.StarContraction2022.Quantum.exists_quantum_minimumDegree_value,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeRepetitions_pos,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeError_six_mul,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeConfidence_error,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeTolerance_correct,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeTolerance_cost_le,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeTolerance_cost_le_sqrt,
  CutQueryComplexity.ImplicitLP.GenericQuery.queryCap_logb_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.leadingConstant_pos,
  CutQueryComplexity.ImplicitLP.GenericQuery.queryCap_le,
  CutQueryComplexity.ImplicitLP.GenericQuery.solve_query_bound,
  CutQueryComplexity.ImplicitLP.GenericQuery.incidenceLP_query_endpoint,
  CutQueryComplexity.ImplicitLP.GenericQuery.polynomial_input_query_bound,
  CutQueryComplexity.StarContraction2022.Certificates.chargeRound_eval,
  CutQueryComplexity.StarContraction2022.Certificates.chargeRound_positive,
  CutQueryComplexity.StarContraction2022.Certificates.chargeRound_expectedQueries,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteQueryFuel.exhausted_cost,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteQueryFuel.capped_every_oracle,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteQueryFuel.capped_eval,
  CutQueryComplexity.StarContraction2022.Certificates.FiniteQueryFuel.capped_abort,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colors,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colors_flipRow,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colors_opposite_law,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colors_opposite_mean_le,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colors_opposite_tenth_tail,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.fairSubset_low_tail,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colors_opposite_low_tail,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.mul_geometric_le_hundredth,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.target_survives_omission,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.GoodRows.omit,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.oppositeStatistics_eval,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.oppositeStatistics_cost,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colored_mean_le,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colored_row_tail,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colored_sum_tail,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.coloredRows_good_failure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.expect_extraOmissions_le,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.extraOmissions_failure_le,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.coloredRows_nonzero_degree,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.coloredRows_zero_real_le,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.colored_stage_failure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.center_goodRows,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.center_lowSources_subset_bad,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.center_lowSources_inside_card_le,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.onRows_rowFraction,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.onRows_good,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.center_subtype_goodRows,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.center_subtype_lowSources_card_le,
  CutQueryComplexity.GHReduction.GuideTree.source_mem,
  CutQueryComplexity.GHReduction.GuideTree.realVertices_card,
  CutQueryComplexity.GHReduction.GuideTree.real_card_le,
  CutQueryComplexity.GHReduction.GuideTree.graphGroup_card,
  CutQueryComplexity.GHReduction.GuideTree.graphGroup_subset,
  CutQueryComplexity.GHReduction.GuideTree.graphGroup_disjoint,
  CutQueryComplexity.GHReduction.GuideTree.centroid_spec,
  CutQueryComplexity.GHReduction.GuideTree.part_nonempty,
  CutQueryComplexity.GHReduction.GuideTree.part_subset,
  CutQueryComplexity.GHReduction.GuideTree.parts_disjoint,
  CutQueryComplexity.GHReduction.GuideTree.graphGroups_disjoint,
  CutQueryComplexity.GHReduction.GuideTree.part_half,
  CutQueryComplexity.GHReduction.GuideTree.graphGroup_half,
  CutQueryComplexity.GHReduction.GuideTree.parts_cover_except_centroid,
  CutQueryComplexity.GHReduction.GuideTree.real_card_le_one_add_groups,
  CutQueryComplexity.GHReduction.GuideTree.two_le_parts,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.twoStar_source_cut,
  CutQueryComplexity.StarContraction2022.Certificates.NeighborCollection.complete,
  CutQueryComplexity.StarContraction2022.Certificates.NeighborCollection.none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.NeighborCollection.expected_le_sum,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.learnedSetNext_present,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.highBucketNeighbors_every_oracle,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.highBucketNeighbors_empty,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.selectedBucketNeighbors_honest_run,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.selectedBucketNeighbors_complete,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.selectedBucketNeighbors_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.selectedBucketNeighbors_expected,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.highBucketNeighbors_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.highBucketNeighbors_complete,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.highBucketNeighbors_expected,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowBucketNeighbors_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.lowBucketNeighbors_complete,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.bucketCall_complete,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.bucketCall_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.jointBucketNeighbors_complete,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.jointBucketNeighbors_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.jointBucketNeighbors_expected_le_sum,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.mixedUpdate_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representatives_card_le_potential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.mixedUpdate_potential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.fairBatch_eval,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.fairBatch_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.fairBatch_potential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertFirst_reachable,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertBatch_reachable,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.assembleNeighbors_monotone,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.mixedUpdate_liveBlocks_mono,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.fairBatch_liveBlocks_mono,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.fairBatch_success,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.insertBatch_failed,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.mixedUpdate_failed,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.fairBatch_failed,
  CutQueryComplexity.GHReduction.path_crossing,
  CutQueryComplexity.GHReduction.pathEdges_nonempty,
  CutQueryComplexity.GHReduction.pathShore_separates,
  CutQueryComplexity.GHReduction.tree_weight_le_crossing_cut,
  CutQueryComplexity.GHReduction.pathShore_minimum_of_bottleneck,
  CutQueryComplexity.GHReduction.cutTree_allPairs,
  CutQueryComplexity.GHReduction.minimumPathEdge_spec,
  CutQueryComplexity.GHReduction.cutTreeAnswer_correct,
  CutQueryComplexity.GHReduction.cutTreeAnswerProgram_run,
  CutQueryComplexity.GHReduction.cutTreeAnswerProgram_correct,
  CutQueryComplexity.GHReduction.GuideTree.retain_respects,
  CutQueryComplexity.GHReduction.separatorPart_excludes_centroid,
  CutQueryComplexity.GHReduction.separatorPart_isCentroidBranch,
  CutQueryComplexity.GHReduction.mem_collapseBranch,
  CutQueryComplexity.GHReduction.collapseBranch_crossSet,
  CutQueryComplexity.GHReduction.collapseBranch_crossing_le,
  CutQueryComplexity.GHReduction.collapseBranch_crossing_decreases,
  CutQueryComplexity.GHReduction.GuideTree.retain_branch_respects,
  CutQueryComplexity.GHReduction.addProxyTree_crossSet,
  CutQueryComplexity.GHReduction.GuideTree.addProxy_real_card,
  CutQueryComplexity.GHReduction.GuideTree.addProxy_source,
  CutQueryComplexity.GHReduction.GuideTree.addProxy_respects,
  CutQueryComplexity.StarContraction2022.Quantum.FinitePolicy.sampleFin_marginal,
  CutQueryComplexity.StarContraction2022.Quantum.FinitePolicy.sampleFamily_marginal,
  CutQueryComplexity.StarContraction2022.Quantum.FinitePolicy.sampleFamily_map_coordinate,
  CutQueryComplexity.StarContraction2022.Quantum.policies_zero,
  CutQueryComplexity.StarContraction2022.Quantum.policies_run,
  CutQueryComplexity.StarContraction2022.Quantum.policies_output,
  CutQueryComplexity.StarContraction2022.Quantum.policies_count,
  CutQueryComplexity.StarContraction2022.Quantum.policies_run_cost_le,
  CutQueryComplexity.StarContraction2022.Quantum.policies_empty_index_cost,
  CutQueryComplexity.GHReduction.mem_frontierProxies,
  CutQueryComplexity.GHReduction.parent_ne_child,
  CutQueryComplexity.GHReduction.frontierVertex_card,
  CutQueryComplexity.GHReduction.sum_fiber_card,
  CutQueryComplexity.GHReduction.sum_frontierProxies_card,
  CutQueryComplexity.GHReduction.frontier_vertex_sum,
  CutQueryComplexity.GHReduction.frontier_vertex_sum_le,
  CutQueryComplexity.GHReduction.frontier_fiber_nonempty,
  CutQueryComplexity.GHReduction.frontierVertex_card_le,
  CutQueryComplexity.GHReduction.frontierVertex_card_bounds,
  CutQueryComplexity.GHReduction.frontier_vertex_active_sum_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_touchesOld,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.advance,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.finish_complete,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.componentCount_le_closed,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.finish_volume_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.processHistory_eq_iff,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.condition_cylinder_freeze,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.processHistory_phase_mass,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.phase_clean_iff_contact_false,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.finish_smallCount,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.smallAt_conditional_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.expect_smallCount_le,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.componentCount_le_small_add,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.smallCount_tail,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.componentCount_tail,
  CutQueryComplexity.StarContraction2022.Contraction.TwoOut.componentCount_tail_of_forty,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representativeScan_vertices_card,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representativeScan_vertices_bounds,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representativeScan_for_batch,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanFairRound_eval,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.scanFairRound_potential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingRound_eval,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingRound_success,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingRound_potential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingStep_absorbs,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingStep_positive,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingStep_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingStep_potential,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingIterations_eval,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingIterations_potential_visits,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingIterations_visits_le,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingRound_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingStep_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingStep_active_back,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingIterations_active_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingIterations_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingIterations_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingPhase_success,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingPhase_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingRound_failed,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingStep_failed,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingIterations_absorbs,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingIterations_failed,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingPhase_failed,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.residualNeighbor_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.residualNeighbor_cost,
  CutQueryComplexity.GHReduction.CandidateExact.valid,
  CutQueryComplexity.GHReduction.CandidateValid.upper,
  CutQueryComplexity.GHReduction.CandidateExact.value_eq,
  CutQueryComplexity.GHReduction.chooseCandidate_mem,
  CutQueryComplexity.GHReduction.chooseCandidate_valid,
  CutQueryComplexity.GHReduction.valid_le_exact_is_exact,
  CutQueryComplexity.GHReduction.chooseCandidate_exact_left,
  CutQueryComplexity.GHReduction.chooseCandidate_exact_right,
  CutQueryComplexity.GHReduction.evaluateCandidate_valid,
  CutQueryComplexity.GHReduction.evaluateCandidate_cost,
  CutQueryComplexity.GHReduction.pairCandidateProgram_valid,
  CutQueryComplexity.GHReduction.pairCandidateProgram_exact,
  CutQueryComplexity.GHReduction.pairCandidateProgram_cost,
  CutQueryComplexity.StarContraction2022.Quantum.RandomizedCompiler.pmf_toReal_sum,
  CutQueryComplexity.StarContraction2022.Quantum.RandomizedCompiler.pmf_map_toReal,
  CutQueryComplexity.StarContraction2022.Quantum.RandomizedCompiler.pmf_event_toReal,
  CutQueryComplexity.StarContraction2022.Quantum.quantum_prob_eq_ite_of_exact,
  CutQueryComplexity.StarContraction2022.Quantum.policyAlg_exact,
  CutQueryComplexity.StarContraction2022.Quantum.policyAlg_prob,
  CutQueryComplexity.StarContraction2022.Quantum.exists_randomizedCompiler,
  CutQueryComplexity.StarContraction2022.Quantum.randomizedAlg_prob,
  CutQueryComplexity.StarContraction2022.Quantum.randomizedRoutine_len,
  CutQueryComplexity.StarContraction2022.Quantum.randomizedRoutine_state,
  CutQueryComplexity.StarContraction2022.Quantum.randomizedAlg_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.randomizedAlg_solves_iff,
  CutQueryComplexity.StarContraction2022.Quantum.randomizedAlg_zero_prob,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.treeProg_run,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.neighborProg_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.neighborProg_cost,
  CutQueryComplexity.GHReduction.refinementCell_eq_none,
  CutQueryComplexity.GHReduction.refinementCell_eq_some,
  CutQueryComplexity.GHReduction.refinedBlockMap_eq_old,
  CutQueryComplexity.GHReduction.refinedBlockMap_eq_residual,
  CutQueryComplexity.GHReduction.refinedBlockMap_eq_child,
  CutQueryComplexity.GHReduction.refinedBlockMap_old_fiber,
  CutQueryComplexity.GHReduction.refinedBlockMap_residual_fiber,
  CutQueryComplexity.GHReduction.refinedBlockMap_child_fiber,
  CutQueryComplexity.GHReduction.refinedBlockParent_map,
  CutQueryComplexity.GHReduction.refinedBlockMap_fiber_subset,
  CutQueryComplexity.GHReduction.refinedBlockMap_pull_parent_fiber,
  CutQueryComplexity.GHReduction.refinedBlockMap_surjective,
  CutQueryComplexity.GHReduction.refinedBlockMap_surjective_of_terminals,
  CutQueryComplexity.GHReduction.refinedBlock_card,
  CutQueryComplexity.GHReduction.refinedBlock_card_le,
  CutQueryComplexity.GHReduction.refinedBlock_growth_le,
  CutQueryComplexity.GHReduction.refinedBlockMap_residual_partition_card,
  CutQueryComplexity.GHReduction.refinedBlockMap_partition_card,
  CutQueryComplexity.GHReduction.filterCandidate_valid,
  CutQueryComplexity.GHReduction.filterCandidate_of_valid,
  CutQueryComplexity.GHReduction.pullCandidate_valid,
  CutQueryComplexity.GHReduction.pullCandidate_of_valid,
  CutQueryComplexity.GHReduction.bestCandidates_valid,
  CutQueryComplexity.GHReduction.bestCandidates_exact,
  CutQueryComplexity.GHReduction.chooseCandidate_le_left,
  CutQueryComplexity.GHReduction.chooseCandidate_le_right,
  CutQueryComplexity.GHReduction.bestCandidates_le,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.mixedBucketCharge_nonneg,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.bucketCall_expected,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.mixedUpdate_expected,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.fairBatch_expected,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.fairBatch_retirementCredit,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.representativeScan_retirement_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingRound_retirement_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingStep_scale_honest,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingStep_retirement_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingIterations_retirement_charge,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.halvingPhase_retirement_charge,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.outside_source_target_card,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.outsideRecoveryProgram_eval,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.outsideRecoveryProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.outsideNeighbors_map,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.outside_fullDegrees,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.outside_baseRatio,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.outside_base_good,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.outside_degree_5000,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.outsideRecoveryProgram_center_success,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_complete,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_level_rise,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_reachable,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsProg_out_zero,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsTree_eval,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfsTree_cost,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.direction_card_le,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.sources_union,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.source_target_disjoint,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.rawDirections_eval,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.oppositeStatisticsOn_eval,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.learnSubgraphProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.learnSubgraphProgram_eval,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.oppositeStatisticsOn_unit,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.measuredExtraOmissions_unit,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.pair_expect_fst,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.pair_expect_snd,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.pair_mass_fst,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.pair_mass_snd,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.twoDirections_abort,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.pairBaseRatio_sum,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.pairRatio_mean,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.pairRatio_tail,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.rawDirections_ratio_failure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.twoDirections_quality_failure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.color_guard_failure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.recoverAfterColor_quality_failure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.learnSubgraphProgram_quality_failure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.twoDirections_supported,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.transcript_supported_rows,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.transcript_pairRatio,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.transcript_quality_goodRows,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.learnSubgraphProgram_output_spec,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.learnSubgraphProgram_failure,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.learnSubgraphProgram_success_half,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.directionNeighbors_map,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.direction_fullDegrees,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.retained_direction_degree,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.direction_baseRatio,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.directionTree_supported_rows,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.parallel_slots_at_scale,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.mixedStageBound_large,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.phaseRoundBound_large,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.geometricPhases_success,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.geometricPhases_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.cappedGeometric_every_oracle,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.cappedGeometric_success,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.cappedGeometric_abort,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.geometricCharge_step,
  CutQueryComplexity.StarContraction2022.Certificates.ParallelState.geometricPhases_expected,
  CutQueryComplexity.StarContraction2022.Certificates.initial_geometric_expected,
  CutQueryComplexity.StarContraction2022.Certificates.sequential_expected_small,
  CutQueryComplexity.StarContraction2022.Certificates.parallelCore_success,
  CutQueryComplexity.StarContraction2022.Certificates.parallelCore_none_cost,
  CutQueryComplexity.StarContraction2022.Certificates.parallelCore_expected,
  CutQueryComplexity.StarContraction2022.Certificates.parallelFuel_every_oracle,
  CutQueryComplexity.StarContraction2022.Certificates.parallelFuel_success,
  CutQueryComplexity.StarContraction2022.Certificates.parallelFuel_abort,
  CutQueryComplexity.StarContraction2022.Certificates.parallelFuel_tail,
  CutQueryComplexity.StarContraction2022.Certificates.parallelFuel_vanishing,
  CutQueryComplexity.StarContraction2022.Certificates.parallelFuel_one_percent,
  CutQueryComplexity.StarContraction2022.Certificates.exists_parallel_certificate,
  CutQueryComplexity.StarContraction2022.Certificates.parallelCertificateProgram_correct,
  CutQueryComplexity.StarContraction2022.Certificates.parallelCompletion_expected_le,
  CutQueryComplexity.StarContraction2022.Certificates.parallelZeroErrorExpectedBound_eq,
  CutQueryComplexity.StarContraction2022.Certificates.parallelCertificateProgram_expected,
  CutQueryComplexity.StarContraction2022.Certificates.exists_parallel_zero_error,
  CutQueryComplexity.StarContraction2022.Certificates.parallelZeroErrorFuel_every_oracle,
  CutQueryComplexity.StarContraction2022.Certificates.parallelZeroErrorFuel_success,
  CutQueryComplexity.StarContraction2022.Certificates.parallelZeroErrorFuel_abort,
  CutQueryComplexity.StarContraction2022.Certificates.parallelZeroErrorFuel_tail,
  CutQueryComplexity.StarContraction2022.Certificates.parallelZeroErrorFuel_one_percent,
  CutQueryComplexity.StarContraction2022.Certificates.exists_parallel_zero_error_capped,
  CutQueryComplexity.GHReduction.sourceBaseProgram_valid,
  CutQueryComplexity.GHReduction.sourceBaseProgram_exact,
  CutQueryComplexity.GHReduction.sourceBaseProgram_cost,
  CutQueryComplexity.GHReduction.sourceBaseProgram_cost_scaled,
  CutQueryComplexity.GHReduction.guideBaseProgram_cost,
  CutQueryComplexity.GHReduction.guideBaseTree_correct,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.originalRowsOn_centers,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.measuredCenterDegrees_eval,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.centerLearnProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph.centerLearnProgram_success_half,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.dfsRun_complete,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.dfsRun_cost_charged,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.dfsProg_exhausted_blocks,
  CutQueryComplexity.GHReduction.groupChoice_mem,
  CutQueryComplexity.GHReduction.mem_groupUnion,
  CutQueryComplexity.GHReduction.groupMap_inl,
  CutQueryComplexity.GHReduction.groupMap_surjective,
  CutQueryComplexity.GHReduction.groupVertex_card_le,
  CutQueryComplexity.GHReduction.inl_mem_groupTerminals,
  CutQueryComplexity.GHReduction.inr_not_mem_groupTerminals,
  CutQueryComplexity.GHReduction.groupTerminals_card,
  CutQueryComplexity.GHReduction.groupPush_trace,
  CutQueryComplexity.GHReduction.groupPull_trace,
  CutQueryComplexity.GHReduction.pull_groupPush,
  CutQueryComplexity.GHReduction.canonical_groupPull,
  CutQueryComplexity.GHReduction.groupIsolatingProgram_correct,
  CutQueryComplexity.GHReduction.groupIsolatingProgram_cost_scaled,
  CutQueryComplexity.GHReduction.refinedBlockParent_endpoint,
  CutQueryComplexity.GHReduction.refinedOldEdge_mem,
  CutQueryComplexity.GHReduction.refinedStarEdge_mem,
  CutQueryComplexity.GHReduction.refinedOldEdge_injective,
  CutQueryComplexity.GHReduction.refinedStarEdge_injective,
  CutQueryComplexity.GHReduction.refinedOldEdge_ne_star,
  CutQueryComplexity.GHReduction.refinedEdge_parts_disjoint,
  CutQueryComplexity.GHReduction.refinedEdges_card,
  CutQueryComplexity.GHReduction.refinedEdges_card_eq_vertices_sub_one,
  CutQueryComplexity.GHReduction.refinedEdges_spans,
  CutQueryComplexity.GHReduction.refinedBlockTree,
  CutQueryComplexity.GHReduction.refinedBlockTree_root,
  CutQueryComplexity.GHReduction.refinedBlockTree_parent_adj,
  CutQueryComplexity.GHReduction.refinedBlock_old_shore_pull,
  CutQueryComplexity.GHReduction.refinedBlock_frontier_sizes,
  CutQueryComplexity.StarContraction2022.Quantum.run_mapAnswers,
  CutQueryComplexity.StarContraction2022.Quantum.run_map_outputs,
  CutQueryComplexity.StarContraction2022.Quantum.mapAnswers_count_law,
  CutQueryComplexity.StarContraction2022.Quantum.decodeCutAnswer_range,
  CutQueryComplexity.StarContraction2022.Quantum.decode_capacityRead,
  CutQueryComplexity.StarContraction2022.Quantum.decodeCutAnswer_zero_weight,
  CutQueryComplexity.StarContraction2022.Quantum.decodeCutAnswer_zero_vertices,
  CutQueryComplexity.StarContraction2022.Quantum.encodeCutResult_spec,
  CutQueryComplexity.StarContraction2022.Quantum.encodeCutResult_eq_none_iff,
  CutQueryComplexity.StarContraction2022.Quantum.encodeCutResult_reject,
  CutQueryComplexity.StarContraction2022.Quantum.encode_decodeFiniteCutResult,
  CutQueryComplexity.StarContraction2022.Quantum.decode_encodeCutResult_sound,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTree_run,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTreeTotal_run,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTree_count_law,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTreeTotal_count_law,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTree_cost_le,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTree_decoded_run,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTreeTotal_decoded_run,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTree_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTree_successProb_honest,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTreeTotal_successProb_honest,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTree_zero_run,
  CutQueryComplexity.StarContraction2022.Quantum.small_sound_outputs_none,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutRoutine_len,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutRoutine_state,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutAlg_prob,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutAlg_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutAlg_successProb_honest,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutAlg_solves_iff,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutAlg_zero_prob,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTotalRoutine_len,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTotalRoutine_state,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTotalAlg_prob,
  CutQueryComplexity.StarContraction2022.Quantum.finiteCutTotalAlg_successProb_honest,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.middlePrefix_bound,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.source_cut_eq_value_add_residual,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.measureCut_eval,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.measured_cut_below_threshold,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.bfs_middlePrefix_bound,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.searchCutOrLevels_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.searchCutOrLevels_correct,
  CutQueryComplexity.GHReduction.GuideTree.centroid_not_mem_part,
  CutQueryComplexity.GHReduction.GuideTree.part_mem_isolationParts,
  CutQueryComplexity.GHReduction.GuideTree.isolationPart_nonempty,
  CutQueryComplexity.GHReduction.GuideTree.isolationPart_subset,
  CutQueryComplexity.GHReduction.GuideTree.isolationParts_disjoint,
  CutQueryComplexity.GHReduction.GuideTree.isolationParts_cover,
  CutQueryComplexity.GHReduction.GuideTree.isolationGroups_disjoint,
  CutQueryComplexity.GHReduction.GuideTree.isolationGroups_nonempty,
  CutQueryComplexity.GHReduction.GuideTree.isolationGroups_union,
  CutQueryComplexity.GHReduction.GuideTree.isolationParts_two_le,
  CutQueryComplexity.GHReduction.GuideTree.isolationParts_card_le,
  CutQueryComplexity.GHReduction.centroidShoreProgram_cost_scaled,
  CutQueryComplexity.GHReduction.centroidShoreProgram_correct,
  CutQueryComplexity.GHReduction.centroidShoreProgram_disjoint,
  CutQueryComplexity.GHReduction.centroid_children_nonterminal_mass,
  CutQueryComplexity.GHReduction.centroid_children_real_potential,
  CutQueryComplexity.GHReduction.centroid_children_total_size,
  CutQueryComplexity.GHReduction.centroid_child_potential_halves,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.avoidance_mass,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.chord_survival,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.product_survival_lower,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.avoidance_lower,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.condition_neighborDraw,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.condition_avoidance,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.joint_mass,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.noncrossing_degree,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.afterTranscriptDraws_avoidance,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.twoOut_joint_good,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.twoOut_joint_minimum,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.afterTranscript_joint_good,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.afterTranscript_joint_minimum,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.tail_bound,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.value_le_source_capacity,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.length_bound,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.le_two_pow_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.productBits_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.rootThreshold_pos,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.rootThreshold_le_n,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.rootThreshold_le_two_sqrt,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.candidateSound_mincut_le,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.productTreeRoutine_len,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.productTreeRoutine_state,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.productTreeRoutine_isQState,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.productTreeAlg_state,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.productTreeAlg_prob,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.productTreeAlg_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.productTree_cost,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.quotient,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.respects,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.card_labels_le,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.preserves_minimum,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.outsideDraws_avoidance_mass,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.outsideRatio_true_subrow,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.outsideDrawsProgram_eval,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.outsideDraws_avoidance_lower,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.outsideDraws_support,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.outsideDraws_unattached,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.outsideDraws_ratio_avoidance,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.outsideDraws_avoidance_complete,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.outsideDraws_edges,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.afterOutsideTranscript_avoidance,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.CenterAttachment.afterOutsideTranscript_complete,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.composedQuotient_preserves,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.composedQuotient_card_le,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.composedQuotient_guard,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.centerDraws_good,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.componentAttachmentDraws_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.componentAttachmentAfter_eval,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.componentAttachmentAfter_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.outsideQuotient_preserves,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.outsideQuotient_card_le,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.outsideQuotient_guard,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.outsideDraws_quotient_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.outsideAttachmentAfter_eval,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.outsideAttachmentAfter_success,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.bitCode_injective,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodeBits_spec,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodeBits_code,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodeBits_none_iff,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.singletonCounts_code,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodeRow_spec,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodeRow_guard,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodeRow_singleton,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodeRow_honest,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodeRow_empty,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.logarithmic_width,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.centerLaw,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.choiceLaw_rectangle,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.starChoiceLaw_some,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.starChoiceLaw_avoidance,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.centerLaw_restriction,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.centerChoiceLaw_mass,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.centerChoiceLaw_integrate,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.centerChoiceLaw_subtract_bad,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.centerChoiceLaw_one_support,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.unit_path_feasible,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitUpdate_stFlow,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitUpdate_integral,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitPhaseRun_facts,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitPhaseProg_finishes,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitPhaseProg_amount_pos,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.unitPhaseProg_cost_sharp,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.cutLetterOfProduct_honest,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.cutTreeToProduct_run,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.cutTreeToProduct_count_law,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.cutTreeToProduct_decoded_run,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.cutTreeToProduct_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.cutTreeToProduct_sound,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.verifyCandidate_run,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.verifyCandidate_sound,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.knownSubgraph_of_edges,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.knownCount_le_observed,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.residualGraph_le,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.residualCount_honest,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.residualGraph_w_eq_indicator,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.residualCount_eq_card,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.residualCount_pos_iff,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.fixedSize_ratio_sixth_tail,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.bernoulli_ratio_sixth_tail,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.center_ratio_sixth_tail,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.ratio_sum_mean_le,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.ratio_max_failure_le,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.quality_failure_le,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.quality_success_log,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.goodRows_star_quality,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.minimum_quality_success,
  CutQueryComplexity.GHReduction.centroidPairProgram_value,
  CutQueryComplexity.GHReduction.labels_mem_of_trace,
  CutQueryComplexity.GHReduction.childGuide_source,
  CutQueryComplexity.GHReduction.childGuide_real_card,
  CutQueryComplexity.GHReduction.guideOneProgram_valid,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.outsideRecovered_properties,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.learnedOutsideDrawsProgram_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.highContractionProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.highAfterCenters_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.highContractionProgram_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.centerRecovered_properties,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.recoverRowsProgram_eval,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.recoverRowsProgram_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.learnedComponentDrawsProgram_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.middleRowsBudget_le,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.middleContractionProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.middleAfterCenters_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.middleContractionProgram_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.checkedHighContractionProgram_guard,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.checkedHighContractionProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.checkedHighContractionProgram_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.checkedMiddleContractionProgram_guard,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.checkedMiddleContractionProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.checkedMiddleContractionProgram_success,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.checkedHighContractionProgram_scheduleGuard,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.checkedMiddleContractionProgram_scheduleGuard,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.recoveryHardCoefficient_schedule,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.highContraction_budget_le_attempt,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.middleContraction_budget_le_attempt,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.pStar_eq_middleContraction_times_certificate,
  CutQueryComplexity.StarContraction2022.Contraction.Joint.pStar_le_highContraction,
  CutQueryComplexity.GHReduction.minCut_inter_isolating,
  CutQueryComplexity.GHReduction.minCut_contract_of_pull,
  CutQueryComplexity.GHReduction.minCut_pull_of_representable,
  CutQueryComplexity.GHReduction.minCut_shorePush,
  CutQueryComplexity.GHReduction.isolating_child_has_minCut,
  CutQueryComplexity.GHReduction.candidateExact_pull_of_representable,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaleAnswers_graph_run,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.twoStar_integral,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaled_internal_pair_bound,
  CutQueryComplexity.StarContraction2022.Randomized.mass_bind_ge_countable,
  CutQueryComplexity.StarContraction2022.Randomized.ninetyNine_of_failure,
  CutQueryComplexity.StarContraction2022.Randomized.highProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Randomized.highProgram_sound,
  CutQueryComplexity.StarContraction2022.Randomized.highContinuation_success,
  CutQueryComplexity.StarContraction2022.Randomized.pStar_le_high_times_certificate,
  CutQueryComplexity.StarContraction2022.Randomized.highProgram_success,
  CutQueryComplexity.StarContraction2022.PublicQuotient.lift_minimum_of_value_eq,
  CutQueryComplexity.StarContraction2022.PublicQuotient.exists_respecting_minimum_of_value_eq,
  CutQueryComplexity.StarContraction2022.CutResult.optimal_of_sound_value,
  CutQueryComplexity.StarContraction2022.Contraction.Uniform.highProgram_guard,
  CutQueryComplexity.StarContraction2022.Contraction.Uniform.highProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.Uniform.highProgram_success,
  CutQueryComplexity.StarContraction2022.Contraction.Uniform.middleProgram_guard,
  CutQueryComplexity.StarContraction2022.Contraction.Uniform.middleProgram_every_oracle,
  CutQueryComplexity.StarContraction2022.Contraction.Uniform.middleProgram_success,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.productRead_singleton_val,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.neighborhoodAnswerValid_honest,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.neighborhoodOfAnswer_honest,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_run,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_cost,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoodResult_none_iff,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoodResult_bad_coordinate,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoodResult_bad_diagonal,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_run_of_valid,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_supported_some,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_rows_outside,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_rows_diagonal,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_run_honest,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_eval_honest,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_successProb_honest,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.outsideCenterNeighbors_exact,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.outsideCenterNeighbors_supported,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_run_empty,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_zero,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_one_honest,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_one_cost,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_physical_length,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_physical_state,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_physical_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_physical_prob,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_physical_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_physical_run_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.centerNeighborhoods_physical_cap,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.sampleBlue_supported_subset,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.sampleBlue_restriction,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.isolation_mass_ennreal,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.isolation_mass,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.isolation_polynomial_lower,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.isolation_lower,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.isolation_failure_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.isolationTrials_failure_mass,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.isolationTrials_failure_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.dyadicProbability_pos,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.dyadicProbability_le_one,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.pow_clog_le_twice,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.dyadic_scale,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.edge_swap,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.edgeGraph_insert,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.edgeFinset_edgeGraph,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.edgeGraph_edgeFinset,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.acyclic,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.card_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.insertEdge_swap,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.subset_insertEdge,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.insertEdge_card_of_not_reachable,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.insertList_card_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.insertEdge_residualSound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.insertList_residualSound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.residualSound_subgraph,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.representative_eq_iff,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.componentCount_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.componentCount_mono,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.deficit_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.deficit_add_residual_components,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.component_card_eq_iff,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.deficit_zero_iff_spans,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.spanningForest_of_deficit_zero,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.centerProbability_pos,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.kcap_eq_n_of_probability_one,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.log_add_two_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.kcap_le_sqrt_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.weighted_budget_le_bmax,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.guarded_branch_index,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.weighted_product_cost,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.QH_envelope,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.quality_mean_bound,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.size_error_le,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.coverage_error_le,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.bad_mass_envelope,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.starQuotient,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.starQuotient_map_eq_iff,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.starLabels_eq_centers,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.starQuotient_card,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.starQuotient_respects,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.starQuotient_surviving_minimum,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.choiceLaw_avoids_mass,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.starChoiceLaw_survival,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.centerChoiceLaw_survival,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.bernoulli_double_upper_tail,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.center_size_failure_le,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.center_empty_row_mass,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.center_empty_row_le,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.center_coverage_failure_le,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.badCenters_mass_le,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.minimum_guarded_survival,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactTree_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactTree_eval,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactTree_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactSharpBudget_eq,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.exists_scaledExactTree,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactRun_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactProg_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactCertificate.minimum_shore,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactCertificate.maximum_flow,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactCertificate.flow_integer,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactProg_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactRun_first,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactRun_history,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactProg_history,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.divideFlow_stFlow,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.divideFlow_residual_pos_iff,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaled_residual_middle_layer_deficit,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.scaled_tail_bound,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.scaled_phase_count,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.PhaseHistory.scaled_length_bound,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactProg_phase_work,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.scaledExactProg_cost_sharp,
  CutQueryComplexity.GHReduction.centroidTree_subtree,
  CutQueryComplexity.GHReduction.GuideTree.part_of_rootward,
  CutQueryComplexity.GHReduction.GuideTree.part_of_child_subtree,
  CutQueryComplexity.GHReduction.GuideTree.oneEdge_part,
  CutQueryComplexity.GHReduction.GuideTree.oneEdge_trace_part,
  CutQueryComplexity.GHReduction.GuideTree.respects_compl,
  CutQueryComplexity.GHReduction.oneEdge_oriented_child,
  CutQueryComplexity.GHReduction.oneEdge_child,
  CutQueryComplexity.GHReduction.childGuide_map_real,
  CutQueryComplexity.GHReduction.guideWork,
  CutQueryComplexity.GHReduction.size_le_guideWork,
  CutQueryComplexity.GHReduction.guideWork_le_twice_size,
  CutQueryComplexity.GHReduction.centroid_children_guideWork,
  CutQueryComplexity.GHReduction.guide_cost_recurrence,
  CutQueryComplexity.GHReduction.guide_root_budget,
  CutQueryComplexity.GHReduction.child_fuel_bound,
  CutQueryComplexity.GHReduction.initial_fuel_bound,
  CutQueryComplexity.GHReduction.guideOneProgram_child_le,
  CutQueryComplexity.GHReduction.guideOneProgram_complete,
  CutQueryComplexity.GHReduction.guideOneProgram_clog_complete,
  CutQueryComplexity.GHReduction.centroidPairProgram_cost,
  CutQueryComplexity.GHReduction.centroidPairProgram_cost_scaled,
  CutQueryComplexity.GHReduction.guideBaseProgram_cost_scaled,
  CutQueryComplexity.GHReduction.childGuide_graph_size_le,
  CutQueryComplexity.GHReduction.guideOneProgram_cost_scaled,
  CutQueryComplexity.GHReduction.guideOneProgram_root_cost,
  CutQueryComplexity.GHReduction.guideOneBudget,
  CutQueryComplexity.GHReduction.guideOneTree,
  CutQueryComplexity.GHReduction.guideOneTree_eval,
  CutQueryComplexity.GHReduction.guideOneTree_correct,
  CutQueryComplexity.GHReduction.exists_guideOneTree,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.PathAt.tight,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.zero_stFlow,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactProg_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.ExactCertificate.value_eq_cut,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.exactRun_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.positive_flow_reachable,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.extractRoutes_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.routedFlowProg_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.locateRoutes_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.located_terminal_bounds,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.originalRouteFlow_divergence,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.routes_cut_domination,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.pruneProg_minimizer,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.pruneProg_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.pruneProg_structure,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_small,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_cost,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_cost_envelope,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.centerStage_eval_valid,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_eval_honest,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_sound,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.weightedFinish_success,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_minimum_mass_of_lt_one,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_minimum_mass_of_probability_one,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_minimum_mass,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_success,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_physical_length,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_physical_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_physical_event_law,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_physical_success,
  CutQueryComplexity.StarContraction2022.Quantum.UniformStars.highCandidate_physical_envelope,
  CutQueryComplexity.StarContraction2022.Randomized.attemptCoefficient_eq,
  CutQueryComplexity.StarContraction2022.Randomized.branch_budgets,
  CutQueryComplexity.StarContraction2022.Randomized.reconstructionBudget_le,
  CutQueryComplexity.StarContraction2022.Randomized.parallelShore_sound,
  CutQueryComplexity.StarContraction2022.Randomized.parallelShore_success,
  CutQueryComplexity.StarContraction2022.Randomized.smallDegreeProgram_success,
  CutQueryComplexity.StarContraction2022.Randomized.middleSolve_success,
  CutQueryComplexity.StarContraction2022.Randomized.middleProgram_success,
  CutQueryComplexity.StarContraction2022.Randomized.reconstructionProgram_correct,
  CutQueryComplexity.StarContraction2022.Randomized.candidateProgram_sound,
  CutQueryComplexity.StarContraction2022.Randomized.candidateProgram_success,
  CutQueryComplexity.StarContraction2022.Randomized.decodeDegrees_spec,
  CutQueryComplexity.StarContraction2022.Randomized.decodeDegrees_correct,
  CutQueryComplexity.StarContraction2022.Randomized.attempt_sound,
  CutQueryComplexity.StarContraction2022.Randomized.attempt_success,
  CutQueryComplexity.StarContraction2022.Randomized.attempt_every_oracle,
  CutQueryComplexity.GHReduction.guideOneGlobalBudget,
  CutQueryComplexity.GHReduction.guideOneProgram_global_cost,
  CutQueryComplexity.GHReduction.guideOneGlobalTree,
  CutQueryComplexity.GHReduction.guideOneGlobalTree_eval,
  CutQueryComplexity.GHReduction.guideOneGlobalTree_complete,
  CutQueryComplexity.GHReduction.frontierBranch,
  CutQueryComplexity.GHReduction.frontierBranch_excludes,
  CutQueryComplexity.GHReduction.frontierBranch_nonempty,
  CutQueryComplexity.GHReduction.frontierBranch_child_subset,
  CutQueryComplexity.GHReduction.frontierBranches_disjoint,
  CutQueryComplexity.GHReduction.exists_frontierBranch,
  CutQueryComplexity.GHReduction.frontierProxy,
  CutQueryComplexity.GHReduction.mem_frontierProxy_branch,
  CutQueryComplexity.GHReduction.frontierProxy_eq_iff,
  CutQueryComplexity.GHReduction.frontierMap,
  CutQueryComplexity.GHReduction.frontierMap_eq_inl,
  CutQueryComplexity.GHReduction.frontierMap_eq_inr,
  CutQueryComplexity.GHReduction.frontierMap_surjective,
  CutQueryComplexity.GHReduction.frontierMap_original_fiber,
  CutQueryComplexity.GHReduction.frontierMap_proxy_fiber,
  CutQueryComplexity.GHReduction.frontier_contraction_promise,
  CutQueryComplexity.GHReduction.frontier_contraction_cut,
  CutQueryComplexity.GHReduction.actual_frontier_vertex_sum,
  CutQueryComplexity.GHReduction.frontierBranch_isCentroidBranch,
  CutQueryComplexity.GHReduction.GuidePruneSeed,
  CutQueryComplexity.GHReduction.GuideTree.keptBranches,
  CutQueryComplexity.GHReduction.GuideTree.source_kept,
  CutQueryComplexity.GHReduction.GuideTree.branch_kept,
  CutQueryComplexity.GHReduction.GuideTree.discarded_branch_disjoint,
  CutQueryComplexity.GHReduction.GuideTree.pruned,
  CutQueryComplexity.GHReduction.GuideTree.pruned_source,
  CutQueryComplexity.GHReduction.GuideTree.pruned_real_mem,
  CutQueryComplexity.GHReduction.GuideTree.pruned_respects,
  CutQueryComplexity.GHReduction.mass_prune_keep_delete,
  CutQueryComplexity.GHReduction.guidePruneTree,
  CutQueryComplexity.GHReduction.guidePruneTree_eval,
  CutQueryComplexity.GHReduction.guidePruneTree_valid,
  CutQueryComplexity.GHReduction.guidePruneTree_failure_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.RoutePath.nodup,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.RoutePath.divergence,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.routeSubtract_balance,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.RouteSpec.load_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.RouteSpec.undirected_load_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.routedFlowProg_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.chooseUnit_spec,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.route_original_source_sum,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.route_original_sink_sum,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.locateRoute_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.route_separated_le_cross,
  CutQueryComplexity.DeterministicAPMCExpansion.Flow.sum_separated_le_routesCross,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.pruning_cut_objective,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverBudget_eq,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestBudget_eq,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.inverse_pow_ceil_log_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.rowTrials_tail,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.rowTrials_tail_ennreal,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.rowTrials_union_error,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRounds_tail,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRounds_deficit_tail,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoveryTape_supported_subset,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.rowQueryIndex_card,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.selectRow_some,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.selectRow_ne_none_iff,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_eval,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_eval_overlap,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_cost,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodedTrial_honest,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.decodedTrial_honest_some_iff,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverResult_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_empty_row,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverResult_ne_none_of_isolated,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverResult_row_failure_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_failure,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_public,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_physical_length,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_physical_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_physical_prob,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRows_physical_successProb,
  CutQueryComplexity.StarContraction2022.Randomized.retainState_sound,
  CutQueryComplexity.StarContraction2022.Randomized.retainState_good_right,
  CutQueryComplexity.StarContraction2022.Randomized.retainState_good_left,
  CutQueryComplexity.StarContraction2022.Randomized.retainedStep_sound,
  CutQueryComplexity.StarContraction2022.Randomized.retainedStep_keep,
  CutQueryComplexity.StarContraction2022.Randomized.retainedStep_failure,
  CutQueryComplexity.StarContraction2022.Randomized.iterate_sound,
  CutQueryComplexity.StarContraction2022.Randomized.iterate_present,
  CutQueryComplexity.StarContraction2022.Randomized.repetitions_pos,
  CutQueryComplexity.StarContraction2022.Randomized.repeated_failure,
  CutQueryComplexity.StarContraction2022.Randomized.program_every_oracle,
  CutQueryComplexity.StarContraction2022.Randomized.program_small,
  CutQueryComplexity.StarContraction2022.Randomized.program_sound,
  CutQueryComplexity.StarContraction2022.Randomized.program_failure,
  CutQueryComplexity.StarContraction2022.Randomized.program_success,
  CutQueryComplexity.StarContraction2022.Randomized.linearConstant_eq,
  CutQueryComplexity.StarContraction2022.Randomized.linearConstant_pos,
  CutQueryComplexity.StarContraction2022.Randomized.exists_uniform_linear_program,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.labelEmbedding_label,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.exists_matching_extends,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.completeMatching_spec,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.assignClones_success,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.ClonePairing.fakeLeft_card,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.ClonePairing.fakeEndpoints_mate,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.ClonePairing.fakeEndpoints_card,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.ClonePairing.routed_left_notFake,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.ClonePairing.real_left_iff,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.slotCount_add_compl,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.slotCount_le,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.sum_slotCount,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.slotCount_shore_le_real,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.bisection_star_totals,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.bisection_clone_card,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropy_pair_average,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropy_average_mono,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropy_le_log_card,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.potential_nil,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.potential_cons_mono,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.potential_le,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Matching.compl_mass_average,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.startMass_le_one,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.leakage_cons_le,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.twice_leakage_le_cut,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.leakage_eq_start_sum,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pairGain_scale,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pairGain_ratio_pos,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.gapConstant_pos,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pairGain_ge,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropyRoundFactor_ge_two,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropyRoundFactor_scaled,
  CutQueryComplexity.GHReduction.tree_membership_of_crossSet_empty,
  CutQueryComplexity.GHReduction.tree_cut_subset_single_branch,
  CutQueryComplexity.GHReduction.GuideTree.part_of_branch,
  CutQueryComplexity.GHReduction.GuideTree.singleBranch_trace_part,
  CutQueryComplexity.GHReduction.singleBranch_oriented_child,
  CutQueryComplexity.GHReduction.singleBranch_child,
  CutQueryComplexity.GHReduction.thresholdLevels,
  CutQueryComplexity.GHReduction.hitLevel,
  CutQueryComplexity.GHReduction.hitLevel_le,
  CutQueryComplexity.GHReduction.hitLevel_scale,
  CutQueryComplexity.GHReduction.uniqueSurvivor_real_bound,
  CutQueryComplexity.GHReduction.uniqueSurvivor_hitLevel_real,
  CutQueryComplexity.GHReduction.uniqueSurvivor_hitLevel,
  CutQueryComplexity.GHReduction.canonicalST_subset_of_mem,
  CutQueryComplexity.GHReduction.canonicalST_disjoint_of_targets_outside,
  CutQueryComplexity.GHReduction.canonicalST_laminar,
  CutQueryComplexity.GHReduction.canonicalIso_eq_pair,
  CutQueryComplexity.GHReduction.accepted_shore_sound,
  CutQueryComplexity.GHReduction.canonical_hit_covers,
  CutQueryComplexity.GHReduction.thresholdAccepted,
  CutQueryComplexity.GHReduction.thresholdCoverage,
  CutQueryComplexity.GHReduction.mem_thresholdCoverage,
  CutQueryComplexity.GHReduction.thresholdCoverage_subset,
  CutQueryComplexity.GHReduction.isolatingValuesProgram_value,
  CutQueryComplexity.GHReduction.thresholdLevelProgram,
  CutQueryComplexity.GHReduction.thresholdLevelProgram_subset,
  CutQueryComplexity.GHReduction.thresholdLevelProgram_sound,
  CutQueryComplexity.GHReduction.thresholdLevelProgram_hit,
  CutQueryComplexity.GHReduction.thresholdRoundProgram,
  CutQueryComplexity.GHReduction.mem_thresholdRoundProgram,
  CutQueryComplexity.GHReduction.thresholdRoundProgram_sound,
  CutQueryComplexity.GHReduction.thresholdRoundProgram_hit,
  CutQueryComplexity.GHReduction.thresholdLevelProgram_cost_scaled,
  CutQueryComplexity.GHReduction.thresholdRoundProgram_cost_scaled,
  CutQueryComplexity.GHReduction.uniqueSurvivor_canonical_disjoint,
  CutQueryComplexity.GHReduction.successfulTargets,
  CutQueryComplexity.GHReduction.successfulTargets_charge,
  CutQueryComplexity.GHReduction.thresholdRoundProgram_charge,
  CutQueryComplexity.GHReduction.thresholdRoundProgram_expected_progress,
  CutQueryComplexity.GHReduction.thresholdRoundBudget,
  CutQueryComplexity.GHReduction.thresholdRoundProgram_cost,
  CutQueryComplexity.GHReduction.thresholdRoundTree,
  CutQueryComplexity.GHReduction.thresholdRoundTree_eval,
  CutQueryComplexity.GHReduction.thresholdRoundTree_sound,
  CutQueryComplexity.GHReduction.thresholdRoundTree_expected_progress,
  CutQueryComplexity.GHReduction.thresholdRemainingTree,
  CutQueryComplexity.GHReduction.thresholdRemainingLaw,
  CutQueryComplexity.GHReduction.thresholdRemainingTree_eval,
  CutQueryComplexity.GHReduction.thresholdRemainingTree_invariant,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.componentCount_sup_edge,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.insertEdge_componentCount,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.insertList_counts,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.insertList_guards_of_closed,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.State.insertList_guards_of_star,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.mem_redVertices,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.mem_blueVertices,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.red_blue_disjoint,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoveredEdge_spec,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoveredEdges_length,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoveredEdges_separate,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoveredEdges_guards,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.roundUpdate_counts,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_eval,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_cost,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.residualNeighbor_iff_mem,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.roundUpdate_residualSound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.roundUpdate_deficit,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_residualSound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_public,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_physical_length,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_physical_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_physical_prob,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.inactive_component_closed,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.componentCount_le_active_add,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.trueResidual_adj,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.deficit_le_active,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.favorableComponents_card_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.favorableComponent_mass,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.favorableComponents_expect,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.favorableComponents_subset_recovered,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.roundUpdate_drift_pointwise,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recovery_error_contribution,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverRound_drift,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_drift,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_eval_full,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.fullRoundState_residualSound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.fullHistoryState_residualSound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_drift_at_full_history,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRound_progress_public,
  CutQueryComplexity.GHReduction.lowTargets,
  CutQueryComplexity.GHReduction.mem_lowTargets,
  CutQueryComplexity.GHReduction.lowTargets_sdiff,
  CutQueryComplexity.GHReduction.thresholdRate,
  CutQueryComplexity.GHReduction.thresholdRate_arg_nonneg,
  CutQueryComplexity.GHReduction.expect_finset_card_ne_top,
  CutQueryComplexity.GHReduction.expected_remainder_of_progress,
  CutQueryComplexity.GHReduction.thresholdRoundTree_expected_remainder,
  CutQueryComplexity.GHReduction.thresholdRemainingTree_expected_low,
  CutQueryComplexity.GHReduction.thresholdRemainingTree_failure_le,
  CutQueryComplexity.GHReduction.thresholdRounds,
  CutQueryComplexity.GHReduction.thresholdRate_block,
  CutQueryComplexity.GHReduction.thresholdRate_rounds,
  CutQueryComplexity.GHReduction.thresholdRate_rounds_mul_card,
  CutQueryComplexity.GHReduction.thresholdClassifyTree,
  CutQueryComplexity.GHReduction.thresholdClassifyTree_subset,
  CutQueryComplexity.GHReduction.thresholdClassifyTree_failure_le,
  CutQueryComplexity.GHReduction.sourceThresholdBudget,
  CutQueryComplexity.GHReduction.sourceMaxAtTree,
  CutQueryComplexity.GHReduction.sourceMaxAtTree_failure_le,
  CutQueryComplexity.GHReduction.sourceMaxTree,
  CutQueryComplexity.GHReduction.IsSourceMaximum,
  CutQueryComplexity.GHReduction.sourceMaxTree_failure_le,
  CutQueryComplexity.GHReduction.stValue_symm,
  CutQueryComplexity.GHReduction.sourceSwitch_lower,
  CutQueryComplexity.GHReduction.sourceSwitch_minCut,
  CutQueryComplexity.GHReduction.sourceSwitchEstimate,
  CutQueryComplexity.GHReduction.sourceSwitchEstimate_upper,
  CutQueryComplexity.GHReduction.sourceSwitchEstimate_exact_at_max,
  CutQueryComplexity.GHReduction.switchedGuide,
  CutQueryComplexity.GHReduction.sourceSwitchProgram,
  CutQueryComplexity.GHReduction.sourceSwitchProgram_upper,
  CutQueryComplexity.GHReduction.sourceSwitchProgram_complete,
  CutQueryComplexity.GHReduction.sourceSwitchProgram_cost,
  CutQueryComplexity.GHReduction.branchTouchesEdge,
  CutQueryComplexity.GHReduction.branchTouchesEdge_iff,
  CutQueryComplexity.GHReduction.exists_branchTouchesEdge,
  CutQueryComplexity.GHReduction.branchTouchesEdge_unique,
  CutQueryComplexity.GHReduction.guideTwo_crossing_cases,
  CutQueryComplexity.GHReduction.GuideTree.branch_real_half,
  CutQueryComplexity.GHReduction.GuideTree.outside_branch_nonempty,
  CutQueryComplexity.GHReduction.GuideTree.sourceBranch,
  CutQueryComplexity.GHReduction.GuideTree.sourceBranch_eq,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Matching.mate_mass_le_compl,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.favored_mass_ge_quarter,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.sum_pairGain,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.favored_gain,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropy_increment_of_low_escape,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.goodStarts_card,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balanced_progress,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.chooseQuarter_none_iff,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.halfCompletion_contains,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedProgram_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedProgram_spec,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedProgram_progress,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedRounds_progress,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedProgram_finishes,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.chooseSmall_none_iff,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.peel_step_card,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.peel_step_invariant,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.peelRun_invariant,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.peelRun_stable,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.peeled_invariant,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.peeled_stable,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.stable_small_expansion,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.stable_expansion,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Matching.cut_ge_removed_shore,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pruned_final_matching_small,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pruned_final_matching_quarter,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedBatch_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedBatch_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedBatch_four_dense,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.finishProgram_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.finishProgram_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.fullProgram_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.fullProgram_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.normalizedRuns_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.normalizedRuns_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.cutPlayer_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.cutPlayer_expands,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestIter_eval,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestIter_eval_succ,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestIter_run_succ,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestIter_cost,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestIter_residualSound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_eval,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_cost,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_residualSound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_output_forest,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.state_eq_empty_of_small,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_eval_small,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_eval_zero,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_eval_one,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestIter_expected_deficit,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestIter_expected_deficit_le_n,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_expected_deficit,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestSuccess_of_deficit_zero,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_failure,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.trueResidual_eq_capacity_support,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestSuccess_iff_capacity_residual,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestSuccess_of_small,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_failure_small,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_failure_zero,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_failure_one,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_public,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_physical_length,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_physical_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_physical_prob,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_physical_event,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRun_physical_successProb,
  CutQueryComplexity.GHReduction.random_run_map,
  CutQueryComplexity.GHReduction.randomTableAux,
  CutQueryComplexity.GHReduction.randomTableAux_entry_support,
  CutQueryComplexity.GHReduction.randomTableAux_cost,
  CutQueryComplexity.GHReduction.randomTable,
  CutQueryComplexity.GHReduction.randomTable_entry_support,
  CutQueryComplexity.GHReduction.randomTable_cost,
  CutQueryComplexity.GHReduction.randomRepeat,
  CutQueryComplexity.GHReduction.randomRepeat_eval,
  CutQueryComplexity.GHReduction.independentSamples_member,
  CutQueryComplexity.GHReduction.randomRepeat_member,
  CutQueryComplexity.GHReduction.randomRepeat_failure_le,
  CutQueryComplexity.GHReduction.randomRepeat_cost,
  CutQueryComplexity.GHReduction.randomTableAux_failure_le,
  CutQueryComplexity.GHReduction.randomTable_failure_le,
  CutQueryComplexity.GHReduction.minEstimate,
  CutQueryComplexity.GHReduction.bestEstimates,
  CutQueryComplexity.GHReduction.EstimateAbove,
  CutQueryComplexity.GHReduction.minEstimate_above,
  CutQueryComplexity.GHReduction.bestEstimates_above,
  CutQueryComplexity.GHReduction.minEstimate_exact_left,
  CutQueryComplexity.GHReduction.minEstimate_exact_right,
  CutQueryComplexity.GHReduction.bestEstimates_exact,
  CutQueryComplexity.GHReduction.candidateEstimate,
  CutQueryComplexity.GHReduction.candidateEstimate_above,
  CutQueryComplexity.GHReduction.candidateEstimate_exact,
  CutQueryComplexity.GHReduction.stValue_le_contract,
  CutQueryComplexity.GHReduction.stValue_contract_eq_of_representable,
  CutQueryComplexity.GHReduction.pullEstimate,
  CutQueryComplexity.GHReduction.pullEstimate_above,
  CutQueryComplexity.GHReduction.pullEstimate_exact,
  CutQueryComplexity.GHReduction.guidePruneTrialsTree,
  CutQueryComplexity.GHReduction.pruneTrials_above,
  CutQueryComplexity.GHReduction.guidePruneTrialsTree_above,
  CutQueryComplexity.GHReduction.guidePruneTrialsTree_failure_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.node_mass_bound,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.leafBoundary_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.root_boundary_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.ShrinkingSequence.zero_after_clog,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.levelMass_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.mass_le_depth,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.depth_le_clog,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.mass_le_clog,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.localTolerance_budget,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.localTolerance_shrink,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.split_child_shrink,
  CutQueryComplexity.DeterministicAPMCExpansion.shaveProgram_preservesFriendly_of_additive,
  CutQueryComplexity.DeterministicAPMCExpansion.shaveProgram_edge_cap_of_boundary,
  CutQueryComplexity.DeterministicAPMCExpansion.partitionAnswers_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.partitionAnswers_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.totalPartitionAnswers_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.totalPartitionAnswers_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.unpadProgram_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.unpadProgram_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.nodes_add_one,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.largeLeaves_mass,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.SparseSplits,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.Covered,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.Shrinks,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.Positive,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.WorkTree.spineSize,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.localTolerance,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.localTolerance_pos,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.pruned_child_shrink,
  CutQueryComplexity.DeterministicAPMCExpansion.edgeCap,
  CutQueryComplexity.DeterministicAPMCExpansion.partitionRecoveryBudget,
  CutQueryComplexity.DeterministicAPMCExpansion.partitionRecoveryBudget_eq,
  CutQueryComplexity.DeterministicAPMCExpansion.partitionAnswers,
  CutQueryComplexity.DeterministicAPMCExpansion.totalPartitionAnswers,
  CutQueryComplexity.DeterministicAPMCExpansion.restrictAnswers,
  CutQueryComplexity.DeterministicAPMCExpansion.unpadProgram,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.rowTrials_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestRounds_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.recoverBudget_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestBudget_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.split_tolerance_log_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forestBudget_split_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.repeated_forestBudget_add_one_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forest_physical_budget_le,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.exists_forest_physical_constant,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.forest_physical_budget_le_fixed_tolerance,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.exists_fixed_tolerance_forest_constant,
  CutQueryComplexity.GHReduction.thresholdRoundTree_run,
  CutQueryComplexity.GHReduction.thresholdRoundTree_cost_scaled,
  CutQueryComplexity.GHReduction.thresholdRemainingTree_cost_scaled,
  CutQueryComplexity.GHReduction.thresholdClassifyTree_cost_scaled,
  CutQueryComplexity.GHReduction.sourceMaxAtTree_cost_scaled,
  CutQueryComplexity.GHReduction.sourceMaxTree_cost_scaled,
  CutQueryComplexity.GHReduction.GuideTree.nodeOfLabel,
  CutQueryComplexity.GHReduction.GuideTree.nodeOfLabel_spec,
  CutQueryComplexity.GHReduction.GuideTree.nodeOfLabel_exists,
  CutQueryComplexity.GHReduction.outsideGuideNodes,
  CutQueryComplexity.GHReduction.source_not_mem_outsideGuideVertices,
  CutQueryComplexity.GHReduction.guideMaximumTree,
  CutQueryComplexity.GHReduction.IsGuideMaximum,
  CutQueryComplexity.GHReduction.guideMaximumTree_guard,
  CutQueryComplexity.GHReduction.guideMaximumTree_failure_le,
  CutQueryComplexity.GHReduction.guideMaximumTree_cost_scaled,
  CutQueryComplexity.GHReduction.guideOneProgram_cost_linear,
  CutQueryComplexity.GHReduction.guideOneProgram_localFuel_cost_scaled,
  CutQueryComplexity.GHReduction.sourceSwitchBudget,
  CutQueryComplexity.GHReduction.sourceSwitchProgram_cost_scaled,
  CutQueryComplexity.GHReduction.cost_le_of_scaled,
  CutQueryComplexity.GHReduction.sourceSwitchGlobalTree,
  CutQueryComplexity.GHReduction.sourceSwitchGlobalTree_eval,
  CutQueryComplexity.GHReduction.guideSwitchContinuation,
  CutQueryComplexity.GHReduction.guideSwitchTree,
  CutQueryComplexity.GHReduction.SourceSwitchSuccess,
  CutQueryComplexity.GHReduction.guideSwitchContinuation_good,
  CutQueryComplexity.GHReduction.guideSwitchTree_failure_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.le_cubeRoot_pow,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.local_rounds_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.roundBudget_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.cubeRoot,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.cubeRoot_pos,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.cubeRoot_min,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.cubeRoot_le_succ,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.pred_cubeRoot_pow_lt,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.log_nat_le_clog,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.balancedRounds_le_clog,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.roundBudget,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.roundBudget_ge_two,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.sizeLog,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.sizeLog_pos,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.roundCoefficient,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.PartVertex,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.partNetwork_searchDepth,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeQuery,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeOracle,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeProgram,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeProgram_eval_public,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.subtypeQuery_eval_public,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.cutPlayer,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.normalizedRounds,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.normalizedRuns,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.fullRounds,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.fullProgram,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedBatch,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.finishProgram,
  CutQueryComplexity.DeterministicAPMCExpansion.bisection_deficit_split,
  CutQueryComplexity.DeterministicAPMCExpansion.matchingRound_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.matchingRound_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.matchingRound_cost_sharp,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.fallbackMatching_crosses,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.roundResponse_crosses,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.gameRead_legal,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.runMatchingGame_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.runMatchingGame_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.executedCutPlayer_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.executedCutPlayer_complete,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.replyTrace_bind,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.replyTrace_map,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedProgram_history_trace,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedBatch_history_trace,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.finishProgram_history_trace,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.fullProgram_history_trace,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.normalizedRuns_history_trace,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.cutPlayer_history_trace,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.runMatchingGame_complete_trace,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.executedCutPlayer_history_of_replay,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.executedCutPlayer_history,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.historyGraph_reverse_cut,
  CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.executedCutPlayer_rounds_expand,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.pairCount_eq_fakeLeft,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.pairCount_eq_deficit,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.pairing_reverse,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.pairing_real_endpoint,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.separated_indicator,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.list_sum_get,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.realCrossing_le_routes,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.round_real_cut_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.history_real_cut_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.cloneShore_compl,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.completed_certificate,
  CutQueryComplexity.StarContraction2022.Quantum.taggedEmbed_norm,
  CutQueryComplexity.StarContraction2022.Quantum.taggedCall_len,
  CutQueryComplexity.StarContraction2022.Quantum.taggedCall_run_basis,
  CutQueryComplexity.StarContraction2022.Quantum.taggedCall_run,
  CutQueryComplexity.StarContraction2022.Quantum.taggedCall_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.taggedRoutine_len,
  CutQueryComplexity.StarContraction2022.Quantum.taggedRoutine_run,
  CutQueryComplexity.StarContraction2022.Quantum.taggedRoutine_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.taggedAlg_state,
  CutQueryComplexity.StarContraction2022.Quantum.taggedAlg_prob,
  CutQueryComplexity.StarContraction2022.Quantum.minimumTagged_singleton_spec,
  CutQueryComplexity.StarContraction2022.Quantum.minimumTagged_tie_break,
  CutQueryComplexity.StarContraction2022.Quantum.minimumTagged_value,
  CutQueryComplexity.StarContraction2022.Quantum.taggedMinimumReadAll_prob,
  CutQueryComplexity.StarContraction2022.Quantum.minimumTagged_counts_nonempty,
  CutQueryComplexity.StarContraction2022.Quantum.minimumTagged_qQuery_le,
  CutQueryComplexity.StarContraction2022.Quantum.exists_minimumTagged_base,
  CutQueryComplexity.StarContraction2022.Quantum.exists_minimumTagged_repeated,
  CutQueryComplexity.StarContraction2022.Quantum.minimumTaggedAlg_correct,
  CutQueryComplexity.StarContraction2022.Quantum.minimumWitnessRaw_state,
  CutQueryComplexity.StarContraction2022.Quantum.minimumWitnessRaw_prob,
  CutQueryComplexity.StarContraction2022.Quantum.minimumWitnessRaw_correct,
  CutQueryComplexity.StarContraction2022.Quantum.minimumWitnessVerified_law,
  CutQueryComplexity.StarContraction2022.Quantum.minimumWitnessVerified_sound,
  CutQueryComplexity.StarContraction2022.Quantum.minimumWitnessVerified_correct,
  CutQueryComplexity.StarContraction2022.Quantum.exists_minimumDegreeWitness_algorithm,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessAlg_law,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessAlg_zero,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessAlg_correct,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessAlg_sound,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessAlg_minimum,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessRoutine_len,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessRoutine_cap,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessRoutine_state,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessRoutine_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessRoutine_event_law,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessAlg_honest_sound,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessAlg_honest_minimum,
  CutQueryComplexity.StarContraction2022.Quantum.minimumDegreeWitnessAlg_simple,
  CutQueryComplexity.StarContraction2022.Quantum.exists_quantum_minimumDegree_witness,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.ForestBatch,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.batchGraphs,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.batchGraphs_cons,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.batchGraphs_length,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.collectForests,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.collectForests_eval_zero,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.collectForests_eval_succ,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.collectForests_run_succ,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.collectForests_cost,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.knownSubgraph_empty,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.knownSubgraph_union,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.residualGraph_empty,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.residualGraph_union,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.BatchSound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.batchSound_cons,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.collectForests_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.collectForests_chain_failure,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.batchCertificate,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.batchCertificate_of_chain,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateRun,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateRun_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateRun_eval_zero,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateRun_chain_failure,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateRun_chain_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateRun_certificate_failure,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateRun_certificate_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateShore,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateShore_spec,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificate_minimum_transfer,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateCandidate,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.LowMinimumCandidate,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateCandidate_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.certificateCandidate_minimum,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_eval,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_run,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_run_zero,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_run_small,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_cost,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_failure,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_public,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_physical_length,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_physical_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_physical_prob,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_physical_event,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_physical_successProb,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_physical_cost,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_physical_cost_fixed_tolerance,
  CutQueryComplexity.StarContraction2022.Quantum.Forest.lowCandidate_physical_public,
  CutQueryComplexity.GHReduction.dependentRandomTableAux,
  CutQueryComplexity.GHReduction.dependentRandomTableAux_entry_support,
  CutQueryComplexity.GHReduction.dependentRandomTableAux_cost,
  CutQueryComplexity.GHReduction.dependentRandomTableAux_failure_le,
  CutQueryComplexity.GHReduction.dependentRandomTable,
  CutQueryComplexity.GHReduction.dependentRandomTable_entry_support,
  CutQueryComplexity.GHReduction.dependentRandomTable_cost,
  CutQueryComplexity.GHReduction.dependentRandomTable_failure_le,
  CutQueryComplexity.GHReduction.dependentRandomTableAux_expect_entry,
  CutQueryComplexity.GHReduction.dependentRandomTable_expect_entry,
  CutQueryComplexity.GHReduction.truncate_expect_zero_le,
  CutQueryComplexity.GHReduction.random_bind_cost,
  CutQueryComplexity.GHReduction.random_map_cost,
  CutQueryComplexity.GHReduction.run_output_support,
  CutQueryComplexity.GHReduction.run_substitute_unit,
  CutQueryComplexity.GHReduction.contractProgram_run,
  CutQueryComplexity.GHReduction.contractProgram_graph_run,
  CutQueryComplexity.GHReduction.TranscriptOracle.AnswerPolicy,
  CutQueryComplexity.GHReduction.TranscriptOracle.run,
  CutQueryComplexity.GHReduction.TranscriptOracle.cost_le,
  CutQueryComplexity.GHReduction.TranscriptOracle.run_fixed,
  CutQueryComplexity.GHReduction.TranscriptOracle.deterministic_cost_le,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.combinedQueries,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.coefficient,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.coefficient_pos,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.one_le_sqrt,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.rootThreshold_parameters,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.splitTolerance_pos,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.splitTolerance_le_one,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.minimumDegreeBaseBudget_le_sqrt_add_one,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.minimumDegreeBaseBudget_le_sqrt,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.minimumWitness_le_sqrt,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.logWidth_power_five_ge_one,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.logWidth_power_four_le_five,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.minimumWitness_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.lowSchedule_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.highSchedule_le_logWidth,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.combinedQueries_le,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.concreteSum_le,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.exists_combined_constant,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.combinedQueries_eq_routine_lengths,
  CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.routine_lengths_le,
  CutQueryComplexity.GHReduction.stValue_approximation,
  CutQueryComplexity.GHReduction.cut_zero_iff_of_approximation,
  CutQueryComplexity.GHReduction.cut_component_zero,
  CutQueryComplexity.GHReduction.reachable_iff_of_approximation,
  CutQueryComplexity.GHReduction.stValue_pos_of_reachable,
  CutQueryComplexity.GHReduction.stValue_zero_of_not_reachable,
  CutQueryComplexity.GHReduction.terminalMin_pos_of_connected,
  CutQueryComplexity.GHReduction.le_terminalMin_of_source,
  CutQueryComplexity.GHReduction.bucketThreshold,
  CutQueryComplexity.GHReduction.bucketCount,
  CutQueryComplexity.GHReduction.bucketThreshold_pos,
  CutQueryComplexity.GHReduction.bucketThreshold_succ,
  CutQueryComplexity.GHReduction.bucketThreshold_mono,
  CutQueryComplexity.GHReduction.bucketThreshold_last,
  CutQueryComplexity.GHReduction.exists_bucket_index,
  CutQueryComplexity.GHReduction.sourceBucket,
  CutQueryComplexity.GHReduction.bucketTerminals,
  CutQueryComplexity.GHReduction.sourceBucket_excludes,
  CutQueryComplexity.GHReduction.sourceBuckets_disjoint,
  CutQueryComplexity.GHReduction.bucketTerminals_two_le,
  CutQueryComplexity.GHReduction.bucketTerminals_pos,
  CutQueryComplexity.GHReduction.stValue_approximation_fixed,
  CutQueryComplexity.GHReduction.sourceBucket_coverage,
  CutQueryComplexity.GHReduction.sourceBucket_small_minCut,
  CutQueryComplexity.GHReduction.componentLift,
  CutQueryComplexity.GHReduction.mem_componentLift,
  CutQueryComplexity.GHReduction.componentLift_subset,
  CutQueryComplexity.GHReduction.componentProject,
  CutQueryComplexity.GHReduction.mem_componentProject,
  CutQueryComplexity.GHReduction.componentLift_project,
  CutQueryComplexity.GHReduction.componentProject_lift,
  CutQueryComplexity.GHReduction.componentMap,
  CutQueryComplexity.GHReduction.componentMap_coe,
  CutQueryComplexity.GHReduction.componentMap_surjective,
  CutQueryComplexity.GHReduction.componentVertex_card,
  CutQueryComplexity.GHReduction.componentVertex_card_le,
  CutQueryComplexity.GHReduction.componentMap_pull,
  CutQueryComplexity.GHReduction.component_cut_inter_le,
  CutQueryComplexity.GHReduction.component_cut_union_le,
  CutQueryComplexity.GHReduction.component_cut_add_outside,
  CutQueryComplexity.GHReduction.component_contract_cut,
  CutQueryComplexity.GHReduction.component_contraction_promise,
  CutQueryComplexity.GHReduction.component_project_cut_le,
  CutQueryComplexity.GHReduction.component_minCut_lift,
  CutQueryComplexity.GHReduction.component_minCut_project,
  CutQueryComplexity.GHReduction.component_canonical_lift,
  CutQueryComplexity.GHReduction.componentSTProgram,
  CutQueryComplexity.GHReduction.componentSTProgram_correct,
  CutQueryComplexity.GHReduction.componentSTProgram_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.even_clone,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.sum_fakeDegrees,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.completed_edge_budget,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.completed_source_cap,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.completed_prune_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.nodeProg_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.nodeProg_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.cappedNode_eval,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.partNode_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.partNode_eval,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.partNode_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.partNode_linear_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.shrinkStep_mono_child,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.shrinkStep_zero,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State.mass_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.run_cost_work,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.run_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.program_eval,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.small_leaf_additive,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.liftShore_sdiff,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.partGraph_localCut,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.pruned_leaf_additive,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.splitGuard_of_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.pruneGuard_of_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.split_cross_of_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.prune_cross_of_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State.finish_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State.join_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.run_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.decomposition_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.disjoint_parts,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.partition_expands,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.SplitTree.partition_boundary_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.representative_mem,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.representative_eq_of_part_eq,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.part_representative,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.representative_idempotent,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.representative_fiber,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.representative_fiber_empty,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.representative_cut_sum,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State.representativeMap_idempotent,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State.representativeMap_additive,
  CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.State.representativeMap_boundary,
  CutQueryComplexity.GHReduction.frontierRepresentative,
  CutQueryComplexity.GHReduction.frontierRepresentative_section,
  CutQueryComplexity.GHReduction.frontierRepresentative_protected,
  CutQueryComplexity.GHReduction.frontier_minCut_lift,
  CutQueryComplexity.GHReduction.frontier_stValue,
  CutQueryComplexity.GHReduction.frontierSTProgram,
  CutQueryComplexity.GHReduction.frontierSTProgram_correct,
  CutQueryComplexity.GHReduction.frontierSTProgram_cost,
  CutQueryComplexity.GHReduction.RoundBlock,
  CutQueryComplexity.GHReduction.roundBlockFintype,
  CutQueryComplexity.GHReduction.roundBlockDecidableEq,
  CutQueryComplexity.GHReduction.roundBlockMap,
  CutQueryComplexity.GHReduction.roundBlockParent,
  CutQueryComplexity.GHReduction.roundBlockParent_map,
  CutQueryComplexity.GHReduction.roundBlockMap_of_fiber,
  CutQueryComplexity.GHReduction.roundBlockMap_residual_iff,
  CutQueryComplexity.GHReduction.roundBlockMap_child_iff,
  CutQueryComplexity.GHReduction.roundBlockMap_residual_fiber,
  CutQueryComplexity.GHReduction.roundBlockMap_child_fiber,
  CutQueryComplexity.GHReduction.roundBlockMap_fiber_subset,
  CutQueryComplexity.GHReduction.roundBlock_old_shore_pull,
  CutQueryComplexity.GHReduction.roundBlockMap_surjective,
  CutQueryComplexity.GHReduction.roundBlock_card,
  CutQueryComplexity.GHReduction.roundOldEdge,
  CutQueryComplexity.GHReduction.roundStarEdge,
  CutQueryComplexity.GHReduction.roundEdges,
  CutQueryComplexity.GHReduction.roundOldEdge_mem,
  CutQueryComplexity.GHReduction.roundStarEdge_mem,
  CutQueryComplexity.GHReduction.roundOldEdge_injective,
  CutQueryComplexity.GHReduction.roundStarEdge_injective,
  CutQueryComplexity.GHReduction.roundEdge_parts_disjoint,
  CutQueryComplexity.GHReduction.roundEdges_card,
  CutQueryComplexity.GHReduction.roundEdges_spans,
  CutQueryComplexity.GHReduction.roundBlockTree,
  CutQueryComplexity.GHReduction.roundBlock_frontier_sizes,
  CutQueryComplexity.GHReduction.SteinerCutTree,
  CutQueryComplexity.GHReduction.SteinerCutTree.terminal_injective,
  CutQueryComplexity.GHReduction.IsSteinerCutTree,
  CutQueryComplexity.GHReduction.terminalTrace,
  CutQueryComplexity.GHReduction.mem_terminalTrace,
  CutQueryComplexity.GHReduction.steinerPathShore,
  CutQueryComplexity.GHReduction.steinerPathShore_separates,
  CutQueryComplexity.GHReduction.cut_steinerPathShore,
  CutQueryComplexity.GHReduction.steiner_weight_le_crossing_cut,
  CutQueryComplexity.GHReduction.steinerTree_allPairs,
  CutQueryComplexity.GHReduction.CutTree.asSteiner,
  CutQueryComplexity.GHReduction.pull_id_shore,
  CutQueryComplexity.GHReduction.cutTree_asSteiner_correct,
  CutQueryComplexity.GHReduction.guideBaseGlobalBudget,
  CutQueryComplexity.GHReduction.guideBaseValueTree,
  CutQueryComplexity.GHReduction.guideBaseValueTree_eval,
  CutQueryComplexity.GHReduction.GuideNodeOutput,
  CutQueryComplexity.GHReduction.guideNodeProgram,
  CutQueryComplexity.GHReduction.guideNodeBudget,
  CutQueryComplexity.GHReduction.guideNodeProgram_cost_scaled,
  CutQueryComplexity.GHReduction.guideNodeTree,
  CutQueryComplexity.GHReduction.guideNodeTree_eval,
  CutQueryComplexity.GHReduction.guideSwitchBudget,
  CutQueryComplexity.GHReduction.guideSourceBranchTree,
  CutQueryComplexity.GHReduction.guideTwoCombine,
  CutQueryComplexity.GHReduction.guideTwoCombine_above,
  CutQueryComplexity.GHReduction.guideParts_card_le,
  CutQueryComplexity.GHReduction.guideTwoBudget,
  CutQueryComplexity.GHReduction.guideTwoTree,
  CutQueryComplexity.GHReduction.GuideTwoSuccess,
  CutQueryComplexity.GHReduction.HasPruningWitness,
  CutQueryComplexity.GHReduction.PruningSuccess,
  CutQueryComplexity.GHReduction.guidePruneTrialsTree_simultaneous,
  CutQueryComplexity.GHReduction.SourceBranchSuccess,
  CutQueryComplexity.GHReduction.SourceBranchSuccess.above,
  CutQueryComplexity.GHReduction.guideSourceBranchTree_failure_le,
  CutQueryComplexity.GHReduction.GuideChildSuccess,
  CutQueryComplexity.GHReduction.guideChildSuccess_of_child,
  CutQueryComplexity.GHReduction.guideTwoCombine_success,
  CutQueryComplexity.GHReduction.guideTwoChildTree,
  CutQueryComplexity.GHReduction.guideTwoChildTree_eval,
  CutQueryComplexity.GHReduction.guideTwoTree_step,
  CutQueryComplexity.GHReduction.guideTwoChildTree_failure_le,
  CutQueryComplexity.GHReduction.guideTwoTree_step_failure_le,
  CutQueryComplexity.GHReduction.guide_two_error_recurrence,
  CutQueryComplexity.GHReduction.guideTwoError,
  CutQueryComplexity.GHReduction.guideBaseValueTree_success,
  CutQueryComplexity.GHReduction.guideTwoTree_failure_le,
  CutQueryComplexity.GHReduction.guideTwoTree_clog_failure_le,
  CutQueryComplexity.GHReduction.guidePruneTree_cost_scaled,
  CutQueryComplexity.GHReduction.guidePruneTrialsTree_cost_scaled,
  CutQueryComplexity.GHReduction.sourceSwitchGlobalTree_cost_scaled,
  CutQueryComplexity.GHReduction.guideSwitchContinuation_cost_scaled,
  CutQueryComplexity.GHReduction.guideSwitchTree_cost_scaled,
  CutQueryComplexity.GHReduction.guideSourceBranchTree_cost_scaled,
  CutQueryComplexity.GHReduction.guideNodeTree_run,
  CutQueryComplexity.GHReduction.guideBaseValueTree_cost_scaled,
  CutQueryComplexity.GHReduction.guideTwoNodeCost,
  CutQueryComplexity.GHReduction.guideTwoTailTree,
  CutQueryComplexity.GHReduction.guideTwoTree_step_run,
  CutQueryComplexity.GHReduction.guideTwoTailTree_cost_scaled,
  CutQueryComplexity.GHReduction.guideTwoTree_step_cost_scaled,
  CutQueryComplexity.GHReduction.guide_two_cost_recurrence,
  CutQueryComplexity.GHReduction.guideTwoTree_cost_scaled,
  CutQueryComplexity.GHReduction.guideTwoSharpBudget,
  CutQueryComplexity.GHReduction.guideTwoTree_cost_linear,
  CutQueryComplexity.GHReduction.guideTwoTree_cost_le_sharp,
  CutQueryComplexity.GHReduction.guideTwoCappedTree,
  CutQueryComplexity.GHReduction.guideTwoCappedTree_failure_le,
  CutQueryComplexity.GHReduction.guideTwoValueTree,
  CutQueryComplexity.GHReduction.guideTwoValueTree_failure_le,
  CutQueryComplexity.StarContraction2022.Quantum.Global.singleton_realizes,
  CutQueryComplexity.StarContraction2022.Quantum.Global.low_realizes,
  CutQueryComplexity.StarContraction2022.Quantum.Global.high_realizes,
  CutQueryComplexity.StarContraction2022.Quantum.Global.component_realizes,
  CutQueryComplexity.StarContraction2022.Quantum.Global.sum_componentQueries,
  CutQueryComplexity.StarContraction2022.Quantum.Global.joint_realizes,
  CutQueryComplexity.StarContraction2022.Quantum.Global.global_realizes,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalAlg_law,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalRoutine_len,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalRoutine_exact_schedule,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalRoutine_state,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalRoutine_normalized,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalRoutine_event_law,
  CutQueryComplexity.StarContraction2022.Quantum.Global.global_small,
  CutQueryComplexity.StarContraction2022.Quantum.Global.eventMass_nonneg,
  CutQueryComplexity.StarContraction2022.Quantum.Global.le_eventMass,
  CutQueryComplexity.StarContraction2022.Quantum.Global.eventMass_congr_event,
  CutQueryComplexity.StarContraction2022.Quantum.Global.eventMass_compl,
  CutQueryComplexity.StarContraction2022.Quantum.Global.eventMass_mono_support,
  CutQueryComplexity.StarContraction2022.Quantum.Global.eventMass_fibre,
  CutQueryComplexity.StarContraction2022.Quantum.Global.positive_fibre,
  CutQueryComplexity.StarContraction2022.Quantum.Global.eventMass_product,
  CutQueryComplexity.StarContraction2022.Quantum.Global.eventMass_coordinate,
  CutQueryComplexity.StarContraction2022.Quantum.Global.realizes_sum,
  CutQueryComplexity.StarContraction2022.Quantum.Global.component_nonneg,
  CutQueryComplexity.StarContraction2022.Quantum.Global.component_sum,
  CutQueryComplexity.StarContraction2022.Quantum.Global.chooseCandidate_mem,
  CutQueryComplexity.StarContraction2022.Quantum.Global.chooseCandidate_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Global.chooseCandidate_le_left,
  CutQueryComplexity.StarContraction2022.Quantum.Global.chooseCandidate_le_right,
  CutQueryComplexity.StarContraction2022.Quantum.Global.bestList_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Global.bestList_le_mem,
  CutQueryComplexity.StarContraction2022.Quantum.Global.minimum_of_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Global.selectCandidate_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Global.selectCandidate_minimum,
  CutQueryComplexity.StarContraction2022.Quantum.Global.singleton_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Global.tree_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Global.component_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Global.joint_supported,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalAlg_sound,
  CutQueryComplexity.StarContraction2022.Quantum.Global.global_event_joint,
  CutQueryComplexity.StarContraction2022.Quantum.Global.singleton_event,
  CutQueryComplexity.StarContraction2022.Quantum.Global.selected_failure_coordinate,
  CutQueryComplexity.StarContraction2022.Quantum.Global.joint_event_factorization,
  CutQueryComplexity.StarContraction2022.Quantum.Global.joint_high_failure,
  CutQueryComplexity.StarContraction2022.Quantum.Global.selected_failure_high,
  CutQueryComplexity.StarContraction2022.Quantum.Global.high_minimum_is_low,
  CutQueryComplexity.StarContraction2022.Quantum.Global.singleton_success,
  CutQueryComplexity.StarContraction2022.Quantum.Global.low_success,
  CutQueryComplexity.StarContraction2022.Quantum.Global.high_success,
  CutQueryComplexity.StarContraction2022.Quantum.Global.graph_cases,
  CutQueryComplexity.StarContraction2022.Quantum.Global.joint_conditional_high,
  CutQueryComplexity.StarContraction2022.Quantum.Global.global_success_of_errors,
  CutQueryComplexity.StarContraction2022.Quantum.Global.exists_public_high_trials,
  CutQueryComplexity.StarContraction2022.Quantum.Global.publicHighTrials_error,
  CutQueryComplexity.StarContraction2022.Quantum.Global.public_singleton_error,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalRoutine_public_success,
  CutQueryComplexity.StarContraction2022.Quantum.Global.exists_public_global_program,
  CutQueryComplexity.GHReduction.relabelRootedTree,
  CutQueryComplexity.GHReduction.relabelRootedTree_iterate,
  CutQueryComplexity.GHReduction.relabelRootedTree_ancestor,
  CutQueryComplexity.GHReduction.relabelRootedTree_subtree,
  CutQueryComplexity.GHReduction.SteinerCutTree.terminal_attach,
  CutQueryComplexity.GHReduction.SteinerCutTree.terminalEquiv,
  CutQueryComplexity.GHReduction.SteinerCutTree.terminalEquiv_apply,
  CutQueryComplexity.GHReduction.SteinerCutTree.terminalEquiv_symm,
  CutQueryComplexity.GHReduction.completeSteinerTree,
  CutQueryComplexity.GHReduction.completeSteinerTree_subtree,
  CutQueryComplexity.GHReduction.completeSteinerTree_correct,
  CutQueryComplexity.GHReduction.completeSteinerTree_allPairs,
  CutQueryComplexity.GHReduction.completeSteinerTreeAnswer,
  CutQueryComplexity.GHReduction.completeSteinerTreeAnswerProgram,
  CutQueryComplexity.GHReduction.completeSteinerTreeAnswerProgram_run,
  CutQueryComplexity.GHReduction.completeSteinerTreeAnswerProgram_eval,
  CutQueryComplexity.GHReduction.completeSteinerTreeAnswer_correct,
  CutQueryComplexity.GHReduction.completeSteinerTreeAnswerProgram_correct,
  CutQueryComplexity.GHReduction.completeSteinerTree_public_decoder,
  CutQueryComplexity.StarContraction2022.Quantum.Global.native_schedule_matches,
  CutQueryComplexity.StarContraction2022.Quantum.Global.native_schedule_all,
  CutQueryComplexity.StarContraction2022.Quantum.Global.logFiveCoefficient,
  CutQueryComplexity.StarContraction2022.Quantum.Global.logFiveCoefficient_eq,
  CutQueryComplexity.StarContraction2022.Quantum.Global.logFiveCoefficient_pos,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalRoutine_logFive_cost,
  CutQueryComplexity.StarContraction2022.Quantum.Global.public_candidate_truthful,
  CutQueryComplexity.StarContraction2022.Quantum.Global.public_minimum_shore_value,
  CutQueryComplexity.StarContraction2022.Quantum.Global.public_tiny_input,
  CutQueryComplexity.StarContraction2022.Quantum.Global.public_log_five_endpoint,
  CutQueryComplexity.StarContraction2022.Quantum.Global.pow_logWidth_le_square,
  CutQueryComplexity.StarContraction2022.Quantum.Global.logWidth_le_four_log,
  CutQueryComplexity.StarContraction2022.Quantum.Global.naturalLogCoefficient,
  CutQueryComplexity.StarContraction2022.Quantum.Global.naturalLogCoefficient_pos,
  CutQueryComplexity.StarContraction2022.Quantum.Global.globalRoutine_naturalLog_cost,
  CutQueryComplexity.StarContraction2022.Quantum.Global.public_natural_log_five_endpoint,
  CutQueryComplexity.StarContraction2022.Quantum.Global.exists_public_endpoint,
  CutQueryComplexity.GHReduction.terminalGuide,
  CutQueryComplexity.GHReduction.terminalGuide_source,
  CutQueryComplexity.GHReduction.terminalGuide_real_card,
  CutQueryComplexity.GHReduction.terminalGuide_realVertices,
  CutQueryComplexity.GHReduction.terminalGuide_respects,
  CutQueryComplexity.GHReduction.guideListEntry,
  CutQueryComplexity.GHReduction.guideListEntry_mem,
  CutQueryComplexity.GHReduction.exists_guideListEntry,
  CutQueryComplexity.GHReduction.mergeGuideValues,
  CutQueryComplexity.GHReduction.sampledGuideContinuation,
  CutQueryComplexity.GHReduction.sampledGuideTree,
  CutQueryComplexity.GHReduction.SourceValuesSuccess,
  CutQueryComplexity.GHReduction.GuideListCoverage,
  CutQueryComplexity.GHReduction.mergeGuideValues_success,
  CutQueryComplexity.GHReduction.guideSampleProgram_source_coverage,
  CutQueryComplexity.GHReduction.sampledGuideContinuation_failure_le,
  CutQueryComplexity.GHReduction.sampledGuideTree_failure_le,
  CutQueryComplexity.GHReduction.bucketTerminals_subset,
  CutQueryComplexity.GHReduction.bucketTerminals_erase,
  CutQueryComplexity.GHReduction.bucketSourceTree,
  CutQueryComplexity.GHReduction.zeroSourceEstimate,
  CutQueryComplexity.GHReduction.mergeBucketValues,
  CutQueryComplexity.GHReduction.singleSourceBudget,
  CutQueryComplexity.GHReduction.singleSourceTree,
  CutQueryComplexity.GHReduction.BucketSourceSuccess,
  CutQueryComplexity.GHReduction.BucketSourceSuccess.above,
  CutQueryComplexity.GHReduction.zeroSourceEstimate_above,
  CutQueryComplexity.GHReduction.mergeBucketValues_success,
  CutQueryComplexity.GHReduction.guideTwoError_mono_real,
  CutQueryComplexity.GHReduction.singleSourceError,
  CutQueryComplexity.GHReduction.bucketSourceTree_failure_le,
  CutQueryComplexity.GHReduction.singleSourceTree_failure_le,
  CutQueryComplexity.GHReduction.sampledGuideContinuation_cost_scaled,
  CutQueryComplexity.GHReduction.sampledGuideTree_cost_scaled,
  CutQueryComplexity.GHReduction.bucketSourceTree_cost_scaled,
  CutQueryComplexity.GHReduction.singleSourceSharpBudget,
  CutQueryComplexity.GHReduction.singleSourceTree_cost_scaled,
  CutQueryComplexity.GHReduction.singleSourceCappedTree,
  CutQueryComplexity.GHReduction.singleSourceCappedTree_failure_le,
  CutQueryComplexity.GHReduction.SteinerCutTree.lift,
  CutQueryComplexity.GHReduction.SteinerCutTree.lift_correct,
  CutQueryComplexity.GHReduction.steiner_attachment_cut_lower,
  CutQueryComplexity.GHReduction.steiner_attachment_agrees_of_cheaper,
  CutQueryComplexity.GHReduction.steiner_bridge_minCut,
  CutQueryComplexity.GHReduction.EdgeShoreSystem,
  CutQueryComplexity.GHReduction.tree_parent_not_mem_subtree,
  CutQueryComplexity.GHReduction.selectedParentEdge,
  CutQueryComplexity.GHReduction.selectedParentEdge_endpoints,
  CutQueryComplexity.GHReduction.selectedParentEdge_mem,
  CutQueryComplexity.GHReduction.selectedParentEdge_identifies,
  CutQueryComplexity.GHReduction.edgeShore_crossSet_singleton,
  CutQueryComplexity.GHReduction.edgeShore_fundamental,
  CutQueryComplexity.GHReduction.assembleCutTree,
  CutQueryComplexity.GHReduction.assembleSteinerTree,
  CutQueryComplexity.GHReduction.stMinCut_reorient,
  CutQueryComplexity.GHReduction.assembleSteinerTree_correct,
  CutQueryComplexity.GHReduction.subtree_parent_cross_iff,
  CutQueryComplexity.GHReduction.rooted_parent_membership_constant,
  CutQueryComplexity.GHReduction.joinedEdges,
  CutQueryComplexity.GHReduction.mem_joinedEdges_ll,
  CutQueryComplexity.GHReduction.mem_joinedEdges_rr,
  CutQueryComplexity.GHReduction.mem_joinedEdges_lr,
  CutQueryComplexity.GHReduction.not_mem_joinedEdges_rl,
  CutQueryComplexity.GHReduction.joinedEdges_spans,
  CutQueryComplexity.GHReduction.leftExtension,
  CutQueryComplexity.GHReduction.rightExtension,
  CutQueryComplexity.GHReduction.leftHalf,
  CutQueryComplexity.GHReduction.mem_leftExtension_inl,
  CutQueryComplexity.GHReduction.mem_leftExtension_inr,
  CutQueryComplexity.GHReduction.mem_rightExtension_inl,
  CutQueryComplexity.GHReduction.mem_rightExtension_inr,
  CutQueryComplexity.GHReduction.mem_leftHalf_inl,
  CutQueryComplexity.GHReduction.not_mem_leftHalf_inr,
  CutQueryComplexity.GHReduction.joinedShore,
  CutQueryComplexity.GHReduction.joinedShore_system,
  CutQueryComplexity.GHReduction.joinedAttach,
  CutQueryComplexity.GHReduction.joinedTerminal,
  CutQueryComplexity.GHReduction.joinedAttach_terminal,
  CutQueryComplexity.GHReduction.pull_joinedAttach_left,
  CutQueryComplexity.GHReduction.pull_joinedAttach_right,
  CutQueryComplexity.GHReduction.pull_joinedAttach_half,
  CutQueryComplexity.GHReduction.joinedWeight,
  CutQueryComplexity.GHReduction.joinSteinerTrees,
  CutQueryComplexity.GHReduction.joinSteinerTrees_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.minimumDegreeProgram_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_correct,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_cost,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.search_logs_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.decomposition_budget_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.recovery_edgeCap_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.recovery_budget_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.coreBudget_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.cubeRoot_cube_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.padded_root_fifth_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.sizeLog_padded_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.headlineConstant_pos,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget_le,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget_bound,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.sizeLog_le_log,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.sizeLog_isBigO_log,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.sizeLog_fifth_isLittleO_third,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.headline_isLittleO_square,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget_isBigO_headline,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget_isLittleO_square,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_exact,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program_cost_bound,
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.deterministic_allPairs,
  CutQueryComplexity.GHReduction.OuterPivot.Batch,
  CutQueryComplexity.GHReduction.OuterPivot.Batch.empty,
  CutQueryComplexity.GHReduction.OuterPivot.Batch.covered,
  CutQueryComplexity.GHReduction.OuterPivot.Batch.mem_covered,
  CutQueryComplexity.GHReduction.OuterPivot.Batch.empty_covered,
  CutQueryComplexity.GHReduction.OuterPivot.Batch.covered_subset,
  CutQueryComplexity.GHReduction.OuterPivot.WellFormed,
  CutQueryComplexity.GHReduction.OuterPivot.empty_wellFormed,
  CutQueryComplexity.GHReduction.OuterPivot.WellFormed.source_not_covered,
  CutQueryComplexity.GHReduction.OuterPivot.acceptedCut,
  CutQueryComplexity.GHReduction.OuterPivot.extendCuts,
  CutQueryComplexity.GHReduction.OuterPivot.extendCuts_mem,
  CutQueryComplexity.GHReduction.OuterPivot.DisjointCuts,
  CutQueryComplexity.GHReduction.OuterPivot.rawBatch,
  CutQueryComplexity.GHReduction.OuterPivot.prepareBatch,
  CutQueryComplexity.GHReduction.OuterPivot.rawBatch_wellFormed,
  CutQueryComplexity.GHReduction.OuterPivot.prepareBatch_wellFormed,
  CutQueryComplexity.GHReduction.OuterPivot.prepareBatch_correct,
  CutQueryComplexity.GHReduction.OuterPivot.levelProgram,
  CutQueryComplexity.GHReduction.OuterPivot.levelProgram_wellFormed,
  CutQueryComplexity.GHReduction.OuterPivot.levelProgram_correct,
  CutQueryComplexity.GHReduction.OuterPivot.isolatingValues_disjoint,
  CutQueryComplexity.GHReduction.OuterPivot.levelProgram_hit,
  CutQueryComplexity.GHReduction.OuterPivot.Output,
  CutQueryComplexity.GHReduction.OuterPivot.bestLevel,
  CutQueryComplexity.GHReduction.OuterPivot.bestLevel_max,
  CutQueryComplexity.GHReduction.OuterPivot.selectLevel,
  CutQueryComplexity.GHReduction.OuterPivot.stepProgram,
  CutQueryComplexity.GHReduction.OuterPivot.stepProgram_eval,
  CutQueryComplexity.GHReduction.OuterPivot.stepProgram_wellFormed,
  CutQueryComplexity.GHReduction.OuterPivot.stepProgram_correct,
  CutQueryComplexity.GHReduction.OuterPivot.level_coverage_le_step,
  CutQueryComplexity.GHReduction.OuterPivot.levelProgram_cost_scaled,
  CutQueryComplexity.GHReduction.OuterPivot.stepProgram_cost_scaled,
  CutQueryComplexity.GHReduction.OuterPivot.stepBudget,
  CutQueryComplexity.GHReduction.OuterPivot.stepProgram_cost,
  CutQueryComplexity.GHReduction.OuterPivot.stepTree,
  CutQueryComplexity.GHReduction.OuterPivot.stepTree_eval,
  CutQueryComplexity.GHReduction.OuterPivot.Output.empty,
  CutQueryComplexity.GHReduction.OuterPivot.randomStepTree,
  CutQueryComplexity.GHReduction.OuterPivot.randomStepTree_eval,
  CutQueryComplexity.GHReduction.OuterPivot.randomStepTree_correct,
  CutQueryComplexity.GHReduction.OuterPivot.successfulTargets_charge_level,
  CutQueryComplexity.GHReduction.OuterPivot.stepProgram_charge,
  CutQueryComplexity.GHReduction.OuterPivot.stepProgram_expected_progress,
  CutQueryComplexity.GHReduction.OuterPivot.balanced_expected_progress,
  CutQueryComplexity.GHReduction.OuterPivot.randomStepTree_expected_progress,
  CutQueryComplexity.GHReduction.OuterPivot.pivotOutputLaw,
  CutQueryComplexity.GHReduction.OuterPivot.pivot_expected_removal,
  CutQueryComplexity.GHReduction.OuterPivot.removalDenominator,
  CutQueryComplexity.GHReduction.OuterPivot.pivot_expected_removal_literal,
  CutQueryComplexity.GHReduction.OuterPivot.excess,
  CutQueryComplexity.GHReduction.OuterPivot.remaining,
  CutQueryComplexity.GHReduction.OuterPivot.remaining_subset,
  CutQueryComplexity.GHReduction.OuterPivot.source_mem_remaining,
  CutQueryComplexity.GHReduction.OuterPivot.remaining_accounting,
  CutQueryComplexity.GHReduction.OuterPivot.step_small_child,
  CutQueryComplexity.GHReduction.OuterPivot.pivotOutputLaw_wellFormed,
  CutQueryComplexity.GHReduction.OuterPivot.removalDenominator_pos,
  CutQueryComplexity.GHReduction.OuterPivot.contractionRate,
  CutQueryComplexity.GHReduction.OuterPivot.contractionRate_arg_nonneg,
  CutQueryComplexity.GHReduction.OuterPivot.contractionRate_le_one,
  CutQueryComplexity.GHReduction.OuterPivot.pivot_expected_removal_real,
  CutQueryComplexity.GHReduction.OuterPivot.largeChild_expected_excess,
  CutQueryComplexity.GHReduction.OuterPivot.remainingLaw,
  CutQueryComplexity.GHReduction.OuterPivot.remainingLaw_expected_excess,
  CutQueryComplexity.GHReduction.OuterPivot.fuelChain,
  CutQueryComplexity.GHReduction.OuterPivot.fuelChain_zero,
  CutQueryComplexity.GHReduction.OuterPivot.fuelChain_succ,
  CutQueryComplexity.GHReduction.OuterPivot.fuelChain_self_loop_consumes,
  CutQueryComplexity.GHReduction.OuterPivot.fuelChain_expected_of_conditional,
  CutQueryComplexity.GHReduction.OuterPivot.fuelChain_depth_tail,
  CutQueryComplexity.GHReduction.OuterPivot.contractionRate_pow_le_exp,
  CutQueryComplexity.GHReduction.OuterPivot.fuelChain_exp_depth_tail,
  CutQueryComplexity.GHReduction.OuterPivot.depthFuel,
  CutQueryComplexity.GHReduction.OuterPivot.depthFuel_error_le,
  CutQueryComplexity.GHReduction.OuterPivot.fuelChain_depthFuel_tail,
  CutQueryComplexity.GHReduction.OuterPivot.Batch.accepted,
  CutQueryComplexity.GHReduction.OuterPivot.Batch.shore,
  CutQueryComplexity.GHReduction.OuterPivot.Batch.value,
  CutQueryComplexity.GHReduction.OuterPivot.WellFormed.indices,
  CutQueryComplexity.GHReduction.OuterPivot.WellFormed.contains,
  CutQueryComplexity.GHReduction.OuterPivot.WellFormed.excludes,
  CutQueryComplexity.GHReduction.OuterPivot.WellFormed.small,
  CutQueryComplexity.GHReduction.OuterPivot.WellFormed.matches,
  CutQueryComplexity.GHReduction.OuterPivot.WellFormed.disjoint,
  CutQueryComplexity.GHReduction.OuterPivot.Output.level,
  CutQueryComplexity.GHReduction.OuterPivot.Output.batch,
  CutQueryComplexity.GHReduction.relabelSteinerTree,
  CutQueryComplexity.GHReduction.relabelSteinerTree_terminal,
  CutQueryComplexity.GHReduction.relabelSteinerTree_shore,
  CutQueryComplexity.GHReduction.relabelSteinerTree_correct,
  CutQueryComplexity.GHReduction.PackedSteinerTree,
  CutQueryComplexity.GHReduction.packSteinerTree,
  CutQueryComplexity.GHReduction.packSteinerTree_correct,
  CutQueryComplexity.GHReduction.singletonSteinerOutput,
  CutQueryComplexity.GHReduction.singletonSteinerOutput_correct,
  CutQueryComplexity.GHReduction.SteinerJoinGuard,
  CutQueryComplexity.GHReduction.checkedSteinerJoin,
  CutQueryComplexity.GHReduction.checkedSteinerJoin_correct,
  CutQueryComplexity.GHReduction.SteinerAssemblyStep,
  CutQueryComplexity.GHReduction.SteinerAssemblyStep.Correct,
  CutQueryComplexity.GHReduction.assembleSteinerSteps,
  CutQueryComplexity.GHReduction.assembleSteinerSteps_correct,
  CutQueryComplexity.GHReduction.finishSteinerAssembly,
  CutQueryComplexity.GHReduction.finishSteinerAssembly_correct,
  CutQueryComplexity.GHReduction.assembleSteinerProgram,
  CutQueryComplexity.GHReduction.assembleSteinerProgram_eval,
  CutQueryComplexity.GHReduction.assembleSteinerProgram_cost,
  CutQueryComplexity.GHReduction.finishSteinerProgram,
  CutQueryComplexity.GHReduction.finishSteinerProgram_eval,
  CutQueryComplexity.GHReduction.finishSteinerProgram_cost,
  CutQueryComplexity.GHReduction.Represents,
  CutQueryComplexity.GHReduction.packSteinerTree_represents,
  CutQueryComplexity.GHReduction.packSteinerTree_attach_eq,
  CutQueryComplexity.GHReduction.checkedSteinerJoin_exists,
  CutQueryComplexity.GHReduction.checkedSteinerJoin_represents,
  CutQueryComplexity.GHReduction.checkedSteinerJoin_attach_left,
  CutQueryComplexity.GHReduction.checkedSteinerJoin_attach_right,
  CutQueryComplexity.GHReduction.starAssemblySteps,
  CutQueryComplexity.GHReduction.assembleDisjointStar,
  CutQueryComplexity.GHReduction.assembleDisjointStar_success,
  CutQueryComplexity.GHReduction.SourcePivotOutput,
  CutQueryComplexity.GHReduction.sourcePivotBudget,
  CutQueryComplexity.GHReduction.sourcePivotFor,
  CutQueryComplexity.GHReduction.sourcePivotTree,
  CutQueryComplexity.GHReduction.sourcePivotFor_eval,
  CutQueryComplexity.GHReduction.sourcePivotTree_eval,
  CutQueryComplexity.GHReduction.sourcePivotTree_support,
  CutQueryComplexity.GHReduction.SourcePivotGood,
  CutQueryComplexity.GHReduction.sourcePivot_good_of_values,
  CutQueryComplexity.GHReduction.sourcePivotFor_failure_le,
  CutQueryComplexity.GHReduction.sourcePivotTree_failure_le,
  CutQueryComplexity.GHReduction.randomStepTree_run,
  CutQueryComplexity.GHReduction.randomStepTree_cost_scaled,
  CutQueryComplexity.GHReduction.sourcePivotSharpBudget,
  CutQueryComplexity.GHReduction.sourcePivotFor_cost_scaled,
  CutQueryComplexity.GHReduction.sourcePivotTree_cost_scaled,
  CutQueryComplexity.GHReduction.sourcePivotPotential,
  CutQueryComplexity.GHReduction.sourcePivotPotential_of_good,
  CutQueryComplexity.GHReduction.sourcePivotPotential_le,
  CutQueryComplexity.GHReduction.randomStep_sourcePotential_charge,
  CutQueryComplexity.GHReduction.sourcePivotFor_potential_charge,
  CutQueryComplexity.GHReduction.sourcePivotTree_potential_charge,
  CutQueryComplexity.GHReduction.sourcePivotTree_expected_potential,
  CutQueryComplexity.GHReduction.trackedPivotChild,
  CutQueryComplexity.GHReduction.trackedPivotChild_subset,
  CutQueryComplexity.GHReduction.trackedPivotChild_excess_le,
  CutQueryComplexity.GHReduction.trackedPivotChild_residual_bound,
  CutQueryComplexity.GHReduction.mem_trackedPivotChild,
  CutQueryComplexity.GHReduction.trackedPivotPotential,
  CutQueryComplexity.GHReduction.trackedPivotPotential_le,
  CutQueryComplexity.GHReduction.trackedPivotPotential_of_good,
  CutQueryComplexity.GHReduction.sourcePivotTree_tracked_residual_bound,
  CutQueryComplexity.GHReduction.sourcePivotTree_expected_tracked_potential,
  CutQueryComplexity.GHReduction.frontierTerminals,
  CutQueryComplexity.GHReduction.mem_frontierTerminals,
  CutQueryComplexity.GHReduction.frontierTerminals_card,
  CutQueryComplexity.GHReduction.frontierTerminals_nonempty,
  CutQueryComplexity.GHReduction.frontierPivotCall,
  CutQueryComplexity.GHReduction.FrontierPivotGood,
  CutQueryComplexity.GHReduction.frontierPivotCall_cost_scaled,
  CutQueryComplexity.GHReduction.frontierPivotCall_failure_le,
  CutQueryComplexity.GHReduction.frontierPivotRound,
  CutQueryComplexity.GHReduction.frontierPivotRound_entry_support,
  CutQueryComplexity.GHReduction.frontierPivotRound_cost_scaled,
  CutQueryComplexity.GHReduction.frontierPivotRound_cost,
  CutQueryComplexity.GHReduction.frontierPivotRound_failure_le,
  CutQueryComplexity.GHReduction.frontierPivotRoundCapped,
  CutQueryComplexity.GHReduction.frontierPivotRoundCapped_failure_le,
  CutQueryComplexity.GHReduction.PublicBlockSplit,
  CutQueryComplexity.GHReduction.ValidBlockSplit,
  CutQueryComplexity.GHReduction.emptyBlockSplit,
  CutQueryComplexity.GHReduction.emptyBlockSplit_valid,
  CutQueryComplexity.GHReduction.normalizeBlockSplit,
  CutQueryComplexity.GHReduction.normalizeBlockSplit_valid,
  CutQueryComplexity.GHReduction.normalizeBlockSplit_of_valid,
  CutQueryComplexity.GHReduction.blockRepresentative,
  CutQueryComplexity.GHReduction.blockRepresentative_mem,
  CutQueryComplexity.GHReduction.liftFrontierSplit,
  CutQueryComplexity.GHReduction.checkedFrontierSplit,
  CutQueryComplexity.GHReduction.checkedFrontierSplit_valid,
  CutQueryComplexity.GHReduction.PublicFrontierState,
  CutQueryComplexity.GHReduction.packFrontierState,
  CutQueryComplexity.GHReduction.initialFrontierState,
  CutQueryComplexity.GHReduction.PublicFrontierState.size_le,
  CutQueryComplexity.GHReduction.PublicFrontierState.frontier_sizes,
  CutQueryComplexity.GHReduction.advanceFrontierState,
  CutQueryComplexity.GHReduction.FrontierRoundRecord,
  CutQueryComplexity.GHReduction.FrontierRoundRecord.split,
  CutQueryComplexity.GHReduction.FrontierRoundRecord.split_valid,
  CutQueryComplexity.GHReduction.FrontierRoundRecord.after,
  CutQueryComplexity.GHReduction.FrontierRoundRecord.after_frontier_sizes,
  CutQueryComplexity.GHReduction.FrontierRoundRecord.Good,
  CutQueryComplexity.GHReduction.frontierRoundBudget,
  CutQueryComplexity.GHReduction.frontierStateStep,
  CutQueryComplexity.GHReduction.frontierStateStep_before,
  CutQueryComplexity.GHReduction.frontierStateStep_failure_le,
  CutQueryComplexity.GHReduction.FrontierTrace,
  CutQueryComplexity.GHReduction.FrontierTrace.Good,
  CutQueryComplexity.GHReduction.FrontierTrace.Follows,
  CutQueryComplexity.GHReduction.frontierExecution,
  CutQueryComplexity.GHReduction.frontierExecution_support,
  CutQueryComplexity.GHReduction.frontierExecution_cost,
  CutQueryComplexity.GHReduction.frontierExecution_failure_le,
  CutQueryComplexity.GHReduction.roundChildShore,
  CutQueryComplexity.GHReduction.mem_roundChildShore_same,
  CutQueryComplexity.GHReduction.mem_roundChildShore_other,
  CutQueryComplexity.GHReduction.roundOldEdge_child_membership,
  CutQueryComplexity.GHReduction.roundChildShore_edgeCut,
  CutQueryComplexity.GHReduction.roundOldShore_edgeCut,
  CutQueryComplexity.GHReduction.roundEdgeShore,
  CutQueryComplexity.GHReduction.roundEdgeShore_old,
  CutQueryComplexity.GHReduction.roundEdgeShore_star,
  CutQueryComplexity.GHReduction.roundEdgeShore_system,
  CutQueryComplexity.GHReduction.roundBlockTree_parent_adj,
  CutQueryComplexity.GHReduction.roundBlockTree_fundamental,
  CutQueryComplexity.GHReduction.refinementChildShore,
  CutQueryComplexity.GHReduction.mem_refinementChildShore_old,
  CutQueryComplexity.GHReduction.mem_refinementChildShore_new,
  CutQueryComplexity.GHReduction.refinedOldEdge_child_membership,
  CutQueryComplexity.GHReduction.refinementChildShore_edgeCut,
  CutQueryComplexity.GHReduction.refinedOldShore_edgeCut,
  CutQueryComplexity.GHReduction.refinedEdgeShore,
  CutQueryComplexity.GHReduction.refinedEdgeShore_old,
  CutQueryComplexity.GHReduction.refinedEdgeShore_star,
  CutQueryComplexity.GHReduction.refinedEdgeShore_system,
  CutQueryComplexity.GHReduction.refinedBlockTree_fundamental,
  CutQueryComplexity.GHReduction.frontierBranch_parent_mem_iff,
  CutQueryComplexity.GHReduction.frontierProxy_parent,
  CutQueryComplexity.GHReduction.auxiliaryAttachment,
  CutQueryComplexity.GHReduction.auxiliaryAttachment_parent,
  CutQueryComplexity.GHReduction.auxiliaryAttachment_some_iff,
  CutQueryComplexity.GHReduction.auxiliaryAttachment_shore_system,
  CutQueryComplexity.GHReduction.auxiliaryShore_pull_disjoint,
  CutQueryComplexity.GHReduction.refinementChildShore_pull,
  CutQueryComplexity.GHReduction.refinementChild_cut,
  CutQueryComplexity.GHReduction.refinementChild_minCut,
  CutQueryComplexity.GHReduction.frontierMap_mem_terminals,
  CutQueryComplexity.GHReduction.frontierMap_injective_on_fiber,
  CutQueryComplexity.GHReduction.frontier_terminal_trace_card,
  CutQueryComplexity.GHReduction.liftFrontierSplit_valid,
  CutQueryComplexity.GHReduction.checkedFrontierSplit_of_wellFormed,
  CutQueryComplexity.GHReduction.checkedFrontierSplit_minCuts,
  CutQueryComplexity.GHReduction.refinementCell_congr_membership,
  CutQueryComplexity.GHReduction.checkedFrontierSplit_shore_pull,
  CutQueryComplexity.GHReduction.frontierMap_representative_other,
  CutQueryComplexity.GHReduction.frontierMap_representative_fiber,
  CutQueryComplexity.GHReduction.frontierMap_representative_parent,
  CutQueryComplexity.GHReduction.roundSplitAttachment,
  CutQueryComplexity.GHReduction.roundSplitAttachment_parent,
  CutQueryComplexity.GHReduction.roundChildShore_pull,
  CutQueryComplexity.GHReduction.roundEdgeShore_minCut_witness,
  CutQueryComplexity.GHReduction.roundBlockTree_minCut_witness,
  CutQueryComplexity.GHReduction.collectBlockTrees,
  CutQueryComplexity.GHReduction.collectBlockTrees_spec,
  CutQueryComplexity.GHReduction.collectBlockTrees_exists,
  CutQueryComplexity.GHReduction.FrontierForest,
  CutQueryComplexity.GHReduction.PublicFrontierState.Discrete,
  CutQueryComplexity.GHReduction.leafFrontierForest,
  CutQueryComplexity.GHReduction.discrete_fiber_singleton,
  CutQueryComplexity.GHReduction.singletonSteinerOutput_represents,
  CutQueryComplexity.GHReduction.leafFrontierForest_correct,
  CutQueryComplexity.GHReduction.leafFrontierForest_coverage,
  CutQueryComplexity.GHReduction.leafFrontierForest_attach,
  CutQueryComplexity.GHReduction.frontierRoundLabel,
  CutQueryComplexity.GHReduction.frontierRoundChild,
  CutQueryComplexity.GHReduction.frontierRoundChild_of_mem,
  CutQueryComplexity.GHReduction.assembleFrontierBlock,
  CutQueryComplexity.GHReduction.assembleFrontierRound,
  CutQueryComplexity.GHReduction.assembleFrontierRound_spec,
  CutQueryComplexity.GHReduction.FrontierForestState,
  CutQueryComplexity.GHReduction.restoreFrontierRecord,
  CutQueryComplexity.GHReduction.restoreFrontierRecord_before,
  CutQueryComplexity.GHReduction.restoreFrontierRecords,
  CutQueryComplexity.GHReduction.assembleFrontierTrace,
  CutQueryComplexity.GHReduction.assembleFrontierTraceProgram,
  CutQueryComplexity.GHReduction.assembleFrontierTraceProgram_eval,
  CutQueryComplexity.GHReduction.assembleFrontierTraceProgram_cost,
  CutQueryComplexity.GHReduction.PublicFrontierState.Witnessed,
  CutQueryComplexity.GHReduction.initialFrontierState_witnessed,
  CutQueryComplexity.GHReduction.frontierBranch_minCut_witness,
  CutQueryComplexity.GHReduction.packFrontierState_witnessed,
  CutQueryComplexity.GHReduction.checkedFrontierSplit_none_children,
  CutQueryComplexity.GHReduction.checkedFrontierSplit_good_minCuts,
  CutQueryComplexity.GHReduction.advanceFrontierState_witnessed,
  CutQueryComplexity.GHReduction.FrontierRoundRecord.split_minCuts,
  CutQueryComplexity.GHReduction.FrontierRoundRecord.after_witnessed,
  CutQueryComplexity.GHReduction.frontierTrace_witnessed,
  CutQueryComplexity.GHReduction.refinementCell_eq_iff_memberships,
  CutQueryComplexity.GHReduction.roundBlockMap_fiber_at,
  CutQueryComplexity.GHReduction.packFrontierState_fiber_at,
  CutQueryComplexity.GHReduction.advanceFrontierState_fiber_at,
  CutQueryComplexity.GHReduction.advanceFrontierState_fiber_subset,
  CutQueryComplexity.GHReduction.checkedFrontierSplit_cell_iff,
  CutQueryComplexity.GHReduction.roundBlockMap_tracked_fiber,
  CutQueryComplexity.GHReduction.advanceFrontierState_tracked_card,
  CutQueryComplexity.GHReduction.frontierVertexExcess,
  CutQueryComplexity.GHReduction.frontierEntryPotential,
  CutQueryComplexity.GHReduction.frontierRoundPotential,
  CutQueryComplexity.GHReduction.frontierRoundPotential_none,
  CutQueryComplexity.GHReduction.frontierRoundPotential_le_entry,
  CutQueryComplexity.GHReduction.frontierPivotCall_expected_entry,
  CutQueryComplexity.GHReduction.frontierStateStep_expected_potential,
  CutQueryComplexity.GHReduction.frontierTracePotential,
  CutQueryComplexity.GHReduction.frontierTrace_good_cons,
  CutQueryComplexity.GHReduction.frontierTracePotential_cons,
  CutQueryComplexity.GHReduction.frontierExecution_expected_potential,
  CutQueryComplexity.GHReduction.frontierExecution_vertex_tail,
  CutQueryComplexity.GHReduction.exists_vertex_excess_of_not_discrete,
  CutQueryComplexity.GHReduction.frontierExecution_good_depth_tail,
  CutQueryComplexity.GHReduction.frontierExecution_termination_failure,
  CutQueryComplexity.GHReduction.frontierExecution_depthFuel,
  CutQueryComplexity.GHReduction.ForestCompatible,
  CutQueryComplexity.GHReduction.leafFrontierForest_compatible,
  CutQueryComplexity.GHReduction.ForestCompatible.unrelabel,
  CutQueryComplexity.GHReduction.edgeShore_is_fundamental,
  CutQueryComplexity.GHReduction.ForestCompatible.on_edgeShore,
  CutQueryComplexity.GHReduction.subtree_subset_frontierBranch,
  CutQueryComplexity.GHReduction.compl_subtree_subset_frontierBranch,
  CutQueryComplexity.GHReduction.frontierMap_opposite_edge,
  CutQueryComplexity.GHReduction.assembleDisjointStar_attach,
  CutQueryComplexity.GHReduction.roundForest_child_attach,
  CutQueryComplexity.GHReduction.roundForest_old_attach,
  CutQueryComplexity.GHReduction.roundForestChild,
  CutQueryComplexity.GHReduction.roundForestAssemble,
  CutQueryComplexity.GHReduction.roundForestAssemble_success,
  CutQueryComplexity.GHReduction.FrontierForestSound,
  CutQueryComplexity.GHReduction.leafFrontierForest_sound,
  CutQueryComplexity.GHReduction.assembleFrontierRound_success,
  CutQueryComplexity.GHReduction.restoreFrontierRecords_success,
  CutQueryComplexity.GHReduction.assembleFrontierTrace_success,
  CutQueryComplexity.GHReduction.TreeOutputSuccess,
  CutQueryComplexity.GHReduction.frontierReduction,
  CutQueryComplexity.GHReduction.frontierReduction_cost,
  CutQueryComplexity.GHReduction.frontierReduction_failure_le,
  CutQueryComplexity.GHReduction.frontierReduction_depthFuel_failure,
  CutQueryComplexity.GHReduction.TreeOutputSuccess.allPairs,
  CutQueryComplexity.GHReduction.reductionSparsifierBudget,
  CutQueryComplexity.GHReduction.reductionSparsifier,
  CutQueryComplexity.GHReduction.reductionBudget,
  CutQueryComplexity.GHReduction.oracleReduction,
  CutQueryComplexity.GHReduction.oracleReduction_cost,
  CutQueryComplexity.GHReduction.reductionSparsifier_failure,
  CutQueryComplexity.GHReduction.oracleReduction_failure_le,
  CutQueryComplexity.GHReduction.oracleReduction_depthFuel_failure,
  CutQueryComplexity.GHReduction.confidenceDenominator,
  CutQueryComplexity.GHReduction.confidenceDenominator_pos,
  CutQueryComplexity.GHReduction.confidenceDepth,
  CutQueryComplexity.GHReduction.confidenceGuideCoefficient,
  CutQueryComplexity.GHReduction.confidenceSamples,
  CutQueryComplexity.GHReduction.confidenceBranchCoefficient,
  CutQueryComplexity.GHReduction.confidenceTrials,
  CutQueryComplexity.GHReduction.confidenceExponent,
  CutQueryComplexity.GHReduction.threeQuarter_pow_log,
  CutQueryComplexity.GHReduction.inverse_pow_log,
  CutQueryComplexity.GHReduction.weighted_inverse_bound,
  CutQueryComplexity.GHReduction.confidence_inner_error,
  CutQueryComplexity.GHReduction.confidence_sparsifier_error,
  CutQueryComplexity.GHReduction.confidence_total_error,
  CutQueryComplexity.GHReduction.confidenceBudget,
  CutQueryComplexity.GHReduction.confidenceReduction,
  CutQueryComplexity.GHReduction.confidenceReduction_failure,
  CutQueryComplexity.GHReduction.confidenceReduction_cost,
  CutQueryComplexity.GHReduction.reductionLog,
  CutQueryComplexity.GHReduction.reductionLog_one_le,
  CutQueryComplexity.GHReduction.binaryLog_mul_le,
  CutQueryComplexity.GHReduction.binaryLog_pow_le,
  CutQueryComplexity.GHReduction.binaryLog_add_one_le,
  CutQueryComplexity.GHReduction.binaryLog_le_self,
  CutQueryComplexity.GHReduction.binaryLog_scaled_power_le,
  CutQueryComplexity.GHReduction.real_log_nat_le_binaryLog,
  CutQueryComplexity.GHReduction.reductionLog_controls,
  CutQueryComplexity.GHReduction.depthCoefficient,
  CutQueryComplexity.GHReduction.confidenceDenominator_log_le,
  CutQueryComplexity.GHReduction.confidenceDepth_le,
  CutQueryComplexity.GHReduction.sampleCoefficient,
  CutQueryComplexity.GHReduction.trialCoefficient,
  CutQueryComplexity.GHReduction.exponentCoefficient,
  CutQueryComplexity.GHReduction.confidenceGuideCoefficient_log_le,
  CutQueryComplexity.GHReduction.confidenceSamples_le,
  CutQueryComplexity.GHReduction.confidenceBranchCoefficient_log_le,
  CutQueryComplexity.GHReduction.confidenceTrials_le,
  CutQueryComplexity.GHReduction.confidenceExponent_le,
  CutQueryComplexity.GHReduction.parameterCoefficient,
  CutQueryComplexity.GHReduction.parameterScale,
  CutQueryComplexity.GHReduction.parameterScale_large,
  CutQueryComplexity.GHReduction.parameterScale_controls,
  CutQueryComplexity.GHReduction.paramc_onePercent,
  CutQueryComplexity.GHReduction.outBound_onePercent_le,
  CutQueryComplexity.GHReduction.capQ_onePercent_le,
  CutQueryComplexity.GHReduction.reductionSparsifierBudget_le,
  CutQueryComplexity.GHReduction.sparsifierLog_le,
  CutQueryComplexity.GHReduction.reductionSparsifierBudget_envelope,
  CutQueryComplexity.GHReduction.raise_query_envelope,
  CutQueryComplexity.GHReduction.add_query_envelopes,
  CutQueryComplexity.GHReduction.mul_query_envelopes,
  CutQueryComplexity.GHReduction.unit_query_envelope,
  CutQueryComplexity.GHReduction.confidenceFrontierBudget_envelope,
  CutQueryComplexity.GHReduction.confidenceBudget_envelope,
  CutQueryComplexity.GHReduction.reductionPolynomialConstant,
  CutQueryComplexity.GHReduction.confidenceBudget_polylog,
  CutQueryComplexity.GHReduction.weightedGHBudget,
  CutQueryComplexity.GHReduction.weightedGHProgram,
  CutQueryComplexity.GHReduction.weightedGHProgram_cost,
  CutQueryComplexity.GHReduction.weightedGHProgram_failure,
  CutQueryComplexity.GHReduction.AllPairsTreeSuccess,
  CutQueryComplexity.GHReduction.weightedGHProgram_allPairs,
  CutQueryComplexity.GHReduction.exists_weighted_gh_reduction,
  CutQueryComplexity.GHReduction.weightedGHProgram_transcript_cost,
  CutQueryComplexity.GHReduction.weightedGHProgram_transcript_fixed,
  CutQueryComplexity.GHReduction.exists_weighted_gh_reduction_transcript,
  CutQueryComplexity.GHReduction.Randomized.RandomCanonicalSTFamily,
  CutQueryComplexity.GHReduction.Randomized.STPrograms.FailsAtMost,
  CutQueryComplexity.GHReduction.Randomized.STPrograms.amplify,
  CutQueryComplexity.GHReduction.Randomized.STPrograms.FailsAtMost.amplify,
  CutQueryComplexity.GHReduction.Randomized.RandomCanonicalSTFamily.amplify_failsAtMost,
  CutQueryComplexity.GHReduction.Randomized.sizeRegular_amplifiedCost,
  CutQueryComplexity.GHReduction.Randomized.amplificationRounds,
  CutQueryComplexity.GHReduction.Randomized.randomizedGHBudget,
  CutQueryComplexity.GHReduction.Randomized.RandomizedGHTarget,
  CutQueryComplexity.GHReduction.Randomized.UnweightedAllPairsTarget,
  CutQueryComplexity.GHReduction.Randomized.amplification_slack,
  CutQueryComplexity.GHReduction.Randomized.unweightedAllPairs_of_randomizedGH,
  CutQueryComplexity.GHReduction.Randomized.CallTree,
  CutQueryComplexity.GHReduction.Randomized.CallTree.interpIdeal,
  CutQueryComplexity.GHReduction.Randomized.CallTree.interpRand,
  CutQueryComplexity.GHReduction.Randomized.CallTree.eval_interpRand_of_exact,
  CutQueryComplexity.GHReduction.Randomized.CallTree.mass_interpRand_le,
  CutQueryComplexity.GHReduction.Randomized.CallProg,
  CutQueryComplexity.GHReduction.Randomized.CallProg.compile,
  CutQueryComplexity.GHReduction.Randomized.CallProg.interpIdeal_compile,
  CutQueryComplexity.GHReduction.Randomized.CallProg.eval_toProg,
  CutQueryComplexity.GHReduction.Randomized.refFamily,
  CutQueryComplexity.GHReduction.Randomized.sizeRegular_refCost,
  CutQueryComplexity.GHReduction.Randomized.CallProg.isolatingValues_idealEval,
  CutQueryComplexity.GHReduction.Randomized.CallProg.isolatingValuesCall_idealCost,
  CutQueryComplexity.GHReduction.Randomized.exists_randomized_isolating,
  CutQueryComplexity.GHReduction.Randomized.CallTree.idealRun,
  CutQueryComplexity.GHReduction.Randomized.CallTree.truncate,
  CutQueryComplexity.GHReduction.Randomized.CallTree.interpIdeal_truncate,
  CutQueryComplexity.GHReduction.Randomized.Twin.frontierPivotRound_cost,
  CutQueryComplexity.GHReduction.Randomized.Twin.weightedGHProgram,
  CutQueryComplexity.GHReduction.Randomized.Twin.weightedGHProgram_eq,
  CutQueryComplexity.GHReduction.Randomized.randomizedGHProgram,
  CutQueryComplexity.GHReduction.Randomized.randomizedGHProgram_failure,
  CutQueryComplexity.GHReduction.Randomized.randomizedGHProgram_allPairs,
  CutQueryComplexity.GHReduction.Randomized.exists_randomized_gh_reduction,
  CutQueryComplexity.GHReduction.Randomized.randomizedGHTarget,
  CutQueryComplexity.GHReduction.Randomized.unweightedAllPairsTarget,
  CutQueryComplexity.GHReduction.Randomized.exists_randomized_unweighted_allPairs,
  CutQueryComplexity.GHReduction.Randomized.exists_weighted_gh_reduction_via_calls,
  CutQueryComplexity.BoundedFlowMinCut.lowDegree_correct,
  CutQueryComplexity.BoundedFlowMinCut.dominating_correct,
  CutQueryComplexity.BoundedFlowMinCut.small_cut_meets_dominating,
  CutQueryComplexity.BoundedFlowMinCut.augment_flowSpec,
  CutQueryComplexity.BoundedFlowMinCut.usedCount_augment_le,
  CutQueryComplexity.BoundedFlowMinCut.witness_reach_iff,
  CutQueryComplexity.BoundedFlowMinCut.witnessPath_some,
  CutQueryComplexity.BoundedFlowMinCut.witnessPath_none,
  CutQueryComplexity.BoundedFlowMinCut.shortcutLoop_spec,
  CutQueryComplexity.BoundedFlowMinCut.shortcutLoop_cost_le,
  CutQueryComplexity.BoundedFlowMinCut.repairForest_spec,
  CutQueryComplexity.BoundedFlowMinCut.repairForest_cost_le,
  CutQueryComplexity.BoundedFlowMinCut.boundedFlow_spec,
  CutQueryComplexity.BoundedFlowMinCut.boundedFlowTree_correct,
  CutQueryComplexity.BoundedFlowMinCut.mainProg_correct,
  CutQueryComplexity.BoundedFlowMinCut.mainProg_cost,
  CutQueryComplexity.BoundedFlowMinCut.program,
  CutQueryComplexity.BoundedFlowMinCut.program_correct,
  CutQueryComplexity.BoundedFlowMinCut.program_cost,
  CutQueryComplexity.BoundedFlowMinCut.queryBudget_bound,
  CutQueryComplexity.BoundedFlowMinCut.queryBudget_isBigO,
  CutQueryComplexity.GlobalSTReduction.RealSTFamily,
  CutQueryComplexity.GlobalSTReduction.RandomRealSTFamily,
  CutQueryComplexity.GlobalSTReduction.OptFailsAtMost,
  CutQueryComplexity.GlobalSTReduction.RealSTFamily.toPrograms,
  CutQueryComplexity.GlobalSTReduction.RealSTFamily.optFailsAtMost_zero,
  CutQueryComplexity.GlobalSTReduction.GlobalSuccess,
  CutQueryComplexity.GlobalSTReduction.ValidOutput,
  CutQueryComplexity.GlobalSTReduction.trialCount,
  CutQueryComplexity.GlobalSTReduction.levelBudget,
  CutQueryComplexity.GlobalSTReduction.searchBudget,
  CutQueryComplexity.GlobalSTReduction.detGlobalBudget,
  CutQueryComplexity.GlobalSTReduction.callCount,
  CutQueryComplexity.GlobalSTReduction.repetitions,
  CutQueryComplexity.GlobalSTReduction.randomGlobalBudget,
  CutQueryComplexity.GlobalSTReduction.trialFailure_le,
  CutQueryComplexity.GlobalSTReduction.callFailure_le,
  CutQueryComplexity.GlobalSTReduction.DetGlobalTarget,
  CutQueryComplexity.GlobalSTReduction.RandomGlobalTarget,
  CutQueryComplexity.GlobalSTReduction.ReplyRule,
  CutQueryComplexity.GlobalSTReduction.anyReply,
  CutQueryComplexity.GlobalSTReduction.optReply,
  CutQueryComplexity.GlobalSTReduction.Holds,
  CutQueryComplexity.GlobalSTReduction.Within,
  CutQueryComplexity.GlobalSTReduction.CostWithin,
  CutQueryComplexity.GlobalSTReduction.CallsWithin,
  CutQueryComplexity.GlobalSTReduction.holds_bind,
  CutQueryComplexity.GlobalSTReduction.holds_contract,
  CutQueryComplexity.GlobalSTReduction.within_bind,
  CutQueryComplexity.GlobalSTReduction.min_setCut_pull,
  CutQueryComplexity.GlobalSTReduction.min_shorePull,
  CutQueryComplexity.GlobalSTReduction.holds_isolatingValuesCall,
  CutQueryComplexity.GlobalSTReduction.holds_isolatingValuesCall_any,
  CutQueryComplexity.GlobalSTReduction.cost_isolatingValuesCall,
  CutQueryComplexity.GlobalSTReduction.calls_isolatingValuesCall,
  CutQueryComplexity.GlobalSTReduction.support_interpRand_compile,
  CutQueryComplexity.GlobalSTReduction.support_interpRand_compile_some,
  CutQueryComplexity.GlobalSTReduction.mass_interpRand_compile_le,
  CutQueryComplexity.GlobalSTReduction.mass_exists_disjoint,
  CutQueryComplexity.GlobalSTReduction.Hit,
  CutQueryComplexity.GlobalSTReduction.mass_hit_ge,
  CutQueryComplexity.GlobalSTReduction.mass_not_hit_le,
  CutQueryComplexity.GlobalSTReduction.hit_trace,
  CutQueryComplexity.GlobalSTReduction.exists_minCut_avoiding,
  CutQueryComplexity.GlobalSTReduction.isMinCut_of_isolating,
  CutQueryComplexity.GlobalSTReduction.levelCall,
  CutQueryComplexity.GlobalSTReduction.candidatesCall,
  CutQueryComplexity.GlobalSTReduction.terminalSets,
  CutQueryComplexity.GlobalSTReduction.select,
  CutQueryComplexity.GlobalSTReduction.globalTree,
  CutQueryComplexity.GlobalSTReduction.globalTree_valid,
  CutQueryComplexity.GlobalSTReduction.globalTree_failure,
  CutQueryComplexity.GlobalSTReduction.select_globalSuccess,
  CutQueryComplexity.GlobalSTReduction.detGlobalProgram,
  CutQueryComplexity.GlobalSTReduction.exists_global_from_st,
  CutQueryComplexity.GlobalSTReduction.detGlobalTarget,
  CutQueryComplexity.GlobalSTReduction.selectShore_stMinCut,
  CutQueryComplexity.GlobalSTReduction.OptFailsAtMost.amplify,
  CutQueryComplexity.GlobalSTReduction.randomGlobalProgram,
  CutQueryComplexity.GlobalSTReduction.exists_global_from_randomized_st,
  CutQueryComplexity.GlobalSTReduction.randomGlobalTarget,
  CutQueryComplexity.GlobalSTReduction.budgetLog,
  CutQueryComplexity.GlobalSTReduction.detGlobalBudget_le,
  CutQueryComplexity.GlobalSTReduction.repetitions_le,
  CutQueryComplexity.GlobalSTReduction.randomGlobalBudget_le,
  CutQueryComplexity.GlobalSTReduction.budgetLog_le_log,
  CutQueryComplexity.GlobalSTReduction.detGlobalBudget_isBigO,
  CutQueryComplexity.GlobalSTReduction.randomGlobalBudget_isBigO,
  CutQueryComplexity.GlobalSTReduction.maximalShore,
  CutQueryComplexity.GlobalSTReduction.reconstructionFamily,
  CutQueryComplexity.GlobalSTReduction.reconstructionFamily_not_canonical,
  CutQueryComplexity.GlobalSTReduction.sizeRegular_sq,
  CutQueryComplexity.GlobalSTReduction.exists_global_reconstruction,
  CutQueryComplexity.GlobalSTReduction.globalFromST_targets,
  CutQueryComplexity.Certificate.UnitAllPairs.eq_of_consistent,
  CutQueryComplexity.Certificate.UnitAllPairs.exists_unit_allPairs_certificate,
  CutQueryComplexity.Certificate.UnitAllPairs.queries_card,
  CutQueryComplexity.Certificate.UnitAllPairs.transcript_certificate,
  CutQueryComplexity.Quantum.DirectedReconstruction.allPairs_correct,
  CutQueryComplexity.Quantum.DirectedReconstruction.directedBudget_le,
  CutQueryComplexity.Quantum.DirectedReconstruction.directedBudget_unit,
  CutQueryComplexity.Quantum.DirectedReconstruction.exists_capacity_allPairs,
  CutQueryComplexity.Quantum.DirectedReconstruction.exists_capacity_global,
  CutQueryComplexity.Quantum.DirectedReconstruction.exists_capacity_terminal,
  CutQueryComplexity.Quantum.DirectedReconstruction.global_correct,
  CutQueryComplexity.Quantum.DirectedReconstruction.physical_allPairs_endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.physical_global_endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.physical_terminal_endpoint,
  CutQueryComplexity.Quantum.DirectedReconstruction.recoverDirectedRoutine_len,
  CutQueryComplexity.Quantum.DirectedReconstruction.recoverDirectedW_prob,
  CutQueryComplexity.Quantum.DirectedReconstruction.recoverDirected_out_prob,
  CutQueryComplexity.Quantum.DirectedReconstruction.symAlgW_prob,
  CutQueryComplexity.Quantum.DirectedReconstruction.symAlg_prob,
  CutQueryComplexity.Quantum.DirectedReconstruction.symCall_run_honest,
  CutQueryComplexity.Quantum.DirectedReconstruction.terminal_correct,
  CutQueryComplexity.Quantum.DirectedReconstruction.withImbalance_prob,
  CutQueryComplexity.Quantum.LinearReconstruction.allPairsAlg_simple_success,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_capacity_allPairs,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_capacity_global,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_capacity_terminal,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_unit_allPairs,
  CutQueryComplexity.Quantum.LinearReconstruction.exists_unit_terminal,
  CutQueryComplexity.Quantum.LinearReconstruction.globalReconstructAlg_success,
  CutQueryComplexity.Quantum.LinearReconstruction.graphToCapacity_read,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraphAlg_born,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraphAlg_normalized,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraph_len_two,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraph_len_unit,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverGraph_run,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverRow_len,
  CutQueryComplexity.Quantum.LinearReconstruction.recoverRow_run_coherent,
  CutQueryComplexity.Reconstruction.CompressedDirected.allPairsRandomized_success,
  CutQueryComplexity.Reconstruction.CompressedDirected.allPairs_certificate,
  CutQueryComplexity.Reconstruction.CompressedDirected.allPairs_deterministic,
  CutQueryComplexity.Reconstruction.CompressedDirected.allPairs_randomized,
  CutQueryComplexity.Reconstruction.CompressedDirected.budget_bound,
  CutQueryComplexity.Reconstruction.CompressedDirected.global_deterministic,
  CutQueryComplexity.Reconstruction.CompressedDirected.program_run,
  CutQueryComplexity.Reconstruction.DirectedData.allPairsAnswers_correct,
  CutQueryComplexity.Reconstruction.DirectedData.cut_correct,
  CutQueryComplexity.Reconstruction.DirectedData.globalAnswer_correct,
  CutQueryComplexity.Reconstruction.DirectedData.terminalAnswer_correct,
  CutQueryComplexity.Reconstruction.WeightedDirected.allPairs_certificate,
  CutQueryComplexity.Reconstruction.WeightedDirected.deterministic_allPairs,
  CutQueryComplexity.Reconstruction.WeightedDirected.deterministic_global,
  CutQueryComplexity.Reconstruction.WeightedDirected.deterministic_terminal,
  CutQueryComplexity.Reconstruction.WeightedDirected.queries_cut_equivalent,
  CutQueryComplexity.Reconstruction.WeightedDirected.randomized_allPairs,
  CutQueryComplexity.Reconstruction.WeightedDirected.randomized_global,
  CutQueryComplexity.Reconstruction.WeightedDirected.randomized_terminal,
  CutQueryComplexity.Reconstruction.WeightedUndirected.allPairs_certificate,
  CutQueryComplexity.Reconstruction.WeightedUndirected.deterministic_allPairs,
  CutQueryComplexity.Reconstruction.WeightedUndirected.deterministic_terminal,
  CutQueryComplexity.Reconstruction.WeightedUndirected.eq_of_consistent,
  CutQueryComplexity.Reconstruction.WeightedUndirected.queryBudget_le,
  CutQueryComplexity.Reconstruction.WeightedUndirected.randomized_allPairs,
  CutQueryComplexity.Reconstruction.WeightedUndirected.randomized_terminal,
  CutQueryComplexity.WeightedMinCut.Endpoint.program_run,
  CutQueryComplexity.WeightedMinCut.Endpoint.queryBudget_logSquared,
  CutQueryComplexity.WeightedMinCut.Endpoint.weighted_global,
  CutQueryComplexityChecks.CoverageClassical.real_directed_public_all_pairs,
  CutQueryComplexityChecks.CoverageClassical.real_undirected_certificate,
  CutQueryComplexityChecks.CoverageClassical.real_undirected_public_all_pairs,
  CutQueryComplexityChecks.CoverageClassical.unit_directed_joint_execution,
  CutQueryComplexityChecks.CoverageClassical.weighted_global_public,
  CutQueryComplexityChecks.CoverageProducers.known_unit_graph_certificate,
  CutQueryComplexityChecks.CoverageProducers.public_directed_answers,
  CutQueryComplexityChecks.CoverageQuantum.Directed.original_allPairs,
  CutQueryComplexityChecks.CoverageQuantum.Directed.original_global,
  CutQueryComplexityChecks.CoverageQuantum.Directed.original_terminal,
  CutQueryComplexityChecks.CoverageQuantum.Directed.public_physical_allPairs,
  CutQueryComplexityChecks.CoverageQuantum.Undirected.capacity_global,
  CutQueryComplexityChecks.CoverageQuantum.Undirected.original_terminal,
  CutQueryComplexityChecks.CoverageQuantum.Undirected.public_physical_allPairs,
  CutQueryComplexityChecks.CoverageQuantum.Undirected.tiny_has_zero_native_calls,
  CutQueryComplexityChecks.CoverageQuantumReconstruction.no_honesty_needed_for_normalization,
  CutQueryComplexityChecks.CoverageQuantumReconstruction.physical_public_reconstruction,
  CutQueryComplexityChecks.CoverageQuantumReconstruction.unit_and_symmetrized_counts
]

/- Literal contracts for the completed undirected decoder, output wrapper,
and fixed canonical count. This block is a candidate until compiled as part
of the integration and strict audit files. -/

example {V : Type} [Fintype V] [DecidableEq V] (Q : Finset (Finset V)) :
    ∃ decode : (Q → ℝ) → WeightedGraph V,
      (∀ answers : Q → ℝ, (decode answers).edgeCount ≤ Q.card) ∧
      ∀ G : WeightedGraph V, ∀ S ∈ Q,
        (decode (fun T => G.cut T.val)).cut S = G.cut S := by
  refine ⟨UndirectedClosure.sparseCompletion Q,
    UndirectedClosure.sparseCompletion_edgeCount Q, ?_⟩
  intro G S hS
  exact UndirectedClosure.sparseCompletion_consistent G Q S hS

example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        ((max 1 (Nat.clog 2 (2 * n)) : ℕ) : ℝ) ^ 5 ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n) × ℝ)) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), ∃ S,
          D.eval G.cut = some (S, mincutValue G) ∧
          (S.Nonempty ∧ S ≠ Finset.univ) ∧
          ∀ T : Finset (Fin n), (T.Nonempty ∧ T ≠ Finset.univ) → G.cut S ≤ G.cut T := by
  simpa only [DetMinCut.logL, IsMinCut, ProperShore] using
    UndirectedClosure.deterministic_mincut_shore_value_log5

example {V : Type} [Fintype V] [DecidableEq V]
    (C : Finset V) (K J : WeightedGraph V) {s t : V} (hst : s ≠ t)
    (hJ : AllPairsAudit.Unweighted J)
    (hsupp : ∀ u v, u ∉ C ∨ v ∉ C → J.w u v = 0)
    {D n b : ℕ} (hD : 2 ≤ D) (hCn : C.card ≤ n) (hbn : b ≤ n)
    (hdeg : ∀ v ∈ C, (D : ℝ) ≤ J.degree v) :
    ∀ L : WeightedGraph V,
      (∀ u v, u ∉ C ∨ v ∉ C → L.w u v = 0) → J.IsSubgraph L →
      ((CanonicalST.canonicalFamily C K s t).filter
        (fun S => (K.add L).cut S ≤ (b : ℝ))).card ≤
          (2 * n) ^ ⌈32 * ((C.card : ℝ) + (b : ℝ)) / (D : ℝ)⌉₊ :=
  CanonicalST.Counting.canonicalFamily_card_le C K J hst hJ hsupp hD hCn hbn hdeg


/- The actual public O(n) family precedes every hidden graph. -/
section RandomizedContracts1
open scoped ENNReal
open CutQueryComplexity CutQueryComplexity.Probability
open CutQueryComplexity.StarContraction2022

example :
    ∃ C : ℕ, 0 < C ∧
      ∃ P : (n : ℕ) → RTree (Finset (Fin n)) ℝ (CutResult (Fin n)) (C * n),
        (∀ n read (out : CutResult (Fin n) × ℕ),
          out ∈ (RTree.run read (P n)).support → out.2 ≤ C * n) ∧
        (∀ n, 2 ≤ n → ∀ G : SimpleInput (Fin n), ∀ out,
          out ∈ ((P n).eval G.toWeighted.cut).support →
          ProperShore out.shore ∧ out.value = G.toWeighted.cut out.shore) ∧
        (∀ n, 2 ≤ n → ∀ G : SimpleInput (Fin n),
          ENNReal.ofReal (2 / 3 : ℝ) ≤
            mass ((P n).eval G.toWeighted.cut) (fun out =>
              ProperShore out.shore ∧ out.value = G.toWeighted.cut out.shore ∧
              IsMinCut G.toWeighted out.shore ∧ out.value = mincutValue G.toWeighted)) ∧
        (∀ n, n < 2 → ∀ read, (P n).eval read = PMF.pure ⟨∅, 0⟩) :=
  Randomized.exists_uniform_linear_program


end RandomizedContracts1

/- Executed route and pruning contracts, with public hard caps. -/
namespace PublicContracts2
open CutQueryComplexity CutQueryComplexity.DeterministicAPMCExpansion
open Flow Pruning Certificate AllPairsAudit Finset
open scoped Classical
noncomputable section

namespace APMCLiteral1

-- This acceptance statement constructs one public capped tree before G.
-- Route count, terminal bounds, and cut congestion come from its execution.
theorem routed_public_contract {V : Type} [Fintype V] [DecidableEq V]
    (C R t : ℕ) (hC : 1 ≤ C) (hCR : C ≤ R) (ht : 1 ≤ t)
    (hqpos : 1 ≤ Fintype.card V) (hq : Fintype.card V ≤ t ^ 3) (a z : V → ℕ)
    (ha : (∑ v, a v) ≤ Fintype.card V * t) :
    ∃ tree : DTree (Finset V) ℝ
        (Option (ExactResult V × RouteResult (NetworkVertex V))) (exactSharpBudget V R t),
      (∀ read, tree.cost read ≤ exactSharpBudget V R t) ∧
      ∀ G : WeightedGraph V, Unweighted G →
        ∃ result routes, tree.eval G.cut = some result ∧
          ExactCertificate (directed (twoStar (scaledInternal G C) a z)) result.1 ∧
          locateRoutes result.2.routes = some routes ∧
          routes.map LocatedRoute.nodes = result.2.routes ∧
          routes.length = eventValue result.1.events ∧
          (∀ v, startCount routes v ≤ a v ∧ finishCount routes v ≤ z v) ∧
          (∀ T : Finset V,
            (routes.map (fun route => separated T route.start route.finish)).sum ≤
              (C : ℝ) * G.cut T) := by
  refine ⟨(routedFlowProg C a z).toDTree (exactSharpBudget V R t), ?_, ?_⟩
  · intro read
    exact DTree.cost_le _ _
  · intro G hG
    let result := (routedFlowProg C a z).eval G.cut
    have hcost : (routedFlowProg C a z).cost G.cut ≤ exactSharpBudget V R t := by
      rw [routedFlowProg_cost]
      exact scaledExactProg_cost_sharp G hG C R t hC hCR ht hqpos hq a z ha
    obtain ⟨hc, hs⟩ := routedFlowProg_correct G hG C a z
    change ExactCertificate (directed (twoStar (scaledInternal G C) a z)) result.1 at hc
    change RouteSpec result.1.flow source sink (eventValue result.1.events) result.2 at hs
    obtain ⟨routes, hlocated, hmap, hcorrect⟩ := locateRoutes_correct
      (scaledInternal G C) a z result.1.flow hc.feasible.1 result.2.routes hs.paths
    refine ⟨result, routes, Prog.toDTree_eval G.cut _ _ hcost, hc, hlocated, hmap, ?_, ?_, ?_⟩
    · have hlength := congrArg List.length hmap
      simpa only [List.length_map, hs.count] using hlength
    · exact located_terminal_bounds (scaledInternal G C) a z result.1.flow hc.feasible.1
        (eventValue result.1.events) result.2 hs routes hmap hcorrect
    · intro T
      have hpaths : ∀ route ∈ routes,
          RoutePath (fun u v => 0 < result.1.flow u v) source sink route.nodes := by
        intro route hr
        apply hs.paths route.nodes
        rw [← hmap]
        exact List.mem_map_of_mem hr
      have hcongestion : ∀ u v,
          ((routeLoad (routes.map LocatedRoute.nodes) (.inl u) (.inl v) +
            routeLoad (routes.map LocatedRoute.nodes) (.inl v) (.inl u) : ℕ) : ℝ) ≤
              (scaledInternal G C).w u v := by
        intro u v
        simpa only [hmap, twoStar_internal] using
          hs.undirected_load_le hc.feasible.1 (.inl u) (.inl v)
      have hcut := routes_cut_domination (scaledInternal G C) routes
        (fun u v => 0 < result.1.flow u v) hpaths hcorrect hcongestion T
      simpa only [scaledInternal_cut] using hcut

-- The pruning minimizer is computed by the actual program. The tree and
-- hard cap are public; fake-edge expansion is a separate producer invariant.
theorem pruning_public_contract {V : Type} [Fintype V] [DecidableEq V]
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hqpos : 1 ≤ Fintype.card V)
    (hq : Fintype.card V ≤ t ^ 3) (a : V → ℕ)
    (ha : (∑ v, a v) ≤ Fintype.card V * t) :
    ∃ tree : DTree (Finset V) ℝ (Option (Finset V)) (exactSharpBudget V R t),
      (∀ read, tree.cost read ≤ exactSharpBudget V R t) ∧
      ∀ G : WeightedGraph V, Unweighted G →
        tree.eval G.cut = some ((pruneProg R t a).eval G.cut) ∧
          IsPruningMinimizer G (fun v => (a v : ℝ)) (2 * t) R
            ((pruneProg R t a).eval G.cut) := by
  refine ⟨(pruneProg R t a).toDTree (exactSharpBudget V R t), ?_, ?_⟩
  · intro read
    exact DTree.cost_le _ _
  · intro G hG
    exact ⟨Prog.toDTree_eval G.cut _ _
      (pruneProg_cost G hG R t hR ht hqpos hq a ha), pruneProg_minimizer G hG R t a⟩

end APMCLiteral1

#print axioms APMCLiteral1.routed_public_contract
#print axioms APMCLiteral1.pruning_public_contract
end
end PublicContracts2


/- Literal executed-program contract. -/
namespace APMCContracts1
set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.DeterministicAPMCExpansion
open Flow CutMatching AllPairsAudit Finset
open scoped Classical
noncomputable section

namespace APMCLiteral2

-- One public capped oracle tree is fixed before G. Its literal clone-star
-- capacities imply the source-mass bound; its actual routes imply SlotsFit.
-- Neither fact is assumed by the contract.
theorem actual_flow_clone_contract {V : Type} [Fintype V] [DecidableEq V]
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t)
    (hqpos : 1 ≤ Fintype.card V) (hq : Fintype.card V ≤ t ^ 3)
    (cut : Bisection (Clone V (2 * t))) :
    ∃ tree : DTree (Finset V) ℝ
        (Option (ExactResult V × RouteResult (NetworkVertex V))) (exactSharpBudget V R t),
      (∀ read, tree.cost read ≤ exactSharpBudget V R t) ∧
      ∀ G : WeightedGraph V, Unweighted G →
        ∃ result routes, ∃ pairs : ClonePairing cut routes,
          tree.eval G.cut = some result ∧
          ExactCertificate (directed (twoStar (scaledInternal G 1)
            (slotCount cut.shore) (slotCount cut.shoreᶜ))) result.1 ∧
          locateRoutes result.2.routes = some routes ∧
          assignClones cut routes = some pairs ∧
          routes.length = eventValue result.1.events ∧
          pairs.fakeLeft.card = cut.shore.card - eventValue result.1.events ∧
          pairs.fakeEndpoints.card = 2 * pairs.fakeLeft.card ∧
          pairs.matching.Crosses cut.shore ∧
          (∀ i, pairs.matching.mate (pairs.left i).val = (pairs.right i).val) ∧
          (∀ i, (pairs.left i).val.1 = (routes.get i).start) ∧
          (∀ i, (pairs.right i).val.1 = (routes.get i).finish) := by
  let a := slotCount cut.shore
  let z := slotCount cut.shoreᶜ
  have ha : (∑ v, a v) ≤ Fintype.card V * t := by
    change (∑ v, slotCount cut.shore v) ≤ _
    rw [sum_slotCount]
    nlinarith only [bisection_clone_card cut]
  refine ⟨(routedFlowProg 1 a z).toDTree (exactSharpBudget V R t), ?_, ?_⟩
  · intro read
    exact DTree.cost_le _ _
  · intro G hG
    let result := (routedFlowProg 1 a z).eval G.cut
    have hcost : (routedFlowProg 1 a z).cost G.cut ≤ exactSharpBudget V R t := by
      rw [routedFlowProg_cost]
      exact scaledExactProg_cost_sharp G hG 1 R t le_rfl hR ht hqpos hq a z ha
    obtain ⟨hc, hs⟩ := routedFlowProg_correct G hG 1 a z
    change ExactCertificate (directed (twoStar (scaledInternal G 1) a z)) result.1 at hc
    change RouteSpec result.1.flow source sink (eventValue result.1.events) result.2 at hs
    obtain ⟨routes, hlocated, hmap, hcorrect⟩ := locateRoutes_correct
      (scaledInternal G 1) a z result.1.flow hc.feasible.1 result.2.routes hs.paths
    have hfit : SlotsFit cut routes := located_terminal_bounds
      (scaledInternal G 1) a z result.1.flow hc.feasible.1
      (eventValue result.1.events) result.2 hs routes hmap hcorrect
    let pairs := buildClonePairing cut routes hfit
    have hlength : routes.length = eventValue result.1.events := by
      have h := congrArg List.length hmap
      simpa only [List.length_map, hs.count] using h
    refine ⟨result, routes, pairs, Prog.toDTree_eval G.cut _ _ hcost, hc, hlocated,
      assignClones_success cut routes hfit, hlength, ?_, pairs.fakeEndpoints_card,
      pairs.crosses, pairs.paired, pairs.source_label, pairs.sink_label⟩
    rw [pairs.fakeLeft_card, hlength]

-- A universal positive gap and natural factor are constructed analytically;
-- no entropy-gap parameter is supplied by the caller.
theorem analytic_public_constants :
    ∃ c : ℝ, 0 < c ∧ ∃ factor : ℕ, 2 ≤ factor ∧
      (64 : ℝ) ≤ factor * c ∧
      ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → 2 * q ≤ p → c * p ≤ pairGain p q := by
  refine ⟨gapConstant, gapConstant_pos, entropyRoundFactor,
    entropyRoundFactor_ge_two, entropyRoundFactor_scaled, ?_⟩
  intro p q hp hq hb
  exact pairGain_ge hp hq hb

end APMCLiteral2

#print CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.assignClones
#check CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.completeMatching_spec
#check CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.bisection_clone_card
#check CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.potential_cons_mono
#check CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.potential_le
#check CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.twice_leakage_le_cut
#check CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.pairGain_ge
#print axioms APMCLiteral2.actual_flow_clone_contract
#print axioms APMCLiteral2.analytic_public_constants


end

end APMCContracts1


/- Literal executed-program contract. -/
namespace GHContracts1
set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction
open scoped Classical ENNReal
open CutQueryComplexity.Probability

namespace GH207Contract

-- The public program is chosen before every reply function and hidden graph.
-- Coverage expectation retains every canonical/input/size hypothesis.
theorem publicRound {V : Type} [Fintype V] [DecidableEq V]
    {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (W : ℝ) (z levels : ℕ) :
    ∃ P : RTree (Finset V) ℝ (Finset V)
        ((levels + 1) * (Nat.clog 2 n + 3) * (Q n + n)),
      (∀ (read : Finset V → ℝ) (out : Finset V × ℕ),
        out ∈ (P.run read).support →
          out.2 ≤ (levels + 1) * (Nat.clog 2 n + 3) * (Q n + n)) ∧
      (∀ read : Finset V → ℝ, P.eval read =
        (thresholdSeedPMF V levels).map (fun seed =>
          Prog.eval read (thresholdRoundProgram family U s W z levels seed))) ∧
      (∀ (G : WeightedGraph V) (covered : Finset V),
        covered ∈ (P.eval G.cut).support →
          ∀ x ∈ covered, x ∈ U ∧ x ≠ s ∧ stValue G x s ≤ W) ∧
      (∀ (G : WeightedGraph V), InputPromise M G →
        ∀ (D : Finset V) (C : V → Finset V),
          thresholdLevels U.card ≤ levels → D ⊆ U → s ∈ U →
          (∀ v ∈ D, IsCanonicalSTCut G v s (C v)) →
          (∀ v ∈ D, stValue G v s ≤ W) →
          (∀ v ∈ D, (C v ∩ U).card ≤ z) →
          (D.card : ℝ≥0∞) * ENNReal.ofReal (1 / 8 : ℝ) ≤ (levels + 1 : ℕ) *
            expect (P.eval G.cut) (fun covered => (covered.card : ℝ≥0∞))) := by
  refine ⟨thresholdRoundTree family n U s W z levels, ?_, ?_, ?_, ?_⟩
  · exact fun read out hout => RTree.cost_le _ read hout
  · exact fun read => thresholdRoundTree_eval family hvn hQ U s W z levels read
  · exact fun G covered hcovered =>
      thresholdRoundTree_sound family hvn hQ G U s W z levels hcovered
  · exact fun G hG D C hlevels hDU hsU hC hvalue hsize =>
      thresholdRoundTree_expected_progress family hvn hQ G hG D U s W z levels C
        hlevels hDU hsU hC hvalue hsize

-- Fresh adaptive rounds retain their exact execution law and a hard cap
-- for every supported run, including replies outside any graph promise.
theorem publicRemaining {V : Type} [Fintype V] [DecidableEq V]
    {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (W : ℝ) (levels rounds : ℕ) :
    ∃ P : RTree (Finset V) ℝ (Finset V)
        (rounds * ((levels + 1) * (Nat.clog 2 n + 3) * (Q n + n))),
      (∀ (read : Finset V → ℝ) (out : Finset V × ℕ),
        out ∈ (P.run read).support →
          out.2 ≤ rounds * ((levels + 1) * (Nat.clog 2 n + 3) * (Q n + n))) ∧
      (∀ read : Finset V → ℝ, P.eval read =
        thresholdRemainingLaw family s W n levels read rounds U) ∧
      (∀ (G : WeightedGraph V) (R : Finset V), R ∈ (P.eval G.cut).support →
        R ⊆ U ∧ (s ∈ U → s ∈ R) ∧ ∀ x ∈ U \ R, x ≠ s ∧ stValue G x s ≤ W) := by
  refine ⟨thresholdRemainingTree family n s W levels rounds U, ?_, ?_, ?_⟩
  · exact fun read out hout => RTree.cost_le _ read hout
  · exact fun read => thresholdRemainingTree_eval family hvn hQ s W levels rounds U read
  · exact fun G R hR => thresholdRemainingTree_invariant family hvn hQ G s W levels rounds U hR

end GH207Contract

#audit_cut_decl GHContracts1.GH207Contract.publicRound
#audit_cut_decl GHContracts1.GH207Contract.publicRemaining

#check @CutQueryComplexity.GHReduction.singleBranch_child
#check @CutQueryComplexity.GHReduction.uniqueSurvivor_hitLevel
#check @CutQueryComplexity.GHReduction.thresholdRoundTree_expected_progress
#check @CutQueryComplexity.GHReduction.thresholdRemainingTree_eval
#check @CutQueryComplexity.GHReduction.thresholdRemainingTree_invariant


end GHContracts1


namespace QuantumForestContracts1
set_option autoImplicit false


open CutQueryComplexity CutQueryComplexity.StarContraction2022.Quantum
open CutQueryComplexity.StarContraction2022.Quantum.Forest
open CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms
open scoped Classical ENNReal

-- Check the literal public-before-input statement as well as the full modules.
example (n : ℕ) (F : CutQueryComplexity.StarContraction2022.Quantum.Forest.State n) (E : ProductPrograms.LearnedEdges n) (eta : ℝ)
    (heta : 0 < eta) :
    ∃ T : ProductTree n (CutQueryComplexity.StarContraction2022.Quantum.Forest.State n) (recoverBudget n eta),
      (∀ read out, out ∈ (RTree.run read T).support → out.2 ≤ recoverBudget n eta) ∧
      ∀ G : CapacityGraph (Fin n) 1, ProductPrograms.KnownSubgraph E G →
        F.ResidualSound G.toWeighted.support E →
        (∀ H ∈ (T.eval (productRead G)).support, H.ResidualSound G.toWeighted.support E) ∧
        CutQueryComplexity.Probability.expect (T.eval (productRead G))
          (fun H => (H.deficit G.toWeighted.support E : ℝ≥0∞)) ≤
            (3 / 4 : ℝ≥0∞) * F.deficit G.toWeighted.support E + ENNReal.ofReal (eta / 8) :=
  forestRound_progress_public F E eta heta

#check forestRound_drift_at_full_history
#check forestRound_physical_prob


end QuantumForestContracts1


/- Literal execution contract: gh. -/
section GHContracts2

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction
open scoped Classical ENNReal
open CutQueryComplexity.Probability

namespace GH208Contract

-- A public classifier with a hard every-reply cap, its exact adaptive law,
-- honest one-sided soundness, and the actual polynomial failure bound.
theorem publicClassify {V : Type} [Fintype V] [DecidableEq V]
    {M n scale : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (U : Finset V) (s : V) (W : ℝ) (levels exponent : ℕ)
    (hlevels : thresholdLevels n ≤ levels) (hsU : s ∈ U) :
    ∃ P : RTree (Finset V) ℝ (Finset V)
        (((8 * (levels + 1)) * ((exponent + 1) * Nat.clog 2 (scale + 2))) *
          ((levels + 1) * (Nat.clog 2 n + 3) * (Q n + n))),
      (∀ (read : Finset V → ℝ) (out : Finset V × ℕ),
        out ∈ (P.run read).support →
          out.2 ≤ ((8 * (levels + 1)) * ((exponent + 1) * Nat.clog 2 (scale + 2))) *
            ((levels + 1) * (Nat.clog 2 n + 3) * (Q n + n))) ∧
      (∀ read : Finset V → ℝ, P.eval read =
        (thresholdRemainingLaw family s W n levels read
          (thresholdRounds levels scale exponent) U).map (fun remaining => U \ remaining)) ∧
      (∀ (G : WeightedGraph V) (covered : Finset V), covered ∈ (P.eval G.cut).support →
        covered ⊆ lowTargets G U s W) ∧
      (∀ (G : WeightedGraph V), InputPromise M G →
        mass (P.eval G.cut) (fun covered => covered ≠ lowTargets G U s W) ≤
          (((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent) := by
  refine ⟨thresholdClassifyTree family n U s W levels scale exponent, ?_, ?_, ?_, ?_⟩
  · exact fun read out hout => RTree.cost_le _ read hout
  · intro read
    change ((thresholdRemainingTree family n s W levels
      (thresholdRounds levels scale exponent) U).map (fun remaining => U \ remaining)).eval read = _
    rw [RTree.eval_map, thresholdRemainingTree_eval family hvn hQ]
  · exact fun G covered hcovered =>
      thresholdClassifyTree_subset family hvn hQ G U s W levels scale exponent hcovered
  · exact fun G hG =>
      thresholdClassifyTree_failure_le family hvn hQ hnscale G hG U s W levels exponent hlevels hsU

-- The maximum selector is itself the public executed randomized tree.
-- Its failure bound charges each conditional classifier call once.
theorem publicSourceMaximum {V : Type} [Fintype V] [DecidableEq V]
    {M n scale : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (hnscale : n ≤ scale)
    (R : Finset V) (s : V) (levels exponent : ℕ)
    (hlevels : thresholdLevels n ≤ levels) (hR : R.Nonempty) (hs : s ∉ R) :
    ∃ P : RTree (Finset V) ℝ (Option V)
        (Nat.clog 2 (M + 1) *
          (((8 * (levels + 1)) * ((exponent + 1) * Nat.clog 2 (scale + 2))) *
            ((levels + 1) * (Nat.clog 2 n + 3) * (Q n + n)))),
      (∀ (read : Finset V → ℝ) (out : Option V × ℕ),
        out ∈ (P.run read).support →
          out.2 ≤ Nat.clog 2 (M + 1) *
            (((8 * (levels + 1)) * ((exponent + 1) * Nat.clog 2 (scale + 2))) *
              ((levels + 1) * (Nat.clog 2 n + 3) * (Q n + n)))) ∧
      (∀ (G : WeightedGraph V), InputPromise M G →
        mass (P.eval G.cut)
          (fun out => ¬∃ v, out = some v ∧ v ∈ R ∧
            ∀ w ∈ R, stValue G w s ≤ stValue G v s) ≤
          (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent)) := by
  refine ⟨sourceMaxTree family n R s levels scale exponent, ?_, ?_⟩
  · exact fun read out hout => RTree.cost_le _ read hout
  · exact fun G hG => sourceMaxTree_failure_le family hvn hQ hnscale G hG R s
      levels exponent hlevels hR hs

-- This branch remains conditional on the selected terminal being a maximum.
-- Composing its cost and failure with a bounded GuideSwitchTree is unallocated.
theorem publicSourceSwitch {V N : Type} [Fintype V] [DecidableEq V]
    [Fintype N] [DecidableEq N] {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N)
    (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ) (has : T.source ≠ T.label a)
    (hbranch : IsCentroidBranch T.tree T.centroid C) :
    ∃ P : Prog (Finset V) ℝ (V → Option ℝ),
      (∀ read : Finset V → ℝ, Prog.cost read P ≤ Q (Fintype.card V) + 1 +
        Prog.cost read (guideOneProgram family
          (Nat.clog 2 ((switchedGuide T C a ha).real.card + 1)) (switchedGuide T C a ha))) ∧
      (∀ (G : WeightedGraph V), InputPromise M G →
        (∀ t ∈ (switchedGuide T C a ha).realVertices,
          stValue G t T.source ≤ stValue G (T.label a) T.source) →
        (∀ (t : V) (value : ℝ), Prog.eval G.cut P t = some value →
          stValue G t T.source ≤ value) ∧
        (∀ t ∈ (switchedGuide T C a ha).realVertices,
          ∀ (S : Finset V), IsSTMinCut G t T.source S →
            ∀ (A : Finset N), (∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S) →
              (T.tree.crossSet A).card ≤ 2 →
              ∀ e ∈ T.tree.crossSet A, (e ∈ C ∨ T.tree.parent e ∈ C) →
                Prog.eval G.cut P t = some (stValue G t T.source))) := by
  refine ⟨sourceSwitchProgram family T C a ha, ?_, ?_⟩
  · exact fun read => sourceSwitchProgram_cost family T C a ha read
  · intro G hG hmax
    constructor
    · exact fun t value hvalue => sourceSwitchProgram_upper family G hG T C a ha has hmax hvalue
    · exact fun t ht S hS A hA hcross e he heC =>
        sourceSwitchProgram_complete family G hG T C a ha has hbranch hmax ht hS A hA hcross e he heC

end GH208Contract





end GHContracts2


/- Literal execution contract: apmc. -/
section APMCContracts2

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.DeterministicAPMCExpansion
open CutMatching Finset
open scoped Classical
noncomputable section

namespace APMCLiteral3

-- The public balanced procedure is charged on every reply function. Legal
-- responses imply actual termination and the required quarter-shore density.
theorem balanced_execution_contract {V : Type} [Fintype V] [DecidableEq V]
    (heven : Even (Fintype.card V)) (hN : 0 < Fintype.card V)
    (past : List (Matching V)) :
    ∀ read : MatchRequest V → Matching V,
      (balancedProgram heven (balancedRounds (Fintype.card V)) past []).cost read ≤
        balancedRounds (Fintype.card V) ∧
      (LegalResponses read →
        let result := (balancedProgram heven (balancedRounds (Fintype.card V)) past []).eval read
        result.complete = true ∧ ∀ S : Finset V,
          Fintype.card V ≤ 4 * S.card → 2 * S.card ≤ Fintype.card V →
          (S.card : ℝ) ≤ 4 * (historyGraph result.history).cut S) := by
  intro read
  refine ⟨balancedProgram_cost heven read _ past [], ?_⟩
  intro hlegal
  have hcomplete := balancedProgram_finishes heven hN read hlegal past
  refine ⟨hcomplete, ?_⟩
  intro S hquarter hhalf
  have hnone := balancedProgram_spec heven read _ past [] hcomplete S
  by_contra h
  exact hnone ⟨hquarter, hhalf, lt_of_not_ge h⟩

-- The explicit graph is the output of four executed balanced games. Its
-- quarter density is derived here, rather than supplied as an extra premise.
theorem executed_peeling_contract {V : Type} [Fintype V] [DecidableEq V]
    (heven : Even (Fintype.card V)) (hN : 0 < Fintype.card V)
    (read : MatchRequest V → Matching V) (hlegal : LegalResponses read)
    (past : List (Matching V)) :
    let H := historyGraph ((balancedBatch heven 4 past).eval read).history
    4 * (peeled H).card < Fintype.card V ∧
      2 * H.cut (peeled H) ≤ ((peeled H).card : ℝ) ∧
      (∀ S, ¬ SparseHalf H (peeled H) S) ∧
      ∀ S : Finset V, S ⊆ (peeled H)ᶜ →
        min (S.card : ℝ) (((peeled H)ᶜ \ S).card : ℝ) ≤
          2 * H.localCut (peeled H)ᶜ S := by
  let H := historyGraph ((balancedBatch heven 4 past).eval read).history
  have hdense : QuarterDense H := balancedBatch_four_dense heven hN read hlegal past
  have hinv := peeled_invariant H hdense hN
  refine ⟨hinv.small, hinv.boundary, peeled_stable H, ?_⟩
  intro S hS
  exact stable_expansion H (peeled_stable H) hS

-- The tree is fixed before all response functions. Its literal bound counts
-- matching requests, not graph-cut queries. Full normalization is charged.
theorem actual_player_contract {V : Type} [Fintype V] [DecidableEq V]
    (heven : Even (Fintype.card V)) :
    ∃ tree : DTree (MatchRequest V) (Matching V) (Option (BalancedResult V))
        (16 * (⌈64 / gapConstant * Real.log (Fintype.card V : ℝ)⌉₊ + 1) + 4),
      (∀ read : MatchRequest V → Matching V,
        (cutPlayer heven).cost read ≤
          16 * (⌈64 / gapConstant * Real.log (Fintype.card V : ℝ)⌉₊ + 1) + 4 ∧
        tree.run read = (some ((cutPlayer heven).eval read), (cutPlayer heven).cost read)) ∧
      ∀ read : MatchRequest V → Matching V, LegalResponses read →
        0 < Fintype.card V →
        ∃ result : BalancedResult V,
          tree.eval read = some result ∧
          result = (normalizedRuns heven 4 []).eval read ∧
          result.complete = true ∧
          ∀ S : Finset V,
            min (S.card : ℝ) (Sᶜ.card : ℝ) ≤ (historyGraph result.history).cut S := by
  refine ⟨(cutPlayer heven).toDTree (normalizedRounds (Fintype.card V)), ?_, ?_⟩
  · intro read
    have hcost := cutPlayer_cost heven read
    exact ⟨hcost, Prog.toDTree_run read _ _ hcost⟩
  · intro read hlegal hN
    have hcost := cutPlayer_cost heven read
    have hcorrect := cutPlayer_expands heven hN read hlegal
    exact ⟨(cutPlayer heven).eval read, Prog.toDTree_eval read _ _ hcost,
      rfl, hcorrect.1, hcorrect.2⟩

end APMCLiteral3




end

end APMCContracts2


/- Literal execution contract: quantum-forest. -/
section QuantumForestContracts2

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest
noncomputable section
open ProductPrograms QuantumQueryComplexity
open scoped Classical ENNReal Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

-- Literal public-before-hidden-input endpoint, including actual residual edges.
theorem check_forest_public (n : ℕ) (E : LearnedEdges n) (eta : ℝ) (heta : 0 < eta) :
    ∃ T : ProductTree n (CutQueryComplexity.StarContraction2022.Quantum.Forest.State n) (forestBudget n eta),
      (∀ read out, out ∈ (RTree.run read T).support → out.2 ≤ forestBudget n eta) ∧
      ∀ G : CapacityGraph (Fin n) 1, KnownSubgraph E G →
        (∀ F ∈ (T.eval (productRead G)).support,
          F.val ⊆ G.toWeighted.support.edgeFinset \ E ∧ F.graph.IsAcyclic ∧ F.val.card ≤ n - 1) ∧
        CutQueryComplexity.Probability.mass (T.eval (productRead G))
          (fun F => ¬IsSpanningForest (residualGraph G E).toWeighted F.graph) ≤ ENNReal.ofReal eta ∧
        1 - eta ≤ T.successProb (productRead G)
          (fun F => IsSpanningForest (residualGraph G E).toWeighted F.graph) :=
  forestRun_public n E eta heta

-- Literal guarantee for the implemented physical algorithm, not a supplied oracle.
theorem check_forest_physical (n : ℕ) (E : LearnedEdges n) (eta : ℝ) (G : CapacityGraph (Fin n) 1)
    (hE : KnownSubgraph E G) (heta : 0 < eta) :
    1 - eta ≤ goodProb (productTreeAlg (forestRun n E eta)).readout
      (fun F => IsSpanningForest (residualGraph G E).toWeighted F.graph)
      ((productTreeAlg (forestRun n E eta)).state (capacityRead G)
        (12 * productBits n 1 * forestBudget n eta)) :=
  forestRun_physical_successProb E eta G hE heta

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest



end QuantumForestContracts2


/- Literal execution contract: randomized. -/
section RandomizedContracts2

/-! Test-only literal execution contracts for the GH reduction. -/

set_option autoImplicit false

namespace CutQueryComplexity.GHRepetitionContracts
noncomputable section
open scoped Classical ENNReal BigOperators
open GHReduction Probability WeightedGraph

section Plumbing
variable {I A O J : Type} [DecidableEq J] {q : ℕ}

theorem table_cons_eval (fallback : O) (f : J → RTree I A O q)
    (j : J) (L : List J) (read : I → A) :
    (randomTableAux fallback f (j :: L)).eval read =
      ((f j).eval read).bind (fun value =>
        ((randomTableAux fallback f L).eval read).map
          (fun output => Function.update output j value)) := by
  simp only [randomTableAux, RTree.eval_cast, RTree.eval_bind, RTree.eval_map]

theorem table_cons_run (fallback : O) (f : J → RTree I A O q)
    (j : J) (L : List J) (read : I → A) :
    RTree.run read (randomTableAux fallback f (j :: L)) =
      (RTree.run read (f j)).bind (fun first =>
        (RTree.run read (randomTableAux fallback f L)).map
          (fun tail => (Function.update tail.1 j first.1, first.2 + tail.2))) := by
  simp only [randomTableAux, RTree.run_cast, RTree.run_bind, random_run_map,
    PMF.map_comp]
  rfl

theorem table_every_oracle [Fintype J] (fallback : O) (f : J → RTree I A O q)
    (read : I → A) {p : (J → O) × ℕ}
    (hp : p ∈ (RTree.run read (randomTable fallback f)).support) :
    p.2 ≤ Fintype.card J * q := RTree.cost_le _ _ hp

theorem repeat_succ_run (T : RTree I A O q) (h : ℕ) (read : I → A) :
    RTree.run read (randomRepeat T (h + 1)) =
      (RTree.run read T).bind (fun first =>
        (RTree.run read (randomRepeat T h)).map
          (fun tail => (first.1 :: tail.1, first.2 + tail.2))) := by
  simp only [randomRepeat, RTree.run_cast, RTree.run_bind, random_run_map,
    PMF.map_comp]
  rfl

theorem repeat_length (T : RTree I A O q) (h : ℕ) (read : I → A)
    {L : List O} (hL : L ∈ ((randomRepeat T h).eval read).support) : L.length = h := by
  rw [randomRepeat_eval] at hL
  exact independentSamples_length _ _ hL

end Plumbing

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

theorem pruning_run_preserves_realized_count {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials : ℕ) (T : GuideTree V N)
    (read : Finset V → ℝ) :
    RTree.run read (guidePruneTrialsTree family n trials T) =
      (RTree.run read (randomRepeat (guidePruneTree family n T) trials)).map
        (fun p => ((fun t => bestEstimates (p.1.map
          (fun output => candidateEstimate (output t)))), p.2)) := by
  exact random_run_map _ _ read

theorem pruning_fresh_eval {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials : ℕ) (T : GuideTree V N)
    (read : Finset V → ℝ) :
    (guidePruneTrialsTree family n trials T).eval read =
      (independentSamples ((guidePruneTree family n T).eval read) trials).map
        (fun L t => bestEstimates (L.map (fun output => candidateEstimate (output t)))) := by
  rw [guidePruneTrialsTree, RTree.eval_map, randomRepeat_eval]

/-- Public tree selection, before any hidden input, with the literal hard cap. -/
theorem pruning_public_contract {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials : ℕ) (T : GuideTree V N) :
    ∃ P : RTree (Finset V) ℝ (V → Option ℝ) (trials * guideOneGlobalBudget Q n),
      P = guidePruneTrialsTree family n trials T ∧
      (∀ read (out : (V → Option ℝ) × ℕ),
        out ∈ (RTree.run read P).support → out.2 ≤ trials * guideOneGlobalBudget Q n) ∧
      (∀ read, P.eval read =
        (independentSamples ((guidePruneTree family n T).eval read) trials).map
          (fun L t => bestEstimates (L.map (fun output => candidateEstimate (output t))))) := by
  refine ⟨guidePruneTrialsTree family n trials T, rfl, ?_, ?_⟩
  · intro read out hout
    exact RTree.cost_le _ _ hout
  · exact pruning_fresh_eval family n trials T

theorem pruning_supported_upper_bound {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (trials : ℕ) {output : V → Option ℝ}
    (hout : output ∈ ((guidePruneTrialsTree family n trials T).eval G.cut).support)
    (t : V) (value : ℝ) (hvalue : output t = some value) :
    stValue G t T.source ≤ value :=
  guidePruneTrialsTree_above family G hG T hvn hQ trials hout t value hvalue

/-- Every graph, source-branch, target and two-crossing premise is explicit. -/
theorem pruning_geometric_failure {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (trials : ℕ)
    (keep delete : frontierProxies T.tree T.centroid) (hne : keep ≠ delete)
    (hs : T.sourceNode ∉ frontierBranch T.tree T.centroid delete)
    (t : N) (ht : t ∈ T.real) (htkeep : t ∈ frontierBranch T.tree T.centroid keep)
    (S : Finset V) (hS : IsSTMinCut G (T.label t) T.source S)
    (A : Finset N) (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S)
    (hcross : (T.tree.crossSet A).card ≤ 2)
    (e : N) (he : e ∈ T.tree.crossSet A)
    (heB : e ∈ frontierBranch T.tree T.centroid delete ∨
      T.tree.parent e ∈ frontierBranch T.tree T.centroid delete) :
    mass ((guidePruneTrialsTree family n trials T).eval G.cut)
      (fun output => output (T.label t) ≠ some (stValue G (T.label t) T.source)) ≤
        ENNReal.ofReal (3 / 4 : ℝ) ^ trials :=
  guidePruneTrialsTree_failure_le family G hG T hvn hQ trials keep delete hne hs
    t ht htkeep S hS A hA hcross e he heB

theorem pruning_table_every_oracle {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials entries : ℕ) (T : GuideTree V N)
    (read : Finset V → ℝ) {out : (Fin entries → V → Option ℝ) × ℕ}
    (hout : out ∈ (RTree.run read
      (randomTable (fun _ => none)
        (fun _ : Fin entries => guidePruneTrialsTree family n trials T))).support) :
    out.2 ≤ entries * (trials * guideOneGlobalBudget Q n) := by
  simpa only [Fintype.card_fin] using RTree.cost_le _ _ hout

theorem pruning_table_supported_upper_bound {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (trials entries : ℕ) {output : Fin entries → V → Option ℝ}
    (hout : output ∈ ((randomTable (fun _ => none)
      (fun _ : Fin entries => guidePruneTrialsTree family n trials T)).eval G.cut).support)
    (j : Fin entries) (t : V) (value : ℝ) (hvalue : output j t = some value) :
    stValue G t T.source ≤ value := by
  have hj := randomTable_entry_support (fun _ => none)
    (fun _ : Fin entries => guidePruneTrialsTree family n trials T) G.cut hout j
  exact pruning_supported_upper_bound family G hG T hvn hQ trials hj t value hvalue

/-- The table union bound is instantiated with the actual amplified pruning tree. -/
theorem pruning_table_failure {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (trials entries : ℕ)
    (keep delete : frontierProxies T.tree T.centroid) (hne : keep ≠ delete)
    (hs : T.sourceNode ∉ frontierBranch T.tree T.centroid delete)
    (t : N) (ht : t ∈ T.real) (htkeep : t ∈ frontierBranch T.tree T.centroid keep)
    (S : Finset V) (hS : IsSTMinCut G (T.label t) T.source S)
    (A : Finset N) (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S)
    (hcross : (T.tree.crossSet A).card ≤ 2)
    (e : N) (he : e ∈ T.tree.crossSet A)
    (heB : e ∈ frontierBranch T.tree T.centroid delete ∨
      T.tree.parent e ∈ frontierBranch T.tree T.centroid delete) :
    mass ((randomTable (fun _ => none)
      (fun _ : Fin entries => guidePruneTrialsTree family n trials T)).eval G.cut)
      (fun output => ¬∀ j, output j (T.label t) = some (stValue G (T.label t) T.source)) ≤
        (entries : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ trials := by
  have h := randomTable_failure_le (fun _ => none)
    (fun _ : Fin entries => guidePruneTrialsTree family n trials T) G.cut
    (fun _ output => output (T.label t) = some (stValue G (T.label t) T.source))
    (fun _ => ENNReal.ofReal (3 / 4 : ℝ) ^ trials)
    (fun _ => guidePruneTrialsTree_failure_le family G hG T hvn hQ trials keep delete hne hs
      t ht htkeep S hS A hA hcross e he heB)
  simpa using h

end
end CutQueryComplexity.GHRepetitionContracts

end RandomizedContracts2


/- Literal execution contract: quantum-neighbors. -/
section QuantumNeighborsContracts1

/-! Evidence only: literal constructors, unconditional transcript caps, and
conditional honest-cut correctness. No partition producer is assumed or defined. -/

set_option autoImplicit false

namespace APMCAccountingContracts

open CutQueryComplexity CutQueryComplexity.WeightedGraph
open CutQueryComplexity.AllPairsAudit
open CutQueryComplexity.AllPairs CutQueryComplexity.DeterministicAPMCExpansion
open CutQueryComplexity.DeterministicAPMCExpansion.Decomposition
open CutQueryComplexity.DeterministicAPMCExpansion.Pruning
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- One fixed literal tree serves every hidden graph; the query cap has no
graph or partition-invariant premise. Honest correctness keeps those premises. -/
theorem literal_partition_contract (p : V → V) (b R β : ℕ) :
    ∃ T : DTree (Finset V) ℝ (Answers V) (partitionRecoveryBudget V b R β),
      T = totalPartitionAnswers p b R β ∧
      (∀ oracle : Finset V → ℝ, T.cost oracle ≤ partitionRecoveryBudget V b R β) ∧
      (∀ G : WeightedGraph V, Unweighted G → (∀ v, 2 ≤ G.degree v) →
        0 < b → 0 < R → 0 < β → Fintype.card V ≤ b * β →
        AdditivePartition G p b R β →
        (∑ v, G.cut (fiber p v)) ≤
          2 * (b : ℝ) * Fintype.card V * Nat.clog 2 (Fintype.card V) →
        allPairsGood G (T.eval G.cut)) := by
  refine ⟨totalPartitionAnswers p b R β, rfl, ?_, ?_⟩
  · exact totalPartitionAnswers_cost p b R β
  · intro G hG hdegree hb hR hβ hN hexpand hboundary
    exact totalPartitionAnswers_correct hG hdegree p hb hR hβ hN hexpand hboundary

/-- The actual padded query program is substituted and its exact output
restricted, with the same advertised budget on every original oracle. -/
theorem literal_padding_contract (p : Padded V → Padded V) (b R β : ℕ) :
    ∃ T : DTree (Finset V) ℝ (Answers V) (partitionRecoveryBudget (Padded V) b R β),
      T = unpadProgram (totalPartitionAnswers p b R β) ∧
      (∀ oracle : Finset V → ℝ,
        T.cost oracle ≤ partitionRecoveryBudget (Padded V) b R β) ∧
      (∀ G : WeightedGraph V, Unweighted G →
        0 < b → 0 < R → 0 < β → Fintype.card (Padded V) ≤ b * β →
        AdditivePartition (paddedGraph G) p b R β →
        (∑ v, (paddedGraph G).cut (fiber p v)) ≤
          2 * (b : ℝ) * Fintype.card (Padded V) * Nat.clog 2 (Fintype.card (Padded V)) →
        allPairsGood G (T.eval G.cut)) := by
  refine ⟨unpadProgram (totalPartitionAnswers p b R β), rfl, ?_, ?_⟩
  · exact unpadProgram_cost (totalPartitionAnswers p b R β)
  · intro G hG hb hR hβ hN hexpand hboundary
    apply unpadProgram_correct
    exact totalPartitionAnswers_correct (padded_unweighted hG) (padded_min_degree G)
      p hb hR hβ hN hexpand hboundary

theorem literal_padding_eval (p : Padded V → Padded V) (b R β : ℕ)
    (G : WeightedGraph V) :
    (unpadProgram (totalPartitionAnswers p b R β)).eval G.cut =
      restrictAnswers ((totalPartitionAnswers p b R β).eval (paddedGraph G).cut) := by
  simp only [unpadProgram, DTree.eval_cast, DTree.eval_map,
    CutQueryComplexity.DeterministicAPMCExpansion.padded_substitute_eval]

/-- The input to both-child progress is the actual integer tolerance, never
an assumed logarithmic depth or a stored successful-query budget. -/
theorem literal_split_contract {q R left right : ℕ} (hR : 1 ≤ R)
    (hq : 64 * R < q) (hsum : left + right = q)
    (hleft : localTolerance q R < left) (hright : localTolerance q R < right) :
    32 * R * localTolerance q R ≤ q ∧
      ShrinkStep (64 * R) q left ∧ ShrinkStep (64 * R) q right :=
  ⟨localTolerance_budget q R, split_child_shrink hR hq hsum hleft hright⟩

theorem actual_work_tree_bounds (tree : WorkTree V) (R N : ℕ) (hR : 1 ≤ R)
    (hc : tree.Covered) (hs : tree.Shrinks (64 * R)) (hp : tree.Positive)
    (hN : tree.vertices.card ≤ N) :
    tree.depth ≤ 64 * R * Nat.clog 2 (N + 1) ∧
      tree.mass ≤ 64 * R * Nat.clog 2 (N + 1) * N := by
  have ha : 0 < 64 * R := by omega
  exact ⟨tree.depth_le_clog (64 * R) N ha hs hp hN,
    tree.mass_le_clog (64 * R) N ha hc hs hp hN⟩

end
end APMCAccountingContracts


end QuantumNeighborsContracts1


/- Literal execution contract: quantum-uniform. -/
section QuantumUniformContracts1

set_option autoImplicit false



namespace CostBoundsContract
open CutQueryComplexity.StarContraction2022.Quantum

/-- Literal numerical contract: the same C works before n, r and eta. -/
theorem universal :
    ∃ C : ℝ, 0 < C ∧ ∀ (n r : ℕ), 2 ≤ n → 1 ≤ r →
      r ≤ ProductPrograms.rootThreshold n → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ((12 * productBits n 1 * (r * Forest.forestBudget n (eta / (r : ℝ)) + 1) : ℕ) : ℝ) ≤
        C * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 3 *
          ((ProductPrograms.logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 :=
  Forest.exists_forest_physical_constant

/-- Literal fixed-tolerance contract, with C depending only on eta. -/
theorem fixed {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n r : ℕ), 2 ≤ n → 1 ≤ r →
      r ≤ ProductPrograms.rootThreshold n →
      ((12 * productBits n 1 * (r * Forest.forestBudget n (eta / (r : ℝ)) + 1) : ℕ) : ℝ) ≤
        C * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 5 :=
  Forest.exists_fixed_tolerance_forest_constant heta heta1

end CostBoundsContract

end QuantumUniformContracts1

#audit_cut_decl APMCLiteral3.balanced_execution_contract
#audit_cut_decl APMCLiteral3.executed_peeling_contract
#audit_cut_decl APMCLiteral3.actual_player_contract
#audit_cut_decl GH208Contract.publicClassify
#audit_cut_decl GH208Contract.publicSourceMaximum
#audit_cut_decl GH208Contract.publicSourceSwitch
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Forest.check_forest_public
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Forest.check_forest_physical
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.table_cons_eval
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.table_cons_run
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.table_every_oracle
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.repeat_succ_run
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.repeat_length
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.pruning_run_preserves_realized_count
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.pruning_fresh_eval
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.pruning_public_contract
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.pruning_supported_upper_bound
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.pruning_geometric_failure
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.pruning_table_every_oracle
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.pruning_table_supported_upper_bound
#audit_cut_decl CutQueryComplexity.GHRepetitionContracts.pruning_table_failure
#audit_cut_decl APMCAccountingContracts.literal_partition_contract
#audit_cut_decl APMCAccountingContracts.literal_padding_contract
#audit_cut_decl APMCAccountingContracts.literal_padding_eval
#audit_cut_decl APMCAccountingContracts.literal_split_contract
#audit_cut_decl APMCAccountingContracts.actual_work_tree_bounds
#audit_cut_decl CostBoundsContract.universal
#audit_cut_decl CostBoundsContract.fixed


/- Actual execution contract: gh. -/
section GHContracts3

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction
open scoped Classical ENNReal
open CutQueryComplexity.Probability

namespace GH209Contract

-- Exact continuation law even for arbitrary oracle replies and invalid choices.
theorem continuationLaw {V N : Type} [Fintype V] [DecidableEq V]
    [Fintype N] [DecidableEq N] {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n : ℕ) (T : GuideTree V N) (C : Finset N)
    (read : Finset V → ℝ) (choice : Option N) :
    (guideSwitchContinuation family n T C choice).eval read =
      match choice with
      | none => PMF.pure (fun _ : V => (none : Option ℝ))
      | some a => if ha : a ∈ outsideGuideNodes T C then
          PMF.pure ((sourceSwitchGlobalTree family n T C a ha).eval read)
        else PMF.pure (fun _ : V => (none : Option ℝ)) := by
  cases choice with
  | none => simp [guideSwitchContinuation]
  | some a =>
    by_cases ha : a ∈ outsideGuideNodes T C
    · simp only [guideSwitchContinuation, ha, dite_true, RTree.eval,
        RTree.run_ofDeterministic, PMF.pure_map]
      rfl
    · simp [guideSwitchContinuation, ha]

-- One public tree is chosen before the hidden graph and all correctness premises.
-- Its bad event includes one-sidedness and all retained target equalities at once.
theorem publicGuideSwitch {V N : Type} [Fintype V] [DecidableEq V]
    [Fintype N] [DecidableEq N] {M n scale : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (T : GuideTree V N) (C : Finset N)
    (levels exponent : ℕ) :
    ∃ P : RTree (Finset V) ℝ (V → Option ℝ)
        (Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent + sourceSwitchBudget Q n),
      (∀ (read : Finset V → ℝ) (out : (V → Option ℝ) × ℕ),
        out ∈ (P.run read).support → out.2 ≤
          Nat.clog 2 (M + 1) * sourceThresholdBudget Q n levels scale exponent + sourceSwitchBudget Q n) ∧
      (∀ read : Finset V → ℝ, P.eval read =
        ((guideMaximumTree family n T C levels scale exponent).eval read).bind (fun choice =>
          match choice with
          | none => PMF.pure (fun _ : V => (none : Option ℝ))
          | some a => if ha : a ∈ outsideGuideNodes T C then
              PMF.pure ((sourceSwitchGlobalTree family n T C a ha).eval read)
            else PMF.pure (fun _ : V => (none : Option ℝ)))) ∧
      (Fintype.card V ≤ n → SizeRegular n Q → n ≤ scale →
        ∀ (G : WeightedGraph V), InputPromise M G →
          thresholdLevels n ≤ levels → T.sourceNode ∈ C →
          IsCentroidBranch T.tree T.centroid C → (outsideGuideNodes T C).Nonempty →
          mass (P.eval G.cut) (fun output => ¬(
            (∀ t value, output t = some value → stValue G t T.source ≤ value) ∧
            (∀ t ∈ T.real, t ∉ C → ∀ S : Finset V, IsSTMinCut G (T.label t) T.source S →
              ∀ A : Finset N, (∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S) →
                (T.tree.crossSet A).card ≤ 2 → ∀ e ∈ T.tree.crossSet A,
                  (e ∈ C ∨ T.tree.parent e ∈ C) →
                    output (T.label t) = some (stValue G (T.label t) T.source)))) ≤
            (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent)) := by
  refine ⟨guideSwitchTree family n T C levels scale exponent, ?_, ?_, ?_⟩
  · exact fun read out hout => RTree.cost_le _ read hout
  · intro read
    rw [guideSwitchTree, RTree.eval_bind]
    apply congrArg (PMF.bind ((guideMaximumTree family n T C levels scale exponent).eval read))
    funext choice
    exact continuationLaw family n T C read choice
  · exact fun hvn hQ hnscale G hG hlevels hs hbranch houtside =>
      guideSwitchTree_failure_le family hvn hQ hnscale G hG T C levels exponent
        hlevels hs hbranch houtside

end GH209Contract





end GHContracts3


/- Actual execution contract: quantum-neighbors. -/
section QuantumNeighborsContracts2

/-! Evidence only: actual public cube-root schedule, matching requests and
subtype query adapters. No routed matching or decomposition producer is supplied. -/

set_option autoImplicit false

namespace APMCCubeRootContracts

open CutQueryComplexity CutQueryComplexity.WeightedGraph
open CutQueryComplexity.DeterministicAPMCExpansion.CutMatching
open CutQueryComplexity.DeterministicAPMCExpansion.Pruning
open scoped Classical
noncomputable section

theorem cube_root_schedule (N : ℕ) :
    0 < cubeRoot N ∧ N ≤ cubeRoot N ^ 3 ∧ cubeRoot N ≤ N + 1 ∧
      (∀ t : ℕ, 0 < t → N ≤ t ^ 3 → cubeRoot N ≤ t) ∧
      (0 < N → (cubeRoot N - 1) ^ 3 < N) ∧
      2 ≤ roundBudget N ∧ roundBudget N ≤ roundCoefficient * sizeLog N :=
  ⟨cubeRoot_pos N, le_cubeRoot_pow N, cubeRoot_le_succ N,
    fun _ ht hN => cubeRoot_min ht hN, pred_cubeRoot_pow_lt,
    roundBudget_ge_two N, roundBudget_le N⟩

theorem cube_root_zero : cubeRoot 0 = 1 := by
  have hp := cubeRoot_pos 0
  have hu := cubeRoot_le_succ 0
  omega

/-- The exact sixteen balanced subgames and four final matching requests. -/
theorem normalization_charge (q N : ℕ) :
    normalizedRounds (q * (2 * cubeRoot N)) =
      16 * balancedRounds (q * (2 * cubeRoot N)) + 4 := rfl

variable {V : Type} [Fintype V] [DecidableEq V]

/-- q actual part vertices, each with the public 2*cubeRoot N clone count. -/
abbrev PartClones (W : Finset V) (N : ℕ) := PartVertex W × Fin (2 * cubeRoot N)

theorem partClones_card (W : Finset V) (N : ℕ) :
    Fintype.card (PartClones W N) = W.card * (2 * cubeRoot N) := by
  simp only [PartClones, Fintype.card_prod, partVertex_card, Fintype.card_fin]

theorem partClones_even (W : Finset V) (N : ℕ) :
    Even (Fintype.card (PartClones W N)) := by
  rw [partClones_card]
  exact ⟨W.card * cubeRoot N, by ring⟩

theorem partClones_pos (W : Finset V) (N : ℕ) (hW : 0 < W.card) :
    0 < Fintype.card (PartClones W N) := by
  rw [partClones_card]
  exact Nat.mul_pos hW (Nat.mul_pos (by decide) (cubeRoot_pos N))

/-- No legality or hidden-graph premise is used to bound actual requests. -/
theorem literal_player_request_bound (W : Finset V) (N : ℕ) (hsize : W.card ≤ N)
    (read : MatchRequest (PartClones W N) → Matching (PartClones W N)) :
    (cutPlayer (partClones_even W N)).cost read ≤ roundBudget N := by
  have hs : normalizedRounds (Fintype.card (PartClones W N)) ≤ roundBudget N := by
    simpa only [partClones_card] using local_rounds_le hsize
  exact (cutPlayer_cost (partClones_even W N) read).trans hs

/-- A literal public tree is chosen before any response function. Its exact
run shows that the cap wrapper never truncates, even on illegal responses. -/
theorem literal_capped_player (W : Finset V) (N : ℕ) (hsize : W.card ≤ N) :
    ∃ T : DTree (MatchRequest (PartClones W N)) (Matching (PartClones W N))
        (Option (BalancedResult (PartClones W N))) (roundBudget N),
      T = Prog.toDTree (cutPlayer (partClones_even W N)) (roundBudget N) ∧
      (∀ read, DTree.run read T =
        (some ((cutPlayer (partClones_even W N)).eval read),
          (cutPlayer (partClones_even W N)).cost read)) ∧
      (∀ read, T.cost read ≤ roundBudget N) ∧
      (∀ read, T.cost read ≤ roundCoefficient * sizeLog N) := by
  refine ⟨Prog.toDTree (cutPlayer (partClones_even W N)) (roundBudget N), rfl,
    ?_, ?_, ?_⟩
  · intro read
    exact Prog.toDTree_run read _ _ (literal_player_request_bound W N hsize read)
  · intro read
    exact DTree.cost_le _ _
  · intro read
    exact (DTree.cost_le _ read).trans (roundBudget_le N)

/-- This is the accepted conditional game guarantee. It does not assert that
a cut-query flow implementation has produced legal matching responses. -/
theorem literal_player_expands (W : Finset V) (N : ℕ) (hsize : W.card ≤ N)
    (hW : 0 < W.card)
    (read : MatchRequest (PartClones W N) → Matching (PartClones W N))
    (hlegal : LegalResponses read) :
    ∃ out : BalancedResult (PartClones W N),
      DTree.run read (Prog.toDTree (cutPlayer (partClones_even W N)) (roundBudget N)) =
        (some out, (cutPlayer (partClones_even W N)).cost read) ∧
      out.complete = true ∧ ∀ S : Finset (PartClones W N),
        min (S.card : ℝ) (Sᶜ.card : ℝ) ≤ (historyGraph out.history).cut S := by
  refine ⟨(cutPlayer (partClones_even W N)).eval read, ?_, ?_⟩
  · exact Prog.toDTree_run read _ _ (literal_player_request_bound W N hsize read)
  · exact cutPlayer_expands (partClones_even W N) (partClones_pos W N hW) read hlegal

/-- Three actual ambient cut queries, chosen before the hidden graph. -/
theorem literal_subtype_query (W : Finset V) (S : Finset (PartVertex W)) :
    ∃ T : DTree (Finset V) ℝ ℝ 3,
      T = subtypeQuery W S ∧
      (∀ oracle, DTree.run oracle T = (subtypeOracle W oracle S, 3)) ∧
      (∀ G : WeightedGraph V, T.eval G.cut = (partGraph G W).cut S) :=
  ⟨subtypeQuery W S, rfl, subtypeQuery_run W S, fun G => subtypeQuery_eval G W S⟩

/-- The supplied public tree is arbitrary, with no solver correctness assumed.
Its adaptive semantics and realized costs are transported by the real adapter. -/
theorem literal_subtype_program {O : Type} {q : ℕ} (W : Finset V)
    (T : DTree (Finset (PartVertex W)) ℝ O q) :
    ∃ U : DTree (Finset V) ℝ O (q * 3),
      U = subtypeProgram W T ∧
      (∀ oracle, U.eval oracle = T.eval (subtypeOracle W oracle)) ∧
      (∀ oracle, U.cost oracle = T.cost (subtypeOracle W oracle) * 3) ∧
      (∀ oracle, U.cost oracle ≤ q * 3) ∧
      (∀ G : WeightedGraph V, U.eval G.cut = T.eval (partGraph G W).cut) :=
  ⟨subtypeProgram W T, rfl, subtypeProgram_eval_public W T,
    subtypeProgram_cost W T, subtypeProgram_cost_le W T, fun G => subtypeProgram_eval G W T⟩

/-- Actual local cardinalities avoid an ambient-cardinality charge at every node. -/
theorem literal_subtype_sizes (W : Finset V) :
    Fintype.card (PartVertex W) = W.card ∧
      Fintype.card (PartVertex W ⊕ Fin 2) = W.card + 2 ∧
      searchDepth (PartVertex W ⊕ Fin 2) = Nat.clog 2 (W.card + 2) :=
  ⟨partVertex_card W, partNetwork_card W, partNetwork_searchDepth W⟩

end
end APMCCubeRootContracts


end QuantumNeighborsContracts2


/- Actual execution contract: apmc. -/
section APMCContracts3

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.DeterministicAPMCExpansion
open Flow CutMatching AllPairsAudit Finset
open CutQueryComplexity.DeterministicAPMCExpansion.Pruning
open CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds
open scoped Classical
noncomputable section

namespace APMCLiteral4

-- This is a bound on the uncapped interpreter for every real-valued reply
-- function. It does not use the sharper honest-unit-graph bound.
theorem actual_coarse_cost {V : Type} [Fintype V] [DecidableEq V] {b : ℕ}
    (β : ℝ) (heven : Even (Fintype.card (Clone V b))) (read : Finset V → ℝ) :
    (executedCutPlayer β heven).cost read ≤
      ((Fintype.card V * b + 1) *
        (bfsBudget V + (Fintype.card V * b + 1) * bfsBudget V)) *
      normalizedRounds (Fintype.card (Clone V b)) := by
  let Q := (Fintype.card V * b + 1) *
    (bfsBudget V + (Fintype.card V * b + 1) * bfsBudget V)
  have hQ (cut : Bisection (Clone V b)) : (matchingRound β cut).cost read ≤ Q := by
    have htotal : (∑ v, slotCount cut.shore v) ≤ Fintype.card V * b := by
      rw [sum_slotCount]
      simpa only [Clone, Fintype.card_prod, Fintype.card_fin] using card_le_univ cut.shore
    have hfuel : exactFuel (slotCount cut.shore) ≤ Fintype.card V * b + 1 :=
      Nat.add_le_add_right htotal 1
    apply (matchingRound_cost read β cut).trans
    exact Nat.mul_le_mul hfuel
      (Nat.add_le_add_left (Nat.mul_le_mul_right (bfsBudget V) hfuel) (bfsBudget V))
  have hcost := runMatchingGame_cost read β Q hQ (cutPlayer heven)
  exact hcost.trans (Nat.mul_le_mul_left Q (cutPlayer_cost heven (gameRead read β)))

-- Both fallback branches are public legal matchings. The operational
-- interpreter still stops on split/invalid; fallback is only semantic replay.
theorem replay_legality {V : Type} [Fintype V] [DecidableEq V] {b : ℕ}
    (read : Finset V → ℝ) (β : ℝ) :
    (∀ request : MatchRequest (Clone V b),
      (gameRead read β request).Crosses request.cut.shore) ∧
    (∀ cut : Bisection (Clone V b),
      roundResponse (MatchingRoundResult.split (cut := cut) ∅) = fallbackMatching cut ∧
      roundResponse (MatchingRoundResult.invalid (cut := cut)) = fallbackMatching cut) := by
  exact ⟨gameRead_legal read β, fun _ => ⟨rfl, rfl⟩⟩

-- A public sharp cap is imposed by toDTree, before the hidden graph. On
-- honest unit graphs the executed sharp theorem proves no truncation. The
-- outcome is either an actual sparse split or the actual certified history.
theorem capped_execution_and_certificate {V : Type} [Fintype V] [DecidableEq V]
    (β R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t)
    (hqpos : 1 ≤ Fintype.card V) (hq : Fintype.card V ≤ t ^ 3)
    (hrounds : normalizedRounds (Fintype.card (Clone V (2 * t))) ≤ R) :
    ∃ heven : Even (Fintype.card (Clone V (2 * t))),
      ∃ tree : DTree (Finset V) ℝ
          (Option (GameResult V (2 * t) (BalancedResult (Clone V (2 * t)))))
          (exactSharpBudget V R t * R),
        (∀ read, tree.cost read ≤ exactSharpBudget V R t * R) ∧
        ∀ G : WeightedGraph V, Unweighted G →
          ∃ outcome : GameResult V (2 * t) (BalancedResult (Clone V (2 * t))),
            tree.eval G.cut = some outcome ∧
            tree.cost G.cut = (executedCutPlayer (β : ℝ) heven).cost G.cut ∧
            outcome = (executedCutPlayer (β : ℝ) heven).eval G.cut ∧
            match outcome with
            | .split P =>
                (β : ℝ) < P.card ∧ (β : ℝ) < Pᶜ.card ∧
                  G.cut P < (2 * t : ℕ) * min (P.card : ℝ) (Pᶜ.card : ℝ)
            | .invalid => False
            | .complete out rounds =>
                out.complete = true ∧ rounds.length ≤ R ∧
                out.history = (rounds.map (fun round => round.pairs.matching)).reverse ∧
                (∀ S : Finset (Clone V (2 * t)),
                  min (S.card : ℝ) (Sᶜ.card : ℝ) ≤
                    (historyGraph (rounds.map (fun round => round.pairs.matching))).cut S) ∧
                (∀ round ∈ rounds, MatchingRoundCorrect G β round.cut round.routes round.pairs) ∧
                (∀ round ∈ rounds, FakeEdges.pairCount (marked round) =
                  round.cut.shore.card - round.routes.length) ∧
                (∀ T : Finset V, (FakeEdges.realCutCount (markedHistory rounds) T : ℝ) ≤
                  (R : ℝ) * G.cut T) ∧
                FakeCertificate G (FakeEdges.fakeGraph (markedHistory rounds)) (2 * t : ℕ) R ∧
                FakeEdges.edgeCount (markedHistory rounds) ≤ R * β * (2 * t) ∧
                (∀ v, FakeEdges.degreeTable (markedHistory rounds) v ≤ R * (2 * t)) ∧
                (∀ v, (FakeEdges.fakeGraph (markedHistory rounds)).degree v =
                  (FakeEdges.degreeTable (markedHistory rounds) v : ℝ)) ∧
                (∑ v, (FakeEdges.fakeGraph (markedHistory rounds)).degree v) =
                  2 * (FakeEdges.edgeCount (markedHistory rounds) : ℝ) := by
  have heven : Even (Fintype.card (Clone V (2 * t))) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact ⟨Fintype.card V * t, by ring⟩
  have hb : 0 < 2 * t := by omega
  have hV : 0 < Fintype.card V := hqpos
  let program := executedCutPlayer (β : ℝ) heven
  let budget := exactSharpBudget V R t * R
  refine ⟨heven, program.toDTree budget, ?_, ?_⟩
  · intro read
    exact DTree.cost_le _ _
  · intro G hG
    have hcost : program.cost G.cut ≤ budget :=
      (executedCutPlayer_cost G hG R t hR ht hqpos hq β heven).trans
        (Nat.mul_le_mul_left (exactSharpBudget V R t) hrounds)
    refine ⟨program.eval G.cut, Prog.toDTree_eval G.cut _ _ hcost,
      Prog.toDTree_cost G.cut _ _ hcost, rfl, ?_⟩
    have hcorrect := runMatchingGame_correct G hG β (Nat.cast_nonneg _) hb (cutPlayer heven)
    change GameCorrect G β (cutPlayer heven) (program.eval G.cut) at hcorrect
    cases hexec : program.eval G.cut with
    | split P =>
        rw [hexec] at hcorrect
        exact hcorrect
    | invalid =>
        rw [hexec] at hcorrect
        exact hcorrect
    | complete out rounds =>
        have hc := executedCutPlayer_complete G hG β (Nat.cast_nonneg _) hb hV
          heven out rounds hexec
        have hlength := hc.2.2.1.trans hrounds
        have hcert := completed_certificate G hG β R hb hV heven hrounds out rounds hexec
        refine ⟨hc.1, hlength,
          executedCutPlayer_history G hG β (Nat.cast_nonneg _) hb heven out rounds hexec,
          executedCutPlayer_rounds_expand G hG β (Nat.cast_nonneg _) hb hV
            heven out rounds hexec,
          hc.2.2.2, ?_, ?_, hcert.1, hcert.2.1, hcert.2.2,
          FakeEdges.fakeGraph_degree (markedHistory rounds),
          FakeEdges.sum_degrees (markedHistory rounds)⟩
        · intro round _
          exact pairCount_eq_deficit round.pairs
        · intro T
          exact (history_real_cut_le G β rounds hc.2.2.2 T).trans
            (mul_le_mul_of_nonneg_right
              (show (rounds.length : ℝ) ≤ R by exact_mod_cast hlength) (G.cut_nonneg T))

end APMCLiteral4




end

end APMCContracts3


/- Actual execution contract: quantum-uniform. -/
section QuantumUniformContracts2

set_option autoImplicit false



namespace WitnessContract209
open CutQueryComplexity QuantumQueryComplexity
open CutQueryComplexity.StarContraction2022.Quantum
open scoped Matrix

theorem coherent_adapter {I A J B W : Type} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]
    (select : J → I) (tag : J → A → B) :
    (taggedCall (W := W) select tag).len = 2 ∧
    ∀ (read : I → A) (ψ : QBasis J B W → ℂ),
      (taggedCall select tag).run read *ᵥ taggedEmbed ψ =
        taggedEmbed (oracleMat (fun j => tag j (read (select j))) *ᵥ ψ) :=
  ⟨taggedCall_len select tag, taggedCall_run select tag⟩

theorem public_witness (n t : ℕ) (ht : 0 < t) :
    ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
      (T : CutQAlg n 1 (DegreeWitness n) Work)
      (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) Work),
      R.len = minimumDegreeWitnessQueries n t ∧
      R.len ≤ 4 * t * minimumDegreeBaseBudget n + 1 ∧
      (∀ read, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ read out, T.prob read R.len out = minimumDegreeWitnessLaw n t ht read out) ∧
      (∀ (G : CapacityGraph (Fin n) 1),
        (∀ (_hn : 2 ≤ n) (v : Fin n) (a : CutAnswer n 1),
          0 < T.prob (capacityRead G) R.len (some (v, a)) →
          ProperShore ({v} : Finset (Fin n)) ∧ (a : ℕ) = G.cut {v}) ∧
        (0 < n → ∃ v : Fin n, G.cut {v} = (minimumDegreeValue G : ℕ) ∧
          (∀ u, G.cut {v} ≤ G.cut {u}) ∧
          1 - (8 / 9 : ℝ) ^ t ≤ T.prob (capacityRead G) R.len (some (v, capacityRead G {v})))) := exists_quantum_minimumDegree_witness n t ht

theorem empty (t : ℕ) (ht : 0 < t) (read : Finset (Fin 0) → CutAnswer 0 1) :
    (minimumDegreeWitnessRoutine 0 t ht).len = 0 ∧
    (minimumDegreeWitnessAlg 0 t ht).prob read 0 none = 1 := by
  exact ⟨by simp, minimumDegreeWitnessAlg_zero t ht read⟩

end WitnessContract209

end QuantumUniformContracts2


/- Actual execution contract: quantum-forest. -/
section QuantumForestContracts3

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Forest
noncomputable section
open ProductPrograms QuantumQueryComplexity
open scoped Classical ENNReal Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

-- Literal public tree, arbitrary-answer cap, unconditional soundness, and true minimum success.
theorem check_public_low_candidate (n r : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ T : ProductTree n (Candidate n) (r * forestBudget n (eta / (r : ℝ)) + 1),
      (∀ read out, out ∈ (RTree.run read T).support →
        out.2 ≤ r * forestBudget n (eta / (r : ℝ)) + 1) ∧
      ∀ G : CapacityGraph (Fin n) 1, ProductTreeSound T G ∧
        (2 ≤ n → mincutValue G.toWeighted < r →
          1 - eta ≤ T.successProb (productRead G)
            (fun out => ∃ S a, out = some (S, a) ∧ IsMinCut G.toWeighted S ∧
              decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)) := by
  have h := lowCandidate_public n r eta heta
  unfold LowMinimumCandidate at h
  exact h

-- Verification remains correct even when one or more forest calls fail to span.
theorem check_verified_soundness (n r : ℕ) (eta : ℝ) (G : CapacityGraph (Fin n) 1)
    (S : Finset (Fin n)) (a : CutAnswer n 1)
    (h : some (S, a) ∈ ((lowCandidate n r eta).eval (productRead G)).support) :
    ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S :=
  lowCandidate_sound n r eta G (some (S, a)) h

-- The actual adaptive forest outputs satisfy the full two-sided certificate relation.
theorem check_actual_threshold_certificate (n r : ℕ) (eta : ℝ) (heta : 0 < eta) (G : CapacityGraph (Fin n) 1) :
    1 - eta ≤ (certificateRun n r eta).successProb (productRead G)
      (fun B => (batchCertificate B).IsSubgraph G.toWeighted ∧
        (batchCertificate B).IsIntegral ∧
        (batchCertificate B).edgeMass ≤ (r * (n - 1) : ℕ) ∧
        ∀ S, min (r : ℝ) ((batchCertificate B).cut S) = min (r : ℝ) (G.toWeighted.cut S)) := by
  simpa only [IsThresholdCertificate, Fintype.card_fin] using
    certificateRun_certificate_successProb n r eta heta G

-- The implemented physical routine returns an actual minimum shore and exact original value.
theorem check_physical_minimum (n r : ℕ) (eta : ℝ) (heta : 0 < eta) (G : CapacityGraph (Fin n) 1)
    (hn : 2 ≤ n) (hlt : mincutValue G.toWeighted < r) :
    1 - eta ≤ goodProb (productTreeAlg (lowCandidate n r eta)).readout
      (fun out => ∃ S a, out = some (S, a) ∧ IsMinCut G.toWeighted S ∧
        decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
      ((productTreeAlg (lowCandidate n r eta)).state (capacityRead G)
        (12 * productBits n 1 * (r * forestBudget n (eta / (r : ℝ)) + 1))) := by
  have h := lowCandidate_physical_successProb n r eta heta G hn hlt
  unfold goodProb at h ⊢
  unfold LowMinimumCandidate at h
  convert h using 1
  congr 1
  funext b
  simp only [decide_eq_decide]

-- The analytic bound is for that same actual routine and keeps every numerical premise.
theorem check_physical_cost {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) (hrroot : r ≤ rootThreshold n)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ((productTreeRoutine (lowCandidate n r eta)).len : ℝ) ≤
      70860 * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 3 *
        ((logWidth n : ℝ) + Real.log (1 / eta)) ^ 2 :=
  lowCandidate_physical_cost hn hr hrroot heta heta1

end
end CutQueryComplexity.StarContraction2022.Quantum.Forest



end QuantumForestContracts3


/- Actual execution contract: randomized. -/
section RandomizedContracts3

/-! Evidence-only contracts for the actual dependent table and transcript interpreter. -/

set_option autoImplicit false

namespace CutQueryComplexity.GHDependentContracts
noncomputable section
open scoped Classical ENNReal BigOperators
open GHReduction Probability WeightedGraph

section DependentExecution
variable {I A J : Type} {O : J → Type} [DecidableEq J] {q : ℕ}

/-- The dependent bind sequence preserves outputs and adds actual query counts. -/
theorem table_cons_run (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (j : J) (L : List J) (read : I → A) :
    RTree.run read (dependentRandomTableAux fallback f (j :: L)) =
      (RTree.run read (f j)).bind (fun first =>
        (RTree.run read (dependentRandomTableAux fallback f L)).map
          (fun tail => (Function.update tail.1 j first.1, first.2 + tail.2))) := by
  simp only [dependentRandomTableAux, RTree.run_cast, RTree.run_bind, random_run_map,
    PMF.map_comp]
  rfl

theorem table_every_transcript [Fintype J] (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (answer : TranscriptOracle.AnswerPolicy I A)
    (history : List (I × A)) {out : ((j : J) → O j) × ℕ}
    (hout : out ∈ (TranscriptOracle.run answer (dependentRandomTable fallback f) history).support) :
    out.2 ≤ Fintype.card J * q := TranscriptOracle.cost_le _ _ _ hout

theorem table_fixed_joint [Fintype J] (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (read : I → A) (history : List (I × A)) :
    TranscriptOracle.run (fun _ i => PMF.pure (read i))
      (dependentRandomTable fallback f) history =
        RTree.run read (dependentRandomTable fallback f) := TranscriptOracle.run_fixed _ _ _

end DependentExecution

/-- The same query is asked twice. -/
def repeatedQuery : RTree Unit Bool (Bool × Bool) 2 :=
  RTree.query () (fun first => RTree.query () (fun second =>
    RTree.pure (q := 0) (PMF.pure (first, second))))

def inconsistentPolicy : TranscriptOracle.AnswerPolicy Unit Bool :=
  fun history _ => PMF.pure history.isEmpty

/-- A literal inconsistent transcript has two distinct answers and exactly two queries. -/
theorem inconsistent_joint :
    TranscriptOracle.run inconsistentPolicy repeatedQuery [] = PMF.pure ((true, false), 2) := by
  simp [repeatedQuery, inconsistentPolicy, TranscriptOracle.run, RTree.query, RTree.pure,
    PMF.pure_map]

theorem repeated_query_every_transcript (answer : TranscriptOracle.AnswerPolicy Unit Bool)
    (history : List (Unit × Bool)) {out : (Bool × Bool) × ℕ}
    (hout : out ∈ (TranscriptOracle.run answer repeatedQuery history).support) : out.2 ≤ 2 :=
  TranscriptOracle.cost_le _ _ _ hout

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

/-- A concrete finite dependent table of the accepted amplified pruning program. -/
def pruningTable {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials entries : ℕ) (T : GuideTree V N) :
    RTree (Finset V) ℝ (Fin entries → V → Option ℝ)
      (entries * (trials * guideOneGlobalBudget Q n)) :=
  (dependentRandomTable (fun _ _ => none)
    (fun _ : Fin entries => guidePruneTrialsTree family n trials T)).cast (by simp)

/-- The constructor is selected before the hidden graph; the cap quantifies over all policies. -/
theorem pruning_public_contract {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials entries : ℕ) (T : GuideTree V N) :
    ∃ P : RTree (Finset V) ℝ (Fin entries → V → Option ℝ)
        (entries * (trials * guideOneGlobalBudget Q n)),
      P = pruningTable family n trials entries T ∧
      (∀ answer history (out : (Fin entries → V → Option ℝ) × ℕ),
        out ∈ (TranscriptOracle.run answer P history).support →
          out.2 ≤ entries * (trials * guideOneGlobalBudget Q n)) ∧
      (∀ read history, TranscriptOracle.run (fun _ i => PMF.pure (read i)) P history =
        RTree.run read P) := by
  refine ⟨pruningTable family n trials entries T, rfl, ?_, ?_⟩
  · intro answer history out hout
    exact TranscriptOracle.cost_le _ _ _ hout
  · exact TranscriptOracle.run_fixed _

theorem pruning_table_run {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials entries : ℕ) (T : GuideTree V N)
    (read : Finset V → ℝ) :
    RTree.run read (pruningTable family n trials entries T) =
      RTree.run read (dependentRandomTableAux (fun _ _ => none)
        (fun _ : Fin entries => guidePruneTrialsTree family n trials T) Finset.univ.toList) := by
  simp only [pruningTable, dependentRandomTable, RTree.run_cast]

/-- This is the exact marginal for every nonnegative potential of the executed entry. -/
theorem pruning_entry_expect {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials entries : ℕ) (T : GuideTree V N)
    (read : Finset V → ℝ) (j : Fin entries) (potential : (V → Option ℝ) → ℝ≥0∞) :
    expect ((pruningTable family n trials entries T).eval read)
      (fun table => potential (table j)) =
        expect ((guidePruneTrialsTree family n trials T).eval read) potential := by
  rw [pruningTable, RTree.eval_cast]
  exact dependentRandomTable_expect_entry _ _ _ _ _

theorem pruning_truncate_expect {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials entries : ℕ) (T : GuideTree V N)
    (cap : ℕ) (read : Finset V → ℝ) (potential : (Fin entries → V → Option ℝ) → ℝ≥0∞) :
    expect (((pruningTable family n trials entries T).truncate cap).eval read)
      (fun out => out.elim 0 potential) ≤
        expect ((pruningTable family n trials entries T).eval read) potential :=
  truncate_expect_zero_le _ _ _ _

theorem pruning_table_above {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (trials entries : ℕ) {output : Fin entries → V → Option ℝ}
    (hout : output ∈ ((pruningTable family n trials entries T).eval G.cut).support)
    (j : Fin entries) (t : V) (value : ℝ) (hvalue : output j t = some value) :
    stValue G t T.source ≤ value := by
  rw [pruningTable, RTree.eval_cast] at hout
  have hj := dependentRandomTable_entry_support (fun _ _ => none)
    (fun _ : Fin entries => guidePruneTrialsTree family n trials T) G.cut hout j
  exact guidePruneTrialsTree_above family G hG T hvn hQ trials hj t value hvalue

/-- All original graph, source-branch, target, and two-crossing probability premises remain. -/
theorem pruning_table_failure {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (trials entries : ℕ)
    (keep delete : frontierProxies T.tree T.centroid) (hne : keep ≠ delete)
    (hs : T.sourceNode ∉ frontierBranch T.tree T.centroid delete)
    (t : N) (ht : t ∈ T.real) (htkeep : t ∈ frontierBranch T.tree T.centroid keep)
    (S : Finset V) (hS : IsSTMinCut G (T.label t) T.source S)
    (A : Finset N) (hA : ∀ v ∈ T.real, v ∈ A ↔ T.label v ∈ S)
    (hcross : (T.tree.crossSet A).card ≤ 2)
    (e : N) (he : e ∈ T.tree.crossSet A)
    (heB : e ∈ frontierBranch T.tree T.centroid delete ∨
      T.tree.parent e ∈ frontierBranch T.tree T.centroid delete) :
    mass ((pruningTable family n trials entries T).eval G.cut)
      (fun output => ¬∀ j, output j (T.label t) = some (stValue G (T.label t) T.source)) ≤
        (entries : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ trials := by
  rw [pruningTable, RTree.eval_cast]
  have h := dependentRandomTable_failure_le (fun _ _ => none)
    (fun _ : Fin entries => guidePruneTrialsTree family n trials T) G.cut
    (fun _ output => output (T.label t) = some (stValue G (T.label t) T.source))
    (fun _ => ENNReal.ofReal (3 / 4 : ℝ) ^ trials)
    (fun _ => guidePruneTrialsTree_failure_le family G hG T hvn hQ trials keep delete hne hs
      t ht htkeep S hS A hA hcross e he heB)
  simpa using h

/-- One additional actual query is chosen adaptively from the executed table. -/
def pruningTableWithQuery {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials entries : ℕ) (T : GuideTree V N)
    (select : (Fin entries → V → Option ℝ) → Finset V) :
    RTree (Finset V) ℝ ((Fin entries → V → Option ℝ) × ℝ)
      (entries * (trials * guideOneGlobalBudget Q n) + 1) :=
  (pruningTable family n trials entries T).bind (fun table =>
    RTree.query (select table) (fun answer => RTree.pure (q := 0) (PMF.pure (table, answer))))

theorem pruning_query_joint {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials entries : ℕ) (T : GuideTree V N)
    (select : (Fin entries → V → Option ℝ) → Finset V) (read : Finset V → ℝ) :
    RTree.run read (pruningTableWithQuery family n trials entries T select) =
      (RTree.run read (pruningTable family n trials entries T)).map
        (fun p => ((p.1, read (select p.1)), p.2 + 1)) := by
  simp only [pruningTableWithQuery, RTree.run_bind, RTree.run_query, RTree.run_pure,
    PMF.pure_map]
  rfl

theorem pruning_query_cost {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n trials entries : ℕ) (T : GuideTree V N)
    (select : (Fin entries → V → Option ℝ) → Finset V) (read : Finset V → ℝ)
    {out : ((Fin entries → V → Option ℝ) × ℝ) × ℕ}
    (hout : out ∈ (RTree.run read (pruningTableWithQuery family n trials entries T select)).support) :
    out.2 ≤ entries * (trials * guideOneGlobalBudget Q n) + 1 := by
  simpa only [Nat.one_mul] using random_bind_cost (pruningTable family n trials entries T)
    (fun table => RTree.query (select table)
      (fun answer => RTree.pure (q := 0) (PMF.pure (table, answer)))) read
    1 (entries * (trials * guideOneGlobalBudget Q n)) 1
    (fun p hp => by simpa only [Nat.one_mul] using RTree.cost_le _ _ hp)
    (fun _ _ p hp => by simpa only [Nat.one_mul] using RTree.cost_le _ _ hp) hout

variable {W : Type} [Fintype W] [DecidableEq W]

theorem pruning_contraction_joint {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials entries : ℕ) (T : GuideTree V N)
    (π : W → V) (read : Finset W → ℝ) :
    RTree.run read (contractProgram π (pruningTable family n trials entries T)) =
      RTree.run (read ∘ WeightedGraph.pull π) (pruningTable family n trials entries T) :=
  contractProgram_run _ _ _

theorem pruning_contraction_graph_joint {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (n trials entries : ℕ) (T : GuideTree V N)
    (π : W → V) (G : WeightedGraph W) :
    RTree.run G.cut (contractProgram π (pruningTable family n trials entries T)) =
      RTree.run (G.contract π).cut (pruningTable family n trials entries T) :=
  contractProgram_graph_run _ _ _

end
end CutQueryComplexity.GHDependentContracts

end RandomizedContracts3

#audit_cut_decl GH209Contract.continuationLaw
#audit_cut_decl GH209Contract.publicGuideSwitch
#audit_cut_decl APMCCubeRootContracts.cube_root_schedule
#audit_cut_decl APMCCubeRootContracts.cube_root_zero
#audit_cut_decl APMCCubeRootContracts.normalization_charge
#audit_cut_decl APMCCubeRootContracts.partClones_card
#audit_cut_decl APMCCubeRootContracts.partClones_even
#audit_cut_decl APMCCubeRootContracts.partClones_pos
#audit_cut_decl APMCCubeRootContracts.literal_player_request_bound
#audit_cut_decl APMCCubeRootContracts.literal_capped_player
#audit_cut_decl APMCCubeRootContracts.literal_player_expands
#audit_cut_decl APMCCubeRootContracts.literal_subtype_query
#audit_cut_decl APMCCubeRootContracts.literal_subtype_program
#audit_cut_decl APMCCubeRootContracts.literal_subtype_sizes
#audit_cut_decl APMCLiteral4.actual_coarse_cost
#audit_cut_decl APMCLiteral4.replay_legality
#audit_cut_decl APMCLiteral4.capped_execution_and_certificate
#audit_cut_decl WitnessContract209.coherent_adapter
#audit_cut_decl WitnessContract209.public_witness
#audit_cut_decl WitnessContract209.empty
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Forest.check_public_low_candidate
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Forest.check_verified_soundness
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Forest.check_actual_threshold_certificate
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Forest.check_physical_minimum
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Forest.check_physical_cost
#audit_cut_decl CutQueryComplexity.GHDependentContracts.table_cons_run
#audit_cut_decl CutQueryComplexity.GHDependentContracts.table_every_transcript
#audit_cut_decl CutQueryComplexity.GHDependentContracts.table_fixed_joint
#audit_cut_decl CutQueryComplexity.GHDependentContracts.inconsistent_joint
#audit_cut_decl CutQueryComplexity.GHDependentContracts.repeated_query_every_transcript
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_public_contract
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_table_run
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_entry_expect
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_truncate_expect
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_table_above
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_table_failure
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_query_joint
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_query_cost
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_contraction_joint
#audit_cut_decl CutQueryComplexity.GHDependentContracts.pruning_contraction_graph_joint


/- Actual execution contract: quantum-forest. -/
section QuantumForestContracts4

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds
noncomputable section
open ProductPrograms
open scoped Classical
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

-- The literal numerical expression retains every verification and physical conversion.
theorem check_concrete_sum {n t : ℕ} (hn : 2 ≤ n) (ht : 1 ≤ t) (K : ℕ)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ((minimumDegreeWitnessQueries n t +
      12 * productBits n 1 *
        (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) +
      K * (12 * productBits n 1 * UniformStars.QH n) : ℕ) : ℝ) ≤
      (819205 * (t : ℝ) + 70860 * (1 + Real.log (1 / eta)) ^ 2 + 600000000000 * (K : ℝ)) *
        Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 :=
  concreteSum_le hn ht K heta heta1

-- The constant is chosen before the size; no rank, ceiling or cost envelope is assumed.
theorem check_constant_before_size (t K : ℕ) (ht : 1 ≤ t) (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ((minimumDegreeWitnessQueries n t +
        12 * productBits n 1 *
          (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) +
        K * (12 * productBits n 1 * UniformStars.QH n) : ℕ) : ℝ) ≤
        C * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 :=
  exists_combined_constant t K ht eta heta heta1

-- Exact correspondence with accepted physical routines; no unaccepted global run is imported.
theorem check_accepted_routine_lengths (n t K : ℕ) (eta : ℝ) (ht : 0 < t) :
    minimumDegreeWitnessQueries n t +
      12 * productBits n 1 *
        (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) +
      K * (12 * productBits n 1 * UniformStars.QH n) =
      (minimumDegreeWitnessRoutine n t ht).len +
      (productTreeRoutine (Forest.lowCandidate n (rootThreshold n) eta)).len +
      K * (productTreeRoutine (UniformStars.highCandidate n)).len :=
  combinedQueries_eq_routine_lengths n t K eta ht

theorem check_accepted_routine_cost {n t : ℕ} (hn : 2 ≤ n) (ht : 0 < t) (K : ℕ)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (((minimumDegreeWitnessRoutine n t ht).len +
      (productTreeRoutine (Forest.lowCandidate n (rootThreshold n) eta)).len +
      K * (productTreeRoutine (UniformStars.highCandidate n)).len : ℕ) : ℝ) ≤
      (819205 * (t : ℝ) + 70860 * (1 + Real.log (1 / eta)) ^ 2 + 600000000000 * (K : ℝ)) *
        Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 :=
  routine_lengths_le hn ht K heta heta1

end
end CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds



end QuantumForestContracts4


/- Actual execution contract: randomized. -/
section RandomizedContracts4

/-! Evidence-only geometry and literal public component-program contracts.
The simultaneous approximation event remains a supplied semantic premise. -/

set_option autoImplicit false

namespace CutQueryComplexity.GHGeometryContracts
noncomputable section
open scoped Classical
open GHReduction WeightedGraph Certificate

variable {V : Type} [Fintype V] [DecidableEq V]

theorem explicit_component_eq (F K : WeightedGraph V) {eps : ℝ} (heps : eps < 1)
    (happrox : ∀ S, (1 - eps) * F.cut S ≤ K.cut S ∧ K.cut S ≤ (1 + eps) * F.cut S)
    (c : V) : forestBlock F.support c = forestBlock K.support c := by
  ext v
  simp only [mem_forestBlock]
  exact reachable_iff_of_approximation F K heps happrox c v

theorem explicit_component_zero (F K : WeightedGraph V) {eps : ℝ} (heps : eps < 1)
    (happrox : ∀ S, (1 - eps) * F.cut S ≤ K.cut S ∧ K.cut S ≤ (1 + eps) * F.cut S)
    (c : V) : F.cut (forestBlock K.support c) = 0 :=
  (cut_zero_iff_of_approximation F K heps happrox _).mpr (cut_component_zero K c)

/-- Positivity is used for at least two terminals inside one actual component. -/
theorem terminal_positive_inside_component (F K : WeightedGraph V) {eps : ℝ}
    (heps : eps < 1)
    (happrox : ∀ S, (1 - eps) * F.cut S ≤ K.cut S ∧ K.cut S ≤ (1 + eps) * F.cut S)
    (c : V) (U : Finset V) (hU : 2 ≤ U.card) (hsub : U ⊆ forestBlock K.support c) :
    0 < terminalMin F U := by
  apply terminalMin_pos_of_connected F U hU
  intro a ha b hb
  have hca := (mem_forestBlock K.support c a).mp (hsub ha)
  have hcb := (mem_forestBlock K.support c b).mp (hsub hb)
  exact (reachable_iff_of_approximation F K heps happrox a b).mpr (hca.symm.trans hcb)

/-- The actual finite bucket data are selected from K, U, s and M before hidden F. -/
theorem public_buckets {M : ℕ} (K : WeightedGraph V) (U : Finset V) (s : V) :
    ∃ buckets : Fin (bucketCount M) → Finset V,
      buckets = (fun j => sourceBucket K U s j.val) ∧
      (∀ j, s ∉ buckets j) ∧
      (∀ (F : WeightedGraph V), InputPromise M F →
        (∀ S, (99 / 100 : ℝ) * F.cut S ≤ K.cut S ∧ K.cut S ≤ (101 / 100 : ℝ) * F.cut S) →
        ∀ t ∈ U, t ≠ s → 0 < stValue F t s → ∃ j, t ∈ buckets j) := by
  refine ⟨(fun j => sourceBucket K U s j.val), rfl, ?_, ?_⟩
  · intro j
    exact sourceBucket_excludes K U s j.val
  · intro F hF happrox t ht hts hpos
    exact sourceBucket_coverage F K hF happrox U s ht hts hpos

theorem bucket_local_geometry (F K : WeightedGraph V)
    (happrox : ∀ S, (99 / 100 : ℝ) * F.cut S ≤ K.cut S ∧ K.cut S ≤ (101 / 100 : ℝ) * F.cut S)
    (U : Finset V) (s : V) (j : ℕ) {t : V} (ht : t ∈ sourceBucket K U s j)
    {S : Finset V} (hS : IsSTMinCut F t s S) :
    2 ≤ (bucketTerminals K U s j).card ∧
      0 < terminalMin K (bucketTerminals K U s j) ∧
      F.cut S ≤ (11 / 10 : ℝ) * terminalMin F (bucketTerminals K U s j) :=
  ⟨bucketTerminals_two_le K U s j ⟨t, ht⟩,
    bucketTerminals_pos K U s j ⟨t, ht⟩,
    sourceBucket_small_minCut F K happrox U s j ht hS⟩

section CompactComponent
variable {U : Finset V}

theorem compact_shore_data (S : Finset U) (A : Finset V) :
    Fintype.card U = U.card ∧ (componentLift S).card = S.card ∧
      componentLift S ⊆ U ∧ componentProject U (componentLift S) = S ∧
      componentLift (componentProject U A) = A ∩ U := by
  refine ⟨componentVertex_card U, ?_, componentLift_subset S,
    componentProject_lift S, componentLift_project A⟩
  exact Finset.card_image_of_injective S Subtype.val_injective

theorem component_query_one (G : WeightedGraph V) (r : U) (hU : G.cut U = 0)
    (S : Finset U) :
    DTree.run G.cut (contractQuery (componentMap r) S) = (G.cut (componentLift S), 1) := by
  apply Prod.ext
  · change (contractQuery (componentMap r) S).eval G.cut = G.cut (componentLift S)
    rw [contractQuery_eval, component_contract_cut G r hU]
  · exact contractQuery_cost _ _ _

/-- The component's actual output map preserves its realized query count. -/
theorem component_run_map {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (r s t : U) (read : Finset V → ℝ) :
    DTree.run read (componentSTProgram family r s t) =
      (componentLift (DTree.run read
        (contractDetProgram (componentMap r) (canonicalSTProgram family s t))).1,
       (DTree.run read (contractDetProgram (componentMap r) (canonicalSTProgram family s t))).2) :=
  DTree.run_map _ _ _

theorem component_output_subset {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (r s t : U) (read : Finset V → ℝ) :
    (componentSTProgram family r s t).eval read ⊆ U := by
  rw [componentSTProgram, DTree.eval_map]
  exact componentLift_subset _

/-- The public constructor needs neither hidden G nor its zero-boundary proof. -/
theorem component_public_contract {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (r s t : U) :
    ∃ P : DTree (Finset V) ℝ (Finset V) (Q (Fintype.card U)),
      P = componentSTProgram family r s t ∧
      (∀ read, P.cost read ≤ Q U.card ∧ P.eval read ⊆ U) ∧
      (∀ (G : WeightedGraph V), InputPromise M G → G.cut U = 0 → s ≠ t →
        IsCanonicalSTCut G s.val t.val (P.eval G.cut)) ∧
      (∀ answer history (out : Finset V × ℕ),
        out ∈ (TranscriptOracle.run answer (RTree.ofDeterministic P) history).support →
          out.2 ≤ Q U.card) := by
  refine ⟨componentSTProgram family r s t, rfl, ?_, ?_, ?_⟩
  · intro read
    exact ⟨componentSTProgram_cost family r s t read, component_output_subset family r s t read⟩
  · intro G hG hU hst
    exact componentSTProgram_correct family G hG r s t hU hst
  · intro answer history out hout
    simpa only [componentVertex_card] using TranscriptOracle.cost_le _ _ _ hout

theorem component_fixed_joint {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (r s t : U) (read : Finset V → ℝ) (history : List (Finset V × ℝ)) :
    TranscriptOracle.run (fun _ S => PMF.pure (read S))
      (RTree.ofDeterministic (componentSTProgram family r s t)) history =
        PMF.pure (DTree.run read (componentSTProgram family r s t)) := by
  rw [TranscriptOracle.run_fixed, RTree.run_ofDeterministic]

end CompactComponent

/-- A single supplied approximation event provides the correctness premise for
the actual component call, even when the public component was selected from K. -/
theorem approximator_component_public_contract {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (K : WeightedGraph V) (c : V)
    (r s t : forestBlock K.support c) :
    ∃ P : DTree (Finset V) ℝ (Finset V) (Q (Fintype.card (forestBlock K.support c))),
      P = componentSTProgram family r s t ∧
      (∀ read, P.cost read ≤ Q (forestBlock K.support c).card) ∧
      (∀ (F : WeightedGraph V), InputPromise M F → ∀ eps : ℝ, eps < 1 →
        (∀ S, (1 - eps) * F.cut S ≤ K.cut S ∧ K.cut S ≤ (1 + eps) * F.cut S) →
        s ≠ t → IsCanonicalSTCut F s.val t.val (P.eval F.cut)) := by
  refine ⟨componentSTProgram family r s t, rfl, componentSTProgram_cost family r s t, ?_⟩
  intro F hF eps heps happrox hst
  exact componentSTProgram_correct family F hF r s t
    (explicit_component_zero F K heps happrox c) hst

end
end CutQueryComplexity.GHGeometryContracts

end RandomizedContracts4


/- Actual execution contract: apmc. -/
section APMCContracts4

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.DeterministicAPMCExpansion
open Flow CutMatching AllPairsAudit Finset WeightedGraph
open CutQueryComplexity.DeterministicAPMCExpansion.Pruning
open CutQueryComplexity.DeterministicAPMCExpansion.Decomposition
open scoped Classical
noncomputable section

namespace APMCLiteral5

-- The public cap is chosen before the unit graph. Honest nontruncation
-- follows from the actual matching game plus its derived pruning source mass.
theorem actual_capped_node {V : Type} [Fintype V] [DecidableEq V]
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hV : 0 < Fintype.card V)
    (hq : Fintype.card V ≤ t ^ 3)
    (hrounds : normalizedRounds (Fintype.card (Clone V (2 * t))) ≤ R) :
    ∃ tree : DTree (Finset V) ℝ (NodeResult V) (nodeBudget V R t),
      tree = cappedNode R t ∧
      (∀ read, tree.cost read ≤ nodeBudget V R t) ∧
      ∀ G : WeightedGraph V, Unweighted G →
        tree.eval G.cut = (nodeProg R t).eval G.cut ∧
        tree.cost G.cut = (nodeProg R t).cost G.cut ∧
        match tree.eval G.cut with
        | .split P =>
            (localTolerance (Fintype.card V) R : ℝ) < P.card ∧
            (localTolerance (Fintype.card V) R : ℝ) < Pᶜ.card ∧
            G.cut P < (2 * t : ℕ) * min (P.card : ℝ) (Pᶜ.card : ℝ)
        | .pruned P =>
            8 * P.card ≤ Fintype.card V ∧
            G.cut P ≤ (2 * (t : ℝ)) * P.card ∧
            ∀ T : Finset V, T ⊆ Pᶜ →
              (2 * (t : ℝ)) * min (T.card : ℝ) ((Pᶜ \ T).card : ℝ) ≤
                4 * (R : ℝ) * G.localCut Pᶜ T
        | .invalid => False := by
  refine ⟨cappedNode R t, rfl, fun read => DTree.cost_le _ read, ?_⟩
  intro G hG
  have he := cappedNode_eval G hG R t hR ht hV hq hrounds
  refine ⟨he, ?_, ?_⟩
  · simpa only [cappedNode, DTree.cost, DTree.run_map] using
      Prog.toDTree_cost G.cut _ _ (nodeProg_cost G hG R t hR ht hV hq hrounds)
  · rw [he]
    have hc := nodeProg_correct G hG R t hR ht hV hrounds
    cases hx : (nodeProg (V := V) R t).eval G.cut with
    | split P => simpa only [hx, NodeCorrect, SplitCorrect] using hc
    | pruned P => simpa only [hx, NodeCorrect] using hc
    | invalid => simp only [hx, NodeCorrect] at hc

-- Exactly one ambient adapter is used, on q actual vertices and q+2 flow
-- vertices. Every virtual query, including on inconsistent replies, costs 3.
theorem actual_part_adapter {V : Type} [Fintype V] [DecidableEq V]
    (R t : ℕ) (W : Finset V) (read : Finset V → ℝ) :
    Fintype.card (PartVertex W) = W.card ∧
    Fintype.card (PartVertex W ⊕ Fin 2) = W.card + 2 ∧
    (∀ S : Finset (PartVertex W),
      DTree.run read (subtypeQuery W S) = (subtypeOracle W read S, 3)) ∧
    (partNode R t W).eval read =
      (cappedNode R t).eval (subtypeOracle W read) ∧
    (partNode R t W).cost read =
      (cappedNode R t).cost (subtypeOracle W read) * 3 ∧
    (partNode R t W).cost read ≤ nodeBudget (PartVertex W) R t * 3 := by
  refine ⟨partVertex_card W, partNetwork_card W, fun S => subtypeQuery_run W S read,
    ?_, ?_, partNode_cost R t W read⟩
  · rw [partNode, treeProg_eval, subtypeProgram_eval_public]
  · rw [partNode, treeProg_cost, subtypeProgram_cost]

-- This ledger refers to the work tree returned by the actual recursive
-- execution, even on invalid replies. The outer cap never truncates that run.
theorem actual_recursive_ledger {V : Type} [Fintype V] [DecidableEq V]
    (R t : ℕ) (hR : 1 ≤ R) (fuel : ℕ) (W : Finset V) (read : Finset V → ℝ) :
    ∃ actual : State R W,
      (program R t hR fuel W).eval read = actual ∧
      actual = (run R t hR fuel W).eval read ∧
      (program R t hR fuel W).cost read = (run R t hR fuel W).cost read ∧
      (run R t hR fuel W).cost read ≤
        nodeUnitBudget (Fintype.card V) R t * actual.work.mass ∧
      actual.tree.vertices = W ∧ actual.tree.DisjointSplits ∧
      actual.work.vertices ⊆ W ∧ actual.work.Covered ∧
      actual.work.Shrinks (64 * R) ∧ actual.work.Positive ∧
      actual.work.depth ≤ (64 * R) * Nat.clog 2 (Fintype.card V + 1) ∧
      actual.work.mass ≤ (64 * R) * Nat.clog 2 (Fintype.card V + 1) * Fintype.card V ∧
      (program R t hR fuel W).cost read ≤ queryBudget (Fintype.card V) R t := by
  let actual := (run R t hR fuel W).eval read
  have hcost := run_cost (Fintype.card V) R t hR fuel W (card_le_univ W) read
  refine ⟨actual, program_eval R t hR fuel W read, rfl, ?_,
    run_cost_work (Fintype.card V) R t hR fuel W (card_le_univ W) read,
    actual.covers, actual.disjoint, actual.work_subset, actual.work_covered,
    actual.work_shrinks, actual.work_positive, ?_,
    actual.mass_le R (Fintype.card V) hR (card_le_univ W), DTree.cost_le _ _⟩
  · simpa only [CutQueryComplexity.DeterministicAPMCExpansion.Decomposition.program, DTree.cost, DTree.run_map] using
      Prog.toDTree_cost read _ _ hcost
  · exact actual.work.depth_le_clog (64 * R) (Fintype.card V) (by omega)
      actual.work_shrinks actual.work_positive
      ((card_le_card actual.work_subset).trans (card_le_univ W))

-- The entire partition program is fixed before G. No partition, expanding
-- leaf, fake certificate, or success/query bound is supplied by the caller.
theorem public_partition {V : Type} [Fintype V] [DecidableEq V]
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hN : Fintype.card V ≤ t ^ 3)
    (hrounds : ∀ q ≤ Fintype.card V, normalizedRounds (q * (2 * t)) ≤ R) :
    ∃ tree : DTree (Finset V) ℝ (V → V) (queryBudget (Fintype.card V) R t),
      tree = (decomposition (V := V) R t hR).map State.representativeMap ∧
      (∀ read, tree.cost read ≤ queryBudget (Fintype.card V) R t) ∧
      (∀ read, tree.eval read =
        ((run R t hR (Fintype.card V) univ).eval read).representativeMap) ∧
      ∀ G : WeightedGraph V, Unweighted G →
        ∃ result : State R (univ : Finset V),
          result = (decomposition R t hR).eval G.cut ∧
          tree.eval G.cut = result.representativeMap ∧
          result.complete = true ∧ result.tree.vertices = univ ∧
          result.tree.DisjointSplits ∧ result.tree.SparseSplits G (2 * t) ∧
          result.tree.ExpandingLeaves G R t ∧
          (∀ v, tree.eval G.cut (tree.eval G.cut v) = tree.eval G.cut v) ∧
          (∀ v, ∀ T : Finset V, T ⊆ fiber (tree.eval G.cut) v →
            ((2 * t : ℕ) : ℝ) *
              min (T.card : ℝ) ((fiber (tree.eval G.cut) v \ T).card : ℝ) ≤
                ((8 * R : ℕ) : ℝ) * G.localCut (fiber (tree.eval G.cut) v) T +
                  2 * ((8 * R : ℕ) : ℝ) * (t ^ 2 : ℕ) * (2 * t : ℕ)) ∧
          (∑ v, G.cut (fiber (tree.eval G.cut) v)) ≤
            2 * ((2 * t : ℕ) : ℝ) * Fintype.card V * Nat.clog 2 (Fintype.card V) := by
  let tree := (decomposition (V := V) R t hR).map State.representativeMap
  refine ⟨tree, rfl, fun read => DTree.cost_le _ read, ?_, ?_⟩
  · intro read
    simp only [tree, DTree.eval_map, decomposition, program_eval]
  · intro G hG
    let result := (decomposition (V := V) R t hR).eval G.cut
    have hc : result.Correct G t := decomposition_correct G hG R t hR ht hN hrounds
    have he : tree.eval G.cut = result.representativeMap := DTree.eval_map _ _ _
    refine ⟨result, rfl, he, hc.1, result.covers, result.disjoint, hc.2.1, hc.2.2,
      ?_, ?_, ?_⟩
    · rw [he]
      exact result.representativeMap_idempotent
    · rw [he]
      exact result.representativeMap_additive G t hc
    · rw [he]
      exact result.representativeMap_boundary G t hc

theorem exact_budget (N R t : ℕ) :
    queryBudget N R t = 73728 * N * (R + 1) * R ^ 2 * t ^ 2 *
      (Nat.clog 2 (N + 2) + 1) * Nat.clog 2 (N + 1) := by
  unfold queryBudget nodeUnitBudget
  ring

end APMCLiteral5




end

end APMCContracts4


/- Actual execution contract: quantum-neighbors. -/
section QuantumNeighborsContracts3

/-! Evidence only: the literal public frontier program, exact contraction
execution, witnessed protection, and actual refinement/Steiner geometry. -/

set_option autoImplicit false

namespace GHFrontierContracts

open CutQueryComplexity CutQueryComplexity.GHReduction CutQueryComplexity.WeightedGraph
open scoped Classical BigOperators
noncomputable section

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

omit [DecidableEq V] [Fintype B] in
theorem literal_contract_query (π : V → B) (S : Finset B) (read : Finset V → ℝ) :
    DTree.run read (contractQuery π S) = (read (pull π S), 1) := rfl

/-- The actual one-query adapter preserves the entire output/cost pair on
every oracle. This is a theorem of substitution, not an assumed cost ledger. -/
theorem substitute_contract_run {O : Type} {q : ℕ} (π : V → B)
    (T : DTree (Finset B) ℝ O q) (read : Finset V → ℝ) :
    DTree.run read (T.substitute (contractQuery π)) =
      DTree.run (fun S => read (pull π S)) T := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rcases T with out | ⟨S, next⟩
      · simp [DTree.substitute, DTree.run]
      · rw [DTree.substitute, DTree.run_cast, DTree.run_bind]
        change
          ((DTree.run read ((next (read (pull π S))).substitute (contractQuery π))).1,
            1 + (DTree.run read ((next (read (pull π S))).substitute (contractQuery π))).2) =
          ((DTree.run (fun U => read (pull π U)) (next (read (pull π S)))).1,
            (DTree.run (fun U => read (pull π U)) (next (read (pull π S)))).2 + 1)
        rw [ih]
        simp only [Nat.add_comm]

theorem contractDetProgram_run_public {O : Type} {q : ℕ} (π : V → B)
    (T : DTree (Finset B) ℝ O q) (read : Finset V → ℝ) :
    DTree.run read (contractDetProgram π T) =
      DTree.run (fun S => read (pull π S)) T := by
  rw [contractDetProgram, DTree.run_cast]
  exact substitute_contract_run π T read

/-- Exact execution of the implemented frontier program, including its realized
query count. No input promise or protected-shore witness is needed here. -/
theorem literal_frontier_run {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (p : V → B) (T : RootedTree B) (b : B) (s t : fiber p b) (read : Finset V → ℝ) :
    DTree.run read (frontierSTProgram A p T b s t) =
      (pull (frontierMap p T b)
        ((canonicalSTProgram A (Sum.inl s : FrontierVertex p T b) (Sum.inl t)).eval
          (fun S => read (pull (frontierMap p T b) S))),
       (canonicalSTProgram A (Sum.inl s : FrontierVertex p T b) (Sum.inl t)).cost
          (fun S => read (pull (frontierMap p T b) S))) := by
  rw [frontierSTProgram, DTree.run_map, contractDetProgram_run_public]
  rfl

/-- One literal public program serves all hidden graphs satisfying the original
input promise and the original per-proxy minimum-shore witnesses. -/
theorem literal_frontier_contract {M : ℕ} {Q : ℕ → ℕ} (A : CanonicalSTFamily M Q)
    (p : V → B) (T : RootedTree B) (b : B) (s t : fiber p b) :
    ∃ P : DTree (Finset V) ℝ (Finset V) (Q (Fintype.card (FrontierVertex p T b))),
      P = frontierSTProgram A p T b s t ∧
      (∀ read, P.cost read ≤ Q ((fiber p b).card + (frontierProxies T b).card)) ∧
      (∀ G : WeightedGraph V, InputPromise M G →
        ∀ r c : frontierProxies T b → V,
          (∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e))) →
          s ≠ t → IsSTMinCut G s.val t.val (P.eval G.cut)) := by
  refine ⟨frontierSTProgram A p T b s t, rfl, ?_, ?_⟩
  · intro read
    simpa only [frontierVertex_card] using frontierSTProgram_cost A p T b s t read
  · intro G hG r c hcut hst
    exact frontierSTProgram_correct A G hG p T b r c hcut s t hst

/-- Protection and a section of the actual quotient map are derived from the
original witnesses. There is no arbitrary-contraction preservation assumption. -/
theorem actual_frontier_protection (G : WeightedGraph V)
    (p : V → B) (T : RootedTree B) (b : B) (r c : frontierProxies T b → V)
    (hcut : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e))) :
    (∀ z, frontierMap p T b (frontierRepresentative p T b r z) = z) ∧
      (∀ z, Certificate.GomoryHu.RootProtected G (fiber (frontierMap p T b) z)
        (frontierRepresentative p T b r z)) ∧
      Function.Surjective (frontierMap p T b) := by
  have hs := frontierRepresentative_section p T b r
    (fun e => (mem_pull _ _ _).mp (hcut e).1)
  exact ⟨hs, frontierRepresentative_protected G p T b r c hcut,
    fun z => ⟨frontierRepresentative p T b r z, hs z⟩⟩

theorem actual_frontier_counts (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) :
    (∀ b, Function.Surjective (frontierMap p T b)) ∧
      (∑ b, Fintype.card (FrontierVertex p T b)) =
        Fintype.card V + 2 * (Fintype.card B - 1) ∧
      (∑ b, Fintype.card (FrontierVertex p T b)) ≤ 3 * Fintype.card V ∧
      (∀ b, Fintype.card (FrontierVertex p T b) ≤ Fintype.card V) := by
  have h := actual_frontier_vertex_sum p hp T
  exact ⟨h.1, h.2.1, h.2.2, frontierVertex_card_le p hp T⟩

variable {ι : Type} [DecidableEq ι]

/-- Surjectivity is derived from real residual pivots and child vertices;
the bounds apply to this very refined map and its public BFS topology. -/
theorem literal_round_refinement (p : V → B) (I : B → Finset ι)
    (S : B → ι → Finset V) (T : RootedTree B) (a : (b : B) → B → Option (I b))
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (r : B → V) (hr : ∀ b, p (r b) = b) (hrS : ∀ b, ∀ i ∈ I b, r b ∉ S b i)
    (hchild : ∀ b, ∀ i : I b, ∃ v : V, p v = b ∧ v ∈ S b i.val) :
    Function.Surjective (roundBlockMap p I S) ∧
      (∑ c, Fintype.card (FrontierVertex (roundBlockMap p I S) (roundBlockTree T I a) c)) =
        Fintype.card V + 2 * (Fintype.card B + (∑ b, (I b).card) - 1) ∧
      (∑ c, Fintype.card (FrontierVertex (roundBlockMap p I S) (roundBlockTree T I a) c)) ≤
        3 * Fintype.card V ∧
      (∀ c, Fintype.card (FrontierVertex (roundBlockMap p I S) (roundBlockTree T I a) c) ≤
        Fintype.card V) := by
  have hs := roundBlockMap_surjective p I S hdisj r hr hrS hchild
  exact ⟨hs, roundBlock_frontier_sizes p I S T a hs⟩

theorem literal_round_edges (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) :
    (roundEdges T I a).card = Fintype.card B - 1 + ∑ b, (I b).card ∧
      SpanTree.Spans (roundEdges T I a) :=
  ⟨roundEdges_card T I a, roundEdges_spans T I a⟩

variable {U : Type} [Fintype U] [DecidableEq U]

/-- Steiner geometry keeps the full fundamental-shore correctness hypothesis. -/
theorem actual_steiner_minima (G : WeightedGraph V) (T : SteinerCutTree V U)
    (hT : IsSteinerCutTree G T) {s t : U} (hst : s ≠ t) :
    ∃ e ∈ pathEdges T.tree.topology s t,
      (∀ d ∈ pathEdges T.tree.topology s t, T.tree.weight e ≤ T.tree.weight d) ∧
      IsSTMinCut G (T.terminal s) (T.terminal t) (steinerPathShore T s e) ∧
      G.cut (steinerPathShore T s e) = T.tree.weight e :=
  steinerTree_allPairs G T hT hst

/-- Only the supplied completed tree is decoded. This does not construct a GH
tree from independently witnessed shores. No hidden graph chooses the program. -/
theorem literal_completed_tree_decoder (T : CutTree V) (s t : V) :
    ∃ P : DTree (Finset V) ℝ (Finset V × ℝ) 0,
      P = cutTreeAnswerProgram T s t ∧
      (∀ read, DTree.run read P = (cutTreeAnswer T s t, 0)) ∧
      (∀ G : WeightedGraph V, IsSteinerCutTree G T.asSteiner → s ≠ t →
        IsSTMinCut G s t (P.eval G.cut).1 ∧ G.cut (P.eval G.cut).1 = (P.eval G.cut).2) := by
  refine ⟨cutTreeAnswerProgram T s t, rfl, cutTreeAnswerProgram_run T s t, ?_⟩
  intro G hT hst
  exact cutTreeAnswerProgram_correct T hst G ((cutTree_asSteiner_correct G T).mp hT)

end
end GHFrontierContracts


end QuantumNeighborsContracts3


/- Actual execution contract: gh. -/
section GHContracts4

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction
open CutQueryComplexity.Probability
open scoped Classical ENNReal

namespace GH210Contract
noncomputable section

variable {V N : Type} [Fintype V] [DecidableEq V]
  [Fintype N] [DecidableEq N] {M n : ℕ} {Q : ℕ → ℕ}

-- A false public child guard really returns the all-none output.
theorem invalidChildGuard (family : CanonicalSTFamily M Q)
    (trials levels scale exponent fuel : ℕ) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (shores : T.parts → Finset V) (P : T.parts)
    (hguard : shores P ∩ T.realVertices ≠ T.graphGroup P.val) (read : Finset V → ℝ) :
    (guideTwoChildTree family n trials levels scale exponent fuel T hvn shores P).eval read =
      PMF.pure (fun _ : V => (none : Option ℝ)) := by
  simp only [guideTwoChildTree, hguard, dite_false, RTree.eval_pure]

-- The base branch executes the actual canonical pair program at every fuel.
theorem smallTreeLaw (family : CanonicalSTFamily M Q)
    (trials levels scale exponent fuel : ℕ) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (hsmall : T.real.card ≤ 10) (read : Finset V → ℝ) :
    (guideTwoTree family n trials levels scale exponent fuel T hvn).eval read =
      PMF.pure (fun t => candidateEstimate (Prog.eval read (guideBaseProgram family T) t)) := by
  cases fuel with
  | zero =>
    simp only [guideTwoTree, guideTwoBudget, hsmall, ite_true]
    exact guideBaseValueTree_eval family T hsmall hvn hQ read
  | succ fuel =>
    rw [guideTwoTree, ite_eq_left hsmall, RTree.eval_weaken]
    exact guideBaseValueTree_eval family T hsmall hvn hQ read

-- Equality of actual output laws: the sharp cap removes no honest run.
theorem honestNoTruncation (family : CanonicalSTFamily M Q)
    (trials levels scale exponent : ℕ) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) :
    (guideTwoCappedTree family n trials levels scale exponent T hvn).eval G.cut =
      ((guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1)) T hvn).eval
        G.cut).map some := by
  rw [guideTwoCappedTree, RTree.eval_truncate, RTree.eval, PMF.map_comp]
  apply PMF.ext
  intro output
  simp only [PMF.map_apply, Function.comp_def]
  apply tsum_congr
  intro p
  by_cases hp : p ∈ (RTree.run G.cut
      (guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1)) T hvn)).support
  · rw [ite_eq_left (guideTwoTree_cost_le_sharp family hQ trials levels scale exponent _
      G hG T hvn hp)]
  · have hz : RTree.run G.cut
        (guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1)) T hvn) p = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hp
    simp only [hz, ite_self]

theorem honestValueLaw (family : CanonicalSTFamily M Q)
    (trials levels scale exponent : ℕ) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) :
    (guideTwoValueTree family n trials levels scale exponent T hvn).eval G.cut =
      (guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1)) T hvn).eval
        G.cut := by
  rw [guideTwoValueTree, RTree.eval_map,
    honestNoTruncation family trials levels scale exponent T hvn hQ G hG, PMF.map_comp]
  exact PMF.map_id _

-- The two concrete public trees are fixed before the hidden graph, promises,
-- and every history-dependent answer policy. Repeated answers may disagree.
theorem publicTwoRespectingTrees (family : CanonicalSTFamily M Q)
    (trials levels scale exponent : ℕ) (T : GuideTree V N) (hvn : Fintype.card V ≤ n) :
    ∃ capped : RTree (Finset V) ℝ (Option (V → Option ℝ))
        (guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))),
    ∃ values : RTree (Finset V) ℝ (V → Option ℝ)
        (guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))),
      capped = guideTwoCappedTree family n trials levels scale exponent T hvn ∧
      values = guideTwoValueTree family n trials levels scale exponent T hvn ∧
      (∀ answer : TranscriptOracle.AnswerPolicy (Finset V) ℝ,
        ∀ history p, p ∈ (TranscriptOracle.run answer capped history).support →
          p.2 ≤ guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) ∧
      (∀ answer : TranscriptOracle.AnswerPolicy (Finset V) ℝ,
        ∀ history p, p ∈ (TranscriptOracle.run answer values history).support →
          p.2 ≤ guideTwoSharpBudget M Q n trials levels scale exponent (Nat.clog 2 (n + 1))) ∧
      (SizeRegular n Q → ∀ G : WeightedGraph V, InputPromise M G →
        capped.eval G.cut =
          ((guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1)) T hvn).eval
            G.cut).map some ∧
        values.eval G.cut =
          (guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1)) T hvn).eval
            G.cut) ∧
      (SizeRegular n Q → n ≤ scale → thresholdLevels n ≤ levels →
        ∀ G : WeightedGraph V, InputPromise M G →
          mass (capped.eval G.cut) (fun output => ¬output.elim False (GuideTwoSuccess G T)) ≤
            (2 * Nat.clog 2 (n + 1) * (T.real.card - 2) : ℕ) *
              (ENNReal.ofReal (3 / 4 : ℝ) ^ trials +
                (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent)) ∧
          mass (values.eval G.cut) (fun output => ¬(
            (∀ t value, output t = some value → stValue G t T.source ≤ value) ∧
            (∀ t ∈ T.realVertices, (∃ S, IsSTMinCut G t T.source S ∧ T.RespectsCut S 2) →
              output t = some (stValue G t T.source)))) ≤
            (2 * Nat.clog 2 (n + 1) * (T.real.card - 2) : ℕ) *
              (ENNReal.ofReal (3 / 4 : ℝ) ^ trials +
                (Nat.clog 2 (M + 1) : ℝ≥0∞) * ((((scale + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ exponent))) := by
  refine ⟨guideTwoCappedTree family n trials levels scale exponent T hvn,
    guideTwoValueTree family n trials levels scale exponent T hvn, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact fun answer history p hp => TranscriptOracle.cost_le _ answer history hp
  · exact fun answer history p hp => TranscriptOracle.cost_le _ answer history hp
  · intro hQ G hG
    exact ⟨honestNoTruncation family trials levels scale exponent T hvn hQ G hG,
      honestValueLaw family trials levels scale exponent T hvn hQ G hG⟩
  · intro hQ hnscale hlevels G hG
    exact ⟨guideTwoCappedTree_failure_le family hQ hnscale trials levels exponent hlevels G hG T hvn,
      guideTwoValueTree_failure_le family hQ hnscale trials levels exponent hlevels G hG T hvn⟩

end
end GH210Contract




end GHContracts4


/- Actual execution contract: quantum-uniform. -/
section QuantumUniformContracts3

set_option autoImplicit false



namespace GlobalContract210
open CutQueryComplexity QuantumQueryComplexity
open CutQueryComplexity.StarContraction2022.Quantum
open CutQueryComplexity.StarContraction2022.Quantum.Global
open CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms
open scoped Classical Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

/-- The actual product-run compilation realizes this law for every native table. -/
theorem native_joint (n t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (T : CutQAlg n 1 (Batch n K) W),
      ∀ (read : AnswerTable n) (y : Batch n K),
        T.prob read (minimumDegreeWitnessQueries n t + lowQueries n eta + K * highQueries n) y =
          ∏ i, componentLaw n t K ht eta i read (y i) := by
  obtain ⟨W, hF, hD, T, hT⟩ := joint_realizes n t K ht eta
  exact ⟨W, hF, hD, T, hT⟩

/-- No success, independence, or cap hypotheses are arguments of this contract. -/
theorem public_execution :
    ∃ K : ℕ, ∀ n : ℕ, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (T : CutQAlg n 1 (Candidate n) W)
      (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) W),
      R.len = (if 2 ≤ n then
        (4 * 12 * minimumDegreeBaseBudget n + 1) +
        12 * productBits n 1 *
          (rootThreshold n * Forest.forestBudget n ((1 / 3 : ℝ) / (rootThreshold n : ℝ)) + 1) +
        K * (12 * productBits n 1 * UniformStars.QH n) else 0) ∧
      T.step = R.step ∧
      (∀ read : AnswerTable n, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ (G : CapacityGraph (Fin n) 1) (S : Finset (Fin n)) (a : CutAnswer n 1),
        0 < T.prob (capacityRead G) R.len (some (S, a)) →
          ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S) ∧
      (∀ (G : CapacityGraph (Fin n) 1), 2 ≤ n →
        2 / 3 ≤ goodProb T.readout
          (fun c => ∃ S a, c = some (S, a) ∧ IsMinCut G.toWeighted S ∧
            decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
          (R.run (capacityRead G) *ᵥ T.init)) ∧
      (n < 2 → R.len = 0 ∧ ∀ read : AnswerTable n, T.prob read R.len none = 1) := by
  obtain ⟨K, hK⟩ := exists_public_global_program
  refine ⟨K, fun n => ?_⟩
  obtain ⟨W, hF, hD, T, R, hlen, hstep, hrun, hs, hp, hsmall⟩ := hK n
  refine ⟨W, hF, hD, T, R, ?_, hstep, hrun, ?_, ?_, hsmall⟩
  · rw [hlen]
    by_cases hn : 2 ≤ n
    · simp [globalQueries, hn, jointQueries, lowQueries, highQueries,
        minimumDegreeWitnessQueries_pos (by omega : 0 < n)]
    · simp [globalQueries, hn]
  · intro G S a ha
    exact hs G (some (S, a)) ha
  · intro G hn
    apply (hp G hn).trans_eq
    rw [goodProb_eq_sum_ite, goodProb_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro b _
    exact congrArg
      (fun d : Decidable (Forest.LowMinimumCandidate G (T.readout b)) =>
        @ite ℝ (Forest.LowMinimumCandidate G (T.readout b)) d
          (Complex.normSq ((R.run (capacityRead G) *ᵥ T.init) b)) 0)
      (Subsingleton.elim _ _)

theorem conditional_execution {n : ℕ} (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) (E₀ E₁ E : Candidate n → Prop)
    (hprefix : 0 < eventMass (jointLaw n t K ht eta read)
      (fun y => E₀ (y 0) ∧ E₁ (y (Fin.succ 0)))) :
    eventMass (jointLaw n t K ht eta read)
      (fun y => E₀ (y 0) ∧ E₁ (y (Fin.succ 0)) ∧ ∀ i : Fin K, E (y i.succ.succ)) /
      eventMass (jointLaw n t K ht eta read) (fun y => E₀ (y 0) ∧ E₁ (y (Fin.succ 0))) =
        eventMass (highLaw n read) E ^ K := joint_conditional_high t K ht eta read E₀ E₁ E hprefix

theorem small_input {n : ℕ} (hn : n < 2) (t K : ℕ) (ht : 0 < t) (eta : ℝ)
    (read : AnswerTable n) :
    (globalRoutine n t K ht eta).len = 0 ∧ (globalAlg n t K ht eta).prob read 0 none = 1 :=
  global_small hn t K ht eta read

end GlobalContract210

end QuantumUniformContracts3


/- Same-circuit quantum endpoint. -/
section CombinedQuantumContracts

set_option autoImplicit false

namespace QuantumGlobalContracts
open CutQueryComplexity QuantumQueryComplexity
open CutQueryComplexity.StarContraction2022.Quantum
open CutQueryComplexity.StarContraction2022.Quantum.Global
open CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms
open scoped Classical Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

/-- Match the numerical envelope to the actual native circuit, without an oracle adapter. -/
theorem native_schedule_matches {n : ℕ} (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    (globalRoutine n t K ht eta).len = CostBounds.combinedQueries n t K eta := by
  simp only [globalRoutine_len, globalQueries, ite_eq_left hn, jointQueries,
    lowQueries, highQueries, CostBounds.combinedQueries]

/-- One constant precedes every size; the same named physical circuit has the
native-query log-power-five bound and the explicit original minimum-shore/value
success event. No probability, independence or cost premise is supplied. -/
theorem public_log_five_endpoint :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      let T := globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)
      let R := globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)
      R.len = (if 2 ≤ n then CostBounds.combinedQueries n 12 publicHighTrials (1 / 3) else 0) ∧
      (R.len : ℝ) ≤ C * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 ∧
      T.step = R.step ∧
      (∀ read : AnswerTable n, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ (G : CapacityGraph (Fin n) 1) (S : Finset (Fin n)) (a : CutAnswer n 1),
        0 < T.prob (capacityRead G) R.len (some (S, a)) →
          ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S) ∧
      (∀ G : CapacityGraph (Fin n) 1, 2 ≤ n →
        2 / 3 ≤ goodProb T.readout
          (fun c => ∃ S a, c = some (S, a) ∧ IsMinCut G.toWeighted S ∧
            decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
          (R.run (capacityRead G) *ᵥ T.init)) ∧
      (n < 2 → R.len = 0 ∧ ∀ read : AnswerTable n, T.prob read R.len none = 1) := by
  refine ⟨CostBounds.coefficient 12 publicHighTrials (1 / 3),
    CostBounds.coefficient_pos (by norm_num) _ _, fun n => ?_⟩
  dsimp only
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · by_cases hn : 2 ≤ n
    · rw [native_schedule_matches hn]
      exact CostBounds.combinedQueries_le hn (by norm_num) publicHighTrials
        (by norm_num) (by norm_num)
    · have hlen := (global_small (Nat.lt_of_not_ge hn) 12 publicHighTrials
        (by norm_num) (1 / 3) (fun _ => 0)).1
      rw [hlen, Nat.cast_zero]
      have hc := (CostBounds.coefficient_pos (by norm_num : 1 ≤ 12) publicHighTrials (1 / 3)).le
      positivity
  · intro read
    exact ⟨globalRoutine_state _ _ _ _ _ read, globalRoutine_normalized _ _ _ _ _ read⟩
  · intro G S a h
    exact globalAlg_sound _ _ _ _ _ G (some (S, a)) h
  · intro G hn
    apply (globalRoutine_public_success n G hn).trans_eq
    rw [goodProb_eq_sum_ite, goodProb_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro b _
    exact congrArg
      (fun d : Decidable (Forest.LowMinimumCandidate G
        ((globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).readout b)) =>
        @ite ℝ (Forest.LowMinimumCandidate G
          ((globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).readout b)) d
          (Complex.normSq (((globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).run
            (capacityRead G) *ᵥ (globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)).init) b)) 0)
      (Subsingleton.elim _ _)
  · intro hn
    have hlen := (global_small hn 12 publicHighTrials (by norm_num) (1 / 3) (fun _ => 0)).1
    refine ⟨hlen, fun read => ?_⟩
    rw [hlen]
    exact (global_small hn 12 publicHighTrials (by norm_num) (1 / 3) read).2


end QuantumGlobalContracts

end CombinedQuantumContracts

#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.check_concrete_sum
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.check_constant_before_size
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.check_accepted_routine_lengths
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.CostBounds.check_accepted_routine_cost
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.explicit_component_eq
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.explicit_component_zero
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.terminal_positive_inside_component
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.public_buckets
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.bucket_local_geometry
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.compact_shore_data
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.component_query_one
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.component_run_map
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.component_output_subset
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.component_public_contract
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.component_fixed_joint
#audit_cut_decl CutQueryComplexity.GHGeometryContracts.approximator_component_public_contract
#audit_cut_decl APMCLiteral5.actual_capped_node
#audit_cut_decl APMCLiteral5.actual_part_adapter
#audit_cut_decl APMCLiteral5.actual_recursive_ledger
#audit_cut_decl APMCLiteral5.public_partition
#audit_cut_decl APMCLiteral5.exact_budget
#audit_cut_decl GHFrontierContracts.literal_contract_query
#audit_cut_decl GHFrontierContracts.substitute_contract_run
#audit_cut_decl GHFrontierContracts.contractDetProgram_run_public
#audit_cut_decl GHFrontierContracts.literal_frontier_run
#audit_cut_decl GHFrontierContracts.literal_frontier_contract
#audit_cut_decl GHFrontierContracts.actual_frontier_protection
#audit_cut_decl GHFrontierContracts.actual_frontier_counts
#audit_cut_decl GHFrontierContracts.literal_round_refinement
#audit_cut_decl GHFrontierContracts.literal_round_edges
#audit_cut_decl GHFrontierContracts.actual_steiner_minima
#audit_cut_decl GHFrontierContracts.literal_completed_tree_decoder
#audit_cut_decl GH210Contract.invalidChildGuard
#audit_cut_decl GH210Contract.smallTreeLaw
#audit_cut_decl GH210Contract.honestNoTruncation
#audit_cut_decl GH210Contract.honestValueLaw
#audit_cut_decl GH210Contract.publicTwoRespectingTrees
#audit_cut_decl GlobalContract210.native_joint
#audit_cut_decl GlobalContract210.public_execution
#audit_cut_decl GlobalContract210.conditional_execution
#audit_cut_decl GlobalContract210.small_input
#audit_cut_decl QuantumGlobalContracts.native_schedule_matches
#audit_cut_decl QuantumGlobalContracts.public_log_five_endpoint


/- Actual execution contract: quantum-uniform. -/
section QuantumUniformContracts4

set_option autoImplicit false



namespace SteinerEndpointContract211
open CutQueryComplexity CutQueryComplexity.GHReduction
open scoped Classical

variable {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem terminal_equivalence (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) :
    (∀ u, T.terminalEquiv hcover u = T.terminal u) ∧
    (T.terminalEquiv hcover).symm = T.attach ∧
    (∀ v, T.terminal (T.attach v) = v) :=
  ⟨T.terminalEquiv_apply hcover, T.terminalEquiv_symm hcover, T.terminal_attach hcover⟩

theorem completed_geometry (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) :
    (completeSteinerTree T hcover).topology.root = T.terminal T.tree.topology.root ∧
    ∀ u, (completeSteinerTree T hcover).topology.parent (T.terminal u) =
      T.terminal (T.tree.topology.parent u) ∧
      (completeSteinerTree T hcover).topology.depth (T.terminal u) = T.tree.topology.depth u ∧
      (completeSteinerTree T hcover).weight (T.terminal u) = T.tree.weight u ∧
      (completeSteinerTree T hcover).topology.D (T.terminal u) =
        WeightedGraph.pull T.attach (T.tree.topology.D u) := by
  refine ⟨rfl, fun u => ⟨?_, ?_, ?_, completeSteinerTree_subtree T hcover u⟩⟩
  · change T.terminalEquiv hcover
      (T.tree.topology.parent ((T.terminalEquiv hcover).symm (T.terminal u))) = _
    rw [T.terminalEquiv_symm, T.attach_terminal]
    rfl
  · change T.tree.topology.depth ((T.terminalEquiv hcover).symm (T.terminal u)) = _
    rw [T.terminalEquiv_symm, T.attach_terminal]
  · change T.tree.weight (T.attach (T.terminal u)) = _
    rw [T.attach_terminal]

/-- The family is public before G. Its actual output separates s and t,
beats every original competing shore, and reports the exact original value. -/
theorem public_zero_query_decoding (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) :
    ∃ P : V → V → DTree (Finset V) ℝ (Finset V × ℝ) 0,
      (∀ (s t : V) (read : Finset V → ℝ),
        (P s t).run read = (cutTreeAnswer (completeSteinerTree T hcover) s t, 0)) ∧
      (∀ (G : WeightedGraph V), IsSteinerCutTree G T → ∀ (s t : V), s ≠ t →
        s ∈ ((P s t).eval G.cut).1 ∧ t ∉ ((P s t).eval G.cut).1 ∧
        (∀ S : Finset V, s ∈ S → t ∉ S → G.cut ((P s t).eval G.cut).1 ≤ G.cut S) ∧
        G.cut ((P s t).eval G.cut).1 = ((P s t).eval G.cut).2) := by
  obtain ⟨P, hrun, hcorrect⟩ := completeSteinerTree_public_decoder T hcover
  refine ⟨P, hrun, ?_⟩
  intro G hT s t hst
  obtain ⟨hmin, hvalue⟩ := hcorrect G hT s t hst
  exact ⟨hmin.1, hmin.2.1, hmin.2.2, hvalue⟩

/-- Both output and zero calls are fixed for arbitrary replies, without a
correctness premise and also for coincident requested terminals. -/
theorem arbitrary_reply_run (T : SteinerCutTree V U)
    (hcover : Function.Surjective T.terminal) (s t : V) (read : Finset V → ℝ) :
    (completeSteinerTreeAnswerProgram T hcover s t).run read =
      ((pathShore (completeSteinerTree T hcover).topology s
          (minimumPathEdge (completeSteinerTree T hcover) s t),
        (completeSteinerTree T hcover).weight (minimumPathEdge (completeSteinerTree T hcover) s t)), 0) := rfl

end SteinerEndpointContract211

end QuantumUniformContracts4


/- Actual execution contract: quantum-forest. -/
section QuantumForestContracts5

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.Global
noncomputable section
open QuantumQueryComplexity ProductPrograms
open scoped Classical Matrix
attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

-- Complete literal contract: public_log_five_endpoint
theorem check_public_log_five :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      let T := globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)
      let R := globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)
      R.len = (if 2 ≤ n then CostBounds.combinedQueries n 12 publicHighTrials (1 / 3) else 0) ∧
      (R.len : ℝ) ≤ C * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 ∧
      T.step = R.step ∧
      (∀ read : AnswerTable n, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ (G : CapacityGraph (Fin n) 1) (S : Finset (Fin n)) (a : CutAnswer n 1),
        0 < T.prob (capacityRead G) R.len (some (S, a)) →
          ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S) ∧
      (∀ G : CapacityGraph (Fin n) 1, 2 ≤ n →
        2 / 3 ≤ goodProb T.readout
          (fun c => ∃ S a, c = some (S, a) ∧ IsMinCut G.toWeighted S ∧
            decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
          (R.run (capacityRead G) *ᵥ T.init)) ∧
      (n < 2 → R.len = 0 ∧ ∀ read : AnswerTable n, T.prob read R.len none = 1) :=
  public_log_five_endpoint

-- Complete literal contract: public_natural_log_five_endpoint
theorem check_public_natural_log_five :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      let T := globalAlg n 12 publicHighTrials (by norm_num) (1 / 3)
      let R := globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)
      R.len = (if 2 ≤ n then CostBounds.combinedQueries n 12 publicHighTrials (1 / 3) else 0) ∧
      (2 ≤ n → (R.len : ℝ) ≤ C * Real.sqrt (n : ℝ) * (Real.log (2 * (n : ℝ))) ^ 5) ∧
      T.step = R.step ∧
      (∀ read : AnswerTable n, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ (G : CapacityGraph (Fin n) 1) (S : Finset (Fin n)) (a : CutAnswer n 1),
        0 < T.prob (capacityRead G) R.len (some (S, a)) →
          ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S) ∧
      (∀ G : CapacityGraph (Fin n) 1, 2 ≤ n →
        2 / 3 ≤ goodProb T.readout
          (fun c => ∃ S a, c = some (S, a) ∧ IsMinCut G.toWeighted S ∧
            decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
          (R.run (capacityRead G) *ᵥ T.init)) ∧
      (n < 2 → R.len = 0 ∧ ∀ read : AnswerTable n, T.prob read R.len none = 1) :=
  public_natural_log_five_endpoint

-- Complete literal contract: exists_public_endpoint
theorem check_exists_public :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∃ (Work : Type) (_ : Fintype Work) (_ : DecidableEq Work)
        (T : CutQAlg n 1 (Candidate n) Work)
        (R : QRoutine (Finset (Fin n)) (CutAnswer n 1) Work),
      R.len = (if 2 ≤ n then CostBounds.combinedQueries n 12 publicHighTrials (1 / 3) else 0) ∧
      (R.len : ℝ) ≤ C * Real.sqrt (n : ℝ) * (logWidth n : ℝ) ^ 5 ∧
      (2 ≤ n → (R.len : ℝ) ≤ (1024 * C) * Real.sqrt (n : ℝ) * (Real.log (2 * (n : ℝ))) ^ 5) ∧
      T.step = R.step ∧
      (∀ read : AnswerTable n, R.run read *ᵥ T.init = T.state read R.len ∧
        IsQState (R.run read *ᵥ T.init)) ∧
      (∀ (G : CapacityGraph (Fin n) 1) (S : Finset (Fin n)) (a : CutAnswer n 1),
        0 < T.prob (capacityRead G) R.len (some (S, a)) →
          ProperShore S ∧ decodeCutAnswer a = G.toWeighted.cut S) ∧
      (∀ G : CapacityGraph (Fin n) 1, 2 ≤ n →
        2 / 3 ≤ goodProb T.readout
          (fun c => ∃ S a, c = some (S, a) ∧ IsMinCut G.toWeighted S ∧
            decodeCutAnswer a = G.toWeighted.cut S ∧ decodeCutAnswer a = mincutValue G.toWeighted)
          (R.run (capacityRead G) *ᵥ T.init)) ∧
      (n < 2 → R.len = 0 ∧ ∀ read : AnswerTable n, T.prob read R.len none = 1) :=
  exists_public_endpoint

-- Every native charge remains in the exact executed schedule.
theorem check_exact_native_charges {n : ℕ} (hn : 2 ≤ n) (t K : ℕ) (ht : 0 < t) (eta : ℝ) :
    (globalRoutine n t K ht eta).len =
      minimumDegreeWitnessQueries n t +
      12 * productBits n 1 *
        (rootThreshold n * Forest.forestBudget n (eta / (rootThreshold n : ℝ)) + 1) +
      K * (12 * productBits n 1 * UniformStars.QH n) :=
  native_schedule_matches hn t K ht eta

-- The conventional logarithm is derived, not supplied as an envelope.
theorem check_log_comparison {n : ℕ} (hn : 2 ≤ n) :
    (logWidth n : ℝ) ≤ 4 * Real.log (2 * (n : ℝ)) := logWidth_le_four_log hn

-- The concrete natural-log coefficient is 1024 times the exact original coefficient.
theorem check_explicit_natural_coefficient {n : ℕ} (hn : 2 ≤ n) :
    ((globalRoutine n 12 publicHighTrials (by norm_num) (1 / 3)).len : ℝ) ≤
      (1024 * (819205 * 12 + 70860 * (1 + Real.log 3) ^ 2 +
        600000000000 * (publicHighTrials : ℝ))) * Real.sqrt (n : ℝ) *
        (Real.log (2 * (n : ℝ))) ^ 5 := by
  have h := globalRoutine_naturalLog_cost hn
  simpa only [naturalLogCoefficient, logFiveCoefficient_eq] using h

end
end CutQueryComplexity.StarContraction2022.Quantum.Global



end QuantumForestContracts5


/- Actual execution contract: gh. -/
section GHContracts5

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction
open CutQueryComplexity.Probability
open scoped Classical ENNReal

namespace GH211Contract
noncomputable section

-- Exact output/count coupling for the actual truncation constructor.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem truncateRunLaw {I A O : Type} {q : ℕ} (T : RTree I A O q)
    (k : ℕ) (read : I → A) :
    RTree.run read (T.truncate k) = (RTree.run read T).map
      (fun p => (if p.2 ≤ k then some p.1 else none, min p.2 k)) := by
  induction q generalizing k with
  | zero =>
    simp [RTree.truncate, RTree.run_pure, RTree.run, PMF.map_comp, Function.comp_def]
  | succ q ih =>
    cases k with
    | zero =>
      simp only [RTree.truncate, RTree.run, PMF.map_comp, PMF.map_bind, Function.comp_def]
      rw [PMF.map]
      congr 1
      funext action
      rcases action with o | ⟨i, next⟩
      · simp [PMF.pure_map]
      · simp only [PMF.map_comp, Function.comp_def, Nat.not_succ_le_zero,
          ite_false, Nat.min_zero]
        exact (PMF.map_const (RTree.run read (next (read i))) (none, 0)).symm
    | succ k =>
      simp only [RTree.truncate, RTree.run, PMF.bind_map, PMF.map_bind, Function.comp_def]
      congr 1
      funext action
      rcases action with o | ⟨i, next⟩
      · simp [PMF.pure_map]
      · dsimp only
        rw [ih]
        simp only [PMF.map_comp, Function.comp_def, Nat.add_le_add_iff_right]
        apply congrArg (fun f => (RTree.run read (next (read i))).map f)
        funext p
        apply Prod.ext
        · rfl
        · omega

variable {V : Type} [Fintype V] [DecidableEq V] {M n : ℕ} {Q : ℕ → ℕ}

theorem badLengthRunLaw (family : CanonicalSTFamily M Q)
    (samples trials levels scale exponent : ℕ) (U : Finset V) (s : U)
    (hvn : Fintype.card V ≤ n) (L : List (RootedTree U)) (hlen : L.length ≠ samples)
    (read : Finset V → ℝ) :
    RTree.run read (sampledGuideContinuation family n samples trials levels scale exponent U s hvn L) =
      PMF.pure ((fun _ : V => (none : Option ℝ)), 0) := by
  simp only [sampledGuideContinuation, hlen, dite_false, RTree.run_pure, PMF.pure_map]

theorem validLengthRunLaw (family : CanonicalSTFamily M Q)
    (samples trials levels scale exponent : ℕ) (U : Finset V) (s : U)
    (hvn : Fintype.card V ≤ n) (L : List (RootedTree U)) (hlen : L.length = samples)
    (read : Finset V → ℝ) :
    RTree.run read (sampledGuideContinuation family n samples trials levels scale exponent U s hvn L) =
      (RTree.run read (randomTable (fun _ => none) (fun i : Fin samples =>
        guideTwoTree family n trials levels scale exponent (Nat.clog 2 (n + 1))
          (terminalGuide U s (guideListEntry L hlen i)) hvn))).map
            (fun p => (mergeGuideValues p.1, p.2)) := by
  rw [sampledGuideContinuation, dite_eq_left hlen, RTree.run_cast, random_run_map]

-- Sampling uses only K, costs zero input queries, and binds the actual list.
theorem sampledRunLaw (family : CanonicalSTFamily M Q)
    (samples trials levels scale exponent : ℕ) (K : WeightedGraph V)
    (U : Finset V) (s : U) (hU : 2 ≤ U.card) (hpos : 0 < terminalMin K U)
    (hvn : Fintype.card V ≤ n) (read : Finset V → ℝ) :
    RTree.run read (sampledGuideTree family n samples trials levels scale exponent K U s hU hpos hvn) =
      (independentSamples (terminalGuidePMF K U hU hpos) samples).bind
        (fun L => RTree.run read
          (sampledGuideContinuation family n samples trials levels scale exponent U s hvn L)) := by
  simp only [sampledGuideTree, RTree.run_cast, RTree.run_bind, guideSampleProgram,
    RTree.run_pure, PMF.bind_map, Function.comp_def, zero_add, Prod.eta]
  apply congrArg (fun f => (independentSamples (terminalGuidePMF K U hU hpos) samples).bind f)
  funext L
  exact PMF.map_id _

theorem singleSourceRunLaw (family : CanonicalSTFamily M Q)
    (samples trials levels scale exponent : ℕ) (K : WeightedGraph V) (U : Finset V)
    (s : V) (hvn : Fintype.card V ≤ n) (read : Finset V → ℝ) :
    RTree.run read (singleSourceTree family n samples trials levels scale exponent K U s hvn) =
      (RTree.run read (randomTable (fun _ => none) (fun j : Fin (bucketCount M) =>
        bucketSourceTree family n samples trials levels scale exponent K U s hvn j.val))).map
          (fun p => (mergeBucketValues K U s p.1, p.2)) := by
  unfold singleSourceTree singleSourceBudget
  rw [RTree.run_cast, random_run_map]

theorem zeroValueLaw (G K : WeightedGraph V) (U : Finset V) (s t : V)
    (ht : t ∈ U) (hts : t ≠ s) (hzero : stValue G t s = 0)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
      K.cut S ≤ (101 / 100 : ℝ) * G.cut S) :
    zeroSourceEstimate K U s t = some 0 := by
  have ha := (stValue_approximation_fixed G K happrox hts).2
  have hn := stValue_nonneg K t s
  have hzK : stValue K t s = 0 := by rw [hzero] at ha; linarith
  simp [zeroSourceEstimate, ht, hts, hzK]

theorem honestCostBound (family : CanonicalSTFamily M Q)
    (samples trials levels scale exponent : ℕ) (K : WeightedGraph V) (U : Finset V)
    (s : V) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) {p : (V → Option ℝ) × ℕ}
    (hp : p ∈ (RTree.run G.cut
      (singleSourceTree family n samples trials levels scale exponent K U s hvn)).support) :
    p.2 ≤ singleSourceSharpBudget M Q n samples trials levels scale exponent := by
  haveI : Nonempty V := ⟨s⟩
  exact cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
    (singleSourceTree_cost_scaled family hQ samples trials levels scale exponent G K hG U s hvn hp)

-- No honest truncation: preserve the joint law, including each actual count.
theorem honestJointLaw (family : CanonicalSTFamily M Q)
    (samples trials levels scale exponent : ℕ) (K : WeightedGraph V) (U : Finset V)
    (s : V) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) :
    RTree.run G.cut (singleSourceCappedTree family n samples trials levels scale exponent K U s hvn) =
      (RTree.run G.cut (singleSourceTree family n samples trials levels scale exponent K U s hvn)).map
        (fun p => (some p.1, p.2)) := by
  rw [singleSourceCappedTree, truncateRunLaw]
  apply PMF.ext
  intro output
  simp only [PMF.map_apply]
  apply tsum_congr
  intro p
  by_cases hp : p ∈ (RTree.run G.cut
      (singleSourceTree family n samples trials levels scale exponent K U s hvn)).support
  · have hcost := honestCostBound family samples trials levels scale exponent K U s hvn hQ G hG hp
    rw [ite_eq_left hcost, Nat.min_eq_left hcost]
  · have hz : RTree.run G.cut
        (singleSourceTree family n samples trials levels scale exponent K U s hvn) p = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hp
    simp only [hz, ite_self]

theorem honestOutputLaw (family : CanonicalSTFamily M Q)
    (samples trials levels scale exponent : ℕ) (K : WeightedGraph V) (U : Finset V)
    (s : V) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) :
    (singleSourceCappedTree family n samples trials levels scale exponent K U s hvn).eval G.cut =
      ((singleSourceTree family n samples trials levels scale exponent K U s hvn).eval G.cut).map some := by
  simp only [RTree.eval, honestJointLaw family samples trials levels scale exponent K U s hvn hQ G hG,
    PMF.map_comp, Function.comp_def]

-- K is explicit public data. Its approximation premise is quantified after P
-- and the hidden input G; no computed sparsifier or completed GH tree is assumed.
theorem publicSingleSource (family : CanonicalSTFamily M Q)
    (samples trials levels scale exponent : ℕ) (K : WeightedGraph V) (U : Finset V)
    (s : V) (hvn : Fintype.card V ≤ n) :
    ∃ P : RTree (Finset V) ℝ (Option (V → Option ℝ))
        (singleSourceSharpBudget M Q n samples trials levels scale exponent),
      P = singleSourceCappedTree family n samples trials levels scale exponent K U s hvn ∧
      (∀ answer : TranscriptOracle.AnswerPolicy (Finset V) ℝ, ∀ history p,
        p ∈ (TranscriptOracle.run answer P history).support →
          p.2 ≤ singleSourceSharpBudget M Q n samples trials levels scale exponent) ∧
      (SizeRegular n Q → ∀ G : WeightedGraph V, InputPromise M G →
        RTree.run G.cut P =
          (RTree.run G.cut (singleSourceTree family n samples trials levels scale exponent K U s hvn)).map
            (fun p => (some p.1, p.2))) ∧
      (SizeRegular n Q → n ≤ scale → thresholdLevels n ≤ levels →
        ∀ G : WeightedGraph V, InputPromise M G → s ∈ U →
          (∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
            K.cut S ≤ (101 / 100 : ℝ) * G.cut S) →
          mass (P.eval G.cut) (fun output => ¬output.elim False (fun values =>
            (∀ t value, values t = some value → stValue G t s ≤ value) ∧
            (∀ t ∈ U, t ≠ s → values t = some (stValue G t s)))) ≤
            (bucketCount M : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) ^ samples +
              (samples : ℝ≥0∞) * guideTwoError M trials scale exponent (Nat.clog 2 (n + 1)) n)) := by
  refine ⟨singleSourceCappedTree family n samples trials levels scale exponent K U s hvn,
    rfl, ?_, ?_, ?_⟩
  · exact fun answer history p hp => TranscriptOracle.cost_le _ answer history hp
  · exact fun hQ G hG => honestJointLaw family samples trials levels scale exponent K U s hvn hQ G hG
  · exact fun hQ hnscale hlevels G hG hs happrox =>
      singleSourceCappedTree_failure_le family hQ hnscale samples trials levels exponent hlevels
        G K hG U s hs hvn happrox

end
end GH211Contract




end GHContracts5


/- Actual execution contract: quantum-neighbors. -/
section QuantumNeighborsContracts4

/-! Literal evidence for the supplied public finite constructions. The child
trees and original shore witnesses remain premises; no recursive producer is
asserted. Querying a supplied bridge shore is charged explicitly. -/

set_option autoImplicit false

namespace GHAssemblyContracts

open CutQueryComplexity CutQueryComplexity.GHReduction CutQueryComplexity.WeightedGraph
open scoped Classical
noncomputable section

variable {V W U : Type} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [Fintype U] [DecidableEq U]

theorem literal_lift_constructor (T : SteinerCutTree W U) (pi : V → W)
    (r : W → V) (hr : ∀ w, pi (r w) = w) :
    ∃ P : DTree (Finset V) ℝ (SteinerCutTree V U) 0,
      P = DTree.pure (T.lift pi r hr) ∧
      (∀ read, P.run read = (T.lift pi r hr, 0)) ∧
      (∀ G : WeightedGraph V,
        (∀ w, Certificate.GomoryHu.RootProtected G (fiber pi w) (r w)) →
        IsSteinerCutTree (G.contract pi) T → IsSteinerCutTree G (P.eval G.cut)) := by
  refine ⟨DTree.pure (T.lift pi r hr), rfl, fun _ => rfl, ?_⟩
  intro G hroot hT
  exact T.lift_correct G pi r hr hroot hT

theorem literal_assembly_constructor (F : Finset (U × U)) (hF : SpanTree.Spans F)
    (root : U) (weight : U × U → ℝ) (terminal : U → V) (attach : V → U)
    (hfix : ∀ u, attach (terminal u) = u) :
    ∃ P : DTree (Finset V) ℝ (SteinerCutTree V U) 0,
      P = DTree.pure (assembleSteinerTree F hF root weight terminal attach hfix) ∧
      (∀ read, P.run read = (assembleSteinerTree F hF root weight terminal attach hfix, 0)) ∧
      (∀ G : WeightedGraph V, ∀ shore : U × U → Finset U,
        EdgeShoreSystem F shore →
        (∀ e ∈ F, IsSTMinCut G (terminal e.1) (terminal e.2) (pull attach (shore e))) →
        (∀ e ∈ F, weight e = G.cut (pull attach (shore e))) →
        IsSteinerCutTree G (P.eval G.cut)) := by
  refine ⟨DTree.pure (assembleSteinerTree F hF root weight terminal attach hfix),
    rfl, fun _ => rfl, ?_⟩
  intro G shore hshore hmin hweight
  exact assembleSteinerTree_correct G F hF root weight terminal attach hfix
    shore hshore hmin hweight

theorem actual_joined_geometry (L : RootedTree U) (R : RootedTree W) (a : U) (b : W) :
    SpanTree.Spans (joinedEdges L R a b) ∧
      EdgeShoreSystem (joinedEdges L R a b) (joinedShore L R a b) :=
  ⟨joinedEdges_spans L R a b, joinedShore_system L R a b⟩

theorem derived_bridge_minimum (G : WeightedGraph V)
    (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (hL : IsSteinerCutTree G L) (hR : IsSteinerCutTree G R)
    (u : U) (v : W) (S : Finset V)
    (hS : IsSTMinCut G (L.terminal u) (R.terminal v) S)
    (hLterm : ∀ x, L.terminal x ∈ S) (hRterm : ∀ x, R.terminal x ∉ S) :
    IsSTMinCut G (L.terminal (L.attach (R.terminal v)))
      (R.terminal (R.attach (L.terminal u))) S :=
  steiner_bridge_minCut G L R hL hR u v S hS
    (hLterm (L.attach (R.terminal v))) (hRterm (R.attach (L.terminal u)))

theorem literal_join_constructor (S : Finset V)
    (L : SteinerCutTree V U) (R : SteinerCutTree V W) (u : U) (v : W)
    (bridge : ℝ) (hLterm : ∀ x, L.terminal x ∈ S) (hRterm : ∀ x, R.terminal x ∉ S) :
    ∃ P : DTree (Finset V) ℝ (SteinerCutTree V (U ⊕ W)) 0,
      P = DTree.pure (joinSteinerTrees S L R (L.attach (R.terminal v))
        (R.attach (L.terminal u)) bridge hLterm hRterm) ∧
      (∀ read, P.run read = (joinSteinerTrees S L R (L.attach (R.terminal v))
        (R.attach (L.terminal u)) bridge hLterm hRterm, 0)) ∧
      (∀ G : WeightedGraph V, IsSteinerCutTree G L → IsSteinerCutTree G R →
        IsSTMinCut G (L.terminal u) (R.terminal v) S →
        (∀ x, x ∉ S → L.attach x = L.attach (R.terminal v)) →
        (∀ x ∈ S, R.attach x = R.attach (L.terminal u)) →
        bridge = G.cut S → IsSteinerCutTree G (P.eval G.cut)) := by
  refine ⟨DTree.pure (joinSteinerTrees S L R (L.attach (R.terminal v))
    (R.attach (L.terminal u)) bridge hLterm hRterm), rfl, fun _ => rfl, ?_⟩
  intro G hL hR hS hLout hRin hbridge
  exact joinSteinerTrees_correct G S L R hL hR u v hS hLterm hRterm
    hLout hRin bridge hbridge

/-- The actual public path selector, with its shore pulled through the supplied
attachment. No graph or correctness witness enters the selector. -/
def steinerAnswer (T : SteinerCutTree V U) (s t : U) : Finset V × ℝ :=
  (pull T.attach (cutTreeAnswer T.tree s t).1, (cutTreeAnswer T.tree s t).2)

def steinerAnswerProgram (T : SteinerCutTree V U) (s t : U) :
    DTree (Finset V) ℝ (Finset V × ℝ) 0 := DTree.pure (steinerAnswer T s t)

theorem literal_steiner_answer_run (T : SteinerCutTree V U) (s t : U)
    (read : Finset V → ℝ) :
    (steinerAnswerProgram T s t).run read = (steinerAnswer T s t, 0) := rfl

theorem actual_steiner_answer_correct (G : WeightedGraph V) (T : SteinerCutTree V U)
    (hT : IsSteinerCutTree G T) {s t : U} (hst : s ≠ t) :
    IsSTMinCut G (T.terminal s) (T.terminal t) (steinerAnswer T s t).1 ∧
      G.cut (steinerAnswer T s t).1 = (steinerAnswer T s t).2 := by
  let e := minimumPathEdge T.tree s t
  obtain ⟨he, hleast⟩ := minimumPathEdge_spec T.tree hst
  have he0 := ((mem_pathEdges T.tree.topology s t e).mp he).1
  have hweight : G.cut (steinerPathShore T s e) = T.tree.weight e := by
    rw [cut_steinerPathShore]
    exact (hT e he0).2.symm
  obtain ⟨hs, ht⟩ := steinerPathShore_separates T he
  change IsSTMinCut G (T.terminal s) (T.terminal t) (steinerPathShore T s e) ∧
    G.cut (steinerPathShore T s e) = T.tree.weight e
  refine ⟨⟨hs, ht, fun A hsA htA => ?_⟩, hweight⟩
  obtain ⟨d, hcross, hpath⟩ := path_crossing T.tree.topology
    (S := terminalTrace T A) (by simpa using hsA) (by simpa using htA)
  rw [hweight]
  exact (hleast d hpath).trans (steiner_weight_le_crossing_cut G T hT hcross)

theorem literal_steiner_decoder (T : SteinerCutTree V U) (s t : U) :
    ∃ P : DTree (Finset V) ℝ (Finset V × ℝ) 0,
      P = steinerAnswerProgram T s t ∧
      (∀ read, P.run read = (steinerAnswer T s t, 0)) ∧
      (∀ G : WeightedGraph V, IsSteinerCutTree G T → s ≠ t →
        IsSTMinCut G (T.terminal s) (T.terminal t) (P.eval G.cut).1 ∧
        G.cut (P.eval G.cut).1 = (P.eval G.cut).2) := by
  refine ⟨steinerAnswerProgram T s t, rfl, literal_steiner_answer_run T s t, ?_⟩
  intro G hT hst
  exact actual_steiner_answer_correct G T hT hst

/-- An evidence-only wrapper executes one original cut query for the supplied
bridge shore, then applies the unchanged public join constructor. -/
def queriedJoin (S : Finset V) (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (u : U) (v : W) (hLterm : ∀ x, L.terminal x ∈ S) (hRterm : ∀ x, R.terminal x ∉ S) :
    DTree (Finset V) ℝ (SteinerCutTree V (U ⊕ W)) 1 :=
  DTree.query S (fun bridge => DTree.pure (joinSteinerTrees S L R
    (L.attach (R.terminal v)) (R.attach (L.terminal u)) bridge hLterm hRterm))

theorem queriedJoin_run (S : Finset V) (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (u : U) (v : W) (hLterm : ∀ x, L.terminal x ∈ S) (hRterm : ∀ x, R.terminal x ∉ S)
    (read : Finset V → ℝ) :
    (queriedJoin S L R u v hLterm hRterm).run read =
      (joinSteinerTrees S L R (L.attach (R.terminal v)) (R.attach (L.terminal u))
        (read S) hLterm hRterm, 1) := rfl

theorem queriedJoin_correct (S : Finset V) (L : SteinerCutTree V U) (R : SteinerCutTree V W)
    (u : U) (v : W) (hLterm : ∀ x, L.terminal x ∈ S) (hRterm : ∀ x, R.terminal x ∉ S)
    (G : WeightedGraph V) (hL : IsSteinerCutTree G L) (hR : IsSteinerCutTree G R)
    (hS : IsSTMinCut G (L.terminal u) (R.terminal v) S)
    (hLout : ∀ x, x ∉ S → L.attach x = L.attach (R.terminal v))
    (hRin : ∀ x ∈ S, R.attach x = R.attach (L.terminal u)) :
    IsSteinerCutTree G ((queriedJoin S L R u v hLterm hRterm).eval G.cut) :=
  joinSteinerTrees_correct G S L R hL hR u v hS hLterm hRterm hLout hRin (G.cut S) rfl

theorem literal_queried_join_decoder (S : Finset V)
    (L : SteinerCutTree V U) (R : SteinerCutTree V W) (u : U) (v : W)
    (hLterm : ∀ x, L.terminal x ∈ S) (hRterm : ∀ x, R.terminal x ∉ S) (s t : U ⊕ W) :
    ∃ P : DTree (Finset V) ℝ (Finset V × ℝ) 1,
      P = (queriedJoin S L R u v hLterm hRterm).map (fun J => steinerAnswer J s t) ∧
      (∀ read, P.run read =
        (steinerAnswer (joinSteinerTrees S L R (L.attach (R.terminal v))
          (R.attach (L.terminal u)) (read S) hLterm hRterm) s t, 1)) ∧
      (∀ G : WeightedGraph V, IsSteinerCutTree G L → IsSteinerCutTree G R →
        IsSTMinCut G (L.terminal u) (R.terminal v) S →
        (∀ x, x ∉ S → L.attach x = L.attach (R.terminal v)) →
        (∀ x ∈ S, R.attach x = R.attach (L.terminal u)) → s ≠ t →
        IsSTMinCut G (joinedTerminal L R s) (joinedTerminal L R t) (P.eval G.cut).1 ∧
        G.cut (P.eval G.cut).1 = (P.eval G.cut).2) := by
  refine ⟨(queriedJoin S L R u v hLterm hRterm).map (fun J => steinerAnswer J s t),
    rfl, ?_, ?_⟩
  · intro read
    rw [DTree.run_map, queriedJoin_run]
  · intro G hL hR hS hLout hRin hst
    exact actual_steiner_answer_correct G _
      (queriedJoin_correct S L R u v hLterm hRterm G hL hR hS hLout hRin) hst

end
end GHAssemblyContracts


end QuantumNeighborsContracts4


/- Actual execution contract: apmc. -/
section APMCContracts5

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.DeterministicAPMCExpansion
open AllPairs AllPairsAudit Finset WeightedGraph Filter Asymptotics
open CutQueryComplexity.DeterministicAPMCExpansion.Pruning
open scoped Classical
noncomputable section

namespace APMCLiteral6

-- Follow the literal indexed tree with replies allowed to depend on the
-- entire transcript. Repeated identical questions may receive different answers.
def historyRun {I A O : Type} (reply : List (I × A) → I → A)
    (history : List (I × A)) : {q : ℕ} → DTree I A O q → O × ℕ
  | 0, out => (out, 0)
  | _ + 1, .inl out => (out, 0)
  | _ + 1, .inr (i, next) =>
      let answer := reply history i
      let result := historyRun reply (history ++ [(i, answer)]) (next answer)
      (result.1, result.2 + 1)

theorem historyRun_cost_le {I A O : Type} (reply : List (I × A) → I → A) :
    {q : ℕ} → (T : DTree I A O q) → (history : List (I × A)) →
      (historyRun reply history T).2 ≤ q
  | 0, _, _ => le_rfl
  | _ + 1, .inl _, _ => Nat.zero_le _
  | _ + 1, .inr (i, next), history =>
      Nat.succ_le_succ (historyRun_cost_le reply (next (reply history i))
        (history ++ [(i, reply history i)]))

theorem historyRun_of_read {I A O : Type} (read : I → A) :
    {q : ℕ} → (T : DTree I A O q) → (history : List (I × A)) →
      historyRun (fun _ i => read i) history T = DTree.run read T
  | 0, _, _ => rfl
  | _ + 1, .inl _, _ => rfl
  | _ + 1, .inr (i, next), history => by
      simp only [historyRun, DTree.run, historyRun_of_read read]

-- The single original cut in paddedQuery is an executed query; its triangle
-- correction is public. Substituting it preserves the full output/count pair.
theorem padded_substitute_run {V O : Type} [Fintype V] [DecidableEq V]
    (read : Finset V → ℝ) : {q : ℕ} → (T : DTree (Finset (Padded V)) ℝ O q) →
      DTree.run read (T.substitute paddedQuery) =
        DTree.run (fun A => read (originalShore A) + triangleGraph.cut A) T
  | 0, _ => rfl
  | _ + 1, .inl _ => by simp [DTree.substitute, DTree.run_pure, DTree.run]
  | _ + 1, .inr (i, next) => by
      simp only [DTree.substitute, DTree.run_cast, DTree.run_bind, paddedQuery,
        DTree.eval_query, DTree.eval_pure, DTree.cost, DTree.run_query,
        padded_substitute_run read, DTree.run, Nat.zero_add, Nat.add_comm]

theorem unpadProgram_run {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (T : DTree (Finset (Padded V)) ℝ (Answers (Padded V)) q) (read : Finset V → ℝ) :
    DTree.run read (unpadProgram T) =
      (restrictAnswers (T.eval (fun A => read (originalShore A) + triangleGraph.cut A)),
       T.cost (fun A => read (originalShore A) + triangleGraph.cut A)) := by
  simp only [unpadProgram, DTree.run_cast, DTree.run_map, padded_substitute_run,
    DTree.eval, DTree.cost]

theorem padding_exact_count (n : ℕ) (read : Finset (Fin n) → ℝ) :
    DTree.run read (CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program n) =
      (restrictAnswers ((minimumDegreeProgram (V := Padded (Fin n))).eval
        (fun A => read (originalShore A) + triangleGraph.cut A)),
       (minimumDegreeProgram (V := Padded (Fin n))).cost
        (fun A => read (originalShore A) + triangleGraph.cut A)) :=
  unpadProgram_run (minimumDegreeProgram (V := Padded (Fin n))) read

-- The actual decomposition output supplies the recovery premises. This
-- contract quantifies over the original graph with only the unit-weight promise.
theorem actual_padded_pipeline (n : ℕ) (G : WeightedGraph (Fin n)) (hG : Unweighted G) :
    let N := Fintype.card (Padded (Fin n))
    let R := roundBudget N
    let t := cubeRoot N
    let hR : 1 ≤ R := by have h := roundBudget_ge_two N; omega
    let state := (Decomposition.decomposition (V := Padded (Fin n)) R t hR).eval (paddedGraph G).cut
    ∃ out : Answers (Padded (Fin n)),
      state.Correct (paddedGraph G) t ∧
      (partitionAnswers state.representativeMap (2 * t) (8 * R) (t ^ 2)).eval
        (paddedGraph G).cut = some out ∧
      (minimumDegreeProgram (V := Padded (Fin n))).eval (paddedGraph G).cut = out ∧
      (CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program n).eval G.cut = restrictAnswers out ∧
      allPairsGood G (restrictAnswers out) := by
  dsimp only
  let N := Fintype.card (Padded (Fin n))
  let R := roundBudget N
  let t := cubeRoot N
  have hR : 1 ≤ R := by have h := roundBudget_ge_two N; omega
  have ht : 0 < t := cubeRoot_pos N
  let state := (Decomposition.decomposition (V := Padded (Fin n)) R t hR).eval (paddedGraph G).cut
  have hc : state.Correct (paddedGraph G) t :=
    Decomposition.decomposition_correct (paddedGraph G) (padded_unweighted hG) R t hR
      (by omega) (le_cubeRoot_pow N) (fun q hq => local_rounds_le hq)
  have hN : Fintype.card (Padded (Fin n)) ≤ (2 * t) * t ^ 2 := by
    have h := le_cubeRoot_pow N
    change N ≤ t ^ 3 at h
    change N ≤ (2 * t) * t ^ 2
    nlinarith
  obtain ⟨out, he, hgood⟩ := partitionAnswers_correct (padded_unweighted hG)
    (padded_min_degree G) state.representativeMap (by omega : 0 < 2 * t)
    (by omega : 0 < 8 * R) (pow_pos ht 2) hN
    (state.representativeMap_additive (paddedGraph G) t hc)
    (state.representativeMap_boundary (paddedGraph G) t hc)
  have hcore : (minimumDegreeProgram (V := Padded (Fin n))).eval (paddedGraph G).cut = out := by
    simp only [minimumDegreeProgram, CutQueryComplexity.DeterministicAPMCExpansion.Pruning.coreBudget, DTree.eval_bind,
      totalPartitionAnswers, DTree.eval_map]
    change ((partitionAnswers state.representativeMap (2 * t) (8 * R) (t ^ 2)).eval
      (paddedGraph G).cut).getD emptyAnswers = out
    rw [he]
    rfl
  refine ⟨out, hc, he, hcore, ?_, restrictAnswers_correct G hgood⟩
  have horacle : (fun A => G.cut (originalShore A) + triangleGraph.cut A) =
      (paddedGraph G).cut := by
    funext A
    exact (padded_cut_eq G A).symm
  have hp := congrArg Prod.fst (padding_exact_count n G.cut)
  change (CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program n).eval G.cut = restrictAnswers
    ((minimumDegreeProgram (V := Padded (Fin n))).eval
      (fun A => G.cut (originalShore A) + triangleGraph.cut A)) at hp
  rw [horacle, hcore] at hp
  exact hp

theorem budget_le_natural_log {n : ℕ} (hn : 2 ≤ n) :
    (CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget n : ℝ) ≤ (headlineConstant * (5 / Real.log 2) ^ 5) *
      (n : ℝ) ^ (5 / 3 : ℝ) * Real.log (n : ℝ) ^ 5 := by
  calc
    _ ≤ headlineConstant * (n : ℝ) ^ (5 / 3 : ℝ) * (sizeLog n : ℝ) ^ 5 :=
      budget_le (by omega)
    _ ≤ headlineConstant * (n : ℝ) ^ (5 / 3 : ℝ) *
        ((5 / Real.log 2) * Real.log (n : ℝ)) ^ 5 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (sizeLog_le_log hn) 5)
        (mul_nonneg headlineConstant_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = _ := by ring

-- Literal uniform endpoint, explicitly tied to the named CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program. Constants,
-- CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget and CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program family all precede input size, hidden graph and replies.
theorem literal_deterministic_allPairs :
    ∃ (Cceil Cln : ℝ) (q : ℕ → ℕ)
      (P : (n : ℕ) → DTree (Finset (Fin n)) ℝ (Answers (Fin n)) (q n)),
      0 < Cceil ∧ 0 < Cln ∧ q = CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget ∧ HEq P CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program ∧
      (∀ (n : ℕ) (G : WeightedGraph (Fin n)), Unweighted G →
        ∀ s t : Fin n, s ≠ t →
          s ∈ (((P n).eval G.cut) s t).shore ∧
          t ∉ (((P n).eval G.cut) s t).shore ∧
          (∀ S : Finset (Fin n), s ∈ S → t ∉ S →
            G.cut (((P n).eval G.cut) s t).shore ≤ G.cut S) ∧
          (((P n).eval G.cut) s t).value = G.cut (((P n).eval G.cut) s t).shore) ∧
      (∀ n (read : Finset (Fin n) → ℝ), (P n).cost read ≤ q n) ∧
      (∀ n (reply : List (Finset (Fin n) × ℝ) → Finset (Fin n) → ℝ),
        (historyRun reply [] (P n)).2 ≤ q n) ∧
      (∀ n : ℕ, 2 ≤ n → (q n : ℝ) ≤ Cceil * (n : ℝ) ^ (5 / 3 : ℝ) *
        ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 5) ∧
      (∀ n : ℕ, 2 ≤ n → (q n : ℝ) ≤ Cln * (n : ℝ) ^ (5 / 3 : ℝ) *
        Real.log (n : ℝ) ^ 5) ∧
      ((fun n : ℕ => (q n : ℝ)) =o[atTop] fun n => (n : ℝ) ^ 2) := by
  refine ⟨headlineConstant, headlineConstant * (5 / Real.log 2) ^ 5,
    CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget, CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program, headlineConstant_pos, ?_, rfl, HEq.rfl, ?_, program_cost,
    fun n reply => historyRun_cost_le reply (CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program n) [],
    fun n hn => budget_le (by omega), fun n hn => budget_le_natural_log hn,
    budget_isLittleO_square⟩
  · exact mul_pos headlineConstant_pos
      (pow_pos (div_pos (by norm_num) (Real.log_pos (by norm_num))) 5)
  · intro n G hG s t hst
    have hc := program_exact n G hG s t hst
    exact ⟨hc.1.1, hc.1.2.1, hc.1.2.2, hc.2⟩

-- No distinct pair exists for n=0/1. The actual zero-size CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget is zero;
-- no new zero-query promise is imposed on the unchanged singleton CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program.
theorem small_size_conventions :
    CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget 0 = 0 ∧ (∀ read : Finset (Fin 0) → ℝ, (CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program 0).cost read = 0) ∧
    (∀ n : ℕ, n ≤ 1 → ∀ G : WeightedGraph (Fin n), allPairsGood G ((CutQueryComplexity.DeterministicAPMCExpansion.Pruning.program n).eval G.cut)) := by
  have hz : CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget 0 = 0 := by
    simp only [CutQueryComplexity.DeterministicAPMCExpansion.Pruning.budget, CutQueryComplexity.DeterministicAPMCExpansion.Pruning.coreBudget, Decomposition.queryBudget, Decomposition.nodeUnitBudget,
      partitionRecoveryBudget_eq, edgeCap, padded_card, Fintype.card_fin,
      Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
  refine ⟨hz, ?_, ?_⟩
  · intro read
    exact Nat.eq_zero_of_le_zero ((program_cost 0 read).trans_eq hz)
  · intro n hn G s t hst
    have he : s = t := Fin.ext (by omega)
    exact (hst he).elim

end APMCLiteral6




end

end APMCContracts5


/- Actual execution contract: randomized. -/
section RandomizedContracts5

/-! Evidence-only contracts for the actual supplied-vector outer-pivot step.
Pivot averaging is semantic; no source-value or frontier solver is constructed. -/

set_option autoImplicit false

namespace CutQueryComplexity.GHOuterPivotContracts
noncomputable section
open scoped Classical BigOperators ENNReal
open GHReduction GHReduction.OuterPivot WeightedGraph Probability

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Arbitrary public cut tables are guarded before they can become children. -/
theorem guarded_batch (U R : Finset V) (s : V) (values : V → Option ℝ)
    (cuts : R → Finset V × ℝ) :
    WellFormed U s values (prepareBatch U R s values cuts) ∧
      s ∉ (prepareBatch U R s values cuts).covered U ∧
      ((prepareBatch U R s values cuts).accepted : Set V).PairwiseDisjoint
        (prepareBatch U R s values cuts).shore := by
  have h := prepareBatch_wellFormed U R s values cuts
  exact ⟨h, h.source_not_covered, h.disjoint⟩

theorem malformed_table_empty (U R : Finset V) (s : V) (values : V → Option ℝ)
    (cuts : R → Finset V × ℝ) (hd : ¬DisjointCuts cuts) :
    prepareBatch U R s values cuts = Batch.empty := by
  simp only [prepareBatch, hd, ite_false]

/-- The actual deterministic step is not truncated under the public size premises. -/
theorem step_exact_run {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (seed : ThresholdSeed V levels) (read : Finset V → ℝ) :
    DTree.run read (stepTree family n U s values levels seed) =
      (some (Prog.eval read (stepProgram family U s values levels seed)),
       Prog.cost read (stepProgram family U s values levels seed)) :=
  Prog.toDTree_run read _ _ (stepProgram_cost family hvn hQ U s values levels seed read)

/-- The fresh public seed preserves the full executed output-and-count law. -/
theorem random_step_joint {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ) (read : Finset V → ℝ) :
    RTree.run read (randomStepTree family n U s values levels) =
      (thresholdSeedPMF V levels).map
        (fun seed => Prog.run read (stepProgram family U s values levels seed)) := by
  simp only [randomStepTree, RTree.run_mix, PMF.bind_map, Function.comp_def,
    RTree.run_ofDeterministic, DTree.run_map, step_exact_run family hvn hQ, Option.getD_some]
  rfl

/-- The tree is chosen before a graph and before any oracle response policy. -/
theorem public_step {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ) :
    ∃ P : RTree (Finset V) ℝ (Output V levels) (stepBudget Q n levels),
      P = randomStepTree family n U s values levels ∧
      (∀ answer history (out : Output V levels × ℕ),
        out ∈ (TranscriptOracle.run answer P history).support → out.2 ≤ stepBudget Q n levels) ∧
      (∀ read history, TranscriptOracle.run (fun _ S => PMF.pure (read S)) P history =
        RTree.run read P) := by
  refine ⟨randomStepTree family n U s values levels, rfl, ?_, ?_⟩
  · intro answer history out hout
    exact TranscriptOracle.cost_le _ _ _ hout
  · exact TranscriptOracle.run_fixed _

/-- The selected batch is from the actual seed and maximizes executed level coverage. -/
theorem supported_public_geometry {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ) (read : Finset V → ℝ)
    {output : Output V levels}
    (hout : output ∈ ((randomStepTree family n U s values levels).eval read).support) :
    WellFormed U s values output.batch ∧
      ∃ seed ∈ (thresholdSeedPMF V levels).support,
        output = Prog.eval read (stepProgram family U s values levels seed) ∧
        ∀ i : Fin (levels + 1),
          ((Prog.eval read (levelProgram family U (levelSample U s i.val seed) s values)).covered U).card ≤
            (output.batch.covered U).card := by
  rw [randomStepTree_eval family hvn hQ] at hout
  obtain ⟨seed, hseed, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact ⟨stepProgram_wellFormed family U s values levels seed read, seed, hseed, rfl,
    level_coverage_le_step family U s values levels seed read⟩

theorem honest_supported_shores {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (U : Finset V) (s : V) (values : V → Option ℝ) (levels : ℕ)
    (hvalues : ∀ v ∈ U.erase s, values v = some (stValue G v s))
    {output : Output V levels}
    (hout : output ∈ ((randomStepTree family n U s values levels).eval G.cut).support) :
    WellFormed U s values output.batch ∧ s ∉ output.batch.covered U ∧
      (output.batch.accepted : Set V).PairwiseDisjoint output.batch.shore ∧
      ∀ v ∈ output.batch.accepted,
        IsSTMinCut G v s (output.batch.shore v) ∧
        output.batch.value v = G.cut (output.batch.shore v) ∧
        2 * (output.batch.shore v ∩ U).card ≤ U.card := by
  obtain ⟨hform, hcorrect⟩ := randomStepTree_correct family hvn hQ G U s values levels hvalues hout
  exact ⟨hform, hform.source_not_covered, hform.disjoint,
    fun v hv => ⟨(hcorrect v hv).1, (hcorrect v hv).2, hform.small v hv⟩⟩

/-- A canonical hit contributes its whole terminal trace to selected coverage. -/
theorem canonical_hit_coverage {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s v : V)
    (values : V → Option ℝ) (levels : ℕ) (seed : ThresholdSeed V levels)
    (i : Fin (levels + 1)) (C : Finset V) (hsU : s ∈ U) (hvU : v ∈ U)
    (hC : IsCanonicalSTCut G v s C) (hvalue : values v = some (stValue G v s))
    (hsize : 2 * (C ∩ U).card ≤ U.card) (hhit : UniqueSurvivor (C ∩ U) v i.val seed) :
    (C ∩ U).card ≤
      ((Prog.eval G.cut (stepProgram family U s values levels seed)).batch.covered U).card := by
  have htrace : C ∩ levelSample U s i.val seed = {v} := by
    rw [Finset.inter_comm]
    exact uniqueSurvivor_trace U C s seed (Finset.mem_inter.mpr ⟨hC.1.1, hvU⟩) hC.1.2.1 hhit
  exact (Finset.card_le_card (levelProgram_hit family G hG values
    (source_mem_levelSample hsU i.val seed) hvU hC htrace hvalue hsize)).trans
      (level_coverage_le_step family U s values levels seed G.cut i)

/-- Expected removal is attached to the actual capped program and one supplied vector. -/
theorem actual_expected_removal {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (U : Finset V) (s : V)
    (values : V → Option ℝ) (levels : ℕ) (hlevels : thresholdLevels U.card ≤ levels)
    (hsU : s ∈ U) (hvalues : ∀ v ∈ U.erase s, values v = some (stValue G v s)) :
    ((balancedTargets G U s).card : ℝ≥0∞) ≤ (8 * (levels + 1) : ℕ) *
      expect ((randomStepTree family n U s values levels).eval G.cut)
        (fun output => ((output.batch.covered U).card : ℝ≥0∞)) :=
  randomStepTree_expected_progress family hvn hQ G hG U s values levels hlevels hsU hvalues

/-- This equality is semantic pivot averaging; it does not compute source vectors. -/
theorem pivot_law_of_executed_steps {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (read : Finset V → ℝ) :
    pivotOutputLaw family U hU values levels read =
      (PMF.uniformOfFinset U hU).bind
        (fun s => (randomStepTree family n U s (values s) levels).eval read) := by
  simp_rw [randomStepTree_eval family hvn hQ]
  rfl

theorem actual_remaining_support {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (read : Finset V → ℝ) {R : Finset V}
    (hR : R ∈ (remainingLaw family U hU values levels read).support) : R ⊆ U ∧ R.Nonempty := by
  rw [remainingLaw] at hR
  obtain ⟨output, hout, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hR
  obtain ⟨s, hs, hform⟩ := pivotOutputLaw_wellFormed family U hU values levels read hout
  exact ⟨remaining_subset U output, s, source_mem_remaining hs hform⟩

/-- The original graph, level and branch-value premises yield real removal and drift. -/
theorem actual_large_child_bounds {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (U : Finset V) (hU : U.Nonempty) (values : V → V → Option ℝ) (levels : ℕ)
    (hlevels : thresholdLevels U.card ≤ levels)
    (hvalues : ∀ s ∈ U, ∀ v ∈ U.erase s, values s v = some (stValue G v s)) :
    (excess U : ℝ) / (32 * (levels + 1 : ℝ) ^ 2) ≤
      (expect (pivotOutputLaw family U hU values levels G.cut)
        (fun output => ((output.batch.covered U).card : ℝ≥0∞))).toReal ∧
    expect (remainingLaw family U hU values levels G.cut) (fun R => (excess R : ℝ≥0∞)) ≤
      contractionRate levels * (excess U : ℝ≥0∞) :=
  ⟨pivot_expected_removal_real family G hG U hU values levels hlevels hvalues,
    remainingLaw_expected_excess family G hG U hU values levels hlevels hvalues⟩

/-- A literal self-loop still goes from fuel+1 to fuel. -/
theorem self_loop_fuel {X : Type} (fuel : ℕ) (x : X) :
    fuelChain (fun y => PMF.pure y) (fuel + 1) x = fuelChain (fun y => PMF.pure y) fuel x :=
  fuelChain_self_loop_consumes _ _ _ rfl

/-- Conditional invariance and drift remain explicit for a future recursion. -/
theorem conditional_depth_tails {X : Type} (next : X → PMF X) (Inv : X → Prop)
    (potential : X → ℕ) (levels : ℕ)
    (hpreserve : ∀ x, Inv x → ∀ y ∈ (next x).support, Inv y)
    (hstep : ∀ x, Inv x → expect (next x) (fun y => (potential y : ℝ≥0∞)) ≤
      contractionRate levels * (potential x : ℝ≥0∞))
    (fuel : ℕ) (x : X) (hx : Inv x) :
    mass (fuelChain next fuel x) (fun y => 0 < potential y) ≤
      contractionRate levels ^ fuel * (potential x : ℝ≥0∞) ∧
    mass (fuelChain next fuel x) (fun y => 0 < potential y) ≤
      ENNReal.ofReal (Real.exp (-(fuel : ℝ) / (removalDenominator levels : ℝ))) *
        (potential x : ℝ≥0∞) ∧
    ∀ failure : ℝ, 0 < failure →
      mass (fuelChain next (depthFuel levels (potential x) failure) x)
        (fun y => 0 < potential y) ≤ ENNReal.ofReal failure :=
  ⟨fuelChain_depth_tail next Inv potential (contractionRate levels) hpreserve hstep fuel x hx,
    fuelChain_exp_depth_tail next Inv potential levels hpreserve hstep fuel x hx,
    fun _ hf => fuelChain_depthFuel_tail next Inv potential levels hpreserve hstep hf x hx⟩

end
end CutQueryComplexity.GHOuterPivotContracts

end RandomizedContracts5

#audit_cut_decl SteinerEndpointContract211.terminal_equivalence
#audit_cut_decl SteinerEndpointContract211.completed_geometry
#audit_cut_decl SteinerEndpointContract211.public_zero_query_decoding
#audit_cut_decl SteinerEndpointContract211.arbitrary_reply_run
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.check_public_log_five
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.check_public_natural_log_five
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.check_exists_public
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.check_exact_native_charges
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.check_log_comparison
#audit_cut_decl CutQueryComplexity.StarContraction2022.Quantum.Global.check_explicit_natural_coefficient
#audit_cut_decl GH211Contract.truncateRunLaw
#audit_cut_decl GH211Contract.badLengthRunLaw
#audit_cut_decl GH211Contract.validLengthRunLaw
#audit_cut_decl GH211Contract.sampledRunLaw
#audit_cut_decl GH211Contract.singleSourceRunLaw
#audit_cut_decl GH211Contract.zeroValueLaw
#audit_cut_decl GH211Contract.honestCostBound
#audit_cut_decl GH211Contract.honestJointLaw
#audit_cut_decl GH211Contract.honestOutputLaw
#audit_cut_decl GH211Contract.publicSingleSource
#audit_cut_decl GHAssemblyContracts.literal_lift_constructor
#audit_cut_decl GHAssemblyContracts.literal_assembly_constructor
#audit_cut_decl GHAssemblyContracts.actual_joined_geometry
#audit_cut_decl GHAssemblyContracts.derived_bridge_minimum
#audit_cut_decl GHAssemblyContracts.literal_join_constructor
#audit_cut_decl GHAssemblyContracts.literal_steiner_answer_run
#audit_cut_decl GHAssemblyContracts.actual_steiner_answer_correct
#audit_cut_decl GHAssemblyContracts.literal_steiner_decoder
#audit_cut_decl GHAssemblyContracts.queriedJoin_run
#audit_cut_decl GHAssemblyContracts.queriedJoin_correct
#audit_cut_decl GHAssemblyContracts.literal_queried_join_decoder
#audit_cut_decl APMCLiteral6.historyRun_cost_le
#audit_cut_decl APMCLiteral6.historyRun_of_read
#audit_cut_decl APMCLiteral6.padded_substitute_run
#audit_cut_decl APMCLiteral6.unpadProgram_run
#audit_cut_decl APMCLiteral6.padding_exact_count
#audit_cut_decl APMCLiteral6.actual_padded_pipeline
#audit_cut_decl APMCLiteral6.budget_le_natural_log
#audit_cut_decl APMCLiteral6.literal_deterministic_allPairs
#audit_cut_decl APMCLiteral6.small_size_conventions
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.guarded_batch
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.malformed_table_empty
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.step_exact_run
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.random_step_joint
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.public_step
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.supported_public_geometry
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.honest_supported_shores
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.canonical_hit_coverage
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.actual_expected_removal
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.pivot_law_of_executed_steps
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.actual_remaining_support
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.actual_large_child_bounds
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.self_loop_fuel
#audit_cut_decl CutQueryComplexity.GHOuterPivotContracts.conditional_depth_tails


/- Actual execution contract: quantum-neighbors. -/
section QuantumNeighborsContracts5

/-! Literal contracts for supplied finite public trees, shores and values.
Disjoint-star success is derived from its original premises. These contracts
do not produce the child certificates or implement outer GH recursion. -/

set_option autoImplicit false

namespace GHStarContracts
open CutQueryComplexity CutQueryComplexity.GHReduction CutQueryComplexity.WeightedGraph
open scoped Classical
noncomputable section

variable {V U : Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem literal_pack (T : SteinerCutTree V U) :
    ∃ P : DTree (Finset V) ℝ (PackedSteinerTree V) 0,
      P = DTree.pure (packSteinerTree T) ∧
      (∀ read, P.run read = (packSteinerTree T, 0)) ∧
      (packSteinerTree T).size = Fintype.card U ∧
      (∀ x, Represents (packSteinerTree T) x ↔ ∃ u, T.terminal u = x) ∧
      (∀ G : WeightedGraph V, IsSteinerCutTree G T → IsSteinerCutTree G (P.eval G.cut).value) := by
  exact ⟨DTree.pure (packSteinerTree T), rfl, fun _ => rfl, rfl,
    packSteinerTree_represents T, fun G hT => packSteinerTree_correct G T hT⟩

theorem literal_fold_run (base : PackedSteinerTree V) (steps : List (SteinerAssemblyStep V))
    (read : Finset V → ℝ) :
    Prog.run read (assembleSteinerProgram base steps) = (assembleSteinerSteps base steps, 0) := rfl

theorem literal_finish_run (base : PackedSteinerTree V) (steps : List (SteinerAssemblyStep V))
    (read : Finset V → ℝ) :
    Prog.run read (finishSteinerProgram base steps) = (finishSteinerAssembly base steps, 0) := rfl

/-- An actual successful fold preserves the base attachment relation outside
all appended child shores. This lemma assumes no graph correctness. -/
theorem star_attach_outside (r : V) (child : V → PackedSteinerTree V)
    (S : V → Finset V) (value : V → ℝ) (L : List V) :
    ∀ base out : PackedSteinerTree V,
      assembleDisjointStar base r child S value L = some out →
      ∀ x y : V, (∀ i ∈ L, x ∉ S i) → (∀ i ∈ L, y ∉ S i) →
      base.value.attach x = base.value.attach y → out.value.attach x = out.value.attach y := by
  induction L with
  | nil =>
      intro base out hout x y _ _ heq
      have h : base = out := by simpa [assembleDisjointStar, starAssemblySteps,
        assembleSteinerSteps] using hout
      exact h ▸ heq
  | cons i L ih =>
      intro base out hout x y hx hy heq
      cases hj : checkedSteinerJoin base (child i) (S i)ᶜ r i (value i) with
      | none =>
          simp [assembleDisjointStar, starAssemblySteps, assembleSteinerSteps, hj] at hout
      | some middle =>
          have hrest : assembleDisjointStar middle r child S value L = some out := by
            simpa [assembleDisjointStar, starAssemblySteps, assembleSteinerSteps, hj] using hout
          have hmiddle := checkedSteinerJoin_attach_left base (child i) (S i)ᶜ r i (value i) hj
            (Finset.mem_compl.mpr (hx i List.mem_cons_self))
            (Finset.mem_compl.mpr (hy i List.mem_cons_self)) heq
          exact ih middle out hrest x y
            (fun j hj => hx j (List.mem_cons_of_mem _ hj))
            (fun j hj => hy j (List.mem_cons_of_mem _ hj)) hmiddle

/-- Inside one child shore, disjointness ensures subsequent joins preserve
that child's actual attachment relation. -/
theorem star_attach_child (r : V) (child : V → PackedSteinerTree V)
    (S : V → Finset V) (value : V → ℝ) (L : List V) :
    L.Pairwise (fun i j => Disjoint (S i) (S j)) →
    ∀ base out : PackedSteinerTree V,
      assembleDisjointStar base r child S value L = some out →
      ∀ i ∈ L, ∀ x ∈ S i, ∀ y ∈ S i,
      (child i).value.attach x = (child i).value.attach y →
      out.value.attach x = out.value.attach y := by
  induction L with
  | nil => simp
  | cons j L ih =>
      intro hdisj base out hout i hi x hx y hy heq
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdisj
      cases hj : checkedSteinerJoin base (child j) (S j)ᶜ r j (value j) with
      | none =>
          simp [assembleDisjointStar, starAssemblySteps, assembleSteinerSteps, hj] at hout
      | some middle =>
          have hrest : assembleDisjointStar middle r child S value L = some out := by
            simpa [assembleDisjointStar, starAssemblySteps, assembleSteinerSteps, hj] using hout
          rcases List.mem_cons.mp hi with hij | hi
          · subst i
            have hmiddle := checkedSteinerJoin_attach_right base (child j) (S j)ᶜ r j (value j) hj
              (by simpa using hx) (by simpa using hy) heq
            exact star_attach_outside r child S value L middle out hrest x y
              (fun k hk h => Finset.disjoint_left.mp (hhead k hk) hx h)
              (fun k hk h => Finset.disjoint_left.mp (hhead k hk) hy h) hmiddle
          · exact ih htail middle out hrest i hi x hx y hy heq

/-- The public constructor is fixed before the graph. A `some` result, its
full certificate, exact coverage and attachment laws follow from the original
star premises, rather than a supplied successful-fold hypothesis. -/
theorem literal_star_constructor (base : PackedSteinerTree V) (r : V)
    (child : V → PackedSteinerTree V) (S : V → Finset V) (value : V → ℝ) (L : List V) :
    ∃ P : Prog (Finset V) ℝ (Option (PackedSteinerTree V)),
      P = assembleSteinerProgram base (starAssemblySteps r child S value L) ∧
      (∀ read, Prog.run read P = (assembleDisjointStar base r child S value L, 0)) ∧
      (∀ G : WeightedGraph V,
        IsSteinerCutTree G base.value → Represents base r →
        L.Pairwise (fun i j => Disjoint (S i) (S j)) →
        (∀ i ∈ L, Represents (child i) i) →
        (∀ i ∈ L, ∀ u, (child i).value.terminal u ∈ S i) →
        (∀ i ∈ L, ∀ x, x ∉ S i → (child i).value.attach x = (child i).value.attach r) →
        (∀ i ∈ L, IsSteinerCutTree G (child i).value) →
        (∀ i ∈ L, IsSTMinCut G i r (S i)) →
        (∀ i ∈ L, value i = G.cut (S i)) →
        (∀ i ∈ L, ∀ u, base.value.terminal u ∉ S i) →
        (∀ i ∈ L, ∀ x ∈ S i, ∀ y ∈ S i, base.value.attach x = base.value.attach y) →
        ∃ out, Prog.eval G.cut P = some out ∧ IsSteinerCutTree G out.value ∧ Represents out r ∧
          (∀ x, Represents out x ↔ Represents base x ∨ ∃ i ∈ L, Represents (child i) x) ∧
          (∀ x y, (∀ i ∈ L, x ∉ S i) → (∀ i ∈ L, y ∉ S i) →
            base.value.attach x = base.value.attach y → out.value.attach x = out.value.attach y) ∧
          (∀ i ∈ L, ∀ x ∈ S i, ∀ y ∈ S i,
            (child i).value.attach x = (child i).value.attach y →
            out.value.attach x = out.value.attach y)) := by
  refine ⟨assembleSteinerProgram base (starAssemblySteps r child S value L), rfl,
    fun _ => rfl, ?_⟩
  intro G hbase hr hdisj hrep hin hout hcorrect hcut hvalue havoid hconstant
  obtain ⟨out, hfold, htree, hroot, hcoverage⟩ := assembleDisjointStar_success G r child S value L
    base hbase hr hdisj hrep hin hout hcorrect hcut hvalue havoid hconstant
  exact ⟨out, hfold, htree, hroot, hcoverage,
    star_attach_outside r child S value L base out hfold,
    star_attach_child r child S value L hdisj base out hfold⟩

theorem finish_of_covered_fold (base : PackedSteinerTree V) (steps : List (SteinerAssemblyStep V))
    (out : PackedSteinerTree V) (hfold : assembleSteinerSteps base steps = some out)
    (hcover : Function.Surjective out.value.terminal) :
    finishSteinerAssembly base steps = some (completeSteinerTree out.value hcover) := by
  simp only [finishSteinerAssembly, hfold, Option.bind_some, hcover, dite_true]

/-- The actual public finishing program followed by public cut-tree decoding.
All supplied bridge values are data, so this program makes zero oracle calls. -/
def starDecoderProgram (base : PackedSteinerTree V) (r : V)
    (child : V → PackedSteinerTree V) (S : V → Finset V) (value : V → ℝ) (L : List V)
    (s t : V) : Prog (Finset V) ℝ (Option (Finset V × ℝ)) :=
  (finishSteinerProgram base (starAssemblySteps r child S value L)).map
    (fun out => out.map (fun tree => cutTreeAnswer tree s t))

/-- Compile that zero-query program with budget zero; flatten only the outer
compiler option. Exact execution proves this never incurs truncation. -/
def starDecoderTree (base : PackedSteinerTree V) (r : V)
    (child : V → PackedSteinerTree V) (S : V → Finset V) (value : V → ℝ) (L : List V)
    (s t : V) : DTree (Finset V) ℝ (Option (Finset V × ℝ)) 0 :=
  ((starDecoderProgram base r child S value L s t).toDTree 0).map Option.join

theorem literal_star_decoder_run (base : PackedSteinerTree V) (r : V)
    (child : V → PackedSteinerTree V) (S : V → Finset V) (value : V → ℝ) (L : List V)
    (s t : V) (read : Finset V → ℝ) :
    Prog.run read (starDecoderProgram base r child S value L s t) =
      ((finishSteinerAssembly base (starAssemblySteps r child S value L)).map
        (fun tree => cutTreeAnswer tree s t), 0) ∧
    (starDecoderTree base r child S value L s t).run read =
      ((finishSteinerAssembly base (starAssemblySteps r child S value L)).map
        (fun tree => cutTreeAnswer tree s t), 0) := ⟨rfl, rfl⟩

/-- Full vertex coverage is stated on the supplied base/child terminal sets.
The successful fold and the finishing guard are both derived, before decoding
the actual completed tree for any distinct original vertices. -/
theorem literal_completed_star_decoder (base : PackedSteinerTree V) (r : V)
    (child : V → PackedSteinerTree V) (S : V → Finset V) (value : V → ℝ) (L : List V)
    (hcoverInput : ∀ x, Represents base x ∨ ∃ i ∈ L, Represents (child i) x) :
    ∃ P : V → V → DTree (Finset V) ℝ (Option (Finset V × ℝ)) 0,
      P = starDecoderTree base r child S value L ∧
      (∀ s t read, (P s t).run read =
        ((finishSteinerAssembly base (starAssemblySteps r child S value L)).map
          (fun tree => cutTreeAnswer tree s t), 0)) ∧
      (∀ G : WeightedGraph V,
        IsSteinerCutTree G base.value → Represents base r →
        L.Pairwise (fun i j => Disjoint (S i) (S j)) →
        (∀ i ∈ L, Represents (child i) i) →
        (∀ i ∈ L, ∀ u, (child i).value.terminal u ∈ S i) →
        (∀ i ∈ L, ∀ x, x ∉ S i → (child i).value.attach x = (child i).value.attach r) →
        (∀ i ∈ L, IsSteinerCutTree G (child i).value) →
        (∀ i ∈ L, IsSTMinCut G i r (S i)) →
        (∀ i ∈ L, value i = G.cut (S i)) →
        (∀ i ∈ L, ∀ u, base.value.terminal u ∉ S i) →
        (∀ i ∈ L, ∀ x ∈ S i, ∀ y ∈ S i, base.value.attach x = base.value.attach y) →
        ∀ s t, s ≠ t → ∃ answer, (P s t).eval G.cut = some answer ∧
          IsSTMinCut G s t answer.1 ∧ G.cut answer.1 = answer.2) := by
  refine ⟨starDecoderTree base r child S value L, rfl,
    fun s t read => (literal_star_decoder_run base r child S value L s t read).2, ?_⟩
  intro G hbase hr hdisj hrep hin hout hcorrect hcut hvalue havoid hconstant s t hst
  obtain ⟨out, hfold, htree, _, hcoverage⟩ := assembleDisjointStar_success G r child S value L
    base hbase hr hdisj hrep hin hout hcorrect hcut hvalue havoid hconstant
  have hcover : Function.Surjective out.value.terminal :=
    fun x => (hcoverage x).mpr (hcoverInput x)
  have hfinish := finish_of_covered_fold base (starAssemblySteps r child S value L) out hfold hcover
  refine ⟨cutTreeAnswer (completeSteinerTree out.value hcover) s t, ?_, ?_⟩
  · change (finishSteinerAssembly base (starAssemblySteps r child S value L)).map
      (fun tree => cutTreeAnswer tree s t) = _
    rw [hfinish]
    rfl
  · exact cutTreeAnswer_correct G _ (completeSteinerTree_correct G out.value hcover htree) hst

end
end GHStarContracts


end QuantumNeighborsContracts5


/- Actual execution contract: gh. -/
section GHContracts6

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction
open CutQueryComplexity.Probability CutQueryComplexity.WeightedGraph
open scoped Classical ENNReal BigOperators

namespace GH212Contract
noncomputable section

-- Exact output/count coupling for the actual truncation constructor.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem truncateRunLaw {I A O : Type} {q : ℕ} (T : RTree I A O q)
    (k : ℕ) (read : I → A) :
    RTree.run read (T.truncate k) = (RTree.run read T).map
      (fun p => (if p.2 ≤ k then some p.1 else none, min p.2 k)) := by
  induction q generalizing k with
  | zero =>
    simp [RTree.truncate, RTree.run_pure, RTree.run, PMF.map_comp, Function.comp_def]
  | succ q ih =>
    cases k with
    | zero =>
      simp only [RTree.truncate, RTree.run, PMF.map_comp, PMF.map_bind, Function.comp_def]
      rw [PMF.map]
      congr 1
      funext action
      rcases action with o | ⟨i, next⟩
      · simp [PMF.pure_map]
      · simp only [PMF.map_comp, Function.comp_def, Nat.not_succ_le_zero,
          ite_false, Nat.min_zero]
        exact (PMF.map_const (RTree.run read (next (read i))) (none, 0)).symm
    | succ k =>
      simp only [RTree.truncate, RTree.run, PMF.bind_map, PMF.map_bind, Function.comp_def]
      congr 1
      funext action
      rcases action with o | ⟨i, next⟩
      · simp [PMF.pure_map]
      · dsimp only
        rw [ih]
        simp only [PMF.map_comp, Function.comp_def, Nat.add_le_add_iff_right]
        apply congrArg (fun f => (RTree.run read (next (read i))).map f)
        funext p
        apply Prod.ext
        · rfl
        · omega


-- The dependent table runs its literal list order and adds the realized counts.
theorem dependentTableRunStep {I A J : Type} {O : J → Type} {q : ℕ} [DecidableEq J]
    (fallback : (j : J) → O j) (f : (j : J) → RTree I A (O j) q)
    (j : J) (L : List J) (read : I → A) :
    RTree.run read (dependentRandomTableAux fallback f (j :: L)) =
      (RTree.run read (f j)).bind (fun first =>
        (RTree.run read (dependentRandomTableAux fallback f L)).map (fun tail =>
          (Function.update tail.1 j first.1, first.2 + tail.2))) := by
  simp only [dependentRandomTableAux, RTree.run_cast, RTree.run_bind,
    random_run_map, PMF.map_comp, Function.comp_def]

variable {V : Type} [Fintype V] [DecidableEq V] {M n : ℕ} {Q : ℕ → ℕ}

-- The fresh isolating continuation receives the actual returned values.
theorem sourcePivotForRunLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (U : Finset V) (s : V) (hvn : Fintype.card V ≤ n) (read : Finset V → ℝ) :
    RTree.run read (sourcePivotFor family n samples trials guideLevels scale exponent levels K U s hvn) =
      (RTree.run read (singleSourceTree family n samples trials guideLevels scale exponent K U s hvn)).bind
        (fun first => (RTree.run read (OuterPivot.randomStepTree family n U s first.1 levels)).map
          (fun step => (SourcePivotOutput.mk s first.1 step.1, first.2 + step.2))) := by
  unfold sourcePivotFor sourcePivotBudget
  simp only [RTree.run_bind, random_run_map, PMF.map_comp, Function.comp_def]

theorem sourcePivotTreeRunLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (U : Finset V) (hU : U.Nonempty) (hvn : Fintype.card V ≤ n) (read : Finset V → ℝ) :
    RTree.run read (sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn) =
      (PMF.uniformOfFinset U hU).bind (fun s =>
        (RTree.run read (singleSourceTree family n samples trials guideLevels scale exponent K U s hvn)).bind
          (fun first => (RTree.run read (OuterPivot.randomStepTree family n U s first.1 levels)).map
            (fun step => (SourcePivotOutput.mk s first.1 step.1, first.2 + step.2)))) := by
  simp only [sourcePivotTree, RTree.run_mix, PMF.bind_map, Function.comp_def, sourcePivotForRunLaw]

-- P is selected from public data before the hidden graph and semantic premises.
theorem publicSourcePivot (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (U : Finset V) (hU : U.Nonempty) (hvn : Fintype.card V ≤ n) :
    ∃ P : RTree (Finset V) ℝ (SourcePivotOutput V levels)
        (sourcePivotBudget M Q n samples trials guideLevels scale exponent levels),
      P = sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn ∧
      (∀ answer : TranscriptOracle.AnswerPolicy (Finset V) ℝ, ∀ history p,
        p ∈ (TranscriptOracle.run answer P history).support →
          p.2 ≤ sourcePivotBudget M Q n samples trials guideLevels scale exponent levels) ∧
      (∀ read : Finset V → ℝ, RTree.run read P =
        (PMF.uniformOfFinset U hU).bind (fun s =>
          (RTree.run read (singleSourceTree family n samples trials guideLevels scale exponent K U s hvn)).bind
            (fun first => (RTree.run read (OuterPivot.randomStepTree family n U s first.1 levels)).map
              (fun step => (SourcePivotOutput.mk s first.1 step.1, first.2 + step.2))))) ∧
      (SizeRegular n Q → ∀ G : WeightedGraph V, InputPromise M G →
        ∀ p ∈ (RTree.run G.cut P).support, n * p.2 ≤ Fintype.card V *
          sourcePivotSharpBudget M Q n samples trials guideLevels scale exponent levels) ∧
      (SizeRegular n Q → n ≤ scale → thresholdLevels n ≤ guideLevels →
        ∀ G : WeightedGraph V, InputPromise M G →
          (∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
            K.cut S ≤ (101 / 100 : ℝ) * G.cut S) →
          mass (P.eval G.cut) (fun out => ¬SourcePivotGood G U out) ≤
            singleSourceError M n samples trials scale exponent) := by
  refine ⟨sourcePivotTree family n samples trials guideLevels scale exponent levels K U hU hvn,
    rfl, ?_, ?_, ?_, ?_⟩
  · exact fun answer history p hp => TranscriptOracle.cost_le _ answer history hp
  · exact sourcePivotTreeRunLaw family samples trials guideLevels scale exponent levels K U hU hvn
  · exact fun hQ G hG p hp => sourcePivotTree_cost_scaled family hQ samples trials guideLevels scale exponent
      levels G K hG U hU hvn hp
  · exact fun hQ hnscale hlevels G hG happrox => sourcePivotTree_failure_le family hQ hnscale samples
      trials guideLevels exponent levels hlevels G K hG U hU hvn happrox

variable {B : Type} [Fintype B] [DecidableEq B]

theorem frontierActiveRunLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (b : B)
    (hvn : Fintype.card V ≤ n) (hactive : 2 ≤ (fiber p b).card) (read : Finset V → ℝ) :
    RTree.run read (frontierPivotCall family n samples trials guideLevels scale exponent levels K p hp T b hvn) =
      (RTree.run (read ∘ pull (frontierMap p T b))
        (sourcePivotTree family n samples trials guideLevels scale exponent levels
          (K.contract (frontierMap p T b)) (frontierTerminals p T b)
          (frontierTerminals_nonempty p hp T b) ((frontierVertex_card_le p hp T b).trans hvn))).map
            (fun call => (some call.1, call.2)) := by
  simp only [frontierPivotCall, hactive, ite_true, random_run_map, contractProgram_run]

theorem frontierInactiveRunLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (b : B)
    (hvn : Fintype.card V ≤ n) (hinactive : ¬2 ≤ (fiber p b).card) (read : Finset V → ℝ) :
    RTree.run read (frontierPivotCall family n samples trials guideLevels scale exponent levels K p hp T b hvn) =
      PMF.pure (none, 0) := by
  simp only [frontierPivotCall, hinactive, ite_false, RTree.run_pure, PMF.pure_map]

theorem frontierTableRunLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (hvn : Fintype.card V ≤ n) (read : Finset V → ℝ) :
    RTree.run read (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn) =
      RTree.run read (dependentRandomTableAux (fun _ => none)
        (fun b => frontierPivotCall family n samples trials guideLevels scale exponent levels K p hp T b hvn)
        (Finset.univ : Finset B).toList) := by
  simp only [frontierPivotRound, dependentRandomTable, RTree.run_cast]

-- The cost theorem covers every honest outcome, including incorrect estimates.
theorem frontierHonestJointLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (hn : 0 < n) (G : WeightedGraph V) (hG : InputPromise M G) :
    RTree.run G.cut (frontierPivotRoundCapped family n samples trials guideLevels scale exponent levels K p hp T hvn) =
      (RTree.run G.cut (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn)).map
        (fun out => (some out.1, out.2)) := by
  rw [frontierPivotRoundCapped, truncateRunLaw]
  apply PMF.ext
  intro output
  simp only [PMF.map_apply]
  apply tsum_congr
  intro out
  by_cases hout : out ∈ (RTree.run G.cut
      (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn)).support
  · have hcost := frontierPivotRound_cost family hQ hn samples trials guideLevels scale exponent levels
      G K hG p hp T hvn hout
    rw [ite_eq_left hcost, Nat.min_eq_left hcost]
  · have hz : RTree.run G.cut
        (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn) out = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hout
    simp only [hz, ite_self]

theorem frontierStateStepRunLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (state : PublicFrontierState V) (read : Finset V → ℝ) :
    RTree.run read (frontierStateStep family n samples trials guideLevels scale exponent levels K hvn state) =
      (RTree.run read (frontierPivotRoundCapped family n samples trials guideLevels scale exponent levels
        K state.block state.onto state.tree hvn)).map
          (fun out => (FrontierRoundRecord.mk state out.1, out.2)) := by
  unfold frontierStateStep frontierRoundBudget
  rw [random_run_map]

theorem frontierStateStepHonestJointLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (state : PublicFrontierState V)
    (hQ : SizeRegular n Q) (hn : 0 < n) (G : WeightedGraph V) (hG : InputPromise M G) :
    RTree.run G.cut (frontierStateStep family n samples trials guideLevels scale exponent levels K hvn state) =
      (RTree.run G.cut (frontierPivotRound family n samples trials guideLevels scale exponent levels
        K state.block state.onto state.tree hvn)).map
          (fun out => (FrontierRoundRecord.mk state (some out.1), out.2)) := by
  rw [frontierStateStepRunLaw,
    frontierHonestJointLaw family samples trials guideLevels scale exponent levels K
      state.block state.onto state.tree hvn hQ hn G hG]
  simp only [PMF.map_comp, Function.comp_def]

-- A joint semantic law with exactly the same dependent next-state recursion.
-- This is an evidence-only description of the implemented run, not a producer assumption.
def frontierExecutionLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (read : Finset V → ℝ) :
    ℕ → PublicFrontierState V → PMF (FrontierTrace V levels × ℕ)
  | 0, state => PMF.pure (⟨state, []⟩, 0)
  | fuel + 1, state =>
      (RTree.run read (frontierStateStep family n samples trials guideLevels scale exponent levels K hvn state)).bind
        (fun first => (frontierExecutionLaw family samples trials guideLevels scale exponent levels
          K hvn read fuel first.1.after).map (fun tail =>
            (⟨tail.1.endState, first.1 :: tail.1.records⟩, first.2 + tail.2)))

theorem frontierExecutionRunLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (fuel : ℕ) (state : PublicFrontierState V) (read : Finset V → ℝ) :
    RTree.run read (frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel state) =
      frontierExecutionLaw family samples trials guideLevels scale exponent levels K hvn read fuel state := by
  induction fuel generalizing state with
  | zero => simp only [frontierExecution, RTree.run_pure, PMF.pure_map, frontierExecutionLaw]
  | succ fuel ih =>
      simp only [frontierExecution, RTree.run_cast, RTree.run_bind, random_run_map,
        PMF.map_comp, Function.comp_def, ih, frontierExecutionLaw]

-- Public finite guards reject malformed data and preserve a nonempty partition.
theorem checkedFallbackLaw (U : Finset V) (r : U) (S : PublicBlockSplit V)
    (hinvalid : ¬ValidBlockSplit U S) : normalizeBlockSplit U r S = emptyBlockSplit r.val := by
  simp only [normalizeBlockSplit, hinvalid, ite_false]

theorem recordPartitionLaw {levels : ℕ} (record : FrontierRoundRecord V levels) :
    (∀ b, ValidBlockSplit (fiber record.before.block b) (record.split b)) ∧
      Function.Surjective record.after.block ∧
      (∑ b, Fintype.card (FrontierVertex record.after.block record.after.tree b)) =
        Fintype.card V + 2 * (record.after.size - 1) ∧
      (∑ b, Fintype.card (FrontierVertex record.after.block record.after.tree b)) ≤ 3 * Fintype.card V ∧
      ∀ b, Fintype.card (FrontierVertex record.after.block record.after.tree b) ≤ Fintype.card V :=
  ⟨record.split_valid, record.after.onto, record.after.frontier_sizes⟩

-- This gives good records under K's explicit approximation event, without a GH-tree claim.
theorem publicFrontierExecution (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (fuel : ℕ) (state : PublicFrontierState V) :
    ∃ P : RTree (Finset V) ℝ (FrontierTrace V levels)
        (fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels),
      P = frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel state ∧
      (∀ answer : TranscriptOracle.AnswerPolicy (Finset V) ℝ, ∀ history p,
        p ∈ (TranscriptOracle.run answer P history).support →
          p.2 ≤ fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels) ∧
      (∀ read : Finset V → ℝ, RTree.run read P =
        frontierExecutionLaw family samples trials guideLevels scale exponent levels K hvn read fuel state) ∧
      (∀ read : Finset V → ℝ, ∀ trace ∈ (P.eval read).support,
        trace.records.length = fuel ∧ FrontierTrace.Follows state trace.records trace.endState) ∧
      (SizeRegular n Q → 0 < n → ∀ G : WeightedGraph V, InputPromise M G →
        ∀ current : PublicFrontierState V,
          RTree.run G.cut (frontierStateStep family n samples trials guideLevels scale exponent levels K hvn current) =
            (RTree.run G.cut (frontierPivotRound family n samples trials guideLevels scale exponent levels
              K current.block current.onto current.tree hvn)).map
                (fun out => (FrontierRoundRecord.mk current (some out.1), out.2))) ∧
      (SizeRegular n Q → 0 < n → n ≤ scale → thresholdLevels n ≤ guideLevels →
        ∀ G : WeightedGraph V, InputPromise M G →
          (∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧
            K.cut S ≤ (101 / 100 : ℝ) * G.cut S) →
          mass (P.eval G.cut) (fun trace => ¬trace.Good G) ≤
            (fuel : ℝ≥0∞) * ((n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent)) := by
  refine ⟨frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel state,
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun answer history p hp => TranscriptOracle.cost_le _ answer history hp
  · exact frontierExecutionRunLaw family samples trials guideLevels scale exponent levels K hvn fuel state
  · exact fun read trace htrace => frontierExecution_support family samples trials guideLevels scale exponent
      levels K hvn fuel state read htrace
  · exact fun hQ hn G hG current => frontierStateStepHonestJointLaw family samples trials guideLevels scale exponent
      levels K hvn current hQ hn G hG
  · exact fun hQ hn hnscale hlevels G hG happrox => frontierExecution_failure_le family hQ hn hnscale
      samples trials guideLevels exponent levels hlevels G K hG hvn happrox fuel state

end
end GH212Contract




end GHContracts6


/- Actual execution contract: apmc. -/
section APMCContracts6

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction WeightedGraph
open scoped Classical
noncomputable section

namespace RoundCutContracts

variable {V B ι : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq ι]

/-- Explicit original vertices of one child plus every attached old branch. -/
def originalChildShore (p : V → B) (I : B → Finset ι) (S : B → ι → Finset V)
    (a : (b : B) → B → Option (I b)) (b : B) (i : I b) : Finset V :=
  Finset.univ.filter (fun v => (p v = b ∧ v ∈ S b i.val) ∨
    (p v ≠ b ∧ a b (p v) = some i))

theorem child_shore_pull (p : V → B) (I : B → Finset ι) (S : B → ι → Finset V)
    (a : (b : B) → B → Option (I b))
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (b : B) (i : I b) :
    pull (roundBlockMap p I S) (roundChildShore I a b i) =
      originalChildShore p I S a b i := by
  apply Finset.ext
  intro v
  constructor
  · intro hv
    have hm := (Finset.mem_filter.mp
      ((mem_pull (roundBlockMap p I S) (roundChildShore I a b i) v).mp hv)).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hm with hm | hm
    · exact Or.inl ((roundBlockMap_child_iff p I S hdisj v b i).mp hm)
    · exact Or.inr hm
  · intro hv
    apply (mem_pull (roundBlockMap p I S) (roundChildShore I a b i) v).mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases (Finset.mem_filter.mp hv).2 with hm | hm
    · exact Or.inl ((roundBlockMap_child_iff p I S hdisj v b i).mpr hm)
    · exact Or.inr hm

/-- Every parent edge is literally one retained old edge or one child star edge. -/
theorem actual_parent_edge (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) {v : RoundBlock I}
    (hv : v ≠ (roundBlockTree T I a).root) :
    (∃ e : B, e ≠ T.root ∧
      selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v = roundOldEdge T I a e) ∨
    (∃ (b : B) (i : I b),
      selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v = roundStarEdge I ⟨b, i⟩) := by
  have hm := selectedParentEdge_mem (roundBlockTree T I a) (roundEdges T I a)
    (roundBlockTree_parent_adj T I a hv)
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
    exact Or.inl ⟨e, (Finset.mem_erase.mp he).1, heq.symm⟩
  · obtain ⟨⟨b, i⟩, _, heq⟩ := Finset.mem_image.mp hm
    exact Or.inr ⟨b, i, heq.symm⟩

/-- Old rooted shores exclude the actual new root, fixing the orientation exactly. -/
theorem old_fundamental_exact (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b))
    (hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e))
    {v : RoundBlock I} (hv : v ≠ (roundBlockTree T I a).root)
    {e : B} (he : e ≠ T.root)
    (hselected : selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v =
      roundOldEdge T I a e) :
    (roundBlockTree T I a).D v = pull (roundBlockParent I) (T.D e) := by
  have hf := roundBlockTree_fundamental T I a hconstant hv
  rw [hselected, roundEdgeShore_old T I a he] at hf
  rcases hf with hf | hf
  · exact hf
  · have hroot : (roundBlockTree T I a).root ∉ pull (roundBlockParent I) (T.D e) := by
      intro hm
      exact T.root_not_mem_D he
        ((mem_pull (roundBlockParent I) (T.D e) (roundBlockTree T I a).root).mp hm)
    exact ((roundBlockTree T I a).root_not_mem_D hv
      (hf.symm ▸ Finset.mem_compl.mpr hroot)).elim

theorem child_root_membership (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b)) (b : B) (i : I b) :
    (roundBlockTree T I a).root ∈ roundChildShore I a b i ↔
      T.root ≠ b ∧ a b T.root = some i := by
  by_cases hr : T.root = b
  · subst b
    constructor
    · intro hm
      have hn := (mem_roundChildShore_same I a T.root i none).mp hm
      cases hn
    · rintro ⟨hne, _⟩
      exact (hne rfl).elim
  · exact ⟨fun hm => ⟨hr, (mem_roundChildShore_other I a b i hr none).mp hm⟩,
      fun hm => (mem_roundChildShore_other I a b i hr none).mpr hm.2⟩

/-- The attachment of the old root determines a child shore's exact orientation. -/
theorem star_fundamental_exact (T : RootedTree B) (I : B → Finset ι)
    (a : (b : B) → B → Option (I b))
    (hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e))
    {v : RoundBlock I} (hv : v ≠ (roundBlockTree T I a).root)
    (b : B) (i : I b)
    (hselected : selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v =
      roundStarEdge I ⟨b, i⟩) :
    (roundBlockTree T I a).D v =
      if T.root ≠ b ∧ a b T.root = some i then (roundChildShore I a b i)ᶜ
      else roundChildShore I a b i := by
  have hf := roundBlockTree_fundamental T I a hconstant hv
  rw [hselected, roundEdgeShore_star] at hf
  by_cases hr : T.root ≠ b ∧ a b T.root = some i
  · have hm := (child_root_membership T I a b i).mpr hr
    rcases hf with hf | hf
    · exact ((roundBlockTree T I a).root_not_mem_D hv (hf.symm ▸ hm)).elim
    · exact hf.trans (ite_eq_left hr).symm
  · have hm : (roundBlockTree T I a).root ∉ roundChildShore I a b i :=
      fun h => hr ((child_root_membership T I a b i).mp h)
    rcases hf with hf | hf
    · exact hf.trans (ite_eq_right hr).symm
    · exact ((roundBlockTree T I a).root_not_mem_D hv
        (hf.symm ▸ Finset.mem_compl.mpr hm)).elim

theorem old_pull_exact (p : V → B) (T : RootedTree B) (I : B → Finset ι)
    (S : B → ι → Finset V) (a : (b : B) → B → Option (I b))
    (hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e))
    {v : RoundBlock I} (hv : v ≠ (roundBlockTree T I a).root)
    {e : B} (he : e ≠ T.root)
    (hselected : selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v =
      roundOldEdge T I a e) :
    pull (roundBlockMap p I S) ((roundBlockTree T I a).D v) = pull p (T.D e) :=
  (congrArg (pull (roundBlockMap p I S))
    (old_fundamental_exact T I a hconstant hv he hselected)).trans
      (roundBlock_old_shore_pull p I S (T.D e))

theorem star_pull_exact (p : V → B) (T : RootedTree B) (I : B → Finset ι)
    (S : B → ι → Finset V) (a : (b : B) → B → Option (I b))
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e))
    {v : RoundBlock I} (hv : v ≠ (roundBlockTree T I a).root) (b : B) (i : I b)
    (hselected : selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v =
      roundStarEdge I ⟨b, i⟩) :
    pull (roundBlockMap p I S) ((roundBlockTree T I a).D v) =
      if T.root ≠ b ∧ a b T.root = some i then (originalChildShore p I S a b i)ᶜ
      else originalChildShore p I S a b i := by
  rw [star_fundamental_exact T I a hconstant hv b i hselected]
  split <;> simp only [pull_compl, child_shore_pull p I S a hdisj]

/-- The block labels are those of the constructed map, with every disjointness premise. -/
theorem quotient_labels (p : V → B) (I : B → Finset ι) (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j)) :
    (∀ v, roundBlockParent I (roundBlockMap p I S v) = p v) ∧
    (∀ v b, roundBlockMap p I S v = ⟨b, none⟩ ↔ p v = b ∧ ∀ i ∈ I b, v ∉ S b i) ∧
    (∀ v b (i : I b), roundBlockMap p I S v = ⟨b, some i⟩ ↔ p v = b ∧ v ∈ S b i.val) :=
  ⟨roundBlockParent_map p I S, roundBlockMap_residual_iff p I S,
    roundBlockMap_child_iff p I S hdisj⟩

/-- Public finite construction is fixed before any replies or hidden graph. -/
def publicRoundProgram (p : V → B) (T : RootedTree B) (I : B → Finset ι)
    (S : B → ι → Finset V) (a : (b : B) → B → Option (I b)) :
    DTree (Finset V) ℝ (RootedTree (RoundBlock I) × (V → RoundBlock I)) 0 :=
  DTree.pure (roundBlockTree T I a, roundBlockMap p I S)

omit [Fintype V] in
theorem public_round_run (p : V → B) (T : RootedTree B) (I : B → Finset ι)
    (S : B → ι → Finset V) (a : (b : B) → B → Option (I b)) :
    ∃ P : DTree (Finset V) ℝ (RootedTree (RoundBlock I) × (V → RoundBlock I)) 0,
      P = publicRoundProgram p T I S a ∧
      ∀ read : Finset V → ℝ,
        DTree.run read P = ((roundBlockTree T I a, roundBlockMap p I S), 0) :=
  ⟨publicRoundProgram p T I S a, rfl, fun _ => rfl⟩

/-- Literal structural contract on the executed constructor's output. This does
not assert original-graph minimum cuts or produce the supplied refinement data. -/
theorem public_round_geometry (p : V → B) (T : RootedTree B) (I : B → Finset ι)
    (S : B → ι → Finset V) (a : (b : B) → B → Option (I b))
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e))
    (read : Finset V → ℝ) :
    let out := (publicRoundProgram p T I S a).eval read
    (publicRoundProgram p T I S a).cost read = 0 ∧
    (∀ x, roundBlockParent I (out.2 x) = p x) ∧
    ∀ v, v ≠ out.1.root →
      (∃ e : B, e ≠ T.root ∧
        selectedParentEdge out.1 (roundEdges T I a) v = roundOldEdge T I a e ∧
        pull out.2 (out.1.D v) = pull p (T.D e)) ∨
      (∃ (b : B) (i : I b),
        selectedParentEdge out.1 (roundEdges T I a) v = roundStarEdge I ⟨b, i⟩ ∧
        pull out.2 (out.1.D v) =
          if T.root ≠ b ∧ a b T.root = some i then (originalChildShore p I S a b i)ᶜ
          else originalChildShore p I S a b i) := by
  refine ⟨rfl, roundBlockParent_map p I S, ?_⟩
  intro v hv
  rcases actual_parent_edge T I a hv with ⟨e, he, hs⟩ | ⟨b, i, hs⟩
  · exact Or.inl ⟨e, he, hs, old_pull_exact p T I S a hconstant hv he hs⟩
  · exact Or.inr ⟨b, i, hs, star_pull_exact p T I S a hdisj hconstant hv b i hs⟩

/-- Equality of original cut values follows from the structural equations for
any weighted graph. Minimality remains a separate semantic obligation. -/
theorem original_cut_values (p : V → B) (T : RootedTree B) (I : B → Finset ι)
    (S : B → ι → Finset V) (a : (b : B) → B → Option (I b))
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hconstant : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e))
    (G : WeightedGraph V) {v : RoundBlock I} (hv : v ≠ (roundBlockTree T I a).root) :
    (∃ e : B, e ≠ T.root ∧
      selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v = roundOldEdge T I a e ∧
      G.cut (pull (roundBlockMap p I S) ((roundBlockTree T I a).D v)) = G.cut (pull p (T.D e))) ∨
    (∃ (b : B) (i : I b),
      selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v = roundStarEdge I ⟨b, i⟩ ∧
      G.cut (pull (roundBlockMap p I S) ((roundBlockTree T I a).D v)) =
        G.cut (originalChildShore p I S a b i)) := by
  rcases actual_parent_edge T I a hv with ⟨e, he, hs⟩ | ⟨b, i, hs⟩
  · exact Or.inl ⟨e, he, hs, congrArg G.cut (old_pull_exact p T I S a hconstant hv he hs)⟩
  · refine Or.inr ⟨b, i, hs, ?_⟩
    rw [star_pull_exact p T I S a hdisj hconstant hv b i hs]
    split <;> simp only [cut_compl]

end RoundCutContracts





end

end APMCContracts6


/- Actual execution contract: randomized. -/
section RandomizedContracts6

/-! Literal contracts for the supplied-data block refinement.
The graph enters only the semantic statements, with the original witnesses. -/

set_option autoImplicit false

namespace CutQueryComplexity.GHBlockRefinementContracts
noncomputable section
open scoped Classical
open GHReduction WeightedGraph

variable {V B ι : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq ι]

/-- The actual map and BFS tree are fixed from public data before a hidden graph. -/
theorem public_refinement (p : V → B) (T : RootedTree B) (b : B) (I : Finset ι)
    (S : ι → Finset (FrontierVertex p T b)) :
    ∃ q : V → RefinedBlock b I, ∃ tree : RootedTree (RefinedBlock b I),
      q = refinedBlockMap p b I (fun j => pull (frontierMap p T b) (S j)) ∧
      tree = refinedBlockTree T b I (auxiliaryAttachment p T b I S) ∧
      (∀ v, refinedBlockParent b I (q v) = p v) ∧
      tree.root = Sum.inr none ∧
      EdgeShoreSystem (refinedEdges T b I (auxiliaryAttachment p T b I S))
        (refinedEdgeShore T b I (auxiliaryAttachment p T b I S)) := by
  refine ⟨refinedBlockMap p b I (fun j => pull (frontierMap p T b) (S j)),
    refinedBlockTree T b I (auxiliaryAttachment p T b I S), rfl, rfl, ?_, rfl, ?_⟩
  · exact refinedBlockParent_map p b I _
  · exact auxiliaryAttachment_shore_system p T b I S

/-- The concrete proxy lookup is constant along old edges within one branch. -/
theorem attachment_semantics (p : V → B) (T : RootedTree B) (b : B) (I : Finset ι)
    (S : ι → Finset (FrontierVertex p T b))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) :
    (∀ e, e ≠ T.root → e ≠ b → T.parent e ≠ b →
      auxiliaryAttachment p T b I S e = auxiliaryAttachment p T b I S (T.parent e)) ∧
    (∀ c (hc : c ≠ b) (i : I), auxiliaryAttachment p T b I S c = some i ↔
      (Sum.inr (frontierProxy T b c hc) : FrontierVertex p T b) ∈ S i.val) :=
  ⟨fun _ he heb hpb => auxiliaryAttachment_parent p T b I S he heb hpb,
    auxiliaryAttachment_some_iff p T b I S hdisj⟩

/-- Every retained old edge still denotes exactly its original vertex shore. -/
theorem old_edge_pullback (p : V → B) (T : RootedTree B) (b : B) (I : Finset ι)
    (S : ι → Finset (FrontierVertex p T b)) {e : B} (he : e ≠ T.root) :
    pull (refinedBlockMap p b I (fun j => pull (frontierMap p T b) (S j)))
      (refinedEdgeShore T b I (auxiliaryAttachment p T b I S)
        (refinedOldEdge T b I (auxiliaryAttachment p T b I S) e)) = pull p (T.D e) := by
  rw [refinedEdgeShore_old T b I _ he, refinedBlock_old_shore_pull]

/-- Every new star edge includes exactly its whole attached original proxy branches. -/
theorem child_edge_pullback (p : V → B) (T : RootedTree B) (b : B) (I : Finset ι)
    (S : ι → Finset (FrontierVertex p T b))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) (i : I) :
    pull (refinedBlockMap p b I (fun j => pull (frontierMap p T b) (S j)))
      (refinedEdgeShore T b I (auxiliaryAttachment p T b I S) (refinedStarEdge b I i)) =
        pull (frontierMap p T b) (S i.val) := by
  rw [refinedEdgeShore_star, refinementChildShore_pull p T b I S hdisj i]

/-- The full old/star system identifies fundamental shores of this actual BFS tree. -/
theorem actual_fundamental (p : V → B) (T : RootedTree B) (b : B) (I : Finset ι)
    (S : ι → Finset (FrontierVertex p T b)) {v : RefinedBlock b I}
    (hv : v ≠ (refinedBlockTree T b I (auxiliaryAttachment p T b I S)).root) :
    let tree := refinedBlockTree T b I (auxiliaryAttachment p T b I S)
    let edges := refinedEdges T b I (auxiliaryAttachment p T b I S)
    let shore := refinedEdgeShore T b I (auxiliaryAttachment p T b I S)
    selectedParentEdge tree edges v ∈ edges ∧
      (tree.D v = shore (selectedParentEdge tree edges v) ∨
        tree.D v = (shore (selectedParentEdge tree edges v))ᶜ) := by
  dsimp only
  exact ⟨selectedParentEdge_mem _ _ (refinedBlockTree_parent_adj T b I _ hv),
    refinedBlockTree_fundamental T b I (auxiliaryAttachment p T b I S)
      (fun e he heb hpb => auxiliaryAttachment_parent (e := e) p T b I S he heb hpb) hv⟩

theorem actual_single_crossing (p : V → B) (T : RootedTree B) (b : B) (I : Finset ι)
    (S : ι → Finset (FrontierVertex p T b)) {v : RefinedBlock b I}
    (hv : v ≠ (refinedBlockTree T b I (auxiliaryAttachment p T b I S)).root) :
    let tree := refinedBlockTree T b I (auxiliaryAttachment p T b I S)
    let edges := refinedEdges T b I (auxiliaryAttachment p T b I S)
    tree.crossSet (refinedEdgeShore T b I (auxiliaryAttachment p T b I S)
      (selectedParentEdge tree edges v)) = {v} := by
  dsimp only
  exact edgeShore_crossSet_singleton _ _
    (fun _ h => refinedBlockTree_parent_adj T b I _ h) _
    (auxiliaryAttachment_shore_system p T b I S) hv

/-- Original minimum-cut witnesses suffice to derive the protected frontier fibers. -/
theorem protected_frontier (G : WeightedGraph V) (p : V → B) (T : RootedTree B) (b : B)
    (r c : frontierProxies T b → V)
    (hcut : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e))) :
    (∀ z, frontierMap p T b (frontierRepresentative p T b r z) = z) ∧
    (∀ z, Certificate.GomoryHu.RootProtected G (fiber (frontierMap p T b) z)
      (frontierRepresentative p T b r z)) :=
  ⟨frontierRepresentative_section p T b r (fun e => (mem_pull _ _ _).mp (hcut e).1),
    frontierRepresentative_protected G p T b r c hcut⟩

/-- Old witnesses remain about the identical original shore and cut value. -/
theorem old_witness_retained (G : WeightedGraph V) (p : V → B) (T : RootedTree B)
    (b : B) (I : Finset ι) (S : ι → Finset (FrontierVertex p T b))
    {e : B} (he : e ≠ T.root) (s t : V)
    (hcut : IsSTMinCut G s t (pull p (T.D e))) :
    let shore := pull (refinedBlockMap p b I (fun j => pull (frontierMap p T b) (S j)))
      (refinedEdgeShore T b I (auxiliaryAttachment p T b I S)
        (refinedOldEdge T b I (auxiliaryAttachment p T b I S) e))
    IsSTMinCut G s t shore ∧ G.cut shore = G.cut (pull p (T.D e)) := by
  dsimp only
  rw [old_edge_pullback p T b I S he]
  exact ⟨hcut, rfl⟩

/-- Child correctness uses the original disjointness, proxy witnesses, and auxiliary mincut. -/
theorem child_semantics (G : WeightedGraph V) (p : V → B) (T : RootedTree B)
    (b : B) (I : Finset ι) (S : ι → Finset (FrontierVertex p T b))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (r c : frontierProxies T b → V)
    (hcut : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e)))
    {s t : fiber p b} (i : I)
    (hS : IsSTMinCut (G.contract (frontierMap p T b)) (Sum.inl s) (Sum.inl t) (S i.val)) :
    let shore := pull (refinedBlockMap p b I (fun j => pull (frontierMap p T b) (S j)))
      (refinedEdgeShore T b I (auxiliaryAttachment p T b I S) (refinedStarEdge b I i))
    IsSTMinCut G s.val t.val shore ∧
      G.cut shore = (G.contract (frontierMap p T b)).cut (S i.val) ∧
      G.cut shore = stValue G s.val t.val := by
  dsimp only
  rw [refinedEdgeShore_star]
  have h := refinementChild_minCut G p T b I S hdisj r c hcut i hS
  exact ⟨h, refinementChild_cut G p T b I S hdisj i, stValue_eq_of_minCut G h⟩

end
end CutQueryComplexity.GHBlockRefinementContracts

end RandomizedContracts6

#audit_cut_decl GHStarContracts.literal_pack
#audit_cut_decl GHStarContracts.literal_fold_run
#audit_cut_decl GHStarContracts.literal_finish_run
#audit_cut_decl GHStarContracts.star_attach_outside
#audit_cut_decl GHStarContracts.star_attach_child
#audit_cut_decl GHStarContracts.literal_star_constructor
#audit_cut_decl GHStarContracts.finish_of_covered_fold
#audit_cut_decl GHStarContracts.literal_star_decoder_run
#audit_cut_decl GHStarContracts.literal_completed_star_decoder
#audit_cut_decl GH212Contract.truncateRunLaw
#audit_cut_decl GH212Contract.dependentTableRunStep
#audit_cut_decl GH212Contract.sourcePivotForRunLaw
#audit_cut_decl GH212Contract.sourcePivotTreeRunLaw
#audit_cut_decl GH212Contract.publicSourcePivot
#audit_cut_decl GH212Contract.frontierActiveRunLaw
#audit_cut_decl GH212Contract.frontierInactiveRunLaw
#audit_cut_decl GH212Contract.frontierTableRunLaw
#audit_cut_decl GH212Contract.frontierHonestJointLaw
#audit_cut_decl GH212Contract.frontierStateStepRunLaw
#audit_cut_decl GH212Contract.frontierStateStepHonestJointLaw
#audit_cut_decl GH212Contract.frontierExecutionRunLaw
#audit_cut_decl GH212Contract.checkedFallbackLaw
#audit_cut_decl GH212Contract.recordPartitionLaw
#audit_cut_decl GH212Contract.publicFrontierExecution
#audit_cut_decl RoundCutContracts.child_shore_pull
#audit_cut_decl RoundCutContracts.actual_parent_edge
#audit_cut_decl RoundCutContracts.old_fundamental_exact
#audit_cut_decl RoundCutContracts.child_root_membership
#audit_cut_decl RoundCutContracts.star_fundamental_exact
#audit_cut_decl RoundCutContracts.old_pull_exact
#audit_cut_decl RoundCutContracts.star_pull_exact
#audit_cut_decl RoundCutContracts.quotient_labels
#audit_cut_decl RoundCutContracts.public_round_run
#audit_cut_decl RoundCutContracts.public_round_geometry
#audit_cut_decl RoundCutContracts.original_cut_values
#audit_cut_decl CutQueryComplexity.GHBlockRefinementContracts.public_refinement
#audit_cut_decl CutQueryComplexity.GHBlockRefinementContracts.attachment_semantics
#audit_cut_decl CutQueryComplexity.GHBlockRefinementContracts.old_edge_pullback
#audit_cut_decl CutQueryComplexity.GHBlockRefinementContracts.child_edge_pullback
#audit_cut_decl CutQueryComplexity.GHBlockRefinementContracts.actual_fundamental
#audit_cut_decl CutQueryComplexity.GHBlockRefinementContracts.actual_single_crossing
#audit_cut_decl CutQueryComplexity.GHBlockRefinementContracts.protected_frontier
#audit_cut_decl CutQueryComplexity.GHBlockRefinementContracts.old_witness_retained
#audit_cut_decl CutQueryComplexity.GHBlockRefinementContracts.child_semantics


/- Actual execution contract: gh. -/
section GHContracts7

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction
open CutQueryComplexity.WeightedGraph
open scoped Classical

namespace GH213Contract
noncomputable section

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

-- The half-size count uses original block terminals, excluding all proxies.
theorem traceCardLaw (p : V → B) (T : RootedTree B) (b : B)
    (shore : Finset (FrontierVertex p T b)) :
    (pull (frontierMap p T b) shore ∩ fiber p b).card =
      (shore ∩ frontierTerminals p T b).card :=
  frontier_terminal_trace_card p T b shore

-- hgood is the semantic premise on the actual returned value, not a new
-- assumption that the public normalization guard accepts it.
theorem goodGuardLaw (G : WeightedGraph V) (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) {levels : ℕ}
    (out : SourcePivotOutput (FrontierVertex p T b) levels)
    (hgood : SourcePivotGood (G.contract (frontierMap p T b)) (frontierTerminals p T b) out) :
    checkedFrontierSplit p hp T b (some out) =
      liftFrontierSplit p T b (blockRepresentative p hp b) (some out) ∧
    ValidBlockSplit (fiber p b) (checkedFrontierSplit p hp T b (some out)) ∧
    ∃ s : fiber p b, out.pivot = Sum.inl s ∧
      (checkedFrontierSplit p hp T b (some out)).source = s.val := by
  have hguard := checkedFrontierSplit_of_wellFormed p hp T b out hgood.1 hgood.2.2.1
  refine ⟨hguard, checkedFrontierSplit_valid p hp T b (some out), ?_⟩
  obtain ⟨s, hs⟩ := (mem_frontierTerminals p T b out.pivot).mp hgood.1
  refine ⟨s, hs.symm, ?_⟩
  rw [hguard]
  simp only [liftFrontierSplit, hs.symm]

-- The guard keeps the actual lifted shores and queried values verbatim.
theorem guardRetainsFields (G : WeightedGraph V) (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) {levels : ℕ}
    (out : SourcePivotOutput (FrontierVertex p T b) levels)
    (hgood : SourcePivotGood (G.contract (frontierMap p T b)) (frontierTerminals p T b) out)
    (v : V) :
    (checkedFrontierSplit p hp T b (some out)).shore v =
      pull (frontierMap p T b) (out.step.batch.shore (frontierMap p T b v)) ∧
    (checkedFrontierSplit p hp T b (some out)).value v =
      out.step.batch.value (frontierMap p T b v) := by
  rw [checkedFrontierSplit_of_wellFormed p hp T b out hgood.1 hgood.2.2.1]
  exact ⟨rfl, rfl⟩

-- This public nonempty-residual invariant even holds for malformed replies.
theorem checkedResidualLaw (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) {levels : ℕ}
    (out : Option (SourcePivotOutput (FrontierVertex p T b) levels)) :
    (checkedFrontierSplit p hp T b out).source ∈
      fiber p b \ ((checkedFrontierSplit p hp T b out).children.biUnion
        (fun v => (checkedFrontierSplit p hp T b out).shore v ∩ fiber p b)) := by
  have hvalid := checkedFrontierSplit_valid p hp T b out
  refine Finset.mem_sdiff.mpr ⟨hvalid.source_mem, ?_⟩
  intro hcovered
  obtain ⟨v, hv, hsource⟩ := Finset.mem_biUnion.mp hcovered
  exact hvalid.excludes v hv (Finset.mem_inter.mp hsource).1

-- The protected proxy branch witnesses are indispensable explicit inputs.
theorem protectedMinimumLaw (G : WeightedGraph V) (p : V → B)
    (hp : Function.Surjective p) (T : RootedTree B) (b : B)
    (r c : frontierProxies T b → V)
    (hbranch : ∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e)))
    {levels : ℕ} (out : SourcePivotOutput (FrontierVertex p T b) levels)
    (hgood : SourcePivotGood (G.contract (frontierMap p T b)) (frontierTerminals p T b) out) :
    ∀ v ∈ (checkedFrontierSplit p hp T b (some out)).children,
      IsSTMinCut G v (checkedFrontierSplit p hp T b (some out)).source
        ((checkedFrontierSplit p hp T b (some out)).shore v) ∧
      (checkedFrontierSplit p hp T b (some out)).value v =
        G.cut ((checkedFrontierSplit p hp T b (some out)).shore v) :=
  checkedFrontierSplit_minCuts G p hp T b r c hbranch out hgood

-- A literal zero-query readout of the actual public checked split, selected
-- before G. This wrapper performs no auxiliary solve: hgood must come from
-- the preceding executed source-pivot call (or another proof of that premise).
theorem publicCheckedSplit (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) {levels : ℕ}
    (out : SourcePivotOutput (FrontierVertex p T b) levels) :
    ∃ P : RTree (Finset V) ℝ (PublicBlockSplit V) 0,
      P = RTree.pure (PMF.pure (checkedFrontierSplit p hp T b (some out))) ∧
      (∀ answer : TranscriptOracle.AnswerPolicy (Finset V) ℝ, ∀ history,
        TranscriptOracle.run answer P history =
          PMF.pure (checkedFrontierSplit p hp T b (some out), 0)) ∧
      (∀ G : WeightedGraph V,
        SourcePivotGood (G.contract (frontierMap p T b)) (frontierTerminals p T b) out →
        ∀ r c : frontierProxies T b → V,
        (∀ e, IsSTMinCut G (r e) (c e) (pull p (frontierBranch T b e))) →
        ∀ read : Finset V → ℝ, ∀ split ∈ (P.eval read).support,
          split = liftFrontierSplit p T b (blockRepresentative p hp b) (some out) ∧
          ValidBlockSplit (fiber p b) split ∧
          split.source ∈ fiber p b \ (split.children.biUnion (fun v => split.shore v ∩ fiber p b)) ∧
          ∀ v ∈ split.children, IsSTMinCut G v split.source (split.shore v) ∧
            split.value v = G.cut (split.shore v)) := by
  refine ⟨RTree.pure (PMF.pure (checkedFrontierSplit p hp T b (some out))), rfl, ?_, ?_⟩
  · intro answer history
    simp only [TranscriptOracle.run, RTree.pure, PMF.pure_map]
  · intro G hgood r c hbranch read split hsplit
    simp only [RTree.eval_pure] at hsplit
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hsplit
    exact ⟨(goodGuardLaw G p hp T b out hgood).1,
      checkedFrontierSplit_valid p hp T b (some out),
      checkedResidualLaw p hp T b (some out),
      checkedFrontierSplit_minCuts G p hp T b r c hbranch out hgood⟩

end
end GH213Contract




end GHContracts7


/- Actual execution contract: apmc. -/
section APMCContracts7

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction WeightedGraph
open scoped Classical
noncomputable section

namespace FrontierGeometryContracts

variable {V B ι : Type} [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq ι]

/-- The actual representative attachment is derived from pullback geometry.
No independently supplied attachment invariant appears in this contract. -/
theorem attached_parent_geometry (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (I : B → Finset ι) (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b), S b i = pull (frontierMap p T b) A) :
    let a := roundSplitAttachment p hp I S
    ∀ v, v ≠ (roundBlockTree T I a).root →
      (∃ e : B, e ≠ T.root ∧
        selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v = roundOldEdge T I a e ∧
        pull (roundBlockMap p I S) ((roundBlockTree T I a).D v) = pull p (T.D e)) ∨
      (∃ (b : B) (i : I b),
        selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v = roundStarEdge I ⟨b, i⟩ ∧
        pull (roundBlockMap p I S) ((roundBlockTree T I a).D v) =
          if T.root ≠ b ∧ a b T.root = some i then (S b i.val)ᶜ else S b i.val) := by
  dsimp only
  intro v hv
  let a := roundSplitAttachment p hp I S
  have hc : ∀ b e, e ≠ T.root → e ≠ b → T.parent e ≠ b → a b e = a b (T.parent e) := by
    intro b e he heb hpb
    exact roundSplitAttachment_parent p hp T I S hdisj hpull b he heb hpb
  have hm := selectedParentEdge_mem (roundBlockTree T I a) (roundEdges T I a)
    (roundBlockTree_parent_adj T I a hv)
  have hf := roundBlockTree_fundamental T I a hc hv
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨e, he, hedge⟩ := Finset.mem_image.mp hm
    have he0 : e ≠ T.root := (Finset.mem_erase.mp he).1
    rw [← hedge, roundEdgeShore_old T I a he0] at hf
    have hroot : (roundBlockTree T I a).root ∉ pull (roundBlockParent I) (T.D e) := by
      intro h
      exact T.root_not_mem_D he0
        ((mem_pull (roundBlockParent I) (T.D e) (roundBlockTree T I a).root).mp h)
    have hd : (roundBlockTree T I a).D v = pull (roundBlockParent I) (T.D e) := by
      rcases hf with hf | hf
      · exact hf
      · exact ((roundBlockTree T I a).root_not_mem_D hv
          (hf.symm ▸ Finset.mem_compl.mpr hroot)).elim
    exact Or.inl ⟨e, he0, hedge.symm,
      (congrArg (pull (roundBlockMap p I S)) hd).trans (roundBlock_old_shore_pull p I S (T.D e))⟩
  · obtain ⟨⟨b, i⟩, _, hedge⟩ := Finset.mem_image.mp hm
    rw [← hedge, roundEdgeShore_star] at hf
    have hroot : (roundBlockTree T I a).root ∈ roundChildShore I a b i ↔
        T.root ≠ b ∧ a b T.root = some i := by
      by_cases hr : T.root = b
      · subst b
        constructor
        · intro hm
          have hn := (mem_roundChildShore_same I a T.root i none).mp hm
          cases hn
        · rintro ⟨hne, _⟩
          exact (hne rfl).elim
      · exact ⟨fun hm => ⟨hr, (mem_roundChildShore_other I a b i hr none).mp hm⟩,
          fun hm => (mem_roundChildShore_other I a b i hr none).mpr hm.2⟩
    have hchild := roundChildShore_pull p hp T I S hdisj hpull b i
    refine Or.inr ⟨b, i, hedge.symm, ?_⟩
    by_cases hr : T.root ≠ b ∧ a b T.root = some i
    · have hd : (roundBlockTree T I a).D v = (roundChildShore I a b i)ᶜ :=
        hf.resolve_left (fun h => (roundBlockTree T I a).root_not_mem_D hv
          (h.symm ▸ hroot.mpr hr))
      exact ((congrArg (pull (roundBlockMap p I S)) hd).trans
        ((pull_compl (roundBlockMap p I S) (roundChildShore I a b i)).trans
          (congrArg (fun A : Finset V => Aᶜ) hchild))).trans (ite_eq_left hr).symm
    · have hnr : (roundBlockTree T I a).root ∉ roundChildShore I a b i :=
        fun h => hr (hroot.mp h)
      have hd : (roundBlockTree T I a).D v = roundChildShore I a b i :=
        hf.resolve_right (fun h => (roundBlockTree T I a).root_not_mem_D hv
          (h.symm ▸ Finset.mem_compl.mpr hnr))
      exact ((congrArg (pull (roundBlockMap p I S)) hd).trans hchild).trans (ite_eq_right hr).symm

/-- Explicit witness endpoints are kept or swapped exactly with the shore.
Old/new witnesses remain semantic inputs; they are not produced by this lemma. -/
theorem selected_parent_semantics (G : WeightedGraph V)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (I : B → Finset ι) (S : B → ι → Finset V)
    (hdisj : ∀ b, ∀ i ∈ I b, ∀ j ∈ I b, i ≠ j → Disjoint (S b i) (S b j))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b), S b i = pull (frontierMap p T b) A)
    (oldSource oldTarget : B → V) (newSource newTarget : (b : B) → I b → V)
    (hold : ∀ e, e ≠ T.root → IsSTMinCut G (oldSource e) (oldTarget e) (pull p (T.D e)))
    (hnew : ∀ b (i : I b), IsSTMinCut G (newSource b i) (newTarget b i) (S b i.val)) :
    let a := roundSplitAttachment p hp I S
    ∀ v, v ≠ (roundBlockTree T I a).root →
      (∃ e : B, e ≠ T.root ∧
        selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v = roundOldEdge T I a e ∧
        pull (roundBlockMap p I S) ((roundBlockTree T I a).D v) = pull p (T.D e) ∧
        IsSTMinCut G (oldSource e) (oldTarget e)
          (pull (roundBlockMap p I S) ((roundBlockTree T I a).D v))) ∨
      (∃ (b : B) (i : I b),
        selectedParentEdge (roundBlockTree T I a) (roundEdges T I a) v = roundStarEdge I ⟨b, i⟩ ∧
        pull (roundBlockMap p I S) ((roundBlockTree T I a).D v) =
          (if T.root ≠ b ∧ a b T.root = some i then (S b i.val)ᶜ else S b i.val) ∧
        (if T.root ≠ b ∧ a b T.root = some i then
          IsSTMinCut G (newTarget b i) (newSource b i)
            (pull (roundBlockMap p I S) ((roundBlockTree T I a).D v))
        else IsSTMinCut G (newSource b i) (newTarget b i)
            (pull (roundBlockMap p I S) ((roundBlockTree T I a).D v)))) := by
  dsimp only
  intro v hv
  rcases attached_parent_geometry p hp T I S hdisj hpull v hv with
    ⟨e, he, hedge, hshore⟩ | ⟨b, i, hedge, hshore⟩
  · exact Or.inl ⟨e, he, hedge, hshore, hshore.symm ▸ hold e he⟩
  · refine Or.inr ⟨b, i, hedge, hshore, ?_⟩
    by_cases hr : T.root ≠ b ∧ roundSplitAttachment p hp I S b T.root = some i
    · rw [ite_eq_left hr, hshore, ite_eq_left hr]
      exact stMinCut_compl G (hnew b i)
    · rw [ite_eq_right hr, hshore, ite_eq_right hr]
      exact hnew b i

/-- Guards and frontier pullbacks hold for every record, including malformed
or absent results. There is no Good-record premise or minimum-cut assumption. -/
theorem checked_record_inputs {levels : ℕ} (record : FrontierRoundRecord V levels) :
    (∀ b, ∀ i ∈ (record.split b).children, ∀ j ∈ (record.split b).children,
      i ≠ j → Disjoint ((record.split b).shore i) ((record.split b).shore j)) ∧
    (∀ b i, ∃ A : Finset (FrontierVertex record.before.block record.before.tree b),
      (record.split b).shore i = pull (frontierMap record.before.block record.before.tree b) A) := by
  refine ⟨?_, ?_⟩
  · intro b i hi j hj hij
    exact (record.split_valid b).disjoint hi hj hij
  · intro b i
    exact checkedFrontierSplit_shore_pull record.before.block record.before.onto record.before.tree b
      (record.result.elim none (fun table => table b)) i

theorem checked_record_attachment {levels : ℕ} (record : FrontierRoundRecord V levels)
    (b e : Fin record.before.size) (he : e ≠ record.before.tree.root)
    (heb : e ≠ b) (hpb : record.before.tree.parent e ≠ b) :
    roundSplitAttachment record.before.block record.before.onto
      (fun b => (record.split b).children) (fun b => (record.split b).shore) b e =
    roundSplitAttachment record.before.block record.before.onto
      (fun b => (record.split b).children) (fun b => (record.split b).shore) b (record.before.tree.parent e) :=
  roundSplitAttachment_parent record.before.block record.before.onto record.before.tree _ _
    (checked_record_inputs record).1 (checked_record_inputs record).2 b he heb hpb

theorem checked_record_child_pull {levels : ℕ} (record : FrontierRoundRecord V levels)
    (b : Fin record.before.size) (i : (record.split b).children) :
    pull (roundBlockMap record.before.block (fun b => (record.split b).children)
      (fun b => (record.split b).shore))
      (roundChildShore (fun b => (record.split b).children)
        (roundSplitAttachment record.before.block record.before.onto
          (fun b => (record.split b).children) (fun b => (record.split b).shore)) b i) =
      (record.split b).shore i.val :=
  roundChildShore_pull record.before.block record.before.onto record.before.tree _ _
    (checked_record_inputs record).1 (checked_record_inputs record).2 b i

/-- The raw tree and partition used inside this record's actual after-state. -/
def rawRound {levels : ℕ} (record : FrontierRoundRecord V levels) :
    RootedTree (RoundBlock (fun b => (record.split b).children)) ×
      (V → RoundBlock (fun b => (record.split b).children)) :=
  (roundBlockTree record.before.tree (fun b => (record.split b).children)
    (roundSplitAttachment record.before.block record.before.onto
      (fun b => (record.split b).children) (fun b => (record.split b).shore)),
   roundBlockMap record.before.block (fun b => (record.split b).children) (fun b => (record.split b).shore))

theorem actual_after_representation {levels : ℕ} (record : FrontierRoundRecord V levels) :
    record.after.size = Fintype.card (RoundBlock (fun b => (record.split b).children)) ∧
    HEq record.after.block
      (Fintype.equivFin (RoundBlock (fun b => (record.split b).children)) ∘ (rawRound record).2) ∧
    HEq record.after.tree
      (relabelRootedTree (rawRound record).1
        (Fintype.equivFin (RoundBlock (fun b => (record.split b).children)))) :=
  ⟨rfl, HEq.rfl, HEq.rfl⟩

theorem rawRound_onto {levels : ℕ} (record : FrontierRoundRecord V levels) :
    Function.Surjective (rawRound record).2 := by
  intro c
  obtain ⟨v, hv⟩ := record.after.onto
    ((Fintype.equivFin (RoundBlock (fun b => (record.split b).children))) c)
  exact ⟨v, (Fintype.equivFin (RoundBlock (fun b => (record.split b).children))).injective hv⟩

theorem checked_record_geometry {levels : ℕ} (record : FrontierRoundRecord V levels) :
    let a := roundSplitAttachment record.before.block record.before.onto
      (fun b => (record.split b).children) (fun b => (record.split b).shore)
    ∀ v, v ≠ (rawRound record).1.root →
      (∃ e, e ≠ record.before.tree.root ∧
        selectedParentEdge (rawRound record).1
          (roundEdges record.before.tree (fun b => (record.split b).children) a) v =
            roundOldEdge record.before.tree (fun b => (record.split b).children) a e ∧
        pull (rawRound record).2 ((rawRound record).1.D v) = pull record.before.block (record.before.tree.D e)) ∨
      (∃ (b : Fin record.before.size) (i : (record.split b).children),
        selectedParentEdge (rawRound record).1
          (roundEdges record.before.tree (fun b => (record.split b).children) a) v =
            roundStarEdge (fun b => (record.split b).children) ⟨b, i⟩ ∧
        pull (rawRound record).2 ((rawRound record).1.D v) =
          if record.before.tree.root ≠ b ∧ a b record.before.tree.root = some i then
            ((record.split b).shore i.val)ᶜ else (record.split b).shore i.val) :=
  attached_parent_geometry record.before.block record.before.onto record.before.tree _ _
    (checked_record_inputs record).1 (checked_record_inputs record).2

/-- Original witnesses are still hypotheses. This is a single checked-record
transport, not an induction deriving witnesses along the executed history. -/
theorem checked_record_minimum_witnesses {levels : ℕ} (record : FrontierRoundRecord V levels)
    (G : WeightedGraph V)
    (hold : ∀ e, e ≠ record.before.tree.root →
      ∃ s t, IsSTMinCut G s t (pull record.before.block (record.before.tree.D e)))
    (hnew : ∀ b i, i ∈ (record.split b).children →
      ∃ s t, IsSTMinCut G s t ((record.split b).shore i)) :
    ∀ v, v ≠ (rawRound record).1.root →
      ∃ s t, IsSTMinCut G s t (pull (rawRound record).2 ((rawRound record).1.D v)) := by
  intro v hv
  exact roundBlockTree_minCut_witness G record.before.block record.before.onto record.before.tree _ _
    (checked_record_inputs record).1 (checked_record_inputs record).2 hold hnew hv

/-- Public postprocessing is fixed before the hidden graph and every reply.
The conditional semantic assertion is on its actual output and original cut. -/
theorem literal_public_postprocessing {levels : ℕ} (record : FrontierRoundRecord V levels) :
    ∃ P : DTree (Finset V) ℝ
      (RootedTree (RoundBlock (fun b => (record.split b).children)) ×
        (V → RoundBlock (fun b => (record.split b).children))) 0,
      P = DTree.pure (rawRound record) ∧
      ∀ read : Finset V → ℝ,
        DTree.run read P = (rawRound record, 0) ∧
        ∀ G : WeightedGraph V,
          (∀ e, e ≠ record.before.tree.root →
            ∃ s t, IsSTMinCut G s t (pull record.before.block (record.before.tree.D e))) →
          (∀ b i, i ∈ (record.split b).children →
            ∃ s t, IsSTMinCut G s t ((record.split b).shore i)) →
          ∀ v, v ≠ (P.eval read).1.root →
            ∃ s t, s ∈ pull (P.eval read).2 ((P.eval read).1.D v) ∧
              t ∉ pull (P.eval read).2 ((P.eval read).1.D v) ∧
              ∀ A : Finset V, s ∈ A → t ∉ A →
                G.cut (pull (P.eval read).2 ((P.eval read).1.D v)) ≤ G.cut A := by
  refine ⟨DTree.pure (rawRound record), rfl, ?_⟩
  intro read
  refine ⟨rfl, ?_⟩
  intro G hold hnew v hv
  exact checked_record_minimum_witnesses record G hold hnew v hv

theorem absent_result_shores (p : V → B) (hp : Function.Surjective p)
    (T : RootedTree B) (b : B) (levels : ℕ) (v : V) :
    (checkedFrontierSplit p hp T b (levels := levels) none).shore v = ∅ := by
  unfold checkedFrontierSplit normalizeBlockSplit
  split <;> rfl

end FrontierGeometryContracts





end

end APMCContracts7


/- Actual execution contract: quantum-neighbors. -/
section QuantumNeighborsContracts6

/-! Literal public execution and data-coherence contracts. These do not assert
that a good trace terminates or assembles successfully, and do not replace the
missing recursive attachment invariant with an assumed successful output. -/

set_option autoImplicit false

namespace FrontierAssemblyContracts
open CutQueryComplexity CutQueryComplexity.GHReduction CutQueryComplexity.WeightedGraph
open scoped Classical
noncomputable section

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

theorem collect_exact (results : B → Option (PackedSteinerTree V))
    (out : B → PackedSteinerTree V) :
    collectBlockTrees results = some out ↔ ∀ b, results b = some (out b) := by
  constructor
  · exact collectBlockTrees_spec results
  · intro h
    obtain ⟨actual, ha, hs⟩ := collectBlockTrees_exists results (fun b => ⟨out b, h b⟩)
    have he : actual = out := by
      funext b
      exact Option.some.inj ((hs b).symm.trans (h b))
    simpa only [he] using ha

theorem collect_none_iff (results : B → Option (PackedSteinerTree V)) :
    collectBlockTrees results = none ↔ ∃ b, results b = none := by
  constructor
  · intro hn
    by_contra h
    have hall : ∀ b, ∃ T, results b = some T := by
      intro b
      cases hb : results b with
      | none => exact (h ⟨b, hb⟩).elim
      | some T => exact ⟨T, rfl⟩
    obtain ⟨out, ho, _⟩ := collectBlockTrees_exists results hall
    rw [hn] at ho
    contradiction
  · rintro ⟨b, hb⟩
    cases hc : collectBlockTrees results with
    | none => rfl
    | some out =>
        have hs := collectBlockTrees_spec results hc b
        rw [hb] at hs
        contradiction

theorem literal_leaf_forest (state : PublicFrontierState V) :
    ∃ P : DTree (Finset V) ℝ (FrontierForest state) 0,
      P = DTree.pure (leafFrontierForest state) ∧
      (∀ read, P.run read = (leafFrontierForest state, 0)) ∧
      (∀ b, (leafFrontierForest state b).size = 1) ∧
      (∀ b x y, (leafFrontierForest state b).value.attach x =
        (leafFrontierForest state b).value.attach y) ∧
      (∀ G : WeightedGraph V, ∀ b, IsSteinerCutTree G ((P.eval G.cut) b).value) := by
  exact ⟨DTree.pure (leafFrontierForest state), rfl, fun _ => rfl, fun _ => rfl,
    leafFrontierForest_attach state, fun G => leafFrontierForest_correct G state⟩

theorem leaf_exact_coverage (state : PublicFrontierState V) (h : state.Discrete) :
    (∀ b x, Represents (leafFrontierForest state b) x ↔ x ∈ fiber state.block b) ∧
      (∀ x, Represents (leafFrontierForest state (state.block x)) x) := by
  refine ⟨leafFrontierForest_coverage state h, ?_⟩
  intro x
  exact (leafFrontierForest_coverage state h (state.block x) x).mpr
    ((mem_fiber _ _ _).mpr rfl)

variable {levels : ℕ}

/-- This is exactly the finite relabeling stored in the next state. -/
theorem actual_round_labels (record : FrontierRoundRecord V levels) :
    Function.Bijective (frontierRoundLabel record) ∧
      (∀ x, record.after.block x = frontierRoundLabel record
        (roundBlockMap record.before.block (fun b => (record.split b).children)
          (fun b => (record.split b).shore) x)) := by
  exact ⟨(Fintype.equivFin _).bijective, fun _ => rfl⟩

theorem actual_child_lookup (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) (b : Fin record.before.size) (i : V) :
    (∀ hi : i ∈ (record.split b).children, frontierRoundChild record forest b i =
      forest (frontierRoundLabel record ⟨b, some ⟨i, hi⟩⟩)) ∧
      (i ∉ (record.split b).children → frontierRoundChild record forest b i =
        forest (frontierRoundLabel record ⟨b, none⟩)) := by
  refine ⟨fun hi => frontierRoundChild_of_mem record forest b i hi, ?_⟩
  intro hi
  simp only [frontierRoundChild, hi, dite_false]

theorem literal_block_call (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) (b : Fin record.before.size) :
    assembleFrontierBlock record forest b =
      assembleDisjointStar (forest (frontierRoundLabel record ⟨b, none⟩))
        (record.split b).source (frontierRoundChild record forest b)
        (record.split b).shore (record.split b).value (record.split b).children.toList := rfl

theorem round_collection_exact (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) (out : FrontierForest record.before) :
    assembleFrontierRound record forest = some out ↔
      ∀ b, assembleFrontierBlock record forest b = some (out b) :=
  collect_exact _ _

theorem round_collection_none (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) :
    assembleFrontierRound record forest = none ↔
      ∃ b, assembleFrontierBlock record forest b = none := collect_none_iff _

theorem restore_matching_record (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) :
    restoreFrontierRecord record ⟨record.after, forest⟩ =
      (assembleFrontierRound record forest).map (fun trees => ⟨record.before, trees⟩) := by
  simp only [restoreFrontierRecord, dite_true]

theorem restore_mismatched_record (record : FrontierRoundRecord V levels)
    (forest : FrontierForestState V) (h : forest.state ≠ record.after) :
    restoreFrontierRecord record forest = none := by
  simp only [restoreFrontierRecord, h, dite_false]

/-- Conditional observational information only: this does not assert that the
restoration succeeds or that the restored trees satisfy a graph invariant. -/
theorem restored_record_states (record : FrontierRoundRecord V levels)
    (forest out : FrontierForestState V)
    (hout : restoreFrontierRecord record forest = some out) :
    forest.state = record.after ∧ out.state = record.before := by
  refine ⟨?_, restoreFrontierRecord_before record forest hout⟩
  by_contra h
  rw [restore_mismatched_record record forest h] at hout
  contradiction

/-- Concatenation restores the right-hand trace first: the concrete fold runs
backwards, rather than replaying records in forward order. -/
theorem restore_append (left right : List (FrontierRoundRecord V levels))
    (forest : FrontierForestState V) :
    restoreFrontierRecords (left ++ right) forest =
      (restoreFrontierRecords right forest).bind (restoreFrontierRecords left) := by
  induction left with
  | nil =>
      simp only [List.nil_append]
      cases h : restoreFrontierRecords right forest <;> rfl
  | cons record rest ih =>
      simp only [List.cons_append, restoreFrontierRecords, ih]
      cases h : restoreFrontierRecords right forest <;> rfl

theorem restore_two_records (first second : FrontierRoundRecord V levels)
    (forest : FrontierForestState V) :
    restoreFrontierRecords [first, second] forest =
      (restoreFrontierRecord second forest).bind (restoreFrontierRecord first) := rfl

theorem restored_coherent_start (start : PublicFrontierState V)
    (records : List (FrontierRoundRecord V levels)) (forest out : FrontierForestState V)
    (hfollows : FrontierTrace.Follows start records forest.state)
    (hout : restoreFrontierRecords records forest = some out) : out.state = start := by
  cases records with
  | nil =>
      have he : forest = out := Option.some.inj hout
      exact he ▸ hfollows
  | cons record rest =>
      cases hrest : restoreFrontierRecords rest forest with
      | none => simp only [restoreFrontierRecords, hrest, Option.bind_none, reduceCtorEq] at hout
      | some middle =>
          have hrecord : restoreFrontierRecord record middle = some out := by
            simpa only [restoreFrontierRecords, hrest, Option.bind_some] using hout
          exact (restoreFrontierRecord_before record middle hrecord).trans hfollows.1

/-- The state-coherence premise is obtained from support of the actual
frontier executor, including arbitrary oracle tables and its fallback paths. -/
theorem actual_execution_restored_start {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (fuel : ℕ) (start : PublicFrontierState V)
    (read : Finset V → ℝ) (trace : FrontierTrace V levels)
    (hsupport : trace ∈ ((frontierExecution family n samples trials guideLevels scale exponent levels
      K hvn fuel start).eval read).support) (out : FrontierForestState V)
    (hrestore : restoreFrontierRecords trace.records
      ⟨trace.endState, leafFrontierForest trace.endState⟩ = some out) :
    trace.records.length = fuel ∧ out.state = start := by
  have h := frontierExecution_support family samples trials guideLevels scale exponent levels
    K hvn fuel start read hsupport
  exact ⟨h.1, restored_coherent_start start trace.records _ out h.2 hrestore⟩

theorem trace_nondiscrete_none (trace : FrontierTrace V levels)
    (h : ¬trace.endState.Discrete) : assembleFrontierTrace trace = none := by
  simp only [assembleFrontierTrace, h, ite_false]

theorem trace_restoration_none (trace : FrontierTrace V levels)
    (h : restoreFrontierRecords trace.records
      ⟨trace.endState, leafFrontierForest trace.endState⟩ = none) :
    assembleFrontierTrace trace = none := by
  by_cases hd : trace.endState.Discrete <;> simp only [assembleFrontierTrace, hd,
    ite_true, ite_false, h, Option.bind_none]

theorem trace_incomplete_coverage_none (trace : FrontierTrace V levels)
    (forest : FrontierForestState V)
    (hrestore : restoreFrontierRecords trace.records
      ⟨trace.endState, leafFrontierForest trace.endState⟩ = some forest)
    (hcover : ¬Function.Surjective (forest.trees forest.state.tree.root).value.terminal) :
    assembleFrontierTrace trace = none := by
  by_cases hd : trace.endState.Discrete <;> simp only [assembleFrontierTrace, hd,
    ite_true, ite_false, hrestore, Option.bind_some, hcover, dite_false]

/-- A literal final-guard branch equation. This does not supply the successful
restoration or infer that its tree is a Gomory-Hu tree. -/
theorem trace_complete_branch (trace : FrontierTrace V levels) (hd : trace.endState.Discrete)
    (forest : FrontierForestState V)
    (hrestore : restoreFrontierRecords trace.records
      ⟨trace.endState, leafFrontierForest trace.endState⟩ = some forest)
    (hcover : Function.Surjective (forest.trees forest.state.tree.root).value.terminal) :
    assembleFrontierTrace trace =
      some (completeSteinerTree (forest.trees forest.state.tree.root).value hcover) := by
  simp only [assembleFrontierTrace, hd, ite_true, hrestore, Option.bind_some, hcover, dite_true]

theorem literal_public_program :
    ∃ P : FrontierTrace V levels → Prog (Finset V) ℝ (Option (CutTree V)),
      P = assembleFrontierTraceProgram ∧
      (∀ trace read, Prog.run read (P trace) = (assembleFrontierTrace trace, 0)) ∧
      (∀ trace read, ((P trace).toDTree 0).run read = (some (assembleFrontierTrace trace), 0)) := by
  exact ⟨assembleFrontierTraceProgram, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end
end FrontierAssemblyContracts


end QuantumNeighborsContracts6

#audit_cut_decl GH213Contract.traceCardLaw
#audit_cut_decl GH213Contract.goodGuardLaw
#audit_cut_decl GH213Contract.guardRetainsFields
#audit_cut_decl GH213Contract.checkedResidualLaw
#audit_cut_decl GH213Contract.protectedMinimumLaw
#audit_cut_decl GH213Contract.publicCheckedSplit
#audit_cut_decl FrontierGeometryContracts.attached_parent_geometry
#audit_cut_decl FrontierGeometryContracts.selected_parent_semantics
#audit_cut_decl FrontierGeometryContracts.checked_record_inputs
#audit_cut_decl FrontierGeometryContracts.checked_record_attachment
#audit_cut_decl FrontierGeometryContracts.checked_record_child_pull
#audit_cut_decl FrontierGeometryContracts.actual_after_representation
#audit_cut_decl FrontierGeometryContracts.rawRound_onto
#audit_cut_decl FrontierGeometryContracts.checked_record_geometry
#audit_cut_decl FrontierGeometryContracts.checked_record_minimum_witnesses
#audit_cut_decl FrontierGeometryContracts.literal_public_postprocessing
#audit_cut_decl FrontierGeometryContracts.absent_result_shores
#audit_cut_decl FrontierAssemblyContracts.collect_exact
#audit_cut_decl FrontierAssemblyContracts.collect_none_iff
#audit_cut_decl FrontierAssemblyContracts.literal_leaf_forest
#audit_cut_decl FrontierAssemblyContracts.leaf_exact_coverage
#audit_cut_decl FrontierAssemblyContracts.actual_round_labels
#audit_cut_decl FrontierAssemblyContracts.actual_child_lookup
#audit_cut_decl FrontierAssemblyContracts.literal_block_call
#audit_cut_decl FrontierAssemblyContracts.round_collection_exact
#audit_cut_decl FrontierAssemblyContracts.round_collection_none
#audit_cut_decl FrontierAssemblyContracts.restore_matching_record
#audit_cut_decl FrontierAssemblyContracts.restore_mismatched_record
#audit_cut_decl FrontierAssemblyContracts.restored_record_states
#audit_cut_decl FrontierAssemblyContracts.restore_append
#audit_cut_decl FrontierAssemblyContracts.restore_two_records
#audit_cut_decl FrontierAssemblyContracts.restored_coherent_start
#audit_cut_decl FrontierAssemblyContracts.actual_execution_restored_start
#audit_cut_decl FrontierAssemblyContracts.trace_nondiscrete_none
#audit_cut_decl FrontierAssemblyContracts.trace_restoration_none
#audit_cut_decl FrontierAssemblyContracts.trace_incomplete_coverage_none
#audit_cut_decl FrontierAssemblyContracts.trace_complete_branch
#audit_cut_decl FrontierAssemblyContracts.literal_public_program


/- Actual execution contract: gh. -/
section GHContracts8

set_option autoImplicit false

open CutQueryComplexity CutQueryComplexity.GHReduction
open CutQueryComplexity.Probability CutQueryComplexity.WeightedGraph
open CutQueryComplexity.GHReduction.OuterPivot
open scoped Classical ENNReal BigOperators

namespace GH214Contract
noncomputable section

-- Exact output/count coupling for the actual truncation constructor.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem truncateRunLaw {I A O : Type} {q : ℕ} (T : RTree I A O q)
    (k : ℕ) (read : I → A) :
    RTree.run read (T.truncate k) = (RTree.run read T).map
      (fun p => (if p.2 ≤ k then some p.1 else none, min p.2 k)) := by
  induction q generalizing k with
  | zero =>
    simp [RTree.truncate, RTree.run_pure, RTree.run, PMF.map_comp, Function.comp_def]
  | succ q ih =>
    cases k with
    | zero =>
      simp only [RTree.truncate, RTree.run, PMF.map_comp, PMF.map_bind, Function.comp_def]
      rw [PMF.map]
      congr 1
      funext action
      rcases action with o | ⟨i, next⟩
      · simp [PMF.pure_map]
      · simp only [PMF.map_comp, Function.comp_def, Nat.not_succ_le_zero,
          ite_false, Nat.min_zero]
        exact (PMF.map_const (RTree.run read (next (read i))) (none, 0)).symm
    | succ k =>
      simp only [RTree.truncate, RTree.run, PMF.bind_map, PMF.map_bind, Function.comp_def]
      congr 1
      funext action
      rcases action with o | ⟨i, next⟩
      · simp [PMF.pure_map]
      · dsimp only
        rw [ih]
        simp only [PMF.map_comp, Function.comp_def, Nat.add_le_add_iff_right]
        apply congrArg (fun f => (RTree.run read (next (read i))).map f)
        funext p
        apply Prod.ext
        · rfl
        · omega


variable {V : Type} [Fintype V] [DecidableEq V] {M n : ℕ} {Q : ℕ → ℕ}
variable {B : Type} [Fintype B] [DecidableEq B]

theorem frontierHonestJointLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (p : V → B) (hp : Function.Surjective p) (T : RootedTree B) (hvn : Fintype.card V ≤ n)
    (hQ : SizeRegular n Q) (hn : 0 < n) (G : WeightedGraph V) (hG : InputPromise M G) :
    RTree.run G.cut (frontierPivotRoundCapped family n samples trials guideLevels scale exponent levels K p hp T hvn) =
      (RTree.run G.cut (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn)).map
        (fun out => (some out.1, out.2)) := by
  rw [frontierPivotRoundCapped, truncateRunLaw]
  apply PMF.ext
  intro output
  simp only [PMF.map_apply]
  apply tsum_congr
  intro out
  by_cases hout : out ∈ (RTree.run G.cut
      (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn)).support
  · have hcost := frontierPivotRound_cost family hQ hn samples trials guideLevels scale exponent levels
      G K hG p hp T hvn hout
    rw [ite_eq_left hcost, Nat.min_eq_left hcost]
  · have hz : RTree.run G.cut
        (frontierPivotRound family n samples trials guideLevels scale exponent levels K p hp T hvn) out = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hout
    simp only [hz, ite_self]

theorem frontierStateStepRunLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (state : PublicFrontierState V) (read : Finset V → ℝ) :
    RTree.run read (frontierStateStep family n samples trials guideLevels scale exponent levels K hvn state) =
      (RTree.run read (frontierPivotRoundCapped family n samples trials guideLevels scale exponent levels
        K state.block state.onto state.tree hvn)).map
          (fun out => (FrontierRoundRecord.mk state out.1, out.2)) := by
  unfold frontierStateStep frontierRoundBudget
  rw [random_run_map]

theorem frontierStateStepHonestJointLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (state : PublicFrontierState V)
    (hQ : SizeRegular n Q) (hn : 0 < n) (G : WeightedGraph V) (hG : InputPromise M G) :
    RTree.run G.cut (frontierStateStep family n samples trials guideLevels scale exponent levels K hvn state) =
      (RTree.run G.cut (frontierPivotRound family n samples trials guideLevels scale exponent levels
        K state.block state.onto state.tree hvn)).map
          (fun out => (FrontierRoundRecord.mk state (some out.1), out.2)) := by
  rw [frontierStateStepRunLaw,
    frontierHonestJointLaw family samples trials guideLevels scale exponent levels K
      state.block state.onto state.tree hvn hQ hn G hG]
  simp only [PMF.map_comp, Function.comp_def]

-- A joint semantic law with exactly the same dependent next-state recursion.
-- This is an evidence-only description of the implemented run, not a producer assumption.
def frontierExecutionLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (read : Finset V → ℝ) :
    ℕ → PublicFrontierState V → PMF (FrontierTrace V levels × ℕ)
  | 0, state => PMF.pure (⟨state, []⟩, 0)
  | fuel + 1, state =>
      (RTree.run read (frontierStateStep family n samples trials guideLevels scale exponent levels K hvn state)).bind
        (fun first => (frontierExecutionLaw family samples trials guideLevels scale exponent levels
          K hvn read fuel first.1.after).map (fun tail =>
            (⟨tail.1.endState, first.1 :: tail.1.records⟩, first.2 + tail.2)))

theorem frontierExecutionRunLaw (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (fuel : ℕ) (state : PublicFrontierState V) (read : Finset V → ℝ) :
    RTree.run read (frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel state) =
      frontierExecutionLaw family samples trials guideLevels scale exponent levels K hvn read fuel state := by
  induction fuel generalizing state with
  | zero => simp only [frontierExecution, RTree.run_pure, PMF.pure_map, frontierExecutionLaw]
  | succ fuel ih =>
      simp only [frontierExecution, RTree.run_cast, RTree.run_bind, random_run_map,
        PMF.map_comp, Function.comp_def, ih, frontierExecutionLaw]


-- Every prefix state and its actual successor inherit original cut witnesses.
theorem followsGoodWitnesses (G : WeightedGraph V) {levels : ℕ}
    (records : List (FrontierRoundRecord V levels)) :
    ∀ start final, FrontierTrace.Follows start records final → start.Witnessed G →
      (∀ record ∈ records, record.Good G) →
      final.Witnessed G ∧ ∀ record ∈ records,
        record.before.Witnessed G ∧ record.after.Witnessed G := by
  induction records with
  | nil =>
      intro start final hfollow hstart _
      change final = start at hfollow
      subst final
      exact ⟨hstart, by simp⟩
  | cons record rest ih =>
      intro start final hfollow hstart hgood
      obtain ⟨hbefore, hrest⟩ := hfollow
      have hrecord : record.before.Witnessed G := hbefore.symm ▸ hstart
      have hafter := record.after_witnessed G hrecord (hgood record (by simp))
      have htail := ih record.after final hrest hafter
        (fun next hnext => hgood next (List.mem_cons_of_mem _ hnext))
      refine ⟨htail.1, ?_⟩
      intro next hnext
      rcases List.mem_cons.mp hnext with he | hm
      · subst next
        exact ⟨hrecord, hafter⟩
      · exact htail.2 next hm

theorem executedGoodWitnesses (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (fuel : ℕ) (r : V) (read : Finset V → ℝ)
    (G : WeightedGraph V) {trace : FrontierTrace V levels}
    (htrace : trace ∈ ((frontierExecution family n samples trials guideLevels scale exponent levels
      K hvn fuel (initialFrontierState r)).eval read).support) (hgood : trace.Good G) :
    trace.endState.Witnessed G ∧ ∀ record ∈ trace.records,
      record.before.Witnessed G ∧ record.after.Witnessed G ∧
      ∀ b, ∀ v ∈ (record.split b).children,
        IsSTMinCut G v (record.split b).source ((record.split b).shore v) ∧
        (record.split b).value v = G.cut ((record.split b).shore v) := by
  have hs := frontierExecution_support family samples trials guideLevels scale exponent levels
    K hvn fuel (initialFrontierState r) read htrace
  have hw := followsGoodWitnesses G trace.records _ _ hs.2 (initialFrontierState_witnessed G r) hgood
  refine ⟨hw.1, ?_⟩
  intro record hrecord
  exact ⟨(hw.2 record hrecord).1, (hw.2 record hrecord).2,
    fun b => record.split_minCuts G (hw.2 record hrecord).1 (hgood record hrecord) b⟩

-- The exact tracked cardinality belongs to the actual guarded/refined fiber.
theorem actualTrackedFiberCard (state : PublicFrontierState V)
    (splits : Fin state.size → PublicBlockSplit V)
    (hvalid : ∀ b, ValidBlockSplit (fiber state.block b) (splits b))
    (b : Fin state.size) {levels : ℕ}
    (out : SourcePivotOutput (FrontierVertex state.block state.tree b) levels)
    (hpivot : out.pivot ∈ frontierTerminals state.block state.tree b)
    (hform : WellFormed (frontierTerminals state.block state.tree b) out.pivot out.values out.step.batch)
    (hsplit : splits b = checkedFrontierSplit state.block state.onto state.tree b (some out))
    (v : V) (hv : state.block v = b) :
    (fiber (advanceFrontierState state splits hvalid).block
      ((advanceFrontierState state splits hvalid).block v)).card =
      (trackedPivotChild (frontierTerminals state.block state.tree b) out.step
        (frontierMap state.block state.tree b v)).card :=
  advanceFrontierState_tracked_card state splits hvalid b out hpivot hform hsplit v hv

-- A bad prefix kills only this analysis potential; the program still runs.
theorem tracePotentialAppend (G : WeightedGraph V) {levels : ℕ}
    (past : List (FrontierRoundRecord V levels)) (tail : FrontierTrace V levels) (v : V) :
    frontierTracePotential G ⟨tail.endState, past ++ tail.records⟩ v =
      if (∀ record ∈ past, record.Good G) then frontierTracePotential G tail v else 0 := by
  have hg : (⟨tail.endState, past ++ tail.records⟩ : FrontierTrace V levels).Good G ↔
      (∀ record ∈ past, record.Good G) ∧ tail.Good G := by
    simp only [FrontierTrace.Good, List.mem_append, or_imp, forall_and]
  unfold frontierTracePotential
  rw [hg]
  by_cases hp : ∀ record ∈ past, record.Good G
  · by_cases ht : tail.Good G
    · rw [ite_eq_left ⟨hp, ht⟩, ite_eq_left hp, ite_eq_left ht]
    · rw [ite_eq_right (fun h => ht h.2), ite_eq_left hp, ite_eq_right ht]
  · rw [ite_eq_right (fun h => hp h.1), ite_eq_right hp]

-- H can contain the entire preceding query/answer and random history.
-- The future is the actual fresh execution at state h, without conditioning it
-- on later good outcomes. The history distribution and state map are arbitrary.
theorem historyConditionalPotential {H : Type} (historyLaw : PMF H)
    (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (past : H → List (FrontierRoundRecord V levels)) (state : H → PublicFrontierState V) (hlevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (fuel : ℕ) (v : V) :
    expect (historyLaw.bind (fun h =>
      ((frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel (state h)).eval G.cut).map
        (fun tail => (h, tail))))
      (fun result => (frontierTracePotential G
        ⟨result.2.endState, past result.1 ++ result.2.records⟩ v : ℝ≥0∞)) ≤
      contractionRate levels ^ fuel * expect historyLaw
        (fun h => (if (∀ record ∈ past h, record.Good G)
          then (frontierVertexExcess (state h) v : ℝ≥0∞) else 0)) := by
  rw [expect_bind]
  simp only [expect_map, tracePotentialAppend]
  calc
    _ ≤ expect historyLaw (fun h => contractionRate levels ^ fuel *
        (if (∀ record ∈ past h, record.Good G)
          then (frontierVertexExcess (state h) v : ℝ≥0∞) else 0)) := by
      apply expect_mono_on_support
      intro h _
      by_cases hp : ∀ record ∈ past h, record.Good G
      · simpa only [ite_eq_left hp] using frontierExecution_expected_potential family hQ
          samples trials guideLevels scale exponent levels hlevels G K hG hvn fuel (state h) v
      · simp only [ite_eq_right hp, Nat.cast_zero, expect_const, mul_zero, le_refl]
    _ = _ := expect_const_mul _ _ _

-- Witness induction strengthens the same termination event at no extra cost.
theorem goodDiscreteWitnessFailure (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (hQ : SizeRegular n Q) (hn : 0 < n) (hnscale : n ≤ scale)
    (hguideLevels : thresholdLevels n ≤ guideLevels) (hpivotLevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧ K.cut S ≤ (101 / 100 : ℝ) * G.cut S)
    (fuel : ℕ) (r : V) :
    mass ((frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel
      (initialFrontierState r)).eval G.cut)
      (fun trace => ¬(trace.Good G ∧ trace.endState.Discrete ∧ trace.endState.Witnessed G)) ≤
      (fuel : ℝ≥0∞) * ((n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent) +
        (n : ℝ≥0∞) * (contractionRate levels ^ fuel * (n : ℝ≥0∞)) := by
  apply le_trans (mass_mono_on_support _ ?_)
    (frontierExecution_termination_failure family hQ hn hnscale samples trials guideLevels exponent levels
      hguideLevels hpivotLevels G K hG hvn happrox fuel (initialFrontierState r))
  intro trace htrace hbad hterm
  exact hbad ⟨hterm.1, hterm.2, (executedGoodWitnesses family samples trials guideLevels scale exponent
    levels K hvn fuel r G.cut G htrace hterm.1).1⟩

theorem depthFuelGoodDiscreteFailure (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ)
    (hQ : SizeRegular n Q) (hn : 0 < n) (hnscale : n ≤ scale)
    (hguideLevels : thresholdLevels n ≤ guideLevels) (hpivotLevels : thresholdLevels n ≤ levels)
    (G K : WeightedGraph V) (hG : InputPromise M G) (hvn : Fintype.card V ≤ n)
    (happrox : ∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧ K.cut S ≤ (101 / 100 : ℝ) * G.cut S)
    (r : V) (failure : ℝ) (hf : 0 < failure) :
    mass ((frontierExecution family n samples trials guideLevels scale exponent levels K hvn
      (depthFuel levels (n * n) failure) (initialFrontierState r)).eval G.cut)
      (fun trace => ¬(trace.Good G ∧ trace.endState.Discrete ∧ trace.endState.Witnessed G)) ≤
      (depthFuel levels (n * n) failure : ℝ≥0∞) *
        ((n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent) + ENNReal.ofReal failure := by
  let fuel := depthFuel levels (n * n) failure
  let P := (frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel
    (initialFrontierState r)).eval G.cut
  calc
    _ ≤ mass P (fun trace => ¬trace.Good G ∨ (trace.Good G ∧ ¬trace.endState.Discrete)) := by
      apply mass_mono_on_support
      intro trace htrace hbad
      by_cases hg : trace.Good G
      · exact Or.inr ⟨hg, fun hd => hbad ⟨hg, hd,
          (executedGoodWitnesses family samples trials guideLevels scale exponent levels
            K hvn fuel r G.cut G htrace hg).1⟩⟩
      · exact Or.inl hg
    _ ≤ mass P (fun trace => ¬trace.Good G) + mass P (fun trace => trace.Good G ∧ ¬trace.endState.Discrete) :=
      mass_or_le P _ _
    _ ≤ _ := add_le_add
      (frontierExecution_failure_le family hQ hn hnscale samples trials guideLevels exponent levels
        hguideLevels G K hG hvn happrox fuel (initialFrontierState r))
      (frontierExecution_depthFuel family hQ samples trials guideLevels scale exponent levels
        hpivotLevels G K hG hvn (initialFrontierState r) hf)

-- The program is fixed before G. All correctness is proved externally about
-- its actual records; no Witnessed/progress/termination field is supplied.
theorem publicTerminatingExecution (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels : ℕ) (K : WeightedGraph V)
    (hvn : Fintype.card V ≤ n) (fuel : ℕ) (r : V) :
    ∃ P : RTree (Finset V) ℝ (FrontierTrace V levels)
        (fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels),
      P = frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel
        (initialFrontierState r) ∧
      (∀ answer : TranscriptOracle.AnswerPolicy (Finset V) ℝ, ∀ history p,
        p ∈ (TranscriptOracle.run answer P history).support →
          p.2 ≤ fuel * frontierRoundBudget M Q n samples trials guideLevels scale exponent levels) ∧
      (∀ read : Finset V → ℝ, RTree.run read P =
        frontierExecutionLaw family samples trials guideLevels scale exponent levels K hvn read fuel
          (initialFrontierState r)) ∧
      (∀ read : Finset V → ℝ, ∀ trace ∈ (P.eval read).support,
        trace.records.length = fuel ∧ FrontierTrace.Follows (initialFrontierState r) trace.records trace.endState) ∧
      (∀ G : WeightedGraph V, ∀ trace ∈ (P.eval G.cut).support, trace.Good G →
        trace.endState.Witnessed G ∧ ∀ record ∈ trace.records,
          record.before.Witnessed G ∧ record.after.Witnessed G ∧
          ∀ b, ∀ v ∈ (record.split b).children,
            IsSTMinCut G v (record.split b).source ((record.split b).shore v) ∧
            (record.split b).value v = G.cut ((record.split b).shore v)) ∧
      (SizeRegular n Q → 0 < n → n ≤ scale → thresholdLevels n ≤ guideLevels →
        thresholdLevels n ≤ levels → ∀ G : WeightedGraph V, InputPromise M G →
          (∀ S, (99 / 100 : ℝ) * G.cut S ≤ K.cut S ∧ K.cut S ≤ (101 / 100 : ℝ) * G.cut S) →
          mass (P.eval G.cut) (fun trace => ¬(trace.Good G ∧ trace.endState.Discrete ∧ trace.endState.Witnessed G)) ≤
            (fuel : ℝ≥0∞) * ((n : ℝ≥0∞) * singleSourceError M n samples trials scale exponent) +
              (n : ℝ≥0∞) * (contractionRate levels ^ fuel * (n : ℝ≥0∞))) := by
  refine ⟨frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel
    (initialFrontierState r), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun answer history p hp => TranscriptOracle.cost_le _ answer history hp
  · exact frontierExecutionRunLaw family samples trials guideLevels scale exponent levels K hvn fuel
      (initialFrontierState r)
  · exact fun read trace htrace => frontierExecution_support family samples trials guideLevels scale exponent levels
      K hvn fuel (initialFrontierState r) read htrace
  · exact fun G trace htrace hgood => executedGoodWitnesses family samples trials guideLevels scale exponent
      levels K hvn fuel r G.cut G htrace hgood
  · exact fun hQ hn hnscale hg hp G hG happrox => goodDiscreteWitnessFailure family samples trials guideLevels scale exponent levels
      hQ hn hnscale hg hp G K hG hvn happrox fuel r

end
end GH214Contract




end GHContracts8


/- Actual execution contract: quantum-neighbors. -/
section QuantumNeighborsContracts7

/-! Literal single-round contracts. Successful joins are derived from the
original child certificates, exact fibers, cut/value and compatibility premises.
This does not provide their executed-history induction or prove termination. -/

set_option autoImplicit false

namespace RoundForestContracts
open CutQueryComplexity CutQueryComplexity.GHReduction CutQueryComplexity.WeightedGraph
open scoped Classical
noncomputable section

variable {V B : Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]

theorem literal_leaf_compatible (state : PublicFrontierState V) :
    ∃ P : DTree (Finset V) ℝ (FrontierForest state) 0,
      P = DTree.pure (leafFrontierForest state) ∧
      (∀ read, P.run read = (leafFrontierForest state, 0)) ∧
      ForestCompatible state.block state.tree (leafFrontierForest state) :=
  ⟨DTree.pure (leafFrontierForest state), rfl, fun _ => rfl,
    leafFrontierForest_compatible state⟩

theorem literal_child_lookup (I : B → Finset V)
    (forest : RoundBlock I → PackedSteinerTree V) (b : B) (i : V) :
    (∀ hi : i ∈ I b, roundForestChild I forest b i = forest ⟨b, some ⟨i, hi⟩⟩) ∧
      (i ∉ I b → roundForestChild I forest b i = forest ⟨b, none⟩) := by
  constructor
  · intro hi
    simp only [roundForestChild, hi, dite_true]
  · intro hi
    simp only [roundForestChild, hi, dite_false]

variable {levels : ℕ}

theorem literal_record_child (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) (b : Fin record.before.size) (i : V) :
    roundForestChild (fun b => (record.split b).children)
      (fun z => forest (frontierRoundLabel record z)) b i =
      frontierRoundChild record forest b i := rfl

theorem literal_record_block (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) (b : Fin record.before.size) :
    roundForestAssemble record.split (fun z => forest (frontierRoundLabel record z)) b =
      assembleFrontierBlock record forest b := rfl

theorem actual_record_compatibility (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after)
    (h : ForestCompatible record.after.block record.after.tree forest) :
    ForestCompatible
      (roundBlockMap record.before.block (fun b => (record.split b).children)
        (fun b => (record.split b).shore))
      (roundBlockTree record.before.tree (fun b => (record.split b).children)
        (roundSplitAttachment record.before.block record.before.onto
          (fun b => (record.split b).children) (fun b => (record.split b).shore)))
      (fun z => forest (frontierRoundLabel record z)) :=
  ForestCompatible.unrelabel _ _ (Fintype.equivFin _) forest h

/-- The accepted public finite fold, with the exact residual, child lookup,
shore list and recorded values used by roundForestAssemble. -/
def roundProgram (splits : B → PublicBlockSplit V)
    (forest : RoundBlock (fun b => (splits b).children) → PackedSteinerTree V) (b : B) :
    Prog (Finset V) ℝ (Option (PackedSteinerTree V)) :=
  assembleSteinerProgram (forest ⟨b, none⟩)
    (starAssemblySteps (splits b).source
      (roundForestChild (fun b => (splits b).children) forest b)
      (splits b).shore (splits b).value (splits b).children.toList)

theorem literal_round_program (splits : B → PublicBlockSplit V)
    (forest : RoundBlock (fun b => (splits b).children) → PackedSteinerTree V) :
    ∃ P : B → Prog (Finset V) ℝ (Option (PackedSteinerTree V)),
      P = roundProgram splits forest ∧
      (∀ b read, Prog.run read (P b) = (roundForestAssemble splits forest b, 0)) ∧
      (∀ b read, ((P b).toDTree 0).run read =
        (some (roundForestAssemble splits forest b), 0)) :=
  ⟨roundProgram splits forest, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Public bottleneck selection in the returned tree, lifted by its actual
attachment map. It has no hidden graph or minimum-cut witness input. -/
def packedAnswer (out : PackedSteinerTree V) (s t : V) : Finset V × ℝ :=
  let u := out.value.attach s
  let v := out.value.attach t
  let e := minimumPathEdge out.value.tree u v
  (steinerPathShore out.value u e, out.value.tree.weight e)

theorem packedAnswer_correct (out : PackedSteinerTree V) (s t : V)
    (hs : Represents out s) (ht : Represents out t) (hst : s ≠ t)
    (G : WeightedGraph V) (hT : IsSteinerCutTree G out.value) :
    IsSTMinCut G s t (packedAnswer out s t).1 ∧
      G.cut (packedAnswer out s t).1 = (packedAnswer out s t).2 := by
  rcases hs with ⟨u, rfl⟩
  rcases ht with ⟨v, rfl⟩
  have huv : u ≠ v := fun he => hst (congrArg out.value.terminal he)
  let e := minimumPathEdge out.value.tree u v
  obtain ⟨he, hleast⟩ := minimumPathEdge_spec out.value.tree huv
  have he0 := ((mem_pathEdges out.value.tree.topology u v e).mp he).1
  have hweight : G.cut (steinerPathShore out.value u e) = out.value.tree.weight e := by
    rw [cut_steinerPathShore]
    exact (hT e he0).2.symm
  simp only [packedAnswer, out.value.attach_terminal]
  change IsSTMinCut G (out.value.terminal u) (out.value.terminal v)
    (steinerPathShore out.value u e) ∧
    G.cut (steinerPathShore out.value u e) = out.value.tree.weight e
  obtain ⟨hs, ht⟩ := steinerPathShore_separates out.value he
  refine ⟨⟨hs, ht, fun S hsS htS => ?_⟩, hweight⟩
  obtain ⟨d, hcross, hpath⟩ := path_crossing out.value.tree.topology
    (S := terminalTrace out.value S) (by simpa only [mem_terminalTrace] using hsS)
    (by simpa only [mem_terminalTrace] using htS)
  rw [hweight]
  exact (hleast d hpath).trans (steiner_weight_le_crossing_cut G out.value hT hcross)

def roundDecoderProgram (splits : B → PublicBlockSplit V)
    (forest : RoundBlock (fun b => (splits b).children) → PackedSteinerTree V)
    (b : B) (s t : V) : Prog (Finset V) ℝ (Option (Finset V × ℝ)) :=
  (roundProgram splits forest b).map (fun out => out.map (fun tree => packedAnswer tree s t))

theorem literal_round_decoder (splits : B → PublicBlockSplit V)
    (forest : RoundBlock (fun b => (splits b).children) → PackedSteinerTree V)
    (b : B) (s t : V) (read : Finset V → ℝ) :
    Prog.run read (roundDecoderProgram splits forest b s t) =
      ((roundForestAssemble splits forest b).map (fun tree => packedAnswer tree s t), 0) ∧
    ((roundDecoderProgram splits forest b s t).toDTree 0).run read =
      (some ((roundForestAssemble splits forest b).map (fun tree => packedAnswer tree s t)), 0) :=
  ⟨rfl, rfl⟩

/-- The same public programs are fixed before G. The some result, every edge's
original shore/value certificate, all old attachment classes and pair decoding
are conclusions from the original structural and semantic premises. -/
theorem literal_round_success (p : V → B) (hp : Function.Surjective p) (T : RootedTree B)
    (splits : B → PublicBlockSplit V)
    (hvalid : ∀ b, ValidBlockSplit (fiber p b) (splits b))
    (hpull : ∀ b i, ∃ A : Finset (FrontierVertex p T b),
      (splits b).shore i = pull (frontierMap p T b) A)
    (forest : RoundBlock (fun b => (splits b).children) → PackedSteinerTree V)
    (hcover : ∀ z x, Represents (forest z) x ↔
      roundBlockMap p (fun b => (splits b).children) (fun b => (splits b).shore) x = z)
    (hcompatible : ForestCompatible
      (roundBlockMap p (fun b => (splits b).children) (fun b => (splits b).shore))
      (roundBlockTree T (fun b => (splits b).children)
        (roundSplitAttachment p hp (fun b => (splits b).children) (fun b => (splits b).shore))) forest) :
    ∃ P : B → Prog (Finset V) ℝ (Option (PackedSteinerTree V)),
    ∃ D : B → V → V → Prog (Finset V) ℝ (Option (Finset V × ℝ)),
      P = roundProgram splits forest ∧ D = roundDecoderProgram splits forest ∧
      (∀ b read, Prog.run read (P b) = (roundForestAssemble splits forest b, 0)) ∧
      (∀ G : WeightedGraph V,
        (∀ b i, i ∈ (splits b).children →
          IsSTMinCut G i (splits b).source ((splits b).shore i) ∧
          (splits b).value i = G.cut ((splits b).shore i)) →
        (∀ z, IsSteinerCutTree G (forest z).value) →
        ∀ b, ∃ out, roundForestAssemble splits forest b = some out ∧
          (∀ read, Prog.run read (P b) = (some out, 0)) ∧
          IsSteinerCutTree G out.value ∧ (∀ x, Represents out x ↔ p x = b) ∧
          (∀ e, e ≠ T.root → ∀ x y,
            ¬(b ∈ T.D e ↔ p x ∈ T.D e) → ¬(b ∈ T.D e ↔ p y ∈ T.D e) →
            out.value.attach x = out.value.attach y) ∧
          (∀ e, e ≠ out.value.tree.topology.root →
            IsSTMinCut G (out.value.terminal e)
              (out.value.terminal (out.value.tree.topology.parent e))
              (pull out.value.attach (out.value.tree.topology.D e)) ∧
            out.value.tree.weight e = G.cut (pull out.value.attach (out.value.tree.topology.D e))) ∧
          (∀ s t, p s = b → p t = b → s ≠ t → ∃ answer,
            (∀ read, Prog.run read (D b s t) = (some answer, 0)) ∧
            IsSTMinCut G s t answer.1 ∧ G.cut answer.1 = answer.2)) := by
  refine ⟨roundProgram splits forest, roundDecoderProgram splits forest, rfl, rfl,
    fun _ _ => rfl, ?_⟩
  intro G hcuts hcorrect b
  obtain ⟨out, hout, hT, hcoverage, hclasses⟩ :=
    roundForestAssemble_success G p hp T splits hvalid hpull hcuts forest hcorrect hcover hcompatible b
  refine ⟨out, hout, ?_, hT, hcoverage, hclasses, hT, ?_⟩
  · intro read
    change (roundForestAssemble splits forest b, 0) = _
    rw [hout]
  · intro s t hs ht hst
    refine ⟨packedAnswer out s t, ?_,
      packedAnswer_correct out s t ((hcoverage s).mpr hs) ((hcoverage t).mpr ht) hst G hT⟩
    intro read
    change ((roundForestAssemble splits forest b).map (fun tree => packedAnswer tree s t), 0) = _
    rw [hout]
    rfl

/-- A single actual record restoration, including its exact Fin relabeling.
Validity and pullbacks come from the checked record, not extra input guards.
Original mincut/value witnesses, child certificates and compatibility remain
explicit; their executed-history production is outside this contract. -/
theorem actual_record_round (record : FrontierRoundRecord V levels)
    (forest : FrontierForest record.after) (G : WeightedGraph V)
    (hcuts : ∀ b i, i ∈ (record.split b).children →
      IsSTMinCut G i (record.split b).source ((record.split b).shore i) ∧
      (record.split b).value i = G.cut ((record.split b).shore i))
    (hcorrect : ∀ b, IsSteinerCutTree G (forest b).value)
    (hcover : ∀ b x, Represents (forest b) x ↔ record.after.block x = b)
    (hcompatible : ForestCompatible record.after.block record.after.tree forest) :
    ∃ out : FrontierForest record.before,
      assembleFrontierRound record forest = some out ∧
      restoreFrontierRecord record ⟨record.after, forest⟩ = some ⟨record.before, out⟩ ∧
      (∀ b, IsSteinerCutTree G (out b).value) ∧
      (∀ b x, Represents (out b) x ↔ record.before.block x = b) ∧
      ForestCompatible record.before.block record.before.tree out := by
  have hpull : ∀ b i, ∃ A : Finset (FrontierVertex record.before.block record.before.tree b),
      (record.split b).shore i = pull (frontierMap record.before.block record.before.tree b) A :=
    fun b i => checkedFrontierSplit_shore_pull _ _ _ b _ i
  have hcover' : ∀ z x, Represents (forest (frontierRoundLabel record z)) x ↔
      roundBlockMap record.before.block (fun b => (record.split b).children)
        (fun b => (record.split b).shore) x = z := by
    intro z x
    rw [hcover]
    change Fintype.equivFin _ (roundBlockMap record.before.block
      (fun b => (record.split b).children) (fun b => (record.split b).shore) x) =
      Fintype.equivFin _ z ↔ _
    exact (Fintype.equivFin _).injective.eq_iff
  have hs := fun b => roundForestAssemble_success G record.before.block record.before.onto
    record.before.tree record.split record.split_valid hpull hcuts
    (fun z => forest (frontierRoundLabel record z)) (fun z => hcorrect _)
    hcover' (actual_record_compatibility record forest hcompatible) b
  choose outputs houtputs htrees hcoverage hclasses using hs
  have hblocks : ∀ b, assembleFrontierBlock record forest b = some (outputs b) := houtputs
  obtain ⟨out, hround, hout⟩ := collectBlockTrees_exists (assembleFrontierBlock record forest)
    (fun b => ⟨outputs b, hblocks b⟩)
  have he : out = outputs := by
    funext b
    exact Option.some.inj ((hout b).symm.trans (hblocks b))
  subst out
  change assembleFrontierRound record forest = some outputs at hround
  refine ⟨outputs, hround, ?_, htrees, hcoverage, ?_⟩
  · simp only [restoreFrontierRecord, dite_true, hround]
    rfl
  · exact hclasses

end
end RoundForestContracts


end QuantumNeighborsContracts7

#audit_cut_decl GH214Contract.truncateRunLaw
#audit_cut_decl GH214Contract.frontierHonestJointLaw
#audit_cut_decl GH214Contract.frontierStateStepRunLaw
#audit_cut_decl GH214Contract.frontierStateStepHonestJointLaw
#audit_cut_decl GH214Contract.frontierExecutionRunLaw
#audit_cut_decl GH214Contract.followsGoodWitnesses
#audit_cut_decl GH214Contract.executedGoodWitnesses
#audit_cut_decl GH214Contract.actualTrackedFiberCard
#audit_cut_decl GH214Contract.tracePotentialAppend
#audit_cut_decl GH214Contract.historyConditionalPotential
#audit_cut_decl GH214Contract.goodDiscreteWitnessFailure
#audit_cut_decl GH214Contract.depthFuelGoodDiscreteFailure
#audit_cut_decl GH214Contract.publicTerminatingExecution
#audit_cut_decl RoundForestContracts.literal_leaf_compatible
#audit_cut_decl RoundForestContracts.literal_child_lookup
#audit_cut_decl RoundForestContracts.literal_record_child
#audit_cut_decl RoundForestContracts.literal_record_block
#audit_cut_decl RoundForestContracts.actual_record_compatibility
#audit_cut_decl RoundForestContracts.literal_round_program
#audit_cut_decl RoundForestContracts.packedAnswer_correct
#audit_cut_decl RoundForestContracts.literal_round_decoder
#audit_cut_decl RoundForestContracts.literal_round_success
#audit_cut_decl RoundForestContracts.actual_record_round


/- Actual execution contract: gh. -/
section GHContracts9

set_option autoImplicit false
open CutQueryComplexity CutQueryComplexity.GHReduction
open CutQueryComplexity.Probability CutQueryComplexity.WeightedGraph
open scoped Classical ENNReal BigOperators

namespace GH215Contract
noncomputable section

attribute [local irreducible] RTree reductionPolynomialConstant confidenceBudget

variable {V : Type} [Fintype V] [DecidableEq V]

-- Exact joint law: the returned execution trace is the assembly input; assembly adds no queries.
theorem frontierAssemblyJointLaw {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (samples trials guideLevels scale exponent levels fuel : ℕ)
    (K : WeightedGraph V) (hvn : Fintype.card V ≤ n) (r : V) (read : Finset V → ℝ) :
    RTree.run read (frontierReduction family n samples trials guideLevels scale exponent levels fuel K hvn r) =
      (RTree.run read (frontierExecution family n samples trials guideLevels scale exponent levels K hvn fuel
        (initialFrontierState r))).map (fun p => (assembleFrontierTrace p.1, p.2)) := by
  simp [frontierReduction, RTree.map, RTree.run_bind, PMF.map, Function.comp_def]

-- This is the executed accepted sparsifier, at the literal one-percent accuracy.
theorem executedSparsifierLaw (confidence : ℝ) (read : Finset V → ℝ) :
    RTree.run read (reductionSparsifier V confidence) =
      RTree.run read (sparsify (paramρ V confidence) (paramc V confidence (1 / 100))
        (paramR V confidence) ⌈2 * paramc V confidence (1 / 100) * (Fintype.card V : ℝ) ^ 2⌉₊
        (capQ V (paramρ V confidence) (paramc V confidence (1 / 100)))) := rfl

-- The actual returned K determines the actual continuation; none preserves the queries already spent.
theorem oracleContinuationJointLaw {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (confidence : ℝ) (samples trials guideLevels scale exponent levels fuel : ℕ)
    (r : V) (read : Finset V → ℝ) :
    RTree.run read (oracleReduction family confidence samples trials guideLevels scale exponent levels fuel r) =
      (RTree.run read (reductionSparsifier V confidence)).bind (fun p =>
        match p.1 with
        | none => PMF.pure (none, p.2)
        | some K => (RTree.run read (frontierReduction family (Fintype.card V) samples trials guideLevels
            scale exponent levels fuel K le_rfl r)).map (fun t => (t.1, p.2 + t.2))) := by
  unfold oracleReduction reductionBudget
  rw [RTree.run_bind]
  congr 1
  funext p
  cases hp : p.1 with
  | none => simp [RTree.run_pure, PMF.pure_map]
  | some K => rfl

-- Public weakening changes neither output nor realized query count.
theorem publicProgramJointLaw {n M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hn : 2 ≤ n) (b : ℕ) (read : Finset (Fin n) → ℝ) :
    RTree.run read (weightedGHProgram family hn b) =
      RTree.run read (oracleReduction family ((b + 3 : ℕ) : ℝ)
        (confidenceSamples M n b) (confidenceTrials M n b) (thresholdLevels n) n
        (confidenceExponent M n b) (thresholdLevels n) (confidenceDepth n b) (⟨0, by omega⟩ : Fin n)) := by
  unfold weightedGHProgram
  rw [RTree.run_weaken]
  unfold confidenceReduction confidenceBudget
  exact congrArg (fun k : ℕ => RTree.run read
    (oracleReduction family ((b + 3 : ℕ) : ℝ)
      (confidenceSamples M k b) (confidenceTrials M k b) (thresholdLevels k) k
      (confidenceExponent M k b) (thresholdLevels k) (confidenceDepth k b)
      (⟨0, by omega⟩ : Fin n))) (Fintype.card_fin n)

-- Total original capacity derives both integral compact graphs and per-edge primitive promises.
theorem compactContractionPromise {B : Type} [Fintype B] [DecidableEq B] {M : ℕ}
    (G : WeightedGraph V) (hintegral : G.IsIntegral) (hmass : G.edgeMass ≤ M) (π : V → B) :
    (G.contract π).IsIntegral ∧ (G.contract π).edgeMass ≤ M ∧
      (∀ u v, (G.contract π).w u v ≤ M) ∧ (∀ S, (G.contract π).cut S ≤ M) := by
  exact ⟨integral_contract G hintegral π, (edgeMass_contract_le G π).trans hmass,
    contract_capacity_bounds G π hmass⟩

-- Success retains every fundamental certificate and a concrete public decoder.
def FullSuccess (G : WeightedGraph V) (output : Option (CutTree V)) : Prop :=
  ∃ tree, output = some tree ∧ IsGomoryHuTree G tree ∧
    (∀ v, v ≠ tree.topology.root →
      IsSTMinCut G v (tree.topology.parent v) (tree.topology.D v) ∧
        tree.weight v = G.cut (tree.topology.D v)) ∧
    (∀ s t : V, s ≠ t →
      minimumPathEdge tree s t ∈ pathEdges tree.topology s t ∧
      (∀ e ∈ pathEdges tree.topology s t, tree.weight (minimumPathEdge tree s t) ≤ tree.weight e) ∧
      IsSTMinCut G s t (cutTreeAnswer tree s t).1 ∧
      G.cut (cutTreeAnswer tree s t).1 = (cutTreeAnswer tree s t).2) ∧
    AllPairsTreeSuccess G output

theorem fullSuccess_of_tree (G : WeightedGraph V) {output : Option (CutTree V)}
    (h : TreeOutputSuccess G output) : FullSuccess G output := by
  obtain ⟨tree, hout, htree⟩ := h
  refine ⟨tree, hout, htree, htree, ?_, ?_⟩
  · intro s t hst
    obtain ⟨hmem, hmin⟩ := minimumPathEdge_spec tree hst
    exact ⟨hmem, hmin, cutTreeAnswer_correct G tree htree hst⟩
  · exact TreeOutputSuccess.allPairs G ⟨tree, hout, htree⟩

-- Every tied least-weight edge works, even at zero; no positivity or uniqueness premise.
theorem anyBottleneckMinShore (G : WeightedGraph V) (tree : CutTree V)
    (htree : IsGomoryHuTree G tree) {s t v : V}
    (hv : v ∈ pathEdges tree.topology s t)
    (hmin : ∀ e ∈ pathEdges tree.topology s t, tree.weight v ≤ tree.weight e) :
    IsSTMinCut G s t (pathShore tree.topology s v) ∧
      G.cut (pathShore tree.topology s v) = tree.weight v :=
  pathShore_minimum_of_bottleneck G tree htree hv hmin

theorem literalFailure {n M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) (G : WeightedGraph (Fin n))
    (hintegral : G.IsIntegral) (hmass : G.edgeMass ≤ M) :
    mass ((weightedGHProgram family hn b).eval G.cut) (fun output => ¬FullSuccess G output) ≤
      (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  apply le_trans (mass_mono _ ?_) (weightedGHProgram_failure family hQ hn b G ⟨hintegral, hmass⟩)
  intro output hbad htree
  exact hbad (fullSuccess_of_tree G htree)

-- Literal quantifier order, exact named implementation, exact logarithmic cap, arbitrary policies,
-- exact fixed-policy output/count law, and the original total-capacity input promise.
theorem publicLiteralEndpoint {n M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (hQ : SizeRegular n Q) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) (weightedGHBudget n M b Q),
      program = weightedGHProgram family hn b ∧
      weightedGHBudget n M b Q =
        parameterCoefficient b ^ 22 * (n + Q n) * (1 + Nat.clog 2 (n + M + 2)) ^ 22 ∧
      (∀ answer : TranscriptOracle.AnswerPolicy (Finset (Fin n)) ℝ, ∀ history out,
        out ∈ (TranscriptOracle.run answer program history).support →
          out.2 ≤ weightedGHBudget n M b Q) ∧
      (∀ read history, TranscriptOracle.run (fun _ i => PMF.pure (read i)) program history =
        RTree.run read program) ∧
      ∀ G : WeightedGraph (Fin n), G.IsIntegral → G.edgeMass ≤ M →
        mass (program.eval G.cut) (fun output => ¬FullSuccess G output) ≤
          (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  have hbudget : weightedGHBudget n M b Q =
      parameterCoefficient b ^ 22 * (n + Q n) * (1 + Nat.clog 2 (n + M + 2)) ^ 22 := by
    unfold weightedGHBudget reductionPolynomialConstant
    rfl
  refine ⟨weightedGHProgram family hn b, rfl, hbudget, ?_, ?_, ?_⟩
  · exact fun answer history out hout => weightedGHProgram_transcript_cost family hn b answer history hout
  · exact fun read history => weightedGHProgram_transcript_fixed family hn b read history
  · exact fun G hi hm => literalFailure family hQ hn b G hi hm

end
end GH215Contract




end GHContracts9

#audit_cut_decl GH215Contract.frontierAssemblyJointLaw
#audit_cut_decl GH215Contract.executedSparsifierLaw
#audit_cut_decl GH215Contract.oracleContinuationJointLaw
#audit_cut_decl GH215Contract.publicProgramJointLaw
#audit_cut_decl GH215Contract.compactContractionPromise
#audit_cut_decl GH215Contract.fullSuccess_of_tree
#audit_cut_decl GH215Contract.anyBottleneckMinShore
#audit_cut_decl GH215Contract.literalFailure
#audit_cut_decl GH215Contract.publicLiteralEndpoint


section CentralContracts

/- A literal contract for the exact executed program and its decoder. -/
set_option autoImplicit false

namespace WeightedGHEndpointContract
noncomputable section
open scoped Classical ENNReal
open CutQueryComplexity CutQueryComplexity.GHReduction
open WeightedGraph Probability

attribute [local irreducible] RTree reductionPolynomialConstant confidenceBudget

theorem public_weighted_gh_endpoint (b : ℕ) :
    ∃ C : ℕ, C = reductionPolynomialConstant b ∧
      ∀ (n M : ℕ) (Q : ℕ → ℕ) (hn : 2 ≤ n) (family : CanonicalSTFamily M Q),
        ∃ q : ℕ, ∃ P : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) q,
          q = C * (n + Q n) * (1 + Nat.clog 2 (n + M + 2)) ^ 22 ∧
          q = weightedGHBudget n M b Q ∧ HEq P (weightedGHProgram family hn b) ∧
          (∀ answer : TranscriptOracle.AnswerPolicy (Finset (Fin n)) ℝ,
            ∀ history out, out ∈ (TranscriptOracle.run answer P history).support → out.2 ≤ q) ∧
          (∀ (read : Finset (Fin n) → ℝ) history,
            TranscriptOracle.run (fun _ S => PMF.pure (read S)) P history = RTree.run read P) ∧
          (∀ G : WeightedGraph (Fin n), G.IsIntegral ∧ G.edgeMass ≤ M → SizeRegular n Q →
            mass (P.eval G.cut) (fun output => ¬∃ tree, output = some tree ∧
              IsGomoryHuTree G tree ∧ ∀ s t : Fin n, s ≠ t →
                minimumPathEdge tree s t ∈ pathEdges tree.topology s t ∧
                (∀ e ∈ pathEdges tree.topology s t,
                  tree.weight (minimumPathEdge tree s t) ≤ tree.weight e) ∧
                s ∈ (cutTreeAnswer tree s t).1 ∧ t ∉ (cutTreeAnswer tree s t).1 ∧
                (∀ S : Finset (Fin n), s ∈ S → t ∉ S →
                  G.cut (cutTreeAnswer tree s t).1 ≤ G.cut S) ∧
                G.cut (cutTreeAnswer tree s t).1 = (cutTreeAnswer tree s t).2 ∧
                ∀ read : Finset (Fin n) → ℝ,
                  (cutTreeAnswerProgram tree s t).run read = (cutTreeAnswer tree s t, 0)) ≤
              (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b) := by
  refine ⟨reductionPolynomialConstant b, rfl, ?_⟩
  intro n M Q hn family
  refine ⟨weightedGHBudget n M b Q, weightedGHProgram family hn b,
    rfl, rfl, HEq.rfl, ?_, ?_, ?_⟩
  · exact fun answer history out hout =>
      weightedGHProgram_transcript_cost family hn b answer history hout
  · exact fun read history => weightedGHProgram_transcript_fixed family hn b read history
  · intro G hG hQ
    apply le_trans (mass_mono _ ?_) (weightedGHProgram_failure family hQ hn b G hG)
    intro output hbad hgood
    obtain ⟨tree, rfl, htree⟩ := hgood
    apply hbad
    refine ⟨tree, rfl, htree, ?_⟩
    intro s t hst
    obtain ⟨hv, hmin⟩ := minimumPathEdge_spec tree hst
    have hanswer := cutTreeAnswer_correct G tree htree hst
    exact ⟨hv, hmin, hanswer.1.1, hanswer.1.2.1, hanswer.1.2.2, hanswer.2,
      fun read => cutTreeAnswerProgram_run tree s t read⟩

end
end WeightedGHEndpointContract


end CentralContracts

#audit_cut_decl WeightedGHEndpointContract.public_weighted_gh_endpoint

/- The Gomory–Hu reduction with a randomized canonical s–t family
(`GHReduction/Randomized/`):
literal restatements of the public endpoints. -/
section RandomizedGH

set_option autoImplicit false
open CutQueryComplexity CutQueryComplexity.GHReduction CutQueryComplexity.GHReduction.Randomized
open CutQueryComplexity.Probability CutQueryComplexity.WeightedGraph
open scoped Classical ENNReal

namespace RandomizedGHEndpoint
noncomputable section

attribute [local irreducible] RTree reductionPolynomialConstant confidenceBudget

-- One public randomized program, then every graph with integral weights of total at most `M`.
-- The family only promises success probability `2/3` on each instance with edge weights `≤ M`.
example {n M : ℕ} {Q : ℕ → ℕ} (family : RandomCanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) (randomizedGHBudget n M b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ randomizedGHBudget n M b Q) ∧
      ∀ G : WeightedGraph (Fin n), G.IsIntegral → G.edgeMass ≤ M →
        mass (program.eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
          2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b := by
  obtain ⟨program, hcost, hfail⟩ := exists_randomized_gh_reduction family hQ hn b
  exact ⟨program, hcost, fun G hi hm => hfail G ⟨hi, hm⟩⟩

-- The budget is the deterministic budget at the amplified cost `r (Q k + k)`.
example (n M b : ℕ) (Q : ℕ → ℕ) :
    randomizedGHBudget n M b Q =
      weightedGHBudget n M b (fun k => amplificationRounds n M b Q * (Q k + k)) := rfl

-- The success probability of a randomized family is `2/3` on every promised instance.
example {M : ℕ} {Q : ℕ → ℕ} (family : RandomCanonicalSTFamily M Q) (k : ℕ) (s t : Fin k)
    (hst : s ≠ t) (G : WeightedGraph (Fin k)) (hint : G.IsIntegral) (hcap : ∀ u v, G.w u v ≤ M) :
    mass ((family.program k s t).eval G.cut) (fun S => ¬IsCanonicalSTCut G s t S) ≤ 1 / 3 :=
  family.correct k s t hst G hint hcap

-- All-pairs minimum cuts of unweighted graphs from a randomized weighted s–t family.
example {n : ℕ} {Q : ℕ → ℕ} (family : RandomCanonicalSTFamily (n * n) Q) (hQ : SizeRegular n Q)
    (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n)))
        (randomizedGHBudget n (n * n) b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support,
        out.2 ≤ randomizedGHBudget n (n * n) b Q) ∧
      ∀ G : WeightedGraph (Fin n), (∀ u v, G.w u v = 0 ∨ G.w u v = 1) →
        mass (program.eval G.cut) (fun output => ¬AllPairsTreeSuccess G output) ≤
          2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b :=
  exists_randomized_unweighted_allPairs family hQ hn b

-- The deterministic reduction, through the call language, keeps its budget and failure.
example {n M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q) (hQ : SizeRegular n Q)
    (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Option (CutTree (Fin n))) (weightedGHBudget n M b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ weightedGHBudget n M b Q) ∧
      ∀ G : WeightedGraph (Fin n), InputPromise M G →
        mass (program.eval G.cut) (fun output => ¬TreeOutputSuccess G output) ≤
          (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b :=
  exists_weighted_gh_reduction_via_calls family hQ hn b

end
end RandomizedGHEndpoint

end RandomizedGH

#audit_cut_decl CutQueryComplexity.GHReduction.Randomized.exists_randomized_gh_reduction
#audit_cut_decl CutQueryComplexity.GHReduction.Randomized.exists_randomized_unweighted_allPairs
#audit_cut_decl CutQueryComplexity.GHReduction.Randomized.exists_weighted_gh_reduction_via_calls

section BoundedFlowMinCut

open CutQueryComplexity.BoundedFlowMinCut

namespace BoundedFlowMinCutEndpoint
noncomputable section

-- One public deterministic program on `Fin n`, fixed before the graph: every run on
-- every oracle (including malformed answers) stays within `queryBudget n`.
example (n : ℕ) (read : Finset (Fin n) → ℝ) : (program n).cost read ≤ queryBudget n :=
  program_cost n read

-- On every unweighted graph (each weight 0 or 1) with at least two vertices, the
-- program returns a global minimum shore together with its exact cut value.
example (n : ℕ) (hn : 2 ≤ n) (G : WeightedGraph (Fin n))
    (hG : ∀ u v, G.w u v = 0 ∨ G.w u v = 1) :
    ∃ out, (program n).eval G.cut = some out ∧
      IsMinCut G out.shore ∧ out.value = G.cut out.shore :=
  program_correct n hn G hG

-- The cap, literally: `n` degree queries, `C n (⌊√n⌋ + 1) L²` for the branches, one
-- final value query, with `L = ⌈log₂ (2n + 2)⌉ + 1` and `C = 83 + 48 · 3^8`.
example (n : ℕ) :
    queryBudget n =
      n + (83 + 48 * 3 ^ 8) * n * (Nat.sqrt n + 1) * (Nat.clog 2 (2 * n + 2) + 1) ^ 2 + 1 :=
  rfl

-- An explicit constant with `queryBudget n ≤ C n^{3/2} L²` for `n ≥ 2`.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    (queryBudget n : ℝ) ≤
      C * (n : ℝ) ^ (3 / 2 : ℝ) * ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 2 :=
  queryBudget_bound

-- `O(n^{3/2} log² n)` cut queries.
example : (fun n : ℕ => (queryBudget n : ℝ)) =O[Filter.atTop]
    (fun n => (n : ℝ) ^ (3 / 2 : ℝ) * (Real.log (n : ℝ)) ^ 2) :=
  queryBudget_isBigO

end
end BoundedFlowMinCutEndpoint

end BoundedFlowMinCut

#audit_cut_decl CutQueryComplexity.BoundedFlowMinCut.program_correct
#audit_cut_decl CutQueryComplexity.BoundedFlowMinCut.program_cost
#audit_cut_decl CutQueryComplexity.BoundedFlowMinCut.queryBudget_bound
#audit_cut_decl CutQueryComplexity.BoundedFlowMinCut.queryBudget_isBigO

section GlobalSTReduction

open CutQueryComplexity.GlobalSTReduction
open CutQueryComplexity.Probability
open scoped ENNReal

namespace GlobalSTReductionEndpoint
noncomputable section

-- A deterministic family on every compact size `Fin k` that returns *some* minimum
-- s-t shore on every real-weighted graph; no canonical answer, no weight promise.
example (Q : ℕ → ℕ) (A : RealSTFamily Q) (k : ℕ) (s t : Fin k) (hst : s ≠ t)
    (G : WeightedGraph (Fin k)) : IsSTMinCut G s t ((A.program k s t).eval G.cut) :=
  A.correct k s t hst G

-- A randomized family misses a minimum shore with probability at most 1/3.
example (Q : ℕ → ℕ) (A : RandomRealSTFamily Q) (k : ℕ) (s t : Fin k) (hst : s ≠ t)
    (G : WeightedGraph (Fin k)) :
    mass ((A.program k s t).eval G.cut) (fun S => ¬IsSTMinCut G s t S) ≤ (1 / 3 : ℝ≥0∞) :=
  A.correct k s t hst G

-- Success: a minimum proper shore with its exact value.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (out : Finset V × ℝ) :
    GlobalSuccess G out ↔ IsMinCut G out.1 ∧ out.2 = G.cut out.1 := Iff.rfl

-- The caps, literally.
example (n b : ℕ) (Q : ℕ → ℕ) :
    detGlobalBudget n b Q =
      1 + 8 * (b + 1) * Nat.clog 2 (n + 2) * (Nat.clog 2 (2 * n) + 1) *
        ((Nat.clog 2 n + 2) * Q n + n) := rfl

example (n b : ℕ) :
    repetitions n b =
      1 + Nat.clog 3 (max 1 (8 * (b + 1) * Nat.clog 2 (n + 2) * (Nat.clog 2 (2 * n) + 1) *
        (Nat.clog 2 n + n)) * (n + 2) ^ b) := rfl

example (n b : ℕ) (Q : ℕ → ℕ) :
    randomGlobalBudget n b Q =
      detGlobalBudget n b (fun k => repetitions n b * (Q k + k)) := rfl

-- Deterministic family: one public program before the graph; every run on every
-- oracle within the cap; every output a proper shore with its exact value; failure
-- at most `(n+2)^{-b}`.
example {n : ℕ} {Q : ℕ → ℕ} (family : RealSTFamily Q)
    (hQ : ∀ s, 1 ≤ s → s ≤ n → n * Q s ≤ s * Q n) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Finset (Fin n) × ℝ) (detGlobalBudget n b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ detGlobalBudget n b Q) ∧
      (∀ G : WeightedGraph (Fin n), ∀ out ∈ (program.eval G.cut).support,
        ProperShore out.1 ∧ out.2 = G.cut out.1) ∧
      ∀ G : WeightedGraph (Fin n),
        mass (program.eval G.cut) (fun out => ¬(IsMinCut G out.1 ∧ out.2 = G.cut out.1)) ≤
          (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b :=
  exists_global_from_st family hQ hn b

-- Randomized family: the same with the amplified cap and failure `2 (n+2)^{-b}`.
example {n : ℕ} {Q : ℕ → ℕ} (family : RandomRealSTFamily Q)
    (hQ : ∀ s, 1 ≤ s → s ≤ n → n * Q s ≤ s * Q n) (hn : 2 ≤ n) (b : ℕ) :
    ∃ program : RTree (Finset (Fin n)) ℝ (Finset (Fin n) × ℝ) (randomGlobalBudget n b Q),
      (∀ read, ∀ out ∈ (RTree.run read program).support, out.2 ≤ randomGlobalBudget n b Q) ∧
      (∀ G : WeightedGraph (Fin n), ∀ out ∈ (program.eval G.cut).support,
        ProperShore out.1 ∧ out.2 = G.cut out.1) ∧
      ∀ G : WeightedGraph (Fin n),
        mass (program.eval G.cut) (fun out => ¬(IsMinCut G out.1 ∧ out.2 = G.cut out.1)) ≤
          2 * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b :=
  exists_global_from_randomized_st family hQ hn b

-- Explicit sizes for `n ≥ 2`, with `ℓ = ⌈log₂(n+2)⌉`.
example {n : ℕ} (hn : 2 ≤ n) (b : ℕ) (Q : ℕ → ℕ) :
    detGlobalBudget n b Q ≤
      32 * (b + 1) * (Q n * Nat.clog 2 (n + 2) ^ 3 + n * Nat.clog 2 (n + 2) ^ 2) :=
  detGlobalBudget_le hn b Q

example {n : ℕ} (hn : 2 ≤ n) (b : ℕ) (Q : ℕ → ℕ) :
    randomGlobalBudget n b Q ≤
      32 * (b + 1) * (Nat.clog 2 (32 * (b + 1)) + b + 5) * (Q n + n) *
        Nat.clog 2 (n + 2) ^ 4 :=
  randomGlobalBudget_le hn b Q

-- `O(Q(n) log³ n + n log² n)` and `O((Q(n) + n) log⁴ n)` for fixed `b`.
example (b : ℕ) (Q : ℕ → ℕ) :
    (fun n : ℕ => (detGlobalBudget n b Q : ℝ)) =O[Filter.atTop]
      (fun n => (Q n : ℝ) * Real.log (n : ℝ) ^ 3 + (n : ℝ) * Real.log (n : ℝ) ^ 2) :=
  detGlobalBudget_isBigO b Q

example (b : ℕ) (Q : ℕ → ℕ) :
    (fun n : ℕ => (randomGlobalBudget n b Q : ℝ)) =O[Filter.atTop]
      (fun n => ((Q n : ℝ) + n) * Real.log (n : ℝ) ^ 4) :=
  randomGlobalBudget_isBigO b Q

-- The interface admits non-canonical answers: the reconstruction family returns
-- `{0, 2}`, not the canonical `{0}`, on the edgeless graph on `Fin 3`.
example : ¬GHReduction.IsCanonicalSTCut (0 : WeightedGraph (Fin 3)) 0 1
    ((reconstructionFamily.program 3 0 1).eval (0 : WeightedGraph (Fin 3)).cut) :=
  reconstructionFamily_not_canonical

-- Degenerate size: the endpoint applies at `n = 2`.
example (b : ℕ) :
    ∃ program : RTree (Finset (Fin 2)) ℝ (Finset (Fin 2) × ℝ)
        (detGlobalBudget 2 b (fun k => k ^ 2)),
      (∀ read, ∀ out ∈ (RTree.run read program).support,
        out.2 ≤ detGlobalBudget 2 b (fun k => k ^ 2)) ∧
      (∀ G : WeightedGraph (Fin 2), ∀ out ∈ (program.eval G.cut).support, ValidOutput G out) ∧
      ∀ G : WeightedGraph (Fin 2),
        mass (program.eval G.cut) (fun out => ¬GlobalSuccess G out) ≤ (((2 + 2 : ℕ) : ℝ≥0∞)⁻¹) ^ b :=
  exists_global_reconstruction le_rfl b

end
end GlobalSTReductionEndpoint

end GlobalSTReduction

#audit_cut_decl CutQueryComplexity.GlobalSTReduction.exists_global_from_st
#audit_cut_decl CutQueryComplexity.GlobalSTReduction.exists_global_from_randomized_st
#audit_cut_decl CutQueryComplexity.GlobalSTReduction.detGlobalBudget_isBigO
#audit_cut_decl CutQueryComplexity.GlobalSTReduction.randomGlobalBudget_isBigO
#audit_cut_decl CutQueryComplexity.GlobalSTReduction.exists_global_reconstruction

/-! Theorem 5: a learned explicit tree of a safe quotient, with all-cut quality. -/

example :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * (Real.log (2 * (n : ℝ)))^4 ≤ α → α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) * (Real.log (2 * (n : ℝ)))^5 ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (TreeCutSparsifier.Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), 0 < mincutValue G →
          ∃ out, D.eval G.cut = some out ∧ TreeCutSparsifier.Correct G α out :=
  TreeCutSparsifier.theorem5

example {V : Type} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {α : ℝ} {out : TreeCutSparsifier.Output V}
    (h : TreeCutSparsifier.Correct G α out) : out.data.tree.m ≤ 8 * Fintype.card V :=
  h.size

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) {r : V → V} (hs : DetMinCut.SafePartition G r) :
    2 ≤ Fintype.card (DetMinCut.Cls r) ∧
      mincutValue (DetMinCut.quot G r) = mincutValue G :=
  ⟨TreeCutSparsifier.safePartition_two_le_card G hn hs,
    TreeCutSparsifier.safePartition_mincutValue G hn hs⟩

/-! Positive-support forest and connectivity test (paper 1, `lem:forest`). -/

section SupportForestEndpoint
open SupportForest

-- The budget is explicit and `O(n log(2n))`.
example (n : ℕ) : forestBudget n = n + 2 * n + 4 * n * Nat.clog 2 n := rfl

example (n : ℕ) : forestBudget n ≤ 7 * n * DetMinCut.logL n :=
  forestBudget_le_linear_log n

-- One decision tree per `n` learns a maximal spanning forest of the positive support of
-- every nonnegative real-weighted graph on `Fin n`.
example (n : ℕ) :
    ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) (forestBudget n),
      (∀ read, D.cost read ≤ forestBudget n) ∧
      ∀ G : WeightedGraph (Fin n), ∃ out, D.eval G.cut = some out ∧ Correct G out :=
  exists_support_forest n

-- The correctness predicate, spelled out.
example {V : Type} [Fintype V] [DecidableEq V] {G : WeightedGraph V} {out : Output V}
    (h : Correct G out) :
    (∀ u v, out.r u = out.r v ↔ G.support.Reachable u v) ∧
    (∀ e ∈ out.edges, 0 < G.w e.1 e.2.1 ∧ e.2.2 = G.w e.1 e.2.1) ∧
    (edgeGraph out.edges).IsAcyclic ∧
    (∀ u v, G.support.Reachable u v ↔ (edgeGraph out.edges).Reachable u v) ∧
    IsSpanningForest G (edgeGraph out.edges) :=
  ⟨h.fiber_iff, h.edges_pos, h.forest, h.spanning, h.isSpanningForest⟩

-- Connectivity test: `none` when the support is connected, otherwise a zero proper shore.
example (n : ℕ) (hn : 2 ≤ n) :
    ∃ D : DTree (Finset (Fin n)) ℝ (Option (Option (Finset (Fin n)))) (forestBudget n),
      ∀ G : WeightedGraph (Fin n),
        (G.support.Connected → D.eval G.cut = some none) ∧
        (¬ G.support.Connected → ∃ S, D.eval G.cut = some (some S) ∧
            ProperShore S ∧ G.cut S = 0) :=
  exists_connectivity_test n hn

-- Connected support is the same as a positive minimum-cut value; a zero proper shore is a
-- minimum cut of value zero.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) : G.support.Connected ↔ 0 < mincutValue G :=
  support_connected_iff_pos G hn

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) {S : Finset V}
    (hS : ProperShore S) (h0 : G.cut S = 0) : IsMinCut G S ∧ mincutValue G = 0 :=
  isMinCut_of_cut_eq_zero G hS h0

-- Theorem 5 without the positivity promise: a zero proper shore or a sparsifier output.
example :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * (Real.log (2 * (n : ℝ)))^4 ≤ α → α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) * (Real.log (2 * (n : ℝ)))^5 ∧
      ∃ D : DTree (Finset (Fin n)) ℝ
          (Option (Finset (Fin n) ⊕ TreeCutSparsifier.Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), ∃ res, D.eval G.cut = some res ∧
          Sum.elim (fun S => ProperShore S ∧ G.cut S = 0) (TreeCutSparsifier.Correct G α) res :=
  TreeCutSparsifier.theorem5_or_zero_cut

end SupportForestEndpoint

#audit_cut_decl CutQueryComplexity.SupportForest.exists_support_forest
#audit_cut_decl CutQueryComplexity.SupportForest.exists_connectivity_test
#audit_cut_decl CutQueryComplexity.SupportForest.support_connected_iff_pos
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.theorem5_or_zero_cut

/-! Canonicalization of an explicit tree cut sparsifier, and the conversion theorem. -/

section CanonicalizationEndpoint
open Hierarchy TreeCutSparsifier

-- The input promise is only the two-sided approximation, with any terminal locations.
example {V : Type} [Fintype V] [DecidableEq V] (input : TreeData V) (G : WeightedGraph V)
    (B : ℝ) : input.Approximates G B ↔
      ∀ S, G.cut S ≤ input.tree.H.rep input.cap S ∧ input.tree.H.rep input.cap S ≤ B * G.cut S :=
  Iff.rfl

-- Normalization keeps every representation cost between the cut and the old cost, assuming
-- only cut domination (no positive minimum cut, no upper bound).
example {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (input : TreeData V)
    (G : WeightedGraph V) (hdom : ∀ S, G.cut S ≤ input.tree.H.rep input.cap S) (S : Finset V) :
    G.cut S ≤ (normalTopology input.tree).H.rep ((normalTopology input.tree).H.canon G) S ∧
      (normalTopology input.tree).H.rep ((normalTopology input.tree).H.canon G) S ≤
        input.tree.H.rep input.cap S :=
  input.normalTopology_rep_le G hdom S

-- The structural guarantees of the normalized topology.
example {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (P : Pkg V) :
    (normalTopology P).m ≤ 2 * Fintype.card V - 1 ∧ (normalTopology P).H.LeafChildless ∧
    (∀ x, (normalTopology P).H.children x = ∅ → (normalTopology P).H.IsLeaf x) ∧
    (∀ x, ¬ (normalTopology P).H.IsLeaf x → 2 ≤ ((normalTopology P).H.children x).card) ∧
    (∀ v, (normalTopology P).H.cluster ((normalTopology P).H.leaf v) = {v}) ∧
    (∀ x, (P.H.cluster x).Nonempty → ∃ y, (normalTopology P).H.cluster y = P.H.cluster x) :=
  let h := normalTopology_normal P
  ⟨h.size, h.leaves, h.childless_isLeaf, h.branching, h.singleton,
    fun x hx => normalTopology_cluster_of_nonempty P hx⟩

-- The public endpoint: topology and decision tree selected before the graph, cap `2n − 2`.
example (n : ℕ) (hn : 1 ≤ n) (input : TreeData (Fin n)) :
    ∃ (P : Pkg (Fin n)) (D : DTree (Finset (Fin n)) ℝ (Option (TreeData (Fin n))) (2 * n - 2)),
      P.Normal ∧
      (∀ x, (input.tree.H.cluster x).Nonempty → ∃ y, P.H.cluster y = input.tree.H.cluster x) ∧
      (∀ read, D.cost read ≤ 2 * n - 2) ∧
      ∀ (G : WeightedGraph (Fin n)) (B : ℝ), input.Approximates G B →
        ∃ out, D.eval G.cut = some out ∧ out.tree = P ∧ out.cap = out.tree.H.canon G ∧
          out.Good G B ∧ ∀ S, out.tree.H.rep out.cap S ≤ input.tree.H.rep input.cap S :=
  exists_canonicalization n hn input

-- Compatibility: a `Good` output is normalized without loss.
example {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (input : TreeData V)
    (G : WeightedGraph V) {α : ℝ} (h : input.Good G α) :
    ((canonicalize input).eval G.cut).tree.Normal ∧ ((canonicalize input).eval G.cut).Good G α :=
  ⟨(canonicalize_good input G h).1, (canonicalize_good input G h).2.1⟩

-- The conversion theorem: `O(n B L(n)⁵)` and `O(n B log⁵(2n))` for an arbitrary input tree.
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B * (DetMinCut.logL n : ℝ) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ TwoRespecting.IsWeakSkeleton G F :=
  exists_conversion

example :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B * (Real.log (2 * (n : ℝ))) ^ 5 ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ TwoRespecting.IsWeakSkeleton G F :=
  exists_conversion_log

/-! Small structural cases. -/

-- One terminal: no query. Two terminals: at most two queries and three nodes.
example (input : TreeData (Fin 1)) (read : Finset (Fin 1) → ℝ) :
    (canonicalize input).cost read = 0 := by
  have := canonicalize_cost input read
  simpa using this

example (input : TreeData (Fin 2)) (read : Finset (Fin 2) → ℝ) :
    (canonicalize input).cost read ≤ 2 ∧ (normalTopology input.tree).m ≤ 3 :=
  ⟨by simpa using canonicalize_cost input read,
    by simpa using (normalTopology_normal input.tree).size⟩

-- A terminal at the root: the two-node tree `1 → 0` with terminal `0` at the root, terminal `1`
-- at the other node, and zero capacities, is an accepted input.
def rootTerminalTree : TwoRespecting.RootedTree (Fin 2) where
  root := 0
  parent _ := 0
  depth i := i.val
  parent_root := rfl
  depth_root := rfl
  depth_parent v hv := by
    fin_cases v
    · exact absurd rfl hv
    · rfl

def rootTerminalInput : TreeData (Fin 2) :=
  ⟨⟨2, ⟨rootTerminalTree, id, fun _ _ h => h⟩⟩, fun _ => 0, fun _ => le_rfl⟩

example : ∃ (P : Pkg (Fin 2)) (D : DTree (Finset (Fin 2)) ℝ (Option (TreeData (Fin 2))) (2 * 2 - 2)),
      P.Normal ∧ (∀ read, D.cost read ≤ 2 * 2 - 2) ∧
      ∀ (G : WeightedGraph (Fin 2)) (B : ℝ), rootTerminalInput.Approximates G B →
        ∃ out, D.eval G.cut = some out ∧ out.tree = P ∧ out.Good G B := by
  obtain ⟨P, D, hN, -, hc, hG⟩ := exists_canonicalization 2 (by norm_num) rootTerminalInput
  refine ⟨P, D, hN, hc, fun G B h => ?_⟩
  obtain ⟨out, he, ht, -, hg, -⟩ := hG G B h
  exact ⟨out, he, ht, hg⟩

-- Arbitrary (possibly negative or inconsistent) answers: the output is well-formed data with
-- nonnegative capacities, and the executed cost obeys the cap.
example {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (input : TreeData V)
    (read : Finset V → ℝ) :
    (∀ x, 0 ≤ ((canonicalize input).eval read).cap x) ∧
      (canonicalize input).cost read ≤ 2 * Fintype.card V - 2 :=
  ⟨((canonicalize input).eval read).cap_nonneg, canonicalize_cost input read⟩

end CanonicalizationEndpoint

#audit_cut_decl CutQueryComplexity.Hierarchy.normalTopology_rep_le
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.exists_canonicalization
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.exists_conversion
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.exists_conversion_log

/-! Offline Räcke–Shah tree cut sparsifiers. -/

section RackeShahEndpoint
open Hierarchy Hierarchy.RackeShah

-- The constant is explicit.
example : rsConstant = 268 := rfl

-- The plan's schematic endpoint, literally.
example :
    ∃ C : ℝ, 1 ≤ C ∧
      HierarchyBound (fun n => C * (DetMinCut.logL n : ℝ) * (DetMinCut.logL (DetMinCut.logL n) : ℝ))
        (fun n => 2 * DetMinCut.logL n) :=
  exists_hierarchyBound_log_mul_loglog

-- With the explicit constant, and `HierarchyBound` unfolded: every finite vertex type, every
-- nonnegative real weighted graph (zero weights and disconnected graphs included), one
-- hierarchy for all shores.
example : ∀ (W : Type) [Fintype W] [DecidableEq W] (J : WeightedGraph W),
    ∃ m : ℕ, ∃ H : Hier W (Fin m), m ≤ 2 * Fintype.card W + 1 ∧ H.LeafChildless ∧
      H.height ≤ 2 * DetMinCut.logL (Fintype.card W) ∧
      ∀ S, H.rep (H.canon J) S ≤
        268 * (DetMinCut.logL (Fintype.card W) : ℝ) * (DetMinCut.logL (DetMinCut.logL (Fintype.card W)) : ℝ) * J.cut S :=
  rackeShah_hierarchyBound

-- The lower bound `c_J(S) ≤ R(S)` holds for every hierarchy with canonical capacities.
example {W : Type} [Fintype W] [DecidableEq W] {m : ℕ} (H : Hier W (Fin m)) (J : WeightedGraph W)
    (S : Finset W) : J.cut S ≤ H.rep (H.canon J) S :=
  H.cut_le_rep J S

-- The empty vertex set and the zero graph are covered by the general statement.
example : ∃ m : ℕ, ∃ H : Hier (Fin 0) (Fin m), m ≤ 2 * Fintype.card (Fin 0) + 1 ∧
    H.LeafChildless ∧ H.height ≤ 2 * DetMinCut.logL (Fintype.card (Fin 0)) ∧
    ∀ S, H.rep (H.canon (0 : WeightedGraph (Fin 0))) S ≤ 268 * (DetMinCut.logL (Fintype.card (Fin 0)) : ℝ) *
      (DetMinCut.logL (DetMinCut.logL (Fintype.card (Fin 0))) : ℝ) * (0 : WeightedGraph (Fin 0)).cut S :=
  rackeShah_hierarchyBound (Fin 0) 0

example (J : WeightedGraph (Fin 3)) : ∃ m : ℕ, ∃ H : Hier (Fin 3) (Fin m), m ≤ 7 ∧
    H.LeafChildless ∧ H.height ≤ 2 * DetMinCut.logL 3 ∧
    ∀ S, H.rep (H.canon J) S ≤ 268 * (DetMinCut.logL 3 : ℝ) * (DetMinCut.logL (DetMinCut.logL 3) : ℝ) * J.cut S :=
  rackeShah_hierarchyBound (Fin 3) J

-- The explicit-tree form for nonempty vertex sets, with `TreeData.Good`.
example {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : WeightedGraph V) :
    ∃ P : Pkg V, P.m ≤ 2 * Fintype.card V + 1 ∧ P.H.LeafChildless ∧
      P.H.height ≤ 2 * DetMinCut.logL (Fintype.card V) ∧
      (TreeCutSparsifier.canonicalTree P G).Good G
        (rsConstant * DetMinCut.logL (Fintype.card V) * DetMinCut.logL (DetMinCut.logL (Fintype.card V))) :=
  TreeCutSparsifier.exists_good_tree_log_mul_loglog G

-- The asymptotic reading of the factor: `O(log n log log n)` in natural logarithms.
example {n : ℕ} (hn : 2 ≤ n) :
    (DetMinCut.logL n : ℝ) * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ≤
      9 * Real.log (2 * (n : ℝ)) * Real.log (6 * Real.log (2 * (n : ℝ))) :=
  TreeCutSparsifier.logL_mul_logL_logL_le hn

-- The quadratic-distortion theorem is unchanged.
example : HierarchyBound (fun n => 1690 * (DetMinCut.logL n : ℝ) ^ 2) (fun n => 4 * DetMinCut.logL n) :=
  exists_hierarchyBound_sq

-- The two local interfaces: the weighted-majority bound and the transfer lemma.
example {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N] (H : Hier V N)
    (hlc : H.LeafChildless) (G : WeightedGraph V) (Q : N → WeightedGraph V)
    (hne : ∀ x, (H.cluster x).Nonempty)
    (hloc : ∀ x, ¬ H.IsLeaf x → Local G (H.cluster x) (childParts H x) (Q x)) (A : Finset V) :
    H.rep (H.canon G) A ≤ 2 * ∑ x, (Q x).cut A :=
  rep_le_two_mul_sum_cut H hlc G Q hne hloc A

-- Bounded transportation: supplies dominated by cuts plus receiving capacities route exactly.
example {V : Type} [Fintype V] [DecidableEq V] (Q : WeightedGraph V) (a z : V → ℝ)
    (ha : ∀ v, 0 ≤ a v) (hz : ∀ v, 0 ≤ z v)
    (h : ∀ U : Finset V, ∑ v ∈ U, a v ≤ Q.cut U + ∑ v ∈ U, z v) :
    ∃ F : V → V → ℝ, ∃ r : V → ℝ, Certificate.Feasible Q F ∧
      (∀ v, Certificate.netOut F v = a v - r v) ∧ ∀ v, 0 ≤ r v ∧ r v ≤ z v :=
  exists_transport Q a z ha hz h

-- The split certificate of a bottleneck lies inside the bottleneck.
example {V : Type} [Fintype V] [DecidableEq V] {G : WeightedGraph V} {f : ℝ} (hf : 0 ≤ f)
    {X U : Finset V} (hb : Bottleneck G f X U) :
    ∃ W ρ, W ⊆ U ∧ W ⊆ X ∧ W.Nonempty ∧ 2 * W.card ≤ X.card ∧ 0 ≤ ρ ∧ ρ * f ≤ 2 ∧
      ∀ Z ⊆ W, G.cross Z (X \ W) ≤ G.cross Z (W \ Z) + ρ * ∑ v ∈ Z, bd G X v := by
  obtain ⟨W, ρ, hWU, hc⟩ := exists_splitCert hf hb
  exact ⟨W, ρ, hWU, hc.subset, hc.nonempty, hc.half, hc.rho_nonneg, hc.rho_small, hc.cutIneq⟩

-- The harmonic product bound with `κ = 64`.
example (n : ℕ) {j : ℕ} (hj : 1 ≤ j) : Bprod n j ≤ 2 := Bprod_le_two n hj
example : kappa = 64 := rfl

end RackeShahEndpoint

#audit_cut_decl CutQueryComplexity.Hierarchy.RackeShah.rackeShah_hierarchyBound
#audit_cut_decl CutQueryComplexity.Hierarchy.RackeShah.exists_hierarchyBound_log_mul_loglog
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.exists_good_tree_log_mul_loglog

/-! The log-log bounds: the Räcke–Shah hierarchy
wired into the deterministic minimum-cut proof, the conversion stage and Theorem 5. -/

section LogLogEndpoint
open Hierarchy Hierarchy.RackeShah TwoRespecting TreeCutSparsifier

-- `K = L ∘ L`, and the log-log cap is below the log-five cap.
example (n : ℕ) : KK n = DetMinCut.logL (DetMinCut.logL n) := rfl

example (n : ℕ) : DetMinCut.logL (DetMinCut.logL n) ≤ DetMinCut.logL n := DetMinCut.KK_le_logL n

example (n : ℕ) :
    (DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2 ≤
      (DetMinCut.logL n : ℝ) ^ 5 := by
  have hK : (DetMinCut.logL (DetMinCut.logL n) : ℝ) ≤ DetMinCut.logL n := by
    exact_mod_cast DetMinCut.KK_le_logL n
  have h3 : (0 : ℝ) ≤ (DetMinCut.logL n : ℝ) ^ 3 := by positivity
  calc (DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2
      ≤ (DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL n : ℝ) ^ 2 := by gcongr
    _ = (DetMinCut.logL n : ℝ) ^ 5 := by ring

-- The unconditional deterministic bound `O(n^{3/2} L(n)³ L(L(n))²)`, with the integer
-- logarithm unfolded.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        (((max 1 (Nat.clog 2 (2 * n)) : ℕ) : ℝ) ^ 3 *
          ((max 1 (Nat.clog 2 (2 * max 1 (Nat.clog 2 (2 * n)))) : ℕ) : ℝ) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
        ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧
          (S.Nonempty ∧ S ≠ Finset.univ) ∧
          ∀ T : Finset (Fin n), (T.Nonempty ∧ T ≠ Finset.univ) → G.cut S ≤ G.cut T := by
  simpa only [DetMinCut.logL, IsMinCut, ProperShore] using
    DetMinCut.deterministic_mincut_log3loglog2

-- The same in the paper's notation: `O(n^{3/2} log³ n (log log n)²)`.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
        ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  DetMinCut.deterministic_mincut_log3loglog2_real_log

-- Conditional on the constant cut guard, for any hierarchy bound of quality `A₀ L K`.
example {a : ℕ → ℝ} {h : ℕ → ℕ} (hb : HierarchyBound a h) (ha : ∀ r, 1 ≤ a r)
    (hma : Monotone a) {A0 ρ0 : ℝ}
    (hA : ∀ r, a r ≤ A0 * (DetMinCut.logL r : ℝ) * (DetMinCut.logL (DetMinCut.logL r) : ℝ))
    (hρ0 : 1 ≤ ρ0) (hcg : Hierarchy.ConstantCutGuard ρ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
          ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  DetMinCut.deterministic_mincut_log3loglog2_fin_of_hierarchyBound_of_constantGuard
    hb ha hma hA hρ0 hcg

-- The Räcke–Shah hierarchy bound is such a hierarchy bound.
example : HierarchyBound
    (fun n => rsConstant * (DetMinCut.logL n : ℝ) * (DetMinCut.logL (DetMinCut.logL n) : ℝ))
    (fun n => 2 * DetMinCut.logL n) :=
  rackeShah_hierarchyBound

-- Shore and value, with a hard cap on every answer function.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        ((DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n) × ℝ)) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), ∃ S,
          D.eval G.cut = some (S, mincutValue G) ∧ IsMinCut G S :=
  UndirectedClosure.deterministic_mincut_shore_value_log3loglog2

-- The conversion stage with a supplied canonical hierarchy.
example : ∃ C : ℝ, 0 < C ∧ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (P : Pkg W) (B : ℝ), 2 ≤ Fintype.card W → 1 ≤ B →
    P.H.LeafChildless → P.m ≤ 2 * Fintype.card W + 1 →
    ∃ q : ℕ, (q : ℝ) ≤ C * Fintype.card W * B *
        ((DetMinCut.logL (Fintype.card W) : ℝ) ^ 3 *
          (DetMinCut.logL (DetMinCut.logL (Fintype.card W)) : ℝ) ^ 2) ∧
      ∃ D : DTree (Finset W) ℝ (Option (WeightedGraph W)) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph W, 0 < mincutValue G →
          (∃ S, IsMinCut G S ∧ P.H.rep (P.H.canon G) S ≤ B * mincutValue G) →
          ∃ F, D.eval G.cut = some F ∧ IsWeakSkeleton G F :=
  UndirectedClosure.supplied_hierarchy_log3loglog2

-- The conversion theorem for an arbitrary explicit input tree.
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B *
          ((DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ IsWeakSkeleton G F :=
  exists_conversion_log3loglog2

example :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B *
          (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ IsWeakSkeleton G F :=
  exists_conversion_log3loglog2_real_log

-- Theorem 5 with the Räcke–Shah quality: the constants and the promise, spelled out.
example : discoveryConstantLL = 54 * 268 * 269 := by norm_num [discoveryConstantLL]

example (n : ℕ) :
    distortionLL n = 268 * (DetMinCut.logL n : ℝ) * (DetMinCut.logL (DetMinCut.logL n) : ℝ) := by
  simp only [distortionLL, rsConstant, KK]

example (n : ℕ) (α : ℝ) : AdmissibleLL n α ↔
    2 * discoveryConstantLL *
      ((DetMinCut.logL n : ℝ) ^ 2 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ≤ α ∧
    α ^ 2 ≤ n :=
  Iff.rfl

example :
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ, AdmissibleLL n α →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) *
          ((DetMinCut.logL n : ℝ)^3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ)^2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), 0 < mincutValue G →
          ∃ out, D.eval G.cut = some out ∧ Correct G α out :=
  learn_tree_cut_sparsifier_LL

example :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * ((Real.log (2 * (n : ℝ)))^2 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ≤ α →
        α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) *
          ((Real.log (2 * (n : ℝ)))^3 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), 0 < mincutValue G →
          ∃ out, D.eval G.cut = some out ∧ Correct G α out :=
  theorem5LL

-- The output contract is the one of `theorem5`: a safe partition and a good tree with at
-- most `8n` nodes.
example {V : Type} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {α : ℝ} {out : Output V} (h : Correct G α out) :
    DetMinCut.SafePartition G out.r ∧ out.data.tree.m ≤ 8 * Fintype.card V :=
  ⟨h.1, h.size⟩

example :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * ((Real.log (2 * (n : ℝ)))^2 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ≤ α →
        α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) *
          ((Real.log (2 * (n : ℝ)))^3 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n) ⊕ Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), ∃ res, D.eval G.cut = some res ∧
          Sum.elim (fun S => ProperShore S ∧ G.cut S = 0) (Correct G α) res :=
  theorem5LL_or_zero_cut

end LogLogEndpoint

section TwoStageEndpoint
open Hierarchy TwoRespecting TreeCutSparsifier SupportForest

-- The two-stage composition (M6): the statement of `deterministic_mincut_log3loglog2`, with
-- the integer logarithm unfolded, reached through Theorem 5 and the conversion theorem.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        (((max 1 (Nat.clog 2 (2 * n)) : ℕ) : ℝ) ^ 3 *
          ((max 1 (Nat.clog 2 (2 * max 1 (Nat.clog 2 (2 * n)))) : ℕ) : ℝ) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
        ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧
          (S.Nonempty ∧ S ≠ Finset.univ) ∧
          ∀ T : Finset (Fin n), (T.Nonempty ∧ T ≠ Finset.univ) → G.cut S ≤ G.cut T := by
  simpa only [DetMinCut.logL, IsMinCut, ProperShore] using
    TreeCutSparsifier.deterministic_mincut_two_stage

-- The two routes have literally the same statement.
example : (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        ((DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
        ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S) :=
  TreeCutSparsifier.deterministic_mincut_two_stage

example : (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        ((DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
        ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S) :=
  DetMinCut.deterministic_mincut_log3loglog2

-- The same in the paper's notation.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Finset (Fin n))) q,
        ∀ G : WeightedGraph (Fin n), ∃ S, D.eval G.cut = some S ∧ IsMinCut G S :=
  TreeCutSparsifier.deterministic_mincut_two_stage_real_log

-- The composed program for admissible `α`: forest precheck, Theorem 5, conversion, skeleton
-- search, pull-back; the cap is the sum of the three stage caps.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V] {α : ℝ}
    (hα : 2 * discoveryConstantLL * ((DetMinCut.logL (Fintype.card V) : ℝ) ^ 2 *
        (DetMinCut.logL (DetMinCut.logL (Fintype.card V)) : ℝ) ^ 2) ≤ α ∧ α ^ 2 ≤ Fintype.card V)
    (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) (x₀ : V) :
    IsMinCut G ((twoStage α x₀).eval G.cut) ∧
    ((twoStage α x₀).cost G.cut : ℝ) ≤
      forestBudget (Fintype.card V) + budgetLL (Fintype.card V) α +
        (UndirectedClosure.hierarchyConstantLL * Fintype.card V * α *
          ((DetMinCut.logL (Fintype.card V) : ℝ) ^ 3 *
            (DetMinCut.logL (DetMinCut.logL (Fintype.card V)) : ℝ) ^ 2) +
          DetMinCut.skelBound (Fintype.card V)) :=
  twoStage_spec hα G hn x₀

-- The two-stage program is `SupportForest.program`, then `learnLL` and `convertStage`.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V] (α : ℝ) (x₀ : V) :
    twoStage α x₀ = (SupportForest.program (V := V)).bind fun fo =>
      match fo.test x₀ with
      | some S => Search.Comp.pure S
      | none => (learnLL α).bind (convertStage α) := rfl

-- A minimum cut of a safe quotient pulls back to a minimum cut.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    {r : V → V} (hs : ∀ S, IsMinCut G S → DetMinCut.Sat r S) {T : Finset (DetMinCut.Cls r)}
    (hT : IsMinCut (DetMinCut.quot G r) T) :
    IsMinCut G (WeightedGraph.pull (DetMinCut.proj r) T) :=
  isMinCut_pull_of_safePartition G hn hs hT

end TwoStageEndpoint

#audit_cut_decl CutQueryComplexity.DetMinCut.deterministic_mincut_log3loglog2
#audit_cut_decl CutQueryComplexity.DetMinCut.deterministic_mincut_log3loglog2_real_log
#audit_cut_decl CutQueryComplexity.UndirectedClosure.deterministic_mincut_shore_value_log3loglog2
#audit_cut_decl CutQueryComplexity.UndirectedClosure.supplied_hierarchy_log3loglog2
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.exists_conversion_log3loglog2
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.exists_conversion_log3loglog2_real_log
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.learn_tree_cut_sparsifier_LL
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.theorem5LL
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.theorem5LL_or_zero_cut
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.twoStage_spec
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.deterministic_mincut_two_stage
#audit_cut_decl CutQueryComplexity.TreeCutSparsifier.deterministic_mincut_two_stage_real_log

section AllMinCutsEndpoint
open TwoRespecting AllMinCuts

-- All global minimum cuts, with `Correct`,
-- `IsMinCut`, `ProperShore` and the integer logarithm unfolded: one public tree per `n ≥ 2`,
-- capped on every answer function, whose output on every nonnegative weighted graph is the
-- minimum-cut value and exactly the set of minimum-cut shores.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        (((max 1 (Nat.clog 2 (2 * n)) : ℕ) : ℝ) ^ 3 *
          ((max 1 (Nat.clog 2 (2 * max 1 (Nat.clog 2 (2 * n)))) : ℕ) : ℝ) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (AllMinCuts.Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), ∃ out, D.eval G.cut = some out ∧
          out.value = mincutValue G ∧
          ∀ S : Finset (Fin n), S ∈ out.cuts ↔
            (S.Nonempty ∧ S ≠ Finset.univ) ∧
            ∀ T : Finset (Fin n), (T.Nonempty ∧ T ≠ Finset.univ) → G.cut S ≤ G.cut T := by
  simpa only [DetMinCut.logL, AllMinCuts.Correct, IsMinCut, ProperShore] using
    AllMinCuts.deterministic_all_mincuts_log3loglog2

-- The literal statement of the plan, section 1.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        ((DetMinCut.logL n : ℝ) ^ 3 * (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (AllMinCuts.Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), ∃ out,
          D.eval G.cut = some out ∧ AllMinCuts.Correct G out :=
  AllMinCuts.deterministic_all_mincuts_log3loglog2

-- The same in the paper's notation.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
        (Real.log (2 * (n : ℝ)) ^ 3 * Real.log (6 * Real.log (2 * (n : ℝ))) ^ 2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (AllMinCuts.Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), ∃ out,
          D.eval G.cut = some out ∧ AllMinCuts.Correct G out :=
  AllMinCuts.deterministic_all_mincuts_log3loglog2_real_log

-- `Correct` spelled out.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (out : AllMinCuts.Output V) :
    AllMinCuts.Correct G out ↔
      out.value = mincutValue G ∧ ∀ S : Finset V, S ∈ out.cuts ↔ IsMinCut G S := Iff.rfl

-- The zero graph on `Fin 3`: every correct family has value zero and all `2³ − 2 = 6` proper
-- shores, so the output can be exponentially large.
example (out : AllMinCuts.Output (Fin 3)) (h : AllMinCuts.Correct (0 : WeightedGraph (Fin 3)) out) :
    out.value = 0 ∧ out.cuts.card = 6 := by
  have hzero : ∀ S : Finset (Fin 3), (0 : WeightedGraph (Fin 3)).cut S = 0 := fun S => by
    simp [WeightedGraph.cut]
  have hcuts : out.cuts = properShores (Fin 3) := by
    ext S
    rw [h.2 S, mem_properShores]
    exact ⟨fun hS => hS.1, fun hS => ⟨hS, fun T _ => by rw [hzero, hzero]⟩⟩
  refine ⟨?_, by rw [hcuts]; decide⟩
  rw [h.1]
  exact mincutValue_eq_zero_of_cut_eq_zero _
    (properShore_singleton (0 : Fin 3) (by simp)) (hzero _)

-- A correct family is closed under complements and nonempty for `n ≥ 2`.
example {V : Type} [Fintype V] [DecidableEq V] {G : WeightedGraph V} {out : AllMinCuts.Output V}
    (h : AllMinCuts.Correct G out) {S : Finset V} (hS : S ∈ out.cuts) : Sᶜ ∈ out.cuts :=
  h.compl_mem hS

-- Two equal Monge rows `[0, 1, 0]`: the minima of a row need not form an interval, and the
-- reporter returns all four minimum entries.
example (p : Fin 2 × Fin 3) :
    p ∈ (Search.allMinima [0, 1] [0, 1, 2] (0 : ℝ)).eval
        (Search.entryOracle fun (_ : Fin 2) (j : Fin 3) => if j = 1 then (1 : ℝ) else 0) ↔
      p.2 ≠ 1 := by
  have hR : ([0, 1] : List (Fin 2)).Pairwise (· < ·) := by decide
  have hC : ([0, 1, 2] : List (Fin 3)).Pairwise (· < ·) := by decide
  have hM : Search.IsMonge (fun (_ : Fin 2) (j : Fin 3) => if j = 1 then (1 : ℝ) else 0)
      [0, 1] [0, 1, 2] := by
    intro r _ r' _ c _ c' _ _ _
    exact le_of_eq (add_comm _ _)
  have hlow : ∀ i ∈ ([0, 1] : List (Fin 2)), ∀ j ∈ ([0, 1, 2] : List (Fin 3)),
      (0 : ℝ) ≤ (fun (_ : Fin 2) (j : Fin 3) => if j = 1 then (1 : ℝ) else 0) i j := by
    intro i _ j _
    dsimp only
    split_ifs <;> norm_num
  rw [(Search.allMinima_spec hR hC hM hlow).1 p]
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> simp

-- A level below the whole rectangle is not attained: nothing is reported.
example (p : Fin 2 × Fin 3) :
    p ∉ (Search.allMinima [0, 1] [0, 1, 2] (-1 : ℝ)).eval
        (Search.entryOracle fun (_ : Fin 2) (_ : Fin 3) => (0 : ℝ)) := by
  have hR : ([0, 1] : List (Fin 2)).Pairwise (· < ·) := by decide
  have hC : ([0, 1, 2] : List (Fin 3)).Pairwise (· < ·) := by decide
  have hM : Search.IsMonge (fun (_ : Fin 2) (_ : Fin 3) => (0 : ℝ)) [0, 1] [0, 1, 2] := by
    intro r _ r' _ c _ c' _ _ _
    exact le_refl _
  rw [(Search.allMinima_spec hR hC hM fun _ _ _ _ => by norm_num).1 p]
  simp

-- An empty rectangle costs nothing and reports nothing.
example (M : Fin 2 → Fin 3 → ℝ) (ℓ : ℝ) :
    (Search.allMinima ([] : List (Fin 2)) [0, 1, 2] ℓ).eval (Search.entryOracle M) = [] ∧
      (Search.allMinima ([] : List (Fin 2)) [0, 1, 2] ℓ).cost (Search.entryOracle M) = 0 := by
  simp [Search.allMinima]

-- Weak majority: when two disjoint subtrees both carry exactly half of the mass, both are
-- weak-heavy, so both are ancestors of one of the two returned vertices.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (T : TwoRespecting.RootedTree V)
    {Q A : Type} (o : Q → A) (meas : Finset V → Search.Comp Q A ℝ) {μ : Finset V → ℝ}
    (hμ : IsVertexSum μ) (hD : 0 < μ Finset.univ)
    (hmeas : ∀ X, (meas X).eval o = μ X ∧ (meas X).cost o ≤ 2) {u v : V}
    (hu : 2 * μ (T.subtree u) = μ Finset.univ) (hv : 2 * μ (T.subtree v) = μ Finset.univ) :
    (T.IsAnc u ((weakMajoritySearch T meas (μ Finset.univ)).eval o).1 ∨
        T.IsAnc u ((weakMajoritySearch T meas (μ Finset.univ)).eval o).2) ∧
      (T.IsAnc v ((weakMajoritySearch T meas (μ Finset.univ)).eval o).1 ∨
        T.IsAnc v ((weakMajoritySearch T meas (μ Finset.univ)).eval o).2) :=
  ⟨((weakMajoritySearch_spec o meas hμ hD hmeas).1 u).mp hu.ge,
    ((weakMajoritySearch_spec o meas hμ hD hmeas).1 v).mp hv.ge⟩

-- A two-edge minimum cut that ties a one-edge cut is still reported, together with the one-edge
-- cut: the local report is exact at the level `λ(G)`.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (T : TwoRespecting.RootedTree V)
    (G : WeightedGraph V) (hpos : 0 < mincutValue G) {e f : V} (he : e ≠ T.root)
    (hf : f ≠ T.root) (hef : e ≠ f)
    (h1 : G.cut (T.subtree e) = mincutValue G) (h2 : T.pairCut G e f = mincutValue G) :
    T.subtree e ∈ (allTwoRespecting T (mincutValue G)).eval G.cut ∧
      T.pairShore e f ∈ (allTwoRespecting T (mincutValue G)).eval G.cut :=
  ⟨((allTwoRespecting_spec T G rfl hpos).1 _).mpr ⟨Or.inl ⟨e, he, rfl⟩, h1⟩,
    ((allTwoRespecting_spec T G rfl hpos).1 _).mpr ⟨Or.inr ⟨e, f, he, hf, hef, rfl⟩, h2⟩⟩

-- The reporter at any positive level below every shore crossing one or two tree edges.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (T : TwoRespecting.RootedTree V)
    (G : WeightedGraph V) {ℓ : ℝ} (hlow : ∀ S, T.IsTwoRespShore S → ℓ ≤ G.cut S) (hpos : 0 < ℓ)
    (S : Finset V) :
    S ∈ (allTwoRespecting T ℓ).eval G.cut ↔ T.IsTwoRespShore S ∧ G.cut S = ℓ :=
  allTwoRespecting_correct_of_le G hlow hpos S

-- At the tree's own minimum value: one decision tree returns every shore crossing one or two
-- edges of `T` of least cut; with `0 < λ(G)` there is no further hypothesis on the graph.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (T : TwoRespecting.RootedTree V)
    (hV : ∃ v, v ≠ T.root) :
    ∃ D : DTree (Finset V) ℝ (Option (ℝ × Finset (Finset V)))
        (322 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1)),
      ∀ G : WeightedGraph V, 0 < mincutValue G →
        ∃ out, D.eval G.cut = some out ∧
          ∀ S, S ∈ out.2 ↔ T.IsTwoRespShore S ∧
            ∀ S', T.IsTwoRespShore S' → G.cut S ≤ G.cut S' := by
  obtain ⟨D, hD⟩ := allMinTwoRespecting_queryBound T hV
  refine ⟨D, fun G hlam => ?_⟩
  obtain ⟨out, h1, -, -, h4⟩ := hD G (twoResp_cut_pos_of_mincut_pos G hlam)
  exact ⟨out, h1, h4⟩

-- The reporter on one tree: exact membership at `ℓ = λ(G) > 0`, and the cost bound on every
-- graph and every level.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (T : TwoRespecting.RootedTree V)
    (G : WeightedGraph V) (ℓ : ℝ) :
    (allTwoRespecting T ℓ).cost G.cut ≤ 250 * Fintype.card V * (Nat.clog 2 (Fintype.card V) + 1) :=
  allTwoRespecting_cost G ℓ

-- The skeleton stage: the value is an oracle answer on the shore returned by the existing
-- search, and every tree of the offline cover is searched at that level.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (H : WeightedGraph V) :
    coverReport H = (skeletonMinCut H).bind fun S₀ =>
      (Search.Comp.ask S₀).bind fun ℓ =>
        (Search.Comp.mapList (fun T => allTwoRespecting T ℓ) (coverTrees H)).map fun fams =>
          ⟨unionAll fams ∪ (unionAll fams).image compl, ℓ⟩ := rfl

-- The composed program: forest precheck with the zero family, then Theorem 5 and the positive
-- branch (supplied hierarchy, cover report on the quotient, pull-back).
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V] (α : ℝ) (x₀ : V) :
    allTwoStage α x₀ = (SupportForest.program (V := V)).bind fun fo =>
      match fo.test x₀ with
      | some _ => Search.Comp.pure (zeroOutput fo.r)
      | none => (TreeCutSparsifier.learnLL α).bind (positiveStage α) := rfl

-- The exact quotient correspondence of minimum-cut families.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    {r : V → V} (hs : ∀ S, IsMinCut G S → DetMinCut.Sat r S) (S : Finset V) :
    IsMinCut G S ↔ ∃ T : Finset (DetMinCut.Cls r), IsMinCut (DetMinCut.quot G r) T ∧
      WeightedGraph.pull (DetMinCut.proj r) T = S :=
  isMinCut_iff_exists_quot G hn hs S

end AllMinCutsEndpoint

#audit_cut_decl CutQueryComplexity.Search.allMinima_spec
#audit_cut_decl CutQueryComplexity.TwoRespecting.weakMajoritySearch_spec
#audit_cut_decl CutQueryComplexity.TwoRespecting.allTwoRespecting_spec
#audit_cut_decl CutQueryComplexity.AllMinCuts.isMinCut_iff_exists_quot
#audit_cut_decl CutQueryComplexity.AllMinCuts.suppliedHierarchyProgLL_allMinCuts
#audit_cut_decl CutQueryComplexity.AllMinCuts.coverReport_spec
#audit_cut_decl CutQueryComplexity.AllMinCuts.cut_eq_zero_iff_sat
#audit_cut_decl CutQueryComplexity.AllMinCuts.allTwoStageAuto_spec
#audit_cut_decl CutQueryComplexity.AllMinCuts.deterministic_all_mincuts_log3loglog2
#audit_cut_decl CutQueryComplexity.AllMinCuts.deterministic_all_mincuts_log3loglog2_real_log

section AllMinCutsExtras
open AllMinCuts

-- With a positive minimum cut, every correct family (in particular the output of the
-- deterministic endpoint) has at most `8 (n + n²)` shores.
example {V : Type} [Fintype V] [DecidableEq V] {G : WeightedGraph V} {out : AllMinCuts.Output V}
    (h : AllMinCuts.Correct G out) (hpos : 0 < mincutValue G) :
    out.cuts.card ≤ 8 * (Fintype.card V + Fintype.card V ^ 2) :=
  h.card_cuts_le hpos

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (hpos : 0 < mincutValue G)
    (F : Finset (Finset V)) (hF : ∀ S ∈ F, IsMinCut G S) :
    F.card ≤ 8 * (Fintype.card V + Fintype.card V ^ 2) :=
  card_le_of_isMinCut G hpos F hF

-- All minimum cuts with a randomized sparsifier, with `Correct` unfolded: one public randomized
-- tree per `n` and `s`, every run on every oracle within the cap, failure `(2n+2)^{-s}`.
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ s : ℝ, 0 ≤ s →
    ∃ q : ℕ, (q : ℝ) ≤ C * (s + 8) * n * Real.log (2 * (n : ℝ)) ^ 2 ∧
      ∃ T : RTree (Finset (Fin n)) ℝ (Option (AllMinCuts.Output (Fin n))) q,
        (∀ read : Finset (Fin n) → ℝ, ∀ r ∈ (RTree.run read T).support, r.2 ≤ q) ∧
        ∀ G : WeightedGraph (Fin n),
          Probability.mass (T.eval G.cut) (fun o => ¬∃ out, o = some out ∧
            out.value = mincutValue G ∧ ∀ S : Finset (Fin n), S ∈ out.cuts ↔ IsMinCut G S) ≤
            ENNReal.ofReal ((2 * (n : ℝ) + 2) ^ (-s)) :=
  AllMinCuts.randomized_all_mincuts

-- The randomized program: the library's cut sparsifier at accuracy `1/20`, then the
-- deterministic second stage compiled at the public cap.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (s : ℝ) :
    randomAllMinCuts (V := V) s = (sparsifierAll V s).bind fun oH => match oH with
      | none => RTree.pure (PMF.pure none)
      | some H => RTree.ofDeterministic
          ((reportStage H).toDTree (reportBound (Fintype.card V))) := rfl

-- The second stage, offline on the explicit sparsifier: its zero family, or the cover reporter
-- on the sparsifier rescaled by `20/19`.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (H : WeightedGraph V) :
    reportStage H = if mincutValue H = 0 then Search.Comp.pure (familyOf H)
      else coverReport (H.scale (20 / 19) (by norm_num)) := rfl

-- Any explicit graph within `1 ± 1/20` of every cut suffices for the second stage.
example {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V] (G H : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V)
    (hH : ∀ S, (1 - 1 / 20) * G.cut S ≤ H.cut S ∧ H.cut S ≤ (1 + 1 / 20) * G.cut S) :
    AllMinCuts.Correct G ((reportStage H).eval G.cut) ∧
      (reportStage H).cost G.cut ≤ reportBound (Fintype.card V) :=
  reportStage_spec G H hn hH

end AllMinCutsExtras

#audit_cut_decl CutQueryComplexity.AllMinCuts.card_le_of_isMinCut
#audit_cut_decl CutQueryComplexity.AllMinCuts.Correct.card_cuts_le
#audit_cut_decl CutQueryComplexity.AllMinCuts.randomAllMinCuts_correct
#audit_cut_decl CutQueryComplexity.AllMinCuts.randomized_all_mincuts

section CertificateComplexity
open CutQueryComplexity.Certificate

-- `cert(G)` of the paper, equation (1): the least size of a family of shores whose answers
-- force the minimum-cut value in every nonnegative weighted competitor on the same vertex set.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    certificateComplexity G =
      sInf {m | ∃ Q : Finset (Finset V), Q.card = m ∧
        ∀ G' : WeightedGraph V, (∀ S ∈ Q, G'.cut S = G.cut S) →
          mincutValue G' = mincutValue G} := rfl

-- The minimum is attained.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    ∃ Q : Finset (Finset V), IsMinCutCertificate G Q ∧ Q.card = certificateComplexity G :=
  exists_certificate_card_eq G

-- Theorem 1 as a bound on `cert(G)`: `cert(G) ≤ 18 n ⌈log₂(2n)⌉²` for `n ≥ 2`.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) :
    certificateComplexity G ≤ 18 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 :=
  certificateComplexity_le_bound G hn

example : ∃ C : ℕ, ∀ n (G : WeightedGraph (Fin n)), 2 ≤ n →
    certificateComplexity G ≤ C * n * (Nat.clog 2 (2 * n)) ^ 2 :=
  certificateComplexity_near_linear

-- A zero optimum needs a single shore.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (h0 : mincutValue G = 0) : certificateComplexity G ≤ 1 :=
  certificateComplexity_le_one G hn h0

-- Nonvacuity: no graph on `n ≥ 2` vertices is certified by the empty family.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) : 1 ≤ certificateComplexity G :=
  one_le_certificateComplexity G hn

-- A zero optimum has certificate complexity exactly one.
example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hn : 2 ≤ Fintype.card V) (h0 : mincutValue G = 0) : certificateComplexity G = 1 :=
  certificateComplexity_eq_one G hn h0

-- `cert(G)` lower-bounds deterministic cut-query complexity of the minimum-cut value.
-- Instance-wise: a decision tree whose output on the cut oracle of every nonnegative
-- weighted graph `H` on `V` is `mincutValue H` asks at least `cert(G)` shores on input `G`.
example {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (T : DTree (Finset V) ℝ ℝ q)
    (hT : ∀ H : WeightedGraph V, T.eval H.cut = mincutValue H) (G : WeightedGraph V) :
    certificateComplexity G ≤ T.cost G.cut :=
  certificateComplexity_le_cost hT G

-- The exact deterministic complexity of the value problem, spelled out.
example {V : Type} [Fintype V] [DecidableEq V] :
    minCutValueComplexity V =
      queryComplexity {q | ∃ T : DTree (Finset V) ℝ ℝ q,
        ∀ H : WeightedGraph V, T.eval H.cut = mincutValue H} := rfl

example {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    (certificateComplexity G : WithTop ℕ) ≤ minCutValueComplexity V :=
  certificateComplexity_le_minCutValueComplexity G

-- The `2n − 2` lower bound (Lee, Li, Santha, Zhang): for every `k` the windmill of `k`
-- unit-weight copies of `K₄` sharing a hub, on `n = 3k + 1` vertices, has `cert ≥ 2n − 2`.
example (k : ℕ) : ∃ G : WeightedGraph (Fin (3 * k + 1)),
    2 * (3 * k + 1) - 2 ≤ certificateComplexity G :=
  Windmill.exists_two_mul_sub_two_le_certificateComplexity k

example {k : ℕ} {V : Type} [Fintype V] [DecidableEq V] (φ : Option (Fin k × Fin 3) ≃ V) :
    2 * Fintype.card V - 2 ≤ certificateComplexity (Windmill.windmill φ) :=
  Windmill.two_mul_card_sub_two_le_certificateComplexity φ

-- The windmill has minimum-cut value `3` and its cuts count crossing unit edges.
example {k : ℕ} {V : Type} [Fintype V] [DecidableEq V] (φ : Option (Fin k × Fin 3) ≃ V)
    (hk : 0 < k) : mincutValue (Windmill.windmill φ) = 3 :=
  Windmill.mincutValue_windmill φ hk

example {k : ℕ} {V : Type} [Fintype V] [DecidableEq V] (φ : Option (Fin k × Fin 3) ≃ V)
    (S : Finset V) : (Windmill.windmill φ).cut S = ∑ x, 1 * Windmill.chi φ S x :=
  Windmill.cut_graph φ _ _ S

-- Deterministic cut-query lower bound: every decision tree that outputs the minimum-cut value
-- of every nonnegative weighted graph on `3k + 1` vertices has budget at least `2(3k + 1) − 2`,
-- and the exact deterministic complexity of the value problem is at least that.
example (k q : ℕ) (T : DTree (Finset (Fin (3 * k + 1))) ℝ ℝ q)
    (hT : ∀ H : WeightedGraph (Fin (3 * k + 1)), T.eval H.cut = mincutValue H) :
    2 * (3 * k + 1) - 2 ≤ q :=
  Windmill.two_mul_sub_two_le_budget k hT

example (k : ℕ) :
    ((2 * (3 * k + 1) - 2 : ℕ) : WithTop ℕ) ≤ minCutValueComplexity (Fin (3 * k + 1)) :=
  Windmill.two_mul_sub_two_le_minCutValueComplexity k

-- Shore-output form (the convention of the `deterministic_mincut_*` theorems): one query weaker.
example (k q : ℕ) (T : DTree (Finset (Fin (3 * k + 1))) ℝ (Option (Finset (Fin (3 * k + 1)))) q)
    (hT : ∀ G : WeightedGraph (Fin (3 * k + 1)), ∃ S, T.eval G.cut = some S ∧ IsMinCut G S) :
    2 * (3 * k + 1) - 3 ≤ q :=
  Windmill.two_mul_sub_three_le_shore_budget k hT

end CertificateComplexity

#audit_cut_decl CutQueryComplexity.Certificate.certificateComplexity_le_bound
#audit_cut_decl CutQueryComplexity.Certificate.certificateComplexity_near_linear
#audit_cut_decl CutQueryComplexity.Certificate.certificateComplexity_le_one
#audit_cut_decl CutQueryComplexity.Certificate.exists_certificate_card_eq
#audit_cut_decl CutQueryComplexity.Certificate.one_le_certificateComplexity
#audit_cut_decl CutQueryComplexity.Certificate.certificateComplexity_eq_one
#audit_cut_decl CutQueryComplexity.Certificate.certificateComplexity_le_cost
#audit_cut_decl CutQueryComplexity.Certificate.certificateComplexity_le_minCutValueComplexity
#audit_cut_decl CutQueryComplexity.Certificate.Windmill.exists_two_mul_sub_two_le_certificateComplexity
#audit_cut_decl CutQueryComplexity.Certificate.Windmill.two_mul_card_sub_two_le_certificateComplexity
#audit_cut_decl CutQueryComplexity.Certificate.Windmill.mincutValue_windmill
#audit_cut_decl CutQueryComplexity.Certificate.Windmill.two_mul_sub_two_le_budget
#audit_cut_decl CutQueryComplexity.Certificate.Windmill.two_mul_sub_two_le_minCutValueComplexity
#audit_cut_decl CutQueryComplexity.Certificate.Windmill.two_mul_sub_three_le_shore_budget
