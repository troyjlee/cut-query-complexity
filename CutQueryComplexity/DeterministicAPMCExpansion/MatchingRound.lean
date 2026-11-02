import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.SlotCounts
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.StarCut
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.SharpBudget

/-!
# One literal matching round

The public clone bisection supplies the two terminal capacities. The executed
unit-capacity flow supplies either a strict sparse split or real routes; the
public completion assigns unused clone slots and marks exactly the deficit
as fake pairs. The hidden graph is absent from every program definition.

The coarse bound applies to every transcript. The final theorem also derives
the sharper honest-input bound from the phase-distance analysis. The recursive
caller caps each node before lifting its queries to the ambient graph.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion

open Finset Flow CutMatching Certificate AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {b : ℕ}

inductive MatchingRoundResult (cut : Bisection (Clone V b)) where
  | split : Finset V → MatchingRoundResult cut
  | matched (routes : List (LocatedRoute V)) (pairs : ClonePairing cut routes) :
      MatchingRoundResult cut
  | invalid : MatchingRoundResult cut

def matchingRoundPost (β : ℝ) (cut : Bisection (Clone V b))
    (result : ExactResult V × RouteResult (NetworkVertex V)) : MatchingRoundResult cut :=
  if (eventValue result.1.events : ℝ) + β * b < cut.shore.card then
    .split (originalShore result.1.shore)
  else
    match locateRoutes result.2.routes with
    | none => .invalid
    | some routes =>
        match assignClones cut routes with
        | none => .invalid
        | some pairs => .matched routes pairs

def matchingRound (β : ℝ) (cut : Bisection (Clone V b)) :
    Prog (Finset V) ℝ (MatchingRoundResult cut) :=
  (routedFlowProg 1 (slotCount cut.shore) (slotCount cut.shoreᶜ)).map
    (matchingRoundPost β cut)

def SplitCorrect (G : WeightedGraph V) (b : ℕ) (β : ℝ) (P : Finset V) : Prop :=
  β < (P.card : ℝ) ∧ β < (Pᶜ.card : ℝ) ∧
    G.cut P < (b : ℝ) * min (P.card : ℝ) (Pᶜ.card : ℝ)

structure MatchingRoundCorrect (G : WeightedGraph V) (β : ℝ)
    (cut : Bisection (Clone V b)) (routes : List (LocatedRoute V))
    (pairs : ClonePairing cut routes) : Prop where
  located : ∀ route ∈ routes, LocatedCorrect route
  paths : ∀ route ∈ routes,
    RoutePath (fun u v =>
      0 < (twoStar G (slotCount cut.shore) (slotCount cut.shoreᶜ)).w u v)
      source sink route.nodes
  congestion : ∀ u v,
    ((routeLoad (routes.map LocatedRoute.nodes) (.inl u) (.inl v) +
      routeLoad (routes.map LocatedRoute.nodes) (.inl v) (.inl u) : ℕ) : ℝ) ≤ G.w u v
  fake_count : (pairs.fakeLeft.card : ℝ) ≤ β * b

def RoundCorrect (G : WeightedGraph V) (β : ℝ) (cut : Bisection (Clone V b)) :
    MatchingRoundResult cut → Prop
  | .split P => SplitCorrect G b β P
  | .matched routes pairs => MatchingRoundCorrect G β cut routes pairs
  | .invalid => False

/-- The strict source-capacity deficit forces a large shore on both sides.
Both terminal totals are derived from the public bisection. -/
theorem bisection_deficit_split (G : WeightedGraph V) (β : ℝ) (hβ : 0 ≤ β)
    (hb : 0 < b) (cut : Bisection (Clone V b))
    (A : Finset (NetworkVertex V)) (hs : source ∈ A) (ht : sink ∉ A)
    (hgap : (twoStar G (slotCount cut.shore) (slotCount cut.shoreᶜ)).cut A +
      β * b < cut.shore.card) :
    SplitCorrect G b β (originalShore A) := by
  let P := originalShore A
  have hcut := twoStar_source_cut G (slotCount cut.shore) (slotCount cut.shoreᶜ) A hs ht
  have hsumA := sum_shore_add_compl (fun v => (slotCount cut.shore v : ℝ)) P
  have hsumZ := sum_shore_add_compl (fun v => (slotCount cut.shoreᶜ v : ℝ)) P
  have htotalA : (∑ v, (slotCount cut.shore v : ℝ)) = cut.shore.card := by
    exact_mod_cast (bisection_star_totals cut).1
  have htotalZ : (∑ v, (slotCount cut.shoreᶜ v : ℝ)) = cut.shore.card := by
    exact_mod_cast (bisection_star_totals cut).2
  have ha := slotCount_shore_le_real cut.shore P
  have hz := slotCount_shore_le_real cut.shoreᶜ Pᶜ
  have hnonnegA : 0 ≤ ∑ v ∈ Pᶜ, (slotCount cut.shore v : ℝ) := by positivity
  have hnonnegZ : 0 ≤ ∑ v ∈ P, (slotCount cut.shoreᶜ v : ℝ) := by positivity
  have hleft : G.cut P + β * b < (b : ℝ) * P.card := by linarith
  have hright : G.cut P + β * b < (b : ℝ) * Pᶜ.card := by linarith
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcutNonneg := G.cut_nonneg P
  have hβb : 0 ≤ β * b := mul_nonneg hβ hbR.le
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rcases le_total (P.card : ℝ) (Pᶜ.card : ℝ) with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith

theorem matchingRound_correct (G : WeightedGraph V) (hG : Unweighted G)
    (β : ℝ) (hβ : 0 ≤ β) (hb : 0 < b) (cut : Bisection (Clone V b)) :
    RoundCorrect G β cut ((matchingRound β cut).eval G.cut) := by
  let result := (routedFlowProg 1 (slotCount cut.shore) (slotCount cut.shoreᶜ)).eval G.cut
  obtain ⟨hc, hr⟩ := routedFlowProg_correct G hG 1 (slotCount cut.shore) (slotCount cut.shoreᶜ)
  change ExactCertificate (directed (twoStar (scaledInternal G 1)
    (slotCount cut.shore) (slotCount cut.shoreᶜ))) result.1 at hc
  change RouteSpec result.1.flow source sink (eventValue result.1.events) result.2 at hr
  have hscale : scaledInternal G 1 = G := by
    ext u v
    simp [scaledInternal, WeightedGraph.scale]
  rw [hscale] at hc
  have hhistory := (scaledExactProg_history G hG 1
    (slotCount cut.shore) (slotCount cut.shoreᶜ)).1
  have hvalue : netOut result.1.flow source = (eventValue result.1.events : ℝ) := by
    simpa only [result, routedFlowProg, Prog.eval_map, netOut, sum_const_zero, sub_zero]
      using hhistory.value_difference
  have hshore : (eventValue result.1.events : ℝ) =
      (twoStar G (slotCount cut.shore) (slotCount cut.shoreᶜ)).cut result.1.shore :=
    hvalue.symm.trans hc.value_eq_cut
  simp only [matchingRound, Prog.eval_map]
  change RoundCorrect G β cut (matchingRoundPost β cut result)
  unfold matchingRoundPost
  split_ifs with hgap
  · exact bisection_deficit_split G β hβ hb cut result.1.shore hc.source_mem
      hc.sink_notMem (by simpa only [hshore] using hgap)
  · obtain ⟨routes, hlocate, hmap, hlocated⟩ := locateRoutes_correct G
      (slotCount cut.shore) (slotCount cut.shoreᶜ) result.1.flow hc.feasible.1
      result.2.routes hr.paths
    have hfit : SlotsFit cut routes := fun v => located_terminal_bounds G
      (slotCount cut.shore) (slotCount cut.shoreᶜ) result.1.flow hc.feasible.1
      (eventValue result.1.events) result.2 hr routes hmap hlocated v
    let pairs := buildClonePairing cut routes hfit
    simp only [hlocate, assignClones_success cut routes hfit]
    change MatchingRoundCorrect G β cut routes pairs
    refine ⟨hlocated, ?_, ?_, ?_⟩
    · intro route hroute
      have hp := hr.paths route.nodes (by rw [← hmap]; exact List.mem_map_of_mem hroute)
      apply hp.mono
      intro u v huv
      exact lt_of_lt_of_le huv (hc.feasible.1.2 u v)
    · intro u v
      rw [hmap]
      simpa only [twoStar_internal] using
        hr.undirected_load_le hc.feasible.1 (.inl u) (.inl v)
    · have hlen : routes.length = eventValue result.1.events := by
        have h := congrArg List.length hmap
        simpa only [List.length_map, hr.count] using h
      have hle : routes.length ≤ cut.shore.card := by
        simpa only [Fintype.card_fin, Fintype.card_coe] using
          Fintype.card_le_of_embedding pairs.left
      rw [pairs.fakeLeft_card, Nat.cast_sub hle]
      have hlenR : (routes.length : ℝ) = eventValue result.1.events := by exact_mod_cast hlen
      have hgap' := le_of_not_gt hgap
      linarith

theorem matchingRound_cost (read : Finset V → ℝ) (β : ℝ) (cut : Bisection (Clone V b)) :
    (matchingRound β cut).cost read ≤ exactCoarseBudget (slotCount cut.shore) := by
  rw [matchingRound, Prog.cost_map, routedFlowProg_cost, scaledExactProg, scaleAnswers_cost]
  exact exactProg_cost _ _ _

theorem matchingRound_cost_sharp (G : WeightedGraph V) (hG : Unweighted G)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hqpos : 1 ≤ Fintype.card V)
    (hq : Fintype.card V ≤ t ^ 3) (β : ℝ) (cut : Bisection (Clone V (2 * t))) :
    (matchingRound β cut).cost G.cut ≤ exactSharpBudget V R t := by
  have hcard := bisection_clone_card cut
  have ha : (∑ v, slotCount cut.shore v) ≤ Fintype.card V * t := by
    rw [sum_slotCount]
    nlinarith
  rw [matchingRound, Prog.cost_map, routedFlowProg_cost]
  exact scaledExactProg_cost_sharp G hG 1 R t le_rfl hR ht hqpos hq
    (slotCount cut.shore) (slotCount cut.shoreᶜ) ha

end
end CutQueryComplexity.DeterministicAPMCExpansion

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.bisection_deficit_split
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.matchingRound_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.matchingRound_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.matchingRound_cost_sharp
