import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.FakeEdges
import CutQueryComplexity.DeterministicAPMCExpansion.Pruning.CutAlgebra
import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.HistoryTrace
import CutQueryComplexity.DeterministicAPMCExpansion.Flow.RouteCuts

/-!
# Feed the actual completed routed rounds to the public fake-graph producer

The adapter keeps every matching and marker literally. Real cut crossings
inject into separated extracted routes, whose aggregate congestion pays for
them in the input cut. The cut-player supplies expansion of precisely these
matchings, and the fake producer supplies the complementary cut term.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds

open Finset Flow CutMatching AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {b : ℕ}

def markPairing {cut : Bisection (Clone V b)} {routes : List (LocatedRoute V)}
    (pairs : ClonePairing cut routes) : FakeEdges.MarkedRound (Clone V b) :=
  ⟨pairs.matching, pairs.fakeEndpoints, pairs.fakeEndpoints_mate⟩

def marked (round : RoutedRound V b) : FakeEdges.MarkedRound (Clone V b) :=
  markPairing round.pairs

def markedHistory (rounds : List (RoutedRound V b)) : List (FakeEdges.MarkedRound (Clone V b)) :=
  rounds.map marked

theorem pairCount_eq_fakeLeft {cut : Bisection (Clone V b)} {routes : List (LocatedRoute V)}
    (pairs : ClonePairing cut routes) : FakeEdges.pairCount (markPairing pairs) = pairs.fakeLeft.card := by
  calc
    _ = (cut.shore.filter (fun c => c ∈ pairs.fakeEndpoints)).card :=
      FakeEdges.pairCount_eq_shore (markPairing pairs) cut.shore pairs.crosses
    _ = _ := congrArg Finset.card pairs.fakeLeft_eq_filter.symm

/-- The accepted one-sided fake-pair count is exactly the deficit left by
the actual route list, before projected loops are discarded. -/
theorem pairCount_eq_deficit {cut : Bisection (Clone V b)} {routes : List (LocatedRoute V)}
    (pairs : ClonePairing cut routes) :
    FakeEdges.pairCount (markPairing pairs) = cut.shore.card - routes.length := by
  rw [pairCount_eq_fakeLeft, pairs.fakeLeft_card]

theorem pairing_reverse {cut : Bisection (Clone V b)} {routes : List (LocatedRoute V)}
    (pairs : ClonePairing cut routes) (i : Fin routes.length) :
    pairs.matching.mate (pairs.right i).val = (pairs.left i).val := by
  rw [← pairs.paired i, pairs.matching.involutive]

theorem pairing_real_endpoint {cut : Bisection (Clone V b)} {routes : List (LocatedRoute V)}
    (pairs : ClonePairing cut routes) {c : Clone V b} (hc : c ∉ pairs.fakeEndpoints) :
    ∃ i, c = (pairs.left i).val ∨ c = (pairs.right i).val := by
  by_cases hs : c ∈ cut.shore
  · obtain ⟨i, hi⟩ := (pairs.real_left_iff hs).mp hc
    exact ⟨i, Or.inl hi.symm⟩
  · have hm : pairs.matching.mate c ∈ cut.shore := by
      by_contra h
      exact hs ((pairs.crosses c).mpr h)
    have hf : pairs.matching.mate c ∉ pairs.fakeEndpoints :=
      fun h => hc ((pairs.fakeEndpoints_mate c).mp h)
    obtain ⟨i, hi⟩ := (pairs.real_left_iff hm).mp hf
    refine ⟨i, Or.inr ?_⟩
    have h := pairs.paired i
    rw [hi, pairs.matching.involutive] at h
    exact h

def SeparatedRoute (T : Finset V) (route : LocatedRoute V) : Prop :=
  (route.start ∈ T ∧ route.finish ∉ T) ∨ (route.finish ∈ T ∧ route.start ∉ T)

theorem separated_indicator (T : Finset V) (route : LocatedRoute V) :
    (if SeparatedRoute T route then (1 : ℝ) else 0) = separated T route.start route.finish := by
  by_cases hs : route.start ∈ T <;> by_cases ht : route.finish ∈ T <;>
    simp [SeparatedRoute, separated, hs, ht]

theorem list_sum_get {A : Type} (items : List A) (f : A → ℝ) :
    (items.map f).sum = ∑ i : Fin items.length, f (items.get i) := by
  have he : List.ofFn (fun i : Fin items.length => f (items.get i)) = items.map f := by
    change List.ofFn (f ∘ items.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← he, List.sum_ofFn]

/-- Each crossing real clone pair chooses its unique actual route. Two
opposite endpoints of one pair cannot both lie in the crossing shore. -/
theorem realCrossing_le_routes {cut : Bisection (Clone V b)} {routes : List (LocatedRoute V)}
    (pairs : ClonePairing cut routes) (T : Finset V) :
    (FakeEdges.realCrossing (markPairing pairs) (FakeEdges.cloneShore T) : ℝ) ≤
      (routes.map (fun route => separated T route.start route.finish)).sum := by
  let crossing := (FakeEdges.crossingEndpoints pairs.matching (FakeEdges.cloneShore T)).filter
    (fun c => c ∉ pairs.fakeEndpoints)
  let selected := (univ : Finset (Fin routes.length)).filter
    (fun i => SeparatedRoute T (routes.get i))
  have hdata (c : crossing) : c.val ∈ FakeEdges.cloneShore T ∧
      pairs.matching.mate c.val ∉ FakeEdges.cloneShore T ∧ c.val ∉ pairs.fakeEndpoints := by
    simpa only [crossing, FakeEdges.crossingEndpoints, mem_filter, and_assoc] using c.property
  let index : crossing → Fin routes.length :=
    fun c => Classical.choose (pairing_real_endpoint pairs (hdata c).2.2)
  have hindex (c : crossing) : c.val = (pairs.left (index c)).val ∨
      c.val = (pairs.right (index c)).val :=
    Classical.choose_spec (pairing_real_endpoint pairs (hdata c).2.2)
  have hinj : Function.Injective index := by
    intro c d he
    have hc := hindex c
    rw [he] at hc
    rcases hc with hc | hc <;> rcases hindex d with hd | hd
    · exact Subtype.ext (hc.trans hd.symm)
    · exfalso
      apply (hdata c).2.1
      rw [hc, pairs.paired, ← hd]
      exact (hdata d).1
    · exfalso
      apply (hdata d).2.1
      rw [hd, pairs.paired, ← hc]
      exact (hdata c).1
    · exact Subtype.ext (hc.trans hd.symm)
  have hselected (c : crossing) : index c ∈ selected := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    have hin := (hdata c).1
    have hout := (hdata c).2.1
    rcases hindex c with he | he
    · left
      rw [he, FakeEdges.mem_cloneShore, pairs.source_label] at hin
      rw [he, pairs.paired, FakeEdges.mem_cloneShore, pairs.sink_label] at hout
      exact ⟨hin, hout⟩
    · right
      rw [he, FakeEdges.mem_cloneShore, pairs.sink_label] at hin
      rw [he, pairing_reverse, FakeEdges.mem_cloneShore, pairs.source_label] at hout
      exact ⟨hin, hout⟩
  let embedding : crossing ↪ selected :=
    ⟨fun c => ⟨index c, hselected c⟩, fun c d h => hinj (congrArg Subtype.val h)⟩
  have hcard : crossing.card ≤ selected.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_embedding embedding
  have hcount : (selected.card : ℝ) =
      (routes.map (fun route => separated T route.start route.finish)).sum := by
    rw [list_sum_get]
    simp only [selected, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, separated_indicator]
  change (crossing.card : ℝ) ≤ _
  rw [← hcount]
  exact_mod_cast hcard

theorem round_real_cut_le (G : WeightedGraph V) (β : ℝ) (round : RoutedRound V b)
    (h : MatchingRoundCorrect G β round.cut round.routes round.pairs) (T : Finset V) :
    (FakeEdges.realCrossing (marked round) (FakeEdges.cloneShore T) : ℝ) ≤ G.cut T := by
  apply (realCrossing_le_routes round.pairs T).trans
  exact routes_cut_domination G round.routes _ h.paths h.located h.congestion T

theorem history_real_cut_le (G : WeightedGraph V) (β : ℝ) (rounds : List (RoutedRound V b))
    (h : ∀ round ∈ rounds, MatchingRoundCorrect G β round.cut round.routes round.pairs)
    (T : Finset V) :
    (FakeEdges.realCutCount (markedHistory rounds) T : ℝ) ≤ (rounds.length : ℝ) * G.cut T := by
  induction rounds with
  | nil => simp [markedHistory, FakeEdges.realCutCount]
  | cons round rounds ih =>
      have hhead := round_real_cut_le G β round (h _ (by simp)) T
      have htail := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
      simp only [markedHistory, FakeEdges.realCutCount, List.map_cons, List.sum_cons,
        List.length_cons, Nat.cast_add, Nat.cast_one]
      change (FakeEdges.realCrossing (marked round) (FakeEdges.cloneShore T) : ℝ) +
        (FakeEdges.realCutCount (markedHistory rounds) T : ℝ) ≤
          ((rounds.length : ℝ) + 1) * G.cut T
      linarith

theorem cloneShore_compl (T : Finset V) :
    (FakeEdges.cloneShore (b := b) T)ᶜ = FakeEdges.cloneShore Tᶜ := by
  ext c
  simp only [mem_compl, FakeEdges.mem_cloneShore]

theorem completed_certificate (G : WeightedGraph V) (hG : Unweighted G)
    (β R : ℕ) (hb : 0 < b) (hV : 0 < Fintype.card V)
    (heven : Even (Fintype.card (Clone V b)))
    (hR : normalizedRounds (Fintype.card (Clone V b)) ≤ R)
    (out : BalancedResult (Clone V b)) (rounds : List (RoutedRound V b))
    (hcomplete : (executedCutPlayer (β : ℝ) heven).eval G.cut = .complete out rounds) :
    FakeCertificate G (FakeEdges.fakeGraph (markedHistory rounds)) b R ∧
      FakeEdges.edgeCount (markedHistory rounds) ≤ R * β * b ∧
      ∀ v, FakeEdges.degreeTable (markedHistory rounds) v ≤ R * b := by
  have hc := executedCutPlayer_complete G hG β (Nat.cast_nonneg _) hb hV heven out rounds hcomplete
  have hlength : rounds.length ≤ R := hc.2.2.1.trans hR
  have hexpand := executedCutPlayer_rounds_expand G hG β (Nat.cast_nonneg _) hb hV
    heven out rounds hcomplete
  have hrounds := hc.2.2.2
  have hmarkedLength : (markedHistory rounds).length ≤ R := by
    simpa only [markedHistory, List.length_map] using hlength
  refine ⟨?_, ?_, ?_⟩
  · intro T
    have he := hexpand (FakeEdges.cloneShore T)
    have hsplit := FakeEdges.history_cut_split (markedHistory rounds) T
    have hmap : (markedHistory rounds).map FakeEdges.MarkedRound.matching =
        rounds.map (fun round => round.pairs.matching) := by
      simp only [markedHistory, List.map_map, Function.comp_def, marked, markPairing]
    rw [hmap] at hsplit
    rw [hsplit, cloneShore_compl, FakeEdges.cloneShore_card, FakeEdges.cloneShore_card,
      Nat.cast_mul, Nat.cast_mul] at he
    have hreal := history_real_cut_le G β rounds hrounds T
    have hbound := mul_le_mul_of_nonneg_right
      (show (rounds.length : ℝ) ≤ R by exact_mod_cast hlength) (G.cut_nonneg T)
    have hmin : min ((T.card : ℝ) * b) ((Tᶜ.card : ℝ) * b) =
        (b : ℝ) * min (T.card : ℝ) (Tᶜ.card : ℝ) := by
      rcases le_total (T.card : ℝ) (Tᶜ.card : ℝ) with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))]
        ring
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))]
        ring
    rw [hmin] at he
    linarith
  · apply FakeEdges.edgeCount_le_budget (markedHistory rounds) R β hmarkedLength
    intro annotated hannotated
    obtain ⟨round, hround, rfl⟩ := List.mem_map.mp hannotated
    have hf := (hrounds round hround).fake_count
    change (round.pairs.fakeLeft.card : ℝ) ≤ (β : ℝ) * b at hf
    rw [show marked round = markPairing round.pairs from rfl, pairCount_eq_fakeLeft]
    exact_mod_cast hf
  · intro v
    exact (FakeEdges.degreeTable_le (markedHistory rounds) v).trans
      (Nat.mul_le_mul_right b hmarkedLength)

end
end CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.realCrossing_le_routes
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.round_real_cut_le
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.completed_certificate
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Pruning.ActualRounds.pairCount_eq_deficit
