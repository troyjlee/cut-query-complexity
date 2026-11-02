import CutQueryComplexity.DeterministicAPMCExpansion.MatchingRound
import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.FullPlayer

/-!
# Execute every matching-game request with the actual flow program

The interpreter returns a sparse split immediately, or retains every completed
round's routes and fake marker alongside the game's output. A failed game
still pays for all flow calls made before the split. Definitions selecting
input queries have no graph or response-correctness parameter.

`gameRead` is only a semantic replay of one execution. Its fallback matching
is public and legal for every bisection, so the cut-player's legality premise
is proved here, including requests not reached by the execution.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset Flow AllPairsAudit
open scoped Classical
noncomputable section

variable {V O : Type} [Fintype V] [DecidableEq V] {b : ℕ}

structure RoutedRound (V : Type) [Fintype V] [DecidableEq V] (b : ℕ) where
  cut : Bisection (Clone V b)
  routes : List (LocatedRoute V)
  pairs : ClonePairing cut routes

inductive GameResult (V : Type) [Fintype V] [DecidableEq V] (b : ℕ) (O : Type) where
  | split : Finset V → GameResult V b O
  | complete : O → List (RoutedRound V b) → GameResult V b O
  | invalid : GameResult V b O

def prependRound (round : RoutedRound V b) : GameResult V b O → GameResult V b O
  | .split P => .split P
  | .complete out rounds => .complete out (round :: rounds)
  | .invalid => .invalid

def runMatchingGame (β : ℝ) :
    Prog (MatchRequest (Clone V b)) (Matching (Clone V b)) O →
      Prog (Finset V) ℝ (GameResult V b O)
  | .pure out => .pure (.complete out [])
  | .query request next => (matchingRound β request.cut).bind fun answer =>
      match answer with
      | .split P => .pure (.split P)
      | .invalid => .pure .invalid
      | .matched routes pairs =>
          (runMatchingGame β (next pairs.matching)).map
            (prependRound ⟨request.cut, routes, pairs⟩)

def fallbackMatching {C : Type} [Fintype C] [DecidableEq C]
    (cut : Bisection C) : Matching C :=
  matchingOfEquiv cut.shore (Fintype.equivOfCardEq (by
    simpa only [Fintype.card_coe] using cut.balanced))

theorem fallbackMatching_crosses {C : Type} [Fintype C] [DecidableEq C]
    (cut : Bisection C) : (fallbackMatching cut).Crosses cut.shore :=
  matchingOfEquiv_crosses _ _

def roundResponse {cut : Bisection (Clone V b)} : MatchingRoundResult cut → Matching (Clone V b)
  | .matched _ pairs => pairs.matching
  | .split _ => fallbackMatching cut
  | .invalid => fallbackMatching cut

theorem roundResponse_crosses {cut : Bisection (Clone V b)} (answer : MatchingRoundResult cut) :
    (roundResponse answer).Crosses cut.shore := by
  cases answer with
  | matched routes pairs => exact pairs.crosses
  | split _ => exact fallbackMatching_crosses cut
  | invalid => exact fallbackMatching_crosses cut

/-- Proof-side replay; never called from the operational interpreter. -/
def gameRead (read : Finset V → ℝ) (β : ℝ) (request : MatchRequest (Clone V b)) :
    Matching (Clone V b) := roundResponse ((matchingRound β request.cut).eval read)

theorem gameRead_legal (read : Finset V → ℝ) (β : ℝ) : LegalResponses (gameRead (b := b) read β) :=
  fun request => roundResponse_crosses _

def GameCorrect (G : WeightedGraph V) (β : ℝ)
    (game : Prog (MatchRequest (Clone V b)) (Matching (Clone V b)) O) :
    GameResult V b O → Prop
  | .split P => SplitCorrect G b β P
  | .complete out rounds =>
      out = game.eval (gameRead G.cut β) ∧
        rounds.length = game.cost (gameRead G.cut β) ∧
        ∀ round ∈ rounds, MatchingRoundCorrect G β round.cut round.routes round.pairs
  | .invalid => False

theorem runMatchingGame_correct (G : WeightedGraph V) (hG : Unweighted G)
    (β : ℝ) (hβ : 0 ≤ β) (hb : 0 < b)
    (game : Prog (MatchRequest (Clone V b)) (Matching (Clone V b)) O) :
    GameCorrect G β game ((runMatchingGame β game).eval G.cut) := by
  induction game with
  | pure out => simp [runMatchingGame, GameCorrect]
  | query request next ih =>
      have hround := matchingRound_correct G hG β hβ hb request.cut
      rw [runMatchingGame, Prog.eval_bind]
      cases ha : (matchingRound β request.cut).eval G.cut with
      | split P =>
          simpa only [ha, RoundCorrect, Prog.eval_pure, GameCorrect] using hround
      | invalid =>
          have hfalse : False := by simpa only [ha, RoundCorrect] using hround
          exact hfalse.elim
      | matched routes pairs =>
          have hp : MatchingRoundCorrect G β request.cut routes pairs := by
            simpa only [ha, RoundCorrect] using hround
          have hread : gameRead G.cut β request = pairs.matching := by
            simp only [gameRead, ha, roundResponse]
          rw [Prog.eval_map]
          have hi := ih pairs.matching
          cases hs : (runMatchingGame β (next pairs.matching)).eval G.cut with
          | split P => simpa only [hs, GameCorrect, prependRound] using hi
          | invalid =>
              have hfalse : False := by simpa only [hs, GameCorrect] using hi
              exact hfalse.elim
          | complete out rounds =>
              obtain ⟨hout, hlength, hrounds⟩ := (show GameCorrect G β (next pairs.matching)
                (.complete out rounds) from by simpa only [hs] using hi)
              change out = (Prog.query request next).eval (gameRead G.cut β) ∧
                (⟨request.cut, routes, pairs⟩ :: rounds).length =
                  (Prog.query request next).cost (gameRead G.cut β) ∧ _
              refine ⟨?_, ?_, ?_⟩
              · simpa only [Prog.eval, Prog.run, hread] using hout
              · simpa only [Prog.cost, Prog.run, hread, List.length_cons] using
                  congrArg (fun n => n + 1) hlength
              · intro round hr
                rcases List.mem_cons.mp hr with rfl | hr
                · exact hp
                · exact hrounds round hr

/-- Compositional cost inequality for the literal interpreter. The concrete
cut-player theorem below discharges its per-round cost premise using the
proved exact-flow execution bound. -/
theorem runMatchingGame_cost (read : Finset V → ℝ) (β : ℝ) (Q : ℕ)
    (hQ : ∀ cut : Bisection (Clone V b), (matchingRound β cut).cost read ≤ Q)
    (game : Prog (MatchRequest (Clone V b)) (Matching (Clone V b)) O) :
    (runMatchingGame β game).cost read ≤ Q * game.cost (gameRead read β) := by
  induction game with
  | pure out => simp [runMatchingGame]
  | query request next ih =>
      have hround := hQ request.cut
      rw [runMatchingGame, Prog.cost_bind]
      cases ha : (matchingRound β request.cut).eval read with
      | split P =>
          simp only [Prog.cost_pure, Nat.add_zero]
          change (matchingRound β request.cut).cost read ≤
            Q * ((next (gameRead read β request)).cost (gameRead read β) + 1)
          nlinarith
      | invalid =>
          simp only [Prog.cost_pure, Nat.add_zero]
          change (matchingRound β request.cut).cost read ≤
            Q * ((next (gameRead read β request)).cost (gameRead read β) + 1)
          nlinarith
      | matched routes pairs =>
          have hread : gameRead read β request = pairs.matching := by
            simp only [gameRead, ha, roundResponse]
          rw [Prog.cost_map]
          have hi := ih pairs.matching
          change (matchingRound β request.cut).cost read +
            (runMatchingGame β (next pairs.matching)).cost read ≤
              Q * ((next (gameRead read β request)).cost (gameRead read β) + 1)
          rw [hread]
          nlinarith

def executedCutPlayer (β : ℝ) (heven : Even (Fintype.card (Clone V b))) :
    Prog (Finset V) ℝ (GameResult V b (BalancedResult (Clone V b))) :=
  runMatchingGame β (cutPlayer heven)

theorem executedCutPlayer_cost (G : WeightedGraph V) (hG : Unweighted G)
    (R t : ℕ) (hR : 1 ≤ R) (ht : 1 ≤ t) (hqpos : 1 ≤ Fintype.card V)
    (hq : Fintype.card V ≤ t ^ 3) (β : ℝ)
    (heven : Even (Fintype.card (Clone V (2 * t)))) :
    (executedCutPlayer β heven).cost G.cut ≤
      exactSharpBudget V R t * normalizedRounds (Fintype.card (Clone V (2 * t))) := by
  have hc := runMatchingGame_cost G.cut β (exactSharpBudget V R t)
    (matchingRound_cost_sharp G hG R t hR ht hqpos hq β) (cutPlayer heven)
  exact hc.trans (Nat.mul_le_mul_left _ (cutPlayer_cost heven (gameRead G.cut β)))

/-- A completed execution has the proved normalized expansion and exactly
one retained route record per actual matching-game query. The `HistoryTrace`
module reconciles the matching history with these retained records. -/
theorem executedCutPlayer_complete (G : WeightedGraph V) (hG : Unweighted G)
    (β : ℝ) (hβ : 0 ≤ β) (hb : 0 < b) (hV : 0 < Fintype.card V)
    (heven : Even (Fintype.card (Clone V b))) (out : BalancedResult (Clone V b))
    (rounds : List (RoutedRound V b))
    (hexec : (executedCutPlayer β heven).eval G.cut = .complete out rounds) :
    out.complete = true ∧
      (∀ S : Finset (Clone V b), min (S.card : ℝ) (Sᶜ.card : ℝ) ≤
        (historyGraph out.history).cut S) ∧
      rounds.length ≤ normalizedRounds (Fintype.card (Clone V b)) ∧
      ∀ round ∈ rounds, MatchingRoundCorrect G β round.cut round.routes round.pairs := by
  have h := runMatchingGame_correct G hG β hβ hb (cutPlayer heven)
  change GameCorrect G β (cutPlayer heven) ((executedCutPlayer β heven).eval G.cut) at h
  rw [hexec] at h
  obtain ⟨hout, hcount, hrounds⟩ := h
  have hN : 0 < Fintype.card (Clone V b) := by
    simpa only [Clone, Fintype.card_prod, Fintype.card_fin] using Nat.mul_pos hV hb
  have he := cutPlayer_expands heven hN (gameRead G.cut β) (gameRead_legal G.cut β)
  rw [← hout] at he
  exact ⟨he.1, he.2, hcount.trans_le (cutPlayer_cost heven (gameRead G.cut β)), hrounds⟩

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.runMatchingGame_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.executedCutPlayer_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.executedCutPlayer_complete
