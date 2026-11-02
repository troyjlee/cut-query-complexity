import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Execute

/-!
# Reconcile the actual routed rounds with the cut-player's matching history

The semantic reply trace is chronological. The player's public history is
newest first. A completed execution returns exactly that trace of matching
objects, including multiplicities, so reversing the retained route records
gives the precise history whose expansion was proved by the cut-player.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Flow
open scoped Classical
noncomputable section

def replyTrace {I A O : Type} (read : I → A) : Prog I A O → List A
  | .pure _ => []
  | .query request next => read request :: replyTrace read (next (read request))

theorem replyTrace_bind {I A O P : Type} (read : I → A) (game : Prog I A O)
    (next : O → Prog I A P) :
    replyTrace read (game.bind next) =
      replyTrace read game ++ replyTrace read (next (game.eval read)) := by
  induction game with
  | pure out => rfl
  | query request cont ih =>
      simp only [Prog.bind, replyTrace, Prog.eval, Prog.run, ih, List.cons_append]

theorem replyTrace_map {I A O P : Type} (read : I → A) (game : Prog I A O) (f : O → P) :
    replyTrace read (game.map f) = replyTrace read game := by
  rw [Prog.map, replyTrace_bind]
  simp only [replyTrace, List.append_nil]

variable {V : Type} [Fintype V] [DecidableEq V]

theorem balancedProgram_history_trace (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (hlegal : LegalResponses read)
    (fuel : ℕ) (past history : List (Matching V)) :
    ((balancedProgram heven fuel past history).eval read).history =
      (replyTrace read (balancedProgram heven fuel past history)).reverse ++ history := by
  induction fuel generalizing history with
  | zero => simp [balancedProgram, replyTrace]
  | succ fuel ih =>
      rw [balancedProgram]
      cases hc : chooseQuarter history with
      | none => simp [replyTrace]
      | some chosen =>
          let hsmall : chosen.val.card ≤ Fintype.card V / 2 := by
            have h := chosen.property.half
            omega
          let cut := halfCompletion heven chosen.val hsmall
          let request : MatchRequest V := ⟨history ++ past, cut⟩
          have hM : (read request).Crosses cut.shore := hlegal request
          change ((if (read request).Crosses cut.shore then
              balancedProgram heven fuel past (read request :: history)
            else Prog.pure ⟨history, false⟩).eval read).history =
            (read request :: replyTrace read (if (read request).Crosses cut.shore then
              balancedProgram heven fuel past (read request :: history)
            else Prog.pure ⟨history, false⟩)).reverse ++ history
          rw [if_pos hM, ih]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem balancedBatch_history_trace (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (hlegal : LegalResponses read)
    (count : ℕ) (past : List (Matching V)) :
    ((balancedBatch heven count past).eval read).history =
      (replyTrace read (balancedBatch heven count past)).reverse := by
  induction count generalizing past with
  | zero => simp [balancedBatch, replyTrace]
  | succ count ih =>
      have hfirst := balancedProgram_history_trace heven read hlegal
        (balancedRounds (Fintype.card V)) past []
      simp only [List.append_nil] at hfirst
      simp only [balancedBatch, Prog.eval_bind, replyTrace_bind]
      split_ifs
      · simp only [Prog.eval_map, replyTrace_map, List.reverse_append, ih, hfirst]
      · simp only [Prog.eval_pure, replyTrace, List.append_nil, hfirst]

theorem finishProgram_history_trace (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (hlegal : LegalResponses read)
    (past history : List (Matching V)) :
    ((finishProgram heven past history).eval read).history =
      (replyTrace read (finishProgram heven past history)).reverse ++ history := by
  unfold finishProgram
  split_ifs with hsmall
  · let cut := halfCompletion heven (peeled (historyGraph history)) hsmall
    let request : MatchRequest V := ⟨history ++ past, cut⟩
    have hM : (read request).Crosses cut.shore := hlegal request
    change ((if (read request).Crosses cut.shore then
      Prog.pure (⟨read request :: history, true⟩ : BalancedResult V)
      else Prog.pure (⟨history, false⟩ : BalancedResult V)).eval read).history =
      (read request :: replyTrace read (if (read request).Crosses cut.shore then
        Prog.pure (⟨read request :: history, true⟩ : BalancedResult V)
        else Prog.pure (⟨history, false⟩ : BalancedResult V))).reverse ++ history
    simp only [if_pos hM, Prog.eval_pure, replyTrace, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
  · simp [replyTrace]

theorem fullProgram_history_trace (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (hlegal : LegalResponses read)
    (past : List (Matching V)) :
    ((fullProgram heven past).eval read).history =
      (replyTrace read (fullProgram heven past)).reverse := by
  have hfirst := balancedBatch_history_trace heven read hlegal 4 past
  simp only [fullProgram, Prog.eval_bind, replyTrace_bind]
  split_ifs
  · rw [finishProgram_history_trace heven read hlegal, List.reverse_append, hfirst]
  · simp only [Prog.eval_pure, replyTrace, List.append_nil, hfirst]

theorem normalizedRuns_history_trace (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (hlegal : LegalResponses read)
    (count : ℕ) (past : List (Matching V)) :
    ((normalizedRuns heven count past).eval read).history =
      (replyTrace read (normalizedRuns heven count past)).reverse := by
  induction count generalizing past with
  | zero => simp [normalizedRuns, replyTrace]
  | succ count ih =>
      have hfirst := fullProgram_history_trace heven read hlegal past
      simp only [normalizedRuns, Prog.eval_bind, replyTrace_bind]
      split_ifs
      · simp only [Prog.eval_map, replyTrace_map, List.reverse_append, ih, hfirst]
      · simp only [Prog.eval_pure, replyTrace, List.append_nil, hfirst]

theorem cutPlayer_history_trace (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (hlegal : LegalResponses read) :
    ((cutPlayer heven).eval read).history = (replyTrace read (cutPlayer heven)).reverse :=
  normalizedRuns_history_trace heven read hlegal 4 []

variable {O : Type} {b : ℕ}

theorem runMatchingGame_complete_trace (read : Finset V → ℝ) (β : ℝ)
    (game : Prog (MatchRequest (Clone V b)) (Matching (Clone V b)) O)
    (out : O) (rounds : List (RoutedRound V b))
    (hcomplete : (runMatchingGame β game).eval read = .complete out rounds) :
    rounds.map (fun round => round.pairs.matching) = replyTrace (gameRead read β) game := by
  induction game generalizing out rounds with
  | pure value =>
      simp only [runMatchingGame, Prog.eval_pure, GameResult.complete.injEq] at hcomplete
      rw [← hcomplete.2]
      rfl
  | query request next ih =>
      rw [runMatchingGame, Prog.eval_bind] at hcomplete
      cases ha : (matchingRound β request.cut).eval read with
      | split P =>
          simp only [ha, Prog.eval_pure] at hcomplete
          cases hcomplete
      | invalid =>
          simp only [ha, Prog.eval_pure] at hcomplete
          cases hcomplete
      | matched routes pairs =>
          rw [ha, Prog.eval_map] at hcomplete
          have hread : gameRead read β request = pairs.matching := by
            simp only [gameRead, ha, roundResponse]
          cases hs : (runMatchingGame β (next pairs.matching)).eval read with
          | split P =>
              simp only [hs, prependRound] at hcomplete
              cases hcomplete
          | invalid =>
              simp only [hs, prependRound] at hcomplete
              cases hcomplete
          | complete value rest =>
              simp only [hs, prependRound, GameResult.complete.injEq] at hcomplete
              rw [← hcomplete.2, List.map_cons, replyTrace, hread]
              exact congrArg (List.cons pairs.matching) (ih pairs.matching value rest hs)

/-- Literal equality, not a bound on a separately postulated matching history. -/
theorem executedCutPlayer_history_of_replay (read : Finset V → ℝ) (β : ℝ)
    (heven : Even (Fintype.card (Clone V b))) (out : BalancedResult (Clone V b))
    (rounds : List (RoutedRound V b))
    (hcomplete : (executedCutPlayer β heven).eval read = .complete out rounds)
    (hout : out = (cutPlayer heven).eval (gameRead read β)) :
    out.history = (rounds.map (fun round => round.pairs.matching)).reverse := by
  have htrace := runMatchingGame_complete_trace read β (cutPlayer heven) out rounds hcomplete
  rw [htrace, hout]
  exact cutPlayer_history_trace heven (gameRead read β) (gameRead_legal read β)

theorem executedCutPlayer_history (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (β : ℝ) (hβ : 0 ≤ β) (hb : 0 < b)
    (heven : Even (Fintype.card (Clone V b))) (out : BalancedResult (Clone V b))
    (rounds : List (RoutedRound V b))
    (hcomplete : (executedCutPlayer β heven).eval G.cut = .complete out rounds) :
    out.history = (rounds.map (fun round => round.pairs.matching)).reverse := by
  have h := runMatchingGame_correct G hG β hβ hb (cutPlayer heven)
  change GameCorrect G β (cutPlayer heven) ((executedCutPlayer β heven).eval G.cut) at h
  rw [hcomplete] at h
  exact executedCutPlayer_history_of_replay G.cut β heven out rounds hcomplete h.1

theorem historyGraph_reverse_cut (history : List (Matching V)) (S : Finset V) :
    (historyGraph history.reverse).cut S = (historyGraph history).cut S := by
  induction history with
  | nil => rfl
  | cons M rest ih =>
      rw [List.reverse_cons, historyGraph_append_cut, historyGraph_cons_cut,
        historyGraph_nil_cut, add_zero, ih, historyGraph_cons_cut]
      exact add_comm _ _

/-- Expansion of the actual completed round records, with every repeated
matching kept. No supplied matching-history or legality premise remains. -/
theorem executedCutPlayer_rounds_expand (G : WeightedGraph V) (hG : AllPairsAudit.Unweighted G)
    (β : ℝ) (hβ : 0 ≤ β) (hb : 0 < b) (hV : 0 < Fintype.card V)
    (heven : Even (Fintype.card (Clone V b))) (out : BalancedResult (Clone V b))
    (rounds : List (RoutedRound V b))
    (hcomplete : (executedCutPlayer β heven).eval G.cut = .complete out rounds) :
    ∀ S : Finset (Clone V b), min (S.card : ℝ) (Sᶜ.card : ℝ) ≤
      (historyGraph (rounds.map (fun round => round.pairs.matching))).cut S := by
  intro S
  have he := (executedCutPlayer_complete G hG β hβ hb hV heven out rounds hcomplete).2.1 S
  rw [executedCutPlayer_history G hG β hβ hb heven out rounds hcomplete,
    historyGraph_reverse_cut] at he
  exact he

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.cutPlayer_history_trace
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.runMatchingGame_complete_trace
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.executedCutPlayer_history
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.executedCutPlayer_rounds_expand
