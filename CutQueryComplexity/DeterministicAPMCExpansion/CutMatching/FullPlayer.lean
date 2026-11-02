import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Player
import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Pruning

/-!
# The complete public cut-player and four-run normalization

A full run uses four fresh balanced games, prunes their explicit union, and
asks for one final matching. Four fresh full runs give expansion one. Every
request carries all earlier matchings, so a matching producer may be adaptive.
The cost bounds hold for every response function, including illegal responses.

Correctness here is the public game's contract for legal perfect matchings.
The input-query algorithm must implement those responses by the actual flow
program and account separately for failures and fake edges. This file has no
hidden graph parameter, flow oracle, or all-pairs endpoint claim.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset Prog WeightedGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Each subgame starts with its own empty entropy history. The full past is
retained in requests, but it is not reused as a fresh subgame's potential. -/
def balancedBatch (heven : Even (Fintype.card V)) :
    ℕ → List (Matching V) → Prog (MatchRequest V) (Matching V) (BalancedResult V)
  | 0, _past => .pure ⟨[], true⟩
  | count + 1, past =>
      (balancedProgram heven (balancedRounds (Fintype.card V)) past []).bind fun first =>
        if first.complete = true then
          (balancedBatch heven count (first.history ++ past)).map fun rest =>
            ⟨rest.history ++ first.history, rest.complete⟩
        else .pure first

theorem balancedBatch_cost (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (count : ℕ) (past : List (Matching V)) :
    (balancedBatch heven count past).cost read ≤ count * balancedRounds (Fintype.card V) := by
  induction count generalizing past with
  | zero => simp [balancedBatch]
  | succ count ih =>
      rw [balancedBatch, Prog.cost_bind]
      let first := (balancedProgram heven (balancedRounds (Fintype.card V)) past []).eval read
      change (balancedProgram heven (balancedRounds (Fintype.card V)) past []).cost read +
        (if first.complete = true then
          (balancedBatch heven count (first.history ++ past)).map
            (fun rest => ⟨rest.history ++ first.history, rest.complete⟩)
        else Prog.pure first).cost read ≤ (count + 1) * balancedRounds (Fintype.card V)
      have hfirst := balancedProgram_cost heven read (balancedRounds (Fintype.card V)) past []
      split_ifs
      · rw [Prog.cost_map]
        have hrest := ih (first.history ++ past)
        nlinarith
      · simp only [Prog.cost_pure, Nat.add_zero]
        nlinarith

theorem balancedBatch_correct (heven : Even (Fintype.card V))
    (hN : 0 < Fintype.card V) (read : MatchRequest V → Matching V)
    (hlegal : LegalResponses read) (count : ℕ) (past : List (Matching V)) :
    let result := (balancedBatch heven count past).eval read
    result.complete = true ∧
      ∀ S : Finset V, Fintype.card V ≤ 4 * S.card → 2 * S.card ≤ Fintype.card V →
        (count : ℝ) * S.card ≤ 4 * (historyGraph result.history).cut S := by
  induction count generalizing past with
  | zero => simp [balancedBatch]
  | succ count ih =>
      let first := (balancedProgram heven (balancedRounds (Fintype.card V)) past []).eval read
      have hfirst : first.complete = true := balancedProgram_finishes heven hN read hlegal past
      have hdense : ∀ S : Finset V, Fintype.card V ≤ 4 * S.card →
          2 * S.card ≤ Fintype.card V → (S.card : ℝ) ≤ 4 * (historyGraph first.history).cut S := by
        intro S hquarter hhalf
        have hnone := balancedProgram_spec heven read (balancedRounds (Fintype.card V)) past [] hfirst S
        by_contra h
        exact hnone ⟨hquarter, hhalf, lt_of_not_ge h⟩
      let rest := (balancedBatch heven count (first.history ++ past)).eval read
      have hrest := ih (first.history ++ past)
      change rest.complete = true ∧ _ at hrest
      have hfirstEval :
          ((balancedProgram heven (balancedRounds (Fintype.card V)) past []).eval read).complete =
            true := hfirst
      rw [balancedBatch, Prog.eval_bind]
      simp only [hfirstEval, ↓reduceIte, Prog.eval_map]
      refine ⟨hrest.1, ?_⟩
      intro S hquarter hhalf
      change ((count + 1 : ℕ) : ℝ) * S.card ≤
        4 * (historyGraph (rest.history ++ first.history)).cut S
      rw [historyGraph_append_cut]
      have h1 := hdense S hquarter hhalf
      have h2 := hrest.2 S hquarter hhalf
      push_cast
      nlinarith

theorem balancedBatch_four_dense (heven : Even (Fintype.card V))
    (hN : 0 < Fintype.card V) (read : MatchRequest V → Matching V)
    (hlegal : LegalResponses read) (past : List (Matching V)) :
    QuarterDense (historyGraph ((balancedBatch heven 4 past).eval read).history) := by
  intro S hquarter hhalf
  have h := (balancedBatch_correct heven hN read hlegal 4 past).2 S hquarter hhalf
  norm_num at h
  linarith

/-- The cardinality guard makes this program total on arbitrary replies.
For legal histories its success is proved from the pruning invariant. -/
def finishProgram (heven : Even (Fintype.card V)) (past history : List (Matching V)) :
    Prog (MatchRequest V) (Matching V) (BalancedResult V) :=
  if hsmall : (peeled (historyGraph history)).card ≤ Fintype.card V / 2 then
    let cut := halfCompletion heven (peeled (historyGraph history)) hsmall
    Prog.query ⟨history ++ past, cut⟩ fun M =>
      if M.Crosses cut.shore then .pure ⟨M :: history, true⟩
      else .pure ⟨history, false⟩
  else .pure ⟨history, false⟩

theorem finishProgram_cost (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (past history : List (Matching V)) :
    (finishProgram heven past history).cost read ≤ 1 := by
  unfold finishProgram
  split_ifs
  · change (if _ then Prog.pure _ else Prog.pure _).cost read + 1 ≤ 1
    split_ifs <;> simp
  · simp

theorem finishProgram_correct (heven : Even (Fintype.card V))
    (hN : 0 < Fintype.card V) (read : MatchRequest V → Matching V)
    (hlegal : LegalResponses read) (past history : List (Matching V))
    (hdense : QuarterDense (historyGraph history)) :
    let result := (finishProgram heven past history).eval read
    result.complete = true ∧ ∀ S : Finset V,
      min (S.card : ℝ) (Sᶜ.card : ℝ) ≤ 4 * (historyGraph result.history).cut S := by
  let P := peeled (historyGraph history)
  have hp := (peeled_invariant (historyGraph history) hdense hN).small
  change 4 * P.card < Fintype.card V at hp
  have hsmall : P.card ≤ Fintype.card V / 2 := by omega
  let cut := halfCompletion heven P hsmall
  let request : MatchRequest V := ⟨history ++ past, cut⟩
  let M := read request
  have hM : M.Crosses cut.shore := hlegal request
  have hout : ∀ v ∈ P, M.mate v ∉ P := by
    intro v hv hmate
    have hsub := halfCompletion_contains heven P hsmall
    exact ((hM v).mp (hsub hv)) (hsub hmate)
  have heval : (finishProgram heven past history).eval read = ⟨M :: history, true⟩ := by
    rw [finishProgram, dif_pos hsmall]
    change ((if M.Crosses cut.shore then Prog.pure (⟨M :: history, true⟩ : BalancedResult V)
      else Prog.pure (⟨history, false⟩ : BalancedResult V)).eval read) = _
    simp only [hM, ↓reduceIte, Prog.eval_pure]
  rw [heval]
  refine ⟨rfl, ?_⟩
  intro S
  rw [historyGraph_cons_cut]
  exact pruned_final_matching_quarter (historyGraph history) hdense hN M hout S

def fullRounds (N : ℕ) : ℕ := 4 * balancedRounds N + 1

def fullProgram (heven : Even (Fintype.card V)) (past : List (Matching V)) :
    Prog (MatchRequest V) (Matching V) (BalancedResult V) :=
  (balancedBatch heven 4 past).bind fun first =>
    if first.complete = true then finishProgram heven past first.history
    else .pure first

theorem fullProgram_cost (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (past : List (Matching V)) :
    (fullProgram heven past).cost read ≤ fullRounds (Fintype.card V) := by
  rw [fullProgram, Prog.cost_bind]
  have hfirst := balancedBatch_cost heven read 4 past
  split_ifs
  · have hlast := finishProgram_cost heven read past
      ((balancedBatch heven 4 past).eval read).history
    unfold fullRounds
    omega
  · simp only [Prog.cost_pure, Nat.add_zero]
    unfold fullRounds
    omega

theorem fullProgram_correct (heven : Even (Fintype.card V))
    (hN : 0 < Fintype.card V) (read : MatchRequest V → Matching V)
    (hlegal : LegalResponses read) (past : List (Matching V)) :
    let result := (fullProgram heven past).eval read
    result.complete = true ∧ ∀ S : Finset V,
      min (S.card : ℝ) (Sᶜ.card : ℝ) ≤ 4 * (historyGraph result.history).cut S := by
  have hfirst := (balancedBatch_correct heven hN read hlegal 4 past).1
  have hdense := balancedBatch_four_dense heven hN read hlegal past
  simp only [fullProgram, Prog.eval_bind, hfirst, ↓reduceIte]
  exact finishProgram_correct heven hN read hlegal past _ hdense

def normalizedRuns (heven : Even (Fintype.card V)) :
    ℕ → List (Matching V) → Prog (MatchRequest V) (Matching V) (BalancedResult V)
  | 0, _past => .pure ⟨[], true⟩
  | count + 1, past => (fullProgram heven past).bind fun first =>
      if first.complete = true then
        (normalizedRuns heven count (first.history ++ past)).map fun rest =>
          ⟨rest.history ++ first.history, rest.complete⟩
      else .pure first

theorem normalizedRuns_cost (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (count : ℕ) (past : List (Matching V)) :
    (normalizedRuns heven count past).cost read ≤ count * fullRounds (Fintype.card V) := by
  induction count generalizing past with
  | zero => simp [normalizedRuns]
  | succ count ih =>
      rw [normalizedRuns, Prog.cost_bind]
      have hfirst := fullProgram_cost heven read past
      split_ifs
      · rw [Prog.cost_map]
        have hrest := ih (((fullProgram heven past).eval read).history ++ past)
        nlinarith
      · simp only [Prog.cost_pure, Nat.add_zero]
        nlinarith

theorem normalizedRuns_correct (heven : Even (Fintype.card V))
    (hN : 0 < Fintype.card V) (read : MatchRequest V → Matching V)
    (hlegal : LegalResponses read) (count : ℕ) (past : List (Matching V)) :
    let result := (normalizedRuns heven count past).eval read
    result.complete = true ∧ ∀ S : Finset V,
      (count : ℝ) * min (S.card : ℝ) (Sᶜ.card : ℝ) ≤
        4 * (historyGraph result.history).cut S := by
  induction count generalizing past with
  | zero => simp [normalizedRuns]
  | succ count ih =>
      let first := (fullProgram heven past).eval read
      have hfirst := fullProgram_correct heven hN read hlegal past
      change first.complete = true ∧ _ at hfirst
      let rest := (normalizedRuns heven count (first.history ++ past)).eval read
      have hrest := ih (first.history ++ past)
      change rest.complete = true ∧ _ at hrest
      have hfirstEval : ((fullProgram heven past).eval read).complete = true := hfirst.1
      rw [normalizedRuns, Prog.eval_bind]
      simp only [hfirstEval, ↓reduceIte, Prog.eval_map]
      refine ⟨hrest.1, ?_⟩
      intro S
      change ((count + 1 : ℕ) : ℝ) * min (S.card : ℝ) (Sᶜ.card : ℝ) ≤
        4 * (historyGraph (rest.history ++ first.history)).cut S
      rw [historyGraph_append_cut]
      have h1 := hfirst.2 S
      have h2 := hrest.2 S
      push_cast
      nlinarith

/-- The public bound includes sixteen balanced subgames and four final
matchings. No uncharged normalization repetition occurs downstream. -/
def normalizedRounds (N : ℕ) : ℕ := 16 * balancedRounds N + 4

def cutPlayer (heven : Even (Fintype.card V)) :
    Prog (MatchRequest V) (Matching V) (BalancedResult V) := normalizedRuns heven 4 []

theorem cutPlayer_cost (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) :
    (cutPlayer heven).cost read ≤ normalizedRounds (Fintype.card V) := by
  have h := normalizedRuns_cost heven read 4 []
  simpa only [cutPlayer, fullRounds, normalizedRounds, Nat.mul_add, Nat.mul_one,
    ← Nat.mul_assoc] using h

theorem cutPlayer_expands (heven : Even (Fintype.card V))
    (hN : 0 < Fintype.card V) (read : MatchRequest V → Matching V)
    (hlegal : LegalResponses read) :
    let result := (cutPlayer heven).eval read
    result.complete = true ∧ ∀ S : Finset V,
      min (S.card : ℝ) (Sᶜ.card : ℝ) ≤ (historyGraph result.history).cut S := by
  have h := normalizedRuns_correct heven hN read hlegal 4 []
  refine ⟨h.1, ?_⟩
  intro S
  have hs := h.2 S
  change (4 : ℝ) * min (S.card : ℝ) (Sᶜ.card : ℝ) ≤
    4 * (historyGraph ((cutPlayer heven).eval read).history).cut S at hs
  linarith

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedBatch_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.fullProgram_correct
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.cutPlayer_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.cutPlayer_expands
