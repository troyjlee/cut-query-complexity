import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Balanced
import CutQueryComplexity.Model.Prog
import Mathlib.Data.Fintype.Card

/-!
# The public balanced cut-player program

Each next bisection is selected from the explicit matching history by finite
search. Requests include the complete prior matching history, so the response
may be adaptive. These are matching-game rounds, not hidden-graph cut queries.
The eventual matching-flow program must supply their legal responses.

This module proves termination of the balanced subgame. Full-game pruning,
its final matching, and four fresh full runs remain separate constructions.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset Prog
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

structure SparseQuarter (history : List (Matching V)) (S : Finset V) : Prop where
  quarter : Fintype.card V ≤ 4 * S.card
  half : 2 * S.card ≤ Fintype.card V
  sparse : 4 * (historyGraph history).cut S < (S.card : ℝ)

/-- All inputs are public: this search never reads an unknown input graph. -/
def chooseQuarter (history : List (Matching V)) :
    Option {S : Finset V // SparseQuarter history S} :=
  if h : ∃ S, SparseQuarter history S then
    some ⟨Classical.choose h, Classical.choose_spec h⟩
  else none

theorem chooseQuarter_none_iff (history : List (Matching V)) :
    chooseQuarter history = none ↔ ∀ S, ¬ SparseQuarter history S := by
  unfold chooseQuarter
  split_ifs with h
  · simp only [Option.some_ne_none, false_iff]
    exact not_forall.mpr ⟨Classical.choose h, not_not.mpr (Classical.choose_spec h)⟩
  · simp only [true_iff]
    exact fun S hs => h ⟨S, hs⟩

/-- Deterministic completion of a small public shore to half the vertices. -/
def halfCompletion (heven : Even (Fintype.card V)) (S : Finset V)
    (hsmall : S.card ≤ Fintype.card V / 2) : Bisection V := by
  let existsHalf := Finset.exists_superset_card_eq (s := S) hsmall (Nat.div_le_self _ _)
  let T := Classical.choose existsHalf
  have ht : S ⊆ T ∧ T.card = Fintype.card V / 2 := Classical.choose_spec existsHalf
  refine ⟨T, ?_⟩
  rw [card_compl, ht.2]
  obtain ⟨k, hk⟩ := heven
  omega

theorem halfCompletion_contains (heven : Even (Fintype.card V)) (S : Finset V)
    (hsmall : S.card ≤ Fintype.card V / 2) : S ⊆ (halfCompletion heven S hsmall).shore := by
  exact (Classical.choose_spec
    (Finset.exists_superset_card_eq (s := S) hsmall (Nat.div_le_self _ _))).1

structure MatchRequest (V : Type) [Fintype V] [DecidableEq V] where
  history : List (Matching V)
  cut : Bisection V

def LegalResponses (read : MatchRequest V → Matching V) : Prop :=
  ∀ request, (read request).Crosses request.cut.shore

structure BalancedResult (V : Type) where
  history : List (Matching V)
  complete : Bool

def balancedProgram (heven : Even (Fintype.card V)) :
    ℕ → List (Matching V) → List (Matching V) →
      Prog (MatchRequest V) (Matching V) (BalancedResult V)
  | 0, _past, history => .pure ⟨history, (chooseQuarter history).isNone⟩
  | fuel + 1, past, history =>
      match chooseQuarter history with
      | none => .pure ⟨history, true⟩
      | some chosen =>
          let hsmall : chosen.val.card ≤ Fintype.card V / 2 := by
            have h := chosen.property.half
            omega
          let cut := halfCompletion heven chosen.val hsmall
          Prog.query ⟨history ++ past, cut⟩ fun M =>
            if M.Crosses cut.shore then balancedProgram heven fuel past (M :: history)
            else .pure ⟨history, false⟩

theorem balancedProgram_cost (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (fuel : ℕ) (past history : List (Matching V)) :
    (balancedProgram heven fuel past history).cost read ≤ fuel := by
  induction fuel generalizing history with
  | zero => simp [balancedProgram]
  | succ fuel ih =>
      rw [balancedProgram]
      cases hc : chooseQuarter history with
      | none => simp
      | some chosen =>
          change ((if _ then balancedProgram heven fuel past (_ :: history)
            else Prog.pure ⟨history, false⟩).cost read + 1) ≤ fuel + 1
          split_ifs
          · exact Nat.succ_le_succ (ih _)
          · simp

theorem balancedProgram_spec (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (fuel : ℕ) (past history : List (Matching V)) :
    let result := (balancedProgram heven fuel past history).eval read
    result.complete = true → ∀ S, ¬ SparseQuarter result.history S := by
  induction fuel generalizing history with
  | zero =>
      simp only [balancedProgram, Prog.eval_pure]
      cases hc : chooseQuarter history with
      | none => exact fun _ => (chooseQuarter_none_iff history).mp hc
      | some chosen => simp
  | succ fuel ih =>
      rw [balancedProgram]
      cases hc : chooseQuarter history with
      | none => exact fun _ => (chooseQuarter_none_iff history).mp hc
      | some chosen =>
          simp only [Prog.eval, Prog.run]
          split_ifs
          · exact ih _
          · simp

def progressUnit (V : Type) [Fintype V] : ℝ := gapConstant * Fintype.card V / 64

/-- If the public subgame has not stopped, each of its actually executed
legal responses contributes the proved constant potential increment. -/
theorem balancedProgram_progress (heven : Even (Fintype.card V))
    (read : MatchRequest V → Matching V) (hlegal : LegalResponses read)
    (fuel : ℕ) (past history : List (Matching V)) :
    let result := (balancedProgram heven fuel past history).eval read
    result.complete = true ∨
      potential history + (fuel : ℝ) * progressUnit V ≤ potential result.history := by
  induction fuel generalizing history with
  | zero => right; simp [balancedProgram]
  | succ fuel ih =>
      rw [balancedProgram]
      cases hc : chooseQuarter history with
      | none => exact Or.inl rfl
      | some chosen =>
          let hsmall : chosen.val.card ≤ Fintype.card V / 2 := by
            have h := chosen.property.half
            omega
          let cut := halfCompletion heven chosen.val hsmall
          let request : MatchRequest V := ⟨history ++ past, cut⟩
          let M := read request
          have hM : M.Crosses cut.shore := hlegal request
          have hcross : ∀ v ∈ chosen.val, M.mate v ∉ chosen.val := by
            intro v hv hmate
            have hcut := halfCompletion_contains heven chosen.val hsmall
            exact ((hM v).mp (hcut hv)) (hcut hmate)
          have hg := balanced_progress history chosen.val M chosen.property.quarter
            chosen.property.sparse.le hcross
          change progressUnit V ≤ potential (M :: history) - potential history at hg
          change ((if M.Crosses cut.shore then balancedProgram heven fuel past (M :: history)
            else Prog.pure ⟨history, false⟩).eval read).complete = true ∨
            potential history + ((fuel + 1 : ℕ) : ℝ) * progressUnit V ≤
              potential ((if M.Crosses cut.shore then balancedProgram heven fuel past (M :: history)
                else Prog.pure ⟨history, false⟩).eval read).history
          simp only [hM, ↓reduceIte]
          rcases ih (M :: history) with done | progress
          · exact Or.inl done
          · right
            push_cast
            linarith

/-- A public finite round limit obtained from the proved analytic constant.
Its logarithmic size is an arithmetic lemma, separate from game correctness. -/
def balancedRounds (N : ℕ) : ℕ := ⌈64 / gapConstant * Real.log (N : ℝ)⌉₊ + 1

theorem balancedRounds_progress (hN : 0 < Fintype.card V) :
    (Fintype.card V : ℝ) * Real.log (Fintype.card V : ℝ) <
      (balancedRounds (Fintype.card V) : ℝ) * progressUnit V := by
  have hc := Nat.le_ceil (64 / gapConstant * Real.log (Fintype.card V : ℝ))
  have hg := gapConstant_pos
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  have hround : 64 / gapConstant * Real.log (Fintype.card V : ℝ) <
      (balancedRounds (Fintype.card V) : ℝ) := by
    simp only [balancedRounds, Nat.cast_add, Nat.cast_one]
    linarith
  have hm := mul_lt_mul_of_pos_right hround hg
  have he : (64 / gapConstant * Real.log (Fintype.card V : ℝ)) * gapConstant =
      64 * Real.log (Fintype.card V : ℝ) := by field_simp
  rw [he] at hm
  have hmn := mul_lt_mul_of_pos_right hm hn
  unfold progressUnit
  nlinarith

theorem balancedProgram_finishes (heven : Even (Fintype.card V))
    (hN : 0 < Fintype.card V) (read : MatchRequest V → Matching V)
    (hlegal : LegalResponses read) (past : List (Matching V)) :
    ((balancedProgram heven (balancedRounds (Fintype.card V)) past []).eval read).complete = true := by
  rcases balancedProgram_progress heven read hlegal (balancedRounds (Fintype.card V)) past [] with
    done | progress
  · exact done
  · have hbound := potential_le
      ((balancedProgram heven (balancedRounds (Fintype.card V)) past []).eval read).history hN
    have hstrict := balancedRounds_progress hN
    rw [potential_nil, zero_add] at progress
    linarith

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedProgram_cost
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedProgram_progress
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.balancedProgram_finishes
