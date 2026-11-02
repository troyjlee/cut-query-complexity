import CutQueryComplexity.GHReduction.GuideOneBudget

/-! # One-respecting calls under original-input size regularity

Every call, including calls on contracted graphs, is justified using the single
regularity hypothesis at the original size `n`. The generous local hard cap
depends on `n`; the sharper realized-cost theorem still depends on actual size.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

def guideOneGlobalBudget (Q : ℕ → ℕ) (n : ℕ) : ℕ :=
  (10 + 2 * Nat.clog 2 (n + 1) * (Nat.clog 2 n + 23)) * (Q n + n)

theorem guideOneProgram_global_cost {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    Prog.cost G.cut (guideOneProgram family (Nat.clog 2 (n + 1)) T) ≤
      guideOneGlobalBudget Q n := by
  haveI : Nonempty V := ⟨T.source⟩
  have hn : 0 < n := Fintype.card_pos.trans_le hvn
  have h := guideOneProgram_cost_scaled family hQ (Nat.clog 2 (n + 1)) G hG T hvn
  have hw : guideWork (Fintype.card V) T.real.card ≤ 2 * n :=
    (guideWork_le_twice_size T.real_card_le).trans (Nat.mul_le_mul_left 2 hvn)
  have hmul : n * Prog.cost G.cut (guideOneProgram family (Nat.clog 2 (n + 1)) T) ≤
      n * guideOneGlobalBudget Q n := by
    calc
      _ ≤ (10 * Fintype.card V + Nat.clog 2 (n + 1) * (Nat.clog 2 n + 23) *
          guideWork (Fintype.card V) T.real.card) * (Q n + n) := h
      _ ≤ (10 * n + Nat.clog 2 (n + 1) * (Nat.clog 2 n + 23) * (2 * n)) * (Q n + n) :=
        Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.mul_le_mul_left 10 hvn)
          (Nat.mul_le_mul_left _ hw))
      _ = _ := by unfold guideOneGlobalBudget; ring
  by_contra hbad
  have hstep : guideOneGlobalBudget Q n + 1 ≤
      Prog.cost G.cut (guideOneProgram family (Nat.clog 2 (n + 1)) T) := by omega
  have hscaled := Nat.mul_le_mul_left n hstep
  nlinarith

def guideOneGlobalTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (T : GuideTree V N) :
    DTree (Finset V) ℝ (Option (V → Option (CutCandidate V))) (guideOneGlobalBudget Q n) :=
  Prog.toDTree (guideOneProgram family (Nat.clog 2 (n + 1)) T) (guideOneGlobalBudget Q n)

theorem guideOneGlobalTree_eval {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    (guideOneGlobalTree family n T).eval G.cut =
      some (Prog.eval G.cut (guideOneProgram family (Nat.clog 2 (n + 1)) T)) :=
  Prog.toDTree_eval _ _ _ (guideOneProgram_global_cost family G hG T hvn hQ)

theorem guideOneGlobalTree_complete {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q)
    {t : V} (ht : t ∈ T.realVertices)
    (hrespect : ∃ S, IsSTMinCut G t T.source S ∧ T.RespectsCut S 1) :
    ∃ output C, (guideOneGlobalTree family n T).eval G.cut = some output ∧
      output t = some C ∧ CandidateExact G T.source t C := by
  have hdepth := (T.real_card_le.trans hvn).trans (initial_fuel_bound n)
  obtain ⟨C, hC, hexact⟩ := guideOneProgram_complete family _ G hG T hdepth t ht hrespect
  exact ⟨_, C, guideOneGlobalTree_eval family G hG T hvn hQ, hC, hexact⟩

end
end CutQueryComplexity.GHReduction
