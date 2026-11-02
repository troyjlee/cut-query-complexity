import CutQueryComplexity.GHReduction.GuideMaximum

/-! # Actual-size costs of the lower-parameter guide branches -/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {V N : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]

theorem guideOneProgram_cost_linear {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) (fuel : ℕ) :
    n * Prog.cost G.cut (guideOneProgram family fuel T) ≤
      Fintype.card V * ((10 + 2 * fuel * (Nat.clog 2 n + 23)) * (Q n + n)) := by
  have h := guideOneProgram_cost_scaled family hQ fuel G hG T hvn
  have hw := guideWork_le_twice_size T.real_card_le
  calc
    _ ≤ (10 * Fintype.card V + fuel * (Nat.clog 2 n + 23) *
        guideWork (Fintype.card V) T.real.card) * (Q n + n) := h
    _ ≤ (10 * Fintype.card V + fuel * (Nat.clog 2 n + 23) *
        (2 * Fintype.card V)) * (Q n + n) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hw) _)
    _ = _ := by ring

theorem guideOneProgram_localFuel_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    n * Prog.cost G.cut (guideOneProgram family (Nat.clog 2 (T.real.card + 1)) T) ≤
      Fintype.card V * guideOneGlobalBudget Q n := by
  have hfuel := Nat.clog_mono_right 2 (Nat.add_le_add_right (T.real_card_le.trans hvn) 1)
  have h := guideOneProgram_cost_linear family G hG T hvn hQ (Nat.clog 2 (T.real.card + 1))
  apply h.trans
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_right
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hfuel)) 10

def sourceSwitchBudget (Q : ℕ → ℕ) (n : ℕ) : ℕ := Q n + n + guideOneGlobalBudget Q n

theorem sourceSwitchProgram_cost_scaled {M n : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    n * Prog.cost G.cut (sourceSwitchProgram family T C a ha) ≤
      Fintype.card V * sourceSwitchBudget Q n := by
  haveI : Nonempty V := ⟨T.source⟩
  have hm : 1 ≤ Fintype.card V := Fintype.card_pos
  have hreg := hQ _ hm hvn
  have hunit := Nat.mul_le_mul_right n hm
  have hcost := Nat.mul_le_mul_left n (sourceSwitchProgram_cost family T C a ha G.cut)
  have hrec := guideOneProgram_localFuel_cost_scaled family G hG (switchedGuide T C a ha) hvn hQ
  unfold sourceSwitchBudget
  nlinarith

theorem cost_le_of_scaled {n m cost budget : ℕ} (hn : 0 < n) (hm : m ≤ n)
    (h : n * cost ≤ m * budget) : cost ≤ budget := by
  have hm' := Nat.mul_le_mul_right budget hm
  by_contra hnot
  have hc : budget + 1 ≤ cost := by omega
  have hc' := Nat.mul_le_mul_left n hc
  nlinarith

def sourceSwitchGlobalTree {M : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (n : ℕ) (T : GuideTree V N) (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ) :
    DTree (Finset V) ℝ (V → Option ℝ) (sourceSwitchBudget Q n) :=
  (Prog.toDTree (sourceSwitchProgram family T C a ha) (sourceSwitchBudget Q n)).map
    (fun out => out.getD (fun _ => none))

theorem sourceSwitchGlobalTree_eval {M n : ℕ} {Q : ℕ → ℕ} (family : CanonicalSTFamily M Q)
    (G : WeightedGraph V) (hG : InputPromise M G) (T : GuideTree V N)
    (C : Finset N) (a : N) (ha : a ∈ T.real ∩ Cᶜ)
    (hvn : Fintype.card V ≤ n) (hQ : SizeRegular n Q) :
    (sourceSwitchGlobalTree family n T C a ha).eval G.cut =
      Prog.eval G.cut (sourceSwitchProgram family T C a ha) := by
  haveI : Nonempty V := ⟨T.source⟩
  have hcost := cost_le_of_scaled (Fintype.card_pos.trans_le hvn) hvn
    (sourceSwitchProgram_cost_scaled family G hG T C a ha hvn hQ)
  simp only [sourceSwitchGlobalTree, DTree.eval_map, Prog.toDTree_eval _ _ _ hcost, Option.getD_some]

end
end CutQueryComplexity.GHReduction
