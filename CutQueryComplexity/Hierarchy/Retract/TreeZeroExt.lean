import CutQueryComplexity.Hierarchy.Retract.Rounding
import CutQueryComplexity.Hierarchy.GuardTransfer

/-! # The aggregate tree 0-extension bound (B3)

The limits are taken in a fixed order, on the finite set of terminal-fixing maps.

1. Positive lengths (`exists_fixing_cost_le_of_pos`): by `exists_gridRound_le`, for every mesh
   `m ≥ 1` some fixing map costs at most `42 Σ cap ℓ + E / m`, with `E = 14 Σ cap r` independent
   of `m`. The cost is minimized over the finite set of fixing maps, so `m → ∞` gives the
   bound `42 Σ cap ℓ` (`Retract.exists_le_of_forall_pos`).
2. Nonnegative lengths (`exists_fixing_cost_le`): apply step 1 to `ℓ + ε`. The cost is monotone
   in the lengths, so some fixing map costs at most `42 Σ cap ℓ + 42 ε Σ cap`; let `ε → 0` on
   the same finite set.

`treeZeroExt_42 : TreeZeroExt 42`, without using the childless-leaf hypothesis. With the
minimax duality and the cut transfer, `exists_constantCutGuard : ∃ ρ0, 1 ≤ ρ0 ∧
ConstantCutGuard ρ0` (with `ρ0 = 42`).
-/

namespace CutQueryComplexity
namespace Hierarchy
namespace Hier

open Finset TwoRespecting

variable {V : Type} [Fintype V] [DecidableEq V] {N : Type} [Fintype N] [DecidableEq N]
variable (H : Hier V N) [Nonempty V]

/-- The bound for positive lengths. -/
theorem exists_fixing_cost_le_of_pos (cap ℓ : N → ℝ) (hcap : ∀ x, 0 ≤ cap x)
    (hℓ : ∀ e, 0 < ℓ e) :
    ∃ f : N → V, H.Fixing f ∧
      ∑ y ∈ H.edges, cap y * H.terminalDist ℓ (f y) (f (H.T.parent y)) ≤
        42 * ∑ y ∈ H.edges, cap y * ℓ y := by
  classical
  set E := 14 * ∑ y ∈ H.edges, cap y * H.rdist ℓ y
  have hE : 0 ≤ E := mul_nonneg (by norm_num) (sum_nonneg fun y _ =>
    mul_nonneg (hcap y) (H.rdist_nonneg (fun e => (hℓ e).le) y))
  obtain ⟨f, hf, hle⟩ := Retract.exists_le_of_forall_pos (univ.filter H.Fixing)
    (fun f : N → V => ∑ y ∈ H.edges, cap y * H.terminalDist ℓ (f y) (f (H.T.parent y)))
    (42 * ∑ y ∈ H.edges, cap y * ℓ y) (fun ε hε => by
      set m := ⌈E / ε⌉₊ + 1
      have hm : 0 < m := Nat.succ_pos _
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hEm : E / m ≤ ε := by
        have h1 : E / ε < m := by
          have := Nat.le_ceil (E / ε)
          simp only [m]; push_cast; linarith
        rw [div_lt_iff₀ hε] at h1
        rw [div_le_iff₀ hmR]; linarith
      obtain ⟨f, hf, hc⟩ := H.exists_gridRound_le hℓ cap hcap hm
      exact ⟨f, mem_filter.mpr ⟨mem_univ _, hf⟩, hc.trans (by linarith)⟩)
  exact ⟨f, (mem_filter.mp hf).2, hle⟩

omit [Nonempty V] in
/-- The terminal distance is monotone in the lengths. -/
theorem terminalDist_mono {ℓ ℓ' : N → ℝ} (h : ∀ e, ℓ e ≤ ℓ' e) (u v : V) :
    H.terminalDist ℓ u v ≤ H.terminalDist ℓ' u v :=
  sum_le_sum fun e _ => by split_ifs; exacts [le_rfl, h e]

/-- **The aggregate tree 0-extension bound** with constant `42`, for nonnegative lengths. -/
theorem exists_fixing_cost_le (cap ℓ : N → ℝ) (hcap : ∀ x, 0 ≤ cap x) (hℓ : ∀ e, 0 ≤ ℓ e) :
    ∃ f : N → V, H.Fixing f ∧
      ∑ y ∈ H.edges, cap y * H.terminalDist ℓ (f y) (f (H.T.parent y)) ≤
        42 * ∑ y ∈ H.edges, cap y * ℓ y := by
  classical
  set C := ∑ y ∈ H.edges, cap y
  have hC : 0 ≤ C := sum_nonneg fun y _ => hcap y
  obtain ⟨f, hf, hle⟩ := Retract.exists_le_of_forall_pos (univ.filter H.Fixing)
    (fun f : N → V => ∑ y ∈ H.edges, cap y * H.terminalDist ℓ (f y) (f (H.T.parent y)))
    (42 * ∑ y ∈ H.edges, cap y * ℓ y) (fun ε hε => by
      set ε' := ε / (42 * C + 1)
      have hε' : 0 < ε' := div_pos hε (by linarith)
      obtain ⟨f, hf, hc⟩ := H.exists_fixing_cost_le_of_pos cap (fun e => ℓ e + ε') hcap
        (fun e => by linarith [hℓ e])
      refine ⟨f, mem_filter.mpr ⟨mem_univ _, hf⟩, ?_⟩
      have hmono : ∑ y ∈ H.edges, cap y * H.terminalDist ℓ (f y) (f (H.T.parent y)) ≤
          ∑ y ∈ H.edges, cap y * H.terminalDist (fun e => ℓ e + ε') (f y) (f (H.T.parent y)) :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          (H.terminalDist_mono (fun e => by linarith) _ _) (hcap y)
      have hsplit : ∑ y ∈ H.edges, cap y * (ℓ y + ε') = ∑ y ∈ H.edges, cap y * ℓ y + ε' * C := by
        rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun y _ => by ring
      have hsmall : 42 * (ε' * C) ≤ ε := by
        have : ε' * (42 * C + 1) = ε := div_mul_cancel₀ ε (by linarith)
        nlinarith
      rw [hsplit] at hc
      linarith)
  exact ⟨f, (mem_filter.mp hf).2, hle⟩

end Hier

/-- **B3.** The aggregate tree 0-extension bound holds with constant `42`. -/
theorem treeZeroExt_42 : TreeZeroExt 42 := by
  intro V M _ _ _ _ _ H _ cap ℓ hcap hℓ
  exact H.exists_fixing_cost_le cap ℓ hcap hℓ

/-- `TreeZeroExt` is monotone in the constant. -/
theorem TreeZeroExt.mono {α β : ℝ} (h : TreeZeroExt α) (hαβ : α ≤ β) : TreeZeroExt β := by
  intro V M _ _ _ _ _ H hlc cap ℓ hcap hℓ
  obtain ⟨f, hf, hle⟩ := h V M H hlc cap ℓ hcap hℓ
  have : 0 ≤ ∑ y ∈ H.edges, cap y * ℓ y := Finset.sum_nonneg fun y _ => mul_nonneg (hcap y) (hℓ y)
  exact ⟨f, hf, hle.trans (by nlinarith)⟩

/-- The tree 0-extension bound with constant `100`, implied by `treeZeroExt_42`. -/
theorem treeZeroExt_100 : TreeZeroExt 100 := treeZeroExt_42.mono (by norm_num)

/-- **B4.** A load-bounded distribution of retractions with constant `42`. -/
theorem retractionBound_42 : RetractionBound 42 := retractionBound_of_treeZeroExt treeZeroExt_42

/-- **B4.** The constant-quality terminal cut guard (Lemma 19) holds with `ρ0 = 42`. -/
theorem constantCutGuard_42 : ConstantCutGuard 42 :=
  constantCutGuard_of_retractionBound (by norm_num) retractionBound_42

/-- **B4.** The constant-quality terminal cut guard, with the constant outside. -/
theorem exists_constantCutGuard : ∃ ρ0 : ℝ, 1 ≤ ρ0 ∧ ConstantCutGuard ρ0 :=
  ⟨42, by norm_num, constantCutGuard_42⟩

end Hierarchy
end CutQueryComplexity
