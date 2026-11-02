import CutQueryComplexity.GHReduction.Randomized.CallOps

/-! # A reference exact family

The reconstruction family recovers the contracted instance from its `k` singleton
and `C(k,2)` pair cuts, then returns the canonical shore offline. It is exact on
every graph, so it is a `CanonicalSTFamily M refCost` for every `M`, and its
cost is size-regular at every size.

It is a proof device: the bridge lemmas of Phase 3 say that the old reduction,
run with *any* exact family, evaluates to the ideal output of its call-language
twin. Instantiating them with this family transfers the old correctness
theorems to the ideal output. It is never part of a program.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction.Randomized
noncomputable section
open scoped Classical
open WeightedGraph

/-- Singleton and pair cuts of a `k`-vertex graph. -/
def refCost (k : ℕ) : ℕ := k + k.choose 2

/-- Reconstruct the instance, then select its canonical shore offline. -/
def refFamily (M : ℕ) : CanonicalSTFamily M refCost where
  program k s t := ((reconstruct (V := Fin k)).map (fun H => idealShore H s t)).cast
    (by rw [Fintype.card_fin]; rfl)
  correct k s t hst G _ _ := by
    have h : (reconstruct (V := Fin k)).eval G.cut = G := by
      simp [DTree.eval, reconstruct_run]
    simpa only [DTree.eval_cast, DTree.eval_map, h] using idealShore_spec G hst

theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd

/-- The reference cost is size-regular at every size. -/
theorem sizeRegular_refCost (n : ℕ) : SizeRegular n refCost := by
  intro s _ hsn
  have hs := two_mul_choose_two s
  have hn := two_mul_choose_two n
  have hmul : n * (s * (s - 1)) ≤ s * (n * (n - 1)) := by
    calc
      n * (s * (s - 1)) = s * (n * (s - 1)) := by ring
      _ ≤ s * (n * (n - 1)) :=
        Nat.mul_le_mul_left s (Nat.mul_le_mul_left n (Nat.sub_le_sub_right hsn 1))
  apply Nat.le_of_mul_le_mul_left _ (show 0 < 2 by norm_num)
  simp only [refCost]
  calc
    2 * (n * (s + s.choose 2)) = 2 * (n * s) + n * (2 * s.choose 2) := by ring
    _ = 2 * (n * s) + n * (s * (s - 1)) := by rw [hs]
    _ ≤ 2 * (s * n) + s * (n * (n - 1)) := by rw [Nat.mul_comm n s]; omega
    _ = 2 * (s * (n + n.choose 2)) := by rw [← hn]; ring

end
end CutQueryComplexity.GHReduction.Randomized
