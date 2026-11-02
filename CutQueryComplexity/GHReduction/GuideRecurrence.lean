import CutQueryComplexity.GHReduction.GuideSplit

/-! # Solving the repaired same-parameter cost recurrence

The potential combines nonterminal mass and twice the real count minus two.
It pays for internal graph size. Each parent's total child size separately pays
the constant-real-count base calls, including the zero-potential children.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical BigOperators

def guideWork (s r : ℕ) : ℕ := s - r + 2 * (r - 2)

theorem size_le_guideWork {s r : ℕ} (hrs : r ≤ s) (hr : 4 ≤ r) : s ≤ guideWork s r :=
  internal_size_le_mass_potential hrs hr

theorem guideWork_le_twice_size {s r : ℕ} (hrs : r ≤ s) : guideWork s r ≤ 2 * s := by
  unfold guideWork
  omega

variable {V N I : Type} [Fintype V] [DecidableEq V] [Fintype N] [DecidableEq N]
  [Fintype I] [DecidableEq I]

theorem centroid_children_guideWork {M : ℕ} {Q : ℕ → ℕ}
    (family : CanonicalSTFamily M Q) (G : WeightedGraph V) (hG : InputPromise M G)
    (T : GuideTree V N) (hlarge : 2 < T.real.card) :
    (∑ P : T.parts, guideWork
      ((Prog.eval G.cut (centroidShoreProgram family T) P).card + 1)
      ((T.graphGroup P.val).card + 1)) ≤ guideWork (Fintype.card V) T.real.card := by
  have hm := centroid_children_nonterminal_mass family G hG T hlarge
  have hp := centroid_children_real_potential family G hG T hlarge
  simpa only [guideWork, Finset.sum_add_distrib, ← Finset.mul_sum] using
    Nat.add_le_add hm (Nat.mul_le_mul_left 2 hp)

/-- Scalar recurrence used by the actual recursive execution. The `10 * s i`
terms include every base child and are paid before using potential conservation.
No childwise partition of the parent's full graph is asserted. -/
theorem guide_cost_recurrence (cost size work : I → ℕ)
    {n s w fuel ell K overhead : ℕ}
    (hsize : (∑ i, size i) ≤ 2 * s)
    (hwork : (∑ i, work i) ≤ w) (hsw : s ≤ w)
    (hoverhead : n * overhead ≤ ((ell + 3) * s) * K)
    (hchild : ∀ i, n * cost i ≤ (10 * size i + fuel * (ell + 23) * work i) * K) :
    n * (overhead + ∑ i, cost i) ≤
      (10 * s + (fuel + 1) * (ell + 23) * w) * K := by
  have hchildren : n * (∑ i, cost i) ≤
      (10 * (∑ i, size i) + fuel * (ell + 23) * (∑ i, work i)) * K := by
    calc
      _ = ∑ i, n * cost i := Finset.mul_sum _ _ _
      _ ≤ ∑ i, (10 * size i + fuel * (ell + 23) * work i) * K :=
        Finset.sum_le_sum (fun i _ => hchild i)
      _ = _ := by rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]
  have hchildren' : n * (∑ i, cost i) ≤ (20 * s + fuel * (ell + 23) * w) * K := by
    apply hchildren.trans
    apply Nat.mul_le_mul_right K
    have h1 := Nat.mul_le_mul_left 10 hsize
    have h2 := Nat.mul_le_mul_left (fuel * (ell + 23)) hwork
    nlinarith
  calc
    _ = n * overhead + n * (∑ i, cost i) := Nat.mul_add _ _ _
    _ ≤ ((ell + 3) * s) * K + (20 * s + fuel * (ell + 23) * w) * K :=
      Nat.add_le_add hoverhead hchildren'
    _ = ((ell + 23) * s + fuel * (ell + 23) * w) * K := by ring
    _ ≤ ((ell + 23) * w + fuel * (ell + 23) * w) * K :=
      Nat.mul_le_mul_right K (Nat.add_le_add_right (Nat.mul_le_mul_left (ell + 23) hsw) _)
    _ = ((fuel + 1) * (ell + 23) * w) * K := by ring
    _ ≤ _ := Nat.mul_le_mul_right K (Nat.le_add_left _ _)

/-- Cancel the original size only after all contracted sizes have been charged
against the original primitive cost. -/
theorem guide_root_budget {n r cost fuel ell Qn : ℕ} (hn : 0 < n) (hrn : r ≤ n)
    (hcost : n * cost ≤ (10 * n + fuel * (ell + 23) * guideWork n r) * (Qn + n)) :
    cost ≤ (10 + 2 * fuel * (ell + 23)) * (Qn + n) := by
  have hw := guideWork_le_twice_size hrn
  have hmul : n * cost ≤ n * ((10 + 2 * fuel * (ell + 23)) * (Qn + n)) := by
    calc
      _ ≤ (10 * n + fuel * (ell + 23) * guideWork n r) * (Qn + n) := hcost
      _ ≤ (10 * n + fuel * (ell + 23) * (2 * n)) * (Qn + n) :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hw) _)
      _ = _ := by ring
  by_contra h
  have hs : (10 + 2 * fuel * (ell + 23)) * (Qn + n) + 1 ≤ cost := by omega
  have hscaled := Nat.mul_le_mul_left n hs
  nlinarith

/-- The halving inequality gives a uniform public fuel sufficient for every
same-parameter child of an internal node. -/
theorem child_fuel_bound {r p fuel : ℕ}
    (hhalf : 2 * p ≤ r) (hbound : r ≤ 8 * 2 ^ (fuel + 1) + 2) :
    p + 1 ≤ 8 * 2 ^ fuel + 2 := by
  rw [pow_succ] at hbound
  nlinarith

theorem initial_fuel_bound (r : ℕ) : r ≤ 8 * 2 ^ Nat.clog 2 (r + 1) + 2 := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (r + 1)
  omega

end
end CutQueryComplexity.GHReduction
