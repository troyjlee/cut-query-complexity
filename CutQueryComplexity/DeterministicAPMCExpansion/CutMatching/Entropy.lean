import CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entropy of the public matching walk

The potential starts at zero, is nondecreasing, and is bounded by `N log N`.
The quantitative increment for a sparse balanced cut is a separate obligation;
these elementary bounds alone do not establish a logarithmic strategy.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

open Finset
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def entropy (p : V → ℝ) : ℝ := ∑ v, Real.negMulLog (p v)

/-- Averaging increases entropy; this uses the corrected sign of the
increment in the displayed calculation following KKOV Lemma 4.6. -/
theorem entropy_pair_average (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.negMulLog p + Real.negMulLog q ≤ 2 * Real.negMulLog ((p + q) / 2) := by
  have h := Real.concaveOn_negMulLog.2 hp hq
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  have he : (1 / 2 : ℝ) * p + (1 / 2 : ℝ) * q = (p + q) / 2 := by ring
  rw [he] at h
  linarith

theorem entropy_average_mono (M : Matching V) (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) :
    entropy p ≤ entropy (average M p) := by
  have h := sum_le_sum (s := (univ : Finset V)) fun v _ =>
    entropy_pair_average (p v) (p (M.mate v)) (hp v) (hp (M.mate v))
  change (∑ v, (Real.negMulLog (p v) + Real.negMulLog (p (M.mate v)))) ≤
    ∑ v, 2 * Real.negMulLog (average M p v) at h
  have hperm : (∑ v, Real.negMulLog (p (M.mate v))) =
      ∑ v, Real.negMulLog (p v) := Equiv.sum_comp M.mate (fun v => Real.negMulLog (p v))
  rw [sum_add_distrib, hperm, ← mul_sum] at h
  unfold entropy
  linarith

/-- A finite nonnegative probability vector has entropy at most log N.
Apply `negMulLog x ≤ 1-x` to the scaled entries `N*p v`; the sum of its
right-hand sides is zero. This also handles zero entries exactly. -/
theorem entropy_le_log_card (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (hsum : ∑ v, p v = 1) (hN : 0 < Fintype.card V) :
    entropy p ≤ Real.log (Fintype.card V : ℝ) := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  have h := sum_le_sum (s := (univ : Finset V)) fun v _ =>
    Real.negMulLog_le_one_sub_self (mul_nonneg hn.le (hp v))
  have hleft : (∑ v, Real.negMulLog ((Fintype.card V : ℝ) * p v)) =
      Real.negMulLog (Fintype.card V : ℝ) + (Fintype.card V : ℝ) * entropy p := by
    simp only [entropy, Real.negMulLog_mul, sum_add_distrib, ← sum_mul, ← mul_sum,
      hsum, one_mul]
  have hright : (∑ v, (1 - (Fintype.card V : ℝ) * p v)) = 0 := by
    simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
      ← mul_sum, hsum, sub_self]
  rw [hleft, hright, Real.negMulLog] at h
  have hmul : (Fintype.card V : ℝ) * entropy p ≤
      (Fintype.card V : ℝ) * Real.log (Fintype.card V : ℝ) := by linarith
  exact le_of_mul_le_mul_left hmul hn

def potential (history : List (Matching V)) : ℝ :=
  ∑ u, entropy (walk history u)

@[simp] theorem potential_nil : potential ([] : List (Matching V)) = 0 := by
  simp [potential, entropy, walk, Real.negMulLog]

theorem potential_cons_mono (M : Matching V) (history : List (Matching V)) :
    potential history ≤ potential (M :: history) := by
  apply sum_le_sum
  intro u _
  exact entropy_average_mono M (walk history u) (walk_nonneg history u)

theorem potential_le (history : List (Matching V)) (hN : 0 < Fintype.card V) :
    potential history ≤ (Fintype.card V : ℝ) * Real.log (Fintype.card V : ℝ) := by
  have h := sum_le_sum (s := (univ : Finset V)) fun u _ =>
    entropy_le_log_card (walk history u) (walk_nonneg history u) (walk_row_sum history u) hN
  simpa only [sum_const, card_univ, nsmul_eq_mul, potential] using h

end
end CutQueryComplexity.DeterministicAPMCExpansion.CutMatching

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropy_pair_average
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.entropy_le_log_card
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.potential_cons_mono
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.CutMatching.potential_le
