import CutQueryComplexity.Probability.Events
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor

/-! # Hard query caps and expected-cost bounds

Truncation is an actual stochastic tree. Its output law is coupled to the
original run, preserving precisely those executions that finish within the cap.
The original tree may have any finite public horizon; no output or answer
alphabet finiteness is required. Unbounded processes are a separate interface.
-/
namespace CutQueryComplexity.RTree
noncomputable section
open scoped Classical NNReal ENNReal
open Probability
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {I A O X : Type} {q : ℕ}

/-- Stop before query `k+1`, reporting absence if the program has not halted. -/
def truncate : {q : ℕ} → RTree I A O q → (k : ℕ) → RTree I A (Option O) k
  | 0, T, _ => pure (PMF.map some T)
  | _ + 1, T, 0 => PMF.map (fun action => match action with
      | Sum.inl o => some o
      | Sum.inr _ => none) T
  | _ + 1, T, k + 1 => PMF.map (fun action => match action with
      | Sum.inl o => Sum.inl (some o)
      | Sum.inr (i, next) => Sum.inr (i, fun a => truncate (next a) k)) T

/-- Exact coupling of the capped algorithm with the original output and query count. -/
theorem eval_truncate (T : RTree I A O q) (k : ℕ) (read : I → A) :
    (T.truncate k).eval read = (run read T).map (fun p => if p.2 ≤ k then some p.1 else none) := by
  induction q generalizing k with
  | zero => simp [truncate, eval, run, PMF.map_comp, Function.comp_def]
  | succ q ih =>
      cases k with
      | zero =>
          simp only [truncate, eval, run, PMF.map_comp, PMF.map_bind, Function.comp_def]
          rw [PMF.map]
          congr 1
          funext action
          rcases action with o | ⟨i, next⟩
          · simp [PMF.pure_map]
          · simp only [PMF.map_comp, Function.comp_def, Nat.not_succ_le_zero, ↓reduceIte]
            exact (PMF.map_const (run read (next (read i))) none).symm
      | succ k =>
          simp only [truncate, eval, run, PMF.bind_map, PMF.map_bind, Function.comp_def]
          congr 1
          funext action
          rcases action with o | ⟨i, next⟩
          · simp [PMF.pure_map]
          · simp only [PMF.map_comp, Function.comp_def, Nat.add_le_add_iff_right]
            exact ih (next (read i)) k

/-- Expected actual query count, with extended nonnegative values. -/
def expectedQueries (T : RTree I A O q) (read : I → A) : ℝ≥0∞ :=
  ∑' p, run read T p * (p.2 : ℝ≥0∞)

theorem expectedQueries_le_budget (T : RTree I A O q) (read : I → A) :
    T.expectedQueries read ≤ (q : ℝ≥0∞) := by
  calc
    _ ≤ ∑' p, run read T p * (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro p
      by_cases hp : p ∈ (run read T).support
      · apply mul_le_mul le_rfl _ (by positivity) (by positivity)
        exact_mod_cast cost_le T read hp
      · have hz : run read T p = 0 := by simpa only [PMF.mem_support_iff, not_not] using hp
        simp [hz]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The abort probability is exactly the probability that the original run exceeds the cap. -/
theorem truncate_abort (T : RTree I A O q) (k : ℕ) (read : I → A) :
    mass ((T.truncate k).eval read) (fun o => o = none) =
      mass (run read T) (fun p => k < p.2) := by
  rw [eval_truncate, mass_map]
  congr 1
  funext p
  by_cases h : p.2 ≤ k <;> simp_all

/-- Discrete Markov inequality with the sharp `k+1` denominator. -/
theorem truncate_markov (T : RTree I A O q) (k : ℕ) (read : I → A) :
    (k + 1 : ℝ≥0∞) * mass ((T.truncate k).eval read) (fun o => o = none) ≤
      T.expectedQueries read := by
  rw [truncate_abort, mass_eq_tsum, expectedQueries, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro p
  by_cases h : k < p.2
  · simp only [if_pos h]
    rw [mul_comm]
    apply mul_le_mul le_rfl _ (by positivity) (by positivity)
    exact_mod_cast Nat.succ_le_of_lt h
  · simp [h]

/-- Any expected-cost estimate gives a concrete bound on extra abort probability. -/
theorem truncate_abort_le (T : RTree I A O q) (k : ℕ) (read : I → A) {η : ℝ≥0∞}
    (h : T.expectedQueries read ≤ (k + 1 : ℝ≥0∞) * η) :
    mass ((T.truncate k).eval read) (fun o => o = none) ≤ η := by
  exact (ENNReal.mul_le_mul_iff_right (by simp : (k + 1 : ℝ≥0∞) ≠ 0)
    (by simp)).mp ((truncate_markov T k read).trans h)

/-- Finishing successfully before the cap implies correctness of the truncated output. -/
theorem truncate_failure_le (T : RTree I A O q) (k : ℕ) (read : I → A) (Good : O → Prop)
    {δ η : ℝ≥0∞} (hgood : mass (T.eval read) (fun o => ¬Good o) ≤ δ)
    (hcost : T.expectedQueries read ≤ (k + 1 : ℝ≥0∞) * η) :
    mass ((T.truncate k).eval read) (fun o => ¬o.elim False Good) ≤ δ + η := by
  rw [eval_truncate, mass_map]
  have hunion : mass (run read T) (fun p => ¬(if p.2 ≤ k then some p.1 else none).elim False Good) ≤
      mass (run read T) (fun p => ¬Good p.1) + mass (run read T) (fun p => k < p.2) := by
    simp only [mass_eq_tsum, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro p
    by_cases hc : p.2 ≤ k
    · by_cases hg : Good p.1 <;> simp [hc, hg, Nat.not_lt.mpr hc]
    · simp [hc, Nat.lt_of_not_ge hc]
  apply hunion.trans
  have hg : mass (run read T) (fun p => ¬Good p.1) ≤ δ := by
    simpa only [eval, mass_map] using hgood
  have ht := truncate_abort_le T k read hcost
  rw [truncate_abort] at ht
  exact add_le_add hg ht

/-- Truncate at `ceil(B/η)` queries, adding at most `η` to the failure probability. -/
theorem truncate_solves (T : RTree I A O q) (read : X → I → A) (Good : X → O → Prop)
    {B δ η : ℝ} (_hB : 0 ≤ B) (hδ : 0 ≤ δ) (hη : 0 < η)
    (hT : T.SolvesWithError read Good δ)
    (hcost : ∀ x, T.expectedQueries (read x) ≤ ENNReal.ofReal B) :
    (T.truncate ⌈B / η⌉₊).SolvesWithError read
      (fun x o => o.elim False (Good x)) (δ + η) := by
  intro x
  rw [successProb_eq]
  apply success_of_failure_le _ _ (by linarith)
  have hcap : B ≤ ((⌈B / η⌉₊ : ℝ) + 1) * η := by
    have hc := Nat.le_ceil (B / η)
    have hb := (div_le_iff₀ hη).mp hc
    nlinarith
  have hbound : T.expectedQueries (read x) ≤
      (↑⌈B / η⌉₊ + 1 : ℝ≥0∞) * ENNReal.ofReal η := by
    refine (hcost x).trans ?_
    have hh := ENNReal.ofReal_le_ofReal hcap
    rw [ENNReal.ofReal_mul (show 0 ≤ (⌈B / η⌉₊ : ℝ) + 1 by positivity)] at hh
    simpa only [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hh
  have hg := failure_le_of_success (T.eval (read x)) (Good x) hδ
    (by simpa only [mass, ← successProb_eq] using hT x)
  have hf := truncate_failure_le T _ (read x) (Good x) hg hbound
  simpa only [ENNReal.ofReal_add hδ hη.le] using hf

end
end CutQueryComplexity.RTree
