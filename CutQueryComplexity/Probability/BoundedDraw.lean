import CutQueryComplexity.Probability.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Exponential moments of bounded draws

A draw supported on `[0,1]` satisfies the Bernoulli chord bound for every
real exponential parameter, including negative parameters. Finite lists of
independent draws therefore have moment bound `exp ((exp t - 1) * μ)`.
The bundled draw carries its support proof, so its real mean is always finite.
-/

namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical ENNReal
variable {α : Type*}

theorem exp_mul_le_chord (t : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (t * x) ≤ (1 - x) + x * Real.exp t := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
    (sub_nonneg.mpr hx1) hx (by ring : (1 - x) + x = 1)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, mul_comm x t] using h

/-- A bound valid for both signs of `t`; the given mean is a finite nonnegative real. -/
theorem expMoment_le_of_unitInterval (p : PMF α) (f : α → ℝ)
    (hf : ∀ x ∈ p.support, 0 ≤ f x ∧ f x ≤ 1) {μ : ℝ} (hμ : 0 ≤ μ)
    (hm : expect p (fun x => ENNReal.ofReal (f x)) = ENNReal.ofReal μ) (t : ℝ) :
    expMoment p f t ≤ ENNReal.ofReal (Real.exp ((Real.exp t - 1) * μ)) := by
  let A := expect p (fun x => ENNReal.ofReal (1 - f x))
  have ha : A ≤ 1 := by
    apply expect_le_of_le_on_support
    intro x hx
    exact (ENNReal.ofReal_le_ofReal (by linarith [(hf x hx).1])).trans_eq ENNReal.ofReal_one
  have haf : A ≠ ∞ := ne_of_lt (ha.trans_lt ENNReal.one_lt_top)
  have hasum : A + ENNReal.ofReal μ = 1 := by
    rw [← hm, ← expect_add]
    calc
      _ = expect p (fun _ => 1) := expect_congr_on_support p (fun x hx => by
        rw [← ENNReal.ofReal_add (sub_nonneg.mpr (hf x hx).2) (hf x hx).1]
        simp)
      _ = 1 := expect_const p 1
  have hareal : A.toReal + μ = 1 := by
    have h := congrArg ENNReal.toReal hasum
    simpa only [ENNReal.toReal_add haf ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hμ, ENNReal.toReal_one] using h
  calc
    _ ≤ expect p (fun x => ENNReal.ofReal (1 - f x) +
        ENNReal.ofReal (f x) * ENNReal.ofReal (Real.exp t)) := by
      apply expect_mono_on_support
      intro x hx
      rw [← ENNReal.ofReal_mul (hf x hx).1,
        ← ENNReal.ofReal_add (sub_nonneg.mpr (hf x hx).2)
          (mul_nonneg (hf x hx).1 (Real.exp_pos t).le)]
      exact ENNReal.ofReal_le_ofReal (exp_mul_le_chord t (hf x hx).1 (hf x hx).2)
    _ = A + ENNReal.ofReal μ * ENNReal.ofReal (Real.exp t) := by
      rw [expect_add, expect_mul_const, hm]
    _ = ENNReal.ofReal (A.toReal + μ * Real.exp t) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg hμ (Real.exp_pos t).le),
        ENNReal.ofReal_toReal haf, ENNReal.ofReal_mul hμ]
    _ ≤ ENNReal.ofReal (Real.exp ((Real.exp t - 1) * μ)) := by
      apply ENNReal.ofReal_le_ofReal
      have h := Real.add_one_le_exp ((Real.exp t - 1) * μ)
      nlinarith

/-- One real-valued draw together with its support bound. -/
structure BoundedDraw where
  law : PMF ℝ
  bounded : ∀ x ∈ law.support, 0 ≤ x ∧ x ≤ 1

namespace BoundedDraw

def ofMap (p : PMF α) (f : α → ℝ)
    (hf : ∀ x ∈ p.support, 0 ≤ f x ∧ f x ≤ 1) : BoundedDraw where
  law := p.map f
  bounded y hy := by
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    exact hf x hx

def pure (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : BoundedDraw where
  law := PMF.pure x
  bounded y hy := by
    have he := (PMF.mem_support_pure_iff _ _).mp hy
    subst y
    exact ⟨hx, hx1⟩

theorem expect_le_one (d : BoundedDraw) : expect d.law ENNReal.ofReal ≤ 1 := by
  apply expect_le_of_le_on_support
  intro x hx
  exact (ENNReal.ofReal_le_ofReal (d.bounded x hx).2).trans_eq ENNReal.ofReal_one

theorem expect_ne_top (d : BoundedDraw) : expect d.law ENNReal.ofReal ≠ ∞ :=
  ne_of_lt (d.expect_le_one.trans_lt ENNReal.one_lt_top)

def mean (d : BoundedDraw) : ℝ := (expect d.law ENNReal.ofReal).toReal

theorem mean_nonneg (d : BoundedDraw) : 0 ≤ d.mean := ENNReal.toReal_nonneg

theorem mean_le_one (d : BoundedDraw) : d.mean ≤ 1 := by
  simpa only [mean, ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top d.expect_le_one

theorem expect_eq (d : BoundedDraw) : expect d.law ENNReal.ofReal = ENNReal.ofReal d.mean :=
  (ENNReal.ofReal_toReal d.expect_ne_top).symm

@[simp] theorem mean_pure (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : (pure x hx hx1).mean = x := by
  simp only [mean, pure, expect_pure, ENNReal.toReal_ofReal hx]

theorem expMoment_le (d : BoundedDraw) (t : ℝ) :
    expMoment d.law id t ≤ ENNReal.ofReal (Real.exp ((Real.exp t - 1) * d.mean)) :=
  expMoment_le_of_unitInterval d.law id d.bounded d.mean_nonneg d.expect_eq t

def sumLaw (ds : List BoundedDraw) : PMF ℝ := independentSum (ds.map law)

def sumMean (ds : List BoundedDraw) : ℝ := (ds.map mean).sum

theorem sumMean_nonneg (ds : List BoundedDraw) : 0 ≤ sumMean ds := by
  induction ds with
  | nil => simp [sumMean]
  | cons d ds ih => exact add_nonneg d.mean_nonneg ih

theorem sumLaw_nonneg (ds : List BoundedDraw) {x : ℝ} (hx : x ∈ (sumLaw ds).support) :
    0 ≤ x := by
  induction ds generalizing x with
  | nil =>
      have he := (PMF.mem_support_pure_iff _ _).mp hx
      subst x
      exact le_rfl
  | cons d ds ih =>
      change x ∈ (d.law.bind (fun y => (sumLaw ds).map (fun z => y + z))).support at hx
      obtain ⟨y, hy, hmap⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
      obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
      exact add_nonneg (d.bounded y hy).1 (ih hz)

theorem expect_sumLaw_eq (ds : List BoundedDraw) :
    expect (sumLaw ds) ENNReal.ofReal = ENNReal.ofReal (sumMean ds) := by
  induction ds with
  | nil => simp [sumLaw, independentSum, sumMean]
  | cons d ds ih =>
      change expect (d.law.bind (fun x => (sumLaw ds).map (fun y => x + y))) ENNReal.ofReal =
        ENNReal.ofReal (d.mean + sumMean ds)
      rw [expect_bind]
      calc
        _ = expect d.law (fun x => ENNReal.ofReal x + expect (sumLaw ds) ENNReal.ofReal) := by
          apply expect_congr_on_support
          intro x hx
          rw [expect_map]
          calc
            _ = expect (sumLaw ds) (fun y => ENNReal.ofReal x + ENNReal.ofReal y) :=
              expect_congr_on_support _ (fun y hy =>
                ENNReal.ofReal_add (d.bounded x hx).1 (sumLaw_nonneg ds hy))
            _ = _ := by rw [expect_add, expect_const]
        _ = expect d.law ENNReal.ofReal + expect (sumLaw ds) ENNReal.ofReal := by
          rw [expect_add, expect_const]
        _ = _ := by rw [d.expect_eq, ih, ENNReal.ofReal_add d.mean_nonneg (sumMean_nonneg ds)]

theorem expMoment_sumLaw_le (ds : List BoundedDraw) (t : ℝ) :
    expMoment (sumLaw ds) id t ≤ ENNReal.ofReal (Real.exp ((Real.exp t - 1) * sumMean ds)) := by
  induction ds with
  | nil => simp [sumLaw, independentSum, sumMean]
  | cons d ds ih =>
      have h := expMoment_bind_add_le d.law (fun _ => sumLaw ds)
        (fun x => x) (fun _ y => y) t (d.expMoment_le t) (fun _ _ => ih)
      calc
        _ ≤ ENNReal.ofReal (Real.exp ((Real.exp t - 1) * d.mean)) *
            ENNReal.ofReal (Real.exp ((Real.exp t - 1) * sumMean ds)) := h
        _ = _ := by rw [← ofReal_exp_add]; congr 2; simp only [sumMean, List.map_cons,
          List.sum_cons]; ring

end BoundedDraw
end
end CutQueryComplexity.Probability
