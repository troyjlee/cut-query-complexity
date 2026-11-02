import CutQueryComplexity.Probability.Expectation
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Exponential moments and discrete Chernoff bounds

Moments remain in `ℝ≥0∞`, including when they diverge. The conditional-sum
identity makes dependence explicit; a uniform conditional moment bound
suffices for multiplication of bounds. Independent sums have exactly the
product of the individual moments. Upper and lower tails then follow from
the support-local Markov inequality, without a finite-support assumption.
-/

namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical ENNReal
variable {α β : Type*}

def expMoment (p : PMF α) (f : α → ℝ) (t : ℝ) : ℝ≥0∞ :=
  expect p (fun x => ENNReal.ofReal (Real.exp (t * f x)))

@[simp] theorem expMoment_zero (p : PMF α) (f : α → ℝ) : expMoment p f 0 = 1 := by
  simp [expMoment]

@[simp] theorem expMoment_pure (x : α) (f : α → ℝ) (t : ℝ) :
    expMoment (PMF.pure x) f t = ENNReal.ofReal (Real.exp (t * f x)) :=
  expect_pure x _

@[simp] theorem expMoment_map (p : PMF α) (g : α → β) (f : β → ℝ) (t : ℝ) :
    expMoment (p.map g) f t = expMoment p (fun x => f (g x)) t := expect_map p g _

theorem ofReal_exp_add (a b : ℝ) :
    ENNReal.ofReal (Real.exp (a + b)) =
      ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) := by
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos a).le]

/-- The second draw may depend on the first; its conditional moment stays inside the expectation. -/
theorem expMoment_bind_add (p : PMF α) (q : α → PMF β)
    (f : α → ℝ) (g : α → β → ℝ) (t : ℝ) :
    expMoment (p.bind (fun x => (q x).map (fun y => f x + g x y))) id t =
      expect p (fun x => ENNReal.ofReal (Real.exp (t * f x)) * expMoment (q x) (g x) t) := by
  simp only [expMoment, expect_bind, expect_map, id_eq, mul_add,
    ofReal_exp_add, expect_const_mul]

theorem expMoment_bind_add_le (p : PMF α) (q : α → PMF β)
    (f : α → ℝ) (g : α → β → ℝ) (t : ℝ) {A B : ℝ≥0∞}
    (hp : expMoment p f t ≤ A) (hq : ∀ x ∈ p.support, expMoment (q x) (g x) t ≤ B) :
    expMoment (p.bind (fun x => (q x).map (fun y => f x + g x y))) id t ≤ A * B := by
  rw [expMoment_bind_add]
  calc
    _ ≤ expect p (fun x => ENNReal.ofReal (Real.exp (t * f x)) * B) :=
      expect_mono_on_support p (fun x hx =>
        mul_le_mul le_rfl (hq x hx) (by positivity) (by positivity))
    _ = expMoment p f t * B := expect_mul_const p _ B
    _ ≤ A * B := mul_le_mul hp le_rfl (by positivity) (by positivity)

/-- A finite sequence of independent real-valued draws, with an explicit sum law. -/
def independentSum : List (PMF ℝ) → PMF ℝ
  | [] => PMF.pure 0
  | p :: ps => p.bind (fun x => (independentSum ps).map (fun y => x + y))

theorem expMoment_independentSum (ps : List (PMF ℝ)) (t : ℝ) :
    expMoment (independentSum ps) id t = (ps.map (fun p => expMoment p id t)).prod := by
  induction ps with
  | nil => simp [independentSum]
  | cons p ps ih =>
      rw [independentSum, expMoment_bind_add p (fun _ => independentSum ps)
        (fun x => x) (fun _ y => y) t]
      simp only [expect_mul_const, List.map_cons, List.prod_cons]
      exact congrArg (fun z => expMoment p id t * z) ih

/-- Exponential Markov bound for an event on which `t * f` is bounded below. -/
theorem mass_le_expMoment (p : PMF α) (f : α → ℝ) (P : α → Prop) (t a : ℝ)
    (h : ∀ x ∈ p.support, P x → t * a ≤ t * f x) :
    mass p P ≤ ENNReal.ofReal (Real.exp (-(t * a))) * expMoment p f t := by
  have hm := mul_mass_le_expect p P (fun x => ENNReal.ofReal (Real.exp (t * f x)))
    (ENNReal.ofReal (Real.exp (t * a))) (fun x hx hP =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (h x hx hP)))
  have hi : ENNReal.ofReal (Real.exp (-(t * a))) *
      ENNReal.ofReal (Real.exp (t * a)) = 1 := by
    rw [← ofReal_exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  calc
    _ = (ENNReal.ofReal (Real.exp (-(t * a))) *
        ENNReal.ofReal (Real.exp (t * a))) * mass p P := by rw [hi, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(t * a))) * expMoment p f t := by
      rw [mul_assoc]
      exact mul_le_mul le_rfl hm (by positivity) (by positivity)

theorem upper_tail_le_expMoment (p : PMF α) (f : α → ℝ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    mass p (fun x => a ≤ f x) ≤
      ENNReal.ofReal (Real.exp (-(t * a))) * expMoment p f t :=
  mass_le_expMoment p f _ t a (fun _ _ hx => mul_le_mul_of_nonneg_left hx ht)

theorem lower_tail_le_expMoment (p : PMF α) (f : α → ℝ) (a : ℝ) {t : ℝ} (ht : t ≤ 0) :
    mass p (fun x => f x ≤ a) ≤
      ENNReal.ofReal (Real.exp (-(t * a))) * expMoment p f t :=
  mass_le_expMoment p f _ t a (fun _ _ hx => mul_le_mul_of_nonpos_left hx ht)

theorem upper_tail_le_exp (p : PMF α) (f : α → ℝ) (a : ℝ) {t b : ℝ} (ht : 0 ≤ t)
    (h : expMoment p f t ≤ ENNReal.ofReal (Real.exp b)) :
    mass p (fun x => a ≤ f x) ≤ ENNReal.ofReal (Real.exp (b - t * a)) := by
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-(t * a))) * expMoment p f t :=
      upper_tail_le_expMoment p f a ht
    _ ≤ ENNReal.ofReal (Real.exp (-(t * a))) * ENNReal.ofReal (Real.exp b) :=
      mul_le_mul le_rfl h (by positivity) (by positivity)
    _ = _ := by rw [← ofReal_exp_add]; congr 2; ring

theorem lower_tail_le_exp (p : PMF α) (f : α → ℝ) (a : ℝ) {t b : ℝ} (ht : t ≤ 0)
    (h : expMoment p f t ≤ ENNReal.ofReal (Real.exp b)) :
    mass p (fun x => f x ≤ a) ≤ ENNReal.ofReal (Real.exp (b - t * a)) := by
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-(t * a))) * expMoment p f t :=
      lower_tail_le_expMoment p f a ht
    _ ≤ ENNReal.ofReal (Real.exp (-(t * a))) * ENNReal.ofReal (Real.exp b) :=
      mul_le_mul le_rfl h (by positivity) (by positivity)
    _ = _ := by rw [← ofReal_exp_add]; congr 2; ring

end
end CutQueryComplexity.Probability
