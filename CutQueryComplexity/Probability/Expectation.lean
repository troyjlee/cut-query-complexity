import CutQueryComplexity.Probability.Events

/-! # Nonnegative expectations for discrete distributions

Expectations take values in `ℝ≥0∞`, so divergence is not silently converted
to a real zero. The laws apply to every PMF, without finite outcome alphabets
or measurability assumptions. Hypotheses need hold only on the PMF support.
-/

namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical ENNReal
variable {α β ι : Type*}

def expect (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' x, p x * f x

@[simp] theorem expect_const (p : PMF α) (c : ℝ≥0∞) : expect p (fun _ => c) = c := by
  simp only [expect, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

@[simp] theorem expect_pure (x : α) (f : α → ℝ≥0∞) : expect (PMF.pure x) f = f x := by
  simp [expect, PMF.pure_apply]

theorem expect_mono_on_support (p : PMF α) {f g : α → ℝ≥0∞}
    (h : ∀ x ∈ p.support, f x ≤ g x) : expect p f ≤ expect p g := by
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · exact mul_le_mul le_rfl (h x hx) (by positivity) (by positivity)
  · have hz : p x = 0 := by simpa only [PMF.mem_support_iff, not_not] using hx
    simp [hz]

theorem expect_congr_on_support (p : PMF α) {f g : α → ℝ≥0∞}
    (h : ∀ x ∈ p.support, f x = g x) : expect p f = expect p g :=
  le_antisymm (expect_mono_on_support p (fun x hx => (h x hx).le))
    (expect_mono_on_support p (fun x hx => (h x hx).ge))

theorem expect_le_of_le_on_support (p : PMF α) {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ x ∈ p.support, f x ≤ c) : expect p f ≤ c := by
  simpa using expect_mono_on_support p h

theorem expect_mul_const (p : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    expect p (fun x => f x * c) = expect p f * c := by
  simp only [expect, ← mul_assoc, ENNReal.tsum_mul_right]

theorem expect_const_mul (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expect p (fun x => c * f x) = c * expect p f := by
  simp only [mul_comm c, expect_mul_const]

theorem expect_add (p : PMF α) (f g : α → ℝ≥0∞) :
    expect p (fun x => f x + g x) = expect p f + expect p g := by
  simp only [expect, mul_add, ENNReal.tsum_add]

theorem expect_sum (p : PMF α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    expect p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, expect p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, expect_add, ih]

@[simp] theorem expect_bind (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    expect (p.bind q) f = expect p (fun x => expect (q x) f) := by
  simp only [expect, PMF.bind_apply, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

@[simp] theorem expect_map (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    expect (p.map g) f = expect p (fun x => f (g x)) := by
  simp only [PMF.map, expect_bind, Function.comp_def, expect_pure]

/-- Zero expectation of a nonnegative quantity forces zero at every supported outcome. -/
theorem expect_eq_zero_iff (p : PMF α) (f : α → ℝ≥0∞) :
    expect p f = 0 ↔ ∀ x ∈ p.support, f x = 0 := by
  constructor
  · intro h x hx
    have ht : ∀ y, p y * f y = 0 := ENNReal.tsum_eq_zero.mp h
    exact (mul_eq_zero.mp (ht x)).resolve_left hx
  · intro h
    calc
      _ = expect p (fun _ => 0) := expect_congr_on_support p h
      _ = 0 := expect_const p 0

theorem expect_indicator (p : PMF α) (P : α → Prop) (c : ℝ≥0∞) :
    expect p (fun x => if P x then c else 0) = c * mass p P := by
  rw [expect, mass_eq_tsum, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  by_cases hx : P x <;> simp [hx, mul_comm]

/-- Discrete Markov inequality, with a support-local lower bound on the event. -/
theorem mul_mass_le_expect (p : PMF α) (P : α → Prop) (f : α → ℝ≥0∞) (a : ℝ≥0∞)
    (h : ∀ x ∈ p.support, P x → a ≤ f x) : a * mass p P ≤ expect p f := by
  rw [← expect_indicator]
  apply expect_mono_on_support
  intro x hx
  by_cases hP : P x
  · simpa only [ite_eq_left hP] using h x hx hP
  · simp [hP]

end
end CutQueryComplexity.Probability
