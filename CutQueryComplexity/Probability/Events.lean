import CutQueryComplexity.Model.RandomizedComposition

/-! # Conditional error bounds for countably supported random choices -/

namespace CutQueryComplexity.Probability

noncomputable section
open scoped Classical ENNReal

variable {α β : Type*}

/-- Probability of a predicate, without a measurability restriction on discrete outputs. -/
def mass (p : PMF α) (P : α → Prop) : ℝ≥0∞ := p.toOuterMeasure {x | P x}

theorem mass_eq_tsum (p : PMF α) (P : α → Prop) :
    mass p P = ∑' x, if P x then p x else 0 := by
  simp [mass, PMF.toOuterMeasure_apply, Set.indicator]

@[simp] theorem mass_true (p : PMF α) : mass p (fun _ => True) = 1 := by
  simp [mass_eq_tsum]

@[simp] theorem mass_false (p : PMF α) : mass p (fun _ => False) = 0 := by
  simp [mass_eq_tsum]

theorem mass_mono (p : PMF α) {P Q : α → Prop} (h : ∀ x, P x → Q x) : mass p P ≤ mass p Q :=
  p.toOuterMeasure.mono (fun x hx => h x hx)

theorem mass_le_one (p : PMF α) (P : α → Prop) : mass p P ≤ 1 := by
  simpa using mass_mono p (P := P) (Q := fun _ => True) (fun _ _ => trivial)

theorem mass_ne_top (p : PMF α) (P : α → Prop) : mass p P ≠ ∞ :=
  ne_of_lt ((mass_le_one p P).trans_lt ENNReal.one_lt_top)

@[simp] theorem mass_pure (a : α) (P : α → Prop) :
    mass (PMF.pure a) P = if P a then 1 else 0 := by
  simp [mass, PMF.toOuterMeasure_pure_apply]

@[simp] theorem mass_map (p : PMF α) (f : α → β) (P : β → Prop) :
    mass (p.map f) P = mass p (fun a => P (f a)) := by
  rw [mass, PMF.toOuterMeasure_map_apply]
  rfl

theorem mass_add_compl (p : PMF α) (P : α → Prop) :
    mass p P + mass p (fun x => ¬P x) = 1 := by
  rw [mass_eq_tsum, mass_eq_tsum, ← ENNReal.tsum_add]
  convert p.tsum_coe using 1
  apply tsum_congr
  intro x
  by_cases h : P x <;> simp [h]

@[simp] theorem mass_bind (p : PMF α) (f : α → PMF β) (P : β → Prop) :
    mass (p.bind f) P = ∑' a, p a * mass (f a) P := by
  exact PMF.toOuterMeasure_bind_apply p f {x | P x}

/-- Conditional union bound: the second routine need only be correct after a good first output. -/
theorem mass_bind_le_add (p : PMF α) (f : α → PMF β) (Bad : α → Prop) (Fail : β → Prop)
    {δ ε : ℝ≥0∞} (hp : mass p Bad ≤ δ)
    (hf : ∀ a, ¬Bad a → mass (f a) Fail ≤ ε) : mass (p.bind f) Fail ≤ δ + ε := by
  rw [mass_bind]
  calc
    _ ≤ ∑' a, ((if Bad a then p a else 0) + p a * ε) := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases h : Bad a
      · simp only [ite_eq_left h]
        calc
          _ ≤ p a * 1 := mul_le_mul le_rfl (mass_le_one (f a) Fail) (by positivity) (by positivity)
          _ ≤ p a + p a * ε := by simp
      · simpa only [ite_eq_right h, zero_add] using
          mul_le_mul (le_refl (p a)) (hf a h) (by positivity) (by positivity)
    _ = mass p Bad + ε := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, ← mass_eq_tsum]
    _ ≤ δ + ε := add_le_add hp le_rfl

theorem real_add_compl (p : PMF α) (P : α → Prop) :
    (mass p P).toReal + (mass p (fun x => ¬P x)).toReal = 1 := by
  have h := congrArg ENNReal.toReal (mass_add_compl p P)
  simpa only [ENNReal.toReal_add (mass_ne_top p P) (mass_ne_top p _), ENNReal.toReal_one] using h

theorem failure_le_of_success (p : PMF α) (P : α → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (h : 1 - ε ≤ (mass p P).toReal) : mass p (fun x => ¬P x) ≤ ENNReal.ofReal ε := by
  apply (ENNReal.toReal_le_toReal (mass_ne_top p _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hε]
  have := real_add_compl p P
  linarith

theorem success_of_failure_le (p : PMF α) (P : α → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (h : mass p (fun x => ¬P x) ≤ ENNReal.ofReal ε) : 1 - ε ≤ (mass p P).toReal := by
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hε] at h'
  have := real_add_compl p P
  linarith

end
end CutQueryComplexity.Probability

namespace CutQueryComplexity.RTree

noncomputable section
open scoped Classical
open Probability

variable {I A O P X : Type} {q r : ℕ}

/-- Adaptive randomized routines add their worst-case query budgets and failure probabilities. -/
theorem bind_solves {T : RTree I A O q} {f : O → RTree I A P r}
    {read : X → I → A} {Middle : X → O → Prop} {Good : X → P → Prop} {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hT : T.SolvesWithError read Middle δ)
    (hf : ∀ x o, Middle x o → 1 - ε ≤ (f o).successProb (read x) (Good x)) :
    (T.bind f).SolvesWithError read Good (δ + ε) := by
  intro x
  rw [successProb_eq, eval_bind]
  apply success_of_failure_le _ _ (add_nonneg hδ hε)
  have hp := failure_le_of_success (T.eval (read x)) (Middle x) hδ
    (by simpa only [mass, ← successProb_eq] using hT x)
  have hnext : ∀ o, ¬¬Middle x o →
      mass ((f o).eval (read x)) (fun v => ¬Good x v) ≤ ENNReal.ofReal ε := by
    intro o ho
    apply failure_le_of_success _ _ hε
    simpa only [mass, ← successProb_eq] using hf x o (not_not.mp ho)
  have h := mass_bind_le_add (T.eval (read x)) (fun o => (f o).eval (read x))
    (fun o => ¬Middle x o) (fun v => ¬Good x v) hp hnext
  simpa only [ENNReal.ofReal_add hδ hε] using h

end
end CutQueryComplexity.RTree
