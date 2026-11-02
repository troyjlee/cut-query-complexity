import CutQueryComplexity.Probability.Events

/-! # Finite union bounds on a PMF

The events may be arbitrarily dependent. Implications used to bound failure
need hold only at supported outcomes; zero-probability transcripts are ignored.
-/

namespace CutQueryComplexity.Probability
noncomputable section
open scoped Classical ENNReal
variable {α ι : Type*}

theorem mass_mono_on_support (p : PMF α) {P Q : α → Prop}
    (h : ∀ x ∈ p.support, P x → Q x) : mass p P ≤ mass p Q :=
  p.toOuterMeasure_mono (fun x hx => h x hx.2 hx.1)

theorem mass_eq_one_of_support (p : PMF α) {P : α → Prop}
    (h : ∀ x ∈ p.support, P x) : mass p P = 1 :=
  (p.toOuterMeasure_apply_eq_one_iff _).mpr h

theorem mass_or_le (p : PMF α) (P Q : α → Prop) :
    mass p (fun x => P x ∨ Q x) ≤ mass p P + mass p Q := by
  rw [mass_eq_tsum, mass_eq_tsum, mass_eq_tsum, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hP : P x <;> by_cases hQ : Q x <;> simp [hP, hQ]

theorem mass_exists_finset_le (p : PMF α) (s : Finset ι) (Bad : ι → α → Prop) :
    mass p (fun x => ∃ i ∈ s, Bad i x) ≤ ∑ i ∈ s, mass p (Bad i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have he : (fun x => ∃ j ∈ insert i s, Bad j x) =
          (fun x => Bad i x ∨ ∃ j ∈ s, Bad j x) := by
        funext x
        simp
      rw [he, Finset.sum_insert hi]
      exact (mass_or_le p _ _).trans (add_le_add le_rfl ih)

/-- Finite component failure bounds transfer through a deterministic success implication. -/
theorem mass_failure_le_sum (p : PMF α) (s : Finset ι) (Good : ι → α → Prop)
    (Goal : α → Prop)
    (h : ∀ x ∈ p.support, (∀ i ∈ s, Good i x) → Goal x) :
    mass p (fun x => ¬Goal x) ≤ ∑ i ∈ s, mass p (fun x => ¬Good i x) := by
  apply le_trans (mass_mono_on_support p (Q := fun x => ∃ i ∈ s, ¬Good i x) ?_)
    (mass_exists_finset_le p s (fun i x => ¬Good i x))
  intro x hx hbad
  by_contra hall
  apply hbad (h x hx ?_)
  intro i hi
  by_contra hg
  exact hall ⟨i, hi, hg⟩

theorem mass_failure_le_sum_bounds (p : PMF α) (s : Finset ι) (Good : ι → α → Prop)
    (Goal : α → Prop) (δ : ι → ℝ≥0∞)
    (h : ∀ x ∈ p.support, (∀ i ∈ s, Good i x) → Goal x)
    (hb : ∀ i ∈ s, mass p (fun x => ¬Good i x) ≤ δ i) :
    mass p (fun x => ¬Goal x) ≤ ∑ i ∈ s, δ i :=
  (mass_failure_le_sum p s Good Goal h).trans (Finset.sum_le_sum hb)

theorem mass_failure_le_card_mul (p : PMF α) (s : Finset ι) (Good : ι → α → Prop)
    (Goal : α → Prop) (δ : ℝ≥0∞)
    (h : ∀ x ∈ p.support, (∀ i ∈ s, Good i x) → Goal x)
    (hb : ∀ i ∈ s, mass p (fun x => ¬Good i x) ≤ δ) :
    mass p (fun x => ¬Goal x) ≤ (s.card : ℝ≥0∞) * δ := by
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    mass_failure_le_sum_bounds p s Good Goal (fun _ => δ) h hb

end
end CutQueryComplexity.Probability
