import CutQueryComplexity.StarContraction2022.Contraction.SparseCenters
import CutQueryComplexity.StarContraction2022.Probability.Product
import CutQueryComplexity.Probability.FiniteEvents

/-!
# Public Bernoulli centers and uniform star choices

The choice kernel receives an explicit learned row table. Its coordinates
are independent after that entire table and the centers have been fixed.
`centerChoiceLaw` records the resulting sequential probability law; it does
not implement neighborhood queries or assume that an input graph is public.
No center-size or coverage event is used to condition the choice kernel.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.UniformStars

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The actual Bernoulli law depends only on the public probability. -/
def centerLaw (p : ℝ) (hp : p ≤ 1) : PMF (Finset V) :=
  Contraction.sampleCenters (ENNReal.ofReal p) (ENNReal.ofReal_le_one.mpr hp)

/-- Independent uniform choices in explicit public rows, with no choice in
an empty row. Malformed or empty tables still define a probability law. -/
def choiceLaw (rows : V → Finset V) : PMF (V → Option V) :=
  Probability.product fun v => Probability.neighborDraw (rows v)

/-- Centers select no edge; every other permitted endpoint is a center. -/
def starRows (R : Finset V) (rows : V → Finset V) (v : V) : Finset V :=
  if v ∈ R then ∅ else rows v ∩ R

def starChoiceLaw (R : Finset V) (rows : V → Finset V) : PMF (V → Option V) :=
  choiceLaw (starRows R rows)

/-- Retain the complete center/choice transcript. In correctness proofs,
`table R` will be the table produced by the actual neighborhood-query stage. -/
def centerChoiceLaw (p : ℝ) (hp : p ≤ 1)
    (table : Finset V → V → Finset V) : PMF (Finset V × (V → Option V)) :=
  (centerLaw p hp).bind fun R =>
    (starChoiceLaw R (table R)).map fun f => (R, f)

theorem choiceLaw_support (rows : V → Finset V) (f : V → Option V) :
    f ∈ (choiceLaw rows).support ↔ ∀ v,
      match f v with
      | none => rows v = ∅
      | some w => w ∈ rows v := by
  rw [choiceLaw, Probability.mem_support_product]
  apply forall_congr'
  intro v
  cases f v <;> simp only [Probability.mem_support_neighborDraw]

/-- The product law is for a fixed complete table, not for averaged rows. -/
theorem choiceLaw_rectangle (rows : V → Finset V) (P : V → Option V → Prop) :
    mass (choiceLaw rows) (fun f => ∀ v, P v (f v)) =
      ∏ v, mass (Probability.neighborDraw (rows v)) (P v) := by
  exact Probability.mass_product _ _

theorem choiceLaw_avoidance (rows : V → Finset V) (P : V → V → Prop) :
    mass (choiceLaw rows) (fun f => ∀ v, (f v).elim True (P v)) =
      ∏ v, if (rows v).Nonempty then
        (((rows v).filter (P v)).card : ℝ≥0∞) / (rows v).card else 1 := by
  rw [choiceLaw_rectangle rows (fun v o => o.elim True (P v))]
  exact Finset.prod_congr rfl fun v _ => Probability.mass_neighborDraw (rows v) (P v)

theorem starChoiceLaw_support (R : Finset V) (rows : V → Finset V)
    (f : V → Option V) :
    f ∈ (starChoiceLaw R rows).support ↔ ∀ v,
      match f v with
      | none => starRows R rows v = ∅
      | some w => w ∈ starRows R rows v :=
  choiceLaw_support _ _

theorem starChoiceLaw_some (R : Finset V) (rows : V → Finset V)
    (f : V → Option V) (hf : f ∈ (starChoiceLaw R rows).support)
    (v w : V) (hvw : f v = some w) : v ∉ R ∧ w ∈ rows v ∧ w ∈ R := by
  have hv := (starChoiceLaw_support R rows f).mp hf v
  rw [hvw] at hv
  by_cases hc : v ∈ R
  · simp [starRows, hc] at hv
  · have hw : w ∈ rows v ∩ R := by simpa only [starRows, hc, ite_false] using hv
    exact ⟨hc, (mem_inter.mp hw).1, (mem_inter.mp hw).2⟩

theorem starChoiceLaw_center (R : Finset V) (rows : V → Finset V)
    (f : V → Option V) (hf : f ∈ (starChoiceLaw R rows).support)
    (v : V) (hv : v ∈ R) : f v = none := by
  cases he : f v with
  | none => rfl
  | some w => exact False.elim ((starChoiceLaw_some R rows f hf v w he).1 hv)

theorem starChoiceLaw_avoidance (R : Finset V) (rows : V → Finset V)
    (P : V → V → Prop) :
    mass (starChoiceLaw R rows) (fun f => ∀ v, (f v).elim True (P v)) =
      ∏ v, if (starRows R rows v).Nonempty then
        (((starRows R rows v).filter (P v)).card : ℝ≥0∞) /
          (starRows R rows v).card else 1 :=
  choiceLaw_avoidance _ _

/-- Every individual row is an actual Bernoulli restriction of the same
center set. This asserts no independence between overlapping rows. -/
theorem centerLaw_restriction (p : ℝ) (hp : p ≤ 1) (N : Finset V) :
    (centerLaw p hp).map (fun R => N ∩ R) =
      Probability.bernoulliSubset N (ENNReal.ofReal p) (ENNReal.ofReal_le_one.mpr hp) :=
  Contraction.sampleCenters_restriction _ _ _

theorem centerChoiceLaw_support (p : ℝ) (hp : p ≤ 1)
    (table : Finset V → V → Finset V) (R : Finset V) (f : V → Option V) :
    (R, f) ∈ (centerChoiceLaw p hp table).support ↔
      R ∈ (centerLaw p hp).support ∧ f ∈ (starChoiceLaw R (table R)).support := by
  simp [centerChoiceLaw, and_comm]

/-- Integrate after fixing the complete sampled transcript. -/
theorem centerChoiceLaw_mass (p : ℝ) (hp : p ≤ 1)
    (table : Finset V → V → Finset V) (E : Finset V × (V → Option V) → Prop) :
    mass (centerChoiceLaw p hp table) E =
      expect (centerLaw p hp) (fun R =>
        mass (starChoiceLaw R (table R)) (fun f => E (R, f))) := by
  simp only [centerChoiceLaw, mass_bind, mass_map, CutQueryComplexity.Probability.expect]

theorem centerChoiceLaw_marginal (p : ℝ) (hp : p ≤ 1)
    (table : Finset V → V → Finset V) (P : Finset V → Prop) :
    mass (centerChoiceLaw p hp table) (fun x => P x.1) = mass (centerLaw p hp) P := by
  rw [centerChoiceLaw_mass]
  calc
    _ = expect (centerLaw p hp) (fun R => if P R then 1 else 0) := by
      apply expect_congr_on_support
      intro R _
      by_cases hR : P R <;> simp [hR]
    _ = _ := by rw [expect_indicator, one_mul]

/-- A later pointwise guarantee is integrated against the center event.
This generic identity does not supply a graph-preservation premise. -/
theorem centerChoiceLaw_integrate (p : ℝ) (hp : p ≤ 1)
    (table : Finset V → V → Finset V) (Good : Finset V → Prop)
    (E : Finset V × (V → Option V) → Prop) (c : ℝ≥0∞)
    (h : ∀ R ∈ (centerLaw p hp).support, Good R →
      c ≤ mass (starChoiceLaw R (table R)) (fun f => E (R, f))) :
    mass (centerLaw p hp) Good * c ≤ mass (centerChoiceLaw p hp table) E := by
  apply Probability.mass_bind_ge (centerLaw p hp)
    (fun R => (starChoiceLaw R (table R)).map fun f => (R, f)) Good E c
  intro R hR hG
  simpa only [mass_map] using h R hR hG

/-- Removing size/coverage failures is additive; it does not replace the
choice law by a law conditioned on a random acceptance event. -/
theorem centerChoiceLaw_subtract_bad (p : ℝ) (hp : p ≤ 1)
    (table : Finset V → V → Finset V) (E : Finset V × (V → Option V) → Prop)
    (Bad : Finset V → Prop) :
    mass (centerChoiceLaw p hp table) E - mass (centerLaw p hp) Bad ≤
      mass (centerChoiceLaw p hp table) (fun x => E x ∧ ¬ Bad x.1) := by
  apply tsub_le_iff_right.mpr
  calc
    _ ≤ mass (centerChoiceLaw p hp table)
        (fun x => (E x ∧ ¬ Bad x.1) ∨ Bad x.1) := by
      apply mass_mono
      intro x hx
      by_cases hB : Bad x.1
      · exact Or.inr hB
      · exact Or.inl ⟨hx, hB⟩
    _ ≤ mass (centerChoiceLaw p hp table) (fun x => E x ∧ ¬ Bad x.1) +
        mass (centerChoiceLaw p hp table) (fun x => Bad x.1) := mass_or_le _ _ _
    _ = _ := by rw [centerChoiceLaw_marginal]

/-- Probability one selects every vertex, including on the empty type. -/
theorem centerLaw_one : centerLaw (V := V) 1 le_rfl = PMF.pure univ := by
  ext R : 1
  by_cases hR : R = univ
  · subst R
    simp [centerLaw, Contraction.sampleCenters]
  · have hcard : R.card < (univ : Finset V).card :=
      card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hR⟩)
    have hpow : Fintype.card V - R.card ≠ 0 := by
      simpa only [card_univ] using Nat.ne_of_gt (Nat.sub_pos_of_lt hcard)
    simp [centerLaw, Contraction.sampleCenters, hR, hpow]

/-- The p=1 case contracts no edge, so the later quotient is the identity. -/
theorem centerChoiceLaw_one_support (table : Finset V → V → Finset V)
    (R : Finset V) (f : V → Option V)
    (h : (R, f) ∈ (centerChoiceLaw 1 le_rfl table).support) :
    R = univ ∧ ∀ v, f v = none := by
  obtain ⟨hR, hf⟩ := (centerChoiceLaw_support 1 le_rfl table R f).mp h
  have heq : R = univ := by simpa only [centerLaw_one, PMF.mem_support_pure_iff] using hR
  subst R
  exact ⟨rfl, fun v => starChoiceLaw_center univ (table univ) f hf v (mem_univ v)⟩

#print axioms centerLaw
#print axioms choiceLaw_rectangle
#print axioms starChoiceLaw_some
#print axioms starChoiceLaw_avoidance
#print axioms centerLaw_restriction
#print axioms centerChoiceLaw_mass
#print axioms centerChoiceLaw_integrate
#print axioms centerChoiceLaw_subtract_bad
#print axioms centerChoiceLaw_one_support

end
end CutQueryComplexity.StarContraction2022.Quantum.UniformStars
