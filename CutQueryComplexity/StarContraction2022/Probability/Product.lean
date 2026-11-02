import CutQueryComplexity.Probability.Expectation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.Distributions.Uniform

/-!
# Finite product draws and exact avoidance conditioning

All samplers take explicit finite data. In particular, a neighbor list here is
an already learned public list, not access to the hidden graph. Conditioning is
used only in the analysis. The conditional law is proved from point masses.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Probability

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {I V W : Type*} [Fintype I]
variable {A : I → Type*} [∀ i, Fintype (A i)]

/-- Independent finite draws, constructed by their actual product point mass. -/
def product (p : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  PMF.ofFintype (fun x => ∏ i, p i (x i)) (by
    rw [← Fintype.prod_sum]
    have hp (i : I) : ∑ a, p i a = 1 := by
      simpa only [tsum_fintype] using (p i).tsum_coe
    simp only [hp, Finset.prod_const_one])

@[simp] theorem product_apply (p : ∀ i, PMF (A i)) (x : ∀ i, A i) :
    product p x = ∏ i, p i (x i) := rfl

@[simp] theorem mem_support_product (p : ∀ i, PMF (A i)) (x : ∀ i, A i) :
    x ∈ (product p).support ↔ ∀ i, x i ∈ (p i).support := by
  simp only [PMF.mem_support_iff, product_apply, Finset.prod_ne_zero_iff,
    Finset.mem_univ, true_implies]

/-- Rectangle probabilities factor, including an empty index set. -/
theorem mass_product (p : ∀ i, PMF (A i)) (P : ∀ i, A i → Prop) :
    mass (product p) (fun x => ∀ i, P i (x i)) = ∏ i, mass (p i) (P i) := by
  simp only [mass_eq_tsum, tsum_fintype, product_apply]
  calc
    _ =
        ∑ x : ∀ i, A i, ∏ i, if P i (x i) then p i (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Fintype.prod_ite_zero]
      by_cases hx : ∀ i, P i (x i) <;> simp only [hx, ite_true, ite_false]
    _ = ∏ i, ∑ a, if P i a then p i a else 0 :=
      (Fintype.prod_sum (fun i a => if P i a then p i a else 0)).symm

/-- Coordinate positivity constructs a supported outcome in the whole event. -/
theorem product_event_supported (p : ∀ i, PMF (A i)) (P : ∀ i, A i → Prop)
    (h : ∀ i, ∃ a, P i a ∧ a ∈ (p i).support) :
    ∃ x, (∀ i, P i (x i)) ∧ x ∈ (product p).support := by
  refine ⟨fun i => Classical.choose (h i), fun i => (Classical.choose_spec (h i)).1, ?_⟩
  exact (mem_support_product _ _).mpr fun i => (Classical.choose_spec (h i)).2

theorem filter_apply_mass (p : PMF V) (P : V → Prop)
    (h : ∃ x, P x ∧ x ∈ p.support) (x : V) :
    (p.filter {x | P x} h) x = (if P x then p x else 0) / mass p P := by
  simpa only [Set.indicator, Set.mem_ofPred_eq, mass_eq_tsum, div_eq_mul_inv] using
    PMF.filter_apply (p := p) (s := {x | P x}) h x

/-- The actual conditioned product remains the product of conditioned laws.
No independence premise about a learned graph or a successful clock is used. -/
theorem condition_product (p : ∀ i, PMF (A i)) (P : ∀ i, A i → Prop)
    (h : ∀ i, ∃ a, P i a ∧ a ∈ (p i).support) :
    (product p).filter {x | ∀ i, P i (x i)} (product_event_supported p P h) =
      product (fun i => (p i).filter {a | P i a} (h i)) := by
  ext x : 1
  simp only [filter_apply_mass, product_apply]
  rw [ENNReal.prod_div_distrib_of_ne_top (fun i _ => mass_ne_top (p i) (P i)),
    Fintype.prod_ite_zero, mass_product]
  by_cases hx : ∀ i, P i (x i) <;> simp only [hx, ite_true, ite_false]

variable [Fintype V]

/-- Uniform draws from separate explicit nonempty lists. -/
def uniformRows (N : I → Finset V) (hN : ∀ i, (N i).Nonempty) : PMF (I → V) :=
  product fun i => PMF.uniformOfFinset (N i) (hN i)

@[simp] theorem mem_support_uniformRows (N : I → Finset V)
    (hN : ∀ i, (N i).Nonempty) (x : I → V) :
    x ∈ (uniformRows N hN).support ↔ ∀ i, x i ∈ N i := by
  simp only [uniformRows, mem_support_product, PMF.mem_support_uniformOfFinset_iff]

theorem mass_uniform (N : Finset V) (hN : N.Nonempty) (P : V → Prop) :
    mass (PMF.uniformOfFinset N hN) P =
      ((N.filter P).card : ℝ≥0∞) / N.card := by
  simp only [mass, PMF.toOuterMeasure_uniformOfFinset_apply, Set.mem_ofPred_eq]

theorem mass_uniformRows (N : I → Finset V) (hN : ∀ i, (N i).Nonempty)
    (P : I → V → Prop) :
    mass (uniformRows N hN) (fun x => ∀ i, P i (x i)) =
      ∏ i, (((N i).filter (P i)).card : ℝ≥0∞) / (N i).card := by
  rw [uniformRows, mass_product]
  exact Finset.prod_congr rfl fun i _ => mass_uniform (N i) (hN i) (P i)

theorem uniform_filter_nonempty (N : Finset V) (hN : N.Nonempty) (P : V → Prop)
    (h : ∃ x, P x ∧ x ∈ (PMF.uniformOfFinset N hN).support) :
    (N.filter P).Nonempty := by
  obtain ⟨x, hP, hx⟩ := h
  exact ⟨x, mem_filter.mpr ⟨(PMF.mem_support_uniformOfFinset_iff _ _).mp hx, hP⟩⟩

/-- A uniform list conditioned on membership in an allowed set is uniformly
distributed on its actual filtered list. -/
theorem condition_uniform (N : Finset V) (hN : N.Nonempty) (P : V → Prop)
    (h : ∃ x, P x ∧ x ∈ (PMF.uniformOfFinset N hN).support) :
    (PMF.uniformOfFinset N hN).filter {x | P x} h =
      PMF.uniformOfFinset (N.filter P) (uniform_filter_nonempty N hN P h) := by
  have hcard : (N.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hN)
  ext x : 1
  rw [filter_apply_mass, mass_uniform]
  by_cases hx : x ∈ N.filter P
  · obtain ⟨hxN, hxP⟩ := mem_filter.mp hx
    simp only [hxP, ite_true, PMF.uniformOfFinset_apply_of_mem hN hxN,
      PMF.uniformOfFinset_apply_of_mem (uniform_filter_nonempty N hN P h) hx]
    rw [div_eq_mul_inv,
      ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top N.card)) (Or.inl hcard),
      div_eq_mul_inv, ← mul_assoc,
      ENNReal.inv_mul_cancel hcard (ENNReal.natCast_ne_top N.card), one_mul]
  · by_cases hxP : P x
    · have hxN : x ∉ N := fun hn => hx (mem_filter.mpr ⟨hn, hxP⟩)
      simp [hxP, hxN, hx]
    · simp [hxP, hx]

/-- Avoidance conditioning preserves coordinate independence and makes every
coordinate uniform on the noncrossing list. -/
theorem condition_uniformRows (N : I → Finset V) (hN : ∀ i, (N i).Nonempty)
    (P : I → V → Prop)
    (h : ∀ i, ∃ x, P i x ∧ x ∈ (PMF.uniformOfFinset (N i) (hN i)).support) :
    (uniformRows N hN).filter {x | ∀ i, P i (x i)}
        (product_event_supported _ P h) =
      uniformRows (fun i => (N i).filter (P i))
        (fun i => uniform_filter_nonempty (N i) (hN i) (P i) (h i)) := by
  unfold uniformRows
  rw [condition_product]
  congr 1
  funext i
  exact condition_uniform (N i) (hN i) (P i) (h i)

/-- Empty outgoing rows have no draw. Their vertices remain available in all
other lists; the ambient target type is never reduced. -/
def neighborDraw (N : Finset V) : PMF (Option V) :=
  if h : N.Nonempty then (PMF.uniformOfFinset N h).map some else PMF.pure none

@[simp] theorem neighborDraw_empty : neighborDraw (∅ : Finset V) = PMF.pure none := by
  simp [neighborDraw]

@[simp] theorem mem_support_neighborDraw (N : Finset V) (o : Option V) :
    o ∈ (neighborDraw N).support ↔
      match o with
      | none => N = ∅
      | some v => v ∈ N := by
  cases o with
  | none =>
      by_cases h : N.Nonempty
      · have he : N ≠ ∅ := h.ne_empty
        simp [neighborDraw, h, he]
      · have he : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        simp [neighborDraw, h, he]
  | some v =>
      by_cases h : N.Nonempty
      · simp [neighborDraw, h]
      · have he : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        simp [he]

theorem mass_neighborDraw (N : Finset V) (P : V → Prop) :
    mass (neighborDraw N) (fun o => o.elim True P) =
      if N.Nonempty then ((N.filter P).card : ℝ≥0∞) / N.card else 1 := by
  by_cases h : N.Nonempty
  · simp only [neighborDraw, dite_eq_left h, ite_eq_left h, mass_map, Option.elim_some]
    exact mass_uniform N h P
  · simp [neighborDraw, h]

/-- Public predrawn tape. All vertices have j slots; empty outgoing rows contain
none. Nonempty rows sample independently with replacement at every slot. -/
def neighborTape (N : V → Finset V) (j : ℕ) : PMF (V × Fin j → Option V) :=
  product fun a : V × Fin j => neighborDraw (N a.1)

theorem neighborTape_support (N : V → Finset V) (j : ℕ) (tape : V × Fin j → Option V) :
    tape ∈ (neighborTape N j).support ↔ ∀ a,
      match tape a with
      | none => N a.1 = ∅
      | some v => v ∈ N a.1 := by
  simp only [neighborTape, mem_support_product, mem_support_neighborDraw]

theorem neighborTape_avoidance (N : V → Finset V) (j : ℕ) (P : V → V → Prop) :
    mass (neighborTape N j) (fun tape => ∀ a, (tape a).elim True (P a.1)) =
      ∏ a : V × Fin j,
        if (N a.1).Nonempty then (((N a.1).filter (P a.1)).card : ℝ≥0∞) / (N a.1).card
        else 1 := by
  rw [neighborTape, mass_product (fun a : V × Fin j => neighborDraw (N a.1))
    (fun a o => o.elim True (P a.1))]
  exact Finset.prod_congr rfl fun a _ => mass_neighborDraw (N a.1) (P a.1)

/-- Integrate a pointwise lower bound after fixing the entire previous
transcript. This does not require the transcript events to be independent. -/
theorem mass_bind_ge (p : PMF W) (next : W → PMF V) (Good : W → Prop)
    (Success : V → Prop) (c : ℝ≥0∞)
    (h : ∀ w ∈ p.support, Good w → c ≤ mass (next w) Success) :
    mass p Good * c ≤ mass (p.bind next) Success := by
  rw [mass_eq_tsum, mass_bind, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : Good w
  · simp only [hw, ite_true]
    by_cases hs : w ∈ p.support
    · exact mul_le_mul le_rfl (h w hs hw) (by positivity) (by positivity)
    · have hz : p w = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
      simp [hz]
  · simp [hw]

/-- Conditioning is paired with its event probability before integration.
The second factor is an actual conditional law, never a marginal size law. -/
theorem mass_inter_eq_mul_filter (p : PMF V) (P Q : V → Prop)
    (h : ∃ x, P x ∧ x ∈ p.support) :
    mass p (fun x => P x ∧ Q x) =
      mass p P * mass (p.filter {x | P x} h) Q := by
  have hnonzero : mass p P ≠ 0 := by
    obtain ⟨x, hxP, hxp⟩ := h
    intro hz
    have hd := (p.toOuterMeasure_apply_eq_zero_iff {x | P x}).mp hz
    exact Set.disjoint_left.mp hd hxp hxP
  rw [mass_eq_tsum (p.filter _ _) Q]
  simp_rw [filter_apply_mass]
  calc
    mass p (fun x => P x ∧ Q x) =
        mass p P * ((mass p (fun x => P x ∧ Q x)) / mass p P) := by
      rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel hnonzero (mass_ne_top p P),
        mul_one]
    _ = _ := by
      congr 1
      rw [mass_eq_tsum, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro x
      by_cases hxP : P x <;> by_cases hxQ : Q x <;> simp [hxP, hxQ, div_eq_mul_inv]

#print axioms product
#print axioms mass_product
#print axioms condition_product
#print axioms condition_uniformRows
#print axioms neighborTape_support
#print axioms neighborTape_avoidance
#print axioms mass_bind_ge
#print axioms mass_inter_eq_mul_filter

end
end CutQueryComplexity.StarContraction2022.Probability
