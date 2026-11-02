import CutQueryComplexity.StarContraction2022.Contraction.LearnSubgraph
import CutQueryComplexity.StarContraction2022.Contraction.TwoOut
import CutQueryComplexity.StarContraction2022.Contraction.TwoOut.Components
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Part of the actual contraction proof: noncrossing rows and the avoidance mass bounds. -/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Contraction.Joint

open Finset LearnSubgraph
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

def sameSide (S : Finset V) (v w : V) : Prop := v ∈ S ↔ w ∈ S

def noncrossingRows (N : V → Finset V) (S : Finset V) (v : V) : Finset V :=
  (N v).filter (sameSide S v)

def Avoidance (S : Finset V) {j : ℕ} (tape : V × Fin j → Option V) : Prop :=
  ∀ a, (tape a).elim True (sameSide S a.1)

theorem noncrossingRows_eq_sdiff (N : V → Finset V) (S : Finset V) (v : V) :
    noncrossingRows N S v = N v \ crossingSet S v := by
  ext w
  by_cases hv : v ∈ S <;> simp [noncrossingRows, sameSide, crossingSet, hv]

theorem noncrossingRows_card (N : V → Finset V) (S : Finset V) (v : V) :
    (noncrossingRows N S v).card + ((crossingSet S v) ∩ N v).card = (N v).card := by
  rw [noncrossingRows_eq_sdiff, inter_comm]
  exact card_sdiff_add_card_inter _ _

private theorem rowFraction_eq_card (N : V → Finset V) (S : Finset V) (v : V) :
    rowFraction N S v = (((crossingSet S v) ∩ N v).card : ℝ) / (N v).card := by
  unfold rowFraction Probability.crossingRatio
  apply congrArg (fun F : Finset V => (F.card : ℝ) / (N v).card)
  ext w
  simp only [mem_inter]

theorem row_survival_factor (N : V → Finset V) (S : Finset V) (v : V) :
    (if (N v).Nonempty then ((noncrossingRows N S v).card : ℝ≥0∞) / (N v).card else 1) =
      ENNReal.ofReal (1 - rowFraction N S v) := by
  by_cases hN : (N v).Nonempty
  · have hd : (0 : ℝ) < (N v).card := by exact_mod_cast card_pos.mpr hN
    have hc : ((noncrossingRows N S v).card : ℝ) +
        (((crossingSet S v) ∩ N v).card : ℝ) = (N v).card := by
      exact_mod_cast noncrossingRows_card N S v
    have he : ((noncrossingRows N S v).card : ℝ) / (N v).card =
        1 - rowFraction N S v := by
      rw [rowFraction_eq_card]
      apply (div_eq_iff hd.ne').mpr
      field_simp [hd.ne']
      linarith
    rw [if_pos hN, ← he, ENNReal.ofReal_div_of_pos hd,
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  · have he : N v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    simp [hN, rowFraction, he]

theorem avoidance_mass (N : V → Finset V) (S : Finset V) (j : ℕ) :
    mass (Probability.neighborTape N j) (Avoidance S) =
      ENNReal.ofReal ((∏ v, (1 - rowFraction N S v)) ^ j) := by
  change mass (Probability.neighborTape N j)
    (fun tape : V × Fin j → Option V => ∀ a, (tape a).elim True (sameSide S a.1)) = _
  rw [Probability.neighborTape_avoidance]
  have hfactor (a : V × Fin j) :
      (if (N a.1).Nonempty then (((N a.1).filter (sameSide S a.1)).card : ℝ≥0∞) / (N a.1).card
        else 1) = ENNReal.ofReal (1 - rowFraction N S a.1) :=
    row_survival_factor N S a.1
  simp_rw [hfactor]
  have hnonneg (v : V) : 0 ≤ 1 - rowFraction N S v :=
    sub_nonneg.mpr (Probability.crossingRatio_le_one _ _)
  rw [← ENNReal.ofReal_prod_of_nonneg (fun a _ => hnonneg a.1)]
  congr 1
  rw [Fintype.prod_prod_type_right]
  simp

/-- Convexity in the exponent is the chord inequality behind the sharp
alpha/beta product bound; every individual ratio lies in [0,alpha]. -/
theorem chord_survival {alpha x : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hx0 : 0 ≤ x) (hxa : x ≤ alpha) :
    (1 - alpha) ^ (x / alpha) ≤ 1 - x := by
  have ht0 : 0 ≤ x / alpha := div_nonneg hx0 ha0.le
  have ht1 : x / alpha ≤ 1 := (div_le_iff₀ ha0).mpr (by simpa using hxa)
  have hconv := convexOn_rpow_left (sub_pos.mpr ha1)
  have hchord := hconv.2
  have hc := hchord (x := (0 : ℝ)) (Set.mem_univ _) (y := (1 : ℝ)) (Set.mem_univ _)
    (a := 1 - x / alpha) (b := x / alpha) (sub_nonneg.mpr ht1) ht0
    (by ring : (1 - x / alpha) + x / alpha = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.rpow_zero, Real.rpow_one] at hc
  have he : 1 - x / alpha + x / alpha * (1 - alpha) = 1 - x := by
    field_simp [ha0.ne'] <;> ring
  exact hc.trans_eq he

theorem product_survival_lower (rho : V → ℝ) (alpha beta : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (hr0 : ∀ v, 0 ≤ rho v)
    (hra : ∀ v, rho v ≤ alpha) (hsum : (∑ v, rho v) ≤ beta) :
    (1 - alpha) ^ Nat.ceil (beta / alpha) ≤ ∏ v, (1 - rho v) := by
  have hbase : 0 < 1 - alpha := sub_pos.mpr ha1
  have hsum' : (∑ v, rho v / alpha) ≤ (Nat.ceil (beta / alpha) : ℝ) := by
    rw [← sum_div]
    exact (div_le_div_of_nonneg_right hsum ha0.le).trans (Nat.le_ceil _)
  calc
    _ = (1 - alpha) ^ (Nat.ceil (beta / alpha) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (1 - alpha) ^ (∑ v, rho v / alpha) :=
      Real.rpow_le_rpow_of_exponent_ge hbase (by linarith) hsum'
    _ = ∏ v, (1 - alpha) ^ (rho v / alpha) := Real.rpow_sum_of_pos hbase _ _
    _ ≤ ∏ v, (1 - rho v) := by
      apply Finset.prod_le_prod₀
      · intro v _
        exact Real.rpow_nonneg hbase.le _
      · intro v _
        exact chord_survival ha0 ha1 (hr0 v) (hra v)

/-- The survival probability of j independent draws is a consequence of
the actual sampler and the finite alpha/beta inequalities. -/
theorem avoidance_lower (N : V → Finset V) (S : Finset V) (j : ℕ)
    (alpha beta : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hgood : GoodRows alpha beta N S) :
    ENNReal.ofReal ((1 - alpha) ^ (j * Nat.ceil (beta / alpha))) ≤
      mass (Probability.neighborTape N j) (Avoidance S) := by
  rw [avoidance_mass]
  apply ENNReal.ofReal_le_ofReal
  have hp := product_survival_lower (rowFraction N S) alpha beta ha0 ha1
    (rowFraction_nonneg N S) hgood.1 hgood.2
  have hh := pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr ha1.le) _) hp j
  simpa only [← pow_mul, Nat.mul_comm] using hh

theorem noncrossingRows_nonempty (N : V → Finset V) (S : Finset V) (v : V)
    (hN : (N v).Nonempty) (hr : rowFraction N S v < 1) :
    (noncrossingRows N S v).Nonempty := by
  by_contra hn
  have hz : (noncrossingRows N S v).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
  have hc := noncrossingRows_card N S v
  rw [hz, zero_add] at hc
  have hdegree : (N v).card ≠ 0 := card_ne_zero.mpr hN
  have he : rowFraction N S v = 1 := by
    rw [rowFraction_eq_card]
    rw [hc, div_self (by exact_mod_cast hdegree)]
  exact (ne_of_lt hr) he

section OptionFilter

variable {A : Type*} [Fintype A]

theorem map_some_supported (p : PMF A) (P : A → Prop)
    (h : ∃ v, P v ∧ v ∈ p.support) :
    ∃ o, o.elim True P ∧ o ∈ (p.map some).support := by
  obtain ⟨v, hvP, hvp⟩ := h
  exact ⟨some v, hvP, (PMF.mem_support_map_iff _ _ _).mpr ⟨v, hvp, rfl⟩⟩

theorem condition_map_some (p : PMF A) (P : A → Prop)
    (h : ∃ v, P v ∧ v ∈ p.support) :
    (p.map some).filter {o | o.elim True P} (map_some_supported p P h) =
      (p.filter {v | P v} h).map some := by
  have hmap (q : PMF A) (v : A) : (q.map some) (some v) = q v := by
    simp [PMF.map_apply]
  ext o : 1
  cases o with
  | none => simp [Probability.filter_apply_mass, PMF.map_apply]
  | some v =>
    simp only [Probability.filter_apply_mass, hmap, mass_map, Option.elim_some]

end OptionFilter

theorem neighbor_avoidance_supported (N : Finset V) (P : V → Prop)
    (h : N.Nonempty → (N.filter P).Nonempty) :
    ∃ o, o.elim True P ∧ o ∈ (Probability.neighborDraw N).support := by
  by_cases hN : N.Nonempty
  · obtain ⟨v, hv⟩ := h hN
    exact ⟨some v, (mem_filter.mp hv).2,
      (Probability.mem_support_neighborDraw N (some v)).mpr (mem_filter.mp hv).1⟩
  · exact ⟨none, trivial, (Probability.mem_support_neighborDraw N none).mpr
      (not_nonempty_iff_eq_empty.mp hN)⟩

theorem condition_neighborDraw (N : Finset V) (P : V → Prop)
    (h : N.Nonempty → (N.filter P).Nonempty) :
    (Probability.neighborDraw N).filter {o | o.elim True P}
      (neighbor_avoidance_supported N P h) = Probability.neighborDraw (N.filter P) := by
  by_cases hN : N.Nonempty
  · have hs : ∃ v, P v ∧ v ∈ (PMF.uniformOfFinset N hN).support := by
      obtain ⟨v, hv⟩ := h hN
      exact ⟨v, (mem_filter.mp hv).2,
        (PMF.mem_support_uniformOfFinset_iff _ _).mpr (mem_filter.mp hv).1⟩
    simp only [Probability.neighborDraw, dite_eq_left hN, dite_eq_left (h hN)]
    rw [condition_map_some _ P hs, Probability.condition_uniform N hN P hs]
  · have he : N = ∅ := not_nonempty_iff_eq_empty.mp hN
    subst N
    have hnone : ∃ o, o.elim True P ∧ o ∈ (PMF.pure (none : Option V)).support :=
      ⟨none, trivial, by simp⟩
    change (PMF.pure (none : Option V)).filter {o | o.elim True P} hnone = PMF.pure none
    have hm : mass (PMF.pure (none : Option V)) (fun o => o.elim True P) = 1 :=
      (mass_pure (none : Option V) (fun o => o.elim True P)).trans (ite_eq_left trivial)
    ext o : 1
    rw [Probability.filter_apply_mass, hm, div_one]
    by_cases ho : o.elim True P
    · simp only [ho, ite_true]
    · have hne : o ≠ none := by
        intro he
        subst o
        exact ho trivial
      simp only [ho, ite_false, PMF.pure_apply, hne]

theorem avoidance_supported (N : V → Finset V) (S : Finset V) (j : ℕ)
    (h : ∀ v, rowFraction N S v < 1) :
    ∃ tape, Avoidance S tape ∧ tape ∈ (Probability.neighborTape N j).support :=
  Probability.product_event_supported (fun a : V × Fin j => Probability.neighborDraw (N a.1))
    (fun a o => o.elim True (sameSide S a.1))
    (fun a => neighbor_avoidance_supported _ _ (fun hN => noncrossingRows_nonempty N S a.1 hN (h a.1)))

/-- The complete avoidance-conditioned tape consists of independent uniform
draws from the actual noncrossing lists, including unchanged empty rows. -/
theorem condition_avoidance (N : V → Finset V) (S : Finset V) (j : ℕ)
    (h : ∀ v, rowFraction N S v < 1) :
    (Probability.neighborTape N j).filter {tape | Avoidance S tape}
      (avoidance_supported N S j h) = Probability.neighborTape (noncrossingRows N S) j := by
  have hc := Probability.condition_product
    (fun a : V × Fin j => Probability.neighborDraw (N a.1))
    (fun a o => o.elim True (sameSide S a.1))
    (fun a => neighbor_avoidance_supported _ _
      (fun hN => noncrossingRows_nonempty N S a.1 hN (h a.1)))
  refine hc.trans ?_
  change Probability.product _ = Probability.product _
  apply congrArg Probability.product
  funext a
  exact condition_neighborDraw _ _ (fun hN => noncrossingRows_nonempty N S a.1 hN (h a.1))

/-- This identity, rather than a product of marginal probabilities, is the
interface for the component-size theorem and for fixed-transcript integration. -/
theorem joint_mass (N : V → Finset V) (S : Finset V) (j : ℕ)
    (h : ∀ v, rowFraction N S v < 1) (Q : (V × Fin j → Option V) → Prop) :
    mass (Probability.neighborTape N j) (fun tape => Avoidance S tape ∧ Q tape) =
      mass (Probability.neighborTape N j) (Avoidance S) *
        mass (Probability.neighborTape (noncrossingRows N S) j) Q := by
  rw [Probability.mass_inter_eq_mul_filter _ _ _ (avoidance_supported N S j h),
    condition_avoidance N S j h]

theorem noncrossing_degree (N : V → Finset V) (S : Finset V) (v : V)
    (alpha : ℝ) (ha1 : alpha ≤ 1) (hr : rowFraction N S v ≤ alpha) :
    (1 - alpha) * (N v).card ≤ (noncrossingRows N S v).card := by
  by_cases hN : (N v).Nonempty
  · have hd : (0 : ℝ) < (N v).card := by exact_mod_cast card_pos.mpr hN
    have hc : ((noncrossingRows N S v).card : ℝ) +
        (((crossingSet S v) ∩ N v).card : ℝ) = (N v).card := by
      exact_mod_cast noncrossingRows_card N S v
    rw [rowFraction_eq_card] at hr
    have hm := (div_le_iff₀ hd).mp hr
    nlinarith
  · have he : N v = ∅ := not_nonempty_iff_eq_empty.mp hN
    simp [noncrossingRows, he]

/-- Integrating a lower bound uses arbitrary discrete transcript/output types. -/
private theorem mass_bind_ge_any {T U : Type*} (p : PMF T) (next : T → PMF U)
    (Good : T → Prop) (Success : U → Prop) (c : ℝ≥0∞)
    (h : ∀ t ∈ p.support, Good t → c ≤ mass (next t) Success) :
    mass p Good * c ≤ mass (p.bind next) Success := by
  rw [mass_eq_tsum, mass_bind, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases ht : Good t
  · simp only [ht, ite_true]
    by_cases hs : t ∈ p.support
    · exact mul_le_mul le_rfl (h t hs ht) (by positivity) (by positivity)
    · have hz : p t = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
      simp [hz]
  · simp [ht]

/-- A public fresh-draw kernel for any number of replacement draws. The
complete previous transcript remains part of the returned value. -/
def afterTranscriptDraws {T : Type*} (μ : PMF T) (rows : T → V → Finset V) (j : ℕ) :
    PMF (T × (V × Fin j → Option V)) :=
  μ.bind fun transcript =>
    (Probability.neighborTape (rows transcript) j).map fun tape => (transcript,tape)

/-- Survival is integrated conditional on each complete learned transcript.
This applies to the outside one-out stage and permits arbitrary correlations
within and between all earlier learned rows. -/
theorem afterTranscriptDraws_avoidance {T : Type*} (μ : PMF T)
    (rows : T → V → Finset V) (Good : T → Prop) (S : Finset V) (j : ℕ)
    (alpha beta : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hgood : ∀ transcript ∈ μ.support, Good transcript →
      GoodRows alpha beta (rows transcript) S) :
    mass μ Good * ENNReal.ofReal ((1 - alpha) ^ (j * Nat.ceil (beta / alpha))) ≤
      mass (afterTranscriptDraws μ rows j) (fun out => Good out.1 ∧ Avoidance S out.2) := by
  apply mass_bind_ge_any μ
    (fun transcript => (Probability.neighborTape (rows transcript) j).map
      fun tape => (transcript,tape)) Good _ _
  intro transcript hsupport hG
  rw [mass_map]
  simp only [hG,true_and]
  exact avoidance_lower (rows transcript) S j alpha beta ha0 ha1 (hgood transcript hsupport hG)

section TwoOutBounds

variable [LinearOrder V]

theorem avoidance_twoOut (S : Finset V) (tape : TwoOut.Tape V)
    (h : Avoidance S tape) : TwoOut.Avoids S tape := by
  intro a v hav
  have ha := h a
  simpa only [hav, Option.elim_some, sameSide] using ha

/-- Fixed-transcript joint survival and size. The component theorem is
applied to the actual noncrossing conditional law, never to the unconditioned
rows. The integer lower degree is derived from the original row bound. -/
theorem twoOut_joint_good (N : V → Finset V) (S deficient : Finset V)
    (alpha beta : ℝ) (h ell : ℕ) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hgood : GoodRows alpha beta N S)
    (hdegree : ∀ v, v ∉ deficient → h ≤ (N v).card) (hloop : ∀ v, v ∉ N v)
    (hell : 40 ≤ ell) (hell_le : (ell : ℝ) ≤ (1 - alpha) * h) :
    ENNReal.ofReal ((1 - alpha) ^ (2 * Nat.ceil (beta / alpha))) *
      ENNReal.ofReal (199 / 200 : ℝ) ≤
    mass (Probability.neighborTape N 2) (fun tape => Avoidance S tape ∧
      (TwoOut.componentCount tape : ℝ) ≤ deficient.card +
        (8 * Real.exp 1 ^ 3 + 1) * Fintype.card V / ell) := by
  have hr : ∀ v, rowFraction N S v < 1 := fun v => (hgood.1 v).trans_lt ha1
  have hnoncross : ∀ v, v ∉ deficient → ell ≤ (noncrossingRows N S v).card := by
    intro v hv
    have hdegR : (h : ℝ) ≤ (N v).card := by exact_mod_cast hdegree v hv
    have he : (ell : ℝ) ≤ (noncrossingRows N S v).card :=
      hell_le.trans ((mul_le_mul_of_nonneg_left hdegR (sub_nonneg.mpr ha1.le)).trans
        (noncrossing_degree N S v alpha ha1.le (hgood.1 v)))
    exact_mod_cast he
  have hloops : ∀ v, v ∉ noncrossingRows N S v :=
    fun v hv => hloop v (mem_filter.mp hv).1
  let Q := fun tape : TwoOut.Tape V => (TwoOut.componentCount tape : ℝ) ≤ deficient.card +
    (8 * Real.exp 1 ^ 3 + 1) * Fintype.card V / ell
  have hfail : mass (Probability.neighborTape (noncrossingRows N S) 2) (fun tape => ¬ Q tape) ≤
      ENNReal.ofReal (1 / 200 : ℝ) := by
    have hh := TwoOut.componentCount_tail_of_forty (noncrossingRows N S) deficient ell hell
      hnoncross hloops
    have hc : (200 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 200 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 200),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]
    simpa only [TwoOut.sample, Q, not_le, hc] using hh
  have hQ : ENNReal.ofReal (199 / 200 : ℝ) ≤
      mass (Probability.neighborTape (noncrossingRows N S) 2) Q := by
    have hreal := success_of_failure_le (Probability.neighborTape (noncrossingRows N S) 2)
      Q (by norm_num : (0 : ℝ) ≤ 1 / 200) hfail
    have hr' : (199 / 200 : ℝ) ≤
        (mass (Probability.neighborTape (noncrossingRows N S) 2) Q).toReal := by
      convert hreal using 1 <;> norm_num
    simpa only [ENNReal.ofReal_toReal (mass_ne_top _ _)] using ENNReal.ofReal_le_ofReal hr'
  rw [joint_mass N S 2 hr Q]
  exact mul_le_mul (avoidance_lower N S 2 alpha beta ha0 ha1 hgood) hQ (by positivity) (by positivity)

/-- The same actual tape yields a public component quotient that preserves
a fixed original optimum shore and its exact value on the joint good event. -/
theorem twoOut_joint_minimum (N : V → Finset V) (G : WeightedGraph V)
    (S deficient : Finset V) (hS : IsMinCut G S)
    (alpha beta : ℝ) (h ell : ℕ) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hgood : GoodRows alpha beta N S)
    (hdegree : ∀ v, v ∉ deficient → h ≤ (N v).card) (hloop : ∀ v, v ∉ N v)
    (hell : 40 ≤ ell) (hell_le : (ell : ℝ) ≤ (1 - alpha) * h) :
    ENNReal.ofReal ((1 - alpha) ^ (2 * Nat.ceil (beta / alpha))) *
      ENNReal.ofReal (199 / 200 : ℝ) ≤
    mass (Probability.neighborTape N 2) (fun tape =>
      IsMinCut ((TwoOut.publicQuotient tape).graph G)
        (S.image (TwoOut.publicQuotient tape).map) ∧
      mincutValue ((TwoOut.publicQuotient tape).graph G) = mincutValue G ∧
      2 ≤ TwoOut.componentCount tape ∧
      (TwoOut.componentCount tape : ℝ) ≤ deficient.card +
        (8 * Real.exp 1 ^ 3 + 1) * Fintype.card V / ell) := by
  have hbase := twoOut_joint_good N S deficient alpha beta h ell ha0 ha1 hgood hdegree
    hloop hell hell_le
  have hmono :
      mass (Probability.neighborTape N 2) (fun tape => Avoidance S tape ∧
        (TwoOut.componentCount tape : ℝ) ≤ deficient.card +
          (8 * Real.exp 1 ^ 3 + 1) * Fintype.card V / ell) ≤
      mass (Probability.neighborTape N 2) (fun tape =>
        IsMinCut ((TwoOut.publicQuotient tape).graph G)
          (S.image (TwoOut.publicQuotient tape).map) ∧
        mincutValue ((TwoOut.publicQuotient tape).graph G) = mincutValue G ∧
        2 ≤ TwoOut.componentCount tape ∧
        (TwoOut.componentCount tape : ℝ) ≤ deficient.card +
          (8 * Real.exp 1 ^ 3 + 1) * Fintype.card V / ell) := by
    apply mass_mono
    intro tape ht
    have hr : RespectsBlocks (TwoOut.publicQuotient tape).map S :=
      TwoOut.publicQuotient_respects (avoidance_twoOut S tape ht.1)
    have hcut : IsMinCut ((TwoOut.publicQuotient tape).graph G)
        (S.image (TwoOut.publicQuotient tape).map) :=
      (TwoOut.publicQuotient tape).project_minimum hS hr
    have hvalue : mincutValue ((TwoOut.publicQuotient tape).graph G) = mincutValue G :=
      (TwoOut.publicQuotient tape).mincut_eq hS hr
    have htwo : 2 ≤ TwoOut.componentCount tape := by
      simpa only [TwoOut.componentCount, Fintype.card_eq_nat_card] using
        (TwoOut.publicQuotient tape).two_le_card_of_survives hr hS.1
    exact ⟨hcut, hvalue, htwo, ht.2⟩
  exact hbase.trans hmono

/-- Fresh replacement draws are sampled after the complete learned transcript.
The pair retains that transcript instead of replacing its law by row marginals. -/
def afterTranscript {T : Type*} (μ : PMF T) (rows : T → V → Finset V) :
    PMF (T × TwoOut.Tape V) :=
  μ.bind fun transcript =>
    (Probability.neighborTape (rows transcript) 2).map fun tape => (transcript, tape)

/-- The induced center cut need not be an optimum of the induced graph.
This joint avoidance/size interface uses only its row ratios; preservation
of the original minimum is applied after composing the public quotient. -/
theorem afterTranscript_joint_good {T : Type*} (μ : PMF T)
    (rows : T → V → Finset V) (deficient : T → Finset V) (Good : T → Prop)
    (S : Finset V) (alpha beta tau : ℝ) (h ell : ℕ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hgood : ∀ transcript ∈ μ.support, Good transcript →
      GoodRows alpha beta (rows transcript) S)
    (hdegree : ∀ transcript ∈ μ.support, Good transcript →
      ∀ v, v ∉ deficient transcript → h ≤ (rows transcript v).card)
    (hloop : ∀ transcript ∈ μ.support, Good transcript → ∀ v, v ∉ rows transcript v)
    (hdef : ∀ transcript ∈ μ.support, Good transcript →
      ((deficient transcript).card : ℝ) ≤ tau)
    (hell : 40 ≤ ell) (hell_le : (ell : ℝ) ≤ (1 - alpha) * h) :
    mass μ Good * (ENNReal.ofReal ((1 - alpha) ^ (2 * Nat.ceil (beta / alpha))) *
      ENNReal.ofReal (199 / 200 : ℝ)) ≤
    mass (afterTranscript μ rows) (fun out => Good out.1 ∧ Avoidance S out.2 ∧
      (TwoOut.componentCount out.2 : ℝ) ≤ tau +
        (8 * Real.exp 1 ^ 3 + 1) * Fintype.card V / ell) := by
  apply mass_bind_ge_any μ
    (fun transcript => (Probability.neighborTape (rows transcript) 2).map
      fun tape => (transcript, tape)) Good _ _
  intro transcript hsupport hG
  rw [mass_map]
  apply (twoOut_joint_good (rows transcript) S (deficient transcript)
    alpha beta h ell ha0 ha1 (hgood transcript hsupport hG)
    (hdegree transcript hsupport hG) (hloop transcript hsupport hG) hell hell_le).trans
  apply mass_mono
  intro tape ht
  refine ⟨hG, ht.1, ht.2.trans ?_⟩
  exact add_le_add (hdef transcript hsupport hG) le_rfl

/-- Integrate the proved fixed-transcript joint bound. The earlier transcripts
can be arbitrarily correlated; only the fresh draws use the product kernel.
The good-transcript hypotheses are concrete degree, loop, and cut-ratio bounds,
not an assumed survival, size, or quotient theorem. -/
theorem afterTranscript_joint_minimum {T : Type*} (μ : PMF T)
    (rows : T → V → Finset V) (deficient : T → Finset V) (Good : T → Prop)
    (G : WeightedGraph V) (S : Finset V) (hS : IsMinCut G S)
    (alpha beta : ℝ) (h ell tau : ℕ) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hgood : ∀ transcript ∈ μ.support, Good transcript →
      GoodRows alpha beta (rows transcript) S)
    (hdegree : ∀ transcript ∈ μ.support, Good transcript →
      ∀ v, v ∉ deficient transcript → h ≤ (rows transcript v).card)
    (hloop : ∀ transcript ∈ μ.support, Good transcript → ∀ v, v ∉ rows transcript v)
    (hdef : ∀ transcript ∈ μ.support, Good transcript → (deficient transcript).card ≤ tau)
    (hell : 40 ≤ ell) (hell_le : (ell : ℝ) ≤ (1 - alpha) * h) :
    mass μ Good * (ENNReal.ofReal ((1 - alpha) ^ (2 * Nat.ceil (beta / alpha))) *
      ENNReal.ofReal (199 / 200 : ℝ)) ≤
    mass (afterTranscript μ rows) (fun out => Good out.1 ∧
      IsMinCut ((TwoOut.publicQuotient out.2).graph G)
        (S.image (TwoOut.publicQuotient out.2).map) ∧
      mincutValue ((TwoOut.publicQuotient out.2).graph G) = mincutValue G ∧
      2 ≤ TwoOut.componentCount out.2 ∧
      (TwoOut.componentCount out.2 : ℝ) ≤ tau +
        (8 * Real.exp 1 ^ 3 + 1) * Fintype.card V / ell) := by
  apply mass_bind_ge_any μ
    (fun transcript => (Probability.neighborTape (rows transcript) 2).map
      fun tape => (transcript, tape)) Good _ _
  intro transcript hsupport hG
  rw [mass_map]
  apply (twoOut_joint_minimum (rows transcript) G S (deficient transcript) hS
    alpha beta h ell ha0 ha1 (hgood transcript hsupport hG)
    (hdegree transcript hsupport hG) (hloop transcript hsupport hG) hell hell_le).trans
  apply mass_mono
  intro tape ht
  refine ⟨hG, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.trans ?_⟩
  have hdefR : ((deficient transcript).card : ℝ) ≤ (tau : ℝ) := by
    exact_mod_cast hdef transcript hsupport hG
  exact add_le_add hdefR le_rfl

end TwoOutBounds


#print axioms avoidance_mass
#print axioms chord_survival
#print axioms product_survival_lower
#print axioms avoidance_lower
#print axioms condition_neighborDraw
#print axioms condition_avoidance
#print axioms joint_mass
#print axioms noncrossing_degree
#print axioms afterTranscriptDraws_avoidance
#print axioms twoOut_joint_good
#print axioms twoOut_joint_minimum
#print axioms afterTranscript_joint_good
#print axioms afterTranscript_joint_minimum

end
end CutQueryComplexity.StarContraction2022.Contraction.Joint
