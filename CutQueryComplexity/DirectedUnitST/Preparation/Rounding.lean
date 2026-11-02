import CutQueryComplexity.DirectedUnitST.Preparation.Query
import CutQueryComplexity.DirectedUnitST.Blocking.State
import CutQueryComplexity.DirectedUnitST.Repair.IntegralRounding

/-! # A public residual state for learned canonical capacities

This file first constructs the complete public state before integral rounding.
Both directions of learned pairs are stored; every unknown pair has a public
pure orientation. The singleton values are actual measured answers.
The integral correction uses Repair's checked learned-only selector. Hidden
full capacities occur only in its realization proof, never in the selector.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Preparation

open Finset Acceleration Certificate DirectedCertificate

def symmetricKnown {n : ℕ} (k : ℕ) (r : Fin n → ℚ) : Finset (Fin n × Fin n) :=
  knownPairs k r ∪ (knownPairs k r).image Prod.swap

theorem knownPairs_lt {n k : ℕ} (r : Fin n → ℚ) (i j : Fin n)
    (hij : (i, j) ∈ knownPairs k r) : i < j := by
  obtain ⟨e, _, he⟩ := mem_image.mp hij
  simpa only [he] using e.property

theorem mem_symmetricKnown {n k : ℕ} (r : Fin n → ℚ) (i j : Fin n) :
    (i, j) ∈ symmetricKnown k r ↔ (i, j) ∈ knownPairs k r ∨ (j, i) ∈ knownPairs k r := by
  constructor
  · intro hm
    rcases mem_union.mp hm with hm | hm
    · exact Or.inl hm
    · obtain ⟨p, hp, he⟩ := mem_image.mp hm
      have hp' : p = (j, i) := by simpa using congrArg Prod.swap he
      exact Or.inr (hp' ▸ hp)
  · rintro (hm | hm)
    · exact mem_union_left _ hm
    · exact mem_union_right _ (mem_image.mpr ⟨(j, i), hm, rfl⟩)

theorem symmetricKnown_symm {n k : ℕ} (r : Fin n → ℚ) (i j : Fin n) :
    (i, j) ∈ symmetricKnown k r ↔ (j, i) ∈ symmetricKnown k r := by
  simp only [mem_symmetricKnown, or_comm]

theorem mem_symmetricKnown_canonical {n k : ℕ} (r : Fin n → ℚ) (e : SparseBand.Pair n) :
    e.val ∈ symmetricKnown k r ↔ e ∈ fractionalMask k r := by
  change (e.val.1, e.val.2) ∈ symmetricKnown k r ↔ e ∈ fractionalMask k r
  rw [mem_symmetricKnown]
  have hrev : (e.val.2, e.val.1) ∉ knownPairs k r := by
    intro he
    exact lt_asymm e.property (knownPairs_lt r _ _ he)
  simp only [hrev, or_false, ← mem_knownPairs r e]

theorem symmetricKnown_card {n k : ℕ} (r : Fin n → ℚ) :
    (symmetricKnown k r).card ≤ 2 * (fractionalMask k r).card := by
  have hc := card_union_le (knownPairs k r) ((knownPairs k r).image Prod.swap)
  have hi := card_image_le (s := knownPairs k r) (f := Prod.swap)
  rw [knownPairs_card] at hc hi
  change (symmetricKnown k r).card ≤ _ at hc
  omega

/-- Tie-breaking is public and complementary even on a learned zero coefficient. -/
def outwardTest {n : ℕ} (k : ℕ) (r : Fin n → ℚ) (i j : Fin n) : Prop :=
  if hij : i < j then 0 ≤ coefficients k r ⟨(i, j), hij⟩ else
    if hji : j < i then coefficients k r ⟨(j, i), hji⟩ < 0 else False

instance {n : ℕ} (k : ℕ) (r : Fin n → ℚ) (i j : Fin n) :
    Decidable (outwardTest k r i j) := by
  unfold outwardTest
  split_ifs <;> infer_instance

def outward {n : ℕ} (k : ℕ) (r : Fin n → ℚ) (i : Fin n) : Finset (Fin n) :=
  univ.filter (outwardTest k r i)

theorem outward_complementary {n k : ℕ} (r : Fin n → ℚ) (i j : Fin n) (hne : i ≠ j) :
    j ∈ outward k r i ↔ i ∉ outward k r j := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · simp [outward, outwardTest, hij, not_lt.mpr hij.le]
  · simp [outward, outwardTest, hji, not_lt.mpr hji.le]

def learnedTotal {n : ℕ} (d : Data n) (i j : Fin n) : ℕ :=
  if hij : i < j then d.learned ⟨(i, j), hij⟩ else
    if hji : j < i then d.learned ⟨(j, i), hji⟩ else 0

noncomputable def publicBaseCapacity {n : ℕ} (k : ℕ) (d : Data n) (i j : Fin n) : ℝ :=
  (learnedTotal d i j : ℝ) *
    (1 + (signedPairs (coefficients k d.potential) i j : ℝ) / (2 ^ scheduleBits n : ℕ)) / 2

/-- Every stored field depends only on returned query data. -/
noncomputable def baseState {n : ℕ} (k : ℕ) (d : Data n) : Blocking.State (Fin n) where
  singletonValue i := d.singleton i
  outward := outward k d.potential
  known := symmetricKnown k d.potential
  knownResidual := publicBaseCapacity k d

theorem preparation_learnedTotal {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k)
    (i j : Fin n)
    (hij : (i, j) ∈ symmetricKnown k ((preparationProg hk).eval G.out).potential) :
    learnedTotal ((preparationProg hk).eval G.out) i j = G.sym i j := by
  let d := (preparationProg hk).eval G.out
  change learnedTotal d i j = G.sym i j
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have he : (⟨(i, j), hlt⟩ : SparseBand.Pair n) ∈ fractionalMask k d.potential :=
      (mem_symmetricKnown_canonical d.potential ⟨(i, j), hlt⟩).mp hij
    have hm := preparationProg_learned G hk ⟨(i, j), hlt⟩
    change d.learned ⟨(i, j), hlt⟩ =
      (if ⟨(i, j), hlt⟩ ∈ fractionalMask k d.potential then G.sym i j else 0) at hm
    simpa only [learnedTotal, hlt, ↓reduceDIte, he, ↓reduceIte] using hm
  · simp [learnedTotal]
  · have he : (⟨(j, i), hgt⟩ : SparseBand.Pair n) ∈ fractionalMask k d.potential :=
      (mem_symmetricKnown_canonical d.potential ⟨(j, i), hgt⟩).mp
        ((symmetricKnown_symm d.potential i j).mp hij)
    have hm := preparationProg_learned G hk ⟨(j, i), hgt⟩
    change d.learned ⟨(j, i), hgt⟩ =
      (if ⟨(j, i), hgt⟩ ∈ fractionalMask k d.potential then G.sym j i else 0) at hm
    simpa only [learnedTotal, not_lt.mpr hgt.le, hgt, ↓reduceDIte, he, ↓reduceIte,
      G.sym_comm i j] using hm

theorem realizedBase_unknown {n k : ℕ} (G : DiGraph (Fin n))
    (d : Data n) (i j : Fin n) (hij : (i, j) ∉ symmetricKnown k d.potential) :
    (realizedBase G k d).c i j =
      if j ∈ outward k d.potential i then (realGraph G).sym.w i j else 0 := by
  have hQ : (0 : ℤ) < (2 ^ scheduleBits n : ℕ) := by positivity
  have hQnonneg : (0 : ℤ) ≤ (2 ^ scheduleBits n : ℕ) := hQ.le
  have hQnotneg : ¬ ((2 ^ scheduleBits n : ℕ) : ℤ) < 0 := by omega
  have hnegQ : -((2 ^ scheduleBits n : ℕ) : ℤ) < 0 := by omega
  have hnegQnotnonneg : ¬ (0 : ℤ) ≤ -((2 ^ scheduleBits n : ℕ) : ℤ) := by omega
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have he : (⟨(i, j), hlt⟩ : SparseBand.Pair n) ∉ fractionalMask k d.potential :=
      fun hm => hij ((mem_symmetricKnown_canonical d.potential ⟨(i, j), hlt⟩).mpr hm)
    rcases outside_mask_saturated (coefficients k d.potential)
        (coefficients_bounds k d.potential) ⟨(i, j), hlt⟩ he with hs | hs
    all_goals
      change (representation G (by positivity) (coefficients k d.potential)
        (coefficients_bounds k d.potential)).c i j = _
      rw [representation_forward G _ _ _ ⟨(i, j), hlt⟩]
      norm_num [outward, outwardTest, hlt, hs, hQnonneg, hnegQnotnonneg, WeightedDiGraph.sym_w,
        realGraph, DiGraph.sym]
  · simp [realizedBase, potentialRepresentation, representation_c, outward, outwardTest]
  · have he : (⟨(j, i), hgt⟩ : SparseBand.Pair n) ∉ fractionalMask k d.potential := by
      intro hm
      apply hij
      exact (symmetricKnown_symm d.potential i j).mpr
        ((mem_symmetricKnown_canonical d.potential ⟨(j, i), hgt⟩).mpr hm)
    rcases outside_mask_saturated (coefficients k d.potential)
        (coefficients_bounds k d.potential) ⟨(j, i), hgt⟩ he with hs | hs
    all_goals
      change (representation G (by positivity) (coefficients k d.potential)
        (coefficients_bounds k d.potential)).c i j = _
      rw [representation_reverse G _ _ _ ⟨(j, i), hgt⟩]
      norm_num [outward, outwardTest, hgt, not_lt.mpr hgt.le, hs, hnegQ, hQnotneg,
        WeightedDiGraph.sym_w, realGraph, DiGraph.sym, add_comm]

theorem baseState_realizes {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) :
    let d := (preparationProg hk).eval G.out
    (baseState k d).Realizes (realGraph G) (realizedBase G k d) := by
  let d := (preparationProg hk).eval G.out
  refine ⟨?_, symmetricKnown_symm d.potential, outward_complementary d.potential, ?_, ?_⟩
  · intro i
    change (d.singleton i : ℝ) = (realGraph G).out {i}
    rw [realGraph_out, preparationProg_singleton hk G.out i]
  · intro i j hij
    have hm := preparation_learnedTotal G hk i j hij
    change _ = (learnedTotal d i j : ℝ) * _ / 2
    rw [hm]
    rfl
  · exact realizedBase_unknown G d

noncomputable def publicSubflow {n : ℕ} (k : ℕ) (d : Data n) : Fin n → Fin n → ℝ :=
  Repair.learnedCanonicalSubflow (knownPairs k d.potential) (learnedCapacity k d)

theorem publicSubflow_isFlow {n : ℕ} (k : ℕ) (d : Data n) : IsFlow (publicSubflow k d) :=
  Repair.learnedCanonicalSubflow_isFlow _ _

theorem publicSubflow_zero {n : ℕ} (k : ℕ) (d : Data n) (i j : Fin n)
    (hij : (i, j) ∉ symmetricKnown k d.potential) : publicSubflow k d i j = 0 := by
  have hh : (i, j) ∉ knownPairs k d.potential ∧ (j, i) ∉ knownPairs k d.potential := by
    simpa only [mem_symmetricKnown, not_or] using hij
  simp [publicSubflow, Repair.learnedCanonicalSubflow, hh.1, hh.2]

/-- The selector reads only public learned canonical capacities. -/
noncomputable def publicCorrection {n : ℕ} (k : ℕ) (d : Data n) : Fin n → Fin n → ℝ :=
  Repair.learnedCorrection (publicSubflow k d) (publicSubflow_isFlow k d)

theorem publicCorrection_isFlow {n : ℕ} (k : ℕ) (d : Data n) :
    IsFlow (publicCorrection k d) :=
  Repair.learnedCorrection_isFlow (publicSubflow k d) (publicSubflow_isFlow k d)

theorem publicCorrection_zero {n : ℕ} (k : ℕ) (d : Data n) (i j : Fin n)
    (hij : (i, j) ∉ symmetricKnown k d.potential) : publicCorrection k d i j = 0 :=
  Repair.learnedCorrection_zero (publicSubflow k d) (publicSubflow_isFlow k d)
    i j (publicSubflow_zero k d i j hij)

theorem publicCorrection_l1 {n : ℕ} (k : ℕ) (d : Data n) :
    (∑ i, |2 * netOut (publicCorrection k d) i|) ≤ 2 * n := by
  simpa only [publicCorrection, Repair.l1, Fintype.card_fin] using
    Repair.learnedCorrection_divergence_l1 (publicSubflow k d) (publicSubflow_isFlow k d)

/-- Every omitted contribution is an integer; learned capacities are exact.
This discharges the rounding theorem's background premise from the actual program. -/
theorem publicSubflow_background_integer {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) :
    let d := (preparationProg hk).eval G.out
    ∀ i j, Repair.IntegerValue ((realizedBase G k d).c i j - publicSubflow k d i j) := by
  let d := (preparationProg hk).eval G.out
  refine Repair.learnedCanonicalSubflow_background_integer (realizedBase G k d)
    (knownPairs k d.potential) (learnedCapacity k d) ?_ ?_ ?_
  · intro i j
    refine ⟨((G.c i j + G.c j i : ℕ) : ℤ), ?_⟩
    rw [realizedBase_pair_sum]
    simp [realGraph]
  · intro i j hij hknown
    exact preparationProg_learnedCapacity G hk ⟨(i, j), hij⟩
      ((mem_knownPairs d.potential ⟨(i, j), hij⟩).mp hknown)
  · intro i j hij hunknown
    have he : (⟨(i, j), hij⟩ : SparseBand.Pair n) ∉ fractionalMask k d.potential :=
      fun h => hunknown ((mem_knownPairs d.potential ⟨(i, j), hij⟩).mpr h)
    exact representation_unlearned_integer G (by positivity)
      (coefficients k d.potential) (coefficients_bounds k d.potential) ⟨(i, j), hij⟩ he

/-- Hidden realized graph: it is never an input to public rounding or search. -/
noncomputable def realizedRounded {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) :
    WeightedDiGraph (Fin n) :=
  let d := (preparationProg hk).eval G.out
  Repair.roundedRepresentation (realizedBase G k d) (publicSubflow k d)
    (publicSubflow_isFlow k d) (publicSubflow_background_integer G hk)

theorem realizedRounded_c {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) (i j : Fin n) :
    let d := (preparationProg hk).eval G.out
    (realizedRounded G hk).c i j = (realizedBase G k d).c i j + publicCorrection k d i j := rfl

noncomputable def roundedState {n : ℕ} (k : ℕ) (d : Data n) : Blocking.State (Fin n) :=
  { baseState k d with knownResidual := fun i j => publicBaseCapacity k d i j + publicCorrection k d i j }

theorem roundedState_known_card {n k : ℕ} (hk : 0 < k) (d : Data n) :
    (roundedState k d).known.card ≤ 2 * SparseBand.bandBudget n k :=
  (symmetricKnown_card d.potential).trans
    (Nat.mul_le_mul_left 2 (fractionalMask_card_le hk d.potential))

theorem roundedState_realizes {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) :
    let d := (preparationProg hk).eval G.out
    (roundedState k d).Realizes (realGraph G) (realizedRounded G hk) := by
  let d := (preparationProg hk).eval G.out
  have hb := baseState_realizes G hk
  refine ⟨hb.singleton, hb.known_symm, hb.direction, ?_, ?_⟩
  · intro i j hij
    rw [realizedRounded_c]
    change (realizedBase G k d).c i j + publicCorrection k d i j =
      (baseState k d).knownResidual i j + publicCorrection k d i j
    rw [hb.learned i j hij]
  · intro i j hij
    rw [realizedRounded_c, publicCorrection_zero k d i j hij, add_zero]
    exact hb.unknown i j hij

theorem realizedRounded_integer {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) (i j : Fin n) :
    Repair.IntegerValue ((realizedRounded G hk).c i j) := by
  let d := (preparationProg hk).eval G.out
  exact Repair.roundedRepresentation_integer (realizedBase G k d) (publicSubflow k d)
    (publicSubflow_isFlow k d) (publicSubflow_background_integer G hk) i j

theorem realizedRounded_natural {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) (i j : Fin n) :
    ∃ m : ℕ, (realizedRounded G hk).c i j = m := by
  let d := (preparationProg hk).eval G.out
  exact Repair.roundedRepresentation_natural (realizedBase G k d) (publicSubflow k d)
    (publicSubflow_isFlow k d) (publicSubflow_background_integer G hk) i j

theorem realizedRounded_pair_sum {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) (i j : Fin n) :
    (realizedRounded G hk).c i j + (realizedRounded G hk).c j i =
      (realGraph G).c i j + (realGraph G).c j i := by
  rw [realizedRounded, Repair.roundedRepresentation_pair_sum]
  exact realizedBase_pair_sum G k _ i j

theorem realizedRounded_pairBounded {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hk : 0 < k) : Repair.PairBounded (realizedRounded G hk) := by
  let d := (preparationProg hk).eval G.out
  exact Repair.roundedRepresentation_pairBounded (realizedBase G k d) (publicSubflow k d)
    (publicSubflow_isFlow k d) (publicSubflow_background_integer G hk)
    (realizedBase_pairBounded G hG k d)

theorem realizedRounded_rise {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k)
    (i j : Fin n) (hc : 0 < (realizedRounded G hk).c i j) :
    (((preparationProg hk).eval G.out).potential j : ℝ) -
      ((preparationProg hk).eval G.out).potential i ≤ 2 := by
  let d := (preparationProg hk).eval G.out
  exact Repair.roundedRepresentation_rise (realizedBase G k d) (publicSubflow k d)
    (publicSubflow_isFlow k d) (publicSubflow_background_integer G hk)
    (fun v => (d.potential v : ℝ)) 2 (realizedBase_rise G hk d) i j hc

/-- The rounded divergence uses only the measured old divergence and public correction. -/
noncomputable def roundedDivergence {n : ℕ} (k : ℕ) (d : Data n) (i : Fin n) : ℝ :=
  (measuredDivergence d i : ℝ) + 2 * netOut (publicCorrection k d) i

noncomputable def repairDemand {n : ℕ} (k : ℕ) (d : Data n) (i : Fin n) : ℝ :=
  (roundedDivergence k d i - d.beta i) / 2

theorem realizedRounded_capacityDiv {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) (i : Fin n) :
    Repair.capacityDiv (realizedRounded G hk) i =
      roundedDivergence k ((preparationProg hk).eval G.out) i := by
  rw [realizedRounded, Repair.roundedRepresentation_capacityDiv,
    preparationProg_measuredDivergence]
  rfl

theorem repairDemand_eq {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) (i : Fin n) :
    repairDemand k ((preparationProg hk).eval G.out) i =
      (Repair.capacityDiv (realizedRounded G hk) i - Repair.capacityDiv (realGraph G) i) / 2 := by
  rw [realizedRounded_capacityDiv, ← preparationProg_beta G hk i]
  rfl

/-- Parity follows from integral pair-preserving capacities, via an integer difference flow. -/
theorem repairDemand_integer {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) (i : Fin n) :
    Repair.IntegerValue (repairDemand k ((preparationProg hk).eval G.out) i) := by
  rw [repairDemand_eq]
  apply Repair.integer_comparison_discrepancy
    (realizedRounded G hk) (realGraph G) (realizedRounded_pair_sum G hk)
    (realizedRounded_integer G hk)
  intro u v
  exact ⟨(G.c u v : ℤ), by simp [realGraph]⟩

/-- A witness to routability is constructed for the proof, without revealing it to the program. -/
theorem repairDemand_feasible {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) :
    ∃ f : Fin n → Fin n → ℝ, (realizedRounded G hk).Feasible f ∧
      ∀ i, netOut f i = repairDemand k ((preparationProg hk).eval G.out) i := by
  refine ⟨fun i j => (realizedRounded G hk).c i j - (realGraph G).c i j,
    Repair.comparison_feasible _ _ (realizedRounded_pair_sum G hk), ?_⟩
  intro i
  rw [Repair.comparison_divergence _ _ (realizedRounded_pair_sum G hk), repairDemand_eq]

theorem repairDemand_sum_zero {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) :
    ∑ i, repairDemand k ((preparationProg hk).eval G.out) i = 0 := by
  obtain ⟨f, hf, hdiv⟩ := repairDemand_feasible G hk
  simpa only [hdiv] using WeightedDiGraph.sum_univ_netOut hf.1

/-- The public output consumed by the operational repair layer. -/
structure Output (n : ℕ) where
  data : Data n
  state : Blocking.State (Fin n)
  demand : Fin n → ℝ

noncomputable def finishPreparation {n : ℕ} (k : ℕ) (d : Data n) : Output n :=
  ⟨d, roundedState k d, repairDemand k d⟩

/-- Integral preparation is free postprocessing of the fully counted public queries. -/
noncomputable def integralPreparationProg {n k : ℕ} (hk : 0 < k) :
    DTree (Finset (Fin n)) ℕ (Output n) (queryBudget n k) :=
  (preparationProg hk).map (finishPreparation k)

theorem integralPreparationProg_eval {n k : ℕ} (hk : 0 < k) (read : Finset (Fin n) → ℕ) :
    (integralPreparationProg hk).eval read = finishPreparation k ((preparationProg hk).eval read) :=
  DTree.eval_map _ _ _

theorem integralPreparationProg_cost {n k : ℕ} (hk : 0 < k) (read : Finset (Fin n) → ℕ) :
    (integralPreparationProg hk).cost read = (preparationProg hk).cost read := by
  simp only [integralPreparationProg, DTree.cost, DTree.run_map]

#print axioms outward_complementary
#print axioms preparation_learnedTotal
#print axioms realizedBase_unknown
#print axioms baseState_realizes
#print axioms publicSubflow_background_integer
#print axioms publicCorrection_l1
#print axioms roundedState_realizes
#print axioms realizedRounded_natural
#print axioms realizedRounded_capacityDiv
#print axioms realizedRounded_rise
#print axioms repairDemand_integer
#print axioms repairDemand_feasible
#print axioms repairDemand_sum_zero
#print axioms integralPreparationProg_cost

end CutQueryComplexity.DirectedUnitST.Preparation
