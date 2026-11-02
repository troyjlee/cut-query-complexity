import CutQueryComplexity.DirectedUnitST.Preparation.Basic

/-! # Public sparse-pair learning after the actual potential program

The public offset search is zero-query.  The potential is produced by the
checked accelerated cut program, then only pairs in its public fractional
coefficient mask are measured.  Unmeasured entries in the returned table are
zero.  Hidden capacities occur exclusively in the correctness theorems.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Preparation

open Finset Acceleration DirectedCertificate

/-- All data retained by preparation are functions of public oracle answers. -/
structure Data (n : ℕ) where
  beta : Fin n → ℚ
  potential : Fin n → ℚ
  gradient : Fin n → ℚ
  learned : SparseBand.Pair n → ℕ
  singleton : Fin n → ℕ

def coefficients {n : ℕ} (k : ℕ) (r : Fin n → ℚ) : SparseBand.Pair n → ℤ :=
  publicCoefficients k (scheduleBits n) (SparseBand.offsetRat (SparseBand.selectOffsets n k)) r

theorem coefficients_bounds {n : ℕ} (k : ℕ) (r : Fin n → ℚ) (e : SparseBand.Pair n) :
    -((2 ^ scheduleBits n : ℕ) : ℤ) ≤ coefficients k r e ∧
      coefficients k r e ≤ ((2 ^ scheduleBits n : ℕ) : ℤ) :=
  publicCoefficients_bounds k (scheduleBits n)
    (SparseBand.offsetRat (SparseBand.selectOffsets n k)) r e

/-- Recover the unregularized measured divergence by public rational arithmetic. -/
def measuredDivergence {n : ℕ} (d : Data n) (i : Fin n) : ℚ :=
  d.gradient i + d.beta i - d.potential i

/-- Hidden graph used only to state and prove the output's realization. -/
noncomputable def realizedBase {n : ℕ} (G : DiGraph (Fin n)) (k : ℕ) (d : Data n) :
    WeightedDiGraph (Fin n) :=
  potentialRepresentation G (scheduleBits n) (SparseBand.selectOffsets n k) d.potential

theorem realizedBase_pair_sum {n : ℕ} (G : DiGraph (Fin n)) (k : ℕ) (d : Data n)
    (i j : Fin n) :
    (realizedBase G k d).c i j + (realizedBase G k d).c j i =
      (realGraph G).c i j + (realGraph G).c j i := by
  rw [realizedBase, potentialRepresentation, representation_pair_sum]
  simp [realGraph, DiGraph.sym]

theorem realizedBase_pairBounded {n : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (k : ℕ) (d : Data n) : Repair.PairBounded (realizedBase G k d) :=
  representation_pairBounded G hG (by positivity) (coefficients k d.potential)
    (coefficients_bounds k d.potential)

theorem realizedBase_rise {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) (d : Data n)
    (i j : Fin n) (hc : 0 < (realizedBase G k d).c i j) :
    (d.potential j : ℝ) - d.potential i ≤ 2 :=
  potentialRepresentation_rise_two G hk _ _ _ i j hc

def fractionalMask {n : ℕ} (k : ℕ) (r : Fin n → ℚ) : Finset (SparseBand.Pair n) :=
  SparseBand.coefficientMask (2 ^ scheduleBits n) (coefficients k r)

def knownPairs {n : ℕ} (k : ℕ) (r : Fin n → ℚ) : Finset (Fin n × Fin n) :=
  (fractionalMask k r).image Subtype.val

theorem mem_knownPairs {n k : ℕ} (r : Fin n → ℚ) (e : SparseBand.Pair n) :
    e.val ∈ knownPairs k r ↔ e ∈ fractionalMask k r := by
  constructor
  · intro he
    obtain ⟨d, hd, hde⟩ := mem_image.mp he
    exact (Subtype.ext hde : d = e) ▸ hd
  · exact fun he => mem_image_of_mem Subtype.val he

theorem knownPairs_card {n k : ℕ} (r : Fin n → ℚ) :
    (knownPairs k r).card = (fractionalMask k r).card :=
  card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)

/-- Only learned canonical pair totals enter this public capacity table. -/
noncomputable def learnedCapacity {n : ℕ} (k : ℕ) (d : Data n) (i j : Fin n) : ℝ :=
  if hij : i < j then
    (d.learned ⟨(i, j), hij⟩ : ℝ) *
      (1 + (coefficients k d.potential ⟨(i, j), hij⟩ : ℝ) / (2 ^ scheduleBits n : ℕ)) / 2
  else 0

theorem fractionalMask_card_le {n k : ℕ} (hk : 0 < k) (r : Fin n → ℚ) :
    (fractionalMask k r).card ≤ SparseBand.bandBudget n k :=
  SparseBand.coefficientMask_card_le hk (fun i => (r i : ℝ)) _ _
    (publicCoefficients_active hk (scheduleBits n) (SparseBand.selectOffsets n k) r)

/-- Each supplied canonical pair is measured by the existing three-cut identity. -/
def measurePairs {n : ℕ} : (es : List (SparseBand.Pair n)) →
    DTree (Finset (Fin n)) ℕ (SparseBand.Pair n → ℕ) (3 * es.length)
  | [] => DTree.pure (fun _ => 0)
  | e :: es => ((pairQuery {e.val.1} {e.val.2}).bind fun u =>
      (measurePairs es).map fun a => Function.update a e u).cast
        (by simp only [List.length_cons]; omega)

theorem measurePairs_eval {n : ℕ} (G : DiGraph (Fin n))
    (es : List (SparseBand.Pair n)) (e : SparseBand.Pair n) :
    (measurePairs es).eval G.out e = if e ∈ es then G.sym e.val.1 e.val.2 else 0 := by
  induction es with
  | nil => simp [measurePairs]
  | cons d es ih =>
      have hd : Disjoint ({d.val.1} : Finset (Fin n)) {d.val.2} := by
        simp [ne_of_lt d.property]
      simp only [measurePairs, DTree.eval_cast, DTree.eval_bind, DTree.eval_map,
        pairQuery_eval G hd, DiGraph.pairs, sum_singleton]
      by_cases he : e = d
      · subst e
        simp
      · simp [ih, he]

noncomputable def measureMask {n : ℕ} (k : ℕ) (r : Fin n → ℚ) :
    DTree (Finset (Fin n)) ℕ (SparseBand.Pair n → ℕ) (3 * (fractionalMask k r).card) :=
  (measurePairs (fractionalMask k r).toList).cast (by rw [length_toList])

theorem measureMask_eval {n k : ℕ} (G : DiGraph (Fin n)) (r : Fin n → ℚ)
    (e : SparseBand.Pair n) :
    (measureMask k r).eval G.out e =
      if e ∈ fractionalMask k r then G.sym e.val.1 e.val.2 else 0 := by
  simp only [measureMask, DTree.eval_cast, measurePairs_eval, mem_toList]

/-- The all-potential sparse-band theorem gives one public budget before any answers. -/
noncomputable def measurePublicMask {n k : ℕ} (hk : 0 < k) (r : Fin n → ℚ) :
    DTree (Finset (Fin n)) ℕ (SparseBand.Pair n → ℕ) (3 * SparseBand.bandBudget n k) :=
  DTree.weaken (Nat.mul_le_mul_left 3 (fractionalMask_card_le hk r)) (measureMask k r)

theorem measurePublicMask_eval {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k)
    (r : Fin n → ℚ) (e : SparseBand.Pair n) :
    (measurePublicMask hk r).eval G.out e =
      if e ∈ fractionalMask k r then G.sym e.val.1 e.val.2 else 0 := by
  simpa only [measurePublicMask, DTree.eval, DTree.run_weaken] using measureMask_eval G r e

/-- Original singleton cuts are explicitly queried for the residual-search state. -/
def singletonRows {n : ℕ} : (vs : List (Fin n)) →
    DTree (Finset (Fin n)) ℕ (Fin n → ℕ) vs.length
  | [] => DTree.pure (fun _ => 0)
  | v :: vs => DTree.query {v} fun a =>
      (singletonRows vs).map fun f => Function.update f v a

theorem singletonRows_eval {n : ℕ} (read : Finset (Fin n) → ℕ)
    (vs : List (Fin n)) (v : Fin n) (hv : v ∈ vs) :
    (singletonRows vs).eval read v = read {v} := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
      simp only [singletonRows, DTree.eval_query, DTree.eval_map]
      by_cases he : v = w
      · subst v
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne he]
        exact ih ((List.mem_cons.mp hv).resolve_left he)

noncomputable def singletonProg (n : ℕ) : DTree (Finset (Fin n)) ℕ (Fin n → ℕ) n :=
  (singletonRows (univ : Finset (Fin n)).toList).cast
    (by rw [length_toList, card_univ, Fintype.card_fin])

theorem singletonProg_eval {n : ℕ} (read : Finset (Fin n) → ℕ) (v : Fin n) :
    (singletonProg n).eval read v = read {v} := by
  rw [singletonProg, DTree.eval_cast]
  exact singletonRows_eval read _ v (mem_toList.mpr (mem_univ v))

abbrev potentialBudget (n k : ℕ) : ℕ :=
  2 * n + (scheduleSteps n k + 1) * (6 * (scheduleBits n + 1) * n)

abbrev queryBudget (n k : ℕ) : ℕ := n + (potentialBudget n k + 3 * SparseBand.bandBudget n k)

/-- Public offsets, actual acceleration, then exactly the public fractional mask.
The offset computation is the value of the zero-query `SparseBand.offsetsProg`. -/
noncomputable def preparationProg {n k : ℕ} (hk : 0 < k) :
    DTree (Finset (Fin n)) ℕ (Data n) (queryBudget n k) :=
  (singletonProg n).bind fun singleton =>
    (queryPotentialProg k (SparseBand.selectOffsets n k)).bind fun out =>
      (measurePublicMask hk out.2.1).map fun learned =>
        ⟨out.1, out.2.1, out.2.2, learned, singleton⟩

theorem preparationProg_eval {n k : ℕ} (hk : 0 < k) (read : Finset (Fin n) → ℕ) :
    (preparationProg hk).eval read =
      let out := (queryPotentialProg k (SparseBand.selectOffsets n k)).eval read
      ⟨out.1, out.2.1, out.2.2, (measurePublicMask hk out.2.1).eval read,
        (singletonProg n).eval read⟩ := by
  simp only [preparationProg, DTree.eval_bind, DTree.eval_map]

/-- The uniform budget holds for arbitrary oracle answers. -/
theorem preparationProg_cost {n k : ℕ} (hk : 0 < k) (read : Finset (Fin n) → ℕ) :
    (preparationProg hk).cost read ≤ queryBudget n k := DTree.cost_le _ _

theorem preparationProg_cost_sqrt {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (read : Finset (Fin n) → ℕ) :
    ((preparationProg hk).cost read : ℝ) ≤
      n + (60 * n * (Real.sqrt ((n : ℝ) * k) + 1) * ((scheduleBits n : ℝ) + 1) ^ 2 +
        3 * SparseBand.bandBudget n k) := by
  have hc := queryPotentialProg_cost_sqrt hn (SparseBand.selectOffsets n k) read
  have hm := DTree.cost_le (measurePublicMask hk
    ((queryPotentialProg k (SparseBand.selectOffsets n k)).eval read).2.1) read
  have hmR : ((measurePublicMask hk
      ((queryPotentialProg k (SparseBand.selectOffsets n k)).eval read).2.1).cost read : ℝ) ≤
      3 * SparseBand.bandBudget n k := by exact_mod_cast hm
  have hsR : ((singletonProg n).cost read : ℝ) ≤ n := by
    exact_mod_cast DTree.cost_le (singletonProg n) read
  have he : (preparationProg hk).cost read =
      (singletonProg n).cost read + ((queryPotentialProg k (SparseBand.selectOffsets n k)).cost read +
        (measurePublicMask hk
          ((queryPotentialProg k (SparseBand.selectOffsets n k)).eval read).2.1).cost read) := by
    simp only [preparationProg, DTree.cost, DTree.run_bind, DTree.run_map]
  rw [he, Nat.cast_add, Nat.cast_add]
  exact add_le_add hsR (add_le_add hc hmR)

theorem preparationProg_singleton {n k : ℕ} (hk : 0 < k)
    (read : Finset (Fin n) → ℕ) (v : Fin n) :
    ((preparationProg hk).eval read).singleton v = read {v} := by
  simp only [preparationProg_eval, singletonProg_eval]

/-- Learned entries are exact, and all other table entries are explicitly zero. -/
theorem preparationProg_learned {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k)
    (e : SparseBand.Pair n) :
    let d := (preparationProg hk).eval G.out
    d.learned e = if e ∈ fractionalMask k d.potential then G.sym e.val.1 e.val.2 else 0 := by
  simp only [preparationProg_eval]
  exact measurePublicMask_eval G hk _ e

theorem preparationProg_mask_card {n k : ℕ} (hk : 0 < k) (read : Finset (Fin n) → ℕ) :
    (fractionalMask k ((preparationProg hk).eval read).potential).card ≤
      SparseBand.bandBudget n k := fractionalMask_card_le hk _

theorem preparationProg_learnedCapacity {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k)
    (e : SparseBand.Pair n)
    (he : e ∈ fractionalMask k ((preparationProg hk).eval G.out).potential) :
    let d := (preparationProg hk).eval G.out
    learnedCapacity k d e.val.1 e.val.2 =
      (potentialRepresentation G (scheduleBits n) (SparseBand.selectOffsets n k) d.potential).c
        e.val.1 e.val.2 := by
  have hm := preparationProg_learned G hk e
  simp only [he, ↓reduceIte] at hm
  simp only [learnedCapacity, e.property, ↓reduceDIte, potentialRepresentation,
    representation_forward, coefficients, hm]

theorem preparationProg_beta {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) (i : Fin n) :
    (((preparationProg hk).eval G.out).beta i : ℝ) =
      Repair.capacityDiv (realGraph G) i := by
  rw [preparationProg_eval, realGraph_capacityDiv]
  have h := degreeBetaProg_correct G i
  simpa only [queryPotentialProg, DTree.eval_bind, DTree.eval_map, Rat.cast_sub,
    Rat.cast_natCast] using congrArg (fun t : ℚ => (t : ℝ)) h

theorem preparationProg_mean_zero {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k) :
    (∑ i, ((preparationProg hk).eval G.out).potential i = 0) ∧
      (∑ i, ((preparationProg hk).eval G.out).gradient i = 0) := by
  simpa only [preparationProg_eval] using
    queryPotentialProg_mean_zero G (SparseBand.selectOffsets n k)

theorem preparationProg_l1 {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 0 < k) :
    (∑ i, |(((preparationProg hk).eval G.out).gradient i : ℝ)|) ≤
      4 * (n : ℝ) * Real.sqrt k + n + 1 / 32 := by
  simpa only [preparationProg_eval] using
    queryPotentialProg_l1_explicit G hG hn hk (SparseBand.selectOffsets n k)

/-- Exact regularized divergence for the hidden capacity realization. -/
theorem preparationProg_regularized_divergence {n k : ℕ} (G : DiGraph (Fin n))
    (hk : 0 < k) (i : Fin n) :
    let d := (preparationProg hk).eval G.out
    (d.gradient i : ℝ) = Repair.capacityDiv
      (potentialRepresentation G (scheduleBits n) (SparseBand.selectOffsets n k) d.potential) i -
        d.beta i + d.potential i := by
  simp only [preparationProg_eval, potentialRepresentation, representation_capacityDiv]
  have hh := queryPotentialProg_regularized_divergence G (SparseBand.selectOffsets n k) i
  simpa only [div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast] using hh

theorem preparationProg_measuredDivergence {n k : ℕ} (G : DiGraph (Fin n))
    (hk : 0 < k) (i : Fin n) :
    let d := (preparationProg hk).eval G.out
    Repair.capacityDiv (realizedBase G k d) i = (measuredDivergence d i : ℝ) := by
  have hh := preparationProg_regularized_divergence G hk i
  simp only [measuredDivergence, Rat.cast_sub, Rat.cast_add]
  dsimp only [realizedBase]
  linarith

#print axioms fractionalMask_card_le
#print axioms measurePairs_eval
#print axioms preparationProg_learned
#print axioms preparationProg_singleton
#print axioms preparationProg_learnedCapacity
#print axioms preparationProg_cost
#print axioms preparationProg_cost_sqrt
#print axioms preparationProg_beta
#print axioms preparationProg_regularized_divergence
#print axioms preparationProg_measuredDivergence
#print axioms preparationProg_l1
#print axioms preparationProg_mean_zero

end CutQueryComplexity.DirectedUnitST.Preparation
