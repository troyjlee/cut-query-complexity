import CutQueryComplexity.StarContraction2022.Quantum.UniformStars.Quotient
import CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Neighbors

/-!
# The guarded uniform-star high-degree candidate program

The constructor receives only n. Center rows are obtained from actual singleton
product queries and validated before any choices are drawn. Every continuation
uses the complete learned table; the graph is present only in the proofs.
The weighted adapter retains its existing single original-value query.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.UniformStars

open Finset
open CutQueryComplexity.Probability
open scoped Classical ENNReal
noncomputable section

variable {n : ℕ}

/-- The actual weighted adapter with a public quotient-size guard. -/
def weightedFinish (f : Fin n → Option (Fin n)) :
    ProductPrograms.ProductTree n (ProductPrograms.Candidate n) (bmax n) :=
  if h : 2 ≤ (starLabels f).card ∧ (starLabels f).card ≤ kcap n then
    (ProductPrograms.cutTreeToProduct
      (WeightedAdapter.program (starQuotient f)
        (by simpa only [Fintype.card_fin] using h.1))).weaken
      (weighted_budget_le_bmax h.1 h.2)
  else RTree.pure (PMF.pure none)

/-- Choices use exactly the table obtained from this complete center transcript. -/
def choiceStage (R : Finset (Fin n)) (rows : ProductPrograms.NeighborhoodTable n) :
    ProductPrograms.ProductTree n (ProductPrograms.Candidate n) (bmax n) :=
  RTree.mix ((starChoiceLaw R (ProductPrograms.outsideCenterNeighbors R rows)).map weightedFinish)

/-- The size guard is tested before the first neighborhood query. -/
def centerStage (R : Finset (Fin n)) :
    ProductPrograms.ProductTree n (ProductPrograms.Candidate n) (QH n) :=
  if hR : R.card ≤ kcap n then
    ((ProductPrograms.centerNeighborhoods R).bind (fun rows =>
      match rows with
      | none => RTree.pure (q := bmax n) (PMF.pure none)
      | some rows => choiceStage R rows)).weaken (Nat.add_le_add_right hR (bmax n))
  else RTree.pure (PMF.pure none)

/-- A single public high-degree trial, with pure small-n boundary cases. -/
def highCandidate (n : ℕ) :
    ProductPrograms.ProductTree n (ProductPrograms.Candidate n) (QH n) :=
  if 2 ≤ n then
    RTree.mix ((centerLaw (centerProbability n) (centerProbability_le_one n)).map centerStage)
  else RTree.pure (PMF.pure none)

theorem highCandidate_small {n : ℕ} (hn : n ≤ 1)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    RTree.run read (highCandidate n) = PMF.pure (none, 0) := by
  simp [highCandidate, show ¬ 2 ≤ n by omega, RTree.run_pure, PMF.pure_map]

/-- Every finite answer table obeys the public schedule, including malformed replies. -/
theorem highCandidate_cost (n : ℕ) (read : Finset (Fin n) → ProductAnswer n 1)
    {out : ProductPrograms.Candidate n × ℕ}
    (hout : out ∈ (RTree.run read (highCandidate n)).support) : out.2 ≤ QH n :=
  RTree.cost_le _ read hout

theorem highCandidate_cost_envelope {n : ℕ} (hn : 2 ≤ n)
    (read : Finset (Fin n) → ProductAnswer n 1) {out : ProductPrograms.Candidate n × ℕ}
    (hout : out ∈ (RTree.run read (highCandidate n)).support) :
    (out.2 : ℝ) ≤ 50000000000 * Real.sqrt (n : ℝ) *
      (ProductPrograms.logWidth n : ℝ) ^ 3 := by
  have hc : (out.2 : ℝ) ≤ QH n := by exact_mod_cast highCandidate_cost n read hout
  exact hc.trans (QH_envelope hn)

theorem choiceStage_eval (R : Finset (Fin n)) (rows : ProductPrograms.NeighborhoodTable n)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (choiceStage R rows).eval read =
      (starChoiceLaw R (ProductPrograms.outsideCenterNeighbors R rows)).bind
        (fun f => (weightedFinish f).eval read) := by
  simp only [choiceStage, RTree.eval_mix, PMF.bind_map, Function.comp_def]

/-- Exact conditional law for every accepted complete public row transcript. -/
theorem centerStage_eval_valid (R : Finset (Fin n)) (hR : R.card ≤ kcap n)
    (read : Finset (Fin n) → ProductAnswer n 1)
    (hv : ∀ r ∈ R, ProductPrograms.neighborhoodAnswerValid r (read {r})) :
    (centerStage R).eval read =
      (starChoiceLaw R (ProductPrograms.outsideCenterNeighbors R
        (ProductPrograms.measuredNeighborhoodTable R read))).bind
          (fun f => (weightedFinish f).eval read) := by
  have he : (ProductPrograms.centerNeighborhoods R).eval read =
      PMF.pure (some (ProductPrograms.measuredNeighborhoodTable R read)) := by
    simp only [RTree.eval, ProductPrograms.centerNeighborhoods_run_of_valid R read hv,
      PMF.pure_map]
  unfold centerStage
  rw [dite_eq_left hR]
  exact (RTree.eval_weaken (Nat.add_le_add_right hR (bmax n)) _ read).trans (by
    rw [RTree.eval_bind, he, PMF.pure_bind]
    exact choiceStage_eval R _ read)

theorem honest_starChoiceLaw (G : SimpleInput (Fin n)) (R : Finset (Fin n)) :
    starChoiceLaw R (ProductPrograms.outsideCenterNeighbors R
      (ProductPrograms.exactCenterNeighborhoodTable G R)) =
      starChoiceLaw R (Contraction.SparseCenters.inputRows G) := by
  apply congrArg choiceLaw
  funext v
  by_cases hv : v ∈ R
  · simp only [starRows, hv, ite_true]
  · simp only [starRows, hv, ite_false, ProductPrograms.outsideCenterNeighbors_exact]
    ext w
    have hb := (G.w v w).isLt
    have he : (G.w v w : ℕ) = 1 ↔ 0 < G.toWeighted.w v w := by
      change (G.w v w : ℕ) = 1 ↔ (0 : ℝ) < ((G.w v w : ℕ) : ℝ)
      rw [Nat.cast_pos]
      omega
    simp only [mem_inter, mem_filter, Contraction.SparseCenters.inputRows,
      AllPairs.rowSupport, mem_univ, true_and, he]
    tauto

theorem centerStage_eval_honest (G : SimpleInput (Fin n)) (R : Finset (Fin n)) :
    (centerStage R).eval (productRead G) =
      if R.card ≤ kcap n then
        (starChoiceLaw R (Contraction.SparseCenters.inputRows G)).bind
          (fun f => (weightedFinish f).eval (productRead G))
      else PMF.pure none := by
  by_cases hR : R.card ≤ kcap n
  · rw [ite_eq_left hR]
    rw [centerStage_eval_valid R hR (productRead G)
      (fun r _ => ProductPrograms.neighborhoodAnswerValid_honest G r),
      ProductPrograms.measuredNeighborhoodTable_honest, honest_starChoiceLaw]
  · simp only [centerStage, dite_eq_right hR, ite_eq_right hR, RTree.eval_pure]

theorem highCandidate_eval (n : ℕ) (hn : 2 ≤ n)
    (read : Finset (Fin n) → ProductAnswer n 1) :
    (highCandidate n).eval read =
      (centerLaw (centerProbability n) (centerProbability_le_one n)).bind
        (fun R => (centerStage R).eval read) := by
  simp only [highCandidate, ite_eq_left hn, RTree.eval_mix, PMF.bind_map, Function.comp_def]

/-- Honest execution is the original center/choice law followed by guarded finishing.
Rejected center sets do not change the sampling law or condition its kernel. -/
theorem highCandidate_eval_honest (G : SimpleInput (Fin n)) (hn : 2 ≤ n) :
    (highCandidate n).eval (productRead G) =
      (centerChoiceLaw (centerProbability n) (centerProbability_le_one n)
        (fun _ => Contraction.SparseCenters.inputRows G)).bind (fun x =>
          if x.1.card ≤ kcap n then (weightedFinish x.2).eval (productRead G)
          else PMF.pure none) := by
  rw [highCandidate_eval n hn, centerChoiceLaw, PMF.bind_bind]
  congr 1
  funext R
  rw [centerStage_eval_honest, PMF.bind_map]
  by_cases hR : R.card ≤ kcap n
  · simp only [Function.comp_def, hR, ite_true]
  · simp only [Function.comp_def, hR, ite_false, PMF.bind_const]

private theorem weighted_cutTreeSound (f : Fin n → Option (Fin n))
    (hq : 2 ≤ Fintype.card (Fin (starLabels f).card)) (G : SimpleInput (Fin n)) :
    CutTreeSound (WeightedAdapter.program (starQuotient f) hq) G.toWeighted := by
  intro out k hout
  apply WeightedAdapter.program_sound (starQuotient f) hq G.toWeighted
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(some out, k), hout, rfl⟩

theorem weightedFinish_sound (f : Fin n → Option (Fin n)) (G : SimpleInput (Fin n)) :
    ProductPrograms.ProductTreeSound (weightedFinish f) G := by
  intro out hout
  unfold weightedFinish at hout
  split_ifs at hout with h
  · rw [RTree.eval_weaken] at hout
    exact ProductPrograms.cutTreeToProduct_sound _ G (weighted_cutTreeSound f _ G) out hout
  · rw [RTree.eval_pure, PMF.mem_support_pure_iff] at hout
    subst out
    trivial

/-- Any returned cut is proper and carries its exact original value, whether or
not its sampled star contraction preserved a minimum cut. -/
theorem highCandidate_sound (n : ℕ) (G : SimpleInput (Fin n)) :
    ProductPrograms.ProductTreeSound (highCandidate n) G := by
  intro out hout
  by_cases hn : 2 ≤ n
  · rw [highCandidate_eval_honest G hn, PMF.mem_support_bind_iff] at hout
    obtain ⟨x, _, hout⟩ := hout
    split_ifs at hout
    · exact weightedFinish_sound x.2 G out hout
    · rw [PMF.mem_support_pure_iff] at hout
      subst out
      trivial
  · simp only [highCandidate, ite_eq_right hn, RTree.eval_pure, PMF.mem_support_pure_iff] at hout
    subst out
    trivial

/-- The decoded finite output is an exact original minimum-cut result. -/
def MinimumCandidate (G : SimpleInput (Fin n)) (out : ProductPrograms.Candidate n) : Prop :=
  ∃ r, decodeFiniteCutResult out = some r ∧ r.Sound G.toWeighted ∧
    IsMinCut G.toWeighted r.shore ∧ r.value = mincutValue G.toWeighted

theorem weightedFinish_success (G : SimpleInput (Fin n)) (S R : Finset (Fin n))
    (f : Fin n → Option (Fin n)) (hS : IsMinCut G.toWeighted S)
    (hf : f ∈ (starChoiceLaw R (Contraction.SparseCenters.inputRows G)).support)
    (ha : Avoids (Contraction.SparseCenters.inputCrossRows G S) f)
    (hc : Covered (Contraction.SparseCenters.inputRows G) R) (hR : R.card ≤ kcap n) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤
      mass ((weightedFinish f).eval (productRead G)) (MinimumCandidate G) := by
  have hs := starQuotient_respects G S R f hf ha
  have hq := (starQuotient f).two_le_card_of_survives hs hS.1
  have hq' : 2 ≤ (starLabels f).card := by simpa only [Fintype.card_fin] using hq
  have hcap : (starLabels f).card ≤ kcap n := by
    rw [starLabels_eq_centers R _ f hf hc]
    exact hR
  have hp := success_of_failure_le ((WeightedAdapter.program (starQuotient f) hq).eval
    G.toWeighted.cut) (fun o => ∃ r, o = some r ∧ r.Sound G.toWeighted ∧
      IsMinCut G.toWeighted r.shore ∧ r.value = mincutValue G.toWeighted)
    (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (WeightedAdapter.program_failure (starQuotient f) hq G.toWeighted hS hs)
  have he := ProductPrograms.cutTreeToProduct_successProb
    (WeightedAdapter.program (starQuotient f) hq) G (weighted_cutTreeSound f hq G)
    (fun o => ∃ r, o = some r ∧ r.Sound G.toWeighted ∧
      IsMinCut G.toWeighted r.shore ∧ r.value = mincutValue G.toWeighted)
  simp only [RTree.successProb_eq] at he
  apply ENNReal.ofReal_le_of_le_toReal
  unfold weightedFinish
  rw [dite_eq_left ⟨hq', hcap⟩, RTree.eval_weaken]
  change (mass _ (MinimumCandidate G)).toReal = _ at he
  rw [he]
  unfold mass at hp
  linarith

/-- On the unconditioned center/choice law, the good transcript event has the
proved survival mass, and each such transcript invokes the actual weighted solver. -/
theorem highCandidate_minimum_mass_of_lt_one (G : SimpleInput (Fin n))
    (S : Finset (Fin n)) (δ : ℝ) (hn : 2 ≤ n) (hp : centerProbability n < 1)
    (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ)
    (hS : IsMinCut G.toWeighted S) (hdegree : ∀ v, δ ≤ G.toWeighted.degree v)
    (hcut : G.toWeighted.cut S < δ) :
    ENNReal.ofReal pstar ≤ mass ((highCandidate n).eval (productRead G)) (MinimumCandidate G) := by
  let law := centerChoiceLaw (centerProbability n) (centerProbability_le_one n)
    (fun _ => Contraction.SparseCenters.inputRows G)
  let Good := fun x : Finset (Fin n) × (Fin n → Option (Fin n)) =>
    Avoids (Contraction.SparseCenters.inputCrossRows G S) x.2 ∧
      ¬ BadCenters (Contraction.SparseCenters.inputRows G) x.1
  have hs : ENNReal.ofReal ((3 : ℝ) ^ (-13 : ℤ)) ≤ mass law Good :=
    minimum_guarded_survival G S δ hn hp hδ hS hdegree hcut
  rw [highCandidate_eval_honest G hn]
  calc
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-13 : ℤ)) * ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold pstar
      ring
    _ ≤ mass law Good * ENNReal.ofReal (1 / 2 : ℝ) :=
      mul_le_mul hs le_rfl (by positivity) (by positivity)
    _ ≤ _ := by
      apply Probability.mass_bind_ge law _ Good (MinimumCandidate G) _
      rintro ⟨R, f⟩ hsupport ⟨ha, hb⟩
      have hf := ((centerChoiceLaw_support (centerProbability n)
        (centerProbability_le_one n) _ R f).mp hsupport).2
      have hR : R.card ≤ kcap n := le_of_not_gt (fun h => hb (Or.inl h))
      have hc : Covered (Contraction.SparseCenters.inputRows G) R :=
        not_not.mp (fun h => hb (Or.inr h))
      rw [ite_eq_left hR]
      exact weightedFinish_success G S R f hS hf ha hc hR

/-- Probability one selects every vertex and no edges. Its quotient is the
identity up to public relabeling, so no large-mean hypothesis is needed. -/
theorem highCandidate_minimum_mass_of_probability_one (G : SimpleInput (Fin n))
    (S : Finset (Fin n)) (hn : 2 ≤ n) (hp : centerProbability n = 1)
    (hS : IsMinCut G.toWeighted S) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤
      mass ((highCandidate n).eval (productRead G)) (MinimumCandidate G) := by
  let law := centerChoiceLaw (centerProbability n) (centerProbability_le_one n)
    (fun _ => Contraction.SparseCenters.inputRows G)
  rw [highCandidate_eval_honest G hn]
  calc
    _ = mass law (fun _ => True) * ENNReal.ofReal (1 / 2 : ℝ) := by rw [mass_true, one_mul]
    _ ≤ _ := by
      apply Probability.mass_bind_ge law _ (fun _ => True) (MinimumCandidate G) _
      rintro ⟨R, f⟩ hsupport _
      have hf := ((centerChoiceLaw_support (centerProbability n)
        (centerProbability_le_one n) _ R f).mp hsupport).2
      have hone : (R, f) ∈
          (centerChoiceLaw 1 le_rfl (fun _ => Contraction.SparseCenters.inputRows G)).support := by
        simpa only [law, hp] using hsupport
      obtain ⟨hRu, hnone⟩ := centerChoiceLaw_one_support _ R f hone
      have hR : R.card ≤ kcap n := by
        rw [hRu, card_univ, Fintype.card_fin, kcap_eq_n_of_probability_one hp]
      have hc : Covered (Contraction.SparseCenters.inputRows G) R := by
        intro v hv
        exact False.elim (hv (hRu ▸ mem_univ v))
      have ha : Avoids (Contraction.SparseCenters.inputCrossRows G S) f := by
        intro v
        simp only [hnone v, Option.elim_none]
      rw [ite_eq_left hR]
      exact weightedFinish_success G S R f hS hf ha hc hR

/-- All degree and minimum-cut hypotheses concern the hidden graph solely in
the correctness theorem; the public program itself takes only n. -/
theorem highCandidate_minimum_mass (G : SimpleInput (Fin n)) (δ : ℝ)
    (hn : 2 ≤ n) (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ)
    (hdegree : ∀ v, δ ≤ G.toWeighted.degree v)
    (hmin : mincutValue G.toWeighted < δ) :
    ENNReal.ofReal pstar ≤ mass ((highCandidate n).eval (productRead G)) (MinimumCandidate G) := by
  obtain ⟨S, hS⟩ := exists_isMinCut_of_two_le_card G.toWeighted
    (by simpa only [Fintype.card_fin] using hn)
  by_cases hp : centerProbability n < 1
  · exact highCandidate_minimum_mass_of_lt_one G S δ hn hp hδ hS hdegree
      (by rw [cut_eq_mincut_of_isMinCut hS]; exact hmin)
  · have hp1 : centerProbability n = 1 :=
      le_antisymm (centerProbability_le_one n) (le_of_not_gt hp)
    exact (ENNReal.ofReal_le_ofReal pstar_le_half).trans
      (highCandidate_minimum_mass_of_probability_one G S hn hp1 hS)

theorem highCandidate_success (G : SimpleInput (Fin n)) (δ : ℝ)
    (hn : 2 ≤ n) (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ)
    (hdegree : ∀ v, δ ≤ G.toWeighted.degree v)
    (hmin : mincutValue G.toWeighted < δ) :
    pstar ≤ (highCandidate n).successProb (productRead G) (MinimumCandidate G) := by
  rw [RTree.successProb_eq]
  exact (ENNReal.ofReal_le_iff_le_toReal (mass_ne_top _ _)).mp
    (highCandidate_minimum_mass G δ hn hδ hdegree hmin)

section Physical

open QuantumQueryComplexity
open scoped Matrix

attribute [local instance] ProductPrograms.basisDecidableEq ProductPrograms.workspaceDecidableEq

/-- The actual compiled schedule includes all calls used by the product compiler. -/
theorem highCandidate_physical_length (n : ℕ) :
    (ProductPrograms.productTreeRoutine (highCandidate n)).len =
      12 * productBits n 1 * QH n :=
  ProductPrograms.productTreeRoutine_len _

/-- Operational normalization also holds for physical tables inconsistent with a graph. -/
theorem highCandidate_physical_normalized (n : ℕ)
    (read : Finset (Fin n) → CutAnswer n 1) :
    IsQState ((ProductPrograms.productTreeRoutine (highCandidate n)).run read *ᵥ
      (ProductPrograms.productTreeAlg (highCandidate n)).init) :=
  ProductPrograms.productTreeRoutine_isQState _ read

/-- Exact honest Born-event law at the state produced by the actual routine. -/
theorem highCandidate_physical_event_law (G : SimpleInput (Fin n))
    (Good : ProductPrograms.Candidate n → Prop) :
    goodProb (ProductPrograms.productTreeAlg (highCandidate n)).readout Good
        ((ProductPrograms.productTreeRoutine (highCandidate n)).run (capacityRead G) *ᵥ
          (ProductPrograms.productTreeAlg (highCandidate n)).init) =
      (highCandidate n).successProb (productRead G) Good := by
  rw [ProductPrograms.productTreeRoutine_state, ProductPrograms.productTreeAlg_successProb]

theorem highCandidate_physical_success (G : SimpleInput (Fin n)) (δ : ℝ)
    (hn : 2 ≤ n) (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ)
    (hdegree : ∀ v, δ ≤ G.toWeighted.degree v)
    (hmin : mincutValue G.toWeighted < δ) :
    pstar ≤ goodProb (ProductPrograms.productTreeAlg (highCandidate n)).readout (MinimumCandidate G)
      ((ProductPrograms.productTreeRoutine (highCandidate n)).run (capacityRead G) *ᵥ
        (ProductPrograms.productTreeAlg (highCandidate n)).init) := by
  rw [highCandidate_physical_event_law]
  exact highCandidate_success G δ hn hδ hdegree hmin

theorem highCandidate_physical_envelope {n : ℕ} (hn : 2 ≤ n) :
    ((ProductPrograms.productTreeRoutine (highCandidate n)).len : ℝ) ≤
      600000000000 * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 4 := by
  rw [highCandidate_physical_length]
  push_cast
  have hbits : (productBits n 1 : ℝ) ≤ ProductPrograms.logWidth n := by
    exact_mod_cast ProductPrograms.productBits_le_logWidth n
  have hq := QH_envelope hn
  calc
    _ ≤ 12 * (ProductPrograms.logWidth n : ℝ) *
        (50000000000 * Real.sqrt (n : ℝ) * (ProductPrograms.logWidth n : ℝ) ^ 3) := by gcongr
    _ = _ := by ring

end Physical

#print axioms highCandidate
#print axioms highCandidate_small
#print axioms highCandidate_cost
#print axioms highCandidate_cost_envelope
#print axioms centerStage_eval_valid
#print axioms highCandidate_eval_honest
#print axioms highCandidate_sound
#print axioms weightedFinish_success
#print axioms highCandidate_minimum_mass_of_lt_one
#print axioms highCandidate_minimum_mass_of_probability_one
#print axioms highCandidate_minimum_mass
#print axioms highCandidate_success
#print axioms highCandidate_physical_length
#print axioms highCandidate_physical_normalized
#print axioms highCandidate_physical_event_law
#print axioms highCandidate_physical_success
#print axioms highCandidate_physical_envelope

end
end CutQueryComplexity.StarContraction2022.Quantum.UniformStars
