import CutQueryComplexity.DirectedUnitST.Preparation.Height
import CutQueryComplexity.DirectedUnitST.Preparation.Budget

/-! # The algebraic completion interface for a prepared repair instance

A successful operational repair must restore the measured original divergence.
Equal opposite-pair totals then imply equality of every cut.  This algebraic
statement does not claim to implement the operational flow algorithm.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Preparation

open Finset Certificate DirectedCertificate

theorem out_eq_of_pair_sum_of_capacityDiv {V : Type*} [Fintype V] [DecidableEq V]
    (G H : WeightedDiGraph V)
    (htot : ∀ u v, G.c u v + G.c v u = H.c u v + H.c v u)
    (hdiv : ∀ v, Repair.capacityDiv G v = Repair.capacityDiv H v) (S : Finset V) :
    G.out S = H.out S := by
  have hf := Repair.comparison_feasible G H htot
  have hnet (v : V) : netOut (fun u w => G.c u w - H.c u w) v = 0 := by
    rw [Repair.comparison_divergence G H htot v, hdiv v, sub_self, zero_div]
  have hs : (∑ v ∈ S, netOut (fun u w => G.c u w - H.c u w) v) = 0 := by
    simp only [hnet, sum_const_zero]
  rw [sum_netOut_eq hf.1] at hs
  have he : (∑ u ∈ S, ∑ v ∈ Sᶜ, (G.c u v - H.c u v)) = G.out S - H.out S := by
    simp only [WeightedDiGraph.out, sum_sub_distrib]
  rw [he] at hs
  exact sub_eq_zero.mp hs

/-- The operational layer need only provide a feasible flow with the public
half-divergence discrepancy. Subtracting it restores every original cut. -/
theorem repair_restores_cuts {V : Type*} [Fintype V] [DecidableEq V]
    (G H : WeightedDiGraph V)
    (htot : ∀ u v, H.c u v + H.c v u = G.c u v + G.c v u)
    (f : V → V → ℝ) (hf : H.Feasible f)
    (hdiv : ∀ v, netOut f v = (Repair.capacityDiv H v - Repair.capacityDiv G v) / 2)
    (S : Finset V) : (Repair.residual H f hf).out S = G.out S := by
  apply out_eq_of_pair_sum_of_capacityDiv
  · intro u v
    rw [Repair.residual_pair_sum]
    exact htot u v
  · intro v
    rw [Repair.residual_capacityDiv, hdiv]
    ring

/-- The full public preparation program, including measured singleton cuts and
learned-only rounding, at an executable cubic scale. -/
noncomputable def fiveThirdsIntegralProg (n : ℕ) :
    DTree (Finset (Fin n)) ℕ (Output n) (queryBudget n (cubicScale n)) :=
  integralPreparationProg (cubicScale_pos n)

theorem fiveThirdsIntegralProg_cost {n : ℕ} (hn : 2 ≤ n) (read : Finset (Fin n) → ℕ) :
    ((fiveThirdsIntegralProg n).cost read : ℝ) ≤
      256 * (n : ℝ) ^ (5 / 3 : ℝ) * ((Acceleration.scheduleBits n : ℝ) + 1) ^ 2 := by
  rw [fiveThirdsIntegralProg, integralPreparationProg_cost]
  exact fiveThirdsProg_cost hn read

theorem integralPreparation_volume_four_thirds {n : ℕ} (G : DiGraph (Fin n))
    (hG : G.Simple) (hn : 2 ≤ n) :
    Repair.supply (repairDemand (cubicScale n) ((preparationProg (cubicScale_pos n)).eval G.out)) ≤
      24 * (n : ℝ) ^ (4 / 3 : ℝ) := by
  have hv := integralPreparation_height G hG hn (cubicScale_pos n)
  have hs := cubicScale_sqrt_le (show 1 ≤ n by omega)
  have hm : 10 * (n : ℝ) * Real.sqrt (cubicScale n) ≤ 20 * (n : ℝ) ^ (4 / 3 : ℝ) := by
    calc
      _ ≤ 10 * (n : ℝ) * (2 * (n : ℝ) ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 20 * ((n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ = _ := by rw [n_mul_cuberoot (show 0 < n by omega)]
  linarith

/-- The honest preparation output has the scale needed by the operational
repair's `n * sqrt R` accounting. This does not assume any run-cost theorem. -/
theorem integralPreparation_repair_scale {n : ℕ} (G : DiGraph (Fin n))
    (hG : G.Simple) (hn : 2 ≤ n) :
    (n : ℝ) * Real.sqrt (Repair.supply
      (repairDemand (cubicScale n) ((preparationProg (cubicScale_pos n)).eval G.out))) ≤
        5 * (n : ℝ) ^ (5 / 3 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hv := integralPreparation_volume_four_thirds G hG hn
  have hp : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = (n : ℝ) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    norm_num
  have hs : Real.sqrt (Repair.supply
      (repairDemand (cubicScale n) ((preparationProg (cubicScale_pos n)).eval G.out))) ≤
        5 * (n : ℝ) ^ (2 / 3 : ℝ) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow, hp]
    norm_num
    nlinarith only [hv, Real.rpow_nonneg (Nat.cast_nonneg n) (4 / 3 : ℝ)]
  have he : (n : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (5 / 3 : ℝ) := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + 2 / 3) := (Real.rpow_add hnpos _ _).symm
      _ = _ := by norm_num
  calc
    _ ≤ (n : ℝ) * (5 * (n : ℝ) ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)
    _ = 5 * ((n : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) := by ring
    _ = _ := by rw [he]

/-- Correctness relation for the public output and its hidden integral realization.
All fields are proved by the preparation program below. `H` is a mathematical
witness; no executable operation receives it or its hidden capacities. -/
structure PreparationSpec {n : ℕ} (G : DiGraph (Fin n))
    (H : WeightedDiGraph (Fin n)) (out : Output n) : Prop where
  realizes : out.state.Realizes (realGraph G) H
  pair_totals : ∀ i j, H.c i j + H.c j i = (realGraph G).c i j + (realGraph G).c j i
  integral : ∀ i j, ∃ m : ℕ, H.c i j = m
  pairBounded : Repair.PairBounded H
  divergence : ∀ i, out.demand i = (Repair.capacityDiv H i - Repair.capacityDiv (realGraph G) i) / 2
  demand_integer : ∀ i, Repair.IntegerValue (out.demand i)
  demand_zero : ∑ i, out.demand i = 0
  feasible : ∃ f : Fin n → Fin n → ℝ, H.Feasible f ∧ ∀ i, netOut f i = out.demand i
  volume : Repair.supply out.demand ≤ 24 * (n : ℝ) ^ (4 / 3 : ℝ)
  coarse_volume : Repair.supply out.demand ≤ (n : ℝ) ^ 2 / 2
  potential_zero : ∑ i, out.data.potential i = 0
  rise : ∀ i j, 0 < H.c i j → (out.data.potential j : ℝ) - out.data.potential i ≤ 2
  learned_bound : out.state.known.card ≤ 2 * SparseBand.bandBudget n (cubicScale n)

/-- Unconditional preparation theorem for every simple directed input.
It constructs the public residual-search state and an integral, routable,
small-volume repair instance; operational flow is the next layer. -/
theorem fiveThirdsIntegralProg_correct {n : ℕ} (G : DiGraph (Fin n))
    (hG : G.Simple) (hn : 2 ≤ n) :
    ∃ H : WeightedDiGraph (Fin n), PreparationSpec G H ((fiveThirdsIntegralProg n).eval G.out) := by
  simp only [fiveThirdsIntegralProg, integralPreparationProg_eval]
  refine ⟨realizedRounded G (cubicScale_pos n), ?_⟩
  exact
    { realizes := roundedState_realizes G (cubicScale_pos n)
      pair_totals := realizedRounded_pair_sum G (cubicScale_pos n)
      integral := realizedRounded_natural G (cubicScale_pos n)
      pairBounded := realizedRounded_pairBounded G hG (cubicScale_pos n)
      divergence := repairDemand_eq G (cubicScale_pos n)
      demand_integer := repairDemand_integer G (cubicScale_pos n)
      demand_zero := repairDemand_sum_zero G (cubicScale_pos n)
      feasible := repairDemand_feasible G (cubicScale_pos n)
      volume := integralPreparation_volume_four_thirds G hG hn
      coarse_volume := integralPreparation_supply_le_half_sq G hG (cubicScale_pos n)
      potential_zero := (preparationProg_mean_zero G (cubicScale_pos n)).1
      rise := realizedRounded_rise G (cubicScale_pos n)
      learned_bound := roundedState_known_card (cubicScale_pos n) _ }

/-- Any operational repair satisfying the prepared public demand restores all
original outgoing cuts. No cut-equivalence premise is required. -/
theorem PreparationSpec.restores_cuts {n : ℕ} {G : DiGraph (Fin n)}
    {H : WeightedDiGraph (Fin n)} {out : Output n} (h : PreparationSpec G H out)
    (f : Fin n → Fin n → ℝ) (hf : H.Feasible f) (hnet : ∀ i, netOut f i = out.demand i)
    (S : Finset (Fin n)) : (Repair.residual H f hf).out S = (G.out S : ℝ) := by
  rw [← realGraph_out]
  exact repair_restores_cuts (realGraph G) H h.pair_totals f hf
    (fun i => (hnet i).trans (h.divergence i)) S

#print axioms out_eq_of_pair_sum_of_capacityDiv
#print axioms repair_restores_cuts
#print axioms fiveThirdsIntegralProg_cost
#print axioms integralPreparation_volume_four_thirds
#print axioms integralPreparation_repair_scale
#print axioms fiveThirdsIntegralProg_correct
#print axioms PreparationSpec.restores_cuts

end CutQueryComplexity.DirectedUnitST.Preparation
