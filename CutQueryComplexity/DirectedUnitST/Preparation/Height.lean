import CutQueryComplexity.DirectedUnitST.Preparation.Rounding
import CutQueryComplexity.DirectedUnitST.Repair.Height

/-! # Height of the query-realized preparation instance

Both the initial fractional graph and the learned-only integral rounding have
small, publicly known repair demand. The correction error comes from the
checked selector itself; there is no assumed rounding or height guarantee.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Preparation

open Finset Acceleration Certificate DirectedCertificate

theorem preparation_height {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 0 < k) :
    let d := (preparationProg hk).eval G.out
    Repair.supply (fun i => ((measuredDivergence d i : ℝ) - d.beta i) / 2) ≤
      4 * (n : ℝ) ^ (4 / 3 : ℝ) +
        5 * (4 * (n : ℝ) * Real.sqrt k + n + 1 / 32) / 4 := by
  let d := (preparationProg hk).eval G.out
  have hzero : ∑ i, (d.potential i : ℝ) = 0 := by
    exact_mod_cast (preparationProg_mean_zero G hk).1
  have hpos : 0 < Fintype.card (Fin n) := by simp; omega
  have hh := Repair.representation_height (realizedBase G k d) (realGraph G)
    (realizedBase_pairBounded G hG k d) (realizedBase_pair_sum G k d)
    (fun i => (d.potential i : ℝ)) hpos hzero (realizedBase_rise G hk d)
  have hy (i : Fin n) : Repair.capacityDiv (realizedBase G k d) i =
      (measuredDivergence d i : ℝ) := preparationProg_measuredDivergence G hk i
  have hb (i : Fin n) : Repair.capacityDiv (realGraph G) i = (d.beta i : ℝ) :=
    (preparationProg_beta G hk i).symm
  have he (i : Fin n) : (measuredDivergence d i : ℝ) - d.beta i + d.potential i =
      (d.gradient i : ℝ) := by
    simp only [measuredDivergence, Rat.cast_sub, Rat.cast_add]
    ring
  simp only [hy, hb, he, Fintype.card_fin, Repair.l1] at hh
  have hg := preparationProg_l1 G hG hn hk
  change (∑ i, |(d.gradient i : ℝ)|) ≤ _ at hg
  change Repair.supply (fun i => ((measuredDivergence d i : ℝ) - d.beta i) / 2) ≤ _
  linarith

/-- An independent coarse volume bound, useful for repair initialization. -/
theorem preparation_supply_le_half_sq {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hk : 0 < k) :
    let d := (preparationProg hk).eval G.out
    Repair.supply (fun i => ((measuredDivergence d i : ℝ) - d.beta i) / 2) ≤
      (n : ℝ) ^ 2 / 2 := by
  let d := (preparationProg hk).eval G.out
  let H := realizedBase G k d
  have ht := realizedBase_pair_sum G k d
  have hf := Repair.comparison_feasible H (realGraph G) ht
  have hh := Repair.feasible_supply_le_half_sq H (realizedBase_pairBounded G hG k d)
    (fun i j => H.c i j - (realGraph G).c i j) hf
  have he (i : Fin n) :
      netOut (fun u v => H.c u v - (realGraph G).c u v) i =
        ((measuredDivergence d i : ℝ) - d.beta i) / 2 := by
    rw [Repair.comparison_divergence H (realGraph G) ht i,
      preparationProg_measuredDivergence G hk i, ← preparationProg_beta G hk i]
  have hfun : netOut (fun u v => H.c u v - (realGraph G).c u v) =
      fun i => ((measuredDivergence d i : ℝ) - d.beta i) / 2 := funext he
  simpa only [hfun, Fintype.card_fin] using hh

theorem rounded_regularized_error {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 0 < k) :
    let d := (preparationProg hk).eval G.out
    (∑ i, |roundedDivergence k d i - d.beta i + d.potential i|) ≤
      8 * (n : ℝ) * Real.sqrt k := by
  let d := (preparationProg hk).eval G.out
  have he (i : Fin n) : roundedDivergence k d i - d.beta i + d.potential i =
      (d.gradient i : ℝ) + 2 * netOut (publicCorrection k d) i := by
    simp only [roundedDivergence, measuredDivergence, Rat.cast_sub, Rat.cast_add]
    ring
  have ht : (∑ i, |roundedDivergence k d i - d.beta i + d.potential i|) ≤
      (∑ i, |(d.gradient i : ℝ)|) + ∑ i, |2 * netOut (publicCorrection k d) i| := by
    simp only [he]
    calc
      _ ≤ ∑ i, (|(d.gradient i : ℝ)| + |2 * netOut (publicCorrection k d) i|) :=
        sum_le_sum fun i _ => abs_add_le _ _
      _ = _ := sum_add_distrib
  have hg := preparationProg_l1 G hG hn hk
  change (∑ i, |(d.gradient i : ℝ)|) ≤ _ at hg
  have hc := publicCorrection_l1 k d
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 1 ≤ Real.sqrt (k : ℝ) := by simpa using Real.sqrt_le_sqrt hkR
  have hp : (n : ℝ) ≤ n * Real.sqrt (k : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) n)
  change (∑ i, |roundedDivergence k d i - d.beta i + d.potential i|) ≤ _
  linarith

/-- Rounded repair volume from the actual zero-mean potential and all-arc rise. -/
theorem integralPreparation_height {n k : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hn : 2 ≤ n) (hk : 0 < k) :
    Repair.supply (repairDemand k ((preparationProg hk).eval G.out)) ≤
      4 * (n : ℝ) ^ (4 / 3 : ℝ) + 10 * n * Real.sqrt k := by
  let d := (preparationProg hk).eval G.out
  have hzero : ∑ i, (d.potential i : ℝ) = 0 := by
    exact_mod_cast (preparationProg_mean_zero G hk).1
  have hpos : 0 < Fintype.card (Fin n) := by simp; omega
  have hh := Repair.representation_height (realizedRounded G hk) (realGraph G)
    (realizedRounded_pairBounded G hG hk) (realizedRounded_pair_sum G hk)
    (fun i => (d.potential i : ℝ)) hpos hzero (realizedRounded_rise G hk)
  have hb (i : Fin n) : Repair.capacityDiv (realGraph G) i = (d.beta i : ℝ) :=
    (preparationProg_beta G hk i).symm
  simp only [realizedRounded_capacityDiv, hb, Fintype.card_fin, Repair.l1] at hh
  change Repair.supply (fun i => (roundedDivergence k d i - d.beta i) / 2) ≤
    4 * (n : ℝ) ^ (4 / 3 : ℝ) +
      5 * (∑ i, |roundedDivergence k d i - d.beta i + d.potential i|) / 4 at hh
  have he := rounded_regularized_error G hG hn hk
  change (∑ i, |roundedDivergence k d i - d.beta i + d.potential i|) ≤ _ at he
  change Repair.supply (fun i => (roundedDivergence k d i - d.beta i) / 2) ≤ _
  linarith

theorem integralPreparation_supply_le_half_sq {n k : ℕ} (G : DiGraph (Fin n))
    (hG : G.Simple) (hk : 0 < k) :
    Repair.supply (repairDemand k ((preparationProg hk).eval G.out)) ≤ (n : ℝ) ^ 2 / 2 := by
  obtain ⟨f, hf, hdiv⟩ := repairDemand_feasible G hk
  have hh := Repair.feasible_supply_le_half_sq (realizedRounded G hk)
    (realizedRounded_pairBounded G hG hk) f hf
  have hfun : netOut f = repairDemand k ((preparationProg hk).eval G.out) := funext hdiv
  simpa only [hfun, Fintype.card_fin] using hh

#print axioms preparation_height
#print axioms preparation_supply_le_half_sq
#print axioms rounded_regularized_error
#print axioms integralPreparation_height
#print axioms integralPreparation_supply_le_half_sq

end CutQueryComplexity.DirectedUnitST.Preparation
