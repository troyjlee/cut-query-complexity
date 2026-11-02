import CutQueryComplexity.DirectedUnitST.Acceleration.Oracle
import CutQueryComplexity.DirectedUnitST.SparseBand.Certificate
import CutQueryComplexity.DirectedUnitST.Repair.Basic

/-! # Canonical capacities realized by a public quantized potential

`representation` is a hidden mathematical realization, never an input to the
public program.  Its forward capacity is `u*(1+h/Q)/2`; the reverse capacity is
the complementary part of the same integer pair total.  Outside the public
fractional mask both capacities are integral.  No rounding theorem is assumed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Preparation

open Finset Acceleration DirectedCertificate

/-- The original natural capacities, viewed over the reals. -/
def realGraph {n : ℕ} (G : DiGraph (Fin n)) : WeightedDiGraph (Fin n) where
  c i j := G.c i j
  nonneg i j := Nat.cast_nonneg _
  diag i := by simp [G.diag]

@[simp] theorem realGraph_c {n : ℕ} (G : DiGraph (Fin n)) (i j : Fin n) :
    (realGraph G).c i j = (G.c i j : ℝ) := rfl

theorem realGraph_out {n : ℕ} (G : DiGraph (Fin n)) (S : Finset (Fin n)) :
    (realGraph G).out S = (G.out S : ℝ) := by
  simp [WeightedDiGraph.out, DiGraph.out, DiGraph.arcs, realGraph]

theorem realGraph_capacityDiv {n : ℕ} (G : DiGraph (Fin n)) (i : Fin n) :
    Repair.capacityDiv (realGraph G) i = (G.outdeg i : ℝ) - G.indeg i := by
  simp [Repair.capacityDiv, realGraph, DiGraph.outdeg, DiGraph.indeg, sum_sub_distrib]

theorem signedPairs_bounds {n Q : ℕ} (h : SparseBand.Pair n → ℤ)
    (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ)) (i j : Fin n) :
    -(Q : ℤ) ≤ signedPairs h i j ∧ signedPairs h i j ≤ (Q : ℤ) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simpa [signedPairs, hij] using hb ⟨(i, j), hij⟩
  · simp
  · have hh := hb ⟨(j, i), hji⟩
    simp only [signedPairs, not_lt.mpr hji.le, hji, ↓reduceDIte]
    omega

theorem signedRatio_bounds {n Q : ℕ} (hQ : 0 < Q) (h : SparseBand.Pair n → ℤ)
    (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ)) (i j : Fin n) :
    -1 ≤ (signedPairs h i j : ℝ) / Q ∧ (signedPairs h i j : ℝ) / Q ≤ 1 := by
  have hp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hh := signedPairs_bounds h hb i j
  constructor
  · apply (le_div_iff₀ hp).mpr
    have : -(Q : ℝ) ≤ (signedPairs h i j : ℝ) := by exact_mod_cast hh.1
    linarith
  · apply (div_le_iff₀ hp).mpr
    have : (signedPairs h i j : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hh.2
    linarith

/-- Proof-only capacity realization; the program never receives `G`. -/
noncomputable def representation {n Q : ℕ} (G : DiGraph (Fin n)) (hQ : 0 < Q)
    (h : SparseBand.Pair n → ℤ) (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ)) :
    WeightedDiGraph (Fin n) where
  c i j := (G.sym i j : ℝ) * (1 + (signedPairs h i j : ℝ) / Q) / 2
  nonneg i j := by
    have hh := (signedRatio_bounds hQ h hb i j).1
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by norm_num)
  diag i := by simp

@[simp] theorem representation_c {n Q : ℕ} (G : DiGraph (Fin n)) (hQ : 0 < Q)
    (h : SparseBand.Pair n → ℤ) (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ))
    (i j : Fin n) :
    (representation G hQ h hb).c i j =
      (G.sym i j : ℝ) * (1 + (signedPairs h i j : ℝ) / Q) / 2 := rfl

theorem representation_forward {n Q : ℕ} (G : DiGraph (Fin n)) (hQ : 0 < Q)
    (h : SparseBand.Pair n → ℤ) (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ))
    (e : SparseBand.Pair n) :
    (representation G hQ h hb).c e.val.1 e.val.2 =
      (G.sym e.val.1 e.val.2 : ℝ) * (1 + (h e : ℝ) / Q) / 2 := by
  simp [representation_c, signedPairs, e.property]

theorem representation_reverse {n Q : ℕ} (G : DiGraph (Fin n)) (hQ : 0 < Q)
    (h : SparseBand.Pair n → ℤ) (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ))
    (e : SparseBand.Pair n) :
    (representation G hQ h hb).c e.val.2 e.val.1 =
      (G.sym e.val.1 e.val.2 : ℝ) * (1 - (h e : ℝ) / Q) / 2 := by
  simp [representation_c, signedPairs, e.property, not_lt.mpr e.property.le,
    G.sym_comm e.val.2 e.val.1, sub_eq_add_neg, neg_div]

theorem representation_pair_sum {n Q : ℕ} (G : DiGraph (Fin n)) (hQ : 0 < Q)
    (h : SparseBand.Pair n → ℤ) (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ))
    (i j : Fin n) :
    (representation G hQ h hb).c i j + (representation G hQ h hb).c j i = G.sym i j := by
  rw [representation_c, representation_c, signedPairs_skew, G.sym_comm j i]
  push_cast
  ring

theorem representation_pairBounded {n Q : ℕ} (G : DiGraph (Fin n)) (hG : G.Simple)
    (hQ : 0 < Q) (h : SparseBand.Pair n → ℤ)
    (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ)) :
    Repair.PairBounded (representation G hQ h hb) := by
  intro i j
  rw [representation_pair_sum]
  have : G.sym i j ≤ 2 := by have := hG i j; have := hG j i; simp only [DiGraph.sym]; omega
  exact_mod_cast this

theorem representation_capacityDiv {n Q : ℕ} (G : DiGraph (Fin n)) (hQ : 0 < Q)
    (h : SparseBand.Pair n → ℤ) (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ))
    (i : Fin n) :
    Repair.capacityDiv (representation G hQ h hb) i =
      divergence (fun e : SparseBand.Pair n => e.val.1) (fun e => e.val.2)
        (fun e => (G.sym e.val.1 e.val.2 : ℝ) * ((h e : ℝ) / Q)) i := by
  rw [Repair.capacityDiv, canonical_divergence_row]
  apply sum_congr rfl
  intro j _
  rw [representation_c, representation_c, signedPairs_skew, G.sym_comm j i]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [signedPairs, hij, not_lt.mpr hij.le, ↓reduceDIte, Int.cast_neg]
    ring
  · simp
  · simp only [signedPairs, not_lt.mpr hji.le, hji, ↓reduceDIte, Int.cast_neg,
      G.sym_comm i j]
    ring

/-- Every omitted coefficient is exactly an endpoint, with no graph premise. -/
theorem outside_mask_saturated {n Q : ℕ} (h : SparseBand.Pair n → ℤ)
    (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ)) (e : SparseBand.Pair n)
    (he : e ∉ SparseBand.coefficientMask Q h) : h e = -(Q : ℤ) ∨ h e = (Q : ℤ) := by
  have hh := hb e
  simp only [SparseBand.coefficientMask, mem_filter, mem_univ, true_and, not_and] at he
  omega

/-- Integrality outside the learned mask is proved from exact saturation. -/
theorem representation_unlearned_integer {n Q : ℕ} (G : DiGraph (Fin n)) (hQ : 0 < Q)
    (h : SparseBand.Pair n → ℤ) (hb : ∀ e, -(Q : ℤ) ≤ h e ∧ h e ≤ (Q : ℤ))
    (e : SparseBand.Pair n) (he : e ∉ SparseBand.coefficientMask Q h) :
    (∃ z : ℤ, (representation G hQ h hb).c e.val.1 e.val.2 = z) ∧
      (∃ z : ℤ, (representation G hQ h hb).c e.val.2 e.val.1 = z) := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ)
  rw [representation_forward, representation_reverse]
  rcases outside_mask_saturated h hb e he with hh | hh
  · refine ⟨⟨0, ?_⟩, ⟨(G.sym e.val.1 e.val.2 : ℤ), ?_⟩⟩ <;> norm_num [hh, hQr]
  · refine ⟨⟨(G.sym e.val.1 e.val.2 : ℤ), ?_⟩, ⟨0, ?_⟩⟩ <;> norm_num [hh, hQr]

noncomputable def potentialRepresentation {n k : ℕ} (G : DiGraph (Fin n))
    (b : ℕ) (c : SparseBand.OffsetTable n k) (r : Fin n → ℚ) : WeightedDiGraph (Fin n) :=
  representation G (by positivity : 0 < 2 ^ b)
    (publicCoefficients k b (SparseBand.offsetRat c) r)
    (publicCoefficients_bounds k b (SparseBand.offsetRat c) r)

/-- The rise bound applies to every positive realized capacity, including saturated pairs. -/
theorem potentialRepresentation_rise {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k)
    (b : ℕ) (c : SparseBand.OffsetTable n k) (r : Fin n → ℚ) (i j : Fin n)
    (hc : 0 < (potentialRepresentation G b c r).c i j) :
    (r j : ℝ) - r i ≤ 1 + 1 / (k : ℝ) := by
  let h := publicCoefficients (k : ℚ) b (SparseBand.offsetRat c) r
  have hb := publicCoefficients_bounds (k : ℚ) b (SparseBand.offsetRat c) r
  rcases lt_trichotomy i j with hij | rfl | hji
  · apply publicCoefficients_forward_rise hk b c r ⟨(i, j), hij⟩
    by_contra hh
    have he : h ⟨(i, j), hij⟩ = -((2 ^ b : ℕ) : ℤ) := by
      dsimp only [h]
      have := hb ⟨(i, j), hij⟩
      omega
    have hz : (potentialRepresentation G b c r).c i j = 0 := by
      change (representation G _ h hb).c i j = 0
      rw [representation_forward G _ h hb ⟨(i, j), hij⟩]
      simp [he]
    linarith
  · rw [(potentialRepresentation G b c r).diag] at hc
    exact False.elim (lt_irrefl _ hc)
  · apply publicCoefficients_reverse_rise hk b c r ⟨(j, i), hji⟩
    by_contra hh
    have he : h ⟨(j, i), hji⟩ = ((2 ^ b : ℕ) : ℤ) := by
      dsimp only [h]
      have := hb ⟨(j, i), hji⟩
      omega
    have hz : (potentialRepresentation G b c r).c i j = 0 := by
      change (representation G _ h hb).c i j = 0
      rw [representation_reverse G _ h hb ⟨(j, i), hji⟩]
      simp [he]
    linarith

theorem potentialRepresentation_rise_two {n k : ℕ} (G : DiGraph (Fin n)) (hk : 0 < k)
    (b : ℕ) (c : SparseBand.OffsetTable n k) (r : Fin n → ℚ) (i j : Fin n)
    (hc : 0 < (potentialRepresentation G b c r).c i j) : (r j : ℝ) - r i ≤ 2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hi : 1 / (k : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hkR
  have := potentialRepresentation_rise G hk b c r i j hc
  linarith

#print axioms representation_pair_sum
#print axioms representation_pairBounded
#print axioms representation_capacityDiv
#print axioms representation_unlearned_integer
#print axioms potentialRepresentation_rise

end CutQueryComplexity.DirectedUnitST.Preparation
