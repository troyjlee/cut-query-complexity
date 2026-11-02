import QuantumQueryComplexity.Quantum.Amplitude.Fourier
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Nat.Log

/-! # Exact product Fourier decoding and binary reconstruction

The only quantum transform used here is a tensor product of the existing
normalized finite Fourier matrix. Its columns are exact integer phase ramps,
so the inverse transform recovers the encoded vector with no approximation.
All matrices and bit masks are public. This file makes no query-cost claim.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum

noncomputable section

open QuantumQueryComplexity
open scoped Matrix
open Matrix

section Tensor

variable {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

/-- Tensor a single-register matrix over an arbitrary finite set of registers. -/
def tensorMatrix (U : Matrix J J ℂ) : Matrix (ι → J) (ι → J) ℂ :=
  fun x y => ∏ i, U (x i) (y i)

/-- The tensor construction preserves unitarity, including an empty register set. -/
theorem tensorMatrix_mem_unitaryGroup {U : Matrix J J ℂ}
    (hU : U ∈ Matrix.unitaryGroup J ℂ) :
    tensorMatrix (ι := ι) U ∈ Matrix.unitaryGroup (ι → J) ℂ := by
  classical
  have hcol (a b : J) : (∑ c, star (U c a) * U c b) = if a = b then 1 else 0 := by
    have h := congrArg (fun M : Matrix J J ℂ => M a b)
      (conjTranspose_mul_self_of_unitary hU)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tensorMatrix, star_prod,
    ← Finset.prod_mul_distrib]
  change (∑ z : ι → J, ∏ i : ι, star (U (z i) (x i)) * U (z i) (y i)) =
    (1 : Matrix (ι → J) (ι → J) ℂ) x y
  rw [← Fintype.prod_sum (fun (i : ι) (c : J) => star (U c (x i)) * U c (y i))]
  simp_rw [hcol]
  by_cases hxy : x = y
  · subst y
    simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i :=
      not_forall.mp (fun h => hxy (funext h))
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), Matrix.one_apply_ne hxy]

end Tensor

section Diagonal

variable {H : Type} [Fintype H] [DecidableEq H]

/-- A public real phase table gives an exactly unitary diagonal operator. -/
def phaseMatrix (phase : H → ℝ) : Matrix H H ℂ :=
  Matrix.diagonal (fun p => cexp1 (phase p))

theorem phaseMatrix_mem_unitaryGroup (phase : H → ℝ) :
    phaseMatrix phase ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, phaseMatrix,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hphase : (fun p => star (cexp1 (phase p)) * cexp1 (phase p)) =
      (fun _ : H => (1 : ℂ)) := by
    funext p
    rw [star_cexp1, ← cexp1_add, neg_add_cancel, cexp1_zero]
  change Matrix.diagonal (fun p => star (cexp1 (phase p)) * cexp1 (phase p)) = 1
  rw [hphase]
  exact Matrix.diagonal_one

theorem phaseMatrix_mulVec (phase : H → ℝ) (ψ : H → ℂ) :
    phaseMatrix phase *ᵥ ψ = fun p => cexp1 (phase p) * ψ p := by
  ext p
  simp [phaseMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- The matrix column is the image of its computational basis vector. -/
theorem matrix_mulVec_qBasis (U : Matrix H H ℂ) (p : H) :
    U *ᵥ qBasis p = fun h => U h p := by
  ext h
  simp [Matrix.mulVec, dotProduct, qBasis_apply]

end Diagonal

section ProductFourier

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coordinatewise finite Fourier transform. -/
def productFourier (K : ℕ) : Matrix (ι → Fin K) (ι → Fin K) ℂ :=
  tensorMatrix (fourierMat K)

theorem productFourier_mem_unitaryGroup {K : ℕ} (hK : 0 < K) :
    productFourier (ι := ι) K ∈ Matrix.unitaryGroup (ι → Fin K) ℂ :=
  tensorMatrix_mem_unitaryGroup (fourierMat_mem_unitaryGroup hK)

/-- The common amplitude of the product Fourier zero column. -/
def productUniform (ι : Type) [Fintype ι] (K : ℕ) : ℂ :=
  ∏ _i : ι, (((Real.sqrt K)⁻¹ : ℝ) : ℂ)

/-- The exact integer-vector character, in the positive Fourier convention. -/
def productPhase {K : ℕ} (x y : ι → Fin K) : ℂ :=
  cexp1 (∑ i, ((y i).val : ℝ) * ((x i).val : ℝ) / (K : ℝ))

theorem cexp1_sum {α : Type} (s : Finset α) (f : α → ℝ) :
    cexp1 (∑ i ∈ s, f i) = ∏ i ∈ s, cexp1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, Finset.prod_insert hi, ih, cexp1_add]

theorem productFourier_column {K : ℕ} (x y : ι → Fin K) :
    productFourier K y x = productUniform ι K * productPhase x y := by
  simp only [productFourier, tensorMatrix, fourierMat_apply, productUniform,
    productPhase, cexp1_sum, Finset.prod_mul_distrib]

theorem productFourier_zero {K : ℕ} (hK : 0 < K) (y : ι → Fin K) :
    productFourier K y (fun _ => ⟨0, hK⟩) = productUniform ι K := by
  rw [productFourier_column]
  simp [productPhase]

/-- Exact inverse decoding of every integer-vector ramp. -/
theorem productFourier_decode {K : ℕ} (hK : 0 < K) (x : ι → Fin K) :
    (productFourier K)ᴴ *ᵥ (fun y => productUniform ι K * productPhase x y) =
      qBasis x := by
  have hcolumn : (fun y => productUniform ι K * productPhase x y) =
      productFourier K *ᵥ qBasis x := by
    rw [matrix_mulVec_qBasis]
    funext y
    exact (productFourier_column x y).symm
  rw [hcolumn, Matrix.mulVec_mulVec,
    conjTranspose_mul_self_of_unitary (productFourier_mem_unitaryGroup hK),
    Matrix.one_mulVec]

/-- The complete zero-query Fourier/phase/inverse identity, used after the
actual oracle circuit has implemented the diagonal phase. -/
theorem productFourier_phase_decode {K : ℕ} (hK : 0 < K) (x : ι → Fin K) :
    (productFourier K)ᴴ *ᵥ
      (phaseMatrix (fun y : ι → Fin K =>
          ∑ i, ((y i).val : ℝ) * ((x i).val : ℝ) / (K : ℝ)) *ᵥ
        (productFourier K *ᵥ qBasis (fun _ => ⟨0, hK⟩))) = qBasis x := by
  rw [matrix_mulVec_qBasis, phaseMatrix_mulVec]
  have hphase : (fun p : ι → Fin K =>
      cexp1 (∑ i, ((p i).val : ℝ) * ((x i).val : ℝ) / (K : ℝ)) *
        productFourier K p (fun _ => ⟨0, hK⟩)) =
      (fun p => productUniform ι K * productPhase x p) := by
    funext p
    rw [productFourier_zero hK]
    exact mul_comm _ _
  rw [hphase]
  exact productFourier_decode hK x

end ProductFourier

section Binary

/-- A binary digit defined arithmetically, with no implementation-dependent bits. -/
def binaryDigit (x b : ℕ) : ℕ := (x / 2 ^ b) % 2

theorem binaryDigit_lt_two (x b : ℕ) : binaryDigit x b < 2 :=
  Nat.mod_lt _ (by decide)

theorem binaryDigit_eq_zero_or_one (x b : ℕ) :
    binaryDigit x b = 0 ∨ binaryDigit x b = 1 := by
  have := binaryDigit_lt_two x b
  omega

theorem binaryDigit_eq_indicator (x b : ℕ) :
    binaryDigit x b = if binaryDigit x b = 1 then 1 else 0 := by
  rcases binaryDigit_eq_zero_or_one x b with h | h <;> simp [h]

/-- Exact truncation: the first B digits reconstruct the residue modulo 2^B. -/
theorem sum_binaryDigits (x B : ℕ) :
    ∑ b ∈ Finset.range B, 2 ^ b * binaryDigit x b = x % 2 ^ B := by
  induction B with
  | zero => simp [Nat.mod_one]
  | succ B ih =>
      rw [Finset.sum_range_succ, ih]
      exact Nat.mod_pow_succ.symm

theorem sum_binaryDigits_eq {x B : ℕ} (hx : x < 2 ^ B) :
    ∑ b ∈ Finset.range B, 2 ^ b * binaryDigit x b = x := by
  rw [sum_binaryDigits, Nat.mod_eq_of_lt hx]

/-- Number of exact binary phases sufficient for all bounded row sums. -/
def productBits (n W : ℕ) : ℕ := Nat.clog 2 (W * n + 1)

def productModulus (n W : ℕ) : ℕ := 2 ^ productBits n W

theorem productModulus_pos (n W : ℕ) : 0 < productModulus n W := by
  exact pow_pos (by decide) _

theorem rowBound_lt_productModulus (n W : ℕ) : W * n < productModulus n W := by
  exact (Nat.lt_succ_self (W * n)).trans_le (Nat.le_pow_clog (by decide) (W * n + 1))

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The public shore selected by one bit of a Fourier index. -/
def bitShore {K : ℕ} (y : ι → Fin K) (b : ℕ) : Finset ι :=
  Finset.univ.filter (fun v => binaryDigit (y v).val b = 1)

@[simp] theorem mem_bitShore {K : ℕ} (y : ι → Fin K) (b : ℕ) (v : ι) :
    v ∈ bitShore y b ↔ binaryDigit (y v).val b = 1 := by
  simp [bitShore]

/-- Bit-shore sums reconstruct the full real dot product exactly. -/
theorem bitShore_dot {B : ℕ} (y : ι → Fin (2 ^ B)) (x : ι → ℝ) :
    (∑ b ∈ Finset.range B, (2 : ℝ) ^ b * ∑ v ∈ bitShore y b, x v) =
      ∑ v, ((y v).val : ℝ) * x v := by
  have hbit (b : ℕ) : (∑ v ∈ bitShore y b, x v) =
      ∑ v, (binaryDigit (y v).val b : ℝ) * x v := by
    simp only [bitShore, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    rcases binaryDigit_eq_zero_or_one (y v).val b with h | h <;> simp [h]
  simp_rw [hbit, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  exact_mod_cast sum_binaryDigits_eq (y v).isLt

end Binary

#print axioms tensorMatrix_mem_unitaryGroup
#print axioms phaseMatrix_mem_unitaryGroup
#print axioms productFourier_mem_unitaryGroup
#print axioms productFourier_decode
#print axioms productFourier_phase_decode
#print axioms sum_binaryDigits_eq
#print axioms rowBound_lt_productModulus
#print axioms bitShore_dot

end

end CutQueryComplexity.StarContraction2022.Quantum
