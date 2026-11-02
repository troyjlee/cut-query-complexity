import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.Order.Star.Real

/-! # Laplacian energy and the Loewner order (D2)

Pairs are unordered (`Sym2 V`). For a vector `x`, `pairSq x s(u,v) = (x u − x v)²`. A conductance
function `ω` on a finite support `S` has

* energy `energy ω S x = Σ_{e∈S} ω_e (x_u − x_v)²`, and
* Laplacian `lap ω S = Σ_{e∈S} ω_e a_e a_eᵀ` with `a_e = 1_u − 1_v` (`pairMat`; either orientation).

`quad_lap`: `xᵀ (lap ω S) x = energy ω S x`, for every real vector, including disconnected supports
and zero conductances. Hence the Loewner order of Laplacians is the pointwise order of energies
(`loewner_iff`), Laplacians with nonnegative conductances are positive semidefinite
(`lap_posSemidef`), and a vector has zero energy exactly when the Laplacian annihilates it
(`lap_mulVec_eq_zero_iff`). `psd_add_lower`, `psd_add_upper` add a public positive semidefinite
matrix to both sides of a spectral approximation (source `cor:psd`).
-/

namespace CutQueryComplexity
namespace Spectral

open Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `(x u − x v)²`, a function of the unordered pair. -/
def pairSq (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => (x u - x v) ^ 2, fun u v => by ring⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem pairSq_mk (x : V → ℝ) (u v : V) : pairSq x s(u, v) = (x u - x v) ^ 2 := rfl

omit [Fintype V] [DecidableEq V] in
theorem pairSq_nonneg (x : V → ℝ) (e : Sym2 V) : 0 ≤ pairSq x e := by
  induction e using Sym2.ind with | h u v => exact sq_nonneg _

/-- The oriented incidence vector `1_u − 1_v`. -/
def incVec (u v : V) : V → ℝ := Pi.single u 1 - Pi.single v 1

theorem incVec_dot (u v : V) (x : V → ℝ) : incVec u v ⬝ᵥ x = x u - x v := by
  simp [incVec, sub_dotProduct, single_dotProduct]

/-- The rank-one matrix `a_e a_eᵀ`; it does not depend on the orientation. -/
def pairMat : Sym2 V → Matrix V V ℝ :=
  Sym2.lift ⟨fun u v => vecMulVec (incVec u v) (incVec u v), fun u v => by
    ext i j
    simp only [vecMulVec_apply, incVec, Pi.sub_apply]
    ring⟩

omit [Fintype V] in
@[simp] theorem pairMat_mk (u v : V) :
    pairMat s(u, v) = vecMulVec (incVec u v) (incVec u v) := rfl

theorem quad_pairMat (e : Sym2 V) (x : V → ℝ) : x ⬝ᵥ (pairMat e *ᵥ x) = pairSq x e := by
  induction e using Sym2.ind with
  | h u v =>
      rw [pairMat_mk, dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, dotProduct_comm x,
        incVec_dot, smul_eq_mul, pairSq_mk]
      ring

omit [Fintype V] in
theorem pairMat_isHermitian (e : Sym2 V) : (pairMat e).IsHermitian := by
  induction e using Sym2.ind with
  | h u v =>
      ext i j
      simp [conjTranspose_apply, vecMulVec_apply, mul_comm]

/-- The energy of `x` for conductances `ω` on the support `S`. -/
def energy (ω : Sym2 V → ℝ) (S : Finset (Sym2 V)) (x : V → ℝ) : ℝ :=
  ∑ e ∈ S, ω e * pairSq x e

/-- The Laplacian `Σ_{e∈S} ω_e a_e a_eᵀ`. -/
def lap (ω : Sym2 V → ℝ) (S : Finset (Sym2 V)) : Matrix V V ℝ :=
  ∑ e ∈ S, ω e • pairMat e

/-- **Energy is the quadratic form of the Laplacian**, for every real vector. -/
theorem quad_lap (ω : Sym2 V → ℝ) (S : Finset (Sym2 V)) (x : V → ℝ) :
    x ⬝ᵥ (lap ω S *ᵥ x) = energy ω S x := by
  rw [lap, sum_mulVec, dotProduct_sum, energy]
  refine sum_congr rfl fun e _ => ?_
  rw [smul_mulVec, dotProduct_smul, quad_pairMat, smul_eq_mul]

omit [Fintype V] in
theorem pairMat_symm (e : Sym2 V) (i j : V) : pairMat e j i = pairMat e i j := by
  have := congrFun (congrFun (pairMat_isHermitian e) i) j
  simpa [conjTranspose_apply] using this

omit [Fintype V] in
theorem lap_isHermitian (ω : Sym2 V → ℝ) (S : Finset (Sym2 V)) : (lap ω S).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, lap, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact sum_congr rfl fun e _ => by rw [pairMat_symm]

omit [Fintype V] [DecidableEq V] in
theorem energy_nonneg {ω : Sym2 V → ℝ} (hω : ∀ e, 0 ≤ ω e) (S : Finset (Sym2 V)) (x : V → ℝ) :
    0 ≤ energy ω S x :=
  sum_nonneg fun e _ => mul_nonneg (hω e) (pairSq_nonneg x e)

omit [DecidableEq V] in
/-- The positive-semidefinite order through quadratic forms, for symmetric real matrices. -/
theorem posSemidef_iff_of_isHermitian {M : Matrix V V ℝ} (hM : M.IsHermitian) :
    M.PosSemidef ↔ ∀ x : V → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [posSemidef_iff_dotProduct_mulVec]
  simp only [star_trivial]
  exact ⟨fun h => h.2, fun h => ⟨hM, h⟩⟩

theorem lap_posSemidef {ω : Sym2 V → ℝ} (hω : ∀ e, 0 ≤ ω e) (S : Finset (Sym2 V)) :
    (lap ω S).PosSemidef := by
  rw [posSemidef_iff_of_isHermitian (lap_isHermitian ω S)]
  intro x; rw [quad_lap]; exact energy_nonneg hω S x

/-- **Loewner order of Laplacians is the pointwise order of energies.** -/
theorem loewner_iff (ω ω' : Sym2 V → ℝ) (S S' : Finset (Sym2 V)) :
    (lap ω' S' - lap ω S).PosSemidef ↔ ∀ x, energy ω S x ≤ energy ω' S' x := by
  rw [posSemidef_iff_of_isHermitian ((lap_isHermitian ω' S').sub (lap_isHermitian ω S))]
  refine forall_congr' fun x => ?_
  rw [sub_mulVec, dotProduct_sub, quad_lap, quad_lap, sub_nonneg]

/-- With nonnegative conductances, zero energy means `L x = 0`. -/
theorem lap_mulVec_eq_zero_iff {ω : Sym2 V → ℝ} (hω : ∀ e, 0 ≤ ω e) (S : Finset (Sym2 V))
    (x : V → ℝ) : lap ω S *ᵥ x = 0 ↔ energy ω S x = 0 := by
  rw [← (lap_posSemidef hω S).dotProduct_mulVec_zero_iff, star_trivial, quad_lap]

omit [Fintype V] [DecidableEq V] in
/-- **Adding a public PSD matrix, lower side** (source `cor:psd`). -/
theorem psd_add_lower {H L LQ : Matrix V V ℝ} {ε : ℝ} (hH : H.PosSemidef)
    (h : (LQ - (1 - ε) • L).PosSemidef) (hε0 : 0 ≤ ε) :
    ((H + LQ) - (1 - ε) • (H + L)).PosSemidef := by
  have e : (H + LQ) - (1 - ε) • (H + L) = (LQ - (1 - ε) • L) + ε • H := by
    rw [smul_add]; module
  rw [e]
  exact h.add (hH.smul hε0)

omit [Fintype V] [DecidableEq V] in
/-- **Adding a public PSD matrix, upper side** (source `cor:psd`). -/
theorem psd_add_upper {H L LQ : Matrix V V ℝ} {ε : ℝ} (hH : H.PosSemidef)
    (h : ((1 + ε) • L - LQ).PosSemidef) (hε0 : 0 ≤ ε) :
    ((1 + ε) • (H + L) - (H + LQ)).PosSemidef := by
  have e : (1 + ε) • (H + L) - (H + LQ) = ((1 + ε) • L - LQ) + ε • H := by
    rw [smul_add]; module
  rw [e]
  exact h.add (hH.smul hε0)

end Spectral
end CutQueryComplexity
