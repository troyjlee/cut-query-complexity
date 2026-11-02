import CutQueryComplexity.ImplicitLP.FrozenSolve

/-! # Preconditioned refinement with rounding errors (D7 item 5)

`frozen_solve` assumes exact products with the frozen normal matrix. An implementation from
public aggregates computes each Richardson step only approximately. Write `‖x‖_L = √(xᵀLx)`.
If every computed step lands within `τ` of the exact step in `‖·‖_L`, then
`‖xₖ − x*‖_L ≤ 2⁻ᵏ‖x*‖_L + 2τ` (`frozen_solve_inexact`). The bound is additive, so it covers
`b = 0` and arbitrarily small right-hand sides: then `x* = 0` and the error is at most `2τ`.

* `enorm_add_le`: the triangle inequality for `‖·‖_L` when `L` is symmetric positive
  semidefinite, from `polar_cs`.
* `richardson_inexact`: a step map contracting `‖· − x*‖_L` by `1/2`, perturbed by at most `τ`
  per step, gives error `2⁻ᵏ e₀ + 2τ(1 − 2⁻ᵏ)`.
* `enorm_le_of_coord`: a coordinatewise error `δ` has `‖d‖_L ≤ √Λ √r δ` whenever
  `xᵀLx ≤ Λ‖x‖²`. This converts per-coordinate rounding into the `τ` above.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Spectral

noncomputable section

variable {r n : ℕ}

/-- The energy norm `‖x‖_L = √(xᵀLx)`. -/
def enorm (L : Matrix (Fin r) (Fin r) ℝ) (x : Fin r → ℝ) : ℝ := Real.sqrt (x ⬝ᵥ (L *ᵥ x))

theorem enorm_nonneg (L : Matrix (Fin r) (Fin r) ℝ) (x : Fin r → ℝ) : 0 ≤ enorm L x :=
  Real.sqrt_nonneg _

theorem enorm_sq {L : Matrix (Fin r) (Fin r) ℝ} (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (L *ᵥ x))
    (x : Fin r → ℝ) : enorm L x ^ 2 = x ⬝ᵥ (L *ᵥ x) :=
  Real.sq_sqrt (hpsd x)

theorem enorm_neg (L : Matrix (Fin r) (Fin r) ℝ) (x : Fin r → ℝ) : enorm L (-x) = enorm L x := by
  simp [enorm, mulVec_neg]

/-- **Triangle inequality** for the energy norm of a symmetric positive semidefinite `L`. -/
theorem enorm_add_le {L : Matrix (Fin r) (Fin r) ℝ} (hL : Lᵀ = L)
    (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (L *ᵥ x)) (x y : Fin r → ℝ) :
    enorm L (x + y) ≤ enorm L x + enorm L y := by
  have hcs := polar_cs hL hL one_pos (fun z => by rw [one_mul, abs_of_nonneg (hpsd z)]) x y
  rw [one_pow, one_mul, ← enorm_sq hpsd x, ← enorm_sq hpsd y, ← mul_pow] at hcs
  have hxy : x ⬝ᵥ (L *ᵥ y) ≤ enorm L x * enorm L y :=
    le_of_abs_le (abs_le_of_sq_le_sq' hcs
      (mul_nonneg (enorm_nonneg L x) (enorm_nonneg L y)) |> abs_le.mpr)
  have hsym : y ⬝ᵥ (L *ᵥ x) = x ⬝ᵥ (L *ᵥ y) := dot_mulVec_comm hL y x
  have hexp : (x + y) ⬝ᵥ (L *ᵥ (x + y)) =
      x ⬝ᵥ (L *ᵥ x) + 2 * (x ⬝ᵥ (L *ᵥ y)) + y ⬝ᵥ (L *ᵥ y) := by
    simp only [mulVec_add, dotProduct_add, add_dotProduct]; rw [hsym]; ring
  rw [enorm, Real.sqrt_le_left (add_nonneg (enorm_nonneg L x) (enorm_nonneg L y)), hexp,
    ← enorm_sq hpsd x, ← enorm_sq hpsd y]
  nlinarith

/-- **Inexact refinement.** If `step` contracts the distance to `xs` by `1/2` in `‖·‖_L`, and
each computed iterate `x (j+1)` is within `τ` of `step (x j)`, the error after `k` steps is at
most `2⁻ᵏ e₀ + 2τ(1 − 2⁻ᵏ)`. -/
theorem richardson_inexact {L : Matrix (Fin r) (Fin r) ℝ} (hL : Lᵀ = L)
    (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (L *ᵥ x)) {step : (Fin r → ℝ) → Fin r → ℝ} {xs : Fin r → ℝ}
    (hc : ∀ x, enorm L (step x - xs) ≤ 1 / 2 * enorm L (x - xs)) (x : ℕ → Fin r → ℝ)
    {τ : ℝ} (herr : ∀ j, enorm L (x (j + 1) - step (x j)) ≤ τ) (k : ℕ) :
    enorm L (x k - xs) ≤ (1 / 2) ^ k * enorm L (x 0 - xs) + 2 * τ * (1 - (1 / 2) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsplit : x (k + 1) - xs = (x (k + 1) - step (x k)) + (step (x k) - xs) := by abel
      calc enorm L (x (k + 1) - xs)
          ≤ enorm L (x (k + 1) - step (x k)) + enorm L (step (x k) - xs) := by
            rw [hsplit]; exact enorm_add_le hL hpsd _ _
        _ ≤ τ + 1 / 2 * enorm L (x k - xs) := add_le_add (herr k) (hc (x k))
        _ ≤ τ + 1 / 2 * ((1 / 2) ^ k * enorm L (x 0 - xs) + 2 * τ * (1 - (1 / 2) ^ k)) := by
            linarith
        _ = (1 / 2) ^ (k + 1) * enorm L (x 0 - xs) + 2 * τ * (1 - (1 / 2) ^ (k + 1)) := by
            ring

/-- A coordinatewise error of size `δ` has energy norm at most `√Λ √r δ` when the form of `L`
is bounded by `Λ‖x‖²`. -/
theorem enorm_le_of_coord {L : Matrix (Fin r) (Fin r) ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hup : ∀ x, x ⬝ᵥ (L *ᵥ x) ≤ Λ * euc x ^ 2) {d : Fin r → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ i, |d i| ≤ δ) : enorm L d ≤ Real.sqrt Λ * (Real.sqrt r * δ) := by
  have h1 : euc d ≤ Real.sqrt r * δ := euc_le_sqrt_card_mul hδ hd
  rw [enorm, ← Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg Λ)
    (mul_nonneg (Real.sqrt_nonneg _) hδ)), mul_pow, Real.sq_sqrt hΛ]
  refine Real.sqrt_le_sqrt ((hup d).trans (mul_le_mul_of_nonneg_left ?_ hΛ))
  exact pow_le_pow_left₀ (euc_nonneg d) h1 2

/-- **The frozen normal solve with rounding errors.** In the setting of `frozen_solve`, let
`x : ℕ → ℝʳ` start at `0`, and suppose each computed iterate is within `τ` (in `‖·‖_L`) of the
exact preconditioned Richardson step from the previous one. Then
`‖xₖ − x*‖_L ≤ 2⁻ᵏ‖x*‖_L + 2τ`. -/
theorem frozen_solve_inexact {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ} {K t R : ℕ} {δ ε : ℝ}
    {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G w K t δ R out) (hw0 : ∀ e, 0 ≤ w e)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    (Pz : Matrix (Fin n) (Fin r) ℝ) {E : Matrix (Fin r) (Fin r) ℝ} (hEs : Eᵀ = E)
    {dmin : ℝ} (hdmin : 0 < dmin) (hE : ∀ x, dmin * euc x ^ 2 ≤ x ⬝ᵥ (E *ᵥ x))
    (b xs : Fin r → ℝ)
    (hxs : (pullLap Pz (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) + E)
      *ᵥ xs = b)
    (x : ℕ → Fin r → ℝ) (hx0 : x 0 = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    let L := pullLap Pz (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) + E
    let P := pullLap Pz out univ + E
    let step : (Fin r → ℝ) → Fin r → ℝ := fun y => y + P⁻¹ *ᵥ (b - L *ᵥ y)
    (∀ j, enorm L (x (j + 1) - step (x j)) ≤ τ) →
    ∀ k, enorm L (x k - xs) ≤ (1 / 2) ^ k * enorm L xs + 2 * τ := by
  intro L P step herr k
  have hxsL : L *ᵥ xs = b := hxs
  have hE0 : ∀ y, 0 ≤ y ⬝ᵥ (E *ᵥ y) := fun y =>
    (mul_nonneg hdmin.le (sq_nonneg _)).trans (hE y)
  have hbd := frozen_precond hgood hw0 hε0.le (by linarith) hδlo hδhi Pz hE0
  have hPpos : ∀ y, y ≠ 0 → 0 < y ⬝ᵥ (P *ᵥ y) := fun y hy => by
    have h1 : 0 ≤ y ⬝ᵥ (pullLap Pz out univ *ᵥ y) := by
      rw [quad_pullLap]; exact energy_nonneg hgood.2.1 _ _
    have h3 : 0 < dmin * euc y ^ 2 := mul_pos hdmin (pow_pos (euc_pos_of_ne_zero hy) 2)
    simp only [P, add_mulVec, dotProduct_add]
    linarith [hE y]
  have hPdet : P.det ≠ 0 := det_ne_zero_of_quad_pos hPpos
  have hLs : Lᵀ = L := by simp [L, transpose_add, pullLap_symm, hEs]
  have hPs : Pᵀ = P := by simp [P, transpose_add, pullLap_symm, hEs]
  have hpsd : ∀ y, 0 ≤ y ⬝ᵥ (L *ᵥ y) := fun y => by
    simp only [L, add_mulVec, dotProduct_add]
    rw [quad_pullLap]
    exact add_nonneg (energy_nonneg (fun e => by
      simp only [Sparsify.omegaR, Sparsify.cR, pow_zero, one_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (hw0 e)) _ _) (hE0 y)
  -- the exact step halves the energy-norm error
  have hc0 : 0 ≤ (2 * ε) ^ 2 * (1 + 2 * ε) / (1 - 2 * ε) :=
    div_nonneg (by positivity) (by linarith)
  have hc : (2 * ε) ^ 2 * (1 + 2 * ε) / (1 - 2 * ε) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hcon : ∀ y, enorm L (step y - xs) ≤ 1 / 2 * enorm L (y - xs) := fun y => by
    have hstep := richardson_step hLs hPs hPdet (ε := 2 * ε) (by linarith) (by linarith)
      (fun z => (hbd z).1) (fun z => (hbd z).2) (y - xs)
    simp only at hstep
    have he : step y - xs = (y - xs) - P⁻¹ *ᵥ (L *ᵥ (y - xs)) := by
      simp only [step, mulVec_sub, hxsL]; abel
    have hq : (step y - xs) ⬝ᵥ (L *ᵥ (step y - xs)) ≤ 1 / 4 * ((y - xs) ⬝ᵥ (L *ᵥ (y - xs))) := by
      rw [he]; exact hstep.trans (mul_le_mul_of_nonneg_right hc (hpsd _))
    have hhalf : (1 / 2 : ℝ) * enorm L (y - xs) = Real.sqrt (1 / 4 * ((y - xs) ⬝ᵥ (L *ᵥ (y - xs)))) := by
      rw [Real.sqrt_mul (by norm_num), enorm, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [hhalf, enorm]
    exact Real.sqrt_le_sqrt hq
  have hit := richardson_inexact hLs hpsd hcon x herr k
  rw [hx0, zero_sub, enorm_neg] at hit
  have hτk : 2 * τ * (1 - (1 / 2 : ℝ) ^ k) ≤ 2 * τ := by
    have : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
    nlinarith
  linarith

end

end ImplicitLP
end CutQueryComplexity
