import CutQueryComplexity.ImplicitLP.FrozenInexact

/-! # The frozen normal matrix of the directed LP splits as `L_G + E` (D7 item 5)

In the directed LP (`DirectedMincut.LPReduction`) every hidden copy of a pair `e = {u, v}` is
a constraint row `±(1_u − 1_v)`. Copies of a pair carry identical data, so their frozen weight
is a public function `w e`. The number of copies is the hidden multiplicity `symS G e`. The
remaining rows (`q`, `y⁺`, `y⁻`) are explicit. Record which rows are hidden by
`hid : Fin M → Option (Sym2 (Fin n))`. Then
`AᵀDA = lap(omegaR G w 0) + E` (`gram_split`). The first term is exactly the Laplacian whose
energy is D4's input energy `E₀ G w`, and `E` is the explicit part. When the explicit rows
contain the `+I_r` block, `E ⪰ d_min I` (`explicitGram_ge`).

So the frozen solve of `frozen_solve` and `frozen_solve_inexact` is the LP's own frozen normal
system `gram A D` (`lp_frozen_solve`, `lp_frozen_solve_inexact`), with preconditioner
`lap out + E` built from D4's output and the explicit rows. `direction_error_abs` takes the
additive energy bound of the rounded solve, and `lp_direction_error` composes everything: the
LP's Newton direction computed from D4's output with per-step rounding is within `P₁β` of the
exact direction in every coordinate.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Spectral

noncomputable section

variable {M n : ℕ}

/-- `AᵀDA` as a sum of weighted rank-one row terms. -/
theorem gram_eq_sum (A : Matrix (Fin M) (Fin n) ℝ) (D : Fin M → ℝ) :
    gram A D = ∑ i, D i • vecMulVec (A i) (A i) := by
  ext j k
  simp only [gram, Matrix.mul_apply, transpose_apply, diagonal_apply, Matrix.sum_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, mul_ite, mul_zero, sum_ite_eq',
    mem_univ, ite_true]
  exact sum_congr rfl fun i _ => by ring

/-- The explicit part `E = Σ_{explicit rows} D_i a_i a_iᵀ`. -/
def explicitGram (A : Matrix (Fin M) (Fin n) ℝ) (D : Fin M → ℝ)
    (hid : Fin M → Option (Sym2 (Fin n))) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ univ.filter (fun i => hid i = none), D i • vecMulVec (A i) (A i)

theorem explicitGram_symm (A : Matrix (Fin M) (Fin n) ℝ) (D : Fin M → ℝ)
    (hid : Fin M → Option (Sym2 (Fin n))) : (explicitGram A D hid)ᵀ = explicitGram A D hid := by
  ext j k
  simp only [explicitGram, transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul]
  exact sum_congr rfl fun i _ => by ring

theorem quad_explicitGram (A : Matrix (Fin M) (Fin n) ℝ) (D : Fin M → ℝ)
    (hid : Fin M → Option (Sym2 (Fin n))) (x : Fin n → ℝ) :
    x ⬝ᵥ (explicitGram A D hid *ᵥ x) =
      ∑ i ∈ univ.filter (fun i => hid i = none), D i * (A *ᵥ x) i ^ 2 := by
  rw [explicitGram, sum_mulVec, dotProduct_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_mulVec, vecMul_vecMulVec,
    smul_dotProduct, smul_eq_mul, dotProduct_comm x (A i)]
  have h1 : A i ⬝ᵥ x = (A *ᵥ x) i := rfl
  rw [h1]; ring

/-- **The explicit `+I_r` rows make `E` positive definite.** -/
theorem explicitGram_ge {A : Matrix (Fin M) (Fin n) ℝ} {D : Fin M → ℝ}
    {hid : Fin M → Option (Sym2 (Fin n))} {ι : Fin n → Fin M} (hι : IdRows A ι)
    (hιe : ∀ j, hid (ι j) = none) (hD0 : ∀ i, 0 ≤ D i) {dmin : ℝ}
    (hD : ∀ j, dmin ≤ D (ι j)) (x : Fin n → ℝ) :
    dmin * euc x ^ 2 ≤ x ⬝ᵥ (explicitGram A D hid *ᵥ x) := by
  rw [quad_explicitGram, euc_sq, mul_sum]
  have hrow : ∀ j, (A *ᵥ x) (ι j) = x j := fun j => by
    simp [mulVec, hι.2 j, dotProduct, Pi.single_apply]
  calc ∑ j, dmin * x j ^ 2 ≤ ∑ j, D (ι j) * (A *ᵥ x) (ι j) ^ 2 :=
        sum_le_sum fun j _ => by rw [hrow]; exact mul_le_mul_of_nonneg_right (hD j) (sq_nonneg _)
    _ = ∑ i ∈ univ.image ι, D i * (A *ᵥ x) i ^ 2 := by
        rw [sum_image fun a _ b _ h => hι.1 h]
    _ ≤ ∑ i ∈ univ.filter (fun i => hid i = none), D i * (A *ᵥ x) i ^ 2 :=
        sum_le_sum_of_subset_of_nonneg
          (fun i hi => by
            obtain ⟨j, -, rfl⟩ := mem_image.mp hi
            exact mem_filter.mpr ⟨mem_univ _, hιe j⟩)
          fun i _ _ => mul_nonneg (hD0 i) (sq_nonneg _)

theorem pullLap_one (ω : Sym2 (Fin n) → ℝ) (S : Finset (Sym2 (Fin n))) :
    pullLap (1 : Matrix (Fin n) (Fin n) ℝ) ω S = lap ω S := by
  simp [pullLap]

/-- **The frozen normal matrix splits** into the hidden Laplacian, which carries D4's input
energy, and the explicit part. -/
theorem gram_split {A : Matrix (Fin M) (Fin n) ℝ} {D : Fin M → ℝ}
    (hid : Fin M → Option (Sym2 (Fin n))) (G : DiGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hD : ∀ i e, hid i = some e → D i = w e) (hDpos : ∀ i, 0 < D i)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e) :
    gram A D = lap (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) +
      explicitGram A D hid := by
  rw [gram_eq_sum, ← sum_fiberwise_of_maps_to (g := hid) (t := univ) (fun _ _ => mem_univ _),
    Fintype.sum_option, add_comm, explicitGram]
  congr 1
  -- each hidden pair contributes `symS G e · w e · a_e a_eᵀ`
  have hfib : ∀ e : Sym2 (Fin n),
      ∑ i ∈ univ.filter (fun i => hid i = some e), D i • vecMulVec (A i) (A i) =
        ((Spanner.symS G e : ℕ) : ℝ) • (w e • pairMat e) := fun e => by
    rw [← hcount e, Nat.cast_smul_eq_nsmul, ← sum_const]
    refine sum_congr rfl fun i hi => ?_
    have hi' := (mem_filter.mp hi).2
    rw [hD i e hi', hrow i e hi']
  simp only [hfib, lap, Sparsify.omegaR, Sparsify.cR, pow_zero, one_mul, mul_smul]
  rw [sum_filter]
  refine sum_congr rfl fun e _ => ?_
  by_cases hw : 0 < w e
  · simp [Sparsify.P0, hw]
  · have h0 : Spanner.symS G e = 0 := by
      by_contra hne
      rw [← hcount e] at hne
      obtain ⟨i, hi⟩ := card_pos.mp (Nat.pos_of_ne_zero hne)
      have := hD i e (mem_filter.mp hi).2
      exact hw (this ▸ hDpos i)
    simp [Sparsify.P0, hw, h0]

/-- **The LP's frozen normal solve from D4's output.** For the frozen system `gram A D x = b`
of the directed LP, the preconditioner `lap out + E` is invertible. Exact Richardson steps
reach relative energy error `β²` after `k` steps once `2ᵏβ ≥ 1`. -/
theorem lp_frozen_solve {A : Matrix (Fin M) (Fin n) ℝ} {D : Fin M → ℝ}
    {hid : Fin M → Option (Sym2 (Fin n))} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hD : ∀ i e, hid i = some e → D i = w e) (hDpos : ∀ i, 0 < D i)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {ι : Fin n → Fin M} (hι : IdRows A ι) (hιe : ∀ j, hid (ι j) = none) {dmin : ℝ}
    (hdmin : 0 < dmin) (hDι : ∀ j, dmin ≤ D (ι j)) (hw0 : ∀ e, 0 ≤ w e)
    {K t R : ℕ} {δ ε : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G w K t δ R out)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    (b xs : Fin n → ℝ) (hxs : gram A D *ᵥ xs = b) {β : ℝ} (k : ℕ) (hk : 1 ≤ β * 2 ^ k) :
    let P := lap out univ + explicitGram A D hid
    let step : (Fin n → ℝ) → Fin n → ℝ := fun x => x + P⁻¹ *ᵥ (b - gram A D *ᵥ x)
    P.det ≠ 0 ∧
      (step^[k] 0 - xs) ⬝ᵥ (gram A D *ᵥ (step^[k] 0 - xs)) ≤ β ^ 2 * (xs ⬝ᵥ (gram A D *ᵥ xs)) := by
  intro P step
  have hsplit := gram_split hid G w hrow hD hDpos hcount
  have hE := explicitGram_ge hι hιe (fun i => (hDpos i).le) hDι
  have h := frozen_solve hgood hw0 hε0 hε hδlo hδhi (1 : Matrix (Fin n) (Fin n) ℝ)
    (explicitGram_symm A D hid) hdmin hE b xs (by rw [pullLap_one, ← hsplit]; exact hxs) k hk
  simp only [pullLap_one, ← hsplit] at h
  exact h

/-- **The LP's frozen normal solve with rounding errors.** -/
theorem lp_frozen_solve_inexact {A : Matrix (Fin M) (Fin n) ℝ} {D : Fin M → ℝ}
    {hid : Fin M → Option (Sym2 (Fin n))} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hD : ∀ i e, hid i = some e → D i = w e) (hDpos : ∀ i, 0 < D i)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {ι : Fin n → Fin M} (hι : IdRows A ι) (hιe : ∀ j, hid (ι j) = none) {dmin : ℝ}
    (hdmin : 0 < dmin) (hDι : ∀ j, dmin ≤ D (ι j)) (hw0 : ∀ e, 0 ≤ w e)
    {K t R : ℕ} {δ ε : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G w K t δ R out)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    (b xs : Fin n → ℝ) (hxs : gram A D *ᵥ xs = b) (x : ℕ → Fin n → ℝ) (hx0 : x 0 = 0)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    let P := lap out univ + explicitGram A D hid
    let step : (Fin n → ℝ) → Fin n → ℝ := fun y => y + P⁻¹ *ᵥ (b - gram A D *ᵥ y)
    (∀ j, enorm (gram A D) (x (j + 1) - step (x j)) ≤ τ) →
    ∀ k, enorm (gram A D) (x k - xs) ≤ (1 / 2) ^ k * enorm (gram A D) xs + 2 * τ := by
  intro P step
  have hsplit := gram_split hid G w hrow hD hDpos hcount
  have hE := explicitGram_ge hι hιe (fun i => (hDpos i).le) hDι
  have h := frozen_solve_inexact hgood hw0 hε0 hε hδlo hδhi (1 : Matrix (Fin n) (Fin n) ℝ)
    (explicitGram_symm A D hid) hdmin hE b xs (by rw [pullLap_one, ← hsplit]; exact hxs) x hx0 hτ
  simp only [pullLap_one, ← hsplit] at h
  exact h


/-- `u ≤ √c √v` from `u² ≤ c v`. -/
theorem le_sqrt_mul_sqrt_of_sq {u c v : ℝ} (hu : 0 ≤ u) (hc : 0 ≤ c) (h : u ^ 2 ≤ c * v) :
    u ≤ Real.sqrt c * Real.sqrt v := by
  rw [← Real.sqrt_mul hc, ← Real.sqrt_sq hu]
  exact Real.sqrt_le_sqrt h

set_option maxHeartbeats 1600000 in
/-- **`lem:numeric` from an additive energy-norm bound.** The hypothesis
`‖π̃ − π̂‖_{L̂} ≤ β(‖π̂‖_{L̂} + 1)` is what `frozen_solve_inexact` gives once `2⁻ᵏ ≤ β` and
`2τ ≤ β`. It holds for zero and arbitrarily small right-hand sides. The conclusion is the
coordinate bound of `direction_error` with
`E₂ = c₂(P_π + E₁) + c₃`, `c₂ = √(2/ℓ)·√(3d₊/2)·a`, `c₃ = √(2/ℓ)`. -/
theorem direction_error_abs {A : Matrix (Fin M) (Fin n) ℝ} {D Dh q qh : Fin M → ℝ}
    {p0 ph pt pb : Fin n → ℝ} {a dp Q ℓ β : ℝ}
    (hA : ∀ x, euc (A *ᵥ x) ≤ a * euc x) (hAt : ∀ y, euc (Aᵀ *ᵥ y) ≤ a * euc y)
    (hrow : ∀ x i, |(A *ᵥ x) i| ≤ Real.sqrt 2 * euc x) (ha : 0 ≤ a)
    (hD : ∀ i, 0 < D i) (hDp : ∀ i, D i ≤ dp) (hdp : 0 ≤ dp)
    (hDh : ∀ i, |Dh i - D i| ≤ β * D i) (hq : ∀ i, |q i| ≤ Q) (hQ : 0 ≤ Q)
    (hqh : ∀ i, |qh i - q i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (hℓ : 0 < ℓ)
    (hL : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (gram A D *ᵥ x))
    (hp : gram A D *ᵥ p0 = Aᵀ *ᵥ fun i => D i * q i)
    (hph : gram A Dh *ᵥ ph = Aᵀ *ᵥ fun i => Dh i * qh i)
    (hpt : enorm (gram A Dh) (pt - ph) ≤ β * (enorm (gram A Dh) ph + 1))
    (hpb : ∀ j, |pb j - pt j| ≤ β) :
    let Pp := a * Real.sqrt M * dp * Q / ℓ
    let E₁ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pp)
    let E₂ := Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * (Pp + E₁) + Real.sqrt (2 / ℓ)
    let E := E₁ + E₂ + Real.sqrt n
    let P₁ := dp * (Q + 2) + Real.sqrt 2 * dp * (Pp + E) + Real.sqrt 2 * dp * E
    ∀ i, |-Dh i * (qh i - (A *ᵥ pb) i) - -D i * (q i - (A *ᵥ p0) i)| ≤ P₁ * β := by
  intro Pp E₁ E₂ E P₁
  have hlo := frozen_gram_lo (A := A) hD hDh hβ hL
  have hup := frozen_gram_up hA hD hDp hdp hDh hβ
  have hpsd : ∀ y, 0 ≤ y ⬝ᵥ (gram A Dh *ᵥ y) := fun y =>
    (mul_nonneg (by positivity) (sq_nonneg _)).trans (hlo y)
  -- `‖y‖₂ ≤ √(2/ℓ) ‖y‖_{L̂}` and `‖y‖_{L̂} ≤ √(3d₊/2) a ‖y‖₂`
  have heuc : ∀ y, euc y ≤ Real.sqrt (2 / ℓ) * enorm (gram A Dh) y := fun y => by
    refine le_sqrt_mul_sqrt_of_sq (euc_nonneg y) (by positivity) ?_
    have := hlo y
    rw [div_mul_eq_mul_div, le_div_iff₀ hℓ] at *
    nlinarith
  have hen : ∀ y, enorm (gram A Dh) y ≤ Real.sqrt (3 / 2 * dp) * (a * euc y) := fun y => by
    rw [enorm, ← Real.sqrt_sq (mul_nonneg ha (euc_nonneg y)), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt ((hup y).trans_eq (by ring))
  have hΔt' : euc (pt - ph) ≤
      β * (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * euc ph + Real.sqrt (2 / ℓ)) := by
    have h1 := heuc (pt - ph)
    have h2 := hen ph
    have hs : 0 ≤ Real.sqrt (2 / ℓ) := Real.sqrt_nonneg _
    calc euc (pt - ph) ≤ Real.sqrt (2 / ℓ) * enorm (gram A Dh) (pt - ph) := h1
      _ ≤ Real.sqrt (2 / ℓ) * (β * (enorm (gram A Dh) ph + 1)) :=
          mul_le_mul_of_nonneg_left hpt hs
      _ ≤ Real.sqrt (2 / ℓ) * (β * (Real.sqrt (3 / 2 * dp) * (a * euc ph) + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hβ0) hs
      _ = _ := by ring
  exact direction_error_core hA hAt hrow ha hD hDp hdp hDh hq hQ hqh hβ0 hβ hℓ hL hp hph
    (by positivity) (Real.sqrt_nonneg _) hΔt' hpb

set_option maxHeartbeats 1600000 in
/-- **The LP's Newton direction from D4's output, with rounding.** Freeze `D` and `q`, and
precondition the LP's frozen normal system `gram A D̂` with `lap out + E` from a `Good` D4
output. Run `k` Richardson steps from `0` with per-step energy-norm error `τ`, where
`2⁻ᵏ ≤ β` and `2τ ≤ β`, and round the result to coordinate error `β`. The resulting direction
is within `P₁β` of the exact Newton direction in every coordinate. -/
theorem lp_direction_error {A : Matrix (Fin M) (Fin n) ℝ} {D Dh q qh : Fin M → ℝ}
    {p0 ph pb : Fin n → ℝ} {a dp Q ℓ β : ℝ}
    (hA : ∀ x, euc (A *ᵥ x) ≤ a * euc x) (hAt : ∀ y, euc (Aᵀ *ᵥ y) ≤ a * euc y)
    (hrowA : ∀ x i, |(A *ᵥ x) i| ≤ Real.sqrt 2 * euc x) (ha : 0 ≤ a)
    (hD : ∀ i, 0 < D i) (hDp : ∀ i, D i ≤ dp) (hdp : 0 ≤ dp)
    (hDh : ∀ i, |Dh i - D i| ≤ β * D i) (hq : ∀ i, |q i| ≤ Q) (hQ : 0 ≤ Q)
    (hqh : ∀ i, |qh i - q i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (hℓ : 0 < ℓ)
    (hL : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (gram A D *ᵥ x))
    (hp : gram A D *ᵥ p0 = Aᵀ *ᵥ fun i => D i * q i)
    (hph : gram A Dh *ᵥ ph = Aᵀ *ᵥ fun i => Dh i * qh i)
    -- row structure of the directed LP, with the frozen weights `D̂`
    {hid : Fin M → Option (Sym2 (Fin n))} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hDw : ∀ i e, hid i = some e → Dh i = w e)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {ι : Fin n → Fin M} (hι : IdRows A ι) (hιe : ∀ j, hid (ι j) = none) {dmin : ℝ}
    (hdmin : 0 < dmin) (hDι : ∀ j, dmin ≤ Dh (ι j)) (hw0 : ∀ e, 0 ≤ w e)
    -- D4's output
    {K t R : ℕ} {δ ε : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G w K t δ R out)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    -- the computed refinement sequence
    (x : ℕ → Fin n → ℝ) (hx0 : x 0 = 0) {τ : ℝ} (hτ : 0 ≤ τ) (hτβ : 2 * τ ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β)
    (herr : ∀ j, enorm (gram A Dh) (x (j + 1) - (x j + (lap out univ + explicitGram A Dh hid)⁻¹ *ᵥ
      ((Aᵀ *ᵥ fun i => Dh i * qh i) - gram A Dh *ᵥ x j))) ≤ τ)
    (hpb : ∀ j, |pb j - x k j| ≤ β) :
    let Pp := a * Real.sqrt M * dp * Q / ℓ
    let E₁ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pp)
    let E₂ := Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * (Pp + E₁) + Real.sqrt (2 / ℓ)
    let E := E₁ + E₂ + Real.sqrt n
    let P₁ := dp * (Q + 2) + Real.sqrt 2 * dp * (Pp + E) + Real.sqrt 2 * dp * E
    ∀ i, |-Dh i * (qh i - (A *ᵥ pb) i) - -D i * (q i - (A *ᵥ p0) i)| ≤ P₁ * β := by
  have hDhpos : ∀ i, 0 < Dh i := fun i => by
    have := (abs_le.mp (hDh i)).1; nlinarith [hD i]
  have hsolve := lp_frozen_solve_inexact hrow hDw hDhpos hcount hι hιe hdmin hDι hw0 hgood
    hε0 hε hδlo hδhi _ ph hph x hx0 hτ herr k
  have hpt : enorm (gram A Dh) (x k - ph) ≤ β * (enorm (gram A Dh) ph + 1) := by
    have h0 := enorm_nonneg (gram A Dh) ph
    calc _ ≤ (1 / 2) ^ k * enorm (gram A Dh) ph + 2 * τ := hsolve
      _ ≤ β * enorm (gram A Dh) ph + β := add_le_add (mul_le_mul_of_nonneg_right hk h0) hτβ
      _ = _ := by ring
  exact direction_error_abs hA hAt hrowA ha hD hDp hdp hDh hq hQ hqh hβ0 hβ hℓ hL hp hph hpt hpb

end

end ImplicitLP
end CutQueryComplexity
