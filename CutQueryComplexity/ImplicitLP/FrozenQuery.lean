import CutQueryComplexity.ImplicitLP.HiddenGram
import CutQueryComplexity.Primitive.DyadicAggregate
import CutQueryComplexity.Model.Reduction

/-! # The frozen normal solve as a query program (D7 item 5)

The hidden part of every Richardson step is the product `L_G x` with the hidden Laplacian
`L_G = lap(omegaR G w 0)`. Its coordinates are row aggregates (`hiddenLap_apply`):
`(L_G x)_v = Σ_{u ≠ v} sym(v,u) · w(uv)(x_v − x_u)`.
On the dyadic grids `w ∈ 2^{e_w} ℤ` and `x ∈ 2^{−p} ℤ`, the public pair formula
`w(uv)(x_v − x_u)` is an integer times `2^{e_w − p}`. With `B` magnitude bits it is a
`DyadicFormula` (`matvecFormula`), and `allRowsUniv` computes `L_G x` exactly in `6Bn`
outgoing-cut queries (`hiddenMatvec_correct`).

`frozenSolveProg` runs `k` refinement steps. Each step queries `L_G x`, adds the explicit part
offline, applies the preconditioner inverse offline, and rounds down to the grid `2^{−p}ℤ`
(`roundGrid`). It uses at most `k · 6Bn` queries. When every iterate passes the bit check
`BitOK`, the program's output is the exact-arithmetic rounded iteration (`frozenSolveProg_eval`).
The rounding contributes `τ = √Λ √n 2^{−p}` per step (`roundGrid_enorm`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Spectral

noncomputable section

variable {n : ℕ}

/-! ## Coordinates of the hidden Laplacian -/

theorem vecMulVec_self_mulVec_apply (a x : Fin n → ℝ) (i : Fin n) :
    (vecMulVec a a *ᵥ x) i = a i * (a ⬝ᵥ x) := by
  simp only [mulVec, dotProduct, vecMulVec_apply, mul_sum, mul_assoc]

theorem pairMat_mulVec_apply (a b : Fin n) (x : Fin n → ℝ) (i : Fin n) :
    (pairMat s(a, b) *ᵥ x) i = incVec a b i * (x a - x b) := by
  rw [pairMat_mk, vecMulVec_self_mulVec_apply, incVec_dot]

theorem incVec_apply (a b i : Fin n) :
    incVec a b i = (if i = a then 1 else 0) - (if i = b then 1 else 0) := by
  simp [incVec, Pi.single_apply]

/-- **Coordinates of a Laplacian:** `(lap ω S x)_v = Σ_{u ≠ v} [s(v,u) ∈ S] ω(vu) (x_v − x_u)`. -/
theorem lap_mulVec_apply (ω : Sym2 (Fin n) → ℝ) (S : Finset (Sym2 (Fin n))) (x : Fin n → ℝ)
    (v : Fin n) :
    (lap ω S *ᵥ x) v =
      ∑ u ∈ univ.erase v, (if s(v, u) ∈ S then ω s(v, u) else 0) * (x v - x u) := by
  rw [lap, sum_mulVec, Finset.sum_apply]
  simp only [smul_mulVec, Pi.smul_apply, smul_eq_mul]
  symm
  refine sum_bij_ne_zero (fun u _ _ => s(v, u)) ?_ ?_ ?_ ?_
  · intro u _ h
    by_contra hS
    exact h (by simp [hS])
  · intro u₁ _ _ u₂ _ _ h
    exact (Sym2.congr_right.mp h)
  · intro e he hne
    induction e using Sym2.ind with
    | h a b =>
        rw [pairMat_mulVec_apply, incVec_apply] at hne
        by_cases hva : v = a
        · subst hva
          have hvb : v ≠ b := by rintro rfl; simp at hne
          refine ⟨b, mem_erase.mpr ⟨hvb.symm, mem_univ _⟩, ?_, rfl⟩
          simp only [he, ↓reduceIte, ne_eq]
          intro h0
          apply hne
          simp only [↓reduceIte, hvb]
          rcases mul_eq_zero.mp h0 with h | h
          · rw [h, zero_mul]
          · rw [h]; ring
        · by_cases hvb : v = b
          · subst hvb
            refine ⟨a, mem_erase.mpr ⟨Ne.symm hva, mem_univ _⟩, ?_, Sym2.eq_swap⟩
            rw [Sym2.eq_swap] at he
            simp only [he, ↓reduceIte, ne_eq]
            intro h0
            apply hne
            simp only [hva, ↓reduceIte]
            rcases mul_eq_zero.mp h0 with h | h
            · rw [Sym2.eq_swap, h, zero_mul]
            · have : x v = x a := by linarith
              rw [this]; ring
          · exfalso; apply hne; simp [hva, hvb]
  · intro u hu h
    have huv : u ≠ v := (mem_erase.mp hu).1
    have hS : s(v, u) ∈ S := by by_contra hS; exact h (by simp [hS])
    rw [pairMat_mulVec_apply, incVec_apply]
    simp only [hS, ↓reduceIte, Ne.symm huv]
    ring

/-- **The hidden Laplacian's coordinates** are row aggregates of the pair formula
`w(vu)(x_v − x_u)`. -/
theorem hiddenLap_apply (G : DiGraph (Fin n)) {w : Sym2 (Fin n) → ℝ} (hw0 : ∀ e, 0 ≤ w e)
    (x : Fin n → ℝ) (v : Fin n) :
    (lap (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) *ᵥ x) v =
      ∑ u ∈ univ.erase v, (G.sym v u : ℝ) * (w s(v, u) * (x v - x u)) := by
  rw [lap_mulVec_apply]
  refine sum_congr rfl fun u _ => ?_
  simp only [mem_filter, mem_univ, true_and, Sparsify.P0, decide_eq_true_eq,
    Sparsify.omegaR, Sparsify.cR, pow_zero, one_mul, Spanner.symS_mk]
  split_ifs with h
  · ring
  · have : w s(v, u) = 0 := le_antisymm (not_lt.mp h) (hw0 _)
    rw [this]; ring

theorem rowCand_true (v : Fin n) : rowCand (fun _ _ => true) v = univ.erase v := by
  ext u; simp [rowCand]

/-! ## The hidden matrix-vector product as a query program -/

/-- One hidden product: all row aggregates of a pair formula. -/
def hiddenMatvec (q : DyadicFormula (Fin n)) :
    DTree (Finset (Fin n)) ℕ (Fin n → ℝ) (6 * q.pos.length * Fintype.card (Fin n)) :=
  allRowsUniv q fun _ _ => true

/-- **Correctness of the hidden product.** If the public formula evaluates to
`w(vu)(x_v − x_u)` off the diagonal, the program returns `L_G x` exactly. -/
theorem hiddenMatvec_correct (G : DiGraph (Fin n)) {w : Sym2 (Fin n) → ℝ} (hw0 : ∀ e, 0 ≤ w e)
    (x : Fin n → ℝ) (q : DyadicFormula (Fin n))
    (hq : ∀ v u, u ≠ v → q.val v u = w s(v, u) * (x v - x u)) :
    (hiddenMatvec q).eval G.out =
      lap (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) *ᵥ x := by
  funext v
  rw [hiddenMatvec, allRowsUniv_correct, hiddenLap_apply G hw0, rowCand_true]
  exact sum_congr rfl fun u hu => by rw [hq v u (mem_erase.mp hu).1]

/-- The pair formula `w(vu)(x_v − x_u)` on positions `e, …, e + B − 1`. -/
def matvecFormula (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) (e : ℤ) (B : ℕ) :
    DyadicFormula (Fin n) :=
  intFormula (fun v u => ⌊w s(v, u) * (x v - x u) / (2 : ℝ) ^ e⌋) e B

theorem matvecFormula_pos_length (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) (e : ℤ) (B : ℕ) :
    (matvecFormula w x e B).pos.length = B := by
  simp [matvecFormula, intFormula]

/-- The formula is exact when the pair value is an integer multiple of `2^e` below
`2^B · 2^e` in magnitude. -/
theorem matvecFormula_val {w : Sym2 (Fin n) → ℝ} {x : Fin n → ℝ} {e : ℤ} {B : ℕ} {v u : Fin n}
    (hm : ∃ m : ℤ, w s(v, u) * (x v - x u) = m * (2 : ℝ) ^ e)
    (hB : |w s(v, u) * (x v - x u)| < (2 : ℝ) ^ B * (2 : ℝ) ^ e) :
    (matvecFormula w x e B).val v u = w s(v, u) * (x v - x u) := by
  obtain ⟨m, hm⟩ := hm
  have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
  have hfl : ⌊w s(v, u) * (x v - x u) / (2 : ℝ) ^ e⌋ = m := by
    rw [hm, mul_div_cancel_right₀ _ h2.ne', Int.floor_intCast]
  have hmB : m.natAbs < 2 ^ B := by
    rw [hm, abs_mul, abs_of_pos h2] at hB
    have h3 : |(m : ℝ)| < 2 ^ B := lt_of_mul_lt_mul_right hB h2.le
    have h4 : ((m.natAbs : ℕ) : ℝ) < ((2 ^ B : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Nat.cast_pow, Nat.cast_ofNat]
      simpa [Int.cast_abs] using h3
    exact_mod_cast h4
  rw [matvecFormula, intFormula_val _ e B (by simpa [hfl] using hmB), hfl, hm]

/-! ## Rounding to the grid `2^{−p} ℤ` -/

/-- Round each coordinate down to the grid `2^{−p} ℤ`. -/
def roundGrid (p : ℕ) (y : Fin n → ℝ) : Fin n → ℝ := fun i => (⌊y i * 2 ^ p⌋ : ℝ) / 2 ^ p

theorem roundGrid_err (p : ℕ) (y : Fin n → ℝ) (i : Fin n) :
    |roundGrid p y i - y i| ≤ 1 / 2 ^ p := by
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have h1 := Int.floor_le (y i * 2 ^ p)
  have h3 := Int.lt_floor_add_one (y i * 2 ^ p)
  have he : roundGrid p y i - y i = ((⌊y i * 2 ^ p⌋ : ℝ) - y i * 2 ^ p) / 2 ^ p := by
    rw [roundGrid]; field_simp
  rw [he, abs_div, abs_of_pos h2, div_le_div_iff_of_pos_right h2, abs_le]
  constructor <;> linarith

theorem roundGrid_mem (p : ℕ) (y : Fin n → ℝ) (i : Fin n) :
    ∃ m : ℤ, roundGrid p y i = m / 2 ^ p :=
  ⟨⌊y i * 2 ^ p⌋, rfl⟩

/-- **Rounding error in the energy norm:** `τ = √Λ √n 2^{−p}`. -/
theorem roundGrid_enorm {L : Matrix (Fin n) (Fin n) ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hup : ∀ x, x ⬝ᵥ (L *ᵥ x) ≤ Λ * euc x ^ 2) (p : ℕ) (y : Fin n → ℝ) :
    enorm L (roundGrid p y - y) ≤ Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)) :=
  enorm_le_of_coord hΛ hup (by positivity) fun i => by
    simpa using roundGrid_err p y i


/-! ## The refinement program -/

/-- The bit check for one iterate: every pair value lies below `2^B · 2^{e_w − p}`. -/
def BitOK (w : Sym2 (Fin n) → ℝ) (ew : ℤ) (p B : ℕ) (x : Fin n → ℝ) : Prop :=
  ∀ v u, u ≠ v → |w s(v, u) * (x v - x u)| < (2 : ℝ) ^ B * (2 : ℝ) ^ (ew - p)

/-- One exact-arithmetic refinement step, rounded down to the grid. -/
def gridStep (L Pinv : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (p : ℕ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  roundGrid p (x + Pinv *ᵥ (b - L *ᵥ x))

/-- **The frozen solve as a query program.** Each of the `k` steps queries the hidden product
(`6Bn` queries) and does everything else offline. -/
def frozenSolveProg (w : Sym2 (Fin n) → ℝ) (ew : ℤ) (p B : ℕ) (E Pinv : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) : (k : ℕ) → (Fin n → ℝ) →
    DTree (Finset (Fin n)) ℕ (Fin n → ℝ) (k * (6 * B * n))
  | 0, x => DTree.pure x
  | k + 1, x => ((hiddenMatvec (matvecFormula w x (ew - p) B)).bind fun y =>
      frozenSolveProg w ew p B E Pinv b k (roundGrid p (x + Pinv *ᵥ (b - (y + E *ᵥ x))))).cast
        (by rw [matvecFormula_pos_length, Fintype.card_fin]; ring)

/-- On the grids, the pair value is an integer multiple of `2^{e_w − p}`. -/
theorem pair_mem_grid {w : Sym2 (Fin n) → ℝ} {ew : ℤ} {p : ℕ}
    (hw : ∀ e, ∃ m : ℤ, w e = m * (2 : ℝ) ^ ew) {x : Fin n → ℝ}
    (hx : ∀ i, ∃ m : ℤ, x i = m / 2 ^ p) (v u : Fin n) :
    ∃ m : ℤ, w s(v, u) * (x v - x u) = m * (2 : ℝ) ^ (ew - p) := by
  obtain ⟨a, ha⟩ := hw s(v, u)
  obtain ⟨c, hc⟩ := hx v
  obtain ⟨d, hd⟩ := hx u
  refine ⟨a * (c - d), ?_⟩
  rw [ha, hc, hd, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  push_cast
  field_simp

/-- **Correctness of the refinement program.** Start on the grid, and suppose every iterate of
the exact-arithmetic rounded iteration passes the bit check. Then the program outputs the
`k`-th iterate, computed with exact hidden products `L_G x` and `L = L_G + E`. -/
theorem frozenSolveProg_eval (G : DiGraph (Fin n)) {w : Sym2 (Fin n) → ℝ} (hw0 : ∀ e, 0 ≤ w e)
    {ew : ℤ} (hw : ∀ e, ∃ m : ℤ, w e = m * (2 : ℝ) ^ ew) (p B : ℕ)
    (E Pinv : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (x : Fin n → ℝ), (∀ i, ∃ m : ℤ, x i = m / 2 ^ p) →
      (∀ j < k, BitOK w ew p B ((gridStep (lap (Sparsify.omegaR G w 0)
        (univ.filter fun e => Sparsify.P0 w e = true) + E) Pinv b p)^[j] x)) →
      (frozenSolveProg w ew p B E Pinv b k x).eval G.out =
        (gridStep (lap (Sparsify.omegaR G w 0)
          (univ.filter fun e => Sparsify.P0 w e = true) + E) Pinv b p)^[k] x := by
  intro k
  induction k with
  | zero => intro x _ _; simp [frozenSolveProg]
  | succ k ih =>
      intro x hx hbit
      have h0 := hbit 0 (Nat.succ_pos k)
      simp only [Function.iterate_zero, id] at h0
      have hq : ∀ v u, u ≠ v →
          (matvecFormula w x (ew - p) B).val v u = w s(v, u) * (x v - x u) := fun v u huv =>
        matvecFormula_val (pair_mem_grid hw hx v u) (h0 v u huv)
      rw [frozenSolveProg, DTree.eval_cast, DTree.eval_bind, hiddenMatvec_correct G hw0 x _ hq,
        Function.iterate_succ_apply]
      have hstep : roundGrid p (x + Pinv *ᵥ (b - (lap (Sparsify.omegaR G w 0)
          (univ.filter fun e => Sparsify.P0 w e = true) *ᵥ x + E *ᵥ x))) =
          gridStep (lap (Sparsify.omegaR G w 0)
            (univ.filter fun e => Sparsify.P0 w e = true) + E) Pinv b p x := by
        rw [gridStep, add_mulVec]
      rw [hstep]
      exact ih _ (roundGrid_mem p _) fun j hj => by
        have := hbit (j + 1) (Nat.succ_lt_succ hj)
        rwa [Function.iterate_succ_apply] at this

/-- **The bit check from a public magnitude bound.** If `‖x‖₂ ≤ X`, `|w| ≤ W` and
`2WX < 2^B 2^{e_w − p}`, then `x` passes the bit check. -/
theorem bitOK_of_bound {w : Sym2 (Fin n) → ℝ} {ew : ℤ} {p B : ℕ} {W X : ℝ}
    (hW : ∀ e, |w e| ≤ W) {x : Fin n → ℝ} (hX : euc x ≤ X)
    (hB : W * (2 * X) < (2 : ℝ) ^ B * (2 : ℝ) ^ (ew - p)) : BitOK w ew p B x := by
  intro v u _
  have h1 : |x v - x u| ≤ 2 * X := by
    have := abs_sub (x v) (x u)
    linarith [abs_le_euc x v, abs_le_euc x u]
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW s(v, u))
  rw [abs_mul]
  exact lt_of_le_of_lt (mul_le_mul (hW _) h1 (abs_nonneg _) hW0) hB

/-- `‖y‖₂ ≤ √(1/ℓ') ‖y‖_L` when `ℓ' ‖y‖² ≤ yᵀLy`. -/
theorem euc_le_enorm {L : Matrix (Fin n) (Fin n) ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlo : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (L *ᵥ x)) (y : Fin n → ℝ) :
    euc y ≤ Real.sqrt (1 / ℓ) * enorm L y := by
  refine le_sqrt_mul_sqrt_of_sq (euc_nonneg y) (by positivity) ?_
  have := hlo y
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hℓ]
  linarith

set_option maxHeartbeats 1600000 in
/-- **The LP's frozen normal solve as a query program.** Assume the row structure of
`gram_split`, a `Good` D4 output, public lower and upper envelopes `ℓ'`, `Λ` of the frozen
matrix, public bounds `‖π̂‖₂ ≤ X̂`, `‖π̂‖_L ≤ Ê` and `|w| ≤ W` for the exact solution `π̂`,
a weight grid `w ∈ 2^{e_w}ℤ`, and bit length `B` with `2W X < 2^B 2^{e_w − p}`, where
`X = X̂ + √(1/ℓ')(Ê + 2τ)` and `τ = √Λ √n 2^{−p}`. Then `frozenSolveProg` uses at most
`k · 6Bn` queries and outputs `xₖ` with `‖xₖ − π̂‖_L ≤ 2⁻ᵏ‖π̂‖_L + 2τ`. -/
theorem lp_frozen_query_solve {M : ℕ} {A : Matrix (Fin M) (Fin n) ℝ} {D : Fin M → ℝ}
    {hid : Fin M → Option (Sym2 (Fin n))} {G : DiGraph (Fin n)} {w : Sym2 (Fin n) → ℝ}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hD : ∀ i e, hid i = some e → D i = w e) (hDpos : ∀ i, 0 < D i)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {ι : Fin n → Fin M} (hι : IdRows A ι) (hιe : ∀ j, hid (ι j) = none) {dmin : ℝ}
    (hdmin : 0 < dmin) (hDι : ∀ j, dmin ≤ D (ι j)) (hw0 : ∀ e, 0 ≤ w e)
    {K t R : ℕ} {δ ε : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G w K t δ R out)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    (b xs : Fin n → ℝ) (hxs : gram A D *ᵥ xs = b)
    {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 ≤ Λ) (hlo : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (gram A D *ᵥ x))
    (hup : ∀ x, x ⬝ᵥ (gram A D *ᵥ x) ≤ Λ * euc x ^ 2)
    {Xh Eh W : ℝ} (hXh : euc xs ≤ Xh) (hEh : enorm (gram A D) xs ≤ Eh) (hW : ∀ e, |w e| ≤ W)
    {ew : ℤ} (hwg : ∀ e, ∃ m : ℤ, w e = m * (2 : ℝ) ^ ew) (p B : ℕ)
    (hB : W * (2 * (Xh + Real.sqrt (1 / ℓ) *
      (Eh + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) < (2 : ℝ) ^ B * (2 : ℝ) ^ (ew - p))
    (k : ℕ) :
    let P := lap out univ + explicitGram A D hid
    let xk := (frozenSolveProg w ew p B (explicitGram A D hid) P⁻¹ b k 0).eval G.out
    enorm (gram A D) (xk - xs) ≤ (1 / 2) ^ k * enorm (gram A D) xs +
      2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p))) := by
  intro P xk
  set τ := Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)) with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hsplit := gram_split hid G w hrow hD hDpos hcount
  set L := gram A D with hL
  -- the exact-arithmetic rounded iteration
  set x : ℕ → Fin n → ℝ := fun j =>
    (gridStep (lap (Sparsify.omegaR G w 0) (univ.filter fun e => Sparsify.P0 w e = true) +
      explicitGram A D hid) P⁻¹ b p)^[j] 0 with hxdef
  have hstepL : ∀ j, x (j + 1) = roundGrid p (x j + P⁻¹ *ᵥ (b - L *ᵥ x j)) := fun j => by
    simp only [hxdef, Function.iterate_succ_apply', gridStep]
    rw [hsplit]
  have herr : ∀ j, enorm L (x (j + 1) - (x j + P⁻¹ *ᵥ (b - L *ᵥ x j))) ≤ τ := fun j => by
    rw [hstepL]; exact roundGrid_enorm hΛ hup p _
  have hsolve := lp_frozen_solve_inexact hrow hD hDpos hcount hι hιe hdmin hDι hw0 hgood
    hε0 hε hδlo hδhi b xs hxs x (by simp [hxdef]) hτ0 herr
  -- every iterate passes the bit check
  have hbit : ∀ j, BitOK w ew p B (x j) := fun j => by
    have h1 := hsolve j
    have h2 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h3 : enorm L (x j - xs) ≤ Eh + 2 * τ := by
      have h0 := enorm_nonneg L xs
      calc _ ≤ (1 / 2) ^ j * enorm L xs + 2 * τ := h1
        _ ≤ 1 * enorm L xs + 2 * τ := by gcongr
        _ ≤ Eh + 2 * τ := by linarith
    have h4 : euc (x j) ≤ Xh + Real.sqrt (1 / ℓ) * (Eh + 2 * τ) := by
      have h5 := euc_le_enorm hℓ hlo (x j - xs)
      have h6 := euc_add_le (x j - xs) xs
      rw [sub_add_cancel] at h6
      have h7 : Real.sqrt (1 / ℓ) * enorm L (x j - xs) ≤ Real.sqrt (1 / ℓ) * (Eh + 2 * τ) :=
        mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
      linarith
    exact bitOK_of_bound hW h4 hB
  have heval := frozenSolveProg_eval G hw0 hwg p B (explicitGram A D hid) P⁻¹ b k 0
    (fun i => ⟨0, by simp⟩) fun j _ => hbit j
  have hxk : xk = x k := heval
  rw [hxk]
  exact hsolve k

/-- **The query cost** of the frozen solve is at most `k · 6Bn` (`DTree.cost_le`). -/
theorem frozenSolveProg_cost (G : DiGraph (Fin n)) (w : Sym2 (Fin n) → ℝ) (ew : ℤ) (p B : ℕ)
    (E Pinv : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ) :
    (frozenSolveProg w ew p B E Pinv b k x).cost G.out ≤ k * (6 * B * n) :=
  DTree.cost_le _ _

end

end ImplicitLP
end CutQueryComplexity
