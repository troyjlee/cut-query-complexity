import CutQueryComplexity.ImplicitLP.NormalBounds
import CutQueryComplexity.ImplicitLP.LPRows
import CutQueryComplexity.ImplicitLP.SlackFloor
import CutQueryComplexity.ImplicitLP.Size

/-! # `lem:numeric` for the computed direction (D7)

* `lem_numeric_abs_env`: `lem_numeric_env` with the additive energy-norm solve bound
  `‖π̃ − π̂‖_{L̂} ≤ β(‖π̂‖_{L̂} + 1)` (via `direction_error_abs_note`), so `E_π` has the extra
  additive `√(2/ℓ)` and `c₂ = √(2/ℓ)√(3d₊/2)a`.
* `lem_numeric_query`: the solve is the query program `frozenSolveProg` (output
  `.eval G.out`), with `2⁻ᵏ ≤ β`, `2τ ≤ β`, `τ = √Λ√r2^{−p}`. The frozen solution `π̂`, its
  bounds `‖π̂‖₂ ≤ P_π`, `‖π̂‖_{L̂} ≤ √Λ P_π` and the frozen envelopes `ℓ/2`, `Λ` are derived.
* `lem_numeric_lp`: the same for the actual LP rows `lpA`/`lpD`.
* `weight_invariants`: `1/(4M̄) ≤ w ≤ 4`, `Σw ≤ 4r` from `eq_gsize` and the log window.
* `lem_numeric_query_inv`, `lem_numeric_lp_inv`: weight and slack hypotheses replaced by the
  path-following invariants (`eq_gsize`, `slack_floor_note`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ}

section Instance

variable {A : Matrix (Fin M) (Fin r) ℝ} {κ m x w c : Fin M → ℝ} {t U : ℝ}

set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` at a barrier point from an additive energy-norm solve bound**
`‖π̃ − π̂‖_{L̂} ≤ β(‖π̂‖_{L̂} + 1)`. As `lem_numeric_env`, with the additive `E_π`
of `direction_error_abs_note`. -/
theorem lem_numeric_abs_env (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) {wmin dp : ℝ} (hwmin : 0 < wmin) (hwlo : ∀ i, wmin ≤ w i)
    (hdp : U ^ 2 / wmin ≤ dp) (hwhi : ∀ i, w i ≤ 4) (hwsum : ∑ i, w i ≤ 4 * r) {sst ε : ℝ}
    (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * r / ε)
    (hc : ‖c‖ ≤ 4 * U) (hrowA : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι)
    {Dh qh : Fin M → ℝ} {p0 ph pt pb : Fin r → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |Dh i - normD w (barS κ m x) i| ≤ β * normD w (barS κ m x) i)
    (hqh : ∀ i, |qh i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hp : gram A (normD w (barS κ m x)) *ᵥ p0 =
      Aᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    (hph : gram A Dh *ᵥ ph = Aᵀ *ᵥ fun i => Dh i * qh i)
    (hpt : enorm (gram A Dh) (pt - ph) ≤ β * (enorm (gram A Dh) ph + 1))
    (hpb : ∀ j, |pb j - pt j| ≤ β) :
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let h : Fin M → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin M → ℝ := fun i => -Dh i * (qh i - (A *ᵥ pb) i)
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * M)
    let Q := 64 * r * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt r
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt r⌉₊ : ℝ)
    ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ repairDir A ι ht' = 0 ∧
      mixed C w (fun i => barS κ m x i * (repairDir A ι ht' - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * M) * P₁ * β := by
  intro D q h ht' ℓ a Q Pπ Eπ P₁ T₀
  have hU0 : 0 < U := by linarith
  have hw : ∀ i, 0 < w i := fun i => hwmin.trans_le (hwlo i)
  have hS : ∀ i, 0 < barS κ m x i := barS_pos hκ hx
  obtain ⟨h1, h2, -, h4⟩ := normalbounds (t := t) (c := c) hκ hx hU1 hU hwmin hwlo hwhi hsst hs
    hrowA hι
  have hL : ∀ y, ℓ * euc y ^ 2 ≤ y ⬝ᵥ (gram A D *ᵥ y) := fun y => by
    have := h2 y; simp only [ℓ]; norm_num at this ⊢; linarith
  have hdp0 : 0 ≤ dp := (by positivity : 0 ≤ U ^ 2 / wmin).trans hdp
  have hq : ∀ i, |q i| ≤ Q := fun i => (h4 i).trans (add_le_add (by
    calc |t| * ‖c‖ ≤ 16 * r / ε * (4 * U) := mul_le_mul ht hc (norm_nonneg _) (by positivity)
      _ = 64 * r * U / ε := by ring) (by norm_num))
  have hcoord := direction_error_abs_note (opnorm_le hrowA) (opnorm_transpose_le hrowA)
    (row_apply_le hrowA) (Real.sqrt_nonneg _) (fun i => (h1 i).1) (fun i => (h1 i).2.trans hdp)
    hdp0 hDh hq (by positivity) hqh hβ0 hβ (by positivity) hL hp hph hpt hpb
  have hP₁ : 0 ≤ P₁ := by simp only [P₁, Eπ, Pπ, Q, ℓ, a]; positivity
  have hinf : ‖ht' - h‖ ≤ P₁ * β :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Real.norm_eq_abs]; exact hcoord i
  have hh := (exact_dir_spec (A := A) hw hS hp).1
  refine ⟨hinf, repair_feasible hι ht', ?_⟩
  have hSbar : ∀ i, barS κ m x i ≤ 2 / sst := fun i => by
    have hsi : 0 < slk κ m x i := hsst.trans_le (hs i)
    rw [le_div_iff₀ hsst]
    nlinarith [(barrier_env hκ hx hU1 hU i).2.1, hs i, hS i]
  have hrep := repair_mixed hι (abs_entry_le_of_rows hrowA) hh (h' := ht') hC
    (fun i => (hw i).le) (fun i => (hS i).le) (by positivity) hSbar hwsum
  refine hrep.trans ?_
  have hT : 1 + C * Real.sqrt (4 * r) ≤ T₀ := by
    have : Real.sqrt (4 * r) = 2 * Real.sqrt r := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [this]
    have := Nat.le_ceil (Real.sqrt r)
    simp only [T₀]; nlinarith
  have hM0 : 0 ≤ 1 + Real.sqrt 2 * M := by positivity
  calc (1 + C * Real.sqrt (4 * r)) * (2 / sst) * ((1 + Real.sqrt 2 * M) * ‖ht' - h‖)
      ≤ T₀ * (2 / sst) * ((1 + Real.sqrt 2 * M) * (P₁ * β)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hT (by positivity))
          (mul_le_mul_of_nonneg_left hinf hM0) (by positivity)
          (by simp only [T₀]; positivity)
    _ = 2 * T₀ / sst * (1 + Real.sqrt 2 * M) * P₁ * β := by ring


open Spectral in
set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` for the direction computed by the frozen-solve query program.** The frozen
system `L̂π̂ = b`, `b = Aᵀ(D̂q̂)`, is solved by `frozenSolveProg` (D4's preconditioner, `k`
Richardson steps, each rounded to `2^{−p}ℤ`, hidden products by queries), started at `0`. The
computed direction is `h̃ = −D̂(q̂ − A xₖ)` with `xₖ` the program's output. Public envelopes:
`X ≥ P_π`, `Λ ≥ (3/2)d₊·2M`, `τ = √Λ√r 2^{−p}`; weights on a grid `2^{e_w}ℤ`, `|ŵ| ≤ W`, and the
bit length `B` satisfies `2W(X + √(32/s_*²)(√Λ X + 2τ)) < 2^B 2^{e_w − p}`. With `2⁻ᵏ ≤ β` and
`2τ ≤ β`, the conclusions of `lem_numeric_abs_env` hold for `h̃`. -/
theorem lem_numeric_query (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) {wmin dp : ℝ} (hwmin : 0 < wmin) (hwlo : ∀ i, wmin ≤ w i)
    (hdp : U ^ 2 / wmin ≤ dp) (hwhi : ∀ i, w i ≤ 4) (hwsum : ∑ i, w i ≤ 4 * r) {sst ε : ℝ}
    (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * r / ε)
    (hc : ‖c‖ ≤ 4 * U) (hrowA : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι)
    {Dh qh : Fin M → ℝ} {p0 : Fin r → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |Dh i - normD w (barS κ m x) i| ≤ β * normD w (barS κ m x) i)
    (hqh : ∀ i, |qh i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hp : gram A (normD w (barS κ m x)) *ᵥ p0 =
      Aᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    -- the hidden-row structure and D4's output
    {hid : Fin M → Option (Sym2 (Fin r))} {G : DiGraph (Fin r)} {wf : Sym2 (Fin r) → ℝ}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hDw : ∀ i e, hid i = some e → Dh i = wf e)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    (hιe : ∀ j, hid (ι j) = none) {dmin : ℝ} (hdmin : 0 < dmin) (hDι : ∀ j, dmin ≤ Dh (ι j))
    (hwf0 : ∀ e, 0 ≤ wf e)
    {K t' R : ℕ} {δ εs : ℝ} {out : Sym2 (Fin r) → ℝ} (hgood : Sparsify.Good G wf K t' δ R out)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    -- public envelopes, grid and bit length
    {X Λ W : ℝ}
    (hX : 4 * Real.sqrt (2 * M) * Real.sqrt M * dp * (64 * r * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * M) ≤ Λ) (hW : ∀ e, |wf e| ≤ W)
    {ew : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew) (p B : ℕ)
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt r * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ B * (2 : ℝ) ^ (ew - p))
    (hτβ : 2 * (Real.sqrt Λ * (Real.sqrt r * (1 / 2 ^ p))) ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β) :
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let b : Fin r → ℝ := Aᵀ *ᵥ fun i => Dh i * qh i
    let P := lap out univ + explicitGram A Dh hid
    let xk := (frozenSolveProg wf ew p B (explicitGram A Dh hid) P⁻¹ b k 0).eval G.out
    let h : Fin M → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin M → ℝ := fun i => -Dh i * (qh i - (A *ᵥ xk) i)
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * M)
    let Q := 64 * r * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt r
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt r⌉₊ : ℝ)
    ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ repairDir A ι ht' = 0 ∧
      mixed C w (fun i => barS κ m x i * (repairDir A ι ht' - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * M) * P₁ * β := by
  intro D q b P xk h ht' ℓ a Q Pπ Eπ P₁ T₀
  have hU0 : 0 < U := by linarith
  obtain ⟨h1, h2, -, h4⟩ := normalbounds (t := t) (c := c) hκ hx hU1 hU hwmin hwlo hwhi hsst hs
    hrowA hι
  have hD : ∀ i, 0 < D i := fun i => (h1 i).1
  have hDp : ∀ i, D i ≤ dp := fun i => (h1 i).2.trans hdp
  have hdp0 : 0 ≤ dp := (by positivity : 0 ≤ U ^ 2 / wmin).trans hdp
  have hℓ : 0 < ℓ := by positivity
  have hL : ∀ y, ℓ * euc y ^ 2 ≤ y ⬝ᵥ (gram A D *ᵥ y) := fun y => by
    have := h2 y; simp only [ℓ]; norm_num at this ⊢; linarith
  have hq : ∀ i, |q i| ≤ Q := fun i => (h4 i).trans (add_le_add (by
    calc |t| * ‖c‖ ≤ 16 * r / ε * (4 * U) := mul_le_mul ht hc (norm_nonneg _) (by positivity)
      _ = 64 * r * U / ε := by ring) (by norm_num))
  have hQ : 0 ≤ Q := by simp only [Q]; positivity
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hDhpos : ∀ i, 0 < Dh i := fun i => by
    have := (abs_le.mp (hDh i)).1; nlinarith [hD i]
  have hDh_up : ∀ i, Dh i ≤ 3 / 2 * dp := fun i => by
    have := (abs_le.mp (hDh i)).2; nlinarith [hD i, hDp i]
  -- envelopes of the frozen matrix
  have hlo : ∀ y, ℓ / 2 * euc y ^ 2 ≤ y ⬝ᵥ (gram A Dh *ᵥ y) := frozen_gram_lo hD hDh hβ hL
  have hup : ∀ y, y ⬝ᵥ (gram A Dh *ᵥ y) ≤ Λ * euc y ^ 2 := fun y => by
    have h0 := frozen_gram_up (opnorm_le hrowA) hD hDp hdp0 hDh hβ y
    have ha2 : a ^ 2 = 2 * M := Real.sq_sqrt (by positivity)
    rw [ha2] at h0
    exact h0.trans (mul_le_mul_of_nonneg_right hΛ (sq_nonneg _))
  have hΛ0 : 0 ≤ Λ := (by positivity : (0 : ℝ) ≤ 3 / 2 * dp * (2 * M)).trans hΛ
  -- the exact frozen solution
  have hdet : (gram A Dh).det ≠ 0 := det_ne_zero_of_quad_pos fun y hy => by
    have h0 : 0 < euc y := by
      rcases (euc_nonneg y).lt_or_eq with h0 | h0
      · exact h0
      · exfalso; apply hy; funext j
        have := abs_le_euc y j; rw [← h0] at this
        exact abs_nonpos_iff.mp this
    exact lt_of_lt_of_le (by positivity) (hlo y)
  set ph : Fin r → ℝ := (gram A Dh)⁻¹ *ᵥ b with hph_def
  have hph : gram A Dh *ᵥ ph = b := by
    rw [hph_def, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  -- `‖π̂‖₂ ≤ P_π ≤ X`, `‖π̂‖_L ≤ √Λ X`
  have hphn : euc ph ≤ Pπ := by
    have hs1 := solve_bound (by positivity) hlo hph
    have hs2 : euc (fun i => Dh i * qh i) ≤ Real.sqrt M * (2 * dp * (Q + 1)) :=
      euc_le_sqrt_card_mul (by positivity) fun i => by
        rw [abs_mul, abs_of_pos (hDhpos i)]
        have hq1 : |qh i| ≤ Q + 1 / 2 := by
          have := abs_sub_abs_le_abs_sub (qh i) (q i); linarith [hqh i, hq i]
        calc Dh i * |qh i| ≤ 3 / 2 * dp * (Q + 1 / 2) :=
              mul_le_mul (hDh_up i) hq1 (abs_nonneg _) (by positivity)
          _ ≤ 2 * dp * (Q + 1) := by nlinarith
    have hs3 := opnorm_transpose_le hrowA (fun i => Dh i * qh i)
    calc euc ph ≤ euc b / (ℓ / 2) := hs1
      _ ≤ a * (Real.sqrt M * (2 * dp * (Q + 1))) / (ℓ / 2) :=
          div_le_div_of_nonneg_right (hs3.trans (mul_le_mul_of_nonneg_left hs2 ha))
            (by positivity)
      _ = Pπ := by simp only [Pπ]; field_simp; ring
  have hXh : euc ph ≤ X := hphn.trans hX
  have hEh : enorm (gram A Dh) ph ≤ Real.sqrt Λ * X := by
    rw [enorm]
    calc Real.sqrt (ph ⬝ᵥ (gram A Dh *ᵥ ph)) ≤ Real.sqrt (Λ * euc ph ^ 2) :=
          Real.sqrt_le_sqrt (hup ph)
      _ = Real.sqrt Λ * euc ph := by
          rw [Real.sqrt_mul hΛ0, Real.sqrt_sq (euc_nonneg _)]
      _ ≤ Real.sqrt Λ * X := mul_le_mul_of_nonneg_left hXh (Real.sqrt_nonneg _)
  -- the query program's guarantee
  have hsolve := lp_frozen_query_solve hrow hDw hDhpos hcount hι hιe hdmin hDι hwf0 hgood
    hεs0 hεs hδlo hδhi b ph hph (by positivity : (0 : ℝ) < ℓ / 2) hΛ0 hlo hup hXh hEh hW hwg p B
    hB k
  have hpt : enorm (gram A Dh) (xk - ph) ≤ β * (enorm (gram A Dh) ph + 1) := by
    have h0 := enorm_nonneg (gram A Dh) ph
    calc _ ≤ (1 / 2) ^ k * enorm (gram A Dh) ph +
          2 * (Real.sqrt Λ * (Real.sqrt r * (1 / 2 ^ p))) := hsolve
      _ ≤ β * enorm (gram A Dh) ph + β := add_le_add (mul_le_mul_of_nonneg_right hk h0) hτβ
      _ = _ := by ring
  exact lem_numeric_abs_env hκ hx hU1 hU hwmin hwlo hdp hwhi hwsum hsst hs hε ht hc hrowA hι hC
    hDh hqh hβ0 hβ hp hph hpt (fun j => by simp [hβ0])

end Instance

/-! ## The actual LP rows -/

section LP

variable {n : ℕ} (G : DiGraph (Fin n))

theorem sq_ind_sub_le (a b j : Fin n) :
    ((if j = a then (1 : ℝ) else 0) - (if j = b then 1 else 0)) ^ 2 ≤
      (if j = a then 1 else 0) + (if j = b then 1 else 0) := by
  split_ifs <;> norm_num

theorem sum_sq_ind_sub_le (a b : Fin n) :
    ∑ j, ((if j = a then (1 : ℝ) else 0) - (if j = b then 1 else 0)) ^ 2 ≤ 2 := by
  refine (sum_le_sum fun j _ => sq_ind_sub_le a b j).trans_eq ?_
  rw [sum_add_distrib]; simp; norm_num

/-- **Row norms of the LP matrix are at most `√2`.** -/
theorem lpA_row_sq_le (s t : Fin n) (i : Fin (lpM G)) : ∑ j, lpA G s t i j ^ 2 ≤ 2 := by
  simp only [lpA]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j))
  · simpa [lpRowVec, incVec_apply] using sum_sq_ind_sub_le p.1.1 p.1.2
  · simpa [lpRowVec, DirectedMincut.chi] using sum_sq_ind_sub_le s t
  · simp [lpRowVec, Pi.single_apply]
  · simp [lpRowVec, Pi.single_apply]

variable {κ m x w c : Fin (lpM G) → ℝ} {t U : ℝ}

open Spectral in
set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` for the directed LP, from the frozen-solve query program.** The rows are
the actual LP rows `lpA`, the frozen weights are `lpD` (the public pair formula `ŵ` on hidden
copies, explicit `d_q, d₊, d₋` elsewhere), and the D4 graph is `G` itself. Every structural
hypothesis of `lem_numeric_query` is discharged (`lpA_row_sq_le`, `lpA_idRows`, `lpA_hrow`,
`lpD_hD`, `lp_hcount`, `lpHid_iota`). -/
theorem lem_numeric_lp (s t₀ : Fin n) (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) {wmin dp : ℝ} (hwmin : 0 < wmin) (hwlo : ∀ i, wmin ≤ w i)
    (hdp : U ^ 2 / wmin ≤ dp) (hwhi : ∀ i, w i ≤ 4) (hwsum : ∑ i, w i ≤ 4 * n) {sst ε : ℝ}
    (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * n / ε)
    (hc : ‖c‖ ≤ 4 * U)
    {wf : Sym2 (Fin n) → ℝ} {dq : ℝ} {dpv dmv : Fin n → ℝ} {qh : Fin (lpM G) → ℝ}
    {p0 : Fin n → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |lpD G wf dq dpv dmv i - normD w (barS κ m x) i| ≤
      β * normD w (barS κ m x) i)
    (hqh : ∀ i, |qh i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hp : gram (lpA G s t₀) (normD w (barS κ m x)) *ᵥ p0 =
      (lpA G s t₀)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {dmin : ℝ} (hdmin : 0 < dmin) (hdpv : ∀ j, dmin ≤ dpv j) (hwf0 : ∀ e, 0 ≤ wf e)
    {K t' R : ℕ} {δ εs : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G wf K t' δ R out)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    {X Λ W : ℝ}
    (hX : 4 * Real.sqrt (2 * lpM G) * Real.sqrt (lpM G) * dp * (64 * n * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * lpM G) ≤ Λ) (hW : ∀ e, |wf e| ≤ W)
    {ew : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew) (p B : ℕ)
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ B * (2 : ℝ) ^ (ew - p))
    (hτβ : 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p))) ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β) :
    let A := lpA G s t₀
    let Dh := lpD G wf dq dpv dmv
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let b : Fin n → ℝ := Aᵀ *ᵥ fun i => Dh i * qh i
    let P := lap out univ + explicitGram A Dh (lpHidF G)
    let xk := (frozenSolveProg wf ew p B (explicitGram A Dh (lpHidF G)) P⁻¹ b k 0).eval G.out
    let h : Fin (lpM G) → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin (lpM G) → ℝ := fun i => -Dh i * (qh i - (A *ᵥ xk) i)
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * lpM G)
    let Q := 64 * n * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt (lpM G) * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt (lpM G) * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt n
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt n⌉₊ : ℝ)
    ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ repairDir A (lpIota G) ht' = 0 ∧
      mixed C w (fun i => barS κ m x i * (repairDir A (lpIota G) ht' - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * lpM G) * P₁ * β :=
  lem_numeric_query hκ hx hU1 hU hwmin hwlo hdp hwhi hwsum hsst hs hε ht hc
    (lpA_row_sq_le G s t₀) (lpA_idRows G s t₀) hC hDh hqh hβ0 hβ hp
    (lpA_hrow G s t₀) (lpD_hD G wf dq dpv dmv) (lp_hcount G) (lpHid_iota G) hdmin
    (fun j => by simpa [lpD, lpIota, lpWeight] using hdpv j) hwf0 hgood hεs0 hεs hδlo hδhi
    hX hΛ hW hwg p B hB hτβ k hk

end LP

/-! ## The weight and slack hypotheses from the repository's invariants -/

section Invariants

variable {A : Matrix (Fin M) (Fin r) ℝ}

/-- `AᵀA` is invertible when `A` contains the identity rows. -/
theorem det_ne_zero_of_idRows {ι : Fin r → Fin M} (hι : IdRows A ι) : (Aᵀ * A).det ≠ 0 := by
  have e : gram A (fun _ => (1 : ℝ)) = Aᵀ * A := by
    rw [gram, show (diagonal fun _ : Fin M => (1 : ℝ)) = 1 from diagonal_one, Matrix.mul_one]
  rw [← e]
  refine det_ne_zero_of_quad_pos fun y hy => ?_
  have h0 : 0 < euc y := by
    rcases (euc_nonneg y).lt_or_eq with h0 | h0
    · exact h0
    · exfalso; apply hy; funext j
      have := abs_le_euc y j; rw [← h0] at this
      exact abs_nonpos_iff.mp this
  have := gram_ge_of_idRows hι (fun _ => zero_le_one) (dmin := 1) (fun _ => le_rfl) y
  nlinarith

/-- **The weight window from `eq:gsize`.** Let `g = gfun(p, c₀)` be the regularized Lewis
weights at `x` (`p = 1 − 1/L₀`, `L₀ ≥ 2`), with `1/(2M̄) ≤ c₀ ≤ 1/(2M)`, `M ≤ M̄`, `r ≥ 1`,
and let `w` be within `1/5` of `g` in log. Then `1/(4M̄) ≤ w ≤ 4` and `Σw ≤ 4r`. In fact
`w ≤ 15/8` and `Σw ≤ (5/4)(r + 1/2)`. -/
theorem weight_invariants (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    {κ m x : Fin M → ℝ} {c₀ Mbar : ℝ} (hc₀lo : 1 / (2 * Mbar) ≤ c₀) (hcM : c₀ ≤ 1 / (2 * M))
    (hMbar : (M : ℝ) ≤ Mbar) (hr : (1 : ℝ) ≤ r) {w : Fin M → ℝ} (hw : ∀ i, 0 < w i)
    (hwin : ∀ i, |Real.log (w i) - Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)| ≤ 1 / 5) :
    (∀ i, 1 / (4 * Mbar) ≤ w i) ∧ (∀ i, w i ≤ 4) ∧ ∑ i, w i ≤ 4 * r := by
  set g := gfun κ m (1 - 1 / L₀) c₀ A x with hg_def
  set A' := diagonal (fun j => exp (sfun κ m x j)) * A with hA'
  have hA'det : (A'ᵀ * A').det ≠ 0 := diag_det hA fun j => exp_ne_zero _
  have hrow' : ∀ i, A' i ≠ 0 := fun i h0 => by
    apply hrow i; funext j
    have := congrFun h0 j
    simp only [hA', diagonal_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (exp_ne_zero _)
  have hp0 : 0 < 1 - 1 / L₀ := by
    have : 1 / L₀ ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hp2 : 1 - 1 / L₀ < 2 := by have : 0 < 1 / L₀ := by positivity
                                  linarith
  obtain ⟨hsum, hbd⟩ := eq_gsize hA'det hrow' hp0 hp2 c₀
  obtain ⟨he1, -⟩ := exp_fifth_bounds
  have hg : ∀ i, g i = exp (lewisLog (1 - 1 / L₀) A' i) + c₀ := fun i => rfl
  have hwg : ∀ i, w i ≤ 5 / 4 * g i ∧ g i ≤ 5 / 4 * w i := fun i => by
    have hgi : 0 < g i := lt_of_le_of_lt (by
      have : 0 < (M : ℝ) := by exact_mod_cast Fin.pos i
      have : 0 < Mbar := this.trans_le hMbar
      exact (by positivity : (0 : ℝ) ≤ 1 / (2 * Mbar)).trans hc₀lo) (hbd i).1
    have h1 := abs_le.mp (hwin i)
    have a1 : w i ≤ exp (1 / 5) * g i := by
      rw [← exp_log (hw i), ← exp_log hgi, ← exp_add, exp_le_exp]; linarith
    have a2 : g i ≤ exp (1 / 5) * w i := by
      rw [← exp_log (hw i), ← exp_log hgi, ← exp_add, exp_le_exp]; linarith
    exact ⟨a1.trans (mul_le_mul_of_nonneg_right he1 hgi.le),
      a2.trans (mul_le_mul_of_nonneg_right he1 (hw i).le)⟩
  have hc₀half : (M : ℝ) * c₀ ≤ 1 / 2 := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · simp [hM]
    · have hM' : (0 : ℝ) < M := by exact_mod_cast hM
      calc (M : ℝ) * c₀ ≤ M * (1 / (2 * M)) := mul_le_mul_of_nonneg_left hcM hM'.le
        _ = 1 / 2 := by field_simp
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Fin.pos i
    have hMb : 0 < Mbar := by linarith
    have h1 := (hwg i).2
    have h2 := (hbd i).1
    have h3 : 1 / (4 * Mbar) ≤ 4 / 5 * (1 / (2 * Mbar)) := by
      rw [div_le_iff₀ (by positivity)]; field_simp; norm_num
    rw [← hg i] at h2
    nlinarith
  · have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Fin.pos i
    have h1 := (hwg i).1
    have h2 := (hbd i).2
    rw [← hg i] at h2
    have h3 : c₀ ≤ 1 / 2 := hcM.trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    nlinarith
  · have h1 : ∑ i, w i ≤ ∑ i, 5 / 4 * g i := sum_le_sum fun i _ => (hwg i).1
    rw [← mul_sum] at h1
    have h2 : ∑ i, g i = r + M * c₀ := by rw [← hsum]; exact sum_congr rfl fun i _ => hg i
    rw [h2] at h1
    nlinarith

variable {κ m w c : Fin M → ℝ} {t U : ℝ}

open Spectral in
set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` for the query program, from the path-following invariants.** The weight and
slack hypotheses of `lem_numeric_query` are derived rather than assumed:
* `1/(4M̄) ≤ w ≤ 4` and `Σw ≤ 4r` from `eq:gsize` and the window `|log w − log g| ≤ 1/20`
  (`weight_invariants`, needing `1/(2M̄) ≤ c₀ ≤ 1/(2M)` and `M ≤ M̄`);
* `s_* = ε/(2¹² r M̄² U³) ≤ sᵢ(x)` from `eq:slackfloor` (`slack_floor_note`), using the
  centrality `δ ≤ 1/1000`, feasibility of `x`, and a feasible reference `x⁰` with slacks
  `≥ 1/U`;
* `(AᵀA)` invertible from the identity rows (`det_ne_zero_of_idRows`).
Here `d₊ = 4M̄U²` (`= U²/w_min` with `w_min = 1/(4M̄)`). -/
theorem lem_numeric_query_inv {A : Matrix (Fin M) (Fin r) ℝ} {bc : Fin r → ℝ}
    (hrowne : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) {c₀ Mbar ε : ℝ} (hc₀lo : 1 / (2 * Mbar) ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) (hU1 : 1 ≤ U) (hU : ∀ i, π / κ i ≤ U) {x x₀ : Fin M → ℝ}
    (hx : x ∈ Feasible A bc κ m) (hx₀ : x₀ ∈ Feasible A bc κ m) (hMbar : (M : ℝ) ≤ Mbar)
    (hr : (1 : ℝ) ≤ r) (hε : 0 < ε) (hε1 : ε ≤ 1) (hw : ∀ i, 0 < w i)
    (ht : |t| ≤ 16 * r / ε) (hc : ‖c‖ ≤ 4 * U)
    (hwin : ∀ i, |Real.log (w i) - Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)| ≤ 1 / 20)
    (hδc : cent (48 * (2 * L₀)) A (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs0 : ∀ i, 1 / U ≤ slk κ m x₀ i)
    {sst dp : ℝ} (hsst : sst = ε / (2 ^ 12 * r * Mbar ^ 2 * U ^ 3)) (hdp : dp = 4 * Mbar * U ^ 2)
    (hrowA : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι)
    {Dh qh : Fin M → ℝ} {p0 : Fin r → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |Dh i - normD w (barS κ m x) i| ≤ β * normD w (barS κ m x) i)
    (hqh : ∀ i, |qh i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hp : gram A (normD w (barS κ m x)) *ᵥ p0 =
      Aᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {hid : Fin M → Option (Sym2 (Fin r))} {G : DiGraph (Fin r)} {wf : Sym2 (Fin r) → ℝ}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hDw : ∀ i e, hid i = some e → Dh i = wf e)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    (hιe : ∀ j, hid (ι j) = none) {dmin : ℝ} (hdmin : 0 < dmin) (hDι : ∀ j, dmin ≤ Dh (ι j))
    (hwf0 : ∀ e, 0 ≤ wf e)
    {K t' R : ℕ} {δ εs : ℝ} {out : Sym2 (Fin r) → ℝ} (hgood : Sparsify.Good G wf K t' δ R out)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    {X Λ W : ℝ}
    (hX : 4 * Real.sqrt (2 * M) * Real.sqrt M * dp * (64 * r * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * M) ≤ Λ) (hW : ∀ e, |wf e| ≤ W)
    {ew : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew) (p B : ℕ)
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt r * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ B * (2 : ℝ) ^ (ew - p))
    (hτβ : 2 * (Real.sqrt Λ * (Real.sqrt r * (1 / 2 ^ p))) ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β) :
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let b : Fin r → ℝ := Aᵀ *ᵥ fun i => Dh i * qh i
    let P := lap out univ + explicitGram A Dh hid
    let xk := (frozenSolveProg wf ew p B (explicitGram A Dh hid) P⁻¹ b k 0).eval G.out
    let h : Fin M → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin M → ℝ := fun i => -Dh i * (qh i - (A *ᵥ xk) i)
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * M)
    let Q := 64 * r * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt r
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt r⌉₊ : ℝ)
    ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ repairDir A ι ht' = 0 ∧
      mixed C w (fun i => barS κ m x i * (repairDir A ι ht' - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * M) * P₁ * β := by
  have hA := det_ne_zero_of_idRows hι
  have hwin5 : ∀ i, |Real.log (w i) - Real.log (gfun κ m (1 - 1 / L₀) c₀ A x i)| ≤ 1 / 5 :=
    fun i => (hwin i).trans (by norm_num)
  obtain ⟨hwlo, hwhi, hwsum⟩ := weight_invariants hA hrowne hL hc₀lo hcM hMbar hr hw hwin5
  have hM1 : (1 : ℝ) ≤ M := by
    have hr0 : 0 < r := by exact_mod_cast (show (0 : ℝ) < r by linarith)
    exact_mod_cast Fin.pos (ι ⟨0, hr0⟩)
  have hMb : 0 < Mbar := by linarith
  have hc₀ : 0 ≤ c₀ := (by positivity : (0 : ℝ) ≤ 1 / (2 * Mbar)).trans hc₀lo
  have hs : ∀ i, sst ≤ slk κ m x i := fun i => by
    rw [hsst]
    exact slack_floor_note hA hrowne hL hLM hκ hc₀ hcM hU1 hU hx hx₀ hMbar hr hε hε1 hwlo hwsum ht
      hc hwin hδc hs0 i
  have hU0 : 0 < U := by linarith
  have hsst0 : 0 < sst := by rw [hsst]; positivity
  exact lem_numeric_query (wmin := 1 / (4 * Mbar)) hκ hx.2 hU1 hU (by positivity) hwlo
    (by rw [hdp]; field_simp; rfl) hwhi hwsum hsst0 hs hε ht hc hrowA hι hC hDh hqh hβ0 hβ hp
    hrow hDw hcount hιe hdmin hDι hwf0 hgood hεs0 hεs hδlo hδhi hX hΛ hW hwg p B hB hτβ k hk

end Invariants

/-! ## The directed LP from the invariants -/

section LPInv

variable {n : ℕ} (G : DiGraph (Fin n))

/-- Every LP row is nonzero when `s ≠ t` (the `q` row is `χ = e_s − e_t`). -/
theorem lpA_row_ne_zero {s t : Fin n} (hst : s ≠ t) (i : Fin (lpM G)) : lpA G s t i ≠ 0 := by
  simp only [lpA]
  generalize (lpEquiv G).symm i = x
  intro h0
  rcases x with ⟨p, _⟩ | (_ | (j | j))
  · have := congrFun h0 p.1.1
    simp [lpRowVec, incVec_apply, p.2.ne] at this
  · have := congrFun h0 s
    simp [lpRowVec, DirectedMincut.chi, hst] at this
  · have := congrFun h0 j
    simp [lpRowVec] at this
  · have := congrFun h0 j
    simp [lpRowVec] at this

variable {κ m w c : Fin (lpM G) → ℝ} {t U : ℝ}

open Spectral in
set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` for the directed LP from the query program and the invariants.** The
composition of `lem_numeric_query_inv` with the LP rows (`s ≠ t₀`). -/
theorem lem_numeric_lp_inv (s t₀ : Fin n) (hst : s ≠ t₀) {bc : Fin n → ℝ}
    {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * lpM G) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) {c₀ Mbar ε : ℝ} (hc₀lo : 1 / (2 * Mbar) ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * lpM G)) (hU1 : 1 ≤ U) (hU : ∀ i, π / κ i ≤ U)
    {x x₀ : Fin (lpM G) → ℝ}
    (hx : x ∈ Feasible (lpA G s t₀) bc κ m) (hx₀ : x₀ ∈ Feasible (lpA G s t₀) bc κ m)
    (hMbar : (lpM G : ℝ) ≤ Mbar) (hr : (1 : ℝ) ≤ n) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hw : ∀ i, 0 < w i) (ht : |t| ≤ 16 * n / ε) (hc : ‖c‖ ≤ 4 * U)
    (hwin : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (lpA G s t₀) x i)| ≤ 1 / 20)
    (hδc : cent (48 * (2 * L₀)) (lpA G s t₀) (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs0 : ∀ i, 1 / U ≤ slk κ m x₀ i)
    {sst dp : ℝ} (hsst : sst = ε / (2 ^ 12 * n * Mbar ^ 2 * U ^ 3)) (hdp : dp = 4 * Mbar * U ^ 2)
    {wf : Sym2 (Fin n) → ℝ} {dq : ℝ} {dpv dmv : Fin n → ℝ} {qh : Fin (lpM G) → ℝ}
    {p0 : Fin n → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |lpD G wf dq dpv dmv i - normD w (barS κ m x) i| ≤
      β * normD w (barS κ m x) i)
    (hqh : ∀ i, |qh i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hp : gram (lpA G s t₀) (normD w (barS κ m x)) *ᵥ p0 =
      (lpA G s t₀)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {dmin : ℝ} (hdmin : 0 < dmin) (hdpv : ∀ j, dmin ≤ dpv j) (hwf0 : ∀ e, 0 ≤ wf e)
    {K t' R : ℕ} {δ εs : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G wf K t' δ R out)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    {X Λ W : ℝ}
    (hX : 4 * Real.sqrt (2 * lpM G) * Real.sqrt (lpM G) * dp * (64 * n * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * lpM G) ≤ Λ) (hW : ∀ e, |wf e| ≤ W)
    {ew : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew) (p B : ℕ)
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ B * (2 : ℝ) ^ (ew - p))
    (hτβ : 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p))) ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β) :
    let A := lpA G s t₀
    let Dh := lpD G wf dq dpv dmv
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let b : Fin n → ℝ := Aᵀ *ᵥ fun i => Dh i * qh i
    let P := lap out univ + explicitGram A Dh (lpHidF G)
    let xk := (frozenSolveProg wf ew p B (explicitGram A Dh (lpHidF G)) P⁻¹ b k 0).eval G.out
    let h : Fin (lpM G) → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin (lpM G) → ℝ := fun i => -Dh i * (qh i - (A *ᵥ xk) i)
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * lpM G)
    let Q := 64 * n * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt (lpM G) * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt (lpM G) * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt n
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt n⌉₊ : ℝ)
    ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ repairDir A (lpIota G) ht' = 0 ∧
      mixed C w (fun i => barS κ m x i * (repairDir A (lpIota G) ht' - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * lpM G) * P₁ * β :=
  lem_numeric_query_inv (lpA_row_ne_zero G hst) hL hLM hκ hc₀lo hcM hU1 hU hx hx₀ hMbar hr hε
    hε1 hw ht hc hwin hδc hs0 hsst hdp (lpA_row_sq_le G s t₀) (lpA_idRows G s t₀) hC hDh hqh
    hβ0 hβ hp (lpA_hrow G s t₀) (lpD_hD G wf dq dpv dmv) (lp_hcount G) (lpHid_iota G) hdmin
    (fun j => by simpa [lpD, lpIota, lpWeight] using hdpv j) hwf0 hgood hεs0 hεs hδlo hδhi
    hX hΛ hW hwg p B hB hτβ k hk

end LPInv

end

end ImplicitLP
end CutQueryComplexity
