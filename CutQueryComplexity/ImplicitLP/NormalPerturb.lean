import CutQueryComplexity.ImplicitLP.Support
import CutQueryComplexity.ImplicitLP.Lewis

/-! # Absolute accuracy of the frozen Newton direction (`lem:numeric`, D7 item 5)

The exact direction is `h = −D(q − Aπ)` with `Lπ = AᵀDq`, `L = AᵀDA`. The computation freezes
`D` to relative error `β` (`D̂`) and `q` to absolute coordinate error `β` (`q̂`). It solves the
frozen system `L̂π̂ = AᵀD̂q̂` to relative energy error `β`, giving `π̃`, rounds to coordinate error `β`,
giving `π̄`, and forms `h̃ = −D̂(q̂ − Aπ̄)`.

`direction_error` assumes the envelope `‖A‖₂ ≤ a`, `‖Aᵀ‖₂ ≤ a`, `|(Ax)ᵢ| ≤ √2‖x‖₂`,
`0 < Dᵢ ≤ d₊`, `‖q‖_∞ ≤ Q`, `L ⪰ ℓ I`, and `0 ≤ β ≤ 1/2`. It then proves
`‖h̃ − h‖_∞ ≤ P₁ β` with the explicit polynomial
* `P_π = a√M d₊ Q / ℓ` (bounds `‖π‖₂`),
* `E₁ = (2/ℓ)(a√M d₊ (Q + 2) + a² d₊ P_π)` (`‖π̂ − π‖₂ ≤ βE₁`),
* `E₂ = 2a√(d₊/ℓ)(P_π + E₁)` (`‖π̃ − π̂‖₂ ≤ βE₂`); `direction_error_core` takes any
  `E₂ = c₂(P_π + E₁) + c₃` from an absolute bound `‖π̃ − π̂‖₂ ≤ β(c₂‖π̂‖₂ + c₃)`,
* `E = E₁ + E₂ + √r` (`‖π̄ − π‖₂ ≤ βE`),
* `P₁ = d₊(Q + 2) + √2 d₊(P_π + E) + √2 d₊ E`.

This replaces the audited draft's informal "poly(𝒩)" chain with explicit constants. No relative accuracy
with respect to `π` is used, so the bound holds when the right-hand side is zero. Combined with
the exact repair (`repair_mixed`), it gives `N_w(S(d − h)) ≤ P(𝒩) β`.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ}

theorem euc_le_sqrt_card_mul {v : Fin M → ℝ} {c : ℝ} (hc : 0 ≤ c) (hv : ∀ i, |v i| ≤ c) :
    euc v ≤ Real.sqrt M * c := by
  unfold euc wnorm
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (Nat.cast_nonneg M)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, 1 * v i ^ 2 ≤ ∑ _i : Fin M, c ^ 2 := sum_le_sum fun i _ => by
        rw [one_mul, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
    _ = M * c ^ 2 := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `x ⬝ (Gx) ≥ ℓ‖x‖²` gives `‖G⁻¹y‖₂ ≤ ‖y‖₂/ℓ` along a solution `Gx = y`. -/
theorem solve_bound {G : Matrix (Fin r) (Fin r) ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hG : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (G *ᵥ x)) {x y : Fin r → ℝ} (hxy : G *ᵥ x = y) :
    euc x ≤ euc y / ℓ := by
  have h1 := hG x
  rw [hxy] at h1
  have h2 : x ⬝ᵥ y ≤ euc x * euc y := by
    have := dot_le_euc x y; exact this
  rw [le_div_iff₀ hℓ]
  rcases eq_or_lt_of_le (euc_nonneg x) with h0 | h0
  · rw [← h0]; simp [euc_nonneg]
  · nlinarith

theorem euc_le_of_abs_le {u v : Fin M → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |u i| ≤ c * |v i|) :
    euc u ≤ c * euc v := by
  rw [← abs_of_nonneg hc, ← euc_smul]
  unfold euc wnorm
  apply Real.sqrt_le_sqrt
  refine sum_le_sum fun i _ => ?_
  simp only [one_mul, Pi.smul_apply, smul_eq_mul]
  rw [← sq_abs, ← sq_abs (c * v i), abs_mul, abs_of_nonneg hc]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem gram_mulVec_eq (A : Matrix (Fin M) (Fin r) ℝ) (d : Fin M → ℝ) (x : Fin r → ℝ) :
    gram A d *ᵥ x = Aᵀ *ᵥ fun i => d i * (A *ᵥ x) i := by
  rw [gram, ← mulVec_mulVec, ← mulVec_mulVec]
  congr 1; funext i; rw [mulVec_diagonal]

set_option maxHeartbeats 1600000 in
/-- **Core of `lem:numeric`.** The same conclusion as `direction_error`, from an absolute
bound `‖π̃ − π̂‖₂ ≤ β(c₂‖π̂‖₂ + c₃)` on the frozen solve instead of a relative energy bound.
With `c₃ = 0` this is the exact-solve case; `c₃ > 0` absorbs additive rounding. -/
theorem direction_error_core {A : Matrix (Fin M) (Fin r) ℝ} {D Dh q qh : Fin M → ℝ}
    {p0 ph pt pb : Fin r → ℝ} {a dp Q ℓ β : ℝ}
    (hA : ∀ x, euc (A *ᵥ x) ≤ a * euc x) (hAt : ∀ y, euc (Aᵀ *ᵥ y) ≤ a * euc y)
    (hrow : ∀ x i, |(A *ᵥ x) i| ≤ Real.sqrt 2 * euc x) (ha : 0 ≤ a)
    (hD : ∀ i, 0 < D i) (hDp : ∀ i, D i ≤ dp) (hdp : 0 ≤ dp)
    (hDh : ∀ i, |Dh i - D i| ≤ β * D i) (hq : ∀ i, |q i| ≤ Q) (hQ : 0 ≤ Q)
    (hqh : ∀ i, |qh i - q i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (hℓ : 0 < ℓ)
    (hL : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (gram A D *ᵥ x))
    (hp : gram A D *ᵥ p0 = Aᵀ *ᵥ fun i => D i * q i)
    (hph : gram A Dh *ᵥ ph = Aᵀ *ᵥ fun i => Dh i * qh i)
    {c₂ c₃ : ℝ} (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hΔt' : euc (pt - ph) ≤ β * (c₂ * euc ph + c₃))
    (hpb : ∀ j, |pb j - pt j| ≤ β) :
    let Pp := a * Real.sqrt M * dp * Q / ℓ
    let E₁ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pp)
    let E₂ := c₂ * (Pp + E₁) + c₃
    let E := E₁ + E₂ + Real.sqrt r
    let P₁ := dp * (Q + 2) + Real.sqrt 2 * dp * (Pp + E) + Real.sqrt 2 * dp * E
    ∀ i, |-Dh i * (qh i - (A *ᵥ pb) i) - -D i * (q i - (A *ᵥ p0) i)| ≤ P₁ * β := by
  intro Pp E₁ E₂ E P₁
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hDh_lo : ∀ i, D i / 2 ≤ Dh i := fun i => by
    have := (abs_le.mp (hDh i)).1; nlinarith [hD i]
  have hDh_up : ∀ i, Dh i ≤ 3 / 2 * dp := fun i => by
    have := (abs_le.mp (hDh i)).2; nlinarith [hD i, hDp i]
  have hDh0 : ∀ i, 0 ≤ Dh i := fun i => by linarith [hDh_lo i, hD i]
  -- the frozen normal matrix
  have hLh_lo : ∀ x, ℓ / 2 * euc x ^ 2 ≤ x ⬝ᵥ (gram A Dh *ᵥ x) := fun x => by
    have h1 := hL x
    rw [gram_quad] at h1 ⊢
    have : ∑ i, D i * (A *ᵥ x) i ^ 2 / 2 ≤ ∑ i, Dh i * (A *ᵥ x) i ^ 2 :=
      sum_le_sum fun i _ => by nlinarith [hDh_lo i, sq_nonneg ((A *ᵥ x) i)]
    rw [← sum_div] at this
    linarith
  have hLh_up : ∀ x, x ⬝ᵥ (gram A Dh *ᵥ x) ≤ 3 / 2 * dp * a ^ 2 * euc x ^ 2 := fun x => by
    rw [gram_quad]
    have h1 : ∑ i, Dh i * (A *ᵥ x) i ^ 2 ≤ 3 / 2 * dp * euc (A *ᵥ x) ^ 2 := by
      rw [euc_sq, mul_sum]
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hDh_up i) (sq_nonneg _)
    have h2 : euc (A *ᵥ x) ^ 2 ≤ (a * euc x) ^ 2 := pow_le_pow_left₀ (euc_nonneg _) (hA x) 2
    nlinarith
  -- `‖p0‖ ≤ P_p0`
  have hpn : euc p0 ≤ Pp := by
    have h1 := solve_bound hℓ hL hp
    have h2 : euc (fun i => D i * q i) ≤ Real.sqrt M * (dp * Q) :=
      euc_le_sqrt_card_mul (mul_nonneg hdp hQ) fun i => by
        rw [abs_mul, abs_of_pos (hD i)]; exact mul_le_mul (hDp i) (hq i) (abs_nonneg _) hdp
    have h3 := hAt (fun i => D i * q i)
    calc euc p0 ≤ euc (Aᵀ *ᵥ fun i => D i * q i) / ℓ := h1
      _ ≤ a * (Real.sqrt M * (dp * Q)) / ℓ :=
          div_le_div_of_nonneg_right (h3.trans (mul_le_mul_of_nonneg_left h2 ha)) hℓ.le
      _ = Pp := by simp only [Pp]; ring
  have hPp : 0 ≤ Pp := (euc_nonneg p0).trans hpn
  -- `‖p̂ − p‖ ≤ β E₁`
  set y : Fin M → ℝ := fun i => Dh i * qh i - D i * q i - (Dh i - D i) * (A *ᵥ p0) i with hy
  have hp' : Aᵀ *ᵥ (fun i => D i * (A *ᵥ p0) i) = Aᵀ *ᵥ (fun i => D i * q i) := by
    rw [← gram_mulVec_eq]; exact hp
  have e1 : Aᵀ *ᵥ y = Aᵀ *ᵥ (fun i => Dh i * qh i) - Aᵀ *ᵥ (fun i => D i * q i) -
      Aᵀ *ᵥ (fun i => (Dh i - D i) * (A *ᵥ p0) i) := by
    rw [← mulVec_sub, ← mulVec_sub]; rfl
  have e2 : Aᵀ *ᵥ (fun i => Dh i * (A *ᵥ p0) i) = Aᵀ *ᵥ (fun i => D i * (A *ᵥ p0) i) +
      Aᵀ *ᵥ (fun i => (Dh i - D i) * (A *ᵥ p0) i) := by
    rw [← mulVec_add]; congr 1; funext i; simp only [Pi.add_apply]; ring
  have hLΔ : gram A Dh *ᵥ (ph - p0) = Aᵀ *ᵥ y := by
    rw [mulVec_sub, hph, gram_mulVec_eq A Dh p0, e2, hp', e1]; abel
  have hβdp : 0 ≤ β * dp := mul_nonneg hβ0 hdp
  have hu1 : euc (fun i => Dh i * qh i - D i * q i) ≤ Real.sqrt M * (β * dp * (Q + 2)) :=
    euc_le_sqrt_card_mul (by positivity) fun i => by
      have h1 : Dh i * qh i - D i * q i = Dh i * (qh i - q i) + (Dh i - D i) * q i := by ring
      rw [h1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hDh0 i)]
      have a1 : Dh i * |qh i - q i| ≤ 3 / 2 * dp * β :=
        mul_le_mul (hDh_up i) (hqh i) (abs_nonneg _) (by positivity)
      have a2 : |Dh i - D i| * |q i| ≤ β * dp * Q :=
        mul_le_mul ((hDh i).trans (mul_le_mul_of_nonneg_left (hDp i) hβ0)) (hq i)
          (abs_nonneg _) hβdp
      nlinarith
  have hu2 : euc (fun i => (Dh i - D i) * (A *ᵥ p0) i) ≤ β * dp * (a * Pp) := by
    refine (euc_le_of_abs_le hβdp fun i => ?_).trans
      (mul_le_mul_of_nonneg_left ((hA p0).trans (mul_le_mul_of_nonneg_left hpn ha)) hβdp)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((hDh i).trans (mul_le_mul_of_nonneg_left (hDp i) hβ0))
      (abs_nonneg _)
  have hyb : euc y ≤ β * (Real.sqrt M * dp * (Q + 2) + dp * a * Pp) := by
    have hsplit : y = (fun i => Dh i * qh i - D i * q i) +
        (-1 : ℝ) • (fun i => (Dh i - D i) * (A *ᵥ p0) i) := by
      funext i; simp only [hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hsplit]
    refine (euc_add_le _ _).trans ?_
    rw [euc_smul, abs_neg, abs_one, one_mul]
    nlinarith
  have hΔ : euc (ph - p0) ≤ β * E₁ := by
    have h1 := solve_bound (by positivity) hLh_lo hLΔ
    have h2 := hAt y
    calc euc (ph - p0) ≤ euc (Aᵀ *ᵥ y) / (ℓ / 2) := h1
      _ ≤ a * (β * (Real.sqrt M * dp * (Q + 2) + dp * a * Pp)) / (ℓ / 2) :=
          div_le_div_of_nonneg_right (h2.trans (mul_le_mul_of_nonneg_left hyb ha)) (by positivity)
      _ = β * E₁ := by simp only [E₁]; field_simp
  have hE₁ : 0 ≤ E₁ := by simp only [E₁]; positivity
  have hphn : euc ph ≤ Pp + E₁ := by
    have := euc_add_le (ph - p0) p0
    rw [sub_add_cancel] at this
    nlinarith
  -- `‖p̃ − p̂‖ ≤ β E₂`
  have hΔt : euc (pt - ph) ≤ β * E₂ := hΔt'.trans (mul_le_mul_of_nonneg_left
      (by simp only [E₂]; nlinarith [mul_le_mul_of_nonneg_left hphn hc₂]) hβ0)
  -- `‖p̄ − p̃‖ ≤ √r β` and `‖p̄ − p‖ ≤ βE`
  have hΔb : euc (pb - pt) ≤ Real.sqrt r * β := euc_le_sqrt_card_mul hβ0 hpb
  have hEb : euc (pb - p0) ≤ β * E := by
    have h1 := euc_add_le (pb - pt) ((pt - ph) + (ph - p0))
    have h2 := euc_add_le (pt - ph) (ph - p0)
    rw [show pb - pt + (pt - ph + (ph - p0)) = pb - p0 by abel] at h1
    simp only [E]; nlinarith
  have hE₂ : 0 ≤ E₂ := add_nonneg (mul_nonneg hc₂ (add_nonneg hPp hE₁)) hc₃
  have hE : 0 ≤ E := by simp only [E]; positivity
  have hpbn : euc pb ≤ Pp + E := by
    have := euc_add_le (pb - p0) p0
    rw [sub_add_cancel] at this
    nlinarith
  -- the coordinate error
  intro i
  have hdecomp : -Dh i * (qh i - (A *ᵥ pb) i) - -D i * (q i - (A *ᵥ p0) i) =
      -(Dh i * qh i - D i * q i) + (Dh i - D i) * (A *ᵥ pb) i + D i * (A *ᵥ (pb - p0)) i := by
    rw [mulVec_sub, Pi.sub_apply]; ring
  rw [hdecomp]
  have t1 : |Dh i * qh i - D i * q i| ≤ β * dp * (Q + 2) := by
    have h1 : Dh i * qh i - D i * q i = Dh i * (qh i - q i) + (Dh i - D i) * q i := by ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hDh0 i)]
    have a1 : Dh i * |qh i - q i| ≤ 3 / 2 * dp * β :=
      mul_le_mul (hDh_up i) (hqh i) (abs_nonneg _) (by positivity)
    have a2 : |Dh i - D i| * |q i| ≤ β * dp * Q :=
      mul_le_mul ((hDh i).trans (mul_le_mul_of_nonneg_left (hDp i) hβ0)) (hq i) (abs_nonneg _) hβdp
    nlinarith
  have t2 : |(Dh i - D i) * (A *ᵥ pb) i| ≤ β * dp * (Real.sqrt 2 * (Pp + E)) := by
    rw [abs_mul]
    exact mul_le_mul ((hDh i).trans (mul_le_mul_of_nonneg_left (hDp i) hβ0))
      ((hrow pb i).trans (mul_le_mul_of_nonneg_left hpbn hs2)) (abs_nonneg _) hβdp
  have t3 : |D i * (A *ᵥ (pb - p0)) i| ≤ dp * (Real.sqrt 2 * (β * E)) := by
    rw [abs_mul, abs_of_pos (hD i)]
    exact mul_le_mul (hDp i) ((hrow _ i).trans (mul_le_mul_of_nonneg_left hEb hs2))
      (abs_nonneg _) hdp
  have := abs_add_le (-(Dh i * qh i - D i * q i) + (Dh i - D i) * (A *ᵥ pb) i)
    (D i * (A *ᵥ (pb - p0)) i)
  have := abs_add_le (-(Dh i * qh i - D i * q i)) ((Dh i - D i) * (A *ᵥ pb) i)
  rw [abs_neg] at this
  simp only [P₁]
  nlinarith


/-- The frozen Gram matrix keeps half of the lower envelope: `ℓ/2 ‖x‖² ≤ xᵀ L̂ x`. -/
theorem frozen_gram_lo {A : Matrix (Fin M) (Fin r) ℝ} {D Dh : Fin M → ℝ} {β ℓ : ℝ}
    (hD : ∀ i, 0 < D i) (hDh : ∀ i, |Dh i - D i| ≤ β * D i) (hβ : β ≤ 1 / 2)
    (hL : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (gram A D *ᵥ x)) (x : Fin r → ℝ) :
    ℓ / 2 * euc x ^ 2 ≤ x ⬝ᵥ (gram A Dh *ᵥ x) := by
  have hDh_lo : ∀ i, D i / 2 ≤ Dh i := fun i => by
    have := (abs_le.mp (hDh i)).1; nlinarith [hD i]
  have h1 := hL x
  rw [gram_quad] at h1 ⊢
  have : ∑ i, D i * (A *ᵥ x) i ^ 2 / 2 ≤ ∑ i, Dh i * (A *ᵥ x) i ^ 2 :=
    sum_le_sum fun i _ => by nlinarith [hDh_lo i, sq_nonneg ((A *ᵥ x) i)]
  rw [← sum_div] at this
  linarith

/-- The frozen Gram matrix's upper envelope: `xᵀ L̂ x ≤ (3/2) d₊ a² ‖x‖²`. -/
theorem frozen_gram_up {A : Matrix (Fin M) (Fin r) ℝ} {D Dh : Fin M → ℝ} {a dp β : ℝ}
    (hA : ∀ x, euc (A *ᵥ x) ≤ a * euc x) (hD : ∀ i, 0 < D i)
    (hDp : ∀ i, D i ≤ dp) (hdp : 0 ≤ dp) (hDh : ∀ i, |Dh i - D i| ≤ β * D i) (hβ : β ≤ 1 / 2)
    (x : Fin r → ℝ) :
    x ⬝ᵥ (gram A Dh *ᵥ x) ≤ 3 / 2 * dp * a ^ 2 * euc x ^ 2 := by
  have hDh_up : ∀ i, Dh i ≤ 3 / 2 * dp := fun i => by
    have := (abs_le.mp (hDh i)).2; nlinarith [hD i, hDp i]
  rw [gram_quad]
  have h1 : ∑ i, Dh i * (A *ᵥ x) i ^ 2 ≤ 3 / 2 * dp * euc (A *ᵥ x) ^ 2 := by
    rw [euc_sq, mul_sum]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hDh_up i) (sq_nonneg _)
  have h2 : euc (A *ᵥ x) ^ 2 ≤ (a * euc x) ^ 2 := pow_le_pow_left₀ (euc_nonneg _) (hA x) 2
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **Absolute accuracy of the frozen Newton direction** (`lem:numeric`). -/
theorem direction_error {A : Matrix (Fin M) (Fin r) ℝ} {D Dh q qh : Fin M → ℝ}
    {p0 ph pt pb : Fin r → ℝ} {a dp Q ℓ β : ℝ}
    (hA : ∀ x, euc (A *ᵥ x) ≤ a * euc x) (hAt : ∀ y, euc (Aᵀ *ᵥ y) ≤ a * euc y)
    (hrow : ∀ x i, |(A *ᵥ x) i| ≤ Real.sqrt 2 * euc x) (ha : 0 ≤ a)
    (hD : ∀ i, 0 < D i) (hDp : ∀ i, D i ≤ dp) (hdp : 0 ≤ dp)
    (hDh : ∀ i, |Dh i - D i| ≤ β * D i) (hq : ∀ i, |q i| ≤ Q) (hQ : 0 ≤ Q)
    (hqh : ∀ i, |qh i - q i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (hℓ : 0 < ℓ)
    (hL : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (gram A D *ᵥ x))
    (hp : gram A D *ᵥ p0 = Aᵀ *ᵥ fun i => D i * q i)
    (hph : gram A Dh *ᵥ ph = Aᵀ *ᵥ fun i => Dh i * qh i)
    (hpt : (pt - ph) ⬝ᵥ (gram A Dh *ᵥ (pt - ph)) ≤ β ^ 2 * (ph ⬝ᵥ (gram A Dh *ᵥ ph)))
    (hpb : ∀ j, |pb j - pt j| ≤ β) :
    let Pp := a * Real.sqrt M * dp * Q / ℓ
    let E₁ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pp)
    let E₂ := 2 * a * Real.sqrt (dp / ℓ) * (Pp + E₁)
    let E := E₁ + E₂ + Real.sqrt r
    let P₁ := dp * (Q + 2) + Real.sqrt 2 * dp * (Pp + E) + Real.sqrt 2 * dp * E
    ∀ i, |-Dh i * (qh i - (A *ᵥ pb) i) - -D i * (q i - (A *ᵥ p0) i)| ≤ P₁ * β := by
  intro Pp E₁ E₂ E P₁
  have hLh_lo := frozen_gram_lo (A := A) hD hDh hβ hL
  have hLh_up := frozen_gram_up hA hD hDp hdp hDh hβ
  -- `‖p̃ − p̂‖ ≤ 2a√(d₊/ℓ) β ‖p̂‖`
  have hΔt' : euc (pt - ph) ≤ β * (2 * a * Real.sqrt (dp / ℓ) * euc ph + 0) := by
    have hep := euc_nonneg ph
    have h1 := hLh_lo (pt - ph)
    have h2 := hLh_up ph
    have hX : 0 ≤ 2 * a * Real.sqrt (dp / ℓ) * β * euc ph := by positivity
    have hsq : euc (pt - ph) ^ 2 ≤ (2 * a * Real.sqrt (dp / ℓ) * β * euc ph) ^ 2 := by
      have hs : Real.sqrt (dp / ℓ) ^ 2 = dp / ℓ := Real.sq_sqrt (by positivity)
      have : (2 * a * Real.sqrt (dp / ℓ) * β * euc ph) ^ 2 = 4 * a ^ 2 * (dp / ℓ) * β ^ 2 * euc ph ^ 2 := by
        rw [show (2 * a * Real.sqrt (dp / ℓ) * β * euc ph) ^ 2 =
          4 * a ^ 2 * Real.sqrt (dp / ℓ) ^ 2 * β ^ 2 * euc ph ^ 2 by ring, hs]
      rw [this]
      have h3 : ℓ / 2 * euc (pt - ph) ^ 2 ≤ β ^ 2 * (3 / 2 * dp * a ^ 2 * euc ph ^ 2) :=
        h1.trans (hpt.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg β)))
      rw [show 4 * a ^ 2 * (dp / ℓ) * β ^ 2 * euc ph ^ 2 = (4 / ℓ) * (dp * a ^ 2 * β ^ 2 * euc ph ^ 2) by
        field_simp]
      have h4 : euc (pt - ph) ^ 2 ≤ (3 / ℓ) * (dp * a ^ 2 * β ^ 2 * euc ph ^ 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hℓ]; nlinarith
      have h5 : (3 / ℓ) * (dp * a ^ 2 * β ^ 2 * euc ph ^ 2) ≤ (4 / ℓ) * (dp * a ^ 2 * β ^ 2 * euc ph ^ 2) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hℓ.le) (by positivity)
      linarith
    have h6 := (abs_le_of_sq_le_sq' hsq hX).2
    linarith
  have h := direction_error_core hA hAt hrow ha hD hDp hdp hDh hq hQ hqh hβ0 hβ hℓ hL hp hph
    (by positivity) le_rfl hΔt' hpb
  simp only [add_zero] at h
  exact h

end

end ImplicitLP
end CutQueryComplexity
