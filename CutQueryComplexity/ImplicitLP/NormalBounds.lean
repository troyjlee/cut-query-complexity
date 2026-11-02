import CutQueryComplexity.ImplicitLP.Refine
import CutQueryComplexity.ImplicitLP.HiddenGram
import CutQueryComplexity.ImplicitLP.Barrier
import CutQueryComplexity.ImplicitLP.CenterClose

/-! # The normal-system envelope constants (`eq:normalbounds`, D7 item 5)

For `H = WS²`, `D = H⁻¹`, `L = AᵀDA` and `q = tc + Wφ'`:

* `Dᵢ ≤ U²/w_min` from `Sᵢ ≥ 1/U` (`normD_le`);
* `Dᵢ ≥ s_*²/(4 w_max)` from `Sᵢsᵢ ≤ 2` and `sᵢ ≥ s_*` (`normD_ge`);
* `|qᵢ| ≤ |t|‖c‖_∞ + w_max/s_*` from `|φᵢ'|sᵢ ≤ 1` (`normQ_le`);
* `L ⪰ (s_*²/(4w_max)) I` through the `+I_r` rows, and `L ⪯ 2M (U²/w_min) I` from row norms `≤ √2`.

`normalbounds_src` is the audited draft's `eq:normalbounds` under the audited draft's hypotheses `r/M ≤ w ≤ 4`.
`normalbounds_note` is the repaired version with `1/(4M̄) ≤ w ≤ 4`: then `d₊ = 4M̄U²`, and the
upper bound is `8MM̄U²` instead of `2M²U²/r`.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ}

/-- `D = (WS²)⁻¹`. -/
def normD (w S : Fin M → ℝ) : Fin M → ℝ := fun i => 1 / (w i * S i ^ 2)

/-- `q = tc + Wφ'`. -/
def normQ (t : ℝ) (c w dφ : Fin M → ℝ) : Fin M → ℝ := fun i => t * c i + w i * dφ i

section Scalar

variable {w S : Fin M → ℝ}

theorem normD_pos (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) (i : Fin M) : 0 < normD w S i := by
  have := hw i; have := hS i; unfold normD; positivity

/-- `Dᵢ ≤ U²/w_min`. -/
theorem normD_le {wmin U : ℝ} (hwmin : 0 < wmin) (hw : ∀ i, wmin ≤ w i) (hU : 0 < U)
    (hS : ∀ i, 1 / U ≤ S i) (i : Fin M) : normD w S i ≤ U ^ 2 / wmin := by
  have hS0 : 0 < S i := lt_of_lt_of_le (by positivity) (hS i)
  have hwi : 0 < w i := lt_of_lt_of_le hwmin (hw i)
  unfold normD
  rw [div_le_div_iff₀ (by positivity) hwmin, one_mul]
  have h1 : 1 ≤ U * S i := by have := hS i; rw [div_le_iff₀ hU] at this; linarith
  have h2 : 1 ≤ (U * S i) ^ 2 := one_le_pow₀ h1
  calc wmin ≤ w i := hw i
    _ ≤ w i * (U * S i) ^ 2 := le_mul_of_one_le_right hwi.le h2
    _ = U ^ 2 * (w i * S i ^ 2) := by ring

/-- `Dᵢ ≥ s_*²/(4 w_max)`. -/
theorem normD_ge {s : Fin M → ℝ} {wmax sst : ℝ} (hw : ∀ i, 0 < w i) (hwmax : ∀ i, w i ≤ wmax)
    (hS : ∀ i, 0 < S i) (hSs : ∀ i, S i * s i ≤ 2) (hsst : 0 < sst) (hs : ∀ i, sst ≤ s i)
    (i : Fin M) : sst ^ 2 / (4 * wmax) ≤ normD w S i := by
  have hwi := hw i; have hSi := hS i
  have hwm : 0 < wmax := hwi.trans_le (hwmax i)
  unfold normD
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h1 : sst * S i ≤ 2 := by nlinarith [hs i, hSs i]
  have h2 : (sst * S i) ^ 2 ≤ 4 := by nlinarith [mul_pos hsst hSi]
  calc sst ^ 2 * (w i * S i ^ 2) = w i * (sst * S i) ^ 2 := by ring
    _ ≤ wmax * 4 := mul_le_mul (hwmax i) h2 (sq_nonneg _) hwm.le
    _ = 4 * wmax := by ring

/-- `|qᵢ| ≤ |t|‖c‖_∞ + w_max/s_*`. -/
theorem normQ_le {c dφ s : Fin M → ℝ} {t wmax sst : ℝ} (hw : ∀ i, 0 < w i)
    (hwmax : ∀ i, w i ≤ wmax) (hdφ : ∀ i, |dφ i| * s i ≤ 1) (hsst : 0 < sst)
    (hs : ∀ i, sst ≤ s i) (i : Fin M) : |normQ t c w dφ i| ≤ |t| * ‖c‖ + wmax / sst := by
  have hwi := hw i
  have hwm : 0 < wmax := hwi.trans_le (hwmax i)
  unfold normQ
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c i)
      (abs_nonneg _)
  · rw [abs_mul, abs_of_pos hwi]
    have hsi : 0 < s i := hsst.trans_le (hs i)
    have h1 : |dφ i| ≤ 1 / sst := by
      rw [le_div_iff₀ hsst]
      exact (mul_le_mul_of_nonneg_left (hs i) (abs_nonneg _)).trans (hdφ i)
    calc w i * |dφ i| ≤ wmax * (1 / sst) := mul_le_mul (hwmax i) h1 (abs_nonneg _) hwm.le
      _ = wmax / sst := by ring

end Scalar

section Gram

variable {A : Matrix (Fin M) (Fin r) ℝ}

/-- `xᵀ(AᵀDA)x ≤ 2M d₊ ‖x‖²` when row norms are at most `√2` and `0 ≤ D ≤ d₊`. -/
theorem gram_le_of_rows (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {D : Fin M → ℝ} {dp : ℝ}
    (hD0 : ∀ i, 0 ≤ D i) (hDp : ∀ i, D i ≤ dp) (x : Fin r → ℝ) :
    x ⬝ᵥ (gram A D *ᵥ x) ≤ 2 * M * dp * euc x ^ 2 := by
  have hdp : 0 ≤ dp ∨ M = 0 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · exact Or.inr h
    · exact Or.inl ((hD0 ⟨0, h⟩).trans (hDp ⟨0, h⟩))
  rw [gram_quad]
  have h1 : ∑ i, D i * (A *ᵥ x) i ^ 2 ≤ dp * euc (A *ᵥ x) ^ 2 := by
    rw [euc_sq, mul_sum]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hDp i) (sq_nonneg _)
  rcases hdp with hdp | hM
  · have h2 := opnorm_le hrow x
    have h3 : euc (A *ᵥ x) ^ 2 ≤ (Real.sqrt (2 * M) * euc x) ^ 2 :=
      pow_le_pow_left₀ (euc_nonneg _) h2 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at h3
    nlinarith [mul_le_mul_of_nonneg_left h3 hdp]
  · subst hM; simp

end Gram

/-! ## The envelope at a barrier point -/

section Barrier

variable {A : Matrix (Fin M) (Fin r) ℝ} {κ m x w c : Fin M → ℝ} {t U : ℝ}

/-- The barrier facts used by the envelope: `U⁻¹ ≤ Sᵢ`, `Sᵢsᵢ ≤ 2`, `|φᵢ'|sᵢ ≤ 1`. -/
theorem barrier_env (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) (i : Fin M) :
    1 / U ≤ barS κ m x i ∧ barS κ m x i * slk κ m x i ≤ 2 ∧
      |barDphi κ m x i| * slk κ m x i ≤ 1 := by
  obtain ⟨-, h2, -, h4, h5⟩ := eq_barrier hκ hx i
  refine ⟨?_, h4, h2⟩
  have hk := hκ i
  have hU0 : 0 < U := by linarith
  have : 1 / U ≤ κ i := by
    rw [div_le_iff₀ hU0]
    have := hU i
    rw [div_le_iff₀ hk] at this
    nlinarith [Real.two_le_pi]
  exact this.trans h5

/-- **`eq:normalbounds`, general form.** At an interior point with box widths `≤ U`, weights
`w_min ≤ w ≤ w_max`, slacks `≥ s_*`, row norms `≤ √2` and the `+I_r` rows:
(a) `0 < Dᵢ ≤ U²/w_min`; (b) `L ⪰ s_*²/(4w_max)`; (c) `L ⪯ 2M U²/w_min`;
(d) `|qᵢ| ≤ |t|‖c‖_∞ + w_max/s_*`. -/
theorem normalbounds (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) {wmin wmax sst : ℝ} (hwmin : 0 < wmin) (hwlo : ∀ i, wmin ≤ w i)
    (hwhi : ∀ i, w i ≤ wmax) (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i)
    (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι) :
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    (∀ i, 0 < D i ∧ D i ≤ U ^ 2 / wmin) ∧
      (∀ y, sst ^ 2 / (4 * wmax) * euc y ^ 2 ≤ y ⬝ᵥ (gram A D *ᵥ y)) ∧
      (∀ y, y ⬝ᵥ (gram A D *ᵥ y) ≤ 2 * M * (U ^ 2 / wmin) * euc y ^ 2) ∧
      (∀ i, |q i| ≤ |t| * ‖c‖ + wmax / sst) := by
  intro D q
  have hU0 : 0 < U := by linarith
  have hw : ∀ i, 0 < w i := fun i => hwmin.trans_le (hwlo i)
  have hS : ∀ i, 0 < barS κ m x i := barS_pos hκ hx
  have henv := barrier_env hκ hx hU1 hU
  have hDpos := normD_pos hw hS
  have hDle := normD_le hwmin hwlo hU0 (fun i => (henv i).1)
  have hDge := normD_ge hw hwhi hS (fun i => (henv i).2.1) hsst hs
  refine ⟨fun i => ⟨hDpos i, hDle i⟩, fun y => ?_, fun y => ?_, fun i => ?_⟩
  · exact gram_ge_of_idRows hι (fun i => (hDpos i).le) (fun j => hDge (ι j)) y
  · exact gram_le_of_rows hrow (fun i => (hDpos i).le) hDle y
  · exact normQ_le hw hwhi (fun i => (henv i).2.2) hsst hs i

/-- **`eq:normalbounds` as stated in the audited draft** (weights `r/M ≤ w ≤ 4`, `|t| ≤ 16r/ε`,
`‖c‖_∞ ≤ 4U`): `s_*²/16 · I ⪯ L ⪯ (2M²U²/r) I`, `‖D‖ ≤ MU²/r`, `‖q‖_∞ ≤ 64rU/ε + 4/s_*`. -/
theorem normalbounds_src (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) (hr : 0 < r) (hwlo : ∀ i, (r : ℝ) / M ≤ w i) (hwhi : ∀ i, w i ≤ 4)
    {sst ε : ℝ} (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε)
    (ht : |t| ≤ 16 * r / ε) (hc : ‖c‖ ≤ 4 * U)
    (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι) :
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    (∀ i, 0 < D i ∧ D i ≤ M * U ^ 2 / r) ∧
      (∀ y, sst ^ 2 / 16 * euc y ^ 2 ≤ y ⬝ᵥ (gram A D *ᵥ y)) ∧
      (∀ y, y ⬝ᵥ (gram A D *ᵥ y) ≤ 2 * M ^ 2 * U ^ 2 / r * euc y ^ 2) ∧
      (∀ i, |q i| ≤ 64 * r * U / ε + 4 / sst) := by
  intro D q
  have hM : 0 < M := Fin.pos (ι ⟨0, hr⟩)
  have hwmin : (0 : ℝ) < r / M := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := normalbounds (t := t) (c := c) hκ hx hU1 hU hwmin hwlo hwhi hsst hs
    hrow hι
  have hU0 : 0 < U := by linarith
  have e1 : U ^ 2 / ((r : ℝ) / M) = M * U ^ 2 / r := by field_simp
  refine ⟨fun i => ⟨(h1 i).1, (h1 i).2.trans_eq e1⟩, fun y => ?_, fun y => ?_, fun i => ?_⟩
  · have := h2 y; norm_num at this ⊢; linarith
  · have := h3 y; rw [e1] at this
    calc _ ≤ _ := this
      _ = _ := by field_simp
  · refine (h4 i).trans (add_le_add ?_ le_rfl)
    calc |t| * ‖c‖ ≤ 16 * r / ε * (4 * U) := mul_le_mul ht hc (norm_nonneg _) (by positivity)
      _ = 64 * r * U / ε := by ring

/-- **`eq:normalbounds` with the repaired weight floor** (`1/(4M̄) ≤ w ≤ 4`): `d₊ = 4M̄U²`, so
`s_*²/16 · I ⪯ L ⪯ 8MM̄U² I`, `‖D‖ ≤ 4M̄U²`, `‖q‖_∞ ≤ 64rU/ε + 4/s_*`. -/
theorem normalbounds_note (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) {Mbar : ℝ} (hMbar : 0 < Mbar) (hwlo : ∀ i, 1 / (4 * Mbar) ≤ w i)
    (hwhi : ∀ i, w i ≤ 4) {sst ε : ℝ} (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i)
    (hε : 0 < ε) (ht : |t| ≤ 16 * r / ε) (hc : ‖c‖ ≤ 4 * U)
    (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι) :
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    (∀ i, 0 < D i ∧ D i ≤ 4 * Mbar * U ^ 2) ∧
      (∀ y, sst ^ 2 / 16 * euc y ^ 2 ≤ y ⬝ᵥ (gram A D *ᵥ y)) ∧
      (∀ y, y ⬝ᵥ (gram A D *ᵥ y) ≤ 8 * M * Mbar * U ^ 2 * euc y ^ 2) ∧
      (∀ i, |q i| ≤ 64 * r * U / ε + 4 / sst) := by
  intro D q
  have hwmin : (0 : ℝ) < 1 / (4 * Mbar) := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := normalbounds (t := t) (c := c) hκ hx hU1 hU hwmin hwlo hwhi hsst hs
    hrow hι
  have e1 : U ^ 2 / (1 / (4 * Mbar)) = 4 * Mbar * U ^ 2 := by field_simp
  refine ⟨fun i => ⟨(h1 i).1, (h1 i).2.trans_eq e1⟩, fun y => ?_, fun y => ?_, fun i => ?_⟩
  · have := h2 y; norm_num at this ⊢; linarith
  · have := h3 y; rw [e1] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  · refine (h4 i).trans (add_le_add ?_ le_rfl)
    calc |t| * ‖c‖ ≤ 16 * r / ε * (4 * U) := mul_le_mul ht hc (norm_nonneg _) (by positivity)
      _ = 64 * r * U / ε := by ring

end Barrier

/-! ## The audited draft's explicit polynomial `P₁`

The audited draft bounds `‖π̂‖₂` directly by `P_π = 4a√M d₊(Q+1)/ℓ` (from `L̂ ⪰ ℓ/2`, `D̂ ≤ 3d₊/2`,
`|q̂| ≤ Q + 1/2`) and decomposes
`h̃ − h = −(D̂ − D)(q − Aπ) − D̂(q̂ − q) + D̂A(π̄ − π)`. This gives the audited draft's
`E_π` and `P₁` verbatim. It is a different (and smaller in the condition number) chain from the
repository's `direction_error`, whose `E₂` multiplies `E₁` by `√(cond)` again. -/

section NoteForm

variable {A : Matrix (Fin M) (Fin r) ℝ}

set_option maxHeartbeats 1600000 in
/-- **`lem:numeric` with the audited draft's `P_π`, `E_π`, `P₁`**, from an absolute frozen-solve bound
`‖π̃ − π̂‖₂ ≤ β(c₂‖π̂‖₂ + c₃)`. -/
theorem direction_error_note_core {D Dh q qh : Fin M → ℝ}
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
    let Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) + (c₂ * Pπ + c₃) +
      Real.sqrt r
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    ∀ i, |-Dh i * (qh i - (A *ᵥ pb) i) - -D i * (q i - (A *ᵥ p0) i)| ≤ P₁ * β := by
  intro Pπ Eπ P₁
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hDh_lo : ∀ i, D i / 2 ≤ Dh i := fun i => by
    have := (abs_le.mp (hDh i)).1; nlinarith [hD i]
  have hDh_up : ∀ i, Dh i ≤ 3 / 2 * dp := fun i => by
    have := (abs_le.mp (hDh i)).2; nlinarith [hD i, hDp i]
  have hDh0 : ∀ i, 0 ≤ Dh i := fun i => by linarith [hDh_lo i, hD i]
  have hLh_lo := frozen_gram_lo (A := A) hD hDh hβ hL
  have hPπ : 0 ≤ Pπ := by simp only [Pπ]; positivity
  -- `‖π‖ ≤ a√M d₊ Q/ℓ ≤ P_π`
  set Pp := a * Real.sqrt M * dp * Q / ℓ with hPp_def
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
  have hPpπ : Pp ≤ Pπ := by
    simp only [Pp, Pπ]
    apply div_le_div_of_nonneg_right _ hℓ.le
    have : 0 ≤ a * Real.sqrt M * dp := by positivity
    nlinarith
  have hPp : 0 ≤ Pp := (euc_nonneg p0).trans hpn
  -- `‖π̂‖ ≤ P_π`, directly from the frozen system
  have hphn : euc ph ≤ Pπ := by
    have h1 := solve_bound (by positivity) hLh_lo hph
    have h2 : euc (fun i => Dh i * qh i) ≤ Real.sqrt M * (2 * dp * (Q + 1)) :=
      euc_le_sqrt_card_mul (by positivity) fun i => by
        rw [abs_mul, abs_of_nonneg (hDh0 i)]
        have hq1 : |qh i| ≤ Q + 1 / 2 := by
          have := abs_sub_abs_le_abs_sub (qh i) (q i); linarith [hqh i, hq i]
        calc Dh i * |qh i| ≤ 3 / 2 * dp * (Q + 1 / 2) :=
              mul_le_mul (hDh_up i) hq1 (abs_nonneg _) (by positivity)
          _ ≤ 2 * dp * (Q + 1) := by nlinarith
    have h3 := hAt (fun i => Dh i * qh i)
    calc euc ph ≤ euc (Aᵀ *ᵥ fun i => Dh i * qh i) / (ℓ / 2) := h1
      _ ≤ a * (Real.sqrt M * (2 * dp * (Q + 1))) / (ℓ / 2) :=
          div_le_div_of_nonneg_right (h3.trans (mul_le_mul_of_nonneg_left h2 ha)) (by positivity)
      _ = Pπ := by simp only [Pπ]; field_simp; ring
  -- `‖π̂ − π‖ ≤ β E₁`
  set E₁ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) with hE₁_def
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
  have hu2 : euc (fun i => (Dh i - D i) * (A *ᵥ p0) i) ≤ β * dp * (a * Pπ) := by
    refine (euc_le_of_abs_le hβdp fun i => ?_).trans
      (mul_le_mul_of_nonneg_left ((hA p0).trans (mul_le_mul_of_nonneg_left
        (hpn.trans hPpπ) ha)) hβdp)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((hDh i).trans (mul_le_mul_of_nonneg_left (hDp i) hβ0))
      (abs_nonneg _)
  have hyb : euc y ≤ β * (Real.sqrt M * dp * (Q + 2) + dp * a * Pπ) := by
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
      _ ≤ a * (β * (Real.sqrt M * dp * (Q + 2) + dp * a * Pπ)) / (ℓ / 2) :=
          div_le_div_of_nonneg_right (h2.trans (mul_le_mul_of_nonneg_left hyb ha)) (by positivity)
      _ = β * E₁ := by simp only [E₁]; field_simp
  -- `‖π̃ − π̂‖ ≤ β(c₂P_π + c₃)`, `‖π̄ − π̃‖ ≤ √r β`, so `‖π̄ − π‖ ≤ βE_π`
  have hΔt : euc (pt - ph) ≤ β * (c₂ * Pπ + c₃) := hΔt'.trans (mul_le_mul_of_nonneg_left
      (by nlinarith [mul_le_mul_of_nonneg_left hphn hc₂]) hβ0)
  have hΔb : euc (pb - pt) ≤ Real.sqrt r * β := euc_le_sqrt_card_mul hβ0 hpb
  have hEb : euc (pb - p0) ≤ β * Eπ := by
    have h1 := euc_add_le (pb - pt) ((pt - ph) + (ph - p0))
    have h2 := euc_add_le (pt - ph) (ph - p0)
    rw [show pb - pt + (pt - ph + (ph - p0)) = pb - p0 by abel] at h1
    simp only [Eπ]; nlinarith
  -- the coordinate error
  intro i
  have hdecomp : -Dh i * (qh i - (A *ᵥ pb) i) - -D i * (q i - (A *ᵥ p0) i) =
      -((Dh i - D i) * (q i - (A *ᵥ p0) i)) - Dh i * (qh i - q i) +
        Dh i * (A *ᵥ (pb - p0)) i := by
    rw [mulVec_sub, Pi.sub_apply]; ring
  rw [hdecomp]
  have t1 : |(Dh i - D i) * (q i - (A *ᵥ p0) i)| ≤ β * dp * (Q + Real.sqrt 2 * Pπ) := by
    rw [abs_mul]
    refine mul_le_mul ((hDh i).trans (mul_le_mul_of_nonneg_left (hDp i) hβ0)) ?_
      (abs_nonneg _) hβdp
    refine (abs_sub _ _).trans (add_le_add (hq i) ?_)
    exact (hrow p0 i).trans (mul_le_mul_of_nonneg_left (hpn.trans hPpπ) hs2)
  have t2 : |Dh i * (qh i - q i)| ≤ 2 * dp * β := by
    rw [abs_mul, abs_of_nonneg (hDh0 i)]
    calc Dh i * |qh i - q i| ≤ 3 / 2 * dp * β :=
          mul_le_mul (hDh_up i) (hqh i) (abs_nonneg _) (by positivity)
      _ ≤ 2 * dp * β := by nlinarith
  have hEπ0 : 0 ≤ Eπ := by simp only [Eπ]; positivity
  have t3 : |Dh i * (A *ᵥ (pb - p0)) i| ≤ 2 * dp * (Real.sqrt 2 * Eπ) * β := by
    rw [abs_mul, abs_of_nonneg (hDh0 i)]
    calc Dh i * |(A *ᵥ (pb - p0)) i| ≤ 3 / 2 * dp * (Real.sqrt 2 * (β * Eπ)) :=
          mul_le_mul (hDh_up i) ((hrow _ i).trans (mul_le_mul_of_nonneg_left hEb hs2))
            (abs_nonneg _) (by positivity)
      _ ≤ 2 * dp * (Real.sqrt 2 * Eπ) * β := by
          have : 0 ≤ dp * (Real.sqrt 2 * Eπ) * β := by positivity
          nlinarith
  have k1 := abs_add_le (-((Dh i - D i) * (q i - (A *ᵥ p0) i)) - Dh i * (qh i - q i))
    (Dh i * (A *ᵥ (pb - p0)) i)
  have k2 := abs_sub (-((Dh i - D i) * (q i - (A *ᵥ p0) i))) (Dh i * (qh i - q i))
  rw [abs_neg] at k2
  simp only [P₁]
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **`lem:numeric` with the audited draft's polynomial, verbatim.** Relative energy error `β` for the
frozen solve: `‖π̃ − π̂‖_{L̂} ≤ β‖π̂‖_{L̂}`. Then `‖h̃ − h‖_∞ ≤ P₁β` with
`P_π = 4a√M d₊(Q+1)/ℓ`,
`E_π = (2/ℓ)(a√M d₊(Q+2) + a²d₊P_π) + 2a√(d₊/ℓ)P_π + √r`,
`P₁ = d₊(Q + √2P_π) + 2d₊(1 + √2E_π)`. -/
theorem direction_error_note {D Dh q qh : Fin M → ℝ}
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
    let Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      2 * a * Real.sqrt (dp / ℓ) * Pπ + Real.sqrt r
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    ∀ i, |-Dh i * (qh i - (A *ᵥ pb) i) - -D i * (q i - (A *ᵥ p0) i)| ≤ P₁ * β := by
  intro Pπ Eπ P₁
  have hLh_lo := frozen_gram_lo (A := A) hD hDh hβ hL
  have hLh_up := frozen_gram_up hA hD hDp hdp hDh hβ
  have hΔt' : euc (pt - ph) ≤ β * (2 * a * Real.sqrt (dp / ℓ) * euc ph + 0) := by
    have hep := euc_nonneg ph
    have h1 := hLh_lo (pt - ph)
    have h2 := hLh_up ph
    have hX : 0 ≤ 2 * a * Real.sqrt (dp / ℓ) * β * euc ph := by positivity
    have hsq : euc (pt - ph) ^ 2 ≤ (2 * a * Real.sqrt (dp / ℓ) * β * euc ph) ^ 2 := by
      have hs : Real.sqrt (dp / ℓ) ^ 2 = dp / ℓ := Real.sq_sqrt (by positivity)
      have : (2 * a * Real.sqrt (dp / ℓ) * β * euc ph) ^ 2 =
          4 * a ^ 2 * (dp / ℓ) * β ^ 2 * euc ph ^ 2 := by
        rw [show (2 * a * Real.sqrt (dp / ℓ) * β * euc ph) ^ 2 =
          4 * a ^ 2 * Real.sqrt (dp / ℓ) ^ 2 * β ^ 2 * euc ph ^ 2 by ring, hs]
      rw [this]
      have h3 : ℓ / 2 * euc (pt - ph) ^ 2 ≤ β ^ 2 * (3 / 2 * dp * a ^ 2 * euc ph ^ 2) :=
        h1.trans (hpt.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg β)))
      rw [show 4 * a ^ 2 * (dp / ℓ) * β ^ 2 * euc ph ^ 2 =
        (4 / ℓ) * (dp * a ^ 2 * β ^ 2 * euc ph ^ 2) by field_simp]
      have h4 : euc (pt - ph) ^ 2 ≤ (3 / ℓ) * (dp * a ^ 2 * β ^ 2 * euc ph ^ 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hℓ]; nlinarith
      have h5 : (3 / ℓ) * (dp * a ^ 2 * β ^ 2 * euc ph ^ 2) ≤
          (4 / ℓ) * (dp * a ^ 2 * β ^ 2 * euc ph ^ 2) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hℓ.le) (by positivity)
      linarith
    have h6 := (abs_le_of_sq_le_sq' hsq hX).2
    linarith
  have h := direction_error_note_core hA hAt hrow ha hD hDp hdp hDh hq hQ hqh hβ0 hβ hℓ hL hp hph
    (by positivity) le_rfl hΔt' hpb
  simp only [add_zero] at h
  exact h

set_option maxHeartbeats 1600000 in
/-- **The audited draft's polynomial from an additive energy-norm bound**
`‖π̃ − π̂‖_{L̂} ≤ β(‖π̂‖_{L̂} + 1)` (what D4's refinement with rounding gives). Same `P_π`, `P₁`
as the audited draft; `E_π` has `c₂ = √(2/ℓ)√(3d₊/2)a ≤ 2a√(d₊/ℓ)` and the extra additive `√(2/ℓ)`. -/
theorem direction_error_abs_note {D Dh q qh : Fin M → ℝ}
    {p0 ph pt pb : Fin r → ℝ} {a dp Q ℓ β : ℝ}
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
    let Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt r
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    ∀ i, |-Dh i * (qh i - (A *ᵥ pb) i) - -D i * (q i - (A *ᵥ p0) i)| ≤ P₁ * β := by
  have hlo := frozen_gram_lo (A := A) hD hDh hβ hL
  have hup := frozen_gram_up hA hD hDp hdp hDh hβ
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
  exact direction_error_note_core hA hAt hrow ha hD hDp hdp hDh hq hQ hqh hβ0 hβ hℓ hL hp hph
    (by positivity) (Real.sqrt_nonneg _) hΔt' hpb

/-- `√(2/ℓ)·√(3d₊/2)·a ≤ 2a√(d₊/ℓ)`: the additive form's `c₂` is at most the audited draft's. -/
theorem abs_c2_le {a dp ℓ : ℝ} (ha : 0 ≤ a) (hℓ : 0 < ℓ) :
    Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) ≤ 2 * a * Real.sqrt (dp / ℓ) := by
  have e : Real.sqrt (2 / ℓ) * Real.sqrt (3 / 2 * dp) = Real.sqrt 3 * Real.sqrt (dp / ℓ) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by norm_num)]
    congr 1; field_simp
  have h3 : Real.sqrt 3 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a)
      = a * (Real.sqrt 3 * Real.sqrt (dp / ℓ)) := by rw [← e]; ring
    _ ≤ a * (2 * Real.sqrt (dp / ℓ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)) ha
    _ = 2 * a * Real.sqrt (dp / ℓ) := by ring

open Spectral in
set_option maxHeartbeats 1600000 in
/-- **The LP's Newton direction from D4's output, with the audited draft's `P_π` and `P₁`.** As
`lp_direction_error`, with the conclusion in the audited draft's form (`direction_error_abs_note`). -/
theorem lp_direction_error_note {D Dh q qh : Fin M → ℝ}
    {p0 ph pb : Fin r → ℝ} {a dp Q ℓ β : ℝ}
    (hA : ∀ x, euc (A *ᵥ x) ≤ a * euc x) (hAt : ∀ y, euc (Aᵀ *ᵥ y) ≤ a * euc y)
    (hrowA : ∀ x i, |(A *ᵥ x) i| ≤ Real.sqrt 2 * euc x) (ha : 0 ≤ a)
    (hD : ∀ i, 0 < D i) (hDp : ∀ i, D i ≤ dp) (hdp : 0 ≤ dp)
    (hDh : ∀ i, |Dh i - D i| ≤ β * D i) (hq : ∀ i, |q i| ≤ Q) (hQ : 0 ≤ Q)
    (hqh : ∀ i, |qh i - q i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (hℓ : 0 < ℓ)
    (hL : ∀ x, ℓ * euc x ^ 2 ≤ x ⬝ᵥ (gram A D *ᵥ x))
    (hp : gram A D *ᵥ p0 = Aᵀ *ᵥ fun i => D i * q i)
    (hph : gram A Dh *ᵥ ph = Aᵀ *ᵥ fun i => Dh i * qh i)
    {hid : Fin M → Option (Sym2 (Fin r))} {G : DiGraph (Fin r)} {w : Sym2 (Fin r) → ℝ}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hDw : ∀ i e, hid i = some e → Dh i = w e)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {ι : Fin r → Fin M} (hι : IdRows A ι) (hιe : ∀ j, hid (ι j) = none) {dmin : ℝ}
    (hdmin : 0 < dmin) (hDι : ∀ j, dmin ≤ Dh (ι j)) (hw0 : ∀ e, 0 ≤ w e)
    {K t R : ℕ} {δ ε : ℝ} {out : Sym2 (Fin r) → ℝ} (hgood : Sparsify.Good G w K t δ R out)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    (x : ℕ → Fin r → ℝ) (hx0 : x 0 = 0) {τ : ℝ} (hτ : 0 ≤ τ) (hτβ : 2 * τ ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β)
    (herr : ∀ j, enorm (gram A Dh) (x (j + 1) - (x j + (lap out univ + explicitGram A Dh hid)⁻¹ *ᵥ
      ((Aᵀ *ᵥ fun i => Dh i * qh i) - gram A Dh *ᵥ x j))) ≤ τ)
    (hpb : ∀ j, |pb j - x k j| ≤ β) :
    let Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt r
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
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
  exact direction_error_abs_note hA hAt hrowA ha hD hDp hdp hDh hq hQ hqh hβ0 hβ hℓ hL hp hph
    hpt hpb

end NoteForm

/-! ## Instantiation at a barrier point and the exact repair -/

section Instance

variable {A : Matrix (Fin M) (Fin r) ℝ} {κ m x w c : Fin M → ℝ} {t U : ℝ}

/-- The exact Newton direction `h = −D(q − Aπ)` is feasible and satisfies
`qᵢ + wᵢSᵢ²hᵢ = (Aπ)ᵢ`, the form used by `eq_projection_note`. -/
theorem exact_dir_spec {w S q : Fin M → ℝ} (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    {p0 : Fin r → ℝ} (hp : gram A (normD w S) *ᵥ p0 = Aᵀ *ᵥ fun i => normD w S i * q i) :
    let h : Fin M → ℝ := fun i => -normD w S i * (q i - (A *ᵥ p0) i)
    Aᵀ *ᵥ h = 0 ∧ ∀ i, q i + w i * S i ^ 2 * h i = (A *ᵥ p0) i := by
  intro h
  refine ⟨?_, fun i => ?_⟩
  · have e : h = (fun i => normD w S i * (A *ᵥ p0) i) - fun i => normD w S i * q i := by
      funext i; simp only [h, Pi.sub_apply]; ring
    rw [e, mulVec_sub, ← gram_mulVec_eq, hp, sub_self]
  · have := hw i; have := hS i
    simp only [h, normD]
    field_simp
    ring

theorem abs_entry_le_of_rows (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ 2) (i : Fin M) (j : Fin r) :
    |A i j| ≤ Real.sqrt 2 := by
  apply Real.abs_le_sqrt
  exact (single_le_sum (f := fun j => A i j ^ 2) (fun j _ => sq_nonneg _) (mem_univ j)).trans
    (hrow i)

set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` at a barrier point with explicit constants.** Weights
`w_min ≤ w ≤ 4` with `Σw ≤ 4r`; slacks `≥ s_*`; `|t| ≤ 16r/ε`, `‖c‖_∞ ≤ 4U`; row norms `≤ √2`
and the `+I_r` rows. Take any `d₊ ≥ U²/w_min`, `ℓ_* = s_*²/16`, `a = √(2M)`,
`Q = 64rU/ε + 4/s_*`, and the audited draft's `P_π, E_π, P₁`. Freezing `D, q` to precision `β ≤ 1/2`,
solving to relative energy error `β` and rounding to coordinate error `β` gives
`‖h̃ − h‖_∞ ≤ P₁β`. The repaired `d = h̃ − R_*Aᵀh̃` satisfies `Aᵀd = 0` and
`N_w(S(d − h)) ≤ (2T₀/s_*)(1 + √2M)P₁β` with `T₀ = 1 + 2C⌈√r⌉`. -/
theorem lem_numeric_env (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) {wmin dp : ℝ} (hwmin : 0 < wmin) (hwlo : ∀ i, wmin ≤ w i)
    (hdp : U ^ 2 / wmin ≤ dp) (hwhi : ∀ i, w i ≤ 4) (hwsum : ∑ i, w i ≤ 4 * r) {sst ε : ℝ} (hsst : 0 < sst)
    (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * r / ε) (hc : ‖c‖ ≤ 4 * U)
    (hrowA : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι)
    {Dh qh : Fin M → ℝ} {p0 ph pt pb : Fin r → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |Dh i - normD w (barS κ m x) i| ≤ β * normD w (barS κ m x) i)
    (hqh : ∀ i, |qh i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hp : gram A (normD w (barS κ m x)) *ᵥ p0 =
      Aᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    (hph : gram A Dh *ᵥ ph = Aᵀ *ᵥ fun i => Dh i * qh i)
    (hpt : (pt - ph) ⬝ᵥ (gram A Dh *ᵥ (pt - ph)) ≤ β ^ 2 * (ph ⬝ᵥ (gram A Dh *ᵥ ph)))
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
      2 * a * Real.sqrt (dp / ℓ) * Pπ + Real.sqrt r
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
  have hcoord := direction_error_note (opnorm_le hrowA) (opnorm_transpose_le hrowA)
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

set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` with the repaired constants.** Weights `1/(4M̄) ≤ w ≤ 4`, so `d₊ = 4M̄U²`
(the audited draft's `d₊ = MU²/r` assumed `w ≥ r/M`). -/
theorem lem_numeric_note (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) {Mbar : ℝ} (hMbar : 0 < Mbar) (hwlo : ∀ i, 1 / (4 * Mbar) ≤ w i)
    (hwhi : ∀ i, w i ≤ 4) (hwsum : ∑ i, w i ≤ 4 * r) {sst ε : ℝ} (hsst : 0 < sst)
    (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * r / ε) (hc : ‖c‖ ≤ 4 * U)
    (hrowA : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι)
    {Dh qh : Fin M → ℝ} {p0 ph pt pb : Fin r → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |Dh i - normD w (barS κ m x) i| ≤ β * normD w (barS κ m x) i)
    (hqh : ∀ i, |qh i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hp : gram A (normD w (barS κ m x)) *ᵥ p0 =
      Aᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    (hph : gram A Dh *ᵥ ph = Aᵀ *ᵥ fun i => Dh i * qh i)
    (hpt : (pt - ph) ⬝ᵥ (gram A Dh *ᵥ (pt - ph)) ≤ β ^ 2 * (ph ⬝ᵥ (gram A Dh *ᵥ ph)))
    (hpb : ∀ j, |pb j - pt j| ≤ β) :
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let h : Fin M → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin M → ℝ := fun i => -Dh i * (qh i - (A *ᵥ pb) i)
    let dp := 4 * Mbar * U ^ 2
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * M)
    let Q := 64 * r * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      2 * a * Real.sqrt (dp / ℓ) * Pπ + Real.sqrt r
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt r⌉₊ : ℝ)
    ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ repairDir A ι ht' = 0 ∧
      mixed C w (fun i => barS κ m x i * (repairDir A ι ht' - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * M) * P₁ * β :=
  lem_numeric_env hκ hx hU1 hU (by positivity) hwlo (by field_simp; rfl) hwhi hwsum hsst hs hε
    ht hc hrowA hι hC hDh hqh hβ0 hβ hp hph hpt hpb

set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` with the audited draft's hypotheses** (`r/M ≤ w ≤ 4`) and its `d₊ = MU²/r`. -/
theorem lem_numeric_src (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, π / κ i ≤ U) (hr : 0 < r) (hwlo : ∀ i, (r : ℝ) / M ≤ w i)
    (hwhi : ∀ i, w i ≤ 4) (hwsum : ∑ i, w i ≤ 4 * r) {sst ε : ℝ} (hsst : 0 < sst)
    (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * r / ε) (hc : ‖c‖ ≤ 4 * U)
    (hrowA : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι)
    {Dh qh : Fin M → ℝ} {p0 ph pt pb : Fin r → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |Dh i - normD w (barS κ m x) i| ≤ β * normD w (barS κ m x) i)
    (hqh : ∀ i, |qh i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hp : gram A (normD w (barS κ m x)) *ᵥ p0 =
      Aᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    (hph : gram A Dh *ᵥ ph = Aᵀ *ᵥ fun i => Dh i * qh i)
    (hpt : (pt - ph) ⬝ᵥ (gram A Dh *ᵥ (pt - ph)) ≤ β ^ 2 * (ph ⬝ᵥ (gram A Dh *ᵥ ph)))
    (hpb : ∀ j, |pb j - pt j| ≤ β) :
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let h : Fin M → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin M → ℝ := fun i => -Dh i * (qh i - (A *ᵥ pb) i)
    let dp := M * U ^ 2 / r
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * M)
    let Q := 64 * r * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt M * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      2 * a * Real.sqrt (dp / ℓ) * Pπ + Real.sqrt r
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt r⌉₊ : ℝ)
    ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ repairDir A ι ht' = 0 ∧
      mixed C w (fun i => barS κ m x i * (repairDir A ι ht' - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * M) * P₁ * β := by
  have hM : 0 < M := Fin.pos (ι ⟨0, hr⟩)
  exact lem_numeric_env hκ hx hU1 hU (by positivity) hwlo (by field_simp; rfl) hwhi hwsum hsst
    hs hε ht hc hrowA hι hC hDh hqh hβ0 hβ hp hph hpt hpb

end Instance

end

end ImplicitLP
end CutQueryComplexity
