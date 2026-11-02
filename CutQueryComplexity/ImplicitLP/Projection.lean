import CutQueryComplexity.ImplicitLP.LewisDeriv
import CutQueryComplexity.ImplicitLP.Movement
import CutQueryComplexity.ImplicitLP.GMove
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Regularized sensitivity and the projection bound (repair of gap G1 of the Lee–Sidford audit)

Lee–Sidford Theorem 29 claims `c_s(g) ≤ 2m^{1−p}` for `g = w_p + c₀`. Its proof applies a bound
for exact Lewis weights to `g`, and it also miscomputes an exponent (audit G10), so the claim
fails even for `c₀ = 0`. The repair (audit §3 F3) replaces it with two lemmas.

* **Lemma S** (`sens_regLewis`): for Lewis weights `w` with `0 < p ≤ 1`, `α = 2/p − 2`,
  `0 < ε < 1` and `0 ≤ c ≤ ε/M`, put `g = w + c`. Then every row satisfies
  `g_i⁻² aᵢᵀ (Aᵀ G⁻¹ A)⁻¹ aᵢ ≤ (2/(1−ε)) (M/ε)^α`. The proof splits rows into light
  (`wⱼ ≤ ε/M`) and heavy, as in Lee–Sidford Lemma 28.
* **Lemma 13′** (`proj_mixed_bound`): with `Q = W⁻¹A(AᵀW⁻¹A)⁻¹Aᵀ`, the `w`-orthogonal
  projection onto the range of `W⁻¹A`, and `qᵢ = (QW⁻¹)ᵢᵢ ≤ q`, every `y` satisfies
  `N_w(y − Qy) ≤ √(1 + q/C²) N_w(y)`. This follows from Pythagoras in `⟨·,·⟩_w` and
  `|(Qy)ᵢ| ≤ √q ‖Qy‖_w`. It sharpens Lee–Sidford Lemma 13, which has `1 + √q/C`.

Both use the Cauchy–Schwarz inequality `(bᵀy)² ≤ (bᵀG⁻¹b)(yᵀGy)` (`sq_dot_le_invQuad_mul`),
which follows from the variational formula.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ}

/-- **Cauchy–Schwarz in the `G`-metric:** `(bᵀy)² ≤ (bᵀG⁻¹b)(yᵀGy)`. -/
theorem sq_dot_le_invQuad_mul {G : Matrix (Fin r) (Fin r) ℝ} (hG : Gᵀ = G)
    (hpsd : ∀ y, 0 ≤ y ⬝ᵥ (G *ᵥ y)) (hdet : G.det ≠ 0) (b y : Fin r → ℝ) :
    (b ⬝ᵥ y) ^ 2 ≤ (b ⬝ᵥ (G⁻¹ *ᵥ b)) * (y ⬝ᵥ (G *ᵥ y)) := by
  have hq := hpsd y
  have hb : 0 ≤ b ⬝ᵥ (G⁻¹ *ᵥ b) := by
    have := variational_le hG hpsd hdet b 0
    simpa using this
  rcases eq_or_lt_of_le hq with h0 | hpos
  · -- `yᵀGy = 0` forces `bᵀy = 0`
    have : ∀ t : ℝ, 2 * t * (b ⬝ᵥ y) ≤ b ⬝ᵥ (G⁻¹ *ᵥ b) := fun t => by
      have := variational_le hG hpsd hdet b (t • y)
      simp only [dotProduct_smul, mulVec_smul, smul_dotProduct, smul_eq_mul, ← h0] at this
      linarith
    have hby : b ⬝ᵥ y = 0 := by
      by_contra hne
      have := this ((b ⬝ᵥ (G⁻¹ *ᵥ b) + 1) / (2 * (b ⬝ᵥ y)))
      field_simp at this
      linarith
    rw [hby, ← h0]; simp
  · set t := (b ⬝ᵥ y) / (y ⬝ᵥ (G *ᵥ y))
    have := variational_le hG hpsd hdet b (t • y)
    simp only [dotProduct_smul, mulVec_smul, smul_dotProduct, smul_eq_mul] at this
    have e : 2 * (t * (b ⬝ᵥ y)) - t * (t * (y ⬝ᵥ (G *ᵥ y))) =
        (b ⬝ᵥ y) ^ 2 / (y ⬝ᵥ (G *ᵥ y)) := by
      simp only [t]; field_simp; ring
    rw [e, div_le_iff₀ hpos] at this
    linarith

section Pythagoras

variable {A : Matrix (Fin M) (Fin r) ℝ} {w : Fin M → ℝ}

/-- The `w`-orthogonal projection `Q = W⁻¹A(AᵀW⁻¹A)⁻¹Aᵀ` onto the range of `W⁻¹A`. -/
def projW (A : Matrix (Fin M) (Fin r) ℝ) (w : Fin M → ℝ) (y : Fin M → ℝ) : Fin M → ℝ :=
  fun i => (A *ᵥ ((gram A (fun j => 1 / w j))⁻¹ *ᵥ (Aᵀ *ᵥ y))) i / w i

theorem wnorm_sq_projW (hA : (Aᵀ * A).det ≠ 0) (hw : ∀ i, 0 < w i) (y : Fin M → ℝ) :
    let z := (gram A (fun j => 1 / w j))⁻¹ *ᵥ (Aᵀ *ᵥ y)
    (∑ i, w i * projW A w y i ^ 2 = z ⬝ᵥ (gram A (fun j => 1 / w j) *ᵥ z)) ∧
      (∑ i, w i * projW A w y i * y i = z ⬝ᵥ (gram A (fun j => 1 / w j) *ᵥ z)) := by
  intro z
  have hd : (gram A (fun j => 1 / w j)).det ≠ 0 := gram_det_ne hA fun j => by
    have := hw j; positivity
  have hz : gram A (fun j => 1 / w j) *ᵥ z = Aᵀ *ᵥ y := by
    simp only [z]; rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), one_mulVec]
  constructor
  · rw [gram_quad]
    exact sum_congr rfl fun i _ => by
      simp only [projW, z]; field_simp [(hw i).ne']
  · rw [hz, dotProduct_mulVec, vecMul_transpose]
    simp only [dotProduct]
    exact sum_congr rfl fun i _ => by simp only [projW, z]; field_simp [(hw i).ne']

/-- **Lemma 13′** (Pythagorean sharpening of Lee–Sidford Lemma 13): if `(QW⁻¹)ᵢᵢ ≤ q` for all
`i`, then `N_w(y − Qy) ≤ √(1 + q/C²) N_w(y)`. -/
theorem proj_mixed_bound (hA : (Aᵀ * A).det ≠ 0) (hw : ∀ i, 0 < w i) {C q : ℝ} (hC : 0 < C)
    (hq : ∀ i, qform A (fun j => 1 / w j) i / w i ^ 2 ≤ q) (y : Fin M → ℝ) :
    mixed C w (y - projW A w y) ≤ Real.sqrt (1 + q / C ^ 2) * mixed C w y := by
  obtain ⟨hQQ, hQy⟩ := wnorm_sq_projW hA hw y
  set G := gram A (fun j => 1 / w j)
  set z := G⁻¹ *ᵥ (Aᵀ *ᵥ y)
  set T := z ⬝ᵥ (G *ᵥ z)
  set Qy := projW A w y
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hdG : G.det ≠ 0 := gram_det_ne hA fun j => by have := hw j; positivity
  have hGpsd : ∀ v, 0 ≤ v ⬝ᵥ (G *ᵥ v) := gram_psd fun j => by have := hw j; positivity
  have hT0 : 0 ≤ T := hGpsd z
  set Y2 := ∑ i, w i * y i ^ 2
  -- Pythagoras: `‖y − Qy‖²_w = ‖y‖²_w − ‖Qy‖²_w`
  have hpyth : ∑ i, w i * (y - Qy) i ^ 2 = Y2 - T := by
    have : ∑ i, w i * (y - Qy) i ^ 2 =
        Y2 - 2 * ∑ i, w i * Qy i * y i + ∑ i, w i * Qy i ^ 2 := by
      simp only [Y2, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
    rw [this, hQQ, hQy]; ring
  have hTY : T ≤ Y2 := by
    have := sum_nonneg fun i (_ : i ∈ univ) => mul_nonneg (hw0 i) (sq_nonneg ((y - Qy) i))
    linarith
  -- `|(Qy)ᵢ| ≤ √(qT)`
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have h0 : ∀ v : Fin 0 → ℝ, mixed C w v = 0 := fun v => by
      have : v = 0 := Subsingleton.elim _ _
      simp [this, mixed, wnorm]
    rw [h0, h0, mul_zero]
  have hq0 : 0 ≤ q := by
    refine le_trans (div_nonneg ?_ (sq_nonneg _)) (hq ⟨0, hM⟩)
    have := variational_le (gram_symm _) hGpsd hdG (A ⟨0, hM⟩) 0
    simp only [qform]
    simpa using this
  have hQi : ∀ i, |Qy i| ≤ Real.sqrt (q * T) := fun i => by
    have hcs := sq_dot_le_invQuad_mul (gram_symm _) hGpsd hdG (A i) z
    have hqi := hq i
    rw [Real.le_sqrt (abs_nonneg _) (mul_nonneg hq0 hT0), sq_abs]
    have e : Qy i = (A i ⬝ᵥ z) / w i := rfl
    rw [e, div_pow, div_le_iff₀ (by have := hw i; positivity)]
    have : qform A (fun j => 1 / w j) i ≤ q * w i ^ 2 := by
      rwa [div_le_iff₀ (by have := hw i; positivity)] at hqi
    calc (A i ⬝ᵥ z) ^ 2 ≤ qform A (fun j => 1 / w j) i * T := hcs
      _ ≤ q * w i ^ 2 * T := mul_le_mul_of_nonneg_right this hT0
      _ = q * T * w i ^ 2 := by ring
  have hQinf : ‖Qy‖ ≤ Real.sqrt (q * T) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => by
      rw [Real.norm_eq_abs]; exact hQi i
  -- combine
  have hwy : wnorm w y = Real.sqrt Y2 := rfl
  have hwPy : wnorm w (y - Qy) = Real.sqrt (Y2 - T) := by
    unfold wnorm; rw [hpyth]
  have hcomb : Real.sqrt (q * T) + C * Real.sqrt (Y2 - T) ≤
      Real.sqrt (q + C ^ 2) * Real.sqrt Y2 := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    have h1 := Real.sq_sqrt (mul_nonneg hq0 hT0)
    have h2 := Real.sq_sqrt (sub_nonneg.mpr hTY)
    have h3 := Real.sq_sqrt hq0
    have h4 := Real.sq_sqrt hT0
    have e : Real.sqrt (q * T) = Real.sqrt q * Real.sqrt T := Real.sqrt_mul hq0 T
    rw [e]
    nlinarith [sq_nonneg (Real.sqrt q * Real.sqrt (Y2 - T) - C * Real.sqrt T),
      Real.sqrt_nonneg q, Real.sqrt_nonneg T, Real.sqrt_nonneg (Y2 - T)]
  have hroot : Real.sqrt (q + C ^ 2) = C * Real.sqrt (1 + q / C ^ 2) := by
    rw [show q + C ^ 2 = C ^ 2 * (1 + q / C ^ 2) by field_simp; ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC.le]
  have hone : 1 ≤ Real.sqrt (1 + q / C ^ 2) := by
    rw [Real.le_sqrt zero_le_one (by positivity)]; simp; positivity
  unfold mixed
  rw [hwPy, hwy]
  have hinf : ‖y - Qy‖ ≤ ‖y‖ + Real.sqrt (q * T) := (norm_sub_le _ _).trans (by linarith)
  calc ‖y - Qy‖ + C * Real.sqrt (Y2 - T) ≤ ‖y‖ + (Real.sqrt (q * T) + C * Real.sqrt (Y2 - T)) := by
        linarith
    _ ≤ ‖y‖ + Real.sqrt (q + C ^ 2) * Real.sqrt Y2 := by linarith
    _ ≤ Real.sqrt (1 + q / C ^ 2) * ‖y‖ + Real.sqrt (1 + q / C ^ 2) * (C * Real.sqrt Y2) := by
        rw [hroot]
        nlinarith [norm_nonneg y, Real.sqrt_nonneg Y2]
    _ = Real.sqrt (1 + q / C ^ 2) * (‖y‖ + C * Real.sqrt Y2) := by ring

end Pythagoras

section Sensitivity

variable {A : Matrix (Fin M) (Fin r) ℝ} {p : ℝ}

/-- Leverage scores of a full-rank matrix are at most one. -/
theorem lev_le_one {X : Matrix (Fin M) (Fin r) ℝ} (hX : (Xᵀ * X).det ≠ 0) (i : Fin M) :
    lev X i ≤ 1 := by
  have hs := proj_symm X
  have hi := proj_idem hX
  have h := diag_eq_sum_sq hs hi i
  have hle : proj X i i ^ 2 ≤ proj X i i :=
    calc proj X i i ^ 2 ≤ ∑ j, proj X i j ^ 2 :=
          single_le_sum (f := fun j => proj X i j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
      _ = proj X i i := h.symm
  unfold lev
  nlinarith [sq_nonneg (proj X i i)]

/-- **Lemma S (regularized sensitivity):** for `0 < p ≤ 1`, `0 < ε < 1`, `0 ≤ c ≤ ε/M`, and
`g = w_p(A) + c`, every row satisfies `g_i⁻² aᵢᵀ (AᵀG⁻¹A)⁻¹ aᵢ ≤ (2/(1−ε)) (M/ε)^{2/p−2}`. -/
theorem sens_regLewis (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {ε c : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hc0 : 0 ≤ c) (hcε : c ≤ ε / M) (i : Fin M) :
    qform A (fun j => 1 / (exp (lewisLog p A j) + c)) i / (exp (lewisLog p A i) + c) ^ 2 ≤
      2 / (1 - ε) * (M / ε) ^ (2 / p - 2) := by
  have hp2 : p < 2 := by linarith
  set y := lewisLog p A with hy
  set g : Fin M → ℝ := fun j => exp (y j) + c with hg
  set γ : ℝ := 1 - 2 / p
  set α : ℝ := 2 / p - 2
  have hα : 0 ≤ α := by simp only [α]; rw [sub_nonneg, le_div_iff₀ hp0]; linarith
  have hM : 0 < (M : ℝ) := by exact_mod_cast Fin.pos i
  set Kc : ℝ := 2 / (1 - ε) * (M / ε) ^ α
  have hgpos : ∀ j, 0 < g j := fun j => add_pos_of_pos_of_nonneg (exp_pos _) hc0
  -- (1) the Lewis identity: `aⱼᵀ H⁻¹ aⱼ = w_j^{2/p}`
  set H := gram A (fun j => exp (γ * y j))
  have hLew : ∀ j, qform A (fun k => exp (γ * y k)) j = exp (2 / p * y j) := fun j => by
    have h := lev_lewisLog hA hrow hp0 hp2 j
    rw [lev_diag] at h
    have e : ∀ k, exp ((1 / 2 - 1 / p) * lewisLog p A k) ^ 2 = exp (γ * y k) := fun k => by
      rw [← exp_nat_mul]; congr 1; simp only [γ, hy]; push_cast; ring
    simp only [e] at h
    have hne : exp (γ * y j) ≠ 0 := exp_ne_zero _
    have : qform A (fun k => exp (γ * y k)) j = exp (y j) / exp (γ * y j) := by
      field_simp; linarith
    rw [this, ← exp_sub]; congr 1; simp only [γ]; ring
  -- (2) Lewis weights are at most one
  have hw1 : ∀ j, y j ≤ 0 := fun j => by
    have hB := diag_det hA (e := fun k => exp ((1 / 2 - 1 / p) * lewisLog p A k))
      fun k => exp_ne_zero _
    have := lev_le_one hB j
    rw [lev_lewisLog hA hrow hp0 hp2 j] at this
    simpa [hy] using this
  -- (3) `vᵀHv ≤ Kc · vᵀ(AᵀG⁻¹A)v`
  have hHpsd : ∀ v, 0 ≤ v ⬝ᵥ (H *ᵥ v) := gram_psd fun j => (exp_pos _).le
  have hHdet : H.det ≠ 0 := gram_det_ne hA fun j => exp_pos _
  have hquad : ∀ v, v ⬝ᵥ (H *ᵥ v) ≤ Kc * v ⬝ᵥ (gram A (fun j => 1 / g j) *ᵥ v) := by
    intro v
    set L := univ.filter fun j : Fin M => exp (y j) ≤ ε / M
    have hsplit := (sum_filter_add_sum_filter_not univ (fun j : Fin M => exp (y j) ≤ ε / M)
      (fun j => exp (γ * y j) * (A *ᵥ v) j ^ 2)).symm
    rw [← gram_quad] at hsplit
    -- light rows contribute at most `ε vᵀHv`
    have hlight : ∑ j ∈ L, exp (γ * y j) * (A *ᵥ v) j ^ 2 ≤ ε * v ⬝ᵥ (H *ᵥ v) := by
      have hrowb : ∀ j, (A *ᵥ v) j ^ 2 ≤ exp (2 / p * y j) * v ⬝ᵥ (H *ᵥ v) := fun j => by
        have := sq_dot_le_invQuad_mul (gram_symm _) hHpsd hHdet (A j) v
        rw [← hLew j]; exact this
      calc ∑ j ∈ L, exp (γ * y j) * (A *ᵥ v) j ^ 2
          ≤ ∑ j ∈ L, exp (y j) * v ⬝ᵥ (H *ᵥ v) := sum_le_sum fun j _ => by
            have := mul_le_mul_of_nonneg_left (hrowb j) (exp_pos (γ * y j)).le
            rw [← mul_assoc, ← exp_add] at this
            convert this using 3; simp only [γ]; ring
        _ ≤ ∑ _j ∈ L, ε / M * v ⬝ᵥ (H *ᵥ v) := sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_right (mem_filter.mp hj).2 (hHpsd v)
        _ = L.card * (ε / M) * v ⬝ᵥ (H *ᵥ v) := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ M * (ε / M) * v ⬝ᵥ (H *ᵥ v) := by
            apply mul_le_mul_of_nonneg_right _ (hHpsd v)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have := card_filter_le univ fun j : Fin M => exp (y j) ≤ ε / M
            rw [card_univ, Fintype.card_fin] at this
            exact_mod_cast this
        _ = ε * v ⬝ᵥ (H *ᵥ v) := by field_simp
    -- heavy rows: `e^{γ y} ≤ 2 (M/ε)^α / g`
    have hheavy : ∑ j ∈ univ.filter (fun j : Fin M => ¬ exp (y j) ≤ ε / M),
        exp (γ * y j) * (A *ᵥ v) j ^ 2 ≤
        2 * (M / ε) ^ α * v ⬝ᵥ (gram A (fun j => 1 / g j) *ᵥ v) := by
      rw [gram_quad, mul_sum]
      refine (sum_le_sum fun j hj => ?_).trans (sum_le_sum_of_subset_of_nonneg
        (filter_subset _ univ) fun j _ _ => mul_nonneg (by positivity)
          (mul_nonneg (one_div_pos.mpr (hgpos j)).le (sq_nonneg _)))
      have hj' : ε / M < exp (y j) := lt_of_not_ge (mem_filter.mp hj).2
      have hcy : c ≤ exp (y j) := hcε.trans hj'.le
      -- `e^{−α y} ≤ (M/ε)^α`
      have h1 : exp (-(α * y j)) ≤ (M / ε) ^ α := by
        rw [rpow_def_of_pos (by positivity), exp_le_exp, mul_comm (Real.log _)]
        have : Real.log (ε / M) < y j := by
          rw [← exp_lt_exp, exp_log (by positivity)]; exact hj'
        rw [Real.log_div hε0.ne' hM.ne'] at this
        rw [Real.log_div hM.ne' hε0.ne']
        have h' : -y j ≤ Real.log M - Real.log ε := by linarith
        have := mul_le_mul_of_nonneg_left h' hα
        linarith
      -- `e^{−y} ≤ 2/g`
      have h2 : exp (-y j) ≤ 2 * (1 / g j) := by
        have h' : 1 / exp (y j) ≤ 2 / g j := by
          rw [div_le_div_iff₀ (exp_pos _) (hgpos j)]; simp only [hg]; linarith
        rw [exp_neg, ← one_div, mul_one_div]; exact h'
      have e : exp (γ * y j) = exp (-(α * y j)) * exp (-y j) := by
        rw [← exp_add]; congr 1; simp only [γ, α]; ring
      rw [e]
      calc exp (-(α * y j)) * exp (-y j) * (A *ᵥ v) j ^ 2
          ≤ (M / ε) ^ α * (2 * (1 / g j)) * (A *ᵥ v) j ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul h1 h2 (exp_pos _).le (by positivity)
        _ = 2 * (M / ε) ^ α * (1 / g j * (A *ᵥ v) j ^ 2) := by ring
    have hpos1 : 0 < 1 - ε := by linarith
    have : (1 - ε) * v ⬝ᵥ (H *ᵥ v) ≤ 2 * (M / ε) ^ α * v ⬝ᵥ (gram A (fun j => 1 / g j) *ᵥ v) := by
      linarith
    simp only [Kc]
    rw [div_mul_eq_mul_div, mul_comm, ← mul_div_assoc, le_div_iff₀ hpos1]
    linarith
  -- (4) invert the comparison
  have hKc : 0 < Kc := by
    have : 0 < 1 - ε := by linarith
    positivity
  have hinv := invQuad_le_of_quad_le (gram_symm _) hHpsd hHdet
    (gram_det_ne hA fun j => one_div_pos.mpr (hgpos j)) hKc hquad (A i)
  -- `hinv : qform(1/g) ≤ Kc · w_i^{2/p}`
  change qform A (fun j => 1 / g j) i ≤ Kc * qform A (fun k => exp (γ * y k)) i at hinv
  rw [hLew] at hinv
  -- (5) `w_i^{2/p} / g_i² ≤ w_i^α ≤ 1`
  have hfin : exp (2 / p * y i) / g i ^ 2 ≤ 1 := by
    rw [div_le_one (by have := hgpos i; positivity)]
    have hwg : exp (y i) ≤ g i := by simp only [hg]; linarith
    have : exp (2 / p * y i) ≤ exp (y i) ^ 2 := by
      rw [← exp_nat_mul, exp_le_exp]
      push_cast
      have : 2 ≤ 2 / p := by rw [le_div_iff₀ hp0]; linarith
      nlinarith [hw1 i]
    exact this.trans (pow_le_pow_left₀ (exp_pos _).le hwg 2)
  calc qform A (fun j => 1 / g j) i / g i ^ 2 ≤ Kc * exp (2 / p * y i) / g i ^ 2 :=
        div_le_div_of_nonneg_right hinv (by positivity)
    _ = Kc * (exp (2 / p * y i) / g i ^ 2) := by ring
    _ ≤ Kc * 1 := mul_le_mul_of_nonneg_left hfin hKc.le
    _ = Kc := mul_one _

/-- **Lemma S with the audited draft's constants:** for `p = 1 − 1/L₀` with `L₀ − 1 ≥ log₂(2M)`,
`ε = 1/2`, and `0 ≤ c ≤ 1/(2M)`, the regularized sensitivity is at most `16`. -/
theorem sens_note (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) {c : ℝ} (hc0 : 0 ≤ c) (hcM : c ≤ 1 / (2 * M))
    (i : Fin M) :
    qform A (fun j => 1 / (exp (lewisLog (1 - 1 / L₀) A j) + c)) i /
      (exp (lewisLog (1 - 1 / L₀) A i) + c) ^ 2 ≤ 16 := by
  have hL0 : 0 < L₀ := by linarith
  have hp0 : 0 < 1 - 1 / L₀ := by rw [sub_pos, div_lt_one hL0]; linarith
  have hp1 : 1 - 1 / L₀ ≤ 1 := by have : 0 < 1 / L₀ := by positivity
                                  linarith
  have hM : 0 < (M : ℝ) := by exact_mod_cast Fin.pos i
  have h := sens_regLewis hA hrow hp0 hp1 (ε := 1 / 2) (c := c) (by norm_num) (by norm_num) hc0
    (by rw [show (1 / 2 : ℝ) / M = 1 / (2 * M) by field_simp]; exact hcM) i
  refine h.trans ?_
  -- `(2M)^α ≤ 4` with `α = 2/(L₀ − 1)`
  have hα : 2 / (1 - 1 / L₀) - 2 = 2 / (L₀ - 1) := by
    field_simp
    have : L₀ - 1 ≠ 0 := by linarith
    field_simp; ring
  rw [hα, show (M : ℝ) / (1 / 2) = 2 * M by field_simp]
  have hpow : (2 * (M : ℝ)) ^ (2 / (L₀ - 1)) ≤ 4 := by
    have h2M : 0 < 2 * (M : ℝ) := by positivity
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_logb (by norm_num : (0:ℝ) < 2)
      (by norm_num) h2M, ← Real.rpow_mul (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith
  calc 2 / (1 - 1 / 2) * (2 * (M : ℝ)) ^ (2 / (L₀ - 1)) ≤ 2 / (1 - 1 / 2) * 4 :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 16 := by norm_num

end Sensitivity

section Contract

variable {B : Matrix (Fin M) (Fin r) ℝ} {w : Fin M → ℝ}

/-- `W⁻¹Bν`. -/
def rowRange (B : Matrix (Fin M) (Fin r) ℝ) (w : Fin M → ℝ) (ν : Fin r → ℝ) : Fin M → ℝ :=
  fun i => (B *ᵥ ν) i / w i

theorem gram_inv_mulVec_rowRange (hB : (Bᵀ * B).det ≠ 0) (hw : ∀ i, 0 < w i) (ν : Fin r → ℝ) :
    (gram B (fun j => 1 / w j))⁻¹ *ᵥ (Bᵀ *ᵥ rowRange B w ν) = ν := by
  have hd : (gram B (fun j => 1 / w j)).det ≠ 0 := gram_det_ne hB fun j => by
    have := hw j; positivity
  have : Bᵀ *ᵥ rowRange B w ν = gram B (fun j => 1 / w j) *ᵥ ν := by
    rw [gram, ← mulVec_mulVec, ← mulVec_mulVec]
    congr 1; funext i; simp [rowRange, mulVec_diagonal, div_eq_inv_mul]
  rw [this, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), one_mulVec]

/-- `Q` fixes the range of `W⁻¹B`. -/
theorem projW_rowRange (hB : (Bᵀ * B).det ≠ 0) (hw : ∀ i, 0 < w i) (ν : Fin r → ℝ) :
    projW B w (rowRange B w ν) = rowRange B w ν := by
  funext i; simp only [projW, gram_inv_mulVec_rowRange hB hw ν, rowRange]

theorem projW_sub (u v : Fin M → ℝ) : projW B w (u - v) = projW B w u - projW B w v := by
  funext i; simp only [projW, mulVec_sub, Pi.sub_apply, sub_div]

/-- **The `eq:projection` contract** (repaired Lee–Sidford Lemma 10 + Lemma 13′). Let
`δ = inf_ν N_w(y − W⁻¹Bν)` be the centrality, and let `z` satisfy `Bᵀz = 0` and
`y + z = W⁻¹Bν₀`; for the exact Newton direction `h`, `z = Sh`. Then
`δ ≤ N_w(z) ≤ √(1 + q/C²) δ`. -/
theorem projection_contract (hB : (Bᵀ * B).det ≠ 0) (hw : ∀ i, 0 < w i) {C q : ℝ} (hC : 0 < C)
    (hq : ∀ i, qform B (fun j => 1 / w j) i / w i ^ 2 ≤ q) (y z : Fin M → ℝ)
    (hz : Bᵀ *ᵥ z = 0) {ν₀ : Fin r → ℝ} (hν₀ : y + z = rowRange B w ν₀) :
    (⨅ ν, mixed C w (y - rowRange B w ν)) ≤ mixed C w z ∧
      mixed C w z ≤ Real.sqrt (1 + q / C ^ 2) * ⨅ ν, mixed C w (y - rowRange B w ν) := by
  have hbdd : BddBelow (Set.range fun ν => mixed C w (y - rowRange B w ν)) :=
    ⟨0, fun _ ⟨ν, hν⟩ => hν ▸ mixed_nonneg hC.le _⟩
  have hneg : ∀ v : Fin M → ℝ, mixed C w (-v) = mixed C w v := fun v => by
    simp [mixed, norm_neg, wnorm_neg]
  -- `y − W⁻¹Bν₀ = −z`
  have hyν₀ : y - rowRange B w ν₀ = -z := by rw [← hν₀]; abel
  -- `Qy = W⁻¹Bν₀`, so `y − Qy = −z`
  have hQy : y - projW B w y = -z := by
    have hBy : Bᵀ *ᵥ y = Bᵀ *ᵥ rowRange B w ν₀ := by
      rw [← hν₀, mulVec_add, hz, add_zero]
    have : projW B w y = rowRange B w ν₀ := by
      funext i; simp only [projW, hBy, gram_inv_mulVec_rowRange hB hw ν₀, rowRange]
    rw [this, hyν₀]
  -- every residual has the same `(I − Q)`-part
  have hres : ∀ ν, (y - rowRange B w ν) - projW B w (y - rowRange B w ν) = -z := fun ν => by
    rw [projW_sub, projW_rowRange hB hw, ← hQy]; abel
  refine ⟨?_, ?_⟩
  · calc (⨅ ν, mixed C w (y - rowRange B w ν)) ≤ mixed C w (y - rowRange B w ν₀) :=
          ciInf_le hbdd ν₀
      _ = mixed C w z := by rw [hyν₀, hneg]
  · rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      have h0 : mixed C w z = 0 := by
        have : z = 0 := Subsingleton.elim _ _
        simp [this, mixed, wnorm]
      rw [h0]
      exact mul_nonneg (Real.sqrt_nonneg _) (le_ciInf fun ν => mixed_nonneg hC.le _)
    have hd1 : ∀ j, 0 < 1 / w j := fun j => one_div_pos.mpr (hw j)
    have hq0 : 0 ≤ q := by
      refine le_trans (div_nonneg ?_ (sq_nonneg _)) (hq ⟨0, hM⟩)
      have := variational_le (gram_symm (B := B) (fun j => 1 / w j))
        (gram_psd (B := B) fun j => (hd1 j).le) (gram_det_ne hB hd1) (B ⟨0, hM⟩) 0
      simp only [qform]; simpa using this
    have hroot : 0 < Real.sqrt (1 + q / C ^ 2) := by positivity
    rw [← div_le_iff₀' hroot]
    refine le_ciInf fun ν => ?_
    rw [div_le_iff₀' hroot]
    have := proj_mixed_bound hB hw hC hq (y - rowRange B w ν)
    rwa [hres, hneg] at this

/-- Weight-window comparison: if `(4/5)g ≤ w ≤ (5/4)g` then
`qform(1/w)ᵢ / wᵢ² ≤ (5/4)³ · qform(1/g)ᵢ / gᵢ²`. -/
theorem sens_window (hB : (Bᵀ * B).det ≠ 0) {g : Fin M → ℝ} (hg : ∀ i, 0 < g i)
    (hlo : ∀ i, 4 / 5 * g i ≤ w i) (hhi : ∀ i, w i ≤ 5 / 4 * g i) (i : Fin M) :
    qform B (fun j => 1 / w j) i / w i ^ 2 ≤
      (5 / 4) ^ 3 * (qform B (fun j => 1 / g j) i / g i ^ 2) := by
  have hw : ∀ i, 0 < w i := fun i => lt_of_lt_of_le (mul_pos (by norm_num) (hg i)) (hlo i)
  have h1 : qform B (fun j => 1 / w j) i ≤ 5 / 4 * qform B (fun j => 1 / g j) i := by
    refine qform_le hB (fun j => one_div_pos.mpr (hg j)) (fun j => one_div_pos.mpr (hw j))
      (by norm_num) (fun j => ?_) i
    rw [div_le_iff₀ (hg j)]
    have := hlo j
    rw [show 5 / 4 * (1 / w j) * g j = 5 / 4 * g j / w j by ring, le_div_iff₀ (hw j)]
    have := hhi j
    linarith
  have h2 : 1 / w i ^ 2 ≤ (5 / 4) ^ 2 * (1 / g i ^ 2) := by
    rw [div_le_iff₀ (by have := hw i; positivity)]
    have := hlo i
    rw [show (5 / 4 : ℝ) ^ 2 * (1 / g i ^ 2) * w i ^ 2 = (5 / 4 * w i / g i) ^ 2 by
      field_simp]
    have : 1 ≤ 5 / 4 * w i / g i := by
      rw [le_div_iff₀ (hg i)]; linarith
    nlinarith
  have hq0 : 0 ≤ qform B (fun j => 1 / g j) i := by
    have := variational_le (gram_symm _) (gram_psd fun j => (one_div_pos.mpr (hg j)).le)
      (gram_det_ne hB fun j => one_div_pos.mpr (hg j)) (B i) 0
    simp only [qform]; simpa using this
  have hq0' : 0 ≤ qform B (fun j => 1 / w j) i := by
    have := variational_le (gram_symm _) (gram_psd fun j => (one_div_pos.mpr (hw j)).le)
      (gram_det_ne hB fun j => one_div_pos.mpr (hw j)) (B i) 0
    simp only [qform]; simpa using this
  rw [div_eq_mul_one_div, div_eq_mul_one_div (qform B _ i)]
  calc qform B (fun j => 1 / w j) i * (1 / w i ^ 2)
      ≤ (5 / 4 * qform B (fun j => 1 / g j) i) * ((5 / 4) ^ 2 * (1 / g i ^ 2)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (5 / 4) ^ 3 * (qform B (fun j => 1 / g j) i * (1 / g i ^ 2)) := by ring

/-- `√(1 + 32/(48k)²) ≤ 1 + 1/(16k)` for `k ≥ 1`. -/
theorem gamma_bound {k : ℝ} (hk : 1 ≤ k) :
    Real.sqrt (1 + 32 / (48 * k) ^ 2) ≤ 1 + 1 / (16 * k) := by
  have hk0 : 0 < k := by linarith
  rw [Real.sqrt_le_left (by positivity)]
  have e : 32 / (48 * k) ^ 2 = 1 / (72 * k ^ 2) := by field_simp; ring
  rw [e]
  have h1 : 1 / (72 * k ^ 2) ≤ 2 * (1 / (16 * k)) := by
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  nlinarith [sq_nonneg (1 / (16 * k))]

end Contract

section Note

variable {A : Matrix (Fin M) (Fin r) ℝ} {κ m : Fin M → ℝ}

/-- **`eq:projection` with the audited draft's parameters and the repaired regularization.**

Let `p = 1 − 1/L₀`, `k = 2L₀`, `C_N = 48k`, `log₂(2M) ≤ L₀ − 1` and `0 ≤ c₀ ≤ 1/(2M)`, and let
`g = w_p(A_x) + c₀`. Take weights in the window `(4/5)g ≤ w ≤ (5/4)g`, and let `h` be the exact
feasible Newton direction: `Aᵀh = 0` and `f + wS²h = Aπ`, where `f = tc + wφ'`. Then, with
`δ = inf_ν N_w((f − Aν)/(wS))`, we have `δ ≤ N_w(Sh) ≤ (1 + 1/(16k)) δ`.

A public bound `M̄ ≥ M` also satisfies the hypotheses on `c₀` and `L₀`. -/
theorem eq_projection_note (hA : (Aᵀ * A).det ≠ 0) (hrow : ∀ i, A i ≠ 0) {L₀ : ℝ} (hL : 2 ≤ L₀)
    (hLM : Real.logb 2 (2 * M) ≤ L₀ - 1) (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * M)) {x : Fin M → ℝ} (hx : Interior κ m x) {w : Fin M → ℝ}
    (hlo : ∀ i, 4 / 5 * gfun κ m (1 - 1 / L₀) c₀ A x i ≤ w i)
    (hhi : ∀ i, w i ≤ 5 / 4 * gfun κ m (1 - 1 / L₀) c₀ A x i)
    {f h : Fin M → ℝ} {π₀ : Fin r → ℝ} (hh1 : Aᵀ *ᵥ h = 0)
    (hh2 : ∀ i, f i + w i * barS κ m x i ^ 2 * h i = (A *ᵥ π₀) i) :
    let δ := ⨅ ν, mixed (48 * (2 * L₀)) w
      (fun i => (f i - (A *ᵥ ν) i) / (w i * barS κ m x i))
    δ ≤ mixed (48 * (2 * L₀)) w (fun i => barS κ m x i * h i) ∧
      mixed (48 * (2 * L₀)) w (fun i => barS κ m x i * h i) ≤ (1 + 1 / (16 * (2 * L₀))) * δ := by
  intro δ
  set B := diagonal (fun j => exp (sfun κ m x j)) * A with hBdef
  set g := gfun κ m (1 - 1 / L₀) c₀ A x
  have hS : ∀ i, 0 < barS κ m x i := barS_pos hκ hx
  have hBd : (Bᵀ * B).det ≠ 0 := diag_det hA fun j => exp_ne_zero _
  have hBr : ∀ i, B i ≠ 0 := diag_rows hrow fun j => exp_ne_zero _
  have hg : ∀ i, 0 < g i := fun i => add_pos_of_pos_of_nonneg (exp_pos _) hc₀
  have hw : ∀ i, 0 < w i := fun i => lt_of_lt_of_le (mul_pos (by norm_num) (hg i)) (hlo i)
  have hBv : ∀ ν i, (B *ᵥ ν) i = (A *ᵥ ν) i / barS κ m x i := fun ν i => by
    rw [hBdef, ← mulVec_mulVec, mulVec_diagonal, exp_sfun hκ hx]; ring
  -- sensitivity: `q ≤ 32`
  have hsens : ∀ i, qform B (fun j => 1 / w j) i / w i ^ 2 ≤ 32 := fun i => by
    have h1 := sens_window hBd hg hlo hhi i
    have h2 := sens_note hBd hBr hL hLM hc₀ hcM i
    calc qform B (fun j => 1 / w j) i / w i ^ 2 ≤ (5 / 4) ^ 3 * (qform B (fun j => 1 / g j) i /
          g i ^ 2) := h1
      _ ≤ (5 / 4) ^ 3 * 16 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 32 := by norm_num
  -- translate the Newton direction
  set y : Fin M → ℝ := fun i => f i / (w i * barS κ m x i)
  set z : Fin M → ℝ := fun i => barS κ m x i * h i
  have hz : Bᵀ *ᵥ z = 0 := by
    rw [← hh1]; funext a
    simp only [mulVec, dotProduct, transpose_apply, z]
    exact sum_congr rfl fun i _ => by
      rw [hBdef, diagonal_mul, exp_sfun hκ hx]; field_simp [(hS i).ne']
  have hyz : y + z = rowRange B w π₀ := by
    funext i
    simp only [Pi.add_apply, y, z, rowRange, hBv, ← hh2 i]
    field_simp [(hw i).ne', (hS i).ne']
  have hδ : δ = ⨅ ν, mixed (48 * (2 * L₀)) w (y - rowRange B w ν) := by
    refine iInf_congr fun ν => ?_
    congr 1; funext i
    simp only [Pi.sub_apply, y, rowRange, hBv]
    field_simp [(hw i).ne', (hS i).ne']
  have hC : (0 : ℝ) < 48 * (2 * L₀) := by positivity
  obtain ⟨h1, h2⟩ := projection_contract hBd hw hC hsens y z hz hyz
  rw [← hδ] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  have hδ0 : 0 ≤ δ := by
    rw [hδ]; exact le_ciInf fun ν => mixed_nonneg hC.le _
  exact mul_le_mul_of_nonneg_right (gamma_bound (by linarith)) hδ0

end Note

end

end ImplicitLP
end CutQueryComplexity
