import CutQueryComplexity.ImplicitLP.Leverage
import Mathlib.Topology.MetricSpace.Contracting

/-! # Lewis weights: existence and uniqueness by contraction (Lee–Sidford audit)

Let `B ∈ ℝ^{M×r}` have full column rank (`det(BᵀB) ≠ 0`) and no zero rows, and let `0 < p < 2`.
The `ℓ_p` Lewis weights are the positive `w` with `w = σ(W^{1/2−1/p} B)` (`IsLewis`).

In log coordinates `y = log w`, with `a = 1 − 2/p`, the Lewis map is
`T(y)ᵢ = (p/2) log (bᵢᵀ (Bᵀ diag(e^{a y}) B)⁻¹ bᵢ)`. Changing `y` by `E` in sup norm changes the
Gram matrix by factors `e^{±|a|E}` in the quadratic-form order, hence each `log bᵢᵀG⁻¹bᵢ` by at
most `|a|E` (`invQuad_le_of_quad_le`), so `T` contracts by `(p/2)|a| = 1 − p/2`
(`lewisMap_contracting`). Banach's fixed-point theorem gives a unique fixed point, and fixed
points are exactly the logarithms of Lewis weights (`lewis_exists_unique`). This replaces the
incomplete box-restriction step of Lee–Sidford Lemma 22 (audit gap G9).

Inverse comparisons use the variational formula `bᵀG⁻¹b = max_y (2bᵀy − yᵀGy)`
(`variational_le`), never an abstract Loewner inversion.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real

noncomputable section

variable {M r : ℕ}

section Quadratic

variable {G G₁ G₂ : Matrix (Fin r) (Fin r) ℝ}

theorem dot_mulVec_comm (hG : Gᵀ = G) (x y : Fin r → ℝ) : x ⬝ᵥ (G *ᵥ y) = y ⬝ᵥ (G *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hG, dotProduct_comm]

/-- **Variational formula:** for symmetric positive semidefinite invertible `G`,
`2bᵀy − yᵀGy ≤ bᵀG⁻¹b` for every `y`. -/
theorem variational_le (hG : Gᵀ = G) (hpsd : ∀ y, 0 ≤ y ⬝ᵥ (G *ᵥ y)) (hdet : G.det ≠ 0)
    (b y : Fin r → ℝ) : 2 * (b ⬝ᵥ y) - y ⬝ᵥ (G *ᵥ y) ≤ b ⬝ᵥ (G⁻¹ *ᵥ b) := by
  set x := G⁻¹ *ᵥ b
  have hx : G *ᵥ x = b := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  have h := hpsd (y - x)
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hx,
    dot_mulVec_comm hG x y, hx] at h
  have h1 : y ⬝ᵥ b = b ⬝ᵥ y := dotProduct_comm _ _
  have h2 : x ⬝ᵥ b = b ⬝ᵥ x := dotProduct_comm _ _
  linarith

theorem variational_eq (hdet : G.det ≠ 0) (b : Fin r → ℝ) :
    2 * (b ⬝ᵥ (G⁻¹ *ᵥ b)) - (G⁻¹ *ᵥ b) ⬝ᵥ (G *ᵥ (G⁻¹ *ᵥ b)) = b ⬝ᵥ (G⁻¹ *ᵥ b) := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec,
    dotProduct_comm (G⁻¹ *ᵥ b)]
  ring

/-- **Scaled anti-monotonicity of the inverse quadratic form:** if `yᵀG₁y ≤ c·yᵀG₂y` for all
`y`, then `bᵀG₂⁻¹b ≤ c·bᵀG₁⁻¹b`. -/
theorem invQuad_le_of_quad_le (hG₁ : G₁ᵀ = G₁) (hpsd₁ : ∀ y, 0 ≤ y ⬝ᵥ (G₁ *ᵥ y))
    (hdet₁ : G₁.det ≠ 0) (hdet₂ : G₂.det ≠ 0) {c : ℝ} (hc : 0 < c)
    (hle : ∀ y, y ⬝ᵥ (G₁ *ᵥ y) ≤ c * y ⬝ᵥ (G₂ *ᵥ y)) (b : Fin r → ℝ) :
    b ⬝ᵥ (G₂⁻¹ *ᵥ b) ≤ c * b ⬝ᵥ (G₁⁻¹ *ᵥ b) := by
  set q := b ⬝ᵥ (G₂⁻¹ *ᵥ b)
  set y := c⁻¹ • (G₂⁻¹ *ᵥ b)
  have hv := variational_le hG₁ hpsd₁ hdet₁ b y
  have hy2 : y ⬝ᵥ (G₂ *ᵥ y) = c⁻¹ ^ 2 * q := by
    simp only [y, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, mulVec_mulVec,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet₂), one_mulVec, q]
    rw [dotProduct_comm]; ring
  have hby : b ⬝ᵥ y = c⁻¹ * q := by simp [y, q, dotProduct_smul]
  have h1 := hle y
  rw [hy2] at h1
  rw [hby] at hv
  have hc' : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  have : c⁻¹ * q ≤ b ⬝ᵥ (G₁⁻¹ *ᵥ b) := by
    have : c * (c⁻¹ ^ 2 * q) = c⁻¹ * q := by field_simp
    nlinarith
  calc q = c * (c⁻¹ * q) := by rw [← mul_assoc, hc', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left this hc.le

end Quadratic

section Gram

variable {B : Matrix (Fin M) (Fin r) ℝ}

/-- The weighted Gram matrix `Bᵀ diag(d) B`. -/
def gram (B : Matrix (Fin M) (Fin r) ℝ) (d : Fin M → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Bᵀ * diagonal d * B

theorem gram_symm (d : Fin M → ℝ) : (gram B d)ᵀ = gram B d := by
  simp [gram, transpose_mul, Matrix.mul_assoc]

theorem gram_quad (d : Fin M → ℝ) (x : Fin r → ℝ) :
    x ⬝ᵥ (gram B d *ᵥ x) = ∑ j, d j * (B *ᵥ x) j ^ 2 := by
  rw [gram, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal]
  exact sum_congr rfl fun j _ => by ring

theorem gram_psd {d : Fin M → ℝ} (hd : ∀ j, 0 ≤ d j) (x : Fin r → ℝ) :
    0 ≤ x ⬝ᵥ (gram B d *ᵥ x) := by
  rw [gram_quad]; exact sum_nonneg fun j _ => mul_nonneg (hd j) (sq_nonneg _)

theorem mulVec_eq_zero_of_rank (hB : (Bᵀ * B).det ≠ 0) {x : Fin r → ℝ} (hx : B *ᵥ x = 0) :
    x = 0 := by
  by_contra hne
  apply hB
  rw [← exists_mulVec_eq_zero_iff]
  exact ⟨x, hne, by rw [← mulVec_mulVec, hx, mulVec_zero]⟩

theorem gram_pos (hB : (Bᵀ * B).det ≠ 0) {d : Fin M → ℝ} (hd : ∀ j, 0 < d j) {x : Fin r → ℝ}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ (gram B d *ᵥ x) := by
  rw [gram_quad]
  have : B *ᵥ x ≠ 0 := fun h => hx (mulVec_eq_zero_of_rank hB h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp this
  exact sum_pos' (fun j _ => mul_nonneg (hd j).le (sq_nonneg _))
    ⟨j, mem_univ j, mul_pos (hd j) (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hj).symm)⟩

theorem gram_det_ne (hB : (Bᵀ * B).det ≠ 0) {d : Fin M → ℝ} (hd : ∀ j, 0 < d j) :
    (gram B d).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hGx⟩ := exists_mulVec_eq_zero_iff.mpr h0
  have := gram_pos hB hd hx
  rw [hGx, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- `qform B d i = bᵢᵀ (Bᵀ diag(d) B)⁻¹ bᵢ`. -/
def qform (B : Matrix (Fin M) (Fin r) ℝ) (d : Fin M → ℝ) (i : Fin M) : ℝ :=
  B i ⬝ᵥ ((gram B d)⁻¹ *ᵥ B i)

theorem qform_pos (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) {d : Fin M → ℝ}
    (hd : ∀ j, 0 < d j) (i : Fin M) : 0 < qform B d i := by
  set G := gram B d
  set x := G⁻¹ *ᵥ B i
  have hx : G *ᵥ x = B i := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (gram_det_ne hB hd)),
      one_mulVec]
  have hx0 : x ≠ 0 := fun h => hrow i (by rw [← hx, h, mulVec_zero])
  have := gram_pos hB hd hx0
  have e : x ⬝ᵥ (G *ᵥ x) = B i ⬝ᵥ x := by rw [hx, dotProduct_comm]
  show 0 < B i ⬝ᵥ x
  rw [← e]; exact this

/-- `d ≤ c d'` coordinatewise gives `qform d' ≤ c · qform d`. -/
theorem qform_le (hB : (Bᵀ * B).det ≠ 0) {d d' : Fin M → ℝ} (hd : ∀ j, 0 < d j)
    (hd' : ∀ j, 0 < d' j) {c : ℝ} (hc : 0 < c) (hle : ∀ j, d j ≤ c * d' j) (i : Fin M) :
    qform B d' i ≤ c * qform B d i := by
  refine invQuad_le_of_quad_le (gram_symm d) (gram_psd fun j => (hd j).le) (gram_det_ne hB hd)
    (gram_det_ne hB hd') hc (fun y => ?_) (B i)
  rw [gram_quad, gram_quad, mul_sum]
  exact sum_le_sum fun j _ => by
    have := sq_nonneg ((B *ᵥ y) j)
    nlinarith [hle j]

/-- `σ(diag(s) B)ᵢ = sᵢ² · bᵢᵀ (Bᵀ diag(s²) B)⁻¹ bᵢ`. -/
theorem lev_diag (s : Fin M → ℝ) (i : Fin M) :
    lev (diagonal s * B) i = s i ^ 2 * qform B (fun j => s j ^ 2) i := by
  have hg : (diagonal s * B)ᵀ * (diagonal s * B) = gram B (fun j => s j ^ 2) := by
    have hd : diagonal s * diagonal s = diagonal (fun j => s j ^ 2) := by
      rw [diagonal_mul_diagonal]; congr 1; funext j; ring
    simp only [gram, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal s) (diagonal s) B, hd]
  unfold lev proj
  rw [hg, transpose_mul, diagonal_transpose]
  have : diagonal s * B * (gram B fun j => s j ^ 2)⁻¹ * (Bᵀ * diagonal s) =
      diagonal s * (B * (gram B fun j => s j ^ 2)⁻¹ * Bᵀ) * diagonal s := by
    simp only [Matrix.mul_assoc]
  rw [this, mul_diagonal, diagonal_mul]
  have hq : (B * (gram B fun j => s j ^ 2)⁻¹ * Bᵀ) i i = qform B (fun j => s j ^ 2) i := by
    simp only [qform, mul_apply, transpose_apply, dotProduct, mulVec, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun a _ => by
      rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
  rw [hq]; ring

end Gram

section Lewis

variable {B : Matrix (Fin M) (Fin r) ℝ} {p : ℝ}

/-- **The Lewis map in log coordinates:** `T(y)ᵢ = (p/2) log qform(e^{(1−2/p)y})ᵢ`. -/
def lewisMap (p : ℝ) (B : Matrix (Fin M) (Fin r) ℝ) (y : Fin M → ℝ) : Fin M → ℝ :=
  fun i => p / 2 * Real.log (qform B (fun j => exp ((1 - 2 / p) * y j)) i)

/-- `w` are the `ℓ_p` Lewis weights of `B`: `w > 0` and `w = σ(W^{1/2−1/p} B)`. -/
def IsLewis (p : ℝ) (B : Matrix (Fin M) (Fin r) ℝ) (w : Fin M → ℝ) : Prop :=
  (∀ i, 0 < w i) ∧ ∀ i, lev (diagonal (fun j => w j ^ (1 / 2 - 1 / p)) * B) i = w i

theorem abs_log_qform_sub_le (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) {a E : ℝ}
    {y y' : Fin M → ℝ} (hE : ∀ j, |y j - y' j| ≤ E) (i : Fin M) :
    |Real.log (qform B (fun j => exp (a * y j)) i) -
      Real.log (qform B (fun j => exp (a * y' j)) i)| ≤ |a| * E := by
  have hb : ∀ j, |a * (y j - y' j)| ≤ |a| * E := fun j => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hE j) (abs_nonneg a)
  have hE0 : ∀ j, exp (a * y j) ≤ exp (|a| * E) * exp (a * y' j) := fun j => by
    rw [← exp_add, exp_le_exp]
    have := (le_abs_self _).trans (hb j)
    linarith
  have hE1 : ∀ j, exp (a * y' j) ≤ exp (|a| * E) * exp (a * y j) := fun j => by
    rw [← exp_add, exp_le_exp]
    have := (neg_abs_le _).trans' (neg_le_neg (hb j))
    linarith
  have hpos : ∀ z : Fin M → ℝ, ∀ j, 0 < exp (a * z j) := fun _ _ => exp_pos _
  have q1 := qform_pos hB hrow (hpos y) i
  have q2 := qform_pos hB hrow (hpos y') i
  have h1 := qform_le hB (hpos y) (hpos y') (exp_pos _) hE0 i
  have h2 := qform_le hB (hpos y') (hpos y) (exp_pos _) hE1 i
  rw [abs_le]
  constructor
  · have := Real.log_le_log q2 h1
    rw [Real.log_mul (exp_pos _).ne' q1.ne', Real.log_exp] at this
    linarith
  · have := Real.log_le_log q1 h2
    rw [Real.log_mul (exp_pos _).ne' q2.ne', Real.log_exp] at this
    linarith

/-- **The Lewis map contracts by `1 − p/2`** in the sup metric. -/
theorem lewisMap_dist_le (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p)
    (hp2 : p < 2) (y y' : Fin M → ℝ) :
    dist (lewisMap p B y) (lewisMap p B y') ≤ (1 - p / 2) * dist y y' := by
  have hc : 0 ≤ 1 - p / 2 := by linarith
  refine (dist_pi_le_iff (mul_nonneg hc dist_nonneg)).mpr fun i => ?_
  have hE : ∀ j, |y j - y' j| ≤ dist y y' := fun j => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist y y' j
  have h := abs_log_qform_sub_le (a := 1 - 2 / p) hB hrow hE i
  have ha : |1 - 2 / p| = 2 / p - 1 := by
    rw [abs_of_nonpos (by rw [sub_nonpos, le_div_iff₀ hp0]; linarith)]; ring
  rw [ha] at h
  rw [Real.dist_eq]
  unfold lewisMap
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < p / 2)]
  calc p / 2 * |_| ≤ p / 2 * ((2 / p - 1) * dist y y') :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (1 - p / 2) * dist y y' := by field_simp

theorem lewisMap_contracting (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p)
    (hp2 : p < 2) : ContractingWith (Real.toNNReal (1 - p / 2)) (lewisMap p B) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
  · rw [Real.toNNReal_lt_one]; linarith
  · rw [Real.coe_toNNReal _ (by linarith)]
    exact lewisMap_dist_le hB hrow hp0 hp2 y y'

/-- Fixed points of the Lewis map are exactly logarithms of Lewis weights. -/
theorem isLewis_iff_fixed (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p)
    (y : Fin M → ℝ) : IsLewis p B (fun i => exp (y i)) ↔ lewisMap p B y = y := by
  have hs : ∀ j, (exp (y j) ^ (1 / 2 - 1 / p)) ^ 2 = exp ((1 - 2 / p) * y j) := fun j => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (exp_pos _).le, ← Real.exp_mul]
    congr 1; push_cast; ring
  have hq : ∀ i, 0 < qform B (fun j => exp ((1 - 2 / p) * y j)) i :=
    qform_pos hB hrow fun j => exp_pos _
  have key : ∀ i, lev (diagonal (fun j => exp (y j) ^ (1 / 2 - 1 / p)) * B) i =
      exp ((1 - 2 / p) * y i) * qform B (fun j => exp ((1 - 2 / p) * y j)) i := fun i => by
    rw [lev_diag, hs]; simp_rw [hs]
  constructor
  · rintro ⟨-, h⟩
    funext i
    have := h i
    rw [key] at this
    -- `e^{a yᵢ} q = e^{yᵢ}` gives `log q = (2/p) yᵢ`
    have hlog : Real.log (qform B (fun j => exp ((1 - 2 / p) * y j)) i) = 2 / p * y i := by
      have h2 : qform B (fun j => exp ((1 - 2 / p) * y j)) i = exp (2 / p * y i) := by
        have he : exp ((1 - 2 / p) * y i) * exp (2 / p * y i) = exp (y i) := by
          rw [← exp_add]; congr 1; ring
        have hne : exp ((1 - 2 / p) * y i) ≠ 0 := (exp_pos _).ne'
        apply mul_left_cancel₀ hne
        rw [this, he]
      rw [h2, Real.log_exp]
    unfold lewisMap
    rw [hlog]; field_simp
  · intro h
    refine ⟨fun i => exp_pos _, fun i => ?_⟩
    rw [key]
    have hi := congrFun h i
    unfold lewisMap at hi
    have hlog : Real.log (qform B (fun j => exp ((1 - 2 / p) * y j)) i) = 2 / p * y i := by
      field_simp at hi ⊢; linarith
    have h2 : qform B (fun j => exp ((1 - 2 / p) * y j)) i = exp (2 / p * y i) := by
      rw [← hlog, Real.exp_log (hq i)]
    rw [h2, ← exp_add]; congr 1; ring

/-- **Existence and uniqueness of Lewis weights** for `0 < p < 2`. -/
theorem lewis_exists_unique (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p)
    (hp2 : p < 2) : ∃! w, IsLewis p B w := by
  have hK := lewisMap_contracting hB hrow hp0 hp2
  set y := ContractingWith.fixedPoint (lewisMap p B) hK
  have hy : lewisMap p B y = y := ContractingWith.fixedPoint_isFixedPt hK
  refine ⟨fun i => exp (y i), (isLewis_iff_fixed hB hrow hp0 y).mpr hy, ?_⟩
  intro w hw
  have hw' : (fun i => exp ((fun i => Real.log (w i)) i)) = w := by
    funext i; exact Real.exp_log (hw.1 i)
  have hfix : lewisMap p B (fun i => Real.log (w i)) = fun i => Real.log (w i) := by
    rw [← isLewis_iff_fixed hB hrow hp0, hw']; exact hw
  have := ContractingWith.fixedPoint_unique hK hfix
  rw [← hw', this]

end Lewis

end

end ImplicitLP
end CutQueryComplexity
