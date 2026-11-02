import CutQueryComplexity.ImplicitLP.LewisIter
import CutQueryComplexity.ImplicitLP.HiddenGram

/-! # Lewis iteration with leverage values from the sparsifier inverse (D7 items 4/5)

The audited draft's Lewis iteration (`lem:lewis`) evaluates
`log T(v)ᵢ = (p/2) log σᵢ(V^{1/2−1/p}B) + (1 − p/2) log vᵢ`, and the leverage values come from
the explicit sparsifier inverse rather than the exact Gram inverse.

* `invQuad_sandwich` (item 1): if `L` is symmetric positive definite, `P` is symmetric and
  `(1−η)P ⪯ L ⪯ (1+η)P` with `0 ≤ η < 1`, then `P` is positive definite and
  `(1+η)⁻¹ aᵀP⁻¹a ≤ aᵀL⁻¹a ≤ (1−η)⁻¹ aᵀP⁻¹a`. The proof uses the variational formula of
  `Lewis.lean` (`invQuad_le_of_quad_le`), never an abstract Loewner inversion.
* `abs_log_invQuad_sub_le`: for `a ≠ 0` and `η ≤ 1/2`, `|log aᵀP⁻¹a − log aᵀL⁻¹a| ≤ 2η`.
* `lewisMapApprox` (item 2) replaces `(BᵀW^aB)⁻¹` by `P⁻¹`. It equals the leverage form with
  the approximate leverage `σ̃ᵢ = sᵢ² bᵢᵀP⁻¹bᵢ` (`lewisMapApprox_eq_lev`) and is within `p η` of
  `lewisMap` in every coordinate (`lewisMapApprox_err`).
* `lewis_inexact_lev` (item 3): with fresh preconditioners `P_j` and outputs rounded to within
  `μ` (e.g. on the dyadic mesh `2^{-k}ℤ`, `dyadicRound`), the error is at most
  `(1−p/2)^j E₀ + (pη + μ)/(p/2)`.
* `lp_lewis_iter`, `lp_lewis_iter_note` (item 4): in the LP, `B = diag(1/s) A`, the Lewis Gram
  is the frozen Gram `gram A D_j` with `D_j = s⁻² e^{a y_j}` (`gram_diag_mul`), which splits as
  hidden Laplacian plus explicit part (`gram_split`). D4's output gives `η = 2ε`
  (`frozen_precond`). The leverage of a hidden pair row is the public pair formula `pairLev`
  of the explicit matrix `P⁻¹`, evaluated offline with no queries. With `1/2 ≤ p < 2`,
  `ε ≤ Δ/1024` and `μ ≤ Δ/256`, the per-iteration log error is at most `Δ/128` and the
  error after `j` steps is at most `(3/4)^j E₀ + Δ/32`.

The audited draft is the earlier, unpublished version of Section 15 of paper P4
(`papers/P4/subquadratic-directed-minimum-cuts.pdf`) checked in `docs/lee-sidford-audit/`;
labels such as `eq:barrier` are its own.
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Spectral

noncomputable section

section Inverse

variable {r : ℕ} {L P : Matrix (Fin r) (Fin r) ℝ}

theorem psd_of_pd {G : Matrix (Fin r) (Fin r) ℝ} (h : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x))
    (x : Fin r → ℝ) : 0 ≤ x ⬝ᵥ (G *ᵥ x) := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (h x hx).le

/-- The upper half of the sandwich makes `P` positive definite. -/
theorem quad_pos_of_sandwich (hLpos : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (L *ᵥ x)) {η : ℝ} (hη : 0 ≤ η)
    (hhi : ∀ x, x ⬝ᵥ (L *ᵥ x) ≤ (1 + η) * x ⬝ᵥ (P *ᵥ x)) (x : Fin r → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (P *ᵥ x) := by
  have h1 := hLpos x hx
  have h2 := hhi x
  by_contra h
  have h3 := not_lt.mp h
  nlinarith

/-- `aᵀG⁻¹a > 0` for positive definite `G` and `a ≠ 0`. -/
theorem invQuad_pos {G : Matrix (Fin r) (Fin r) ℝ} (h : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x))
    {a : Fin r → ℝ} (ha : a ≠ 0) : 0 < a ⬝ᵥ (G⁻¹ *ᵥ a) := by
  have hd := det_ne_zero_of_quad_pos h
  set x := G⁻¹ *ᵥ a
  have hx : G *ᵥ x = a := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), one_mulVec]
  have hx0 : x ≠ 0 := fun h0 => ha (by rw [← hx, h0, mulVec_zero])
  have := h x hx0
  rwa [hx, dotProduct_comm] at this

/-- **Inverse comparison** (item 1). -/
theorem invQuad_sandwich (hP : Pᵀ = P) (hL : Lᵀ = L)
    (hLpos : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (L *ᵥ x)) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hlo : ∀ x, (1 - η) * x ⬝ᵥ (P *ᵥ x) ≤ x ⬝ᵥ (L *ᵥ x))
    (hhi : ∀ x, x ⬝ᵥ (L *ᵥ x) ≤ (1 + η) * x ⬝ᵥ (P *ᵥ x)) (a : Fin r → ℝ) :
    (1 + η)⁻¹ * (a ⬝ᵥ (P⁻¹ *ᵥ a)) ≤ a ⬝ᵥ (L⁻¹ *ᵥ a) ∧
      a ⬝ᵥ (L⁻¹ *ᵥ a) ≤ (1 - η)⁻¹ * (a ⬝ᵥ (P⁻¹ *ᵥ a)) := by
  have hPpos := quad_pos_of_sandwich hLpos hη0 hhi
  have hLd := det_ne_zero_of_quad_pos hLpos
  have hPd := det_ne_zero_of_quad_pos hPpos
  constructor
  · have := invQuad_le_of_quad_le hL (psd_of_pd hLpos) hLd hPd (by linarith : (0 : ℝ) < 1 + η)
      hhi a
    rw [inv_mul_le_iff₀ (by linarith)]
    exact this
  · refine invQuad_le_of_quad_le hP (psd_of_pd hPpos) hPd hLd
      (inv_pos.mpr (by linarith : (0 : ℝ) < 1 - η)) (fun y => ?_) a
    rw [le_inv_mul_iff₀ (by linarith)]
    exact hlo y

theorem log_one_add_le_two_mul {η : ℝ} (hη0 : 0 ≤ η) : Real.log (1 + η) ≤ 2 * η := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + η)
  linarith

theorem log_inv_one_sub_le {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) :
    Real.log (1 - η)⁻¹ ≤ 2 * η := by
  have h1 : (0 : ℝ) < 1 - η := by linarith
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  have h2 : (1 - η)⁻¹ - 1 ≤ 2 * η := by
    rw [inv_eq_one_div, div_sub_one h1.ne', div_le_iff₀ h1]; nlinarith
  linarith

/-- **Log form of the inverse comparison:** `|log aᵀP⁻¹a − log aᵀL⁻¹a| ≤ 2η` for `η ≤ 1/2`. -/
theorem abs_log_invQuad_sub_le (hP : Pᵀ = P) (hL : Lᵀ = L)
    (hLpos : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (L *ᵥ x)) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hlo : ∀ x, (1 - η) * x ⬝ᵥ (P *ᵥ x) ≤ x ⬝ᵥ (L *ᵥ x))
    (hhi : ∀ x, x ⬝ᵥ (L *ᵥ x) ≤ (1 + η) * x ⬝ᵥ (P *ᵥ x)) {a : Fin r → ℝ} (ha : a ≠ 0) :
    |Real.log (a ⬝ᵥ (P⁻¹ *ᵥ a)) - Real.log (a ⬝ᵥ (L⁻¹ *ᵥ a))| ≤ 2 * η := by
  have hPpos := quad_pos_of_sandwich hLpos hη0 hhi
  have qP := invQuad_pos hPpos ha
  have qL := invQuad_pos hLpos ha
  obtain ⟨h1, h2⟩ := invQuad_sandwich hP hL hLpos hη0 (by linarith) hlo hhi a
  have hp1 : (0 : ℝ) < 1 + η := by linarith
  have hm1 : (0 : ℝ) < 1 - η := by linarith
  rw [abs_le]
  constructor
  · -- `log q_L ≤ log q_P + log (1−η)⁻¹`
    have := Real.log_le_log qL h2
    rw [Real.log_mul (inv_pos.mpr hm1).ne' qP.ne'] at this
    linarith [log_inv_one_sub_le hη0 hη]
  · -- `log q_P ≤ log q_L + log (1+η)`
    have h1' : a ⬝ᵥ (P⁻¹ *ᵥ a) ≤ (1 + η) * a ⬝ᵥ (L⁻¹ *ᵥ a) := by
      rw [inv_mul_le_iff₀ hp1] at h1; exact h1
    have := Real.log_le_log qP h1'
    rw [Real.log_mul hp1.ne' qL.ne'] at this
    linarith [log_one_add_le_two_mul hη0]

end Inverse

section Approx

variable {M r : ℕ} {B : Matrix (Fin M) (Fin r) ℝ} {p : ℝ}

/-- **The Lewis map with approximate leverages:** `(BᵀW^aB)⁻¹` is replaced by the explicit
inverse `P⁻¹` of a preconditioner, `T̃(y)ᵢ = (p/2) log bᵢᵀP⁻¹bᵢ`. -/
def lewisMapApprox (p : ℝ) (B : Matrix (Fin M) (Fin r) ℝ) (P : Matrix (Fin r) (Fin r) ℝ) :
    Fin M → ℝ :=
  fun i => p / 2 * Real.log (B i ⬝ᵥ (P⁻¹ *ᵥ B i))

/-- The approximate update in the audited draft's leverage form: with `sⱼ = e^{(1/2−1/p)yⱼ}` and the
approximate leverage `σ̃ᵢ = sᵢ² bᵢᵀP⁻¹bᵢ`,
`T̃(y)ᵢ = (p/2) log σ̃ᵢ + (1 − p/2) yᵢ`. -/
theorem lewisMapApprox_eq_lev {P : Matrix (Fin r) (Fin r) ℝ} (hp0 : 0 < p) (y : Fin M → ℝ)
    (i : Fin M) (hq : 0 < B i ⬝ᵥ (P⁻¹ *ᵥ B i)) :
    lewisMapApprox p B P i =
      p / 2 * Real.log (exp ((1 / 2 - 1 / p) * y i) ^ 2 * (B i ⬝ᵥ (P⁻¹ *ᵥ B i)))
        + (1 - p / 2) * y i := by
  have e : exp ((1 / 2 - 1 / p) * y i) ^ 2 = exp ((1 - 2 / p) * y i) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  rw [e, Real.log_mul (exp_pos _).ne' hq.ne', Real.log_exp, lewisMapApprox]
  field_simp
  ring

/-- **Leverage approximation** (item 2): if `(1−η)P ⪯ BᵀW^aB ⪯ (1+η)P` with `0 ≤ η ≤ 1/2`,
the approximate update is within `p η` of the Lewis map in every coordinate. -/
theorem lewisMapApprox_err (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p)
    {P : Matrix (Fin r) (Fin r) ℝ} (hP : Pᵀ = P) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (y : Fin M → ℝ)
    (hlo : ∀ x, (1 - η) * x ⬝ᵥ (P *ᵥ x) ≤
      x ⬝ᵥ (gram B (fun k => exp ((1 - 2 / p) * y k)) *ᵥ x))
    (hhi : ∀ x, x ⬝ᵥ (gram B (fun k => exp ((1 - 2 / p) * y k)) *ᵥ x) ≤
      (1 + η) * x ⬝ᵥ (P *ᵥ x)) (i : Fin M) :
    |lewisMapApprox p B P i - lewisMap p B y i| ≤ p * η := by
  have hLpos : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (gram B (fun k => exp ((1 - 2 / p) * y k)) *ᵥ x) :=
    fun x hx => gram_pos hB (fun k => exp_pos _) hx
  have h := abs_log_invQuad_sub_le hP (gram_symm _) hLpos hη0 hη hlo hhi (hrow i)
  unfold lewisMapApprox lewisMap qform
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < p / 2)]
  calc p / 2 * _ ≤ p / 2 * (2 * η) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = p * η := by ring

/-- Rounding down to the dyadic mesh `2^{-k}ℤ`. -/
def dyadicRound (k : ℕ) (x : ℝ) : ℝ := ⌊x * 2 ^ k⌋ / 2 ^ k

theorem abs_dyadicRound_sub_le (k : ℕ) (x : ℝ) : |dyadicRound k x - x| ≤ (1 / 2) ^ k := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have h1 := Int.floor_le (x * 2 ^ k)
  have h3 := Int.lt_floor_add_one (x * 2 ^ k)
  have e : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := _root_.one_div_pow 2 k
  have ha : (⌊x * 2 ^ k⌋ : ℝ) / 2 ^ k ≤ x := (div_le_iff₀ h2).mpr h1
  have hb : x - 1 / 2 ^ k ≤ (⌊x * 2 ^ k⌋ : ℝ) / 2 ^ k := by
    rw [le_div_iff₀ h2, sub_mul, one_div_mul_cancel h2.ne']; linarith
  rw [e, dyadicRound, abs_le]
  have : (0 : ℝ) ≤ 1 / 2 ^ k := by positivity
  constructor <;> linarith

/-- **The Lewis iteration with approximate leverages and rounding** (item 3). Iteration `j`
uses a fresh symmetric preconditioner `P j` of the current Lewis Gram with accuracy `η ≤ 1/2`,
and its output is within `μ` of the approximate update in every coordinate. Then
`‖y_j − y*‖_∞ ≤ (1 − p/2)^j ‖y₀ − y*‖_∞ + (pη + μ)/(p/2)`. -/
theorem lewis_inexact_lev (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p)
    (hp2 : p < 2) {η μ : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hμ : 0 ≤ μ)
    {y : ℕ → Fin M → ℝ} {P : ℕ → Matrix (Fin r) (Fin r) ℝ} (hP : ∀ j, (P j)ᵀ = P j)
    (hlo : ∀ j x, (1 - η) * x ⬝ᵥ (P j *ᵥ x) ≤
      x ⬝ᵥ (gram B (fun k => exp ((1 - 2 / p) * y j k)) *ᵥ x))
    (hhi : ∀ j x, x ⬝ᵥ (gram B (fun k => exp ((1 - 2 / p) * y j k)) *ᵥ x) ≤
      (1 + η) * x ⬝ᵥ (P j *ᵥ x))
    (hround : ∀ j i, |y (j + 1) i - lewisMapApprox p B (P j) i| ≤ μ)
    {ystar : Fin M → ℝ} (hfix : lewisMap p B ystar = ystar) (j : ℕ) :
    dist (y j) ystar ≤ (1 - p / 2) ^ j * dist (y 0) ystar + (p * η + μ) / (p / 2) := by
  have hζ : 0 ≤ p * η + μ := by positivity
  refine inexact_iter hB hrow hp0 hp2 hζ (fun j => ?_) hfix j
  refine (dist_pi_le_iff hζ).mpr fun i => ?_
  rw [Real.dist_eq]
  have h1 := hround j i
  have h2 := lewisMapApprox_err hB hrow hp0 (hP j) hη0 hη (y j) (hlo j) (hhi j) i
  calc |y (j + 1) i - lewisMap p B (y j) i|
      ≤ |y (j + 1) i - lewisMapApprox p B (P j) i| +
        |lewisMapApprox p B (P j) i - lewisMap p B (y j) i| := abs_sub_le _ _ _
    _ ≤ μ + p * η := add_le_add h1 h2
    _ = p * η + μ := add_comm _ _

/-- The same with the outputs rounded down to the dyadic mesh `2^{-k}ℤ`: `μ = 2^{-k}`. -/
theorem lewis_inexact_dyadic (hB : (Bᵀ * B).det ≠ 0) (hrow : ∀ i, B i ≠ 0) (hp0 : 0 < p)
    (hp2 : p < 2) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (k : ℕ)
    {y : ℕ → Fin M → ℝ} {P : ℕ → Matrix (Fin r) (Fin r) ℝ} (hP : ∀ j, (P j)ᵀ = P j)
    (hlo : ∀ j x, (1 - η) * x ⬝ᵥ (P j *ᵥ x) ≤
      x ⬝ᵥ (gram B (fun k => exp ((1 - 2 / p) * y j k)) *ᵥ x))
    (hhi : ∀ j x, x ⬝ᵥ (gram B (fun k => exp ((1 - 2 / p) * y j k)) *ᵥ x) ≤
      (1 + η) * x ⬝ᵥ (P j *ᵥ x))
    (hy : ∀ j i, y (j + 1) i = dyadicRound k (lewisMapApprox p B (P j) i))
    {ystar : Fin M → ℝ} (hfix : lewisMap p B ystar = ystar) (j : ℕ) :
    dist (y j) ystar ≤
      (1 - p / 2) ^ j * dist (y 0) ystar + (p * η + (1 / 2) ^ k) / (p / 2) :=
  lewis_inexact_lev hB hrow hp0 hp2 hη0 hη (by positivity) hP hlo hhi
    (fun j i => by rw [hy]; exact abs_dyadicRound_sub_le k _) hfix j

end Approx

section LP

variable {M n : ℕ}

/-- Row scaling commutes into the Gram weights: `gram (diag(s) A) d = gram A (s² d)`. -/
theorem gram_diag_mul (A : Matrix (Fin M) (Fin n) ℝ) (s d : Fin M → ℝ) :
    gram (diagonal s * A) d = gram A (fun i => s i ^ 2 * d i) := by
  simp only [gram, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal d) (diagonal s), diagonal_mul_diagonal,
    ← Matrix.mul_assoc (diagonal s) (diagonal _), diagonal_mul_diagonal]
  congr 3
  funext i; ring

theorem diag_mul_row (A : Matrix (Fin M) (Fin n) ℝ) (s : Fin M → ℝ) (i : Fin M) :
    (diagonal s * A) i = s i • A i := by
  funext k; simp [diagonal_mul]

/-- **The public pair formula** `a_eᵀQa_e = Σ_{j,k} (a_e a_eᵀ)_{jk} Q_{jk}`. For `Q = P⁻¹`
with `P` the explicit preconditioner, it is evaluated offline from `P` with no queries. -/
def pairLev (Q : Matrix (Fin n) (Fin n) ℝ) (e : Sym2 (Fin n)) : ℝ :=
  ∑ j, ∑ k, pairMat e j k * Q j k

theorem dot_mulVec_eq_pairLev {a : Fin n → ℝ} {e : Sym2 (Fin n)}
    (h : vecMulVec a a = pairMat e) (Q : Matrix (Fin n) (Fin n) ℝ) :
    a ⬝ᵥ (Q *ᵥ a) = pairLev Q e := by
  simp only [dotProduct, mulVec, pairLev, mul_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [← h, vecMulVec_apply]; ring

/-- **The approximate leverage values of the LP rows**, `bᵢᵀQbᵢ` for `B = diag(s) A`. A hidden
row `i` (`hid i = some e`) uses only the public pair formula `pairLev Q e` and the public scalar
`sᵢ`; duplicate copies of a pair get the same value. An explicit row uses its explicit row. -/
def lpLev (A : Matrix (Fin M) (Fin n) ℝ) (s : Fin M → ℝ) (hid : Fin M → Option (Sym2 (Fin n)))
    (Q : Matrix (Fin n) (Fin n) ℝ) (i : Fin M) : ℝ :=
  s i ^ 2 * (match hid i with
    | some e => pairLev Q e
    | none => A i ⬝ᵥ (Q *ᵥ A i))

theorem lpLev_eq {A : Matrix (Fin M) (Fin n) ℝ} {s : Fin M → ℝ}
    {hid : Fin M → Option (Sym2 (Fin n))}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (Q : Matrix (Fin n) (Fin n) ℝ) (i : Fin M) :
    lpLev A s hid Q i = (diagonal s * A) i ⬝ᵥ (Q *ᵥ (diagonal s * A) i) := by
  rw [diag_mul_row, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    lpLev]
  rcases h : hid i with _ | e
  · simp only; ring
  · simp only; rw [dot_mulVec_eq_pairLev (hrow i e h)]; ring

theorem explicitGram_psd (A : Matrix (Fin M) (Fin n) ℝ) {D : Fin M → ℝ} (hD : ∀ i, 0 ≤ D i)
    (hid : Fin M → Option (Sym2 (Fin n))) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (explicitGram A D hid *ᵥ x) := by
  rw [quad_explicitGram]
  exact sum_nonneg fun i _ => mul_nonneg (hD i) (sq_nonneg _)

theorem lap_transpose (ω : Sym2 (Fin n) → ℝ) (S : Finset (Sym2 (Fin n))) :
    (lap ω S)ᵀ = lap ω S := by
  have := (lap_isHermitian ω S).eq
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **The LP's Lewis iteration with leverages from D4's sparsifier** (item 4).
Here `B = diag(s) A` with `s` the inverse slacks, and iteration `j` has the Lewis Gram
`gram B e^{a y_j} = gram A D_j`, `D_j = s² e^{a y_j}` (`gram_diag_mul`), whose hidden part
carries the public frozen pair weights `w j` (`gram_split`). A `Good` D4 output `out j` for
`w j` gives the explicit preconditioner `P_j = lap(out j) + E_j` with `η = 2ε`
(`frozen_precond`). Each computed coordinate is within `μ` of `(p/2) log lpLev(P_j⁻¹)ᵢ`, which
for a hidden row is the public pair formula of `P_j⁻¹` (no queries). Then
`‖y_j − y*‖_∞ ≤ (1 − p/2)^j ‖y₀ − y*‖_∞ + (p(2ε) + μ)/(p/2)`. -/
theorem lp_lewis_iter {A : Matrix (Fin M) (Fin n) ℝ} {s : Fin M → ℝ} (hs : ∀ i, 0 < s i)
    (hB : ((diagonal s * A)ᵀ * (diagonal s * A)).det ≠ 0)
    (hrowB : ∀ i, (diagonal s * A) i ≠ 0)
    {hid : Fin M → Option (Sym2 (Fin n))} {G : DiGraph (Fin n)}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) {y : ℕ → Fin M → ℝ} {w : ℕ → Sym2 (Fin n) → ℝ}
    (hD : ∀ j i e, hid i = some e → s i ^ 2 * exp ((1 - 2 / p) * y j i) = w j e)
    (hw0 : ∀ j e, 0 ≤ w j e)
    {K t R : ℕ} {δ ε : ℝ} {out : ℕ → Sym2 (Fin n) → ℝ}
    (hgood : ∀ j, Sparsify.Good G (w j) K t δ R (out j))
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    {μ : ℝ} (hμ : 0 ≤ μ)
    (hround : ∀ j i, |y (j + 1) i - p / 2 * Real.log (lpLev A s hid
      (lap (out j) univ + explicitGram A (fun k => s k ^ 2 * exp ((1 - 2 / p) * y j k)) hid)⁻¹
      i)| ≤ μ)
    {ystar : Fin M → ℝ} (hfix : lewisMap p (diagonal s * A) ystar = ystar) (j : ℕ) :
    dist (y j) ystar ≤ (1 - p / 2) ^ j * dist (y 0) ystar + (p * (2 * ε) + μ) / (p / 2) := by
  set D : ℕ → Fin M → ℝ := fun j k => s k ^ 2 * exp ((1 - 2 / p) * y j k) with hDdef
  have hDpos : ∀ j k, 0 < D j k := fun j k => mul_pos (pow_pos (hs k) 2) (exp_pos _)
  set P : ℕ → Matrix (Fin n) (Fin n) ℝ := fun j => lap (out j) univ + explicitGram A (D j) hid
  have hPs : ∀ j, (P j)ᵀ = P j := fun j => by
    simp only [P, transpose_add, lap_transpose, explicitGram_symm]
  have hsplit : ∀ j, gram (diagonal s * A) (fun k => exp ((1 - 2 / p) * y j k)) =
      lap (Sparsify.omegaR G (w j) 0) (univ.filter fun e => Sparsify.P0 (w j) e = true) +
        explicitGram A (D j) hid := fun j => by
    rw [gram_diag_mul]
    exact gram_split hid G (w j) hrow (hD j) (hDpos j) hcount
  have hbd : ∀ j x, (1 - 2 * ε) * (x ⬝ᵥ (P j *ᵥ x)) ≤
        x ⬝ᵥ (gram (diagonal s * A) (fun k => exp ((1 - 2 / p) * y j k)) *ᵥ x) ∧
      x ⬝ᵥ (gram (diagonal s * A) (fun k => exp ((1 - 2 / p) * y j k)) *ᵥ x) ≤
        (1 + 2 * ε) * (x ⬝ᵥ (P j *ᵥ x)) := fun j x => by
    have h := frozen_precond (hgood j) (hw0 j) hε0 hε hδlo hδhi (1 : Matrix (Fin n) (Fin n) ℝ)
      (explicitGram_psd A (fun k => (hDpos j k).le) hid) x
    simp only [pullLap_one] at h
    rw [hsplit j]
    exact h
  refine lewis_inexact_lev hB hrowB hp0 hp2 (η := 2 * ε) (by linarith) (by linarith) hμ hPs
    (fun j x => (hbd j x).1) (fun j x => (hbd j x).2) (fun j i => ?_) hfix j
  have h := hround j i
  rw [lpLev_eq hrow] at h
  exact h

/-- **The audited draft's parameters** (`lem:lewis` and the Lewis-iteration paragraph). With
`1/2 ≤ p < 2`, `ε ≤ min(1/4, Δ/1024)` and mesh error `μ ≤ Δ/256`, the per-iteration log error
`p(2ε) + μ` is at most `Δ/128` and `‖y_j − y*‖_∞ ≤ (3/4)^j ‖y₀ − y*‖_∞ + Δ/32`. Hence, if
`‖y₀ − y*‖_∞ ≤ E₀` (e.g. `E₀ = log(1/q_*)` from a restart at `v = 1`, `restart_error`) and
`(3/4)^j E₀ ≤ Δ/32`, the final log error is at most `Δ/16`. -/
theorem lp_lewis_iter_note {A : Matrix (Fin M) (Fin n) ℝ} {s : Fin M → ℝ} (hs : ∀ i, 0 < s i)
    (hB : ((diagonal s * A)ᵀ * (diagonal s * A)).det ≠ 0)
    (hrowB : ∀ i, (diagonal s * A) i ≠ 0)
    {hid : Fin M → Option (Sym2 (Fin n))} {G : DiGraph (Fin n)}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp2 : p < 2) {y : ℕ → Fin M → ℝ} {w : ℕ → Sym2 (Fin n) → ℝ}
    (hD : ∀ j i e, hid i = some e → s i ^ 2 * exp ((1 - 2 / p) * y j i) = w j e)
    (hw0 : ∀ j e, 0 ≤ w j e)
    {K t R : ℕ} {δ ε : ℝ} {out : ℕ → Sym2 (Fin n) → ℝ}
    (hgood : ∀ j, Sparsify.Good G (w j) K t δ R (out j))
    {Δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hεΔ : ε ≤ Δ / 1024)
    (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε)
    {μ : ℝ} (hμ : 0 ≤ μ) (hμΔ : μ ≤ Δ / 256)
    (hround : ∀ j i, |y (j + 1) i - p / 2 * Real.log (lpLev A s hid
      (lap (out j) univ + explicitGram A (fun k => s k ^ 2 * exp ((1 - 2 / p) * y j k)) hid)⁻¹
      i)| ≤ μ)
    {ystar : Fin M → ℝ} (hfix : lewisMap p (diagonal s * A) ystar = ystar) (j : ℕ) :
    p * (2 * ε) + μ ≤ Δ / 128 ∧
      dist (y j) ystar ≤ (3 / 4) ^ j * dist (y 0) ystar + Δ / 32 ∧
      ∀ E₀, dist (y 0) ystar ≤ E₀ → (3 / 4) ^ j * E₀ ≤ Δ / 32 → dist (y j) ystar ≤ Δ / 16 := by
  have hζ : p * (2 * ε) + μ ≤ Δ / 128 := by nlinarith
  have h := lp_lewis_iter hs hB hrowB hrow hcount (by linarith) hp2 hD hw0 hgood hε0 hε hδlo
    hδhi hμ hround hfix j
  have hc : (1 - p / 2) ^ j ≤ (3 / 4) ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
  have hz : (p * (2 * ε) + μ) / (p / 2) ≤ Δ / 32 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ Δ := by linarith
    nlinarith
  have hmain : dist (y j) ystar ≤ (3 / 4) ^ j * dist (y 0) ystar + Δ / 32 :=
    h.trans (add_le_add (mul_le_mul_of_nonneg_right hc dist_nonneg) hz)
  refine ⟨hζ, hmain, fun E₀ hE₀ hj => ?_⟩
  have : (3 / 4 : ℝ) ^ j * dist (y 0) ystar ≤ (3 / 4) ^ j * E₀ :=
    mul_le_mul_of_nonneg_left hE₀ (by positivity)
  linarith

end LP

end

end ImplicitLP
end CutQueryComplexity
