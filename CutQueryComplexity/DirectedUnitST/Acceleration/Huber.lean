import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Order.Compact

/-! # The actual Huber potential and its quadratic models

The parameter `k > 0` is the reciprocal smoothing radius.  The definition is
the quadratic support formula with its explicit maximizing clipped coefficient;
no minimum, gradient oracle, or stationarity assertion is supplied as data.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Acceleration

open Finset

noncomputable section

variable {V : Type*} [Fintype V]

def dot (x y : V → ℝ) : ℝ := ∑ i, x i * y i
def sqNorm (x : V → ℝ) : ℝ := ∑ i, x i ^ 2
def sqDist (x y : V → ℝ) : ℝ := sqNorm (fun i => x i - y i)

theorem sqNorm_nonneg (x : V → ℝ) : 0 ≤ sqNorm x :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem sqDist_nonneg (x y : V → ℝ) : 0 ≤ sqDist x y := sqNorm_nonneg _

def clip (t : ℝ) : ℝ := max (-1) (min 1 t)

theorem clip_bounds (t : ℝ) : -1 ≤ clip t ∧ clip t ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_of_le {t : ℝ} (h : t ≤ -1) : clip t = -1 := by
  simp [clip, min_eq_right (by linarith : t ≤ 1), max_eq_left h]

theorem clip_of_ge {t : ℝ} (h : 1 ≤ t) : clip t = 1 := by
  simp [clip, min_eq_left h]

theorem clip_of_mem {t : ℝ} (hl : -1 ≤ t) (hu : t ≤ 1) : clip t = t := by
  simp [clip, min_eq_right hu, max_eq_right hl]

theorem clip_optimal (t q : ℝ) (hq : -1 ≤ q ∧ q ≤ 1) :
    (t - clip t) * (q - clip t) ≤ 0 := by
  by_cases hl : t ≤ -1
  · rw [clip_of_le hl]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hq.1])
  by_cases hu : 1 ≤ t
  · rw [clip_of_ge hu]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [hq.2])
  rw [clip_of_mem (by linarith) (by linarith)]
  simp

/-- Huber smoothing of `abs`, of radius `1/k`, in support-function form. -/
def huber (k t : ℝ) : ℝ := t * clip (k * t) - clip (k * t) ^ 2 / (2 * k)

theorem huber_support {k : ℝ} (hk : 0 < k) (t q : ℝ)
    (hq : -1 ≤ q ∧ q ≤ 1) :
    t * q - q ^ 2 / (2 * k) ≤ huber k t := by
  have ho := clip_optimal (k * t) q hq
  have hs := sq_nonneg (q - clip (k * t))
  have he : 2 * k * (huber k t - (t * q - q ^ 2 / (2 * k))) =
      -2 * (k * t - clip (k * t)) * (q - clip (k * t)) +
        (q - clip (k * t)) ^ 2 := by
    unfold huber
    field_simp [ne_of_gt hk]
    ring
  nlinarith

/-- The affine lower model, with the explicit clipped slope. -/
theorem huber_lower {k : ℝ} (hk : 0 < k) (x y : ℝ) :
    huber k x + clip (k * x) * (y - x) ≤ huber k y := by
  have h := huber_support hk y (clip (k * x)) (clip_bounds _)
  unfold huber at *
  nlinarith

/-- The global quadratic upper model, including transitions across both kinks. -/
theorem huber_upper {k : ℝ} (hk : 0 < k) (x y : ℝ) :
    huber k y ≤ huber k x + clip (k * x) * (y - x) + k / 2 * (y - x) ^ 2 := by
  have ho := clip_optimal (k * x) (clip (k * y)) (clip_bounds _)
  have hs := sq_nonneg (k * (y - x) - (clip (k * y) - clip (k * x)))
  have he : 2 * k * (huber k y - huber k x - clip (k * x) * (y - x)) =
      2 * (k * x - clip (k * x)) * (clip (k * y) - clip (k * x)) +
      2 * k * (clip (k * y) - clip (k * x)) * (y - x) -
      (clip (k * y) - clip (k * x)) ^ 2 := by
    unfold huber
    field_simp [ne_of_gt hk]
    ring
  nlinarith

theorem huber_eq_quadratic {k t : ℝ} (hk : 0 < k)
    (ht : |k * t| ≤ 1) : huber k t = k * t ^ 2 / 2 := by
  rw [huber, clip_of_mem (abs_le.mp ht).1 (abs_le.mp ht).2]
  field_simp [ne_of_gt hk]
  ring

theorem huber_eq_positive {k t : ℝ} (h : 1 ≤ k * t) :
    huber k t = t - 1 / (2 * k) := by simp [huber, clip_of_ge h]

theorem huber_eq_negative {k t : ℝ} (h : k * t ≤ -1) :
    huber k t = -t - 1 / (2 * k) := by simp [huber, clip_of_le h]

theorem huber_nonneg {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 ≤ huber k t := by
  simpa using huber_support hk t 0 (by norm_num)

theorem huber_abs_lower {k : ℝ} (hk : 0 < k) (t : ℝ) :
    |t| - 1 / (2 * k) ≤ huber k t := by
  rcases le_total 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using huber_support hk t 1 (by norm_num)
  · simpa [abs_of_nonpos ht] using huber_support hk t (-1) (by norm_num)

theorem huber_abs_upper {k : ℝ} (hk : 0 < k) (t : ℝ) : huber k t ≤ |t| := by
  have hb := clip_bounds (k * t)
  have hd : 0 ≤ clip (k * t) ^ 2 / (2 * k) := by positivity
  unfold huber
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    nlinarith
  · rw [abs_of_nonpos ht]
    nlinarith

section Graph

variable {E : Type*} [Fintype E] [DecidableEq V]

/-- Divergence of one shared signed coefficient per edge, with plus at `tail`. -/
def divergence (tail head : E → V) (w : E → ℝ) : V → ℝ :=
  fun i => ∑ e, ((if tail e = i then w e else 0) - (if head e = i then w e else 0))

theorem divergence_sum (tail head : E → V) (w : E → ℝ) :
    ∑ i, divergence tail head w i = 0 := by
  unfold divergence
  rw [sum_comm]
  simp [sum_sub_distrib]

theorem divergence_dot (tail head : E → V) (w : E → ℝ) (r : V → ℝ) :
    dot (divergence tail head w) r = ∑ e, w e * (r (tail e) - r (head e)) := by
  unfold dot divergence
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  simp [sub_mul, sum_sub_distrib, ite_mul, mul_sub]

def graphPotential (tail head : E → V) (u c : E → ℝ) (beta : V → ℝ)
    (k : ℝ) (r : V → ℝ) : ℝ :=
  (∑ e, u e * huber k (r (tail e) - r (head e) - c e)) - dot beta r + sqNorm r / 2

def graphGradient (tail head : E → V) (u c : E → ℝ) (beta : V → ℝ)
    (k : ℝ) (r : V → ℝ) : V → ℝ :=
  fun i => divergence tail head (fun e => u e * clip (k * (r (tail e) - r (head e) - c e))) i -
    beta i + r i

omit [DecidableEq V] in
private theorem quadratic_expansion (beta x y : V → ℝ) :
    -dot beta y + sqNorm y / 2 - (-dot beta x + sqNorm x / 2) =
      dot (fun i => -beta i + x i) (fun i => y i - x i) + sqDist y x / 2 := by
  unfold dot sqDist sqNorm
  simp only [sum_div, ← sum_neg_distrib, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  ring

private theorem gradient_dot (tail head : E → V) (u c : E → ℝ) (beta : V → ℝ)
    (k : ℝ) (x y : V → ℝ) :
    dot (graphGradient tail head u c beta k x) (fun i => y i - x i) =
      (∑ e, u e * clip (k * (x (tail e) - x (head e) - c e)) *
        ((y (tail e) - y (head e) - c e) - (x (tail e) - x (head e) - c e))) +
      dot (fun i => -beta i + x i) (fun i => y i - x i) := by
  have hd := divergence_dot tail head
    (fun e => u e * clip (k * (x (tail e) - x (head e) - c e))) (fun i => y i - x i)
  unfold graphGradient dot at *
  simp only [add_mul, sub_mul, neg_mul, sum_neg_distrib, sum_add_distrib, sum_sub_distrib] at *
  rw [hd]
  have hchange : ∀ e, (y (tail e) - x (tail e)) - (y (head e) - x (head e)) =
      (y (tail e) - y (head e) - c e) - (x (tail e) - x (head e) - c e) := by
    intros
    ring
  simp_rw [hchange]
  ring

/-- One-strong-convexity model of the actual regularized Huber graph potential. -/
theorem graphPotential_lower (tail head : E → V) (u c : E → ℝ) (beta : V → ℝ)
    {k : ℝ} (hk : 0 < k) (hu : ∀ e, 0 ≤ u e) (x y : V → ℝ) :
    graphPotential tail head u c beta k x +
      dot (graphGradient tail head u c beta k x) (fun i => y i - x i) + sqDist y x / 2 ≤
        graphPotential tail head u c beta k y := by
  have hh := sum_le_sum (s := (univ : Finset E)) fun e _ =>
    mul_le_mul_of_nonneg_left (huber_lower hk
      (x (tail e) - x (head e) - c e) (y (tail e) - y (head e) - c e)) (hu e)
  rw [gradient_dot]
  have he := quadratic_expansion beta x y
  simp only [mul_add, sum_add_distrib, ← mul_assoc] at hh
  unfold graphPotential
  linarith

/-- Smoothness of the same potential, from the explicit graph quadratic form. -/
theorem graphPotential_upper (tail head : E → V) (u c : E → ℝ) (beta : V → ℝ)
    {k B : ℝ} (hk : 0 < k) (hu : ∀ e, 0 ≤ u e)
    (hB : ∀ d : V → ℝ, (∑ e, u e * (d (tail e) - d (head e)) ^ 2) ≤ B * sqNorm d)
    (x y : V → ℝ) :
    graphPotential tail head u c beta k y ≤
      graphPotential tail head u c beta k x +
      dot (graphGradient tail head u c beta k x) (fun i => y i - x i) +
      (k * B + 1) / 2 * sqDist y x := by
  have hh := sum_le_sum (s := (univ : Finset E)) fun e _ =>
    mul_le_mul_of_nonneg_left (huber_upper hk
      (x (tail e) - x (head e) - c e) (y (tail e) - y (head e) - c e)) (hu e)
  have hb := mul_le_mul_of_nonneg_left (hB (fun i => y i - x i)) (by positivity : 0 ≤ k / 2)
  have he := quadratic_expansion beta x y
  have hdiff : ∀ e, (y (tail e) - y (head e) - c e) -
      (x (tail e) - x (head e) - c e) =
      (y (tail e) - x (tail e)) - (y (head e) - x (head e)) := by intros; ring
  simp only [mul_add, sum_add_distrib] at hh
  have hs : (∑ e, u e * (k / 2 *
      ((y (tail e) - y (head e) - c e) - (x (tail e) - x (head e) - c e)) ^ 2)) =
      k / 2 * ∑ e, u e * ((y (tail e) - x (tail e)) - (y (head e) - x (head e))) ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro e _
    rw [hdiff]
    ring
  rw [hs] at hh
  simp only [← mul_assoc] at hh
  rw [gradient_dot]
  unfold graphPotential sqDist at *
  nlinarith

/-- Feasible divergence gives a global coercive lower bound on the actual objective. -/
theorem graphPotential_coercive_lower (tail head : E → V) (u c z : E → ℝ)
    {k : ℝ} (hk : 1 ≤ k) (hu : ∀ e, 0 ≤ u e)
    (hc : ∀ e, |c e| ≤ 1) (hz : ∀ e, |z e| ≤ u e) (r : V → ℝ) :
    sqNorm r / 2 - (3 / 2) * ∑ e, u e ≤
      graphPotential tail head u c (divergence tail head z) k r := by
  have hkpos : 0 < k := by linarith
  have hdelta : 1 / (2 * k) ≤ (1 : ℝ) / 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * k) (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  have hpoint : ∀ e, -(3 / 2) * u e ≤
      u e * huber k (r (tail e) - r (head e) - c e) - z e * (r (tail e) - r (head e)) := by
    intro e
    let d := r (tail e) - r (head e)
    have ht : |d| ≤ |d - c e| + 1 := by
      have h := abs_add_le (d - c e) (c e)
      simp only [sub_add_cancel] at h
      linarith [hc e]
    have hzd : z e * d ≤ u e * |d| := by
      calc
        z e * d ≤ |z e * d| := le_abs_self _
        _ = |z e| * |d| := abs_mul _ _
        _ ≤ u e * |d| := mul_le_mul_of_nonneg_right (hz e) (abs_nonneg _)
    have hh := mul_le_mul_of_nonneg_left (huber_abs_lower hkpos (d - c e)) (hu e)
    have ht' := mul_le_mul_of_nonneg_left ht (hu e)
    have hdel' := mul_le_mul_of_nonneg_left hdelta (hu e)
    change -(3 / 2) * u e ≤ u e * huber k (d - c e) - z e * d
    nlinarith
  have hs := sum_le_sum (s := (univ : Finset E)) fun e _ => hpoint e
  simp only [sum_sub_distrib, ← mul_sum] at hs
  unfold graphPotential
  rw [divergence_dot]
  linarith

omit [DecidableEq V] in
theorem graphPotential_zero_le (tail head : E → V) (u c : E → ℝ) (beta : V → ℝ)
    {k : ℝ} (hk : 0 < k) (hu : ∀ e, 0 ≤ u e) (hc : ∀ e, |c e| ≤ 1) :
    graphPotential tail head u c beta k (fun _ => 0) ≤ ∑ e, u e := by
  have hs := sum_le_sum (s := (univ : Finset E)) fun e _ =>
    mul_le_mul_of_nonneg_left ((huber_abs_upper hk (-c e)).trans (by simpa using hc e)) (hu e)
  simpa [graphPotential, dot, sqNorm] using hs

/-- Initial energy bound from feasibility alone; no value or minimizer is queried. -/
theorem graphPotential_initial_energy (tail head : E → V) (u c z : E → ℝ)
    {k : ℝ} (hk : 1 ≤ k) (hu : ∀ e, 0 ≤ u e)
    (hc : ∀ e, |c e| ≤ 1) (hz : ∀ e, |z e| ≤ u e) (r : V → ℝ) :
    graphPotential tail head u c (divergence tail head z) k (fun _ => 0) -
      graphPotential tail head u c (divergence tail head z) k r + sqNorm r / 2 ≤
        (5 / 2) * ∑ e, u e := by
  have hlow := graphPotential_coercive_lower tail head u c z hk hu hc hz r
  have hzero := graphPotential_zero_le tail head u c (divergence tail head z)
    (show 0 < k by linarith) hu hc
  linarith

omit [DecidableEq V] in
theorem graphPotential_continuous (tail head : E → V) (u c : E → ℝ) (beta : V → ℝ) (k : ℝ) :
    Continuous (graphPotential tail head u c beta k) := by
  unfold graphPotential dot sqNorm huber clip
  fun_prop

/-- Existence is proved on an explicit compact box; the witness is analysis-only. -/
theorem graphPotential_exists_minimizer (tail head : E → V) (u c z : E → ℝ)
    {k : ℝ} (hk : 1 ≤ k) (hu : ∀ e, 0 ≤ u e)
    (hc : ∀ e, |c e| ≤ 1) (hz : ∀ e, |z e| ≤ u e) :
    ∃ r, ∀ x, graphPotential tail head u c (divergence tail head z) k r ≤
      graphPotential tail head u c (divergence tail head z) k x := by
  let M := ∑ e, u e
  let R := M + 3
  let F := graphPotential tail head u c (divergence tail head z) k
  have hM : 0 ≤ M := sum_nonneg fun e _ => hu e
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have hzero : F (fun _ => 0) ≤ M :=
    graphPotential_zero_le tail head u c _ (by linarith) hu hc
  have hmem : (fun _ : V => (0 : ℝ)) ∈ Set.Icc (fun _ => -R) (fun _ => R) := by
    constructor <;> intro i <;> dsimp <;> linarith
  obtain ⟨r, hr, hmin⟩ := (isCompact_Icc :
    IsCompact (Set.Icc (fun _ : V => -R) (fun _ => R))).exists_isMinOn ⟨_, hmem⟩
      (graphPotential_continuous tail head u c _ k).continuousOn
  refine ⟨r, fun x => ?_⟩
  by_cases hx : F (fun _ => 0) ≤ F x
  · exact (hmin hmem).trans hx
  · have hlow := graphPotential_coercive_lower tail head u c z hk hu hc hz x
    have hsq : sqNorm x ≤ 5 * M := by change sqNorm x / 2 - (3 / 2) * M ≤ F x at hlow; linarith
    have hxbox : x ∈ Set.Icc (fun _ => -R) (fun _ => R) := by
      have hi : ∀ i, -R ≤ x i ∧ x i ≤ R := by
        intro i
        have hi := single_le_sum (fun j (_ : j ∈ (univ : Finset V)) => sq_nonneg (x j)) (mem_univ i)
        have hR2 : (x i) ^ 2 ≤ R ^ 2 := by
          change (x i) ^ 2 ≤ sqNorm x at hi
          dsimp [R]
          nlinarith [sq_nonneg M]
        exact abs_le_of_sq_le_sq' hR2 hR
      exact ⟨fun i => (hi i).1, fun i => (hi i).2⟩
    exact hmin hxbox

end Graph

section Canonical

/-- Rewrite a canonical-pair sum as an ordinary upper-triangular sum. -/
theorem sum_canonical {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ e : {ij : Fin n × Fin n // ij.1 < ij.2}, f e.val) =
      ∑ i, ∑ j, if i < j then f (i, j) else 0 := by
  have h := (sum_subtype (p := fun ij : Fin n × Fin n => ij.1 < ij.2) (F := inferInstance)
    (univ.filter fun ij : Fin n × Fin n => ij.1 < ij.2)
    (by simp) f).symm
  simpa only [sum_filter, Fintype.sum_prod_type] using h

/-- Each vertex is incident to at most `n` canonical pairs. -/
theorem canonical_endpoint_sq_le {n : ℕ} (d : Fin n → ℝ) :
    (∑ e : {ij : Fin n × Fin n // ij.1 < ij.2}, (d e.val.1 ^ 2 + d e.val.2 ^ 2)) ≤
      n * sqNorm d := by
  rw [sum_canonical (fun ij : Fin n × Fin n => d ij.1 ^ 2 + d ij.2 ^ 2)]
  have split : (∑ i : Fin n, ∑ j : Fin n, if i < j then d i ^ 2 + d j ^ 2 else 0) =
      (∑ i, ∑ j, if i < j then d i ^ 2 else 0) +
      (∑ i, ∑ j, if i < j then d j ^ 2 else 0) := by
    simp only [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [split, sum_comm (f := fun i j : Fin n => if i < j then d j ^ 2 else 0),
    ← sum_add_distrib]
  calc
    (∑ i : Fin n, ((∑ j, if i < j then d i ^ 2 else 0) +
        ∑ j, if j < i then d i ^ 2 else 0)) ≤ ∑ i : Fin n, ∑ _j : Fin n, d i ^ 2 := by
      apply sum_le_sum
      intro i _
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro j _
      rcases lt_trichotomy i j with h | h | h
      · simp [h, not_lt.mpr (le_of_lt h)]
      · subst j
        simp [sq_nonneg]
      · simp [h, not_lt.mpr (le_of_lt h)]
    _ = n * sqNorm d := by simp [sqNorm, ← mul_sum]

/-- The simple directed graph's pair capacities `u ≤ 2` give the `4n` Laplacian bound. -/
theorem canonical_laplacian_bound {n : ℕ}
    (u : {ij : Fin n × Fin n // ij.1 < ij.2} → ℝ)
    (hu : ∀ e, 0 ≤ u e ∧ u e ≤ 2) (d : Fin n → ℝ) :
    (∑ e, u e * (d e.val.1 - d e.val.2) ^ 2) ≤ (4 * n) * sqNorm d := by
  calc
    (∑ e, u e * (d e.val.1 - d e.val.2) ^ 2) ≤
        ∑ e : {ij : Fin n × Fin n // ij.1 < ij.2}, 4 * (d e.val.1 ^ 2 + d e.val.2 ^ 2) := by
      apply sum_le_sum
      intro e _
      have hm := mul_le_mul_of_nonneg_right (hu e).2 (sq_nonneg (d e.val.1 - d e.val.2))
      nlinarith [sq_nonneg (d e.val.1 + d e.val.2)]
    _ = 4 * ∑ e : {ij : Fin n × Fin n // ij.1 < ij.2},
        (d e.val.1 ^ 2 + d e.val.2 ^ 2) := by rw [mul_sum]
    _ ≤ 4 * (n * sqNorm d) := mul_le_mul_of_nonneg_left (canonical_endpoint_sq_le d) (by norm_num)
    _ = (4 * n) * sqNorm d := by ring

end Canonical

end

#print axioms graphPotential_lower
#print axioms graphPotential_upper
#print axioms graphPotential_initial_energy
#print axioms graphPotential_exists_minimizer
#print axioms canonical_laplacian_bound

end CutQueryComplexity.DirectedUnitST.Acceleration
