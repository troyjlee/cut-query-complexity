import CutQueryComplexity.Discovery.ResidualPreparation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.Log
import Mathlib.Algebra.BigOperators.Field

/-! # Bucketed center selection: the mathematical core (Lemma 30)

* `cross_overlap` is `eq:overlapping-mass` for possibly overlapping sets, and
  `overlapMass_spec` evaluates it for the residual `G - K` with six cut queries.
* For row weights `ω` (the residual weights `w_R`), residual degrees `r`, and a center
  set `C`, `coef`, `pot`, `active`, `Phi` and `score` are `a_{vu}`, `p_v`, the active
  set, `Φ` and `σ`. Under relative lightness, `pot_gt_half` gives `p_v > 1/2`,
  `score_total` gives `∑_{u ∉ C} σ(u) ≥ (k/4) Φ`, and `Phi_insert_le` gives
  `Φ(C ∪ {u}) ≤ Φ(C) - σ(u)`.
* `rscore` is the surrogate `σ̃` with `θ_v = p_v / r_v` rounded down to a power of two;
  `half_score_le_rscore`, `rscore_le_score` give `σ/2 ≤ σ̃ ≤ σ`, `sum_rscore` is
  `eq:bucketed-score`, and `card_buckets_le` bounds the number of buckets.
* `select_bound`: a vertex of above-average surrogate score has `σ(u) ≥ (k/(8N)) Φ`.
* `avgSearch` is the balanced search for such a vertex from group totals.
* `pow_fuel_le`: after `⌈(8N/k) ln (2N)⌉` selections `N (1 - k/(8N))^s ≤ 1/2`.
-/

namespace CutQueryComplexity
namespace Discovery

open Search Search.Comp WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

section Overlap

/-- `eq:overlapping-mass`: with `I = A ∩ W`, `X = A \ W`, `Y = W \ A`, `Z = (A ∪ W)ᶜ`,
`m(A, W) = ∑_{v ∈ I} d_v - w(I, Z) + w(X, Y)`. -/
theorem cross_overlap (R : WeightedGraph V) (A W : Finset V) :
    R.cross A W = ∑ v ∈ A ∩ W, R.degree v - R.cross (A ∩ W) (A ∪ W)ᶜ +
      R.cross (A \ W) (W \ A) := by
  have hdeg : ∑ v ∈ A ∩ W, R.degree v = R.cross (A ∩ W) univ := by simp [cross, degree]
  have e1 : R.cross A W = R.cross (A ∩ W) W + R.cross (A \ W) W := by
    rw [← R.cross_union_left _ _ _ (by rw [Finset.disjoint_left]; intro x; simp; tauto)]
    congr 1; ext x; simp; tauto
  have e2 : R.cross (A \ W) W = R.cross (A \ W) (A ∩ W) + R.cross (A \ W) (W \ A) := by
    rw [← R.cross_union_right _ _ _ (by rw [Finset.disjoint_left]; intro x; simp; tauto)]
    congr 1; ext x; simp; tauto
  have e3 : R.cross (A ∩ W) univ =
      R.cross (A ∩ W) W + (R.cross (A ∩ W) (A \ W) + R.cross (A ∩ W) (A ∪ W)ᶜ) := by
    rw [← R.cross_union_right _ (A \ W) _ (by rw [Finset.disjoint_left]; intro x; simp; tauto),
      ← R.cross_union_right _ W _ (by rw [Finset.disjoint_left]; intro x; simp)]
    congr 1; ext x; simp; tauto
  rw [hdeg, e1, e2, e3, R.cross_comm (A \ W) (A ∩ W)]
  ring

/-- The residual weight between disjoint sets from three cut queries to `G`. -/
noncomputable def residualCross (K : WeightedGraph V) (S T : Finset V) :
    Comp (Finset V) ℝ ℝ :=
  (ask S).bind fun a => (ask T).bind fun b => (ask (S ∪ T)).bind fun c =>
    Comp.pure (((a - K.cut S) + (b - K.cut T) - (c - K.cut (S ∪ T))) / 2)

theorem residualCross_spec (G K : WeightedGraph V) (h : ∀ u v, K.w u v ≤ G.w u v)
    {S T : Finset V} (hST : Disjoint S T) :
    (residualCross K S T).eval G.cut = (G.subtract K).cross S T ∧
      (residualCross K S T).cost G.cut = 3 := by
  refine ⟨?_, by simp [residualCross]⟩
  simp only [residualCross, eval_bind, eval_ask, eval_pure]
  rw [(G.subtract K).cross_eq_three_cuts hST, cut_subtract G K h, cut_subtract G K h,
    cut_subtract G K h]

/-- The overlapping mass `m_R(A, W)` from the known residual degrees and six cut queries. -/
noncomputable def overlapMass (r : V → ℝ) (K : WeightedGraph V) (A W : Finset V) :
    Comp (Finset V) ℝ ℝ :=
  (residualCross K (A ∩ W) (A ∪ W)ᶜ).bind fun x =>
    (residualCross K (A \ W) (W \ A)).map fun y => ∑ v ∈ A ∩ W, r v - x + y

theorem overlapMass_spec (G K : WeightedGraph V) (h : ∀ u v, K.w u v ≤ G.w u v)
    {r : V → ℝ} (hr : ∀ v, r v = (G.subtract K).degree v) (A W : Finset V) :
    (overlapMass r K A W).eval G.cut = (G.subtract K).cross A W ∧
      (overlapMass r K A W).cost G.cut = 6 := by
  have h1 := residualCross_spec G K h (S := A ∩ W) (T := (A ∪ W)ᶜ)
    (by rw [Finset.disjoint_left]; intro x; simp; tauto)
  have h2 := residualCross_spec G K h (S := A \ W) (T := W \ A)
    (by rw [Finset.disjoint_left]; intro x; simp; tauto)
  simp only [overlapMass, eval_bind, eval_map, cost_bind, cost_map, h1.1, h1.2, h2.1, h2.2,
    hr, cross_overlap (G.subtract K) A W]
  exact ⟨trivial, trivial⟩

end Overlap

section Potential

/-- Weierstrass: `1 - ∑ x_i ≤ ∏ (1 - x_i)` for `x_i ∈ [0, 1]`. -/
theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (x : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ x i)
    (h1 : ∀ i ∈ s, x i ≤ 1) : 1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi))
      (fun i hi => h1 i (mem_insert_of_mem hi))
    have hs : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    have hxa0 := h0 a (mem_insert_self a s)
    have hxa1 := h1 a (mem_insert_self a s)
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr hxa1)]

variable (t : ℝ) (k : ℕ) (r : V → ℝ) (ω : V → V → ℝ)

/-- `a_{vu} = k ω(v, u) / (2 r_v)`. -/
noncomputable def coef (v u : V) : ℝ := k * ω v u / (2 * r v)

/-- `p_v = ∏_{c ∈ C} (1 - a_{vc})`. -/
noncomputable def pot (C : Finset V) (v : V) : ℝ := ∏ c ∈ C, (1 - coef k r ω v c)

/-- `b_v = w(v, C)`. -/
def bmass (C : Finset V) (v : V) : ℝ := ∑ c ∈ C, ω v c

/-- A vertex is active: `v ∉ C`, `r_v > t` and `b_v < r_v / k`. -/
def IsActive (C : Finset V) (v : V) : Prop := v ∉ C ∧ t < r v ∧ bmass ω C v < r v / k

open scoped Classical in
/-- The active vertices. -/
noncomputable def active (C : Finset V) : Finset V := univ.filter (IsActive t k r ω C)

/-- The potential `Φ = ∑_{v active} p_v`. -/
noncomputable def Phi (C : Finset V) : ℝ := ∑ v ∈ active t k r ω C, pot k r ω C v

/-- The score `σ(u) = ∑_{v active} p_v a_{vu}`. -/
noncomputable def score (C : Finset V) (u : V) : ℝ :=
  ∑ v ∈ active t k r ω C, pot k r ω C v * coef k r ω v u

/-- `θ_v = p_v / r_v`. -/
noncomputable def theta (C : Finset V) (v : V) : ℝ := pot k r ω C v / r v

/-- The bucket of `v`: `θ_v` rounds down to `2 ^ bucketOf v`. -/
noncomputable def bucketOf (C : Finset V) (v : V) : ℤ := Int.log 2 (theta k r ω C v)

/-- The surrogate score `σ̃(u) = (k/2) ∑_{v active} θ̃_v ω(v, u)`. -/
noncomputable def rscore (C : Finset V) (u : V) : ℝ :=
  k / 2 * ∑ v ∈ active t k r ω C, (2 : ℝ) ^ bucketOf k r ω C v * ω v u

/-- The bucket indices that occur. -/
noncomputable def buckets (C : Finset V) : Finset ℤ :=
  (active t k r ω C).image (bucketOf k r ω C)

/-- The active vertices of bucket `j`. -/
noncomputable def bucket (C : Finset V) (j : ℤ) : Finset V :=
  (active t k r ω C).filter fun v => bucketOf k r ω C v = j

variable {t k r ω}

omit [DecidableEq V] in
theorem mem_active {C : Finset V} {v : V} : v ∈ active t k r ω C ↔ IsActive t k r ω C v := by
  simp [active]

section Bounds

variable (hω : ∀ v u, 0 ≤ ω v u) (hlight : ∀ v, r v ≤ t ∨ ∀ u, ω v u ≤ r v / k)
  (ht : 0 ≤ t) (hk : 0 < k)
include hω ht

omit [Fintype V] [DecidableEq V] hω in
theorem r_pos {C : Finset V} {v : V} (hv : IsActive t k r ω C v) : 0 < r v :=
  lt_of_le_of_lt ht hv.2.1

omit [Fintype V] [DecidableEq V] in
theorem coef_nonneg {C : Finset V} {v : V} (hv : IsActive t k r ω C v) (u : V) :
    0 ≤ coef k r ω v u := by
  have := r_pos ht hv
  have := hω v u
  unfold coef; positivity

include hlight hk

omit [Fintype V] [DecidableEq V] hω in
theorem coef_le_half {C : Finset V} {v : V} (hv : IsActive t k r ω C v) (u : V) :
    coef k r ω v u ≤ 1 / 2 := by
  have hr := r_pos ht hv
  have hl := (hlight v).resolve_left (not_le.mpr hv.2.1) u
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold coef
  rw [div_le_iff₀ (by positivity)]
  calc (k : ℝ) * ω v u ≤ k * (r v / k) := mul_le_mul_of_nonneg_left hl hkR.le
    _ = 1 / 2 * (2 * r v) := by rw [mul_div_cancel₀ _ hkR.ne']; ring

omit [Fintype V] [DecidableEq V] hω in
theorem pot_nonneg {C : Finset V} {v : V} (hv : IsActive t k r ω C v) :
    0 ≤ pot k r ω C v :=
  prod_nonneg fun c _ => by linarith [coef_le_half hlight ht hk hv c]

omit [Fintype V] [DecidableEq V] in
theorem pot_le_one {C : Finset V} {v : V} (hv : IsActive t k r ω C v) :
    pot k r ω C v ≤ 1 :=
  prod_le_one₀ (fun c _ => by linarith [coef_le_half hlight ht hk hv c])
    fun c _ => by linarith [coef_nonneg hω ht hv c]

omit [Fintype V] [DecidableEq V] in
/-- An active vertex has `p_v > 1/2`. -/
theorem pot_gt_half {C : Finset V} {v : V} (hv : IsActive t k r ω C v) :
    1 / 2 < pot k r ω C v := by
  have hr := r_pos ht hv
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : ∑ c ∈ C, coef k r ω v c = k * bmass ω C v / (2 * r v) := by
    simp only [coef, ← Finset.sum_div, ← Finset.mul_sum, bmass]
  have hkb : k * bmass ω C v < r v := by
    have := mul_lt_mul_of_pos_left hv.2.2 hkR
    rwa [mul_div_cancel₀ _ hkR.ne'] at this
  have hlt : ∑ c ∈ C, coef k r ω v c < 1 / 2 := by
    rw [hsum, div_lt_iff₀ (by positivity)]; linarith
  have := one_sub_sum_le_prod C (coef k r ω v) (fun c _ => coef_nonneg hω ht hv c)
    fun c _ => by linarith [coef_le_half hlight ht hk hv c]
  unfold pot; linarith

omit [DecidableEq V] in
theorem score_nonneg (C : Finset V) (u : V) : 0 ≤ score t k r ω C u :=
  sum_nonneg fun _v hv => mul_nonneg (pot_nonneg hlight ht hk (mem_active.mp hv))
    (coef_nonneg hω ht (mem_active.mp hv) u)

omit [DecidableEq V] in
theorem Phi_le_card (C : Finset V) : Phi t k r ω C ≤ Fintype.card V := by
  calc Phi t k r ω C ≤ ∑ _v ∈ active t k r ω C, (1 : ℝ) :=
        sum_le_sum fun _v hv => pot_le_one hω hlight ht hk (mem_active.mp hv)
    _ = (active t k r ω C).card := by simp
    _ ≤ Fintype.card V := by exact_mod_cast card_le_univ _

omit [DecidableEq V] in
theorem Phi_gt_half {C : Finset V} (hne : (active t k r ω C).Nonempty) :
    1 / 2 < Phi t k r ω C := by
  obtain ⟨v, hv⟩ := hne
  calc (1 : ℝ) / 2 < pot k r ω C v := pot_gt_half hω hlight ht hk (mem_active.mp hv)
    _ ≤ _ := single_le_sum (fun x hx => pot_nonneg hlight ht hk (mem_active.mp hx)) hv

/-- `eq:center-total-score`: `∑_{u ∉ C} σ(u) ≥ (k/4) Φ` when `k ≥ 2` and the rows sum to
the degrees. -/
theorem score_total (hk2 : 2 ≤ k) (hsum : ∀ v, ∑ u, ω v u = r v) (C : Finset V) :
    k / 4 * Phi t k r ω C ≤ ∑ u ∈ Cᶜ, score t k r ω C u := by
  unfold score Phi
  rw [Finset.sum_comm, Finset.mul_sum]
  apply sum_le_sum
  intro v hv
  have hv := mem_active.mp hv
  have hr := r_pos ht hv
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  rw [← Finset.mul_sum]
  have hsc : ∑ u ∈ Cᶜ, coef k r ω v u = k * (r v - bmass ω C v) / (2 * r v) := by
    simp only [coef, ← Finset.sum_div, ← Finset.mul_sum]
    congr 2
    have := Finset.sum_add_sum_compl C (ω v)
    rw [hsum] at this
    unfold bmass; linarith
  rw [hsc]
  have hb0 : 0 ≤ bmass ω C v := sum_nonneg fun c _ => hω v c
  have hkb : k * bmass ω C v < r v := by
    have := mul_lt_mul_of_pos_left hv.2.2 (by linarith : (0 : ℝ) < k)
    rwa [mul_div_cancel₀ _ (by linarith : (k : ℝ) ≠ 0)] at this
  have hfrac : (k : ℝ) / 4 ≤ k * (r v - bmass ω C v) / (2 * r v) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hp := pot_nonneg hlight ht hk hv
  nlinarith

/-- Adding a center `u` decreases the potential by at least `σ(u)`. -/
theorem Phi_insert_le {C : Finset V} {u : V} (hu : u ∉ C) :
    Phi t k r ω (insert u C) ≤ Phi t k r ω C - score t k r ω C u := by
  have hsub : active t k r ω (insert u C) ⊆ active t k r ω C := by
    intro v hv
    rw [mem_active] at hv ⊢
    refine ⟨fun h => hv.1 (mem_insert_of_mem h), hv.2.1, lt_of_le_of_lt ?_ hv.2.2⟩
    unfold bmass
    rw [sum_insert hu]
    linarith [hω v u]
  have hpot : ∀ v, pot k r ω (insert u C) v = (1 - coef k r ω v u) * pot k r ω C v :=
    fun v => prod_insert hu
  calc Phi t k r ω (insert u C)
      = ∑ v ∈ active t k r ω (insert u C), (1 - coef k r ω v u) * pot k r ω C v :=
        sum_congr rfl fun v _ => hpot v
    _ ≤ ∑ v ∈ active t k r ω C, (1 - coef k r ω v u) * pot k r ω C v :=
        sum_le_sum_of_subset_of_nonneg hsub fun v hv _ =>
          mul_nonneg (by linarith [coef_le_half hlight ht hk (mem_active.mp hv) u])
            (pot_nonneg hlight ht hk (mem_active.mp hv))
    _ = Phi t k r ω C - score t k r ω C u := by
        unfold Phi score
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun v _ => by ring

omit [Fintype V] [DecidableEq V] in
theorem theta_pos {C : Finset V} {v : V} (hv : IsActive t k r ω C v) :
    0 < theta k r ω C v :=
  div_pos (lt_trans (by norm_num) (pot_gt_half hω hlight ht hk hv)) (r_pos ht hv)

omit [Fintype V] [DecidableEq V] in
theorem zpow_bucket_le {C : Finset V} {v : V} (hv : IsActive t k r ω C v) :
    (2 : ℝ) ^ bucketOf k r ω C v ≤ theta k r ω C v := by
  have := Int.zpow_log_le_self (b := 2) one_lt_two (theta_pos hω hlight ht hk hv)
  simpa [bucketOf] using this

omit [Fintype V] [DecidableEq V] hω hlight ht hk in
theorem theta_lt_zpow_bucket (C : Finset V) (v : V) :
    theta k r ω C v < 2 * (2 : ℝ) ^ bucketOf k r ω C v := by
  have := Int.lt_zpow_succ_log_self (R := ℝ) (b := 2) one_lt_two (theta k r ω C v)
  rw [zpow_add_one₀ (by norm_num)] at this
  simpa [bucketOf, mul_comm] using this

omit [DecidableEq V] hω hlight ht hk in
theorem score_eq_theta (C : Finset V) (u : V) :
    score t k r ω C u = k / 2 * ∑ v ∈ active t k r ω C, theta k r ω C v * ω v u := by
  rw [score, Finset.mul_sum]
  exact sum_congr rfl fun v _ => by unfold coef theta; ring

omit [DecidableEq V] in
/-- `σ̃ ≤ σ`. -/
theorem rscore_le_score (C : Finset V) (u : V) :
    rscore t k r ω C u ≤ score t k r ω C u := by
  rw [score_eq_theta, rscore]
  exact mul_le_mul_of_nonneg_left (sum_le_sum fun v hv =>
    mul_le_mul_of_nonneg_right (zpow_bucket_le hω hlight ht hk (mem_active.mp hv)) (hω v u))
    (by positivity)

omit [DecidableEq V] hlight ht in
/-- `σ / 2 ≤ σ̃`. -/
theorem half_score_le_rscore (C : Finset V) (u : V) :
    score t k r ω C u / 2 ≤ rscore t k r ω C u := by
  rw [score_eq_theta, rscore, mul_div_assoc, Finset.sum_div]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => ?_) (by positivity)
  have h1 := theta_lt_zpow_bucket (k := k) (r := r) (ω := ω) C v
  have h2 := hω v u
  nlinarith

/-- `select_bound`: a vertex `u ∉ C` whose surrogate score is at least the average over
`V \ C` has `σ(u) ≥ (k / (8N)) Φ`, in the form `k Φ ≤ 8 N σ(u)`. -/
theorem select_bound (hk2 : 2 ≤ k) (hsum : ∀ v, ∑ u, ω v u = r v) {C : Finset V} {u : V}
    (havg : ∑ x ∈ Cᶜ, rscore t k r ω C x ≤ rscore t k r ω C u * (Cᶜ).card) :
    k * Phi t k r ω C ≤ 8 * Fintype.card V * score t k r ω C u := by
  have h1 := score_total hω hlight ht hk hk2 hsum C
  have h2 : ∑ x ∈ Cᶜ, score t k r ω C x / 2 ≤ ∑ x ∈ Cᶜ, rscore t k r ω C x :=
    sum_le_sum fun x _ => half_score_le_rscore hω hk C x
  rw [← Finset.sum_div] at h2
  have h3 : 0 ≤ rscore t k r ω C u := le_trans
    (by have := score_nonneg hω hlight ht hk C u; positivity)
    (half_score_le_rscore hω hk C u)
  have h4 : ((Cᶜ).card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ _
  have h5 := rscore_le_score hω hlight ht hk C u
  have h6 : rscore t k r ω C u * (Cᶜ).card ≤ rscore t k r ω C u * Fintype.card V :=
    mul_le_mul_of_nonneg_left h4 h3
  have h7 : rscore t k r ω C u * Fintype.card V ≤ score t k r ω C u * Fintype.card V :=
    mul_le_mul_of_nonneg_right h5 (by positivity)
  nlinarith

end Bounds

omit [DecidableEq V] in
/-- `eq:bucketed-score`: the surrogate total over `W` is a combination of the overlapping
masses `m(A_j, W)` of the buckets. -/
theorem sum_rscore (C W : Finset V) :
    ∑ u ∈ W, rscore t k r ω C u = k / 2 * ∑ j ∈ buckets t k r ω C,
      (2 : ℝ) ^ j * ∑ v ∈ bucket t k r ω C j, ∑ u ∈ W, ω v u := by
  calc ∑ u ∈ W, rscore t k r ω C u
      = k / 2 * ∑ v ∈ active t k r ω C, (2 : ℝ) ^ bucketOf k r ω C v * ∑ u ∈ W, ω v u := by
        unfold rscore
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact sum_congr rfl fun v _ => by rw [Finset.mul_sum]
    _ = k / 2 * ∑ j ∈ buckets t k r ω C, ∑ v ∈ bucket t k r ω C j,
          (2 : ℝ) ^ bucketOf k r ω C v * ∑ u ∈ W, ω v u := by
        rw [buckets]
        unfold bucket
        rw [sum_fiberwise_of_maps_to fun v hv => mem_image_of_mem _ hv]
    _ = _ := by
        congr 1
        refine sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun v hv => ?_
        simp only [bucket, mem_filter] at hv
        rw [hv.2]

omit [DecidableEq V] in
/-- The number of buckets is at most `M + 1` when residual degrees of active vertices are
at most `D` and `2D ≤ t 2^M`. -/
theorem card_buckets_le (hω : ∀ v u, 0 ≤ ω v u) (hlight : ∀ v, r v ≤ t ∨ ∀ u, ω v u ≤ r v / k)
    (ht : 0 < t) (hk : 0 < k) {D : ℝ} {M : ℕ} (hD : ∀ v, r v ≤ D)
    (hM : 2 * D ≤ t * 2 ^ M) (C : Finset V) :
    (buckets t k r ω C).card ≤ M + 1 := by
  rcases (active t k r ω C).eq_empty_or_nonempty with h | ⟨v₀, hv₀⟩
  · simp [buckets, h]
  have hD0 : 0 < D := lt_of_lt_of_le (r_pos ht.le (mem_active.mp hv₀)) (hD v₀)
  have hlo := Int.zpow_log_le_self (R := ℝ) (b := 2) one_lt_two
    (by positivity : (0 : ℝ) < 1 / (2 * D))
  have hlo' := Int.lt_zpow_succ_log_self (R := ℝ) (b := 2) one_lt_two (1 / (2 * D))
  generalize Int.log 2 (1 / (2 * D)) = lo at hlo hlo'
  push_cast at hlo hlo'
  have hsub : buckets t k r ω C ⊆ Ico lo (lo + 1 + M) := by
    intro j hj
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hj
    have hv := mem_active.mp hv
    have hr := r_pos ht.le hv
    have hp := pot_gt_half hω hlight ht.le hk hv
    have hp1 := pot_le_one hω hlight ht.le hk hv
    have hθlo : 1 / (2 * D) < theta k r ω C v := by
      rw [theta, div_lt_div_iff₀ (by positivity) hr]
      nlinarith [hD v]
    have hθhi : theta k r ω C v < 1 / t := by
      rw [theta, div_lt_div_iff₀ hr ht]
      nlinarith [hv.2.1]
    have h1 : (2 : ℝ) ^ lo < 2 ^ (bucketOf k r ω C v + 1) := by
      have := theta_lt_zpow_bucket (k := k) (r := r) (ω := ω) C v
      rw [zpow_add_one₀ (by norm_num)]
      linarith
    have h2 : (2 : ℝ) ^ bucketOf k r ω C v < 2 ^ (lo + 1 + M) := by
      have hb := zpow_bucket_le hω hlight ht.le hk hv
      have ht' : 1 / t ≤ 2 ^ M * (1 / (2 * D)) := by
        rw [div_le_iff₀ ht]
        have : 2 ^ M * (1 / (2 * D)) * t = t * 2 ^ M / (2 * D) := by ring
        rw [this, le_div_iff₀ (by positivity)]
        linarith
      rw [zpow_add₀ (by norm_num), zpow_natCast]
      calc (2 : ℝ) ^ bucketOf k r ω C v < 1 / t := lt_of_le_of_lt hb hθhi
        _ ≤ 2 ^ M * (1 / (2 * D)) := ht'
        _ < 2 ^ M * 2 ^ (lo + 1) := mul_lt_mul_of_pos_left hlo' (by positivity)
        _ = _ := mul_comm _ _
    rw [zpow_lt_zpow_iff_right₀ one_lt_two] at h1 h2
    exact mem_Ico.mpr ⟨by omega, h2⟩
  calc (buckets t k r ω C).card ≤ (Ico lo (lo + 1 + M)).card := card_le_card hsub
    _ = M + 1 := by rw [Int.card_Ico]; omega

end Potential

section Termination

/-- After `F = ⌈(8N/k) ln (2N)⌉` selections, each shrinking `Φ` by the factor
`1 - k/(8N)`, the bound `N (1 - k/(8N))^F` is at most `1/2`. -/
theorem pow_fuel_le {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (hkN : k ≤ 8 * N) :
    (N : ℝ) * (1 - k / (8 * N)) ^ ⌈8 * N / k * Real.log (2 * N)⌉₊ ≤ 1 / 2 := by
  set F := ⌈(8 * N / k : ℝ) * Real.log (2 * N)⌉₊
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set x : ℝ := k / (8 * N)
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hkN
  have h1 : (1 - x) ^ F ≤ Real.exp (-x) ^ F :=
    pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg x) F
  rw [← Real.exp_nat_mul] at h1
  have hF : (8 * N / k : ℝ) * Real.log (2 * N) ≤ F := Nat.le_ceil _
  have hlog : Real.log (2 * N) ≤ F * x := by
    have : (8 * N / k : ℝ) * Real.log (2 * N) * x = Real.log (2 * N) := by
      simp only [x]; field_simp
    nlinarith
  have h2 : Real.exp (F * -x) ≤ 1 / (2 * N) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 1 / (2 * N)), Real.exp_le_exp,
      one_div, Real.log_inv]
    linarith
  calc (N : ℝ) * (1 - x) ^ F ≤ N * (1 / (2 * N)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hNR.le
    _ = 1 / 2 := by field_simp

theorem fuel_le {N k : ℕ} (hk : 0 < k) :
    (⌈8 * N / k * Real.log (2 * N)⌉₊ : ℝ) < 8 * N / k * Real.log (2 * N) + 1 := by
  have : 0 ≤ (8 * N / k : ℝ) * Real.log (2 * N) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ 2 * N := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast h
        linarith
      have := Real.log_nonneg this
      positivity
  exact Nat.ceil_lt_add_one this

end Termination

section AverageSearch

variable {Q A : Type}

/-- Balanced search for a vertex of at least average value, from group totals `grp`.
`m` is the known total over `W`; the half with the larger average is kept. -/
noncomputable def avgSearch (grp : Finset V → Comp Q A ℝ) (dflt : V) (W : List V) (m : ℝ) :
    Comp Q A V :=
  if W.length ≤ 1 then Comp.pure (W.headD dflt) else
    (grp (W.take (W.length / 2)).toFinset).bind fun a =>
      if (m - a) * (W.take (W.length / 2)).length ≤ a * (W.drop (W.length / 2)).length then
        avgSearch grp dflt (W.take (W.length / 2)) a
      else avgSearch grp dflt (W.drop (W.length / 2)) (m - a)
termination_by W.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

omit [Fintype V] in
/-- If `grp X` evaluates `∑_{u ∈ X} f u` with at most `c` queries and `τ |W| ≤ ∑_W f`, the
search returns `u ∈ W` with `τ ≤ f u`, using at most `c ⌈log₂ |W|⌉` queries. -/
theorem avgSearch_spec (o : Q → A) (grp : Finset V → Comp Q A ℝ) (dflt : V) (f : V → ℝ)
    {c : ℕ} (hgrp : ∀ X, (grp X).eval o = ∑ u ∈ X, f u) (hc : ∀ X, (grp X).cost o ≤ c)
    (τ : ℝ) :
    ∀ (n : ℕ) (W : List V) (m : ℝ), W.length ≤ n → W.Nodup → W ≠ [] →
      m = ∑ u ∈ W.toFinset, f u → τ * W.length ≤ m →
      (avgSearch grp dflt W m).eval o ∈ W ∧ τ ≤ f ((avgSearch grp dflt W m).eval o) ∧
      (avgSearch grp dflt W m).cost o ≤ c * Nat.clog 2 W.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W m hn hnd hne hm hτ
    rw [avgSearch]
    by_cases hW : W.length ≤ 1
    · simp only [hW, ↓reduceIte, eval_pure, cost_pure, zero_le, and_true]
      match W, hW, hne with
      | [w], _, _ => simp_all
    simp only [hW, ↓reduceIte, eval_bind, cost_bind, hgrp]
    set L := W.length
    set W₁ := W.take (L / 2)
    set W₂ := W.drop (L / 2)
    have hl₁ : W₁.length = L / 2 := by simp only [W₁, List.length_take, L]; omega
    have hl₂ : W₂.length = L - L / 2 := by simp only [W₂, List.length_drop, L]
    have hsplit : W = W₁ ++ W₂ := (List.take_append_drop _ _).symm
    have hnd' := hsplit ▸ hnd
    rw [List.nodup_append] at hnd'
    have hdisj : Disjoint W₁.toFinset W₂.toFinset :=
      List.disjoint_toFinset_iff_disjoint.mpr fun a h₁ h₂ => hnd'.2.2 a h₁ a h₂ rfl
    set a := ∑ u ∈ W₁.toFinset, f u
    have ha : m - a = ∑ u ∈ W₂.toFinset, f u := by
      rw [hm, hsplit, List.toFinset_append, Finset.sum_union hdisj]; ring
    have hne₁ : W₁ ≠ [] := fun h => by
      have := congrArg List.length h; simp only [List.length_nil] at this; omega
    have hne₂ : W₂ ≠ [] := fun h => by
      have := congrArg List.length h; simp only [List.length_nil] at this; omega
    have hl₁pos : (1 : ℝ) ≤ W₁.length := by rw [hl₁]; exact_mod_cast (by omega : 1 ≤ L / 2)
    have hl₂pos : (1 : ℝ) ≤ W₂.length := by
      rw [hl₂]; exact_mod_cast (by omega : 1 ≤ L - L / 2)
    have hLsum : (L : ℝ) = W₁.length + W₂.length := by
      have : W₁.length + W₂.length = L := by omega
      exact_mod_cast this.symm
    rw [hLsum] at hτ
    have hcost : ∀ l, l ≤ (L + 1) / 2 → c + c * Nat.clog 2 l ≤ c * Nat.clog 2 L := by
      intro l hl
      have := clog_half_succ_le (L := L) (l := l) (by omega) hl
      calc c + c * Nat.clog 2 l = c * (Nat.clog 2 l + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left c this
    by_cases hcmp : (m - a) * (W₁.length : ℝ) ≤ a * W₂.length
    · simp only [hcmp, ↓reduceIte]
      have hτ₁ : τ * W₁.length ≤ a := by
        by_contra hcon
        push Not at hcon
        have h1 : a * W₂.length < τ * W₁.length * W₂.length :=
          mul_lt_mul_of_pos_right hcon (by linarith)
        have h3 : m - a < τ * W₂.length := by
          by_contra h
          push Not at h
          have := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ W₁.length)
          nlinarith
        linarith
      obtain ⟨hmem, hf, hc'⟩ := ih (L / 2) (by omega) W₁ a (by omega) hnd'.1 hne₁ rfl hτ₁
      refine ⟨List.mem_of_mem_take hmem, hf, ?_⟩
      have := hcost W₁.length (by omega)
      have := hc W₁.toFinset
      omega
    · simp only [hcmp, ↓reduceIte]
      push Not at hcmp
      have hτ₂ : τ * W₂.length ≤ m - a := by
        by_contra hcon
        push Not at hcon
        have h1 : (m - a) * W₁.length < τ * W₂.length * W₁.length :=
          mul_lt_mul_of_pos_right hcon (by linarith)
        have h3 : a < τ * W₁.length := by
          by_contra h
          push Not at h
          have := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ W₂.length)
          nlinarith
        linarith
      obtain ⟨hmem, hf, hc'⟩ := ih (L - L / 2) (by omega) W₂ (m - a) (by omega) hnd'.2.1 hne₂
        ha hτ₂
      refine ⟨List.mem_of_mem_drop hmem, hf, ?_⟩
      have := hcost W₂.length (by omega)
      have := hc W₁.toFinset
      omega

end AverageSearch

end Discovery
end CutQueryComplexity
