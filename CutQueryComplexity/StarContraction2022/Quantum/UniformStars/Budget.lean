import CutQueryComplexity.StarContraction2022.Quantum.ProductPrograms.Counts
import CutQueryComplexity.StarContraction2022.Adapters.Weighted

/-!
# Public schedules for guarded uniform stars

Every definition uses only the public vertex count. The weighted cap bounds
the actual adapter index, including its existing single verification query.
The exponential estimates are numerical bounds; they do not assert a bad-event
probability or replace the original sampling law by a conditioned law.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum.UniformStars

open scoped Classical
noncomputable section

/-- The sampling probability, total also when the public threshold is zero. -/
def centerProbability (n : ℕ) : ℝ :=
  min 1 (1200 * (ProductPrograms.logWidth n : ℝ) / ProductPrograms.rootThreshold n)

/-- Public guard checked before any center-neighborhood query. -/
def kcap (n : ℕ) : ℕ := min n ⌈2 * centerProbability n * (n : ℝ)⌉₊

/-- One weighted call, including the adapter's one original-value query. -/
def bmax (n : ℕ) : ℕ :=
  ⌈5000000 * (kcap n : ℝ) * Real.log (2 * (n : ℝ) + 2) ^ 2⌉₊ + 1

/-- Fixed virtual index for the later guarded high-degree program. -/
def QH (n : ℕ) : ℕ := kcap n + bmax n

/-- The numerical target retained for later pointwise weighted composition. -/
def pstar : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ (-13 : ℤ)

theorem centerProbability_nonneg (n : ℕ) : 0 ≤ centerProbability n := by
  unfold centerProbability
  apply le_min (by norm_num)
  positivity

theorem centerProbability_le_one (n : ℕ) : centerProbability n ≤ 1 :=
  min_le_left _ _

theorem centerProbability_le_ratio (n : ℕ) :
    centerProbability n ≤
      1200 * (ProductPrograms.logWidth n : ℝ) / ProductPrograms.rootThreshold n :=
  min_le_right _ _

theorem centerProbability_pos {n : ℕ} (hn : 2 ≤ n) : 0 < centerProbability n := by
  have hr : (0 : ℝ) < ProductPrograms.rootThreshold n := by
    exact_mod_cast ProductPrograms.rootThreshold_pos (show 0 < n by omega)
  have hL : (0 : ℝ) < ProductPrograms.logWidth n := by
    exact_mod_cast ProductPrograms.logWidth_pos n
  unfold centerProbability
  exact lt_min (by norm_num) (div_pos (by positivity) hr)

@[simp] theorem centerProbability_zero : centerProbability 0 = 0 := by
  simp [centerProbability, ProductPrograms.rootThreshold_zero]

@[simp] theorem centerProbability_one : centerProbability 1 = 1 := by
  have hr : ProductPrograms.rootThreshold 1 = 1 := by
    norm_num [ProductPrograms.rootThreshold]
  have hL : (1 : ℝ) ≤ ProductPrograms.logWidth 1 := by
    exact_mod_cast Nat.succ_le_of_lt (ProductPrograms.logWidth_pos 1)
  unfold centerProbability
  rw [hr, Nat.cast_one, div_one]
  exact min_eq_left (by linarith)

theorem kcap_le (n : ℕ) : kcap n ≤ n := Nat.min_le_left _ _

theorem kcap_le_ceil (n : ℕ) : kcap n ≤ ⌈2 * centerProbability n * (n : ℝ)⌉₊ :=
  Nat.min_le_right _ _

@[simp] theorem kcap_zero : kcap 0 = 0 := by simp [kcap]

@[simp] theorem kcap_one : kcap 1 = 1 := by
  norm_num [kcap, centerProbability_one]

@[simp] theorem bmax_zero : bmax 0 = 1 := by simp [bmax]

@[simp] theorem QH_zero : QH 0 = 1 := by simp [QH]

theorem bmax_pos (n : ℕ) : 0 < bmax n := by unfold bmax; omega

theorem kcap_le_QH (n : ℕ) : kcap n ≤ QH n := Nat.le_add_right _ _

theorem pstar_pos : 0 < pstar := by norm_num [pstar]

theorem pstar_le_half : pstar ≤ (1 / 2 : ℝ) := by norm_num [pstar]

/-- The identity branch retains all vertices and needs no large-mean premise. -/
theorem kcap_eq_n_of_probability_one {n : ℕ} (hp : centerProbability n = 1) :
    kcap n = n := by
  unfold kcap
  rw [hp]
  apply Nat.min_eq_left
  have h : (n : ℝ) ≤ (⌈2 * (1 : ℝ) * (n : ℝ)⌉₊ : ℝ) :=
    (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)] : (n : ℝ) ≤ 2 * (1 : ℝ) * n).trans
      (Nat.le_ceil _)
  exact_mod_cast h

theorem logWidth_ge_one (n : ℕ) : (1 : ℝ) ≤ ProductPrograms.logWidth n := by
  exact_mod_cast Nat.succ_le_of_lt (ProductPrograms.logWidth_pos n)

/-- Natural logarithms are bounded using the existing public binary width. -/
theorem log_add_two_le_logWidth (n : ℕ) :
    Real.log ((n : ℝ) + 2) ≤ ProductPrograms.logWidth n := by
  have hpow : (n : ℝ) + 2 ≤ (2 : ℝ) ^ ProductPrograms.logWidth n := by
    exact_mod_cast ProductPrograms.le_two_pow_logWidth n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n + 2) hpow
  rw [Real.log_pow] at hlog
  have htwo : Real.log 2 ≤ (1 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (ProductPrograms.logWidth n : ℝ) * Real.log 2 := hlog
    _ ≤ (ProductPrograms.logWidth n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _)
    _ = _ := by ring

theorem log_n_le_logWidth {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) ≤ ProductPrograms.logWidth n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (Real.log_le_log hn0 (by linarith : (n : ℝ) ≤ n + 2)).trans
    (log_add_two_le_logWidth n)

theorem log_double_nonneg (n : ℕ) : 0 ≤ Real.log (2 * (n : ℝ) + 2) :=
  Real.log_nonneg (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

theorem log_double_le_two_logWidth (n : ℕ) :
    Real.log (2 * (n : ℝ) + 2) ≤ 2 * ProductPrograms.logWidth n := by
  have harg : 2 * (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 2 := by
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 * n + 2) harg
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith [log_add_two_le_logWidth n]

theorem probability_times_size_le {n : ℕ} (hn : 2 ≤ n) :
    centerProbability n * n ≤
      1200 * Real.sqrt (n : ℝ) * ProductPrograms.logWidth n := by
  have hr : (0 : ℝ) < ProductPrograms.rootThreshold n := by
    exact_mod_cast ProductPrograms.rootThreshold_pos (show 0 < n by omega)
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hroot := ProductPrograms.sqrt_le_rootThreshold n
  have hnr : (n : ℝ) ≤ (ProductPrograms.rootThreshold n : ℝ) * Real.sqrt n := by
    nlinarith [mul_le_mul_of_nonneg_right hroot hs0]
  have hpr := (le_div_iff₀ hr).mp (centerProbability_le_ratio n)
  calc
    _ ≤ centerProbability n *
        ((ProductPrograms.rootThreshold n : ℝ) * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hnr (centerProbability_nonneg n)
    _ = (centerProbability n * ProductPrograms.rootThreshold n) * Real.sqrt n := by ring
    _ ≤ (1200 * (ProductPrograms.logWidth n : ℝ)) * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hpr hs0
    _ = _ := by ring

theorem kcap_le_mean_add_one (n : ℕ) :
    (kcap n : ℝ) ≤ 2 * centerProbability n * n + 1 := by
  have hcap : (kcap n : ℝ) ≤ (⌈2 * centerProbability n * (n : ℝ)⌉₊ : ℝ) := by
    exact_mod_cast kcap_le_ceil n
  have hnonneg : 0 ≤ 2 * centerProbability n * (n : ℝ) := by
    have := centerProbability_nonneg n
    positivity
  exact hcap.trans (Nat.ceil_lt_add_one hnonneg).le

theorem kcap_le_sqrt_logWidth {n : ℕ} (hn : 2 ≤ n) :
    (kcap n : ℝ) ≤ 2400 * Real.sqrt (n : ℝ) * ProductPrograms.logWidth n + 1 := by
  have h := probability_times_size_le hn
  have hc := kcap_le_mean_add_one n
  nlinarith

theorem kcap_le_sqrt_logWidth_mul {n : ℕ} (hn : 2 ≤ n) :
    (kcap n : ℝ) ≤ 2401 * Real.sqrt (n : ℝ) * ProductPrograms.logWidth n := by
  have hs : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))
  have hL := logWidth_ge_one n
  have hprod : (1 : ℝ) ≤ Real.sqrt (n : ℝ) * ProductPrograms.logWidth n := by
    simpa only [one_mul] using
      mul_le_mul hs hL (by norm_num : (0 : ℝ) ≤ 1)
        (Real.sqrt_nonneg (n : ℝ))
  have hc := kcap_le_sqrt_logWidth hn
  nlinarith

/-- A public quotient-size guard bounds the real source estimate first,
then the actual natural-number index. The one verification query is retained. -/
theorem weighted_budget_le_bmax {n q : ℕ} (hq : 2 ≤ q) (hcap : q ≤ kcap n) :
    WeightedAdapter.budget (Fin q) + 1 ≤ bmax n := by
  have hqn : q ≤ n := hcap.trans (kcap_le n)
  have hqR : (q : ℝ) ≤ kcap n := by exact_mod_cast hcap
  have hqnR : (q : ℝ) ≤ n := by exact_mod_cast hqn
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 * q + 2)
    (show 2 * (q : ℝ) + 2 ≤ 2 * (n : ℝ) + 2 by linarith)
  have hlog0 := log_double_nonneg q
  have hb := WeightedAdapter.source_budget_le (Q := Fin q)
    (by simpa only [Fintype.card_fin] using hq)
  have hbound : (WeightedAdapter.budget (Fin q) : ℝ) ≤
      5000000 * (kcap n : ℝ) * Real.log (2 * (n : ℝ) + 2) ^ 2 := by
    calc
      _ ≤ 5000000 * (q : ℝ) * Real.log (2 * (q : ℝ) + 2) ^ 2 := by
        simpa only [WeightedGraph.baseB, Fintype.card_fin] using hb
      _ ≤ _ := by gcongr
  have hceil := hbound.trans
    (Nat.le_ceil (5000000 * (kcap n : ℝ) * Real.log (2 * (n : ℝ) + 2) ^ 2))
  unfold bmax
  exact Nat.add_le_add_right (by exact_mod_cast hceil) 1

theorem guarded_branch_index {n q : ℕ} (R : Finset (Fin n))
    (hR : R.card ≤ kcap n) (hq : 2 ≤ q) (hcap : q ≤ kcap n) :
    R.card + (WeightedAdapter.budget (Fin q) + 1) ≤ QH n :=
  Nat.add_le_add hR (weighted_budget_le_bmax hq hcap)

/-- The actual finite product conversion preserves the adapter's index.
This cost holds for every product-answer table, not just graph replies. -/
theorem weighted_product_cost {n q : ℕ} (π : PublicQuotient (Fin n) (Fin q))
    (hq : 2 ≤ q) (hcap : q ≤ kcap n)
    (read : Finset (Fin n) → ProductAnswer n 1)
    {out : ProductPrograms.Candidate n × ℕ}
    (ho : out ∈ (RTree.run read (ProductPrograms.cutTreeToProduct
      (WeightedAdapter.program π (by simpa only [Fintype.card_fin] using hq)))).support) :
    out.2 ≤ bmax n :=
  (ProductPrograms.cutTreeToProduct_cost _ read ho).trans (weighted_budget_le_bmax hq hcap)

theorem bmax_le_log_envelope (n : ℕ) :
    (bmax n : ℝ) ≤
      5000000 * (kcap n : ℝ) * Real.log (2 * (n : ℝ) + 2) ^ 2 + 2 := by
  have hnonneg : 0 ≤ 5000000 * (kcap n : ℝ) * Real.log (2 * (n : ℝ) + 2) ^ 2 :=
    by positivity
  have hc := (Nat.ceil_lt_add_one hnonneg).le
  unfold bmax
  push_cast
  linarith

theorem QH_le_logWidth_envelope (n : ℕ) :
    (QH n : ℝ) ≤ (20000000 * (ProductPrograms.logWidth n : ℝ) ^ 2 + 1) * kcap n + 2 := by
  have hb := bmax_le_log_envelope n
  have hl := log_double_le_two_logWidth n
  have hl0 := log_double_nonneg n
  have hm : 5000000 * (kcap n : ℝ) * Real.log (2 * (n : ℝ) + 2) ^ 2 ≤
      5000000 * (kcap n : ℝ) * (2 * (ProductPrograms.logWidth n : ℝ)) ^ 2 := by
    gcongr
  unfold QH
  push_cast
  nlinarith

/-- The planned literal upper bound on the public natural-number schedule. -/
theorem QH_envelope {n : ℕ} (hn : 2 ≤ n) :
    (QH n : ℝ) ≤ 50000000000 * Real.sqrt (n : ℝ) *
      (ProductPrograms.logWidth n : ℝ) ^ 3 := by
  let s : ℝ := Real.sqrt (n : ℝ)
  let L : ℝ := ProductPrograms.logWidth n
  have hs : 1 ≤ s := by
    simpa only [s, Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))
  have hL : 1 ≤ L := logWidth_ge_one n
  have hL2 : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hsl3 : (1 : ℝ) ≤ s * L ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 ^ 3 := by norm_num
      _ ≤ s * L ^ 3 := by gcongr
  have hk : (kcap n : ℝ) ≤ 2401 * s * L := kcap_le_sqrt_logWidth_mul hn
  have hb : (QH n : ℝ) ≤ (20000000 * L ^ 2 + 1) * kcap n + 2 :=
    QH_le_logWidth_envelope n
  have hcoeff : 20000000 * L ^ 2 + 1 ≤ 20000001 * L ^ 2 := by linarith
  calc
    _ ≤ (20000000 * L ^ 2 + 1) * kcap n + 2 := hb
    _ ≤ (20000001 * L ^ 2) * (2401 * s * L) + 2 := by gcongr
    _ = 48020002401 * (s * L ^ 3) + 2 := by ring
    _ ≤ 50000000000 * s * L ^ 3 := by nlinarith

theorem probability_eq_ratio_of_lt_one {n : ℕ} (hp : centerProbability n < 1) :
    centerProbability n =
      1200 * (ProductPrograms.logWidth n : ℝ) / ProductPrograms.rootThreshold n := by
  unfold centerProbability at hp ⊢
  have hratio := (min_lt_iff.mp hp).resolve_left (lt_irrefl (1 : ℝ))
  exact min_eq_right hratio.le

theorem probability_mul_root {n : ℕ} (hn : 2 ≤ n) (hp : centerProbability n < 1) :
    centerProbability n * ProductPrograms.rootThreshold n =
      1200 * (ProductPrograms.logWidth n : ℝ) := by
  have hr : (0 : ℝ) < ProductPrograms.rootThreshold n := by
    exact_mod_cast ProductPrograms.rootThreshold_pos (show 0 < n by omega)
  rw [probability_eq_ratio_of_lt_one hp, div_mul_cancel₀ _ hr.ne']

theorem probability_mul_degree {n : ℕ} {δ : ℝ} (hn : 2 ≤ n)
    (hp : centerProbability n < 1) (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ) :
    1200 * (ProductPrograms.logWidth n : ℝ) ≤ centerProbability n * δ := by
  rw [← probability_mul_root hn hp]
  exact mul_le_mul_of_nonneg_left hδ (centerProbability_nonneg n)

/-- This is the numerical premise needed by the already checked quality theorem. -/
theorem quality_mean_bound {n : ℕ} {δ : ℝ} (hn : 2 ≤ n)
    (hp : centerProbability n < 1) (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ) :
    1200 * Real.log (n : ℝ) ≤ centerProbability n * δ := by
  have hl := log_n_le_logWidth hn
  have hm := probability_mul_degree hn hp hδ
  linarith

theorem size_error_le {n : ℕ} (hn : 2 ≤ n) (hp : centerProbability n < 1) :
    Real.exp (-centerProbability n * n / 3) ≤
      Real.exp (-400 * (ProductPrograms.logWidth n : ℝ)) := by
  have hroot : (ProductPrograms.rootThreshold n : ℝ) ≤ n := by
    exact_mod_cast ProductPrograms.rootThreshold_le_n n
  have hm := probability_mul_degree hn hp hroot
  apply Real.exp_le_exp.mpr
  nlinarith

theorem coverage_error_le {n : ℕ} {δ : ℝ} (hn : 2 ≤ n)
    (hp : centerProbability n < 1) (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ) :
    (n : ℝ) * Real.exp (-centerProbability n * δ) ≤
      Real.exp (-1199 * (ProductPrograms.logWidth n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := probability_mul_degree hn hp hδ
  have hl := log_n_le_logWidth hn
  calc
    _ = Real.exp (Real.log (n : ℝ) - centerProbability n * δ) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hn0]
      simp only [neg_mul]
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith

private theorem two_exp_neg_four_hundred_le :
    2 * Real.exp (-400 : ℝ) ≤ (3 : ℝ) ^ (-13 : ℤ) := by
  have he4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have he40 : (5 : ℝ) ^ 10 ≤ Real.exp 40 := by
    calc
      (5 : ℝ) ^ 10 ≤ Real.exp 4 ^ 10 := by gcongr
      _ = Real.exp 40 := by rw [← Real.exp_nat_mul]; norm_num
  have he400 : (2 : ℝ) * 3 ^ 13 ≤ Real.exp 400 := by
    have hmono : Real.exp (40 : ℝ) ≤ Real.exp 400 := Real.exp_le_exp.mpr (by norm_num)
    norm_num at he40 ⊢
    linarith
  calc
    _ = 2 / Real.exp (400 : ℝ) := by rw [Real.exp_neg]; ring
    _ ≤ 2 / ((2 : ℝ) * 3 ^ 13) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) he400
    _ = _ := by norm_num

/-- Arithmetic bound for later subtraction of size and coverage failure mass.
No probabilistic estimate or success premise is assumed in this theorem. -/
theorem bad_mass_envelope {n : ℕ} {δ : ℝ} (hn : 2 ≤ n)
    (hp : centerProbability n < 1) (hδ : (ProductPrograms.rootThreshold n : ℝ) ≤ δ) :
    Real.exp (-centerProbability n * n / 3) +
      (n : ℝ) * Real.exp (-centerProbability n * δ) ≤ (3 : ℝ) ^ (-13 : ℤ) := by
  have hL := logWidth_ge_one n
  have hs := size_error_le hn hp
  have hc := coverage_error_le hn hp hδ
  have hs' : Real.exp (-400 * (ProductPrograms.logWidth n : ℝ)) ≤ Real.exp (-400 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hc' : Real.exp (-1199 * (ProductPrograms.logWidth n : ℝ)) ≤ Real.exp (-400 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp (-400 : ℝ) + Real.exp (-400 : ℝ) := add_le_add (hs.trans hs') (hc.trans hc')
    _ = 2 * Real.exp (-400 : ℝ) := by ring
    _ ≤ _ := two_exp_neg_four_hundred_le

#print axioms centerProbability_pos
#print axioms kcap_eq_n_of_probability_one
#print axioms log_add_two_le_logWidth
#print axioms kcap_le_sqrt_logWidth
#print axioms weighted_budget_le_bmax
#print axioms guarded_branch_index
#print axioms weighted_product_cost
#print axioms QH_envelope
#print axioms quality_mean_bound
#print axioms size_error_le
#print axioms coverage_error_le
#print axioms bad_mass_envelope

end
end CutQueryComplexity.StarContraction2022.Quantum.UniformStars
