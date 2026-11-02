import CutQueryComplexity.Sparsification.Weighted
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Explicit parameters: failure at most `(2n+2)^{−s}`

Fix `s ≥ 0` and `0 < ε ≤ 1`, and write `B = 2n + 2`, `L = ln B`. The parameters

```text
ρ = 128 (s+8) L,       δ₀ = 4(2n)² B^{−(s+8)},       δ = B^{−(s+1)},
c = 8 (2 ln 2n + ln(4/δ)) / ε²,       R = ⌈ρn²⌉,
```

satisfy every hypothesis of `sparsify_sparse`. The resulting failure probability is
at most `B^{−s} ≤ n^{−s}`: the estimation term is at most `(34/256)·B^{−s}` and the
output term is at most `B^{−s}/2`. Here `ρ = Θ(s log n)` and
`c = Θ(s log n/ε²)`. So the hard cap `capQ` is `O(s·n log² n·(1 + 1/ε²))` and
the edge bound is `O(s·n log n/ε²)`.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V]

/-- The base `B = 2n + 2`. -/
abbrev baseB (V : Type) [Fintype V] : ℝ := 2 * Fintype.card V + 2

def paramρ (V : Type) [Fintype V] (s : ℝ) : ℝ := 128 * (s + 8) * Real.log (baseB V)
def paramδ₀ (V : Type) [Fintype V] (s : ℝ) : ℝ :=
  4 * ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * baseB V ^ (-(s + 8))
def paramδ (V : Type) [Fintype V] (s : ℝ) : ℝ := baseB V ^ (-(s + 1))
def paramc (V : Type) [Fintype V] (s ε : ℝ) : ℝ :=
  8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / paramδ V s)) / ε ^ 2
def paramR (V : Type) [Fintype V] (s : ℝ) : ℕ := ⌈paramρ V s * (Fintype.card V : ℝ) ^ 2⌉₊

theorem baseB_ge (V : Type) [Fintype V] : 2 ≤ baseB V := by
  have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  simp only [baseB]
  linarith

theorem exp_paramρ (V : Type) [Fintype V] (s : ℝ) (k : ℝ) :
    Real.exp (-(paramρ V s / k)) = baseB V ^ (-(128 * (s + 8) / k)) := by
  rw [Real.rpow_def_of_pos (by linarith [baseB_ge V]), paramρ]
  congr 1
  ring

theorem fuel_arith (m : ℕ) (hm : 1 ≤ m) :
    1 + (m + 1) * ((m + 1) * (m ^ 2 + 2)) ≤ 2 * (m + 1) ^ 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  ring_nf
  nlinarith [sq_nonneg k]

theorem fuelBound_le (hn : 1 ≤ Fintype.card V) :
    fuelBound V ≤ 2 * (Fintype.card V + 1) ^ 4 := by
  unfold fuelBound potWidth
  set m := Fintype.card V
  have hlog : Nat.log 2 (m ^ 2) ≤ m ^ 2 := (Nat.log_lt_self 2 (by positivity)).le
  have h1 : (m + 1) * ((m + 1) * (Nat.log 2 (m ^ 2) + 2)) ≤ (m + 1) * ((m + 1) * (m ^ 2 + 2)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have h2 : 1 + (m + 1) * ((m + 1) * (m ^ 2 + 2)) ≤ 2 * (m + 1) ^ 4 := fuel_arith m hn
  omega

theorem log_baseB_pos (V : Type) [Fintype V] : 0 < Real.log (baseB V) :=
  Real.log_pos (by linarith [baseB_ge V])

/-- **Explicit-parameter weighted sparsification.** For `n ≥ 1`, `s ≥ 0`, and
`0 < ε ≤ 1`, the capped algorithm outputs a `1 ± ε` cut sparsifier with at most
`⌊4c(n−1) + n⌋` edges, except with probability at most `(2n+2)^{−s}`. -/
theorem sparsify_whp (G : WeightedGraph V) (hn : 1 ≤ Fintype.card V) {s ε : ℝ} (hs : 0 ≤ s)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Probability.mass
      ((sparsify (paramρ V s) (paramc V s ε) (paramR V s)
        ⌈2 * paramc V s ε * (Fintype.card V : ℝ) ^ 2⌉₊
          (capQ V (paramρ V s) (paramc V s ε))).eval G.cut)
      (fun o => ¬∃ X, o = some X ∧
        IsSparseCutSparsifier ε (edgeBound V (paramc V s ε)) G X) ≤
        ENNReal.ofReal (baseB V ^ (-s)) := by
  set n := Fintype.card V
  set B := baseB V
  have hB2 : 2 ≤ B := baseB_ge V
  have hB0 : 0 < B := by linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := log_baseB_pos V
  -- Powers of `B`.
  set x := B ^ (-s) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hB0 _
  have hpow8 : B ^ (-(s + 8)) = x / B ^ 8 := by
    rw [show -(s + 8) = -s + -((8 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add hB0,
      Real.rpow_neg hB0.le ((8 : ℕ) : ℝ), Real.rpow_natCast, ← hx, div_eq_mul_inv]
  have hpow1 : B ^ (-(s + 1)) = x / B := by
    rw [show -(s + 1) = -s + -(1 : ℝ) by ring, Real.rpow_add hB0, Real.rpow_neg_one]
    ring
  have hpowle : B ^ (-(4 * (s + 8))) ≤ B ^ (-(s + 8)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hBn : B = 2 * (n + 1) := by simp only [B, baseB]; ring
  -- Hypotheses of the general theorem.
  have hρ : 2 ≤ paramρ V s := by
    have hl : 1 ≤ Real.log B := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ B by
        simp only [B, baseB]; linarith)
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      norm_num at this
      linarith
    simp only [paramρ]
    nlinarith
  have hR : paramρ V s * (n : ℝ) ^ 2 ≤ paramR V s := Nat.le_ceil _
  have hexp' : ((2 * n : ℕ) : ℝ) ^ 2 * Real.exp (-(paramρ V s / 128)) = paramδ₀ V s / 4 := by
    rw [exp_paramρ, paramδ₀, show 128 * (s + 8) / 128 = s + 8 by ring]
    ring
  have hn2 : ((2 * n : ℕ) : ℝ) ^ 2 ≤ B ^ 2 := by
    push_cast
    nlinarith
  have hδ₀0 : 0 ≤ paramδ₀ V s := by unfold paramδ₀; positivity
  have hδ₀2 : paramδ₀ V s ≤ 2 := by
    unfold paramδ₀
    rw [hpow8]
    have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hB6 : (64 : ℝ) ≤ B ^ 6 := by
      calc (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ B ^ 6 := pow_le_pow_left₀ (by norm_num) hB2 6
    have : 4 * ((2 * n : ℕ) : ℝ) ^ 2 * (x / B ^ 8) ≤ 4 * B ^ 2 * (1 / B ^ 8) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hn2 (by norm_num)) _ (by positivity)
        (by positivity)
      exact div_le_div_of_nonneg_right hx1 (by positivity)
    calc _ ≤ 4 * B ^ 2 * (1 / B ^ 8) := this
      _ = 4 / B ^ 6 := by field_simp
      _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hδ0 : 0 < paramδ V s := Real.rpow_pos_of_pos hB0 _
  have hδ2 : paramδ V s ≤ 2 := by
    have : paramδ V s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    linarith
  have hlog : 8 * (2 * Real.log (2 * n) + Real.log (4 / paramδ V s)) ≤
      ε ^ 2 * paramc V s ε := by
    rw [paramc, mul_div_cancel₀]
    positivity
  have hc : 0 < paramc V s ε := by
    have h4 : 1 ≤ 4 / paramδ V s := by
      rw [le_div_iff₀ hδ0]
      linarith
    have : 0 ≤ Real.log (4 / paramδ V s) := Real.log_nonneg h4
    have : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
    unfold paramc
    apply div_pos _ (by positivity)
    have : 0 < Real.log (4 / paramδ V s) := Real.log_pos (by
      rw [lt_div_iff₀ hδ0]
      have : paramδ V s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      linarith)
    positivity
  have hmain := sparsify_sparse G hρ hR hδ₀0 hδ₀2 hexp'.le hc hε.le hε1 hδ0 hδ2 hlog
  refine hmain.trans ?_
  -- Numerical bound on the failure probability.
  have hfuel : (fuelBound V : ℝ) ≤ 2 * (n + 1) ^ 4 := by
    exact_mod_cast fuelBound_le hn
  have hcf : callFailure V (paramρ V s) (paramδ₀ V s) =
      ENNReal.ofReal (n * Real.exp (-(paramρ V s / 32)) +
        n * ((n - 1 : ℕ) * paramδ₀ V s)) := by
    have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        ENNReal.ofReal (n * a + n * b) = n * ENNReal.ofReal a + n * ENNReal.ofReal b := by
      intro a b ha hb
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    rw [key _ _ (by positivity) (by positivity)]
    rfl
  rw [hcf, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- Estimation term.
  have hexp32 : Real.exp (-(paramρ V s / 32)) ≤ x / B ^ 8 := by
    rw [exp_paramρ, ← hpow8]
    convert hpowle using 2
    ring
  have hδ₀v : paramδ₀ V s ≤ 4 * B ^ 2 * (x / B ^ 8) := by
    unfold paramδ₀
    rw [hpow8]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn2 (by norm_num)) (by positivity)
  have hn1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hB8 : B ^ 8 = 256 * (n + 1) ^ 8 := by rw [hBn]; ring
  have hest : (fuelBound V : ℝ) * (n * Real.exp (-(paramρ V s / 32)) +
      n * ((n - 1 : ℕ) * paramδ₀ V s)) ≤ (34 / 256) * x := by
    have h1 : n * Real.exp (-(paramρ V s / 32)) + n * ((n - 1 : ℕ) * paramδ₀ V s) ≤
        (n + n * (n * (4 * B ^ 2))) * (x / B ^ 8) := by
      have := mul_le_mul_of_nonneg_left hexp32 (show (0 : ℝ) ≤ n by positivity)
      have := mul_le_mul hn1 hδ₀v (by positivity) (by positivity)
      nlinarith
    have h2 : (n + n * (n * (4 * B ^ 2))) ≤ 17 * (n + 1) ^ 4 := by
      rw [hBn]
      nlinarith
    calc _ ≤ (2 * (n + 1) ^ 4) * ((17 * (n + 1) ^ 4) * (x / B ^ 8)) := by
          apply mul_le_mul hfuel (h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity)))
            (by positivity) (by positivity)
      _ = (34 / 256) * x := by
          rw [hB8]
          field_simp
          ring
  -- Output term.
  have hout : ((n - 1 : ℕ) : ℝ) * paramδ V s ≤ x / 2 := by
    unfold paramδ
    rw [hpow1, hBn]
    have : ((n - 1 : ℕ) : ℝ) ≤ n + 1 := by linarith
    calc ((n - 1 : ℕ) : ℝ) * (x / (2 * (n + 1))) ≤ (n + 1) * (x / (2 * (n + 1))) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = x / 2 := by field_simp
  linarith

end
end CutQueryComplexity.WeightedGraph
