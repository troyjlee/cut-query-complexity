import CutQueryComplexity.Sparsification.LocalCutCounting
import CutQueryComplexity.Sparsification.CountedConcentration
import Mathlib.Algebra.Order.Field.GeomSum

/-! # Summing the exponential cut tails

Group the positive shores of a normalized BK piece by `k = ⌈cut / c⌉`. At most
`(2|U|)^(2k)` shores have level at most `k`, and each contributes at most
`exp(-ε²c/8)^k`, because `cut ≥ c` and `cut > (k-1)c` give `2 cut / c ≥ k`.
The resulting geometric series is bounded once its ratio is at most `1/2`.
This yields explicit confidence parameters for the counted sampler.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical ENNReal
open Probability
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Abstract layer-cake bound: a polynomial count at every integer threshold makes
the exponential sum geometric. -/
theorem sum_exp_le_of_threshold_count {ι : Type} (P : Finset ι) (g : ι → ℝ) {c : ℝ}
    (hc : 0 < c) (hg : ∀ S ∈ P, c ≤ g S) {m a : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a)
    (hcount : ∀ k : ℕ, 1 ≤ k → ((P.filter (fun S => g S ≤ k * c)).card : ℝ) ≤ m ^ k)
    (hq : m * Real.exp (-a) ≤ 1 / 2) :
    ∑ S ∈ P, Real.exp (-(2 * a * g S / c)) ≤ 2 * (m * Real.exp (-a)) := by
  set x := Real.exp (-a)
  have hx : 0 < x := Real.exp_pos _
  let lvl : ι → ℕ := fun S => ⌈g S / c⌉₊
  have hlvl_pos {S} (hS : S ∈ P) : 1 ≤ lvl S := by
    have : 0 < g S / c := div_pos (hc.trans_le (hg S hS)) hc
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr this).ne'
  have hlvl_le {S} (hS : S ∈ P) : g S ≤ lvl S * c :=
    (div_le_iff₀ hc).mp (Nat.le_ceil _)
  -- Each term is at most `x ^ level`.
  have hterm {S} (hS : S ∈ P) : Real.exp (-(2 * a * g S / c)) ≤ x ^ lvl S := by
    have h1 : 1 ≤ g S / c := (one_le_div hc).mpr (hg S hS)
    have h2 : (lvl S : ℝ) < g S / c + 1 := Nat.ceil_lt_add_one (by linarith)
    have hk : (lvl S : ℝ) ≤ 2 * (g S / c) := by linarith
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have : a * lvl S ≤ a * (2 * (g S / c)) := mul_le_mul_of_nonneg_left hk ha
    have he : 2 * a * g S / c = a * (2 * (g S / c)) := by ring
    rw [he]
    linarith
  set q := m * x with hqdef
  have hq0 : 0 ≤ q := mul_nonneg hm hx.le
  set N := P.sup lvl + 1
  have hmaps : ∀ S ∈ P, lvl S ∈ Finset.Ico 1 N := fun S hS =>
    Finset.mem_Ico.mpr ⟨hlvl_pos hS, Nat.lt_succ_of_le (Finset.le_sup hS)⟩
  calc
    ∑ S ∈ P, Real.exp (-(2 * a * g S / c)) ≤ ∑ S ∈ P, x ^ lvl S :=
      Finset.sum_le_sum fun S hS => hterm hS
    _ = ∑ k ∈ Finset.Ico 1 N, ∑ S ∈ P.filter (fun S => lvl S = k), x ^ lvl S :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ k ∈ Finset.Ico 1 N, ((P.filter (fun S => lvl S = k)).card : ℝ) * x ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => x ^ k)
        (fun S hS => by rw [(Finset.mem_filter.mp hS).2]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.Ico 1 N, q ^ k := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hsub : P.filter (fun S => lvl S = k) ⊆ P.filter (fun S => g S ≤ k * c) := by
        intro S hS'
        obtain ⟨hS, rfl⟩ := Finset.mem_filter.mp hS'
        exact Finset.mem_filter.mpr ⟨hS, hlvl_le hS⟩
      have hcard : ((P.filter (fun S => lvl S = k)).card : ℝ) ≤ m ^ k :=
        (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount k hk1)
      rw [hqdef, mul_pow]
      exact mul_le_mul_of_nonneg_right hcard (pow_nonneg hx.le _)
    _ ≤ q ^ 1 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 (by linarith)
    _ ≤ 2 * q := by
      rw [pow_one, div_le_iff₀ (by linarith)]
      nlinarith

/-- The exponential tail sum of a normalized BK piece is geometric in the piece size. -/
theorem strengthPiece_cutTailSum_le (G : WeightedGraph V) {U : Finset V}
    (hU : U ∈ G.strongComponents) {c ε : ℝ} (hc : 0 < c)
    (hq : ((2 * U.card : ℕ) : ℝ) ^ 2 * Real.exp (-(ε ^ 2 * c / 8)) ≤ 1 / 2) :
    ((G.strengthPiece G U).scale c hc.le).cutTailSum U ε ≤
      ENNReal.ofReal (4 * (((2 * U.card : ℕ) : ℝ) ^ 2 * Real.exp (-(ε ^ 2 * c / 8)))) := by
  set H := (G.strengthPiece G U).scale c hc.le
  set P := H.positiveLocalShores U
  have hmin := G.strengthPiece_reference_mincut hU c hc.le
  have hind := G.scaled_strengthPiece_induce G U c hc.le
  have hg : ∀ S ∈ P, c ≤ H.cut S := by
    intro S hS
    have hl := H.inducedMincut_le ((H.mem_positiveLocalShores U S).mp hS).1
    rw [localCut_eq_cut_induce, hind] at hl
    rwa [← hmin]
  have hsum := sum_exp_le_of_threshold_count P H.cut hc hg
    (a := ε ^ 2 * c / 8) (by positivity) (by positivity)
    (fun k hk => by
      have := G.strengthPiece_bounded_shores_card hU hc k hk
      rw [← pow_mul]
      exact_mod_cast this) hq
  unfold cutTailSum
  rw [← ENNReal.ofReal_ofNat 2]
  simp_rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  have he : ∀ S ∈ P, Real.exp (-(ε ^ 2 * H.cut S / 4)) =
      Real.exp (-(2 * (ε ^ 2 * c / 8) * H.cut S / c)) := by
    intro S _
    congr 2
    field_simp
    ring
  rw [Finset.sum_congr rfl he]
  linarith

/-- An explicit exponent on the whole vertex type bounds every piece's tail sum by `δ`. -/
theorem strengthPiece_cutTailSum_le_of_exp (G : WeightedGraph V) {U : Finset V}
    (hU : U ∈ G.strongComponents) {c ε δ : ℝ} (hc : 0 < c) (hδ : δ ≤ 2)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ε ^ 2 * c / 8)) ≤ δ / 4) :
    ((G.strengthPiece G U).scale c hc.le).cutTailSum U ε ≤ ENNReal.ofReal δ := by
  have hU' : ((2 * U.card : ℕ) : ℝ) ^ 2 ≤ ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 := by
    gcongr
    exact U.card_le_univ
  have hmono : ((2 * U.card : ℕ) : ℝ) ^ 2 * Real.exp (-(ε ^ 2 * c / 8)) ≤ δ / 4 :=
    (mul_le_mul_of_nonneg_right hU' (Real.exp_pos _).le).trans hexp
  apply (G.strengthPiece_cutTailSum_le hU hc (by linarith)).trans
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Logarithmic sample-count condition giving the exponential condition above. -/
theorem exp_condition_of_log {n : ℕ} {c ε δ : ℝ} (hδ : 0 < δ)
    (hc : 8 * (2 * Real.log (2 * n) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    ((2 * n : ℕ) : ℝ) ^ 2 * Real.exp (-(ε ^ 2 * c / 8)) ≤ δ / 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have h2n : (0 : ℝ) < 2 * n := by positivity
  have hl : ((2 * n : ℕ) : ℝ) ^ 2 = Real.exp (2 * Real.log (2 * n)) := by
    rw [two_mul (Real.log _), Real.exp_add, Real.exp_log h2n]
    push_cast
    ring
  have h4 : δ / 4 = Real.exp (-Real.log (4 / δ)) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hl, h4, ← Real.exp_add, Real.exp_le_exp]
  linarith

namespace CountedBucket

/-- High-probability sparsification for fixed buckets with an explicit exponent. -/
theorem sampleLaw_success_of_exp (bs : List (CountedBucket V))
    {ε c δ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2)
    (hb : ∀ b ∈ bs, b.Admissible (reference bs) c)
    (hexp : ((2 * Fintype.card V : ℕ) : ℝ) ^ 2 * Real.exp (-(ε ^ 2 * c / 8)) ≤ δ / 4) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤
      (Probability.mass (sampleLaw bs) (IsCutSparsifier ε (reference bs))).toReal :=
  sampleLaw_success_of_cut_tail_bounds bs hε hε1 hc hδ hb
    (fun _ hU => (reference bs).strengthPiece_cutTailSum_le_of_exp hU hc hδ2 hexp)

/-- Explicit confidence: with `ε² c ≥ 8 (2 log(2n) + log(4/δ))`, every cut is preserved
within `1 ± ε` with probability at least `1 - (n-1)δ`. -/
theorem sampleLaw_success_of_log (bs : List (CountedBucket V))
    {ε c δ : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hb : ∀ b ∈ bs, b.Admissible (reference bs) c)
    (hlog : 8 * (2 * Real.log (2 * Fintype.card V) + Real.log (4 / δ)) ≤ ε ^ 2 * c) :
    1 - (Fintype.card V - 1 : ℕ) * δ ≤
      (Probability.mass (sampleLaw bs) (IsCutSparsifier ε (reference bs))).toReal :=
  sampleLaw_success_of_exp bs hε hε1 hc hδ.le hδ2 hb (exp_condition_of_log hδ hlog)

end CountedBucket
end
end CutQueryComplexity.WeightedGraph
