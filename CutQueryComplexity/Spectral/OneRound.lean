import CutQueryComplexity.Spectral.Normalize
import CutQueryComplexity.Spectral.QuarterSampling

/-! # The conditional one-round guarantee (D3; source `lem:bernstein`)

The current support `E'` with conductances `ω ≥ 0` has Laplacian `L`. Its remaining pairs are
listed injectively as `p : Fin N → Sym2 (Fin n)`, and the rest `E' \ image p` is the fixed bundle.
Each remaining pair `e` satisfies the bundle bound `ω_e (x_u − x_v)² ≤ λ xᵀ L x`
(`Spanner.bundle_dominated`, with `λ = C α / t`). A fresh quarter mask `ξ` keeps each remaining
pair as a whole with probability `1/4` and multiplies its conductance by four (`sampledEnergy`).

`one_round`: for `0 < δ ≤ 1`, outside an event of probability at most `2n exp(−δ²/(8λ))`,

  `(1 − δ) xᵀ L x ≤ sampledEnergy ξ x ≤ (1 + δ) xᵀ L x`  for every real vector `x`.

The proof normalizes on the range of `L` (`Spectral.normPair`, `‖A_e‖ ≤ λ`, `Σ A_e ⪯ I`) and
applies `quarter_tail_pmf`. Vectors in `ker L` see no sampled pair (`kernel_pairs`), so the
bound transfers back to every vector (`transfer`). The guarantee is uniform over the fixed
bundle and remaining list, so it holds conditionally on any earlier transcript that produced
them.
-/

namespace CutQueryComplexity
namespace Spectral

open Matrix Finset Probability
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {n N : ℕ}

/-- The energy after sampling: the bundle as is, and each kept remaining pair with conductance
multiplied by four. -/
def sampledEnergy (ω : Sym2 (Fin n) → ℝ) (E' : Finset (Sym2 (Fin n))) (p : Fin N → Sym2 (Fin n))
    (ξ : Fin N → Bool) (x : Fin n → ℝ) : ℝ :=
  energy ω (E' \ univ.image p) x + ∑ i, (if ξ i then 4 else 0) * (ω (p i) * pairSq x (p i))

theorem energy_split {ω : Sym2 (Fin n) → ℝ} {E' : Finset (Sym2 (Fin n))}
    {p : Fin N → Sym2 (Fin n)} (hp : Function.Injective p) (hpE : ∀ i, p i ∈ E')
    (x : Fin n → ℝ) :
    energy ω E' x = energy ω (E' \ univ.image p) x + ∑ i, ω (p i) * pairSq x (p i) := by
  have hsub : univ.image p ⊆ E' := fun e he => by
    obtain ⟨i, -, rfl⟩ := mem_image.mp he; exact hpE i
  unfold energy
  rw [← sum_sdiff hsub, sum_image fun i _ j _ h => hp h]

/-- **One round of sampling**, conditional on the bundle and the remaining list. -/
theorem one_round {ω : Sym2 (Fin n) → ℝ} (hω : ∀ e, 0 ≤ ω e) {E' : Finset (Sym2 (Fin n))}
    {p : Fin N → Sym2 (Fin n)} (hp : Function.Injective p) (hpE : ∀ i, p i ∈ E') {lam : ℝ}
    (hlam : 0 ≤ lam) (hlev : ∀ i y, ω (p i) * pairSq y (p i) ≤ lam * energy ω E' y)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (mass (maskPMF N) fun ξ => ¬ ∀ x, |sampledEnergy ω E' p ξ x - energy ω E' x| ≤
      δ * energy ω E' x).toReal ≤ 2 * n * Real.exp (-(δ ^ 2) / (8 * lam)) := by
  set L := lap ω E'
  have hL : L.IsHermitian := lap_isHermitian ω E'
  have hpsd : ∀ x, 0 ≤ x ⬝ᵥ (L *ᵥ x) := fun x => by rw [quad_lap]; exact energy_nonneg hω E' x
  set A : Fin N → Matrix (Fin n) (Fin n) ℝ := fun i => normPair hL ω (p i)
  have hsum : ∀ x, ∑ i, x ⬝ᵥ (A i *ᵥ x) ≤ x ⬝ᵥ x := fun x => by
    have hsub : univ.image p ⊆ E' := fun e he => by
      obtain ⟨i, -, rfl⟩ := mem_image.mp he; exact hpE i
    calc ∑ i, x ⬝ᵥ (A i *ᵥ x) = ∑ e ∈ univ.image p, x ⬝ᵥ (normPair hL ω e *ᵥ x) := by
          rw [sum_image fun i _ j _ h => hp h]
      _ ≤ ∑ e ∈ E', x ⬝ᵥ (normPair hL ω e *ᵥ x) :=
          sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => normPair_psd hL hω e x
      _ ≤ x ⬝ᵥ x := sum_normPair_le hL rfl x
  have htail := quarter_tail_pmf A (fun i => normPair_isHermitian hL ω (p i))
    (fun i x => normPair_psd hL hω (p i) x)
    (fun i => norm_normPair_le hL hω rfl hlam (hlev i)) hsum hδ hδ1
  refine le_trans (ENNReal.toReal_mono (mass_ne_top _ _) (mass_mono _ fun ξ hbad => ?_)) htail
  -- on the good event the sampled energy is close
  by_contra hgood
  push Not at hgood
  apply hbad
  intro x
  set M : Matrix (Fin n) (Fin n) ℝ := ∑ i ∈ (univ : Finset (Fin N)),
    qsign (ξ i) • (ω (p i) • pairMat (p i))
  have hWMW : matW hL * M * matW hL = ∑ i, qsample A i ξ := by
    simp only [M, Matrix.mul_sum, Matrix.sum_mul, qsample, A, normPair, Matrix.mul_smul,
      Matrix.smul_mul]
  have hMherm : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [conjTranspose_smul, conjTranspose_smul, (pairMat_isHermitian _).eq, star_trivial,
      star_trivial]
  have hker : ∀ k, L *ᵥ k = 0 → M *ᵥ k = 0 := fun k hk =>
    kernel_pairs hω rfl univ p (fun i _ => hpE i) (fun i => qsign (ξ i)) hk
  have htr := transfer hL hpsd hMherm hker (δ := δ) (by rw [hWMW]; exact hgood.le) x
  have hquad : x ⬝ᵥ (M *ᵥ x) = sampledEnergy ω E' p ξ x - energy ω E' x := by
    rw [energy_split hp hpE x, sampledEnergy, sum_mulVec, dotProduct_sum]
    have : ∀ i : Fin N, x ⬝ᵥ ((qsign (ξ i) • (ω (p i) • pairMat (p i))) *ᵥ x) =
        (if ξ i then 4 else 0) * (ω (p i) * pairSq x (p i)) - ω (p i) * pairSq x (p i) := by
      intro i
      rw [smul_mulVec, smul_mulVec, dotProduct_smul, dotProduct_smul, quad_pairMat, smul_eq_mul,
        smul_eq_mul]
      cases ξ i <;> simp [qsign]
      all_goals ring
    rw [sum_congr rfl fun i _ => this i, sum_sub_distrib]
    ring
  rw [hquad, quad_lap] at htr
  exact htr

end

end Spectral
end CutQueryComplexity
