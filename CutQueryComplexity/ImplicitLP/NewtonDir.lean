import CutQueryComplexity.ImplicitLP.Lewis

/-! # The exact feasible Newton direction (D7)

For positive `wᵢ, Sᵢ` and `q = tc + wφ'`, put `D = (WS²)⁻¹` and `L = AᵀDA`. The normal matrix is
invertible because `A` has full column rank. The exact direction is `h = −D(q − Aπ)` with
`Lπ = AᵀDq` (`newtonPot`, `newtonDir`). It satisfies `Aᵀh = 0` and `q + WS²h = Aπ`
(`newtonDir_spec`). These are exactly the hypotheses used by `eq:projection` and `eq:newton`.
The direction is unique: any `h'` with these two properties equals `h` (`newtonDir_unique`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset

noncomputable section

variable {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ}

/-- The Newton potential `π = (AᵀDA)⁻¹AᵀDq` with `D = diag(1/(wS²))`. -/
def newtonPot (A : Matrix (Fin M) (Fin r) ℝ) (w S q : Fin M → ℝ) : Fin r → ℝ :=
  (gram A (fun i => 1 / (w i * S i ^ 2)))⁻¹ *ᵥ (Aᵀ *ᵥ fun i => q i / (w i * S i ^ 2))

/-- The exact feasible Newton direction `h = −D(q − Aπ)`. -/
def newtonDir (A : Matrix (Fin M) (Fin r) ℝ) (w S q : Fin M → ℝ) : Fin M → ℝ :=
  fun i => -(q i - (A *ᵥ newtonPot A w S q) i) / (w i * S i ^ 2)

/-- **The exact direction is feasible and stationary:** `Aᵀh = 0` and `q + WS²h = Aπ`. -/
theorem newtonDir_spec (hA : (Aᵀ * A).det ≠ 0) {w S q : Fin M → ℝ} (hw : ∀ i, 0 < w i)
    (hS : ∀ i, 0 < S i) :
    Aᵀ *ᵥ newtonDir A w S q = 0 ∧
      ∀ i, q i + w i * S i ^ 2 * newtonDir A w S q i = (A *ᵥ newtonPot A w S q) i := by
  have hd : ∀ i, 0 < 1 / (w i * S i ^ 2) := fun i => by
    have := hw i; have := hS i; positivity
  set G := gram A (fun i => 1 / (w i * S i ^ 2))
  have hG : G.det ≠ 0 := gram_det_ne hA hd
  set π := newtonPot A w S q
  have hGπ : G *ᵥ π = Aᵀ *ᵥ fun i => q i / (w i * S i ^ 2) := by
    simp only [π, newtonPot, G]
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), one_mulVec]
  have hGv : G *ᵥ π = Aᵀ *ᵥ fun i => (A *ᵥ π) i / (w i * S i ^ 2) := by
    simp only [G, gram]
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    congr 1; funext i; simp [mulVec_diagonal, div_eq_inv_mul]
  refine ⟨?_, fun i => ?_⟩
  · have : newtonDir A w S q =
        (fun i => (A *ᵥ π) i / (w i * S i ^ 2)) - fun i => q i / (w i * S i ^ 2) := by
      funext i; simp only [newtonDir, Pi.sub_apply, π]; ring
    rw [this, mulVec_sub, ← hGv, ← hGπ, sub_self]
  · have hne : w i * S i ^ 2 ≠ 0 := by have := hw i; have := hS i; positivity
    simp only [newtonDir, π]
    field_simp [(hw i).ne', (hS i).ne']
    ring

/-- **Uniqueness of the exact direction.** -/
theorem newtonDir_unique (hA : (Aᵀ * A).det ≠ 0) {w S q : Fin M → ℝ} (hw : ∀ i, 0 < w i)
    (hS : ∀ i, 0 < S i) {h : Fin M → ℝ} {π' : Fin r → ℝ} (h1 : Aᵀ *ᵥ h = 0)
    (h2 : ∀ i, q i + w i * S i ^ 2 * h i = (A *ᵥ π') i) : h = newtonDir A w S q := by
  obtain ⟨g1, g2⟩ := newtonDir_spec hA (q := q) hw hS
  set h₀ := newtonDir A w S q
  set π := newtonPot A w S q
  -- `WS²(h − h₀) = A(π' − π)` and `Aᵀ(h − h₀) = 0`
  have hdiff : ∀ i, w i * S i ^ 2 * (h i - h₀ i) = (A *ᵥ (π' - π)) i := fun i => by
    rw [mulVec_sub, Pi.sub_apply, ← h2 i, ← g2 i]; ring
  have hker : Aᵀ *ᵥ (h - h₀) = 0 := by rw [mulVec_sub, h1, g1, sub_self]
  -- `Σ wS²(h − h₀)² = (h − h₀)ᵀA(π' − π) = 0`
  have hsum : ∑ i, w i * S i ^ 2 * (h i - h₀ i) ^ 2 = 0 := by
    have : ∑ i, w i * S i ^ 2 * (h i - h₀ i) ^ 2 = (h - h₀) ⬝ᵥ (A *ᵥ (π' - π)) := by
      simp only [dotProduct, Pi.sub_apply, ← hdiff]
      exact sum_congr rfl fun i _ => by ring
    rw [this, dotProduct_mulVec, ← mulVec_transpose, hker, zero_dotProduct]
  funext i
  have hnn : ∀ j ∈ univ, 0 ≤ w j * S j ^ 2 * (h j - h₀ j) ^ 2 := fun j _ => by
    have := hw j; have := hS j; positivity
  have := (sum_eq_zero_iff_of_nonneg hnn).mp hsum i (mem_univ i)
  have hpos : 0 < w i * S i ^ 2 := by have := hw i; have := hS i; positivity
  have : (h i - h₀ i) ^ 2 = 0 := by
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hpos.ne'
    · exact h0
  linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this]

end

end ImplicitLP
end CutQueryComplexity
