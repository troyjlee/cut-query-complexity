import CutQueryComplexity.ImplicitLP.Centrality
import CutQueryComplexity.ImplicitLP.Lewis

/-! # The centrality minimum is attained (Lee–Sidford audit, gap G8)

Lee–Sidford's Lemma 10 writes `δ_t` as a minimum over `ν` without proving that the minimum is
attained. Here `ν ↦ N_w(y − Lν)`, with `L ν = Aν/(wS)` injective, is continuous and coercive:
`‖ν‖ ≤ K‖Lν‖` by the finite-dimensional antilipschitz bound. So it attains its infimum
(`cent_attained`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Real Metric

noncomputable section

variable {M r : ℕ} {C : ℝ} {A : Matrix (Fin M) (Fin r) ℝ} {S dφ c : Fin M → ℝ}

/-- **The centrality minimum is attained.** -/
theorem cent_attained (hC : 0 < C) (hA : (Aᵀ * A).det ≠ 0) (hS : ∀ i, 0 < S i) (t : ℝ)
    {w : Fin M → ℝ} (hw : ∀ i, 0 < w i) :
    ∃ ν, cent C A S dφ c t w =
      mixed C w (fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i)) := by
  set d : Fin M → ℝ := fun i => 1 / (w i * S i)
  have hd : ∀ i, 0 < d i := fun i => one_div_pos.mpr (mul_pos (hw i) (hS i))
  set y : Fin M → ℝ := fun i => (t * c i + w i * dφ i) / (w i * S i)
  set L := Matrix.toLin' (diagonal d * A)
  have hL : ∀ ν i, L ν i = (A *ᵥ ν) i / (w i * S i) := fun ν i => by
    simp only [L, Matrix.toLin'_apply, ← mulVec_mulVec, mulVec_diagonal, d]; ring
  set F : (Fin r → ℝ) → ℝ := fun ν => mixed C w (y - L ν)
  have hF : ∀ ν, mixed C w (fun i => (t * c i + w i * dφ i - (A *ᵥ ν) i) / (w i * S i)) = F ν :=
    fun ν => by
      congr 1; funext i; simp only [Pi.sub_apply, y, hL, sub_div]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ν hν
    apply mulVec_eq_zero_of_rank hA
    funext i
    have := congrFun hν i
    rw [hL] at this
    simp only [Pi.zero_apply] at this ⊢
    rcases div_eq_zero_iff.mp this with h | h
    · exact h
    · exact absurd h (mul_pos (hw i) (hS i)).ne'
  obtain ⟨K, hK, hanti⟩ := L.exists_antilipschitzWith hker
  have hcont : Continuous F :=
    continuous_mixed.comp (continuous_const.sub L.continuous_of_finiteDimensional)
  set R : ℝ := K * (F 0 + ‖y‖ + 1)
  have hF0 : 0 ≤ F 0 := mixed_nonneg hC.le _
  have hR : 0 ≤ R := by positivity
  obtain ⟨ν₀, -, hmin⟩ := (isCompact_closedBall (0 : Fin r → ℝ) R).exists_isMinOn
    ⟨0, mem_closedBall_self hR⟩ hcont.continuousOn
  have hglob : ∀ ν, F ν₀ ≤ F ν := by
    intro ν
    by_cases hν : ν ∈ closedBall (0 : Fin r → ℝ) R
    · exact hmin hν
    · have h0 : F ν₀ ≤ F 0 := hmin (mem_closedBall_self hR)
      rw [mem_closedBall, dist_zero_right, not_le] at hν
      have h1 : ‖ν‖ ≤ K * ‖L ν‖ := hanti.le_mul_norm (map_zero L) ν
      have h2 : ‖L ν‖ ≤ ‖y‖ + F ν := by
        have := norm_le_mixed (g := w) hC.le (y - L ν)
        have := norm_sub_norm_le (L ν) y
        rw [norm_sub_rev] at this
        linarith [norm_sub_rev y (L ν)]
      have hK' : (0 : ℝ) < K := by exact_mod_cast hK
      have h3 := mul_le_mul_of_nonneg_left h2 hK'.le
      have h4 : K * (F 0 + ‖y‖ + 1) < K * (‖y‖ + F ν) := by
        simp only [R] at hν; linarith
      have := lt_of_mul_lt_mul_left h4 hK'.le
      linarith
  have hcent : cent C A S dφ c t w = ⨅ ν, F ν := by unfold cent; simp_rw [hF]
  refine ⟨ν₀, ?_⟩
  rw [hcent, hF]
  exact (le_antisymm (ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ mixed_nonneg hC.le _⟩ ν₀)
    (le_ciInf hglob))

end

end ImplicitLP
end CutQueryComplexity
