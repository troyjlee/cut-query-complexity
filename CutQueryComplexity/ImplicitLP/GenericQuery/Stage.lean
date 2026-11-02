import CutQueryComplexity.ImplicitLP.GenericQuery.Lewis

/-! # Actual Lewis restart with the original row-norm lower bound

The public floor includes `a0^2`. Rank, nonzero rows, the restart error and the
finite Lewis call count follow from original row norms and the state's slack
floor; no restart or weight-approximation oracle is assumed.
-/

set_option autoImplicit false
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Real Spectral Probability
open scoped ENNReal
noncomputable section
variable {n me : ℕ} (G : DiGraph (Fin n))
variable {κ m x : Fin (rowCount G me) → ℝ}

theorem lewis_restart (ER : ExplicitRows n me) (hn : 0 < n)
    {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 ≤ 1)
    (hrows : ∀ j, a0 ^ 2 ≤ ∑ v, ER.matrix j v ^ 2 ∧ ∑ v, ER.matrix j v ^ 2 ≤ 2) (hκ : ∀ i, 0 < κ i)
    (hx : Interior κ m x) {U : ℝ} (hU1 : 1 ≤ U) (hU : ∀ i, π / κ i ≤ U)
    {sst Mbar : ℝ} (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hMbar : (rowCount G me : ℝ) ≤ Mbar)
    {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    let B := diagonal (fun j => exp (sfun κ m x j)) * matrix G ER
    (Bᵀ * B).det ≠ 0 ∧ (∀ i, B i ≠ 0) ∧ lewisMap p B (lewisLog p B) = lewisLog p B ∧
      (∀ i, qStar a0 Mbar U sst ≤ exp (lewisLog p B i) ∧ exp (lewisLog p B i) ≤ 1) ∧
      0 ≤ restartLog a0 Mbar U sst ∧ dist (0 : Fin (rowCount G me) → ℝ) (lewisLog p B) ≤ restartLog a0 Mbar U sst := by
  intro B
  set A := matrix G ER
  have hA : (Aᵀ * A).det ≠ 0 := det_ne_zero_of_idRows (matrix_idRows G ER)
  have hS0 := barS_pos hκ hx
  have hdiag : (fun j => exp (sfun κ m x j)) = fun j => (barS κ m x j)⁻¹ := by
    funext j; rw [exp_sfun hκ hx j, one_div]
  have hBeq : B = diagonal (fun j => (barS κ m x j)⁻¹) * A := by simp only [B, A, hdiag]
  have hB : (Bᵀ * B).det ≠ 0 := diag_det hA fun j => (exp_pos _).ne'
  have hrowB : ∀ i, B i ≠ 0 := fun i h0 => by
    apply matrix_row_ne_zero G ER ha0 ha1 hrows i
    funext j
    have := congrFun h0 j
    simp only [B, diagonal_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (exp_pos _).ne'
  have hfix := lewisLog_fixed hB hrowB hp0 hp2
  -- the floor `q_* ≤ w` and `w ≤ 1`
  have hM : 0 < rowCount G me := Fin.pos (iota G ER ⟨0, hn⟩)
  have hM1 : (1 : ℝ) ≤ rowCount G me := by exact_mod_cast hM
  have hU0 : 0 < U := by linarith
  have hslk0 : ∀ i, 0 < slk κ m x i := fun i => lt_of_lt_of_le hsst (hs i)
  have hS := fun i => barrier_env hκ hx hU1 hU i
  have hShi : ∀ i, barS κ m x i ≤ 2 / slk κ m x i := fun i => by
    rw [le_div_iff₀ (hslk0 i)]; exact (hS i).2.1
  have hMb0 : 0 < Mbar := by linarith
  have hq0 : 0 < qStar a0 Mbar U sst := qStar_pos ha0 hMb0 hU0 hsst
  have hqle : ∀ i, qStar a0 Mbar U sst ≤ exp (lewisLog p B i) := fun i => by
    rw [hBeq]
    exact lewis_floor_public G ER hn ha0 ha1 hrows hMbar hU0 hsst (barS κ m x) (slk κ m x)
      (fun i => (hS i).1) hShi hs hp0 hp2 i
  have hhi : ∀ i, exp (lewisLog p B i) ≤ 1 := fun i => by
    have := ((eq_gsize hB hrowB hp0 hp2 0).2 i).2
    linarith
  have hq1 : qStar a0 Mbar U sst ≤ 1 := (hqle (iota G ER ⟨0, hn⟩)).trans (hhi _)
  have hE0 : 0 ≤ restartLog a0 Mbar U sst :=
    Real.log_nonneg (by rw [le_div_iff₀ hq0]; linarith)
  exact ⟨hB, hrowB, hfix, fun i => ⟨hqle i, hhi i⟩, hE0,
    restart_error hq0 hq1 hqle hhi⟩


set_option maxHeartbeats 3200000 in
theorem lewisStage (ER : ExplicitRows n me) (hn : 0 < n)
    {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 ≤ 1)
    (hrows : ∀ j, a0 ^ 2 ≤ ∑ v, ER.matrix j v ^ 2 ∧ ∑ v, ER.matrix j v ^ 2 ≤ 2) (hκ : ∀ i, 0 < κ i)
    (hx : Interior κ m x) {U : ℝ} (hU1 : 1 ≤ U) (hU : ∀ i, π / κ i ≤ U)
    {sst Mbar : ℝ} (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hMbar : (rowCount G me : ℝ) ≤ Mbar)
    {spt : Point n me} (hspt : vec G spt = fun i => exp (sfun κ m x i))
    {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp2 : p < 2) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 256)
    {K : ℕ} (J : ℕ) {t' : ℕ} (R : ℕ) {Cs : ℝ} (hCs0 : 0 ≤ Cs)
    (hCs : ∀ e, (Spanner.symS G e : ℝ) ≤ Cs) (hK : n ≤ 2 ^ K) (ht' : 0 < t') :
    let JL := lewisJL Δ (restartLog a0 Mbar U sst)
    let prog := lewisLoop ER p (levBits Δ) spt 0 K J t' R JL
    let ystar := lewisLog p (diagonal (fun j => exp (sfun κ m x j)) * matrix G ER)
    (∀ o ∈ (RTree.run G.out prog).support,
      o.2 ≤ JL * (R * Sparsify.levelBudget (n := n) K J t' + 3 * n)) ∧
    mass (prog.eval G.out)
        (fun o => ¬ ∃ y, o = some y ∧ dist (vec G y) ystar ≤ Δ / 16 ∧
          ∀ i, |Real.log (exp (vec G y i) + c₀) -
            Real.log (gfun κ m p c₀ (matrix G ER) x i)| ≤ Δ / 16) ≤
      JL * (R * (t' * (2⁻¹ : ℝ≥0∞) ^ J + ENNReal.ofReal (2 * n *
          Real.exp (-(levDelta Δ R ^ 2) / (8 * (Cs * (2 * K + 1 : ℕ) / t'))))) +
        (Fintype.card (Sym2 (Fin n)) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ R) := by
  intro JL prog ystar
  obtain ⟨-, -, hfix, -, -, hrest⟩ :=
    lewis_restart G ER hn ha0 ha1 hrows hκ hx hU1 hU hsst hs hMbar (p := p) (by linarith) hp2
  refine ⟨fun o ho => lewisLoop_cost ER p (levBits Δ) spt 0 K J t' R JL G.out ho, ?_⟩
  have hspos : ∀ i, 0 < vec G spt i := fun i => by rw [hspt]; exact exp_pos _
  have hfix' : lewisMap p (diagonal (vec G spt) * matrix G ER) ystar = ystar := by
    rw [hspt]; exact hfix
  have h := lewisLoop_fail_le G ER (matrix_row_ne_zero G ER ha0 ha1 hrows) hspos hp0 hp2 hΔ0 hΔ 0 J R hCs0 hCs hK ht' hfix' JL
  refine le_trans (mass_mono _ fun o ho => ?_) h
  intro hgood
  apply ho
  obtain ⟨y, rfl, hy⟩ := hgood
  rw [vec_zero] at hy
  have hd : dist (vec G y) ystar ≤ Δ / 16 :=
    hy.trans (lewis_cap_final hΔ0 dist_nonneg hrest)
  refine ⟨y, rfl, hd, fun i => ?_⟩
  have hi : |vec G y i - ystar i| ≤ Δ / 16 := by
    rw [← Real.dist_eq]; exact (dist_le_pi_dist _ _ i).trans hd
  exact (abs_log_exp_add_sub_le hc₀ _ _).trans hi


#print axioms lewis_restart
#print axioms lewisStage

end
end CutQueryComplexity.ImplicitLP.GenericQuery
