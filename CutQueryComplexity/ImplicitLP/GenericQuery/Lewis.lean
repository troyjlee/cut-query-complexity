import CutQueryComplexity.ImplicitLP.GenericQuery.Scalars

/-! # Actual leverage and Lewis query execution for general explicit rows

Hidden quadratic forms use their public pair. Every arbitrary explicit row
uses its known vector; all inverses and scalar operations are free exact
computation. The finite adaptive loop uses the actual spectral query program.
-/

set_option autoImplicit false

namespace CutQueryComplexity.ImplicitLP.GenericQuery

open Matrix Finset Real Spectral Probability
open scoped ENNReal
noncomputable section
variable {n me : ℕ}

def lewisW (a : ℝ) (spt ypt : Point n me) : Sym2 (Fin n) → ℝ :=
  fun e => pairOf spt.pair e ^ 2 * exp (a * pairOf ypt.pair e)

def lewisD (a : ℝ) (spt ypt : Point n me) : Point n me :=
  fun i => spt i ^ 2 * exp (a * ypt i)

def lewisE (E : ExplicitRows n me) (a : ℝ) (spt ypt : Point n me) :
    Matrix (Fin n) (Fin n) ℝ := knownGram E (lewisD a spt ypt).explicit

/-- Rounded log leverage at the canonical pair or the actual known explicit row. -/
def lewisNewY (E : ExplicitRows n me) (p : ℝ) (k : ℕ) (spt : Point n me)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Point n me :=
  Point.mk (fun u v => dyadicRound k (p / 2 * log (spt.pair u v ^ 2 * pairLev Q s(u, v))))
    (fun j => dyadicRound k (p / 2 * log (spt.explicit j ^ 2 *
      (E.matrix j ⬝ᵥ (Q *ᵥ E.matrix j)))))

variable (G : DiGraph (Fin n))

theorem explicitGram_lewis (E : ExplicitRows n me) (a : ℝ) (spt ypt : Point n me) :
    explicitGram (matrix G E) (fun i => vec G spt i ^ 2 * exp (a * vec G ypt i))
      (hidden G me) = lewisE E a spt ypt :=
  explicitGram_eq G E (lewisD a spt ypt)

theorem vec_lewisNewY (E : ExplicitRows n me) (p : ℝ) (k : ℕ) (spt : Point n me)
    (Q : Matrix (Fin n) (Fin n) ℝ) (i : Fin (rowCount G me)) :
    vec G (lewisNewY E p k spt Q) i =
      dyadicRound k (p / 2 * log (lpLev (matrix G E) (vec G spt) (hidden G me) Q i)) := by
  simp only [vec, lpLev, hidden, matrix]
  generalize (rowEquiv G me).symm i = r
  rcases r with ⟨pair, k⟩ | j <;> rfl

theorem lewis_step_err (E : ExplicitRows n me) (hrowA : ∀ i, matrix G E i ≠ 0) {spt ypt : Point n me}
    (hs : ∀ i, 0 < vec G spt i) {p : ℝ} (hp0 : 0 < p) (k : ℕ)
    {K t' R : ℕ} {δ ε : ℝ} {out : Sym2 (Fin n) → ℝ}
    (hgood : Sparsify.Good G (lewisW (1 - 2 / p) spt ypt) K t' δ R out)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hδlo : 1 - ε ≤ (1 - δ) ^ R) (hδhi : (1 + δ) ^ R ≤ 1 + ε) :
    let B := diagonal (vec G spt) * matrix G E
    let Q := (lap out univ + lewisE E (1 - 2 / p) spt ypt)⁻¹
    dist (vec G (lewisNewY E p k spt Q)) (lewisMap p B (vec G ypt)) ≤
      p * (2 * ε) + (1 / 2) ^ k := by
  intro B Q
  set A := matrix G E
  set sv := vec G spt
  set y := vec G ypt
  set a := 1 - 2 / p
  set D : Fin (rowCount G me) → ℝ := fun k => sv k ^ 2 * Real.exp (a * y k) with hDdef
  have hDpos : ∀ k, 0 < D k := fun k => mul_pos (pow_pos (hs k) 2) (Real.exp_pos _)
  have hA := det_ne_zero_of_idRows (matrix_idRows G E)
  have hB : (Bᵀ * B).det ≠ 0 := diag_det hA fun j => (hs j).ne'
  have hrowB : ∀ i, B i ≠ 0 := fun i h0 => by
    apply hrowA i
    funext j
    have := congrFun h0 j
    simp only [B, diagonal_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (hs i).ne'
  have hw0 : ∀ e, 0 ≤ lewisW a spt ypt e := fun e => by
    unfold lewisW; positivity
  have hD : ∀ i e, hidden G me i = some e → sv i ^ 2 * Real.exp (a * y i) = lewisW a spt ypt e :=
    fun i e he => by
      simp only [sv, y, lewisW, vec_hidden G spt i e he, vec_hidden G ypt i e he]
  set P := lap out univ + explicitGram A D (hidden G me)
  have hPQ : Q = P⁻¹ := by
    simp only [Q, P, D, A]; rw [explicitGram_lewis]
  have hPs : Pᵀ = P := by
    simp only [P, transpose_add, lap_transpose, explicitGram_symm]
  have hsplit : gram B (fun k => Real.exp (a * y k)) =
      lap (Sparsify.omegaR G (lewisW a spt ypt) 0)
          (univ.filter fun e => Sparsify.P0 (lewisW a spt ypt) e = true) +
        explicitGram A D (hidden G me) := by
    simp only [B]
    rw [gram_diag_mul]
    exact gram_split (hidden G me) G (lewisW a spt ypt) (matrix_hidden G E) hD hDpos (hidden_count G me)
  have hbd : ∀ x, (1 - 2 * ε) * (x ⬝ᵥ (P *ᵥ x)) ≤
        x ⬝ᵥ (gram B (fun k => Real.exp (a * y k)) *ᵥ x) ∧
      x ⬝ᵥ (gram B (fun k => Real.exp (a * y k)) *ᵥ x) ≤ (1 + 2 * ε) * (x ⬝ᵥ (P *ᵥ x)) :=
    fun x => by
      have h := frozen_precond hgood hw0 hε0 hε hδlo hδhi (1 : Matrix (Fin n) (Fin n) ℝ)
        (explicitGram_psd A (fun k => (hDpos k).le) (hidden G me)) x
      simp only [pullLap_one] at h
      rw [hsplit]
      exact h
  have hζ : 0 ≤ p * (2 * ε) + (1 / 2) ^ k := by positivity
  refine (dist_pi_le_iff hζ).mpr fun i => ?_
  rw [Real.dist_eq]
  have h1 : |vec G (lewisNewY E p k spt Q) i - lewisMapApprox p B P i| ≤ (1 / 2) ^ k := by
    rw [vec_lewisNewY, hPQ, lpLev_eq (matrix_hidden G E)]
    exact abs_dyadicRound_sub_le k _
  have h2 := lewisMapApprox_err hB hrowB hp0 hPs (η := 2 * ε) (by linarith) (by linarith) y
    (fun x => (hbd x).1) (fun x => (hbd x).2) i
  calc _ ≤ |vec G (lewisNewY E p k spt Q) i - lewisMapApprox p B P i| +
        |lewisMapApprox p B P i - lewisMap p B y i| := abs_sub_le _ _ _
    _ ≤ (1 / 2) ^ k + p * (2 * ε) := add_le_add h1 h2
    _ = _ := add_comm _ _

def lewisStepProg (E : ExplicitRows n me) (p : ℝ) (k : ℕ) (spt ypt : Point n me) (K J t' R : ℕ) :
    RTree (Finset (Fin n)) ℕ (Option (Point n me))
      ((R * Sparsify.levelBudget (n := n) K J t' + 3 * n) + 0) :=
  (Sparsify.sparsify (lewisW (1 - 2 / p) spt ypt) K J t' R).bind fun o => match o with
  | none => RTree.pure (PMF.pure none)
  | some out => RTree.pure (PMF.pure (some (lewisNewY E p k spt
      (lap out univ + lewisE E (1 - 2 / p) spt ypt)⁻¹)))

/-- **The Lewis loop**: `J_L` iterations from `y₀`; `none` once a D4 call aborts. -/
def lewisLoop (E : ExplicitRows n me) (p : ℝ) (k : ℕ) (spt y0 : Point n me) (K J t' R : ℕ) :
    (JL : ℕ) → RTree (Finset (Fin n)) ℕ (Option (Point n me))
      (JL * ((R * Sparsify.levelBudget (n := n) K J t' + 3 * n) + 0))
  | 0 => RTree.pure (PMF.pure (some y0))
  | JL + 1 => ((lewisLoop E p k spt y0 K J t' R JL).bind fun o => match o with
      | none => RTree.pure (PMF.pure none)
      | some y => lewisStepProg E p k spt y K J t' R).cast (by ring)

/-- **Budget on every execution:** `J_L · q_D4`. -/
theorem lewisLoop_cost (E : ExplicitRows n me) (p : ℝ) (k : ℕ) (spt y0 : Point n me)
    (K J t' R JL : ℕ) (read : Finset (Fin n) → ℕ) {o : Option (Point n me) × ℕ}
    (ho : o ∈ (RTree.run read (lewisLoop E p k spt y0 K J t' R JL)).support) :
    o.2 ≤ JL * (R * Sparsify.levelBudget (n := n) K J t' + 3 * n) := by
  have := RTree.cost_le _ _ ho
  simpa using this

/-! ## Public Lewis parameters and the guarantee -/

/-- Adaptive finite-loop accuracy and spectral failure allocation. -/
theorem lewisLoop_fail_le (E : ExplicitRows n me) (hrowA : ∀ i, matrix G E i ≠ 0) {spt : Point n me}
    (hs : ∀ i, 0 < vec G spt i) {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp2 : p < 2)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 256) (y0 : Point n me)
    {K : ℕ} (J : ℕ) {t' : ℕ} (R : ℕ) {Cs : ℝ} (hCs0 : 0 ≤ Cs)
    (hCs : ∀ e, (Spanner.symS G e : ℝ) ≤ Cs) (hK : n ≤ 2 ^ K) (ht' : 0 < t')
    {ystar : Fin (rowCount G me) → ℝ}
    (hfix : lewisMap p (diagonal (vec G spt) * matrix G E) ystar = ystar) (JL : ℕ) :
    mass ((lewisLoop E p (levBits Δ) spt y0 K J t' R JL).eval G.out)
        (fun o => ¬ ∃ y, o = some y ∧
          dist (vec G y) ystar ≤ (3 / 4) ^ JL * dist (vec G y0) ystar + Δ / 32) ≤
      JL * (R * (t' * (2⁻¹ : ℝ≥0∞) ^ J + ENNReal.ofReal (2 * n *
          Real.exp (-(levDelta Δ R ^ 2) / (8 * (Cs * (2 * K + 1 : ℕ) / t'))))) +
        (Fintype.card (Sym2 (Fin n)) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ R) := by
  set F : ℝ≥0∞ := R * (t' * (2⁻¹ : ℝ≥0∞) ^ J + ENNReal.ofReal (2 * n *
      Real.exp (-(levDelta Δ R ^ 2) / (8 * (Cs * (2 * K + 1 : ℕ) / t'))))) +
    (Fintype.card (Sym2 (Fin n)) : ℝ≥0∞) * (4⁻¹ : ℝ≥0∞) ^ R with hF
  set Eerr := dist (vec G y0) ystar
  set Inv : ℕ → Option (Point n me) → Prop := fun j o => ∃ y, o = some y ∧
    dist (vec G y) ystar ≤ (3 / 4) ^ j * Eerr + Δ / 32 with hInv
  obtain ⟨hδ0, hδ1, hδlo, hδhi⟩ := levDelta_spec hΔ0 hΔ R
  have hμ := levBits_spec hΔ0
  have hε0 : 0 ≤ levEps Δ := by unfold levEps; positivity
  have hε : levEps Δ ≤ 1 / 4 := by unfold levEps; linarith
  -- one step preserves the invariant on D4 success
  have hstep : ∀ j (y : Point n me), Inv j (some y) → ∀ out,
      Sparsify.Good G (lewisW (1 - 2 / p) spt y) K t' (levDelta Δ R) R out →
      Inv (j + 1) (some (lewisNewY E p (levBits Δ) spt
        (lap out univ + lewisE E (1 - 2 / p) spt y)⁻¹)) := by
    rintro j y ⟨y', hy', hd⟩ out hg
    cases hy'
    refine ⟨_, rfl, ?_⟩
    set B := diagonal (vec G spt) * matrix G E
    have h1 := lewis_step_err G E hrowA hs (by linarith : 0 < p) (levBits Δ) hg hε0 hε
      hδlo hδhi
    have hA := det_ne_zero_of_idRows (matrix_idRows G E)
    have hB : (Bᵀ * B).det ≠ 0 := diag_det hA fun j => (hs j).ne'
    have hrowB : ∀ i, B i ≠ 0 := fun i h0 => by
      apply hrowA i
      funext j
      have := congrFun h0 j
      simp only [B, diagonal_mul, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left (hs i).ne'
    have h2 := lewisMap_dist_le hB hrowB (by linarith : 0 < p) hp2 (vec G y) ystar
    rw [hfix] at h2
    have hζ : p * (2 * levEps Δ) + (1 / 2) ^ levBits Δ ≤ Δ / 128 := by
      unfold levEps; nlinarith
    have hc : 1 - p / 2 ≤ 3 / 4 := by linarith
    have hE0 : 0 ≤ Eerr := dist_nonneg
    have hd0 : 0 ≤ dist (vec G y) ystar := dist_nonneg
    calc _ ≤ dist (vec G (lewisNewY E p (levBits Δ) spt
            (lap out univ + lewisE E (1 - 2 / p) spt y)⁻¹)) (lewisMap p B (vec G y)) +
          dist (lewisMap p B (vec G y)) ystar := dist_triangle _ _ _
      _ ≤ Δ / 128 + 3 / 4 * dist (vec G y) ystar := by
          refine add_le_add (h1.trans hζ) (h2.trans ?_)
          exact mul_le_mul_of_nonneg_right hc hd0
      _ ≤ Δ / 128 + 3 / 4 * ((3 / 4) ^ j * Eerr + Δ / 32) := by gcongr
      _ = (3 / 4) ^ (j + 1) * Eerr + Δ / 32 := by ring
  -- induction over the iterations
  have hmain : ∀ j, mass ((lewisLoop E p (levBits Δ) spt y0 K J t' R j).eval G.out)
      (fun o => ¬ Inv j o) ≤ j * F := by
    intro j
    induction j with
    | zero =>
        simp only [lewisLoop, RTree.eval_pure, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero]
        rw [mass_eq_tsum]
        refine ENNReal.tsum_eq_zero.mpr fun o => ?_
        by_cases ho : o = some y0
        · subst ho
          have : Inv 0 (some y0) := ⟨y0, rfl, by
            simp only [pow_zero, one_mul, Eerr]; linarith⟩
          simp [this]
        · simp [PMF.pure_apply, ho]
    | succ j ih =>
        simp only [lewisLoop, RTree.eval_cast, RTree.eval_bind]
        refine (mass_bind_le_add _ _ (fun o => ¬ Inv j o) _ (ε := F) ih fun o ho => ?_).trans
          (le_of_eq (by push_cast; ring))
        push Not at ho
        obtain ⟨y, rfl, hy⟩ := ho
        simp only [lewisStepProg, RTree.eval_bind]
        refine (mass_bind_le_add _ _
          (fun o => ¬ ∃ out, o = some out ∧
            Sparsify.Good G (lewisW (1 - 2 / p) spt y) K t' (levDelta Δ R) R out) _
          (ε := 0) ?_ ?_).trans (by rw [add_zero])
        · refine (Sparsify.sparsify_fail_le hCs0 hCs (fun e => by unfold lewisW; positivity)
            hK ht' hδ0 hδ1 R).trans ?_
          refine add_le_add_right (mul_le_mul_left ?_ _) _
          exact_mod_cast Finset.card_le_univ _
        · intro o ho
          push Not at ho
          obtain ⟨out, rfl, hg⟩ := ho
          have := hstep j y ⟨y, rfl, hy⟩ out hg
          simp [RTree.eval_pure, this]
  refine (le_of_eq_of_le ?_ (hmain JL))
  rfl


#print axioms explicitGram_lewis
#print axioms vec_lewisNewY
#print axioms lewis_step_err
#print axioms lewisLoop_cost
#print axioms lewisLoop_fail_le

end
end CutQueryComplexity.ImplicitLP.GenericQuery
