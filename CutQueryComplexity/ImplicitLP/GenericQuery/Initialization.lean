import CutQueryComplexity.ImplicitLP.GenericQuery.Invariant

/-! # Rounded initialization from the supplied general strict start

The artificial cost is formed from the stored rounded observation, hence its
centrality is exactly zero. Feasibility repair is applied before exact addition;
there is no subsequent primal rounding that could destroy the affine equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Real Probability
open scoped ENNReal
noncomputable section
variable {n me : ℕ} {E : NewtonPub}

def roundPoint (p : ℕ) (x : Point n me) : Point n me := mapPt (dyadicRound p) x

theorem roundPoint_error (G : DiGraph (Fin n)) (p : ℕ) (x : Point n me)
    (i : Fin (rowCount G me)) : |vec G (roundPoint p x) i - vec G x i| ≤ (1 / 2 : ℝ) ^ p := by
  rw [roundPoint, vec_mapPt, abs_sub_comm]
  exact sub_dyadicRound_le p _

theorem roundPoint_grid (G : DiGraph (Fin n)) (p : ℕ) (x : Point n me)
    (i : Fin (rowCount G me)) : ∃ k : ℤ, vec G (roundPoint p x) i = k / 2 ^ p := by
  rw [roundPoint, vec_mapPt]
  exact dyadicRound_int p _

/-- The artificial cost is defined from the stored, rounded log weights. -/
def artificialCost (κ m x X : Point n me) : Point n me :=
  map2Pt (fun a b => -Real.exp a * b) X (barDphiPt κ m x)

theorem vec_artificialCost (G : DiGraph (Fin n)) (κ m x X : Point n me) :
    vec G (artificialCost κ m x X) =
      fun i => -Real.exp (vec G X i) * barDphi (vec G κ) (vec G m) (vec G x) i := by
  funext i
  rw [artificialCost, vec_map2Pt, vec_barDphiPt]

/-- Centrality at parameter one is exactly zero, independently of the Lewis error. -/
theorem artificialCost_center (G : DiGraph (Fin n)) (ER : ExplicitRows n me) (κ m x X : Point n me)
    {C : ℝ} (hC : 0 ≤ C) :
    cent C (matrix G ER) (barS (vec G κ) (vec G m) (vec G x))
      (barDphi (vec G κ) (vec G m) (vec G x))
      (vec G (artificialCost κ m x X)) 1 (fun i => exp (vec G X i)) = 0 := by
  apply le_antisymm _ (cent_nonneg hC _ _)
  refine (ciInf_le (cent_bdd hC _ _) (0 : Fin n → ℝ)).trans ?_
  rw [vec_artificialCost]
  simp [mixed, wnorm]
  rfl

/-- Exact addition after explicit-row repair preserves the affine constraint. -/
theorem repaired_update_constraint (G : DiGraph (Fin n)) (ER : ExplicitRows n me)
    (x d : Point n me) {bc : Fin n → ℝ}
    (hx : (matrix G ER)ᵀ *ᵥ vec G x = bc) :
    (matrix G ER)ᵀ *ᵥ vec G
      (addPt x (repairPoint ER d ((matrix G ER)ᵀ *ᵥ vec G d))) = bc := by
  rw [vec_addPt, mulVec_add, vec_repairPoint]
  rw [show vec G d - selector (iota G ER) *ᵥ ((matrix G ER)ᵀ *ᵥ vec G d) =
    repairDir (matrix G ER) (iota G ER) (vec G d) from rfl]
  rw [repair_feasible (matrix_idRows G ER), hx, add_zero]

/-- Rounding before repair changes no hidden coordinate during repair. -/
theorem rounded_repair_hidden (G : DiGraph (Fin n)) (ER : ExplicitRows n me) (p : ℕ)
    (d : Point n me) {i : Fin (rowCount G me)} {e : Sym2 (Fin n)}
    (hi : hidden G me i = some e) :
    vec G (repairPoint ER (roundPoint p d) ((matrix G ER)ᵀ *ᵥ vec G (roundPoint p d))) i =
      dyadicRound p (vec G d i) := by
  rw [vec_hidden G _ i e hi, vec_hidden G d i e hi]
  change pairOf (roundPoint p d).pair e = _
  rw [roundPoint, pairOf_mapPt]

variable {G : DiGraph (Fin E.n)} {P : Params E me} {bc : Fin E.n → ℝ}

theorem potential_of_initial_window (H : Regime G P bc) {x X : Point E.n me}
    (hw : ∀ i, |vec G X i - Real.log
      (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G x) i)| ≤ P.Δ) :
    pot P.μ (vec G X - fun i => Real.log
      (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G x) i)) ≤ 12 * rowCount G me * P.T / (1 / (2 * P.L) / 8) := by
  have ha : 1 / (2 * P.L) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [H.L_ge])
  have hμΔ : P.μ * P.Δ ≤ 1 / 4 := by
    unfold Params.μ
    have hL : 0 < P.L := by linarith [H.L_ge]
    have he : (1 / (2 * P.L) / 8) / (12 * P.Δ) * P.Δ = (1 / (2 * P.L)) / 96 := by
      field_simp [H.Δ_pos.ne', hL.ne']; ring
    rw [he]
    linarith
  have hp : pot P.μ (vec G X - fun i => Real.log
      (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G x) i)) ≤ 4 * rowCount G me := by
    unfold pot
    calc _ ≤ ∑ _i : Fin (rowCount G me), (4 : ℝ) := by
          apply sum_le_sum
          intro i _
          have he := (cosh_add_abs_sinh (P.μ * (vec G X i - Real.log
            (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
              (matrix G P.rows) (vec G x) i)))).1
          have hb : |P.μ * (vec G X i - Real.log
            (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
              (matrix G P.rows) (vec G x) i))| ≤ 1 / 4 := by
            rw [abs_mul, abs_of_pos H.μ_pos]
            exact (mul_le_mul_of_nonneg_left (hw i) H.μ_pos.le).trans hμΔ
          have hExp := (exp_le_exp.mpr hb).trans exp_quarter_le
          simp only [Pi.sub_apply]
          linarith [abs_nonneg (sinh (P.μ * (vec G X i - Real.log
            (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
              (matrix G P.rows) (vec G x) i))))]
      _ = 4 * rowCount G me := by simp; ring
  refine hp.trans ?_
  rw [le_div_iff₀ (by have := H.L_ge; positivity)]
  calc 4 * (rowCount G me : ℝ) * (1 / (2 * P.L) / 8) ≤ 4 * rowCount G me * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ 12 * rowCount G me * P.T := by
      have := mul_le_mul_of_nonneg_left H.T_ge (by positivity : (0 : ℝ) ≤ 12 * rowCount G me)
      nlinarith [H.rows_pos]

def initialWeights (P : Params E me) (x : Point E.n me) :=
  (lewisLoop P.rows (1 - 1 / P.L) (levBits P.Δ) (invSlackPt P.κ P.m x)
    zeroPt P.Kd P.J P.samples P.rounds (batchJL E P.a0 P.Δ)).map fun out =>
      out.map (fun y => roundPoint (levBits P.Δ) (obsPt P.c₀ y))

/-- A rounded initialization yields an invariant at parameter one with its constructed cost.
The input is a feasible point with a licensed slack floor; no initial centrality is assumed. -/
theorem initialWeights_failure (H : Regime G P bc) (x : Point E.n me)
    (hx : vec G x ∈ Feasible (matrix G P.rows) bc (vec G P.κ) (vec G P.m))
    (hs : ∀ i, E.sst ≤ slk (vec G P.κ) (vec G P.m) (vec G x) i) :
    mass ((initialWeights P x).eval G.out)
      (fun out => ¬∃ X, out = some X ∧
        Invariant G {P with c := artificialCost P.κ P.m x X} bc 1 (x, X) ∧
        ∀ i, ∃ k : ℤ, vec G X i = k / 2 ^ levBits P.Δ) ≤
      batchJL E P.a0 P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) := by
  have hsst : 0 < E.sst := by
    have := H.ε_pos
    have hMb : 0 < E.Mbar := H.rows_pos.trans_le H.M_le
    have hn : (0 : ℝ) < E.n := by linarith [H.rank_ge]
    have hU : 0 < E.U := by linarith [H.U_ge]
    unfold NewtonPub.sst
    positivity
  have hc₀ : 0 ≤ P.c₀ := by
    have hMb : 0 < E.Mbar := H.rows_pos.trans_le H.M_le
    unfold Params.c₀
    positivity
  have hΔ : P.Δ ≤ 256 := by
    have ha : 1 / (2 * P.L) ≤ (1 / 4 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [H.L_ge])
    have ha0 : 0 ≤ 1 / (2 * P.L) := by have := H.L_ge; positivity
    have := H.Δ_le
    nlinarith
  obtain ⟨hp0, hp2⟩ := lewisExp_bounds H.L_ge
  obtain ⟨_, hprob⟩ := lewisStage G P.rows H.rank_pos H.a0_pos H.a0_le H.row_norms H.κ_pos hx.2 H.U_ge H.width_le hsst hs H.M_le
    (vec_invSlackPt G H.κ_pos hx.2 (κp := P.κ) (mp := P.m) (xp := x) rfl rfl rfl)
    hp0 hp2 hc₀ H.Δ_pos hΔ P.J P.rounds
    H.Csym_nonneg H.sym_le H.vertices_le H.samples_pos
  rw [initialWeights, RTree.eval_map, mass_map]
  refine (mass_mono _ (fun out hbad hgood => ?_)).trans hprob
  obtain ⟨y, rfl, _, hy⟩ := hgood
  apply hbad
  let X := roundPoint (levBits P.Δ) (obsPt P.c₀ y)
  have hwin : ∀ i, |vec G X i - Real.log
      (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G x) i)| ≤ P.Δ := by
    intro i
    have hr := roundPoint_error G (levBits P.Δ) (obsPt P.c₀ y) i
    have he := levBits_spec H.Δ_pos
    rw [vec_obsPt] at hr
    change |vec G X i - Real.log (exp (vec G y i) + P.c₀)| ≤ (1 / 2 : ℝ) ^ levBits P.Δ at hr
    exact (abs_sub_le (vec G X i) (Real.log (exp (vec G y i) + P.c₀)) _).trans
      (by linarith [hy i, H.Δ_pos])
  refine ⟨X, rfl, ⟨hx, potential_of_initial_window H (x := x) (X := X) hwin, ?_⟩,
    roundPoint_grid G _ _⟩
  have hc := artificialCost_center G P.rows P.κ P.m x X H.C_pos.le
  exact hc.le.trans H.Δ_pos.le


#print axioms artificialCost_center
#print axioms repaired_update_constraint
#print axioms rounded_repair_hidden
#print axioms initialWeights_failure

end
end CutQueryComplexity.ImplicitLP.GenericQuery
