import CutQueryComplexity.ImplicitLP.PathFollowing.Invariant
import CutQueryComplexity.DirectedMincut.SmallShore

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! # Rounded initialization and exact state updates

The Lewis observation is rounded once, before defining the artificial cost. This makes
the artificial centrality exactly zero despite observation error. A repaired public
direction is then added exactly; no coordinate rounding is applied after feasibility repair.
-/

namespace CutQueryComplexity.ImplicitLP.PathFollowing

open Matrix Finset Real
open DirectedMincut (LPPoint)
open Probability
open scoped ENNReal
noncomputable section

variable {n : ℕ} {E : NewtonPub}

/-- The public strict start from the queried degree imbalance. -/
def strictStartPoint (b : Fin n → ℝ) : LPPoint (Fin n) :=
  ⟨fun _ _ => 0, 0, fun v => 2 * n + b v / 2, fun v => 2 * n - b v / 2⟩

/-- Query all in-degrees and out-degrees, then form the strict start. -/
def strictStartProg (n : ℕ) : DTree (Finset (Fin n)) ℕ (LPPoint (Fin n)) (2 * n) :=
  ((DirectedMincut.degs (univ : Finset (Fin n)).toList).map fun d =>
    strictStartPoint (fun v => (d.1 v : ℝ) - d.2 v)).cast (by simp)

theorem strictStartProg_eval (G : DiGraph (Fin n)) :
    (strictStartProg n).eval G.out = strictStartPoint (DirectedMincut.bvec G) := by
  have hd : (DirectedMincut.degs (univ : Finset (Fin n)).toList).eval G.out =
      (G.outdeg, G.indeg) := by
    apply Prod.ext <;> funext v
    · exact (DirectedMincut.degs_correct G _ (by simp : v ∈ (univ : Finset (Fin n)).toList)).1
    · exact (DirectedMincut.degs_correct G _ (by simp : v ∈ (univ : Finset (Fin n)).toList)).2
  simp only [strictStartProg, DTree.eval_cast, DTree.eval_map, hd]
  rfl

/-- The constructed point is strictly feasible for the original directed terminal LP. -/
theorem strictStartProg_feasible (G : DiGraph (Fin n)) (s t : Fin n) (hG : G.Simple) :
    let x := (strictStartProg n).eval G.out
    DirectedMincut.Feasible G s t x ∧ -2 < x.q ∧ x.q < 2 * n ∧
      (∀ v, 0 < x.yp v ∧ x.yp v < 4 * n) ∧
      (∀ v, 0 < x.ym v ∧ x.ym v < 4 * n) := by
  simpa only [strictStartProg_eval, strictStartPoint, Fintype.card_fin] using
    DirectedMincut.strict_start (G := G) (s := s) (t := t) hG

theorem strictStartProg_cost (G : DiGraph (Fin n)) : (strictStartProg n).cost G.out ≤ 2 * n :=
  DTree.cost_le _ _

def roundPoint (p : ℕ) (x : LPPoint (Fin n)) : LPPoint (Fin n) := mapPt (dyadicRound p) x

theorem roundPoint_error (G : DiGraph (Fin n)) (p : ℕ) (x : LPPoint (Fin n))
    (i : Fin (lpM G)) : |lpVec G (roundPoint p x) i - lpVec G x i| ≤ (1 / 2 : ℝ) ^ p := by
  rw [roundPoint, lpVec_mapPt, abs_sub_comm]
  exact sub_dyadicRound_le p _

theorem roundPoint_grid (G : DiGraph (Fin n)) (p : ℕ) (x : LPPoint (Fin n))
    (i : Fin (lpM G)) : ∃ k : ℤ, lpVec G (roundPoint p x) i = k / 2 ^ p := by
  rw [roundPoint, lpVec_mapPt]
  exact dyadicRound_int p _

/-- Clip all public pair coordinates, including pairs that have no actual hidden row. -/
def clipPairPoint (x : LPPoint (Fin n)) : LPPoint (Fin n) :=
  ⟨fun u v => clipTo (-1) 1 (x.z u v), x.q, x.yp, x.ym⟩

theorem clipPairPoint_bounds (x : LPPoint (Fin n)) (u v : Fin n) :
    -1 ≤ (clipPairPoint x).z u v ∧ (clipPairPoint x).z u v ≤ 1 :=
  ⟨le_clipTo _ _ _, clipTo_le (by norm_num) _⟩

/-- Clipping absent pairs is harmless to every actual row, so it is safe before extraction. -/
theorem lpVec_clipPairPoint (G : DiGraph (Fin n)) (x : LPPoint (Fin n))
    (hb : ∀ i e, lpHidF G i = some e → -1 ≤ lpVec G x i ∧ lpVec G x i ≤ 1) :
    lpVec G (clipPairPoint x) = lpVec G x := by
  funext i
  obtain ⟨row, rfl⟩ := (lpEquiv G).surjective i
  rcases row with ⟨p, k⟩ | (_ | (j | j))
  · have hi : lpHidF G (lpEquiv G (.inl ⟨p, k⟩)) = some s(p.1.1, p.1.2) := by
      simp [lpHidF, lpHid]
    have h := hb _ _ hi
    simp only [lpVec, Equiv.symm_apply_apply, lpVal] at h ⊢
    exact clipTo_of_mem h.1 h.2
  all_goals simp only [lpVec, Equiv.symm_apply_apply, lpVal, clipPairPoint]

/-- The public clipping bridge supplies the bounds on absent pairs required by the
terminal LP, while preserving its actual row constraint. -/
theorem clipPairPoint_feasible (G : DiGraph (Fin n)) (s t : Fin n) (x : LPPoint (Fin n))
    (hc : (lpA G s t)ᵀ *ᵥ lpVec G x = DirectedMincut.bvec G)
    (hb : ∀ i e, lpHidF G i = some e → -1 ≤ lpVec G x i ∧ lpVec G x i ≤ 1)
    (hq : -2 ≤ x.q ∧ x.q ≤ 2 * n)
    (hp : ∀ v, 0 ≤ x.yp v ∧ x.yp v ≤ 4 * n)
    (hm : ∀ v, 0 ≤ x.ym v ∧ x.ym v ≤ 4 * n) :
    DirectedMincut.Feasible G s t (clipPairPoint x) := by
  refine ⟨fun u v _ => clipPairPoint_bounds x u v, hq.1, ?_, ?_, ?_, ?_⟩
  · simpa only [clipPairPoint, Fintype.card_fin] using hq.2
  · simpa only [clipPairPoint, Fintype.card_fin] using hp
  · simpa only [clipPairPoint, Fintype.card_fin] using hm
  · intro w
    rw [← lpVec_clipPairPoint G x hb, lpA_transpose_lpVec] at hc
    exact congrFun hc w

theorem clipPairPoint_obj (x : LPPoint (Fin n)) :
    DirectedMincut.obj (clipPairPoint x) = DirectedMincut.obj x := rfl

/-- The artificial cost is defined from the stored, rounded log weights. -/
def artificialCost (κ m x X : LPPoint (Fin n)) : LPPoint (Fin n) :=
  map2Pt (fun a b => -Real.exp a * b) X (barDphiPt κ m x)

theorem lpVec_artificialCost (G : DiGraph (Fin n)) (κ m x X : LPPoint (Fin n)) :
    lpVec G (artificialCost κ m x X) =
      fun i => -Real.exp (lpVec G X i) * barDphi (lpVec G κ) (lpVec G m) (lpVec G x) i := by
  funext i
  rw [artificialCost, lpVec_map2Pt, lpVec_barDphiPt]

/-- Centrality at parameter one is exactly zero, independently of the Lewis error. -/
theorem artificialCost_center (G : DiGraph (Fin n)) (s t : Fin n) (κ m x X : LPPoint (Fin n))
    {C : ℝ} (hC : 0 ≤ C) :
    cent C (lpA G s t) (barS (lpVec G κ) (lpVec G m) (lpVec G x))
      (barDphi (lpVec G κ) (lpVec G m) (lpVec G x))
      (lpVec G (artificialCost κ m x X)) 1 (fun i => exp (lpVec G X i)) = 0 := by
  apply le_antisymm _ (cent_nonneg hC _ _)
  refine (ciInf_le (cent_bdd hC _ _) (0 : Fin n → ℝ)).trans ?_
  rw [lpVec_artificialCost]
  simp [mixed, wnorm]

/-- Exact addition after explicit-row repair preserves the affine constraint. -/
theorem repaired_update_constraint (G : DiGraph (Fin n)) (s t : Fin n)
    (x d : LPPoint (Fin n)) {bc : Fin n → ℝ}
    (hx : (lpA G s t)ᵀ *ᵥ lpVec G x = bc) :
    (lpA G s t)ᵀ *ᵥ lpVec G
      (addPt x (lpRepPt d ((lpA G s t)ᵀ *ᵥ lpVec G d))) = bc := by
  rw [lpVec_addPt, mulVec_add, lpRepPt_spec]
  rw [show lpVec G d - selector (lpIota G) *ᵥ ((lpA G s t)ᵀ *ᵥ lpVec G d) =
    repairDir (lpA G s t) (lpIota G) (lpVec G d) from rfl]
  rw [repair_feasible (lpA_idRows G s t), hx, add_zero]

/-- Rounding before repair changes no hidden coordinate during repair. -/
theorem rounded_repair_hidden (G : DiGraph (Fin n)) (s t : Fin n) (p : ℕ)
    (d : LPPoint (Fin n)) {i : Fin (lpM G)} {e : Sym2 (Fin n)}
    (hi : lpHidF G i = some e) :
    lpVec G (lpRepPt (roundPoint p d) ((lpA G s t)ᵀ *ᵥ lpVec G (roundPoint p d))) i =
      dyadicRound p (lpVec G d i) := by
  rw [lpVec_hid G _ i e hi, lpVec_hid G d i e hi]
  change pairOf (roundPoint p d).z e = _
  rw [roundPoint, pairOf_mapPt]

variable {G : DiGraph (Fin E.n)} {P : Params E} {bc : Fin E.n → ℝ}

theorem potential_of_initial_window (H : Regime G P bc) {x X : LPPoint (Fin E.n)}
    (hw : ∀ i, |lpVec G X i - Real.log
      (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
        (lpA G P.s P.terminal) (lpVec G x) i)| ≤ P.Δ) :
    pot P.μ (lpVec G X - fun i => Real.log
      (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
        (lpA G P.s P.terminal) (lpVec G x) i)) ≤ 12 * lpM G * P.T / (1 / (2 * P.L) / 8) := by
  have ha : 1 / (2 * P.L) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [H.L_ge])
  have hμΔ : P.μ * P.Δ ≤ 1 / 4 := by
    unfold Params.μ
    have hL : 0 < P.L := by linarith [H.L_ge]
    have he : (1 / (2 * P.L) / 8) / (12 * P.Δ) * P.Δ = (1 / (2 * P.L)) / 96 := by
      field_simp [H.Δ_pos.ne', hL.ne']; ring
    rw [he]
    linarith
  have hp : pot P.μ (lpVec G X - fun i => Real.log
      (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
        (lpA G P.s P.terminal) (lpVec G x) i)) ≤ 4 * lpM G := by
    unfold pot
    calc _ ≤ ∑ _i : Fin (lpM G), (4 : ℝ) := by
          apply sum_le_sum
          intro i _
          have he := (cosh_add_abs_sinh (P.μ * (lpVec G X i - Real.log
            (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
              (lpA G P.s P.terminal) (lpVec G x) i)))).1
          have hb : |P.μ * (lpVec G X i - Real.log
            (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
              (lpA G P.s P.terminal) (lpVec G x) i))| ≤ 1 / 4 := by
            rw [abs_mul, abs_of_pos H.μ_pos]
            exact (mul_le_mul_of_nonneg_left (hw i) H.μ_pos.le).trans hμΔ
          have hExp := (exp_le_exp.mpr hb).trans exp_quarter_le
          simp only [Pi.sub_apply]
          linarith [abs_nonneg (sinh (P.μ * (lpVec G X i - Real.log
            (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
              (lpA G P.s P.terminal) (lpVec G x) i))))]
      _ = 4 * lpM G := by simp; ring
  refine hp.trans ?_
  rw [le_div_iff₀ (by have := H.L_ge; positivity)]
  calc 4 * (lpM G : ℝ) * (1 / (2 * P.L) / 8) ≤ 4 * lpM G * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ 12 * lpM G * P.T := by
      have := mul_le_mul_of_nonneg_left H.T_ge (by positivity : (0 : ℝ) ≤ 12 * lpM G)
      nlinarith [H.rows_pos]

def initialWeights (P : Params E) (x : LPPoint (Fin E.n)) :=
  (lewisLoop P.s P.terminal (1 - 1 / P.L) (levBits P.Δ) (invSlackPt P.κ P.m x)
    zeroPt P.Kd P.J P.samples P.rounds (batchJL E P.Δ)).map fun out =>
      out.map (fun y => roundPoint (levBits P.Δ) (obsPt P.c₀ y))

/-- A rounded initialization yields an invariant at parameter one with its constructed cost.
The input is a feasible point with a licensed slack floor; no initial centrality is assumed. -/
theorem initialWeights_failure (H : Regime G P bc) (x : LPPoint (Fin E.n))
    (hx : lpVec G x ∈ Feasible (lpA G P.s P.terminal) bc (lpVec G P.κ) (lpVec G P.m))
    (hs : ∀ i, E.sst ≤ slk (lpVec G P.κ) (lpVec G P.m) (lpVec G x) i) :
    mass ((initialWeights P x).eval G.out)
      (fun out => ¬∃ X, out = some X ∧
        Invariant G {P with c := artificialCost P.κ P.m x X} bc 1 (x, X) ∧
        ∀ i, ∃ k : ℤ, lpVec G X i = k / 2 ^ levBits P.Δ) ≤
      batchJL E P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) := by
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
  obtain ⟨_, hprob⟩ := lewisStage G H.distinct H.κ_pos hx.2 H.U_ge H.width_le hsst hs H.M_le
    (lpVec_invSlackPt G H.κ_pos hx.2 (κp := P.κ) (mp := P.m) (xp := x) rfl rfl rfl)
    hp0 hp2 hc₀ H.Δ_pos hΔ P.J P.rounds
    H.Csym_nonneg H.sym_le H.vertices_le H.samples_pos
  rw [initialWeights, RTree.eval_map, mass_map]
  refine (mass_mono _ (fun out hbad hgood => ?_)).trans hprob
  obtain ⟨y, rfl, _, hy⟩ := hgood
  apply hbad
  let X := roundPoint (levBits P.Δ) (obsPt P.c₀ y)
  have hwin : ∀ i, |lpVec G X i - Real.log
      (gfun (lpVec G P.κ) (lpVec G P.m) (1 - 1 / P.L) P.c₀
        (lpA G P.s P.terminal) (lpVec G x) i)| ≤ P.Δ := by
    intro i
    have hr := roundPoint_error G (levBits P.Δ) (obsPt P.c₀ y) i
    have he := levBits_spec H.Δ_pos
    rw [lpVec_obsPt] at hr
    change |lpVec G X i - Real.log (exp (lpVec G y i) + P.c₀)| ≤ (1 / 2 : ℝ) ^ levBits P.Δ at hr
    exact (abs_sub_le (lpVec G X i) (Real.log (exp (lpVec G y i) + P.c₀)) _).trans
      (by linarith [hy i, H.Δ_pos])
  refine ⟨X, rfl, ⟨hx, potential_of_initial_window H (x := x) (X := X) hwin, ?_⟩,
    roundPoint_grid G _ _⟩
  have hc := artificialCost_center G P.s P.terminal P.κ P.m x X H.C_pos.le
  exact hc.le.trans H.Δ_pos.le

end
end CutQueryComplexity.ImplicitLP.PathFollowing

#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.artificialCost_center
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.strictStartProg_feasible
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.strictStartProg_cost
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.repaired_update_constraint
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.rounded_repair_hidden
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.initialWeights_failure
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.lpVec_clipPairPoint
#print axioms CutQueryComplexity.ImplicitLP.PathFollowing.clipPairPoint_feasible
