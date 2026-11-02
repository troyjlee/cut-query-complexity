import CutQueryComplexity.ImplicitLP.GenericQuery.Budget
import CutQueryComplexity.ImplicitLP.GenericQuery.Initialization

/-! # A real general incidence-LP path execution

Initialization, artificial-cost descent, a margin-producing cost switch,
true-cost ascent and frozen centering are composed into one public query tree.
All later invariants are proved inductively. The final good event works
simultaneously for every feasible comparator in the closed box.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Real Probability
open PathFollowing (cent_cost_change center_step_inexact objective_gap_from_centrality)
open scoped ENNReal
noncomputable section
variable {me : ℕ} {E : NewtonPub} {G : DiGraph (Fin E.n)} {P : Params E me} {bc : Fin E.n → ℝ}

/-- The artificial cost has the public norm bound needed by the numerical primitives. -/
theorem artificialCost_bound (H : Regime G P bc) {x X : Point E.n me}
    (hx : vec G x ∈ Feasible (matrix G P.rows) bc (vec G P.κ) (vec G P.m))
    (hs : ∀ i, 1 / E.U ≤ slk (vec G P.κ) (vec G P.m) (vec G x) i)
    (hp : pot P.μ (vec G X - fun i => Real.log
      (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G x) i)) ≤
      12 * rowCount G me * P.T / (1 / (2 * P.L) / 8)) :
    ‖vec G (artificialCost P.κ P.m x X)‖ ≤ 4 * E.U := by
  have hw := (weight_bounds_of_potential H (st := (x, X)) hp).2.1
  have hU : 0 < E.U := by linarith [H.U_ge]
  rw [vec_artificialCost]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (exp_pos _)]
  have hd := (eq_barrier H.κ_pos hx.2 i).2.1
  have hds : |barDphi (vec G P.κ) (vec G P.m) (vec G x) i| ≤ E.U := by
    have hb := mul_le_mul_of_nonneg_left (hs i)
      (abs_nonneg (barDphi (vec G P.κ) (vec G P.m) (vec G x) i))
    change _ ≤ |barDphi (vec G P.κ) (vec G P.m) (vec G x) i| *
      ((π / 2 - |theta (vec G P.κ) (vec G P.m) (vec G x) i|) / vec G P.κ i) at hb
    have hdiv : |barDphi (vec G P.κ) (vec G P.m) (vec G x) i| / E.U ≤ 1 := by
      simpa only [mul_one_div] using hb.trans hd
    exact (div_le_one hU).mp hdiv
  exact mul_le_mul (hw i) hds (abs_nonneg _) (by norm_num)

def Regime.withCost (H : Regime G P bc) (cp : Point E.n me)
    (hc : ‖vec G cp‖ ≤ 4 * E.U) : Regime G {P with c := cp} bc where
  rank_pos := H.rank_pos
  a0_pos := H.a0_pos
  a0_le := H.a0_le
  row_norms := H.row_norms
  L_ge := H.L_ge
  logM_le := H.logM_le
  κ_pos := H.κ_pos
  U_ge := H.U_ge
  width_le := H.width_le
  reference := H.reference
  reference_feasible := H.reference_feasible
  reference_slack := H.reference_slack
  M_le := H.M_le
  ε_pos := H.ε_pos
  ε_le := H.ε_le
  cost_le := hc
  C_eq := H.C_eq
  η_pos := H.η_pos
  η_le := H.η_le
  Δ_pos := H.Δ_pos
  Δ_le := H.Δ_le
  K_nonneg := H.K_nonneg
  K_le := H.K_le
  window_le := H.window_le
  Csym := H.Csym
  Csym_nonneg := H.Csym_nonneg
  sym_le := H.sym_le
  vertices_le := H.vertices_le
  samples_pos := H.samples_pos

/-- A sufficiently small public parameter lets a successful batch switch to any
licensed public objective, using the batch's proved centrality margin. -/
theorem batchGood_changeCost (H : Regime G P bc) {t : ℝ} {st : State E.n me}
    (cp : Point E.n me) (hcp : ‖vec G cp‖ ≤ 4 * E.U)
    (htsmall : |t| * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤ 1 / (2 * P.L) * P.Δ / 2)
    (hg : BatchGood G P.rows bc (vec G P.κ) (vec G P.m) (vec G P.c)
      t P.L P.c₀ P.Δ P.T (some st)) : Invariant G {P with c := cp} bc t st := by
  obtain ⟨xn, Xn, he, hF, hP, hc⟩ := hg
  have he' : (xn, Xn) = st := Option.some.inj he.symm
  cases he'
  refine ⟨hF, hP, ?_⟩
  have hMb : 0 < E.Mbar := H.rows_pos.trans_le H.M_le
  have hU : 0 < E.U := by linarith [H.U_ge]
  have hweights := (weight_bounds_of_potential H (st := (xn, Xn)) hP).1
  have hS := barS_pos H.κ_pos hF.2
  let q := fun i => (vec G cp i - vec G P.c i) /
    (exp (vec G Xn i) * barS (vec G P.κ) (vec G P.m) (vec G xn) i)
  have hq : ‖q‖ ≤ 32 * E.Mbar * E.U ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have hcp' : |vec G cp i| ≤ 4 * E.U := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ i).trans hcp
    have hc' : |vec G P.c i| ≤ 4 * E.U := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ i).trans H.cost_le
    have hnum : |vec G cp i - vec G P.c i| ≤ 8 * E.U :=
      (abs_sub _ _).trans (by linarith)
    have hden : 1 / (4 * E.Mbar * E.U) ≤ exp (vec G Xn i) *
        barS (vec G P.κ) (vec G P.m) (vec G xn) i := by
      calc 1 / (4 * E.Mbar * E.U) = (1 / (4 * E.Mbar)) * (1 / E.U) := by ring
        _ ≤ _ := mul_le_mul (hweights i) (barrier_env H.κ_pos hF.2 H.U_ge H.width_le i).1
          (by positivity) (exp_pos _).le
    change |q i| ≤ _
    dsimp [q]
    rw [abs_div, abs_of_pos (mul_pos (exp_pos _) (hS i)),
      div_le_iff₀ (mul_pos (exp_pos _) (hS i))]
    refine hnum.trans ?_
    have hh := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 32 * E.Mbar * E.U ^ 2)
    have heq : (32 * E.Mbar * E.U ^ 2) * (1 / (4 * E.Mbar * E.U)) = 8 * E.U := by
      field_simp [hMb.ne', hU.ne']
      ring
    rwa [heq] at hh
  have hmix : mixed P.C (fun i => exp (vec G Xn i)) q ≤ P.T * (32 * E.Mbar * E.U ^ 2) :=
    (mixedEnvelope_of_potential H (st := (xn, Xn)) hP q).trans
      (mul_le_mul_of_nonneg_left hq (by linarith [H.T_ge]))
  have hchange := cent_cost_change (c := vec G P.c) (c' := vec G cp)
    (dφ := barDphi (vec G P.κ) (vec G P.m) (vec G xn)) H.C_pos
    (det_ne_zero_of_idRows (matrix_idRows G P.rows)) hS
    (fun i => exp_pos (vec G Xn i)) t
  have hnew := hchange.trans (add_le_add hc (mul_le_mul_of_nonneg_left hmix (abs_nonneg t)))
  exact hnew.trans (by nlinarith)

/-- Execute one actual batch and then reinterpret its public state at the new objective. -/
theorem batch_switch_failure (H : Regime G P bc) {t : ℝ} {st : State E.n me}
    (cp : Point E.n me) (hcp : ‖vec G cp‖ ≤ 4 * E.U)
    (ht : |t| ≤ 16 * E.n / E.ε)
    (htsmall : |t| * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤ 1 / (2 * P.L) * P.Δ / 2)
    (hs : Invariant G P bc t st) :
    mass ((batch P t st).eval G.out) (fun out => ¬Good G {P with c := cp} bc t out) ≤
      H.batchFailure := by
  rw [batch, RTree.eval_cast]
  refine (mass_mono _ (fun out hbad hg => ?_)).trans (batchProg_fail_public H ht hs)
  have hg' := hg
  obtain ⟨xn, Xn, he, _⟩ := hg
  apply hbad
  refine ⟨(xn, Xn), he, ?_⟩
  rw [he] at hg'
  exact batchGood_changeCost H cp hcp htsmall hg'

def Params.newtonBudget (P : Params E me) : ℕ :=
  (P.rounds * Sparsify.levelBudget (n := E.n) P.Kd P.J P.samples + 3 * E.n) +
    6 * E.n * (E.Brhs + E.k * E.Bmv + E.Brep)

/-- One numerical Newton query program with frozen public log weights. -/
def frozenStep (P : Params E me) (t : ℝ) (X x : Point E.n me) :
    RTree (Finset (Fin E.n)) ℕ (Point E.n me) P.newtonBudget :=
  ((newtonProgPub E P.rows (pairOf (normDPt P.κ P.m x X).pair)
    (normDPt P.κ P.m x X).explicit
    (normQPt t P.κ P.m P.c x X) P.Kd P.J P.samples P.rounds).map (addPt x)).cast
      (by unfold Params.newtonBudget; ring)

/-- The final centering loop is a real sequence of the certified numerical programs. -/
def frozenRun (P : Params E me) (t : ℝ) (X : Point E.n me) : (N : ℕ) →
    Point E.n me → RTree (Finset (Fin E.n)) ℕ (Point E.n me) (N * P.newtonBudget)
  | 0, x => RTree.pure (PMF.pure x)
  | N + 1, x => ((frozenStep P t X x).bind (frozenRun P t X N)).cast (by ring)

structure FrozenInvariant (G : DiGraph (Fin E.n)) (P : Params E me) (bc : Fin E.n → ℝ)
    (t : ℝ) (X : Point E.n me) (D W : ℝ) (x : Point E.n me) : Prop where
  feasible : vec G x ∈ Feasible (matrix G P.rows) bc (vec G P.κ) (vec G P.m)
  centrality : cent P.C (matrix G P.rows) (barS (vec G P.κ) (vec G P.m) (vec G x))
    (barDphi (vec G P.κ) (vec G P.m) (vec G x)) (vec G P.c) t
    (fun i => exp (vec G X i)) ≤ D
  window : ∀ i, |vec G X i - Real.log
    (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
      (matrix G P.rows) (vec G x) i)| ≤ W

theorem frozenStep_failure (H : Regime G P bc) {t D W : ℝ} {X x : Point E.n me}
    (ht : |t| ≤ 16 * E.n / E.ε) (hD : D ≤ 1 / 1000) (hW : W ≤ 1 / 20)
    (hη : E.η ≤ D / 64) (hx : FrozenInvariant G P bc t X D W x) :
    mass ((frozenStep P t X x).eval G.out)
      (fun y => ¬FrozenInvariant G P bc t X (D / 2) (W + 2 * D) y) ≤
      d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) := by
  have hA := det_ne_zero_of_idRows (matrix_idRows G P.rows)
  have hLM : Real.logb 2 (2 * rowCount G me) ≤ P.L - 1 :=
    (Real.logb_le_logb_of_le (by norm_num) (by have := H.rows_pos; positivity)
      (by linarith [H.M_le])).trans H.logM_le
  have hc₀ : 0 ≤ P.c₀ := by
    have hMb := H.rows_pos.trans_le H.M_le
    unfold Params.c₀
    positivity
  have hw : ∀ i, 0 < exp (vec G X i) := fun i => exp_pos _
  have hS := barS_pos H.κ_pos hx.feasible.2
  have hwin : ∀ i, |Real.log (exp (vec G X i)) - Real.log
      (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G x) i)| ≤ 1 / 20 := by
    intro i
    rw [Real.log_exp]
    exact (hx.window i).trans hW
  have hDcopy : normD (fun i => exp (vec G X i))
      (barS (vec G P.κ) (vec G P.m) (vec G x)) =
      vec G (weights (pairOf (normDPt P.κ P.m x X).pair) (normDPt P.κ P.m x X).explicit) := by
    rw [← vec_eq_weights, vec_normDPt]
  have hqcopy : normQ t (vec G P.c) (fun i => exp (vec G X i))
      (barDphi (vec G P.κ) (vec G P.m) (vec G x)) =
      vec G (normQPt t P.κ P.m P.c x X) := (vec_normQPt G t P.κ P.m P.c x X).symm
  have hp := newtonPot_gram (q := normQ t (vec G P.c) (fun i => exp (vec G X i))
    (barDphi (vec G P.κ) (vec G P.m) (vec G x))) hA hw hS
  have hnum := newtonProgPub_numeric G P.rows H.row_ne H.row_sq_le H.L_ge hLM H.κ_pos
    (le_refl _) H.c₀_le H.U_ge H.width_le hx.feasible H.reference_feasible H.M_le
    H.rank_ge H.ε_pos H.ε_le hw ht H.cost_le hwin (hx.centrality.trans hD)
    H.reference_slack (by rw [H.C_eq]; exact H.C_pos.le) H.η_pos hDcopy hqcopy hp
    (J := P.J) P.rounds H.Csym_nonneg H.sym_le H.vertices_le H.samples_pos
  have hcard : ((Sparsify.resid G (Sparsify.P0
      (E.wf (pairOf (normDPt P.κ P.m x X).pair)))).card : ℝ≥0∞) ≤
      (Fintype.card (Sym2 (Fin E.n)) : ℝ≥0∞) := by exact_mod_cast Finset.card_le_univ _
  have hnum' := hnum.trans (add_le_add le_rfl (mul_le_mul' hcard le_rfl))
  rw [newtonDir_eq_normD] at hnum'
  rw [frozenStep, RTree.eval_cast, RTree.eval_map, mass_map]
  refine (mass_mono _ (fun d hbad hgood => ?_)).trans hnum'
  obtain ⟨hAd, hed⟩ := hgood
  let h := newtonDir (matrix G P.rows) (fun i => exp (vec G X i))
    (barS (vec G P.κ) (vec G P.m) (vec G x))
    (normQ t (vec G P.c) (fun i => exp (vec G X i))
      (barDphi (vec G P.κ) (vec G P.m) (vec G x)))
  let e := vec G d - h
  have hAe : (matrix G P.rows)ᵀ *ᵥ e = 0 := by
    rw [show e = vec G d - h from rfl, mulVec_sub, hAd, (newtonDir_spec hA hw hS).1, sub_zero]
  have he : mixed P.C (fun i => exp (vec G X i))
      (fun i => barS (vec G P.κ) (vec G P.m) (vec G x) i * e i) ≤ E.η := by
    rw [← H.C_eq]
    exact hed
  obtain ⟨hy, hc, hm, _⟩ := center_step_inexact hA (H.row_ne)
    H.L_ge hLM H.κ_pos hc₀ H.c₀_le hx.feasible hw
    (fun i => (hwin i).trans (by norm_num)) hx.centrality hD hAe he hη
  have heq : vec G x + (h + e) = vec G (addPt x d) := by rw [vec_addPt]; dsimp [e]; abel
  change vec G x + (h + e) ∈ _ at hy
  change cent P.C _ (barS _ _ (vec G x + (h + e)))
    (barDphi _ _ (vec G x + (h + e))) _ t _ ≤ _ at hc
  change ∀ i, |Real.log (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
    (matrix G P.rows) (vec G x + (h + e)) i) -
    Real.log (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
      (matrix G P.rows) (vec G x) i)| ≤ 2 * D at hm
  rw [heq] at hy hc hm
  apply hbad
  refine ⟨hy, hc.trans ?_, fun i => ?_⟩
  · have hD0 : 0 ≤ D := (cent_nonneg H.C_pos.le t _).trans hx.centrality
    nlinarith [mul_le_mul_of_nonneg_left hD hD0]
  · have ht := abs_sub_le (vec G X i)
      (Real.log (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G x) i))
      (Real.log (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
        (matrix G P.rows) (vec G (addPt x d)) i))
    rw [abs_sub_comm (Real.log (gfun (vec G P.κ) (vec G P.m) (1 - 1 / P.L) P.c₀
      (matrix G P.rows) (vec G x) i))] at ht
    exact ht.trans (add_le_add (hx.window i) (hm i))

/-- The full frozen loop halves a public centrality cap at each step. The moving
log-weight window is proved by summing the geometric movement bounds. -/
theorem frozenRun_failure (H : Regime G P bc) {t D W : ℝ} {X x : Point E.n me}
    (ht : |t| ≤ 16 * E.n / E.ε) (hD : D ≤ 1 / 1000) (hW : W + 4 * D ≤ 1 / 20)
    (N : ℕ) (hη : E.η ≤ (1 / 2 : ℝ) ^ N * D / 64)
    (hx : FrozenInvariant G P bc t X D W x) :
    mass ((frozenRun P t X N x).eval G.out)
      (fun y => ¬FrozenInvariant G P bc t X ((1 / 2 : ℝ) ^ N * D) (W + 4 * D) y) ≤
      N * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) := by
  have hD0 : 0 ≤ D := (cent_nonneg H.C_pos.le t _).trans hx.centrality
  induction N generalizing D W x with
  | zero =>
      have hx' : FrozenInvariant G P bc t X D (W + 4 * D) x :=
        ⟨hx.feasible, hx.centrality, fun i => (hx.window i).trans (by linarith)⟩
      simp [frozenRun, hx']
  | succ N ih =>
      have hηstep : E.η ≤ D / 64 := hη.trans (div_le_div_of_nonneg_right
        (mul_le_of_le_one_left hD0 (pow_le_one₀ (by norm_num) (by norm_num))) (by norm_num))
      have hηtail : E.η ≤ (1 / 2 : ℝ) ^ N * (D / 2) / 64 := by
        calc E.η ≤ (1 / 2 : ℝ) ^ (N + 1) * D / 64 := hη
          _ = (1 / 2 : ℝ) ^ N * (D / 2) / 64 := by rw [pow_succ]; ring
      rw [frozenRun, RTree.eval_cast, RTree.eval_bind]
      refine (mass_bind_le_add _ _ _ _
        (ε := (N : ℝ≥0∞) * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds))
        (frozenStep_failure H ht hD (by linarith) hηstep hx) ?_).trans (le_of_eq ?_)
      · intro y hy
        have hi := ih (D := D / 2) (W := W + 2 * D) (x := y) (by linarith) (by linarith)
          hηtail (not_not.mp hy) (by positivity)
        have hcap : (1 / 2 : ℝ) ^ N * (D / 2) = (1 / 2 : ℝ) ^ (N + 1) * D := by
          rw [pow_succ]
          ring
        have hwindow : (W + 2 * D) + 4 * (D / 2) = W + 4 * D := by ring
        simpa only [hcap, hwindow] using hi
      · push_cast
        ring

theorem frozenRun_cost (read : Finset (Fin E.n) → ℕ) (P : Params E me) (t : ℝ)
    (X x : Point E.n me) (N : ℕ) {out : Point E.n me × ℕ}
    (ho : out ∈ (RTree.run read (frozenRun P t X N x)).support) :
    out.2 ≤ N * P.newtonBudget := RTree.cost_le _ _ ho

theorem Regime.final_constants (H : Regime G P bc) :
    P.Δ ≤ 1 / 1000 ∧ P.K + 4 * P.Δ ≤ 1 / 20 := by
  have ha0 : 0 ≤ 1 / (2 * P.L) := by have := H.L_ge; positivity
  have ha : 1 / (2 * P.L) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [H.L_ge])
  have hd : P.Δ ≤ 1 / 2 ^ 20 := by
    nlinarith [H.Δ_le, mul_le_mul ha ha ha0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hk : P.K ≤ 1 / 2 ^ 22 := by nlinarith [H.K_le]
  constructor <;> linarith

/-- The batch invariant starts final centering; no final-run invariant is a premise. -/
theorem frozenRun_failure_from_invariant (H : Regime G P bc) {t : ℝ} {st : State E.n me}
    (ht : |t| ≤ 16 * E.n / E.ε) (N : ℕ)
    (hη : E.η ≤ (1 / 2 : ℝ) ^ N * P.Δ / 64) (hs : Invariant G P bc t st) :
    mass ((frozenRun P t st.2 N st.1).eval G.out)
      (fun y => ¬FrozenInvariant G P bc t st.2 ((1 / 2 : ℝ) ^ N * P.Δ)
        (P.K + 4 * P.Δ) y) ≤
      N * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) :=
  frozenRun_failure H ht H.final_constants.1 H.final_constants.2 N hη
    ⟨hs.feasible, hs.centrality, logWindow_of_potential H (st := st) hs.potential⟩

/-- A numerical finite-run objective endpoint against every closed feasible comparator.
The final centrality bound is produced by `frozenRun`, not postulated. -/
theorem frozenRun_endpoint (H : Regime G P bc) {t : ℝ} {st : State E.n me}
    (ht0 : 0 < t) (ht : |t| ≤ 16 * E.n / E.ε) (N : ℕ)
    (hη : E.η ≤ (1 / 2 : ℝ) ^ N * P.Δ / 64) (hs : Invariant G P bc t st) :
    mass ((frozenRun P t st.2 N st.1).eval G.out)
      (fun y => ¬(vec G y ∈ Feasible (matrix G P.rows) bc (vec G P.κ) (vec G P.m) ∧
        ∀ v : Fin (rowCount G me) → ℝ, (matrix G P.rows)ᵀ *ᵥ v = bc →
          (∀ i, |theta (vec G P.κ) (vec G P.m) v i| ≤ π / 2) →
        vec G P.c ⬝ᵥ vec G y - vec G P.c ⬝ᵥ v ≤ 4 * E.n / t +
          (∑ i, |vec G P.c i|) * (4 * E.U * ((1 / 2 : ℝ) ^ N * P.Δ)))) ≤
      N * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) := by
  refine (mass_mono _ (fun y hbad hgood => ?_)).trans
    (frozenRun_failure_from_invariant H ht N hη hs)
  have hcap : (1 / 2 : ℝ) ^ N * P.Δ ≤ P.Δ :=
    mul_le_of_le_one_left H.Δ_pos.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hLM : Real.logb 2 (2 * rowCount G me) ≤ P.L - 1 :=
    (Real.logb_le_logb_of_le (by norm_num) (by have := H.rows_pos; positivity)
      (by linarith [H.M_le])).trans H.logM_le
  have hc₀ : 0 ≤ P.c₀ := by
    have hMb := H.rows_pos.trans_le H.M_le
    unfold Params.c₀
    positivity
  apply hbad
  refine ⟨hgood.feasible, fun v hv hbox => ?_⟩
  have hgap := objective_gap_from_centrality
    (det_ne_zero_of_idRows (matrix_idRows G P.rows)) (H.row_ne)
    H.L_ge hLM H.κ_pos hc₀ H.c₀_le (by linarith [H.U_ge]) H.width_le hgood.feasible
    (fun i => exp_pos (vec G st.2 i)) ht0
    (fun i => by rw [Real.log_exp]; exact (hgood.window i).trans H.final_constants.2)
    (hgood.centrality.trans (hcap.trans H.final_constants.1)) hv hbox
  refine hgap.trans (add_le_add ?_ ?_)
  · exact div_le_div_of_nonneg_right
      (weight_bounds_of_potential H (st := st) hs.potential).2.2 ht0.le
  · exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hgood.centrality (by linarith [H.U_ge]))
      (sum_nonneg fun i _ => abs_nonneg (vec G P.c i))

def Params.initialBudget (P : Params E me) : ℕ :=
  batchJL E P.a0 P.Δ * ((P.rounds * Sparsify.levelBudget (n := E.n) P.Kd P.J P.samples + 3 * E.n) + 0)

/-- Compute initial weights, define the artificial cost, and run `N` public batches. -/
def initializedRun (P : Params E me) (x : Point E.n me) (τ : ℕ → ℝ) (N : ℕ) :
    RTree (Finset (Fin E.n)) ℕ (Option (State E.n me × Point E.n me))
      (P.initialBudget + N * P.batchBudget) :=
  ((initialWeights P x).cast (r := P.initialBudget) rfl).bind fun out => match out with
    | none => RTree.pure (PMF.pure none)
    | some X => ((run {P with c := artificialCost P.κ P.m x X} τ N 0 (x, X)).map
        (fun out => out.map (fun st => (st, artificialCost P.κ P.m x X)))).cast (by rfl)

/-- A complete first-phase execution: initialization plus adaptive composition.
The only point hypotheses concern feasibility and initial slack, not centrality. -/
theorem initializedRun_failure (H : Regime G P bc) (x : Point E.n me)
    (hx : vec G x ∈ Feasible (matrix G P.rows) bc (vec G P.κ) (vec G P.m))
    (hs : ∀ i, E.sst ≤ slk (vec G P.κ) (vec G P.m) (vec G x) i)
    (hsU : ∀ i, 1 / E.U ≤ slk (vec G P.κ) (vec G P.m) (vec G x) i)
    {τ : ℕ → ℝ} (hτ : Schedule P τ) (hτ0 : τ 0 = 1) (N : ℕ) :
    mass ((initializedRun P x τ N).eval G.out)
      (fun out => ¬∃ st cp, out = some (st, cp) ∧ ‖vec G cp‖ ≤ 4 * E.U ∧
        Invariant G {P with c := cp} bc (τ N) st) ≤
      batchJL E P.a0 P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) +
        N * H.batchFailure := by
  erw [initializedRun, RTree.eval_bind, RTree.eval_cast]
  refine mass_bind_le_add _ _ _ _ (initialWeights_failure H x hx hs) ?_
  intro out hout
  obtain ⟨X, rfl, hX, _⟩ := not_not.mp hout
  let cp := artificialCost P.κ P.m x X
  have hc : ‖vec G cp‖ ≤ 4 * E.U := artificialCost_bound H (x := x) (X := X) hx hsU hX.potential
  let H' := H.withCost cp hc
  have hinit : Invariant G {P with c := cp} bc (τ 0) (x, X) := by rw [hτ0]; exact hX
  have hτ' : Schedule {P with c := cp} τ :=
    ⟨hτ.positive, hτ.bounded, hτ.move_T, hτ.move_Δ⟩
  have hrun := run_failure H' hτ' N 0 hinit
  simp only [Nat.zero_add] at hrun
  erw [RTree.eval_cast, RTree.eval_map, mass_map]
  refine (mass_mono _ (fun o hbad hgood => ?_)).trans hrun
  obtain ⟨st, rfl, hst⟩ := hgood
  exact hbad ⟨st, cp, rfl, hc, hst⟩

/-- An unconditional query cap for the initialized execution. -/
theorem initializedRun_cost (read : Finset (Fin E.n) → ℕ) (P : Params E me) (x : Point E.n me)
    (τ : ℕ → ℝ) (N : ℕ) {out : Option (State E.n me × Point E.n me) × ℕ}
    (ho : out ∈ (RTree.run read (initializedRun P x τ N)).support) :
    out.2 ≤ P.initialBudget + N * P.batchBudget := RTree.cost_le _ _ ho

/-- Initialization, the artificial path, one margin-producing switch batch, the true-cost
path, and final numerical centering, all as one public query program. -/
def pathSolver (P : Params E me) (x : Point E.n me) (τ : ℕ → ℝ) (Ndown : ℕ)
    (σ : ℕ → ℝ) (Nup Nfinal : ℕ) :
    RTree (Finset (Fin E.n)) ℕ (Option (Point E.n me))
      ((P.initialBudget + Ndown * P.batchBudget) +
        (P.batchBudget + (Nup * P.batchBudget + Nfinal * P.newtonBudget))) :=
  (initializedRun P x τ Ndown).bind fun out => match out with
    | none => RTree.pure (PMF.pure none)
    | some (st, cp) => ((batch {P with c := cp} (τ Ndown) st).cast
        (show {P with c := cp}.batchBudget = P.batchBudget from rfl)).bind fun out => match out with
      | none => RTree.pure (PMF.pure none)
      | some st' => (run P σ Nup 0 st').bind fun out => match out with
        | none => RTree.pure (PMF.pure none)
        | some stf => (frozenRun P (σ Nup) stf.2 Nfinal stf.1).map some

def Endpoint (G : DiGraph (Fin E.n)) (P : Params E me) (bc : Fin E.n → ℝ)
    (t : ℝ) (N : ℕ) (y : Point E.n me) : Prop :=
  vec G y ∈ Feasible (matrix G P.rows) bc (vec G P.κ) (vec G P.m) ∧
    ∀ v : Fin (rowCount G me) → ℝ, (matrix G P.rows)ᵀ *ᵥ v = bc →
      (∀ i, |theta (vec G P.κ) (vec G P.m) v i| ≤ π / 2) →
    vec G P.c ⬝ᵥ vec G y - vec G P.c ⬝ᵥ v ≤ 4 * E.n / t +
      (∑ i, |vec G P.c i|) * (4 * E.U * ((1 / 2 : ℝ) ^ N * P.Δ))

/-- End-to-end execution of the licensed implicit LP routine. Only the initial point's
feasibility and slack are inputs: initialization, both paths, cost switching, and final
centering establish all later invariants. Concrete terminal-LP instantiation is separate. -/
theorem pathSolver_failure (H : Regime G P bc) (x : Point E.n me)
    (hx : vec G x ∈ Feasible (matrix G P.rows) bc (vec G P.κ) (vec G P.m))
    (hs : ∀ i, E.sst ≤ slk (vec G P.κ) (vec G P.m) (vec G x) i)
    (hsU : ∀ i, 1 / E.U ≤ slk (vec G P.κ) (vec G P.m) (vec G x) i)
    {τ σ : ℕ → ℝ} (hτ : Schedule P τ) (hτ0 : τ 0 = 1) (hσ : Schedule P σ)
    (Ndown Nup Nfinal : ℕ) (hjoin : σ 0 = τ Ndown)
    (hswitch : |τ Ndown| * (P.T * (32 * E.Mbar * E.U ^ 2)) ≤
      1 / (2 * P.L) * P.Δ / 2)
    (hη : E.η ≤ (1 / 2 : ℝ) ^ Nfinal * P.Δ / 64)
    :
    mass ((pathSolver P x τ Ndown σ Nup Nfinal).eval G.out)
      (fun out => ¬∃ y, out = some y ∧ Endpoint G P bc (σ Nup) Nfinal y) ≤
      batchJL E P.a0 P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) +
        (Ndown + 1 + Nup : ℕ) * H.batchFailure +
        Nfinal * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) := by
  erw [pathSolver, RTree.eval_bind]
  refine (mass_bind_le_add _ _ _ _
    (ε := H.batchFailure + ((Nup : ℝ≥0∞) * H.batchFailure +
      Nfinal * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds)))
    (initializedRun_failure H x hx hs hsU hτ hτ0 Ndown) ?_).trans (le_of_eq ?_)
  · intro out hout
    obtain ⟨st, cp, rfl, hcp, hst⟩ := not_not.mp hout
    let H' := H.withCost cp hcp
    erw [RTree.eval_bind, RTree.eval_cast]
    refine mass_bind_le_add _ _ _ _
      (ε := (Nup : ℝ≥0∞) * H.batchFailure +
        Nfinal * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds))
      (batch_switch_failure H' P.c H.cost_le (hτ.bounded Ndown) hswitch hst) ?_
    intro out hout
    obtain ⟨st', rfl, hst'⟩ := not_not.mp hout
    have hinit : Invariant G P bc (σ 0) st' := by rw [hjoin]; exact hst'
    have hrun := run_failure H hσ Nup 0 hinit
    simp only [Nat.zero_add] at hrun
    rw [RTree.eval_bind]
    refine mass_bind_le_add _ _ _ _
      (ε := (Nfinal : ℝ≥0∞) * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds))
      hrun ?_
    intro out hout
    obtain ⟨stf, rfl, hstf⟩ := not_not.mp hout
    rw [RTree.eval_map, mass_map]
    refine (mass_mono _ (fun y hbad hgood => hbad ⟨y, rfl, hgood⟩)).trans
      (frozenRun_endpoint H (hσ.positive Nup) (hσ.bounded Nup) Nfinal hη hstf)
  · push_cast
    ring

theorem pathSolver_cost (read : Finset (Fin E.n) → ℕ) (P : Params E me) (x : Point E.n me)
    (τ σ : ℕ → ℝ) (Ndown Nup Nfinal : ℕ) {out : Option (Point E.n me) × ℕ}
    (ho : out ∈ (RTree.run read (pathSolver P x τ Ndown σ Nup Nfinal)).support) :
    out.2 ≤ (P.initialBudget + Ndown * P.batchBudget) +
      (P.batchBudget + (Nup * P.batchBudget + Nfinal * P.newtonBudget)) := RTree.cost_le _ _ ho

def Params.solverBudget (P : Params E me) (Ndown Nup Nfinal : ℕ) : ℕ :=
  (P.initialBudget + Ndown * P.batchBudget) +
    (P.batchBudget + (Nup * P.batchBudget + Nfinal * P.newtonBudget))

def Regime.solverFailure (H : Regime G P bc) (Ndown Nup Nfinal : ℕ) : ℝ≥0∞ :=
  batchJL E P.a0 P.Δ * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) +
    (Ndown + 1 + Nup : ℕ) * H.batchFailure +
    Nfinal * d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds)

def solverSpectralCap (P : Params E me) (Ndown Nup Nfinal : ℕ) : ℕ :=
  batchJL E P.a0 P.Δ + (Ndown + 1 + Nup) * (1 + batchJL E P.a0 P.Δ) + Nfinal

theorem solverFailure_of_per_call (H : Regime G P bc) (Ndown Nup Nfinal : ℕ) {δ : ℝ≥0∞}
    (hsolve : d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (solveDelta P.rounds) ≤ δ)
    (hlev : d4Fail E.n H.Csym P.Kd P.J P.samples P.rounds (levDelta P.Δ P.rounds) ≤ δ) :
    H.solverFailure Ndown Nup Nfinal ≤ solverSpectralCap P Ndown Nup Nfinal * δ := by
  unfold Regime.solverFailure Regime.batchFailure
  calc _ ≤ batchJL E P.a0 P.Δ * δ + (Ndown + 1 + Nup : ℕ) *
        (δ + batchJL E P.a0 P.Δ * δ) + Nfinal * δ :=
      add_le_add (add_le_add (mul_le_mul' le_rfl hlev)
        (mul_le_mul' le_rfl (add_le_add hsolve (mul_le_mul' le_rfl hlev))))
        (mul_le_mul' le_rfl hsolve)
    _ = solverSpectralCap P Ndown Nup Nfinal * δ := by
      unfold solverSpectralCap
      push_cast
      ring


#print axioms artificialCost_bound
#print axioms batchGood_changeCost
#print axioms frozenRun_failure
#print axioms frozenRun_endpoint
#print axioms initializedRun_failure
#print axioms pathSolver_failure
#print axioms pathSolver_cost
#print axioms solverFailure_of_per_call

end
end CutQueryComplexity.ImplicitLP.GenericQuery
