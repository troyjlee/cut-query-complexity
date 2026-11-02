import CutQueryComplexity.ImplicitLP.GenericQuery.Numeric

/-! # Public frozen Newton calls for arbitrary explicit rows

The actual query program clips hidden coefficients on every transcript, derives
its required grids and bit caps from a successful state's analytic envelope,
and repairs the public identity block exactly. Explicit arithmetic is free.
-/

set_option autoImplicit false

namespace CutQueryComplexity.ImplicitLP.GenericQuery
open Matrix Finset Spectral
open scoped ENNReal
noncomputable section
variable {n me : ℕ}

/-- Hidden targets are clipped and quantized; explicit coordinates remain exact. -/
def freezeQ (p : ℕ) (Q : ℝ) (qt : Point n me) : Point n me :=
  Point.mk (fun u v => truncDyadic p (clipTo (-Q) Q (qt.pair u v))) qt.explicit

theorem freezeQ_grid (p : ℕ) (Q : ℝ) (qt : Point n me) :
    ∀ u v, ∃ m : ℤ, (freezeQ p Q qt).pair u v = m * (2 : ℝ) ^ (-(p : ℤ)) := fun u v => by
  obtain ⟨m, hm⟩ := (truncDyadic_props p (clipTo (-Q) Q (qt.pair u v))).2.2.2
  exact ⟨m, by simp only [freezeQ, Point.pair_mk]; rw [hm, _root_.zpow_neg, zpow_natCast, div_eq_mul_inv]⟩

theorem abs_freezeQ {p : ℕ} {Q : ℝ} (hQ : 0 ≤ Q) (qt : Point n me) (u v) :
    |(freezeQ p Q qt).pair u v| ≤ Q := by
  have h1 := (truncDyadic_props p (clipTo (-Q) Q (qt.pair u v))).1
  have h2 : |clipTo (-Q) Q (qt.pair u v)| ≤ Q :=
    abs_le.mpr ⟨le_clipTo _ _ _, clipTo_le (by linarith) _⟩
  exact h1.trans h2

variable (G : DiGraph (Fin n))

/-- Every interpreted weight is either a public pair value or an explicit value. -/
theorem weights_cases (w w' : Sym2 (Fin n) → ℝ) (de : Fin me → ℝ)
    (i : Fin (rowCount G me)) :
    (∃ e, hidden G me i = some e ∧ vec G (weights w de) i = w e ∧
      vec G (weights w' de) i = w' e) ∨
      vec G (weights w de) i = vec G (weights w' de) i := by
  simp only [vec, hidden]
  generalize (rowEquiv G me).symm i = x
  rcases x with ⟨p, k⟩ | j
  · exact Or.inl ⟨_, rfl, rfl, rfl⟩
  · exact Or.inr rfl

/-- Equal explicit components leave only the hidden pair case. -/
theorem vec_cases (pt pt' : Point n me) (he : pt.explicit = pt'.explicit)
    (i : Fin (rowCount G me)) :
    (∃ u v, vec G pt i = pt.pair u v ∧ vec G pt' i = pt'.pair u v) ∨
      vec G pt i = vec G pt' i := by
  simp only [vec]
  generalize (rowEquiv G me).symm i = x
  rcases x with ⟨p, k⟩ | j
  · exact Or.inl ⟨_, _, rfl, rfl⟩
  · exact Or.inr (congrFun he j)

theorem freezeW_rel {p : ℕ} {lo hi β : ℝ} (hβ0 : 0 ≤ β) (he : (1 / 2 : ℝ) ^ p ≤ β * lo)
    (Dw : Sym2 (Fin n) → ℝ) (de : Fin me → ℝ)
    (hlo : ∀ i, lo ≤ vec G (weights Dw de) i) (hhi : ∀ i, vec G (weights Dw de) i ≤ hi) (i : Fin (rowCount G me)) :
    0 ≤ vec G (weights (freezeW p lo hi Dw) de) i - vec G (weights Dw de) i ∧
      |vec G (weights (freezeW p lo hi Dw) de) i - vec G (weights Dw de) i| ≤
        β * vec G (weights Dw de) i := by
  have hD0 : 0 ≤ β * vec G (weights Dw de) i := by
    have : 0 ≤ β * lo := ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p)).trans he
    nlinarith [hlo i]
  rcases weights_cases G (freezeW p lo hi Dw) Dw de i with ⟨s, -, h1, h2⟩ | h
  · rw [h1, h2]
    have hl := hlo i; have hh := hhi i
    rw [h2] at hl hh
    unfold freezeW
    rw [clipTo_of_mem hl hh]
    refine ⟨sub_nonneg.mpr (le_dyadicUp _ _), ?_⟩
    rw [abs_sub_comm]
    refine (abs_dyadicUp_sub_le p _).trans (he.trans ?_)
    exact mul_le_mul_of_nonneg_left hl hβ0
  · rw [h, sub_self, abs_zero]; exact ⟨le_rfl, hD0⟩

/-- **Absolute error of the frozen `q̂`.** If the target interpreted from `qt` has `|q| ≤ Q` on the rows
and `2^{−p} ≤ β`, then the frozen target has absolute error `≤ β` on every row. -/
theorem freezeQ_abs {p : ℕ} {Q β : ℝ} (he : (1 / 2 : ℝ) ^ p ≤ β)
    (qt : Point n me) (hQ : ∀ i, |vec G qt i| ≤ Q) (i : Fin (rowCount G me)) :
    |vec G (freezeQ p Q qt) i - vec G qt i| ≤ β := by
  rcases vec_cases G (freezeQ p Q qt) qt rfl i with ⟨u, v, h1, h2⟩ | h
  · rw [h1, h2]
    have hq := hQ i
    rw [h2] at hq
    simp only [freezeQ, Point.pair_mk]
    rw [clipTo_of_mem (neg_le_of_abs_le hq) (le_of_abs_le hq), abs_sub_comm]
    exact (truncDyadic_props p _).2.2.1.trans he
  · rw [h, sub_self, abs_zero]; exact ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p)).trans he


def newtonProg (ER : ExplicitRows n me) (wf : Sym2 (Fin n) → ℝ) (de : Fin me → ℝ)
    (qp : Point n me) (K J t' R : ℕ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ) :
    RTree (Finset (Fin n)) ℕ (Point n me)
      ((R * Sparsify.levelBudget (n := n) K J t' + 3 * n) +
        (6 * Brhs * n + (k * (6 * Bmv * n) + 6 * Brep * n))) :=
  (Sparsify.sparsify wf K J t' R).bind fun o => match o with
  | none => RTree.pure (PMF.pure 0)
  | some out => RTree.ofDeterministic (newtonStepProg ER wf de qp out ew eq p Brhs Bmv Brep k)

/-- **Budget:** every execution uses at most `q_D4 + 6n(B_rhs + k·B_mv + B_rep)` queries,
`q_D4 = R · levelBudget + 3n`. -/
theorem newtonProg_cost (ER : ExplicitRows n me) (wf : Sym2 (Fin n) → ℝ) (de : Fin me → ℝ)
    (qp : Point n me) (K J t' R : ℕ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ) (read : Finset (Fin n) → ℕ)
    {o : Point n me × ℕ}
    (ho : o ∈ (RTree.run read (newtonProg ER wf de qp K J t' R ew eq p Brhs Bmv Brep k)).support) :
    o.2 ≤ (R * Sparsify.levelBudget (n := n) K J t' + 3 * n) + 6 * n * (Brhs + k * Bmv + Brep) :=
  (RTree.cost_le _ _ ho).trans (le_of_eq (by ring))

open Probability in
/-- **Failure probability of D4 + Newton step.** Any property `Q` that the Newton step's
output has whenever D4's output is `Good` fails with probability at most `sparsify_fail_le`'s
bound. -/
theorem newtonProg_fail_le (ER : ExplicitRows n me) {wf : Sym2 (Fin n) → ℝ} (de : Fin me → ℝ)
    (qp : Point n me) {K : ℕ} (J : ℕ) {t' : ℕ} (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ e, (Spanner.symS G e : ℝ) ≤ C)
    (hw0 : ∀ e, 0 ≤ wf e) (hK : n ≤ 2 ^ K) (ht : 0 < t') {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (Q : Point n me → Prop)
    (hQ : ∀ out, Sparsify.Good G wf K t' δ R out →
      Q ((newtonStepProg ER wf de qp out ew eq p Brhs Bmv Brep k).eval G.out)) :
    mass ((newtonProg ER wf de qp K J t' R ew eq p Brhs Bmv Brep k).eval G.out)
        (fun d => ¬ Q d) ≤
      R * (t' * (2⁻¹ : ℝ≥0∞) ^ J +
        ENNReal.ofReal (2 * n * Real.exp (-(δ ^ 2) / (8 * (C * (2 * K + 1 : ℕ) / t'))))) +
      (Sparsify.resid G (Sparsify.P0 wf)).card * (4⁻¹ : ℝ≥0∞) ^ R := by
  unfold newtonProg
  rw [RTree.eval_bind]
  refine (mass_bind_le_add _ _ (fun o => ¬ ∃ out, o = some out ∧ Sparsify.Good G wf K t' δ R out)
    _ (ε := 0) (Sparsify.sparsify_fail_le hC0 hC hw0 hK ht hδ hδ1 R) ?_).trans (by rw [add_zero])
  intro o ho
  push Not at ho
  obtain ⟨out, rfl, hg⟩ := ho
  simp [RTree.eval_ofDeterministic, hQ out hg]


def qp (E : NewtonPub) (qt : Point E.n me) : Point E.n me :=
  freezeQ E.pq E.Q qt

/-- Fully public deterministic Newton call. -/
def newtonStepPub (E : NewtonPub) (ER : ExplicitRows E.n me)
    (Dw : Sym2 (Fin E.n) → ℝ) (de : Fin me → ℝ) (qt : Point E.n me)
    (out : Sym2 (Fin E.n) → ℝ) :=
  newtonStepProg ER (E.wf Dw) de (qp E qt) out E.ew E.eq E.p E.Brhs E.Bmv E.Brep E.k

theorem newtonStepPub_cost (E : NewtonPub) (ER : ExplicitRows E.n me)
    (Dw : Sym2 (Fin E.n) → ℝ) (de : Fin me → ℝ) (qt : Point E.n me)
    (out : Sym2 (Fin E.n) → ℝ) (read : Finset (Fin E.n) → ℕ) :
    (newtonStepPub E ER Dw de qt out).cost read ≤
      6 * E.n * (E.Brhs + E.k * E.Bmv + E.Brep) :=
  newtonStepProg_cost ER (E.wf Dw) de (qp E qt) out E.ew E.eq E.p E.Brhs E.Bmv E.Brep E.k read

/-- A public sparsifier followed by the actual frozen-and-repaired Newton program. -/
def newtonProgPub (E : NewtonPub) (ER : ExplicitRows E.n me)
    (Dw : Sym2 (Fin E.n) → ℝ) (de : Fin me → ℝ) (qt : Point E.n me) (K J t' R : ℕ) :=
  newtonProg ER (E.wf Dw) de (qp E qt) K J t' R E.ew E.eq E.p E.Brhs E.Bmv E.Brep E.k

theorem newtonProgPub_cost (E : NewtonPub) (ER : ExplicitRows E.n me)
    (Dw : Sym2 (Fin E.n) → ℝ) (de : Fin me → ℝ) (qt : Point E.n me) (K J t' R : ℕ)
    (read : Finset (Fin E.n) → ℕ) {o : Point E.n me × ℕ}
    (ho : o ∈ (RTree.run read (newtonProgPub E ER Dw de qt K J t' R)).support) :
    o.2 ≤ (R * Sparsify.levelBudget (n := E.n) K J t' + 3 * E.n) +
      6 * E.n * (E.Brhs + E.k * E.Bmv + E.Brep) :=
  newtonProg_cost ER (E.wf Dw) de (qp E qt) K J t' R E.ew E.eq E.p E.Brhs E.Bmv E.Brep E.k read ho

variable {E : NewtonPub} (G : DiGraph (Fin E.n))

open Spectral in
set_option maxHeartbeats 6400000 in
/-- All grid, refinement and aggregate-bit obligations follow from the analytic
state envelope and fixed public scalar choices. -/
theorem newtonStep_public (ER : ExplicitRows E.n me)
    (hrowne : ∀ i, matrix G ER i ≠ 0) (hrowA : ∀ i, ∑ j, matrix G ER i j ^ 2 ≤ 2) {bc : Fin E.n → ℝ}
    {κ m w c : Fin (rowCount G me) → ℝ} {t : ℝ}
    {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * rowCount G me) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀lo : 1 / (2 * E.Mbar) ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * rowCount G me)) (hU1 : 1 ≤ E.U) (hU : ∀ i, Real.pi / κ i ≤ E.U)
    {x x₀ : Fin (rowCount G me) → ℝ}
    (hx : x ∈ Feasible (matrix G ER) bc κ m) (hx₀ : x₀ ∈ Feasible (matrix G ER) bc κ m)
    (hMbar : (rowCount G me : ℝ) ≤ E.Mbar) (hr : (1 : ℝ) ≤ E.n) (hε : 0 < E.ε) (hε1 : E.ε ≤ 1)
    (hw : ∀ i, 0 < w i) (ht : |t| ≤ 16 * E.n / E.ε) (hc : ‖c‖ ≤ 4 * E.U)
    (hwin : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (matrix G ER) x i)| ≤ 1 / 20)
    (hδc : cent (48 * (2 * L₀)) (matrix G ER) (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs0 : ∀ i, 1 / E.U ≤ slk κ m x₀ i) (hC : 0 ≤ E.C) (hη : 0 < E.η)
    -- copy-constant targets (D8's state invariant)
    {Dw : Sym2 (Fin E.n) → ℝ} {de : Fin me → ℝ}
    (hDcopy : normD w (barS κ m x) = vec G (weights Dw de))
    {qt : Point E.n me} (hqcopy : normQ t c w (barDphi κ m x) = vec G qt)
    -- the exact Newton solution
    {p0 : Fin E.n → ℝ}
    (hp : gram (matrix G ER) (normD w (barS κ m x)) *ᵥ p0 =
      (matrix G ER)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    -- one successful spectral call
    {K t' R : ℕ} {out : Sym2 (Fin E.n) → ℝ}
    (hgood : Sparsify.Good G (E.wf Dw) K t' (solveDelta R) R out) :
    let A := matrix G ER
    let h : Fin (rowCount G me) → ℝ := fun i =>
      -normD w (barS κ m x) i * (normQ t c w (barDphi κ m x) i - (A *ᵥ p0) i)
    let d := (newtonStepPub E ER Dw de qt out).eval G.out
    Aᵀ *ᵥ vec G d = 0 ∧ mixed E.C w (fun i => barS κ m x i * (vec G d - h) i) ≤ E.η := by
  intro A h d
  -- invariants → weight and slack windows
  have hA := det_ne_zero_of_idRows (matrix_idRows G ER)
  have hwin5 : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (matrix G ER) x i)| ≤ 1 / 5 :=
    fun i => (hwin i).trans (by norm_num)
  obtain ⟨hwlo, hwhi, hwsum⟩ := weight_invariants hA hrowne hL hc₀lo hcM hMbar hr hw hwin5
  have hM1 : (1 : ℝ) ≤ rowCount G me := by
    have hr0 : 0 < E.n := by exact_mod_cast (show (0 : ℝ) < E.n by linarith)
    exact_mod_cast Fin.pos (iota G ER ⟨0, hr0⟩)
  have hr0 : 0 < E.n := by exact_mod_cast (show (0 : ℝ) < E.n by linarith)
  have hMb : 0 < E.Mbar := by linarith
  have hc₀ : 0 ≤ c₀ := (by positivity : (0 : ℝ) ≤ 1 / (2 * E.Mbar)).trans hc₀lo
  have hs : ∀ i, E.sst ≤ slk κ m x i := fun i =>
    slack_floor_note hA hrowne hL hLM hκ hc₀ hcM hU1 hU hx hx₀ hMbar hr hε hε1 hwlo hwsum ht
      hc hwin hδc hs0 i
  have hU0 : 0 < E.U := by linarith
  have hsst0 : 0 < E.sst := by unfold NewtonPub.sst; positivity
  have hℓ : 0 < E.ell := by unfold NewtonPub.ell; positivity
  have hdp0 : 0 < E.dp := by unfold NewtonPub.dp; positivity
  have hQ0 : 0 ≤ E.Q := by unfold NewtonPub.Q; positivity
  -- envelope bounds on the rows
  have hwpos : ∀ i, 0 < w i := hw
  have hS := fun i => barrier_env hκ hx.2 hU1 hU i
  have hDlo : ∀ i, E.ell ≤ normD w (barS κ m x) i := fun i => by
    have := normD_ge hwpos hwhi (barS_pos hκ hx.2) (fun i => (hS i).2.1) hsst0 hs i
    unfold NewtonPub.ell; convert this using 2; norm_num
  have hDhi : ∀ i, normD w (barS κ m x) i ≤ E.dp := fun i => by
    have := normD_le (by positivity : (0 : ℝ) < 1 / (4 * E.Mbar)) hwlo hU0 (fun i => (hS i).1) i
    unfold NewtonPub.dp; convert this using 1; field_simp
  have hqb : ∀ i, |normQ t c w (barDphi κ m x) i| ≤ E.Q := fun i => by
    have h1 := normQ_le (t := t) (c := c) hwpos hwhi (fun i => (hS i).2.2) hsst0 hs i
    have h2 : |t| * ‖c‖ ≤ 16 * E.n / E.ε * (4 * E.U) :=
      mul_le_mul ht hc (norm_nonneg _) (by positivity)
    unfold NewtonPub.Q
    calc _ ≤ _ := h1
      _ ≤ 16 * E.n / E.ε * (4 * E.U) + 4 / E.sst := by linarith
      _ = _ := by ring
  have hβ0 : 0 < E.β := NewtonPub.β_pos hη
  have hβ4 := NewtonPub.β_le (E := E)
  have hew := NewtonPub.half_pow_pD_le hη hℓ
  have hℓdp : E.ell ≤ E.dp := (hDlo (iota G ER ⟨0, hr0⟩)).trans (hDhi _)
  -- grid freezing
  have hDlo' : ∀ i, E.ell ≤ vec G (weights Dw de) i := fun i => hDcopy ▸ hDlo i
  have hDhi' : ∀ i, vec G (weights Dw de) i ≤ E.dp := fun i => hDcopy ▸ hDhi i
  have hDh : ∀ i, |vec G (weights (E.wf Dw) de) i - normD w (barS κ m x) i| ≤
      E.β * normD w (barS κ m x) i := fun i => by
    rw [hDcopy]; exact (freezeW_rel G hβ0.le hew Dw de hDlo' hDhi' i).2
  have hqh : ∀ i, |vec G (qp E qt) i - normQ t c w (barDphi κ m x) i| ≤ E.β := fun i => by
    rw [hqcopy]
    exact freezeQ_abs G (NewtonPub.half_pow_pq_le hη) qt (fun i => hqcopy ▸ hqb i) i
  have hdpv : ∀ j, E.ell ≤ de (ER.iota j) := fun j => by
    have := hDlo' (iota G ER j); simpa [vec, iota, weights, rowIndex, Point.mk, Point.explicit] using this
  have hwf0 : ∀ e, 0 ≤ E.wf Dw e := fun e => hℓ.le.trans (le_freezeW _ _ _ Dw e)
  have hW : ∀ e, |E.wf Dw e| ≤ E.W := fun e => by
    refine (abs_freezeW hℓ.le hℓdp Dw e).trans ?_
    unfold NewtonPub.W
    nlinarith [hew, hℓdp]
  have hQz : ∀ u v, |(qp E qt).pair u v| ≤ E.Qz := fun u v => abs_freezeQ hQ0 qt u v
  -- envelope at the public row bound
  have hX : 4 * Real.sqrt (2 * rowCount G me) * Real.sqrt (rowCount G me) * E.dp *
      (64 * E.n * E.U / E.ε + 4 / E.sst + 1) / (E.sst ^ 2 / 16) ≤ E.X := by
    show _ ≤ 4 * Real.sqrt (2 * E.Mbar) * Real.sqrt E.Mbar * E.dp * (E.Q + 1) / E.ell
    unfold NewtonPub.Q NewtonPub.ell
    gcongr
  have hΛ : 3 / 2 * E.dp * (2 * rowCount G me) ≤ E.Λ := by unfold NewtonPub.Λ; gcongr
  obtain ⟨hδ0, -, hδlo, hδhi⟩ := solveDelta_spec R
  obtain ⟨-, -, H3, H4⟩ := newtonStep_numeric_inv G ER hrowne hrowA hL hLM hκ hc₀lo hcM hU1 hU hx
    hx₀ hMbar hr hε hε1 hw ht hc hwin hδc hs0 (sst := E.sst) (dp := E.dp) rfl rfl hC hDh hqh
    hβ0.le (by linarith) hp hℓ hdpv hwf0 hgood (by norm_num) le_rfl hδlo hδhi hX hΛ hW hQz
    (NewtonPub.ew_grid (E := E) Dw) (freezeQ_grid _ _ _) E.p E.Brhs E.Bmv E.Brep
    NewtonPub.eq_le NewtonPub.hBmv NewtonPub.hBrhs NewtonPub.hBrep (NewtonPub.hτβ hη) E.k
    (NewtonPub.hk hη)
  refine ⟨H3, H4.trans ?_⟩
  have hmono := NewtonPub.P_mono hC hsst0 hdp0.le hQ0 hℓ (by linarith) hMbar
  have hpub := NewtonPub.P_nonneg hC hsst0 hdp0.le hQ0 hℓ (hMb.le)
  calc E.P (rowCount G me) * E.β ≤ E.Ppub * E.β := mul_le_mul_of_nonneg_right hmono hβ0.le
    _ ≤ E.η := NewtonPub.Ppub_mul_β_le hη hpub


open Probability Spectral in
set_option maxHeartbeats 6400000 in
/-- **`lem:numeric` for D4 + the public Newton step, with probability.** Under the invariants
and the copy-constant frozen targets, outside the failure mass of one D4 call at
`δ = solveDelta R` (`ε_solve = 1/8`), the output `d` has `Aᵀd = 0` and mixed error `≤ η`. -/
theorem newtonProgPub_numeric (ER : ExplicitRows E.n me)
    (hrowne : ∀ i, matrix G ER i ≠ 0) (hrowA : ∀ i, ∑ j, matrix G ER i j ^ 2 ≤ 2) {bc : Fin E.n → ℝ}
    {κ m w c : Fin (rowCount G me) → ℝ} {t : ℝ}
    {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * rowCount G me) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) {c₀ : ℝ} (hc₀lo : 1 / (2 * E.Mbar) ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * rowCount G me)) (hU1 : 1 ≤ E.U) (hU : ∀ i, Real.pi / κ i ≤ E.U)
    {x x₀ : Fin (rowCount G me) → ℝ}
    (hx : x ∈ Feasible (matrix G ER) bc κ m) (hx₀ : x₀ ∈ Feasible (matrix G ER) bc κ m)
    (hMbar : (rowCount G me : ℝ) ≤ E.Mbar) (hr : (1 : ℝ) ≤ E.n) (hε : 0 < E.ε) (hε1 : E.ε ≤ 1)
    (hw : ∀ i, 0 < w i) (ht : |t| ≤ 16 * E.n / E.ε) (hc : ‖c‖ ≤ 4 * E.U)
    (hwin : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (matrix G ER) x i)| ≤ 1 / 20)
    (hδc : cent (48 * (2 * L₀)) (matrix G ER) (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs0 : ∀ i, 1 / E.U ≤ slk κ m x₀ i) (hC : 0 ≤ E.C) (hη : 0 < E.η)
    {Dw : Sym2 (Fin E.n) → ℝ} {de : Fin me → ℝ}
    (hDcopy : normD w (barS κ m x) = vec G (weights Dw de))
    {qt : Point E.n me} (hqcopy : normQ t c w (barDphi κ m x) = vec G qt)
    {p0 : Fin E.n → ℝ}
    (hp : gram (matrix G ER) (normD w (barS κ m x)) *ᵥ p0 =
      (matrix G ER)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {K J t' : ℕ} (R : ℕ) {Cs : ℝ} (hCs0 : 0 ≤ Cs) (hCs : ∀ e, (Spanner.symS G e : ℝ) ≤ Cs)
    (hK : E.n ≤ 2 ^ K) (ht' : 0 < t') :
    let A := matrix G ER
    let h : Fin (rowCount G me) → ℝ := fun i =>
      -normD w (barS κ m x) i * (normQ t c w (barDphi κ m x) i - (A *ᵥ p0) i)
    mass ((newtonProgPub E ER Dw de qt K J t' R).eval G.out)
        (fun d => ¬ (Aᵀ *ᵥ vec G d = 0 ∧
          mixed E.C w (fun i => barS κ m x i * (vec G d - h) i) ≤ E.η)) ≤
      R * (t' * (2⁻¹ : ℝ≥0∞) ^ J + ENNReal.ofReal (2 * E.n *
          Real.exp (-(solveDelta R ^ 2) / (8 * (Cs * (2 * K + 1 : ℕ) / t'))))) +
        (Sparsify.resid G (Sparsify.P0 (E.wf Dw))).card * (4⁻¹ : ℝ≥0∞) ^ R := by
  intro A h
  obtain ⟨hδ0, hδ1, -, -⟩ := solveDelta_spec R
  have hwf0 : ∀ e, 0 ≤ E.wf Dw e := fun e => by
    have hU0 : 0 < E.U := by linarith
    have hr0 : 0 < E.n := by exact_mod_cast (show (0 : ℝ) < E.n by linarith)
    have hM1 : (1 : ℝ) ≤ rowCount G me := by exact_mod_cast Fin.pos (iota G ER ⟨0, hr0⟩)
    have hMb : 0 < E.Mbar := by linarith
    have : 0 < E.ell := by
      unfold NewtonPub.ell NewtonPub.sst; positivity
    exact this.le.trans (le_freezeW _ _ _ Dw e)
  exact newtonProg_fail_le G ER de (qp E qt) J E.ew E.eq E.p E.Brhs E.Bmv E.Brep E.k
    hCs0 hCs hwf0 hK ht' hδ0 hδ1 R _ fun out hgood =>
      newtonStep_public G ER hrowne hrowA hL hLM hκ hc₀lo hcM hU1 hU hx hx₀ hMbar hr hε hε1 hw ht hc
        hwin hδc hs0 hC hη hDcopy hqcopy hp hgood


#print axioms freezeW_rel
#print axioms freezeQ_abs
#print axioms newtonProg_cost
#print axioms newtonProg_fail_le
#print axioms newtonStep_public
#print axioms newtonProgPub_numeric

end
end CutQueryComplexity.ImplicitLP.GenericQuery
