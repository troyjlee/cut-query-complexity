import CutQueryComplexity.ImplicitLP.NumericLP
import CutQueryComplexity.ImplicitLP.NewtonQuery
import CutQueryComplexity.Model.RandomizedReduction

/-! # One complete Newton-step query program (D7)

* `explicitGram_lp`: the explicit part of the LP's frozen Gram matrix is the public matrix
  `E = d_q χχᵀ + diag(d₊ + d₋)` (`lpE`), so `P = lap out + E` needs no row enumeration.
* Copy-constant vectors are public points (`LPPoint`): `D̂ ⊙ q̂` (`lpMulPt`), `A y` (`lpAPt`),
  `h̃ = −D̂(q̂ − A y)` (`lpHPt`), the repaired direction (`lpRepPt`). Each equals its row
  vector by construction (`lpD_mul_lpVec`, `lpA_mulVec`, `lpHPt_spec`, `lpRepPt_spec`).
* `transposeProg`: `Aᵀ(lpVec pt)` exactly on a grid, one `allRowsUniv` via `hiddenDiv_exact`
  (`transposeProg_eval`).
* `newtonStepProg`: RHS query, `k` frozen-solve steps, repair-residual query; cost
  `6n(B_rhs + k·B_mv + B_rep)` (`newtonStepProg_cost`); output = repaired direction
  (`newtonStepProg_eval`); with `lem_numeric_lp`/`lem_numeric_lp_inv`
  (`newtonStep_numeric_lp`, `newtonStep_numeric_lp_inv`); public repair bit check via
  `query_xk_bound`.
* `newtonProg`: D4 (`sparsify`) then the Newton step; budget `q_D4 + 6n(…)`
  (`newtonProg_cost`); failure probability that of `sparsify_fail_le` (`newtonProg_fail_le`,
  `newtonProg_numeric_lp`).
-/

namespace CutQueryComplexity
namespace ImplicitLP

open Matrix Finset Spectral

noncomputable section

variable {n : ℕ} (G : DiGraph (Fin n))

/-! ## The explicit part of the frozen Gram matrix -/

/-- The explicit part `E = d_q χχᵀ + diag(d₊ + d₋)`, a public matrix. -/
def lpE (s t : Fin n) (dq : ℝ) (dp dm : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  dq • vecMulVec (DirectedMincut.chi s t) (DirectedMincut.chi s t) + diagonal (dp + dm)

theorem explicitGram_lp (s t : Fin n) (w : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ) :
    explicitGram (lpA G s t) (lpD G w dq dp dm) (lpHidF G) = lpE s t dq dp dm := by
  rw [explicitGram, sum_filter, ← (lpEquiv G).sum_comp]
  simp only [lpHidF, lpA, lpD, Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [lpHid, reduceCtorEq, ite_false, sum_const_zero, zero_add, ite_true, lpWeight,
    lpRowVec, Fintype.univ_punit, sum_singleton]
  ext j k
  simp [lpE, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply, Pi.single_apply,
    diagonal_apply]
  by_cases h : j = k
  · subst h; simp
  · simp [h]

/-! ## Public points: copy-constant row vectors -/

open DirectedMincut (LPPoint chi)

/-- `D̂ ⊙ y` for a copy-constant `y = lpVec pt`, as a public point. -/
def lpMulPt (wf : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ) (pt : LPPoint (Fin n)) :
    LPPoint (Fin n) :=
  ⟨fun u v => wf s(u, v) * pt.z u v, dq * pt.q, fun j => dp j * pt.yp j, fun j => dm j * pt.ym j⟩

theorem lpD_mul_lpVec (wf : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ)
    (pt : LPPoint (Fin n)) :
    (fun i => lpD G wf dq dp dm i * lpVec G pt i) = lpVec G (lpMulPt wf dq dp dm pt) := by
  funext i
  simp only [lpD, lpVec]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j)) <;> rfl

/-- `A y` as a public point: `y_u − y_v` on the copies of `u < v`, `y_s − y_t`, `y`, `−y`. -/
def lpAPt (s t : Fin n) (y : Fin n → ℝ) : LPPoint (Fin n) :=
  ⟨fun u v => y u - y v, y s - y t, y, fun j => -y j⟩

theorem chi_dot (s t : Fin n) (y : Fin n → ℝ) : chi s t ⬝ᵥ y = y s - y t := by
  simp [chi, dotProduct, sub_mul, sum_sub_distrib, ite_mul]

theorem lpA_mulVec (s t : Fin n) (y : Fin n → ℝ) : lpA G s t *ᵥ y = lpVec G (lpAPt s t y) := by
  funext i
  simp only [mulVec, lpA, lpVec]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j))
  · exact incVec_dot _ _ _
  · exact chi_dot s t y
  · simp [lpRowVec, lpVal, lpAPt]
  · simp [lpRowVec, lpVal, lpAPt, dotProduct, Pi.single_apply, sum_neg_distrib]

/-- The approximate direction `h̃ = −D̂(q̂ − A y)` as a public point. -/
def lpHPt (wf : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ) (qp : LPPoint (Fin n))
    (s t : Fin n) (y : Fin n → ℝ) : LPPoint (Fin n) :=
  ⟨fun u v => -wf s(u, v) * (qp.z u v - (y u - y v)), -dq * (qp.q - (y s - y t)),
    fun j => -dp j * (qp.yp j - y j), fun j => -dm j * (qp.ym j - -y j)⟩

theorem lpHPt_spec (wf : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ) (qp : LPPoint (Fin n))
    (s t : Fin n) (y : Fin n → ℝ) :
    (fun i => -lpD G wf dq dp dm i * (lpVec G qp i - (lpA G s t *ᵥ y) i)) =
      lpVec G (lpHPt wf dq dp dm qp s t y) := by
  rw [lpA_mulVec]
  funext i
  simp only [lpD, lpVec]
  generalize (lpEquiv G).symm i = x
  rcases x with ⟨p, _⟩ | (_ | (j | j)) <;> rfl

/-- The repaired direction as a public point: subtract the residual `ρ` on the `y⁺` rows. -/
def lpRepPt (h : LPPoint (Fin n)) (ρ : Fin n → ℝ) : LPPoint (Fin n) :=
  ⟨h.z, h.q, fun j => h.yp j - ρ j, h.ym⟩

theorem lpRepPt_spec (h : LPPoint (Fin n)) (ρ : Fin n → ℝ) :
    lpVec G (lpRepPt h ρ) = lpVec G h - selector (lpIota G) *ᵥ ρ := by
  funext i
  obtain ⟨x, rfl⟩ := (lpEquiv G).surjective i
  simp only [Pi.sub_apply, mulVec, dotProduct, selector, lpIota, Equiv.apply_eq_iff_eq,
    ite_mul, one_mul, zero_mul, lpVec, Equiv.symm_apply_apply]
  rcases x with ⟨p, _⟩ | (_ | (j | j)) <;> simp [lpVal, lpRepPt]

/-! ## Hidden `Aᵀ y` for copy-constant `y` as an exact query program -/

/-- The explicit part `y_q χ + y⁺ − y⁻` of `Aᵀ y`. -/
def lpExpl (s t : Fin n) (pt : LPPoint (Fin n)) : Fin n → ℝ :=
  fun w => pt.q * chi s t w + pt.yp w - pt.ym w

/-- The hidden divergence on the grid `2^e`, with `B` magnitude bits: one `allRowsUniv`. -/
def divProg (z : Fin n → Fin n → ℝ) (e : ℤ) (B : ℕ) :
    DTree (Finset (Fin n)) ℕ (Fin n → ℝ) (6 * B * n) :=
  (allRowsUniv (intFormula (fun w x => ⌊antiForm z w x / (2 : ℝ) ^ e⌋) e B) fun _ _ => true).cast
    (by simp [intFormula])

/-- `Aᵀ (lpVec pt)`: the hidden divergence by queries, the explicit part offline. -/
def transposeProg (s t : Fin n) (pt : LPPoint (Fin n)) (e : ℤ) (B : ℕ) :
    DTree (Finset (Fin n)) ℕ (Fin n → ℝ) (6 * B * n) :=
  (divProg pt.z e B).map fun y => y + lpExpl s t pt

theorem antiForm_grid {z : Fin n → Fin n → ℝ} {e : ℤ} (hm : ∀ u v, ∃ m : ℤ, z u v = m * (2 : ℝ) ^ e)
    (w x : Fin n) : ∃ m : ℤ, antiForm z w x = m * (2 : ℝ) ^ e := by
  unfold antiForm
  split_ifs
  · exact hm w x
  · obtain ⟨m, hm⟩ := hm x w
    exact ⟨-m, by rw [hm]; push_cast; ring⟩
  · exact ⟨0, by simp⟩

theorem antiForm_bound {z : Fin n → Fin n → ℝ} {c : ℝ} (hc : 0 < c) (hB : ∀ u v, |z u v| < c)
    (w x : Fin n) : |antiForm z w x| < c := by
  unfold antiForm
  split_ifs
  · exact hB w x
  · rw [abs_neg]; exact hB x w
  · simpa using hc

/-- **Exact `Aᵀ y` on copy-constant points.** -/
theorem transposeProg_eval (s t : Fin n) (pt : LPPoint (Fin n)) (e : ℤ) (B : ℕ)
    (hm : ∀ u v, ∃ m : ℤ, pt.z u v = m * (2 : ℝ) ^ e)
    (hB : ∀ u v, |pt.z u v| < (2 : ℝ) ^ B * (2 : ℝ) ^ e) :
    (transposeProg s t pt e B).eval G.out = (lpA G s t)ᵀ *ᵥ lpVec G pt := by
  rw [transposeProg, DTree.eval_map, divProg, DTree.eval_cast,
    hiddenDiv_exact G pt.z e B (antiForm_grid hm) (antiForm_bound (by positivity) hB),
    lpA_transpose_lpVec]
  funext w
  simp only [Pi.add_apply, lpExpl]
  ring

/-! ## Grids -/

theorem mul_grid {a b : ℝ} {e₁ e₂ : ℤ} (ha : ∃ m : ℤ, a = m * (2 : ℝ) ^ e₁)
    (hb : ∃ m : ℤ, b = m * (2 : ℝ) ^ e₂) : ∃ m : ℤ, a * b = m * (2 : ℝ) ^ (e₁ + e₂) := by
  obtain ⟨m₁, rfl⟩ := ha
  obtain ⟨m₂, rfl⟩ := hb
  exact ⟨m₁ * m₂, by rw [zpow_add₀ (by norm_num)]; push_cast; ring⟩

theorem sub_grid {a b : ℝ} {e : ℤ} (ha : ∃ m : ℤ, a = m * (2 : ℝ) ^ e)
    (hb : ∃ m : ℤ, b = m * (2 : ℝ) ^ e) : ∃ m : ℤ, a - b = m * (2 : ℝ) ^ e := by
  obtain ⟨m₁, rfl⟩ := ha
  obtain ⟨m₂, rfl⟩ := hb
  exact ⟨m₁ - m₂, by push_cast; ring⟩

theorem neg_grid {a : ℝ} {e : ℤ} (ha : ∃ m : ℤ, a = m * (2 : ℝ) ^ e) :
    ∃ m : ℤ, -a = m * (2 : ℝ) ^ e := by
  obtain ⟨m, rfl⟩ := ha
  exact ⟨-m, by push_cast; ring⟩

/-- A point of `2^{−p}ℤ` lies on every finer grid `2^{e}ℤ`, `e ≤ −p`. -/
theorem grid_of_le {a : ℝ} {p : ℕ} {e : ℤ} (he : e ≤ -(p : ℤ)) (ha : ∃ m : ℤ, a = m / 2 ^ p) :
    ∃ m : ℤ, a = m * (2 : ℝ) ^ e := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨d, hd⟩ := Int.le.dest he
  refine ⟨m * 2 ^ d, ?_⟩
  have h1 : (m : ℝ) / 2 ^ p = m * (2 : ℝ) ^ (-(p : ℤ)) := by
    rw [_root_.zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [h1, ← hd, zpow_add₀ (by norm_num), zpow_natCast]
  push_cast; ring

/-- The frozen solve's output lies on the grid `2^{−p}ℤ`. -/
theorem frozenSolveProg_grid (G : DiGraph (Fin n)) (w : Sym2 (Fin n) → ℝ) (ew : ℤ) (p B : ℕ)
    (E Pinv : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (x : Fin n → ℝ), (∀ i, ∃ m : ℤ, x i = m / 2 ^ p) →
      ∀ i, ∃ m : ℤ, (frozenSolveProg w ew p B E Pinv b k x).eval G.out i = m / 2 ^ p := by
  intro k
  induction k with
  | zero => intro x hx; simpa [frozenSolveProg] using hx
  | succ k ih =>
      intro x _
      rw [frozenSolveProg, DTree.eval_cast, DTree.eval_bind]
      exact ih _ (roundGrid_mem p _)

/-! ## One complete Newton step -/

/-- **One Newton step as a query program.** Given D4's output `out` and the public frozen data
(`wf` on hidden rows, `dq, d₊, d₋` explicit; `q̂ = lpVec qp`):
(a) query the right-hand side `b = Aᵀ(D̂q̂)` exactly (`6 B_rhs n` queries);
(b) run `k` preconditioned Richardson steps with `P⁻¹ = (lap out + E)⁻¹` (`k · 6 B_mv n`);
(c) form `h̃ = −D̂(q̂ − A xₖ)` offline, query the repair residual `Aᵀh̃` exactly (`6 B_rep n`),
and output the repaired direction `h̃ − R_* Aᵀh̃` as a public point. -/
def newtonStepProg (s t : Fin n) (wf : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ)
    (qp : LPPoint (Fin n)) (out : Sym2 (Fin n) → ℝ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ) :
    DTree (Finset (Fin n)) ℕ (LPPoint (Fin n))
      (6 * Brhs * n + (k * (6 * Bmv * n) + 6 * Brep * n)) :=
  (transposeProg s t (lpMulPt wf dq dp dm qp) (ew + eq) Brhs).bind fun b =>
    (frozenSolveProg wf ew p Bmv (lpE s t dq dp dm) (lap out univ + lpE s t dq dp dm)⁻¹ b k
      0).bind fun xk =>
      (transposeProg s t (lpHPt wf dq dp dm qp s t xk) (ew + eq) Brep).map fun ρ =>
        lpRepPt (lpHPt wf dq dp dm qp s t xk) ρ

/-- **Cost** `≤ 6n(B_rhs + k·B_mv + B_rep)`. -/
theorem newtonStepProg_cost (s t : Fin n) (wf : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ)
    (qp : LPPoint (Fin n)) (out : Sym2 (Fin n) → ℝ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ) :
    (newtonStepProg s t wf dq dp dm qp out ew eq p Brhs Bmv Brep k).cost G.out ≤
      6 * n * (Brhs + k * Bmv + Brep) :=
  (DTree.cost_le _ _).trans (le_of_eq (by ring))

/-- **Correctness of the Newton step program.** On the grids (`ŵ ∈ 2^{e_w}ℤ`,
`q̂` on hidden rows in `2^{e_q}ℤ`, `e_q ≤ −p`) and under the two bit checks, the program's
output, copied to the rows, is exactly the repaired direction computed from the exact
right-hand side `b = Aᵀ(D̂q̂)` and the frozen-solve output `xₖ`. -/
theorem newtonStepProg_eval (s t : Fin n) (wf : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ)
    (qp : LPPoint (Fin n)) (out : Sym2 (Fin n) → ℝ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ)
    (hwg : ∀ e, ∃ m : ℤ, wf e = m * (2 : ℝ) ^ ew)
    (hqg : ∀ u v, ∃ m : ℤ, qp.z u v = m * (2 : ℝ) ^ eq) (heq : eq ≤ -(p : ℤ))
    (hrhs : ∀ u v, |wf s(u, v) * qp.z u v| < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq)) :
    let A := lpA G s t
    let Dh := lpD G wf dq dp dm
    let b : Fin n → ℝ := Aᵀ *ᵥ fun i => Dh i * lpVec G qp i
    let P := lap out univ + explicitGram A Dh (lpHidF G)
    let xk := (frozenSolveProg wf ew p Bmv (explicitGram A Dh (lpHidF G)) P⁻¹ b k 0).eval G.out
    (∀ u v, |wf s(u, v) * (qp.z u v - (xk u - xk v))| < (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq)) →
    lpVec G ((newtonStepProg s t wf dq dp dm qp out ew eq p Brhs Bmv Brep k).eval G.out) =
      repairDir A (lpIota G) (fun i => -Dh i * (lpVec G qp i - (A *ᵥ xk) i)) := by
  intro A Dh b P xk hrep
  have hE : explicitGram A Dh (lpHidF G) = lpE s t dq dp dm := explicitGram_lp G s t wf dq dp dm
  have hb : (transposeProg s t (lpMulPt wf dq dp dm qp) (ew + eq) Brhs).eval G.out = b := by
    rw [transposeProg_eval G s t _ _ _ (fun u v => mul_grid (hwg _) (hqg u v)) hrhs]
    simp only [b, Dh, A]
    rw [lpD_mul_lpVec]
  have hx : (frozenSolveProg wf ew p Bmv (lpE s t dq dp dm) (lap out univ + lpE s t dq dp dm)⁻¹
      b k 0).eval G.out = xk := by
    simp only [xk, P, hE]
  have hxg := frozenSolveProg_grid G wf ew p Bmv (lpE s t dq dp dm)
    (lap out univ + lpE s t dq dp dm)⁻¹ b k 0 (fun _ => ⟨0, by simp⟩)
  rw [hx] at hxg
  have hhg : ∀ u v, ∃ m : ℤ, (lpHPt wf dq dp dm qp s t xk).z u v = m * (2 : ℝ) ^ (ew + eq) :=
    fun u v => by
      simp only [lpHPt, neg_mul]
      exact neg_grid (mul_grid (hwg _) (sub_grid (hqg u v)
        (sub_grid (grid_of_le heq (hxg u)) (grid_of_le heq (hxg v)))))
  have hhB : ∀ u v, |(lpHPt wf dq dp dm qp s t xk).z u v| <
      (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq) := fun u v => by
    simp only [lpHPt, neg_mul, abs_neg]
    exact hrep u v
  simp only [newtonStepProg, DTree.eval_bind, DTree.eval_map]
  rw [hb, hx, lpRepPt_spec, transposeProg_eval G s t _ _ _ hhg hhB, ← lpHPt_spec]
  rfl

/-! ## A public bound on the frozen-solve output (for the repair bit check) -/

set_option maxHeartbeats 3200000 in
/-- **The frozen-solve output is bounded publicly:** under the hypotheses of
`lem_numeric_query`, `‖xₖ‖₂ ≤ X + √(1/(ℓ/2)) (√Λ X + 2τ)`, the same quantity that enters its
bit check. -/
theorem query_xk_bound {M r : ℕ} {A : Matrix (Fin M) (Fin r) ℝ} {κ m x w c : Fin M → ℝ}
    {t U : ℝ} (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, Real.pi / κ i ≤ U) {wmin dp : ℝ} (hwmin : 0 < wmin) (hwlo : ∀ i, wmin ≤ w i)
    (hdp : U ^ 2 / wmin ≤ dp) (hwhi : ∀ i, w i ≤ 4) {sst ε : ℝ}
    (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * r / ε)
    (hc : ‖c‖ ≤ 4 * U) (hrowA : ∀ i, ∑ j, A i j ^ 2 ≤ 2) {ι : Fin r → Fin M} (hι : IdRows A ι)
    {Dh qh : Fin M → ℝ} {β : ℝ}
    (hDh : ∀ i, |Dh i - normD w (barS κ m x) i| ≤ β * normD w (barS κ m x) i)
    (hqh : ∀ i, |qh i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ : β ≤ 1 / 2)
    {hid : Fin M → Option (Sym2 (Fin r))} {G : DiGraph (Fin r)} {wf : Sym2 (Fin r) → ℝ}
    (hrow : ∀ i e, hid i = some e → vecMulVec (A i) (A i) = pairMat e)
    (hDw : ∀ i e, hid i = some e → Dh i = wf e)
    (hcount : ∀ e, (univ.filter fun i => hid i = some e).card = Spanner.symS G e)
    (hιe : ∀ j, hid (ι j) = none) {dmin : ℝ} (hdmin : 0 < dmin) (hDι : ∀ j, dmin ≤ Dh (ι j))
    (hwf0 : ∀ e, 0 ≤ wf e)
    {K t' R : ℕ} {δ εs : ℝ} {out : Sym2 (Fin r) → ℝ} (hgood : Sparsify.Good G wf K t' δ R out)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    {X Λ W : ℝ}
    (hX : 4 * Real.sqrt (2 * M) * Real.sqrt M * dp * (64 * r * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * M) ≤ Λ) (hW : ∀ e, |wf e| ≤ W)
    {ew : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew) (p B : ℕ)
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt r * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ B * (2 : ℝ) ^ (ew - p))
    (k : ℕ) :
    let b : Fin r → ℝ := Aᵀ *ᵥ fun i => Dh i * qh i
    let P := lap out univ + explicitGram A Dh hid
    let xk := (frozenSolveProg wf ew p B (explicitGram A Dh hid) P⁻¹ b k 0).eval G.out
    euc xk ≤ X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt r * (1 / 2 ^ p)))) := by
  intro b P xk
  set ℓ := sst ^ 2 / 16 with hℓdef
  set D := normD w (barS κ m x)
  set q := normQ t c w (barDphi κ m x)
  set a := Real.sqrt (2 * M)
  set Q := 64 * r * U / ε + 4 / sst
  set Pπ := 4 * a * Real.sqrt M * dp * (Q + 1) / ℓ
  have hU0 : 0 < U := by linarith
  obtain ⟨h1, h2, -, h4⟩ := normalbounds (t := t) (c := c) hκ hx hU1 hU hwmin hwlo hwhi hsst hs
    hrowA hι
  have hD : ∀ i, 0 < D i := fun i => (h1 i).1
  have hDp : ∀ i, D i ≤ dp := fun i => (h1 i).2.trans hdp
  have hdp0 : 0 ≤ dp := (by positivity : 0 ≤ U ^ 2 / wmin).trans hdp
  have hℓ : 0 < ℓ := by positivity
  have hL : ∀ y, ℓ * euc y ^ 2 ≤ y ⬝ᵥ (gram A D *ᵥ y) := fun y => by
    have := h2 y; simp only [ℓ]; norm_num at this ⊢; linarith
  have hq : ∀ i, |q i| ≤ Q := fun i => (h4 i).trans (add_le_add (by
    calc |t| * ‖c‖ ≤ 16 * r / ε * (4 * U) := mul_le_mul ht hc (norm_nonneg _) (by positivity)
      _ = 64 * r * U / ε := by ring) (by norm_num))
  have hQ : 0 ≤ Q := by simp only [Q]; positivity
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hDhpos : ∀ i, 0 < Dh i := fun i => by
    have := (abs_le.mp (hDh i)).1; nlinarith [hD i]
  have hDh_up : ∀ i, Dh i ≤ 3 / 2 * dp := fun i => by
    have := (abs_le.mp (hDh i)).2; nlinarith [hD i, hDp i]
  have hlo : ∀ y, ℓ / 2 * euc y ^ 2 ≤ y ⬝ᵥ (gram A Dh *ᵥ y) := frozen_gram_lo hD hDh hβ hL
  have hup : ∀ y, y ⬝ᵥ (gram A Dh *ᵥ y) ≤ Λ * euc y ^ 2 := fun y => by
    have h0 := frozen_gram_up (opnorm_le hrowA) hD hDp hdp0 hDh hβ y
    have ha2 : a ^ 2 = 2 * M := Real.sq_sqrt (by positivity)
    rw [ha2] at h0
    exact h0.trans (mul_le_mul_of_nonneg_right hΛ (sq_nonneg _))
  have hΛ0 : 0 ≤ Λ := (by positivity : (0 : ℝ) ≤ 3 / 2 * dp * (2 * M)).trans hΛ
  have hdet : (gram A Dh).det ≠ 0 := det_ne_zero_of_quad_pos fun y hy => by
    have h0 : 0 < euc y := by
      rcases (euc_nonneg y).lt_or_eq with h0 | h0
      · exact h0
      · exfalso; apply hy; funext j
        have := abs_le_euc y j; rw [← h0] at this
        exact abs_nonpos_iff.mp this
    exact lt_of_lt_of_le (by positivity) (hlo y)
  set ph : Fin r → ℝ := (gram A Dh)⁻¹ *ᵥ b with hph_def
  have hph : gram A Dh *ᵥ ph = b := by
    rw [hph_def, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  have hphn : euc ph ≤ Pπ := by
    have hs1 := solve_bound (by positivity) hlo hph
    have hs2 : euc (fun i => Dh i * qh i) ≤ Real.sqrt M * (2 * dp * (Q + 1)) :=
      euc_le_sqrt_card_mul (by positivity) fun i => by
        rw [abs_mul, abs_of_pos (hDhpos i)]
        have hq1 : |qh i| ≤ Q + 1 / 2 := by
          have := abs_sub_abs_le_abs_sub (qh i) (q i); linarith [hqh i, hq i]
        calc Dh i * |qh i| ≤ 3 / 2 * dp * (Q + 1 / 2) :=
              mul_le_mul (hDh_up i) hq1 (abs_nonneg _) (by positivity)
          _ ≤ 2 * dp * (Q + 1) := by nlinarith
    have hs3 := opnorm_transpose_le hrowA (fun i => Dh i * qh i)
    calc euc ph ≤ euc b / (ℓ / 2) := hs1
      _ ≤ a * (Real.sqrt M * (2 * dp * (Q + 1))) / (ℓ / 2) :=
          div_le_div_of_nonneg_right (hs3.trans (mul_le_mul_of_nonneg_left hs2 ha))
            (by positivity)
      _ = Pπ := by simp only [Pπ]; field_simp; ring
  have hXh : euc ph ≤ X := hphn.trans hX
  have hEh : enorm (gram A Dh) ph ≤ Real.sqrt Λ * X := by
    rw [enorm]
    calc Real.sqrt (ph ⬝ᵥ (gram A Dh *ᵥ ph)) ≤ Real.sqrt (Λ * euc ph ^ 2) :=
          Real.sqrt_le_sqrt (hup ph)
      _ = Real.sqrt Λ * euc ph := by
          rw [Real.sqrt_mul hΛ0, Real.sqrt_sq (euc_nonneg _)]
      _ ≤ Real.sqrt Λ * X := mul_le_mul_of_nonneg_left hXh (Real.sqrt_nonneg _)
  have hsolve := lp_frozen_query_solve hrow hDw hDhpos hcount hι hιe hdmin hDι hwf0 hgood
    hεs0 hεs hδlo hδhi b ph hph (by positivity : (0 : ℝ) < ℓ / 2) hΛ0 hlo hup hXh hEh hW hwg p B
    hB k
  set τ := Real.sqrt Λ * (Real.sqrt r * (1 / 2 ^ p))
  have h3 : enorm (gram A Dh) (xk - ph) ≤ Real.sqrt Λ * X + 2 * τ := by
    have h0 := enorm_nonneg (gram A Dh) ph
    have h5 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc _ ≤ (1 / 2) ^ k * enorm (gram A Dh) ph + 2 * τ := hsolve
      _ ≤ 1 * enorm (gram A Dh) ph + 2 * τ := by gcongr
      _ ≤ Real.sqrt Λ * X + 2 * τ := by linarith
  have h5 := euc_le_enorm (by positivity : (0 : ℝ) < ℓ / 2) hlo (xk - ph)
  have h6 := euc_add_le (xk - ph) ph
  rw [sub_add_cancel] at h6
  have h7 : Real.sqrt (1 / (ℓ / 2)) * enorm (gram A Dh) (xk - ph) ≤
      Real.sqrt (1 / (ℓ / 2)) * (Real.sqrt Λ * X + 2 * τ) :=
    mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
  linarith

/-- The repair bit check from public bounds: `|ŵ| ≤ W`, `|q̂_z| ≤ Q_z`, `‖y‖₂ ≤ X_k`. -/
theorem repair_bit_of_bound {wf : Sym2 (Fin n) → ℝ} {qz : Fin n → Fin n → ℝ} {y : Fin n → ℝ}
    {W Qz Xk c : ℝ} (hW : ∀ e, |wf e| ≤ W) (hQz : ∀ u v, |qz u v| ≤ Qz) (hy : euc y ≤ Xk)
    (hc : W * (Qz + 2 * Xk) < c) (u v : Fin n) :
    |wf s(u, v) * (qz u v - (y u - y v))| < c := by
  have h1 : |qz u v - (y u - y v)| ≤ Qz + 2 * Xk := by
    have := abs_sub (qz u v) (y u - y v)
    have := abs_sub (y u) (y v)
    linarith [abs_le_euc y u, abs_le_euc y v, hQz u v]
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW s(u, v))
  rw [abs_mul]
  exact lt_of_le_of_lt (mul_le_mul (hW _) h1 (abs_nonneg _) hW0) hc

/-! ## `lem:numeric` for the complete Newton-step program -/

open Spectral in
set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` for the program's output.** `newtonStepProg` queries `b = Aᵀ(D̂q̂)`
exactly, runs the frozen solve, and queries the repair residual exactly. Its output `d`
(a public point; `lpVec d` its copies on the rows) is the repaired direction, so `Aᵀd = 0`
exactly, and `d` is within the mixed-norm bound of `lem_numeric_lp` of the exact Newton direction.
All bit checks are public: `W Q_z < 2^{B_rhs} 2^{e_w+e_q}` and
`W(Q_z + 2X_k) < 2^{B_rep} 2^{e_w+e_q}`, `X_k = X + √(1/(ℓ/2))(√Λ X + 2τ)`. -/
theorem newtonStep_numeric_lp (s t₀ : Fin n) {κ m x w c : Fin (lpM G) → ℝ} {t U : ℝ}
    (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, Real.pi / κ i ≤ U) {wmin dp : ℝ} (hwmin : 0 < wmin) (hwlo : ∀ i, wmin ≤ w i)
    (hdp : U ^ 2 / wmin ≤ dp) (hwhi : ∀ i, w i ≤ 4) (hwsum : ∑ i, w i ≤ 4 * n) {sst ε : ℝ}
    (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * n / ε)
    (hc : ‖c‖ ≤ 4 * U)
    {wf : Sym2 (Fin n) → ℝ} {dq : ℝ} {dpv dmv : Fin n → ℝ} {qp : LPPoint (Fin n)}
    {p0 : Fin n → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |lpD G wf dq dpv dmv i - normD w (barS κ m x) i| ≤
      β * normD w (barS κ m x) i)
    (hqh : ∀ i, |lpVec G qp i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / 2)
    (hp : gram (lpA G s t₀) (normD w (barS κ m x)) *ᵥ p0 =
      (lpA G s t₀)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {dmin : ℝ} (hdmin : 0 < dmin) (hdpv : ∀ j, dmin ≤ dpv j) (hwf0 : ∀ e, 0 ≤ wf e)
    {K t' R : ℕ} {δ εs : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G wf K t' δ R out)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    {X Λ W Qz : ℝ}
    (hX : 4 * Real.sqrt (2 * lpM G) * Real.sqrt (lpM G) * dp * (64 * n * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * lpM G) ≤ Λ) (hW : ∀ e, |wf e| ≤ W) (hQz : ∀ u v, |qp.z u v| ≤ Qz)
    {ew eq : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew)
    (hqg : ∀ u v, ∃ z : ℤ, qp.z u v = z * (2 : ℝ) ^ eq) (p Brhs Bmv Brep : ℕ)
    (heq : eq ≤ -(p : ℤ))
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Bmv * (2 : ℝ) ^ (ew - p))
    (hBrhs : W * Qz < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq))
    (hBrep : W * (Qz + 2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq))
    (hτβ : 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p))) ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β) :
    let A := lpA G s t₀
    let Dh := lpD G wf dq dpv dmv
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let b : Fin n → ℝ := Aᵀ *ᵥ fun i => Dh i * lpVec G qp i
    let P := lap out univ + explicitGram A Dh (lpHidF G)
    let xk := (frozenSolveProg wf ew p Bmv (explicitGram A Dh (lpHidF G)) P⁻¹ b k 0).eval G.out
    let h : Fin (lpM G) → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin (lpM G) → ℝ := fun i => -Dh i * (lpVec G qp i - (A *ᵥ xk) i)
    let d := (newtonStepProg s t₀ wf dq dpv dmv qp out ew eq p Brhs Bmv Brep k).eval G.out
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * lpM G)
    let Q := 64 * n * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt (lpM G) * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt (lpM G) * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt n
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt n⌉₊ : ℝ)
    lpVec G d = repairDir A (lpIota G) ht' ∧ ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ lpVec G d = 0 ∧
      mixed C w (fun i => barS κ m x i * (lpVec G d - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * lpM G) * P₁ * β := by
  intro A Dh D q b P xk h ht' d ℓ a Q Pπ Eπ P₁ T₀
  have hxk : euc xk ≤ _ := query_xk_bound hκ hx hU1 hU hwmin hwlo hdp hwhi hsst hs hε ht hc
    (lpA_row_sq_le G s t₀) (lpA_idRows G s t₀) hDh hqh hβ (lpA_hrow G s t₀)
    (lpD_hD G wf dq dpv dmv) (lp_hcount G) (lpHid_iota G) hdmin
    (fun j => by simpa [lpD, lpIota, lpWeight] using hdpv j) hwf0 hgood hεs0 hεs hδlo hδhi
    hX hΛ hW hwg p Bmv hB k
  have hrhs : ∀ u v, |wf s(u, v) * qp.z u v| < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq) :=
    fun u v => by
      have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW s(u, v))
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_mul (hW _) (hQz u v) (abs_nonneg _) hW0) hBrhs
  have hd : lpVec G d = repairDir A (lpIota G) ht' :=
    newtonStepProg_eval G s t₀ wf dq dpv dmv qp out ew eq p Brhs Bmv Brep k hwg hqg heq hrhs
      (repair_bit_of_bound hW hQz hxk hBrep)
  obtain ⟨H1, H2, H3⟩ := lem_numeric_lp G s t₀ hκ hx hU1 hU hwmin hwlo hdp hwhi hwsum hsst hs hε
    ht hc hC hDh hqh hβ0 hβ hp hdmin hdpv hwf0 hgood hεs0 hεs hδlo hδhi hX hΛ hW hwg p Bmv hB
    hτβ k hk
  refine ⟨hd, H1, ?_, ?_⟩
  · rw [hd]; exact H2
  · rw [hd]; exact H3

open Spectral in
set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` for the program's output, from the path-following invariants** (`s ≠ t₀`):
`newtonStep_numeric_lp` with the weight and slack hypotheses derived as in
`lem_numeric_lp_inv` (`d₊ = 4M̄U²`, `s_* = ε/(2¹² n M̄² U³)`). -/
theorem newtonStep_numeric_lp_inv (s t₀ : Fin n) (hst : s ≠ t₀) {bc : Fin n → ℝ}
    {κ m w c : Fin (lpM G) → ℝ} {t U : ℝ}
    {L₀ : ℝ} (hL : 2 ≤ L₀) (hLM : Real.logb 2 (2 * lpM G) ≤ L₀ - 1)
    (hκ : ∀ i, 0 < κ i) {c₀ Mbar ε : ℝ} (hc₀lo : 1 / (2 * Mbar) ≤ c₀)
    (hcM : c₀ ≤ 1 / (2 * lpM G)) (hU1 : 1 ≤ U) (hU : ∀ i, Real.pi / κ i ≤ U)
    {x x₀ : Fin (lpM G) → ℝ}
    (hx : x ∈ Feasible (lpA G s t₀) bc κ m) (hx₀ : x₀ ∈ Feasible (lpA G s t₀) bc κ m)
    (hMbar : (lpM G : ℝ) ≤ Mbar) (hr : (1 : ℝ) ≤ n) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hw : ∀ i, 0 < w i) (ht : |t| ≤ 16 * n / ε) (hc : ‖c‖ ≤ 4 * U)
    (hwin : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (lpA G s t₀) x i)| ≤ 1 / 20)
    (hδc : cent (48 * (2 * L₀)) (lpA G s t₀) (barS κ m x) (barDphi κ m x) c t w ≤ 1 / 1000)
    (hs0 : ∀ i, 1 / U ≤ slk κ m x₀ i)
    {sst dp : ℝ} (hsst : sst = ε / (2 ^ 12 * n * Mbar ^ 2 * U ^ 3)) (hdp : dp = 4 * Mbar * U ^ 2)
    {wf : Sym2 (Fin n) → ℝ} {dq : ℝ} {dpv dmv : Fin n → ℝ} {qp : LPPoint (Fin n)}
    {p0 : Fin n → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |lpD G wf dq dpv dmv i - normD w (barS κ m x) i| ≤
      β * normD w (barS κ m x) i)
    (hqh : ∀ i, |lpVec G qp i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / 2)
    (hp : gram (lpA G s t₀) (normD w (barS κ m x)) *ᵥ p0 =
      (lpA G s t₀)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {dmin : ℝ} (hdmin : 0 < dmin) (hdpv : ∀ j, dmin ≤ dpv j) (hwf0 : ∀ e, 0 ≤ wf e)
    {K t' R : ℕ} {δ εs : ℝ} {out : Sym2 (Fin n) → ℝ} (hgood : Sparsify.Good G wf K t' δ R out)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    {X Λ W Qz : ℝ}
    (hX : 4 * Real.sqrt (2 * lpM G) * Real.sqrt (lpM G) * dp * (64 * n * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * lpM G) ≤ Λ) (hW : ∀ e, |wf e| ≤ W) (hQz : ∀ u v, |qp.z u v| ≤ Qz)
    {ew eq : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew)
    (hqg : ∀ u v, ∃ z : ℤ, qp.z u v = z * (2 : ℝ) ^ eq) (p Brhs Bmv Brep : ℕ)
    (heq : eq ≤ -(p : ℤ))
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Bmv * (2 : ℝ) ^ (ew - p))
    (hBrhs : W * Qz < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq))
    (hBrep : W * (Qz + 2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq))
    (hτβ : 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p))) ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β) :
    let A := lpA G s t₀
    let Dh := lpD G wf dq dpv dmv
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let b : Fin n → ℝ := Aᵀ *ᵥ fun i => Dh i * lpVec G qp i
    let P := lap out univ + explicitGram A Dh (lpHidF G)
    let xk := (frozenSolveProg wf ew p Bmv (explicitGram A Dh (lpHidF G)) P⁻¹ b k 0).eval G.out
    let h : Fin (lpM G) → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ht' : Fin (lpM G) → ℝ := fun i => -Dh i * (lpVec G qp i - (A *ᵥ xk) i)
    let d := (newtonStepProg s t₀ wf dq dpv dmv qp out ew eq p Brhs Bmv Brep k).eval G.out
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * lpM G)
    let Q := 64 * n * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt (lpM G) * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt (lpM G) * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt n
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt n⌉₊ : ℝ)
    lpVec G d = repairDir A (lpIota G) ht' ∧ ‖ht' - h‖ ≤ P₁ * β ∧ Aᵀ *ᵥ lpVec G d = 0 ∧
      mixed C w (fun i => barS κ m x i * (lpVec G d - h) i) ≤
        2 * T₀ / sst * (1 + Real.sqrt 2 * lpM G) * P₁ * β := by
  intro A Dh D q b P xk h ht' d ℓ a Q Pπ Eπ P₁ T₀
  -- the weight and slack windows, as in `lem_numeric_query_inv`
  have hA := det_ne_zero_of_idRows (lpA_idRows G s t₀)
  have hrowne := lpA_row_ne_zero G hst
  have hwin5 : ∀ i, |Real.log (w i) -
      Real.log (gfun κ m (1 - 1 / L₀) c₀ (lpA G s t₀) x i)| ≤ 1 / 5 :=
    fun i => (hwin i).trans (by norm_num)
  obtain ⟨hwlo, hwhi, hwsum⟩ := weight_invariants hA hrowne hL hc₀lo hcM hMbar hr hw hwin5
  have hM1 : (1 : ℝ) ≤ lpM G := by
    have hr0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
    exact_mod_cast Fin.pos (lpIota G ⟨0, hr0⟩)
  have hMb : 0 < Mbar := by linarith
  have hc₀ : 0 ≤ c₀ := (by positivity : (0 : ℝ) ≤ 1 / (2 * Mbar)).trans hc₀lo
  have hs : ∀ i, sst ≤ slk κ m x i := fun i => by
    rw [hsst]
    exact slack_floor_note hA hrowne hL hLM hκ hc₀ hcM hU1 hU hx hx₀ hMbar hr hε hε1 hwlo hwsum ht
      hc hwin hδc hs0 i
  have hU0 : 0 < U := by linarith
  have hsst0 : 0 < sst := by rw [hsst]; positivity
  have hdp' : U ^ 2 / (1 / (4 * Mbar)) ≤ dp := by rw [hdp]; field_simp; rfl
  exact newtonStep_numeric_lp G s t₀ (wmin := 1 / (4 * Mbar)) hκ hx.2 hU1 hU (by positivity)
    hwlo hdp' hwhi hwsum hsst0 hs hε ht hc hC hDh hqh hβ0 hβ hp hdmin hdpv hwf0 hgood hεs0 hεs
    hδlo hδhi hX hΛ hW hQz hwg hqg p Brhs Bmv Brep heq hB hBrhs hBrep hτβ k hk

/-! ## The randomized wrapper: D4, then one Newton step -/

open scoped ENNReal

/-- **D4 followed by one Newton step.** Run the sparsifier on the frozen hidden weights `wf`;
on success run `newtonStepProg` with its output (on failure output `0`). -/
def newtonProg (s t : Fin n) (wf : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ)
    (qp : LPPoint (Fin n)) (K J t' R : ℕ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ) :
    RTree (Finset (Fin n)) ℕ (LPPoint (Fin n))
      ((R * Sparsify.levelBudget (n := n) K J t' + 3 * n) +
        (6 * Brhs * n + (k * (6 * Bmv * n) + 6 * Brep * n))) :=
  (Sparsify.sparsify wf K J t' R).bind fun o => match o with
  | none => RTree.pure (PMF.pure ⟨0, 0, 0, 0⟩)
  | some out => RTree.ofDeterministic (newtonStepProg s t wf dq dp dm qp out ew eq p Brhs Bmv Brep k)

/-- **Budget:** every execution uses at most `q_D4 + 6n(B_rhs + k·B_mv + B_rep)` queries,
`q_D4 = R · levelBudget + 3n`. -/
theorem newtonProg_cost (s t : Fin n) (wf : Sym2 (Fin n) → ℝ) (dq : ℝ) (dp dm : Fin n → ℝ)
    (qp : LPPoint (Fin n)) (K J t' R : ℕ) (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ)
    {o : LPPoint (Fin n) × ℕ}
    (ho : o ∈ (RTree.run G.out (newtonProg s t wf dq dp dm qp K J t' R ew eq p Brhs Bmv Brep k)).support) :
    o.2 ≤ (R * Sparsify.levelBudget (n := n) K J t' + 3 * n) + 6 * n * (Brhs + k * Bmv + Brep) :=
  (RTree.cost_le _ _ ho).trans (le_of_eq (by ring))

open Probability in
/-- **Failure probability of D4 + Newton step.** Any property `Q` that the Newton step's
output has whenever D4's output is `Good` fails with probability at most `sparsify_fail_le`'s
bound. -/
theorem newtonProg_fail_le (s t : Fin n) {wf : Sym2 (Fin n) → ℝ} (dq : ℝ) (dp dm : Fin n → ℝ)
    (qp : LPPoint (Fin n)) {K : ℕ} (J : ℕ) {t' : ℕ} (ew eq : ℤ) (p Brhs Bmv Brep k : ℕ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ e, (Spanner.symS G e : ℝ) ≤ C)
    (hw0 : ∀ e, 0 ≤ wf e) (hK : n ≤ 2 ^ K) (ht : 0 < t') {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (Q : LPPoint (Fin n) → Prop)
    (hQ : ∀ out, Sparsify.Good G wf K t' δ R out →
      Q ((newtonStepProg s t wf dq dp dm qp out ew eq p Brhs Bmv Brep k).eval G.out)) :
    mass ((newtonProg s t wf dq dp dm qp K J t' R ew eq p Brhs Bmv Brep k).eval G.out)
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

open Probability Spectral in
set_option maxHeartbeats 3200000 in
/-- **`lem:numeric` for D4 + one Newton step, with probability.** Outside the sparsifier's
failure probability, the program's output `d` satisfies `Aᵀd = 0` exactly and is within the
mixed-norm bound `P·β` of the exact Newton direction `h` (as in `newtonStep_numeric_lp`). The
budget is `q_D4 + 6n(B_rhs + k·B_mv + B_rep)` (`newtonProg_cost`). -/
theorem newtonProg_numeric_lp (s t₀ : Fin n) {κ m x w c : Fin (lpM G) → ℝ} {t U : ℝ}
    (hκ : ∀ i, 0 < κ i) (hx : Interior κ m x) (hU1 : 1 ≤ U)
    (hU : ∀ i, Real.pi / κ i ≤ U) {wmin dp : ℝ} (hwmin : 0 < wmin) (hwlo : ∀ i, wmin ≤ w i)
    (hdp : U ^ 2 / wmin ≤ dp) (hwhi : ∀ i, w i ≤ 4) (hwsum : ∑ i, w i ≤ 4 * n) {sst ε : ℝ}
    (hsst : 0 < sst) (hs : ∀ i, sst ≤ slk κ m x i) (hε : 0 < ε) (ht : |t| ≤ 16 * n / ε)
    (hc : ‖c‖ ≤ 4 * U)
    {wf : Sym2 (Fin n) → ℝ} {dq : ℝ} {dpv dmv : Fin n → ℝ} {qp : LPPoint (Fin n)}
    {p0 : Fin n → ℝ} {β C : ℝ} (hC : 0 ≤ C)
    (hDh : ∀ i, |lpD G wf dq dpv dmv i - normD w (barS κ m x) i| ≤
      β * normD w (barS κ m x) i)
    (hqh : ∀ i, |lpVec G qp i - normQ t c w (barDphi κ m x) i| ≤ β) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / 2)
    (hp : gram (lpA G s t₀) (normD w (barS κ m x)) *ᵥ p0 =
      (lpA G s t₀)ᵀ *ᵥ fun i => normD w (barS κ m x) i * normQ t c w (barDphi κ m x) i)
    {dmin : ℝ} (hdmin : 0 < dmin) (hdpv : ∀ j, dmin ≤ dpv j) (hwf0 : ∀ e, 0 ≤ wf e)
    -- the sparsifier
    {K J t' R : ℕ} {δ εs Cs : ℝ} (hCs0 : 0 ≤ Cs) (hCs : ∀ e, (Spanner.symS G e : ℝ) ≤ Cs)
    (hK : n ≤ 2 ^ K) (ht' : 0 < t') (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hεs0 : 0 < εs) (hεs : εs ≤ 1 / 8) (hδlo : 1 - εs ≤ (1 - δ) ^ R)
    (hδhi : (1 + δ) ^ R ≤ 1 + εs)
    {X Λ W Qz : ℝ}
    (hX : 4 * Real.sqrt (2 * lpM G) * Real.sqrt (lpM G) * dp * (64 * n * U / ε + 4 / sst + 1) /
      (sst ^ 2 / 16) ≤ X)
    (hΛ : 3 / 2 * dp * (2 * lpM G) ≤ Λ) (hW : ∀ e, |wf e| ≤ W) (hQz : ∀ u v, |qp.z u v| ≤ Qz)
    {ew eq : ℤ} (hwg : ∀ e, ∃ z : ℤ, wf e = z * (2 : ℝ) ^ ew)
    (hqg : ∀ u v, ∃ z : ℤ, qp.z u v = z * (2 : ℝ) ^ eq) (p Brhs Bmv Brep : ℕ)
    (heq : eq ≤ -(p : ℤ))
    (hB : W * (2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Bmv * (2 : ℝ) ^ (ew - p))
    (hBrhs : W * Qz < (2 : ℝ) ^ Brhs * (2 : ℝ) ^ (ew + eq))
    (hBrep : W * (Qz + 2 * (X + Real.sqrt (1 / (sst ^ 2 / 16 / 2)) *
      (Real.sqrt Λ * X + 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p)))))) <
        (2 : ℝ) ^ Brep * (2 : ℝ) ^ (ew + eq))
    (hτβ : 2 * (Real.sqrt Λ * (Real.sqrt n * (1 / 2 ^ p))) ≤ β)
    (k : ℕ) (hk : (1 / 2 : ℝ) ^ k ≤ β) :
    let A := lpA G s t₀
    let D := normD w (barS κ m x)
    let q := normQ t c w (barDphi κ m x)
    let h : Fin (lpM G) → ℝ := fun i => -D i * (q i - (A *ᵥ p0) i)
    let ℓ := sst ^ 2 / 16
    let a := Real.sqrt (2 * lpM G)
    let Q := 64 * n * U / ε + 4 / sst
    let Pπ := 4 * a * Real.sqrt (lpM G) * dp * (Q + 1) / ℓ
    let Eπ := 2 / ℓ * (a * Real.sqrt (lpM G) * dp * (Q + 2) + a ^ 2 * dp * Pπ) +
      (Real.sqrt (2 / ℓ) * (Real.sqrt (3 / 2 * dp) * a) * Pπ + Real.sqrt (2 / ℓ)) + Real.sqrt n
    let P₁ := dp * (Q + Real.sqrt 2 * Pπ) + 2 * dp * (1 + Real.sqrt 2 * Eπ)
    let T₀ := 1 + 2 * C * (⌈Real.sqrt n⌉₊ : ℝ)
    mass ((newtonProg s t₀ wf dq dpv dmv qp K J t' R ew eq p Brhs Bmv Brep k).eval G.out)
        (fun d => ¬ (Aᵀ *ᵥ lpVec G d = 0 ∧
          mixed C w (fun i => barS κ m x i * (lpVec G d - h) i) ≤
            2 * T₀ / sst * (1 + Real.sqrt 2 * lpM G) * P₁ * β)) ≤
      R * (t' * (2⁻¹ : ℝ≥0∞) ^ J +
        ENNReal.ofReal (2 * n * Real.exp (-(δ ^ 2) / (8 * (Cs * (2 * K + 1 : ℕ) / t'))))) +
      (Sparsify.resid G (Sparsify.P0 wf)).card * (4⁻¹ : ℝ≥0∞) ^ R := by
  intro A D q h ℓ a Q Pπ Eπ P₁ T₀
  refine newtonProg_fail_le G s t₀ dq dpv dmv qp J ew eq p Brhs Bmv Brep k hCs0 hCs hwf0 hK ht'
    hδ hδ1 R _ fun out hgood => ?_
  obtain ⟨-, -, H3, H4⟩ := newtonStep_numeric_lp G s t₀ hκ hx hU1 hU hwmin hwlo hdp hwhi hwsum
    hsst hs hε ht hc hC hDh hqh hβ0 hβ hp hdmin hdpv hwf0 hgood hεs0 hεs hδlo hδhi hX hΛ hW hQz
    hwg hqg p Brhs Bmv Brep heq hB hBrhs hBrep hτβ k hk
  exact ⟨H3, H4⟩

end

end ImplicitLP
end CutQueryComplexity
