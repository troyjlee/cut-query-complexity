import CutQueryComplexity.ImplicitLP.GenericQuery.Rows
import CutQueryComplexity.ImplicitLP.PathFollowing.Main

/-! # Original-input envelopes and generic accuracy scales

These certificates concern only original public data and honest input graphs.
They do not assert the existence of a solver, internal state or query cap.
The Lewis restart retains `a0^2`; final objective accuracy uses `Mbar * U`.
-/

set_option autoImplicit false

namespace CutQueryComplexity.ImplicitLP.GenericQuery

open Matrix Finset Real
noncomputable section
variable {n m : ℕ}

/-- Canonical pairs and explicit coordinates are the used public input indices. -/
def Used : Index n m → Prop
  | .inl (u, v) => u < v
  | .inr _ => True

def DyadicValue (x : ℝ) : Prop := ∃ (k : ℕ) (z : ℤ), x = z / (2 : ℝ) ^ k

/-- Public numerical parameters; the cap and algorithm are not fields. -/
structure Envelope where
  C : ℝ
  Cexp : ℝ
  Mbar : ℝ
  U : ℝ
  a0 : ℝ
  ε : ℝ
  ζ : ℝ

def Envelope.Npub (P : Envelope) (n : ℕ) : ℝ :=
  2 + n + P.Mbar + P.U + P.ε⁻¹ + P.a0⁻¹ + P.ζ⁻¹

/-- Static properties of the original input, independent of the hidden graph. -/
structure PublicHyp (D : Data n m) (P : Envelope) : Prop where
  rank_ge : 2 ≤ n
  C_ge : 1 ≤ P.C
  Cexp_ge : 1 ≤ P.Cexp
  explicit_count : (m : ℝ) ≤ P.Cexp * n
  rows_bound : P.C * n * ((n : ℝ) - 1) / 2 + m ≤ P.Mbar
  U_ge : 2 ≤ P.U
  a0_pos : 0 < P.a0
  a0_le : P.a0 ≤ 1
  ε_pos : 0 < P.ε
  ε_le : P.ε ≤ 1
  ζ_pos : 0 < P.ζ
  ζ_le : P.ζ ≤ 1 / 2
  row_norms : ∀ j, P.a0 ^ 2 ≤ ∑ v, D.rows.matrix j v ^ 2 ∧
    ∑ v, D.rows.matrix j v ^ 2 ≤ 2
  width_pos : ∀ i, Used i → D.lower i < D.upper i
  width_le : ∀ i, Used i → D.upper i - D.lower i ≤ P.U
  coordinate_bound : ∀ i, Used i → |D.lower i| ≤ P.U ∧ |D.upper i| ≤ P.U ∧
    |D.cost i| ≤ P.U ∧ |D.initial i| ≤ P.U
  rhs_bound : ∀ j, |D.rhs j| ≤ P.U
  matrix_dyadic : ∀ i j, DyadicValue (D.rows.matrix i j)
  coordinate_dyadic : ∀ i, Used i → DyadicValue (D.lower i) ∧ DyadicValue (D.upper i) ∧
    DyadicValue (D.cost i) ∧ DyadicValue (D.initial i)
  rhs_dyadic : ∀ j, DyadicValue (D.rhs j)

/-- Only honest multiplicities and supplied starting feasibility/slack are promised. -/
structure HonestInput (G : DiGraph (Fin n)) (D : Data n m) (P : Envelope) : Prop where
  multiplicity : ∀ u v, (G.sym u v : ℝ) ≤ P.C
  initial_feasible : (matrix G D.rows)ᵀ *ᵥ vec G D.initial = D.rhs
  initial_lower : ∀ i, 1 / P.U ≤ vec G D.initial i - vec G D.lower i
  initial_upper : ∀ i, 1 / P.U ≤ vec G D.upper i - vec G D.initial i

theorem rowIndex_used {G : DiGraph (Fin n)} (r : Row G m) : Used (rowIndex r) := by
  rcases r with ⟨p, k⟩ | j
  · exact p.2
  · trivial

theorem original_row_count {G : DiGraph (Fin n)} {D : Data n m} {P : Envelope}
    (H : PublicHyp D P) (HG : HonestInput G D P) : (rowCount G m : ℝ) ≤ P.Mbar :=
  (rowCount_le G HG.multiplicity).trans H.rows_bound

/-- The general objective l1 norm has no terminal-specific coefficient. -/
theorem objective_l1 {G : DiGraph (Fin n)} {D : Data n m} {P : Envelope}
    (H : PublicHyp D P) (HG : HonestInput G D P) :
    (∑ i, |vec G D.cost i|) ≤ P.Mbar * P.U := by
  have hU : 0 ≤ P.U := by linarith [H.U_ge]
  calc
    _ ≤ ∑ _i : Fin (rowCount G m), P.U := by
      apply sum_le_sum
      intro i _
      exact (H.coordinate_bound _ (rowIndex_used ((rowEquiv G m).symm i))).2.2.1
    _ = (rowCount G m : ℝ) * P.U := by simp
    _ ≤ P.Mbar * P.U := mul_le_mul_of_nonneg_right (original_row_count H HG) hU

/-- The public Lewis floor for arbitrary nonzero explicit rows. -/
def qStar (a0 Mbar U sst : ℝ) : ℝ := a0 ^ 2 * sst ^ 2 / (8 * Mbar * U ^ 2)
def restartLog (a0 Mbar U sst : ℝ) : ℝ := Real.log (1 / qStar a0 Mbar U sst)

theorem qStar_pos {a0 Mbar U sst : ℝ} (ha0 : 0 < a0) (hM : 0 < Mbar)
    (hU : 0 < U) (hs : 0 < sst) : 0 < qStar a0 Mbar U sst := by
  unfold qStar
  positivity

/-- Derive the public floor from the generic Lewis theorem and original row norms. -/
theorem lewis_floor_public (G : DiGraph (Fin n)) (E : ExplicitRows n m)
    (hn : 0 < n) {a0 Mbar U sst p : ℝ} (ha0 : 0 < a0) (ha1 : a0 ≤ 1)
    (hrows : ∀ j, a0 ^ 2 ≤ ∑ v, E.matrix j v ^ 2 ∧ ∑ v, E.matrix j v ^ 2 ≤ 2)
    (hMbar : (rowCount G m : ℝ) ≤ Mbar) (hU : 0 < U) (hsst : 0 < sst)
    (S sl : Fin (rowCount G m) → ℝ) (hSlo : ∀ i, 1 / U ≤ S i)
    (hShi : ∀ i, S i ≤ 2 / sl i) (hsl : ∀ i, sst ≤ sl i)
    (hp0 : 0 < p) (hp2 : p < 2) (i : Fin (rowCount G m)) :
    qStar a0 Mbar U sst ≤
      exp (lewisLog p (diagonal (fun i => (S i)⁻¹) * matrix G E) i) := by
  let A := matrix G E
  let B := diagonal (fun i => (S i)⁻¹) * A
  have hM := rowCount_pos G E hn
  have hMr : (0 : ℝ) < rowCount G m := by exact_mod_cast hM
  have hMb : 0 < Mbar := hMr.trans_le hMbar
  have hS : ∀ i, 0 < S i := fun i => (one_div_pos.mpr hU).trans_le (hSlo i)
  have hA := det_ne_zero_of_idRows (matrix_idRows G E)
  have hB : (Bᵀ * B).det ≠ 0 := diag_det hA (fun i => inv_ne_zero (hS i).ne')
  have hrowB : ∀ i, B i ≠ 0 := fun i hzero => by
    apply matrix_row_ne_zero G E ha0 ha1 hrows i
    funext j
    have hz := congrFun hzero j
    simp only [B, diagonal_mul, Pi.zero_apply] at hz
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (hS i).ne')
  have hlo : ∀ i, a0 ^ 2 ≤ euc (A i) ^ 2 := fun i => by
    rw [euc_sq]
    exact (matrix_row_bounds G E ha0.le ha1 hrows i).1
  have hhi : ∀ i, euc (A i) ^ 2 ≤ 2 := fun i => by
    rw [euc_sq]
    exact (matrix_row_bounds G E ha0.le ha1 hrows i).2
  have hf := lewis_floor_qstar hB hrowB hp0 hp2 hM ha0 hU hsst hlo hhi hSlo hShi hsl i
  refine le_trans ?_ hf
  unfold qStar
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)

/-- Fixed final centrality for the general objective bound. -/
def finalGoal (Mbar U ε : ℝ) : ℝ := ε / (8 * Mbar * U ^ 2)

theorem finalGoal_pos {Mbar U ε : ℝ} (hM : 0 < Mbar) (hU : 0 < U) (hε : 0 < ε) :
    0 < finalGoal Mbar U ε := by unfold finalGoal; positivity

/-- The public target discharges the actual general objective error term. -/
theorem final_error_le {M : ℕ} (c : Fin M → ℝ) {Mbar U ε d : ℝ}
    (hM : 0 < Mbar) (hU : 0 < U) (hε : 0 < ε)
    (hc : (∑ i, |c i|) ≤ Mbar * U) (hd : 0 ≤ d) (hdgoal : d ≤ finalGoal Mbar U ε) :
    (∑ i, |c i|) * (4 * U * d) ≤ ε / 2 := by
  calc
    _ ≤ (Mbar * U) * (4 * U * finalGoal Mbar U ε) :=
      mul_le_mul hc (by gcongr) (by positivity) (by positivity)
    _ = ε / 2 := by unfold finalGoal; field_simp [hM.ne', hU.ne']; ring

/-- Finite public final-centering count; no state enters its definition. -/
def finalCount (Mbar U ε Δ : ℝ) : ℕ := iters (finalGoal Mbar U ε / Δ)

theorem finalCount_reaches {Mbar U ε Δ : ℝ} (hM : 0 < Mbar) (hU : 0 < U)
    (hε : 0 < ε) (hΔ : 0 < Δ) :
    (1 / 2 : ℝ) ^ finalCount Mbar U ε Δ * Δ ≤ finalGoal Mbar U ε := by
  have hgoal := finalGoal_pos hM hU hε
  have hi := half_pow_iters_le (div_pos hgoal hΔ)
  exact (mul_le_mul_of_nonneg_right hi hΔ.le).trans_eq (div_mul_cancel₀ _ hΔ.ne')

#print axioms original_row_count
#print axioms objective_l1
#print axioms lewis_floor_public
#print axioms final_error_le
#print axioms finalCount_reaches

end
end CutQueryComplexity.ImplicitLP.GenericQuery
