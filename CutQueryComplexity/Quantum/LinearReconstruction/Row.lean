import CutQueryComplexity.StarContraction2022.Quantum.CutProduct

/-! # Physical singleton-row recovery with capacity-only Fourier modulus
The public schedule has six native compute/phase/uncompute calls per bit of W+1.
No graph enters the circuit, initial state, or readout. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace CutQueryComplexity.Quantum.LinearReconstruction
noncomputable section
open QuantumQueryComplexity
open CutQueryComplexity.StarContraction2022.Quantum
open scoped Matrix
open Matrix

def rowBits (W : ℕ) : ℕ := Nat.clog 2 (W + 1)
def rowModulus (W : ℕ) : ℕ := 2 ^ rowBits W
 theorem rowModulus_pos (W : ℕ) : 0 < rowModulus W := pow_pos (by decide) _
theorem capacity_lt_rowModulus (W : ℕ) : W < rowModulus W :=
  (Nat.lt_succ_self W).trans_le (Nat.le_pow_clog (by decide) (W + 1))
abbrev RowAnswer (n W : ℕ) := Fin n → Fin (rowModulus W)
def rowZero (n W : ℕ) : RowAnswer n W := fun _ => ⟨0, rowModulus_pos W⟩
def rowRead {n W : ℕ} (G : CapacityGraph (Fin n) W) (v : Fin n) : RowAnswer n W :=
  fun u => ⟨(G.w u v).val, (Nat.le_of_lt_succ (G.w u v).isLt).trans_lt
    (capacity_lt_rowModulus W)⟩
@[simp] theorem rowRead_val {n W : ℕ} (G : CapacityGraph (Fin n) W) (v u : Fin n) :
    (rowRead G v u).val = (G.w u v).val := rfl
@[simp] theorem productNat_singleton {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (v u : Fin n) : productNat G {v} u = (G.w u v).val := by
  by_cases h : u = v
  · subst u; simp [productNat, G.diag]
  · simp [productNat, h]

section RegisterFourier

variable {I A D : Type} [Fintype I] [DecidableEq I] [Fintype A]
  [DecidableEq A] [Fintype D] [DecidableEq D]

/-- Lift the product Fourier gate while treating the physical query registers
and the complete public control as spectators. -/
def rowRegisterEquiv (n W : ℕ) :
    QBasis I A (D × RowAnswer n W) ≃
      RowAnswer n W × (Option I × Option A × D) where
  toFun p := (p.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun p := (p.2.1, p.2.2.1, p.2.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A product-vector state with a retained control basis and clean physical
scratch. Arbitrary coherent controls follow from the existing basis expansion. -/
def rowRegisterState (n W : ℕ) (d : D) (ψ : RowAnswer n W → ℂ) :
    QBasis I A (D × RowAnswer n W) → ℂ :=
  cleanEmbed (rowRegisterEquiv n W) (none, none, d) ψ

/-- The corresponding control/product state before adding physical scratch.
The retained control is a basis value, while the Fourier register is arbitrary. -/
def rowControlState (n W : ℕ) (d : D) (ψ : RowAnswer n W → ℂ) :
    D × RowAnswer n W → ℂ :=
  fun p => if p.1 = d then ψ p.2 else 0

/-- A diagonal phase preserves the retained control and acts on its whole
Fourier-register state. This algebra does not assume a phase-query primitive. -/
theorem rowControlState_mul (n W : ℕ) (d : D) (ψ : RowAnswer n W → ℂ)
    (f : D × RowAnswer n W → ℂ) :
    (fun p => f p * rowControlState n W d ψ p) =
      rowControlState n W d (fun y => f (d, y) * ψ y) := by
  funext p
  rcases p with ⟨d', y⟩
  by_cases h : d' = d
  · subst d'
    simp [rowControlState]
  · simp [rowControlState, h]

/-- Match the Fourier-register layout to the checked phase gadget's clean
control layout, without discarding any physical or retained-control register. -/
theorem rowRegisterState_eq_workEmbed (n W : ℕ) (d : D)
    (ψ : RowAnswer n W → ℂ) :
    rowRegisterState (I := I) (A := A) n W d ψ =
      workEmbed (rowControlState n W d ψ) := by
  funext p
  rcases p with ⟨i, a, c, y⟩
  by_cases hi : i = none <;> by_cases ha : a = none <;> by_cases hc : c = d <;>
    simp [rowRegisterState, rowControlState, cleanEmbed_apply,
      rowRegisterEquiv, workEmbed, workBasisEquiv, hi, ha, hc]

/-- Forward Fourier is a public zero-query unitary on the actual physical
space; no graph is an input to its construction. -/
def rowFourierGate (n W : ℕ) : QRoutine I A (D × RowAnswer n W) :=
  QRoutine.ofUnitary
    (kronLift (rowRegisterEquiv n W) (productFourier (rowModulus W)))
    (kronLift_mem_unitaryGroup _ (productFourier_mem_unitaryGroup (rowModulus_pos W)))

/-- The inverse Fourier gate also uses zero physical queries. -/
def rowInverseFourierGate (n W : ℕ) : QRoutine I A (D × RowAnswer n W) :=
  QRoutine.ofUnitary
    (kronLift (rowRegisterEquiv n W) ((productFourier (rowModulus W))ᴴ))
    (kronLift_mem_unitaryGroup _
      (conjTranspose_mem_qUnitary (productFourier_mem_unitaryGroup (rowModulus_pos W))))

@[simp] theorem rowFourierGate_len (n W : ℕ) :
    (rowFourierGate (I := I) (A := A) (D := D) n W).len = 0 := rfl

@[simp] theorem rowInverseFourierGate_len (n W : ℕ) :
    (rowInverseFourierGate (I := I) (A := A) (D := D) n W).len = 0 := rfl

/-- Exact forward action with retained controls and scratch. -/
theorem rowFourierGate_run (n W : ℕ) (read : I → A) (d : D)
    (ψ : RowAnswer n W → ℂ) :
    (rowFourierGate n W).run read *ᵥ rowRegisterState n W d ψ =
      rowRegisterState n W d (productFourier (rowModulus W) *ᵥ ψ) := by
  rw [rowFourierGate, QRoutine.ofUnitary_run]
  exact kronLift_cleanEmbed (rowRegisterEquiv n W) (none, none, d) _ ψ

/-- Exact inverse action; together with the checked character-decoding identity
this is the final free gate of the future implemented recovery circuit. -/
theorem rowInverseFourierGate_run (n W : ℕ) (read : I → A) (d : D)
    (ψ : RowAnswer n W → ℂ) :
    (rowInverseFourierGate n W).run read *ᵥ rowRegisterState n W d ψ =
      rowRegisterState n W d ((productFourier (rowModulus W))ᴴ *ᵥ ψ) := by
  rw [rowInverseFourierGate, QRoutine.ofUnitary_run]
  exact kronLift_cleanEmbed (rowRegisterEquiv n W) (none, none, d) _ ψ

/-- The public clean zero/product basis has no extra phase or scale. -/
theorem rowRegisterState_qBasis (n W : ℕ) (d : D) (y : RowAnswer n W) :
    rowRegisterState (I := I) (A := A) n W d (qBasis y) =
      qBasis (none, none, d, y) := by
  funext p
  rcases p with ⟨i, a, c, y'⟩
  by_cases hi : i = none <;> by_cases ha : a = none <;>
      by_cases hc : c = d <;> by_cases hy : y' = y <;>
    simp [rowRegisterState, cleanEmbed_apply, rowRegisterEquiv,
      qBasis_apply, hi, ha, hc, hy]

/-- Forward preparation of the exact uniform product register, with all
physical scratch and the control retained. -/
theorem rowFourierGate_zero (n W : ℕ) (read : I → A) (d : D) :
    (rowFourierGate n W).run read *ᵥ qBasis (none, none, d, rowZero n W) =
      rowRegisterState n W d (fun _ => productUniform (Fin n) (rowModulus W)) := by
  rw [← rowRegisterState_qBasis, rowFourierGate_run, matrix_mulVec_qBasis]
  apply congrArg (rowRegisterState (I := I) (A := A) n W d)
  funext y
  exact productFourier_zero (rowModulus_pos W) y

/-- Exact inverse decoding of a complete character. The actual query loop must
produce this character; this lemma assumes no query or solver primitive. -/
theorem rowInverseFourierGate_decode (n W : ℕ) (read : I → A) (d : D)
    (x : RowAnswer n W) :
    (rowInverseFourierGate n W).run read *ᵥ
      rowRegisterState n W d (fun y =>
        productUniform (Fin n) (rowModulus W) * productPhase x y) =
      qBasis (none, none, d, x) := by
  rw [rowInverseFourierGate_run, productFourier_decode (rowModulus_pos W),
    rowRegisterState_qBasis]

end RegisterFourier

section ProductBitShores

variable {D : Type} [Fintype D] [DecidableEq D]

/-- Public left shore selected by one Fourier-index bit, with the retained
query shore removed. Both the control and Fourier vector remain registers. -/
def rowBitLeft {n W : ℕ} (z : D → Fin n) (b : ℕ)
    (p : D × RowAnswer n W) : Finset (Fin n) :=
  bitShore p.2 b \ {z p.1}

/-- The retained query shore is itself the public right-shore selector. -/
def rowBitRight {n W : ℕ} (z : D → Fin n)
    (p : D × RowAnswer n W) : Finset (Fin n) := {z p.1}

/-- Disjointness for every coherent basis value is constructed by the actual
public maps, rather than supplied as a property of an unknown graph. -/
theorem rowBit_disjoint {n W : ℕ} (z : D → Fin n) (b : ℕ)
    (p : D × RowAnswer n W) :
    Disjoint (rowBitLeft z b p) (rowBitRight z p) := by
  apply Finset.disjoint_left.mpr
  intro v hvL hvR
  exact (Finset.mem_sdiff.mp hvL).2 hvR

end ProductBitShores

section Recovery

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The exact answer-dependent phase of one implemented bit round. All three
cut terms are retained even when the query shore is coherent. -/
def rowBitPhase (n W : ℕ) (z : D → Fin n) (b : ℕ)
    (read : Finset (Fin n) → CutAnswer n W) (p : D × RowAnswer n W) : ℝ :=
  (2 : ℝ) ^ b *
    (((read (rowBitLeft z b p) : ℕ) : ℝ) +
      ((read (rowBitRight z p) : ℕ) : ℝ) -
      ((read (rowBitLeft z b p ∪ rowBitRight z p) : ℕ) : ℝ)) /
    (2 * (rowModulus W : ℝ))

/-- A finite sequence of actual six-query routines. Its index is public and
does not depend on graph replies or a promised solver. -/
def rowPhaseRounds (n W : ℕ) (z : D → Fin n) : ℕ →
    QRoutine (Finset (Fin n)) (CutAnswer n W) (D × RowAnswer n W)
  | 0 => QRoutine.identity
  | t + 1 => (rowPhaseRounds n W z t).comp
      (crossPhase n W (rowModulus W) (rowBitLeft z t)
        (rowBitRight z) (fun _ => (2 : ℝ) ^ t))

@[simp] theorem rowPhaseRounds_len (n W : ℕ) (z : D → Fin n) (t : ℕ) :
    (rowPhaseRounds n W z t).len = 6 * t := by
  induction t with
  | zero => simp [rowPhaseRounds]
  | succ t ih => simp [rowPhaseRounds, ih, Nat.mul_succ]

/-- Complete arbitrary-answer coherent action of the actual finite loop.
Every bit round returns the physical index and answer scratch to blank. -/
theorem rowPhaseRounds_run_read (n W : ℕ) (z : D → Fin n)
    (read : Finset (Fin n) → CutAnswer n W) (t : ℕ)
    (ψ : D × RowAnswer n W → ℂ) :
    (rowPhaseRounds n W z t).run read *ᵥ workEmbed ψ =
      workEmbed (fun p => cexp1 (∑ b ∈ Finset.range t, rowBitPhase n W z b read p) *
        ψ p) := by
  induction t with
  | zero => simp [rowPhaseRounds]
  | succ t ih =>
      rw [rowPhaseRounds, QRoutine.comp_run, ← Matrix.mulVec_mulVec, ih,
        crossPhase_run_read]
      apply congrArg workEmbed
      funext p
      change cexp1 (rowBitPhase n W z t read p) *
        (cexp1 (∑ b ∈ Finset.range t, rowBitPhase n W z b read p) * ψ p) = _
      rw [Finset.sum_range_succ, cexp1_add]
      ring

/-- The honest meaning of each bit-round exponent, proved from the actual
selected disjoint shores and the checked three-cut identity. -/
theorem rowBitPhase_honest {n W : ℕ} (z : D → Fin n)
    (G : CapacityGraph (Fin n) W) (b : ℕ) (p : D × RowAnswer n W) :
    rowBitPhase n W z b (capacityRead G) p =
      (2 : ℝ) ^ b * (crossNat G (rowBitLeft z b p) (rowBitRight z p) : ℝ) /
        (rowModulus W : ℝ) := by
  unfold rowBitPhase
  simp only [capacityRead_val]
  exact crossNat_phase_identity G (rowBit_disjoint z b p)
    (rowModulus_pos W) ((2 : ℝ) ^ b)

/-- Binary reconstruction turns the implemented cut phases into the exact
bounded integer-vector character. There is no residual shore-dependent phase. -/
theorem rowPhaseExponent_honest {n W : ℕ} (z : D → Fin n)
    (G : CapacityGraph (Fin n) W) (p : D × RowAnswer n W) :
    (∑ b ∈ Finset.range (rowBits W), rowBitPhase n W z b (capacityRead G) p) =
      ∑ v, ((p.2 v).val : ℝ) * ((rowRead G (z p.1) v).val : ℝ) /
        (rowModulus W : ℝ) := by
  have hcross (b : ℕ) :
      (crossNat G (rowBitLeft z b p) (rowBitRight z p) : ℝ) =
        ∑ v ∈ bitShore p.2 b, (productNat G {z p.1} v : ℝ) := by
    simp only [rowBitLeft, rowBitRight]
    rw [← productNat_sum_eq_crossNat]
    simp only [Nat.cast_sum]
  have hbits :
      (∑ b ∈ Finset.range (rowBits W),
        (2 : ℝ) ^ b * ∑ v ∈ bitShore p.2 b, (productNat G {z p.1} v : ℝ)) =
        ∑ v, ((p.2 v).val : ℝ) * (productNat G {z p.1} v : ℝ) := by
    simpa only [rowModulus] using
      (bitShore_dot (B := rowBits W) p.2
        (fun v => (productNat G {z p.1} v : ℝ)))
  simp only [productNat_singleton] at hbits
  simp_rw [rowBitPhase_honest, hcross, rowRead_val, productNat_singleton]
  rw [← Finset.sum_div, hbits, Finset.sum_div]

/-- Honest coherent phase action on the entire control/product space. -/
theorem rowPhaseRounds_run {n W : ℕ} (z : D → Fin n)
    (G : CapacityGraph (Fin n) W) (ψ : D × RowAnswer n W → ℂ) :
    (rowPhaseRounds n W z (rowBits W)).run (capacityRead G) *ᵥ workEmbed ψ =
      workEmbed (fun p => productPhase (rowRead G (z p.1)) p.2 * ψ p) := by
  rw [rowPhaseRounds_run_read]
  apply congrArg workEmbed
  funext p
  rw [rowPhaseExponent_honest]
  rfl

/-- The actual public exact-recovery routine: Fourier, every physical bit
phase, inverse Fourier. No hidden graph enters any of its gates. -/
def recoverRow (n W : ℕ) (z : D → Fin n) :
    QRoutine (Finset (Fin n)) (CutAnswer n W) (D × RowAnswer n W) :=
  ((rowFourierGate n W).comp (rowPhaseRounds n W z (rowBits W))).comp
    (rowInverseFourierGate n W)

/-- Every physical query is counted, for every answer table. -/
@[simp] theorem recoverRow_len (n W : ℕ) (z : D → Fin n) :
    (recoverRow n W z).len = 6 * rowBits W := by
  simp [recoverRow]

/-- Exact honest recovery, with retained control and all physical scratch
clean. The equality includes the amplitude and therefore forbids a hidden phase. -/
theorem recoverRow_run_basis {n W : ℕ} (z : D → Fin n)
    (G : CapacityGraph (Fin n) W) (d : D) :
    (recoverRow n W z).run (capacityRead G) *ᵥ
      qBasis (none, none, d, rowZero n W) =
      qBasis (none, none, d, rowRead G (z d)) := by
  rw [recoverRow, QRoutine.comp_run, QRoutine.comp_run,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rowFourierGate_zero,
    rowRegisterState_eq_workEmbed, rowPhaseRounds_run,
    rowControlState_mul, ← rowRegisterState_eq_workEmbed]
  have hphase : (fun y : RowAnswer n W =>
      productPhase (rowRead G (z d)) y * productUniform (Fin n) (rowModulus W)) =
      (fun y => productUniform (Fin n) (rowModulus W) *
        productPhase (rowRead G (z d)) y) := by
    funext y
    exact mul_comm _ _
  rw [hphase, rowInverseFourierGate_decode]

/-- Linear recovery on arbitrary coherent controls and spectators. This is
stronger than measured success on separately chosen classical shores. -/
theorem recoverRow_run_coherent {n W : ℕ} (z : D → Fin n)
    (G : CapacityGraph (Fin n) W) (ψ : D → ℂ) :
    (recoverRow n W z).run (capacityRead G) *ᵥ
      (∑ d, ψ d • qBasis (none, none, d, rowZero n W)) =
      ∑ d, ψ d • qBasis (none, none, d, rowRead G (z d)) := by
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, recoverRow_run_basis]

end Recovery


section Measured

def recoverRowAlg (n W : ℕ) (v : Fin n) :
    CutQAlg n W (RowAnswer n W) (Unit × RowAnswer n W) :=
  (recoverRow n W (fun _ : Unit => v)).toAlg
    (qBasis (none, none, (), rowZero n W)) (isQState_qBasis _) (fun p => p.2.2.2)

theorem recoverRowAlg_state {n W : ℕ} (v : Fin n) (G : CapacityGraph (Fin n) W) :
    (recoverRowAlg n W v).state (capacityRead G) (6 * rowBits W) =
      qBasis (none, none, (), rowRead G v) := by
  unfold recoverRowAlg
  rw [← recoverRow_len n W (fun _ : Unit => v), QRoutine.toAlg_state_len,
    recoverRow_run_basis]

theorem recoverRowAlg_born {n W : ℕ} (v : Fin n) (G : CapacityGraph (Fin n) W)
    (y : RowAnswer n W) :
    (recoverRowAlg n W v).prob (capacityRead G) (6 * rowBits W) y =
      if rowRead G v = y then 1 else 0 := by
  rw [QAlg.prob, recoverRowAlg_state, qProb_qBasis]
  rfl

theorem recoverRowAlg_prob {n W : ℕ} (v : Fin n) (G : CapacityGraph (Fin n) W) :
    (recoverRowAlg n W v).prob (capacityRead G) (6 * rowBits W) (rowRead G v) = 1 := by
  simp [recoverRowAlg_born]

theorem recoverRowAlg_normalized (n W : ℕ) (v : Fin n)
    (read : Finset (Fin n) → CutAnswer n W) (t : ℕ) :
    ∑ y, (recoverRowAlg n W v).prob read t y = 1 :=
  sum_qProb_eq_one ((recoverRowAlg n W v).state_isQState read t) _

@[simp] theorem rowBits_zero : rowBits 0 = 0 := by simp [rowBits]
@[simp] theorem rowBits_one : rowBits 1 = 1 := by decide
@[simp] theorem rowBits_two : rowBits 2 = 2 := by decide
end Measured
#print axioms rowBits
#print axioms rowModulus
#print axioms capacity_lt_rowModulus
#print axioms RowAnswer
#print axioms rowZero
#print axioms rowRead
#print axioms rowRead_val
#print axioms productNat_singleton
#print axioms rowRegisterEquiv
#print axioms rowRegisterState
#print axioms rowControlState
#print axioms rowControlState_mul
#print axioms rowRegisterState_eq_workEmbed
#print axioms rowFourierGate
#print axioms rowInverseFourierGate
#print axioms rowFourierGate_len
#print axioms rowInverseFourierGate_len
#print axioms rowFourierGate_run
#print axioms rowInverseFourierGate_run
#print axioms rowRegisterState_qBasis
#print axioms rowFourierGate_zero
#print axioms rowInverseFourierGate_decode
#print axioms rowBitLeft
#print axioms rowBitRight
#print axioms rowBit_disjoint
#print axioms rowBitPhase
#print axioms rowPhaseRounds
#print axioms rowPhaseRounds_len
#print axioms rowPhaseRounds_run_read
#print axioms rowBitPhase_honest
#print axioms rowPhaseExponent_honest
#print axioms rowPhaseRounds_run
#print axioms recoverRow
#print axioms recoverRow_len
#print axioms recoverRow_run_basis
#print axioms recoverRow_run_coherent
#print axioms recoverRowAlg
#print axioms recoverRowAlg_state
#print axioms recoverRowAlg_born
#print axioms recoverRowAlg_prob
#print axioms recoverRowAlg_normalized
#print axioms rowBits_zero
#print axioms rowBits_one
#print axioms rowBits_two
end
end CutQueryComplexity.Quantum.LinearReconstruction
