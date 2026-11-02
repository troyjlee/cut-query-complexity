import CutQueryComplexity.StarContraction2022.Quantum.CoherentTransport
import CutQueryComplexity.StarContraction2022.Quantum.FourierProduct
import CutQueryComplexity.StarContraction2022.Quantum.CutProductPhase
import QuantumQueryComplexity.Quantum.PostQuery

/-! # Public coherent product-oracle construction

Public Fourier gates and the implemented six-query cross-phase routine recover
the complete bounded product vector. The native simulated oracle then computes,
copies and uncomputes that vector, counting the inverse calls as well. Hidden
graphs occur only in mathematical targets and honest-input correctness proofs.
All circuits are unitary and have their fixed counts for every finite answer
table; integer decoding and vector cleanup use honest graph replies.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum

noncomputable section

open QuantumQueryComplexity
open scoped Matrix
open Matrix

/-- Public finite alphabet for the exact bounded cut-product vector. -/
abbrev ProductAnswer (n W : ℕ) := Fin n → Fin (productModulus n W)

/-- The public initial product register, including the modulus-one boundary. -/
def productZero (n W : ℕ) : ProductAnswer n W :=
  fun _ => ⟨0, productModulus_pos n W⟩

/-- At zero public row bound the exact binary schedule is empty. -/
theorem productBits_of_rowBound_zero {n W : ℕ} (h : W * n = 0) :
    productBits n W = 0 := by
  simp [productBits, h]

/-- The modulus-one alphabet has just its public zero vector, including the
empty-vertex case. This checks the boundary without introducing a query. -/
theorem productAnswer_eq_zero_of_rowBound_zero {n W : ℕ} (h : W * n = 0)
    (y : ProductAnswer n W) : y = productZero n W := by
  funext v
  apply Fin.ext
  change (y v).val = 0
  have hy := (y v).isLt
  have hmod : productModulus n W = 1 := by
    simp [productModulus, productBits_of_rowBound_zero h]
  omega

/-- The bounded mathematical target, used only in correctness specifications.
It is absent from the public circuit, initialization and readout constructors. -/
def productRead {n W : ℕ} (G : CapacityGraph (Fin n) W) (z : Finset (Fin n)) :
    ProductAnswer n W := fun v =>
  ⟨productNat G z v, (by
    have hb : productNat G z v ≤ W * n := by
      simpa only [Fintype.card_fin] using productNat_le_rowBound G z v
    exact hb.trans_lt (rowBound_lt_productModulus n W))⟩

@[simp] theorem productRead_val {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (z : Finset (Fin n)) (v : Fin n) :
    (productRead G z v).val = productNat G z v := rfl

@[simp] theorem productRead_empty {n W : ℕ} (G : CapacityGraph (Fin n) W) :
    productRead G ∅ = productZero n W := by
  funext v
  apply Fin.ext
  simp [productZero]

/-- The exact recovered integer vector also determines the original cut. -/
theorem productRead_sum {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (z : Finset (Fin n)) : (∑ v, (productRead G z v).val) = G.cut z :=
  productNat_sum_eq_cut G z

section RegisterFourier

variable {I A D : Type} [Fintype I] [DecidableEq I] [Fintype A]
  [DecidableEq A] [Fintype D] [DecidableEq D]

/-- Lift the product Fourier gate while treating the physical query registers
and the complete public control as spectators. -/
def productRegisterEquiv (n W : ℕ) :
    QBasis I A (D × ProductAnswer n W) ≃
      ProductAnswer n W × (Option I × Option A × D) where
  toFun p := (p.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun p := (p.2.1, p.2.2.1, p.2.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A product-vector state with a retained control basis and clean physical
scratch. Arbitrary coherent controls follow from the existing basis expansion. -/
def productRegisterState (n W : ℕ) (d : D) (ψ : ProductAnswer n W → ℂ) :
    QBasis I A (D × ProductAnswer n W) → ℂ :=
  cleanEmbed (productRegisterEquiv n W) (none, none, d) ψ

/-- The corresponding control/product state before adding physical scratch.
The retained control is a basis value, while the Fourier register is arbitrary. -/
def productControlState (n W : ℕ) (d : D) (ψ : ProductAnswer n W → ℂ) :
    D × ProductAnswer n W → ℂ :=
  fun p => if p.1 = d then ψ p.2 else 0

/-- A diagonal phase preserves the retained control and acts on its whole
Fourier-register state. This algebra does not assume a phase-query primitive. -/
theorem productControlState_mul (n W : ℕ) (d : D) (ψ : ProductAnswer n W → ℂ)
    (f : D × ProductAnswer n W → ℂ) :
    (fun p => f p * productControlState n W d ψ p) =
      productControlState n W d (fun y => f (d, y) * ψ y) := by
  funext p
  rcases p with ⟨d', y⟩
  by_cases h : d' = d
  · subst d'
    simp [productControlState]
  · simp [productControlState, h]

/-- Match the Fourier-register layout to the checked phase gadget's clean
control layout, without discarding any physical or retained-control register. -/
theorem productRegisterState_eq_workEmbed (n W : ℕ) (d : D)
    (ψ : ProductAnswer n W → ℂ) :
    productRegisterState (I := I) (A := A) n W d ψ =
      workEmbed (productControlState n W d ψ) := by
  funext p
  rcases p with ⟨i, a, c, y⟩
  by_cases hi : i = none <;> by_cases ha : a = none <;> by_cases hc : c = d <;>
    simp [productRegisterState, productControlState, cleanEmbed_apply,
      productRegisterEquiv, workEmbed, workBasisEquiv, hi, ha, hc]

/-- Forward Fourier is a public zero-query unitary on the actual physical
space; no graph is an input to its construction. -/
def productFourierGate (n W : ℕ) : QRoutine I A (D × ProductAnswer n W) :=
  QRoutine.ofUnitary
    (kronLift (productRegisterEquiv n W) (productFourier (productModulus n W)))
    (kronLift_mem_unitaryGroup _ (productFourier_mem_unitaryGroup (productModulus_pos n W)))

/-- The inverse Fourier gate also uses zero physical queries. -/
def productInverseFourierGate (n W : ℕ) : QRoutine I A (D × ProductAnswer n W) :=
  QRoutine.ofUnitary
    (kronLift (productRegisterEquiv n W) ((productFourier (productModulus n W))ᴴ))
    (kronLift_mem_unitaryGroup _
      (conjTranspose_mem_qUnitary (productFourier_mem_unitaryGroup (productModulus_pos n W))))

@[simp] theorem productFourierGate_len (n W : ℕ) :
    (productFourierGate (I := I) (A := A) (D := D) n W).len = 0 := rfl

@[simp] theorem productInverseFourierGate_len (n W : ℕ) :
    (productInverseFourierGate (I := I) (A := A) (D := D) n W).len = 0 := rfl

/-- Exact forward action with retained controls and scratch. -/
theorem productFourierGate_run (n W : ℕ) (read : I → A) (d : D)
    (ψ : ProductAnswer n W → ℂ) :
    (productFourierGate n W).run read *ᵥ productRegisterState n W d ψ =
      productRegisterState n W d (productFourier (productModulus n W) *ᵥ ψ) := by
  rw [productFourierGate, QRoutine.ofUnitary_run]
  exact kronLift_cleanEmbed (productRegisterEquiv n W) (none, none, d) _ ψ

/-- Exact inverse action; together with the checked character-decoding identity
this is the final free gate of the future implemented recovery circuit. -/
theorem productInverseFourierGate_run (n W : ℕ) (read : I → A) (d : D)
    (ψ : ProductAnswer n W → ℂ) :
    (productInverseFourierGate n W).run read *ᵥ productRegisterState n W d ψ =
      productRegisterState n W d ((productFourier (productModulus n W))ᴴ *ᵥ ψ) := by
  rw [productInverseFourierGate, QRoutine.ofUnitary_run]
  exact kronLift_cleanEmbed (productRegisterEquiv n W) (none, none, d) _ ψ

/-- The public clean zero/product basis has no extra phase or scale. -/
theorem productRegisterState_qBasis (n W : ℕ) (d : D) (y : ProductAnswer n W) :
    productRegisterState (I := I) (A := A) n W d (qBasis y) =
      qBasis (none, none, d, y) := by
  funext p
  rcases p with ⟨i, a, c, y'⟩
  by_cases hi : i = none <;> by_cases ha : a = none <;>
      by_cases hc : c = d <;> by_cases hy : y' = y <;>
    simp [productRegisterState, cleanEmbed_apply, productRegisterEquiv,
      qBasis_apply, hi, ha, hc, hy]

/-- Forward preparation of the exact uniform product register, with all
physical scratch and the control retained. -/
theorem productFourierGate_zero (n W : ℕ) (read : I → A) (d : D) :
    (productFourierGate n W).run read *ᵥ qBasis (none, none, d, productZero n W) =
      productRegisterState n W d (fun _ => productUniform (Fin n) (productModulus n W)) := by
  rw [← productRegisterState_qBasis, productFourierGate_run, matrix_mulVec_qBasis]
  apply congrArg (productRegisterState (I := I) (A := A) n W d)
  funext y
  exact productFourier_zero (productModulus_pos n W) y

/-- Exact inverse decoding of a complete character. The actual query loop must
produce this character; this lemma assumes no query or solver primitive. -/
theorem productInverseFourierGate_decode (n W : ℕ) (read : I → A) (d : D)
    (x : ProductAnswer n W) :
    (productInverseFourierGate n W).run read *ᵥ
      productRegisterState n W d (fun y =>
        productUniform (Fin n) (productModulus n W) * productPhase x y) =
      qBasis (none, none, d, x) := by
  rw [productInverseFourierGate_run, productFourier_decode (productModulus_pos n W),
    productRegisterState_qBasis]

end RegisterFourier

section ProductBitShores

variable {D : Type} [Fintype D] [DecidableEq D]

/-- Public left shore selected by one Fourier-index bit, with the retained
query shore removed. Both the control and Fourier vector remain registers. -/
def productBitLeft {n W : ℕ} (z : D → Finset (Fin n)) (b : ℕ)
    (p : D × ProductAnswer n W) : Finset (Fin n) :=
  bitShore p.2 b \ z p.1

/-- The retained query shore is itself the public right-shore selector. -/
def productBitRight {n W : ℕ} (z : D → Finset (Fin n))
    (p : D × ProductAnswer n W) : Finset (Fin n) := z p.1

/-- Disjointness for every coherent basis value is constructed by the actual
public maps, rather than supplied as a property of an unknown graph. -/
theorem productBit_disjoint {n W : ℕ} (z : D → Finset (Fin n)) (b : ℕ)
    (p : D × ProductAnswer n W) :
    Disjoint (productBitLeft z b p) (productBitRight z p) := by
  apply Finset.disjoint_left.mpr
  intro v hvL hvR
  exact (Finset.mem_sdiff.mp hvL).2 hvR

end ProductBitShores

section Recovery

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The exact answer-dependent phase of one implemented bit round. All three
cut terms are retained even when the query shore is coherent. -/
def productBitPhase (n W : ℕ) (z : D → Finset (Fin n)) (b : ℕ)
    (read : Finset (Fin n) → CutAnswer n W) (p : D × ProductAnswer n W) : ℝ :=
  (2 : ℝ) ^ b *
    (((read (productBitLeft z b p) : ℕ) : ℝ) +
      ((read (productBitRight z p) : ℕ) : ℝ) -
      ((read (productBitLeft z b p ∪ productBitRight z p) : ℕ) : ℝ)) /
    (2 * (productModulus n W : ℝ))

/-- A finite sequence of actual six-query routines. Its index is public and
does not depend on graph replies or a promised solver. -/
def productPhaseRounds (n W : ℕ) (z : D → Finset (Fin n)) : ℕ →
    QRoutine (Finset (Fin n)) (CutAnswer n W) (D × ProductAnswer n W)
  | 0 => QRoutine.identity
  | t + 1 => (productPhaseRounds n W z t).comp
      (crossPhase n W (productModulus n W) (productBitLeft z t)
        (productBitRight z) (fun _ => (2 : ℝ) ^ t))

@[simp] theorem productPhaseRounds_len (n W : ℕ) (z : D → Finset (Fin n)) (t : ℕ) :
    (productPhaseRounds n W z t).len = 6 * t := by
  induction t with
  | zero => simp [productPhaseRounds]
  | succ t ih => simp [productPhaseRounds, ih, Nat.mul_succ]

/-- Complete arbitrary-answer coherent action of the actual finite loop.
Every bit round returns the physical index and answer scratch to blank. -/
theorem productPhaseRounds_run_read (n W : ℕ) (z : D → Finset (Fin n))
    (read : Finset (Fin n) → CutAnswer n W) (t : ℕ)
    (ψ : D × ProductAnswer n W → ℂ) :
    (productPhaseRounds n W z t).run read *ᵥ workEmbed ψ =
      workEmbed (fun p => cexp1 (∑ b ∈ Finset.range t, productBitPhase n W z b read p) *
        ψ p) := by
  induction t with
  | zero => simp [productPhaseRounds]
  | succ t ih =>
      rw [productPhaseRounds, QRoutine.comp_run, ← Matrix.mulVec_mulVec, ih,
        crossPhase_run_read]
      apply congrArg workEmbed
      funext p
      change cexp1 (productBitPhase n W z t read p) *
        (cexp1 (∑ b ∈ Finset.range t, productBitPhase n W z b read p) * ψ p) = _
      rw [Finset.sum_range_succ, cexp1_add]
      ring

/-- The honest meaning of each bit-round exponent, proved from the actual
selected disjoint shores and the checked three-cut identity. -/
theorem productBitPhase_honest {n W : ℕ} (z : D → Finset (Fin n))
    (G : CapacityGraph (Fin n) W) (b : ℕ) (p : D × ProductAnswer n W) :
    productBitPhase n W z b (capacityRead G) p =
      (2 : ℝ) ^ b * (crossNat G (productBitLeft z b p) (productBitRight z p) : ℝ) /
        (productModulus n W : ℝ) := by
  unfold productBitPhase
  simp only [capacityRead_val]
  exact crossNat_phase_identity G (productBit_disjoint z b p)
    (productModulus_pos n W) ((2 : ℝ) ^ b)

/-- Binary reconstruction turns the implemented cut phases into the exact
bounded integer-vector character. There is no residual shore-dependent phase. -/
theorem productPhaseExponent_honest {n W : ℕ} (z : D → Finset (Fin n))
    (G : CapacityGraph (Fin n) W) (p : D × ProductAnswer n W) :
    (∑ b ∈ Finset.range (productBits n W), productBitPhase n W z b (capacityRead G) p) =
      ∑ v, ((p.2 v).val : ℝ) * ((productRead G (z p.1) v).val : ℝ) /
        (productModulus n W : ℝ) := by
  have hcross (b : ℕ) :
      (crossNat G (productBitLeft z b p) (productBitRight z p) : ℝ) =
        ∑ v ∈ bitShore p.2 b, (productNat G (z p.1) v : ℝ) := by
    simp only [productBitLeft, productBitRight]
    rw [← productNat_sum_eq_crossNat]
    simp only [Nat.cast_sum]
  have hbits :
      (∑ b ∈ Finset.range (productBits n W),
        (2 : ℝ) ^ b * ∑ v ∈ bitShore p.2 b, (productNat G (z p.1) v : ℝ)) =
        ∑ v, ((p.2 v).val : ℝ) * (productNat G (z p.1) v : ℝ) := by
    simpa only [productModulus] using
      (bitShore_dot (B := productBits n W) p.2
        (fun v => (productNat G (z p.1) v : ℝ)))
  simp_rw [productBitPhase_honest, hcross, productRead_val]
  rw [← Finset.sum_div, hbits, Finset.sum_div]

/-- Honest coherent phase action on the entire control/product space. -/
theorem productPhaseRounds_run {n W : ℕ} (z : D → Finset (Fin n))
    (G : CapacityGraph (Fin n) W) (ψ : D × ProductAnswer n W → ℂ) :
    (productPhaseRounds n W z (productBits n W)).run (capacityRead G) *ᵥ workEmbed ψ =
      workEmbed (fun p => productPhase (productRead G (z p.1)) p.2 * ψ p) := by
  rw [productPhaseRounds_run_read]
  apply congrArg workEmbed
  funext p
  rw [productPhaseExponent_honest]
  rfl

/-- The actual public exact-recovery routine: Fourier, every physical bit
phase, inverse Fourier. No hidden graph enters any of its gates. -/
def recoverProduct (n W : ℕ) (z : D → Finset (Fin n)) :
    QRoutine (Finset (Fin n)) (CutAnswer n W) (D × ProductAnswer n W) :=
  ((productFourierGate n W).comp (productPhaseRounds n W z (productBits n W))).comp
    (productInverseFourierGate n W)

/-- Every physical query is counted, for every answer table. -/
@[simp] theorem recoverProduct_len (n W : ℕ) (z : D → Finset (Fin n)) :
    (recoverProduct n W z).len = 6 * productBits n W := by
  simp [recoverProduct]

/-- Exact honest recovery, with retained control and all physical scratch
clean. The equality includes the amplitude and therefore forbids a hidden phase. -/
theorem recoverProduct_run_basis {n W : ℕ} (z : D → Finset (Fin n))
    (G : CapacityGraph (Fin n) W) (d : D) :
    (recoverProduct n W z).run (capacityRead G) *ᵥ
      qBasis (none, none, d, productZero n W) =
      qBasis (none, none, d, productRead G (z d)) := by
  rw [recoverProduct, QRoutine.comp_run, QRoutine.comp_run,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, productFourierGate_zero,
    productRegisterState_eq_workEmbed, productPhaseRounds_run,
    productControlState_mul, ← productRegisterState_eq_workEmbed]
  have hphase : (fun y : ProductAnswer n W =>
      productPhase (productRead G (z d)) y * productUniform (Fin n) (productModulus n W)) =
      (fun y => productUniform (Fin n) (productModulus n W) *
        productPhase (productRead G (z d)) y) := by
    funext y
    exact mul_comm _ _
  rw [hphase, productInverseFourierGate_decode]

/-- Linear recovery on arbitrary coherent controls and spectators. This is
stronger than measured success on separately chosen classical shores. -/
theorem recoverProduct_run_coherent {n W : ℕ} (z : D → Finset (Fin n))
    (G : CapacityGraph (Fin n) W) (ψ : D → ℂ) :
    (recoverProduct n W z).run (capacityRead G) *ᵥ
      (∑ d, ψ d • qBasis (none, none, d, productZero n W)) =
      ∑ d, ψ d • qBasis (none, none, d, productRead G (z d)) := by
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, recoverProduct_run_basis]

end Recovery

section CopyControl

variable {J Y W : Type} [Fintype J] [DecidableEq J] [Fintype Y]
  [DecidableEq Y] [Fintype W] [DecidableEq W]

/-- Copy a separately computed answer into the native virtual answer register.
The virtual index, virtual workspace, and computed-answer scratch are retained.
On the idle sector the copy is the identity. -/
def copyControl : Equiv.Perm (QBasis J Y W × Y) :=
  Function.Involutive.toPerm
    (fun p => ((p.1.1,
      (match p.1.1 with
        | none => p.1.2.1
        | some _ => Equiv.swap none (some p.2) p.1.2.1), p.1.2.2), p.2))
    (by
      rintro ⟨⟨i, a, w⟩, y⟩
      cases i <;> simp)

@[simp] theorem copyControl_symm_apply (p : QBasis J Y W × Y) :
    (copyControl (J := J) (Y := Y) (W := W)).symm p = copyControl p := rfl

theorem copyControl_involutive :
    Function.Involutive (copyControl (J := J) (Y := Y) (W := W)) := by
  intro p
  simpa only [copyControl_symm_apply] using
    (copyControl (J := J) (Y := Y) (W := W)).symm_apply_apply p

@[simp] theorem copyControl_idle (a : Option Y) (w : W) (y : Y) :
    copyControl (((none, a, w) : QBasis J Y W), y) = ((none, a, w), y) := rfl

@[simp] theorem copyControl_active (j : J) (a : Option Y) (w : W) (y : Y) :
    copyControl (((some j, a, w) : QBasis J Y W), y) =
      ((some j, Equiv.swap none (some y) a, w), y) := rfl

/-- Copying never changes which shore the inverse recovery must use. -/
@[simp] theorem copyControl_index (p : QBasis J Y W × Y) :
    (copyControl p).1.1 = p.1.1 := by
  rcases p with ⟨⟨i, a, w⟩, y⟩
  cases i <;> rfl

@[simp] theorem copyControl_workspace (p : QBasis J Y W × Y) :
    (copyControl p).1.2.2 = p.1.2.2 := by
  rcases p with ⟨⟨i, a, w⟩, y⟩
  cases i <;> rfl

@[simp] theorem copyControl_scratch (p : QBasis J Y W × Y) :
    (copyControl p).2 = p.2 := by
  rcases p with ⟨⟨i, a, w⟩, y⟩
  cases i <;> rfl

/-- With the actual recovered letter present, the public permutation performs
exactly the library's native value-oracle transposition. -/
theorem copyControl_oracle (read : J → Y) (p : QBasis J Y W) (y : Y)
    (hy : ∀ j, p.1 = some j → y = read j) :
    copyControl (p, y) = (oracleMap read p, y) := by
  rcases p with ⟨i, a, w⟩
  cases i with
  | none => rfl
  | some j =>
      have h := hy j rfl
      subst y
      rfl

/-- The copy gate is unitary on the whole space, independently of whether its
scratch contains a correct answer. -/
theorem copyControl_unitary :
    qPerm (copyControl (J := J) (Y := Y) (W := W)) ∈
      Matrix.unitaryGroup (QBasis J Y W × Y) ℂ :=
  qPerm_mem_unitaryGroup _

end CopyControl

/-- Name the standard structural equality decision once per native basis.
This keeps nested physical/virtual register instance search small without
changing the equality decision or any elaborator resource limit. -/
local instance basisDecidableEq {I A D : Type} [DecidableEq I]
    [DecidableEq A] [DecidableEq D] : DecidableEq (QBasis I A D) :=
  inferInstanceAs (DecidableEq (Option I × Option A × D))

/-- The computed-answer register is a public product of the native basis
and its finite answer alphabet, using their standard equality decisions. -/
local instance callWorkspaceDecidableEq {J Y D : Type} [DecidableEq J]
    [DecidableEq Y] [DecidableEq D] : DecidableEq (QBasis J Y D × Y) :=
  inferInstanceAs (DecidableEq ((Option J × Option Y × D) × Y))

section CallLayout

variable {I A J Y W : Type} [Fintype I] [DecidableEq I] [Fintype A]
  [DecidableEq A] [Fintype J] [DecidableEq J] [Fintype Y] [DecidableEq Y]
  [Fintype W] [DecidableEq W]

/-- The public copy permutation lifted to the full physical query space.
Both physical query registers are spectators, and the computed vector remains
available for the inverse recovery. -/
def copyPhysical : Equiv.Perm (QBasis I A (QBasis J Y W × Y)) :=
  Function.Involutive.toPerm
    (fun p => (p.1, p.2.1, copyControl p.2.2))
    (by
      intro p
      change (p.1, p.2.1, copyControl (copyControl p.2.2)) = p
      rw [copyControl_involutive])

@[simp] theorem copyPhysical_apply (p : QBasis I A (QBasis J Y W × Y)) :
    copyPhysical p = (p.1, p.2.1, copyControl p.2.2) := rfl

/-- The copy is an actual public zero-query routine. -/
def copyGate : QRoutine I A (QBasis J Y W × Y) :=
  QRoutine.ofUnitary (qPerm copyPhysical) (qPerm_mem_unitaryGroup _)

@[simp] theorem copyGate_len :
    (copyGate (I := I) (A := A) (J := J) (Y := Y) (W := W)).len = 0 := rfl

/-- Its complete physical basis action, for arbitrary physical answer tables. -/
theorem copyGate_run (read : I → A) (p : QBasis I A (QBasis J Y W × Y)) :
    copyGate.run read *ᵥ qBasis p = qBasis (copyPhysical p) := by
  rw [copyGate, QRoutine.ofUnitary_run, qPerm_mulVec_qBasis]

/-- The proof-only correct-letter condition instantiates the public copy gate
with the exact native virtual oracle action. The eventual recovery circuit
must supply this letter; neither the gate nor its count depends on this proof. -/
theorem copyGate_run_correct (read : I → A) (f : J → Y) (p : QBasis J Y W)
    (y : Y) (hy : ∀ j, p.1 = some j → y = f j) :
    copyGate.run read *ᵥ qBasis ((none, none, p, y) : QBasis I A (QBasis J Y W × Y)) =
      qBasis (none, none, oracleMap f p, y) := by
  rw [copyGate_run, copyPhysical_apply, copyControl_oracle f p y hy]

/-- Final native-oracle layout: retain the entire virtual basis and expose
all physical scratch, including the computed vector, as a separate factor. -/
def productCallBasisEquiv :
    QBasis I A (QBasis J Y W × Y) ≃ QBasis J Y W × (Option I × Option A × Y) where
  toFun p := (p.2.2.1, p.1, p.2.1, p.2.2.2)
  invFun p := (p.2.1, p.2.2.1, p.1, p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The clean embedding to which the existing circuit compiler will apply.
The clean vector is public; the graph-dependent vector never enters this map. -/
def productCallEmbed (zero : Y) (ψ : QBasis J Y W → ℂ) :
    QBasis I A (QBasis J Y W × Y) → ℂ :=
  cleanEmbed productCallBasisEquiv (none, none, zero) ψ

@[simp] theorem productCallEmbed_apply (zero : Y) (ψ : QBasis J Y W → ℂ)
    (p : QBasis J Y W) :
    productCallEmbed (I := I) (A := A) zero ψ (none, none, p, zero) = ψ p := by
  simp [productCallEmbed, cleanEmbed_apply, productCallBasisEquiv]

/-- Every virtual state's norm is retained in the complete physical layout. -/
theorem productCallEmbed_norm (zero : Y) (ψ : QBasis J Y W → ℂ) :
    qNormSq (productCallEmbed (I := I) (A := A) zero ψ) = qNormSq ψ :=
  qNormSq_cleanEmbed productCallBasisEquiv (none, none, zero) ψ

/-- Reuse the existing basis expansion, retaining arbitrary virtual amplitudes
and therefore all coherent relative phases. -/
theorem productCallEmbed_eq_sum (zero : Y) (ψ : QBasis J Y W → ℂ) :
    productCallEmbed (I := I) (A := A) zero ψ =
      ∑ p : QBasis J Y W, ψ p • qBasis (none, none, p, zero) := by
  exact splitVec_qBasis_eq_sum productCallBasisEquiv ψ (none, none, zero)

/-- The complete clean physical basis corresponding to one virtual basis. -/
theorem productCallEmbed_qBasis (zero : Y) (p : QBasis J Y W) :
    productCallEmbed (I := I) (A := A) zero (qBasis p) =
      qBasis (none, none, p, zero) := by
  funext q
  rcases q with ⟨i, a, p', y⟩
  by_cases hi : i = none <;> by_cases ha : a = none <;>
      by_cases hp : p' = p <;> by_cases hy : y = zero <;>
    simp [productCallEmbed, cleanEmbed_apply, productCallBasisEquiv,
      qBasis_apply, hi, ha, hp, hy]

/-- Public clean initialization is a quantum state whenever the virtual
initialization is one; no hidden input appears in this fact. -/
theorem productCallEmbed_isQState (zero : Y) {ψ : QBasis J Y W → ℂ}
    (hψ : IsQState ψ) : IsQState (productCallEmbed (I := I) (A := A) zero ψ) := by
  change qNormSq (productCallEmbed zero ψ) = 1
  rw [productCallEmbed_norm]
  exact hψ

/-- The linear extension needed by the actual clean compiler. The later
implemented recovery/copy/uncompute circuit must prove the basis identity;
this lemma alone supplies no graph oracle or query-cost result. -/
theorem productCall_run_of_basis
    (R : QRoutine I A (QBasis J Y W × Y)) (read : I → A) (f : J → Y) (zero : Y)
    (h : ∀ p : QBasis J Y W,
      R.run read *ᵥ qBasis (none, none, p, zero) =
        qBasis (none, none, oracleMap f p, zero))
    (ψ : QBasis J Y W → ℂ) :
    R.run read *ᵥ productCallEmbed zero ψ =
      productCallEmbed zero (oracleMat f *ᵥ ψ) := by
  have hright : productCallEmbed (I := I) (A := A) zero (oracleMat f *ᵥ ψ) =
      ∑ p : QBasis J Y W, ψ p • qBasis (none, none, oracleMap f p, zero) := by
    rw [productCallEmbed_eq_sum]
    rw [← Equiv.sum_comp (oraclePerm (W := W) f)
      (fun p : QBasis J Y W => (oracleMat f *ᵥ ψ) p •
        qBasis ((none, none, p, zero) : QBasis I A (QBasis J Y W × Y)))]
    simp only [oraclePerm_apply, oracleMat_mulVec_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [oracleMap_involutive f p]
  rw [hright, productCallEmbed_eq_sum, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, h]

end CallLayout

section NativeCall

variable {Work : Type} [Fintype Work] [DecidableEq Work]

/-- An idle virtual query uses the empty shore during recovery. Active queries
retain their exact shore, independent of all answer and workspace registers. -/
def virtualProductShore {n W : ℕ}
    (p : QBasis (Finset (Fin n)) (ProductAnswer n W) Work) : Finset (Fin n) :=
  p.1.getD ∅

/-- A native virtual oracle never changes the recovery shore. This is the
invariant needed to uncompute after the answer-copy permutation. -/
@[simp] theorem virtualProductShore_oracle {n W : ℕ}
    (f : Finset (Fin n) → ProductAnswer n W)
    (p : QBasis (Finset (Fin n)) (ProductAnswer n W) Work) :
    virtualProductShore (oracleMap f p) = virtualProductShore p := by
  rcases p with ⟨i, a, w⟩
  cases i <;> rfl

/-- The actual public native product-oracle simulation. Recovery and its
inverse surround a public copy permutation. Both directions' calls are charged. -/
def productCall (n W : ℕ) (Work : Type) [Fintype Work] [DecidableEq Work] :
    QRoutine (Finset (Fin n)) (CutAnswer n W)
      (QBasis (Finset (Fin n)) (ProductAnswer n W) Work × ProductAnswer n W) :=
  (recoverProduct n W (virtualProductShore (Work := Work))).conjFixed
    (qPerm copyPhysical) (qPerm_mem_unitaryGroup _)

/-- The implemented inverse uses another full recovery budget. The equality
is a property of the public routine, independent of any honest-input premise. -/
@[simp] theorem productCall_len (n W : ℕ) :
    (productCall n W Work).len = 12 * productBits n W := by
  simp only [productCall, QRoutine.conjFixed_len, recoverProduct_len]
  omega

/-- Honest native-oracle basis action, including arbitrary virtual answers,
the idle sector, retained workspace and restoration of every auxiliary register. -/
theorem productCall_run_basis {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (p : QBasis (Finset (Fin n)) (ProductAnswer n W) Work) :
    (productCall n W Work).run (capacityRead G) *ᵥ
      qBasis (none, none, p, productZero n W) =
      qBasis (none, none, oracleMap (productRead G) p, productZero n W) := by
  have hy : ∀ S, p.1 = some S →
      productRead G (virtualProductShore p) = productRead G S := by
    intro S hs
    simp [virtualProductShore, hs]
  simp only [productCall, QRoutine.conjFixed, QRoutine.comp_run,
    QRoutine.ofUnitary_run, ← Matrix.mulVec_mulVec]
  rw [recoverProduct_run_basis, qPerm_mulVec_qBasis, copyPhysical_apply,
    copyControl_oracle (productRead G) p _ hy]
  apply routine_inverse_of_image
  simpa only [virtualProductShore_oracle] using
    recoverProduct_run_basis (virtualProductShore (Work := Work)) G
      (oracleMap (productRead G) p)

/-- Exact coherent simulation on every virtual state. This discharges the
clean compiler's oracle premise using the implemented graph circuit. -/
theorem productCall_run {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (ψ : QBasis (Finset (Fin n)) (ProductAnswer n W) Work → ℂ) :
    (productCall n W Work).run (capacityRead G) *ᵥ productCallEmbed (productZero n W) ψ =
      productCallEmbed (productZero n W) (oracleMat (productRead G) *ᵥ ψ) := by
  exact productCall_run_of_basis (productCall n W Work) (capacityRead G) (productRead G)
    (productZero n W) (productCall_run_basis G) ψ

end NativeCall

section MeasuredRecovery

/-- Public fixed-shore recovery algorithm. The hidden graph is absent from
its routine, basis initialization and product-register readout. -/
def recoverProductAlg (n W : ℕ) (z : Finset (Fin n)) :
    CutQAlg n W (ProductAnswer n W) (Unit × ProductAnswer n W) :=
  (recoverProduct n W (fun _ : Unit => z)).toAlg
    (qBasis (none, none, (), productZero n W)) (isQState_qBasis _)
    (fun p => p.2.2.2)

/-- The honest final state is exactly the recovered-vector basis state. -/
theorem recoverProductAlg_state {n W : ℕ} (z : Finset (Fin n))
    (G : CapacityGraph (Fin n) W) :
    (recoverProductAlg n W z).state (capacityRead G) (6 * productBits n W) =
      qBasis (none, none, (), productRead G z) := by
  unfold recoverProductAlg
  rw [← recoverProduct_len n W (fun _ : Unit => z),
    QRoutine.toAlg_state_len, recoverProduct_run_basis]

/-- Actual measured probability one, with the public algorithm chosen before
every graph input. No recovery, solver, or query-cost premise is supplied. -/
theorem recoverProductAlg_prob {n W : ℕ} (z : Finset (Fin n))
    (G : CapacityGraph (Fin n) W) :
    (recoverProductAlg n W z).prob (capacityRead G) (6 * productBits n W)
      (productRead G z) = 1 := by
  rw [QAlg.prob, recoverProductAlg_state, qProb_qBasis]
  simp [recoverProductAlg, QRoutine.toAlg]

theorem recoverProductAlg_correct (n W : ℕ) (z : Finset (Fin n)) :
    ComputesWithErrorOn (recoverProductAlg n W z) (6 * productBits n W)
      capacityRead (fun G => productRead G z) 0 := by
  intro G
  rw [recoverProductAlg_prob]
  norm_num

/-- Literal program-before-input exact cut-product endpoint with explicit
finite workspace. The query count includes every physical native call. -/
theorem exists_exact_cutProduct (n W : ℕ) (z : Finset (Fin n)) :
    ∃ T : CutQAlg n W (ProductAnswer n W) (Unit × ProductAnswer n W),
      ∀ G : CapacityGraph (Fin n) W,
        T.prob (capacityRead G) (6 * Nat.clog 2 (W * n + 1)) (productRead G z) = 1 := by
  exact ⟨recoverProductAlg n W z, fun G => recoverProductAlg_prob z G⟩

end MeasuredRecovery

section ProductCompiler

variable {O Work : Type} [DecidableEq O] [Fintype Work] [DecidableEq Work]

/-- Substitute actual cut-product calls into a public virtual algorithm.
The graph appears only later, in the exact state and probability theorems. -/
def compileProductAlg (n W : ℕ)
    (T : QAlg (Finset (Fin n)) (ProductAnswer n W) O Work) (q : ℕ) :
    CutQAlg n W O
      (QBasis (Finset (Fin n)) (ProductAnswer n W) Work × ProductAnswer n W) :=
  compileCleanAlg productCallBasisEquiv (none, none, productZero n W)
    (productCall n W Work) T q

/-- The checked coherent call identity is discharged here; no oracle-simulation
or cost assumption is exposed to clients of the graph-specific compiler. -/
theorem compileProductAlg_state {n W : ℕ}
    (T : QAlg (Finset (Fin n)) (ProductAnswer n W) O Work) (q : ℕ)
    (G : CapacityGraph (Fin n) W) :
    (compileProductAlg n W T q).state (capacityRead G) (q * (12 * productBits n W)) =
      productCallEmbed (productZero n W) (T.state (productRead G) q) := by
  simpa only [compileProductAlg, productCall_len, productCallEmbed] using
    compileCleanAlg_state productCallBasisEquiv (none, none, productZero n W)
      (productCall n W Work) T q (capacityRead G) (productRead G) (productCall_run G)

/-- Exact Born-law preservation at the proved physical budget. -/
theorem compileProductAlg_prob {n W : ℕ}
    (T : QAlg (Finset (Fin n)) (ProductAnswer n W) O Work) (q : ℕ)
    (G : CapacityGraph (Fin n) W) (o : O) :
    (compileProductAlg n W T q).prob (capacityRead G) (q * (12 * productBits n W)) o =
      T.prob (productRead G) q o := by
  simpa only [compileProductAlg, productCall_len] using
    compileCleanAlg_prob productCallBasisEquiv (none, none, productZero n W)
      (productCall n W Work) T q (capacityRead G) (productRead G) (productCall_run G) o

/-- Reuse any virtual product-query algorithm without an additional error
term. Its input algorithm is public; the product oracle is actually implemented. -/
theorem compileProductAlg_correct {n W : ℕ}
    (T : QAlg (Finset (Fin n)) (ProductAnswer n W) O Work) (q : ℕ)
    (f : CapacityGraph (Fin n) W → O) (ε : ℝ)
    (hT : ComputesWithErrorOn T q productRead f ε) :
    ComputesWithErrorOn (compileProductAlg n W T q) (q * (12 * productBits n W))
      capacityRead f ε := by
  intro G
  rw [compileProductAlg_prob]
  exact hT G

end ProductCompiler

#print axioms productFourierGate_len
#print axioms productAnswer_eq_zero_of_rowBound_zero
#print axioms productControlState_mul
#print axioms productInverseFourierGate_len
#print axioms productFourierGate_run
#print axioms productInverseFourierGate_run
#print axioms productRegisterState_qBasis
#print axioms productFourierGate_zero
#print axioms productInverseFourierGate_decode
#print axioms productBit_disjoint
#print axioms copyControl_index
#print axioms copyControl_oracle
#print axioms copyControl_unitary
#print axioms copyGate_len
#print axioms copyGate_run_correct
#print axioms productCallEmbed_norm
#print axioms productCallEmbed_qBasis
#print axioms productCall_run_of_basis
#print axioms productRead_sum
#print axioms productRegisterState_eq_workEmbed
#print axioms productPhaseRounds_len
#print axioms productPhaseRounds_run_read
#print axioms productPhaseExponent_honest
#print axioms productPhaseRounds_run
#print axioms recoverProduct_len
#print axioms recoverProduct_run_basis
#print axioms recoverProduct_run_coherent
#print axioms productCall_len
#print axioms productCall_run_basis
#print axioms productCall_run
#print axioms recoverProductAlg_state
#print axioms recoverProductAlg_prob
#print axioms recoverProductAlg_correct
#print axioms exists_exact_cutProduct
#print axioms compileProductAlg_state
#print axioms compileProductAlg_prob
#print axioms compileProductAlg_correct

end

end CutQueryComplexity.StarContraction2022.Quantum
