import CutQueryComplexity.StarContraction2022.Quantum.CoherentTransport
import QuantumQueryComplexity.Quantum.PostQuery

/-! # Two native queries for public index-dependent answer recoding

The physical registers compute the native answer, a public controlled
transposition writes the tagged answer into the virtual register, and the
second native query clears the scratch. The whole virtual basis is retained,
so the identity holds for arbitrary amplitudes and entangled virtual workspace.
Neither the gates nor the fixed schedule depend on the answer table.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum
noncomputable section
open QuantumQueryComplexity
open scoped Matrix

local instance taggedBasisDecidableEq {I A W : Type} [DecidableEq I]
    [DecidableEq A] [DecidableEq W] : DecidableEq (QBasis I A W) :=
  inferInstanceAs (DecidableEq (Option I × Option A × W))

variable {I A J B W O : Type} [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]

/-- Virtual state followed by the two clean physical query registers. -/
def taggedBasisEquiv : QBasis I A (QBasis J B W) ≃ QBasis J B W × (Option I × Option A) where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun p := (p.2.1, p.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

def taggedEmbed (ψ : QBasis J B W → ℂ) : QBasis I A (QBasis J B W) → ℂ :=
  cleanEmbed taggedBasisEquiv (none, none) ψ

theorem taggedEmbed_norm (ψ : QBasis J B W → ℂ) :
    qNormSq (taggedEmbed (I := I) (A := A) ψ) = qNormSq ψ :=
  qNormSq_cleanEmbed taggedBasisEquiv (none, none) ψ

theorem taggedEmbed_eq_sum (ψ : QBasis J B W → ℂ) :
    taggedEmbed (I := I) (A := A) ψ =
      ∑ p : QBasis J B W, ψ p • qBasis (none, none, p) :=
  splitVec_qBasis_eq_sum taggedBasisEquiv ψ (none, none)

/-- Retaining the virtual index permits any public selection, without injectivity. -/
def taggedSelect (select : J → I) : Equiv.Perm (QBasis I A (QBasis J B W)) :=
  Function.Involutive.toPerm
    (fun p => (Equiv.swap none (p.2.2.1.map select) p.1, p.2))
    (by rintro ⟨i, a, j, b, w⟩; simp)

/-- Public native transposition controlled by the computed physical answer. -/
def taggedCopy (tag : J → A → B) : Equiv.Perm (QBasis I A (QBasis J B W)) :=
  Function.Involutive.toPerm
    (fun p => (p.1, p.2.1, p.2.2.1,
      (match p.2.2.1, p.2.1 with
        | some j, some a => Equiv.swap none (some (tag j a)) p.2.2.2.1
        | _, _ => p.2.2.2.1), p.2.2.2.2))
    (by rintro ⟨i, a, j, b, w⟩; cases j <;> cases a <;> simp)

omit [Fintype I] [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W] in
@[simp] theorem taggedSelect_apply (select : J → I) (p : QBasis I A (QBasis J B W)) :
    taggedSelect select p = (Equiv.swap none (p.2.2.1.map select) p.1, p.2) := rfl

omit [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Fintype J]
  [DecidableEq J] [Fintype B] [Fintype W] [DecidableEq W] in
@[simp] theorem taggedCopy_apply (tag : J → A → B) (p : QBasis I A (QBasis J B W)) :
    taggedCopy tag p = (p.1, p.2.1, p.2.2.1,
      (match p.2.2.1, p.2.1 with
        | some j, some a => Equiv.swap none (some (tag j a)) p.2.2.2.1
        | _, _ => p.2.2.2.1), p.2.2.2.2) := rfl

/-- Compute, controlled copy, uncompute: exactly two physical native calls. -/
def taggedCall (select : J → I) (tag : J → A → B) :
    QRoutine I A (QBasis J B W) where
  len := 2
  step := fun t => if t = 1 then qPerm (taggedCopy tag) else qPerm (taggedSelect select)
  step_unitary := fun t => by split_ifs <;> exact qPerm_mem_unitaryGroup _

@[simp] theorem taggedCall_len (select : J → I) (tag : J → A → B) :
    (taggedCall (W := W) select tag).len = 2 := rfl

theorem taggedCall_run_matrix (select : J → I) (tag : J → A → B) (read : I → A) :
    (taggedCall (W := W) select tag).run read =
      qPerm (taggedSelect select) * (oracleMat read *
        (qPerm (taggedCopy tag) * (oracleMat read * qPerm (taggedSelect select)))) := by
  simp [taggedCall, QRoutine.run, QRoutine.runUpto]

/-- On each clean basis vector the scratch is cleared and the tagged native
oracle is performed, including the idle virtual-index sector. -/
theorem taggedCall_run_basis (select : J → I) (tag : J → A → B) (read : I → A)
    (p : QBasis J B W) :
    (taggedCall select tag).run read *ᵥ qBasis (none, none, p) =
      qBasis (none, none, oracleMap (fun j => tag j (read (select j))) p) := by
  rw [taggedCall_run_matrix]
  simp only [← Matrix.mulVec_mulVec, qPerm_mulVec_qBasis, oracleMat_mulVec_qBasis]
  congr 1
  rcases p with ⟨j, b, w⟩
  cases j <;> simp [taggedSelect_apply, taggedCopy_apply, oracleMap]

/-- The exact coherent adapter identity, proved from the implemented two-call
routine. No simulation equation or promise about the answer table is assumed. -/
theorem taggedCall_run (select : J → I) (tag : J → A → B) (read : I → A)
    (ψ : QBasis J B W → ℂ) :
    (taggedCall select tag).run read *ᵥ taggedEmbed ψ =
      taggedEmbed (oracleMat (fun j => tag j (read (select j))) *ᵥ ψ) := by
  let b : J → B := fun j => tag j (read (select j))
  have hr : taggedEmbed (I := I) (A := A) (oracleMat b *ᵥ ψ) =
      ∑ p : QBasis J B W, ψ p • qBasis (none, none, oracleMap b p) := by
    rw [taggedEmbed_eq_sum]
    rw [← Equiv.sum_comp (oraclePerm (W := W) b)
      (fun p : QBasis J B W => (oracleMat b *ᵥ ψ) p •
        qBasis ((none, none, p) : QBasis I A (QBasis J B W)))]
    simp only [oraclePerm_apply, oracleMat_mulVec_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [oracleMap_involutive b p]
  rw [hr, taggedEmbed_eq_sum, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, taggedCall_run_basis]
  rfl

theorem taggedCall_normalized (select : J → I) (tag : J → A → B) (read : I → A)
    {ψ : QBasis J B W → ℂ} (hψ : IsQState ψ) :
    IsQState ((taggedCall select tag).run read *ᵥ taggedEmbed ψ) := by
  rw [taggedCall_run]
  apply cleanEmbed_isQState
  exact IsQState.mulVec (oracleMat_mem_unitaryGroup _) hψ

/-- The public circuit replacing every virtual call by the proved adapter. -/
def taggedRoutine (select : J → I) (tag : J → A → B) (R : QRoutine J B W) :
    QRoutine I A (QBasis J B W) :=
  compileClean taggedBasisEquiv (taggedCall select tag) R

@[simp] theorem taggedRoutine_len (select : J → I) (tag : J → A → B)
    (R : QRoutine J B W) : (taggedRoutine select tag R).len = 2 * R.len := by
  simp [taggedRoutine, Nat.mul_comm]

theorem taggedRoutine_run (select : J → I) (tag : J → A → B) (R : QRoutine J B W)
    (read : I → A) (ψ : QBasis J B W → ℂ) :
    (taggedRoutine select tag R).run read *ᵥ taggedEmbed ψ =
      taggedEmbed (R.run (fun j => tag j (read (select j))) *ᵥ ψ) :=
  compileClean_run taggedBasisEquiv (none, none) (taggedCall select tag) R read
    (fun j => tag j (read (select j))) (taggedCall_run select tag read) ψ

theorem taggedRoutine_normalized (select : J → I) (tag : J → A → B)
    (R : QRoutine J B W) (read : I → A) {ψ : QBasis J B W → ℂ}
    (hψ : IsQState ψ) :
    IsQState ((taggedRoutine select tag R).run read *ᵥ taggedEmbed ψ) :=
  IsQState.mulVec ((taggedRoutine select tag R).run_mem_unitaryGroup read)
    (cleanEmbed_isQState taggedBasisEquiv (none, none) hψ)

def taggedAlg (select : J → I) (tag : J → A → B) (T : QAlg J B O W) (q : ℕ) :
    QAlg I A O (QBasis J B W) :=
  compileCleanAlg taggedBasisEquiv (none, none) (taggedCall select tag) T q

theorem taggedAlg_state [DecidableEq O] (select : J → I) (tag : J → A → B)
    (T : QAlg J B O W) (q : ℕ) (read : I → A) :
    (taggedAlg select tag T q).state read (2 * q) =
      taggedEmbed (T.state (fun j => tag j (read (select j))) q) := by
  simpa only [taggedAlg, taggedCall_len, Nat.mul_comm, taggedEmbed] using
    compileCleanAlg_state taggedBasisEquiv (none, none) (taggedCall select tag)
      T q read (fun j => tag j (read (select j))) (taggedCall_run select tag read)

theorem taggedAlg_prob [DecidableEq O] (select : J → I) (tag : J → A → B)
    (T : QAlg J B O W) (q : ℕ) (read : I → A) (o : O) :
    (taggedAlg select tag T q).prob read (2 * q) o =
      T.prob (fun j => tag j (read (select j))) q o := by
  simpa only [taggedAlg, taggedCall_len, Nat.mul_comm] using
    compileCleanAlg_prob taggedBasisEquiv (none, none) (taggedCall select tag)
      T q read (fun j => tag j (read (select j))) (taggedCall_run select tag read) o

#print axioms taggedEmbed_norm
#print axioms taggedCall_len
#print axioms taggedCall_run_basis
#print axioms taggedCall_run
#print axioms taggedCall_normalized
#print axioms taggedRoutine_len
#print axioms taggedRoutine_run
#print axioms taggedRoutine_normalized
#print axioms taggedAlg_state
#print axioms taggedAlg_prob

end
end CutQueryComplexity.StarContraction2022.Quantum
