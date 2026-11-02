import QuantumQueryComplexity.Quantum.Oracle
import Mathlib.Data.ZMod.Basic

/-! # Two-query simulations of native and modular-addition value access

The native oracle swaps a blank symbol with the answer. A conventional value
oracle adds the answer into a finite additive register. Both simulations below
restore their scratch register and hold on arbitrary superpositions, not just
classical transcripts. An inverse addition query is explicitly charged.
-/

namespace CutQueryComplexity.Encoding

noncomputable section

open QuantumQueryComplexity
open scoped Matrix

variable {I A W : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
  [AddCommGroup A] [Fintype W] [DecidableEq W]

/-- Basis of a value oracle with an additive answer register and an idle index. -/
abbrev AddBasis (I A W : Type) := Option I × A × W

/-- Reversible addition of the whole answer symbol; subtraction is the inverse. -/
def addOracle (a : I → A) : Equiv.Perm (AddBasis I A W) where
  toFun p := match p.1 with
    | none => p
    | some i => (some i, p.2.1 + a i, p.2.2)
  invFun p := match p.1 with
    | none => p
    | some i => (some i, p.2.1 - a i, p.2.2)
  left_inv := by rintro ⟨(_ | i), r, w⟩ <;> simp
  right_inv := by rintro ⟨(_ | i), r, w⟩ <;> simp

/-- Addition access is a unitary permutation oracle. -/
theorem addOracle_unitary (a : I → A) :
    qPerm (addOracle (W := W) a) ∈ Matrix.unitaryGroup (AddBasis I A W) ℂ :=
  qPerm_mem_unitaryGroup _

/-- Input-independent addition controlled by the native scratch answer. -/
def shift : Equiv.Perm (QBasis I A (A × W)) where
  toFun p := match p.2.1 with
    | none => p
    | some s => (p.1, some s, p.2.2.1 + s, p.2.2.2)
  invFun p := match p.2.1 with
    | none => p
    | some s => (p.1, some s, p.2.2.1 - s, p.2.2.2)
  left_inv := by rintro ⟨i, (_ | s), r, w⟩ <;> simp
  right_inv := by rintro ⟨i, (_ | s), r, w⟩ <;> simp

/-- Insert a blank native scratch answer next to the additive target register. -/
def blankNative (p : AddBasis I A W) : QBasis I A (A × W) :=
  (p.1, none, p.2)

/-- Query, add the obtained value, and unquery: two native queries, clean scratch. -/
theorem native_add_native (a : I → A) (p : AddBasis I A W) :
    oracleMap a (shift (oracleMap a (blankNative p))) = blankNative (addOracle a p) := by
  rcases p with ⟨(_ | i), r, w⟩
  · rfl
  · simp [blankNative, oracleMap, shift, addOracle]

/-- The same two native queries implement inverse addition. -/
theorem native_sub_native (a : I → A) (p : AddBasis I A W) :
    oracleMap a (shift.symm (oracleMap a (blankNative p))) =
      blankNative ((addOracle a).symm p) := by
  rcases p with ⟨(_ | i), r, w⟩
  · rfl
  · simp [blankNative, oracleMap, shift, addOracle]

/-- Swap the target blank with the answer held in the additive scratch register. -/
def swapStored : Equiv.Perm (AddBasis I A (Option A × W)) :=
  Function.Involutive.toPerm (fun p => match p.1 with
    | none => p
    | some i => (some i, p.2.1, Equiv.swap none (some p.2.1) p.2.2.1, p.2.2.2))
    (by rintro ⟨(_ | i), s, r, w⟩ <;> simp)

@[simp] theorem swapStored_some (i : I) (s : A) (r : Option A) (w : W) :
    swapStored (some i, s, r, w) = (some i, s, Equiv.swap none (some s) r, w) := rfl

@[simp] theorem swapStored_none (s : A) (r : Option A) (w : W) :
    swapStored (none, s, r, w) = ((none, s, r, w) : AddBasis I A (Option A × W)) := rfl

/-- Insert a zero additive scratch register next to the native target answer. -/
def zeroAdd (p : QBasis I A W) : AddBasis I A (Option A × W) :=
  (p.1, 0, p.2)

/-- One forward and one inverse addition query implement a native query with clean scratch. -/
theorem add_swap_sub (a : I → A) (p : QBasis I A W) :
    (addOracle a).symm (swapStored (addOracle a (zeroAdd p))) = zeroAdd (oracleMap a p) := by
  rcases p with ⟨(_ | i), r, w⟩
  · rfl
  · simp [zeroAdd, addOracle, oracleMap]

/-- Linear extension of a basis embedding, used to state clean-ancilla identities. -/
def embed {H K : Type} [Fintype H] [DecidableEq K] (f : H → K) (ψ : H → ℂ) : K → ℂ :=
  ∑ h, ψ h • qBasis (f h)

theorem embed_perm {H K : Type} [Fintype H] [DecidableEq H] [DecidableEq K]
    (f : H → K) (e : Equiv.Perm H) (ψ : H → ℂ) :
    embed f (qPerm e *ᵥ ψ) = ∑ h, ψ h • qBasis (f (e h)) := by
  rw [embed, qPerm_mulVec]
  change (∑ h, ψ (e.symm h) • qBasis (f h)) = ∑ h, ψ h • qBasis (f (e h))
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (Equiv.sum_comp e (fun h => ψ (e.symm h) • qBasis (f h))).symm

/-- Coherent addition simulation on every input state, restoring the native scratch to blank. -/
theorem native_simulates_add (a : I → A) (ψ : AddBasis I A W → ℂ) :
    oracleMat a *ᵥ (qPerm shift *ᵥ (oracleMat a *ᵥ embed blankNative ψ)) =
      embed blankNative (qPerm (addOracle a) *ᵥ ψ) := by
  rw [embed_perm]
  simp only [embed, Matrix.mulVec_sum, Matrix.mulVec_smul, oracleMat_mulVec_qBasis,
    qPerm_mulVec_qBasis, native_add_native]

/-- Coherent inverse-addition simulation, also using two native queries. -/
theorem native_simulates_sub (a : I → A) (ψ : AddBasis I A W → ℂ) :
    oracleMat a *ᵥ (qPerm shift.symm *ᵥ (oracleMat a *ᵥ embed blankNative ψ)) =
      embed blankNative (qPerm (addOracle a).symm *ᵥ ψ) := by
  rw [embed_perm]
  simp only [embed, Matrix.mulVec_sum, Matrix.mulVec_smul, oracleMat_mulVec_qBasis,
    qPerm_mulVec_qBasis, native_sub_native]

/-- Coherent native-oracle simulation, using one forward and one inverse addition query. -/
theorem add_simulates_native (a : I → A) (ψ : QBasis I A W → ℂ) :
    qPerm (addOracle a).symm *ᵥ (qPerm swapStored *ᵥ
      (qPerm (addOracle a) *ᵥ embed zeroAdd ψ)) = embed zeroAdd (oracleMat a *ᵥ ψ) := by
  rw [oracleMat, embed_perm]
  simp only [embed, Matrix.mulVec_sum, Matrix.mulVec_smul, qPerm_mulVec_qBasis,
    add_swap_sub, oraclePerm_apply]

end
end CutQueryComplexity.Encoding
