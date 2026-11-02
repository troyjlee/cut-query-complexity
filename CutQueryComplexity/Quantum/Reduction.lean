import QuantumQueryComplexity.Quantum.Routine

/-! # Coherent substitution of a proved oracle routine

This interface requires an operator identity on the entire finite workspace.
A classical equality of answers alone does not discharge that premise.
The virtual and physical routines here use the same basis; conversions with
extra registers must first provide an appropriate common-space simulation.
-/
namespace CutQueryComplexity.Coherent
open QuantumQueryComplexity
open scoped Matrix
variable {I A W : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
  [Fintype W] [DecidableEq W]

/-- Replace each virtual call in a prefix by the same public physical routine. -/
def substituteUpto (R call : QRoutine I A W) : ℕ → QRoutine I A W
  | 0 => QRoutine.ofUnitary (R.step 0) (R.step_unitary 0)
  | t + 1 => ((substituteUpto R call t).comp call).comp
      (QRoutine.ofUnitary (R.step (t + 1)) (R.step_unitary (t + 1)))

@[simp] theorem substituteUpto_len (R call : QRoutine I A W) (t : ℕ) :
    (substituteUpto R call t).len = t * call.len := by
  induction t with
  | zero => simp [substituteUpto]
  | succ t ih => simp [substituteUpto, ih, Nat.succ_mul]

/-- A coherent oracle identity is preserved across all interleaved input-independent gates. -/
theorem substituteUpto_run (R call : QRoutine I A W) (a b : I → A)
    (hcall : call.run a = oracleMat (W := W) b) (t : ℕ) :
    (substituteUpto R call t).run a = R.runUpto b t := by
  induction t with
  | zero => simp [substituteUpto]
  | succ t ih =>
      simp only [substituteUpto, QRoutine.comp_run, QRoutine.ofUnitary_run, ih, hcall,
        QRoutine.runUpto_succ]

/-- Substitute into the complete routine, with multiplicative query budget. -/
def substitute (R call : QRoutine I A W) : QRoutine I A W := substituteUpto R call R.len

@[simp] theorem substitute_len (R call : QRoutine I A W) :
    (substitute R call).len = R.len * call.len := substituteUpto_len R call R.len

theorem substitute_run (R call : QRoutine I A W) (a b : I → A)
    (hcall : call.run a = oracleMat (W := W) b) :
    (substitute R call).run a = R.run b := substituteUpto_run R call a b hcall R.len

/-- Substitution is valid on arbitrary superpositions, including entangled workspace states. -/
theorem substitute_apply (R call : QRoutine I A W) (a b : I → A)
    (hcall : call.run a = oracleMat (W := W) b) (ψ : QBasis I A W → ℂ) :
    (substitute R call).run a *ᵥ ψ = R.run b *ᵥ ψ := by rw [substitute_run R call a b hcall]

end CutQueryComplexity.Coherent
