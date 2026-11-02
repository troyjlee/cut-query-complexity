import CutQueryComplexity.StarContraction2022.Quantum.TaggedQuery
import CutQueryComplexity.Quantum.Model
import CutQueryComplexity.Graph.Directed
import CutQueryComplexity.DirectedCertificate.Basic

/-! A physical four-call adapter for a public function of two outgoing-cut answers.
Every query is charged and all scratch is cleared coherently. -/
set_option autoImplicit false

namespace CutQueryComplexity.Quantum.DirectedReconstruction
noncomputable section
open QuantumQueryComplexity
open CutQueryComplexity.StarContraction2022.Quantum
open scoped Matrix

local instance basisDecidableEq {I A W : Type} [DecidableEq I]
    [DecidableEq A] [DecidableEq W] : DecidableEq (QBasis I A W) :=
  inferInstanceAs (DecidableEq (Option I × Option A × W))

section PairAdapter
variable {I A J B W O : Type} [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]

abbrev PairWork (A J B W : Type) := Option A × QBasis J B W

def pairBasisEquiv : QBasis I A (PairWork A J B W) ≃
    QBasis J B W × (Option I × Option A × Option A) where
  toFun p := (p.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun p := (p.2.1, p.2.2.1, p.2.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

def pairEmbed (ψ : QBasis J B W → ℂ) : QBasis I A (PairWork A J B W) → ℂ :=
  cleanEmbed pairBasisEquiv (none, none, none) ψ

theorem pairEmbed_eq_sum (ψ : QBasis J B W → ℂ) :
    pairEmbed (I := I) (A := A) ψ =
      ∑ p : QBasis J B W, ψ p • qBasis (none, none, none, p) :=
  splitVec_qBasis_eq_sum pairBasisEquiv ψ (none, none, none)

def pairSelect (first : J → I) : Equiv.Perm (QBasis I A (PairWork A J B W)) :=
  Function.Involutive.toPerm
    (fun p => (Equiv.swap none (p.2.2.2.1.map first) p.1, p.2))
    (by rintro ⟨i, a, saved, j, b, w⟩; simp)

def pairSwitch (first second : J → I) :
    Equiv.Perm (QBasis I A (PairWork A J B W)) :=
  Function.Involutive.toPerm
    (fun p => (Equiv.swap (p.2.2.2.1.map first) (p.2.2.2.1.map second) p.1,
      p.2.2.1, p.2.1, p.2.2.2))
    (by rintro ⟨i, a, saved, j, b, w⟩; simp)

def pairCopy (tag : J → A → A → B) :
    Equiv.Perm (QBasis I A (PairWork A J B W)) :=
  Function.Involutive.toPerm
    (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1,
      (match p.2.2.2.1, p.2.2.1, p.2.1 with
       | some j, some a, some a' => Equiv.swap none (some (tag j a a')) p.2.2.2.2.1
       | _, _, _ => p.2.2.2.2.1), p.2.2.2.2.2))
    (by rintro ⟨i, a, saved, j, b, w⟩; cases j <;> cases saved <;> cases a <;> simp)

def pairCall (first second : J → I) (tag : J → A → A → B) :
    QRoutine I A (PairWork A J B W) where
  len := 4
  step t := if t = 2 then qPerm (pairCopy tag)
    else if t = 1 ∨ t = 3 then qPerm (pairSwitch first second)
    else qPerm (pairSelect first)
  step_unitary t := by split_ifs <;> exact qPerm_mem_unitaryGroup _

@[simp] theorem pairCall_len (first second : J → I) (tag : J → A → A → B) :
    (pairCall (W := W) first second tag).len = 4 := rfl

theorem pairCall_run_basis (first second : J → I) (tag : J → A → A → B)
    (read : I → A) (p : QBasis J B W) :
    (pairCall first second tag).run read *ᵥ qBasis (none, none, none, p) =
      qBasis (none, none, none, oracleMap (fun j => tag j (read (first j))
        (read (second j))) p) := by
  simp only [pairCall, QRoutine.run, QRoutine.runUpto]
  norm_num only [show (4 : ℕ) ≠ 2 by decide, show (3 : ℕ) ≠ 2 by decide,
    show (1 : ℕ) ≠ 2 by decide, show (0 : ℕ) ≠ 2 by decide,
    show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 3 by decide,
    show (0 : ℕ) ≠ 1 by decide, show (0 : ℕ) ≠ 3 by decide,
    show (3 : ℕ) ≠ 1 by decide, ↓reduceIte, or_self, or_true, true_or]
  simp only [← Matrix.mulVec_mulVec, qPerm_mulVec_qBasis, oracleMat_mulVec_qBasis]
  congr 1
  rcases p with ⟨j, b, w⟩
  cases j <;> simp [pairSelect, pairSwitch, pairCopy, Function.Involutive.toPerm, oracleMap]

theorem pairCall_run (first second : J → I) (tag : J → A → A → B)
    (read : I → A) (ψ : QBasis J B W → ℂ) :
    (pairCall first second tag).run read *ᵥ pairEmbed ψ =
      pairEmbed (oracleMat (fun j => tag j (read (first j)) (read (second j))) *ᵥ ψ) := by
  let b : J → B := fun j => tag j (read (first j)) (read (second j))
  have hr : pairEmbed (I := I) (A := A) (oracleMat b *ᵥ ψ) =
      ∑ p : QBasis J B W, ψ p • qBasis (none, none, none, oracleMap b p) := by
    rw [pairEmbed_eq_sum]
    rw [← Equiv.sum_comp (oraclePerm (W := W) b)
      (fun p : QBasis J B W => (oracleMat b *ᵥ ψ) p •
        qBasis ((none, none, none, p) : QBasis I A (PairWork A J B W)))]
    simp only [oraclePerm_apply, oracleMat_mulVec_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [oracleMap_involutive b p]
  rw [hr, pairEmbed_eq_sum, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, pairCall_run_basis]
  rfl

def pairRoutine (first second : J → I) (tag : J → A → A → B)
    (R : QRoutine J B W) : QRoutine I A (PairWork A J B W) :=
  compileClean pairBasisEquiv (pairCall first second tag) R

@[simp] theorem pairRoutine_len (first second : J → I) (tag : J → A → A → B)
    (R : QRoutine J B W) : (pairRoutine first second tag R).len = 4 * R.len := by
  simp [pairRoutine, Nat.mul_comm]

theorem pairRoutine_run (first second : J → I) (tag : J → A → A → B)
    (R : QRoutine J B W) (read : I → A) (ψ : QBasis J B W → ℂ) :
    (pairRoutine first second tag R).run read *ᵥ pairEmbed ψ =
      pairEmbed (R.run (fun j => tag j (read (first j)) (read (second j))) *ᵥ ψ) :=
  compileClean_run pairBasisEquiv (none, none, none) (pairCall first second tag) R read
    (fun j => tag j (read (first j)) (read (second j))) (pairCall_run first second tag read) ψ

def pairAlg (first second : J → I) (tag : J → A → A → B)
    (T : QAlg J B O W) (q : ℕ) : QAlg I A O (PairWork A J B W) :=
  compileCleanAlg pairBasisEquiv (none, none, none) (pairCall first second tag) T q

theorem pairAlg_state [DecidableEq O] (first second : J → I)
    (tag : J → A → A → B) (T : QAlg J B O W) (q : ℕ) (read : I → A) :
    (pairAlg first second tag T q).state read (4 * q) =
      pairEmbed (T.state (fun j => tag j (read (first j)) (read (second j))) q) := by
  simpa only [pairAlg, pairCall_len, Nat.mul_comm, pairEmbed] using
    compileCleanAlg_state pairBasisEquiv (none, none, none) (pairCall first second tag)
      T q read (fun j => tag j (read (first j)) (read (second j)))
      (pairCall_run first second tag read)

theorem pairAlg_prob [DecidableEq O] (first second : J → I)
    (tag : J → A → A → B) (T : QAlg J B O W) (q : ℕ) (read : I → A) (o : O) :
    (pairAlg first second tag T q).prob read (4 * q) o =
      T.prob (fun j => tag j (read (first j)) (read (second j))) q o := by
  simpa only [pairAlg, pairCall_len, Nat.mul_comm] using
    compileCleanAlg_prob pairBasisEquiv (none, none, none) (pairCall first second tag)
      T q read (fun j => tag j (read (first j)) (read (second j)))
      (pairCall_run first second tag read) o

end PairAdapter

section UnitOracle
open Finset DirectedCertificate
variable {n : ℕ}

/-- The original directed natural capacities, viewed over the reals. -/
def realGraph (G : DiGraph (Fin n)) : WeightedDiGraph (Fin n) where
  c u v := G.c u v
  nonneg _ _ := Nat.cast_nonneg _
  diag v := by simp [G.diag]

@[simp] theorem realGraph_out (G : DiGraph (Fin n)) (S : Finset (Fin n)) :
    (realGraph G).out S = (G.out S : ℝ) := by
  simp [realGraph, WeightedDiGraph.out, DiGraph.out, DiGraph.arcs]

/-- Directed unit capacities have a public finite whole-answer alphabet. -/
theorem unit_out_le (G : DiGraph (Fin n)) (hG : G.Simple) (S : Finset (Fin n)) :
    G.out S ≤ n * n := by
  calc
    G.out S ≤ ∑ _u ∈ S, ∑ _v ∈ Sᶜ, 1 :=
      sum_le_sum fun u _ => sum_le_sum fun v _ => hG u v
    _ = S.card * Sᶜ.card := by simp
    _ ≤ n * n := Nat.mul_le_mul
      (by simpa using card_le_univ S) (by simpa using card_le_univ Sᶜ)

def unitRead (G : DiGraph (Fin n)) (hG : G.Simple) (S : Finset (Fin n)) :
    CutAnswer n 1 := ⟨G.out S, by simpa using Nat.lt_succ_of_le (unit_out_le G hG S)⟩

@[simp] theorem unitRead_val (G : DiGraph (Fin n)) (hG : G.Simple)
    (S : Finset (Fin n)) : (unitRead G hG S : ℕ) = G.out S := rfl

/-- Antiparallel directed arcs give undirected capacities in `{0,1,2}`. -/
def symCapacity (G : DiGraph (Fin n)) (hG : G.Simple) : CapacityGraph (Fin n) 2 where
  w u v := ⟨G.sym u v, by have h₁ := hG u v; have h₂ := hG v u; simp only [DiGraph.sym]; omega⟩
  symm u v := Fin.ext (G.sym_comm u v)
  diag v := Fin.ext (G.sym_self v)

@[simp] theorem symCapacity_w (G : DiGraph (Fin n)) (hG : G.Simple) (u v : Fin n) :
    ((symCapacity G hG).w u v : ℕ) = G.sym u v := rfl

theorem symCapacity_real (G : DiGraph (Fin n)) (hG : G.Simple) :
    (symCapacity G hG).toWeighted = (realGraph G).sym := by
  ext u v
  simp [CapacityGraph.toWeighted, symCapacity, WeightedDiGraph.sym, realGraph, DiGraph.sym]

theorem symCapacity_cut (G : DiGraph (Fin n)) (hG : G.Simple) (S : Finset (Fin n)) :
    (symCapacity G hG).cut S = G.out S + G.out Sᶜ := by
  change G.symCut S = _
  simp only [DiGraph.symCut, DiGraph.pairs_eq, DiGraph.out, compl_compl]

/-- Total recoding, including arbitrary inconsistent native answer tables. -/
def symTag (_S : Finset (Fin n)) (a b : CutAnswer n 1) : CutAnswer n 2 :=
  ⟨a.val + b.val, by have ha := a.isLt; have hb := b.isLt; simp only [one_mul] at ha hb; simp only [two_mul, add_mul]; omega⟩

def symRead (read : Finset (Fin n) → CutAnswer n 1) (S : Finset (Fin n)) : CutAnswer n 2 :=
  symTag S (read S) (read Sᶜ)

theorem symRead_honest (G : DiGraph (Fin n)) (hG : G.Simple) :
    symRead (unitRead G hG) = capacityRead (symCapacity G hG) := by
  funext S
  apply Fin.ext
  exact (symCapacity_cut G hG S).symm

variable {W O : Type} [Fintype W] [DecidableEq W]

/-- The public four-query symmetrization circuit. -/
def symCall : QRoutine (Finset (Fin n)) (CutAnswer n 1)
    (PairWork (CutAnswer n 1) (Finset (Fin n)) (CutAnswer n 2) W) :=
  pairCall id (fun S => Sᶜ) symTag

@[simp] theorem symCall_len : (symCall (n := n) (W := W)).len = 4 := rfl

theorem symCall_run (read : Finset (Fin n) → CutAnswer n 1)
    (ψ : QBasis (Finset (Fin n)) (CutAnswer n 2) W → ℂ) :
    (symCall (n := n)).run read *ᵥ pairEmbed ψ =
      pairEmbed (oracleMat (symRead read) *ᵥ ψ) :=
  pairCall_run id (fun S => Sᶜ) symTag read ψ

theorem symCall_run_honest (G : DiGraph (Fin n)) (hG : G.Simple)
    (ψ : QBasis (Finset (Fin n)) (CutAnswer n 2) W → ℂ) :
    (symCall (n := n)).run (unitRead G hG) *ᵥ pairEmbed ψ =
      pairEmbed (oracleMat (capacityRead (symCapacity G hG)) *ᵥ ψ) := by
  rw [symCall_run, symRead_honest]

/-- Every reply table preserves normalization; honesty is unnecessary. -/
theorem symCall_normalized (read : Finset (Fin n) → CutAnswer n 1)
    {ψ : QBasis (Finset (Fin n)) (CutAnswer n 2) W → ℂ} (hψ : IsQState ψ) :
    IsQState ((symCall (n := n)).run read *ᵥ pairEmbed ψ) :=
  IsQState.mulVec ((symCall (n := n)).run_mem_unitaryGroup read)
    (cleanEmbed_isQState pairBasisEquiv (none, none, none) hψ)

def symRoutine (R : QRoutine (Finset (Fin n)) (CutAnswer n 2) W) :=
  pairRoutine id (fun S => Sᶜ) symTag R

def symAlg (T : CutQAlg n 2 O W) (q : ℕ) :=
  pairAlg id (fun S => Sᶜ) symTag T q

@[simp] theorem symRoutine_len (R : QRoutine (Finset (Fin n)) (CutAnswer n 2) W) :
    (symRoutine R).len = 4 * R.len := pairRoutine_len _ _ _ _

theorem symRoutine_run (R : QRoutine (Finset (Fin n)) (CutAnswer n 2) W)
    (read : Finset (Fin n) → CutAnswer n 1)
    (ψ : QBasis (Finset (Fin n)) (CutAnswer n 2) W → ℂ) :
    (symRoutine R).run read *ᵥ pairEmbed ψ = pairEmbed (R.run (symRead read) *ᵥ ψ) :=
  pairRoutine_run _ _ _ _ _ _

theorem symAlg_prob [DecidableEq O] (T : CutQAlg n 2 O W) (q : ℕ)
    (G : DiGraph (Fin n)) (hG : G.Simple) (o : O) :
    (symAlg T q).prob (unitRead G hG) (4 * q) o =
      T.prob (capacityRead (symCapacity G hG)) q o := by
  change (pairAlg _ _ _ T q).prob _ _ _ = _
  rw [pairAlg_prob]
  change T.prob (symRead (unitRead G hG)) q o = _
  rw [symRead_honest]

end UnitOracle

#print axioms pairCall_run_basis
#print axioms pairCall_run
#print axioms pairRoutine_len
#print axioms pairRoutine_run
#print axioms pairAlg_state
#print axioms pairAlg_prob
#print axioms unit_out_le
#print axioms symCapacity_real
#print axioms symRead_honest
#print axioms symCall_len
#print axioms symCall_run_honest
#print axioms symCall_normalized
#print axioms symAlg_prob

end
end CutQueryComplexity.Quantum.DirectedReconstruction
