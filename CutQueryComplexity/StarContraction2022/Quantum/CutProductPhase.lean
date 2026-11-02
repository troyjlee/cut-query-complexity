import CutQueryComplexity.Quantum.Model
import CutQueryComplexity.Graph.Operations
import CutQueryComplexity.StarContraction2022.Quantum.CoherentTransport
import CutQueryComplexity.StarContraction2022.Quantum.FourierProduct

/-! # Bounded cut-product rows and their exact three-cut character

The graph appears here only in mathematical target definitions and honest-read
identities. The query gadget will be a public routine on finite answer letters.
The routines use checked clean transport and Fourier phase matrices. Three
query/phase/unquery pairs implement the cross-weight character with exactly six
physical native calls. The public circuits contain no graph. Their unitary
construction, query count and clean action hold for arbitrary answer tables;
the interpretation as a graph cross sum uses honest cut replies.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum

noncomputable section

open QuantumQueryComplexity
open scoped Matrix
open Matrix

section GraphAlgebra

variable {V : Type} [Fintype V] [DecidableEq V] {W : ℕ}

/-- The cut-product target is zero inside the queried shore and records total
capacity into the shore at every vertex outside it. -/
def productNat (G : CapacityGraph V W) (z : Finset V) (v : V) : ℕ :=
  if v ∈ z then 0 else ∑ u ∈ z, (G.w v u : ℕ)

/-- Natural cross weight, used to avoid division in a modular answer ring. -/
def crossNat (G : CapacityGraph V W) (L R : Finset V) : ℕ :=
  ∑ v ∈ L, ∑ u ∈ R, (G.w v u : ℕ)

@[simp] theorem productNat_of_mem (G : CapacityGraph V W) (z : Finset V) {v : V}
    (hv : v ∈ z) : productNat G z v = 0 := by
  simp [productNat, hv]

theorem productNat_of_not_mem (G : CapacityGraph V W) (z : Finset V) {v : V}
    (hv : v ∉ z) : productNat G z v = ∑ u ∈ z, (G.w v u : ℕ) := by
  simp [productNat, hv]

@[simp] theorem productNat_empty (G : CapacityGraph V W) (v : V) :
    productNat G ∅ v = 0 := by
  simp [productNat]

@[simp] theorem productNat_univ (G : CapacityGraph V W) (v : V) :
    productNat G Finset.univ v = 0 := by
  simp [productNat]

/-- A public bound for every coordinate of the exact integer target. -/
theorem productNat_le_rowBound (G : CapacityGraph V W) (z : Finset V) (v : V) :
    productNat G z v ≤ W * Fintype.card V := by
  by_cases hv : v ∈ z
  · simp [productNat, hv]
  · rw [productNat_of_not_mem G z hv]
    calc
      (∑ u ∈ z, (G.w v u : ℕ)) ≤ ∑ _u ∈ z, W :=
        Finset.sum_le_sum fun u _ => Nat.le_of_lt_succ (G.w v u).isLt
      _ = z.card * W := by simp
      _ ≤ Fintype.card V * W := Nat.mul_le_mul_right W (Finset.card_le_univ z)
      _ = W * Fintype.card V := Nat.mul_comm _ _

/-- The public zero-capacity boundary needs no recovery queries: every
integer coordinate is forced to zero by the established row bound. -/
theorem productNat_zeroCapacity (G : CapacityGraph V 0) (z : Finset V) (v : V) :
    productNat G z v = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using productNat_le_rowBound G z v

/-- The natural target agrees with the already checked real-weight cross sum. -/
theorem crossNat_cast (G : CapacityGraph V W) (L R : Finset V) :
    (crossNat G L R : ℝ) = G.toWeighted.cross L R := by
  simp [crossNat, WeightedGraph.cross, CapacityGraph.toWeighted]

/-- Every masked row sum is a cross sum between disjoint shores. -/
theorem productNat_sum_eq_crossNat (G : CapacityGraph V W) (S z : Finset V) :
    (∑ v ∈ S, productNat G z v) = crossNat G (S \ z) z := by
  rw [crossNat, Finset.sdiff_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ z <;> simp [productNat, hv]

theorem productNat_sum_cast (G : CapacityGraph V W) (S z : Finset V) :
    (∑ v ∈ S, (productNat G z v : ℝ)) = G.toWeighted.cross (S \ z) z := by
  rw [← Nat.cast_sum, productNat_sum_eq_crossNat, crossNat_cast]

/-- Summing the complete returned vector gives the original cut value. -/
theorem productNat_sum_eq_cut (G : CapacityGraph V W) (z : Finset V) :
    (∑ v, productNat G z v) = G.cut z := by
  have hsum : (∑ v, productNat G z v) = crossNat G zᶜ z := by
    simpa [Finset.compl_eq_univ_sdiff] using productNat_sum_eq_crossNat G Finset.univ z
  have hreal : ((∑ v, productNat G z v : ℕ) : ℝ) = (G.cut z : ℝ) := by
    rw [hsum, crossNat_cast, G.toWeighted.cross_comm, WeightedGraph.cross_compl,
      CapacityGraph.toWeighted_cut]
  exact_mod_cast hreal

/-- The three-cut identity in addition form: no truncated natural subtraction
and no division by two in an even modular ring. -/
theorem crossNat_threeCuts (G : CapacityGraph V W) {L R : Finset V}
    (hLR : Disjoint L R) :
    G.cut (L ∪ R) + 2 * crossNat G L R = G.cut L + G.cut R := by
  have h := G.toWeighted.cross_eq_three_cuts hLR
  rw [← crossNat_cast, CapacityGraph.toWeighted_cut, CapacityGraph.toWeighted_cut,
    CapacityGraph.toWeighted_cut] at h
  have hreal : (G.cut (L ∪ R) : ℝ) + 2 * (crossNat G L R : ℝ) =
      (G.cut L : ℝ) + (G.cut R : ℝ) := by linarith
  exact_mod_cast hreal

/-- The exact real phase identity used by three query/phase/unquery pairs.
Both individual-shore terms remain present, including a coherently chosen R. -/
theorem crossNat_phase_identity (G : CapacityGraph V W) {L R : Finset V}
    (hLR : Disjoint L R) {K : ℕ} (hK : 0 < K) (a : ℝ) :
    a * ((G.cut L : ℝ) + (G.cut R : ℝ) - (G.cut (L ∪ R) : ℝ)) / (2 * (K : ℝ)) =
      a * (crossNat G L R : ℝ) / (K : ℝ) := by
  have hreal : (G.cut (L ∪ R) : ℝ) + 2 * (crossNat G L R : ℝ) =
      (G.cut L : ℝ) + (G.cut R : ℝ) := by
    exact_mod_cast crossNat_threeCuts G hLR
  have hdiff : (G.cut L : ℝ) + (G.cut R : ℝ) - (G.cut (L ∪ R) : ℝ) =
      2 * (crossNat G L R : ℝ) := by linarith
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [hdiff]
  field_simp [hK'] <;> ring

end GraphAlgebra


section WorkRegister

variable {I A D : Type} [Fintype I] [DecidableEq I] [Fintype A]
  [DecidableEq A] [Fintype D] [DecidableEq D]

/-- Public layout with arbitrary quantum controls and a separate physical
index/answer scratch pair. -/
def workBasisEquiv : QBasis I A D ≃ D × (Option I × Option A) where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun p := (p.2.1, p.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Clean physical registers retaining the complete control basis. -/
def workEncode (d : D) : QBasis I A D := (none, none, d)

/-- Coherent control embedding, linear in the entire control state. -/
def workEmbed (ψ : D → ℂ) : QBasis I A D → ℂ :=
  cleanEmbed workBasisEquiv (none, none) ψ

@[simp] theorem workEmbed_encode (ψ : D → ℂ) (d : D) :
    workEmbed (I := I) (A := A) ψ (workEncode d) = ψ d := by
  simp [workEmbed, cleanEmbed_apply, workBasisEquiv, workEncode]

/-- A clean embedded control basis vector is the corresponding complete
physical basis vector, with no amplitude or relative-phase factor. -/
theorem workEmbed_qBasis (d : D) :
    workEmbed (I := I) (A := A) (qBasis d) = qBasis (workEncode d) := by
  funext p
  rcases p with ⟨i, a, c⟩
  by_cases hi : i = none <;> by_cases ha : a = none <;> by_cases hc : c = d <;>
    simp [workEmbed, cleanEmbed_apply, workBasisEquiv, workEncode, qBasis_apply, hi, ha, hc]

theorem workEmbed_of_dirty (ψ : D → ℂ) (p : QBasis I A D)
    (hp : (p.1, p.2.1) ≠ (none, none)) : workEmbed ψ p = 0 := by
  simp [workEmbed, cleanEmbed_apply, workBasisEquiv, hp]

@[simp] theorem qNormSq_workEmbed (ψ : D → ℂ) :
    qNormSq (workEmbed (I := I) (A := A) ψ) = qNormSq ψ :=
  qNormSq_cleanEmbed workBasisEquiv (none, none) ψ

/-- Select an arbitrary public function of all controls. This permutation
retains the controls, so the selected-shore map need not be injective. -/
def selectWork (s : D → I) : Equiv.Perm (QBasis I A D) :=
  Function.Involutive.toPerm
    (fun p => (Equiv.swap none (some (s p.2.2)) p.1, p.2))
    (by rintro ⟨i, a, d⟩; simp)

@[simp] theorem selectWork_apply (s : D → I) (p : QBasis I A D) :
    selectWork s p = (Equiv.swap none (some (s p.2.2)) p.1, p.2) := rfl

@[simp] theorem selectWork_symm_apply (s : D → I) (p : QBasis I A D) :
    (selectWork s).symm p = selectWork s p := rfl

theorem selectWork_involutive (s : D → I) :
    Function.Involutive (selectWork (A := A) s) := by
  rintro ⟨i, a, d⟩
  simp

/-- Querying from the clean scratch pair writes exactly the selected answer,
retaining every coherent control coordinate. -/
theorem selectWork_query_encode (s : D → I) (read : I → A) (d : D) :
    oracleMap read (selectWork s (workEncode d)) = (some (s d), some (read (s d)), d) := by
  simp [workEncode, oracleMap]


/-- The actual two-query schedule around a public middle gate. The later
phase specialization supplies a proved diagonal unitary, without a solver or
oracle correctness premise. -/
def querySandwich (s : D → I) (U : Matrix (QBasis I A D) (QBasis I A D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis I A D) ℂ) : QRoutine I A D where
  len := 2
  step := fun t => if t = 1 then U else qPerm (selectWork s)
  step_unitary := by
    intro t
    split_ifs
    · exact hU
    · exact qPerm_mem_unitaryGroup _

@[simp] theorem querySandwich_len (s : D → I)
    (U : Matrix (QBasis I A D) (QBasis I A D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis I A D) ℂ) :
    (querySandwich s U hU).len = 2 := rfl

theorem querySandwich_run_matrix (s : D → I)
    (U : Matrix (QBasis I A D) (QBasis I A D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis I A D) ℂ) (read : I → A) :
    (querySandwich s U hU).run read =
      qPerm (selectWork s) * (oracleMat read * (U * (oracleMat read * qPerm (selectWork s)))) :=
  rfl

/-- Exact action of the implemented two-query schedule for any public
unitary diagonal. The two oracle calls cancel on every physical basis state,
including dirty scratch; only the middle diagonal amplitude remains. -/
theorem querySandwich_diagonal_run (s : D → I) (coeff : QBasis I A D → ℂ)
    (hcoeff : Matrix.diagonal coeff ∈ Matrix.unitaryGroup (QBasis I A D) ℂ)
    (read : I → A) (ψ : QBasis I A D → ℂ) (p : QBasis I A D) :
    ((querySandwich s (Matrix.diagonal coeff) hcoeff).run read *ᵥ ψ) p =
      coeff (oracleMap read (selectWork s p)) * ψ p := by
  rw [querySandwich_run_matrix]
  simp only [← Matrix.mulVec_mulVec, qPerm_mulVec_apply, selectWork_symm_apply,
    oracleMat_mulVec_apply, Matrix.mulVec_diagonal]
  rw [oracleMap_involutive read, selectWork_involutive s]

/-- The corresponding full coherent clean-subspace identity. No graph or
correct-answer premise is needed; every finite answer table is covered. -/
theorem querySandwich_diagonal_clean (s : D → I) (coeff : QBasis I A D → ℂ)
    (hcoeff : Matrix.diagonal coeff ∈ Matrix.unitaryGroup (QBasis I A D) ℂ)
    (read : I → A) (ψ : D → ℂ) :
    (querySandwich s (Matrix.diagonal coeff) hcoeff).run read *ᵥ workEmbed ψ =
      workEmbed (fun d => coeff (some (s d), some (read (s d)), d) * ψ d) := by
  funext p
  rw [querySandwich_diagonal_run]
  by_cases hp : (p.1, p.2.1) = (none, none)
  · rcases p with ⟨i, a, d⟩
    obtain ⟨hi, ha⟩ := Prod.mk.inj hp
    change i = none at hi
    change a = none at ha
    subst i
    subst a
    change coeff (oracleMap read (selectWork s (workEncode d))) *
      workEmbed ψ (workEncode d) = workEmbed _ (workEncode d)
    rw [selectWork_query_encode, workEmbed_encode, workEmbed_encode]
  · rw [workEmbed_of_dirty ψ p hp, mul_zero, workEmbed_of_dirty _ p hp]

/-- Public phase lookup in the native answer register. A blank answer has
zero phase; this convention also defines the gate on the whole physical space. -/
def answerPhase (phase : D → A → ℝ) (p : QBasis I A D) : ℝ :=
  p.2.1.elim 0 (phase p.2.2)

/-- An actual two-query phase gadget with a fully specified public middle
unitary, rather than a promised product or phase oracle. -/
def queryPhase (s : D → I) (phase : D → A → ℝ) : QRoutine I A D :=
  querySandwich s (phaseMatrix (answerPhase (I := I) phase))
    (phaseMatrix_mem_unitaryGroup (answerPhase (I := I) phase))

@[simp] theorem queryPhase_len (s : D → I) (phase : D → A → ℝ) :
    (queryPhase s phase).len = 2 := rfl

/-- The entire control state receives its selected-answer phase coherently,
while both physical scratch registers return to blank, for every answer table. -/
theorem queryPhase_run (s : D → I) (phase : D → A → ℝ) (read : I → A)
    (ψ : D → ℂ) :
    (queryPhase s phase).run read *ᵥ workEmbed ψ =
      workEmbed (fun d => cexp1 (phase d (read (s d))) * ψ d) := by
  exact querySandwich_diagonal_clean s
    (fun p => cexp1 (answerPhase phase p))
    (phaseMatrix_mem_unitaryGroup (answerPhase (I := I) phase)) read ψ

/-- A public unitary on all controls, with both physical query registers as
spectators. It is an actual zero-query routine. -/
def workGate (U : Matrix D D ℂ) (hU : U ∈ Matrix.unitaryGroup D ℂ) :
    QRoutine I A D :=
  QRoutine.ofUnitary (kronLift workBasisEquiv U) (kronLift_mem_unitaryGroup _ hU)

@[simp] theorem workGate_len (U : Matrix D D ℂ)
    (hU : U ∈ Matrix.unitaryGroup D ℂ) :
    (workGate (I := I) (A := A) U hU).len = 0 := rfl

theorem workGate_run (U : Matrix D D ℂ) (hU : U ∈ Matrix.unitaryGroup D ℂ)
    (read : I → A) (ψ : D → ℂ) :
    (workGate U hU).run read *ᵥ workEmbed ψ = workEmbed (U *ᵥ ψ) := by
  rw [workGate, QRoutine.ofUnitary_run]
  exact kronLift_cleanEmbed workBasisEquiv (none, none) U ψ

/-- Free control permutations act exactly on clean physical basis states. -/
theorem workGate_perm_run (e : Equiv.Perm D) (read : I → A) (d : D) :
    (workGate (qPerm e) (qPerm_mem_unitaryGroup e)).run read *ᵥ qBasis (workEncode d) =
      qBasis (workEncode (e d)) := by
  rw [← workEmbed_qBasis, workGate_run, qPerm_mulVec_qBasis, workEmbed_qBasis]

/-- A checked forward-state identity can be reversed by the implemented
routine inverse, which has exactly the same physical query count. -/
theorem routine_inverse_of_image (R : QRoutine I A D) (read : I → A)
    (ψ φ : QBasis I A D → ℂ) (h : R.run read *ᵥ ψ = φ) :
    R.inv.run read *ᵥ φ = ψ := by
  rw [QRoutine.inv_run, ← h, Matrix.mulVec_mulVec,
    conjTranspose_mul_self_of_unitary (R.run_mem_unitaryGroup read), Matrix.one_mulVec]

end WorkRegister


section CrossPhase

variable {D : Type} [Fintype D] [DecidableEq D]

/-- Three query/phase/unquery pairs, including the R-cut term even when R is
part of a coherent control. The constructor is defined for all public K;
positivity and disjointness enter only the honest cross-sum theorem. -/
def crossPhase (n W K : ℕ) (L R : D → Finset (Fin n)) (a : D → ℝ) :
    QRoutine (Finset (Fin n)) (CutAnswer n W) D :=
  let left := queryPhase L
    (fun d (ans : CutAnswer n W) => a d * ((ans : ℕ) : ℝ) / (2 * (K : ℝ)))
  let right := queryPhase R
    (fun d (ans : CutAnswer n W) => a d * ((ans : ℕ) : ℝ) / (2 * (K : ℝ)))
  let union := queryPhase (fun d => L d ∪ R d)
    (fun d (ans : CutAnswer n W) => -a d * ((ans : ℕ) : ℝ) / (2 * (K : ℝ)))
  (left.comp right).comp union


/-- Exact physical call count, independent of the answer table. -/
@[simp] theorem crossPhase_len (n W K : ℕ) (L R : D → Finset (Fin n)) (a : D → ℝ) :
    (crossPhase n W K L R a).len = 6 := by
  simp [crossPhase]

/-- Exact coherent three-cut phase and physical cleanup for arbitrary finite
answer tables; no graph consistency or success event is assumed. -/
theorem crossPhase_run_read (n W K : ℕ) (L R : D → Finset (Fin n)) (a : D → ℝ)
    (read : Finset (Fin n) → CutAnswer n W) (ψ : D → ℂ) :
    (crossPhase n W K L R a).run read *ᵥ workEmbed ψ =
      workEmbed (fun d =>
        cexp1 (a d * (((read (L d) : ℕ) : ℝ) + ((read (R d) : ℕ) : ℝ) -
          ((read (L d ∪ R d) : ℕ) : ℝ)) / (2 * (K : ℝ))) * ψ d) := by
  simp only [crossPhase, QRoutine.comp_run, ← Matrix.mulVec_mulVec]
  rw [queryPhase_run, queryPhase_run, queryPhase_run]
  apply congrArg (workEmbed (I := Finset (Fin n)) (A := CutAnswer n W))
  funext d
  rw [← mul_assoc, ← mul_assoc, ← cexp1_add, ← cexp1_add]
  congr 2
  ring

/-- On honest graph replies, the implemented public circuit gives the exact
cross-weight character with clean scratch and without a control-dependent
extra phase. This identity holds for every control superposition. -/
theorem crossPhase_run {n W K : ℕ} (hK : 0 < K) (L R : D → Finset (Fin n))
    (a : D → ℝ) (hLR : ∀ d, Disjoint (L d) (R d))
    (G : CapacityGraph (Fin n) W) (ψ : D → ℂ) :
    (crossPhase n W K L R a).run (capacityRead G) *ᵥ workEmbed ψ =
      workEmbed (fun d => cexp1 (a d * (crossNat G (L d) (R d) : ℝ) / (K : ℝ)) * ψ d) := by
  rw [crossPhase_run_read]
  apply congrArg (workEmbed (I := Finset (Fin n)) (A := CutAnswer n W))
  funext d
  simp only [capacityRead_val]
  rw [crossNat_phase_identity G (hLR d) hK (a d)]

end CrossPhase

#print axioms productNat_le_rowBound
#print axioms productNat_sum_eq_crossNat
#print axioms productNat_sum_cast
#print axioms productNat_sum_eq_cut
#print axioms crossNat_threeCuts
#print axioms crossNat_phase_identity
#print axioms qNormSq_workEmbed
#print axioms selectWork_query_encode
#print axioms querySandwich_len
#print axioms querySandwich_run_matrix
#print axioms querySandwich_diagonal_clean
#print axioms queryPhase_len
#print axioms queryPhase_run
#print axioms workGate_run
#print axioms workGate_perm_run
#print axioms routine_inverse_of_image
#print axioms crossPhase_len
#print axioms crossPhase_run_read
#print axioms crossPhase_run

end

end CutQueryComplexity.StarContraction2022.Quantum
