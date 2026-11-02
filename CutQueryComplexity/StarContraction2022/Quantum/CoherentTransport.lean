import QuantumQueryComplexity.Quantum.KronLift

/-! # Public query maps and clean-subspace circuit transport

The physical and virtual oracle alphabets and workspaces may differ. A public
factorization of the physical basis supplies a clean spectator register. Each
virtual gate is lifted with the existing `kronLift`, and each virtual query is
replaced by an actual physical `QRoutine`. The simulation premise is a coherent
identity on every embedded state, and the compiler preserves that identity.

The concrete index adapter retains the virtual index in workspace. It therefore
needs no injectivity hypothesis on the public map from virtual to physical
indices. Selecting an index, querying once, and undoing the selection gives an
exact one-query simulation for every finite answer table. All constructors are
independent of the oracle. No graph, solver or query-cost premise is built in.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum

noncomputable section

open QuantumQueryComplexity
open scoped Matrix
open Matrix

section Embedding

variable {H K D O : Type} [Fintype H] [DecidableEq H] [Fintype K]
  [DecidableEq K] [Fintype D] [DecidableEq D]

/-- A virtual state with a fixed clean spectator, in a public basis layout. -/
def cleanEmbed (e : H ≃ K × D) (d : D) (ψ : K → ℂ) : H → ℂ :=
  splitVec e ψ (qBasis d)

theorem cleanEmbed_apply (e : H ≃ K × D) (d : D) (ψ : K → ℂ) (p : H) :
    cleanEmbed e d ψ p = ψ (e p).1 * (if (e p).2 = d then 1 else 0) := by
  simp only [cleanEmbed, splitVec_apply, qBasis_apply]

@[simp] theorem qNormSq_cleanEmbed (e : H ≃ K × D) (d : D) (ψ : K → ℂ) :
    qNormSq (cleanEmbed e d ψ) = qNormSq ψ := by
  rw [cleanEmbed, qNormSq_splitVec, qNormSq_qBasis, mul_one]

theorem cleanEmbed_isQState (e : H ≃ K × D) (d : D) {ψ : K → ℂ}
    (hψ : IsQState ψ) : IsQState (cleanEmbed e d ψ) := by
  change qNormSq (cleanEmbed e d ψ) = 1
  rw [qNormSq_cleanEmbed]
  exact hψ

/-- Lifting a virtual gate preserves the same clean register. -/
theorem kronLift_cleanEmbed (e : H ≃ K × D) (d : D) (U : Matrix K K ℂ)
    (ψ : K → ℂ) :
    kronLift e U *ᵥ cleanEmbed e d ψ = cleanEmbed e d (U *ᵥ ψ) :=
  kronLift_mulVec_splitVec e U ψ (qBasis d)

/-- Reading only the virtual factor preserves every outcome probability. -/
theorem qProb_cleanEmbed [DecidableEq O] (e : H ≃ K × D) (d : D)
    (rd : K → O) (ψ : K → ℂ) (o : O) :
    qProb (fun p => rd (e p).1) (cleanEmbed e d ψ) o = qProb rd ψ o := by
  rw [qProb, qProb]
  rw [← Equiv.sum_comp e.symm (fun p : H =>
    if rd (e p).1 = o then Complex.normSq (cleanEmbed e d ψ p) else 0)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : rd k = o <;>
    simp [cleanEmbed, splitVec_apply, qBasis_apply, hk, apply_ite]

end Embedding

section CleanCompiler

variable {I A W J B V D O : Type}
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
  [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B] [Fintype V] [DecidableEq V]
  [Fintype D] [DecidableEq D]

/-- Compile a virtual prefix by alternating lifted gates and the public call. -/
def compileCleanUpto (e : QBasis I A W ≃ QBasis J B V × D)
    (call : QRoutine I A W) (R : QRoutine J B V) : ℕ → QRoutine I A W
  | 0 => QRoutine.ofUnitary (kronLift e (R.step 0))
      (kronLift_mem_unitaryGroup e (R.step_unitary 0))
  | t + 1 => ((compileCleanUpto e call R t).comp call).comp
      (QRoutine.ofUnitary (kronLift e (R.step (t + 1)))
        (kronLift_mem_unitaryGroup e (R.step_unitary (t + 1))))

@[simp] theorem compileCleanUpto_len (e : QBasis I A W ≃ QBasis J B V × D)
    (call : QRoutine I A W) (R : QRoutine J B V) (t : ℕ) :
    (compileCleanUpto e call R t).len = t * call.len := by
  induction t with
  | zero => simp [compileCleanUpto]
  | succ t ih => simp [compileCleanUpto, ih, Nat.succ_mul]

/-- The prefix simulation holds on every virtual state, including a state
entangled with registers already included in the virtual workspace. -/
theorem compileCleanUpto_run (e : QBasis I A W ≃ QBasis J B V × D)
    (d : D) (call : QRoutine I A W) (R : QRoutine J B V)
    (a : I → A) (b : J → B)
    (hcall : ∀ ψ : QBasis J B V → ℂ,
      call.run a *ᵥ cleanEmbed e d ψ = cleanEmbed e d (oracleMat b *ᵥ ψ))
    (t : ℕ) (ψ : QBasis J B V → ℂ) :
    (compileCleanUpto e call R t).run a *ᵥ cleanEmbed e d ψ =
      cleanEmbed e d (R.runUpto b t *ᵥ ψ) := by
  induction t with
  | zero =>
      simp only [compileCleanUpto, QRoutine.ofUnitary_run, QRoutine.runUpto_zero]
      exact kronLift_cleanEmbed e d (R.step 0) ψ
  | succ t ih =>
      simp only [compileCleanUpto, QRoutine.comp_run, QRoutine.ofUnitary_run,
        ← Matrix.mulVec_mulVec]
      rw [ih, hcall, kronLift_cleanEmbed, QRoutine.runUpto_succ]
      simp only [← Matrix.mulVec_mulVec]

/-- A complete public circuit compiler. The input functions occur only in
the simulation theorem, not in this construction. -/
def compileClean (e : QBasis I A W ≃ QBasis J B V × D)
    (call : QRoutine I A W) (R : QRoutine J B V) : QRoutine I A W :=
  compileCleanUpto e call R R.len

@[simp] theorem compileClean_len (e : QBasis I A W ≃ QBasis J B V × D)
    (call : QRoutine I A W) (R : QRoutine J B V) :
    (compileClean e call R).len = R.len * call.len :=
  compileCleanUpto_len e call R R.len

theorem compileClean_run (e : QBasis I A W ≃ QBasis J B V × D)
    (d : D) (call : QRoutine I A W) (R : QRoutine J B V)
    (a : I → A) (b : J → B)
    (hcall : ∀ ψ : QBasis J B V → ℂ,
      call.run a *ᵥ cleanEmbed e d ψ = cleanEmbed e d (oracleMat b *ᵥ ψ))
    (ψ : QBasis J B V → ℂ) :
    (compileClean e call R).run a *ᵥ cleanEmbed e d ψ =
      cleanEmbed e d (R.run b *ᵥ ψ) :=
  compileCleanUpto_run e d call R a b hcall R.len ψ

/-- Compile a fixed public prefix of a whole algorithm. -/
def compileCleanAlg (e : QBasis I A W ≃ QBasis J B V × D) (d : D)
    (call : QRoutine I A W) (T : QAlg J B O V) (q : ℕ) : QAlg I A O W :=
  (compileClean e call (QRoutine.mk q T.step T.step_unitary)).toAlg
    (cleanEmbed e d T.init) (cleanEmbed_isQState e d T.init_isQState)
    (fun p => T.readout (e p).1)

theorem compileCleanAlg_state [DecidableEq O]
    (e : QBasis I A W ≃ QBasis J B V × D) (d : D)
    (call : QRoutine I A W) (T : QAlg J B O V) (q : ℕ)
    (a : I → A) (b : J → B)
    (hcall : ∀ ψ : QBasis J B V → ℂ,
      call.run a *ᵥ cleanEmbed e d ψ = cleanEmbed e d (oracleMat b *ᵥ ψ)) :
    (compileCleanAlg e d call T q).state a (q * call.len) =
      cleanEmbed e d (T.state b q) := by
  let R : QRoutine J B V := ⟨q, T.step, T.step_unitary⟩
  change ((compileClean e call R).toAlg (cleanEmbed e d T.init)
    (cleanEmbed_isQState e d T.init_isQState)
    (fun p => T.readout (e p).1)).state a (R.len * call.len) = _
  rw [← compileClean_len e call R, QRoutine.toAlg_state_len,
    compileClean_run e d call R a b hcall]
  exact congrArg (cleanEmbed e d) (state_eq_runUpto2 T q b q).symm

/-- Exact Born-law preservation by the implemented clean compiler. -/
theorem compileCleanAlg_prob [DecidableEq O]
    (e : QBasis I A W ≃ QBasis J B V × D) (d : D)
    (call : QRoutine I A W) (T : QAlg J B O V) (q : ℕ)
    (a : I → A) (b : J → B)
    (hcall : ∀ ψ : QBasis J B V → ℂ,
      call.run a *ᵥ cleanEmbed e d ψ = cleanEmbed e d (oracleMat b *ᵥ ψ))
    (o : O) :
    (compileCleanAlg e d call T q).prob a (q * call.len) o = T.prob b q o := by
  change qProb (fun p => T.readout (e p).1)
    ((compileCleanAlg e d call T q).state a (q * call.len)) o =
      qProb T.readout (T.state b q) o
  rw [compileCleanAlg_state e d call T q a b hcall, qProb_cleanEmbed]

theorem computesWithErrorOn_compileClean {X : Type} [DecidableEq O]
    (e : QBasis I A W ≃ QBasis J B V × D) (d : D)
    (call : QRoutine I A W) (T : QAlg J B O V) (q : ℕ)
    (read : X → I → A) (read' : X → J → B) (f : X → O) (ε : ℝ)
    (hcall : ∀ x (ψ : QBasis J B V → ℂ),
      call.run (read x) *ᵥ cleanEmbed e d ψ =
        cleanEmbed e d (oracleMat (read' x) *ᵥ ψ))
    (hT : ComputesWithErrorOn T q read' f ε) :
    ComputesWithErrorOn (compileCleanAlg e d call T q) (q * call.len) read f ε := by
  intro x
  rw [compileCleanAlg_prob e d call T q (read x) (read' x) (hcall x)]
  exact hT x

end CleanCompiler

section IndexMap

variable {I J A W O : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype W] [DecidableEq W]

/-- Retain the virtual index in workspace; the physical index is a spectator. -/
def indexBasisEquiv : QBasis I A (Option J × W) ≃ QBasis J A W × Option I where
  toFun p := ((p.2.2.1, p.2.1, p.2.2.2), p.1)
  invFun p := (p.2, p.1.2.1, p.1.1, p.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The physical basis state with the query index parked at idle. -/
def indexEncode (p : QBasis J A W) : QBasis I A (Option J × W) :=
  (none, p.2.1, p.1, p.2.2)

/-- Linear clean embedding for the one-query index simulation. -/
def indexEmbed (ψ : QBasis J A W → ℂ) : QBasis I A (Option J × W) → ℂ :=
  cleanEmbed indexBasisEquiv none ψ

@[simp] theorem indexEmbed_encode (ψ : QBasis J A W → ℂ) (p : QBasis J A W) :
    indexEmbed (I := I) ψ (indexEncode p) = ψ p := by
  simp [indexEmbed, cleanEmbed_apply, indexEncode, indexBasisEquiv]

theorem indexEmbed_of_index_ne (ψ : QBasis J A W → ℂ)
    (p : QBasis I A (Option J × W)) (hp : p.1 ≠ none) : indexEmbed ψ p = 0 := by
  simp [indexEmbed, cleanEmbed_apply, indexBasisEquiv, hp]

/-- Reversible public index selection, controlled by the retained virtual index. -/
def selectIndex (s : J → I) : Equiv.Perm (QBasis I A (Option J × W)) :=
  Function.Involutive.toPerm
    (fun p => (Equiv.swap none (p.2.2.1.map s) p.1, p.2))
    (by rintro ⟨i, a, j, w⟩; simp)

@[simp] theorem selectIndex_apply (s : J → I) (p : QBasis I A (Option J × W)) :
    selectIndex s p = (Equiv.swap none (p.2.2.1.map s) p.1, p.2) := rfl

@[simp] theorem selectIndex_symm_apply (s : J → I) (p : QBasis I A (Option J × W)) :
    (selectIndex s).symm p = selectIndex s p := rfl

/-- One physical query between selection and its inverse. -/
def indexCall (s : J → I) : QRoutine I A (Option J × W) where
  len := 1
  step := fun _ => qPerm (selectIndex s)
  step_unitary := fun _ => qPerm_mem_unitaryGroup _

@[simp] theorem indexCall_len (s : J → I) : (indexCall (A := A) (W := W) s).len = 1 :=
  rfl

theorem indexCall_run_matrix (s : J → I) (a : I → A) :
    (indexCall (W := W) s).run a =
      qPerm (selectIndex s) * (oracleMat a * qPerm (selectIndex s)) := rfl

private theorem indexOracle_work (a : I → A) (p : QBasis I A (Option J × W)) :
    (oracleMap a p).2.2 = p.2.2 := by
  rcases p with ⟨i, ans, j, w⟩
  cases i <;> rfl

/-- Query selection and unselection preserve the physical index on every basis state. -/
theorem indexSandwich_index (s : J → I) (a : I → A)
    (p : QBasis I A (Option J × W)) :
    (selectIndex s (oracleMap a (selectIndex s p))).1 = p.1 := by
  simp only [selectIndex_apply, oracleMap_fst, indexOracle_work, Equiv.swap_apply_self]

/-- On a clean basis state the sandwich is exactly the virtual native oracle. -/
theorem indexSandwich_encode (s : J → I) (a : I → A) (p : QBasis J A W) :
    selectIndex s (oracleMap a (selectIndex s (indexEncode p))) =
      indexEncode (oracleMap (a ∘ s) p) := by
  rcases p with ⟨j, ans, w⟩
  cases j <;> simp [indexEncode, selectIndex_apply, oracleMap, Function.comp_def]

/-- Exact coherent one-query simulation for arbitrary states and answer tables.
The map `s` need not be injective, and the virtual workspace is unrestricted. -/
theorem indexCall_run (s : J → I) (a : I → A) (ψ : QBasis J A W → ℂ) :
    (indexCall s).run a *ᵥ indexEmbed ψ = indexEmbed (oracleMat (a ∘ s) *ᵥ ψ) := by
  rw [indexCall_run_matrix]
  simp only [← Matrix.mulVec_mulVec]
  funext p
  rw [qPerm_mulVec_apply, oracleMat_mulVec_apply, qPerm_mulVec_apply]
  change indexEmbed ψ (selectIndex s (oracleMap a (selectIndex s p))) =
    indexEmbed (oracleMat (a ∘ s) *ᵥ ψ) p
  rcases p with ⟨i, ans, j, w⟩
  cases i with
  | none =>
      change indexEmbed ψ
        (selectIndex s (oracleMap a (selectIndex s (indexEncode (j, ans, w))))) =
          indexEmbed (oracleMat (a ∘ s) *ᵥ ψ) (indexEncode (j, ans, w))
      rw [indexSandwich_encode, indexEmbed_encode, indexEmbed_encode,
        oracleMat_mulVec_apply]
  | some i =>
      rw [indexEmbed_of_index_ne ψ _ (by
        rw [indexSandwich_index]
        exact Option.some_ne_none i), indexEmbed_of_index_ne _ _ (Option.some_ne_none i)]

/-- A public q-query algorithm pulled back along a public map of indices. -/
def pullQueries (s : J → I) (T : QAlg J A O W) (q : ℕ) :
    QAlg I A O (Option J × W) :=
  compileCleanAlg indexBasisEquiv none (indexCall s) T q

theorem pullQueries_state [DecidableEq O] (s : J → I) (T : QAlg J A O W)
    (q : ℕ) (a : I → A) :
    (pullQueries s T q).state a q = indexEmbed (T.state (a ∘ s) q) := by
  simpa only [pullQueries, indexEmbed, indexCall_len, Nat.mul_one] using
    compileCleanAlg_state indexBasisEquiv none (indexCall s) T q a (a ∘ s)
      (fun ψ => indexCall_run s a ψ)

/-- Every outcome probability is preserved, using exactly q physical queries. -/
theorem pullQueries_prob [DecidableEq O] (s : J → I) (T : QAlg J A O W)
    (q : ℕ) (a : I → A) (o : O) :
    (pullQueries s T q).prob a q o = T.prob (a ∘ s) q o := by
  simpa only [pullQueries, indexCall_len, Nat.mul_one] using
    compileCleanAlg_prob indexBasisEquiv none (indexCall s) T q a (a ∘ s)
      (fun ψ => indexCall_run s a ψ) o

theorem computesWithErrorOn_pullQueries {X : Type} [DecidableEq O]
    (s : J → I) (T : QAlg J A O W) (q : ℕ) (read : X → I → A)
    (f : X → O) (ε : ℝ)
    (hT : ComputesWithErrorOn T q (fun x => read x ∘ s) f ε) :
    ComputesWithErrorOn (pullQueries s T q) q read f ε := by
  intro x
  rw [pullQueries_prob]
  exact hT x

end IndexMap

#print axioms qNormSq_cleanEmbed
#print axioms qProb_cleanEmbed
#print axioms compileCleanUpto_run
#print axioms compileClean_len
#print axioms compileClean_run
#print axioms compileCleanAlg_prob
#print axioms computesWithErrorOn_compileClean
#print axioms indexCall_len
#print axioms indexCall_run
#print axioms pullQueries_state
#print axioms pullQueries_prob
#print axioms computesWithErrorOn_pullQueries

end

end CutQueryComplexity.StarContraction2022.Quantum
