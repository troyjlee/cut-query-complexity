import CutQueryComplexity.StarContraction2022.Quantum.FiniteCutEncoding
import CutQueryComplexity.StarContraction2022.Quantum.RandomizedCompiler

/-! # Public quantum compilation of finitely encoded cut trees

The algorithm is constructed from the public real-answer source tree before
any graph or answer table. Pure finite validation adds no physical query.
Correctness transfers under the explicit source-tree soundness premise;
these generic transport theorems do not construct a minimum-cut solver.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum

noncomputable section
open QuantumQueryComplexity
open scoped Classical Matrix

variable {n q : ℕ}

abbrev finiteCutWork (W : ℕ) (T : OptionalCutTree n q) : Type :=
  randomizedWork (finiteCutTree W T)

/-- A public algorithm with genuinely finite input and output alphabets. -/
def finiteCutAlg (W : ℕ) (T : OptionalCutTree n q) :
    CutQAlg n W (FiniteCutResult n W) (finiteCutWork W T) :=
  randomizedAlg (finiteCutTree W T)

/-- The actual compiled routine, with its full fixed physical schedule. -/
def finiteCutRoutine (W : ℕ) (T : OptionalCutTree n q) :
    QRoutine (Finset (Fin n)) (CutAnswer n W) (finiteCutWork W T) :=
  randomizedRoutine (finiteCutTree W T)

@[simp] theorem finiteCutRoutine_len (W : ℕ) (T : OptionalCutTree n q) :
    (finiteCutRoutine W T).len = q := rfl

theorem finiteCutRoutine_state (W : ℕ) (T : OptionalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) :
    (finiteCutRoutine W T).run read *ᵥ (finiteCutAlg W T).init =
      (finiteCutAlg W T).state read q :=
  randomizedRoutine_state (finiteCutTree W T) read

/-- The exact encoded Born law holds even for inconsistent finite answer tables. -/
theorem finiteCutAlg_prob (W : ℕ) (T : OptionalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) (e : FiniteCutResult n W) :
    (finiteCutAlg W T).prob read q e =
      (((RTree.run (decodeCutAnswer ∘ read) T).map
        (fun p => encodeOptionalCutResult W p.1)) e).toReal := by
  change (randomizedAlg (finiteCutTree W T)).prob read q e = _
  rw [randomizedAlg_prob, finiteCutTree_run, PMF.map_comp]
  rfl

theorem finiteCutAlg_successProb (W : ℕ) (T : OptionalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W)
    (Good : FiniteCutResult n W → Prop) [DecidablePred Good] :
    goodProb (finiteCutAlg W T).readout Good ((finiteCutAlg W T).state read q) =
      T.successProb (decodeCutAnswer ∘ read)
        (fun out => Good (encodeOptionalCutResult W out)) := by
  change goodProb (randomizedAlg (finiteCutTree W T)).readout Good
    ((randomizedAlg (finiteCutTree W T)).state read q) = _
  rw [randomizedAlg_successProb, finiteCutTree_successProb]

/-- Honest-input validation is lossless once retained source results are sound. -/
theorem finiteCutAlg_successProb_honest (W : ℕ) (T : OptionalCutTree n q)
    (G : CapacityGraph (Fin n) W) (h : CutTreeSound T G.toWeighted)
    (Good : Option (CutResult (Fin n)) → Prop) [DecidablePred Good] :
    goodProb (finiteCutAlg W T).readout (fun e => Good (decodeFiniteCutResult e))
      ((finiteCutAlg W T).state (capacityRead G) q) = T.successProb G.toWeighted.cut Good := by
  change goodProb (randomizedAlg (finiteCutTree W T)).readout
    (fun e => Good (decodeFiniteCutResult e))
    ((randomizedAlg (finiteCutTree W T)).state (capacityRead G) q) = _
  rw [randomizedAlg_successProb]
  exact finiteCutTree_successProb_honest T G h Good

/-- Relational error transport with no extra error or query. The source tree
and its soundness are explicit inputs to this generic transport theorem. -/
theorem finiteCutAlg_solves_iff (W : ℕ) (T : OptionalCutTree n q)
    (h : ∀ G : CapacityGraph (Fin n) W, CutTreeSound T G.toWeighted)
    (Good : CapacityGraph (Fin n) W → Option (CutResult (Fin n)) → Prop)
    [∀ G, DecidablePred (Good G)] (ε : ℝ) :
    SolvesWithErrorOn (finiteCutAlg W T) q capacityRead
      (fun G e => Good G (decodeFiniteCutResult e)) ε ↔
    T.SolvesWithError (fun G => G.toWeighted.cut) Good ε := by
  constructor
  · intro hs G
    have hx := hs G
    change 1 - ε ≤ goodProb (finiteCutAlg W T).readout
      (fun e => Good G (decodeFiniteCutResult e))
      ((finiteCutAlg W T).state (capacityRead G) q) at hx
    rw [finiteCutAlg_successProb_honest W T G (h G) (Good G)] at hx
    exact hx
  · intro hs G
    change 1 - ε ≤ goodProb (finiteCutAlg W T).readout
      (fun e => Good G (decodeFiniteCutResult e))
      ((finiteCutAlg W T).state (capacityRead G) q)
    rw [finiteCutAlg_successProb_honest W T G (h G) (Good G)]
    exact hs G

/-- The zero-query case samples and validates outputs without consulting read. -/
theorem finiteCutAlg_zero_prob (W : ℕ) (T : OptionalCutTree n 0)
    (read : Finset (Fin n) → CutAnswer n W) (e : FiniteCutResult n W) :
    (finiteCutAlg W T).prob read 0 e =
      ((((show PMF (Option (CutResult (Fin n))) from T).map
        (encodeOptionalCutResult W)) e)).toReal := by
  rw [finiteCutAlg_prob]
  change ((((show PMF (Option (CutResult (Fin n))) from T).map
    (fun out => (out, (0 : ℕ)))).map
    (fun p => encodeOptionalCutResult W p.1)) e).toReal = _
  rw [PMF.map_comp]
  rfl

abbrev finiteCutTotalWork (W : ℕ) (T : TotalCutTree n q) : Type :=
  finiteCutWork W (T.map some)

def finiteCutTotalAlg (W : ℕ) (T : TotalCutTree n q) :
    CutQAlg n W (FiniteCutResult n W) (finiteCutTotalWork W T) :=
  finiteCutAlg W (T.map some)

def finiteCutTotalRoutine (W : ℕ) (T : TotalCutTree n q) :
    QRoutine (Finset (Fin n)) (CutAnswer n W) (finiteCutTotalWork W T) :=
  finiteCutRoutine W (T.map some)

@[simp] theorem finiteCutTotalRoutine_len (W : ℕ) (T : TotalCutTree n q) :
    (finiteCutTotalRoutine W T).len = q := rfl

theorem finiteCutTotalRoutine_state (W : ℕ) (T : TotalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) :
    (finiteCutTotalRoutine W T).run read *ᵥ (finiteCutTotalAlg W T).init =
      (finiteCutTotalAlg W T).state read q :=
  finiteCutRoutine_state W (T.map some) read

theorem finiteCutTotalAlg_prob (W : ℕ) (T : TotalCutTree n q)
    (read : Finset (Fin n) → CutAnswer n W) (e : FiniteCutResult n W) :
    (finiteCutTotalAlg W T).prob read q e =
      (((RTree.run (decodeCutAnswer ∘ read) T).map
        (fun p => encodeCutResult W p.1)) e).toReal := by
  change (randomizedAlg (finiteCutTreeTotal W T)).prob read q e = _
  rw [randomizedAlg_prob, finiteCutTreeTotal_run, PMF.map_comp]
  rfl

theorem finiteCutTotalAlg_successProb_honest (W : ℕ) (T : TotalCutTree n q)
    (G : CapacityGraph (Fin n) W) (h : TotalCutTreeSound T G.toWeighted)
    (Good : Option (CutResult (Fin n)) → Prop) [DecidablePred Good] :
    goodProb (finiteCutTotalAlg W T).readout (fun e => Good (decodeFiniteCutResult e))
      ((finiteCutTotalAlg W T).state (capacityRead G) q) =
        T.successProb G.toWeighted.cut (fun r => Good (some r)) := by
  change goodProb (randomizedAlg (finiteCutTreeTotal W T)).readout
    (fun e => Good (decodeFiniteCutResult e))
    ((randomizedAlg (finiteCutTreeTotal W T)).state (capacityRead G) q) = _
  rw [randomizedAlg_successProb]
  exact finiteCutTreeTotal_successProb_honest T G h Good

#print axioms finiteCutRoutine_len
#print axioms finiteCutRoutine_state
#print axioms finiteCutAlg_prob
#print axioms finiteCutAlg_successProb
#print axioms finiteCutAlg_successProb_honest
#print axioms finiteCutAlg_solves_iff
#print axioms finiteCutAlg_zero_prob
#print axioms finiteCutTotalRoutine_len
#print axioms finiteCutTotalRoutine_state
#print axioms finiteCutTotalAlg_prob
#print axioms finiteCutTotalAlg_successProb_honest

end
end CutQueryComplexity.StarContraction2022.Quantum
