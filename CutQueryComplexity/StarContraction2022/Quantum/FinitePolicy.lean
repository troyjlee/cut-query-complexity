import CutQueryComplexity.Model.Randomized
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-! # Oracle-independent finite contingent policies

A bounded randomized tree may sample from infinite action spaces. With a
finite answer alphabet, sample all counterfactual answer continuations before
the oracle is supplied. Only the chosen continuation is observed. Its marginal
law is unchanged, so the joint output and actual query-count law is preserved.
When indices and outputs are also finite, the deterministic policy space is
finite by recursion on the public budget. No finite random seed is assumed.
-/

set_option autoImplicit false

namespace CutQueryComplexity.StarContraction2022.Quantum

noncomputable section

namespace FinitePolicy

variable {J X Y : Type}

/-- Sample a complete finite vector of independent coordinates. -/
def sampleFin : (n : ℕ) → (Fin n → PMF X) → PMF (Fin n → X)
  | 0, _ => PMF.pure (fun i => Fin.elim0 i)
  | n + 1, p => (p 0).bind fun x =>
      (sampleFin n (fun i => p i.succ)).map (Fin.cons x)

/-- Every selected coordinate has precisely its requested marginal law. -/
theorem sampleFin_marginal (n : ℕ) :
    ∀ (p : Fin n → PMF X) (i : Fin n),
      (sampleFin n p).map (fun xs => xs i) = p i := by
  induction n with
  | zero => intro p i; exact Fin.elim0 i
  | succ n ih =>
      intro p i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [sampleFin, PMF.map_bind, PMF.map_comp,
          Function.comp_def, Fin.cons_zero]
        calc
          _ = (p 0).bind PMF.pure := by
            apply congrArg (fun f => (p 0).bind f)
            funext x
            exact PMF.map_const (sampleFin n (fun i => p i.succ)) x
          _ = p 0 := PMF.bind_pure (p 0)
      · simp only [sampleFin, PMF.map_bind, PMF.map_comp,
          Function.comp_def, Fin.cons_succ, ih, PMF.bind_const]

/-- Enumerate the finite public answer type and sample all continuations. -/
def sampleFamily [Fintype J] (p : J → PMF X) : PMF (J → X) :=
  (sampleFin (Fintype.card J) (fun i => p ((Fintype.equivFin J).symm i))).map
    (fun xs j => xs (Fintype.equivFin J j))

theorem sampleFamily_marginal [Fintype J] (p : J → PMF X) (j : J) :
    (sampleFamily p).map (fun xs => xs j) = p j := by
  rw [sampleFamily, PMF.map_comp]
  change (sampleFin (Fintype.card J)
    (fun i => p ((Fintype.equivFin J).symm i))).map
      (fun xs => xs (Fintype.equivFin J j)) = p j
  rw [sampleFin_marginal, Equiv.symm_apply_apply]

theorem sampleFamily_map_coordinate [Fintype J] (p : J → PMF X) (j : J)
    (f : X → Y) :
    (sampleFamily p).map (fun xs => f (xs j)) = (p j).map f := by
  simpa only [PMF.map_comp, Function.comp_def] using
    congrArg (fun m : PMF X => m.map f) (sampleFamily_marginal p j)

end FinitePolicy

variable {I A O : Type}

/-- Finite policy space, obtained from the actual deterministic syntax. -/
instance finitePolicyFintype [Fintype I] [Fintype A] [Fintype O] (q : ℕ) :
    Fintype (DTree I A O q) := by
  classical
  induction q with
  | zero => exact inferInstanceAs (Fintype O)
  | succ q ih =>
      letI : Fintype (DTree I A O q) := ih
      exact inferInstanceAs (Fintype (O ⊕ (I × (A → DTree I A O q))))

instance finitePolicyDecidableEq (q : ℕ) : DecidableEq (DTree I A O q) :=
  Classical.decEq _

variable [Fintype A]

/-- Public distribution over full contingent policies. Randomness in the
original next-action PMF is integrated before its answer branches are sampled.
The oracle is not an argument. -/
def policies : {q : ℕ} → RTree I A O q → PMF (DTree I A O q)
  | 0, T => T
  | q + 1, T => T.bind fun action => match action with
    | Sum.inl o => PMF.pure (Sum.inl o)
    | Sum.inr (i, next) =>
        (FinitePolicy.sampleFamily (fun a => policies (next a))).map
          (fun ds => Sum.inr (i, ds))

@[simp] theorem policies_zero (T : RTree I A O 0) : policies T = T := rfl

/-- Exact joint output/count law, uniformly in the oracle. Counterfactual
branches may be sampled independently because execution selects only one. -/
theorem policies_run {q : ℕ} (T : RTree I A O q) (read : I → A) :
    (policies T).map (DTree.run read) = RTree.run read T := by
  induction q with
  | zero => rfl
  | succ q ih =>
      let kernel : (O ⊕ (I × (A → RTree I A O q))) →
          PMF (DTree I A O (q + 1)) := fun action => match action with
        | Sum.inl o => PMF.pure (Sum.inl o)
        | Sum.inr (i, next) =>
            (FinitePolicy.sampleFamily (fun a => policies (next a))).map
              (fun ds => Sum.inr (i, ds))
      have hsplit : (policies T).map (DTree.run (O := O) (q := q + 1) read) =
          T.bind (fun action => (kernel action).map (DTree.run (O := O) (q := q + 1) read)) :=
        PMF.map_bind T kernel (DTree.run (O := O) (q := q + 1) read)
      rw [hsplit]
      change T.bind _ = T.bind _
      apply congrArg (fun f => T.bind f)
      funext action
      rcases action with o | ⟨i, next⟩
      · change (PMF.pure (Sum.inl o : DTree I A O (q + 1))).map
          (DTree.run (O := O) (q := q + 1) read) = PMF.pure (o, 0)
        exact PMF.pure_map (DTree.run (O := O) (q := q + 1) read)
          (Sum.inl o : DTree I A O (q + 1))
      · let bump : O × ℕ → O × ℕ := fun p => (p.1, p.2 + 1)
        change ((FinitePolicy.sampleFamily (fun a => policies (next a))).map
          (fun ds => (Sum.inr (i, ds) : DTree I A O (q + 1)))).map
          (DTree.run (O := O) (q := q + 1) read) =
            (RTree.run read (next (read i))).map bump
        calc
          _ = (FinitePolicy.sampleFamily (fun a => policies (next a))).map
              (fun ds => bump (DTree.run (O := O) (q := q) read (ds (read i)))) :=
            PMF.map_comp (fun ds => (Sum.inr (i, ds) : DTree I A O (q + 1)))
              (FinitePolicy.sampleFamily (fun a => policies (next a)))
              (DTree.run (O := O) (q := q + 1) read)
          _ = (policies (next (read i))).map
              (bump ∘ DTree.run (O := O) (q := q) read) :=
            FinitePolicy.sampleFamily_map_coordinate
              (J := A) (X := DTree I A O q) (Y := O × ℕ)
              (fun a => policies (next a)) (read i)
              (bump ∘ DTree.run (O := O) (q := q) read)
          _ = ((policies (next (read i))).map (DTree.run (O := O) (q := q) read)).map bump :=
            (PMF.map_comp (DTree.run (O := O) (q := q) read)
              (policies (next (read i))) bump).symm
          _ = _ := congrArg (fun m : PMF (O × ℕ) => m.map bump)
            (ih (next (read i)))

theorem policies_output {q : ℕ} (T : RTree I A O q) (read : I → A) :
    (policies T).map (fun D => D.eval read) = (RTree.run read T).map Prod.fst := by
  rw [← policies_run T read, PMF.map_comp]
  rfl

theorem policies_count {q : ℕ} (T : RTree I A O q) (read : I → A) :
    (policies T).map (fun D => D.cost read) = (RTree.run read T).map Prod.snd := by
  rw [← policies_run T read, PMF.map_comp]
  rfl

/-- The full preserved execution law respects the same public cap. -/
theorem policies_run_cost_le {q : ℕ} (T : RTree I A O q) (read : I → A)
    {p : O × ℕ} (hp : p ∈ ((policies T).map (DTree.run read)).support) :
    p.2 ≤ q := by
  rw [policies_run] at hp
  exact RTree.cost_le T read hp

/-- An empty index type forces zero actual classical queries, even with a
positive available budget. Later quantum padding is counted separately. -/
theorem policies_empty_index_cost [IsEmpty I] {q : ℕ} (T : RTree I A O q)
    (read : I → A) {p : O × ℕ} (hp : p ∈ (RTree.run read T).support) :
    p.2 = 0 := by
  rw [← policies_run T read] at hp
  obtain ⟨D, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  cases q with
  | zero => rfl
  | succ q =>
      rcases D with o | ⟨i, next⟩
      · rfl
      · exact isEmptyElim i

#print axioms FinitePolicy.sampleFin_marginal
#print axioms FinitePolicy.sampleFamily_marginal
#print axioms FinitePolicy.sampleFamily_map_coordinate
#print axioms policies_zero
#print axioms policies_run
#print axioms policies_output
#print axioms policies_count
#print axioms policies_run_cost_le
#print axioms policies_empty_index_cost

end

end CutQueryComplexity.StarContraction2022.Quantum
