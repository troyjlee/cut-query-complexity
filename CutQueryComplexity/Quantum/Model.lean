import CutQueryComplexity.Graph.Capacity
import CutQueryComplexity.Model.Complexity
import QuantumQueryComplexity.Quantum.Relation
import QuantumQueryComplexity.Quantum.Complexity

/-! # Finite quantum cut oracles and relational quantum complexity

The quantum model is the sibling library's `QAlg`, specialized to whole cut
answers. The weight bound is public. Arbitrary real-weight classical oracles
are deliberately outside this finite quantum specialization.
-/

namespace CutQueryComplexity

open QuantumQueryComplexity

/-- The finite answer alphabet for `n` vertices and capacities at most `W`. -/
abbrev CutAnswer (n W : ℕ) := Fin (W * n * n + 1)

/-- Exact finite cut observation map. -/
def capacityRead {n W : ℕ} (G : CapacityGraph (Fin n) W) (S : Finset (Fin n)) :
    CutAnswer n W :=
  ⟨G.cut S, by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le (G.cut_le S)⟩

/-- Simple graphs use the same oracle with public capacity bound one. -/
noncomputable def simpleRead {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : CutAnswer n 1 := capacityRead (SimpleGraph.toCapacity G) S

@[simp] theorem capacityRead_val {n W : ℕ} (G : CapacityGraph (Fin n) W)
    (S : Finset (Fin n)) : (capacityRead G S : ℕ) = G.cut S := rfl

/-- Quantum cut-query algorithms reuse the established Hilbert-space semantics. -/
abbrev CutQAlg (n W : ℕ) (O Work : Type) [Fintype Work] [DecidableEq Work] :=
  QAlg (Finset (Fin n)) (CutAnswer n W) O Work

variable {X I A O : Type} [Fintype X] [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A]

/-- Budgets achievable by a quantum algorithm for an arbitrary output relation. -/
def quantumCounts (read : X → I → A) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (ε : ℝ) : Set ℕ :=
  {q | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (T : QAlg I A O W),
    SolvesWithErrorOn T q read Good ε}

/-- Relational quantum query complexity, with value infinity if no algorithm exists. -/
noncomputable def quantumComplexity (read : X → I → A) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (ε : ℝ) : WithTop ℕ :=
  queryComplexity (quantumCounts read Good ε)

theorem quantumComplexity_le {read : X → I → A} {Good : X → O → Prop}
    [∀ x, DecidablePred (Good x)] {ε : ℝ} {q : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] {T : QAlg I A O W}
    (h : SolvesWithErrorOn T q read Good ε) : quantumComplexity read Good ε ≤ q :=
  queryComplexity_le ⟨W, inferInstance, inferInstance, T, h⟩

/-- Equality-output relations give exactly the sibling library's function query counts. -/
theorem quantumCounts_eq_function [DecidableEq O] (read : X → I → A)
    (f : X → O) (ε : ℝ) :
    quantumCounts read (fun x y => y = f x) ε = QueryCounts read f ε := by
  ext q
  simp only [quantumCounts, QueryCounts, Set.mem_setOf_eq, solvesWithErrorOn_eq_iff]

/-- Compatibility with the natural-valued complexity on solvable function problems. -/
theorem quantumComplexity_eq_function [DecidableEq O] (read : X → I → A)
    (f : X → O) (ε : ℝ) (h : (QueryCounts read f ε).Nonempty) :
    quantumComplexity read (fun x y => y = f x) ε = (qQueryOn read f ε : WithTop ℕ) := by
  rw [quantumComplexity, quantumCounts_eq_function, queryComplexity_eq_nat_sInf h]
  rfl

end CutQueryComplexity
