import CutQueryComplexity.Model.Randomized
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice

/-! # Relational query complexity, with infinity for unsolvable problems -/

namespace CutQueryComplexity

/-- The infimum of achievable natural budgets, taken in `WithTop ℕ`. -/
noncomputable def queryComplexity (counts : Set ℕ) : WithTop ℕ :=
  ⨅ q ∈ counts, (q : WithTop ℕ)

theorem queryComplexity_le {counts : Set ℕ} {q : ℕ} (h : q ∈ counts) :
    queryComplexity counts ≤ q :=
  iInf_le_of_le q (iInf_le _ h)

theorem le_queryComplexity {counts : Set ℕ} {b : WithTop ℕ}
    (h : ∀ q ∈ counts, b ≤ q) : b ≤ queryComplexity counts :=
  le_iInf fun q => le_iInf fun hq => h q hq

/-- Allowing more algorithms can only decrease complexity. -/
theorem queryComplexity_mono {C D : Set ℕ} (h : C ⊆ D) :
    queryComplexity D ≤ queryComplexity C :=
  le_queryComplexity fun _ hq => queryComplexity_le (h hq)

@[simp] theorem queryComplexity_empty : queryComplexity ∅ = ⊤ := by
  simp [queryComplexity]

/-- On solvable problems this is the ordinary minimum natural query count. -/
theorem queryComplexity_eq_nat_sInf {counts : Set ℕ} (h : counts.Nonempty) :
    queryComplexity counts = (sInf counts : ℕ) := by
  exact (WithTop.coe_sInf h ⟨0, fun _ _ => Nat.zero_le _⟩).symm

variable {X I A O : Type}

/-- Budgets of exact deterministic algorithms for an output relation. -/
def deterministicCounts (read : X → I → A) (Good : X → O → Prop) : Set ℕ :=
  {q | ∃ T : DTree I A O q, T.Solves read Good}

/-- Budgets of randomized algorithms satisfying a per-input error bound. -/
def randomizedCounts (read : X → I → A) (Good : X → O → Prop) (ε : ℝ) : Set ℕ :=
  {q | ∃ T : RTree I A O q, T.SolvesWithError read Good ε}

/-- Exact deterministic relational complexity. -/
noncomputable def deterministicComplexity (read : X → I → A) (Good : X → O → Prop) :
    WithTop ℕ := queryComplexity (deterministicCounts read Good)

/-- Bounded-error randomized relational complexity. -/
noncomputable def randomizedComplexity (read : X → I → A) (Good : X → O → Prop) (ε : ℝ) :
    WithTop ℕ := queryComplexity (randomizedCounts read Good ε)

/-- Any one correct deterministic program bounds the complexity. -/
theorem deterministicComplexity_le {q : ℕ} {read : X → I → A} {Good : X → O → Prop}
    {T : DTree I A O q} (h : T.Solves read Good) :
    deterministicComplexity read Good ≤ q := queryComplexity_le ⟨T, h⟩

theorem randomizedComplexity_le {q : ℕ} {read : X → I → A} {Good : X → O → Prop}
    {T : RTree I A O q} {ε : ℝ} (h : T.SolvesWithError read Good ε) :
    randomizedComplexity read Good ε ≤ q := queryComplexity_le ⟨T, h⟩

/-- Randomization contains exact deterministic computation, with no cost increase. -/
theorem randomizedComplexity_le_deterministic (read : X → I → A)
    (Good : X → O → Prop) {ε : ℝ} (hε : 0 ≤ ε) :
    randomizedComplexity read Good ε ≤ deterministicComplexity read Good := by
  apply queryComplexity_mono
  rintro q ⟨T, hT⟩
  exact ⟨RTree.ofDeterministic T, (RTree.ofDeterministic_solves hT).mono hε⟩

end CutQueryComplexity
