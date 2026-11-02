import CutQueryComplexity.DeterministicAPMCExpansion.Basic
import CutQueryComplexity.AllPairsAudit.Star
import CutQueryComplexity.Primitive.Reductions
import CutQueryComplexity.DirectedUnitST.Repair.HeavyTerminal

/-!
# A symmetric unit graph with two known terminal stars

The network has `card V + 2` vertices. Only its internal graph is unknown;
terminal capacities and the current signed flow are public. Query programs do
not receive the hidden graph or a feasibility witness.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DeterministicAPMCExpansion.Flow

open Finset WeightedGraph AllPairsAudit Certificate DirectedCertificate
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev NetworkVertex (V : Type) := V ⊕ Fin 2

def source : NetworkVertex V := .inr 0
def sink : NetworkVertex V := .inr 1

theorem source_ne_sink : (source : NetworkVertex V) ≠ sink := by
  simp [source, sink]

theorem network_card : Fintype.card (NetworkVertex V) = Fintype.card V + 2 := by
  simp [NetworkVertex]

def embedded (G : WeightedGraph V) : WeightedGraph (NetworkVertex V) where
  w
    | .inl u, .inl v => G.w u v
    | _, _ => 0
  symm u v := by cases u <;> cases v <;> simp [G.symm]
  nonneg u v := by cases u <;> cases v <;> simp [G.nonneg]
  diag u := by cases u <;> simp [G.diag]

def terminalCapacity (a z : V → ℕ) (i : Fin 2) (v : V) : ℝ :=
  if i = 0 then a v else z v

theorem terminalCapacity_nonneg (a z : V → ℕ) (i : Fin 2) (v : V) :
    0 ≤ terminalCapacity a z i v := by
  unfold terminalCapacity
  split <;> positivity

/-- The known graph contains only the two terminal stars. Both may touch
the same original vertex. -/
def knownStars (a z : V → ℕ) : WeightedGraph (NetworkVertex V) where
  w
    | .inl u, .inr i => terminalCapacity a z i u
    | .inr i, .inl v => terminalCapacity a z i v
    | _, _ => 0
  symm u v := by cases u <;> cases v <;> rfl
  nonneg u v := by
    cases u <;> cases v <;> first | exact terminalCapacity_nonneg _ _ _ _ | exact le_rfl
  diag u := by cases u <;> rfl

def twoStar (G : WeightedGraph V) (a z : V → ℕ) : WeightedGraph (NetworkVertex V) where
  w u v := (embedded G).w u v + (knownStars a z).w u v
  symm u v := by rw [(embedded G).symm u v, (knownStars a z).symm u v]
  nonneg u v := add_nonneg ((embedded G).nonneg u v) ((knownStars a z).nonneg u v)
  diag u := by rw [(embedded G).diag, (knownStars a z).diag, add_zero]

@[simp] theorem twoStar_internal (G : WeightedGraph V) (a z : V → ℕ) (u v : V) :
    (twoStar G a z).w (.inl u) (.inl v) = G.w u v := by
  simp [twoStar, embedded, knownStars]

@[simp] theorem twoStar_source (G : WeightedGraph V) (a z : V → ℕ) (v : V) :
    (twoStar G a z).w source (.inl v) = a v := by
  simp [twoStar, embedded, knownStars, source, terminalCapacity]

@[simp] theorem twoStar_sink (G : WeightedGraph V) (a z : V → ℕ) (v : V) :
    (twoStar G a z).w sink (.inl v) = z v := by
  simp [twoStar, embedded, knownStars, sink, terminalCapacity]

theorem embedded_cut (G : WeightedGraph V) (A : Finset (NetworkVertex V)) :
    (embedded G).cut A = G.cut (originalShore A) := by
  simp [cut_eq_sum_ite, Fintype.sum_sum_type, embedded]

theorem twoStar_cut (G : WeightedGraph V) (a z : V → ℕ)
    (A : Finset (NetworkVertex V)) :
    (twoStar G a z).cut A = G.cut (originalShore A) + (knownStars a z).cut A := by
  change (∑ u ∈ A, ∑ v ∈ Aᶜ,
    ((embedded G).w u v + (knownStars a z).w u v)) = _
  simp only [sum_add_distrib]
  change (embedded G).cut A + (knownStars a z).cut A = _
  rw [embedded_cut]

/-- One query to the internal graph, plus the fully known star contribution. -/
def twoStarQuery (a z : V → ℕ) (A : Finset (NetworkVertex V)) :
    DTree (Finset V) ℝ ℝ 1 :=
  DTree.query (originalShore A) fun answer =>
    DTree.pure (answer + (knownStars a z).cut A)

theorem twoStarQuery_eval (G : WeightedGraph V) (a z : V → ℕ)
    (A : Finset (NetworkVertex V)) :
    (twoStarQuery a z A).eval G.cut = (twoStar G a z).cut A := by
  simp only [twoStarQuery, DTree.eval_query, DTree.eval_pure, twoStar_cut]

/-- Regard the symmetric capacities as a directed capacity matrix, so the
existing signed-flow and heavy-terminal geometry can be used unchanged. -/
def directed (G : WeightedGraph V) : WeightedDiGraph V where
  c := G.w
  nonneg := G.nonneg
  diag := G.diag

@[simp] theorem directed_out (G : WeightedGraph V) (S : Finset V) :
    (directed G).out S = G.cut S := rfl

def residualEntry (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ) (u v : NetworkVertex V) : ℝ :=
  (twoStar G a z).w u v - f u v

theorem residual_nonneg {G : WeightedGraph V} {a z : V → ℕ}
    {f : NetworkVertex V → NetworkVertex V → ℝ}
    (hf : (directed (twoStar G a z)).Feasible f) (u v : NetworkVertex V) :
    0 ≤ residualEntry G a z f u v := sub_nonneg.mpr (hf.2 u v)

@[simp] theorem residual_diagonal {G : WeightedGraph V} {a z : V → ℕ}
    {f : NetworkVertex V → NetworkVertex V → ℝ}
    (hf : (directed (twoStar G a z)).Feasible f) (u : NetworkVertex V) :
    residualEntry G a z f u u = 0 := by
  simp only [residualEntry, (twoStar G a z).diag, hf.1.self, sub_self]

/-- Large terminal capacities are absent from this bound. -/
theorem internal_residual_pair_bound {G : WeightedGraph V} (hG : Unweighted G)
    {a z : V → ℕ} {f : NetworkVertex V → NetworkVertex V → ℝ}
    (hf : (directed (twoStar G a z)).Feasible f) (u v : V) :
    residualEntry G a z f (.inl u) (.inl v) +
      residualEntry G a z f (.inl v) (.inl u) ≤ 2 := by
  have hw := unweighted_edge_le_one hG u v
  simp only [residualEntry, twoStar_internal, hf.1 (.inl u) (.inl v), G.symm v u]
  linarith

/-- The three queried network cuts each cost one internal-graph query.
The signed flow is explicit public data and is subtracted offline. -/
def residualRectangleQuery (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (A B : Finset (NetworkVertex V)) : DTree (Finset V) ℝ ℝ 3 :=
  ((crossQuery A B).substitute (twoStarQuery a z)).map
    (fun answer => answer - ∑ u ∈ A, ∑ v ∈ B, f u v)

theorem residual_rectangle_query (G : WeightedGraph V) (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    {A B : Finset (NetworkVertex V)} (hAB : Disjoint A B) :
    (residualRectangleQuery a z f A B).eval G.cut =
      ∑ u ∈ A, ∑ v ∈ B, residualEntry G a z f u v := by
  simp only [residualRectangleQuery, DTree.eval_map, DTree.eval_substitute,
    twoStarQuery_eval, crossQuery_eval _ hAB]
  simp only [residualEntry, cross, sum_sub_distrib]

theorem residualRectangleQuery_cost (a z : V → ℕ)
    (f : NetworkVertex V → NetworkVertex V → ℝ)
    (A B : Finset (NetworkVertex V)) (oracle : Finset V → ℝ) :
    (residualRectangleQuery a z f A B).cost oracle ≤ 3 := DTree.cost_le _ _

end
end CutQueryComplexity.DeterministicAPMCExpansion.Flow

#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.twoStarQuery_eval
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.residual_rectangle_query
#print axioms CutQueryComplexity.DeterministicAPMCExpansion.Flow.internal_residual_pair_bound
