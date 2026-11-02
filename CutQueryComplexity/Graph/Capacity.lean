import CutQueryComplexity.Graph.Weighted
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Pi

/-! # Publicly bounded integral capacities and finite cut answers -/

namespace CutQueryComplexity

/-- Natural edge capacities bounded by the public parameter `W`. -/
@[ext] structure CapacityGraph (V : Type*) (W : ℕ) where
  w : V → V → Fin (W + 1)
  symm : ∀ u v, w u v = w v u
  diag : ∀ v, w v v = 0

namespace CapacityGraph

variable {V : Type*} {W : ℕ}

/-- A bounded-capacity graph is determined by its finite table. -/
noncomputable instance [Fintype V] : Fintype (CapacityGraph V W) := by
  classical
  exact Fintype.ofInjective CapacityGraph.w (fun _ _ h => CapacityGraph.ext h)

/-- Real-valued interpretation of the integral capacities. -/
def toWeighted (G : CapacityGraph V W) : WeightedGraph V where
  w u v := (G.w u v : ℕ)
  symm u v := by rw [G.symm u v]
  nonneg _ _ := Nat.cast_nonneg _
  diag v := by rw [G.diag]; simp

variable [Fintype V] [DecidableEq V]

/-- Exact natural-valued cut answer. -/
def cut (G : CapacityGraph V W) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, (G.w u v : ℕ)

@[simp] theorem toWeighted_cut (G : CapacityGraph V W) (S : Finset V) :
    G.toWeighted.cut S = (G.cut S : ℝ) := by
  simp [WeightedGraph.cut, toWeighted, cut]

/-- A loose range bound keeps the answer alphabet independent of the input. -/
theorem cut_le (G : CapacityGraph V W) (S : Finset V) :
    G.cut S ≤ W * Fintype.card V * Fintype.card V := by
  have h : G.cut S ≤ S.card * (Sᶜ.card * W) := by
    unfold cut
    calc
      _ ≤ ∑ _u ∈ S, ∑ _v ∈ Sᶜ, W :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          Nat.le_of_lt_succ (G.w u v).isLt
      _ = _ := by simp
  calc
    G.cut S ≤ S.card * (Sᶜ.card * W) := h
    _ ≤ Fintype.card V * (Fintype.card V * W) :=
      Nat.mul_le_mul (Finset.card_le_univ S)
        (Nat.mul_le_mul_right W (Finset.card_le_univ Sᶜ))
    _ = _ := by ring

/-- A whole cut answer occupies one finite alphabet symbol, not one query per bit. -/
def read (G : CapacityGraph V W) (S : Finset V) :
    Fin (W * Fintype.card V * Fintype.card V + 1) :=
  ⟨G.cut S, Nat.lt_succ_of_le (G.cut_le S)⟩

@[simp] theorem read_val (G : CapacityGraph V W) (S : Finset V) :
    (G.read S : ℕ) = G.cut S := rfl

end CapacityGraph

namespace SimpleGraph

variable {V : Type*}
open scoped Classical

/-- Interpret a simple graph as capacities in `{0,1}`. -/
noncomputable def toCapacity (G : SimpleGraph V) : CapacityGraph V 1 := by
  classical
  exact {
    w := fun u v => if G.Adj u v then 1 else 0
    symm := fun u v => by simp [G.adj_comm]
    diag := fun v => by simp }

/-- The unit-weight interpretation of a simple graph. -/
noncomputable def toWeighted (G : SimpleGraph V) : WeightedGraph V :=
  (toCapacity G).toWeighted

@[simp] theorem toWeighted_w (G : SimpleGraph V) (u v : V) :
    (toWeighted G).w u v = if G.Adj u v then 1 else 0 := by
  classical
  by_cases h : G.Adj u v <;> simp [toWeighted, toCapacity, CapacityGraph.toWeighted, h]

end SimpleGraph
end CutQueryComplexity
