import CutQueryComplexity.Graph.Integral
import Mathlib.Data.Fintype.Prod

/-! # Adding weighted edges and graphs

An edge index retains an orientation only as a name. Its graph is undirected,
and graph addition accumulates repeated occurrences of the same edge.
-/

namespace CutQueryComplexity.WeightedGraph
noncomputable section
open scoped Classical
variable {V : Type}

instance : Add (WeightedGraph V) := ⟨add⟩

/-- The addition notation uses the existing pointwise graph addition, on any vertex type. -/
@[simp] theorem add_weight (G H : WeightedGraph V) (u v : V) :
    (G + H).w u v = G.w u v + H.w u v := rfl

@[simp] theorem add_zero (G : WeightedGraph V) : G + 0 = G := by ext; simp
@[simp] theorem zero_add (G : WeightedGraph V) : 0 + G = G := by ext; simp

theorem add_assoc (G H K : WeightedGraph V) : (G + H) + K = G + (H + K) := by
  ext; simp only [add_weight, _root_.add_assoc]

def sumGraphs : List (WeightedGraph V) → WeightedGraph V
  | [] => 0
  | G :: gs => G + sumGraphs gs

@[simp] theorem sumGraphs_w (gs : List (WeightedGraph V)) (u v : V) :
    (sumGraphs gs).w u v = (gs.map (fun G => G.w u v)).sum := by
  induction gs with
  | nil => rfl
  | cons G gs ih => simp [sumGraphs, ih]

theorem sumGraphs_append (gs hs : List (WeightedGraph V)) :
    sumGraphs (gs ++ hs) = sumGraphs gs + sumGraphs hs := by
  induction gs with
  | nil => simp [sumGraphs]
  | cons G gs ih => simp [sumGraphs, ih, add_assoc]

theorem sumGraphs_replicate_scale (G : WeightedGraph V) {r : ℕ} (hr : 0 < r) :
    sumGraphs (List.replicate r (G.scale (1 / r) (by positivity))) = G := by
  ext u v
  simp only [sumGraphs_w, List.map_replicate, List.sum_replicate, nsmul_eq_mul, scale]
  have hn : (r : ℝ) ≠ 0 := by positivity
  rw [one_div, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

def finiteSum {ι : Type*} (s : Finset ι) (F : ι → WeightedGraph V) : WeightedGraph V where
  w u v := ∑ i ∈ s, (F i).w u v
  symm u v := by simp only [WeightedGraph.symm]
  nonneg u v := Finset.sum_nonneg (fun i _ => (F i).nonneg u v)
  diag v := by simp only [WeightedGraph.diag, Finset.sum_const_zero]

/-- A named edge with distinct original endpoints. Both orientations are allowed as names. -/
abbrev EdgeIndex (V : Type) := {e : V × V // e.1 ≠ e.2}

def edgeGraph (e : EdgeIndex V) (a : ℝ) (ha : 0 ≤ a) : WeightedGraph V where
  w u v := (if (u, v) = e.val then a else 0) + (if (v, u) = e.val then a else 0)
  symm _ _ := by apply _root_.add_comm
  nonneg _ _ := add_nonneg (by split <;> positivity) (by split <;> positivity)
  diag u := by
    have hn : (u, u) ≠ e.val := by
      intro h
      exact e.property (by rw [← h])
    simp [hn]

@[simp] theorem edgeGraph_zero (e : EdgeIndex V) : edgeGraph e 0 le_rfl = 0 := by
  ext; simp [edgeGraph]

theorem edgeGraph_scale (e : EdgeIndex V) (a : ℝ) (ha : 0 ≤ a) (c : ℝ) (hc : 0 ≤ c) :
    (edgeGraph e a ha).scale c hc = edgeGraph e (c * a) (mul_nonneg hc ha) := by
  ext u v
  simp only [scale, edgeGraph, mul_add, mul_ite, mul_zero]

variable [Fintype V] [DecidableEq V]

@[simp] theorem cut_addition (G H : WeightedGraph V) (S : Finset V) :
    (G + H).cut S = G.cut S + H.cut S := cut_add G H S

theorem cut_edgeGraph (e : EdgeIndex V) (a : ℝ) (ha : 0 ≤ a) (S : Finset V) :
    (edgeGraph e a ha).cut S =
      if (e.val.1 ∈ S ∧ e.val.2 ∉ S) ∨ (e.val.2 ∈ S ∧ e.val.1 ∉ S) then a else 0 := by
  rcases e with ⟨⟨u, v⟩, hne⟩
  simp only [cut, edgeGraph, Prod.mk.injEq, Finset.sum_add_distrib, ite_and,
    Finset.sum_ite_irrel]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv, eq_comm]

theorem cut_edgeGraph_le (e : EdgeIndex V) (a : ℝ) (ha : 0 ≤ a) (S : Finset V) :
    (edgeGraph e a ha).cut S ≤ a := by
  rw [cut_edgeGraph]
  split <;> simp_all

end
end CutQueryComplexity.WeightedGraph
