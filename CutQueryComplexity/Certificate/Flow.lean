import CutQueryComplexity.Graph.Operations

/-! # Signed flows, consistency, and weak duality

A signed flow is an antisymmetric function on ordered pairs; `f u v` is the
amount sent from `u` to `v`. It is feasible in `G` when `|f u v| ≤ w u v`.
The net outflow `netOut f v = ∑ u, f v u` is the divergence `Df` of the paper.

* `sum_netOut_eq`: the net outflow of a shore is the flow across its boundary.
* `sum_netOut_le_cut`: weak duality, `∑ v ∈ S, netOut f v ≤ c_G(S)`.
* `Consistent`: a competitor graph agrees with `G` on every queried shore.
* `IsMinCutCertificate`, `IsMinCutWitnessCertificate`: the certificate notions
  of Theorem 2; the competitor ranges over all weighted graphs on `V`.
-/

namespace CutQueryComplexity
namespace Certificate

open WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Antisymmetry of a signed flow on ordered pairs. -/
def IsFlow (f : V → V → ℝ) : Prop := ∀ u v, f v u = -f u v

/-- A signed flow respecting the capacities of `G`. -/
def Feasible (G : WeightedGraph V) (f : V → V → ℝ) : Prop :=
  IsFlow f ∧ ∀ u v, |f u v| ≤ G.w u v

/-- Net outflow (divergence) of a signed flow at a vertex. -/
def netOut (f : V → V → ℝ) (v : V) : ℝ := ∑ u, f v u

/-- The competitor `G'` answers every query in `Q` as `G` does. -/
def Consistent (G G' : WeightedGraph V) (Q : Finset (Finset V)) : Prop :=
  ∀ S ∈ Q, G'.cut S = G.cut S

/-- The queries `Q` determine the global minimum-cut value. -/
def IsMinCutCertificate (G : WeightedGraph V) (Q : Finset (Finset V)) : Prop :=
  ∀ G' : WeightedGraph V, Consistent G G' Q → mincutValue G' = mincutValue G

/-- The queries `Q` contain a shore `S` that is a minimum cut of every consistent graph. -/
def IsMinCutWitnessCertificate (G : WeightedGraph V) (Q : Finset (Finset V))
    (S : Finset V) : Prop :=
  S ∈ Q ∧ ∀ G' : WeightedGraph V, Consistent G G' Q → IsMinCut G' S

theorem Consistent.mono {G G' : WeightedGraph V} {Q Q' : Finset (Finset V)}
    (h : Consistent G G' Q') (hQ : Q ⊆ Q') : Consistent G G' Q :=
  fun S hS => h S (hQ hS)

theorem consistent_union {G G' : WeightedGraph V} {Q Q' : Finset (Finset V)} :
    Consistent G G' (Q ∪ Q') ↔ Consistent G G' Q ∧ Consistent G G' Q' := by
  simp only [Consistent, Finset.mem_union]
  exact ⟨fun h => ⟨fun S hS => h S (Or.inl hS), fun S hS => h S (Or.inr hS)⟩,
    fun h S hS => hS.elim (h.1 S) (h.2 S)⟩

/-- Consistency fixes the weight between two disjoint queried shores. -/
theorem Consistent.cross_eq {G G' : WeightedGraph V} {Q : Finset (Finset V)}
    (h : Consistent G G' Q) {S T : Finset V} (hST : Disjoint S T) (hS : S ∈ Q)
    (hT : T ∈ Q) (hU : S ∪ T ∈ Q) : G'.cross S T = G.cross S T := by
  rw [G'.cross_eq_three_cuts hST, G.cross_eq_three_cuts hST, h S hS, h T hT, h _ hU]

/-- Consistency fixes an edge weight whose three rectangle shores are queried. -/
theorem Consistent.w_eq {G G' : WeightedGraph V} {Q : Finset (Finset V)}
    (h : Consistent G G' Q) {u v : V} (huv : u ≠ v) (hu : {u} ∈ Q) (hv : {v} ∈ Q)
    (huv' : {u, v} ∈ Q) : G'.w u v = G.w u v := by
  rw [G'.edge_eq_three_cuts huv, G.edge_eq_three_cuts huv, h _ hu, h _ hv, h _ huv']

omit [Fintype V] [DecidableEq V] in
theorem IsFlow.self {f : V → V → ℝ} (hf : IsFlow f) (v : V) : f v v = 0 := by
  have := hf v v; linarith

omit [Fintype V] [DecidableEq V] in
theorem Feasible.le {G : WeightedGraph V} {f : V → V → ℝ} (hf : Feasible G f) (u v : V) :
    f u v ≤ G.w u v :=
  (le_abs_self _).trans (hf.2 u v)

omit [Fintype V] [DecidableEq V] in
/-- Internal pairs of a shore contribute nothing to its net outflow. -/
theorem IsFlow.sum_sum_eq_zero {f : V → V → ℝ} (hf : IsFlow f) (S : Finset V) :
    ∑ u ∈ S, ∑ v ∈ S, f u v = 0 := by
  have h : ∑ u ∈ S, ∑ v ∈ S, f u v = ∑ u ∈ S, ∑ v ∈ S, f v u := Finset.sum_comm
  have h2 : ∑ u ∈ S, ∑ v ∈ S, f v u = -∑ u ∈ S, ∑ v ∈ S, f u v := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun u _ => by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun v _ => hf u v
  linarith

/-- The net outflow of a shore equals the flow crossing its boundary. -/
theorem sum_netOut_eq {f : V → V → ℝ} (hf : IsFlow f) (S : Finset V) :
    ∑ v ∈ S, netOut f v = ∑ u ∈ S, ∑ v ∈ Sᶜ, f u v := by
  have h : ∀ u, netOut f u = ∑ v ∈ S, f u v + ∑ v ∈ Sᶜ, f u v := fun u =>
    (Finset.sum_add_sum_compl S (f u)).symm
  simp only [h, Finset.sum_add_distrib, hf.sum_sum_eq_zero, zero_add]

/-- Weak duality: a feasible flow cannot push more out of `S` than its cut capacity. -/
theorem sum_netOut_le_cut {G : WeightedGraph V} {f : V → V → ℝ} (hf : Feasible G f)
    (S : Finset V) : ∑ v ∈ S, netOut f v ≤ G.cut S := by
  rw [sum_netOut_eq hf.1, cut]
  exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hf.le u v

omit [DecidableEq V] in
/-- Net outflow is bounded by the weighted degree. -/
theorem netOut_le_degree {G : WeightedGraph V} {f : V → V → ℝ} (hf : Feasible G f) (v : V) :
    netOut f v ≤ G.degree v :=
  Finset.sum_le_sum fun u _ => hf.le v u

omit [DecidableEq V] in
theorem netOut_add (f g : V → V → ℝ) (v : V) :
    netOut (fun a b => f a b + g a b) v = netOut f v + netOut g v := by
  simp [netOut, Finset.sum_add_distrib]

omit [DecidableEq V] in
theorem netOut_smul (c : ℝ) (g : V → V → ℝ) (v : V) :
    netOut (fun a b => c * g a b) v = c * netOut g v := by
  simp [netOut, Finset.mul_sum]

/-- Adding one vertex to a shore raises its cut by at most the vertex degree. -/
theorem cut_insert_le (G : WeightedGraph V) (S : Finset V) (x : V) :
    G.cut (insert x S) ≤ G.cut S + G.degree x := by
  have h := G.cut_submodular S {x}
  rw [cut_singleton] at h
  have h2 := G.cut_nonneg (S ∩ {x})
  rw [Finset.union_comm, ← Finset.insert_eq] at h
  linarith

/-- Adding a set raises a cut by at most the total degree of the added vertices. -/
theorem cut_union_le (G : WeightedGraph V) (S A : Finset V) :
    G.cut (S ∪ A) ≤ G.cut S + ∑ x ∈ A \ S, G.degree x := by
  have key : ∀ B : Finset V, G.cut (S ∪ B) ≤ G.cut S + ∑ x ∈ B, G.degree x := by
    intro B
    induction B using Finset.induction_on with
    | empty => simp
    | insert x B hx ih =>
      rw [Finset.sum_insert hx, Finset.union_insert]
      have := cut_insert_le G (S ∪ B) x
      linarith
  have h := key (A \ S)
  rwa [Finset.union_sdiff_self_eq_union] at h

end Certificate
end CutQueryComplexity
