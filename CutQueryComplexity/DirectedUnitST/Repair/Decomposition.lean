import CutQueryComplexity.DirectedUnitST.Repair.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! # Signed unit flows on walks and cycles

A graph cycle supplies a nonzero conserving direction with coordinates in
`{-1,0,1}` supported on its edges. This is the constructive algebraic input
for a fractional-cycle rounding step; bounded adjustment and termination
are separate obligations.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DirectedUnitST.Repair

open Finset Certificate DirectedCertificate

variable {V : Type*} [DecidableEq V]

/-- One unit in a directed pair, with its antisymmetric reverse. -/
def unitArcFlow (u v a b : V) : ℝ :=
  (if a = u ∧ b = v then 1 else 0) - (if a = v ∧ b = u then 1 else 0)

theorem unitArcFlow_isFlow (u v : V) : IsFlow (unitArcFlow u v) := by
  intro a b
  simp only [unitArcFlow]
  have h₁ : (b = u ∧ a = v) ↔ (a = v ∧ b = u) := and_comm
  have h₂ : (b = v ∧ a = u) ↔ (a = u ∧ b = v) := and_comm
  simp only [h₁, h₂]
  ring

theorem unitArcFlow_values (u v a b : V) :
    unitArcFlow u v a b = -1 ∨ unitArcFlow u v a b = 0 ∨ unitArcFlow u v a b = 1 := by
  simp only [unitArcFlow]
  split_ifs <;> norm_num

theorem unitArcFlow_eq_zero_of_edge_ne (u v a b : V)
    (hne : s(a, b) ≠ s(u, v)) : unitArcFlow u v a b = 0 := by
  have hforward : ¬ (a = u ∧ b = v) := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  have hreverse : ¬ (a = v ∧ b = u) := by
    rintro ⟨rfl, rfl⟩
    exact hne Sym2.eq_swap
  simp only [unitArcFlow, hforward, hreverse, ↓reduceIte, sub_self]

variable [Fintype V]

theorem unitArcFlow_divergence (u v a : V) :
    netOut (unitArcFlow u v) a =
      (if a = u then 1 else 0) - (if a = v then 1 else 0) := by
  have hsum (u v : V) : (∑ b, if a = u ∧ b = v then (1 : ℝ) else 0) =
      if a = u then 1 else 0 := by
    by_cases h : a = u <;> simp [h]
  simp only [netOut, unitArcFlow, sum_sub_distrib, hsum]

variable {G : SimpleGraph V}

/-- Sum the signed unit flows along a walk. -/
def walkFlow {u v : V} : G.Walk u v → V → V → ℝ
  | .nil => fun _ _ => 0
  | .cons' u v _ _ p => fun a b => unitArcFlow u v a b + walkFlow p a b

omit [Fintype V] in
theorem walkFlow_isFlow {u v : V} (p : G.Walk u v) : IsFlow (walkFlow p) := by
  induction p with
  | nil => intro a b; simp [walkFlow]
  | @cons u v w h p ih =>
    intro a b
    change unitArcFlow u v b a + walkFlow p b a =
      -(unitArcFlow u v a b + walkFlow p a b)
    rw [unitArcFlow_isFlow u v a b, ih a b]
    ring

/-- Divergence telescopes along every walk. -/
theorem walkFlow_divergence {u v : V} (p : G.Walk u v) (a : V) :
    netOut (walkFlow p) a =
      (if a = u then 1 else 0) - (if a = v then 1 else 0) := by
  induction p with
  | nil => simp [walkFlow, netOut]
  | @cons u v w h p ih =>
    change (∑ b, (unitArcFlow u v a b + walkFlow p a b)) = _
    rw [sum_add_distrib]
    change netOut (unitArcFlow u v) a + netOut (walkFlow p) a = _
    rw [unitArcFlow_divergence, ih]
    ring

theorem walkFlow_conserves {u : V} (p : G.Walk u u) (a : V) :
    netOut (walkFlow p) a = 0 := by
  rw [walkFlow_divergence]
  simp

omit [Fintype V] in
theorem walkFlow_eq_zero_of_notMem {u v : V} (p : G.Walk u v) (a b : V)
    (hnot : s(a, b) ∉ p.edges) : walkFlow p a b = 0 := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at hnot
    change unitArcFlow u v a b + walkFlow p a b = 0
    rw [unitArcFlow_eq_zero_of_edge_ne u v a b hnot.1, ih hnot.2, zero_add]

omit [Fintype V] in
/-- A trail uses each undirected edge at most once, so all coordinates are
zero or a signed unit. -/
theorem walkFlow_values {u v : V} (p : G.Walk u v) (hp : p.IsTrail) (a b : V) :
    walkFlow p a b = -1 ∨ walkFlow p a b = 0 ∨ walkFlow p a b = 1 := by
  induction p with
  | nil => simp [walkFlow]
  | @cons u v w h p ih =>
    obtain ⟨hp, hnot⟩ := (SimpleGraph.Walk.isTrail_cons h p).mp hp
    change unitArcFlow u v a b + walkFlow p a b = -1 ∨
      unitArcFlow u v a b + walkFlow p a b = 0 ∨
      unitArcFlow u v a b + walkFlow p a b = 1
    by_cases he : s(a, b) = s(u, v)
    · have hz := walkFlow_eq_zero_of_notMem p a b (by simpa only [he] using hnot)
      simpa only [hz, add_zero] using unitArcFlow_values u v a b
    · rw [unitArcFlow_eq_zero_of_edge_ne u v a b he, zero_add]
      exact ih hp

omit [Fintype V] in
theorem walkFlow_nonzero_adj {u v a b : V} (p : G.Walk u v)
    (h : walkFlow p a b ≠ 0) : G.Adj a b := by
  apply p.adj_of_mem_edges
  by_contra hnot
  exact h (walkFlow_eq_zero_of_notMem p a b hnot)

omit [Fintype V] in
/-- A nonempty trail has a nonzero signed-flow coordinate. -/
theorem walkFlow_cons_forward {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
    (hp : (SimpleGraph.Walk.cons h p).IsTrail) :
    walkFlow (SimpleGraph.Walk.cons h p) u v = 1 := by
  have hnot := ((SimpleGraph.Walk.isTrail_cons h p).mp hp).2
  have hz := walkFlow_eq_zero_of_notMem p u v hnot
  simp [walkFlow, hz, unitArcFlow, h.ne]

/-- A genuine graph cycle produces the sparse conserving direction needed
for cycle rounding. No circulation direction is postulated as an input. -/
theorem cycle_circulation_direction {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    ∃ z : V → V → ℝ, IsFlow z ∧ (∀ a, netOut z a = 0) ∧
      (∀ a b, z a b = -1 ∨ z a b = 0 ∨ z a b = 1) ∧
      (∀ a b, z a b ≠ 0 → G.Adj a b) ∧ ∃ a b, z a b = 1 := by
  refine ⟨walkFlow p, walkFlow_isFlow p, walkFlow_conserves p,
    walkFlow_values p hp.isTrail, fun a b h => walkFlow_nonzero_adj p h, ?_⟩
  cases p with
  | nil => exact (hp.ne_nil rfl).elim
  | @cons u v w h p => exact ⟨u, v, walkFlow_cons_forward h p hp.isTrail⟩

end CutQueryComplexity.DirectedUnitST.Repair

#print axioms CutQueryComplexity.DirectedUnitST.Repair.walkFlow_divergence
#print axioms CutQueryComplexity.DirectedUnitST.Repair.walkFlow_values
#print axioms CutQueryComplexity.DirectedUnitST.Repair.cycle_circulation_direction
