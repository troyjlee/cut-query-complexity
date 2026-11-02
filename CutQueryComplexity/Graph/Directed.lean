import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Directed multigraphs and the outgoing-cut oracle (D1)

A loopless directed multigraph has `c u v` arcs from `u` to `v` (antiparallel arcs allowed).
Its only oracle is the outgoing cut `F(S) = |E(S, V \ S)|` (`out`). For an unordered pair,
`sym u v = c u v + c v u` counts the arcs between its endpoints in both directions.

The cut identities of directed graphs:

* `out_add_out`: for disjoint `A, B`, `F(A) + F(B) = F(A ∪ B) + Σ_{u∈A, v∈B} sym u v`, so
  `pairs_eq_out` recovers the pair count from three queries;
* `two_mul_out`: `2 F(S) = cut_sym(S) + Σ_{v∈S} (d⁺(v) − d⁻(v))`;
* `out_add_arcs_self`, `arcs_self_eq_sum_lt`: `F(S) = Σ_{v∈S} d⁺(v) − Σ_{u<v, u,v∈S} sym u v`.
-/

namespace CutQueryComplexity

/-- A loopless directed multigraph: `c u v` arcs from `u` to `v`. -/
@[ext] structure DiGraph (V : Type*) where
  c : V → V → ℕ
  diag : ∀ v, c v v = 0

namespace DiGraph

open Finset

variable {V : Type*} (G : DiGraph V)

/-- The arcs between the endpoints of an unordered pair, in both directions. -/
def sym (u v : V) : ℕ := G.c u v + G.c v u

theorem sym_comm (u v : V) : G.sym u v = G.sym v u := Nat.add_comm _ _

@[simp] theorem sym_self (v : V) : G.sym v v = 0 := by simp [sym, G.diag]

/-- A simple digraph: at most one arc for each ordered pair. -/
def Simple : Prop := ∀ u v, G.c u v ≤ 1

variable [Fintype V] [DecidableEq V]

/-- The arcs from `A` to `B`. -/
def arcs (A B : Finset V) : ℕ := ∑ u ∈ A, ∑ v ∈ B, G.c u v

/-- **The oracle**: the number of arcs leaving `S`. -/
def out (S : Finset V) : ℕ := G.arcs S Sᶜ

/-- The pair multiplicities between `A` and `B`. -/
def pairs (A B : Finset V) : ℕ := ∑ u ∈ A, ∑ v ∈ B, G.sym u v

/-- The symmetrized cut. -/
def symCut (S : Finset V) : ℕ := G.pairs S Sᶜ

/-- Out-degree. -/
def outdeg (v : V) : ℕ := ∑ u, G.c v u

/-- In-degree. -/
def indeg (v : V) : ℕ := ∑ u, G.c u v

omit [Fintype V] [DecidableEq V] in
theorem pairs_eq (A B : Finset V) : G.pairs A B = G.arcs A B + G.arcs B A := by
  unfold pairs arcs sym
  rw [sum_comm (s := B)]
  simp only [sum_add_distrib]

omit [Fintype V] [DecidableEq V] in
theorem pairs_comm (A B : Finset V) : G.pairs A B = G.pairs B A := by
  rw [pairs_eq, pairs_eq, Nat.add_comm]

omit [Fintype V] in
theorem arcs_union_left {A B : Finset V} (h : Disjoint A B) (C : Finset V) :
    G.arcs (A ∪ B) C = G.arcs A C + G.arcs B C := by
  unfold arcs; rw [sum_union h]

omit [Fintype V] in
theorem arcs_union_right (A : Finset V) {B C : Finset V} (h : Disjoint B C) :
    G.arcs A (B ∪ C) = G.arcs A B + G.arcs A C := by
  unfold arcs; rw [← sum_add_distrib]; exact sum_congr rfl fun u _ => sum_union h

omit [DecidableEq V] in
theorem arcs_univ_right (A : Finset V) : G.arcs A univ = ∑ u ∈ A, G.outdeg u := rfl

omit [DecidableEq V] in
theorem arcs_univ_left (B : Finset V) : G.arcs univ B = ∑ v ∈ B, G.indeg v := by
  unfold arcs indeg; rw [sum_comm]

theorem arcs_split_right (A S : Finset V) : G.arcs A univ = G.arcs A S + G.arcs A Sᶜ := by
  rw [← G.arcs_union_right A disjoint_compl_right, union_compl]

theorem arcs_split_left (S B : Finset V) : G.arcs univ B = G.arcs S B + G.arcs Sᶜ B := by
  rw [← G.arcs_union_left disjoint_compl_right B, union_compl]

/-- **Three-cut identity.** For disjoint shores, `F(A) + F(B) = F(A ∪ B) + Σ_{A×B} sym`. -/
theorem out_add_out {A B : Finset V} (h : Disjoint A B) :
    G.out A + G.out B = G.out (A ∪ B) + G.pairs A B := by
  have hA : Aᶜ = B ∪ (A ∪ B)ᶜ := by
    ext x; simp only [mem_compl, mem_union]
    constructor
    · intro hx; by_cases hb : x ∈ B
      · exact Or.inl hb
      · exact Or.inr (by tauto)
    · rintro (hb | hx)
      · exact fun ha => disjoint_left.mp h ha hb
      · tauto
  have hB : Bᶜ = A ∪ (A ∪ B)ᶜ := by
    ext x; simp only [mem_compl, mem_union]
    constructor
    · intro hx; by_cases ha : x ∈ A
      · exact Or.inl ha
      · exact Or.inr (by tauto)
    · rintro (ha | hx)
      · exact fun hb => disjoint_left.mp h ha hb
      · tauto
  have dA : Disjoint B (A ∪ B)ᶜ := disjoint_left.mpr fun x hx hc =>
    (mem_compl.mp hc) (mem_union_right _ hx)
  have dB : Disjoint A (A ∪ B)ᶜ := disjoint_left.mpr fun x hx hc =>
    (mem_compl.mp hc) (mem_union_left _ hx)
  unfold out
  rw [hA, hB, G.arcs_union_right A dA, G.arcs_union_right B dB, G.arcs_union_left h,
    pairs_eq]
  ring

/-- The pair count between disjoint shores from three oracle answers. -/
theorem pairs_eq_out {A B : Finset V} (h : Disjoint A B) :
    G.pairs A B = G.out A + G.out B - G.out (A ∪ B) := by
  rw [G.out_add_out h]; omega

/-- `2 F(S) = cut_sym(S) + Σ_{v∈S} (d⁺(v) − d⁻(v))`, over the integers. -/
theorem two_mul_out (S : Finset V) :
    2 * (G.out S : ℤ) = G.symCut S + ∑ v ∈ S, ((G.outdeg v : ℤ) - G.indeg v) := by
  have h1 := G.arcs_split_right S S
  have h2 := G.arcs_split_left S S
  rw [G.arcs_univ_right] at h1
  rw [G.arcs_univ_left] at h2
  have h1' : (∑ v ∈ S, (G.outdeg v : ℤ)) = G.arcs S S + G.arcs S Sᶜ := by exact_mod_cast h1
  have h2' : (∑ v ∈ S, (G.indeg v : ℤ)) = G.arcs S S + G.arcs Sᶜ S := by exact_mod_cast h2
  rw [sum_sub_distrib, h1', h2', symCut, pairs_eq, out]
  push_cast; ring

/-- `F(S) + (arcs inside S) = Σ_{v∈S} d⁺(v)`. -/
theorem out_add_arcs_self (S : Finset V) : G.out S + G.arcs S S = ∑ v ∈ S, G.outdeg v := by
  rw [← G.arcs_univ_right, G.arcs_split_right S S, out]; ring

omit [Fintype V] [DecidableEq V] in
/-- The arcs inside `S` are the pair multiplicities of its unordered pairs. -/
theorem arcs_self_eq_sum_lt [LinearOrder V] (S : Finset V) :
    G.arcs S S = ∑ u ∈ S, ∑ v ∈ S.filter (u < ·), G.sym u v := by
  unfold arcs sym
  have hsplit : ∀ u ∈ S, ∑ v ∈ S, G.c u v =
      ∑ v ∈ S.filter (u < ·), G.c u v + ∑ v ∈ S.filter (· < u), G.c u v := by
    intro u _
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun v _ => ?_
    rcases lt_trichotomy u v with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [G.diag]
    · simp [h, not_lt.mpr h.le]
  rw [sum_congr rfl hsplit, sum_add_distrib]
  simp only [sum_add_distrib]
  congr 1
  simp only [sum_filter]
  rw [sum_comm]

/-- **`F(S) = Σ_{v∈S} d⁺(v) − Σ_{u<v in S} sym u v`.** -/
theorem out_eq_sum_outdeg [LinearOrder V] (S : Finset V) :
    G.out S = ∑ v ∈ S, G.outdeg v - ∑ u ∈ S, ∑ v ∈ S.filter (u < ·), G.sym u v := by
  rw [← G.arcs_self_eq_sum_lt, ← G.out_add_arcs_self]; omega

end DiGraph
end CutQueryComplexity
