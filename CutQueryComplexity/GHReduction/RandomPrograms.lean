import CutQueryComplexity.GHReduction.Programs
import CutQueryComplexity.Probability.FiniteEvents

/-! # Finite randomized tables with realized query accounting

Every table entry is an actual bounded randomized query tree. Adaptive outer
calls may choose the entire table after earlier answers. This module records
the supported entry outputs and adds their realized query costs.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical

variable {I A O J : Type} {q : ℕ} [DecidableEq J]

theorem random_run_map (T : RTree I A O q) {P : Type} (f : O → P) (read : I → A) :
    RTree.run read (T.map f) = (RTree.run read T).map (fun p => (f p.1, p.2)) := by
  simp [RTree.map, RTree.run_bind, PMF.map, Function.comp_def]

def randomTableAux (fallback : O) (f : J → RTree I A O q) :
    (L : List J) → RTree I A (J → O) (L.length * q)
  | [] => RTree.pure (PMF.pure (fun _ => fallback))
  | j :: L => ((f j).bind (fun value =>
      (randomTableAux fallback f L).map (fun output => Function.update output j value))).cast
        (by simp only [List.length_cons, Nat.succ_mul]; omega)

theorem randomTableAux_entry_support (fallback : O) (f : J → RTree I A O q)
    (L : List J) (read : I → A) {output : J → O}
    (hout : output ∈ ((randomTableAux fallback f L).eval read).support)
    {j : J} (hj : j ∈ L) : output j ∈ ((f j).eval read).support := by
  induction L generalizing output with
  | nil => simp at hj
  | cons k L ih =>
    simp only [randomTableAux, RTree.eval_cast, RTree.eval_bind] at hout
    obtain ⟨value, hvalue, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    rw [RTree.eval_map] at hnext
    obtain ⟨tail, htail, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
    rw [← heq]
    by_cases hjk : j = k
    · subst j
      simpa only [Function.update_self] using hvalue
    · rw [Function.update_of_ne hjk]
      exact ih htail ((List.mem_cons.mp hj).resolve_left hjk)

theorem randomTableAux_cost (fallback : O) (f : J → RTree I A O q)
    (L : List J) (read : I → A) (scale : ℕ) (budget : J → ℕ)
    (hf : ∀ j ∈ L, ∀ p ∈ (RTree.run read (f j)).support, scale * p.2 ≤ budget j)
    {p : (J → O) × ℕ} (hp : p ∈ (RTree.run read (randomTableAux fallback f L)).support) :
    scale * p.2 ≤ (L.map budget).sum := by
  induction L generalizing p with
  | nil =>
    simp only [randomTableAux, RTree.run_pure, PMF.pure_map] at hp
    have heq := (PMF.mem_support_pure_iff _ _).mp hp
    subst p
    simp
  | cons j L ih =>
    simp only [randomTableAux, RTree.run_cast, RTree.run_bind] at hp
    obtain ⟨first, hfirst, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
    obtain ⟨second, hsecond, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
    rw [random_run_map] at hsecond
    obtain ⟨tail, htail, htailEq⟩ := (PMF.mem_support_map_iff _ _ _).mp hsecond
    have hfirstCost := hf j List.mem_cons_self first hfirst
    have htailCost := ih (fun k hk => hf k (List.mem_cons_of_mem _ hk)) htail
    rw [← heq, ← htailEq]
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add hfirstCost htailCost

def randomTable [Fintype J] (fallback : O) (f : J → RTree I A O q) :
    RTree I A (J → O) (Fintype.card J * q) :=
  (randomTableAux fallback f (Finset.univ : Finset J).toList).cast (by simp)

theorem randomTable_entry_support [Fintype J] (fallback : O) (f : J → RTree I A O q)
    (read : I → A) {output : J → O}
    (hout : output ∈ ((randomTable fallback f).eval read).support) (j : J) :
    output j ∈ ((f j).eval read).support := by
  apply randomTableAux_entry_support fallback f Finset.univ.toList read
    (by simpa only [randomTable, RTree.eval_cast] using hout)
  simp

theorem randomTable_cost [Fintype J] (fallback : O) (f : J → RTree I A O q)
    (read : I → A) (scale : ℕ) (budget : J → ℕ)
    (hf : ∀ j, ∀ p ∈ (RTree.run read (f j)).support, scale * p.2 ≤ budget j)
    {p : (J → O) × ℕ} (hp : p ∈ (RTree.run read (randomTable fallback f)).support) :
    scale * p.2 ≤ ∑ j, budget j := by
  have h := randomTableAux_cost fallback f Finset.univ.toList read scale budget
    (fun j _ => hf j) (by simpa only [randomTable, RTree.run_cast] using hp)
  simpa only [Finset.sum_map_toList] using h

end
end CutQueryComplexity.GHReduction
