import CutQueryComplexity.GHReduction.RandomTableFailure

/-! # Executed randomized tables with different finite output types

Each frontier block has its own auxiliary vertex type. The dependent table
keeps these types, runs every named entry, and adds actual query counts.
Failure accounting follows the same finite bind order as the implementation.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal BigOperators
open Probability

variable {I A J : Type} {O : J → Type} {q : ℕ} [DecidableEq J]

def dependentRandomTableAux (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) :
    (L : List J) → RTree I A ((j : J) → O j) (L.length * q)
  | [] => RTree.pure (PMF.pure fallback)
  | j :: L => ((f j).bind (fun value =>
      (dependentRandomTableAux fallback f L).map (fun output => Function.update output j value))).cast
        (by simp only [List.length_cons, Nat.succ_mul]; omega)

theorem dependentRandomTableAux_entry_support (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (L : List J) (read : I → A)
    {output : (j : J) → O j}
    (hout : output ∈ ((dependentRandomTableAux fallback f L).eval read).support)
    {j : J} (hj : j ∈ L) : output j ∈ ((f j).eval read).support := by
  induction L generalizing output with
  | nil => simp at hj
  | cons k L ih =>
      simp only [dependentRandomTableAux, RTree.eval_cast, RTree.eval_bind] at hout
      obtain ⟨value, hvalue, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      rw [RTree.eval_map] at hnext
      obtain ⟨tail, htail, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      rw [← heq]
      by_cases hjk : j = k
      · subst j
        simpa only [Function.update_self] using hvalue
      · rw [Function.update_of_ne hjk]
        exact ih htail ((List.mem_cons.mp hj).resolve_left hjk)

theorem dependentRandomTableAux_cost (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (L : List J) (read : I → A)
    (scale : ℕ) (budget : J → ℕ)
    (hf : ∀ j ∈ L, ∀ p ∈ (RTree.run read (f j)).support, scale * p.2 ≤ budget j)
    {p : ((j : J) → O j) × ℕ}
    (hp : p ∈ (RTree.run read (dependentRandomTableAux fallback f L)).support) :
    scale * p.2 ≤ (L.map budget).sum := by
  induction L generalizing p with
  | nil =>
      simp only [dependentRandomTableAux, RTree.run_pure, PMF.pure_map] at hp
      have heq := (PMF.mem_support_pure_iff _ _).mp hp
      subst p
      simp
  | cons j L ih =>
      simp only [dependentRandomTableAux, RTree.run_cast, RTree.run_bind] at hp
      obtain ⟨first, hfirst, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      obtain ⟨second, hsecond, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      rw [random_run_map] at hsecond
      obtain ⟨tail, htail, htailEq⟩ := (PMF.mem_support_map_iff _ _ _).mp hsecond
      have hfirstCost := hf j List.mem_cons_self first hfirst
      have htailCost := ih (fun k hk => hf k (List.mem_cons_of_mem _ hk)) htail
      rw [← heq, ← htailEq]
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      exact Nat.add_le_add hfirstCost htailCost

theorem dependentRandomTableAux_failure_le (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (L : List J) (read : I → A)
    (Good : (j : J) → O j → Prop) (δ : J → ℝ≥0∞)
    (hgood : ∀ j ∈ L, mass ((f j).eval read) (fun output => ¬Good j output) ≤ δ j) :
    mass ((dependentRandomTableAux fallback f L).eval read)
      (fun output => ¬∀ j ∈ L, Good j (output j)) ≤ (L.map δ).sum := by
  induction L with
  | nil => simp [dependentRandomTableAux]
  | cons j L ih =>
      have htail := ih (fun k hk => hgood k (List.mem_cons_of_mem _ hk))
      simp only [dependentRandomTableAux, RTree.eval_cast, RTree.eval_bind,
        List.map_cons, List.sum_cons]
      apply mass_bind_le_add _ _ (fun first => ¬Good j first) _
        (hgood j List.mem_cons_self)
      intro first hfirst
      have hj : Good j first := not_not.mp hfirst
      rw [RTree.eval_map, mass_map]
      apply le_trans (mass_mono _ ?_) htail
      intro tail hfail htailGood
      apply hfail
      intro k hk
      by_cases hkj : k = j
      · subst k
        simpa only [Function.update_self] using hj
      · rw [Function.update_of_ne hkj]
        exact htailGood k ((List.mem_cons.mp hk).resolve_left hkj)

def dependentRandomTable [Fintype J] (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) :
    RTree I A ((j : J) → O j) (Fintype.card J * q) :=
  (dependentRandomTableAux fallback f (Finset.univ : Finset J).toList).cast (by simp)

theorem dependentRandomTable_entry_support [Fintype J] (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (read : I → A) {output : (j : J) → O j}
    (hout : output ∈ ((dependentRandomTable fallback f).eval read).support) (j : J) :
    output j ∈ ((f j).eval read).support := by
  apply dependentRandomTableAux_entry_support fallback f Finset.univ.toList read
    (by simpa only [dependentRandomTable, RTree.eval_cast] using hout)
  simp

theorem dependentRandomTable_cost [Fintype J] (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (read : I → A) (scale : ℕ) (budget : J → ℕ)
    (hf : ∀ j, ∀ p ∈ (RTree.run read (f j)).support, scale * p.2 ≤ budget j)
    {p : ((j : J) → O j) × ℕ}
    (hp : p ∈ (RTree.run read (dependentRandomTable fallback f)).support) :
    scale * p.2 ≤ ∑ j, budget j := by
  have h := dependentRandomTableAux_cost fallback f Finset.univ.toList read scale budget
    (fun j _ => hf j) (by simpa only [dependentRandomTable, RTree.run_cast] using hp)
  simpa only [Finset.sum_map_toList] using h

theorem dependentRandomTable_failure_le [Fintype J] (fallback : (j : J) → O j)
    (f : (j : J) → RTree I A (O j) q) (read : I → A)
    (Good : (j : J) → O j → Prop) (δ : J → ℝ≥0∞)
    (hgood : ∀ j, mass ((f j).eval read) (fun output => ¬Good j output) ≤ δ j) :
    mass ((dependentRandomTable fallback f).eval read)
      (fun output => ¬∀ j, Good j (output j)) ≤ ∑ j, δ j := by
  have h := dependentRandomTableAux_failure_le fallback f Finset.univ.toList read Good δ
    (fun j _ => hgood j)
  simpa only [dependentRandomTable, RTree.eval_cast, Finset.mem_toList, Finset.mem_univ,
    forall_true_left, Finset.sum_map_toList] using h

end
end CutQueryComplexity.GHReduction
