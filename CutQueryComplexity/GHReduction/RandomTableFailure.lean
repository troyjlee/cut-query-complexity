import CutQueryComplexity.GHReduction.RandomPrograms

/-! # Conditional failure accounting for finite query tables

The union bound follows the program's bind order. Entry programs can be chosen
from the complete preceding history; no independence of different invocations
in an outer recursion is used.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GHReduction
noncomputable section
open scoped Classical ENNReal BigOperators
open Probability

variable {I A O J : Type} {q : ℕ} [DecidableEq J]

theorem randomTableAux_failure_le (fallback : O) (f : J → RTree I A O q)
    (L : List J) (read : I → A) (Good : J → O → Prop) (δ : J → ℝ≥0∞)
    (hgood : ∀ j ∈ L, mass ((f j).eval read) (fun output => ¬Good j output) ≤ δ j) :
    mass ((randomTableAux fallback f L).eval read)
      (fun output => ¬∀ j ∈ L, Good j (output j)) ≤ (L.map δ).sum := by
  induction L with
  | nil => simp [randomTableAux]
  | cons j L ih =>
    have htail := ih (fun k hk => hgood k (List.mem_cons_of_mem _ hk))
    simp only [randomTableAux, RTree.eval_cast, RTree.eval_bind,
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

theorem randomTable_failure_le [Fintype J] (fallback : O) (f : J → RTree I A O q)
    (read : I → A) (Good : J → O → Prop) (δ : J → ℝ≥0∞)
    (hgood : ∀ j, mass ((f j).eval read) (fun output => ¬Good j output) ≤ δ j) :
    mass ((randomTable fallback f).eval read) (fun output => ¬∀ j, Good j (output j)) ≤
      ∑ j, δ j := by
  have h := randomTableAux_failure_le fallback f Finset.univ.toList read Good δ
    (fun j _ => hgood j)
  simpa only [randomTable, RTree.eval_cast, Finset.mem_toList, Finset.mem_univ,
    forall_true_left, Finset.sum_map_toList] using h

end
end CutQueryComplexity.GHReduction
