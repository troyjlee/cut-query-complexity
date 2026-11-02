import CutQueryComplexity.AllPairsAudit.Star
import CutQueryComplexity.Model.RandomizedReduction

/-!
# Public triangles remove the minimum-degree restriction

Attach a private triangle to each original vertex. The original vertex is one
corner, and the other two corners have no other incident edges. This raises all
degrees to at least two and preserves every original terminal minimum. Each
padded cut is one original cut plus the explicitly known triangle cut.
The construction therefore avoids a separate adaptive leaf-peeling algorithm.
-/

set_option autoImplicit false

namespace CutQueryComplexity.AllPairs

open Finset WeightedGraph AllPairsAudit
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev Padded (V : Type) := V ⊕ (V ⊕ V)

def embeddedGraph (G : WeightedGraph V) : WeightedGraph (Padded V) where
  w
    | .inl u, .inl v => G.w u v
    | _, _ => 0
  symm u v := by cases u <;> cases v <;> simp [G.symm]
  nonneg u v := by cases u <;> cases v <;> simp [G.nonneg]
  diag u := by cases u <;> simp [G.diag]

/-- The six directed incidences of each public triangle. -/
def triangleGraph : WeightedGraph (Padded V) where
  w
    | .inl u, .inr (.inl v) => if u = v then 1 else 0
    | .inl u, .inr (.inr v) => if u = v then 1 else 0
    | .inr (.inl u), .inl v => if u = v then 1 else 0
    | .inr (.inr u), .inl v => if u = v then 1 else 0
    | .inr (.inl u), .inr (.inr v) => if u = v then 1 else 0
    | .inr (.inr u), .inr (.inl v) => if u = v then 1 else 0
    | _, _ => 0
  symm u v := by
    rcases u with u | u <;> rcases v with v | v
    · rfl
    · cases v <;> simp [eq_comm]
    · cases u <;> simp [eq_comm]
    · cases u <;> cases v <;> simp [eq_comm]
  nonneg u v := by
    rcases u with u | u <;> rcases v with v | v
    · simp
    · cases v <;> dsimp <;> split <;> norm_num
    · cases u <;> dsimp <;> split <;> norm_num
    · cases u <;> cases v <;> dsimp <;> (try split) <;> norm_num
  diag u := by
    rcases u with u | u
    · rfl
    · cases u <;> rfl

def paddedGraph (G : WeightedGraph V) : WeightedGraph (Padded V) where
  w u v := (embeddedGraph G).w u v + triangleGraph.w u v
  symm u v := by rw [(embeddedGraph G).symm u v, triangleGraph.symm u v]
  nonneg u v := add_nonneg ((embeddedGraph G).nonneg u v) (triangleGraph.nonneg u v)
  diag u := by simp [(embeddedGraph G).diag u, triangleGraph.diag u]

/-- Lift an original shore by taking the entire triangle at each member. -/
def triangleLift (S : Finset V) : Finset (Padded V) := S.disjSum (S.disjSum S)

@[simp] theorem triangleLift_original (S : Finset V) :
    originalShore (triangleLift S) = S := by ext; simp [triangleLift]

omit [DecidableEq V] in
theorem padded_card : Fintype.card (Padded V) = 3 * Fintype.card V := by
  simp only [Padded, Fintype.card_sum]
  omega

theorem embedded_cut (G : WeightedGraph V) (A : Finset (Padded V)) :
    (embeddedGraph G).cut A = G.cut (originalShore A) := by
  simp [cut_eq_sum_ite, Fintype.sum_sum_type, embeddedGraph]

theorem padded_cut_eq (G : WeightedGraph V) (A : Finset (Padded V)) :
    (paddedGraph G).cut A = G.cut (originalShore A) + triangleGraph.cut A := by
  change (∑ u ∈ A, ∑ v ∈ Aᶜ,
    ((embeddedGraph G).w u v + triangleGraph.w u v)) = _
  simp only [sum_add_distrib]
  change (embeddedGraph G).cut A + triangleGraph.cut A = _
  rw [embedded_cut]

theorem triangle_cut_lift (S : Finset V) :
    triangleGraph.cut (triangleLift S) = 0 := by
  apply sum_eq_zero
  intro u hu
  apply sum_eq_zero
  intro v hv
  have hv' : v ∉ triangleLift S := mem_compl.mp hv
  rcases u with u | u <;> rcases v with v | v
  · rfl
  · rcases v with v | v <;> dsimp [triangleGraph] <;> split_ifs with h
    · subst v; exact False.elim (hv' (by simpa [triangleLift] using hu))
    · rfl
    · subst v; exact False.elim (hv' (by simpa [triangleLift] using hu))
    · rfl
  · rcases u with u | u <;> dsimp [triangleGraph] <;> split_ifs with h
    · subst v; exact False.elim (hv' (by simpa [triangleLift] using hu))
    · rfl
    · subst v; exact False.elim (hv' (by simpa [triangleLift] using hu))
    · rfl
  · rcases u with u | u <;> rcases v with v | v
    · rfl
    · dsimp [triangleGraph]
      split_ifs with h
      · subst v; exact False.elim (hv' (by simpa [triangleLift] using hu))
      · rfl
    · dsimp [triangleGraph]
      split_ifs with h
      · subst v; exact False.elim (hv' (by simpa [triangleLift] using hu))
      · rfl
    · rfl

theorem padded_cut_lift (G : WeightedGraph V) (S : Finset V) :
    (paddedGraph G).cut (triangleLift S) = G.cut S := by
  rw [padded_cut_eq, triangleLift_original, triangle_cut_lift, add_zero]

theorem padded_cut_dominates (G : WeightedGraph V) (A : Finset (Padded V)) :
    G.cut (originalShore A) ≤ (paddedGraph G).cut A := by
  rw [padded_cut_eq]
  exact le_add_of_nonneg_right (triangleGraph.cut_nonneg A)

theorem triangle_degree (v : Padded V) : triangleGraph.degree v = 2 := by
  rcases v with v | v
  · norm_num [degree, Fintype.sum_sum_type, triangleGraph]
  · rcases v with v | v <;> norm_num [degree, Fintype.sum_sum_type, triangleGraph]

theorem padded_min_degree (G : WeightedGraph V) (v : Padded V) :
    2 ≤ (paddedGraph G).degree v := by
  have hn := AllPairsAudit.degree_nonneg (embeddedGraph G) v
  change 2 ≤ ∑ u, ((embeddedGraph G).w v u + triangleGraph.w v u)
  rw [sum_add_distrib]
  change 2 ≤ (embeddedGraph G).degree v + triangleGraph.degree v
  rw [triangle_degree]
  linarith

omit [Fintype V] in
theorem padded_unweighted {G : WeightedGraph V} (hG : Unweighted G) :
    Unweighted (paddedGraph G) := by
  intro u v
  rcases u with u | u <;> rcases v with v | v
  · simpa [paddedGraph, embeddedGraph, triangleGraph] using hG u v
  · rcases v with v | v <;> simp only [paddedGraph, embeddedGraph, triangleGraph, zero_add]
    all_goals by_cases h : u = v <;> simp [h]
  · rcases u with u | u <;> simp only [paddedGraph, embeddedGraph, triangleGraph, zero_add]
    all_goals by_cases h : u = v <;> simp [h]
  · rcases u with u | u <;> rcases v with v | v
    all_goals simp only [paddedGraph, embeddedGraph, triangleGraph, zero_add]
    all_goals first | exact Or.inl rfl | (by_cases h : u = v <;> simp [h])

/-- Every padded minimum for two original terminals extracts with exact value.
No degree, connectedness, or positive minimum-cut promise is needed. -/
theorem padded_minimum_extract (G : WeightedGraph V) {s t : V}
    {A : Finset (Padded V)}
    (hA : IsSTMinCut (paddedGraph G) (.inl s) (.inl t) A) :
    IsSTMinCut G s t (originalShore A) ∧
      (paddedGraph G).cut A = G.cut (originalShore A) := by
  have hs : s ∈ originalShore A := by simpa using hA.1
  have ht : t ∉ originalShore A := by simpa using hA.2.1
  have hupper := hA.2.2 (triangleLift (originalShore A))
    (by simpa [triangleLift] using hs) (by simpa [triangleLift] using ht)
  rw [padded_cut_lift] at hupper
  refine ⟨⟨hs, ht, ?_⟩, le_antisymm hupper (padded_cut_dominates G A)⟩
  intro S hsS htS
  have h := hA.2.2 (triangleLift S)
    (by simpa [triangleLift] using hsS) (by simpa [triangleLift] using htS)
  rw [padded_cut_lift] at h
  exact (padded_cut_dominates G A).trans h

/-- An actual one-query implementation of each padded cut. -/
def paddedQuery (A : Finset (Padded V)) : DTree (Finset V) ℝ ℝ 1 :=
  DTree.query (originalShore A) fun answer => DTree.pure (answer + triangleGraph.cut A)

theorem paddedQuery_eval (G : WeightedGraph V) (A : Finset (Padded V)) :
    (paddedQuery A).eval G.cut = (paddedGraph G).cut A := by
  simp only [paddedQuery, DTree.eval_query, DTree.eval_pure, padded_cut_eq]

/-- Substitution preserves a randomized padded algorithm's distribution and
public query budget exactly, since each padded query costs one original query. -/
theorem padded_substitute_eval {O : Type} {q : ℕ}
    (T : RTree (Finset (Padded V)) ℝ O q) (G : WeightedGraph V) :
    (T.substitute paddedQuery).eval G.cut = T.eval (paddedGraph G).cut := by
  simp only [RTree.eval_substitute, paddedQuery_eval]

end
end CutQueryComplexity.AllPairs

#print axioms CutQueryComplexity.AllPairs.padded_min_degree
#print axioms CutQueryComplexity.AllPairs.padded_unweighted
#print axioms CutQueryComplexity.AllPairs.padded_minimum_extract
#print axioms CutQueryComplexity.AllPairs.padded_substitute_eval
