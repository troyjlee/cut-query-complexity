import CutQueryComplexity.DetMinCut.Normalize

/-! # Safe partitions for tree cut sparsifier discovery

The nonempty fibers of a map `r : V → V` form a partition of `V`.
It is safe for `G` when every global minimum-cut shore is a union of
these fibers. This preserves every minimum cut, rather than only its value
or one chosen optimum. The quotient uses `Cls r`, so unused labels of
`r` do not create empty parts.

This definition does not require positive minimum-cut value. The positive
minimum-cut hypothesis belongs to the learning theorem.
-/

set_option autoImplicit false

namespace CutQueryComplexity.DetMinCut

open WeightedGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The partition into the nonempty fibers of `r` is safe if no global
minimum cut separates two vertices in the same part. -/
def SafePartition (G : WeightedGraph V) (r : V → V) : Prop :=
  ∀ S : Finset V, IsMinCut G S → Sat r S

/-- Every minimum-cut shore is a union of parts, expressed as a pullback
of a shore of the quotient. -/
theorem safePartition_iff_minCut_is_union (G : WeightedGraph V) (r : V → V) :
    SafePartition G r ↔
      ∀ S : Finset V, IsMinCut G S →
        ∃ T : Finset (Cls r), pull (proj r) T = S := by
  constructor
  · intro h S hS
    exact ⟨S.image (proj r), pull_image_of_sat (h S hS)⟩
  · intro h S hS
    obtain ⟨T, hT⟩ := h S hS
    rw [← hT]
    exact sat_pull r T

/-- The partition into singletons is safe. -/
@[simp] theorem safePartition_id (G : WeightedGraph V) : SafePartition G id := by
  intro S _ x y hxy
  change x = y at hxy
  rw [hxy]

/-- Refining a safe partition remains safe. The implication on equal labels
says that every new part is contained in an old part. -/
theorem SafePartition.of_refinement {G : WeightedGraph V} {r r' : V → V}
    (h : SafePartition G r)
    (href : ∀ x y, r' x = r' y → r x = r y) : SafePartition G r' := by
  intro S hS x y hxy
  exact h S hS x y (href x y hxy)

/-- Every original minimum-cut shore survives in the quotient with its
cut value unchanged. -/
theorem SafePartition.exists_quotient_cut {G : WeightedGraph V} {r : V → V}
    (h : SafePartition G r) {S : Finset V} (hS : IsMinCut G S) :
    ∃ T : Finset (Cls r), pull (proj r) T = S ∧ (quot G r).cut T = G.cut S := by
  have hsat : Sat r S := h S hS
  refine ⟨S.image (proj r), pull_image_of_sat hsat, ?_⟩
  rw [cut_contract, pull_image_of_sat hsat]

end CutQueryComplexity.DetMinCut

