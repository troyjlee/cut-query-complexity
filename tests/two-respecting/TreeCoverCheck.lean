import CutQueryComplexity.TwoRespecting.TreeCover

/-! Axiom checks for the tree cover (Lemma 12) and Corollary 14.

Run with `lake env lean tests/two-respecting/TreeCoverCheck.lean`.
-/

open CutQueryComplexity.TwoRespecting

#print axioms exists_light_spanning
#print axioms exists_tree_covering_quarter
#print axioms exists_tree_cover
#print axioms isTwoRespShore_of_card_le_two
#print axioms weakSkeleton_minCut
#print axioms minCut_of_weakSkeleton
