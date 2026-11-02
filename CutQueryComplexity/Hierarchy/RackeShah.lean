import CutQueryComplexity.Hierarchy.RackeShah.Basic
import CutQueryComplexity.Hierarchy.RackeShah.WeightedMajority
import CutQueryComplexity.Hierarchy.RackeShah.Transport
import CutQueryComplexity.Hierarchy.RackeShah.Partition
import CutQueryComplexity.Hierarchy.RackeShah.LogBounds
import CutQueryComplexity.Hierarchy.RackeShah.Refinement
import CutQueryComplexity.Hierarchy.RackeShah.Decomposition
import CutQueryComplexity.Hierarchy.RackeShah.Construction
import CutQueryComplexity.Hierarchy.RackeShah.Existence

/-! # Offline Räcke–Shah tree cut sparsifiers

The umbrella of `Hierarchy/RackeShah/`: the cut-only formalization of the existential
`O(log n log log n)` bound of Räcke and Shah (ESA 2014) with sparsest-cut factor `β = 1`.
The endpoint is `RackeShah.rackeShah_hierarchyBound` (distortion `268 L(n) L(L(n))`, height
`2 L(n)`), restated as `RackeShah.exists_hierarchyBound_log_mul_loglog`; the explicit-tree
adapter is `TreeCutSparsifier.exists_good_tree_log_mul_loglog`.
-/
