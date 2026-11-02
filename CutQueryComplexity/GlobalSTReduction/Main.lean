import CutQueryComplexity.GlobalSTReduction.Asymptotics
import CutQueryComplexity.GlobalSTReduction.Examples

/-! # Randomized global minimum cut from a real-weight s-t family

The public facade of `GlobalSTReduction`. For undirected graphs with arbitrary
nonnegative real weights on `Fin n`, `n ≥ 2`, and any confidence `b`:

* `exists_global_from_st`: from a deterministic `RealSTFamily Q` that returns
  *some* minimum s-t shore, with `SizeRegular n Q`, one public randomized
  program with cap `detGlobalBudget n b Q = O(Q(n) log³ n + n log² n)`
  (`detGlobalBudget_isBigO`). Every output is a proper shore with its exact
  value; it is a global minimum shore except with probability `(n+2)^{-b}`.
* `exists_global_from_randomized_st`: the same from a `RandomRealSTFamily Q`
  that fails with probability at most `1/3`, with cap
  `randomGlobalBudget n b Q = O((Q(n) + n) log⁴ n)`
  (`randomGlobalBudget_isBigO`) and failure `2 (n+2)^{-b}`.

No budget depends on edge weights, and neither family has an integrality,
capacity or precision promise or needs canonical answers. The method is the
isolating-cut lemma with threshold terminal sampling (Li–Panigrahi):
`Isolating`, `Sampling`, `Program`. `Calls.mass_interpRand_compile_le` is the
adaptive union bound over the calls of a compiled call program.
`Examples.exists_global_reconstruction` applies the deterministic endpoint to a
family whose answers are not canonical.
-/

set_option autoImplicit false

namespace CutQueryComplexity.GlobalSTReduction

/-- Both Phase 0 targets hold: global minimum cut from a deterministic or a
randomized real-weight s-t family. -/
theorem globalFromST_targets : DetGlobalTarget ∧ RandomGlobalTarget :=
  ⟨detGlobalTarget, randomGlobalTarget⟩

end CutQueryComplexity.GlobalSTReduction
