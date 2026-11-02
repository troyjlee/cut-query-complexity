import CutQueryComplexity.Hierarchy.Supplied

/-! # A constant-quality terminal cut guard (the cut form of Lemma 19)

`ConstantCutGuard ρ₀` is the deferred input of the log-seven bound: for every hierarchy whose
leaf nodes are childless and all nonnegative capacities on its edges (zero allowed), some
graph `J` on the terminals approximates every terminal-extension cost,

  `R(S) ≤ c_J(S) ≤ ρ₀ R(S)`  for all `S`,

with the same `ρ₀` for every size, depth, and weight spread. This is the cut consequence of
the tree case of the terminal flow sparsification theorem of Englert et al. used in Lemma 19
of the deterministic mincut paper. Nodes without terminals below them (for example the free
nodes of `Hier.restrictInl`) are allowed. It is a hypothesis, never an axiom.

`ConstantCutGuard.guardFor` converts it to the `GuardFor` form used by the skeleton program:
a minimizing binary extension is a real extension of cost `R(S)`.
-/

namespace CutQueryComplexity
namespace Hierarchy

open WeightedGraph

/-- **Lemma 19 with constant quality, as a hypothesis.** -/
def ConstantCutGuard (ρ0 : ℝ) : Prop :=
  ∀ (V M : Type) [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M] (H : Hier V M),
    H.LeafChildless → ∀ cap : M → ℝ, (∀ x, 0 ≤ cap x) →
      ∃ J : WeightedGraph V, ∀ S, H.rep cap S ≤ J.cut S ∧ J.cut S ≤ ρ0 * H.rep cap S

namespace Hier

variable {V M : Type} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]

/-- A cut guard is a guard in the sense of `GuardFor`. -/
theorem ConstantCutGuard.guardFor [LinearOrder M] {ρ0 : ℝ} (hg : ConstantCutGuard ρ0)
    {H : Hier V M} (hlc : H.LeafChildless) : H.GuardFor ρ0 := by
  intro cap hcap _
  obtain ⟨J, hJ⟩ := hg V M H hlc cap hcap
  refine ⟨J, fun S => ⟨?_, (hJ S).2⟩⟩
  obtain ⟨ℓ, hℓ, hR⟩ := H.exists_rep_eq cap S
  exact ⟨toReal ℓ, extendsR_toReal hℓ, hR ▸ (hJ S).1⟩

end Hier

end Hierarchy
end CutQueryComplexity
