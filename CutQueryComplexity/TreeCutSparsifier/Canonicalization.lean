import CutQueryComplexity.TreeCutSparsifier.Basic
import CutQueryComplexity.Hierarchy.Canonicalize

/-! # Canonicalization of an explicit tree cut sparsifier

The input is an explicit rooted tree with nonnegative capacities (`TreeData`), with terminals
anywhere: at internal nodes or at the root, with empty or repeated clusters, and with no bound on
its number of nodes. The promise `TreeData.Approximates G B` says only that its representation
costs lie between every cut of `G` and `B` times that cut; it is weaker than `TreeData.Good`,
which also asks for canonical capacities, childless terminals and a size bound.

`canonicalize input` selects the normalized topology `normalTopology input.tree` from the
supplied tree alone, then queries the cut of each nonroot cluster once (`learnNonroot`); the
root capacity is set to zero without a query. Every answer is clipped at zero, so the output is
well-formed `TreeData` on any transcript, and the query count is `m − 1 ≤ 2n − 2` on every
answer function. On a graph oracle the capacities are exactly the canonical ones, the output is
`Good G B` and `Normal`, and no representation cost exceeds the input's (`canonicalize_spec`).
`exists_canonicalization` compiles this to one decision tree per input tree with cap `2n − 2`.

The input is encoded as an explicit rooted tree (`Pkg`, a `RootedTree` on `Fin m` with an
injective terminal map); an arbitrary finite undirected tree with chosen capacities admits such
an offline rooting, and an adapter from `SimpleGraph.IsTree` would be a separate representation
lemma, not a premise here.
-/

set_option autoImplicit false

namespace CutQueryComplexity.TreeCutSparsifier

open WeightedGraph Search Search.Comp Hierarchy Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The input promise -/

/-- The representation costs of the explicit tree lie between every cut and `B` times it. -/
def TreeData.Approximates (input : TreeData V) (G : WeightedGraph V) (B : ℝ) : Prop :=
  ∀ S, G.cut S ≤ input.tree.H.rep input.cap S ∧ input.tree.H.rep input.cap S ≤ B * G.cut S

theorem TreeData.Good.approximates {G : WeightedGraph V} {α : ℝ} {out : TreeData V}
    (h : out.Good G α) : out.Approximates G α :=
  h.cuts

theorem TreeData.Approximates.dom {input : TreeData V} {G : WeightedGraph V} {B : ℝ}
    (h : input.Approximates G B) : ∀ S, G.cut S ≤ input.tree.H.rep input.cap S :=
  fun S => (h S).1

/-! ## Learning the nonroot capacities -/

/-- Query the cluster of every nonroot node once, in a fixed order; the root capacity is zero.
Answers are clipped at zero so that any transcript yields nonnegative capacities. -/
noncomputable def learnNonroot (P : Pkg V) : Comp (Finset V) ℝ (TreeData V) :=
  (tabulate (fun x => ask (P.H.cluster x)) (univ.erase P.H.T.root).toList).map fun values =>
    ⟨P, fun x => max 0 ((values x).getD 0), fun _ => le_max_left _ _⟩

/-- On a graph oracle the learned capacities are the canonical ones. -/
theorem learnNonroot_eval (P : Pkg V) (G : WeightedGraph V) :
    (learnNonroot P).eval G.cut = canonicalTree P G := by
  simp only [learnNonroot, eval_map, eval_tabulate, eval_ask, mem_toList]
  unfold canonicalTree
  congr 1
  funext x
  by_cases hx : x = P.H.T.root
  · subst hx
    simp [Hier.canon, Hier.cluster_root]
  · simp [hx, Hier.canon, max_eq_right (G.cut_nonneg _)]

omit [DecidableEq V] in
/-- Exactly `m − 1` queries on every answer function. -/
theorem learnNonroot_cost (P : Pkg V) (read : Finset V → ℝ) :
    (learnNonroot P).cost read = P.m - 1 := by
  simp only [learnNonroot, cost_map, cost_tabulate, cost_ask, List.map_const', List.sum_replicate,
    smul_eq_mul, mul_one, length_toList, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin]

/-! ## The canonicalization program -/

variable [Nonempty V]

/-- Normalize the topology offline, then learn its nonroot canonical capacities. -/
noncomputable def canonicalize (input : TreeData V) : Comp (Finset V) ℝ (TreeData V) :=
  learnNonroot (normalTopology input.tree)

theorem canonicalize_eval (input : TreeData V) (G : WeightedGraph V) :
    (canonicalize input).eval G.cut = canonicalTree (normalTopology input.tree) G :=
  learnNonroot_eval _ G

/-- At most `2n − 2` queries on every answer function. -/
theorem canonicalize_cost (input : TreeData V) (read : Finset V → ℝ) :
    (canonicalize input).cost read ≤ 2 * Fintype.card V - 2 := by
  rw [canonicalize, learnNonroot_cost]
  have := (normalTopology_normal input.tree).size
  omega

/-- The normalized tree with canonical capacities, in terms of the input promise. -/
theorem TreeData.normalTopology_rep_le (input : TreeData V) (G : WeightedGraph V)
    (hdom : ∀ S, G.cut S ≤ input.tree.H.rep input.cap S) (S : Finset V) :
    G.cut S ≤ (normalTopology input.tree).H.rep ((normalTopology input.tree).H.canon G) S ∧
      (normalTopology input.tree).H.rep ((normalTopology input.tree).H.canon G) S ≤
        input.tree.H.rep input.cap S :=
  Hierarchy.normalTopology_rep_le input.tree input.cap input.cap_nonneg G hdom S

/-- **Canonicalization.** On every graph that the input approximates within `B`, the output has
the normalized topology, canonical capacities, is a `Good` `B`-tree cut sparsifier, and has no
larger representation cost than the input on any shore. -/
theorem canonicalize_spec (input : TreeData V) (G : WeightedGraph V) {B : ℝ}
    (h : input.Approximates G B) :
    ((canonicalize input).eval G.cut).tree = normalTopology input.tree ∧
    ((canonicalize input).eval G.cut).tree.Normal ∧
    ((canonicalize input).eval G.cut).cap =
      ((canonicalize input).eval G.cut).tree.H.canon G ∧
    ((canonicalize input).eval G.cut).Good G B ∧
    ∀ S, ((canonicalize input).eval G.cut).tree.H.rep ((canonicalize input).eval G.cut).cap S ≤
      input.tree.H.rep input.cap S := by
  rw [canonicalize_eval]
  have hN := normalTopology_normal input.tree
  have hrep := input.normalTopology_rep_le G h.dom
  refine ⟨rfl, hN, rfl, ?_, fun S => (hrep S).2⟩
  refine canonicalTree_good _ G ?_ hN.leaves fun S => ?_
  · have := hN.size; omega
  · exact (hrep S).2.trans (h S).2

/-- Compatibility: an output that is already `Good` is normalized without loss. -/
theorem canonicalize_good (input : TreeData V) (G : WeightedGraph V) {α : ℝ}
    (h : input.Good G α) :
    ((canonicalize input).eval G.cut).tree.Normal ∧ ((canonicalize input).eval G.cut).Good G α ∧
    ∀ S, ((canonicalize input).eval G.cut).tree.H.rep ((canonicalize input).eval G.cut).cap S ≤
      input.tree.H.rep input.cap S :=
  let s := canonicalize_spec input G h.approximates
  ⟨s.2.1, s.2.2.2.1, s.2.2.2.2⟩

end CutQueryComplexity.TreeCutSparsifier

namespace CutQueryComplexity.TreeCutSparsifier

open WeightedGraph Search Search.Comp Hierarchy

/-- **Public canonicalization endpoint.** For every `n ≥ 1` and every explicit input tree on
`Fin n`, a topology `P` and a decision tree, both selected from the input tree alone, such that
`P` has the structural guarantees and contains every nonempty input cluster, the decision tree
makes at most `2n − 2` queries on every answer function, and on every graph approximated by the
input within any `B` it returns `P` with its canonical capacities: a `Good` `B`-tree cut
sparsifier with no larger representation cost than the input on any shore. -/
theorem exists_canonicalization (n : ℕ) (hn : 1 ≤ n) (input : TreeData (Fin n)) :
    ∃ (P : Pkg (Fin n)) (D : DTree (Finset (Fin n)) ℝ (Option (TreeData (Fin n))) (2 * n - 2)),
      P.Normal ∧
      (∀ x, (input.tree.H.cluster x).Nonempty → ∃ y, P.H.cluster y = input.tree.H.cluster x) ∧
      (∀ read, D.cost read ≤ 2 * n - 2) ∧
      ∀ (G : WeightedGraph (Fin n)) (B : ℝ), input.Approximates G B →
        ∃ out, D.eval G.cut = some out ∧ out.tree = P ∧ out.cap = out.tree.H.canon G ∧
          out.Good G B ∧ ∀ S, out.tree.H.rep out.cap S ≤ input.tree.H.rep input.cap S := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨normalTopology input.tree, (canonicalize input).toDTree (2 * n - 2),
    normalTopology_normal _, fun x hx => normalTopology_cluster_of_nonempty _ hx,
    fun read => DTree.cost_le _ read, fun G B h => ?_⟩
  obtain ⟨h1, -, h3, h4, h5⟩ := canonicalize_spec input G h
  exact ⟨_, toDTree_eval _ _ (by simpa using canonicalize_cost input G.cut), h1, h3, h4, h5⟩

end CutQueryComplexity.TreeCutSparsifier
