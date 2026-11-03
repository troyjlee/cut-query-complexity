# Paper 1 in Lean: the headline theorems

**Paper:** [*Finding and Certifying Weighted Minimum Cuts with Cut Queries*](finding-certifying-weighted-minimum-cuts.pdf) (PDF in this folder; also [arXiv:2611.03107](https://arxiv.org/abs/2611.03107)).

This page shows the Lean statements of the paper's four headline theorems and explains how to
read them. You do not need to read any Lean proofs. Lean's kernel checks those, so what matters
is whether the *statements* say what the paper says. With the reading guide below, you can
compare each statement with the paper in a few minutes. At the end we explain how to confirm
that the proofs are complete.

| Paper | Lean theorem (namespace `CutQueryComplexity`) |
| --- | --- |
| Theorem 1: near-linear certificates | [`Certificate.exists_minCut_witnessCertificate`](#theorem-1-near-linear-certificates) |
| Theorem 4: all minimum cuts, deterministically | [`AllMinCuts.deterministic_all_mincuts_log3loglog2`](#theorem-4-all-minimum-cuts-deterministically) |
| Theorem 6: from a tree cut sparsifier to a weak skeleton | [`AllMinCuts.exists_conversion_allMinCuts`](#theorem-6-from-a-tree-cut-sparsifier-to-a-weak-skeleton) |
| Theorem 7: learning a tree cut sparsifier | [`TreeCutSparsifier.theorem5LL`](#theorem-7-learning-a-tree-cut-sparsifier) |

Source links on this page point into this repository, at the version you are browsing. Each
Lean block is copied exactly from the linked file; proofs are omitted.

## How to read the statements

### Graphs and cuts

| Paper | Lean | Meaning |
| --- | --- | --- |
| vertex set of size `n` | `Fin n`, or a finite type `V` with `Fintype.card V = n` | `Fin n = {0, …, n−1}` |
| weighted graph | `G : WeightedGraph V` | symmetric, nonnegative real weights `G.w u v`, zero on the diagonal; weight 0 means no edge |
| cut query on `S` | `G.cut S` | total weight of edges leaving `S` |
| proper shore | `ProperShore S` | `S` is nonempty and not all of `V` |
| `λ(G)` | `mincutValue G` | the least cut value over proper shores |
| `S` is a minimum cut | `IsMinCut G S` | `S` is a proper shore of value `λ(G)` |
| `⌈log₂ 2n⌉` | `Nat.clog 2 (2 * n)` | the ceiling of a base-2 logarithm |
| `⌊√n⌋` | `Nat.sqrt n` | the integer square root |

These are the definitions, from
[Graph/Weighted.lean](../../CutQueryComplexity/Graph/Weighted.lean#L18) and
[Problem/Basic.lean](../../CutQueryComplexity/Problem/Basic.lean#L16):

```lean
@[ext] structure WeightedGraph (V : Type*) where
  w : V → V → ℝ
  symm : ∀ u v, w u v = w v u
  nonneg : ∀ u v, 0 ≤ w u v
  diag : ∀ v, w v v = 0
```

```lean
def cut (G : WeightedGraph V) (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, G.w u v
```

```lean
def ProperShore (S : Finset V) : Prop := S.Nonempty ∧ S ≠ Finset.univ
```

```lean
def properShores (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.filter (fun S => S.Nonempty ∧ S ≠ Finset.univ)
```

```lean
noncomputable def mincutValue (G : WeightedGraph V) : ℝ :=
  if h : (properShores V).Nonempty then (properShores V).inf' h G.cut else 0
```

```lean
def IsMinCut (G : WeightedGraph V) (S : Finset V) : Prop :=
  ProperShore S ∧ ∀ T, ProperShore T → G.cut S ≤ G.cut T
```

Weights are arbitrary nonnegative reals. Nothing requires them to be integers, the graph to be
connected, or `λ(G)` to be positive, unless a theorem says so. `Finset V` is a finite set of
vertices, `Sᶜ` is the complement of `S`, and `univ` is the whole vertex set. The `else 0` branch
of `mincutValue` applies only when there is no proper shore, that is, when `n ≤ 1`; every
theorem below assumes `n ≥ 2`.

### Algorithms are query trees

A deterministic cut-query algorithm is a `DTree`: a decision tree that asks queries, branches on
the answers, and eventually returns an output.
[Model/Deterministic.lean](../../CutQueryComplexity/Model/Deterministic.lean#L14):

```lean
def DTree (I A O : Type) : ℕ → Type
  | 0 => O
  | q + 1 => O ⊕ (I × (A → DTree I A O q))
```

Read `DTree I A O q` as "a program that asks at most `q` queries of type `I`, receives answers of
type `A`, and returns an output of type `O`". With budget `q + 1`, a program either stops with an
output (`O`), or asks a query `i : I` and continues, with budget `q`, along a branch chosen by
the answer. For cut queries, `I = Finset (Fin n)` (a vertex set) and `A = ℝ` (its cut value).
The library's `DTree.query i next` asks `i` and continues with `next answer`, and `DTree.pure o`
returns `o`. For example, this program asks for the cut of `{0}`, then the cut of `{0, 1}`, and
returns the sum of the two answers:

```lean
example : DTree (Finset (Fin 3)) ℝ ℝ 2 :=
  DTree.query {0} fun a => DTree.query {0, 1} fun b => DTree.pure (a + b)
```

(This example is checked in [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).)

Two functions run a program. `D.eval read` returns its output when each query `S` is answered
by `read S`, and `D.cost read` counts the queries it asks. In the theorems, `read` is the cut
oracle `G.cut`, so `D.eval G.cut` is "run the algorithm on `G`".

### The shape of an algorithmic theorem

Theorems 4, 6 and 7 all have this form:

```text
∃ C, 0 < C ∧ ∀ n, 2 ≤ n →
  ∃ q, q ≤ C · f(n) ∧
    ∃ D : DTree (Finset (Fin n)) ℝ (Option Out) q,
      (∀ read, D.cost read ≤ q) ∧
      ∀ G : WeightedGraph (Fin n), [promise about G] →
        ∃ out, D.eval G.cut = some out ∧ [out is correct for G]
```

Check these points when reading one:

1. **`∃ C … ∀ n` is the `O(f(n))`.** One constant works for every `n ≥ 2`. Where the paper writes
   `log`, Lean writes either `Nat.clog 2 (2 * n)` or the natural logarithm `Real.log (2 * n)`;
   these differ by constant factors.
2. **The program `D` is chosen before the graph `G`.** It depends only on `n` (and on any
   public inputs listed before it), so it is one algorithm that works for every graph. It is
   not a graph-specific witness.
3. **The program sees `G` only through `G.cut`.** No weight or edge is ever handed to it
   directly.
4. **`∀ read, D.cost read ≤ q` bounds every run.** The budget holds for every sequence of
   answers, even answers that no graph could produce. The type already guarantees this
   (`DTree.cost_le`); the theorems state it explicitly anyway.
5. **Success is part of the claim.** The output type is an `Option`, and `some out` means the
   program finished normally. The theorem promises success on every graph satisfying the
   promise.
6. **Correctness is spelled out.** Each theorem names a predicate such as `Correct G out`; its
   definition is shown next to the theorem.

As in the paper, only queries are counted. Computation between queries is free and uses exact
real arithmetic, so these are query-complexity theorems, not running-time theorems.

## Theorem 1: near-linear certificates

**Paper.** Every nonnegatively weighted graph `G` on `n ≥ 2` vertices has a certificate of size
`O(n log²(2n))`. The certificate can be chosen to contain a shore `S*` that remains a minimum
cut in every consistent graph. If `λ(G) = 0`, the single query `S*` suffices.

A *certificate* is a set `Q` of queried shores whose cut values pin down the answer: any graph
`G'` that agrees with `G` on every shore in `Q` has the same minimum cut value.
[Certificate/Flow.lean](../../CutQueryComplexity/Certificate/Flow.lean#L34):

```lean
def Consistent (G G' : WeightedGraph V) (Q : Finset (Finset V)) : Prop :=
  ∀ S ∈ Q, G'.cut S = G.cut S
```

```lean
def IsMinCutCertificate (G : WeightedGraph V) (Q : Finset (Finset V)) : Prop :=
  ∀ G' : WeightedGraph V, Consistent G G' Q → mincutValue G' = mincutValue G
```

```lean
def IsMinCutWitnessCertificate (G : WeightedGraph V) (Q : Finset (Finset V))
    (S : Finset V) : Prop :=
  S ∈ Q ∧ ∀ G' : WeightedGraph V, Consistent G G' Q → IsMinCut G' S
```

The theorem,
[Certificate/Main.lean](../../CutQueryComplexity/Certificate/Main.lean#L114):

```lean
theorem exists_minCut_witnessCertificate (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, Q.card ≤ 18 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2 ∧
      IsMinCutWitnessCertificate G Q S
```

**Reading it.**
- For every graph `G` on `n ≥ 2` vertices there is a set `Q` of at most `18 n ⌈log₂ 2n⌉²` shores
  and a shore `S` with the witness property. The constant `18` is explicit.
- This is an existence statement, like an NP witness. `Q` may depend on `G`, and the theorem
  does not claim an algorithm that finds it.
- The competitors `G'` range over *all* weighted graphs on the same vertices, including graphs
  with edges where `G` has none.
- Since `S ∈ Q`, every consistent `G'` gives `S` the same value as `G`, and `S` is a minimum cut
  of `G'`. So `G'` has the same minimum cut value as `G`.

**Companion statements.** The library also states the result as a bound on the certificate
complexity, the least size of a certificate
([Certificate/Main.lean](../../CutQueryComplexity/Certificate/Main.lean#L186)):

```lean
noncomputable def certificateComplexity (G : WeightedGraph V) : ℕ :=
  sInf {m | ∃ Q : Finset (Finset V), Q.card = m ∧ IsMinCutCertificate G Q}
```

```lean
theorem certificateComplexity_le_bound (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V) :
    certificateComplexity G ≤ 18 * Fintype.card V * (Nat.clog 2 (2 * Fintype.card V)) ^ 2
```

```lean
theorem certificateComplexity_eq_one (G : WeightedGraph V) (hn : 2 ≤ Fintype.card V)
    (h0 : mincutValue G = 0) : certificateComplexity G = 1
```

The last theorem is the zero case. The witness form of the zero case, that a single minimum
shore `S` satisfies `IsMinCutWitnessCertificate G {S} S`, takes two lines: a consistent graph
gives `S` value `0`, and no cut is negative. It is proved as `zero_single_shore` in this
folder's [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).

## Theorem 4: all minimum cuts, deterministically

**Paper.** A deterministic algorithm, given cut-query access to an `n`-vertex graph with
arbitrary nonnegative real weights, returns `λ(G)` and every minimum-cut shore using
`O(n^{3/2} log³(2n) (log log(2n))²)` cut queries. If `λ(G) = 0`, it returns the partition of `V`
into the components of the positive support.

The output is a value and a family of shores, and `Correct` says both are right
([AllMinCuts/Basic.lean](../../CutQueryComplexity/AllMinCuts/Basic.lean#L24)):

```lean
structure Output (V : Type) where
  cuts : Finset (Finset V)
  value : ℝ
```

```lean
def Correct (G : WeightedGraph V) (out : Output V) : Prop :=
  out.value = mincutValue G ∧ ∀ S : Finset V, S ∈ out.cuts ↔ IsMinCut G S
```

The theorem uses `logL n = max 1 ⌈log₂ 2n⌉`
([DetMinCut/Parameters.lean](../../CutQueryComplexity/DetMinCut/Parameters.lean#L23)):

```lean
def logL (n : ℕ) : ℕ := max 1 (Nat.clog 2 (2 * n))
```

[AllMinCuts/Endpoint.lean](../../CutQueryComplexity/AllMinCuts/Endpoint.lean#L28):

```lean
theorem deterministic_all_mincuts_log3loglog2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q : ℕ, (q : ℝ) ≤ C * (n : ℝ) * (Nat.sqrt n + 1) *
          ((DetMinCut.logL n : ℝ) ^ 3 *
            (DetMinCut.logL (DetMinCut.logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), ∃ out,
            D.eval G.cut = some out ∧ Correct G out
```

**Reading it.**
- `∃ C, 0 < C ∧ ∀ n, 2 ≤ n →`: one constant for all `n ≥ 2`.
- The budget is `q ≤ C · n · (⌊√n⌋ + 1) · L(n)³ · L(L(n))²` with `L = logL`. Since
  `n (⌊√n⌋ + 1) = O(n^{3/2})`, this is the paper's bound.
- `∃ D : DTree … q`: a deterministic program that depends only on `n`. It asks vertex sets,
  receives real numbers, and returns an `Output` or fails.
- `∀ read, D.cost read ≤ q`: it never asks more than `q` queries.
- `∀ G, ∃ out, D.eval G.cut = some out ∧ Correct G out`: on every weighted graph, with each
  query answered by the true cut value, it succeeds and its output is correct. There is no
  promise about `G` at all.
- `Correct` is an "if and only if": the family contains every minimum cut and nothing else.
  Both shores of each minimum cut appear, since a set and its complement have the same cut.

The library also states the bound with natural logarithms,
`C · n · (⌊√n⌋ + 1) · log(2n)³ · log(6 log(2n))²`, as
`deterministic_all_mincuts_log3loglog2_real_log` in the same file. The factor `6` only keeps
the inner logarithm above `1` for every `n ≥ 2`, so the outer logarithm is comparable to
`log log(2n)`.

**One difference from the paper: the zero case.** When `λ(G) = 0`, the paper returns the
components of the graph's positive-weight edges, while Lean returns the family of all zero
cuts. The components follow from that family without further queries: `u` and `v` are in the
same component exactly when every returned shore contains both of them or neither. This
recovery is proved as `recoveredPart_eq_component` in
[VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean), and
`partition_recovery_preserves_cost` there shows it costs no queries. Note that the family of
zero cuts can be exponentially large (a graph with `c` components has `2^c − 2` of them). As
throughout, only queries are counted.

## Theorem 6: from a tree cut sparsifier to a weak skeleton

**Paper.** Given cut-query access to a graph `G` with `λ(G) > 0` and an explicit `B`-tree cut
sparsifier of `G` with `O(n)` vertices, a deterministic algorithm constructs a weak skeleton of
`G` using `O(n B log³(2n) (log log(2n))²)` cut queries.

**Tree cut sparsifiers, informally.** A tree cut sparsifier is a tree with nonnegative edge
capacities whose nodes include the graph's vertices. It assigns each vertex set `S` a cost: the
cheapest way to label every tree node `0` or `1`, with the vertices in `S` labeled `1` and the
others `0`, paying an edge's capacity whenever its two ends get different labels. It is a
`B`-sparsifier of `G` if, for every `S`, this cost lies between `G.cut S` and `B · G.cut S`. The
Lean definitions are in the [appendix](#appendix-trees-and-tree-cut-sparsifiers); this is
`TreeData.Approximates`
([TreeCutSparsifier/Canonicalization.lean](../../CutQueryComplexity/TreeCutSparsifier/Canonicalization.lean#L37)):

```lean
def TreeData.Approximates (input : TreeData V) (G : WeightedGraph V) (B : ℝ) : Prop :=
  ∀ S, G.cut S ≤ input.tree.H.rep input.cap S ∧ input.tree.H.rep input.cap S ≤ B * G.cut S
```

**The output.** A weak skeleton keeps every minimum cut of `G` small without making any cut
smaller than `λ(G)` ([AllMinCuts/Skeleton.lean](../../CutQueryComplexity/AllMinCuts/Skeleton.lean#L29)):

```lean
def AllMinCutSkeleton {V : Type} [Fintype V] [DecidableEq V] (G H : WeightedGraph V) : Prop :=
  mincutValue G ≤ mincutValue H ∧
    ∀ S, IsMinCut G S → H.cut S ≤ (111 / 100 : ℝ) * mincutValue G
```

The paper's definition allows the constant `5/4`, and Lean proves the stronger `111/100`.
`skeleton_implies_paper_definition` in
[VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean) derives the paper's version.

The theorem,
[AllMinCuts/Conversion.lean](../../CutQueryComplexity/AllMinCuts/Conversion.lean#L53):

```lean
theorem exists_conversion_allMinCuts :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (input : TreeData (Fin n)) (B : ℝ), 2 ≤ n → 1 ≤ B →
      ∃ q : ℕ, (q : ℝ) ≤ C * n * B * ((logL n : ℝ) ^ 3 * (logL (logL n) : ℝ) ^ 2) ∧
        ∃ D : DTree (Finset (Fin n)) ℝ (Option (WeightedGraph (Fin n))) q,
          (∀ read, D.cost read ≤ q) ∧
          ∀ G : WeightedGraph (Fin n), 0 < mincutValue G → input.Approximates G B →
            ∃ F, D.eval G.cut = some F ∧ AllMinCutSkeleton G F
```

**Reading it.**
- The public inputs are `n`, the explicit tree `input` and the number `B ≥ 1`. They come before
  the program `D`, so `D` may use them. The graph `G` comes after `D`, so `D` cannot depend on
  it.
- The promise has two parts: `λ(G) > 0`, and the tree is a `B`-sparsifier of `G`. Under it, the
  program returns a graph `F` that is a weak skeleton of `G`.
- The query bound is `C · n · B · L(n)³ · L(L(n))²` with `L = logL`, matching the paper.
- Lean allows a tree of any size. The paper's assumption that it has `O(n)` vertices is not
  needed.

## Theorem 7: learning a tree cut sparsifier

**Paper.** For every graph `G` on `n ≥ 2` vertices with `λ(G) > 0`, and every `α` with
`C log²(2n) (log log(2n))² ≤ α ≤ √n`, a deterministic algorithm uses
`O((n²/α) log³(2n) (log log(2n))²)` cut queries to find a safe partition `P` of `V(G)` and an
explicit `α`-tree cut sparsifier of the quotient `G/P` with at most `8n` vertices.

(The Lean name `theorem5LL` comes from an earlier numbering of the paper.)

[TreeCutSparsifier/EndpointLL.lean](../../CutQueryComplexity/TreeCutSparsifier/EndpointLL.lean#L111):

```lean
theorem theorem5LL :
    ∃ C Cq : ℝ, 0 < C ∧ 0 < Cq ∧
      ∀ n : ℕ, 2 ≤ n → ∀ α : ℝ,
        C * ((Real.log (2 * (n : ℝ)))^2 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ≤ α →
        α ≤ Real.sqrt n →
      ∃ q : ℕ, (q : ℝ) ≤ Cq * ((n : ℝ)^2 / α) *
          ((Real.log (2 * (n : ℝ)))^3 * (Real.log (6 * Real.log (2 * (n : ℝ))))^2) ∧
      ∃ D : DTree (Finset (Fin n)) ℝ (Option (Output (Fin n))) q,
        (∀ read, D.cost read ≤ q) ∧
        ∀ G : WeightedGraph (Fin n), 0 < mincutValue G →
          ∃ out, D.eval G.cut = some out ∧ Correct G α out
```

**Reading it.**
- `C` is the paper's constant in the lower limit on `α`, and `Cq` is the constant in the query
  bound. `α` is any real number in the stated range; the program may depend on it.
- The logarithms are natural logarithms, with the same `log(6 log(2n))` form as above.
- `Output` and `Correct` here are the ones in the namespace `TreeCutSparsifier`, shown below.

**What the output is.** A partition is represented by a map `r : V → V` that sends each vertex to
a representative of its part. The output is such a map and a tree on the quotient graph
([TreeCutSparsifier/Basic.lean](../../CutQueryComplexity/TreeCutSparsifier/Basic.lean#L37)):

```lean
structure Output (V : Type) [Fintype V] [DecidableEq V] where
  r : V → V
  data : TreeData (Cls r)
```

```lean
def Correct (G : WeightedGraph V) (α : ℝ) (out : Output V) : Prop :=
  SafePartition G out.r ∧ out.data.Good (quot G out.r) α
```

A partition is *safe* if every minimum cut of `G` is a union of parts
([DetMinCut/SafePartition.lean](../../CutQueryComplexity/DetMinCut/SafePartition.lean#L25),
[DetMinCut/Normalize.lean](../../CutQueryComplexity/DetMinCut/Normalize.lean#L56)):

```lean
def SafePartition (G : WeightedGraph V) (r : V → V) : Prop :=
  ∀ S : Finset V, IsMinCut G S → Sat r S
```

```lean
def Sat (r : V → V) (S : Finset V) : Prop := ∀ x y, r x = r y → (x ∈ S ↔ y ∈ S)
```

`quot G r` is the quotient graph `G/P`: one vertex per part (`Cls r`, the representatives
actually used), with the weight between two parts equal to the total weight of edges between
them. Its definition is in the appendix. `Good` collects the properties of the tree
([TreeCutSparsifier/Basic.lean](../../CutQueryComplexity/TreeCutSparsifier/Basic.lean#L25)):

```lean
structure TreeData.Good (G : WeightedGraph V) (α : ℝ) (out : TreeData V) : Prop where
  size : out.tree.m ≤ 8 * Fintype.card V
  leaves : out.tree.H.LeafChildless
  canonical : out.cap = out.tree.H.canon G
  cuts : ∀ S, G.cut S ≤ out.tree.H.rep out.cap S ∧
    out.tree.H.rep out.cap S ≤ α * G.cut S
```

- `size`: the tree has at most `8 ×` (number of parts) `≤ 8n` nodes.
- `cuts`: the tree is an `α`-tree cut sparsifier of the quotient, as in Theorem 6.
- `leaves` and `canonical` are extra normalizations the paper does not require: vertices are
  leaves of the tree, and each tree edge's capacity is the cut value of the vertices below it.

## What is not formalized

The four headline theorems above are formalized in full. Some intermediate statements are
formalized in a weaker or partial form, as the paper's Lean appendix records:

- **Lemma 22** is formalized with the interval error `2M/q`, not the sharper prefix error `M/q`.
- **Lemma 23** omits the edge-count conclusion of the completion step.
- **Remark 14** (sparsifying an all-minimum-cut skeleton) and **Remark 33** (a calibration) are
  not formalized.

## Check it yourself

You do not need to trust this page. [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean)
restates each headline theorem above word for word, as `check_…`, and proves it by citing the
library. If the file compiles, the library proves exactly these statements. The file also runs
two checks on each theorem:

- `#print axioms` lists the axioms the proof depends on. It should show only `propext`,
  `Classical.choice` and `Quot.sound`, Lean's three standard axioms. In particular, no
  `sorryAx` (an unfinished proof) and no extra assumption.
- `#audit_cut_decl` applies the library's own audit of the same kind. It prints nothing when the
  check passes.

Lean's kernel checked every proof when `lake build` compiled the library. `#print axioms`
follows every dependency of a theorem down to the axioms, so an unfinished proof anywhere
beneath a headline theorem would show up there as `sorryAx`. To run the checks, install Lean's
toolchain manager [`elan`](https://github.com/leanprover/elan), then:

```sh
git clone https://github.com/troyjlee/cut-query-complexity.git
cd cut-query-complexity
lake exe cache get        # download prebuilt Mathlib
lake build CutQueryComplexity.AllMinCuts.Endpoint CutQueryComplexity.AllMinCuts.Conversion \
  CutQueryComplexity.Certificate.Main CutQueryComplexity.Certificate.TreePattern.Main \
  CutQueryComplexityChecks.AxiomAudit
lake env lean --trust=0 papers/P1/VerifyHeadlineTheorems.lean
```

The last command should finish with no errors.

## Appendix: trees and tree cut sparsifiers

This appendix gives the Lean definitions behind `TreeData`, `rep` and `quot`, used in Theorems
6 and 7.

**Rooted trees** are given by a parent map and depths that decrease towards the root
([TwoRespecting/Tree.lean](../../CutQueryComplexity/TwoRespecting/Tree.lean#L22)).
`parent^[k]` means the parent map applied `k` times.

```lean
structure RootedTree (V : Type) where
  root : V
  parent : V → V
  depth : V → ℕ
  parent_root : parent root = root
  depth_root : depth root = 0
  depth_parent : ∀ v, v ≠ root → depth (parent v) + 1 = depth v
```

```lean
def IsAnc (u v : V) : Prop := ∃ k, T.parent^[k] v = u
```

**A hierarchy** is a tree on nodes `N` together with an injective placement of the vertices `V`
on its nodes ([Hierarchy/Basic.lean](../../CutQueryComplexity/Hierarchy/Basic.lean#L26),
[Hierarchy/Refine.lean](../../CutQueryComplexity/Hierarchy/Refine.lean#L65)). Vertices need not
be leaves; the theorem input in Theorem 6 allows vertices at internal nodes.

```lean
structure Hier (V N : Type) where
  T : RootedTree N
  leaf : V → N
  leaf_inj : Function.Injective leaf
```

```lean
structure Pkg (V : Type) where
  m : ℕ
  H : Hier V (Fin m)
```

**Tree data** is a hierarchy with nonnegative capacities on its nodes. The capacity of a node is
the capacity of the edge to its parent
([TreeCutSparsifier/Basic.lean](../../CutQueryComplexity/TreeCutSparsifier/Basic.lean#L19)).

```lean
structure TreeData (V : Type) where
  tree : Pkg V
  cap : Fin tree.m → ℝ
  cap_nonneg : ∀ x, 0 ≤ cap x
```

**The cost of a cut.** `rep cap S` is the least cost of a `0`/`1` labeling `ℓ` of the nodes that
gives each vertex label `1` exactly when it is in `S`. A labeling's cost is the total capacity
of the tree edges whose ends get different labels
([Hierarchy/Basic.lean](../../CutQueryComplexity/Hierarchy/Basic.lean#L37)).

```lean
def edges : Finset N := Finset.univ.erase H.T.root
```

```lean
def labelCost (cap : N → ℝ) (ℓ : N → ℝ) : ℝ :=
  ∑ x ∈ H.edges, cap x * |ℓ x - ℓ (H.T.parent x)|
```

```lean
def toReal (ℓ : N → Bool) : N → ℝ := fun x => if ℓ x then 1 else 0
```

```lean
def Extends (S : Finset V) (ℓ : N → Bool) : Prop := ∀ v, ℓ (H.leaf v) = decide (v ∈ S)
```

```lean
noncomputable def rep (cap : N → ℝ) (S : Finset V) : ℝ :=
  (Finset.univ.filter (H.Extends S)).inf' (H.extends_nonempty S)
    fun ℓ => H.labelCost cap (toReal ℓ)
```

This is the paper's representation cost `R_T(S)`. (`extends_nonempty` is the lemma that some
labeling extends `S`; it is not an assumption.) For Theorem 7's `Good`, the *cluster* of a node
is the set of vertices placed at or below it, `canon G` gives each node the cut value of its
cluster, and `LeafChildless` says no node holding a vertex has children
([Hierarchy/Basic.lean](../../CutQueryComplexity/Hierarchy/Basic.lean#L89),
[Hierarchy/Children.lean](../../CutQueryComplexity/Hierarchy/Children.lean#L23)):

```lean
def cluster (x : N) : Finset V := Finset.univ.filter fun v => H.T.IsAnc x (H.leaf v)
```

```lean
def canon (G : WeightedGraph V) : N → ℝ := fun x => G.cut (H.cluster x)
```

```lean
def children (x : N) : Finset N := {c ∈ H.edges | H.T.parent c = x}
```

```lean
def LeafChildless : Prop := ∀ v, H.children (H.leaf v) = ∅
```

**Quotient graphs.** `Cls r` is the set of representatives that `r` actually uses, so the
quotient has no empty parts. `quot G r` contracts each part to a single vertex, with no loops,
and gives two parts the total weight of the edges between them
([DetMinCut/Normalize.lean](../../CutQueryComplexity/DetMinCut/Normalize.lean#L34),
[Graph/Operations.lean](../../CutQueryComplexity/Graph/Operations.lean#L11)):

```lean
abbrev Cls (r : V → V) := {c : V // c ∈ univ.image r}
```

```lean
def proj (r : V → V) (x : V) : Cls r := ⟨r x, mem_image_of_mem r (mem_univ x)⟩
```

```lean
abbrev quot (G : WeightedGraph V) (r : V → V) : WeightedGraph (Cls r) := G.contract (proj r)
```

```lean
def cross (G : WeightedGraph V) (S T : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ T, G.w u v
```

```lean
def pull (π : V → B) (T : Finset B) : Finset V := Finset.univ.filter (fun v => π v ∈ T)
```

```lean
def fiber (π : V → B) (b : B) : Finset V := pull π {b}
```

```lean
def contract (G : WeightedGraph V) (π : V → B) : WeightedGraph B where
  w b c := if b = c then 0 else G.cross (fiber π b) (fiber π c)
  symm b c := by
    by_cases h : b = c
    · subst c; rfl
    · simp [h, Ne.symm h, G.cross_comm]
  nonneg b c := by split <;> simp_all [G.cross_nonneg]
  diag b := by simp
```
