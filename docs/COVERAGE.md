# Coverage of the 48 minimum-cut problems

The best known cut-query bounds for minimum cuts form a table of 48 cells:
three problems (global, s–t, and all-pairs minimum cut), four graph classes
(undirected or directed, unweighted or weighted), and four models
(deterministic, certificate, randomized, quantum). This page gives, for each
cell, the Lean theorem that proves its bound and the source of the argument.

**42 of the 48 cells are proved.** The other six are the weighted quantum
cells, which the quantum model of this library cannot state; see
[the end of this page](#the-six-weighted-quantum-cells).

## Conventions

- There are `n ≥ 2` labeled vertices. Unweighted means 0/1 capacities; a
  digraph may contain both arcs of an antiparallel pair. Weighted means
  arbitrary nonnegative real capacities.
- Undirected queries return the weight of the edges crossing a shore `S`;
  directed queries return the weight of the arcs leaving `S`.
- Every output is an exact value together with a minimizing shore of the input
  graph. All-pairs asks for every pair of distinct vertices, ordered pairs for
  digraphs.
- An algorithm is a program fixed before the graph, and its query bound holds
  for every oracle. Randomized and quantum algorithms fail with probability at
  most `1/3` unless the row says otherwise.
- A certificate is a set `Q` of shores, chosen with knowledge of the input,
  such that every competitor graph agreeing with the input on `Q` has the same
  claimed output. The competitor class is either *any* (arbitrary nonnegative
  real weights, any support) or *unit* (0/1 capacities). The certificate bounds
  in the unweighted tables are defined against unit competitors, the input's own
  class. An *any* entry there is the stronger statement.
- Lean names are relative to the `CutQueryComplexity` namespace.
  [`tests/downstream/Coverage.lean`](../tests/downstream/Coverage.lean) checks
  the coverage exports by cell, and the files in
  [`CutQueryComplexityChecks/`](../CutQueryComplexityChecks) audit every theorem
  below.

A theorem for a larger class covers the smaller one: the weighted theorems
prove the corresponding unweighted cells, and the all-pairs algorithm proves
the randomized s–t cell. The table bound is the one the cell records; the
proved bound is the literal statement, which in two cells is stronger.

## Undirected, unweighted

| Problem | Model | Table bound | Lean theorem | Proved bound | Source |
| --- | --- | --- | --- | --- | --- |
| Global | Deterministic | `O(n^{3/2} log² n)` | `BoundedFlowMinCut.program_correct` | `n + C n (⌊√n⌋+1) (⌈log₂(2n+2)⌉+1)² + 1`, `C = 83 + 48·3⁸` | [KM26] Thm. 1.1, cutoff rebalanced |
| Global | Certificate | `O(n log² n)` | `Certificate.exists_minCut_witnessCertificate` (weighted) | `18 n ⌈log₂ 2n⌉²`, any competitor | [P1] Thm. 1 |
| Global | Randomized | `O(n)` | `StarContraction2022.Randomized.exists_uniform_linear_program` | `C n` | [AEG+22] Thm. 1.1 |
| Global | Quantum | `O(√n log⁵ n)` | `StarContraction2022.Quantum.Global.public_natural_log_five_endpoint` | `C √n ln⁵(2n)` | [AEG+22] Thm. 1.3 |
| s–t | Deterministic | `O(n^{3/2} log³ n)` | `CanonicalST.exists_terminal_sqrt_program` | `⌈2²³ n√n ⌈log₂ 2n⌉³⌉`, also returns a maximum flow | [P2] Thm. 1 |
| s–t | Certificate | `O(n)` | `Certificate.TreePattern.exists_terminal_tree_certificate` (weighted) | `4n`, any competitor | [P1] Lemma 2 |
| s–t | Randomized | `O(n^{3/2} log² n)` | `AllPairs.allPairsProgram_spec` (all pairs) | `600000 (σ+8) n√n (⌈log₂ n⌉+4)²`, failure `≤ (6n+2)^{-σ}` | [KK26] Thm. 1.2 |
| s–t | Quantum | `O(n)` | `Quantum.LinearReconstruction.exists_unit_terminal` | `6n`, probability one | [LSZ21] Thm. 28 |
| All-pairs | Deterministic | `O(n^{5/3} log⁵ n)` | `DeterministicAPMCExpansion.Pruning.deterministic_allPairs` | `C n^{5/3} (⌈log₂(2n+2)⌉+1)⁵` | [P2] Thm. 2 |
| All-pairs | Certificate | `O(n²/log n)` | `Certificate.UnitAllPairs.exists_unit_allPairs_certificate` | **`3n`**, unit competitor | three queries per vertex |
| All-pairs | Randomized | `O(n^{3/2} log² n)` | `AllPairs.allPairsProgram_spec` | as for s–t | [KK26] Thm. 1.2 |
| All-pairs | Quantum | `O(n)` | `Quantum.LinearReconstruction.exists_unit_allPairs` | `6n`, probability one | [LSZ21] Thm. 28 |

`L(n) = max(1, ⌈log₂ 2n⌉)` is `DetMinCut.logL`. The deterministic global
cell uses the source's two branches (a `2δ` threshold certificate for small
minimum degree `δ`, bounded max-flows from a dominating set for large `δ`) with
the degree cutoff `(⌊√n⌋+1)(⌈log₂(2n+2)⌉+1)` instead of `√n`, which balances
them to `log²` (`BoundedFlowMinCut`). The
weighted `log⁵` theorem below still covers this cell as well.

The table bound `n²/log n` of the unweighted all-pairs certificate comes from
Grebinski–Kucherov reconstruction [GK00]. The Lean certificate is linear: for
each vertex `v` it queries `{v}`, the neighborhood `N(v)`, and `N(v) ∪ {v}`.
Against 0/1 competitors these answers force every edge at `v`.

## Undirected, weighted

| Problem | Model | Table bound | Lean theorem | Proved bound | Source |
| --- | --- | --- | --- | --- | --- |
| Global | Deterministic | `O(n^{3/2} log³ n (log log n)²)` | `UndirectedClosure.deterministic_mincut_shore_value_log3loglog2` (also `_log5`, `C n (⌊√n⌋+1) L(n)⁵`; second route `TreeCutSparsifier.deterministic_mincut_two_stage`; all minimum cuts `AllMinCuts.deterministic_all_mincuts_log3loglog2`) | `C n (⌊√n⌋+1) L(n)³ L(L(n))²` | [P1] Thm. 4 |
| Global | Certificate | `O(n log² n)` | `Certificate.exists_minCut_witnessCertificate` | `18 n ⌈log₂ 2n⌉²`, any competitor | [P1] Thm. 1 |
| Global | Randomized | `O(n log⁸ n)` | `WeightedMinCut.Endpoint.weighted_global` (all minimum cuts: `AllMinCuts.randomized_all_mincuts`, `2·10⁸ (s+8) n ln²(2n)`, failure `(2n+2)^{-s}`) | **`10⁹ n ln²(2n)`** | [MN20] Thm. 1.2, with the sparsifier of [PRW24] Thm. 4.13 |
| Global | Quantum | `O(n log⁸ n)` | not formalized; for integral capacities see [below](#the-six-weighted-quantum-cells) | | |
| s–t | Deterministic | `O(n²)` | `Reconstruction.WeightedUndirected.deterministic_terminal` | `n + C(n,2) ≤ n²` | reconstruction |
| s–t | Certificate | `O(n)` | `Certificate.TreePattern.exists_terminal_tree_certificate` | `4n`, any competitor | [P1] Lemma 2 |
| s–t | Randomized | `O(n²)` | `Reconstruction.WeightedUndirected.randomized_terminal` | `n + C(n,2) ≤ n²`, zero error | reconstruction |
| s–t | Quantum | `O(n²)` | not formalized; for integral capacities see [below](#the-six-weighted-quantum-cells) | | |
| All-pairs | Deterministic | `O(n²)` | `Reconstruction.WeightedUndirected.deterministic_allPairs` | `n + C(n,2) ≤ n²` | reconstruction |
| All-pairs | Certificate | `O(n²)` | `Reconstruction.WeightedUndirected.allPairs_certificate` | `n + C(n,2) ≤ n²`, any competitor | reconstruction |
| All-pairs | Randomized | `O(n²)` | `Reconstruction.WeightedUndirected.randomized_allPairs` | `n + C(n,2) ≤ n²`, zero error | reconstruction |
| All-pairs | Quantum | `O(n²)` | not formalized; for integral capacities see [below](#the-six-weighted-quantum-cells) | | |

*Reconstruction* queries every singleton and every pair and recovers each
weight as `w(u,v) = (c({u}) + c({v}) − c({u,v}))/2`
(`reconstruct_solves`, in `Primitive/Learn.lean`). Grebinski–Kucherov
reconstruction does not apply here: it needs weights from a fixed finite set,
while determining an arbitrary real weighting takes `C(n,2)` linearly
independent cut values.
For integral weights,
`GHReduction.exists_weighted_gh_reduction` reduces all-pairs minimum cuts to an
s–t minimum-cut family, inspired by [KK26] Thm. 1.4 (whose proof relies on a
withdrawn size bound that the Lean reduction does not use). `GHReduction.Randomized.exists_randomized_gh_reduction`
does the same from a randomized family that returns the canonical
(inclusion-minimal) minimum s–t shore with probability at least 2/3 and has
size-regular cost (`SizeRegular n Q`), with a logarithmic number of repetitions
per call, and
`exists_randomized_unweighted_allPairs` specializes it to all-pairs minimum cuts
of unweighted graphs, with the family called on weighted instances. These are
conditional refinements, not bounds for this table.

For arbitrary nonnegative real weights,
`GlobalSTReduction.exists_global_from_st` turns any deterministic s–t
minimum-cut family of size-regular cost `Q` that returns *some* minimum shore
(not necessarily the canonical one) into a randomized global minimum cut with
`O(Q(n) log³ n + n log² n)` queries and failure at most `(n+2)^{-b}`, by
isolating cuts with threshold terminal sampling [LP20].
`GlobalSTReduction.exists_global_from_randomized_st` does the same from a
randomized family with success `≥ 2/3`, with `O((Q(n) + n) log⁴ n)` queries and
failure `2 (n+2)^{-b}`. Neither needs an integrality, capacity or precision
promise. This is also a conditional result; it does not change the weighted
randomized global cell, whose `O(n log² n)` bound is already lower.

## Directed, unweighted

| Problem | Model | Table bound | Lean theorem | Proved bound | Source |
| --- | --- | --- | --- | --- | --- |
| Global | Deterministic | `O(n²/log n)` | `Reconstruction.CompressedDirected.global_deterministic` | `(4 + 32768 ln 3) n²/ln(2n)` | [GK00] §4.1 |
| Global | Certificate | `O(n^{3/2})` | `DirectedCertificate.Completion.exists_unit_global_certificate` | `600 n^{3/2}`, any competitor | [P3] Cor. 5 |
| Global | Randomized | `O(n^{7/4} log²² n)` | `ImplicitLP.PathFollowing.directed_global_query_theorem` | `2³⁴⁰ n^{7/4} log₂²²(2n/ζ)`, failure `≤ ζ` | [P4] Thm. 1.2 |
| Global | Quantum | `O(n)` | `Quantum.DirectedReconstruction.physical_global_endpoint` | `50n`, probability one | [LSZ21] Thm. 28 |
| s–t | Deterministic | `O(n^{5/3} log² n)` | `DirectedUnitST.Endpoint.exists_unitST_query_program` | `2049 n^{5/3} (⌈log₂ n⌉+4)²` | [P4] Thm. 1.1 |
| s–t | Certificate | `O(n)` | `DirectedCertificate.Completion.exists_exact_terminal_certificate` (weighted) | `18n + 1`, any competitor | [P3] Thm. 3 |
| s–t | Randomized | `O(n^{3/2} log²¹ n)` | `ImplicitLP.PathFollowing.directed_terminal_query_theorem` | `2³¹⁰ n^{3/2} log₂²¹(2n/ζ)`, failure `≤ ζ` | [P4] Thm. 1.2 |
| s–t | Quantum | `O(n)` | `Quantum.DirectedReconstruction.physical_terminal_endpoint` | `50n`, probability one | [LSZ21] Thm. 28 |
| All-pairs | Deterministic | `O(n²/log n)` | `Reconstruction.CompressedDirected.allPairs_deterministic` | `(4 + 32768 ln 3) n²/ln(2n)` | [GK00] §4.1 |
| All-pairs | Certificate | `O(n²/log n)` | `Reconstruction.CompressedDirected.allPairs_certificate` | `(4 + 32768 ln 3) n²/ln(2n)`, unit competitor | [GK00] §4.1 |
| All-pairs | Randomized | `O(n²/log n)` | `Reconstruction.CompressedDirected.allPairs_randomized` | `(4 + 32768 ln 3) n²/ln(2n)`, zero error | [GK00] §4.1 |
| All-pairs | Quantum | `O(n)` | `Quantum.DirectedReconstruction.physical_allPairs_endpoint` | `50n`, probability one | [LSZ21] Thm. 28 |

Outgoing cuts determine a digraph only up to its symmetrization
`c(u,v) + c(v,u)` and its vertex imbalances, and these suffice for every
minimum cut. The `n²/log n` rows learn the symmetrized rows, whose entries lie
in `{0,1,2}`. Each row is learned with a separating family of size
`16384 n ln 3 / ln(2n)` (`StarContraction2022.Recovery.denseFamily_card_bound`).
This is the Grebinski–Kucherov reconstruction [GK00, §4.1]. As in their §2.1,
the size of the family is proved by a union bound, with anti-concentration
from Sperner's theorem. The quantum rows use the same
symmetrization with the linear-query reconstruction of [LSZ21]. They recover
the outgoing-cut function, not the individual arcs.

## Directed, weighted

| Problem | Model | Table bound | Lean theorem | Proved bound | Source |
| --- | --- | --- | --- | --- | --- |
| Global | Deterministic | `O(n²)` | `Reconstruction.WeightedDirected.deterministic_global` | `n² + 2n` | reconstruction |
| Global | Certificate | `O(n^{5/3})` | `DirectedCertificate.Completion.exists_weighted_global_witnessCertificate` | `C n^{5/3}`, any competitor | [P3] Thm. 2 |
| Global | Randomized | `O(n²)` | `Reconstruction.WeightedDirected.randomized_global` | `n² + 2n`, zero error | reconstruction |
| Global | Quantum | `O(n²)` | not formalized; for integral capacities see [below](#the-six-weighted-quantum-cells) | | |
| s–t | Deterministic | `O(n²)` | `Reconstruction.WeightedDirected.deterministic_terminal` | `n² + 2n` | reconstruction |
| s–t | Certificate | `O(n)` | `DirectedCertificate.Completion.exists_exact_terminal_certificate` | `18n + 1`, any competitor | [P3] Thm. 3 |
| s–t | Randomized | `O(n²)` | `Reconstruction.WeightedDirected.randomized_terminal` | `n² + 2n`, zero error | reconstruction |
| s–t | Quantum | `O(n²)` | not formalized; for integral capacities see [below](#the-six-weighted-quantum-cells) | | |
| All-pairs | Deterministic | `O(n²)` | `Reconstruction.WeightedDirected.deterministic_allPairs` | `n² + 2n` | reconstruction |
| All-pairs | Certificate | `O(n²)` | `Reconstruction.WeightedDirected.allPairs_certificate` | `n² + 2n`, any competitor | reconstruction |
| All-pairs | Randomized | `O(n²)` | `Reconstruction.WeightedDirected.randomized_allPairs` | `n² + 2n`, zero error | reconstruction |
| All-pairs | Quantum | `O(n²)` | not formalized; for integral capacities see [below](#the-six-weighted-quantum-cells) | | |

Here reconstruction queries singletons, their complements, and pairs. This
recovers the symmetrized capacities and the imbalances.

## The six weighted quantum cells

The quantum model (`Quantum.Model`) specializes the `QAlg` model of
QuantumQueryComplexity. There, an oracle answer must lie in a finite set,
`CutAnswer n W = Fin (W n² + 1)` for capacities in `{0, …, W}`. An arbitrary
real-weighted cut oracle therefore cannot be stated, and the six weighted
quantum cells are outside the model. The table fills them by running a
classical algorithm.

With a public bound `W` on integral capacities, all six problems are proved by
linear-query reconstruction [LSZ21], with probability one:

| Graph class | Lean theorems | Proved bound |
| --- | --- | --- |
| Undirected, capacities in `{0,…,W}` | `Quantum.LinearReconstruction.exists_capacity_global`, `exists_capacity_terminal`, `exists_capacity_allPairs` | `6n ⌈log₂(W+1)⌉` native queries |
| Directed, arc capacities in `{0,…,W}` | `Quantum.DirectedReconstruction.exists_capacity_global`, `exists_capacity_terminal`, `exists_capacity_allPairs` | `n (24 ⌈log₂(2W+1)⌉ + 2)` native queries |

The directed construction simulates each symmetrized call with four native calls,
with capacities at most `2W`, and adds `2n` calls for the imbalances. At `W = 1`
its budget is `50n` (`directedBudget_unit`). These are refinements, not the
unrestricted cells: the program depends on `W`, and the bound grows with `log W`.

## Sources

- [AEG+22] S. Apers, Y. Efron, P. Gawrychowski, T. Lee, S. Mukhopadhyay, and
  D. Nanongkai. Cut query algorithms with star contraction. FOCS 2022;
  [arXiv:2201.05674](https://arxiv.org/abs/2201.05674).
- [GK00] V. Grebinski and G. Kucherov. Optimal reconstruction of graphs under
  the additive model. *Algorithmica* 28 (2000), 104–124;
  [doi:10.1007/s004530010033](https://doi.org/10.1007/s004530010033).
- [KK26] Y. Kenneth-Mordoch and R. Krauthgamer. Faster all-pairs minimum cut:
  bypassing exact max-flow. STOC 2026;
  [arXiv:2511.10036](https://arxiv.org/abs/2511.10036).
- [KM26] Y. Kenneth-Mordoch. Deterministic global minimum cut using
  Õ(n^{3/2}) cut queries;
  [arXiv:2610.23461](https://arxiv.org/abs/2610.23461).
- [LP20] J. Li and D. Panigrahi. Deterministic min-cut in poly-logarithmic
  max-flows. FOCS 2020;
  [arXiv:2111.02008](https://arxiv.org/abs/2111.02008).
- [LSZ21] T. Lee, M. Santha, and S. Zhang. Quantum algorithms for graph
  problems with cut queries. SODA 2021;
  [arXiv:2007.08285](https://arxiv.org/abs/2007.08285).
- [MN20] S. Mukhopadhyay and D. Nanongkai. Weighted min-cut: sequential,
  cut-query, and streaming algorithms. STOC 2020;
  [arXiv:1911.01651](https://arxiv.org/abs/1911.01651).
- [PRW24] O. Plevrakis, S. Ragavan, and S. M. Weinberg. On the cut-query
  complexity of approximating max-cut. ICALP 2024;
  [arXiv:2211.04506](https://arxiv.org/abs/2211.04506).

Preprints in [`papers/`](../papers):

- [P1] T. Lee. *Finding and Certifying Weighted Minimum Cuts with Cut Queries*;
  [arXiv:2611.03107](https://arxiv.org/abs/2611.03107); [PDF](../papers/P1/finding-certifying-weighted-minimum-cuts.pdf).
- [P2] *Deterministic s–t and All-Pairs Minimum Cuts with Subquadratic Cut
  Queries*; [PDF](../papers/P2/deterministic-st-all-pairs-minimum-cuts.pdf).
- [P3] *Directed Cut Certificates through Fractional Forests and Shared Flows*;
  [PDF](../papers/P3/directed-cut-certificates.pdf).
- [P4] *Subquadratic Cut-Query Algorithms for Directed Minimum Cuts*;
  [PDF](../papers/P4/subquadratic-directed-minimum-cuts.pdf).
