# Cut query complexity in Lean

[![CI](https://github.com/troyjlee/cut-query-complexity/actions/workflows/ci.yml/badge.svg)](https://github.com/troyjlee/cut-query-complexity/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23885653.svg)](https://doi.org/10.5281/zenodo.23885653)

A Lean library for deterministic, randomized, and quantum algorithms that access
a graph only through cut queries: the algorithm names a vertex set `S` and
learns the total weight of the edges leaving `S`. Every algorithm is an explicit
query program chosen before the hidden graph, and its query bound, error
probability, and output guarantee are proved for every input.

The [main results](#main-results) track the best known cut-query bounds for
global, s–t, and all-pairs minimum cut, for undirected or directed and
unweighted or weighted graphs, in the deterministic, certificate, randomized,
and quantum models. 42 of these 48 bounds are proved in Lean.

The library builds on [QuantumQueryComplexity](https://github.com/troyjlee/quantum-query-complexity)
for the quantum query model and on Mathlib.

## Main results

`n` is the number of vertices and `L(n)` a base-two logarithm of `n` (each
statement fixes the exact form). Weighted graphs have arbitrary nonnegative
real weights unless a row says otherwise. Names are relative to the
`CutQueryComplexity` namespace.

### Minimum cuts in four models

The table gives the best known cut-query bounds for global, s–t, and all-pairs
minimum cut. ✓ marks the 42 of the 48 cells that are proved in Lean, and the
key after a bound names the source of the argument.
[docs/COVERAGE.md](docs/COVERAGE.md) gives each cell's theorem, its exact bound,
and the theorem number in the source. All bounds are `O(·)`.

| | Deterministic | Certificate | Randomized | Quantum |
| --- | --- | --- | --- | --- |
| **Undirected, unweighted** | | | | |
| Global | n³ᐟ² log² n ✓ [\[KM26\]][KM26] | n log² n ✓ [\[P1\]][P1] | n ✓ [\[AEG+22\]][AEG+22] | √n log⁵ n ✓ [\[AEG+22\]][AEG+22] |
| s–t | n³ᐟ² log³ n ✓ [\[P2\]][P2] | n ✓ [\[P1\]][P1] | n³ᐟ² log² n ✓ [\[KK26\]][KK26] | n ✓ [\[LSZ21\]][LSZ21] |
| All-pairs | n⁵ᐟ³ log⁵ n ✓ [\[P2\]][P2] | n ✓ | n³ᐟ² log² n ✓ [\[KK26\]][KK26] | n ✓ [\[LSZ21\]][LSZ21] |
| **Undirected, weighted** | | | | |
| Global | n³ᐟ² log³ n (log log n)² ✓ [\[P1\]][P1] | n log² n ✓ [\[P1\]][P1] | n log² n ✓ [\[MN20\]][MN20], [\[PRW24\]][PRW24] | n log² n [\[MN20\]][MN20], [\[PRW24\]][PRW24] |
| s–t | n² ✓ | n ✓ [\[P1\]][P1] | n² ✓ | n² |
| All-pairs | n² ✓ | n² ✓ | n² ✓ | n² |
| **Directed, unweighted** | | | | |
| Global | n²/log n ✓ [\[GK00\]][GK00] | n³ᐟ² ✓ [\[P3\]][P3] | n⁷ᐟ⁴ log²² n ✓ [\[P4\]][P4] | n ✓ [\[LSZ21\]][LSZ21] |
| s–t | n⁵ᐟ³ log² n ✓ [\[P4\]][P4] | n ✓ [\[P3\]][P3] | n³ᐟ² log²¹ n ✓ [\[P4\]][P4] | n ✓ [\[LSZ21\]][LSZ21] |
| All-pairs | n²/log n ✓ [\[GK00\]][GK00] | n²/log n ✓ [\[GK00\]][GK00] | n²/log n ✓ [\[GK00\]][GK00] | n ✓ [\[LSZ21\]][LSZ21] |
| **Directed, weighted** | | | | |
| Global | n² ✓ | n⁵ᐟ³ ✓ [\[P3\]][P3] | n² ✓ | n² |
| s–t | n² ✓ | n ✓ [\[P3\]][P3] | n² ✓ | n² |
| All-pairs | n² ✓ | n² ✓ | n² ✓ | n² |

Cells without a key use arguments given in the library itself. The `n²` cells
learn the graph from the cut values of all singletons and pairs, and the
unweighted all-pairs certificate queries three sets per vertex. In two cells
the Lean bound is stronger than the source's. The unweighted all-pairs
certificate is linear, where [\[GK00\]][GK00] reconstruction gives `n²/log n`. The weighted
randomized global cut combines the method of [\[MN20\]][MN20] with the sparsifier of
[\[PRW24\]][PRW24].

Every output is an exact value with a minimizing shore, and all-pairs covers
every pair, ordered for digraphs. A certificate is a set of queries, chosen with
knowledge of the graph, whose answers force the same output on every competing
graph that agrees with them. Which competitors count is part of the definition,
and other choices are possible. In the Certificate column the competitors come
from the input's own class, so for an unweighted input they are also unweighted
(0/1 capacities). Allowing competitors with arbitrary weights would be a
stronger requirement, and could only raise the bound. Four of the six unweighted
cells meet the stronger requirement anyway, because their Lean certificates rule
out competitors with arbitrary nonnegative weights. The two unweighted all-pairs
certificates rule out only unweighted competitors.
[docs/COVERAGE.md](docs/COVERAGE.md) gives the competitor class of each cell.
The weighted quantum cells come from running a classical
algorithm. The library's quantum model has finitely many answers per query, so
they are not stated in Lean. For integral weights at most `W` they are proved,
with `O(n log W)` queries.

### Reductions

These theorems assume an s–t minimum-cut algorithm and build a stronger one from
it. The s–t algorithm is a *family*: one public program for each vertex count
`k`, on the vertices `Fin k`, with query cost `Q(k)`. The reductions run it on
contracted graphs, where each of its cut queries costs one original query. The
cost must be size-regular at `n`, that is `n·Q(k) ≤ k·Q(n)` for `1 ≤ k ≤ n`, as
for `Q(k) = kᶜ` with `c ≥ 1`. Each reduction is randomized even when the family
is deterministic. `b` sets the failure probability, which is over the coins of
the reduction and of the family.

**Global minimum cut from s–t minimum cut** (`GlobalSTReduction`), by isolating
cuts on randomly sampled terminal sets, after Li and Panigrahi [\[LP20\]][LP20]. Weights are
arbitrary nonnegative reals, and the family may return any minimum s–t shore.
Every output is a proper shore with its exact cut value, and it is a global
minimum cut except with the stated probability. No bound depends on the weights.

| s–t family | Lean name | Failure | Queries |
| --- | --- | --- | --- |
| Deterministic | `GlobalSTReduction.exists_global_from_st` | `(n+2)^{-b}` | `1 + 8(b+1)⌈log₂(n+2)⌉(⌈log₂ 2n⌉+1)((⌈log₂ n⌉+2) Q(n) + n)`, which is `O(Q(n) log³ n + n log² n)` for fixed `b` |
| Randomized, success `≥ 2/3` | `GlobalSTReduction.exists_global_from_randomized_st` | `2 (n+2)^{-b}` | the bound above with `Q(k)` replaced by `a (Q(k) + k)`, where `a = 1 + ⌈log₃(max(1, N) (n+2)^b)⌉` is the number of repetitions per call and `N` bounds the number of calls; `O((Q(n) + n) log⁴ n)` for fixed `b` |

**Gomory–Hu tree from s–t minimum cut** (`GHReduction`), inspired by Theorem
1.4 of [\[KK26\]][KK26]. That theorem's proof relies on a size bound from a
paper that has since been withdrawn. The Lean reduction is specific to graphs
and does not use that bound (see
[docs/ALL_PAIRS_FORMALIZATION.md](docs/ALL_PAIRS_FORMALIZATION.md)). Weights are integers
with total at most `M`. The family is called with the promise that every edge
weight is at most `M`, and it must return the canonical (inclusion-minimal)
minimum s–t shore. The output is a Gomory–Hu tree (`IsGomoryHuTree`), which
gives a minimum cut for every pair.

| s–t family | Lean name | Failure | Queries |
| --- | --- | --- | --- |
| Deterministic | `GHReduction.exists_weighted_gh_reduction` | `(n+2)^{-b}` | `O((n + Q(n)) L(n + M)^{22})` |
| Randomized, success `≥ 2/3` | `GHReduction.Randomized.exists_randomized_gh_reduction` | `2 (n+2)^{-b}` | `O((n + r (Q(n) + n)) L(n + M)^{22})`, where `r = 2⌈log₃((n+2)^b B₁)⌉ + 2` and `B₁` is this bound at `r = 1` |
| Randomized, success `≥ 2/3`; all-pairs minimum cuts of an unweighted graph | `GHReduction.Randomized.exists_randomized_unweighted_allPairs` | `2 (n+2)^{-b}` | the bound above with `M = n²` |

### Undirected graphs

The Source column names the paper whose argument the Lean proof follows, with
the theorem or section; — marks an argument given in the library itself.

| Result | Lean name | Bound | Source |
| --- | --- | --- | --- |
| `1 ± ε` cut sparsifier with `O(s n log n / ε²)` edges, failure `≤ (2n+2)^{-s}` | `WeightedGraph.sparsify_whp` | `O(s n log² n (1 + 1/ε²))` queries | [\[PRW24\]][PRW24] Thm. 4.13 |
| Randomized weighted global minimum cut, failure `≤ 2 (2n+2)^{-s}` | `WeightedMinCut.weightedMinCut_whp` | sparsifier budget plus `72 n (⌈log₂ n⌉ + 1)` per round | [\[MN20\]][MN20] Thm. 1.2 |
| Randomized weighted global minimum cut, failure `≤ 1/3` | `WeightedMinCut.Endpoint.weighted_global` | `10⁹ n log(2n)²` queries | [\[MN20\]][MN20] Thm. 1.2 |
| Randomized minimum cut of a simple graph, success `≥ 2/3` | `StarContraction2022.Randomized.exists_uniform_linear_program` | `O(n)` queries | [\[AEG+22\]][AEG+22] Thm. 1.1 |
| Quantum minimum cut of a simple graph, success `≥ 2/3` | `StarContraction2022.Quantum.Global.public_log_five_endpoint` | `O(√n L(n)⁵)` queries | [\[AEG+22\]][AEG+22] Thm. 1.3 |
| Deterministic weighted global minimum cut | `DetMinCut.deterministic_mincut_log5` | `O(n^{3/2} L(n)⁵)` queries | [\[P1\]][P1] Thm. 4 |
| Deterministic weighted global minimum cut with the Räcke–Shah hierarchy | `DetMinCut.deterministic_mincut_log3loglog2` | `O(n^{3/2} L(n)³ L(L(n))²)`, i.e. `O(n^{3/2} log³ n (log log n)²)` queries | [\[P1\]][P1] Thm. 4 |
| The same bound by the two-stage composition: connectivity test, Theorem 5 at `α = ⌊√n⌋`, conversion of the learned tree on the safe quotient, skeleton search, pull-back | `TreeCutSparsifier.deterministic_mincut_two_stage` | `O(n^{3/2} L(n)³ L(L(n))²)` queries | [\[P1\]][P1] Thm. 4 |
| Deterministic reporting of all global minimum cuts: the exact value and the complete family of minimum-cut shores (both `S` and `Sᶜ`), including graphs with zero minimum cut | `AllMinCuts.deterministic_all_mincuts_log3loglog2` | `O(n^{3/2} L(n)³ L(L(n))²)` queries | [\[P1\]][P1] Thm. 4 |
| Randomized reporting of all global minimum cuts (randomized cut sparsifier, then the deterministic tree cover and all-minima two-respecting search), failure `≤ (2n+2)^{-s}`; with a positive minimum cut the family has at most `8(n + n²)` shores (`AllMinCuts.card_le_of_isMinCut`) | `AllMinCuts.randomized_all_mincuts` | `2·10⁸ (s+8) n ln²(2n)` queries | [\[PRW24\]][PRW24], [\[P1\]][P1] §12.5 |
| Offline canonical tree cut sparsifier (Räcke–Shah): a hierarchy with distortion `268 L(n) L(L(n)) = O(log n log log n)`, at most `2n+1` nodes and height `2L(n)`, for every nonnegative real weighted graph | `Hierarchy.RackeShah.rackeShah_hierarchyBound` | offline existence, no queries | [\[P1\]][P1] Lemma 28 |
| Canonicalization of an explicit tree cut sparsifier with arbitrary terminal locations: singleton leaves, no unary nodes, `≤ 2n − 1` nodes, same approximation factor | `TreeCutSparsifier.exists_canonicalization` | `2n − 2` queries | [\[P1\]][P1] §4 |
| Weak skeleton from an arbitrary explicit `B`-tree cut sparsifier | `TreeCutSparsifier.exists_conversion` | `O(n B L(n)⁵)` queries | [\[P1\]][P1] Thm. 6 |
| Weak skeleton from an arbitrary explicit `B`-tree cut sparsifier, with the Räcke–Shah hierarchy | `TreeCutSparsifier.exists_conversion_log3loglog2` | `O(n B L(n)³ L(L(n))²)` queries | [\[P1\]][P1] Thm. 6 |
| Learning an explicit `α`-tree cut sparsifier of a safe quotient with the Räcke–Shah quality (Theorem 5), for `C log(2n)² log(6 log 2n)² ≤ α ≤ √n` | `TreeCutSparsifier.theorem5LL` | `O((n²/α) log(2n)³ log(6 log 2n)²)` queries | [\[P1\]][P1] Thm. 7 |
| Deterministic maximal spanning forest of the positive support, and connectivity test | `SupportForest.exists_support_forest`, `SupportForest.exists_connectivity_test` | `3n + 4n ⌈log₂ n⌉ ≤ 7 n L(n)` queries | [\[P1\]][P1] Lemma 9 |
| Deterministic minimum cut of a simple graph | `BoundedFlowMinCut.program_correct` | `n + (83 + 48·3⁸) n (⌊√n⌋+1) (⌈log₂(2n+2)⌉+1)² + 1 = O(n^{3/2} log² n)` queries | [\[KM26\]][KM26] Thm. 1.1 |
| Deterministic minimum s-t cut of a simple graph, with a maximum flow | `CanonicalST.exists_terminal_sqrt_program` | `⌈2²³ n^{3/2} ⌈log₂ 2n⌉³⌉` queries | [\[P2\]][P2] Thm. 1 |
| Minimum-cut certificates | `Certificate.exists_minCut_certificate` | `O(n log² n)` cut values | [\[P1\]][P1] Thm. 1 |
| Minimum s-t cut certificates | `Certificate.TreePattern.exists_terminal_tree_certificate` | `4n` cut values | [\[P1\]][P1] Lemma 2 |
| All-pairs minimum-cut certificates of a simple graph against simple competitors | `Certificate.UnitAllPairs.exists_unit_allPairs_certificate` | `3n` cut values | — |
| Deterministic minimum 2-respecting cut of a given spanning tree | `TwoRespecting.twoRespecting_queryBound` | `72 n (⌈log₂ n⌉ + 1)` queries | [\[P1\]][P1] Thm. 19 |
| Randomized all-pairs minimum cuts of a simple graph, failure `≤ (6n+2)^{-σ}` | `AllPairs.allPairsProgram_spec` | `600000 (σ+8) n^{3/2} (⌈log₂ n⌉+4)²` queries | [\[KK26\]][KK26] Thm. 1.2 |
| Deterministic all-pairs minimum cuts of a simple graph | `DeterministicAPMCExpansion.Pruning.deterministic_allPairs` | `O(n^{5/3} L(n)⁵)`, hence `o(n²)`, queries | [\[P2\]][P2] Thm. 2 |

### Directed graphs

Directed cut queries return the weight of the arcs leaving `S`.

| Result | Lean name | Bound | Source |
| --- | --- | --- | --- |
| Deterministic minimum s-t cut of a simple digraph | `DirectedUnitST.Endpoint.exists_unitST_query_program` | `2049 n^{5/3} L(n)²` queries | [\[P4\]][P4] Thm. 1.1 |
| Randomized minimum s-t cut of a simple digraph, success `≥ 1 − ζ` | `ImplicitLP.PathFollowing.directed_terminal_query_theorem` | `2³¹⁰ n^{3/2} log₂(2n/ζ)²¹` queries | [\[P4\]][P4] Thm. 1.2 |
| Randomized global minimum cut of a simple digraph, success `≥ 1 − ζ` | `ImplicitLP.PathFollowing.directed_global_query_theorem` | `2³⁴⁰ n^{7/4} log₂(2n/ζ)²²` queries | [\[P4\]][P4] Thm. 1.2 |
| Global minimum-cut certificates for weighted digraphs | `DirectedCertificate.Completion.exists_weighted_global_witnessCertificate` | `O(n^{5/3})` cut values | [\[P3\]][P3] Thm. 2 |
| Global minimum-cut certificates for unit-capacity digraphs | `DirectedCertificate.Completion.exists_unit_global_certificate` | `600 n^{3/2}` cut values | [\[P3\]][P3] Cor. 5 |
| Minimum s-t cut certificates for weighted digraphs | `DirectedCertificate.Completion.exists_exact_terminal_certificate` | `18n + 1` cut values | [\[P3\]][P3] Thm. 3 |

### Exact reconstruction

| Result | Lean name | Bound | Source |
| --- | --- | --- | --- |
| Quantum global, terminal, and all-pairs minimum cuts of a graph with integral capacities at most `W`, probability one | `Quantum.LinearReconstruction.exists_capacity_global` and its terminal and all-pairs versions | `6n⌈log₂(W+1)⌉` native queries; `6n` for unit capacities | [\[LSZ21\]][LSZ21] Thm. 28 |
| Quantum global, terminal, and all-pairs minimum cuts of a digraph with integral arc capacities at most `W`, probability one | `Quantum.DirectedReconstruction.exists_capacity_global` and its terminal and all-pairs versions | `n(24⌈log₂(2W+1)⌉ + 2)` native queries; `50n` for unit capacities | [\[LSZ21\]][LSZ21] Thm. 28 |
| Deterministic global and all-pairs minimum cuts of a unit-capacity digraph, following Grebinski–Kucherov | `Reconstruction.CompressedDirected.global_deterministic`, `allPairs_deterministic` | `(4 + 32768 ln 3) n²/ln(2n)` queries | [\[GK00\]][GK00] §4.1 |
| Deterministic terminal and all-pairs minimum cuts of a weighted graph, and an all-pairs certificate | `Reconstruction.WeightedUndirected.deterministic_terminal`, `deterministic_allPairs`, `allPairs_certificate` | `n + C(n,2)` queries | — |
| Deterministic global, terminal, and all-pairs minimum cuts of a weighted digraph, and an all-pairs certificate | `Reconstruction.WeightedDirected.deterministic_global` and its terminal, all-pairs, and certificate versions | `n² + 2n` queries | — |

[docs/COVERAGE.md](docs/COVERAGE.md) gives the source of each minimum-cut
result and the exact form of its bound, and the [notes](docs/README.md) record
the repairs to the randomized all-pairs proof and the design of the weighted
sparsifier. The checks files restate many more intermediate endpoints.

### References

- \[P1\]–\[P4\]: the [papers](#papers) in [`papers/`](papers).
- \[AEG+22\] S. Apers, Y. Efron, P. Gawrychowski, T. Lee, S. Mukhopadhyay, and
  D. Nanongkai. Cut query algorithms with star contraction. FOCS 2022;
  [arXiv:2201.05674](https://arxiv.org/abs/2201.05674).
- \[GK00\] V. Grebinski and G. Kucherov. Optimal reconstruction of graphs under
  the additive model. *Algorithmica* 28 (2000), 104–124;
  [doi:10.1007/s004530010033](https://doi.org/10.1007/s004530010033).
- \[KK26\] Y. Kenneth-Mordoch and R. Krauthgamer. Faster all-pairs minimum cut:
  bypassing exact max-flow. STOC 2026;
  [arXiv:2511.10036](https://arxiv.org/abs/2511.10036).
- \[KM26\] Y. Kenneth-Mordoch. Deterministic global minimum cut using
  Õ(n^{3/2}) cut queries;
  [arXiv:2610.23461](https://arxiv.org/abs/2610.23461).
- \[LP20\] J. Li and D. Panigrahi. Deterministic min-cut in poly-logarithmic
  max-flows. FOCS 2020;
  [arXiv:2111.02008](https://arxiv.org/abs/2111.02008).
- \[LSZ21\] T. Lee, M. Santha, and S. Zhang. Quantum algorithms for graph
  problems with cut queries. SODA 2021;
  [arXiv:2007.08285](https://arxiv.org/abs/2007.08285).
- \[MN20\] S. Mukhopadhyay and D. Nanongkai. Weighted min-cut: sequential,
  cut-query, and streaming algorithms. STOC 2020;
  [arXiv:1911.01651](https://arxiv.org/abs/1911.01651).
- \[PRW24\] O. Plevrakis, S. Ragavan, and S. M. Weinberg. On the cut-query
  complexity of approximating max-cut. ICALP 2024;
  [arXiv:2211.04506](https://arxiv.org/abs/2211.04506).

[P1]: papers/P1/finding-certifying-weighted-minimum-cuts.pdf
[P2]: papers/P2/deterministic-st-all-pairs-minimum-cuts.pdf
[P3]: papers/P3/directed-cut-certificates.pdf
[P4]: papers/P4/subquadratic-directed-minimum-cuts.pdf
[AEG+22]: https://arxiv.org/abs/2201.05674
[GK00]: https://doi.org/10.1007/s004530010033
[KK26]: https://arxiv.org/abs/2511.10036
[KM26]: https://arxiv.org/abs/2610.23461
[LP20]: https://arxiv.org/abs/2111.02008
[LSZ21]: https://arxiv.org/abs/2007.08285
[MN20]: https://arxiv.org/abs/1911.01651
[PRW24]: https://arxiv.org/abs/2211.04506

## Papers

The [`papers/`](papers) folder holds four preprints whose results are
formalized here, one folder each. The tables above cite them as [\[P1\]][P1]–[\[P4\]][P4], and other work by the
keys under [References](#references). Each paper has an appendix that maps its
numbered results to Lean declarations. Each folder also has a **Lean reader**: a guide to the
Lean statements of the paper's headline theorems, written so that a reader who does not use
Lean can check them against the paper, together with a file that checks them.

| | Paper | Lean reader |
| --- | --- | --- |
| P1 | [Finding and Certifying Weighted Minimum Cuts with Cut Queries](papers/P1/finding-certifying-weighted-minimum-cuts.pdf) | [P1 in Lean](papers/P1) |
| P2 | [Deterministic s–t and All-Pairs Minimum Cuts with Subquadratic Cut Queries](papers/P2/deterministic-st-all-pairs-minimum-cuts.pdf) | [P2 in Lean](papers/P2) |
| P3 | [Directed Cut Certificates through Fractional Forests and Shared Flows](papers/P3/directed-cut-certificates.pdf) | [P3 in Lean](papers/P3) |
| P4 | [Subquadratic Cut-Query Algorithms for Directed Minimum Cuts](papers/P4/subquadratic-directed-minimum-cuts.pdf) | [P4 in Lean](papers/P4) |

P2–P4 are preliminary drafts written by Codex GPT-6 Astra, whose main theorems
are verified in Lean 4 and whose prose proofs their author has not yet reviewed; see
[Authorship and AI use](papers/README.md#authorship-and-ai-use).

## Use in another Lean project

Version `0.1.0` uses Lean **4.35.0-rc2**, Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, and QuantumQueryComplexity `v0.1.0`.
Add this dependency to your `lakefile.toml`:

```toml
[[require]]
name = "CutQueryComplexity"
git = "https://github.com/troyjlee/cut-query-complexity"
rev = "v0.1.0"
```

Then run `lake update` and `lake exe cache get`. `import CutQueryComplexity`
imports the whole library; `import CutQueryComplexity.Classical` avoids every
quantum import, which the downstream check enforces.

## Models and conventions

- Deterministic algorithms are decision trees `DTree` and randomized algorithms
  are trees `RTree` whose nodes are probability distributions; the query cap is
  the depth index in the type. Quantum algorithms are finite circuits
  (`QRoutine`, from QuantumQueryComplexity) whose native oracle swaps a blank
  register with the cut value (see `Quantum.Model`).
- A program and its query cap are fixed by `n` (and terminals or accuracy
  parameters) before the hidden graph. Caps hold for every oracle, including
  oracles that do not come from a graph.
- Bounds count cut queries. Running time and gate complexity are not modelled.

## Build and verify

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean --trust=0 CutQueryComplexityChecks.lean
lake env lean --trust=0 CutQueryComplexityChecks/Endpoints.lean
python3 scripts/check-downstream.py
python3 scripts/check-axiom-audit.py
```

The two checks files audit disjoint module lists. Together they check every
declaration of 772 modules transitively and fix the statements of 4,987 named
declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
The downstream check builds a separate Lake project against the library. The
audit probes confirm that the audit rejects `sorry`, new axioms, and invalid
module or pin lists. After `lake exe cache get`, a full build from a fresh
clone takes about 35 minutes on a 30-core machine.

## Layout

| Path | Contents |
| --- | --- |
| `CutQueryComplexity/` | The library |
| `CutQueryComplexityChecks.lean`, `CutQueryComplexityChecks/` | Statement checks and axiom audits |
| `SLT/` | The matrix Bernstein inequality, vendored from [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) under Apache 2.0, with the adaptation diff |
| `tests/` | Downstream-client and regression checks |
| `docs/` | Coverage map, notes, and the audit of the Lee–Sidford facts |
| `papers/` | One folder per preprint (P1–P4) with its PDF and Lean reader; P4's folder also holds a supporting audit note |

## License and citation

The code is under the Apache License 2.0. The PDFs in `papers/` are not
covered by it; see [papers/README.md](papers/README.md). Formalization by Troy
Lee, with AI-assisted development using Claude and Codex.
[CITATION.cff](CITATION.cff) provides citation metadata. Each release is
archived on Zenodo: version 0.1.0 is
[doi:10.5281/zenodo.23885654](https://doi.org/10.5281/zenodo.23885654), and
[doi:10.5281/zenodo.23885653](https://doi.org/10.5281/zenodo.23885653)
resolves to the latest version. [docs/COVERAGE.md](docs/COVERAGE.md) and the
papers credit the underlying mathematical sources.
