# Randomized all-pairs minimum cuts of a simple graph

This note records the formalization of the cut-query upper bound of
Kenneth-Mordoch and Krauthgamer [KK26, Theorem 1.2]. It gives the proof route
the library follows and the places where the published argument needed a
repair. Every repair keeps the theorem and its query bound.

## Statement

`AllPairs.allPairsProgram_spec` (in `AllPairs/Budget.lean`). For a vertex type
`V` with `n ≥ 1` vertices and a confidence parameter `σ ≥ 0`, one public
randomized program `allPairsProgram σ` satisfies the following.

- **Query cap.** Every run on every oracle, including oracles that come from no
  graph, makes at most `600000 (σ+8) · n√n · (⌈log₂ n⌉ + 4)²` cut queries.
- **Correctness.** On every simple graph (0/1 weights), with probability at least
  `1 − (6n+2)^{-σ}`, it returns, for every pair of distinct vertices, a minimum
  s–t shore together with its exact cut value.

[KK26] states `Õ(n^{3/2})` queries with success probability `1 − 1/poly(n)`.
The only randomness is the initial cut sparsifier. There is no assumption on
minimum degree, connectivity, or a supplied decomposition.

## Proof route

The program has five public stages. Each lists the modules that implement it.

| Stage | What it does | Modules |
| --- | --- | --- |
| Padding | Attach a private triangle to every vertex, raising all degrees to at least 2 | `AllPairs/Padding` |
| Sparsifier | Learn an explicit graph `K` with `½ cut_G(S) ≤ cut_K(S) ≤ 3/2 cut_G(S)` for all `S` | `AllPairs/Main` (`initialSparsifier`), `Sparsification/*` |
| Partition and shaving | Split `K` offline into expanding blocks, then shave low-degree and high-boundary vertices | `AllPairs/Partition`, `AllPairs/Shaving` |
| Recovery | Recover every original edge leaving a block, with its endpoints, under a public edge cap | `AllPairs/Recovery` |
| Star and minimization | Replace each block by a star, then minimize every pair offline | `AllPairs/Representation`, `AllPairsAudit/Star`, `AllPairsAudit/Endpoint` |

The structural argument is the star theorem `AllPairsAudit.star_minimum_extract`:

- it applies to any block map that does not split a small friendly cut
  (`PreservesFriendly`);
- every minimum s–t cut of the star graph restricts to a minimum s–t cut of the
  original graph, with equal value;
- the star never underestimates a cut (`star_cut_dominates`).

Here a cut is friendly when every vertex has friendliness at least 1/6, that is,
`6·crossing ≤ 5·degree` (`AllPairsAudit.Friendly`).

## Repairs to the source

Page numbers refer to [KK26] arXiv v2 and [KK26a] arXiv v1.

| Source | Issue | Repair | Lean |
| --- | --- | --- | --- |
| [KK26] Lemma 3.4, p. 8 | The proof claims every vertex of `S∖{s}` has degree at least 3, since moving a degree-2 vertex across the cut would violate minimality. That fails for a vertex adjacent to `s`. Take `K₁₂ ∋ s, t` plus a triangle `s–a–b`: then `{s,a,b}` is a minimal minimum s–t cut, `s` has friendliness `2/13`, and `a, b` have degree 2. | By minimality, a degree-2 vertex of `S∖{s}` has no edge crossing `S`, so its friendliness with respect to `S∖{s}` is at least 1/2. The lemma's conclusion holds. | `AllPairsAudit.degree_two_crossing_zero`, `AllPairsAudit.lemma34` |
| [KK26] Claim 3.5, p. 10 | The proof fixes a minimal minimum shore of `s`, then assumes without loss of generality that `s` is the unfriendly terminal. If `t` is the unfriendly one, its shore `V∖S` is maximal rather than minimal, so Lemma 3.4 does not apply. | First identify the unfriendly terminal, then shrink its own shore to a minimal one. Shrinking only adds crossing edges at that terminal, so it stays unfriendly. | `AllPairsAudit.exists_minimal_unfriendly_inside`, `AllPairsAudit.exists_structured_minimum` |
| [KK26] Theorem 2.1, p. 9 | Contractions are modelled as infinite-capacity edges, and the proof says that capacity cancels in `f_v(X) = cut_H(X) − 2w_H(X,v) + deg(v)`. It does not, because `deg(v)` is the degree in `G`. In the triangle `s–a–t`, contracting `{s,a}` gives a valid sparsifier but `f_s({a}) = 2 − M`. | Not used. Theorem 1.2 goes through the star construction (Theorem 2.3). The Lean star is built from block maps, with no contraction capacities. | `AllPairsAudit.star`, `AllPairsAudit.star_minimum_extract` |
| [KK26a] Algorithm 3, p. 14 | The shaving rule is printed as `d(v) < 4α·|E(v, V∖H)|`. The proof of Claim B.2 needs `4α⁻¹`, and Claim B.3 uses `α⁻¹`. | Keep a vertex exactly when `d(v) ≥ 60τ` and `24·boundary(v) ≤ d(v)`. These are the intended conditions at `α = 1/6`. | `AllPairs.Keep` |
| [KK26a] Lemma C.3, p. 19 | The proof uses a (1 ± ½) cut sparsifier of `G` to check the Prune condition of BalCutPrune, which asks for expansion of an induced subgraph `G[A]`. Edge counts inside `G[A]` are differences of cuts of `G`, so a sparsifier of `G` need not approximate them. This is a gap in the proof, not a counterexample to the lemma. | Replace the expander decomposition of `G` by an offline decomposition of the explicit sparsifier `K`, as described below. The argument uses only `K`'s approximation of the cuts of `G`. | `AllPairs/Partition`, `AllPairs/Shaving`, `AllPairs.friendlyProgram_good` |

[KK26] assumes throughout that no vertex has degree 1 (p. 5) and notes that this
is easily removed. The formalization removes it by attaching a private triangle
to every vertex. Each padded cut is an original cut plus a known triangle cut,
so terminal minima extract exactly (`AllPairs.padded_minimum_extract`).

### The replacement friendly-cut sparsifier

The construction replaces [KK26a] Lemma 1.7 with the same query bound. Set
`τ = ⌊√(2n)⌋ + 1`, so `τ² ≥ 2n`.

1. **Offline decomposition.** Split the explicit sparsifier `K` while some block
   `W` has a subset `A` with `w_K(A, W∖A) < τ · min(|A|, |W∖A|)`. Charging each
   split to the smaller side bounds the sum of the block boundaries in `K` by
   `2τ · n · ⌈log₂ n⌉` (`partitionMap_expands`, `partitionMap_boundary_le`).
2. **Shaving.** In each block, keep the vertices with `d_G(v) ≥ 60τ` and at most a
   `1/24` fraction of their edges leaving the block. The degrees and boundary
   degrees cost at most `3n` queries (`shaveProgram_cost`).
3. **No small friendly cut splits a block of kept vertices.** Suppose a friendly
   cut `S` of `G` with at most `2n` edges separated kept vertices of one block.
   Each kept vertex has at least `(1/6 − 1/24)·60τ = 7.5τ` neighbours on its own
   side within the block. Since `G` is simple, both sides of the block then have
   at least `7.5τ` vertices. The block's expansion in `K` gives
   `cut_K(S) ≥ 7.5τ² ≥ 15n`, while `cut_K(S) ≤ 3/2 · 2n = 3n`, a contradiction
   (`retained_no_split`, `shaveProgram_respects`).
4. **Few surviving edges.** The global approximation transfers the decomposition's
   boundary bound to `G`. After shaving, the blocks leave at most
   `196 τ n ⌈log₂ n⌉ + 120 n τ` original edges (`shaveProgram_sparse_bound`).
   Recovery enumerates them under a public cap and aborts if the cap is exceeded
   (`recoverCapped_correct`, `recoverCapped_abort`).

## Not formalized

- **Theorem 1.4.** It constructs Gomory–Hu trees of symmetric submodular
  functions, and Theorem 1.2 does not use it. Its proof relies on the recursive
  size bound of arXiv:2509.02520, which has been withdrawn. The library's
  graph-only reduction `GHReduction.exists_weighted_gh_reduction` does not depend
  on that paper.
- **The streaming and fully-dynamic results** of [KK26] are outside the
  cut-query model.
- **The algorithm of Theorem 2.1**, which the formalization does not need.

## References

- [KK26] Y. Kenneth-Mordoch and R. Krauthgamer. Faster all-pairs minimum cut:
  bypassing exact max-flow. STOC 2026;
  [arXiv:2511.10036v2](https://arxiv.org/abs/2511.10036v2).
- [KK26a] Y. Kenneth-Mordoch and R. Krauthgamer. All-pairs minimum cut using
  Õ(n^{7/4}) cut queries;
  [arXiv:2510.16741v1](https://arxiv.org/abs/2510.16741v1).
