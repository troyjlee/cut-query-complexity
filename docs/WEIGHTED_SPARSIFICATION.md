# Weighted cut-query sparsification

This note records the sources and the proof design of weight-independent cut
sparsification. The adaptive algorithm is formalized as `WeightedGraph.sparsify`,
and its all-cuts guarantee under a hard query cap is proved
(`sparsify_correct`); §8 lists the Lean modules. The Lean
development uses the simplified schedule described below. It also uses the
counted sampler with `c = Θ(log n/ε²)`, which needs no BK recompression. The
explicit-parameter statement `sparsify_whp` gives failure at most `(2n+2)^{−s}`
and at most `⌊4c(n−1) + n⌋` output edges.

The missing reference is Plevrakis–Ragavan–Weinberg (PRW), *On the cut-query
complexity of approximating max-cut*, ICALP 2024. Its full
[arXiv v3](https://arxiv.org/abs/2211.04506v3), Theorem 4.13 and Appendix G,
provides weighted sparsification without dependence on weight spread. The
arXiv version includes the appendix. RSW is the unweighted predecessor; for arbitrary weights the formalization
relies on PRW rather than on MN Theorem 5.2 alone.

## 1. The theorem

In source form the result is as follows. Let `L(n) = 1 + log(max 2 n)`. For every fixed positive integer `s`, there are
constants `C_s, K_s` and, for every `n ≥ 2` and `0 < ε < 1`, one randomized
cut-query algorithm, chosen independently of the hidden graph, such that:

- Its input is any undirected graph on `Fin n` with nonnegative real weights.
- On every execution it uses at most
  `⌈C_s * n * (L(n)^4 + L(n)^3 / ε²)⌉` queries.
- With probability at least `1 - n^(-s)`, it returns an explicit graph `H`
  with nonnegative weights, `support H ⊆ support G`, at most
  `⌈K_s * n * L(n) / ε²⌉` edges, and
  `∀ S, (1-ε) cut_G(S) ≤ cut_H(S) ≤ (1+ε) cut_G(S)`.

There is no integrality, connectedness, minimum positive weight, or bounded
weight-ratio premise. The budget
is for an exact real-valued classical oracle, with computation and randomness
free. It is not a finite-bit running-time theorem.

The Lean endpoint `WeightedGraph.sparsify_whp` proves a sharper form: for
`s ≥ 0` and `0 < ε ≤ 1` the algorithm uses `O(s n log² n (1 + 1/ε²))` queries
on every execution and fails with probability at most `(2n+2)^{−s}`, and its
output has at most `⌊4c(n−1) + n⌋` edges with `c = Θ(log n/ε²)`. The counted
sampler of §4 gives this support bound directly, without the recompression of §7.

PRW Theorem 4.13 states the query bound and a `2ε` cut guarantee, with failure
`O(n^(5-d))` for an adjustable constant `d`. Reparameterizing the accuracy and
choosing `d` supplies our accuracy and confidence. Its sampling count gives
an intermediate `O(n L(n)^2 / ε²)` support bound. The sharper support bound
above follows by **offline recompression**, explained in §7; it should not
be attributed directly to the theorem's statement.

## 2. The graph invariants

For distinct vertices define pair strength by

```text
k_G(u,v) = max { mincut(G[U]) : {u,v} ⊆ U ⊆ V }.
```

This definition also covers nonedges. It is zero between different positive
weight components. For an original positive edge `e = {u,v}`, write `k_e`.
Do not substitute the minimum global cut separating the endpoints: that is
a different connectivity parameter.

A set is `κ`-strong when every proper cut of its induced graph has weight
at least `κ`; singletons satisfy this vacuously. For `κ > 0`, overlapping
strong sets have a strong union. Consequently maximal strong sets partition
the vertices, and these partitions coarsen as `κ` decreases. Two distinct
vertices are in the same such component exactly when `k_G(u,v) ≥ κ`.

The central charging bound is

```text
∑ e ∈ support G, w_e / k_e ≤ n - 1.
```

Use Benczúr–Karger's 2015 journal version (BK), Lemmas 4.8–4.11, for these
facts. In particular, use the strength
decomposition in BK §5, not an unsupported union bound over all original cuts.

The deterministic decomposition is now proved in Lean. There are at most
`n−1` distinct nontrivial positive-threshold components. Summing consecutive
strength increments over the levels where each component occurs produces
positive coefficients; for a fixed pair, the containing coefficients sum to
its strength. The same coefficients reconstruct every supported outcome graph
from its strength-normalized component pieces. Scaled reference pieces have
minimum induced cut exactly `c`, and the smoothness condition bounds each
scaled outcome edge by one. Component cut approximation transfers with the
same error factor. Expected-graph identities and the union bound across
dependent component pieces are also proved: uniform component failure `δ`
gives total failure at most `(n−1)δ`. The exponential-moment API supplies the
Markov step for both tails. Bounded independent draws satisfy per-cut
failure `2 exp(−ε² cut/4)`. The fixed-bucket counted sampler's mean and cut-law
witnesses are proved. Integer-threshold weighted cut counting is also proved,
using each component's own vertex count. The exponential-sum estimate
(`Sparsification/CutTailBound`) and the adaptive query program
(`Sparsification/Weighted`) complete the proof.

Maintain contractions as a partition `Π` of the original vertices. Keep an
original edge's identity even when different original edges become parallel
between blocks. Quotient capacities suffice for cut evaluation, but a sampled
quotient edge must be resolved back to its original endpoints.

Cache the original cut value `c(B)` of each current block. For a union `U`
of current blocks, the mass of original edges inside `U` whose endpoints
are in different blocks is

```text
M_Π(U) = ((∑ B ∈ Π with B ⊆ U, c(B)) - c(U)) / 2.
```

Initialization uses `n` singleton queries. Merging blocks into `U` needs at most one new
query, for `c(U)`. Each nontrivial merge reduces the number of blocks.

Two useful deterministic/probabilistic query programs follow (PRW Lemma 4.5
and Appendix G.1):

| Program | Contract |
| --- | --- |
| `sampleResidualEdge Π U` | If `M_Π(U) > 0`, return an original surviving unordered edge `e` with probability exactly `w_e / M_Π(U)`, using `O(L(n))` queries |
| `findHeavyResidual Π` | If the total surviving mass is `M > 0`, return an original surviving edge of weight at least `2M/n²`, using `O(L(n))` queries |

The implemented sampler chooses a block proportionally to its residual degree
inside `U`, then samples an original edge from that block to the other blocks
inside `U`. This is a degree-based implementation of the sampling contract.
Writing `T` for the labels in `U`, `S = A ∩ T`, and `R = T \ S`, the additive
degree oracle is

```text
D_T(A) = Σ b∈S c(fiber π b) + (c(pull π R) − c(pull π S) − c(pull π T)) / 2.
```

Each degree sum uses exactly three original cut queries. Binary subset
sampling chooses a block in `3*(2*kB+1)` queries; the existing crossing-edge
sampler resolves original endpoints in `6*(2*kV+1)` more, where
`kB = Nat.clog 2 (card B)` and `kV = Nat.clog 2 n`. Each orientation has
probability `w_e/(2M)`; forgetting orientation gives `w_e/M`. Thus the cached
budget is `6*kB+12*kV+9`, or `18*kV+9` when block labels use the original
vertex type. Zero mass returns `none`. Empty block labels and original edges
that become parallel after contraction are handled explicitly.

For the heavy edge, some block `B` has
`c(B)/(|B|(n-|B|)) ≥ 2M/n²`: sum the numerators and bound the sum of the
denominators by `n²`. Bisect the two sides of its cut, keeping a part whose
average weight per possible pair is at least the current average. This ends
at one original edge with the claimed weight.

## 3. Find relevant scales without a weight-ratio loop

Repeatedly find a heavy surviving edge, record its original weight, and
contract its endpoints. This builds a spanning forest `T` in `O(n L(n))`
queries. At most `n-1` edges are selected.

For connected distinct vertices, let `d̃(u,v)` be the minimum edge weight
on their path in `T`, and set it to zero for disconnected pairs. The forest
is explicit, so every such value is now available without queries. PRW
Lemmas 4.10–4.11 and Corollary 4.12 yield

```text
d̃(u,v) ≤ k_G(u,v) ≤ (n^4 / 2) * d̃(u,v).
```

The implemented Lean proof gives the stronger bound
`d̃(u,v) ≤ k_G(u,v) ≤ (n²/2)*d̃(u,v)` and exports the displayed `n⁴/2` bound
as a corollary. It uses a direct mass argument: while `u,v` lie in different
blocks, the original cut of the block containing `u` separates them, so
`k_G(u,v) ≤ c(B) ≤ M`. Every edge selected while that pair is separated
therefore weighs at least `2*k_G(u,v)/n²`. At the merge connecting the pair,
all previously selected edges satisfy this bound, and they supply the path.
Later insertions preserve it. The lower bound follows by joining strong
two-vertex sets along a path.

`approxKruskal` initializes the cache once, pays three queries to recover each
selected edge's original weight, and pays one query per cache update. Its
public worst-case budget is `n+(n−1)*(6*(clog 2 n+1)+4)`. It returns an explicit
weighted forest with at most `n−1` edges and handles disconnected inputs.
`WeightedGraph.bottleneck` uses the largest connecting edge threshold and
proves zero/disconnected behavior and attainment by an observed edge weight.
The scale schedule below can continue to use the proved weaker PRW interface.

Use PRW Algorithm 4.5's schedule, with an explicit list of **vertex pairs**:

```text
Π := singleton partition; labels := []; κ := unset
P := all distinct pairs with d̃(u,v) > 0
while P is nonempty:
    D := max {d̃(u,v) : (u,v) ∈ P}
    regions := components of T retaining edges of weight ≥ D/(2n^5)
    κ' := least power 2^z, z ∈ ℤ, with κ' ≥ n^4 D/2
    κ := κ' if unset, otherwise min(κ, κ')
    while κ ≥ D/(2n):
        for each region S:
            estimateAndContract(G[S], Π, κ, labels)
        remove from P all pairs now in the same block
        κ := κ/2
    abort if this round removed no pair
```

The pairs include nonedges; storing only their numeric values loses the
information needed for removal. Negative dyadic exponents are essential for
arbitrarily small weights. A successful run never takes the abort branch.

As `D` decreases, these regions form a laminar family of at most `2n-1`
distinct nonempty vertex sets. Previously merged blocks remain inside a
current region. Across different regions, every pair has strength strictly
less than `D/(4n) ≤ κ/2`; hence every `κ/2`-strong component is contained
in a region. An edge excluded from this round remains available in later
rounds. There is no permanent deletion of low-weight edges.

Cache `c(S)` once for each region of this known forest hierarchy. The mass
formula in §2 then answers all repeated `M_Π(S)` requests without a new
query, using the maintained block cuts. This supplies the query accounting
needed when many estimation calls make no contraction; initializing a fresh
data structure for every induced graph would lose the bound.

### Simplified schedule used in Lean

The Lean development uses a simpler schedule with the same guarantees
(`Sparsification/Window`). Before every batch it recomputes `D` over
the remaining pairs and sets `κ := min(κ_prev/2, n²D/2)`. Regions are the
components of the forest above `D/n²`. The quadratic forest bound makes these
constants valid. Rounds, dyadic rounding, and the abort branch are unnecessary.
Under the invariant, `D/2 < κ`, so every batch makes progress toward
contracting a pair attaining `D`. The total number of draws is bounded by a
geometric sum, `8ρ(n−1)`, without a factor for the number of calls.

## 4. A sampling formulation for the Lean proof

PRW's algorithm keeps each distinct sampled edge once, reweighted by its
probability of appearing at least once. That probability is
`1 - (1 - w_e/M)^r`, not the probability in one draw. Its Appendix G proves
the required concentration, including a separate treatment of heavy edges.

The formalization makes a small change: **count every draw**. Draw `r`
original edges independently with replacement, proportional to their weights,
and give each occurrence weight `M/r`. Combine repeated occurrences by
adding their weights. This still outputs a reweighted subgraph, with expected
edge weight `w_e`. It is a variant, not PRW's printed pseudocode.

Here is its concentration proof obligation and reduction. Suppose disjoint
buckets `E_i` partition the positive edges, have masses `M_i > 0`, and have
known positive lower bounds `0 < β_i ≤ k_e` for every edge in the bucket.
Fix `c > 0` and independently sample `r_i` times in bucket `i`, where

```text
r_i ≥ c * M_i / β_i.
```

For analysis only, create a parallel copy `(i,j,e)` for every draw index `j`
and possible edge `e ∈ E_i`. Its random weight is

```text
(M_i/r_i) * 1{draw j selects e}.
```

Each copy has expectation `w_e/r_i`; the expected parallel graph has
exactly the cuts of `G`, and the strength of each copy is `k_e`. Moreover
`c * M_i/r_i ≤ β_i ≤ k_e`, which is precisely `c`-smoothness.

For one draw the indicators are mutually exclusive. For any subset, their
all-one probability is at most the product of the marginals, and their
all-zero probability satisfies `1-∑p_e ≤ ∏(1-p_e)`. Independent draws preserve
both inequalities. These inequalities give the upper and lower exponential
moment bounds needed for weighted Chernoff. Apply the strength decomposition
and cut-counting proof of PRW Theorem G.9 (BK Theorem 5.2 with this negative
dependence argument) to obtain simultaneous `1±a` preservation when
`c ≥ C_d L(n)/a²`, with failure at most a chosen polynomial in `n`.

For this counted sampler, the per-cut proof can also use one bounded
variable per draw directly. Fix a component `U` and a shore `S`. If draw `(i,j)`
selects `e = {u,v}`, its contribution to the normalized piece's cut is

```text
Y_ij = c * M_i / (r_i * k_e) * 1{u,v ∈ U and e crosses S}.
```

Every `Y_ij` lies in `[0,1]` by the sample-count bound. These variables are
independent across draws, and their sum has mean `F_U(G).cut S`. Thus the
formalized bounded-variable moment estimate
`E[exp(tY)] ≤ exp((exp(t)−1) E[Y])`, together with the independent-sum identity,
gives both relative-error tails with exponent `−a²μ/4` for `0 ≤ a ≤ 1`.
The two-sided bound is `2 exp(−a²μ/4)`. In Lean, `HasBoundedCutLaw` specifies
the required independent-sum representation and `HasMean.boundedCut_mean`
identifies its mean. `CountedBucket.sampleLaw` implements the fixed-bucket
probability law, proves its exact mean, and constructs those witnesses from
the sample-count condition. The deterministic integer-threshold cut count and
the summed exponential tails are proved (`CutTailBound`). For fixed
buckets, `ε²c ≥ 8(2 log 2n + log(4/δ))` gives failure at most `(n−1)δ`. The adaptive algorithm constructs the
buckets, proves that their reference sum equals its input graph
(`eventBuckets_reference`), and realizes these draws by query programs
(`Sparsification/OutputRun`).

`sparsifier_failure_le_strength_cut_sum` reduces whole-graph failure
to the sum of these exponential bounds over positive proper shores inside
each reference component. Zero cuts are exact on every supported outcome,
and vertices outside the component do not enlarge the shore family. The
family includes complementary shores. `strengthPiece_bounded_shores_card`
counts them: for every natural `k ≥ 1`, at most `(2 * |U|)^(2k)` shores
of a reference piece have cut weight at most `k c`, where its minimum induced
cut is `c > 0`. The global theorem proves the finer binomial bound by weighted
contraction averaging, with a powerset base case below `2k` vertices. `Sparsification/CutTailBound`
combines these counts with the exponential tails to obtain the
numerical failure budget.

There is no independence claim for different edges of the sampled graph.
Nor is the auxiliary parallel graph an expansion into integer weight copies:
it exists only in this finite probability proof and costs no oracle queries.
This argument works uniformly for `0 < a < 1`, including very small accuracy
parameters. It avoids the heavy-edge coupling in the inclusion sampler.

## 5. The estimation contract and its proof

Choose `ρ = A_d L(n)^2`, with `A_d ≥ 2` large enough for the desired error
exponent. An estimation call sees the residual quotient of `G[S]`, with
mass `M`, and operates as follows:

1. If `M < κ/2`, return without contracting. In particular, skip `M = 0`.
2. Otherwise take `r = ⌈ρ M/κ⌉` weighted draws and give each occurrence
   weight `M/r`, obtaining an explicit graph on the current blocks.
3. Recursively split parts along induced cuts of sampled weight at most
   `3κ/4`, until every remaining nonsingleton part has larger mincut.
   All these computations use the explicit sample and cost no queries.
4. Contract each part containing at least two current blocks. Record its
   original vertex set with label `β = κ/2`.

The desired conditional contract is:

- Every true `κ`-strong component becomes contained in one new block.
- If the old partition refines the true `κ/2`-strong partition, then the
  new partition also refines it.

Here "true" refers to the induced input before these contractions. At the
start of an actual batch the stronger invariant holds that the old blocks
refine its `κ`-strong partition.

For completeness, a true `κ`-strong component remains `κ`-strong in the
quotient. Restrict the draw-copy graph from §4 to this component. Its maximum
copy weight is at most `κ/ρ`, so it is `ρ`-smooth. With sufficiently large
`A_d`, its cuts are all preserved within `1±1/8`. Such a component cannot be
split by a cut of weight at most `3κ/4`. Union-bound over at most `n`
components. If `M < κ/2`, no nonsingleton `κ`-strong residual component
exists, so the skip is valid.

For soundness, fix a recursive decomposition of the true input along cuts
of weight less than `κ/2` until reaching its maximal `κ/2`-strong components.
It uses at most `n-1` cuts. Because old blocks refine these components, each
decomposition cut is a legal quotient cut in its corresponding induced part.
If such a cut has weight `b < κ/2`, its sampled weight has distribution

```text
(M/r) * Binomial(r, b/M).
```

Since `M/r ≤ κ/ρ`, a Chernoff bound gives probability at most
`exp(-ρ/24)` that this weight reaches `3κ/4`. If all these fixed cuts stay
below the threshold, no final sampled strong part can cross the first
decomposition cut that would separate it. Thus the new partition refines
the true one. This proves the contract using at most `n-1` bad-cut events.

**Lean.** Both halves are proved for fixed buckets over an
arbitrary reference graph: `CountedBucket.sampleLaw_sound` and
`CountedBucket.sampleLaw_complete`. The proofs use accuracy `1 ± 1/4` for
completeness, requiring `(2n)² exp(−ρ/128) ≤ δ/4`. Soundness uses
`exp(−ρ/32)` per split cut, from the moment parameter `t = 1/4`. The split
family is constructed by `exists_splitFamily`. `EstimateResidual` and
`EstimateProgram` identify the reference with the residual quotient. They run
the `r = ⌈ρM/κ⌉` draws as a query program, and `residualDraws_sound` and
`residualDraws_complete` state both contracts for that program. `EstimateLift`
lifts them to original vertices and proves the skip rule. `EstimateCall`
packages one call, with one region query, the cached mass, the skip rule, and a
hard draw cap. Its contracts are `estimateCall_sound` and `estimateCall_complete`.

These arguments replace the sampling-specific proofs of PRW Lemmas 4.6–4.7
for our variant; the window and strength arguments remain the same. They
are mathematical reductions to lemmas we must prove, not assumed Lean axioms.

## 6. Labels, termination, and query accounting

Induct on batches, conditioning on successful previous estimation calls:

1. Before a batch at scale `κ`, every uncontracted pair has strength at most
   `2κ`, and the current partition refines the `κ`-strong partition.
2. The regions contain every relevant strong component, so the local
   estimation contracts apply to the original graph's thresholds.
3. After the batch, every pair of strength at least `κ` is contracted;
   no pair of strength below `κ/2` has just been contracted.
4. Every positive edge first internalized in this batch gets a label
   `k_e/4 ≤ β ≤ k_e`.

The first batch after a downward jump is valid because
`κ' ≥ n^4 D/2 ≥ k_G(u,v)` for all remaining pairs. Other batches inherit the
invariant by halving. In the last batch of a round, `κ < D/n ≤ D`;
therefore a pair attaining `D` is contracted. This proves progress and
termination even if that pair is a nonedge. At termination each positive
weight component has become a block, so all positive edges have labels.

The recorded merged sets are laminar and number at most `n-1`. The bucket
owned by a recorded set `C_i` consists of its internal original edges that
were not internal to any earlier recorded descendant. These buckets are
disjoint and cover the positive edges. The algorithm never enumerates them.

For the estimation work, consider an uncontracted positive edge participating
in a call at scale `κ` in a round with maximum `D`. Its endpoints are in one
region, so `d̃_e ≥ D/(2n^5)`, and `κ < n^4 D`. Combined with the invariant,

```text
k_e/2 ≤ κ ≤ 2n^9 k_e.
```

Global scales strictly decrease by at least a factor of two between batches,
and regions in one batch are disjoint. Thus the edge participates in at most
`3 + 9⌈log₂ n⌉` calls. It does not participate once for every factor of two
in the input's weight spread.

Integer sample counts need attention. A call that samples has `M ≥ κ/2`,
so `ρ M/κ ≥ 1` and `⌈ρ M/κ⌉ ≤ 2ρ M/κ`. Thus

```text
total estimation draws
  ≤ 2ρ ∑ calls ∑ surviving e in the call, w_e/κ
  ≤ 4ρ ∑ e, (w_e/k_e) * numberOfCallsContaining(e)
  = O_d(n L(n)^3).
```

Each draw costs `O(L(n))` queries. Initialization, block updates, and cached
region cuts cost `O(n)` beyond those draws, giving `O_d(n L(n)^4)` total.
Rounding one sample up for every tiny-mass call, without the skip, would
not justify this bound.

There are at most `binom(n,2)` successful outer rounds, `O(L(n))` batches
per round, and at most `n` estimation calls per batch. The progress guard
therefore bounds the number of calls on all histories by `O(n^3 L(n))`.
Use conditional error bounds up to the first failed call, and choose their
exponent large enough to union-bound this many events. An unconditional
independence assertion about different calls would be incorrect.

Finally impose the advertised hard query cap, returning failure before an
additional query could exceed it. The charging argument shows that the cap
never binds on a successful history. It supplies a worst-case budget even
when an erroneous contraction would otherwise invalidate the work bound.

## 7. Output sampling and the sharp edge bound

This section gives the source-level route. The Lean development samples with
`c = Θ(log n/ε²)` and does not formalize the BK compression step (see §1).

Condition on a successful realized list `(C_i, β_i)` and use fresh randomness.
Reset the partition to singletons, visit recorded sets with descendants
first, compute the residual internal mass `M_i`, sample its bucket, and
contract `C_i`. Empty buckets require no draws. For `a = ε/4`, take

```text
r_i = ⌈B_d L(n)^2 M_i / (a² β_i)⌉
```

draws in a nonempty bucket, with weight `M_i/r_i` for each occurrence. The
lemma in §4 gives an intermediate `1±a` sparsifier `H₀`. Since each bucket
has `β_i ≥ k_e/4`,

```text
∑ i, r_i ≤ (4B_d L(n)^2/a²) * (n-1) + (n-1).
```

This gives `O_d(n L(n)^2/ε²)` edges and `O_d(n L(n)^3/ε²)` queries, uniformly
in the weights and in `ε`. Fresh randomness is essential: condition on the
labels first, then apply the sampling lemma to their fixed disjoint buckets.

Now `H₀` is entirely explicit. Apply BK's 2015 Compression Theorem 6.2 to
`H₀`, at error `ε/4`, obtaining `O(n L(n)/ε²)` edges with **zero additional
queries to G**. If desired this postprocessing can be deterministic: compute
strengths of the known graph by exhaustive finite search, enumerate the
finite supports of the BK sampling experiment, and select a support that
meets both its size bound and all-cut inequalities. The probabilistic
existence theorem guarantees such a support after fixing sufficient
constants. All candidate weights are determined by `H₀` and their actual
sampling probabilities, including probability-one edges.

This exhaustive choice may be slow; time is free in the query model. It
adds no failure probability and no reliance on being able to check an
unknown cut of `G`. A randomized polynomial-time BK postprocessor is another
option, with its own explicit failure allowance.

The two approximations compose because, for `0 < ε < 1`,

```text
(1-ε/4)^2 ≥ 1-ε,     (1+ε/4)^2 ≤ 1+ε.
```

Support containment is transitive. This proves the sharper edge target
without silently identifying the number of PRW samples with `O(n log n/ε²)`.

## 8. Lean modules

The endpoint is `WeightedGraph.sparsify_whp` (`Sparsification/WeightedParams`), which
instantiates `sparsify_correct` (`Sparsification/Weighted`) with explicit parameters.
Local lemmas are parameterized by the original `n` and a failure budget, even when
the active quotient has fewer vertices, and costs are proved in the oracle program
semantics.

| Modules | Contents |
| --- | --- |
| `Graph/StrongComponent`, `Sparsification/Strength` | Pair strength; laminar partitions; contraction lemmas; strength sum |
| `Sparsification/StrongComponentCount`, `StrengthLevels`, `StrengthCoefficients`, `ComponentNormalization`, `StrengthDecomposition` | At most `n−1` pieces; positive coefficients; uniform reconstruction; normalized component mincuts; cut-error transfer |
| `Probability/Expectation`, `FiniteEvents`, `Exponential`, `Graph/RandomMean`, `Sparsification/RandomDecomposition` | Finite expected graphs; random BK pieces; component union bound; conditional moments; exponential Markov bounds |
| `Probability/BoundedDraw`, `Chernoff`, `Graph/CutConcentration`, `Sparsification/ComponentConcentration` | Bounded-draw moments and means; multiplicative tails; per-cut law interface; reduction to exponential sums over component shores |
| `Graph/EdgeSum`, `IndependentSum`, `Probability/Categorical`, `Sparsification/CountedSampling`, `CountedConcentration` | Fixed-bucket counted law; accumulated occurrences; exact means; per-occurrence bounds; constructed component-cut witnesses |
| `Graph/RespectingCuts`, `ContractionCounting`, `VertexRestriction`, `Sparsification/CutCounting`, `LocalCutCounting` | Weighted survival recurrence; binomial cut counting at integer thresholds; component-local shore counts |
| `Primitive/Residual*`, `Primitive/Heavy*` | Partition mass formula; cache updates; exact sampling law; heavy-edge search; original endpoints |
| `Sparsification/CutTailBound` | Sum exponential tails using the proved cut count; high-probability simultaneous concentration |
| `Graph/Bottleneck`, `Sparsification/KruskalInvariant`, `Sparsification/ApproxKruskal` | Explicit weighted forest and `d̃ ≤ k ≤ n² d̃/2`, with the `n⁴/2` corollary |
| `Sparsification/EstimateSound`, `EstimateComplete` | Split family; additive tail; soundness and completeness of one contraction step for fixed buckets |
| `Sparsification/EstimateResidual`, `EstimateProgram` | Residual-quotient instantiation; exact block-level draw law; `r`-draw query program; rounding; program-level contracts |
| `Sparsification/EstimateLift`, `EstimateCall` | Skip rule, in-program mass, lifting to original vertices, and the packaged call contract |
| `Sparsification/Window` | Region hierarchy, scale invariants, pair progress, and labels |
| `Sparsification/Merge`, `EstimationRun`, `EstimationInvariant`, `EstimationTermination`, `EstimationEvents` | The adaptive estimation run as an iterated query program: merges, the invariant of a good run, termination, and merge events |
| `Sparsification/EstimationCost`, `EstimationCharge`, `EstimationBudget` | Query costs of the estimation run and their charging |
| `Sparsification/OutputSample`, `OutputRun`, `OutputCorrect`, `OutputEdges`, `OutputBudget` | Output sampling from the merge events: draws, correctness, edge count, and query cost |
| `Sparsification/Weighted`, `WeightedParams` | Hard cap, failure accounting, the all-cut relation (`sparsify_correct`), and the explicit-parameter endpoint (`sparsify_whp`) |

## Source correspondence

| Ingredient | Source in the pinned versions |
| --- | --- |
| Arbitrary-weight query bound | PRW Theorem 4.13; §4.3; Appendix G.7–G.8 |
| Residual oracle data structure | PRW Lemma 4.5; Appendix G.1 |
| Approximate maximum spanning forest | PRW Algorithm 4.4, Lemmas 4.10–4.11, Corollary 4.12 |
| Scale schedule and work bound | PRW Algorithm 4.5, Lemma G.40, Corollary G.41, Lemmas G.42–G.48 |
| Negative-dependence concentration | PRW Theorem G.9; its draw-copy application here is the counted variant above |
| Strength structure and sum | BK 2015 §4, especially Lemma 4.11 |
| Smoothness and recompression | BK 2015 Theorem 5.2, Lemma 5.3, Theorem 6.2 |

PRW is cited from
[arXiv:2211.04506v3](https://arxiv.org/pdf/2211.04506v3), retrieved 2026-09-28.
The corresponding [ICALP record](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.115)
identifies the conference publication; theorem numbering here follows the
full arXiv version.
