# Paper 4 in Lean: the headline theorems

**Paper:** [*Subquadratic Cut-Query Algorithms for Directed Minimum Cuts*](subquadratic-directed-minimum-cuts.pdf) (PDF in this folder).

This page shows the Lean statements of the paper's two headline theorems and explains how to
read them. You do not need to read any Lean proofs. Lean's kernel checks those, so what matters
is whether the *statements* say what the paper says. With the reading guide below, you can
compare each statement with the paper in a few minutes. At the end we explain how to confirm
that the proofs are complete.

Each headline theorem has two parts, stated by one or two Lean theorems each:

| Paper | Lean theorem (namespace `CutQueryComplexity`) |
| --- | --- |
| Theorem 1.1: deterministic minimum s–t cut | [`DirectedUnitST.Endpoint.exists_unitST_query_program`](#theorem-11-deterministic-terminal-cut) |
| Theorem 1.1: the integral representation | [`DirectedUnitST.Endpoint.exists_unitST_representation`](#theorem-11-the-integral-representation) |
| Theorem 1.2: randomized minimum s–t cut | [`ImplicitLP.PathFollowing.directed_terminal_query_theorem`](#theorem-12-randomized-terminal-cut), [`ImplicitLP.PathFollowing.calibratedTerminalSolver_valid`](#theorem-12-randomized-terminal-cut) |
| Theorem 1.2: randomized global minimum cut | [`ImplicitLP.PathFollowing.directed_global_query_theorem`](#theorem-12-randomized-global-cut), [`ImplicitLP.PathFollowing.balancedGlobalMinCut_valid`](#theorem-12-randomized-global-cut) |

Source links on this page point into this repository, at the version you are browsing. Each
Lean block is copied exactly from the linked file; proofs are omitted.

## How to read the statements

### Graphs and cuts

| Paper | Lean | Meaning |
| --- | --- | --- |
| vertex set `[n]` | `Fin n` | `{0, …, n−1}` |
| simple digraph `G` | `G : DiGraph (Fin n)` with `G.Simple` | `G.c u v ∈ {0, 1}` arcs from `u` to `v` |
| `F(S)` | `G.out S` | the number of arcs leaving `S` |
| `s`–`t` shore `S` | `s ∈ S ∧ t ∉ S` | |
| global shore `S` | `S.Nonempty ∧ S ≠ univ` | a nonempty proper subset |
| `λ_st`, `λ` | `DirectedMincut.stMin G s t`, `DirectedMincut.globalMin G` | the least `F(S)` over `s`–`t` shores, over global shores |
| `⌈log₂ n⌉` | `Nat.clog 2 n` | the ceiling of a base-2 logarithm |
| `log₂ x` | `Real.logb 2 x` | the real base-2 logarithm |
| `n^{5/3}` | `(n : ℝ) ^ (5 / 3 : ℝ)` | a real power; `5 / 3` is real division |
| `⌈x⌉`, `⌊x⌋` | `⌈x⌉₊`, `⌊x⌋₊` | ceiling and floor, as natural numbers |

These are the definitions, from
[Graph/Directed.lean](../../CutQueryComplexity/Graph/Directed.lean#L25):

```lean
@[ext] structure DiGraph (V : Type*) where
  c : V → V → ℕ
  diag : ∀ v, c v v = 0
```

```lean
def Simple : Prop := ∀ u v, G.c u v ≤ 1
```

```lean
def arcs (A B : Finset V) : ℕ := ∑ u ∈ A, ∑ v ∈ B, G.c u v
```

```lean
def out (S : Finset V) : ℕ := G.arcs S Sᶜ
```

`G.c u v` is the number of arcs from `u` to `v`. There are no loops, and `Simple` allows at most
one arc in each direction, so two vertices are joined by zero, one or two arcs, as in the paper.
Nothing requires `G` to be symmetric, connected, acyclic or Eulerian, or its minimum cut to be
positive. `G.out S` is the paper's `F(S)`, a natural number. `Sᶜ` is the complement of `S`, and
`univ` is the whole vertex set.

### Deterministic algorithms are query trees

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
the answer. Here `I = Finset (Fin n)` (a vertex set) and `A = ℕ` (the number of arcs leaving
it). `DTree.query i next` asks `i` and continues with `next answer`, and `DTree.pure o` returns
`o`. For example, this program asks for `F({0})`, then `F({0, 1})`, and returns the sum:

```lean
example : DTree (Finset (Fin 3)) ℕ ℕ 2 :=
  DTree.query {0} fun a => DTree.query {0, 1} fun b => DTree.pure (a + b)
```

(This example, and the randomized one below, are checked in
[VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).)

`T.eval read` is the output of `T` when each query `S` is answered by `read S`, and
`T.cost read` is the number of queries it asks. In the theorems `read` is the oracle `G.out`, so
`T.eval G.out` is "run the algorithm on `G`".

### Randomized algorithms are random query trees

A randomized algorithm is an `RTree`, a query tree whose steps are drawn at random
([Model/Randomized.lean](../../CutQueryComplexity/Model/Randomized.lean#L14)):

```lean
def RTree (I A O : Type) : ℕ → Type
  | 0 => PMF O
  | q + 1 => PMF (O ⊕ (I × (A → RTree I A O q)))
```

`PMF X` is Mathlib's type of
[probability distributions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Basic.html#PMF)
on `X`: functions from `X` to `[0, ∞]` that sum to `1`. So at each step an `RTree` draws its next
action at random: stop with an output, or ask a query and continue along a branch chosen by the
answer. Each branch is again an `RTree`, so later random choices may depend on everything seen so
far. Random choices are free; only queries are counted. The library's `RTree.mix p` draws a
program from the distribution `p` and runs it, `RTree.query` is as for `DTree`, and
`RTree.pure p` draws the output from `p`. For example, this program picks a vertex `v` uniformly
at random, asks for `F({v})`, and returns the answer:

```lean
example : RTree (Finset (Fin 3)) ℕ ℕ 1 :=
  RTree.mix ((PMF.uniformOfFintype (Fin 3)).map fun v =>
    RTree.query {v} fun a => RTree.pure (PMF.pure a))
```

`RTree.run read T` is the joint distribution of the output and the number of queries asked; each
query adds one to the count
([Model/Randomized.lean](../../CutQueryComplexity/Model/Randomized.lean#L25)):

```lean
def run (read : I → A) : {q : ℕ} → RTree I A O q → PMF (O × ℕ)
  | 0, T => T.map (fun o => (o, 0))
  | _ + 1, T => T.bind fun action => match action with
    | Sum.inl o => PMF.pure (o, 0)
    | Sum.inr (i, next) => (run read (next (read i))).map (fun p => (p.1, p.2 + 1))
```

`T.eval read` is the distribution of the output alone, and `T.successProb read Good` is the
probability that the output satisfies `Good`
([Model/Randomized.lean](../../CutQueryComplexity/Model/Randomized.lean#L65)):

```lean
def successProb (T : RTree I A O q) (read : I → A) (Good : O → Prop) : ℝ :=
  ((run read T).toOuterMeasure {p | Good p.1}).toReal
```

Here `toOuterMeasure E` adds up the probabilities of the outcomes in `E`, and `toReal` makes the
result a real number. The *support* of a distribution is the set of outcomes with positive
probability. The randomized theorems use these definitions as follows.

- **Failure probability.** For a fixed graph `G` the oracle `G.out` is fixed, so all the
  randomness is the program's own. The theorems state `1 − ζ ≤ T.successProb G.out Good` for
  every simple `G`: on each graph separately, the program fails with probability at most `ζ`.
- **The query cap holds on every execution.** The cap is stated for every answer function `read`
  and every pair `out = (output, count)` in the support of `RTree.run read T`. The support
  contains every execution that can happen, including those with a wrong output. So the cap is a
  worst-case bound, not a bound on the expected number of queries or on successful runs only.
- **"With high probability".** The failure probability `ζ` is an input to the program and to the
  theorem, and any `0 < ζ ≤ 1` is allowed. The cap grows with `log₂(2n/ζ)`. The paper's "with
  probability at least `1 − n^{−c}` for any fixed `c > 0`" is the case `ζ = n^{−c}`, worked out
  [below](#theorem-12-randomized-terminal-cut).

### The shape of a theorem

The two statements of Theorem 1.1 have this form (the representation theorem adds one clause):

```text
∀ n, 2 ≤ n → [public inputs] →
  ∃ T : DTree (Finset (Fin n)) ℕ (Option Out) budget,
    (∀ read, T.cost read ≤ bound(n)) ∧
    ∀ G : DiGraph (Fin n), G.Simple →
      ∃ out, T.eval G.out = some out ∧ [out is correct for G]
```

The two main statements of Theorem 1.2 have this form, for a named program `P` built from `n`,
the public inputs and `ζ`:

```text
∀ n, 2 ≤ n → [public inputs] → ∀ ζ, 0 < ζ → ζ ≤ 1 →
  (∀ read, ∀ out ∈ (RTree.run read P).support, out.2 ≤ bound(n, ζ)) ∧
  ∀ G : DiGraph (Fin n), G.Simple → 1 − ζ ≤ P.successProb G.out (Good G)
```

Check these points when reading one:

1. **Constants are explicit.** Each bound is a formula with explicit numbers, not an `O(·)`. To
   compare it with the paper, simplify the formula.
2. **The program is chosen before the graph.** In Theorem 1.1, `∃ T` comes before `∀ G`. In
   Theorem 1.2, the program is a definition whose arguments are `n`, `ζ` and, for an `s`–`t`
   cut, the terminals; `G` is not among them. Either way it is one algorithm that works for
   every graph, not a graph-specific witness.
3. **The program sees `G` only through `G.out`.** No arc is ever handed to it directly.
4. **The cap bounds every run.** It holds for every answer function `read`, even ones that no
   graph produces, and for every execution of a randomized program. The type already bounds
   every run by its index (`DTree.cost_le`, `RTree.cost_le`); the theorems state a sharper bound.
5. **Success is part of the claim.** A deterministic program returns an `Option`, and the theorem
   promises `some out` on every simple graph. A randomized program always returns a candidate,
   and the theorem bounds the probability that it is correct.
6. **Correctness is spelled out**, inline or by a predicate whose definition is shown with the
   theorem.

As in the paper, only queries are counted. Computation between queries is free and uses exact
arithmetic, so these are query-complexity theorems, not running-time theorems.

## Theorem 1.1: deterministic terminal cut

**Paper.** For a simple digraph on `n ≥ 2` vertices, accessed only through `F`, and distinct
terminals `s`, `t`, a deterministic algorithm finds a minimum `s`–`t` shore and its exact
outgoing-cut value using `O(n^{5/3} log²(2n))` queries.

The bound uses two definitions
([DirectedUnitST/Endpoint/Budget.lean](../../CutQueryComplexity/DirectedUnitST/Endpoint/Budget.lean#L26)):

```lean
def logScale (n : ℕ) : ℕ := Nat.clog 2 n + 4
```

```lean
def headlineQueries (n : ℕ) : ℕ :=
  ⌈2048 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2⌉₊
```

The theorem,
[DirectedUnitST/Endpoint/Main.lean](../../CutQueryComplexity/DirectedUnitST/Endpoint/Main.lean#L225):

```lean
theorem exists_unitST_query_program {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t) :
    ∃ T : DTree (Finset (Fin n)) ℕ (Option (Finset (Fin n) × ℕ)) (headlineQueries n),
      (∀ read : Finset (Fin n) → ℕ, T.cost read ≤ headlineQueries n ∧
        (T.cost read : ℝ) ≤ 2049 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2) ∧
      ∀ G : DiGraph (Fin n), G.Simple →
        ∃ S : Finset (Fin n), T.eval G.out = some (S, G.out S) ∧
          s ∈ S ∧ t ∉ S ∧ ∀ W : Finset (Fin n), s ∈ W → t ∉ W → G.out S ≤ G.out W
```

**Reading it.**
- For each `n ≥ 2` and distinct `s`, `t` there is one program `T`, chosen before `G`.
- On every answer function, `T` asks at most `2049 n^{5/3} (⌈log₂ n⌉ + 4)²` queries. For `n ≥ 2`,
  `⌈log₂ n⌉ + 4 ≤ 3 log₂(2n)`, so this is the paper's `O(n^{5/3} log²(2n))`.
- On every simple `G`, `T` succeeds and returns `(S, G.out S)`: a shore with `s ∈ S` and `t ∉ S`,
  and its exact value. No `s`–`t` shore `W` has a smaller value, so `S` is a minimum `s`–`t` cut.
  Optimality is written out against every shore, with no auxiliary definition.
- There is no promise about `G` beyond `G.Simple`; in particular the minimum cut may be `0`.

The statement differs from the paper only in having explicit constants.

## Theorem 1.1: the integral representation

**Paper.** Within the same bound, and before choosing the terminal flow, the algorithm
constructs an implicit integral directed representation with the same outgoing-cut function as
`G`. Every unknown pair is pure in a public direction; every other pair has explicitly known
capacities.

A pair is *pure* if all its capacity is in one direction, and *public* means computable from the
answers and the stored data without another query. The representation has real capacities
([Graph/WeightedDirected.lean](../../CutQueryComplexity/Graph/WeightedDirected.lean#L15)):

```lean
structure WeightedDiGraph (V : Type*) where
  c : V → V → ℝ
  nonneg : ∀ u v, 0 ≤ c u v
  diag : ∀ v, c v v = 0
```

```lean
def out (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, G.c u v
```

In the theorem, the input appears as
[`Preparation.realGraph G`](../../CutQueryComplexity/DirectedUnitST/Preparation/Basic.lean#L20),
the same graph with its arc counts read as real numbers. The total capacity of a pair is
`G.sym.w u v`
([DirectedCertificate/Basic.lean](../../CutQueryComplexity/DirectedCertificate/Basic.lean#L223)):

```lean
def sym : WeightedGraph V where
  w v w := G.c v w + G.c w v
  symm u v := add_comm _ _
  nonneg u v := add_nonneg (G.nonneg u v) (G.nonneg v u)
  diag v := by simp [G.diag]
```

The program's stored data is a `State`, and `Realizes` says how a state describes a graph
([DirectedUnitST/Blocking/State.lean](../../CutQueryComplexity/DirectedUnitST/Blocking/State.lean#L30)):

```lean
structure State (V : Type) where
  singletonValue : V → ℝ
  outward : V → Finset V
  known : Finset (V × V)
  knownResidual : V → V → ℝ
```

```lean
structure Realizes (G H : WeightedDiGraph V) (st : State V) : Prop where
  singleton : ∀ v, st.singletonValue v = G.out {v}
  known_symm : ∀ u v, (u, v) ∈ st.known ↔ (v, u) ∈ st.known
  direction : ∀ u v, u ≠ v → (v ∈ st.outward u ↔ u ∉ st.outward v)
  learned : ∀ u v, (u, v) ∈ st.known → H.c u v = st.knownResidual u v
  unknown : ∀ u v, (u, v) ∉ st.known →
    H.c u v = if v ∈ st.outward u then G.sym.w u v else 0
```

In `st.Realizes G H`, `G` is the input and `H` the represented graph. The stored value of each
vertex `v` is `F({v})`. The known pairs are closed under swapping, and for each pair `u ≠ v` the
table `outward` names exactly one direction (`v ∈ st.outward u` means "from `u` to `v`"). On a
known pair, `H` has the stored capacity. On an unknown pair, `H` puts the whole pair total of `G`
in the stored direction and `0` in the other: the pair is pure in a public direction. The total
itself is not stored, which is why the representation is implicit.

The theorem,
[DirectedUnitST/Endpoint/Representation.lean](../../CutQueryComplexity/DirectedUnitST/Endpoint/Representation.lean#L126):

```lean
theorem exists_unitST_representation {n : ℕ} (hn : 2 ≤ n) :
    ∃ P : DTree (Finset (Fin n)) ℕ (Option (Blocking.SolveResult (Fin n)))
        (representationBudget n),
      (∀ read : Finset (Fin n) → ℕ, P.cost read ≤ headlineQueries n ∧
        (P.cost read : ℝ) ≤ 2049 * (n : ℝ) ^ (5 / 3 : ℝ) * (logScale n : ℝ) ^ 2) ∧
      (∀ G : DiGraph (Fin n), G.Simple →
        ∃ result, P.eval G.out = some result ∧
          ∃ K : WeightedDiGraph (Fin n),
            result.network.internal.Realizes (Preparation.realGraph G) K ∧
            (∀ u v, ∃ m : ℕ, K.c u v = m) ∧
            ∀ S : Finset (Fin n), K.out S = (G.out S : ℝ)) ∧
      ∀ (s t : Fin n) (read : Finset (Fin n) → ℕ),
        (unitSTNatTree n s t).eval read =
          ((terminalAfterRepair n s t (P.eval read)).eval read).map
            fun result => (result.shore, ⌊result.value⌋₊)
```

**Reading it.**
- `P` depends only on `n`: it comes before both the graph and the terminals. Its cost obeys the
  bound of Theorem 1.1. (The budget `representationBudget n` in its type is a number fixed by
  `n`; since the cost is bounded directly, its formula does not matter. It is in the
  [appendix](#appendix-program-plumbing).)
- On every simple `G`, `P` succeeds. Its output contains the state `result.network.internal`.
- That state describes a weighted digraph `K` with natural-number capacities and the same
  outgoing-cut function as `G`. `K` is a mathematical object, not an output; the program knows it
  only through the state. Everything in the state is a function of the answers, so it is public.
- The last clause links `P` to the terminal algorithm. `unitSTNatTree n s t` is the program `T`
  that the proof of [Theorem 1.1](#theorem-11-deterministic-terminal-cut) supplies (its
  guarantees are also stated directly as
  [`unitSTNatTree_correct`](../../CutQueryComplexity/DirectedUnitST/Endpoint/Main.lean#L214)).
  On every answer function, it returns what one gets by running `P` and then the terminal stage
  `terminalAfterRepair n s t` on `P`'s output. So the terminal algorithm uses this
  representation, built before the terminals are chosen.
- Equal cut functions force equal pair totals, `K.c u v + K.c v u = G.c u v + G.c v u`, since
  `c(u,v) + c(v,u) = F({u}) + F({v}) − F({u,v})` for `u ≠ v`. This is
  `pair_totals_of_cut_equivalence` in [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).
  So `K` may have capacity `2` in one direction where `G` has two antiparallel arcs, as the paper
  says. `K` need not equal `G`: no cut query can tell `G` from `G` with a directed cycle
  reversed.

**One difference from the paper.** The paper describes one algorithm that builds the
representation and then solves the terminal problem. Lean states the representation for a
separate program `P`, the part that does not depend on the terminals, and connects it to the
terminal program by the equation in the last clause. That equation is about outputs; the cost of
`P` is bounded on its own, by the bound of Theorem 1.1.

## Theorem 1.2: randomized terminal cut

**Paper.** In the same model, a randomized algorithm finds an exact minimum `s`–`t` cut in
`Õ(n^{3/2})` queries, with probability at least `1 − n^{−c}` for any fixed `c > 0`. Its query
cap holds on failing executions as well. Every returned candidate is a legal original shore with
its value checked by an outgoing-cut query.

Here `Õ` hides factors polylogarithmic in `n` and in the inverse failure probability. A
candidate `r` is a shore `r.1` with a claimed value `r.2`. Success is `STGood`
([DirectedMincut/FlowDuality.lean](../../CutQueryComplexity/DirectedMincut/FlowDuality.lean#L27),
[DirectedMincut/Extraction.lean](../../CutQueryComplexity/DirectedMincut/Extraction.lean#L250)):

```lean
noncomputable def stMin (G : DiGraph V) (s t : V) : ℕ :=
  sInf {k | ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ G.out S = k}
```

```lean
def STGood (s t : V) (G : DiGraph V) (r : Finset V × ℕ) : Prop :=
  s ∈ r.1 ∧ t ∉ r.1 ∧ G.out r.1 = stMin G s t ∧ r.2 = G.out r.1
```

`sInf` of a nonempty set of natural numbers is its least element, so `stMin G s t = λ_st`.
Without `stMin`, `STGood s t G r` says that `s ∈ r.1`, `t ∉ r.1`, and `r.2 = F(r.1) ≤ F(S)` for
every `s`–`t` shore `S`; this equivalence is `stGood_iff_inequalities` in
[VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean). The cap uses `log₂(2n/ζ)`
([ImplicitLP/PathFollowing/PrimitiveBudget.lean](../../CutQueryComplexity/ImplicitLP/PathFollowing/PrimitiveBudget.lean#L20)):

```lean
def queryHeight (n : ℕ) : ℝ := 2 * n
```

```lean
def failureLog (n : ℕ) (ζ : ℝ) : ℝ := Real.logb 2 (queryHeight n / ζ)
```

The program is a definition whose arguments are `n`, `s`, `t` and `ζ`
([ImplicitLP/PathFollowing/Calibration.lean](../../CutQueryComplexity/ImplicitLP/PathFollowing/Calibration.lean#L241)):

```lean
def calibratedTerminalSolver (n : ℕ) (s t : Fin n) (ζ : ℝ) :=
  publicTerminalSolver (calibratedParams n s t ζ) (Sparsify.pK n) (publicExtractionScale n)
```

`calibratedParams n s t ζ` is a table of numerical parameters (step counts, accuracies, sample
sizes) computed from its arguments, and `publicTerminalSolver` runs the LP solver and then
extracts a shore ([appendix](#appendix-program-plumbing)). The program's type is
`RTree (Finset (Fin n)) ℕ (Finset (Fin n) × ℕ) Q` for an explicit, very large `Q`, which does not
matter since the theorem bounds the queries directly.

The theorem,
[ImplicitLP/PathFollowing/QueryEndpoint.lean](../../CutQueryComplexity/ImplicitLP/PathFollowing/QueryEndpoint.lean#L197):

```lean
theorem directed_terminal_query_theorem {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
      out ∈ (RTree.run read (calibratedTerminalSolver n s t ζ)).support →
      (out.2 : ℝ) ≤ 2 ^ 310 * (n : ℝ) ^ (3 / 2 : ℝ) * failureLog n ζ ^ 21) ∧
    (∀ G : DiGraph (Fin n), G.Simple →
      1 - ζ ≤ (calibratedTerminalSolver n s t ζ).successProb G.out (DirectedMincut.STGood s t G))
```

and every candidate is legal,
[ImplicitLP/PathFollowing/GlobalValidity.lean](../../CutQueryComplexity/ImplicitLP/PathFollowing/GlobalValidity.lean#L63):

```lean
theorem calibratedTerminalSolver_valid {n : ℕ} (hn : 2 ≤ n) (s t : Fin n) (hst : s ≠ t)
    (ζ : ℝ) (G : DiGraph (Fin n)) {out : Finset (Fin n) × ℕ}
    (ho : out ∈ ((calibratedTerminalSolver n s t ζ).eval G.out).support) :
    s ∈ out.1 ∧ t ∉ out.1 ∧ out.2 = G.out out.1
```

**Reading it.**
- The first conjunct is the cap: on every answer function and every execution, failing ones
  included, the program asks at most `2^310 n^{3/2} log₂(2n/ζ)^21` queries. In `out`, `out.1` is
  the candidate and `out.2` the number of queries.
- The second conjunct: on every simple `G`, with probability at least `1 − ζ` the program
  returns a minimum `s`–`t` shore with its true value.
- The validity theorem is about the same program. Every candidate it can return on `G` is an
  `s`–`t` shore with its true value, whether or not the run succeeded. It holds for every `ζ`
  and every directed graph, simple or not.
- **With high probability.** Fix `c > 0` and take `ζ = n^{−c}`. This is allowed, since
  `0 < n^{−c} ≤ 1` for `n ≥ 2`, and then `log₂(2n/ζ) = 1 + (1 + c) log₂ n`. So the cap is
  `2^310 n^{3/2} (1 + (1 + c) log₂ n)^21`, which is `Õ(n^{3/2})` for fixed `c`, and the success
  probability is at least `1 − n^{−c}`. This form is `terminal_with_high_probability` in
  [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).

**Differences from the paper.**
- The factor `log₂(2n/ζ)^21` and the constant `2^310` are deliberately loose. They give the
  paper's `Õ(n^{3/2})`, but they do not reproduce the sharper polylogarithmic accounting in the
  paper's proofs.
- The paper says each value is *checked by an outgoing-cut query*. The Lean theorem says that
  the reported value equals `F(S)`. That it comes from a query is a property of the program, not
  of the theorem: the program ends with `DirectedMincut.extract`, whose last step queries the
  returned shore and reports the answer ([appendix](#appendix-program-plumbing)).

**Earlier work.** The randomized algorithm builds on an implicit LP method from an earlier
anonymous note, which relies on facts from Lee and Sidford. The paper replaces the note's
numerical analysis with its own (Section 15), for reasons given in
[LPAudit26](supporting/implicit-lp-audit.pdf) and
[LSAudit26](../../docs/lee-sidford-audit/AUDIT.md). The Lean proof follows the paper's
argument but takes no result of the note or of Lee and Sidford on trust: everything it uses is
proved in Lean, so the theorems have no hypotheses beyond those shown, and the proofs use only
Lean's standard axioms.

## Theorem 1.2: randomized global cut

**Paper.** In the same model, a randomized algorithm finds an exact global minimum cut in
`Õ(n^{7/4})` queries, with probability at least `1 − n^{−c}` for any fixed `c > 0`. Its query
cap holds on failing executions as well. Every returned candidate is a legal original shore with
its value checked by an outgoing-cut query.

The definitions,
[DirectedMincut/GlobalReduction.lean](../../CutQueryComplexity/DirectedMincut/GlobalReduction.lean#L40):

```lean
def globalMin (G : DiGraph V) : ℕ := sInf {k | ∃ S : Finset V, S.Nonempty ∧ S ≠ univ ∧ G.out S = k}
```

```lean
def Valid (G : DiGraph V) (r : Finset V × ℕ) : Prop :=
  r.1.Nonempty ∧ r.1 ≠ univ ∧ r.2 = G.out r.1
```

```lean
def Opt (G : DiGraph V) (r : Finset V × ℕ) : Prop := Valid G r ∧ G.out r.1 = globalMin G
```

`Valid` says that the candidate is a nonempty proper shore with its true value, and `Opt` adds
that the value is `λ`. Without `globalMin`, `Opt G r` says that `r.1` is nonempty and proper and
`r.2 = F(r.1) ≤ F(S)` for every nonempty proper `S` (`opt_iff_inequalities` in
[VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean)). The program takes `n`, a proof `hn`
that `2 ≤ n` (a proof carries no data), and `ζ`
([ImplicitLP/PathFollowing/QueryBound.lean](../../CutQueryComplexity/ImplicitLP/PathFollowing/QueryBound.lean#L539)):

```lean
def publicShoreSize (n : ℕ) : ℕ := min (n - 1) ⌈(n : ℝ) ^ (3 / 4 : ℝ)⌉₊
```

```lean
def balancedGlobalMinCut (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) :=
  calibratedGlobalMinCut n hn ζ (publicShoreSize n)
```

As in the paper's Theorem 10.4, it handles cuts with a shore of at most
`h = min(n − 1, ⌈n^{3/4}⌉)` vertices directly, then runs the terminal program on randomly
sampled terminal pairs and keeps the best candidate ([appendix](#appendix-program-plumbing)).

The theorem,
[ImplicitLP/PathFollowing/QueryEndpoint.lean](../../CutQueryComplexity/ImplicitLP/PathFollowing/QueryEndpoint.lean#L208):

```lean
theorem directed_global_query_theorem {n : ℕ} (hn : 2 ≤ n)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (∀ (read : Finset (Fin n) → ℕ) (out : (Finset (Fin n) × ℕ) × ℕ),
      out ∈ (RTree.run read (balancedGlobalMinCut n hn ζ)).support →
      (out.2 : ℝ) ≤ 2 ^ 340 * (n : ℝ) ^ (7 / 4 : ℝ) * failureLog n ζ ^ 22) ∧
    (∀ G : DiGraph (Fin n), G.Simple →
      1 - ζ ≤ (balancedGlobalMinCut n hn ζ).successProb G.out (DirectedMincut.Opt G))
```

and every candidate is legal,
[ImplicitLP/PathFollowing/GlobalValidity.lean](../../CutQueryComplexity/ImplicitLP/PathFollowing/GlobalValidity.lean#L86):

```lean
theorem balancedGlobalMinCut_valid {n : ℕ} (hn : 2 ≤ n) (ζ : ℝ) (G : DiGraph (Fin n))
    (hG : G.Simple) {out : Finset (Fin n) × ℕ}
    (ho : out ∈ ((balancedGlobalMinCut n hn ζ).eval G.out).support) :
    DirectedMincut.Valid G out
```

**Reading it.**
- The cap `2^340 n^{7/4} log₂(2n/ζ)^22` holds on every answer function and every execution.
- On every simple `G`, with probability at least `1 − ζ` the program returns a global minimum
  cut with its true value.
- On every simple `G`, every candidate the program can return is a nonempty proper shore with
  its true value, for every `ζ`. Unlike the terminal version, this assumes `G.Simple`.
- **With high probability.** As before, `ζ = n^{−c}` gives the cap
  `2^340 n^{7/4} (1 + (1 + c) log₂ n)^22`, which is `Õ(n^{7/4})`, and success probability at
  least `1 − n^{−c}` (`global_with_high_probability` in
  [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean)).

**Differences from the paper.** The same two as for the terminal cut. The factor
`log₂(2n/ζ)^22` and the constant `2^340` are loose. The query behind each value is a property
of the program, not of the theorem: terminal candidates come from `DirectedMincut.extract`, and
the small-shore candidate from `DirectedMincut.finish`, which also queries its shore.

## What is not formalized

The two headline theorems are formalized in full. The paper's Lean appendix (Appendix A) maps
every numbered result to Lean declarations. Three clauses of intermediate results are not
stated in Lean:

- **Corollary 6.2:** only the "if" direction is a single statement. The converse follows from
  the stated formulas for `c_uv`, `F({v})` and `F(V∖{v})`.
- **Corollary 14.7** is proved as two generic matrix inequalities, for any positive semidefinite
  matrix. They are not instantiated at the sparsifier output, and the positive-definiteness
  clause is not stated.
- **Theorem 15.1:** strict interiority of the iterates and the batch count are internal
  invariants of the proof, not exported statements. The fixed-precision claim is formalized only
  for the dyadic quantities on the query side, since offline arithmetic is exact.

The paper's appendix also lists smaller differences of form in other intermediate results. One
concerns the route to Theorem 1.2: the paper derives the terminal bound (Corollary 10.3) from its
general implicit LP theorem (Theorem 10.2), while the Lean proof applies the LP solver to the
terminal LP directly.

## Check it yourself

You do not need to trust this page. [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean)
restates each Lean theorem above word for word, as `check_…`, and proves it by citing the
library. If the file compiles, the library proves exactly these statements. The file also runs
two checks on each theorem:

- `#print axioms` lists the axioms the proof depends on. It should show only `propext`,
  `Classical.choice` and `Quot.sound`, Lean's three standard axioms. In particular, no
  `sorryAx` (an unfinished proof) and no extra assumption.
- `#audit_cut_decl` applies the library's own audit of the same kind. It prints nothing when the
  check passes.

Its last section proves the small facts cited on this page.

Lean's kernel checked every proof when `lake build` compiled the library. `#print axioms`
follows every dependency of a theorem down to the axioms, so an unfinished proof anywhere
beneath a headline theorem would show up there as `sorryAx`. To run the checks, install Lean's
toolchain manager [`elan`](https://github.com/leanprover/elan), then:

```sh
git clone https://github.com/troyjlee/cut-query-complexity.git
cd cut-query-complexity
lake exe cache get        # download prebuilt Mathlib
lake build CutQueryComplexity.DirectedUnitST.Endpoint.Representation \
  CutQueryComplexity.ImplicitLP.PathFollowing.GlobalValidity \
  CutQueryComplexityChecks.AxiomAudit
lake env lean --trust=0 papers/P4/VerifyHeadlineTheorems.lean
```

The last command should finish with no errors.

## Appendix: program plumbing

This appendix shows how the programs in the theorems are assembled. You do not need it to read
the statements, since the theorems bound the cost and describe the output of these programs
directly. For both kinds of tree, `bind` runs a second program on the output of the first, and
`map` changes the output without asking queries.

### The deterministic program

The representation program `P` of Theorem 1.1 is preparation followed by discrepancy repair, and
its type-level budget is the sum of theirs
([DirectedUnitST/Endpoint/Representation.lean](../../CutQueryComplexity/DirectedUnitST/Endpoint/Representation.lean#L21)):

```lean
def representationBudget (n : ℕ) : ℕ :=
  Preparation.queryBudget n (Preparation.cubicScale n) +
    Blocking.repairBudget (Fin n) (supplyCap n)
```

```lean
def representationTree (n : ℕ) :
    DTree (Finset (Fin n)) ℕ (Option (Blocking.SolveResult (Fin n))) (representationBudget n) :=
  (Preparation.fiveThirdsIntegralProg n).bind fun out =>
    Blocking.cappedDiscrepancyRepairTreeNat out.state
      (Blocking.integerDemand out.demand) (supplyCap n)
```

The terminal program `unitSTNatTree n s t` runs the same two stages, then the terminal stage on
the returned state
([DirectedUnitST/Endpoint/Main.lean](../../CutQueryComplexity/DirectedUnitST/Endpoint/Main.lean#L47)):

```lean
def terminalAfterRepair (n : ℕ) (s t : Fin n) :
    Option (Blocking.SolveResult (Fin n)) →
      DTree (Finset (Fin n)) ℕ (Option (Blocking.TerminalResult (Fin n)))
        (terminalStageBudget n)
  | none => DTree.pure none
  | some result => Blocking.terminalTreeNat result.network.internal s t
```

```lean
def unitSTNatTree (n : ℕ) (s t : Fin n) :
    DTree (Finset (Fin n)) ℕ (Option (Finset (Fin n) × ℕ)) (headlineQueries n) :=
  (unitSTTree n s t).map (Option.map fun result => (result.shore, ⌊result.value⌋₊))
```

Here `unitSTTree` composes the three stages with `bind` and cuts the result off at
`headlineQueries n`; the library proves that the cut-off never happens, for any answer function.
The terminal stage `Blocking.terminalTreeNat` ends by querying the returned shore, and the final
`map` converts the answer, stored as a real number, to `ℕ`. The output of the repair,
[`Blocking.SolveResult`](../../CutQueryComplexity/DirectedUnitST/Blocking/Run.lean#L117), records
the repair flow, its value and its phases. Its field `network` is a
[`NetworkState`](../../CutQueryComplexity/DirectedUnitST/Blocking/State.lean#L205), which holds
the `State` of the represented graph (`internal`) and the capacities of two auxiliary terminals
used by the repair.

### The randomized programs

The terminal program runs the LP solver `terminalLP` and then `extract` on its output, or on the
fallback point `zeroPt` if the solver aborts
([ImplicitLP/PathFollowing/Main.lean](../../CutQueryComplexity/ImplicitLP/PathFollowing/Main.lean#L1181)).
`publicTerminalSolver` fixes the step schedules and counts from the parameter table.

```lean
def terminalSolver (P : Params E) (τ σ : ℕ → ℝ) (Ndown Nup Nfinal k : ℕ) (θ : ℝ) :
    RTree (Finset (Fin E.n)) ℕ (Finset (Fin E.n) × ℕ)
      ((2 * E.n + P.solverBudget Ndown Nup Nfinal) + (2 * E.n * (3 + 3 * k) + 1)) :=
  (terminalLP P τ σ Ndown Nup Nfinal).bind fun out =>
    (RTree.ofDeterministic (DirectedMincut.extract P.s P.terminal k θ (out.getD zeroPt))).cast
      (by simp)
```

`extract` searches the thresholded LP solution for a shore, falls back to `{s}` if the search
reaches `t`, and then queries the shore and returns it with the answer
([DirectedMincut/Extraction.lean](../../CutQueryComplexity/DirectedMincut/Extraction.lean#L243)):

```lean
def extract (s t : V) (k : ℕ) (τ : ℝ) (p : LPPoint V) :
    DTree (Finset V) ℕ (Finset V × ℕ) (2 * Fintype.card V * (3 + 3 * k) + 1) :=
  (bfs k (okOf p τ) (2 * Fintype.card V) {s} ∅).bind fun W =>
    let S := if t ∈ W then {s} else W
    DTree.query S fun a => DTree.pure (S, a)
```

The global program gives each terminal call failure probability `ζ/2`, and takes
`publicRootCount n h ζ = ⌈(n/h) ln(2/ζ)⌉` samples, so that missing a minimum cut with two large
shores has probability at most `ζ/2`
([ImplicitLP/PathFollowing/Calibration.lean](../../CutQueryComplexity/ImplicitLP/PathFollowing/Calibration.lean#L340)).
`calibratedGlobalSolver` passes the terminal program's parameters to the reduction `global`.

```lean
def calibratedGlobalMinCut (n : ℕ) (hn : 2 ≤ n) (ζ : ℝ) (h : ℕ) :=
  calibratedGlobalSolver n hn (ζ / 2) h (publicRootCount n h ζ)
```

[DirectedMincut/GlobalReduction.lean](../../CutQueryComplexity/DirectedMincut/GlobalReduction.lean#L248):

```lean
def global [Nonempty V] (k h K : ℕ) (a : V) (T : V → V → RTree (Finset V) ℕ (Finset V × ℕ) qst) :
    RTree (Finset V) ℕ (Finset V × ℕ) (2 * Fintype.card V + (learnFuel (V := V) h * (3 + 3 * k) +
      (learnFuel (V := V) h * (3 + 3 * k) + 1)) + 2 * K * qst) :=
  (RTree.ofDeterministic (smallShore k h)).bind fun r0 => samplePhase a K T r0
```

`global` first runs the deterministic small-shore procedure `smallShore`. Then `samplePhase`
draws `K` vertices uniformly at random, runs the terminal program `T` on the pairs `(a, v)` and
`(v, a)` for each sampled `v ≠ a`, and keeps the candidate with the smallest value. The
small-shore procedure ends with `finish`, which queries its shore
([DirectedMincut/SmallShore.lean](../../CutQueryComplexity/DirectedMincut/SmallShore.lean#L382)):

```lean
def finish (c : Finset V × Bool) : DTree (Finset V) ℕ (Finset V × ℕ) 1 :=
  DTree.query (candShore c) fun a => DTree.pure (q := 0) (candShore c, a)
```
