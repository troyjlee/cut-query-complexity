# Paper 2 in Lean: the headline theorems

**Paper:** [*Deterministic s–t and All-Pairs Minimum Cuts with Subquadratic Cut Queries*](deterministic-st-all-pairs-minimum-cuts.pdf) (PDF in this folder).

This page shows the Lean statements of the paper's two headline theorems and explains how to
read them. You do not need to read any Lean proofs. Lean's kernel checks those, so what matters
is whether the *statements* say what the paper says. With the reading guide below, you can
compare each statement with the paper in a few minutes. At the end we explain how to confirm
that the proofs are complete.

| Paper | Lean theorem (namespace `CutQueryComplexity`) |
| --- | --- |
| Theorem 1: exact deterministic terminal cuts | [`CanonicalST.exists_terminal_sqrt_program`](#theorem-1-exact-deterministic-terminal-cuts) |
| Theorem 2: exact deterministic all-pairs cuts | [`DeterministicAPMCExpansion.Pruning.deterministic_allPairs`](#theorem-2-exact-deterministic-all-pairs-cuts) |

Source links on this page point into this repository, at the version you are browsing. Each
Lean block is copied exactly from the linked file; proofs are omitted.

## How to read the statements

### Graphs and cuts

| Paper | Lean | Meaning |
| --- | --- | --- |
| vertex set `V = [n]` | `Fin n`, or a finite type `V` with `Fintype.card V = n` | `Fin n = {0, …, n−1}` |
| simple unweighted graph | `G : WeightedGraph V` with `AllPairsAudit.Unweighted G` | symmetric weights, zero on the diagonal, each weight `0` or `1` |
| cut query on `S`, `c_G(S)` | `G.cut S` | number of edges leaving `S` |
| minimum `s`–`t` cut | `IsSTMinCut G s t S` | `s ∈ S`, `t ∉ S`, and no such shore has a smaller cut |
| `n` as a real number | `(n : ℝ)` | Lean writes conversions between number types explicitly |
| `⌈log₂ 2n⌉` | `Nat.clog 2 (2 * n)` | the ceiling of a base-2 logarithm |
| `√n` | `Real.sqrt n` | the real square root |
| `⌈x⌉` | `⌈x⌉₊` | the least natural number `≥ x` |
| `n^{5/3}` | `(n : ℝ) ^ (5 / 3 : ℝ)` | a real power |
| `ln x` | `Real.log x` | the natural logarithm |

These are the definitions, from
[Graph/Weighted.lean](../../CutQueryComplexity/Graph/Weighted.lean#L18),
[AllPairsAudit/CutAlgebra.lean](../../CutQueryComplexity/AllPairsAudit/CutAlgebra.lean#L23) and
[Problem/Basic.lean](../../CutQueryComplexity/Problem/Basic.lean#L47):

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
def Unweighted (G : WeightedGraph V) : Prop :=
  ∀ u v, G.w u v = 0 ∨ G.w u v = 1
```

```lean
def IsSTMinCut (G : WeightedGraph V) (s t : V) (S : Finset V) : Prop :=
  s ∈ S ∧ t ∉ S ∧ ∀ T, s ∈ T → t ∉ T → G.cut S ≤ G.cut T
```

Here `V` is a finite type of vertices, `Finset V` is a finite set of vertices, and `Sᶜ` is the
complement of `S`. Together, `WeightedGraph` and `Unweighted` say exactly that `G` is a simple,
loopless, undirected graph: symmetry makes it undirected, the zero diagonal rules out loops, and
weights in `{0, 1}` rule out multiple edges. The sum in `cut` runs over pairs `(u, v)` with
`u ∈ S` and `v ∉ S`, so each crossing edge is counted once and `G.cut S` is the paper's
`c_G(S)`. In `IsSTMinCut`, `T` ranges over vertex sets. Nothing requires `G` to be connected or
to have a minimum degree.

Cut values have type `ℝ` in Lean, so that a program can be run on arbitrary answers (see below).
On an unweighted graph every cut value is a natural number. This is `honest_cut_is_natural` in
this folder's [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).

`IsSTMinCut G s t S` puts `s` in the shore. The paper's single-pair proof puts `t` in the shore
instead. A shore and its complement have the same cut, so the two conventions describe the same
cuts; Theorem 1 below says how Lean handles this.

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
the answer. For cut queries, `I = Finset V` (a vertex set) and `A = ℝ` (its cut value).
The library's `DTree.query i next` asks `i` and continues with `next answer`, and `DTree.pure o`
returns `o`. For example, this program asks for the cuts of `{0}`, `{1}` and `{0, 1}` in a graph
on three vertices, and returns `a + b − c`:

```lean
example : DTree (Finset (Fin 3)) ℝ ℝ 3 :=
  DTree.query {0} fun a => DTree.query {1} fun b => DTree.query {0, 1} fun c =>
    DTree.pure (a + b - c)
```

The edges `{0, 2}` and `{1, 2}` each appear once in `a + b` and once in `c`, so the program
returns twice the weight of the edge `{0, 1}`. In an unweighted graph that is `2` if the edge
is present and `0` if not. The paper finds edges by combining cut queries in this way
(Lemma 3). The example, and the fact that it returns `2 * G.w 0 1` (`three_query_example_eval`),
are checked in [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).

Two functions run a program. `D.eval read` returns its output when each query `S` is answered
by `read S`, and `D.cost read` counts the queries it asks. In the theorems, `read` is the cut
oracle `G.cut`, so `D.eval G.cut` is "run the algorithm on `G`".

### The shape of an algorithmic theorem

Both theorems have this form:

```text
∃ D : DTree (Finset V) ℝ Out q,
  (∀ read, D.cost read ≤ q) ∧
  ∀ G : WeightedGraph V, Unweighted G →
    [D.eval G.cut is correct for G]
```

Theorem 1 states this for each vertex type `V` and each pair of terminals, with an explicit
budget `q`. Theorem 2 states it for every `n` at once, with `V = Fin n`, a budget `q n`, and a
separate clause that bounds `q n`.

Check these points when reading one:

1. **The query bound.** Theorem 1's budget is an explicit formula, including the constant.
   Theorem 2 has `∃ C, 0 < C ∧ ∀ n, 2 ≤ n → q n ≤ C · f(n)`: one constant works for every
   `n ≥ 2`, which is the `O(f(n))`. Where the paper writes `log(2n)`, Lean writes
   `Nat.clog 2 (2 * n)` or `Nat.clog 2 (2 * n + 2) + 1`; for `n ≥ 2` these differ from `log(2n)`
   by constant factors.
2. **The program `D` is chosen before the graph `G`.** It depends only on `n` and on any public
   inputs listed before it (in Theorem 1, the terminals `s` and `t`), so it is one algorithm
   that works for every graph. It is not a graph-specific witness.
3. **The program sees `G` only through `G.cut`.** No weight or edge is ever handed to it
   directly.
4. **`∀ read, D.cost read ≤ q` bounds every run.** The budget holds for every sequence of
   answers, even answers that no graph could produce. The paper asks for this explicitly in
   Theorem 2. The type already guarantees it (`DTree.cost_le`); the theorems state it anyway.
5. **Success is part of the claim.** In Theorem 1 the output type is an `Option`, and `some out`
   means the program finished normally; the theorem promises this on every graph. In Theorem 2
   the output type has no failure value, so the program always returns a full table.
6. **The promise is `Unweighted G`.** Nothing else is assumed about the graph.
7. **Correctness is spelled out.** Each theorem names a predicate, `OutputSpec` or
   `allPairsGood`; its definition is shown next to the theorem.

As in the paper, only queries are counted. Computation between queries is free and uses exact
real arithmetic, so these are query-complexity theorems, not running-time theorems. The paper
says the same: its offline computation need not be polynomial.

## Theorem 1: exact deterministic terminal cuts

**Paper.** Let `G` be a simple, loopless, unweighted undirected graph on `n ≥ 2` vertices, with
distinct terminals `s` and `t`. Given cut-query access to `G`, a deterministic algorithm outputs
`ν(G)`, the least cut of a shore containing `t` but not `s`, together with a shore attaining it
and an explicit integral maximum `s`–`t` flow. It uses `O(n^{3/2} log³(2n))` cut queries and
always succeeds.

The output has three fields, and `OutputSpec` says what they must satisfy
([CanonicalST/Main.lean](../../CutQueryComplexity/CanonicalST/Main.lean#L42)):

```lean
structure Output (V : Type) where
  shore : Finset V
  value : ℝ
  flow : V → V → ℝ
```

```lean
def OutputSpec (G : WeightedGraph V) (s t : V) (out : Output V) : Prop :=
  s ∈ out.shore ∧ t ∉ out.shore ∧ out.value = G.cut out.shore ∧
    (∀ S : Finset V, s ∈ S → t ∉ S → G.cut out.shore ≤ G.cut S) ∧
    Augmentation.FlowSpec G s t out.value out.flow
```

The first four clauses say that `out.shore` is a minimum `s`–`t` shore and `out.value` is its
cut. The last clause concerns the flow. `FlowSpec H s t r f` says that `f` is a feasible flow in
`H` from `s` to `t` of value `r`, with integer values
([CanonicalST/Augmentation/MaxFlow.lean](../../CutQueryComplexity/CanonicalST/Augmentation/MaxFlow.lean#L181),
[Certificate/Flow.lean](../../CutQueryComplexity/Certificate/Flow.lean#L24),
[DirectedUnitST/Repair/IntegralRounding.lean](../../CutQueryComplexity/DirectedUnitST/Repair/IntegralRounding.lean#L24)):

```lean
def FlowSpec (H : WeightedGraph V) (s t : V) (r : ℝ) (f : V → V → ℝ) : Prop :=
  Certificate.Feasible H f ∧
    (∀ x, netOut f x = (if x = s then r else 0) - (if x = t then r else 0)) ∧
    ∀ u v, IntegerValue (f u v)
```

```lean
def IsFlow (f : V → V → ℝ) : Prop := ∀ u v, f v u = -f u v
```

```lean
def Feasible (G : WeightedGraph V) (f : V → V → ℝ) : Prop :=
  IsFlow f ∧ ∀ u v, |f u v| ≤ G.w u v
```

```lean
def netOut (f : V → V → ℝ) (v : V) : ℝ := ∑ u, f v u
```

```lean
def IntegerValue (x : ℝ) : Prop := ∃ z : ℤ, x = z
```

As in the paper, a flow is a function `f u v` on ordered pairs with `f v u = −f u v`. In an
unweighted graph, the capacity bound `|f u v| ≤ G.w u v` makes `f` zero on nonedges and at most
`1` in absolute value on edges. `netOut f x` is the divergence at `x`, and `FlowSpec` asks for
it to be `r` at `s`, `−r` at `t` and `0` elsewhere. `IntegerValue` asks for every value of `f`
to be an integer.

The budget uses `logFactor n = ⌈log₂ 2n⌉`
([CanonicalST/Budget.lean](../../CutQueryComplexity/CanonicalST/Budget.lean#L21)):

```lean
def logFactor (n : ℕ) : ℕ := Nat.clog 2 (2 * n)
```

```lean
def headlineBudget (n : ℕ) : ℕ :=
  ⌈2^23 * (n : ℝ) * Real.sqrt (n : ℝ) * (logFactor n : ℝ)^3⌉₊
```

The theorem,
[CanonicalST/Budget.lean](../../CutQueryComplexity/CanonicalST/Budget.lean#L455):

```lean
theorem exists_terminal_sqrt_program (hn : 2 ≤ Fintype.card V) (s t : V) (hst : s ≠ t) :
    ∃ T : DTree (Finset V) ℝ (Option (Output V)) (headlineBudget (Fintype.card V)),
      (∀ read : Finset V → ℝ, T.cost read ≤ headlineBudget (Fintype.card V)) ∧
      ∀ G : WeightedGraph V, AllPairsAudit.Unweighted G →
        ∃ out, T.eval G.cut = some out ∧ OutputSpec G s t out
```

**Reading it.**
- The inputs listed before `T` are a finite vertex type `V` with `n = Fintype.card V ≥ 2` and
  two distinct terminals `s` and `t`. The program `T` may depend on them. The graph `G` comes
  after `T`, so `T` cannot depend on it.
- The budget is `⌈2^23 · n · √n · ⌈log₂ 2n⌉³⌉`, with an explicit constant. For `n ≥ 2` this is
  `O(n^{3/2} log³(2n))`.
- `∀ read, T.cost read ≤ …`: the program never asks more queries than the budget.
- `∀ G, Unweighted G → ∃ out, T.eval G.cut = some out ∧ OutputSpec G s t out`: on every simple
  unweighted graph, with each query answered by the true cut value, the program succeeds and
  its output is correct.
- The returned value is the cut of a minimum `s`–`t` shore, so it is the minimum `s`–`t` cut
  value.
- **The flow is maximum.** `OutputSpec` does not say "maximum", but it implies it. Every
  feasible flow of value `r` has `r ≤ G.cut S` for each shore `S` with `s ∈ S` and `t ∉ S`
  (weak duality). The returned flow has value `out.value = G.cut out.shore`, so no feasible flow
  has a larger value. `output_flow_is_maximum` in
  [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean) proves this against every feasible
  real-valued flow, not only integral ones.
- `terminal_expanded` in the same file restates the theorem with `Unweighted`, `OutputSpec` and
  `FlowSpec` unfolded, and adds the two consequences above: the value is a natural number, and
  the flow is maximum.

**Differences from the paper.**
- *Which side the shore is on.* The paper defines `ν(G)` using shores that contain `t` but not
  `s`. Lean's shore contains `s` but not `t`. Its complement has the same cut, and
  `output_complement_is_paper_shore` in [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean)
  proves that `out.shoreᶜ` is a minimum shore in the paper's orientation, with cut `out.value`.
  The paper itself notes that either orientation gives the requested cut.
- *Integer values.* The value and the flow have type `ℝ`. The flow values are integers by
  `FlowSpec`, and the value is a natural number because it is a cut of an unweighted graph.
- *"Explicit" flow.* The paper calls the flow explicit: the algorithm writes it out on edges
  whose existence it has learned. In Lean the flow is part of the output, so the program does
  write it out, but the statement does not track which edges the program has learned. It comes
  close. The output depends only on the answers, so the same flow must be feasible in every
  unweighted graph that gives those answers, and every edge carrying flow is an edge of all of
  them. In the library, the flow is a maximum flow of the learned subgraph; see `finish` in
  [CanonicalST/Main.lean](../../CutQueryComplexity/CanonicalST/Main.lean#L61).

## Theorem 2: exact deterministic all-pairs cuts

**Paper.** A deterministic algorithm, given cut-query access to a simple unweighted undirected
graph `G` on `n ≥ 2` vertices, returns for each distinct ordered pair `(s, t)` a set `S_{s,t}`
and an integer `v_{s,t}` with `s ∈ S_{s,t}`, `t ∉ S_{s,t}` and
`v_{s,t} = c_G(S_{s,t}) = min_{s ∈ T, t ∉ T} c_G(T)`. It uses `O(n^{5/3} log⁵(2n))` cut queries.
The query budget and the adaptive procedure depend only on `n`, and the same cap holds for
arbitrary, even inconsistent, replies. The paper does not claim to output a flow for each pair.

The output is a table indexed by ordered pairs, and `allPairsGood` says when it is correct
([AllPairs/Representation.lean](../../CutQueryComplexity/AllPairs/Representation.lean#L86)):

```lean
structure STAnswer (V : Type) where
  shore : Finset V
  value : ℝ
```

```lean
abbrev Answers (V : Type) := V → V → STAnswer V
```

```lean
def allPairsGood (G : WeightedGraph V) (out : Answers V) : Prop :=
  ∀ s t, s ≠ t → IsSTMinCut G s t (out s t).shore ∧
    (out s t).value = G.cut (out s t).shore
```

For each distinct pair, the entry `out s t` must hold a minimum `s`–`t` shore of `G` and its cut
value. The entries `out s s` are not constrained; the paper asks only about distinct pairs.

The theorem,
[DeterministicAPMCExpansion/Pruning/Endpoint.lean](../../CutQueryComplexity/DeterministicAPMCExpansion/Pruning/Endpoint.lean#L42):

```lean
theorem deterministic_allPairs :
    ∃ (q : ℕ → ℕ)
      (P : (n : ℕ) → DTree (Finset (Fin n)) ℝ (Answers (Fin n)) (q n)),
      (∀ (n : ℕ) (G : WeightedGraph (Fin n)), AllPairsAudit.Unweighted G →
        allPairsGood G ((P n).eval G.cut)) ∧
      (∀ (n : ℕ) (read : Finset (Fin n) → ℝ), (P n).cost read ≤ q n) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        (q n : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) *
          ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 5) ∧
      ((fun n : ℕ => (q n : ℝ)) =o[atTop] fun n => (n : ℝ) ^ 2)
```

**Reading it.**
- `∃ (q : ℕ → ℕ) (P : …)`: a budget function `q` and a family of programs, one program `P n`
  for each `n`, are fixed first. `P n` asks vertex sets of `Fin n`, receives real numbers, and
  returns a table of answers. The graph comes later, so neither `q` nor `P` can depend on it.
- The first clause: for every `n` and every unweighted graph `G` on `Fin n`, the table that
  `P n` returns on `G` is correct. There is no promise about `G` beyond `Unweighted`.
- The second clause: on every answer function, `P n` asks at most `q n` queries.
- The third clause: one constant `C > 0` gives `q n ≤ C · n^{5/3} · (⌈log₂(2n+2)⌉ + 1)⁵` for
  every `n ≥ 2`. This is the paper's bound, since the logarithmic factor is at most a constant
  times `log(2n)` (see below).
- The fourth clause is an extra conclusion: `q(n) = o(n²)`. In Mathlib,
  [`f =o[atTop] g`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/Defs.html#Asymptotics.IsLittleO)
  means that for every real `c > 0`, `‖f n‖ ≤ c · ‖g n‖` for all large enough `n`. Here it says
  that for every `c > 0`, eventually `q n ≤ c · n²`.
- `allPairs_expanded` in [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean) restates
  the theorem with `Unweighted`, `allPairsGood` and `IsSTMinCut` unfolded, and adds that every
  returned value is a natural number.

**The logarithmic factor.** The library calls it `sizeLog`, and proves that it is at most a
constant times `ln n` for `n ≥ 2`
([Pruning/Parameters.lean](../../CutQueryComplexity/DeterministicAPMCExpansion/Pruning/Parameters.lean#L89),
[Pruning/Asymptotics.lean](../../CutQueryComplexity/DeterministicAPMCExpansion/Pruning/Asymptotics.lean#L21)):

```lean
def sizeLog (N : ℕ) : ℕ := Nat.clog 2 (2 * N + 2) + 1
```

```lean
theorem sizeLog_le_log {n : ℕ} (hn : 2 ≤ n) :
    (sizeLog n : ℝ) ≤ (5 / Real.log 2) * Real.log (n : ℝ)
```

**Companion statements.** The library also proves correctness and cost separately for its own
program, `program n`
([Pruning/Endpoint.lean](../../CutQueryComplexity/DeterministicAPMCExpansion/Pruning/Endpoint.lean#L24)):

```lean
theorem program_exact (n : ℕ) (G : WeightedGraph (Fin n))
    (hG : AllPairsAudit.Unweighted G) (s t : Fin n) (hst : s ≠ t) :
    IsSTMinCut G s t (((program n).eval G.cut) s t).shore ∧
      (((program n).eval G.cut) s t).value =
        G.cut (((program n).eval G.cut) s t).shore
```

```lean
theorem program_cost_bound (n : ℕ) (hn : 2 ≤ n) (read : Finset (Fin n) → ℝ) :
    ((program n).cost read : ℝ) ≤ headlineConstant * (n : ℝ) ^ (5 / 3 : ℝ) *
      ((Nat.clog 2 (2 * n + 2) + 1 : ℕ) : ℝ) ^ 5
```

Here the constant has a name, `headlineConstant`. It is a fixed positive real number, defined
in the library before any input; the [appendix](#appendix-the-program-and-the-constant-in-theorem-2)
shows its definition, and that of `program`.

**Differences from the paper.**
- *Integer values.* The paper returns an integer `v_{s,t}`. Lean's value has type `ℝ`, but it
  equals a cut of an unweighted graph, so it is a natural number; `allPairs_expanded` states this
  for every entry.
- *The logarithm.* Lean's bound has `(⌈log₂(2n+2)⌉ + 1)⁵` in place of `log⁵(2n)`. As shown
  above, Lean's factor is at most a constant times the paper's, so Lean's bound implies the
  paper's.
- *Small `n` and `o(n²)`.* The correctness and cost clauses hold for every `n`, including
  `n < 2`, and the theorem also proves `q(n) = o(n²)`. Both go beyond the paper.

## What is not formalized

Both headline theorems above are formalized in full. The paper's Lean appendix also maps every
numbered intermediate statement to Lean. It records one statement that is formalized only in
part, and one that is proved differently:

- **Theorem 19** (exact flow with known heavy terminal stars) gives two query bounds. Lean
  proves that the flow and shore are exact for arbitrary known integral stars, and proves the
  second bound, `O(qRt² log(2q+2))` for integers `t, R ≥ 1` with `q ≤ t³`, `1 ≤ C ≤ R` and
  `F ≤ qt`; this is the case that Theorem 2 uses. The general bound in the theorem's first
  display, `O((q + F + C^{1/3} q^{5/3} + q √(CF)) log(2q+2))`, is not stated as a single Lean
  theorem.
- **Lemma 20** (separating assignments) has the same statement in Lean, but a different proof.
  Lean gives an explicit recursive family of `8⌈log₂ ℓ⌉` assignments, which is `O(log(2ℓ))` as
  the lemma requires. The paper instead uses a probabilistic existence argument and then
  selects a family by exhaustive search.

The paper cites some classical results without proof, such as integral max-flow/min-cut. The
Lean proofs do not assume them: the axiom check below shows that the proofs use nothing beyond
Lean's standard axioms.

## Check it yourself

You do not need to trust this page. [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean)
restates each headline theorem above word for word, as `check_…`, together with the two
companion statements of Theorem 2, and proves each by citing the library. If the file compiles,
the library proves exactly these statements. The file also proves the small facts this page
cites: `honest_cut_is_natural`, `output_flow_is_maximum`, `output_complement_is_paper_shore`,
`terminal_expanded`, `allPairs_expanded` and `three_query_example_eval`. It runs two checks:

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
lake build CutQueryComplexity.CanonicalST.Budget \
  CutQueryComplexity.DeterministicAPMCExpansion.Pruning.Endpoint \
  CutQueryComplexityChecks.AxiomAudit
lake env lean --trust=0 papers/P2/VerifyHeadlineTheorems.lean
```

The last command should finish with no errors.

## Appendix: the program and the constant in Theorem 2

This appendix shows the definitions behind `program n` and `headlineConstant`, used in the
companion statements of Theorem 2.

**The program.** `program n` runs the construction on a padded graph and reads the answers
back on the original vertices
([Pruning/Main.lean](../../CutQueryComplexity/DeterministicAPMCExpansion/Pruning/Main.lean#L62)):

```lean
def budget (n : ℕ) : ℕ := coreBudget (Padded (Fin n))
```

```lean
def program (n : ℕ) : DTree (Finset (Fin n)) ℝ (Answers (Fin n)) (budget n) :=
  unpadProgram (minimumDegreeProgram (V := Padded (Fin n)))
```

The padded graph attaches to each vertex a triangle with two new vertices, so it has `3n`
vertices, each of degree at least two, as the construction requires. The new edges are known,
so each query to the padded graph costs one query to `G`. A minimum shore of the padded graph,
restricted to the original vertices, is a minimum shore of `G` with the same value. These steps
are part of the proof of `program_exact`; they are not hypotheses.

**The constant.** `headlineConstant` is built from a few named constants
([Pruning/Budget.lean](../../CutQueryComplexity/DeterministicAPMCExpansion/Pruning/Budget.lean#L171),
[Pruning/Parameters.lean](../../CutQueryComplexity/DeterministicAPMCExpansion/Pruning/Parameters.lean#L93),
[CutMatching/Gap.lean](../../CutQueryComplexity/DeterministicAPMCExpansion/CutMatching/Gap.lean#L89)):

```lean
def headlineConstant : ℝ := (constructionCoefficient : ℝ) * (24 : ℝ) ^ (5 / 3 : ℝ) * 4 ^ 5
```

```lean
def constructionCoefficient : ℕ := 100000 * (roundCoefficient + 1) ^ 3
```

```lean
def roundCoefficient : ℕ := 32 * entropyRoundFactor + 20
```

```lean
def entropyRoundFactor : ℕ := max 2 ⌈64 / gapConstant⌉₊
```

`gapConstant` comes from an entropy inequality used by the cut player
([CutMatching/Gap.lean](../../CutQueryComplexity/DeterministicAPMCExpansion/CutMatching/Gap.lean#L23)):

```lean
def pairGain (p q : ℝ) : ℝ :=
  2 * Real.negMulLog ((p + q) / 2) - Real.negMulLog p - Real.negMulLog q
```

```lean
private theorem exists_gap_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Set.Icc (0 : ℝ) (1 / 2), c ≤ pairGain 1 r
```

```lean
def gapConstant : ℝ := Classical.choose exists_gap_constant
```

```lean
theorem gapConstant_pos : 0 < gapConstant
```

[`Real.negMulLog p`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.html#Real.negMulLog)
is `−p ln p`. `exists_gap_constant` is a theorem, not an assumption: `r ↦ pairGain 1 r` is
continuous and positive on `[0, 1/2]`, so it has a positive lower bound there. `gapConstant` is
one such bound, picked by `Classical.choose`. So `headlineConstant` is a definite positive real
number, although the library does not compute its value. It does not depend on `n`, on the
graph, or on the answers.
