# Paper 3 in Lean: the headline theorems

**Paper:** [*Directed Cut Certificates through Fractional Forests and Shared Flows*](directed-cut-certificates.pdf) (PDF in this folder).

This page shows the Lean statements of the paper's headline results, Theorems 2, 3 and 4 and
Corollary 5, and explains how to read them. You do not need to read any Lean proofs. Lean's
kernel checks those, so what matters is whether the *statements* say what the paper says. With
the reading guide below, you can compare each statement with the paper in a few minutes. At the
end we explain how to confirm that the proofs are complete.

| Paper | Lean theorem (namespace `CutQueryComplexity.DirectedCertificate`) |
| --- | --- |
| Theorem 2: arbitrary-weight global certificates | [`Completion.exists_uniform_certificate`, `Completion.exists_weighted_global_witnessCertificate`, `exists_zero_witnessCertificate`](#theorem-2-arbitrary-weight-global-certificates) |
| Theorem 3: terminal certificates | [`Completion.exists_exact_terminal_certificate`, `Completion.exists_zero_terminal_certificate`](#theorem-3-terminal-certificates) |
| Theorem 4: spread-sensitive refinement | [`Completion.exists_intrinsic_paper_certificate`, `Completion.exists_intrinsic_ratio_paper_certificate`](#theorem-4-spread-sensitive-refinement) |
| Corollary 5: unit-capacity global certificates | [`Completion.exists_unit_paper_certificate`](#corollary-5-unit-capacity-global-certificates) |

Source links on this page point into this repository, at the version you are browsing. Each
Lean block is copied exactly from the linked file; proofs are omitted.

## How to read the statements

The paper is about *certificates*, not algorithms. A certificate for a graph `G` is a set of
queries whose answers already force the minimum cut, in every graph that gives the same answers.
The theorems say that small certificates exist. They do not say how to find them.

### Directed graphs and outgoing cuts

| Paper | Lean | Meaning |
| --- | --- | --- |
| vertex set `V` of size `n` | a finite type `V` with `Fintype.card V = n` | the theorems hold for every finite vertex type |
| graph with capacities `a_uv` | `G : WeightedDiGraph V` | a nonnegative real capacity `G.c u v` on each ordered pair, zero on the diagonal |
| `F_G(S)` | `G.out S` | total capacity of the arcs leaving `S` |
| shore `∅ ≠ S ⊊ V` | `ProperShore S` | `S` is nonempty and not all of `V` |
| `λ(G)` | `G.minValue` | the least outgoing cut over proper shores |
| `S` is a minimum cut | `IsGlobalMinCut G S` | `S` is a proper shore of value `λ(G)` |
| `λ_st(G)` | `terminalValue G s t` | the least outgoing cut over shores with `s ∈ S` and `t ∉ S` |
| `u_{v,w} = a_vw + a_wv` | `G.sym.w v w` | the symmetrized pair weight |
| `U`, `ν`, `κ = U/ν` | `symMaximum G`, `symMinimumPositive G`, `symSpread G` | the largest pair weight, the smallest positive one, and their ratio |
| `q(t)` | `PruningData.q G t` | the number of pairs with `0 < u_e < t` |
| `⌈log₂ 2n⌉`, `⌈n/k⌉` | `logL n`, `ceilDiv n k` | used in Theorem 2's budget |
| `log` in Theorem 4 and Corollary 5 | `Real.log` | the natural logarithm |
| number of queries in `Q` | `Q.card` | the number of shores in `Q` |

Most names live in the namespace `CutQueryComplexity.DirectedCertificate`. The theorems, and the
terminal and spread definitions, are in its sub-namespace `Completion`. `ProperShore` is in
`CutQueryComplexity`.

These are the definitions, from
[Graph/WeightedDirected.lean](../../CutQueryComplexity/Graph/WeightedDirected.lean#L15),
[Problem/Basic.lean](../../CutQueryComplexity/Problem/Basic.lean#L16) and
[DirectedCertificate/Basic.lean](../../CutQueryComplexity/DirectedCertificate/Basic.lean#L39):

```lean
structure WeightedDiGraph (V : Type*) where
  c : V → V → ℝ
  nonneg : ∀ u v, 0 ≤ c u v
  diag : ∀ v, c v v = 0
```

```lean
def out (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, G.c u v
```

```lean
def ProperShore (S : Finset V) : Prop := S.Nonempty ∧ S ≠ Finset.univ
```

```lean
def properShores (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.filter (fun S => S.Nonempty ∧ S ≠ Finset.univ)
```

```lean
noncomputable def minValue : ℝ :=
  if h : (properShores V).Nonempty then (properShores V).inf' h G.out else 0
```

```lean
def IsGlobalMinCut (G : WeightedDiGraph V) (S : Finset V) : Prop :=
  ProperShore S ∧ ∀ T, ProperShore T → G.out S ≤ G.out T
```

`G.c u v` is the capacity of the arc from `u` to `v`. There is no symmetry condition, so `G.c u v`
and `G.c v u` are independent and antiparallel arcs are allowed. As in the paper, parallel arcs
are represented by their total capacity. Capacities are arbitrary nonnegative reals: nothing
requires them to be integers, bounded, or of finite precision. `out` and `minValue` are defined
inside the namespace `WeightedDiGraph`, with `G` as a variable, so they are written `G.out S`
and `G.minValue`. `Finset V` is a finite set of vertices, `Sᶜ` is the complement of `S`, and
`univ` is the whole vertex set. `inf'` is the minimum over a nonempty finite set. The
assumptions `[Fintype V] [DecidableEq V]` say only that `V` is finite and that vertices can be
compared; they are not graph assumptions. The `else 0` branch of `minValue` applies only when
there is no proper shore, that is, when `n ≤ 1`; every global theorem below assumes `n ≥ 2`,
directly or through `1 ≤ k < n`.

### Certificates

The paper's Definition 1 reads as follows. A *global cut certificate* for `G` is a finite family
`𝒬` of shores and a specified optimum shore `S* ∈ 𝒬` such that every graph `G'` with
nonnegative capacities and `F_{G'}(Q) = F_G(Q)` for all `Q ∈ 𝒬` satisfies
`F_{G'}(S*) = λ(G') = λ(G)`. Competitors `G'` range over all loopless nonnegative real-weighted
graphs on `V`, with no restriction on their support or capacity size. A *terminal certificate*
is the same with `S*` an `s`–`t` shore and `λ` replaced by `λ_st`. `C_glob(G)` and `C_st(G)` are
the least possible numbers of queries.

In Lean
([DirectedCertificate/Basic.lean](../../CutQueryComplexity/DirectedCertificate/Basic.lean#L54)):

```lean
def Consistent (G G' : WeightedDiGraph V) (Q : Finset (Finset V)) : Prop :=
  ∀ S ∈ Q, G'.out S = G.out S
```

```lean
def IsMinCutValueCertificate (G : WeightedDiGraph V) (Q : Finset (Finset V)) : Prop :=
  ∀ G' : WeightedDiGraph V, Consistent G G' Q → G'.minValue = G.minValue
```

```lean
def IsMinCutWitnessCertificate (G : WeightedDiGraph V) (Q : Finset (Finset V))
    (S : Finset V) : Prop :=
  S ∈ Q ∧ ∀ G' : WeightedDiGraph V, Consistent G G' Q → IsGlobalMinCut G' S
```

`Consistent G G' Q` says that `G'` answers every query in `Q` exactly as `G` does. A value
certificate forces only the minimum value. A witness certificate is a family `Q` together with
a shore `S ∈ Q` that is a minimum cut of every consistent `G'`. All the global theorems use `IsMinCutWitnessCertificate`. It is the paper's
Definition 1:

- Taking `G' = G` shows that `S` is a minimum cut of `G` itself.
- Since `S ∈ Q`, every consistent `G'` gives `S` the same value as `G`. So
  `F_{G'}(S) = λ(G')` and `F_G(S) = λ(G)` give `λ(G') = λ(G)`: a witness certificate also
  certifies the value.

Both steps are library lemmas
([DirectedCertificate/Basic.lean](../../CutQueryComplexity/DirectedCertificate/Basic.lean#L119)):

```lean
theorem IsMinCutWitnessCertificate.isGlobalMinCut {G : WeightedDiGraph V}
    {Q : Finset (Finset V)} {S : Finset V} (h : IsMinCutWitnessCertificate G Q S) :
    IsGlobalMinCut G S
```

```lean
theorem IsMinCutWitnessCertificate.isValueCertificate {G : WeightedDiGraph V}
    {Q : Finset (Finset V)} {S : Finset V} (h : IsMinCutWitnessCertificate G Q S) :
    IsMinCutValueCertificate G Q
```

Conversely, the paper's condition `F_{G'}(S*) = λ(G')` says exactly that `S*` is a minimum cut
of `G'`. The equivalence of `IsMinCutWitnessCertificate G Q S` with Definition 1 written out
in full is proved as `global_certificate_iff_paper_contract` in this folder's
[VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).

Lean has no separate name for `C_glob(G)`. A statement
`∃ Q S, Q.card ≤ b ∧ IsMinCutWitnessCertificate G Q S` says exactly that `C_glob(G) ≤ b`.

### The shape of a certificate theorem

The global theorems all have this form:

```text
∀ G : WeightedDiGraph V, [assumptions on n, k and G] →
  ∃ Q S, Q.card ≤ [bound] ∧ IsMinCutWitnessCertificate G Q S
```

With the certificate unfolded, the conclusion reads:

```text
∃ Q S, Q.card ≤ [bound] ∧ S ∈ Q ∧
  ∀ G' : WeightedDiGraph V, (∀ A ∈ Q, G'.out A = G.out A) → IsGlobalMinCut G' S
```

(Theorem 4 lists the two conjuncts in the other order.) Check these points when reading one:

1. **The graph comes first.** `G` is fixed before `∃ Q S`, so `Q` and `S` may depend on
   everything about `G`: its arcs, its weights and its minimum cuts. This is an existence
   statement, like an NP witness. Neither the paper nor Lean claims an algorithm that finds `Q`
   with this many queries.
2. **One certificate for all competitors.** `Q` and `S` are chosen before `∀ G'`. The same family
   and the same shore must work against every competitor.
3. **Competitors range over all graphs.** `G'` is any `WeightedDiGraph V`: any nonnegative real
   capacities, with any support and any orientation. It may have arcs where `G` has none, and
   capacities far larger than any in `G`. An assumption such as "`G` has unit capacities"
   constrains `G` only, never `G'`.
4. **The witness is queried.** `S ∈ Q`, so `S` has the same value in every consistent `G'` as in
   `G`. This is what makes the value `λ(G)` certified too.
5. **Only the shores in `Q` are counted.** The bound is on `Q.card`. Whatever the proof knows
   about `G'` must follow from the answers on `Q`. Answers are exact real numbers and agreement
   is exact equality; there is no rounding.
6. **Constants are explicit.** Where the paper writes `O(·)`, Lean gives a number: `512`, `18`,
   `1000`, `600` or `weightedHeadlineConstant`. It does not depend on `G`, its weights, `n` or
   `k`.

## Theorem 2: arbitrary-weight global certificates

**Paper.** For every graph `G` on `n ≥ 2` vertices and every integer `1 ≤ k < n`, there is a
global cut certificate of size `O(nk² + nk log²(2n) + n²/k)`. In particular,
`C_glob(G) = O(n^{5/3})`. If `λ(G) = 0`, one query suffices. The constants are uniform over all
inputs and all weight values.

The budget uses these definitions
([DirectedCertificate/Basic.lean](../../CutQueryComplexity/DirectedCertificate/Basic.lean#L164)):

```lean
def ceilDiv (n k : ℕ) : ℕ := (n + k - 1) / k
```

```lean
def logL (n : ℕ) : ℕ := Nat.clog 2 (2 * n)
```

```lean
def budget (C n k : ℕ) : ℕ := C * (n * k ^ 2 + n * k * logL n ^ 2 + n * (ceilDiv n k + 1))
```

With natural-number division, `(n + k − 1) / k = ⌈n/k⌉`, and `Nat.clog 2 (2 * n)` is
`⌈log₂ 2n⌉`. So `budget 512 n k = 512 (nk² + nk ⌈log₂ 2n⌉² + n (⌈n/k⌉ + 1))`.

The theorem,
[DirectedCertificate/Completion/Main.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Main.lean#L276):

```lean
theorem exists_uniform_certificate (G : WeightedDiGraph V) (r : V)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    ∃ Q S, Q.card ≤ budget 512 (Fintype.card V) k ∧ IsMinCutWitnessCertificate G Q S
```

**Reading it.**
- For every graph `G` and every `k` with `1 ≤ k < n`, there is a family `Q` of at most
  `512 (nk² + nk ⌈log₂ 2n⌉² + n (⌈n/k⌉ + 1))` shores and a shore `S` forming a witness
  certificate.
- The constant `512` is the same for every graph, every weight, every `n` and every `k`.
- When `1 ≤ k < n`, `n (⌈n/k⌉ + 1) ≤ 3n²/k`. This is `ceiling_term_matches_paper` in
  [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean). Also `⌈log₂ 2n⌉` is within a
  constant factor of `log(2n)`. So the Lean budget is `O(nk² + nk log²(2n) + n²/k)`, the paper's
  bound.
- `r : V` is a vertex supplied by the caller, and nothing else in the statement mentions it. So
  any vertex will do, and since `1 ≤ k < n` forces `n ≥ 2`, a vertex always exists.
  `theorem2_expanded` in [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean) states the
  result without `r`, with the certificate written out.

**The `n^{5/3}` bound**
([DirectedCertificate/Completion/Corollaries.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Corollaries.lean#L119)):

```lean
noncomputable def weightedHeadlineConstant : ℝ :=
  512 * (5 + (6 / Real.log 2 + 1) ^ 2 * (2 : ℝ) ^ ((1 : ℝ) / 3))
```

```lean
theorem exists_weighted_global_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) :
    ∃ Q S, (Q.card : ℝ) ≤ weightedHeadlineConstant *
        (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3) ∧ IsMinCutWitnessCertificate G Q S
```

- `weightedHeadlineConstant` is a fixed real number, about `6.3 · 10⁴`.
- `(Q.card : ℝ)` and `(Fintype.card V : ℝ)` are the two counts viewed as real numbers, and
  `x ^ ((5 : ℝ) / 3)` is the real power `x^{5/3}`.
- Lean derives this from `exists_uniform_certificate` by taking `k = ⌊n^{1/3}⌋`. (The paper takes
  `k = min{n − 1, ⌈n^{1/3}⌉}`; either choice gives the `n^{5/3}` bound.)

**The zero case**
([DirectedCertificate/Basic.lean](../../CutQueryComplexity/DirectedCertificate/Basic.lean#L147)):

```lean
theorem exists_zero_witnessCertificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (h0 : G.minValue = 0) :
    ∃ S, (({S} : Finset (Finset V)).card ≤ 1) ∧ IsMinCutWitnessCertificate G {S} S
```

- The certificate is the single query `{S}`. The conjunct `card ≤ 1` is automatically true; the
  content is that `{S}` and `S` form a witness certificate.
- The reason is short: a competitor that agrees on `S` gives it value `0`, and no cut is
  negative.

**Differences from the paper.** None in content. Lean writes the budget with `⌈log₂ 2n⌉` and
`n (⌈n/k⌉ + 1)` in place of `log²(2n)` and `n²/k`, and takes the extra vertex argument `r`; both
are explained above.

## Theorem 3: terminal certificates

**Paper.** For every graph `G` and distinct vertices `s` and `t`, `C_st(G) = O(n)`. If
`λ_st(G) = 0`, one query suffices. The claim holds against the unrestricted competitor class
even when the input has unit capacities.

The terminal definitions minimize over exactly the shores that contain `s` and not `t`
([DirectedCertificate/Completion/Terminal.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Terminal.lean#L21)):

```lean
def terminalShores (s t : V) : Finset (Finset V) :=
  univ.filter fun S => s ∈ S ∧ t ∉ S
```

```lean
noncomputable def terminalValue (G : WeightedDiGraph V) (s t : V) : ℝ :=
  if h : (terminalShores s t).Nonempty then (terminalShores s t).inf' h G.out else 0
```

```lean
def IsTerminalMinCut (G : WeightedDiGraph V) (s t : V) (S : Finset V) : Prop :=
  s ∈ S ∧ t ∉ S ∧ ∀ T : Finset V, s ∈ T → t ∉ T → G.out S ≤ G.out T
```

```lean
def IsTerminalWitnessCertificate (G : WeightedDiGraph V) (s t : V)
    (Q : Finset (Finset V)) (S : Finset V) : Prop :=
  S ∈ Q ∧ ∀ G' : WeightedDiGraph V, Consistent G G' Q → IsTerminalMinCut G' s t S
```

The `else 0` branch of `terminalValue` applies only when `s = t`; both theorems below assume
`s ≠ t`.

The theorem,
[DirectedCertificate/Completion/Terminal.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Terminal.lean#L102):

```lean
theorem exists_exact_terminal_certificate (G : WeightedDiGraph V) {s t : V}
    (hst : s ≠ t) :
    ∃ Q : Finset (Finset V), ∃ S : Finset V, ∃ lam : ℝ,
      Q.card ≤ 18 * Fintype.card V + 1 ∧ S ∈ Q ∧
      lam = terminalValue G s t ∧ 0 ≤ lam ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' Q →
        s ∈ S ∧ t ∉ S ∧ G'.out S = lam ∧ terminalValue G' s t = lam ∧
        ∀ T : Finset V, s ∈ T → t ∉ T → lam ≤ G'.out T
```

**Reading it.**
- The only assumption is `s ≠ t`. There is no assumption that `λ_st(G) > 0`, no bound on other
  cuts, and no condition on the capacities of `G` or `G'`. In particular the theorem covers
  unit-capacity inputs against unrestricted competitors, as the paper's last sentence says.
- `Q.card ≤ 18n + 1` is the explicit form of `O(n)`.
- `lam` is the terminal value `λ_st(G)` of the input, and it is nonnegative.
- `S ∈ Q`: the witness shore is queried.
- For every consistent `G'`: `S` is an `s`–`t` shore, `G'.out S = lam`,
  `terminalValue G' s t = lam`, and every `s`–`t` shore `T` has value at least `lam` in `G'`.
  This is the paper's terminal condition `F_{G'}(S*) = λ_st(G') = λ_st(G)`, written out.

**The zero case**
([DirectedCertificate/Completion/Terminal.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Terminal.lean#L120)):

```lean
theorem exists_zero_terminal_certificate (G : WeightedDiGraph V) {s t : V}
    (hst : s ≠ t) (hzero : terminalValue G s t = 0) :
    ∃ S : Finset V, IsTerminalWitnessCertificate G s t {S} S ∧
      ∀ G' : WeightedDiGraph V, Consistent G G' {S} →
        G'.out S = 0 ∧ terminalValue G' s t = 0
```

- The certificate is the single query `{S}`. In every consistent `G'`, `S` is a minimum `s`–`t`
  shore and both `G'.out S` and `λ_st(G')` are `0`.
- `IsTerminalWitnessCertificate` says the same as the terminal part of Definition 1. Its value
  consequences are the library lemma `IsTerminalWitnessCertificate.values` (same file), and
  `terminal_certificate_iff_paper_contract` in
  [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean) proves the equivalence with the
  definition written out, as for the global predicate.

**Differences from the paper.** None. The `O(n)` bound is `18n + 1`.

## Theorem 4: spread-sensitive refinement

**Paper.** Suppose `λ(G) > 0`. Let `u_{v,w} = a_vw + a_wv` be the symmetrized weight of the pair
`{v, w}`, `ν = min_{u_e > 0} u_e`, `U = max_e u_e`, `κ = U/ν`, and `q(t) = |{e : 0 < u_e < t}|`.
Then

```text
C_glob(G) = O( min{ n^{5/3}, inf_{0 < t ≤ U} [ q(t) + n^{3/2} √((U/t) log(2n)) ] } ).
```

In particular, `C_glob(G) = O(min{n^{5/3}, n^{3/2} √(κ log(2n))})`. No bound on `κ`, on a
competitor's weights, or on its support is assumed in the competitor class.

**The pair weights.** The symmetrization is an undirected weighted graph
([DirectedCertificate/Basic.lean](../../CutQueryComplexity/DirectedCertificate/Basic.lean#L223)):

```lean
def sym : WeightedGraph V where
  w v w := G.c v w + G.c w v
  symm u v := add_comm _ _
  nonneg u v := add_nonneg (G.nonneg u v) (G.nonneg v u)
  diag v := by simp [G.diag]
```

So `G.sym.w v w = G.c v w + G.c w v`, the paper's `u_{v,w}`. The last three lines prove that this
weight is symmetric, nonnegative and zero on the diagonal. `symMaximum G` and
`symMinimumPositive G` are `U` and `ν`, computed from these weights of the input `G`; their
definitions are in the [appendix](#appendix-pair-weights-and-their-extremes). The spread is their
ratio
([DirectedCertificate/Completion/Corollaries.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Corollaries.lean#L180)):

```lean
noncomputable def symSpread (G : WeightedDiGraph V) : ℝ :=
  symMaximum G / symMinimumPositive G
```

The threshold count
([DirectedCertificate/Pruning.lean](../../CutQueryComplexity/DirectedCertificate/Pruning.lean#L463)):

```lean
def q (G : WeightedDiGraph V) (t : ℝ) : ℕ :=
  ((univ.filter fun p : V × V => 0 < G.sym.w p.1 p.2 ∧ G.sym.w p.1 p.2 < t).image
    fun p => s(p.1, p.2)).card
```

This takes the ordered pairs `p = (u, v)` with `0 < u_{u,v} < t`, maps each to the unordered pair
`s(u, v)`, and counts the distinct results. The two orders of a pair give the same unordered
pair, so each pair is counted once, and pairs `(v, v)` have weight `0` and are not counted. So
`PruningData.q G t` is the paper's `q(t)`. It lives in the namespace `PruningData`, but it takes
only `G` and `t`.

The theorem,
[DirectedCertificate/Completion/Corollaries.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Corollaries.lean#L270):

```lean
theorem exists_intrinsic_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (sInf {b : ℝ | ∃ t : ℝ, 0 < t ∧ t ≤ symMaximum G ∧
          b = 1000 * ((PruningData.q G t : ℝ) + (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
            Real.sqrt ((symMaximum G / t) * Real.log (2 * (Fintype.card V : ℝ))))})
```

**Reading it.**
- The assumptions are `n ≥ 2` and `λ(G) > 0`, as in the paper.
- The bound is a minimum of two terms. The first is Theorem 2's `n^{5/3}` bound, with the same
  constant. The second is `sInf` of the set of numbers
  `1000 (q(t) + n^{3/2} √((U/t) ln(2n)))` over thresholds `0 < t ≤ U`: the paper's infimum, times
  `1000`. `Real.sqrt` is the nonnegative square root.
- One certificate attains the bound. `Q` is chosen before the infimum, and `Q.card ≤ sInf A`
  means `Q.card ≤ b` for every `b` in `A` (by the next point, `sInf A` is a true infimum). So
  the same `Q` is good for every threshold at once.
  (In the paper this is automatic, since `C_glob(G)` is a single number.)
- In Lean, `sInf` of an empty set, or of a set with no lower bound, is `0` by convention. Here
  `λ(G) > 0` gives `U > 0`, so `t = U` is an allowed threshold and the set is nonempty; and every
  element is at least `0`. So `sInf` is the ordinary infimum. This is
  `intrinsic_bound_set_nonempty_bddBelow` in
  [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).
- The two terms carry different constants. Since `min(aX, bY) ≤ max(a, b) · min(X, Y)`, this is
  the paper's `O(min{…})` with a single constant.
- `U`, `ν`, `κ` and `q(t)` are computed from `G` alone. The competitors are those of
  `IsMinCutWitnessCertificate`, so nothing bounds a competitor's spread, weights or support.

**The ratio bound**
([DirectedCertificate/Completion/Corollaries.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Corollaries.lean#L346)):

```lean
theorem exists_intrinsic_ratio_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    ∃ Q S, IsMinCutWitnessCertificate G Q S ∧
      (Q.card : ℝ) ≤ min (weightedHeadlineConstant * (Fintype.card V : ℝ) ^ ((5 : ℝ) / 3))
        (1000 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
          Real.sqrt (symSpread G * Real.log (2 * (Fintype.card V : ℝ))))
```

This is the "in particular" clause, `min(C n^{5/3}, 1000 n^{3/2} √(κ ln(2n)))`, with `κ` the
input's spread `U/ν`. Lean sets `x / 0 = 0`, but that case does not arise: `λ(G) > 0` gives
`ν > 0`.

The library proves more: `exists_intrinsic_inf_certificate` and
`exists_intrinsic_ratio_certificate`, in the same file, give the same bounds without the factor
`log(2n)` under the square roots. Both are restated in
[VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean).

**Differences from the paper.** None in content. The logarithm is the natural logarithm, which
changes only constants.

## Corollary 5: unit-capacity global certificates

**Paper.** Every loopless unit-capacity directed input, with antiparallel arcs allowed, has a
global cut certificate of size `O(n^{3/2} √log(2n))`, sound against all consistent nonnegative
real-weighted competitors.

[DirectedCertificate/Completion/Corollaries.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Corollaries.lean#L294):

```lean
theorem exists_unit_paper_certificate (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hunit : ∀ u v, G.c u v = 0 ∨ G.c u v = 1) :
    ∃ Q S, (Q.card : ℝ) ≤ 600 * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) *
        Real.sqrt (Real.log (2 * (Fintype.card V : ℝ))) ∧ IsMinCutWitnessCertificate G Q S
```

**Reading it.**
- `hunit` says that each ordered capacity of the input is `0` or `1`. `G.c u v` and `G.c v u`
  are independent, so antiparallel arcs are allowed. The diagonal is `0` by the definition of
  `WeightedDiGraph`, so the input is loopless.
- `hunit` is about `G` only. The competitors inside `IsMinCutWitnessCertificate` are all
  nonnegative real-weighted graphs, as the paper requires. `corollary5_expanded` in
  [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean) writes the certificate out, so that
  the unrestricted `G'` is visible.
- The bound is `600 n^{3/2} √(ln 2n)`.

The library proves more:
[`exists_unit_global_certificate`](../../CutQueryComplexity/DirectedCertificate/Completion/Main.lean#L472)
gives `600 n^{3/2}`, without the factor `√(ln 2n)`. The theorem above is derived from it, using
`√(ln 2n) ≥ 1` for `n ≥ 2`. The paper derives the corollary from Theorem 4; Lean derives it
from this stronger bound instead. The statement is the same.

**Differences from the paper.** None in the statement.

## What is not formalized

Theorems 2, 3 and 4 and Corollary 5 are formalized in full. Some intermediate statements are
formalized in a weaker or different form, or not at all, as the paper's Lean appendix records:

- **Lemma 7** (sparse weighted domination) is not formalized in its general form, for an
  arbitrary explicit `H ≤ G` with `s` positive arcs. The Lean proof uses a specialized
  replacement: cut domination for the particular pruned graph built in the proof, and a global
  witness certificate of size `30n + 3|ret| + 1`, where `ret` is the set of ordinary arcs that
  graph retains.
- **Lemma 9**: Lean bounds the number of free arcs in each packing by `2(n − 1)`, one more than
  the paper's `2n − 3`. The combined support bound `2(n − 1)λ/μ + 4n − 6` is not a Lean theorem;
  the two packing statements give it with `4(n − 1)` in place of `4n − 6`.
- **Lemma 11**: Lean allows at most `n` exceptional pairs, rather than the paper's `n − 1`.
- **Proposition 24**: the quantity `s_k(H)` has no Lean definition. The Lean theorem takes the
  source set and its two flows as inputs instead.
- **Lemma 25** (weighted centers) has no Lean counterpart. The Lean proof of the spread
  refinement uses the common-source construction instead.
- **Lemma 26** (covering cuts with a capacity cap) is formalized only through its components.
  The assembly for an arbitrary cap `B` is not stated as one theorem.
- **Proposition 28** (unit inputs with capped competitors): Lean proves only the `O(nλ)`
  alternative, with `30n + 6nλ + 1` queries. The capped-competitor alternative
  `O(n² log(2λ)/λ)`, and the minimum of the two, are not formalized.
- **Section 9** (the terminal reduction through symmetrization) contains no numbered statement.
  Lean proves Theorem 3 by the direct flow certificate instead.

## Check it yourself

You do not need to trust this page. [VerifyHeadlineTheorems.lean](VerifyHeadlineTheorems.lean)
restates each headline theorem above word for word, as `check_…`, and proves it by citing the
library. If the file compiles, the library proves exactly these statements. It also restates the
stronger versions mentioned above, and proves the small facts this page cites. The file also
runs two checks on each theorem:

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
lake build CutQueryComplexity.DirectedCertificate.Completion.Corollaries \
  CutQueryComplexityChecks.AxiomAudit
lake env lean --trust=0 papers/P3/VerifyHeadlineTheorems.lean
```

The last command should finish with no errors.

## Appendix: pair weights and their extremes

This appendix gives the Lean definitions behind `U` and `ν` in Theorem 4. The symmetrization
`G.sym` has the undirected graph type of the library
([Graph/Weighted.lean](../../CutQueryComplexity/Graph/Weighted.lean#L18)):

```lean
@[ext] structure WeightedGraph (V : Type*) where
  w : V → V → ℝ
  symm : ∀ u v, w u v = w v u
  nonneg : ∀ u v, 0 ≤ w u v
  diag : ∀ v, w v v = 0
```

The extremes are taken over the finite set of pair weights
([DirectedCertificate/Completion/Corollaries.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Corollaries.lean#L24)):

```lean
noncomputable def symCapacities (G : WeightedDiGraph V) : Finset ℝ := by
  classical
  exact (univ : Finset (V × V)).image fun p => G.sym.w p.1 p.2

noncomputable def positiveSymCapacities (G : WeightedDiGraph V) : Finset ℝ :=
  (symCapacities G).filter fun x => 0 < x
```

```lean
noncomputable def symMaximum (G : WeightedDiGraph V) : ℝ := by
  classical
  exact (insert 0 (symCapacities G)).max' (insert_nonempty _ _)
```

```lean
noncomputable def symMinimumPositive (G : WeightedDiGraph V) : ℝ := by
  classical
  exact if h : (positiveSymCapacities G).Nonempty then
    (positiveSymCapacities G).min' h else 0
```

- `symCapacities G` is the set of values `u_{u,v}` over all ordered pairs `(u, v)`. It includes
  the pairs `(v, v)`, of weight `0`.
- `symMaximum G` is the largest element of that set with `0` added. All weights are nonnegative,
  so neither the extra `0` nor the diagonal changes the maximum: it is `U = max_e u_e`.
- `positiveSymCapacities G` keeps the positive values, and `symMinimumPositive G` is the least of
  them: `ν = min_{u_e > 0} u_e`. Its `else 0` branch applies only when every weight is `0`, which
  `λ(G) > 0` rules out.
- `by classical; exact …` only supplies the equality test on real numbers needed to form a
  finite set. It is not an assumption.

The library checks these readings
([DirectedCertificate/Completion/Corollaries.lean](../../CutQueryComplexity/DirectedCertificate/Completion/Corollaries.lean#L75)):

```lean
theorem intrinsic_parameters (G : WeightedDiGraph V)
    (hn : 2 ≤ Fintype.card V) (hlam : 0 < G.minValue) :
    0 < symMinimumPositive G ∧ symMinimumPositive G ≤ symMaximum G ∧
      (∀ u v, G.sym.w u v ≤ symMaximum G) ∧
      ∀ u v, 0 < G.sym.w u v → symMinimumPositive G ≤ G.sym.w u v
```

When `n ≥ 2` and `λ(G) > 0`: `0 < ν ≤ U`, every pair weight is at most `U`, and every positive
pair weight is at least `ν`.
