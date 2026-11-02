# Audit of the Lee–Sidford facts used by the stable implicit LP

This audit checks the Lee–Sidford facts used by an earlier, unpublished draft
of the stable implicit LP execution; below, *the note* means that draft. The
repaired analysis is Section 15 of [*Subquadratic Cut-Query Algorithms for
Directed Minimum Cuts*](../../papers/P4/subquadratic-directed-minimum-cuts.pdf)
(P4), which cites this audit as [LSAudit26]. The Lean docstrings in
`CutQueryComplexity/ImplicitLP/` call the draft *the audited draft*.
Scripts and numerical evidence are in [`num/`](num/). The LS source was read from the
arXiv e-print listed in §0 and is not vendored here.

---------------------------------------------------------------------------

## 0. Provenance

| Item | Value |
|---|---|
| Audited draft | Unpublished draft of the stable implicit LP execution, SHA-256 `597b788f…781c59`. |
| Cited paper | Y. T. Lee, A. Sidford, *Solving Linear Programs with Õ(√rank) Linear System Solves*, **arXiv:1910.08033v2** [cs.DS], stamped "31 Aug 2020". |
| PDF read | `https://arxiv.org/pdf/1910.08033v2`, 69 pages, SHA-256 `6a660ef7d0c56fd239c1f25972bd78be698eaa296e1ebdf8e9061b335955b909`. |
| LaTeX source read | `https://arxiv.org/e-print/1910.08033v2`, a gzip tar dated 2 Sep 2020, SHA-256 `75cca8e7…8e63e8b`. Relevant files: `sec_maxflow_prelim.tex` (`54ee3005…`), `sec_maxflow_alg.tex` (`bdf8fc18…`), `lewis_weight.tex` (`9193beee…`), and `projection_facts.tex` (`f5f85a73…`). |
| Page numbers below | These are the *printed* page numbers of the v2 PDF. The physical PDF page is the printed number plus 1. |

Quotations are taken verbatim from the v2 LaTeX source. Macros are expanded to
plain notation: `\mixedNorm{y}{w}` becomes `‖y‖_{w+∞}`, and `\cnorm` becomes
`C_norm`. Obvious typesetting typos are marked `[sic]`.

---------------------------------------------------------------------------

## 1. Notation dictionary (LS ↔ note)

| LS (v2) | Note | Meaning |
|---|---|---|
| `m` | `M` | number of rows / LP variables |
| `n` | `r` | number of columns (LS assumes rank n) |
| `A ∈ R^{m×n}`, `Aᵀx = b`, `l_i < x_i < u_i` | same, `A∈R^{M×r}` | LP (1.2)/(eq:lp) |
| `φ_i`, `Φ''`, `√φ''` | `φ_i`, `S = diag √φ''` | barrier, local scaling |
| `A_x = Φ''(x)^{-1/2} A` | `A_x = S(x)^{-1}A` | rescaled matrix |
| `‖y‖_{w+∞} = ‖y‖_∞ + C_norm‖y‖_w` | `N_w(y) = ‖y‖_∞ + C_N‖y‖_w` | mixed norm |
| `C_norm = 24√c_s c_k` (Def. 12) | `C_N = 48k` | mixed-norm constant |
| `c_1, c_s, c_k` | `3r, 4, k` (claimed) | size / sensitivity / consistency |
| `g(x) = w_p(A_x) + c_0` (Thm 29) | `g(x) = w_p(A_x) + 2r/M` | weight function |
| `c_0 = n/(2m)` (LS's choice) | `c_0 = 2r/M` | regularisation (**differs by a factor 4**) |
| `p = 1 − 1/log(4m)` | `p = 1 − 1/L_0`, `L_0 ≥ ⌈log₂(4M)⌉` | Lewis exponent |
| `c_k ≤ 2/(1−p)` | `k = 2L_0` | consistency |
| `δ_t(x,w)` (Def. 11) | `δ_t(x,w)` | centrality (identical formula) |
| `h_t(x,w)` | `h` ("exact feasible Newton direction") | projected Newton step |
| `c_γ` (Lemma 13) | `γ = 1+(16k)^{-1}` | projection factor |
| `ε` in Lemma 16 | `v` | step size in mixed norm |
| `ε` in Lemma 17 | `a` | log-weight change in mixed norm |

---------------------------------------------------------------------------

## 2. LS definitions the facts depend on (verbatim, v2)

**D-Nondeg** (§2 Notation, p. 6). "We call a matrix A *non-degenerate* if it
has full column-rank and no zero rows." "For non-degenerate A we let
P(A) := A(AᵀA)^{-1}Aᵀ denote the orthogonal projection matrix onto A's image and
σ(A) := diag(P(A)) denote A's *leverage scores*. We let Σ(A) := Diag(σ(A)),
P^{(2)}(A) := P(A)∘P(A), Λ(A) := Σ(A) − P^{(2)}(A), and
Λ̄(A) := Σ(A)^{-1/2}Λ(A)Σ(A)^{-1/2}." "For positive w … ‖x‖_w² := Σ_i w_i x_i²."

**Definition 4 (Self-concordance)** (p. 5). "A convex, thrice continuously
differentiable function φ : K → Rⁿ [sic] is a ν-self-concordant barrier
function for open convex set K ⊂ Rⁿ if the following conditions hold:
lim_{i→∞} φ(x_i) → ∞ for all sequences x_i ∈ K converging to boundary of K;
|D³φ(x)[h,h,h]| ≤ 2|D²φ(x)[h,h]|^{3/2} for all x ∈ K and h ∈ Rⁿ;
|Dφ(x)[h]| ≤ √ν |D²φ(x)[h,h]|^{1/2} for all x ∈ K and h ∈ Rⁿ."

**Trigonometric barrier** (§3.1, Case (3), p. 10). "φ_i(x) := −log cos(a_i x + b_i)
for a_i = π/(u_i−l_i) and b_i = −(π/2)(u_i+l_i)/(u_i−l_i) … φ_i'(x) = a_i tan(a_i x+b_i),
φ_i''(x) = a_i²/cos²(a_i x+b_i), φ_i''' = 2a_i³ sin(a_i x+b_i)/cos³(a_i x+b_i).
Therefore, |φ_i'(x)| ≤ a_i/|cos(a_i x+b_i)| = √φ_i''(x) and |φ_i'''(x)| ≤ 2(φ''(x))^{3/2}."
This is exactly the note's φ_i, because a_i x + b_i = π(x − (ℓ+u)/2)/(u−ℓ).

**Penalised objective and Newton step** (§3.2–3.3, pp. 11–12).
f_t(x,w) := t·cᵀx + Σ_i w_i φ_i(x_i). ∇_x f_t = t·c + wφ'(x). Also
"P_{x,w} := I − W^{-1}A_x(A_xᵀW^{-1}A_x)^{-1}A_xᵀ for A_x := Φ''(x)^{-1/2}A" (3.3)
and h_t(x,w) := −(1/√φ''(x)) P_{x,w}( ∇_x f_t(x,w) / (w√φ''(x)) ).

**Definition 11 (Centrality Measure)** (p. 12). "We measure the centrality of
{x,w} by δ_t(x,w) := min_{η∈Rⁿ} ‖ (∇_x f_t(x,w) − Aη)/(w√φ''(x)) ‖_{w+∞}, where for all
y ∈ R^m we let ‖y‖_{w+∞} := ‖y‖_∞ + C_norm‖y‖_W for C_norm > 0 defined in
Definition 12." The note's δ_t is the same expression with C_norm replaced by C_N.

**Definition 12 (Weight Function)** (p. 13). "Differentiable g : Ω° → R^m_{>0} is
a (c_1, c_γ [sic], c_k)-weight function if the following hold for all x ∈ Ω° and
i ∈ [m]:
* The size, c_1, satisfies c_1 ≥ max{1, ‖g(x)‖_1}.
* The sensitivity, c_s, satisfies
  c_s ≥ e_iᵀ G(x)^{-1}A_x(A_xᵀG(x)^{-1}A_x)^{-1}A_xᵀG(x)^{-1}e_i.
* The consistency, c_k, satisfies ‖G(x)^{-1}J_g(x)(Φ''(x))^{-1/2}‖_{g(x)+∞} ≤ 1 − c_k^{-1} < 1.

Through [sic] we assume we have such a weight function and define
C_norm := 24√c_s c_k."

Note: the consistency condition is measured in the mixed norm, and that norm
already contains C_norm. The definition is therefore circular in
`(c_s, c_k, C_norm)`. For the note's fixed C_N, the circularity resolves as
follows. Consistency with constant `c_k = k` holds whenever `C_N ≥ k`; see
F4(b).

**Definition 20 (Lewis Weight)** (p. 19). "For all p > 0 and non-degenerate
A ∈ R^{m×n} we define the ℓ_p Lewis weight w^{(p)}(A) as the unique vector
w ∈ R^m_{>0} such that w = σ(W^{1/2−1/p}A) where W = Diag(w)." The footnote
mentions zero rows and rank deficiency, which are not used here.

**Definition 21 (Volumetric Potential)** (p. 20).
𝒱_p^A(w) := −(1/(1−2/p)) log det(AᵀW^{1−2/p}A).

---------------------------------------------------------------------------

## 3. Fact-by-fact audit

Each subsection gives:

* (a) the LS statement or statements, verbatim;
* (b) the substitution into the note, checked by hand;
* (c) the gaps.

Throughout this section:

* `k = 2L_0`, `p = 1 − 1/L_0`, and `C_N = 48k`.
* `L_0` is a power of two with `L_0 ≥ max{2, ⌈log₂(4M)⌉}`.
* `A ∈ R^{M×r}` has full column rank r, which the explicit `+I_r` block
  guarantees, and has no zero rows.

### F1. `eq:barrier` and self-concordance (LS §3.1, Lemmas 8, 9)

(a) **Lemma 8** ([46, Thm 4.1.6], p. 10). "If s ∈ dom(φ_i) for i ∈ [m], and
r := √φ_i''(s)|s − t| < 1 then t ∈ dom(φ_i) and
(1−r)√φ_i''(s) ≤ √φ_i''(t) ≤ (1−r)^{-1}√φ_i''(s). Therefore √φ_i''(s) ≥ 1/U where U
is the diameter of dom(φ_i)."
**Lemma 9** ([46, Thm 4.2.4], p. 10). "φ_i'(x)·(y − x) ≤ 1 for all
x, y ∈ dom(φ_i) and i ∈ [m]."

(b) The note's `eq:barrier` uses W := u_i−ℓ_i ≤ U, θ := π(x−(ℓ+u)/2)/W ∈ (−π/2, π/2),
S_i = (π/W)/cos θ, and s_i = (W/π)(π/2 − |θ|). Put ϑ := π/2−|θ| ∈ (0,π/2].

* `|φ'| ≤ S`: this is |tan θ| ≤ sec θ. ✓
* `|φ'| ≤ 1/s`: this is equivalent to ϑ·cot ϑ ≤ 1, which holds because ϑ ≤ tan ϑ. ✓
* `U^{-1} ≤ S`: S ≥ π/W ≥ π/U ≥ 1/U. ✓ This uses the hypothesis "U bounds box widths".
* `S ≤ 2/s`: this is equivalent to ϑ ≤ 2 sin ϑ, which holds because sin ϑ ≥ (2/π)ϑ on [0,π/2]. ✓
* `S s ≥ 1`: this is ϑ/sin ϑ ≥ 1. ✓
* `φ'(x)(v−x) ≤ 1` for v ∈ [ℓ,u]: if θ ≥ 0, the worst case is v = u, which gives
  (π/W)tan θ·(W/π)ϑ = ϑ cot ϑ ≤ 1. The case θ < 0 is symmetric. ✓ The closed
  interval is fine; it is the limit of LS Lemma 9.
* "Self-concordance controls Hessian change for normalized step < 1": this is
  Lemma 8. Domain inclusion is immediate from `S s ≥ 1`, since |d| < 1/S ≤ s.
* The lower bound "−φ'(x̄_i) ≥ 1/(2s) for s ≤ (u−ℓ)/4", used in `lem:slack`, is
  equivalent to ϑ cot ϑ ≥ 1/2 for ϑ ≤ π/4. This holds because ϑ cot ϑ is
  decreasing, with value π/4 > 1/2 at ϑ = π/4. ✓
* `lem:newton` uses the integrated form
  `|φ'(x+d) − φ'(x) − S²d| ≤ S·z²/(1−z)`, where z = S|d| < 1. Proof: by Lemma 8,
  |φ''(x+τd) − φ''(x)| ≤ φ''(x)((1−τz)^{-2} − 1), and
  ∫₀¹((1−τz)^{-2}−1)dτ = z/(1−z). Dividing by S(x+d) ≥ (1−z)S gives the
  note's `z²/(1−z)²`. ✓
* The final constant in `lem:newton` is `η/(1−a)+a²/(1−a)² ≤ 8δ²+4η`, where
  a = γδ+η ≤ 1/10 and γ ≤ 17/16. Hand check: a²/(1−a)² ≤ (γ²δ² + 2aη)/0.81 ≤ 1.40δ² + 0.25η,
  and η/(1−a) ≤ 1.12η. ✓ A grid check is in `num/` and agrees.

(c) No mathematical gap. For the citation chain, LS Lemmas 8 and 9 are
imported from Nesterov. For the trigonometric barrier they are better proved
directly as above than through the general theory.

### F2. `eq:gsize` (LS Theorem 29 size part, Lemma 47(2),(6), Definition 20, Lemma 22)

(a) **Theorem 29** (p. 25), verbatim. "For any p ∈ (0,1) and any c_0 ≥ 0, the
weight function g : Ω° → R^m_{>0} defined for all x ∈ R^m_{>0} [sic] as
g(x) := w_p(A_x) + c_0 where A_x := (Φ''(x))^{-1/2}A, is a weight function in the
context of Definition 12 and satisfies c_1(g) ≤ n + c_0 m, c_s(g) ≤ 2m^{1−p}, and
c_k(g) ≤ 2/(1−p). Further, for p = 1 − 1/log(4m) and c_0 = n/(2m), we have
c_1(g) ≤ (3/2)n, c_s(g) ≤ 4, and c_k(g) ≤ 2 log(4m)."

**Lemma 47** (Projection Matrices, p. 46). For an orthogonal projection P
and Σ = Diag(P), the lemma states:

* (1) Σ_ii = Σ_j P_ij^{(2)};
* (2) 0 ⪯ P^{(2)} ⪯ Σ ⪯ I, so in particular 0 ≤ Σ_ii ≤ 1;
* (3) P_ij^{(2)} ≤ Σ_ii Σ_jj;
* (4) ‖Σ^{-1}P^{(2)}x‖_∞ ≤ ‖x‖_Σ;
* (5) ‖Σ^{-1}P^{(2)}x‖_∞ ≤ ‖x‖_∞;
* (6) Σ_i Σ_ii = rank(P).

**Lemma 22** (p. 20). "For all non-degenerate A ∈ R^{m×n} its ℓ_p Lewis weights
exist and are unique for p > 0. For p ≠ 2 the weights w_p(A) are the unique
minimizer of … min_{w>0} 𝒱_p^A(w) + Σ_i w_i …"

(b) Σ_i w_p(A_x)_i = tr P(W^{1/2−1/p}A_x) = rank(A_x) = r. This needs A_x to be
non-degenerate. A_x = S^{-1}A with S > 0, so this follows from A having full
column rank and no zero rows. The note ensures both: it keeps the `+I_r` block
and removes zero explicit rows.

So Σg = r + M·(2r/M) = 3r. ✓ This is an equality, not just c_1 ≤ 3r.

Bounds: 0 < w_p,i ≤ 1 by Lemma 47(2). Positivity holds because σ_i(DB) > 0 when
row i of DB is nonzero and B has full rank. Hence 2r/M < g_i ≤ 1+2r/M. ✓

Derived invariants in the note:

* r/M ≤ w_i ≤ 4, using e^{−K}·2r/M ≥ r/M and e^{K}(1+2r/M) ≤ 4, which needs r ≤ M. ✓
* Σw ≤ 4r. ✓

(c) The size part has no gap. Recorded hypothesis: A must have full column rank
r and no zero rows (`NonDeg`). The note states this, and it must be an explicit
hypothesis.

### F3. `eq:projection` (LS Lemma 10, Lemma 13, Theorem 29 sensitivity)

(a) **Lemma 10** (p. 12). "For any norm ‖·‖ and ‖y‖_Q := min_{η∈Rⁿ}
‖y − Aη/(w√φ''(x))‖, we have ‖y‖_Q ≤ ‖P_{x,w}y‖ ≤ ‖P_{x,w}‖·‖y‖_Q and therefore for all
{x,w} … δ_t(x,w) ≤ ‖√φ''(x) h_t(x,w)‖_{w+∞} ≤ ‖P_{x,w}‖_{w+∞}·δ_t(x,w)." (3.4)

**Lemma 13** (p. 13). "For any w such that (4/5)g(x) ≤ w ≤ (5/4)g(x), we have that
‖P_{x,w}‖_{w+∞} ≤ c_γ where c_γ := 1 + √(2c_s)/C_norm ≤ 1 + 1/(16c_k)."
The proof uses three steps:

* ‖P y‖_{w+∞} ≤ (1 + ‖I−P‖_{w→∞}/C_norm)‖y‖_{w+∞};
* ‖I−P‖_{w→∞}² = max_i e_iᵀW^{-1}A_x(A_xᵀW^{-1}A_x)^{-1}A_xᵀW^{-1}e_i;
* "Since (4/5)g ≤ w ≤ (5/4)g … ≤ 2 max_i e_iᵀG^{-1}A_x(…)^{-1}A_xᵀG^{-1}e_i ≤ 2c_s."

Theorem 29 sensitivity (p. 25) claims c_s(g) ≤ 2m^{1−p}. Its proof is quoted
verbatim: "note that Lemma 26 and that p ≤ 1 yield
e_iᵀG(x)^{-1}A_x(A_xᵀG(x)^{-1}A_x)^{-1}A_xᵀG(x)^{-1}e_i = g(x)_i^{-1}σ(G(x)^{1/2−1/1}A_x)_i
≤ 2m^{α/(1+α)} where α = 2/p − 2/1 …"

**Lemma 26** (p. 23). "For all non-degenerate A ∈ R^{m×n} and w := w_p(A) for
0 < p < r we have σ(W^{1/2−1/r}A)_i w_i^{-1} ≤ c_{p,r,m} := (1+α)^{1/(1+α)}((1+1/α)m)^{α/(1+α)}
≤ 2m^{α/(1+α)} where α = 2/p − 2/r."

(b) Substitution. The note's h satisfies Aᵀh = 0 and tc + Wφ' + WS²h = Aπ.
Hence Sh = −(tc + wφ' − Aπ)/(wS), and

* `δ_t ≤ N_w(Sh)` is immediate from the definition of δ_t, taking ν = π. ✓
* `Sh = −P_{x,w}(∇f/(wS))`. This is LS (3.3) together with Lemma 51 (p. 49). ✓
* The upper bound needs ‖P_{x,w}‖_{N_w} ≤ γ = 1+1/(16k). Via LS this needs
  √(2c_s)/C_N ≤ 1/(16k). With C_N = 48k this means c_s ≤ 4.5. The note uses
  "c_s ≤ 4" from "c_s ≤ 2M^{1−p}" and "M^{1−p} ≤ 2".
  * `M^{1−p} = 2^{log₂M/L_0} < 2` because L_0 ≥ log₂(4M) > log₂M. ✓
  * The comparison factor (5/4)³ = 1.953 ≤ 2 is checked. ✓
  * The arithmetic is √8/(48k) = 1/(16.97k) ≤ 1/(16k). ✓

**The step "c_s(g) ≤ 2M^{1−p}" is false for c_0 > 0.** This is gap G1.

* LS's proof applies Lemma 26, a statement about the *exact* Lewis weights
  w = w_p(A), to g = w_p(A) + c_0 ≠ w_p(A).
* The regularisation decreases G^{-1}. That makes (A_xᵀG^{-1}A_x)^{-1} *larger*,
  so no monotonicity rescues the bound.

Explicit numerical counterexample (`num/counterexample.py`):

* Parameters: p = 1 − 1/16 (L_0 = 16 for M = 10100), M = 10100, r = 100.
* Column 1 contains one row e₁ and K = 10000 rows s·e₁, with
  s = (80/K)^{1/p} = 5.798·10⁻³.
* Columns 2…100 each contain one row e_j.
* The Lewis fixed-point residual is 1e−15, and Σw = 100.
* Result: c_s(w_p) = 1.88, which respects the bound 2M^{1−p} = 3.56. However,
  c_s(w_p + n/(2m)) = **26.87**, which is LS's own choice, and
  c_s(w_p + 2r/M) = **20.16**, which is the note's choice. Both exceed the
  claimed 3.56 and 4.
* Closed form for this block matrix:
  `c_s = 1/(g₀ + K s² g₀²/g_s)` = 1/(0.03215 + 0.01746) = 20.16.
* Along the family, with r ≈ √M, c_s grows like ≈ √M/6 (see `num/t3.py`).
* For incidence-structured matrices (`+I_r` rows and complete-graph edge rows
  with arbitrary positive row scalings), the measured values are 2.79 at r = 100.
  These exceed the unregularised 1.36 and the trend is increasing, but 4 has
  not yet been exceeded. Whether the note's restricted LP class can violate
  `γ ≤ 1+1/(16k)` is **not settled**.

Consequence: `eq:projection` currently has no valid source proof. The statement
itself is not refuted. With the sharper Lemma 13′ below, the constant would
survive whenever c_s(g) ≤ 144k. However, the only general bound for the note's
regularisation is c_s(g) ≤ 1/c_0 = M/(2r), and the family above grows faster
than 144k = 288L_0 for large M.

**Repair (recommended, fully proved here).**

**Lemma S (regularised sensitivity).** Let A ∈ R^{M×r} be non-degenerate, let
0 < p ≤ 1, let w = w_p(A), and let α := 2/p − 2 ≥ 0. Let 0 < ε < 1 and
0 ≤ c ≤ ε/M, and put g = w + c. Then for all i,
`g_i^{-2} a_iᵀ(AᵀG^{-1}A)^{-1}a_i ≤ (2/(1−ε))(M/ε)^α`.

Proof:

1. Put β := 2/p − 1 and H := AᵀW^{-β}A = AᵀW^{1−2/p}A. The Lewis identity
   gives w_i = w_i^{-β}a_iᵀH^{-1}a_i, so a_iᵀH^{-1}a_i = w_i^{2/p}.
2. Call row j light if w_j ≤ ε/M. Then
   tr(H^{-1}Σ_{light} w_j^{-β}a_ja_jᵀ) = Σ_{light} w_j ≤ ε.
3. Hence H_light ⪯ εH, and so H ⪯ (1−ε)^{-1}H_heavy. This is the argument of
   LS Lemma 28.
4. On heavy rows, w_j^{-β} = w_j^{-α}w_j^{-1} ≤ (M/ε)^α w_j^{-1}. Also
   c ≤ ε/M < w_j, so w_j^{-1} ≤ 2/(w_j+c) = 2g_j^{-1}.
5. Therefore H ⪯ (2/(1−ε))(M/ε)^α AᵀG^{-1}A, and (AᵀG^{-1}A)^{-1} ⪯ (2/(1−ε))(M/ε)^α H^{-1}.
6. Then g_i^{-2}a_iᵀ(AᵀG^{-1}A)^{-1}a_i ≤ (2/(1−ε))(M/ε)^α w_i^{2/p}/g_i², and
   w_i^{2/p}/g_i² ≤ w_i^{2/p−2} ≤ 1. ∎

With ε = 1/2 and p = 1−1/L_0, we have α = 2/(L_0−1). Since L_0 − 1 ≥ log₂(2M),
(2M)^α ≤ 4, and therefore **c_s(g) ≤ 16 whenever c_0 ≤ 1/(2M)**. Numerically
the maximum observed is 3.1 (`num/t6.py`).

**Lemma 13′ (Pythagorean sharpening of Lemma 13).** P_{x,w} is the
⟨·,·⟩_w-orthogonal projection, with Q := I − P. Let q(w) := max_i e_iᵀW^{-1}A_x(A_xᵀW^{-1}A_x)^{-1}A_xᵀW^{-1}e_i.

* Then ‖Qy‖_∞ ≤ √q(w)·‖Qy‖_w, because Q = Q².
* Also ‖Py‖_w² = ‖y‖_w² − ‖Qy‖_w².
* Hence N(Py) ≤ ‖y‖_∞ + max_t(√q t + C√(‖y‖_w² − t²)) = ‖y‖_∞ + ‖y‖_w√(q+C²).
* So ‖P‖_{N_w} ≤ √(1+q/C²) ≤ 1 + q/(2C²).

LS's bound is 1 + √q/C. With q(w) ≤ 2c_s(g) ≤ 32 and C_N = 48k,
1 + 32/(2·2304k²) ≤ 1 + 1/(16k). ✓

Alternatively, keep LS's Lemma 13 and choose C_N ≥ 91k (for example 96k).
T_0 then doubles; the asymptotics are unchanged.

Downstream effect of changing the regularisation from 2r/M to 1/(2M):

* eq:gsize becomes Σg = r + 1/2 and 1/(2M) < g_i ≤ 1 + 1/(2M).
* The invariant `r/M ≤ w_i` becomes `w_i ≥ 1/(4M)`.
* Σw ≤ 4r and T_0 are unchanged.
* s_* in `eq:slackfloor` picks up a factor of about 1/(4r). With
  w_min = 1/(4M), t ≤ 16r/ε, ‖c_*‖_∞ ≤ 4U, Σw ≤ 4r and s_0 ≥ 1/U,
  `lem:slack` gives s_* = ε/(2^{11} r M² U³) up to the rounding in the note;
  it must be recomputed downstream.
* q_*, `eq:normalbounds` (‖D‖ ≤ 4MU² instead of MU²/r, and so on), P(𝒩), and β
  change polynomially.

None of these changes affects the Õ(√r) iteration count.

(c) Gaps: G1 (major), and G8 for attainment in Lemma 10, see F8.

### F4. `eq:gmove` (LS Lemma 16 with Theorem 29 consistency, Lemmas 24, 25, 47, 49)

(a) **Lemma 16** (p. 15). "For all t ∈ [0,1], let x_t := x_0 + tΔ for Δ ∈ R^m and
g_t = g(x_t) such that x_t ∈ Ω°. Then for ε = ‖√φ_0''Δ‖_{g_0+∞} ≤ 1/10 we have
‖log(g_1) − log(g_0)‖_{g_0+∞} ≤ (1 − c_k(g)^{-1} + 4ε)ε ≤ 1/5 and for all s,t ∈ [0,1]
and for all y ∈ R^m we have ‖y‖_{g_s+∞} ≤ (1+2ε)‖y‖_{g_t+∞}."

**Theorem 29, consistency part** (p. 25). "c_k(g) ≤ 2/(1−p)." The proof is
quoted verbatim in substance:

* "G(x)^{-1}J_g(x)(Φ''(x))^{-1/2}h = G(x)^{-1}J_w((Φ''(x))^{-1/2})z where
  z = −(1/2)(Φ''(x))^{-2}Φ'''(x)h. By Lemma 25, ‖G^{-1}J_w z‖_{g(x)} ≤ p‖Φ''^{1/2}z‖_{g(x)}
  and ‖G^{-1}J_w z‖_∞ ≤ p‖Φ''^{1/2}z‖_∞ + p‖Φ''^{1/2}z‖_{g(x)}."
* This yields "≤ p(1 + 1/C_norm)‖h‖_{g(x)+∞}".
* Finally "p(1+1/C_norm) ≤ p + 1/(24c_k(g)) = 1 − 2/c_k(g) + 1/(24c_k(g)) ≤ 1 − 1/c_k(g)".

**Lemma 24** (p. 21). "For all non-degenerate A ∈ R^{m×n}, p > 0 with p ≠ 2, and
v ∈ R^m [sic: R^m_{>0}], let w(v) := w_p(VA) where V = Diag(v). Then, for
Λ_v := Λ(W^{1/2−1/p}VA) and W_v := Diag(w(v)) we have
J_w(v) = 2W_v(W_v − (1−2/p)Λ_v)^{-1}Λ_vV^{-1}."

**Lemma 25** (p. 22). "Under the setting of Lemma 24 for any v ∈ R^m_{>0} and
h ∈ R^m, we have that ‖W_v^{-1}J_w(v)h‖_{w(v)} ≤ p·‖V^{-1}h‖_{w(v)} (4.4), and that
‖[W_v^{-1}J_w(v) − pV^{-1}]h‖_∞ ≤ p·max{p/2,1}·‖V^{-1}h‖_{w(v)} (4.5)."

**Lemma 49** (p. 48). "D_wσ(WA)[h] = 2Λ(WA)W^{-1}h."
**Lemma 23** (p. 20) gives ∇𝒱 = −W^{-1}σ_w and ∇²𝒱 = W^{-1}(Σ_w − (1−2/p)Λ_w)W^{-1}.
Its statement reads "Λ_w := P(W^{1/2−1/p}A)" [sic]; it must be Λ(·).

(b) Substitution and checks.

* **Consistency for the note's parameters.** As in LS, the operator norm is
  at most p(1+1/C). With p = 1−1/L_0 we need p(1 + 1/C_N) ≤ 1 − 1/k = 1 − 1/(2L_0).
  Since p(1+1/C_N) = 1 − 1/L_0 + p/C_N ≤ 1 − 1/L_0 + 1/C_N, a sufficient
  condition is 1/C_N ≤ 1/(2L_0), that is C_N ≥ k = 2L_0. C_N = 48k qualifies. ✓ So "c_k ≤ k" holds with
  the note's fixed C_N. LS's own derivation needs c_s ≥ 1 (WLOG) and C_norm ≥ 24c_k.
* **Regularisation.** LS applies Lemma 25, which is stated in the w(v)-norm,
  directly in the g-norm. This is valid because g = w + c_0 ≥ w. The two needed
  comparisons are:
  * ‖G^{-1}u‖_g² = Σu_i²/g_i ≤ Σu_i²/w_i = ‖W^{-1}u‖_w²;
  * |(G^{-1}u)_i| ≤ |(W^{-1}u)_i|;
  * and the right side satisfies ‖V^{-1}z‖_w ≤ ‖V^{-1}z‖_g.
  ✓ This holds for **any** c_0 ≥ 0, so the repair of G1 does not disturb consistency.
* **Chain rule.** Write B(x) = diag(φ''(x)^{-1/2})A. The log-scaling derivative
  is dy_i/dx_i = −φ'''/(2φ''), so G^{-1}J_gΦ''^{-1/2}h = G^{-1}WK(ρ⊙h), where
  ρ_i = −φ_i'''/(2φ_i''^{3/2}). Then |ρ_i| ≤ 1 by self-concordance (F1). ✓
* **Lemma 24 formula, recomputed.** For f(v,w) = −(1/γ)log det(AᵀVW^γVA) + Σw
  with γ = 1−2/p:
  * ∂²f/∂w_i∂w_j = W^{-1}(Σ − γΛ)W^{-1}. This needs Λ = Σ − P^{(2)} (typo above).
  * ∂²f/∂w_i∂v_j = −(2/w_i)Λ_ij/v_j.
  * Hence J = 2W(Σ−γΛ)^{-1}ΛV^{-1}, with Σ = W at the fixed point. ✓
* **Lemma 25, recomputed.** With c := −γ = 2/p − 1 ≥ 0 and β := 2/(1+c) = p,
  the projection-Jacobian bound applies: for K := 2(Σ + cΛ)^{-1}Λ,
  ‖Kh‖_σ ≤ β‖h‖_σ and ‖Kh − βh‖_∞ ≤ β‖h‖_σ. So (4.4) holds with factor p. (4.5) holds with
  factor p, since max{p/2,1} = 1 for p ≤ 2. ✓

**Lemma 16 proof slip (gap G2).**

* LS bounds the integrand operator norm ‖G_t^{-1}J(x_t)Φ_t''^{-1/2}‖_{g_0+∞} by
  (1+2ε)‖…‖_{g_t+∞}.
* Changing the base norm of an *operator* norm costs the norm-equivalence
  factor *twice*: N_0(Mx) ≤ cN_t(Mx) ≤ c‖M‖_tN_t(x) ≤ c²‖M‖_tN_0(x).
* With LS's factor c = 1+2ε, the closing inequality (1+2ε)²(1−a)/(1−ε) < 1−a+4ε
  *fails* for small a = 1/c_k and any ε > 0, since the left side is ≈ (1−a)(1+5ε).
  This was checked on a grid.

**Repair.** Use the sharp equivalence N_{g_s} ≤ e^{u/2}N_{g_t}, where
u = ‖log g_s − log g_t‖_∞ ≤ Q̄(θ) ≤ (1−a+4ε)ε. The weighted ℓ₂ part scales by
√(max g_s/g_t). The closing inequality becomes
`e^{(1−a+4ε)ε}(1−a)/(1−ε) < 1−a+4ε` for ε ∈ (0,1/10] and a ∈ (0,1]. Hand proof:

* e^{1.4ε} ≤ 1+1.4ε+1.96ε² ≤ 1+1.6ε, and 1/(1−ε) ≤ 1+1.12ε.
* Their product is ≤ 1+2.9ε.
* Hence the left side is ≤ (1−a)+2.9ε < 1−a+4ε. ✓

The conclusion of Lemma 16, and hence `eq:gmove`, stands.

The "(1+2ε)" norm-comparison clause of Lemma 16 is also true but unused by the
note. In the bootstrap, ‖q(s)−q(t)‖_∞ ≤ Q̄(t)−Q̄(s) ≤ Q̄(θ) holds via the
integral triangle inequality. ✓

**Substitution into eq:gmove.** Take Δ = d and ε = v = N_{g(x)}(S(x)d) ≤ 1/10.
Then c_k ≤ k gives (1 − 1/c_k + 4v)v ≤ (1 − 1/k + 4v)v. ✓ The hypothesis
"segment interior" is LS's "x_t ∈ Ω° for all t". ✓ Implicit hypothesis: g must
be C¹ along the segment, which needs gap G3 closed.

(c) Gaps: G2 (proof slip, repaired), G3 (differentiability of Lewis weights
not proved in LS), G4 (Lemma 25 norm transfer to g, repaired above), and G5
(typos).

### F5. `eq:wmove` (LS Lemma 17)

(a) **Lemma 17** (p. 16). "Let v, w ∈ R^m_{>0} such that ε = ‖log(w) − log(v)‖_{w+∞} ≤ 1/10.
Then for x ∈ Ω° we have δ_t(x,v) ≤ (1+4ε)(δ_t(x,w) + ε)."

(b) Map v ↦ w̃. The note's `a = N_w(log w̃ − log w)` is measured in the old
weight w, exactly as in LS. ✓ The proof checks out:

* e^{−ε} ≤ v/w ≤ e^ε ≤ (1+ε)² for ε ≤ 1.
* N_v ≤ (1+ε)N_w.
* Keep η_w and split (tc + vφ' − Aη)/(v√φ'') = (w/v)·[(tc + wφ' − Aη)/(w√φ'')] + (v−w)φ'/(v√φ'').
* The first term is ≤ (1+ε)²δ.
* The second term uses |φ'|/√φ'' ≤ 1. Also |(v−w)/v|_i ≤ |u_i|e^{|u_i|}, where
  u = log v − log w, so its N_w-norm is ≤ e^εε.
* Total: (1+ε)³(δ+ε) ≤ (1+4ε)(δ+ε), since 3ε+ε² ≤ 1. ✓
* LS writes `c` for `t·c` (typo, harmless).

This holds for **any** C_N > 0, any positive v and w, and any x. It uses no
Lewis-weight fact.

(c) No gap.

### F6. `eq:tchange` (LS Lemma 14)

(a) **Lemma 14** (p. 14). "For all {x,w} ∈ Ω° × R^m_{>0}, t > 0 and α ≥ 0, we have
δ_{(1+α)t}(x,w) ≤ (1+α)δ_t(x,w) + α(1 + C_norm√‖w‖_1)."

(b) The note's statement is two-sided: |t'/t−1| ≤ α. LS's proof works verbatim
with λ = t'/t ∈ [1−α, 1+α]:

* Scale η_t by λ.
* The residual is λ·(old) + (1−λ)wφ'/(w√φ''), giving ≤ (1+α)δ + α·N_w(φ'/√φ'').
* Here N_w(φ'/√φ'') ≤ 1 + C_N√(Σw) ≤ 1 + C_N·2√r ≤ T_0, using Σw ≤ 4r. ✓
* LS has the sign typo "+Aη_t".

(c) This is a minor citation extension, not a gap. Record the two-sided version
as a lemma.

### F7. Lewis weights: existence, uniqueness, fixed point, contraction, floor (Def. 20, Lemma 22, note `lem:lewis`, `eq:lewisfloor`)

(a) Lemma 22 is quoted in F2.

**LS proof for p < 2.**

* Restrict to w ≤ 1 using ∂_if > 0 when w_i > 1.
* "If j ∈ argmin_i w_i … [σ_w]_j ≥ σ(A)_j and therefore if w_j < σ(A)_j we have
  ∂f/∂w_j < 0. Therefore … inf_{w_i>0} f(w) = inf_{1>w_i≥σ(A)_i} f(w)."
* Then compactness, strict convexity (Lemma 23), and ∇f = 0 ⟺ w = σ(W^{1/2−1/p}A).

(b) The LS restriction-to-box step is incomplete as written (gap G9, minor).
The argmin-coordinate argument only shows that the *smallest* coordinate wants
to increase. Reaching inf over {w_i ≥ σ_min} needs a "water-filling" path that
raises all minimal coordinates together. Along it the directional derivative
Σ_{j∈argmin}∂_jf is negative.

It is simpler to take existence and uniqueness from the note's contraction:

* T_B(v)_i = (b_iᵀ(BᵀV^{1−2/p}B)^{-1}b_i)^{p/2}.
* With a = 1−2/p < 0 and E = ‖log v − log u‖_∞, the Loewner factors are e^{±|a|E}.
* Taking the inverse and then the power p/2 gives factor (p/2)|a| = 1−p/2 < 1
  for all p ∈ (0,2). ✓
* Banach's fixed-point theorem in log-coordinates gives a unique fixed point.
* The fixed point satisfies w = σ(W^{1/2−1/p}B): w_i^{2/p} = b_iᵀM^{-1}b_i ⟺ w_i = w_i^{1−2/p}b_iᵀM^{-1}b_i. ✓
* Any Lewis vector is a fixed point. Uniqueness among positive vectors therefore follows. ✓

The note's iteration formula is
log T_B(v)_i = (p/2)log σ_i(V^{1/2−1/p}B) + (1−p/2)log v_i. ✓
"Adding 2r/M cannot increase the log error" holds because
|log(a+c)−log(b+c)| ≤ |log a−log b|. ✓

`eq:lewisfloor`:

* If j minimises w, then W^a ⪯ w_j^a I because a < 0.
* So w_j = w_j^a b_jᵀ(BᵀW^aB)^{-1}b_j ≥ b_jᵀ(BᵀB)^{-1}b_j ≥ ‖b_j‖²/λ_max(BᵀB).
* With ‖b_j‖² ≥ a_0²s_*²/4 and λ_max ≤ Σ‖b_i‖² ≤ 2MU², this gives
  q_* = a_0²s_*²/(8MU²). ✓

(c) G9 (minor, avoidable).

### F8. Attainment of the centrality minimum and frozen-weight centers (LS Lemma 10 proof, Lemma 41, note `lem:center`)

(a) LS Lemma 10's proof says "letting η_q be such that ‖y‖_Q = ‖…‖". It assumes
the minimum is attained. **Lemma 41** ([46, Thm 4.2.7], p. 35) says: "Let x*
denote an optimal solution … and x_t = argmin f_t(x,w) … Then cᵀx_t(w) − cᵀx* ≤ ‖w‖_1/t."
It assumes the weighted center x_t exists.

(b) Neither attainment nor existence is proved in LS. Both are elementary.

* **Attainment of δ_t:** ν ↦ N_w(r₀ − Bν) is a continuous convex function. It is
  coercive when B = diag(1/(w√φ''))A is injective, which holds because A has
  full column rank. So it attains its minimum on a closed ball. (Alternatively,
  the distance to a finite-dimensional subspace is attained.)
* **Weighted center:** F(y) = t·cᵀy + Σw_iφ_i(y_i) on the relatively open,
  bounded slice {Aᵀy = b, ℓ < y < u}. That set is nonempty because it contains
  x. F is continuous, F → +∞ at the boundary (φ_i → ∞), and F is strictly
  convex since φ_i'' > 0. Hence there is a unique minimiser x̄, characterised by
  tc + Wφ'(x̄) ∈ im A.
* The note's `lem:center` quantitative bound is the note's own argument. It
  uses Newton iterates, `eq:projection`, and `eq:gmove`. Check: v ≤ √(5/4)·γδ_j ≤ 1.19δ_j,
  and the change is (1−1/k+4v)v ≤ 1.4v ≤ 1.7δ_j ≤ 4δ_j. ✓ The total over the
  iterates is ≤ 8δ₀, and the weight window holds since e^{1/20+8Δ} ≤ 5/4. ✓
* Duality gap (Lemma 41): Lemma 9 gives the sum identity. ✓ Note's use:
  cᵀx̄ − OPT ≤ Σw/t_+. OPT is attained because the box is compact and the LP is
  feasible. ✓

(c) G8: missing in LS; elementary.

---------------------------------------------------------------------------

## 4. Constant and parameter checks (summary)

| Check | Result |
|---|---|
| p = 1−1/L_0 ∈ [1/2, 1) for L_0 ≥ 2 | ✓ |
| k = 2L_0 = 2/(1−p), matching LS c_k ≤ 2/(1−p) | ✓ exact |
| M^{1−p} ≤ 2 because L_0 ≥ log₂(4M) | ✓ (LS's "log(4m)" must be base 2; with ln the bound is 2e) |
| c_s ≤ 4 for g = w_p + 2r/M | **✗ false in general (G1)**. Repaired: c_s ≤ 16 for c_0 ≤ 1/(2M) |
| C_N = 48k = 24·√4·k | ✓ given c_s ≤ 4. Under the repair, use Lemma 13′ with 48k, or C_N ≥ 91k with Lemma 13 |
| consistency c_k = k needs C_N ≥ k | ✓ (48k) |
| γ = 1+√(2c_s)/C_N ≤ 1+1/(16k) | ✓ iff c_s ≤ 4.5. Lemma 13′: needs c_s ≤ 144k |
| (5/4)³ ≤ 2 in Lemma 13 | ✓ 1.953 |
| Lemma 16: (1+2ε) operator-norm transfer | **✗ slip (G2)**; repaired with e^{u/2} |
| Lemma 17: (1+ε)³ ≤ 1+4ε for ε ≤ 1/10 | ✓ |
| Lemma 15 aux: ((1−t)^{-2}−1)(1−t)^{-1} ≤ 4t for t ≤ 1/5 | ✓ (not used by note) |
| `lem:newton` constant 8δ²+4η | ✓ |
| Σg = 3r, which needs rank(A) = r | ✓ with explicit hypothesis |

---------------------------------------------------------------------------

## 5. Gaps and repairs

1. **G1 (major; mathematical and citation).** LS Theorem 29's claim
   "c_s(g) ≤ 2m^{1−p}" is false for g = w_p(A_x) + c_0 with c_0 > 0. The
   numerical counterexample is in §3 F3 and `num/counterexample.py`. The note's
   `eq:projection` (γ = 1+1/(16k)) relies on it with c_0 = 2r/M. All
   downstream uses of γ ≤ 17/16 and of the 1/(16k) margin are affected:
   `lem:newton`, `prop:batch`, `lem:center`, and the final phase.
   * **Repair (i).**
     * The regularisation is exactly c_0 = 1/(2M̄), where M̄ ≥ M is a public
       polynomial upper bound (M̄ = M when M is known from the transcript). An upper
       bound on c_0 alone does not give the weight floor.
     * L_0 is chosen from M̄.
     * The maintained floor is w_i ≥ 1/(4M̄), and Σg ≤ r + 1/2.
     * Lemma S (c_s ≤ 16) and Lemma 13′ give q ≤ 32 within the 4/5–5/4 window, so
       ‖P‖_{N_w} ≤ √(1 + 32/(48k)²) ≤ 1 + 1/(144k²) ≤ 1 + 1/(16k). C_N = 48k is kept.
     * The sensitivities 26.8709 and 20.1586, against the claimed 3.5588, were
       reproduced independently.
     * The downstream analysis must recompute w_min, s_*, q_*, `eq:normalbounds` and P(𝒩), and the
       cost-switch parameter. The note's (V) (line 676 of the note) becomes
       20T₀MU². Its factor-4r increase adds only O(log r) to the logarithmic
       path-length bound.
     * The rejected alternative (ii) was a new proof of `eq:projection` for
       c_0 = 2r/M on the incidence-LP class.
2. **G2 (proof slip, repaired).** In LS Lemma 16, the operator-norm change of
   base norm uses one factor (1+2ε) instead of two. The conclusion holds with
   the sharp e^{u/2} factor; see the hand proof in F4(b). Any formal proof must
   follow the repaired argument.
3. **G3 (missing proof).** Differentiability (C¹) of p ↦ w_p(VA) in V is
   assumed in LS Lemma 24 ("taking derivative … on both sides"). It must be
   established by the IFT. The Hessian ∇²_{ww}f = W^{-1}(Σ − (1−2/p)Λ)W^{-1} is
   PD; alternatively, the contraction gives invertibility of I − ∂T. Both
   `eq:gmove` and Definition 12's "differentiable g" depend on this.
4. **G4 (minor; repaired).** Theorem 29's consistency proof applies Lemma 25,
   which is stated in the w-norm, in the g-norm. The comparison g ≥ w makes it
   valid (F4(b)). Record it as an explicit lemma.
5. **G5 (typos; no effect).** These are:
   * Lemma 23's statement defines Λ_w as P(·), but it should be Λ(·).
   * Lemma 14's proof has "+Aη_t".
   * Lemma 17's proof has "c" for "t·c".
   * Lemma 26's proof has "(1+α)m" for "(1+1/α)m".
   * Definition 12 has "c_γ" in the tuple.
   * Lemma 13 eq. (gamma_1) has a stray term.
   * Theorem 29 has "x ∈ R^m_{>0}".
6. **G6 (citation extension).** `eq:tchange` uses Lemma 14 for decreasing t.
   The proof extends verbatim, but it must be stated two-sided.
7. **G7 (log base).** LS's "p = 1−1/log(4m) ⇒ c_s ≤ 4" needs log base 2. The
   note uses log₂ explicitly, so it is unaffected. Do not cite LS's numeric
   corollary.
8. **G8 (missing in LS).** LS does not prove attainment of the
   minimum in δ_t (Lemma 10 proof), existence or uniqueness of weighted centers
   (Lemma 41, `lem:center`), or existence of the exact Newton direction. All
   three are elementary (F8).
9. **G9 (minor; avoidable).** The box-restriction step in LS Lemma 22's
   existence proof for p < 2 needs a water-filling argument. Use the
   contraction (F7) instead.
10. **G10 (arithmetic error; found in review).** Theorem 29's proof asserts
    α/(1+α) = (2−2p)/(2+p) ≤ 1−p with α = 2/p − 2. In fact α/(1+α) = 2(1−p)/(2−p),
    which exceeds 1−p for every p ∈ (0,1). Lemma 26 is correct; only this step is
    wrong. So c_s(w_p) ≤ 2m^{1−p} fails **even with c_0 = 0**.
    * Exact counterexample (`num/exact_c0_zero.py`, rational arithmetic): p = 1/2,
      one column with one entry 1 and 8000 entries 1/400.
      * The Lewis weights are 1/401 and 1/8020.
      * The first-row sensitivity is 401/2, which exceeds 2m^{1−p} = 2√8001 ≈ 178.9.
    * The correct bound from Lemma 26 is 2m^{2(1−p)/(2−p)}. For p = 1 − 1/L_0 this
      is 2m^{2/(L_0+1)} ≤ 8 when L_0 ≥ log₂(4m).
    * Lemma S does not use this step.
11. **Hypotheses to carry explicitly.** These are:
    * A has full column rank r (from `+I_r`) and no zero rows;
    * box widths ≤ U;
    * 1/2 ≤ p < 1;
    * C_N ≥ k for consistency, and C_N satisfying the γ condition;
    * the weight window 4/5–5/4 for `eq:projection`;
    * the segment interior and v ≤ 1/10 for `eq:gmove`;
    * a ≤ 1/10 for `eq:wmove`.
12. **Not audited here:** the note's own later lemmas (`lem:chase`,
    `prop:batch`, `lem:numeric`, `lem:support`). Only their uses of the LS
    facts were checked.

---------------------------------------------------------------------------

## 6. Reproducibility

`num/` (Python, numpy 2.4.6 / scipy 1.17.1; run from that directory):

* `lw.py` contains the Lewis fixed-point iteration (the note's T_B), the
  sensitivity c_s, and L_0.
* `counterexample.py` is the G1 counterexample, with the fixed-point residual printed.
* `t1.py` and `t2.py` are random and Nelder–Mead searches. Small instances
  satisfy the bound.
* `t3.py` is the block family showing c_s growth with M.
* `t4.py` and `t5.py` cover incidence-structured matrices.
* `t6.py` checks the repaired regularisation c_0 = 1/(2M); the maximum
  observed is 3.1, below the proved bound 16.
