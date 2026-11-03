# Papers

Preprints whose results are formalized in this library, one folder each. Each paper has an
appendix that maps its numbered results to the Lean declarations that state them. Each folder
also has a Lean reader (its `README.md`): a guide to the Lean statements of the paper's headline
theorems, with a file `VerifyHeadlineTheorems.lean` that checks them. The top-level
[README](../README.md) and [docs/COVERAGE.md](../docs/COVERAGE.md) cite the papers as P1–P4.

| | Paper | Main results | Lean reader |
| --- | --- | --- | --- |
| P1 | [Finding and Certifying Weighted Minimum Cuts with Cut Queries](P1/finding-certifying-weighted-minimum-cuts.pdf); [arXiv:2611.03107](https://arxiv.org/abs/2611.03107) | Near-linear minimum-cut certificates; deterministic weighted global minimum cut, and all minimum cuts, in `O(n^{3/2} log³ n (log log n)²)` queries; learning a tree cut sparsifier | [P1](P1) |
| P2 | [Deterministic s–t and All-Pairs Minimum Cuts with Subquadratic Cut Queries](P2/deterministic-st-all-pairs-minimum-cuts.pdf) | Deterministic minimum s–t cut of a simple graph, with a maximum flow, in `O(n^{3/2} log³ n)` queries; deterministic all-pairs minimum cuts in `O(n^{5/3} log⁵ n)` queries | [P2](P2) |
| P3 | [Directed Cut Certificates through Fractional Forests and Shared Flows](P3/directed-cut-certificates.pdf) | Directed global minimum-cut certificates with `O(n^{5/3})` queries for real capacities and `O(n^{3/2} √log n)` for unit capacities (the Lean statement removes the logarithm); linear-size s–t certificates | [P3](P3) |
| P4 | [Subquadratic Cut-Query Algorithms for Directed Minimum Cuts](P4/subquadratic-directed-minimum-cuts.pdf) | For simple digraphs: deterministic minimum s–t cut in `O(n^{5/3} log² n)` queries; randomized minimum s–t cut in `Õ(n^{3/2})` and global minimum cut in `Õ(n^{7/4})` queries | [P4](P4) |

## Authorship and AI use

P2–P4 are preliminary drafts. Their results were obtained by prompting Codex
GPT-6 Astra, which also wrote them. Their main theorems are verified in Lean 4;
their author has not yet reviewed the prose proofs. The Lean proofs of their results were developed by Claude Opus
5.5 and audited by GPT-6 Astra. Each paper says this on its title page and in
an "AI use" section; its Lean appendix lists the machine-checked declarations
and notes where they differ from the paper's statements.

## Supporting notes

| Note | Contents |
| --- | --- |
| [Audit of the External Implicit Incidence LP Theorem](P4/supporting/implicit-lp-audit.pdf) | An audit of Theorem 5.3 of the anonymous directed-reachability note, cited by P4 as [LPAudit26]; its exact checks are in [`P4/supporting/implicit_lp_audit_checks.py`](P4/supporting/implicit_lp_audit_checks.py) |

The audit of the Lee–Sidford facts, cited by P4 as [LSAudit26], is in
[`docs/lee-sidford-audit/`](../docs/lee-sidford-audit).

## License

The PDFs in these folders are preprints. They are not covered by the Apache-2.0
license of the code. P1 is licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), as on arXiv
([arXiv:2611.03107](https://arxiv.org/abs/2611.03107)). For P2–P4, all rights are reserved by
their authors.
