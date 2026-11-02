# Notes

These notes accompany the library. The authoritative list of proved
statements is in [`CutQueryComplexityChecks.lean`](../CutQueryComplexityChecks.lean)
and [`CutQueryComplexityChecks/Endpoints.lean`](../CutQueryComplexityChecks/Endpoints.lean).
The preprints whose results are formalized here are in [`papers/`](../papers).

| Note | Topic |
| --- | --- |
| [COVERAGE.md](COVERAGE.md) | The Lean theorem and source for each of the 48 minimum-cut problems |
| [ALL_PAIRS_FORMALIZATION.md](ALL_PAIRS_FORMALIZATION.md) | Randomized all-pairs minimum cuts of a simple graph, following Kenneth-Mordoch–Krauthgamer, and the repairs to its proof and to the friendly-cut sparsifier it imports |
| [WEIGHTED_SPARSIFICATION.md](WEIGHTED_SPARSIFICATION.md) | Weight-independent cut sparsification following Plevrakis–Ragavan–Weinberg: proof design, source correspondence, and the Lean modules |
| [lee-sidford-audit/AUDIT.md](lee-sidford-audit/AUDIT.md) | The audit of the Lee–Sidford facts used by the stable implicit incidence LP, checked against the source, with the gaps found (including a counterexample to a sensitivity bound) and numerical checks in `lee-sidford-audit/num/` |
