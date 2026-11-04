# Changelog

## 0.1.1

- `CutQueryComplexity.Model.Complexity` imports `Mathlib.Order.Lattice.Nat`
  in place of `Mathlib.Data.Nat.Lattice`, which this Mathlib deprecates as an
  empty shim. No statement or proof changes.

## 0.1.0

- First public release of the `CutQueryComplexity` library.
- Requires Lean and Mathlib 4.35.0-rc2 and `QuantumQueryComplexity` `v0.1.0`;
  exact dependencies are in the manifest.
- `import CutQueryComplexity` imports every library module;
  `CutQueryComplexity.Classical` excludes quantum imports.
- `docs/COVERAGE.md` maps the 48 global, s-t, and all-pairs minimum-cut
  problems to their Lean theorems; 42 are proved. `CutQueryComplexity.Coverage`
  exports the coverage endpoints.
- Two axiom audits, `CutQueryComplexityChecks.lean` and
  `CutQueryComplexityChecks/Endpoints.lean`, cover disjoint module lists.
- `papers/` has a folder for each of the four preprints whose results are
  formalized (P1–P4), with its PDF and a Lean reader for its headline theorems;
  P4's folder also holds a supporting audit note; `docs/lee-sidford-audit/` holds the audit of the
  Lee–Sidford facts used by the stable implicit LP.
- Vendors the matrix Bernstein inequality from lean-stat-learning-theory
  under `SLT/`, with its license and patch record.
