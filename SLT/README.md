# Vendored matrix Bernstein inequality (SLT)

These five files are copied from
[lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory),
commit `d0f506f0a695018265dccb33bcb05e2f5ca1c876` (2026-07-15). They are the import closure of
`SLT/RMT/MatBern.lean`, which proves the finite-family matrix Bernstein inequality
`RMT.matrix_bernstein_inequality_hdp_all` in the L2 operator norm.

| File | Upstream path | Changed |
| --- | --- | --- |
| `MatrixInfra/Basic.lean` | `SLT/MatrixInfra/Basic.lean` | 1 edit |
| `MatrixInfra/CourantFischer.lean` | `SLT/MatrixInfra/CourantFischer.lean` | no |
| `MatrixInfra/MatCalc.lean` | `SLT/MatrixInfra/MatCalc.lean` | 3 edits |
| `RMT/Lieb.lean` | `SLT/RMT/Lieb.lean` | no |
| `RMT/MatBern.lean` | `SLT/RMT/MatBern.lean` | 2 edits |

Copyright (c) 2026 Yuanhe Zhang; authors Yuanhe Zhang, Jason D. Lee, Fanghui Liu. Released
under the Apache License 2.0 ([LICENSE](LICENSE)); every file keeps its original header.

## Modifications

Upstream builds against Lean and Mathlib `v4.32.0`. This repository uses Lean `v4.35.0-rc2`
with Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, inherited from
QuantumQueryComplexity. Six edits adapt the files to that version; the full diff is in
[PATCHES.diff](PATCHES.diff). None changes a statement.

1. `Basic.lean`, `orthonormal_leftSingularVector_of_singularValues_ne_zero`: `simp` no longer
   reduces `if i = i then 1 else 0`; insert `rw [if_pos rfl]` before it.
2. `MatCalc.lean`, `rayleighQuotient_mono_of_le`: `LinearMap.le_def` now has implicit arguments;
   `(LinearMap.le_def A B).mp hAB` becomes `LinearMap.le_def.mp hAB`.
3. `MatCalc.lean`, `realMatrixToCStarMatrixStarAlgHom`: the coercion of
   `CStarMatrix.ofMatrixStarAlgEquiv` to a star-algebra homomorphism no longer elaborates; use
   `.toStarAlgHom`.
4. `MatCalc.lean`, a `calc` step after `simp [W, Matrix.diagonal_mul, ...]`: simp no longer
   rewrites the diagonal products; add `erw [Matrix.diagonal_mul, Matrix.mul_diagonal]`.
5. `MatBern.lean`: `Measure.isProbabilityMeasure_map` was removed, since the map of a
   probability measure is now an instance; use `infer_instance`.
6. `MatBern.lean`: `aemeasurable_pi_lambda _ hX_ae` becomes `AEMeasurable.of_eval hX_ae`.

## Audit

All five modules are in the repository's transitive axiom audit
(`CutQueryComplexityChecks.lean`); the only axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The files contain no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
`implemented_by`, `native_decide`, or `extern`. Upstream style linters are not enabled here.
