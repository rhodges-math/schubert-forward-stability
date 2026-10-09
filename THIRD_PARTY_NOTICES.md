# Third-party material

One source file is adapted from Mathlib. All other Lean sources under
`SchubertForwardStability/` were written for this formalization or for the author's
flag-variety library (below).

## Adapted from Mathlib

- `SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean` is adapted from Mathlib's
  `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` at commit `b2bf051`
  (copyright 2025 Rémy Degenne, Apache License 2.0). It is modified so that the random variables
  of a sequence may live on probability spaces that vary with the index. Its header keeps the
  original copyright notice and states the modification.

## Files from the flag-variety library

The 11 files in `SchubertForwardStability/TypeA/` are the files of `Schubert/TypeA/` in the
flag-variety library, version 0.1.0, published in
[rhodges-math/rs-counterexample](https://github.com/rhodges-math/rs-counterexample) by the same
author under the Apache License 2.0. Only the module prefix of their imports differs.

## Downloaded dependencies

These packages are downloaded by Lake at the revisions pinned in `lakefile.toml` and
`lake-manifest.json`. They are not included in this repository and keep their own licenses.

- Mathlib: [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4),
  commit `b2bf051988bf69448bce88722cc09a05fea31662` (Apache License 2.0).
- Its own dependencies, pinned in `lake-manifest.json`: plausible, LeanSearchClient,
  importGraph, proofwidgets, aesop, Qq, batteries (Apache License 2.0) and Cli (MIT License).

## Project license

This repository is licensed under the Apache License 2.0; see [LICENSE](LICENSE) and
[NOTICE](NOTICE).
