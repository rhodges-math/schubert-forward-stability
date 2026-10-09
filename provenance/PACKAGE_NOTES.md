# Source scope and verification

This repository contains the 452-module Lean library `SchubertForwardStability`: the root
module, 180 modules of `SchubertForwardStability/Permutations/` (finitary permutations), 78 of
`SchubertForwardStability/SchubertPolynomials/` (Schubert polynomials), 34 of
`SchubertForwardStability/LimitTheorems/` (limit theorems), 81 of
`SchubertForwardStability/StrongMixing/` (strong mixing), 11 of `SchubertForwardStability/TypeA/`
(files of the flag-variety library) and 67 of `SchubertForwardStability/Paper/` (the paper). The
general libraries never import `SchubertForwardStability/Paper/`. The limit theorems library
imports only Mathlib, the strong mixing library imports it, the Permutations library imports the
TypeA files, and the Schubert polynomials library imports the Permutations library and the TypeA
files. All local imports are included, and every module is imported by the root module, directly
or indirectly. Mathlib (`b2bf051`) is a pinned public Lake dependency and is not included.

## Source preparation

The sources are those of the development tree. Two kinds of files differ from their origin:

- the 11 files of `SchubertForwardStability/TypeA/` are the files of `Schubert/TypeA/` of the
  flag-variety library 0.1.0 (rs-counterexample), with the module prefix `Schubert.TypeA` of their
  imports replaced by `SchubertForwardStability.TypeA`;
- `SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean` is adapted from Mathlib's
  `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`; see `THIRD_PARTY_NOTICES.md`.

`LOCAL_MODULES.json` records, for every module, the path and hash in this release.
`LIBRARY_MANIFEST.json` (in the repository root) records the version, folders and file hashes of
the four general libraries and of the TypeA files.

## Verification records

- `BUILD_CHECK.json`: the full build of this snapshot with `build.py`, in which every local module
  was compiled; the whole-environment axiom audit (the axioms reachable from all declarations of
  the local modules); and the Batteries linters over all of them.
- `ENDPOINT_AUDIT.txt`: the output of `SchubertForwardStability/Paper/Audit.lean`.
- `DEPENDENCIES.json`: the pinned Lake packages.
- `LOCAL_MODULES.json`: the module inventory.
