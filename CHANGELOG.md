# Changelog

All notable user-facing changes to NumStability are recorded here. The project
follows semantic versioning for its public module paths and declaration API.

## [Unreleased]

### Added

- Canonical `NumStability.Source` and `NumStability.Source.Higham` entry points.
- Canonical Chapter 14, Chapter 24, and Chapter 25 source trees with
  independently compiled compatibility imports.
- A canonical Chapter 4 source tree for the §4.1 six-term pairwise example and
  Problem 4.3.
- A reusable `NumStability.Algorithms.LinearSystems.Triangular` family entry
  point.
- Reusable `NumStability.Analysis.Summation.Signs` and
  `Summation.ErrorBounds` leaves, and a declaration-free summation-analysis
  umbrella.
- Reusable `Summation.Recursive.Core`, `Summation.Pairwise.Core`, and
  `Summation.Tree.Chain` modules with complete family umbrellas and isolated
  import tests.
- Reusable insertion-summation `ActiveList`, `Executor`, `Schedule`,
  `RunningError`, and `ScheduleExecution` leaves, plus a canonical Chapter 4
  Section 4.1 insertion-example source module.
- A complete, declaration-free `NumStability.Algorithms.Sylvester` family
  aggregate and isolated aggregate/import smoke tests.
- Architecture, naming, compatibility, and layout checks for repository
  migrations.
- Explicit Apache-2.0 license text, per-file provenance policy, Mathlib
  attribution, citation metadata, and a provenance CI check.

### Changed

- Historical source and triangular-system paths are now import-only forwarding
  modules. They remain supported until a declared breaking release.
- `NumStability.Analysis.Summation` is now an import-only complete aggregate;
  reusable consumers import its semantic leaves directly. `ErrorBounds` is now
  classified as reusable rather than mixed.
- The historical `Summation.Tree.RecursiveBridge` path now forwards to the
  semantic `Summation.Tree.Chain` module.
- `Summation.Insertion` is now a declaration-free complete family aggregate;
  production consumers import its narrow reusable layers, while the historical
  `InsertionSum` path retains the complete reusable and source surface.
- The Algorithms aggregate imports the Sylvester family through one umbrella
  (a step that, at the time, reduced its direct imports from 490 to 463), and
  its imports are sorted and deduplicated by a repository-owned formatter. The
  checked ceilings in
  [`docs/architecture/layout-exceptions.json`](docs/architecture/layout-exceptions.json)
  now cap the aggregate at 446 direct imports below `NumStability`, including
  44 below `NumStability.Analysis` and 73 below `NumStability.Source`; these
  are enforced ceilings, not the live import count.
- `NumStability.Higham` now forwards to the canonical
  `NumStability.Source.Higham` surface.
- Mathlib is pinned to an exact revision and `lake test` has an explicit test
  driver.
- The in-progress 2026-08 reorganization-completion phase canonicalized the
  remaining historical Higham surfaces, including the Chapter 9, 11, 13, 14,
  20, 21, and 28 source trees, the R09 TestMatrices canonicalization, and the
  R10 RandNLA canonicalization. Historical paths remain supported as 712
  import-only forwarding modules over 2,364 canonical targets, and the
  executable tier inventory classifies 2,928 of 2,928 production modules with
  0 unclassified and 0 mixed; CI forbids regression from that state.
- The reviewed I01 wave (R0014/R0015) landed on `main` at
  `9fbb1e36bcc85f866893e902cbe206ba468a65b0`: the Chapter 2 Problem 2.9
  double-rounding counterexample umbrella was split into declaration-free
  aggregates over source leaves, `Source.Higham.Chapter19.Core` was retargeted
  to canonical Householder QR imports, and the retained-production
  compatibility-exception mechanism was retired from
  `tools/architecture/check_compatibility.py`.
- Repository reorganization is now governed by
  [`docs/architecture/PROCESS.md`](docs/architecture/PROCESS.md): per-batch
  static gates, plain-language recorded review, and fast-forward-only `main`.

### Deprecated

- Historical source, triangular-system, and root Higham import paths remain
  supported compatibility paths. Their mappings and removal policy are listed
  in [`docs/architecture/COMPATIBILITY.md`](docs/architecture/COMPATIBILITY.md);
  removal requires a declared breaking release.

### Removed

- A tracked Python bytecode artifact from the experiments tree.
- The stale generated benchmarking PDF; its TeX source and rebuild command
  remain tracked.

## [0.1.0] - 2026-07-21

- Initial tagged NumStability release.

[Unreleased]: https://github.com/AlexGeorgantzas/lean-numerical-stability/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/AlexGeorgantzas/lean-numerical-stability/releases/tag/v0.1.0
