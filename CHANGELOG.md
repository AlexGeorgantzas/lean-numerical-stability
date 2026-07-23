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
- The Algorithms aggregate imports the Sylvester family through one umbrella,
  reducing its direct imports from 490 to 463, and its imports are sorted and
  deduplicated by a repository-owned formatter.
- `NumStability.Higham` now forwards to the canonical
  `NumStability.Source.Higham` surface.
- Mathlib is pinned to an exact revision and `lake test` has an explicit test
  driver.

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
