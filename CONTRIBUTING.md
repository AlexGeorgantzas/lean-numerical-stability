# Contributing to NumStability

The `higham_v01` branch is a release package. Broad development and
reorganization should happen on `main`; changes here should be limited to
release-critical fixes that preserve the published API.

## Before changing modules

Place source-independent mathematics in `FloatingPoint`, `Analysis`, or a
semantic `Algorithms` family. Put numbered source results, source aliases,
corrections, and discrepancies under `NumStability/Source/<work>/`. Put copied
or adapted external code under `NumStability/Upstream/<origin>/` and preserve
its attribution and license.

Do not remove or rename a public declaration or import path from this release
branch without an explicit compatibility decision. Prefer a thin forwarding
module when an old import path must remain available.

## Required checks

Run from the repository root:

```bash
lake exe cache get
lake build NumStability
lake env lean examples/LibraryLookup.lean
```

Generated caches, benchmark output, local references, private agent files, and
scratch files must remain untracked.

## Licensing and provenance

The repository-level default license is MIT. Existing per-file license,
copyright, and author notices must be preserved during moves and refactors.
Do not change a file's license or invent a copyright holder while editing it.

New original Lean files use:

```lean
/-
SPDX-License-Identifier: MIT
-/
```

A file licensed under Apache-2.0 must retain its existing copyright and author
lines and include:

```lean
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
```

Copied, adapted, or backported code must retain the upstream notices, cite the
upstream project and immutable commit, describe the adaptation, and be listed
in [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).
