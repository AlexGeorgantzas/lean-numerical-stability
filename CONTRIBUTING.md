# Contributing to NumStability

NumStability is both a reusable numerical-stability library and a checked
correspondence with numerical-analysis sources. Keep those roles separate when
adding or moving code.

## Before changing modules

Read:

- [`ARCHITECTURE.md`](ARCHITECTURE.md) for API tiers and dependency direction;
- [`docs/architecture/NAMING.md`](docs/architecture/NAMING.md) for canonical
  paths and filenames;
- [`docs/architecture/COMPATIBILITY.md`](docs/architecture/COMPATIBILITY.md)
  before changing a historical import path;
- [`docs/architecture/MIGRATION.md`](docs/architecture/MIGRATION.md) for the
  evidence required by an architecture change.

## Place new code deliberately

Every new or moved production module must be classified in
[`docs/architecture/tiers.json`](docs/architecture/tiers.json). The remaining
historical inventory is recorded exactly in
[`docs/architecture/layout-exceptions.json`](docs/architecture/layout-exceptions.json);
that reviewed debt may only decrease until classification reaches 100%.

- Put source-independent mathematics in `FloatingPoint`, `Analysis`, or a
  semantic `Algorithms` family.
- Put numbered book results, source aliases, examples, corrections, and
  discrepancies under `NumStability/Source/<work>/`.
- Put unsupported proof scaffolding in `Internal/` below its closest
  mathematical owner.
- Put copied or adapted external code under `Upstream/<origin>/` and preserve
  its attribution and license.
- Keep tests in `NumStabilityTest`; production modules must not import tests.

Do not create a new module named for a chapter, theorem number, author, or proof
status in a reusable directory.

## Moving a module

Architecture changes are compatibility-preserving unless a breaking release
explicitly says otherwise.

1. Move the implementation to its canonical mathematical or source path.
2. Keep declaration names stable.
3. Leave the old path as an import-only forwarding module.
4. Update production consumers to the canonical import.
5. Add canonical-only and old-only import smoke tests.
6. Update the tier and compatibility manifests.
7. Regenerate the architecture baseline.

Do not combine a path move with declaration renames, visibility changes,
module-system conversion, or removal of earlier forwarding paths.

## Required checks

Run from the repository root:

```text
python tools/architecture/check_layout.py
python tools/architecture/check_compatibility.py
python tools/architecture/check_provenance.py
python tools/architecture/generate_baseline.py --skip-declarations --strict-source --output-dir benchmark-results/architecture --name source-check
lake build NumStability NumStabilityTest
```

Architecture batches should also build their canonical modules and isolated
historical wrappers directly. A full build does not prove that an old-only
wrapper works in isolation.

Generated caches, benchmark output, private Codex skills, local references, and
scratch files must remain untracked.

## Licensing and provenance

The repository-level default license is MIT. Existing per-file license,
copyright, and author notices must be preserved during moves and refactors.
Do not change a file's license or invent a copyright holder as part of an
architecture migration.

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

Copied, adapted, or backported code must:

1. live under `NumStability/Upstream/<origin>/`;
2. retain the upstream copyright, author, and license notices;
3. cite the upstream project, exact URL, and immutable full commit hash;
4. describe whether it was copied, adapted, or backported;
5. be listed in `THIRD_PARTY_NOTICES.md`.

Compatibility wrappers do not copy the implementation's copyright header
unless they contain copied code. Never perform a bulk relicensing while moving
or renaming modules.
