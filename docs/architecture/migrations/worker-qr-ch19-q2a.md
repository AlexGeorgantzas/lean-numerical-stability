# QR / Chapter 19 Q2A reusable foundations

Q2A moves the next dependency-closed reusable QR foundation below
`NumStability.Algorithms.LinearSystems.QR` while keeping each historical
`NumStability.Algorithms.QR` import as an exact forwarding module.  The lane is
based exactly on published `main` commit
`32771e355612a6fca1b6153733d3f0dc124d26e2` and branch
`codex/org-qr-ch19-q2a`.  The checker extension is committed separately as
`026a704355edc292e1d6607f508cdada02e1c397`.

The immutable full-QR command and declaration contract remains the one frozen
for Householder Wave 1.  All six source blobs at the Q2A base equal their
`qr-ch19-frozen-owners.tsv` integrated blobs.

## Exact surface

| Historical owner | Canonical destination | Declarations | Commands | Private |
| --- | --- | ---: | ---: | ---: |
| `NumStability.Algorithms.QR.GivensSpec` | `NumStability.Algorithms.LinearSystems.QR.GivensSpec` | 71 | 53 | 7 |
| `NumStability.Algorithms.QR.GivensMatrixStep` | `NumStability.Algorithms.LinearSystems.QR.GivensMatrixStep` | 46 | 28 | 0 |
| `NumStability.Algorithms.QR.GivensQR` | `NumStability.Algorithms.LinearSystems.QR.GivensQR` | 110 | 91 | 0 |
| `NumStability.Algorithms.QR.GramSchmidt` | `NumStability.Algorithms.LinearSystems.QR.GramSchmidt` | 416 | 310 | 0 |
| `NumStability.Algorithms.QR.GramSchmidtPolar` | `NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar` | 55 | 55 | 0 |
| `NumStability.Algorithms.QR.QRSolve` | `NumStability.Algorithms.LinearSystems.QR.QRSolve` | 170 | 143 | 0 |
| **Total** | **6 destinations** | **868** | **680** | **7** |

Relative to completed Householder Wave 1, the materialization layers are:

1. `GivensSpec`, `GramSchmidt`, and `QRSolve`;
2. `GivensMatrixStep` and `GramSchmidtPolar`;
3. `GivensQR`.

The reviewed import rewrites are exact:

- `GivensMatrixStep`: `GivensSpec` to its canonical leaf;
- `GivensQR`: `GivensSpec`, `GivensMatrixStep`, and `HouseholderQR` to their
  canonical leaves;
- `GramSchmidt`: `HouseholderQR` to its canonical leaf;
- `GramSchmidtPolar`: `GramSchmidt` to its canonical leaf, with
  `RandNLA.LowRankApprox` unchanged;
- `QRSolve`: `HouseholderQR` to its canonical leaf, with triangular back
  substitution and external imports unchanged;
- `GivensSpec`: no project import rewrite is needed.

Each historical owner now contains exactly its one canonical import.  Six
canonical-only tests and six old-only tests import one leaf apiece.  Their
lane aggregate is `NumStabilityTest.Worker.QrCh19.Q2A`; no partial production
QR aggregate was created.

The seven Givens private declarations remain private and require no
cross-destination promotion.  Their exact candidate names were read from the
built canonical `GivensSpec.ilean` and added to
`qr-ch19-private-rewrites.tsv`.  The manifest now has 22 rows: the 15 reviewed
Householder rewrites plus 7 Q2A rewrites.  Its SHA-256 is
`0AF30AAAC0CD11B54F644999D364E015BBECE889AB6D1D9EE5C5BEDFB4866C84`.

Q2A is an essential compilation dependency for the QR-to-LSQ handoff, but it
supplies no canonical source owner among the coordinator's 69 owner/carrier
rows. The earlier one-row estimate conflated dependency unblocking with
physical handoff ownership. The MGS source family is intentionally not
included in this wave.

## Evidence

The final static materialization gate re-found all 680 frozen command byte
strings exactly once and accepted exactly six wrappers and six destinations.
The checker negative self-test passed.

Compiler-backed gates ran through the shared
`Local\LeanNumericalStabilityLargeBuild` mutex:

- all six canonical targets passed in one focused build: 3,030 jobs;
- all six historical wrappers, all twelve isolated test leaves, and the Q2A
  test aggregate passed in one warmed build: 3,049 jobs;
- warnings were inherited linter warnings only; no source command was edited
  to silence them.

Static gates also passed:

- the six reusable roots reach 65 project modules, with zero missing internal
  imports, zero `NumStability.Source` modules, and zero historical QR modules;
- every canonical-only and old-only test has exactly one reviewed import, and
  the Q2A aggregate has 12 sorted unique imports;
- the placeholder/axiom-command scan passed for all 18 declaration-bearing
  Q2A production and test leaves;
- `check_compatibility.py` passed with 119 forwarding modules and 228
  canonical targets;
- `check_provenance.py` passed with 207 Apache-marked production files and 5
  evidenced upstream modules;
- `git diff --check` passed.

An exact candidate semantic-stream attempt was made without a global build.
The fresh worktree has focused Q2A artifacts but no current
`.lake/build/lib/lean/NumStability.olean`; Lake therefore stopped before
extraction.  Per coordinator instruction, no full global build or cache copy
was launched solely to fill missing consumers.  The normalized incident-graph
stage gate is deferred to the warmed integrator after the shared registration
patches below.

`check_layout.py` reports only the intentionally omitted shared registrations:
the 13 Q2A test modules are not yet reachable from `NumStabilityTest`, and the
two exact import-only wrappers `GramSchmidt` and `GramSchmidtPolar` need
reviewed missing-module-docstring exceptions.  It reports no new import
ordering, mixed-module, umbrella, placeholder, or classification error.

## Exact integrator patch request

After cherry-picking the checker and implementation commits:

1. In `NumStabilityTest.lean`, add
   `import NumStabilityTest.Worker.QrCh19.Q2A` after the existing
   `HouseholderWave1` worker import.
2. In the sorted `legacy.missing_module_docstrings` array of
   `docs/architecture/layout-exceptions.json`, add exactly
   `NumStability.Algorithms.QR.GramSchmidt` and
   `NumStability.Algorithms.QR.GramSchmidtPolar` between `GivensSpec` and
   `Higham19`.
3. Run a warmed full `NumStability` build, retain the candidate format-2
   stream, and run QR stage mode with all 12 Householder destinations and all
   6 Q2A destinations.  The exact expected stage tuple is 22 private rewrites,
   1,501 byte-identical commands, 17 wrappers, and 18 destinations.

No tier change is needed: the existing
`NumStability.Algorithms.LinearSystems.QR` reusable prefix classifies all six
canonical leaves.  `NumStability.Algorithms.LinearSystems` already reaches all
six leaves, and no Source root is involved.  No `COMPATIBILITY.md`, production
aggregate, LSQ, Chapter 9, or Chapter 11 edit is requested.
