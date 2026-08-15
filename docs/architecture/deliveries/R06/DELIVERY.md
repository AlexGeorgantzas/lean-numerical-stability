# R06 delivery — Schur, Sylvester, pivoting, Chapters 9, 11, and 16

R06 executes the frozen, reviewed, and totality-amended B0007 route over 75
C0003 owners holding 9,415 selected declarations. Forty-eight whole owners
move 2,094 declarations to 48 canonical destinations; their historical paths
become declaration-free compatibility wrappers with exactly one import, the
destination named by the frozen R0007 compatibility postimage. Twenty-one
already declaration-free owners remain byte-identical and are classified as
compatibility modules. Six retained owners keep 7,321 declarations in place,
byte-identical to their actual C0003 blobs. No historical path is deleted and
none is Git-renamed.

Base: C0003 `e20de2f931caa12221e708c341e9cb4f64d29b25`

Branch: `codex/reorg-completion-2026-08-r06-schur-sylvester-pivoting-ch09-ch11-ch16`

Controls: planned `b6794f326313f8077c0c3433bb9c76b6e2ed5361` → activation
`405e76f36a342a5d7d31a8e094cc7c580dcb250f` → reviewed private-map totality
amendment `d6a241de6c2af12439bc48885461c7190fc751d6`, each with green Lean CI
(runs 31844203563, 31845432265, and 31893563259).

Projection: P0007 · Shared request: R0007 (integrator-only) · Operator:
`codex-local`.

## Exact delivery

| quantity | value |
| --- | ---: |
| historical owners | 75 (48 relocated / 21 compatibility-classified / 6 retained) |
| selected declarations | 9,415 (9,215 public / 200 private) |
| relocated declarations | 2,094 into 48 destinations |
| retained declarations | 7,321 across 6 retained owners |
| declaration-free wrappers created | 48 (one frozen destination import each) |
| unchanged declaration-free compatibility owners | 21 |
| private normalizations | 200 total map rows: 195 genuine rename rows + 5 identity rows |
| frozen isolated tests | 169 (48 canonical / 75 historical / 45 consumer / 1 aggregate root) |
| additional test modules | exhaustive `PrivateNormalization.lean` + `All.lean` |
| R06 test sources | 171; `All.lean` imports the other 170 |
| `#check` commands | 11,114 across the R06 suite |
| changed paths | 276 (48 modified / 228 added; 96 production / 171 tests / 9 delivery docs) |

## Content and import preservation

Every destination was derived from the pristine actual
`git show e20de2f931caa12221e708c341e9cb4f64d29b25:<owner-path>` blob. It keeps
the owner's complete original import surface and byte-identical declaration
content; exactly 123 in-wave owner-import occurrences were retargeted to the
corresponding sibling destinations. Each of the 48 historical wrappers has
exactly its frozen destination import and no declaration. The 21
compatibility-classified owners and 6 retained owners are byte-identical to
their actual C0003 blobs.

The frozen B0007 module-route metadata has one documented stale blob field:
retained owner `NumStability.Source.Higham.Chapter09.Section06` records
`base_blob_oid` `4ef7c94aa23d3dfe9da918c7a8d5dc9537a1405f`, from before R03 import
retargeting. The actual C0003 blob is
`6c946c73321b74b9350f61954f1742bf166c83d0`, and the R06 worker file is
byte-identical to that authoritative C0003 blob. This is planning-metadata
context only: no route, owner, destination, request, projection, or production
content changed.

The strict-source worker graph has zero unresolved imports, zero cyclic SCCs,
and zero forbidden reusable-reachability pairs. No umbrella/self-reference
cycle exists in this wave, so R06 needs no excluded descendants or
cycle-breaker docstrings.

## Gate disposition

All implementation-owned gates are green: the four frozen test classes,
private normalization, the exhaustive R06 aggregate, the production build,
the combined production/test build, `lake test`, compatibility, provenance,
strict-source, placeholder scan, cache-integrity verification, and the amended
P0007 delivery replay.

The terminal cache-safety audit matched all 22,320 primary IR artifacts to the
pre-build manifest. It found 21,216 reusable worker artifacts still hardlinked,
three worker-root `Chapter11.Section02.Aasen` IR artifacts deliberately
detached and rebuilt, zero missing artifacts, and zero primary changes. The
single exploratory write-through detected earlier was restored byte-for-byte
from a distinct pristine cache copy before the corrected-tree battery, then
verified again after the last Lake command; no tracked checkout content or ref
was touched by that remediation.

`check_layout` exits 1 only for exactly seven integrator-owned items and no
other red:

1. `NumStabilityTest` does not yet import the 171 new R06 test modules.
2. `NumStability.Analysis.MatrixEquations.SylvesterExistence` is new and not
   yet classified in the integrator-owned layout manifest.
3. `NumStability.Source` misses nine new Chapter 16 descendants.
4. `NumStability.Source.Higham` misses the same nine descendants.
5. `NumStability.Source.Higham.Chapter16` misses eleven descendants.
6. `NumStability.Source.Higham.Chapter16.Section03` misses
   `PerturbationAndConditioning.AutomaticBounds.Results.Core`.
7. `NumStability.Source.Higham.CrossChapter` misses
   `SymmetricIndefiniteLU.ActualExecutorBridge` and
   `SymmetricIndefiniteLU.BridgeClosure`.

For items 3–5, the common nine are
`Chapter16.HessenbergSchur.Results`, `Chapter16.HessenbergSchur.Rounded`,
`Chapter16.Minimizers.Results`, `Chapter16.Problem02.Results.Core`,
`Chapter16.QuasiRounded.Sylvester`,
`Chapter16.Section03.PerturbationAndConditioning.AutomaticBounds.Results.Core`,
`Chapter16.Spectrum.Minimizers`, `Chapter16.VecNorm.Results`, and
`Chapter16.VecPermutation.Notes`; the Chapter 16 umbrella additionally misses
`Chapter16.QuasiRounded.Solve` and `Chapter16.Spectrum.Results`.

The measured layout summary is 2,738 modules, 255 unclassified modules, zero
mixed modules, zero missing module docs, 217 legacy naming exceptions, 15
declaration-bearing umbrellas, and zero unsorted import blocks. The seven
findings are intentionally left for R0007 integration.
