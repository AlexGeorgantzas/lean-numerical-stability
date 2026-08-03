# W03 delivery report

Wave `W03`, branch `codex/reorg-2026-08-w03-cholesky-ch10`, phase branch `B0004`, base checkpoint
`C0004` at `b56f609f3bf66b5d7d0b677567cce82fee0c275b`.

W03 reorganizes the 26 owned modules in `NumStability/Algorithms` into a semantic
reusable Cholesky hierarchy and exact Higham Chapter 10, 11, 6 and 14 source modules,
preserving every public declaration name, namespace, kind, visibility, statement,
proof and typed incident edge, and keeping every historical import path compiling.

## Result

| | |
| --- | --- |
| declarations selected by `W03.tsv` | 1034 |
| relocated to canonical modules | 806 |
| retained at the historical owner | 228 |
| canonical destination modules written | 61 |
| destination roots covered | 32 / 32 |
| compatibility modules | 26 (16 declaration-bearing, 10 pure import shims) |
| focused test modules | 87 (61 canonical-only, 26 old-path) |
| source lines at C0004 | 28,505 |

## Why 228 declarations did not move

Lean mangles a private declaration to `_private.<defining module>.<n>.<name>`, so the
defining module is part of the name: relocating a private renames it and every
incident edge is reported missing against the frozen graph. `P0005` contains **93**
private declarations, 52 of them in `Ch10ComplexPositiveDefiniteSourceClosure`.

The reverse dependency closure runs in two stages:

1. a same-module user of a private cannot see it from anywhere else, giving 171;
2. a *different*-owner user would force its canonical destination to import the
   owner's compatibility facade, inverting the direction the strict-source gate
   enforces, giving 228.

`RETENTION.tsv` records every retained declaration with its reason and the private or
retained declaration that triggers it. B0004 anticipates this: it "permits
declaration-bearing historical facades and does not promise 26 pure import shims".
16 of the 26 owners remain declaration-bearing facades and are documented as
such; the other 10 are pure import shims. None is falsely labelled.

## Gates

| # | gate | result |
| --- | --- | --- |
| 1 | B0004 scope audit | passed — 26/26 owned paths, 33/34 destination prefixes, **0 forbidden paths**, 0 unclassified |
| 2 | canonical-only builds | passed — 61 canonical-only test modules, each importing exactly one canonical module |
| 3 | old-path-only builds | passed — 26 old-path test modules, each importing only a historical path |
| 4 | focused W03/family builds | passed — covered by the 87 single-import test modules |
| 5 | `lake build NumStability` | `Build completed successfully (5291 jobs)`, exit 0 |
| 6 | every W03 test module built explicitly | `Build completed successfully (3678 jobs)`, exit 0 |
| 7 | `lake test` (existing full target) | exit 0 |
| 8 | `check_compatibility.py` | passed — 327 forwarding modules, 643 canonical targets |
| 9 | `check_provenance.py` | passed — 200 Apache-marked production files, 5 evidenced upstream modules |
| 10 | `check_layout.py` | **integrator wiring required** — see `INTEGRATOR_REQUESTS.md`; every remaining error resolves only through a forbidden shared aggregate, tier manifest, root test or ratchet |
| 11 | strict-source format-2 generation | exit 0, zero cycles, zero reusable-to-source reachability |
| 12 | full format-2 candidate from the worker tree | `benchmark-results/W03-candidate.tsv`, sha256 `088BD0413F728B18…` |
| 13 | `P0005` replay with recorded arguments | **`phase projection contract passed`**, exit 0 |
| 14 | declaration and edge preservation | `selected_declarations: ?`, `relocated_declarations: ?`, signature ? + body ? |

Every Lean operation ran under the phase build mutex `lean-reorganization-2026-08`
recorded in `phase.json`; acquisition waited 19 minutes for the concurrent W05
worker. Static editing and read-only graph inspection ran without it.

## Static checks run before each build

These caught four defects that a green build would not have revealed, or that would
have cost a full build behind a contended mutex to find:

1. **A reusable-to-source dependency.** `higham10_7_onesMatrix_opNorm2Le` is a generic
   fact about the all-ones matrix that merely carries the chapter prefix; two
   genuinely reusable declarations use it. Leaving it in the source tier made
   `MatrixNorms.EntrywiseAbsolute` depend on `Chapter10.Theorem07`.
2. **A mis-placed cut inside the reusable tier.** `scaled_opNorm2Le_of_factor_bound`
   matches the generic norm pattern but is proved from `chol_cert_colNormSq_le`, so
   classifying it as a matrix-norm fact put a certificate consumer below the
   certificates and closed a cycle.
3. **Ambient Source inheritance.** Reusable destinations derived from the mixed
   `HighamChapter10` inherited its ten direct `Source.Higham.Chapter09.*` imports.
4. **Fourteen noncanonical module names.** `check_layout.py` forbids a
   `Source.Higham.ChapterNN` leaf beginning with `Chapter`, and requires a
   `Theorem|Lemma|Equation` locator leaf to carry exactly two digits. The
   `ChapterSurface`, `Equation1029` and `Equation1022` leaves were renamed to
   `Endpoints`, `Equation29` and `Equation22`, and the stale files removed.

No axiom, `sorry`, `admit`, theorem weakening, proof replacement or fabricated API was
introduced: the base-to-delivery diff adds none, and declaration text is relocated
byte-identically (887 emit units, each verified to appear exactly once).

## Integration

`INTEGRATOR_REQUESTS.md` records every integrator-owned change with exact paths.
W03 is accepted as milestone `M03` only after the integrator retargets the 34
non-owner C0004 consumers, wires the umbrellas and manifests, and reruns the
acceptance gates.
