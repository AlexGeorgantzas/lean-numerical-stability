# W01 delivery — floating-point boundary split

| | |
| --- | --- |
| Phase | `repository-reorganization-2026-08` |
| Phase branch | `B0001` |
| Wave | `W01` |
| Branch | `codex/reorg-2026-08-w01-fp-boundary` |
| Base SHA | `d6e643adf0f20b33f7faebce7e1b9b1f87122c58` |
| Control `origin/main` | `21ae529c005b746e3f979997fa42c46224b6c4ae` (verified) |
| Projection | `P0001`, gzip SHA-256 `6278CE16…` (verified before use) |

This report describes the worker delivery tip. Integrator-owned semantic
boundary refinements and shared wiring, if required by the global gates, are
recorded separately at the acceptance checkpoint.

## What moved

The four owned modules held 67,081 lines and 3,697 selected declarations in one
undifferentiated `Analysis` layer. They now split by semantic role into 14
destinations. Every declaration keeps its name, type, visibility and proof; nothing
was renamed, no visibility changed, and every span was copied byte for byte from the
base commit.

The chapter assignment follows Higham's own structure. Chapter 1, "Principles of
Finite Precision Computation", is cancellation, increasing precision, instability
without cancellation and the HP-48G repeated sqrt/square example. Chapter 2,
"Floating Point Arithmetic", is the IEEE format, the standard model, Sterbenz and
Ferguson's exact-subtraction results and the machine environment. Everything that is
neither — the format model, the IEEE value and exception types, the rounding
selectors and the local-error algebra — is source-neutral and reusable.

| Destination | Family | Declarations |
| --- | --- | --- |
| `NumStability.Analysis.FloatingPointArithmetic.IeeeExceptions` | reusable | 580 |
| `NumStability.Analysis.FloatingPointArithmetic.IeeeOperations` | reusable | 228 |
| `NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError` | reusable | 350 |
| `NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError` | reusable | 276 |
| `NumStability.Analysis.FloatingPointArithmetic.Format` | reusable | 241 |
| `NumStability.Analysis.FloatingPointArithmetic.Rounding` | reusable | 238 |
| `NumStability.Analysis.FloatingPointArithmetic.IeeeValue` | reusable | 227 |
| `NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.InstabilityWithoutCancellation` | Chapter 1 | 872 |
| `NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.CancellationOfRoundingErrors` | Chapter 1 | 88 |
| `NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.IncreasingPrecision` | Chapter 1 | 21 |
| `NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.ExactSubtraction` | Chapter 2 | 179 |
| `NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.StandardModel` | Chapter 2 | 47 |
| `NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.AdditiveUnderflowModel` | Chapter 2 | 37 |
| `NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.Environment` | Chapter 2 | 12 |
| `NumStability.Analysis.CancellationOfRoundingErrors` | retained | 27 |
| `NumStability.Analysis.IncreasingPrecision` | retained | 34 |
| `NumStability.Analysis.InstabilityWithoutCancellation` | retained | 6 |
| `NumStability.Analysis.FloatingPointArithmetic` | retained | 234 |
| **Total** | | **3,697** |

The four old paths remain as declaration-bearing compatibility facades,
re-stating their original imports so that the 46 modules importing them keep
the transitive surface they had. All four retain declarations; see below.

## The 301 retained declarations

`Analysis.BeneficialRounding`, `Analysis.Accumulation` and
`Algorithms.LU.GaussianElimination` all reach `Analysis.FloatingPointArithmetic`,
which W01 turns into a compatibility module importing the new destinations. Any
destination needing those three therefore closes a cycle, and `lake` refuses it.
Since all three are shared and outside `B0001`'s write scope, W01 leaves the
declarations that depend on them -- and, transitively, their users -- in their original
modules.

A second and larger cause is private-name mangling. Lean encodes the defining module
in a private declaration's name, so relocating one renames it and the projection loses
every incident edge; see `PROJECTION.md`. All 21 privates therefore stay put, together
with their user closure. Between the two causes, 301 of 3,697 declarations are
retained and 3,396 relocate.

This is inside the projection contract rather than a workaround of it: `P0001` lists
all four historical modules under `--allow-module`, so each retained declaration keeps
its name, kind, visibility and every incident edge. `SHARED_PATCH_REQUEST.md` records the two-line retarget that releases the
cycle-driven retentions in a follow-up. The private-name retentions are inherent to
Lean and are not releasable by any integrator patch.

## Gate results

| Gate | Result |
| --- | --- |
| 1. Build affected canonical and compatibility modules | `Build completed successfully (4996 jobs)`, exit 0 |
| 2. Isolated old-import and canonical-import tests | `Build completed successfully (3024 jobs)`, exit 0, 18 modules |
| 3. `check_layout.py` | worker delivery requires integrator wiring: direct run reports 18 unreachable W01 tests, 7 unclassified reusable leaves, 1 new declaration-bearing facade, and missing Chapter 1 aggregate reachability; resolved by the acceptance checkpoint |
| 3. `check_compatibility.py` | passed — 296 forwarding modules, 566 canonical targets |
| 3. `check_provenance.py` | passed — 207 Apache-marked files, 5 evidenced upstream modules |
| 4. Locked candidate extraction and `P0001` comparison | **`phase projection contract passed`**, exit 0 — see `PROJECTION.md` |
| 5. 3,697 declarations / 48,076 incident union edges | `selected_declarations: 3697`, `relocated_declarations: 3396`, signature 22,706 + body 45,433 (48,076 distinct pairs) — all preserved |
| 6. `git diff` restricted to owned/destination paths | 40 changed files, **0 out of scope** — see `CHANGED_PATHS.md` |

Structural checks run before every build, on the emitted files:

| Check | Result |
| --- | --- |
| Declaration spans byte-identical to base, each emitted exactly once | 3,523 / 3,523 |
| Destination graph acyclic | 14 destinations, 44 edges, 0 SCCs |
| Reusable → source edges | **0** |
| Destinations mixing two owners' import surfaces | **0** |
| Destination → retained-declaration edges | **0** |
| Namespace/section balance, no duplicated namespace, valid namespace segments, sorted imports | 14 / 14 |
| Import cycles across the whole tree | 0 of 2,264 modules |

## Notes for the reviewer

Five defects surfaced only under the compiler, none visible to span or graph checks,
because relocating a declaration also has to reproduce its elaboration environment.
They are worth knowing before the next wave:

1. **Inherited imports that cycle.** Copying an owned module's project imports into a
   destination pulls in modules that import the owned module back. 3 of 21 candidates
   cycled; excluded by computing each candidate's transitive closure at the base.
2. **Excluding a cyclic import drops what it transitively supplied.**
   `InstabilityWithoutCancellation` reached `gammaValid` through
   `Analysis.Accumulation`; removing Accumulation removed `Analysis.Rounding` with it,
   and Lean reported the unknown identifier 8,500 lines in. Fixed by adding back the
   21 project modules those imports supplied that do not themselves reach an owned
   module.
3. **Widening the import surface is a behaviour change.** A destination shared by two
   owners inherits the union of their Mathlib imports, which the compatibility module
   re-exports downstream. That made `Algorithms/TriangularArbitraryOrder` parse `GL`
   as a token inside an `obtain` pattern and broke two `simp` calls in
   `Analysis/Problem2_24` — both files untouched by W01 and green at the base. Fixed
   by keeping every destination to a single contributing owner.
4. **Private-name mangling is not a namespace path.**
   `_private.<module>.<n>.<name>` split on dots yields `namespace _private` and
   `namespace 0`, which fails the parser. Fixed by stripping to the logical name, with
   a guard rejecting any non-identifier namespace segment.
5. **A file-level `noncomputable section` must travel with its declarations.**
   `FloatingPointArithmetic.lean` opens one; the emitter reproduces it per destination
   and errors if a destination would mix directive and non-directive owners.
