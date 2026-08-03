# W05 delivery — Sylvester, Schur, and source separation

| | |
| --- | --- |
| Phase | `repository-reorganization-2026-08` |
| Phase branch | `B0005` |
| Wave | `W05` |
| Branch | `codex/reorg-2026-08-w05-ch16-ch18` |
| Base checkpoint | `C0004` |
| Base SHA | `b56f609f3bf66b5d7d0b677567cce82fee0c275b` |
| Implementation commit | `f5db61325e470f540c00b1cfead8470e6c818ad1` |
| Projection | `P0006` |
| Final status | **worker delivery ready for integration acceptance** |

This report describes the complete W05 worker delivery.  The final record commit
cannot embed its own SHA; the immutable delivery SHA is the published remote branch
tip reported by the worker and subsequently recorded by the integrator.

## Scope and result

W05 reorganizes exactly ten historical owners containing 17,618 source lines and
the complete P0006 selection of 921 declarations: 121 definitions and 800 theorems.
Every historical import path remains available.

| Outcome | Declarations |
| --- | ---: |
| Reusable canonical APIs | 502 |
| Chapter 16 source modules | 281 |
| Retained in historical `Higham16` | 138 |
| **Total** | **921** |

The reusable declarations comprise 404 Sylvester/Lyapunov declarations, 89
Schur/invariant-subspace declarations, and 9 generic inverse/singular-value bounds.
The emitted production surface has 62 declaration-bearing leaves, 3 import-only
source locators, and 14 narrow `All` entry points: 79 modules in total.

## Semantic boundary

- Reusable Sylvester equations, backward error, perturbation, conditioning, and
  generalized-equation APIs live below
  `NumStability.Algorithms.MatrixEquations.Sylvester`.
- Reusable complex/real Schur and invariant-subspace APIs live below
  `NumStability.Analysis.LinearOperators.Schur`.
- Nine generic inverse/operator-two bounds live below
  `NumStability.Analysis.SingularValues.InverseBounds`; the three
  Sylvester/Lyapunov singular-value bridges live with Sylvester conditioning.
- Numbered Higham declarations live under the exact Chapter 16 Section 01–05
  destinations.  Chapter 16 real-Schur and Chapter 18 complex-Schur source
  destinations are import-only locators over reusable APIs.

No reusable destination imports a historical W05 owner or a `Source` module.  The
new destination import graph is acyclic.  `ROUTING.md` and
`DECLARATION_ROUTES.tsv` provide the human and declaration-level authorities.

## Private identity and historical compatibility

`Higham16` contains three genuine-private declarations.  Since Lean encodes their
defining module in the generated name, they and their complete reverse user closure
remain in the historical module:

- `rectMatMul_left_right_sub`: 64 declarations;
- `sylvesterVecCoeff_det_ne_zero_of_sepLowerBound`: 74 declarations, including
  the 37-declaration closure of
  `sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf`.

The two top-level closures are disjoint: 3 private plus 135 public declarations,
138 total.  The other nine historical owners are import-only facades.  No private
declaration was moved, promoted, or renamed, and no declaration statement or proof
was replaced.  `PRIVATE_CLOSURE.tsv` records the exact witnesses.

The frozen projection records 13 direct W06-to-W05 imports and 8,161 typed
W06-to-W05 declaration edges.  W05 edits no W06 owner.  Exact later retargets,
including the retained-closure exceptions, are patch-ready in
`INTEGRATOR_REQUESTS.md`.

## Tests

| Test class | Count | Isolation |
| --- | ---: | --- |
| Canonical-only | 79 | exactly one canonical production import per test |
| Old-path-only | 10 | exactly one historical owner import per test |
| Focused | 3 | Sylvester, Schur, and inverse-bound behavior |
| **Total** | **92** | all below `NumStabilityTest/Reorganization/W05/` |

`TEST_MATRIX.tsv` records every test, import, and representative declaration.

## Gate ledger

Every Lean build and semantic extraction below held the Windows named mutex
`Local\lean-reorganization-2026-08`.

| Gate | Result |
| --- | --- |
| 79 canonical-only modules | **passed** — `Build completed successfully (3011 jobs)` |
| 10 old-path-only modules after final facade repair | **passed** — `Build completed successfully (2935 jobs)` |
| 3 focused modules | **passed** — `Build completed successfully (2899 jobs)` |
| W06 retained-surface target | **passed** — `Build completed successfully (2647 jobs)` |
| `lake build NumStability` | **passed** — `Build completed successfully (5292 jobs)` |
| Explicit build of all 92 W05 tests | **passed** — `Build completed successfully (3034 jobs)` |
| `lake test` | **passed**, exit 0 — `[6746/6746] Built NumStabilityTest` |
| Compatibility contract | **passed** — 327 forwarding modules, 643 canonical targets |
| Provenance contract | **passed** — 204 Apache-marked production files, 5 evidenced upstream modules |
| No new `axiom`/`sorry`/`admit` | **passed** — zero matches in every changed/added Lean file |
| Static destination graph | **passed** — 79 modules, zero cycles, zero canonical-to-historical imports, zero reusable-to-Source imports, zero missing module docs |
| Isolated-test inventory | **passed** — 79 canonical, 10 compatibility, 3 focused; zero import-isolation mismatches |
| Layout | **integration pending**, exit 1 only for forbidden shared wiring: 92 root-unreachable tests, 43 new reusable modules needing classification, 7 resolved legacy-doc entries needing baseline refresh, and shared aggregate reachability |
| Deterministic migration reconstruction | **passed** — 921 declarations reproduced as 502 reusable, 281 source, and 138 retained |
| Private reverse-closure replay | **passed** — 921 commands, 138 retained, 783 movable |
| Strict-source format-2 audit | **passed**, exit 0 — 1,748 modules, zero unresolved imports, zero cycles, and zero forbidden reusable-to-source/mixed reachability |
| Full format-2 candidate | **passed** — strict build completed successfully (5292 jobs); TSV SHA-256 `89E4BEE5E541E5AD4DD2F386282DAD2F920D7013194A0ECBBE5CB67722FBE89D` |
| Deterministic no-build replay | **passed** — TSV, JSON, and Markdown hashes all reproduced byte-identically |
| P0006 exact comparison | **passed**, exit 0 — 921 selected, 783 relocated, 8,562 signature and 6,894 body edges; 11,020 union edges recorded |
| Exact B0005 scope | **passed** — 193 paths: 10 owned plus 183 authorized additions; zero unowned or forbidden paths |
| `git diff --check` | **passed**, exit 0 |

## Evidence artifacts

| File | Purpose |
| --- | --- |
| `DECLARATION_ROUTES.tsv` | all 921 declarations, exactly one route each |
| `PRIVATE_CLOSURE.tsv` / `PRIVATE_CLOSURE.md` | private seeds, reverse closure, witnesses, and retained partition |
| `ROUTING.md` | reviewed semantic route and declaration counts |
| `TEST_MATRIX.tsv` | all 92 isolated/focused tests |
| `GENERATE_MIGRATION.py` | hash-pinned deterministic tree reconstruction |
| `PRIVATE_CLOSURE_PLAN.py` | hash-pinned C0004/P0006 closure computation |
| `PROJECTION.md` | candidate hashes, replay, arguments, and exact P0006 result |
| `CHANGED_PATHS.md` / `CHECK_SCOPE.py` | generated base-to-delivery inventory and B0005 scope proof |
| `INTEGRATOR_REQUESTS.md` | exact forbidden/shared changes for acceptance and W06 |

## Integrator boundary

W05 does not edit phase controls, global/family aggregates, chapter umbrellas, root
tests, tier/layout manifests, compatibility documentation, CI/toolchain files, or
W06 owners.  The layout-only debt above is resolved solely through those forbidden
shared files.  In particular, the integrator must retarget
`SemiconvergentExistenceFull`, wire the mixed Sylvester aggregate, create the narrow
family/chapter umbrellas, classify nine pure facades as compatibility while retaining
reviewed debt for declaration-bearing `Higham16`, and apply the exact W06 import
rules after W06 is owned.
