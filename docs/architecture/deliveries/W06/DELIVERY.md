# W06 delivery

W06 reorganizes every one of B0006's 67 historical owners and their 84,241
baseline source lines from the C0005 code base
`240c0d041781385a647fbec461d6863537e562cb`.  It preserves all historical
imports and all 3,512 selected declarations while separating reusable
Sylvester/Lyapunov and matrix-power mathematics from exact Higham Chapter 16/18
source material.

The delivery branch is
`codex/reorg-2026-08-w06-ch16-ch18-remaining`.  The immutable final delivery SHA
is the Git object reported in the handoff; a commit cannot embed its own object
name.  This report and the exact base-to-delivery inventory travel in that
commit.

## Scope and path inventory

The final expected inventory is 518 paths:

| Class | Paths |
| --- | ---: |
| Historical W06 owners modified | 67 |
| Canonical production modules added | 176 |
| W06 tests added | 257 |
| W06 delivery/evidence files added | 18 |
| **Total** | **518** |

`CHECK_SCOPE.py` generates `CHANGED_PATHS.md` from the exact
`240c0d041781385a647fbec461d6863537e562cb..DELIVERY_HEAD` Git inventory.  The
final check accounts for 67/67 owners and reports zero forbidden paths, zero
unowned paths, zero paths outside B0006 destinations, and zero tracked build
artifacts.

The 176 canonical production modules comprise 112 declaration leaves, 15
reviewed Source locators, and 49 `.All` modules.  The declaration leaves split
into 67 reusable and 45 source-numbered modules.  Seventeen reviewed activation
suggestions were correctly omitted because their projected declarations are
retained or their proposed leaves would be empty.

## Declaration routing

| Route | Declarations |
| --- | ---: |
| Relocated to reusable APIs | 2,114 |
| Relocated to exact Chapter 16/18 source modules | 623 |
| **Relocated total** | **2,737** |
| Retained in historical owners | 775 |
| **Selected total** | **3,512** |

The retained set contains all 94 private declarations and 681 public
declarations.  The graph-only reverse closure is 768 declarations: 94 private
plus 674 transitively pinned public declarations.  Seven additional public
commands in `Higham16Problem16_2` are retained to preserve their ambient
notation/section context.  No private declaration was moved or renamed.

There are 23 declaration-bearing historical facades and 44 pure import shims.
Every public name, kind, visibility, statement, proof, and typed incident edge
is preserved.  `DECLARATION_ROUTES.tsv`, `RETENTION.tsv`,
`PRIVATE_CLOSURE.tsv`, and `REVIEWED_ROUTE_STATUS.tsv` are the mechanical
authorities.

## Semantic destinations

Reusable declarations are routed only into B0006's reviewed narrow children of:

- `NumStability.Algorithms.MatrixEquations.Sylvester`
- `NumStability.Algorithms.MatrixPowers`
- `NumStability.Algorithms.NormEstimation`
- `NumStability.Analysis.CStarMatrices`
- `NumStability.Analysis.FunctionalCalculus`
- `NumStability.Analysis.LinearOperators.Jordan`
- `NumStability.Analysis.LinearOperators.MatrixPowers`
- `NumStability.Analysis.LinearOperators.NumericalRadius`
- `NumStability.Analysis.LinearOperators.Pseudospectra`
- `NumStability.Analysis.LinearOperators.Schur.Real.Triangularization`
- `NumStability.Analysis.MatrixInequalities.LiebTrace`

Printed equations, numbered results, problem material, corrections, and
source-specific endpoints are routed only to exact children of
`NumStability.Source.Higham.Chapter16` and
`NumStability.Source.Higham.Chapter18`.  No destination outside B0006 was
created.

## Tests

| Test class | Count | Isolation |
| --- | ---: | --- |
| Canonical-only | 176 | exactly one canonical production import per test |
| Old-path-only | 67 | exactly one historical owner import per test |
| Focused | 14 | Sylvester, retained bridges, matrix powers, and protected surfaces |
| **Total** | **257** | all below `NumStabilityTest/Reorganization/W06/` |

`TEST_MATRIX.tsv` records every module, import, class, and representative
declaration.  The protected focused targets cover accepted W02/W05 APIs and the
W07/W09/W11 historical compatibility surfaces.

## Gate ledger

Every Lean build, test, closure replay, and format-2 extraction held the Windows
named mutex `Local\lean-reorganization-2026-08`.

| Gate | Result |
| --- | --- |
| 67 old-path-only modules | **passed** - `Build completed successfully (3991 jobs)`, exit 0 |
| 176 canonical-only modules | **passed** - `Build completed successfully (4089 jobs)`, exit 0 |
| 14 focused modules | **passed** - `Build completed successfully (3982 jobs)`, exit 0 |
| All 257 W06 test modules explicitly | **passed** - `Build completed successfully (4348 jobs)`, exit 0 |
| Eight protected-surface focused modules | **passed** - `Build completed successfully (3673 jobs)`, exit 0 |
| Final repaired canonical targets | **passed** - `Build completed successfully (2953 jobs)`, exit 0 |
| `lake build NumStability` | **passed** - `Build completed successfully (5522 jobs)`, exit 0 |
| `lake build NumStability NumStabilityTest` | **passed** - `Build completed successfully (7169 jobs)`, exit 0 |
| `lake test` | **passed**, 7,166-job target, exit 0 |
| Compatibility contract | **passed** - 337 forwarding modules, 685 canonical targets |
| Provenance contract | **passed** - 201 Apache-marked production files and 5 evidenced upstream modules |
| No new `sorry` / `admit` / `axiom` / placeholder | **passed** - zero findings in all 500 changed Lean paths |
| Import sorting, module docs, and case-fold uniqueness | **passed** for every W06-owned path |
| Deterministic migration reconstruction | **passed** - 3,512 declarations; 2,737 relocated; 775 retained |
| Private reverse-closure replay | **passed** - 3,450 selected commands; 768 graph-retained; SHA-256 `5391A2EAED68263FE9EE2B38D35F79A1660BF06728580D37485286CC115B0E64` |
| W06 canonical import graph | **passed** - 176 modules; zero cycles, unresolved imports, W06-facade reachability, or reusable-to-Source reachability |
| Full format-2 candidate | **passed**, exit 0 - 56,903 declarations and 649,259 typed edge rows scanned |
| Deterministic candidate replay | **passed** - JSON and Markdown reproduced byte-identically |
| P0007 exact comparison | **passed**, exit 0 - 3,512 selected, 2,737 relocated, 775 retained, all typed edges preserved |
| Exact B0006 scope | **passed** - final generated inventory; zero forbidden, unowned, or generated paths |

The repository-wide strict-source command exits 2 on 31 classified
reusable-to-Source pairs caused only by forbidden accepted/future consumers of
mixed historical facades.  Its source scan otherwise has 2,035 modules, zero
unresolved imports, zero cycles, and zero reusable-to-mixed pairs.  The exact
six sources, six targets, and deferred W07 bridge are documented in
`INTEGRATOR_REQUESTS.md`.  This is integration/future-wave debt; the W06-owned
canonical graph itself is green and no authorized worker edit can remove it.

`check_layout.py` similarly exits 1 only for integrator-owned state: 257 tests
are not yet reachable from `NumStabilityTest`, 101 new modules need tier
classification, and shared aggregate reachability is pending.  Import sorting
is already clean.  The exact aggregate gaps are recorded in the integrator
request and generated manifest.

## Projection result

The full candidate TSV SHA-256 is
`7A312F60BDA611BBEB7DDF8060A9C360172DC945C91800B4C5D888A11C447B47`.
P0007 passes with exactly:

- 3,512 selected declarations;
- 2,737 relocated and 775 retained declarations;
- 15,044 signature edge rows;
- 16,341 body/proof edge rows; and
- 22,079 union edges.

`PROJECTION.md` records every pinned hash, the exact replay result, and the
byte-identical deterministic replay.

## Dependency boundaries

- W06 to accepted W05: 13 direct imports; 4,943 signature plus 3,218
  body/proof rows; 8,161 typed rows and 5,777 union pairs.
- W06 to accepted W02: six direct imports; 309 signature plus 217 body/proof
  rows; 526 typed rows and 343 union pairs.
- W06 to future W10: one retained import and three body/proof rows.
- Protected downstream historical imports: W07 = 3, W09 = 1, W11 = 3.

The accepted W05 import actions were applied exactly.  Historical `Higham16`
imports remain only where retained declarations are consumed.  Accepted W02
consumer retargets, shared discovery wiring, test discovery, tiers/layout,
compatibility documentation, and future-wave retargets are all patch-ready in
`INTEGRATOR_REQUESTS.md`; no forbidden consumer or shared file was edited.

## Evidence artifacts

| File | Purpose |
| --- | --- |
| `DECLARATION_ROUTES.tsv` | one exact route for all 3,512 declarations |
| `PRIVATE_CLOSURE.tsv` / `PRIVATE_CLOSURE.md` | private seeds, reverse closure, witnesses, and context retention |
| `RETENTION.tsv` | per-owner moved/retained and facade classification |
| `REVIEWED_ROUTE_STATUS.tsv` | reviewed destination realization and intentional omissions |
| `ROUTING.md` | semantic routing and dependency explanation |
| `TEST_MATRIX.tsv` | all 257 isolated/focused tests |
| `DEPENDENCY_BOUNDARY.tsv` | exact accepted/future typed boundary counts |
| `INTEGRATOR_MANIFEST.json` | exact shared umbrellas, test imports, and tier classifications |
| `GENERATE_MIGRATION.py` | deterministic migration reconstruction |
| `PRIVATE_CLOSURE_PLAN.py` | hash-pinned P0007 closure computation |
| `CHECK_STATIC.py` | W06 canonical graph, test, placeholder, and facade checks |
| `CHECK_PROJECTION.py` | pinned exact P0007 replay |
| `CHECK_SCOPE.py` / `CHANGED_PATHS.md` | generated base-to-delivery scope proof |
| `INTEGRATOR_REQUESTS.md` | exact forbidden/shared changes for acceptance and later waves |

No W04/W07/W08/W09/W10/W11/W90 owner, phase control, root aggregate, tier or
layout manifest, compatibility document, CI/toolchain file, or other worker
branch was modified.
