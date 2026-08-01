# Classification and Chapter 9/11 preparation validation

> **Status: superseded historical validation.** The blocked and deferred states
> below describe the pre-integration worker checkpoint, not the current tree.
> Chapter 9 and Chapter 11 are integrated with passing post gates; see
> `docs/architecture/migrations/2026-07-31-four-lane-final-integration.md`.

This file records the worker's historical validation at `6ecc4d551`. The next
historical integrator hashes, import refreshes, and rerun results were recorded
in `INTEGRATOR_REFRESH_9E7C8E324.md` and its JSON companion.

Static validation passes for the full 386-module proposal and both semantic
contracts. The frozen inventory and exclusions are an exact disjoint
partition of all 603 unclassified modules at the packet base.

| Workstream | Exact result |
| --- | ---: |
| Classification proposal | 386 modules |
| Reusable / source / mixed / aggregate | 129 / 212 / 44 / 1 |
| Chapter 9 candidates / declarations | 11 / 4,420 |
| Chapter 9 public / private | 4,392 / 28 |
| Chapter 11 candidates / declarations | 66 / 6,385 |
| Chapter 11 public / private | 6,239 / 146 |
| Chapter 11 explicit Chapter 9 dependencies | 61 |

The proposal checker, safe-apply self-test, both chapter checker self-tests,
both pre-contract checks, packet integrity, compatibility, provenance, Python
compilation, trust-marker scan, scope audit, and `git diff --check` passed.
`VALIDATION.json` records the exact commands, exit codes, hashes, and counts.

The shared layout gate reports only the three new worker smoke modules. That
is the expected consequence of the packet simultaneously requiring standalone
smokes and forbidding this lane from editing `NumStabilityTest.lean`. The exact
integrator-owned import request is in `INTEGRATOR_REQUEST.md`.

No Lean/lake build is claimed. The coordinator reserved the shared build mutex
for the main CI repair and instructed this lane to continue static work only.
The focused smokes, downstream builds, full build, and `lake test` remain an
explicit integrator rerun after the mutex is released.

Chapter 9 remains `BLOCKED_ON_BLOCKLU_INTEGRATION` until the integrator globally
verifies the observed BlockLU cutover at evidence head
`6ecc4d5513226e67594bb22985913f6a4a383e5c`. Chapter 11 remains
`BLOCKED_ON_CH09_INTEGRATION`; these implementation waves are serial.
